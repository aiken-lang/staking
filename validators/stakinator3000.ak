use aiken/builtin
use aiken/dict
use aiken/interval.{Finite, Interval, IntervalBound}
use aiken/list
use aiken/time.{PosixTime}
use aiken/transaction.{
  DatumHash, InlineDatum, Input, Mint, Output, OutputReference, Publish,
  ScriptContext, Spend, Transaction, WithdrawFrom,
}
use aiken/transaction/certificate.{
  CredentialDelegation, CredentialDeregistration,
}
use aiken/transaction/credential.{
  Address, Credential, Inline, PoolId, ScriptCredential,
}
use aiken/transaction/value.{
  AssetName, PolicyId, from_minted_value, quantity_of, tokens,
}

type Owner {
  PKH(ByteArray)
  NFT(PolicyId, AssetName)
  Receipt(AssetName)
}

type OutputCondition {
  HasAddress(Address)
  HasToken(PolicyId, AssetName, Int)
  HasDatum(Data)
  HasPkh(Credential)
  HasField { field_data: Data, field_path: List<Int> }
  HasHash(ByteArray)
}

type TxCondition {
  Mints(PolicyId, AssetName, Int)
  IsAfter(PosixTime)
  IsBefore(PosixTime)
  /// Please note the `outer list` in InputsCondition could all be satisfied by a single input. 
  /// The checks are per all inputs not a unique input
  /// The `inner list` acts on a single input ensuring the input meets all conditions via &&
  InputsCondition(List<List<OutputCondition>>)
  ReferenceInputsCondition(List<List<OutputCondition>>)
  OutputsCondition(List<List<OutputCondition>>)
  StakesTo(PoolId)
}

type StakeCondition {
  Is(TxCondition)
  And(List<StakeCondition>)
  Or(List<StakeCondition>)
  Not(TxCondition)
}

type State {
  owner: Owner,
  redelegation_condition: StakeCondition,
  stake_registration: PosixTime,
}

type OwnerCheck {
  owner: Owner,
  field1: Data,
  field2: Data,
}

type NFTAsset {
  policy: PolicyId,
  asset: AssetName,
}

validator(init_input: OutputReference) {
  /// remember `rdr` still needs to be wrapped in a index 1 constr for multivalidator purposes
  fn conditional_spend(state: State, rdr: Data, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    expect Spend(own_out_ref) = purpose

    let Transaction {
      inputs,
      reference_inputs,
      outputs,
      mint,
      validity_range,
      extra_signatories,
      certificates,
      ..
    } = transaction

    expect Some(own_input) =
      list.find(inputs, fn(input) { input.output_reference == own_out_ref })

    let Input {
      output: Output { address: in_address, value: in_value, .. },
      ..
    } = own_input

    let Address { payment_credential, .. } = in_address

    // Some destructuring fields in the script context
    expect ScriptCredential(own_policy) = payment_credential

    let State { owner, redelegation_condition, .. } = state

    let Interval { lower_bound, upper_bound } = validity_range

    let IntervalBound { bound_type, is_inclusive: upper_inclusive } =
      upper_bound

    expect Finite(upper) = bound_type

    let IntervalBound { bound_type, is_inclusive: lower_inclusive } =
      lower_bound

    expect Finite(lower) = bound_type

    // Checks current owner is valid
    expect
      when owner is {
        // An owner can be a public key, a spent NFT, or a burned receipt token that was minted by this script
        PKH(signer) -> list.has(extra_signatories, signer)
        // In this case the redeemer out ref refers to some other input that holds the nft 
        // that we check is spent
        NFT(policy, token_name) -> {
          expect nft_input_owner: OutputReference = rdr
          expect Some(nft_input) =
            list.find(
              inputs,
              fn(input) { input.output_reference == nft_input_owner },
            )
          quantity_of(nft_input.output.value, policy, token_name) == 1
        }
        Receipt(token_name) -> {
          let x =
            mint |> from_minted_value |> quantity_of(own_policy, token_name)
          x == -1
        }
      }
    // Check input contains init NFT
    expect quantity_of(in_value, own_policy, "") == 1
    // Validates non-recursive conditions
    let tx_condition_runner =
      fn(cond: TxCondition) -> Bool {
        when cond is {
          Mints(policy, token_name, amount) -> {
            let x = mint |> from_minted_value |> quantity_of(policy, token_name)
            x == amount
          }

          IsAfter(after) -> after > lower && lower_inclusive

          IsBefore(before) -> before < upper && upper_inclusive

          InputsCondition(input_conditions) ->
            validate_inputs(input_conditions, inputs)

          ReferenceInputsCondition(ref_conditions) ->
            validate_inputs(ref_conditions, reference_inputs)

          OutputsCondition(out_conditions) ->
            validate_outputs(out_conditions, outputs)

          StakesTo(pool) -> {
            let expected_cert =
              CredentialDelegation {
                delegator: Inline(ScriptCredential(own_policy)),
                delegatee: pool,
              }
            list.any(certificates, fn(cert) { expected_cert == cert })
          }
        }
      }

    expect
      when redelegation_condition is {
        Is(tx_cond) -> tx_condition_runner(tx_cond)
        Not(tx_cond) -> !tx_condition_runner(tx_cond)
        And(conds) ->
          validate_stake_conditions(conds, True, tx_condition_runner)
        Or(conds) ->
          validate_stake_conditions(conds, False, tx_condition_runner)
      }
    // find output with same address and nft state token
    expect Some(Output { datum: InlineDatum(out_datum), .. }) =
      list.find(
        outputs,
        fn(output) {
          output.address == in_address && quantity_of(
            output.value,
            own_policy,
            "",
          ) == 1
        },
      )

    // Ensure output stake registration shows right time.
    expect State { stake_registration, .. }: State = out_datum

    // Confusing enough we get milliseconds from the node instead of slot time. So time is in milliseconds
    let time_range = ( upper - lower ) / 2 / 1000
    // I'm converting to seconds for simplicity
    stake_registration == lower + time_range && time_range >= 180
  }

  fn conditional_multi(rdr: Data, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    let Transaction {
      inputs,
      reference_inputs,
      outputs,
      mint,
      extra_signatories,
      ..
    } = transaction

    when purpose is {
      Mint(own_policy) -> {
        let minted_under_policy =
          mint
            |> from_minted_value
            |> tokens(own_policy)
            |> dict.to_list

        expect [first_input, ..] = inputs

        let asset_name =
          first_input.output_reference
            |> builtin.serialise_data
            |> builtin.blake2b_256

        when minted_under_policy is {
          // impossible case
          [] -> False
          [(minted_asset_name, 1), ..rest] if minted_asset_name == "" -> {
            expect [output, ..] = outputs

            let Output { address, value, .. } = output

            and {
              address.payment_credential == ScriptCredential(own_policy),
              value.quantity_of(value, own_policy, "") == 1,
              list.any(
                inputs,
                fn(input) { input.output_reference == init_input },
              ),
              check_mint_to_output_datum(
                rest,
                outputs,
                asset_name,
                ScriptCredential(own_policy),
                own_policy,
              ),
            }
          }

          all ->
            check_mint_to_output_datum(
              all,
              outputs,
              asset_name,
              ScriptCredential(own_policy),
              own_policy,
            )
        }
      }

      WithdrawFrom(cred) -> {
        expect Inline(cred) = cred
        expect ScriptCredential(own_policy) = cred

        let find_predicate =
          fn(input: Input) {
            let output = input.output

            output.address.payment_credential == cred && (
              output.value |> quantity_of(own_policy, "")
            ) == 1
          }

        // State token is spent and spend validator will perform owner check
        if list.any(inputs, find_predicate) {
          True
        } else {
          // Not spend so we must check for owner
          expect Some(Input { output: Output { datum, .. }, .. }) =
            list.find(reference_inputs, find_predicate)

          expect InlineDatum(datum) = datum
          expect OwnerCheck { owner, .. }: OwnerCheck = datum

          // Checks current owner is valid
          when owner is {
            // An owner can be a public key, a spent NFT, or a burned receipt token that was minted by this script
            PKH(signer) -> list.has(extra_signatories, signer)
            // In this case the redeemer out ref refers to some other input that holds the nft 
            // that we check is spent
            NFT(policy, token_name) -> {
              expect nft_input_owner: OutputReference = rdr

              expect Some(nft_input) =
                list.find(
                  inputs,
                  fn(input) { input.output_reference == nft_input_owner },
                )

              quantity_of(nft_input.output.value, policy, token_name) == 1
            }

            // Since we are not spending the state token input then we rely on some input just spending with the receipt token
            // In this case the redeemer out ref refers to some other input that holds the receipt token 
            // that we check is spent
            Receipt(token_name) -> {
              expect nft_input_owner: OutputReference = rdr

              expect Some(nft_input) =
                list.find(
                  inputs,
                  fn(input) { input.output_reference == nft_input_owner },
                )

              expect ScriptCredential(own_policy) = cred

              quantity_of(nft_input.output.value, own_policy, token_name) == 1
            }
          }
        }
      }
      Publish(cert) ->
        when cert is {
          CredentialDelegation { delegator, .. } | CredentialDeregistration {
            delegator,
          } -> {
            expect Inline(cred) = delegator
            expect ScriptCredential(own_policy) = cred
            // Checks for state token is spent
            list.any(
              inputs,
              fn(input) {
                let output = input.output

                output.address.payment_credential == cred && (
                  output.value |> quantity_of(own_policy, "")
                ) == 1
              },
            )
          }
          _ -> False
        }
      _ -> False
    }
  }
}

fn validate_stake_conditions(
  conditions: List<StakeCondition>,
  is_and: Bool,
  with: fn(TxCondition) -> Bool,
) {
  when conditions is {
    [] -> is_and
    [cond, ..rest_conds] ->
      when cond is {
        Is(tx_cond) -> {
          let condition_check = with(tx_cond)
          if is_and == condition_check {
            validate_stake_conditions(rest_conds, is_and, with)
          } else {
            condition_check
          }
        }

        Not(tx_cond) -> {
          let condition_check = !with(tx_cond)
          if is_and == condition_check {
            validate_stake_conditions(rest_conds, is_and, with)
          } else {
            condition_check
          }
        }
        And(more_conds) -> {
          let condition_check =
            validate_stake_conditions(more_conds, True, with)
          if is_and == condition_check {
            validate_stake_conditions(rest_conds, is_and, with)
          } else {
            condition_check
          }
        }
        Or(more_conds) -> {
          let condition_check =
            validate_stake_conditions(more_conds, False, with)
          if is_and == condition_check {
            validate_stake_conditions(rest_conds, is_and, with)
          } else {
            condition_check
          }
        }
      }
  }
}

fn validate_inputs(
  input_conditions: List<List<OutputCondition>>,
  inputs: List<Input>,
) -> Bool {
  when input_conditions is {
    [] -> True
    [x, ..xs] -> has_valid_input(x, inputs) && validate_inputs(xs, inputs)
  }
}

fn validate_outputs(
  output_conditions: List<List<OutputCondition>>,
  outputs: List<Output>,
) -> Bool {
  when output_conditions is {
    [] -> True
    [x, ..xs] -> {
      let combined_conditions = build_up_validation(x)
      list.any(outputs, combined_conditions) && validate_outputs(xs, outputs)
    }
  }
}

fn build_up_validation(conds: List<OutputCondition>) -> fn(Output) -> Bool {
  when conds is {
    [] ->
      fn(_output: Output) { True }
    [cond, ..rest_conds] -> {
      let inner_check = build_up_validation(rest_conds)

      when cond is {
        HasAddress(address) ->
          fn(output: Output) {
            output.address == address && inner_check(output)
          }

        HasToken(t_policy, t_name, t_amount) ->
          fn(output: Output) {
            ( output.value |> quantity_of(t_policy, t_name) ) == t_amount && inner_check(
              output,
            )
          }
        HasDatum(datum) -> {
          let inline_datum = InlineDatum(datum)
          fn(output: Output) {
            output.datum == inline_datum && inner_check(output)
          }
        }

        HasPkh(cred) ->
          fn(output: Output) {
            output.address.payment_credential == cred && inner_check(output)
          }

        HasField { field_data, field_path } ->
          fn(output: Output) {
            when output.datum is {
              InlineDatum(dat) ->
                traverse_datum(dat, field_data, field_path) && inner_check(
                  output,
                )
              _ -> False
            }
          }
        HasHash(datum_hash) -> {
          let datum_hash = DatumHash(datum_hash)
          fn(output: Output) {
            output.datum == datum_hash && inner_check(output)
          }
        }
      }
    }
  }
}

fn has_valid_input(
  input_conds: List<OutputCondition>,
  inputs: List<Input>,
) -> Bool {
  let combined_conditions = build_up_validation(input_conds)
  let input_condition_runner =
    fn(input: Input) { combined_conditions(input.output) }

  list.any(inputs, input_condition_runner)
}

fn traverse_datum(datum: Data, field: Data, field_path: List<Int>) -> Bool {
  when field_path is {
    [] -> datum == field
    [path, ..rest_path] -> {
      let list_of_fields = builtin.snd_pair(builtin.un_constr_data(datum))
      when list.at(list_of_fields, path) is {
        None -> False
        Some(x) -> traverse_datum(x, field, rest_path)
      }
    }
  }
}

// Check each minted token name is in the expected list, has quantity of 1,
// and has a corresponding ouput with datum containing token name.
// Alternatively allow for token burning
// Otherwise fail
fn check_mint_to_output_datum(
  minted_assets: List<(ByteArray, Int)>,
  outputs: List<Output>,
  expected_asset: ByteArray,
  validator_cred: Credential,
  validator_policy: PolicyId,
) -> Bool {
  when minted_assets is {
    [] -> True
    [(minted_asset_name, quantity), ..rest_assets] ->
      if quantity == 1 {
        expect expected_asset == minted_asset_name
        expect
          list.any(
            outputs,
            fn(output) {
              let Output { address, value, datum, .. } = output
              if address.payment_credential == validator_cred {
                // Check for nft present
                if quantity_of(value, validator_policy, "") == 1 {
                  // Check for receipt datum for minted receipt token
                  expect InlineDatum(data) = datum
                  expect OwnerCheck { owner: Receipt(asset), .. }: OwnerCheck =
                    data
                  asset == expected_asset
                } else {
                  False
                }
              } else {
                False
              }
            },
          )
        check_mint_to_output_datum(
          rest_assets,
          outputs,
          expected_asset,
          validator_cred,
          validator_policy,
        )
      } else if quantity == -1 {
        check_mint_to_output_datum(
          rest_assets,
          outputs,
          expected_asset,
          validator_cred,
          validator_policy,
        )
      } else {
        False
      }
  }
}
