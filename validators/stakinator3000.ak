use aiken/builtin
use aiken/dict
use aiken/interval.{Finite, Interval, IntervalBound}
use aiken/list
use aiken/time.{PosixTime}
use aiken/transaction.{
  InlineDatum, Input, Mint, Output, OutputReference, Publish, ScriptContext,
  Spend, Transaction, WithdrawFrom,
}
use aiken/transaction/certificate.{
  CredentialDelegation, CredentialDeregistration, CredentialRegistration,
}
use aiken/transaction/credential.{
  Address, Credential, Inline, PaymentCredential, PoolId, ScriptCredential,
}
use aiken/transaction/value.{
  AssetName, PolicyId, from_minted_value, quantity_of, tokens,
}

type Owner {
  PKH(ByteArray)
  NFT(PolicyId, AssetName)
  Receipt(AssetName)
}

type InputCondition {
  HasAddress(Address)
  HasToken(PolicyId, AssetName, Int)
  HasDatum(Data)
  HasPkh(Credential)
  HasField { field_data: Data, field_path: List<Int> }
}

type TxCondition {
  Mints(PolicyId, AssetName, Int)
  IsAfter(PosixTime)
  IsBefore(PosixTime)
  /// Please note the `outer list` in InputsCondition could all be satisfied by a single input. 
  /// The checks are per all inputs not a unique input
  /// The `inner list` acts on a single input ensuring the input meets all conditions via &&
  InputsCondition(List<List<InputCondition>>)
  ReferenceInputsCondition(List<List<InputCondition>>)
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

type NFTAsset {
  policy: PolicyId,
  asset: AssetName,
}

validator(state_token: NFTAsset) {
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

    expect ScriptCredential(own_pkh) = payment_credential

    let State { owner, redelegation_condition, .. } = state

    let NFTAsset { policy: nft_policy, asset: nft_asset } = state_token

    let Interval { lower_bound, upper_bound } = validity_range

    let IntervalBound { bound_type, is_inclusive: upper_inclusive } =
      upper_bound

    expect Finite(upper) = bound_type

    let IntervalBound { bound_type, is_inclusive: lower_inclusive } =
      lower_bound

    expect Finite(lower) = bound_type

    // Checks current owner is valid
    expect True =
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
          let x = mint |> from_minted_value |> quantity_of(own_pkh, token_name)

          x == -1
        }
      }

    // Check input contains parameterized NFT
    expect True = quantity_of(in_value, nft_policy, nft_asset) == 1

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

          StakesTo(pool) -> {
            let expected_cert =
              CredentialDelegation {
                delegator: Inline(ScriptCredential(own_pkh)),
                delegatee: pool,
              }
            list.any(certificates, fn(cert) { expected_cert == cert })
          }
        }
      }

    expect True =
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
            nft_policy,
            nft_asset,
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

    let NFTAsset { policy: nft_policy, asset: nft_asset } = state_token

    when purpose is {
      Mint(own_policy) -> {
        expect [first_input, ..] = inputs

        let asset_name = first_input.output_reference |> builtin.serialise_data

        mint
          |> from_minted_value
          |> tokens(own_policy)
          |> dict.to_list
          |> check_mint_to_output_datum(
               outputs,
               asset_name,
               state_token,
               ScriptCredential(own_policy),
             )
      }

      WithdrawFrom(cred) -> {
        expect Inline(cred) = cred

        let find_predicate =
          fn(input: Input) {
            let output = input.output

            output.address.payment_credential == cred && (
              output.value |> quantity_of(nft_policy, nft_asset)
            ) == 1
          }

        if list.any(inputs, find_predicate) {
          True
        } else {
          expect Some(Input { output: Output { datum, .. }, .. }) =
            list.find(reference_inputs, find_predicate)

          expect InlineDatum(datum) = datum
          expect State { owner, .. }: State = datum

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
            // Checks for state token is spent
            list.any(
              inputs,
              fn(input) {
                let output = input.output

                output.address.payment_credential == cred && (
                  output.value |> quantity_of(nft_policy, nft_asset)
                ) == 1
              },
            )
          }

          CredentialRegistration(_) -> True
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
  input_conditions: List<List<InputCondition>>,
  inputs: List<Input>,
) -> Bool {
  when input_conditions is {
    [] -> True
    [x, ..xs] -> has_valid_input(x, inputs) && validate_inputs(xs, inputs)
  }
}

fn has_valid_input(
  input_conds: List<InputCondition>,
  inputs: List<Input>,
) -> Bool {
  when input_conds is {
    [] -> True
    [cond, ..rest_conds] -> {
      let input_condition_runner =
        when cond is {
          HasAddress(address) ->
            fn(input: Input) { input.output.address == address }

          HasToken(t_policy, t_name, t_amount) ->
            fn(input: Input) {
              ( input.output.value |> quantity_of(t_policy, t_name) ) == t_amount
            }
          HasDatum(datum) -> {
            let inline_datum = InlineDatum(datum)
            fn(input: Input) { input.output.datum == inline_datum }
          }

          HasPkh(cred) ->
            fn(input: Input) { input.output.address.payment_credential == cred }

          HasField { field_data, field_path } ->
            fn(input: Input) {
              when input.output.datum is {
                InlineDatum(dat) -> traverse_datum(dat, field_data, field_path)
                _ -> False
              }
            }
        }

      let inputs_offset = find_input_offset(inputs, input_condition_runner)

      when inputs_offset is {
        [] -> False
        [input, ..rest_inputs] ->
          validate_other_conditions(rest_conds, input) || has_valid_input(
            input_conds,
            rest_inputs,
          )
      }
    }
  }
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

fn find_input_offset(
  inputs: List<Input>,
  with: fn(Input) -> Bool,
) -> List<Input> {
  when inputs is {
    [] ->
      []
    [input, ..rest] ->
      if with(input) {
        inputs
      } else {
        find_input_offset(rest, with)
      }
  }
}

fn validate_other_conditions(
  input_conds: List<InputCondition>,
  input: Input,
) -> Bool {
  when input_conds is {
    [] -> True
    [cond, ..rest] -> {
      let is_valid =
        when cond is {
          HasAddress(address) -> input.output.address == address

          HasToken(t_policy, t_name, t_amount) ->
            ( input.output.value |> quantity_of(t_policy, t_name) ) == t_amount
          HasDatum(datum) -> {
            let inline_datum = InlineDatum(datum)
            input.output.datum == inline_datum
          }

          HasPkh(cred) -> input.output.address.payment_credential == cred

          HasField { field_data, field_path } ->
            when input.output.datum is {
              InlineDatum(dat) -> traverse_datum(dat, field_data, field_path)
              _ -> False
            }
        }

      is_valid && validate_other_conditions(rest, input)
    }
  }
}

type OwnerCheck {
  owner: Owner,
  field1: Data,
  field2: Data,
}

// Check each minted token name is in the expected list, has quantity of 1,
// and has a corresponding ouput with datum containing token name.
// Alternatively allow for token burning
// Otherwise fail
fn check_mint_to_output_datum(
  minted_assets: List<(ByteArray, Int)>,
  outputs: List<Output>,
  expected_asset: ByteArray,
  expected_nft: NFTAsset,
  validator_cred: PaymentCredential,
) -> Bool {
  when minted_assets is {
    [] -> True
    [(minted_asset_name, quantity), ..rest_assets] ->
      if quantity == 1 {
        expect True = expected_asset == minted_asset_name

        expect True =
          list.any(
            outputs,
            fn(output) {
              let Output { address, value, datum, .. } = output

              if address.payment_credential == validator_cred {
                // Check for nft present
                let NFTAsset { policy, asset } = expected_nft
                if quantity_of(value, policy, asset) == 1 {
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
          expected_nft,
          validator_cred,
        )
      } else if quantity == -1 {
        check_mint_to_output_datum(
          rest_assets,
          outputs,
          expected_asset,
          expected_nft,
          validator_cred,
        )
      } else {
        False
      }
  }
}
