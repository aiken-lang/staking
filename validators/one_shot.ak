use aiken/dict
use aiken/list
use aiken/transaction.{Mint, OutputReference, ScriptContext, Transaction}
use aiken/transaction/value.{from_minted_value, tokens}

validator(utxo_ref: OutputReference) {
  fn oneshot(_rdr: Data, ctx: ScriptContext) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    expect Mint(own_policy) = purpose
    let asset_name = "stakinator"

    let Transaction { inputs, mint, .. } = transaction

    expect [(mint_asset, mint_amount)] =
      mint |> from_minted_value |> tokens(own_policy) |> dict.to_list

    mint_asset == asset_name && mint_amount == 1 && list.any(
      inputs,
      fn(input) { input.output_reference == utxo_ref },
    )
  }
}
