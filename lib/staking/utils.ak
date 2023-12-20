use aiken/builtin
use aiken/cbor

test maps_serialize() {
  let thing =
    [(0, 1), (1, 2), (8, 88)]
  let diag = cbor.diagnostic(thing)

  let other_diag = cbor.diagnostic(builtin.serialise_data(thing))

  trace @"first diag"

  trace diag

  trace @"second diag"

  trace other_diag

  True
}
