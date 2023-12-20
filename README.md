# Staking

This repository contains the `staker` stake validator. The validator supports
the following actions:

- `Initialize`: This action is used to initialize the staking process. This
  mints a one time NFT that has an empty token name to store with the staking
  state datum. This allows the minting of one receipt token.
- `Delegate`: This action allows a user to delegate their stake to a validator.
  This requires spending the token created in initialize and satisfying the
  datum condition in addition to being the datum owner. This allows for the
  minting of one receipt token.
- `Withdraw`: This action allows a user to withdraw their stake from a
  validator. The use can prove they are the owner either by spending the init
  NFT or referencing it and proving being the datum owner.
- `Close`: This action is used to close the staking process. This requires
  spending the token created in initialize and satisfying the datum condition in
  addition to being the datum owner.

This validator has no redeemers and uses the existence or lack of existence of
mints, inputs, delegation, and withdraws to validate various actions.

For more details on how these actions work, please refer to the `staker.ak` file
in the `validators` directory.
