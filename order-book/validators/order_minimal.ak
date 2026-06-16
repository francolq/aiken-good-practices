//// Truly minimal `order` validator: `Resolve` only checks that the
//// output at the chosen index pays at least `amount` of the requested
//// asset (anywhere — owner, script, third party). No address, datum
//// or lovelace checks. `Close` only checks the owner's signature.
////
//// Vulnerable in multiple ways:
//// - The output paying `amount` may sit at any address, so the
////   resolver can pay themselves and walk away with the locked value.
//// - Double satisfaction. N script inputs can share a single `out_ix`,
////   satisfying every branch with a single payment.
//// - Any UTxO at the script address is treated as a legitimate order.

use aiken/collection/list
use aiken/crypto.{VerificationKeyHash}
use cardano/assets.{AssetName, PolicyId, quantity_of}
use cardano/transaction.{OutputReference, Transaction}

pub type OrderDatum {
  owner: VerificationKeyHash,
  amount: Int,
  policy_id: PolicyId,
  asset_name: AssetName,
}

pub type SpendRedeemer {
  Resolve(Int)
  Close
}

validator order_minimal {
  spend(
    datum: Option<OrderDatum>,
    redeemer: SpendRedeemer,
    _own_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { outputs, extra_signatories, .. } = self
    expect Some(datum) = datum
    let OrderDatum { owner, amount, policy_id, asset_name } = datum

    when redeemer is {
      Resolve(out_ix) -> {
        expect Some(out) = list.at(outputs, out_ix)
        quantity_of(out.value, policy_id, asset_name) >= amount
      }
      Close -> list.has(extra_signatories, owner)
    }
  }

  else(_) {
    fail
  }
}
