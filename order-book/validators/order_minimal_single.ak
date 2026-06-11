//// Minimal `order` validator with single-input restriction: same as
//// `order_minimal`, but also requires that exactly one input lives at
//// the script's own address. Prevents double-satisfaction at the cost
//// of composability.

use aiken/collection/list
use aiken/crypto.{VerificationKeyHash}
use cardano/assets.{AssetName, PolicyId, quantity_of}
use cardano/transaction.{OutputReference, Transaction, find_input}

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

validator order_minimal_single {
  spend(
    datum: Option<OrderDatum>,
    redeemer: SpendRedeemer,
    own_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { inputs, outputs, extra_signatories, .. } = self
    expect Some(datum) = datum
    let OrderDatum { owner, amount, policy_id, asset_name } = datum

    expect Some(own_in) = find_input(inputs, own_ref)
    let own_addr = own_in.output.address
    let single_input =
      list.count(inputs, fn(i) { i.output.address == own_addr }) == 1

    let branch_ok =
      when redeemer is {
        Resolve(out_ix) -> {
          expect Some(out) = list.at(outputs, out_ix)
          quantity_of(out.value, policy_id, asset_name) >= amount
        }
        Close -> list.has(extra_signatories, owner)
      }

    and {
      single_input?,
      branch_ok?,
    }
  }

  else(_) {
    fail
  }
}
