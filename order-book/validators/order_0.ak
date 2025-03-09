use aiken/crypto.{VerificationKeyHash}
use cardano/assets.{AssetName, PolicyId}
use cardano/transaction.{OutputReference, Transaction}

pub type OrderDatum {
  owner: VerificationKeyHash,
  amount: Int,
  policy_id: PolicyId,
  asset_name: AssetName,
}

pub type OrderRedeemer {
  Resolve
  Close
}

validator order {
  spend(
    _datum: Option<OrderDatum>,
    redeemer: OrderRedeemer,
    _own_ref: OutputReference,
    _self: Transaction,
  ) {
    when redeemer is {
      Resolve -> True
      Close -> True
    }
  }

  mint(_redeemer: Data, _policy_id: PolicyId, _self: Transaction) {
    True
  }

  else(_) {
    fail
  }
}
