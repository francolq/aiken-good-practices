use aiken/crypto.{VerificationKeyHash}
use cardano/assets.{AssetName, PolicyId}
use cardano/transaction.{
  InlineDatum, Output, OutputReference, Transaction, find_input,
}

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
    own_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { inputs, outputs, .. } = self
    when redeemer is {
      Resolve -> {
        expect Some(own_in) = find_input(inputs, own_ref)

        // questions:
        // do we have conditions over own_in?
        // do we have to check for val token in input?

        // assume continuation is the first output
        expect [cont_out, ..] = outputs

        // checks for continuation output
        expect Output {
          address: cont_addr,
          value: _cont_value,
          datum: InlineDatum(_cont_datum),
          reference_script: None,
        } = cont_out

        let cont_has_correct_addr = cont_addr == own_in.output.address

        cont_has_correct_addr?
      }
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
