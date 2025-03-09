use aiken/collection/list.{length}
use aiken/crypto.{VerificationKeyHash}
use cardano/address.{Script}
use cardano/assets.{AssetName, PolicyId, flatten, lovelace_of, quantity_of}
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
    datum: Option<OrderDatum>,
    redeemer: OrderRedeemer,
    own_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { inputs, outputs, .. } = self
    expect Some(OrderDatum { owner, amount, policy_id, asset_name }) = datum

    when redeemer is {
      Resolve -> {
        expect Some(own_in) = find_input(inputs, own_ref)
        expect Script(own_hash) = own_in.output.address.payment_credential

        // checks for continuation output
        expect [cont_out, ..] = outputs

        expect Output {
          address: cont_addr,
          value: cont_value,
          datum: InlineDatum(_cont_datum),
          reference_script: None,
        } = cont_out

        let cont_has_correct_addr = cont_addr == own_in.output.address

        let cont_has_correct_value = {
          // 1. first try:
          // and {
          //   quantity_of(cont_value, own_hash, "val") == 1,
          //   quantity_of(cont_value, policy_id, asset_name) >= amount,
          // }
          //
          // questions:
          // - can add/remove ADA?  YES
          // - can add/remove val token?  NO
          // - can leave some token A?  YES
          // - can add more token B?   YES
          // - can include other tokens?  YES

          // a more restrictive option:
          // - can't remove ADA
          // - all A must be removed
          // - exact amount of B must be added
          //
          // let in_lovelace = lovelace_of(own_in.output.value)
          // let expected_value = from_lovelace(in_lovelace)
          //   |> add(own_hash, "val", 1)
          //   |> add(policy_id, asset_name, amount)
          // // trace "EXPECTED": expected_value
          // // trace "ACTUAL": cont_value
          // match(cont_value, expected_value, >=)

          // chosen option:
          // - can't remove ADA
          // - all A must be removed
          // - can add more B than required
          let in_lovelace = lovelace_of(own_in.output.value)
          and {
            lovelace_of(cont_value) >= in_lovelace,
            quantity_of(cont_value, own_hash, "val") == 1,
            quantity_of(cont_value, policy_id, asset_name) >= amount,
            length(flatten(cont_value)) == 3,
          }
        }

        and {
          cont_has_correct_addr?,
          cont_has_correct_value?,
        }
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
