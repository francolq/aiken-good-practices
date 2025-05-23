use aiken/collection/list
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
  tag: Option<OutputReference>,
}

// to avoid double satisfaction

pub type OrderRedeemer {
  Resolve(Int)
  // int indicates the output index
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
    expect Some(datum) = datum
    let OrderDatum { amount, policy_id, asset_name, .. } = datum

    when redeemer is {
      Resolve(out_ix) -> {
        expect Some(own_in) = find_input(inputs, own_ref)
        expect Script(own_hash) = own_in.output.address.payment_credential

        // continuation is the output with provided index `out_ix`
        expect Some(cont_out) = list.at(outputs, out_ix)

        // checks for continuation output
        expect Output {
          address: cont_addr,
          value: cont_value,
          datum: InlineDatum(cont_datum),
          reference_script: None,
        } = cont_out

        let cont_has_correct_addr = cont_addr == own_in.output.address

        let cont_has_correct_value = {
          // - can't remove lovelace
          // - all A must be removed
          // - can add more B than required
          let in_lovelace = lovelace_of(own_in.output.value)
          and {
            lovelace_of(cont_value) >= in_lovelace,
            quantity_of(cont_value, own_hash, "val") == 1,
            quantity_of(cont_value, policy_id, asset_name) >= amount,
            list.length(flatten(cont_value)) == 3,
          }
        }

        let cont_has_correct_datum = {
          expect cont_datum: OrderDatum = cont_datum
          // avoid double satisfaction: tag must be own_ref
          let expected_datum = OrderDatum { ..datum, tag: Some(own_ref) }
          cont_datum == expected_datum
        }

        and {
          cont_has_correct_addr?,
          cont_has_correct_value?,
          cont_has_correct_datum?,
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
