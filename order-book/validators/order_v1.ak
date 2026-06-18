use aiken/collection/list
use aiken/crypto.{VerificationKeyHash}
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
    let Transaction { inputs, outputs, extra_signatories, .. } = self
    expect Some(datum) = datum
    let OrderDatum { owner, amount, policy_id, asset_name } = datum

    when redeemer is {
      Resolve -> {
        // TODO: check that it is not already resolved

        expect Some(own_in) = find_input(inputs, own_ref)

        // assume continuation is the first output
        expect [cont_out, ..] = outputs

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
            quantity_of(cont_value, policy_id, asset_name) >= amount,
            list.length(flatten(cont_value)) == 2,
          }
        }

        let cont_has_correct_datum = {
          expect cont_datum: OrderDatum = cont_datum
          cont_datum == datum
        }

        and {
          cont_has_correct_addr?,
          cont_has_correct_value?,
          cont_has_correct_datum?,
        }
      }

      Close -> list.has(extra_signatories, owner)
    }
  }

  else(_) {
    fail
  }
}
