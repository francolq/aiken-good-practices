//// Vulnerable variant of `order.ak`: same shape as the Order
//// validator, but the `Resolve` branch checks `tag == None` instead
//// of `tag == Some(own_ref)`. The continuation datum is therefore
//// never bound to a specific input, so two distinct inputs at the
//// script address can be satisfied by a single shared continuation output.

use aiken/collection/dict
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

pub type SpendRedeemer {
  Resolve(Int)
  Close
}

pub type MintRedeemer {
  Mint
  Burn
}

validator order_vulnerable {
  spend(
    datum: Option<OrderDatum>,
    redeemer: SpendRedeemer,
    own_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { inputs, outputs, extra_signatories, mint, .. } = self
    expect Some(datum) = datum
    let OrderDatum { owner, amount, policy_id, asset_name, .. } = datum

    expect Some(own_in) = find_input(inputs, own_ref)
    expect Script(own_hash) = own_in.output.address.payment_credential

    when redeemer is {
      Resolve(out_ix) -> {
        expect Some(cont_out) = list.at(outputs, out_ix)

        expect Output {
          address: cont_addr,
          value: cont_value,
          datum: InlineDatum(cont_datum),
          reference_script: None,
        } = cont_out

        let cont_has_correct_addr = cont_addr == own_in.output.address

        let cont_has_correct_value = {
          let in_lovelace = lovelace_of(own_in.output.value)
          and {
            lovelace_of(cont_value) >= in_lovelace,
            quantity_of(cont_value, own_hash, "val") == 1,
            quantity_of(cont_value, policy_id, asset_name) >= amount,
            list.length(flatten(cont_value)) == 3,
          }
        }

        // VULNERABLE: requires `tag == None` instead of // `tag == Some(own_ref)`.
        let cont_has_correct_datum = {
          expect cont_datum: OrderDatum = cont_datum
          let expected_datum = OrderDatum { ..datum, tag: None }
          cont_datum == expected_datum
        }

        and {
          cont_has_correct_addr?,
          cont_has_correct_value?,
          cont_has_correct_datum?,
        }
      }
      Close -> {
        let tx_is_signed = list.has(extra_signatories, owner)

        let val_token_burned = {
          expect [Pair("val", quantity)] =
            mint
              |> assets.tokens(own_hash)
              |> dict.to_pairs()
          quantity < 0
        }

        and {
          tx_is_signed,
          val_token_burned,
        }
      }
    }
  }

  mint(redeemer: MintRedeemer, policy_id: PolicyId, self: Transaction) {
    let Transaction { outputs, mint, .. } = self

    expect [Pair("val", quantity)] =
      mint
        |> assets.tokens(policy_id)
        |> dict.to_pairs()

    when redeemer is {
      Mint -> {
        expect [order_out, ..] = outputs

        expect Output {
          address: order_addr,
          value: order_value,
          datum: InlineDatum(order_datum),
          reference_script: None,
        } = order_out

        let order_has_correct_addr =
          order_addr.payment_credential == Script(policy_id)

        let order_has_correct_value =
          quantity_of(order_value, policy_id, "val") == 1

        let order_has_correct_datum = {
          expect order_datum: OrderDatum = order_datum
          order_datum.tag == None
        }

        and {
          quantity == 1,
          order_has_correct_addr,
          order_has_correct_value,
          order_has_correct_datum,
        }
      }
      Burn -> quantity < 0
    }
  }

  else(_) {
    fail
  }
}
