use aiken/collection/list
use aiken/collection/dict
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
  tag: OutputReference,
}

pub type SpendRedeemer {
  Resolve(Int)  // int indicates the output index
  Close
}

pub type MintRedeemer {
  Mint(OutputReference)
  Burn
}

validator order {
  spend(
    datum: Option<OrderDatum>,
    redeemer: SpendRedeemer,
    own_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { inputs, outputs, extra_signatories, mint, .. } = self
    expect Some(OrderDatum { owner, amount, policy_id, asset_name, tag }) = datum

    expect Some(own_in) = find_input(inputs, own_ref)
    expect Script(own_hash) = own_in.output.address.payment_credential

    when redeemer is {
      Resolve(out_ix) -> {
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
          Some(cont_datum) == datum
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
    let Transaction { inputs, outputs, mint, .. } = self

    expect [Pair("val", quantity)] =
      mint
        |> assets.tokens(policy_id)
        |> dict.to_pairs()

    when redeemer is {
      Mint(utxo_ref) -> {
        // XXX: does not support creating multiple orders
        // - should allow minting n tokens
        // - should iterate over n order outputs
        // - to be unique, the tag should include the output index

        // check that the given utxo_ref is consumed
        let is_utxo_consumed =
          list.any(inputs, fn(input) { input.output_reference == utxo_ref })

        // assume order output is the first output
        expect [order_out, ..] = outputs

        // checks for all aspects of the order output
        expect Output {
          address: order_addr,
          value: order_value,
          datum: InlineDatum(order_datum),
          reference_script: None,
        } = order_out

        // check for address: staking key is chosen by owner
        let order_has_correct_addr = order_addr.payment_credential == Script(policy_id)

        // check for value: minted token goes in this output
        // XXX: more checks here?
        let order_has_correct_value = quantity_of(order_value, policy_id, "val") == 1

        // check for datum: must have has correct unicity tag
        // (to avoid double satisfaction in spend)
        let order_has_correct_datum = {
          expect order_datum: OrderDatum = order_datum
          order_datum.tag == utxo_ref
        }

        and {
          // only one "val" token can be minted,
          // so only one order can be created
          quantity == 1,
          is_utxo_consumed,
          order_has_correct_addr,
          order_has_correct_value,
          order_has_correct_datum,
        }
      }
      Burn -> {
        quantity < 0
      }
    }
  }

  else(_) {
    fail
  }
}
