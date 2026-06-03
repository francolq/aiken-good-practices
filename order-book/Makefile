.PHONY: all build flats verify clean

# Full pipeline: compile Aiken, encode every validator's UPLC to flat hex, then re-check the Lean proofs.
all: verify

# Compile validators and dump textual UPLC under artifacts/.
build:
	aiken build -u

# Encode every artifacts/<module>.<validator>.<handler>.uplc into
# verify/Scripts/<module>_<handler>.flat for the handlers we verify
# (`spend` and `mint`). Aiken v1.1 (Plutus V3) emits one file per
# handler. Adding a new validator requires no edit here, the loops
# pick it up automatically.
flats: build
	@mkdir -p verify/Scripts
	@invalidate_lean() { \
	  flat="$$1"; \
	  for lean in $$(grep -lF "Scripts/$$flat" verify/Properties/*.lean 2>/dev/null); do \
	    mod=$$(basename "$$lean" .lean); \
	    echo "    invalidate Lake cache for Properties/$$mod (depends on $$flat)"; \
	    rm -f verify/.lake/build/lib/lean/Properties/$$mod.olean \
	          verify/.lake/build/lib/lean/Properties/$$mod.olean.hash \
	          verify/.lake/build/lib/lean/Properties/$$mod.ilean \
	          verify/.lake/build/lib/lean/Properties/$$mod.ilean.hash \
	          verify/.lake/build/lib/lean/Properties/$$mod.trace \
	          verify/.lake/build/ir/Properties/$$mod.c \
	          verify/.lake/build/ir/Properties/$$mod.c.hash \
	          verify/.lake/build/ir/Properties/$$mod.setup.json; \
	  done; \
	}; \
	encode_flat() { \
	  src="$$1"; out="$$2"; tmp="$$out.tmp"; \
	  aiken uplc encode --hex "$$src" > "$$tmp" || { rm -f "$$tmp"; exit 1; }; \
	  if [ ! -e "$$out" ] || ! cmp -s "$$out" "$$tmp"; then \
	    echo "  encode $$src -> $$out (changed)"; \
	    mv "$$tmp" "$$out"; \
	    invalidate_lean "$$(basename "$$out")"; \
	  else \
	    echo "  encode $$src -> $$out (unchanged)"; \
	    rm -f "$$tmp"; \
	  fi; \
	}; \
	for f in artifacts/*.spend.uplc; do \
	  [ -e "$$f" ] || continue; \
	  base=$$(basename "$$f" .spend.uplc); \
	  module=$${base%%.*}; \
	  encode_flat "$$f" "verify/Scripts/$${module}_spend.flat"; \
	done; \
	for f in artifacts/*.mint.uplc; do \
	  [ -e "$$f" ] || continue; \
	  base=$$(basename "$$f" .mint.uplc); \
	  module=$${base%%.*}; \
	  encode_flat "$$f" "verify/Scripts/$${module}_mint.flat"; \
	done

# Re-check every theorem reachable from Properties/Basic.lean.
verify: flats
	@bash -c 'set -o pipefail; cd verify && lake build 2>&1 | awk -f ../scripts/annotate-blaster-logs.awk'

clean:
	rm -rf artifacts build
	rm -f verify/Scripts/*.flat
	cd verify && lake clean
