/-
Axiom audit entrypoint. Lists `#print axioms` for every headline theorem that
this repo hosts as a `formal_proof` target. `scripts/check_axioms.sh` builds
this file and fails CI if any line reports `sorryAx` or an axiom outside the
allowed set `[propext, Classical.choice, Quot.sound]`.

When you add a proof, add its module import and a `#print axioms` line here and
a matching entry in `proofs.yaml`.
-/
import ErdosProblems.Erdos154Sumset

#print axioms Erdos154.erdos_154_sumset
