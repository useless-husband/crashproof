import Crashproof

/-! Prints the axioms every main theorem depends on. `scripts/check-proofs.sh` fails unless
they are among Lean's three standard axioms: `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Crashproof.Theorems.atomicity
#print axioms Crashproof.Theorems.durability
#print axioms Crashproof.Theorems.recovery_idempotent
#print axioms Crashproof.Theorems.crash_while_idle
#print axioms Crashproof.Theorems.get_correct
#print axioms Crashproof.Theorems.put_correct
#print axioms Crashproof.Theorems.put?_ok
#print axioms Crashproof.Theorems.commitAll_spec
#print axioms Crashproof.commit_spec
#print axioms Crashproof.recover_spec
