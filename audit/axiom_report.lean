/-
Kernel axiom report generator (math-commons/formalization-assurance, ADOPTION.md §3).
`lake env lean audit/axiom_report.lean` emits the #print axioms traces; the assurance
gate diffs them against the committed golden `audit/axiom-report.txt`. Each headline is
expected to depend only on the standard three (propext, Classical.choice, Quot.sound).
-/
import HilleYosida.StronglyContinuousSemigroup
import HilleYosida.Bernstein
import HilleYosida.SemigroupGroupExtension
import HilleYosida.BCR_Uniqueness

#print axioms hilleYosidaResolventBound
#print axioms ContractingSemigroup.resolventRightInv
#print axioms bernstein_theorem
#print axioms semigroupGroupBochner
#print axioms laplaceFourier_unique
