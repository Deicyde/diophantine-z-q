import ZInQKernel.Contrib.OneProof.RC.Skeleton.Skeleton
import ZInQKernel.Contrib.OneProof.RC.Boolean.Node
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic

/-!
# Theorem 5.3 from Elliot's steps, with the missing-address argument proved

`restrictedConverseGenuine_of_steps'` is `RC.restrictedConverseGenuine_of_steps` (lane RC0: Elliot's deduction of
Theorem 5.3, both branches, over the shared top layer `ZInQ.Contrib.CloudB3RC53`) with the missing-address node
discharged by `RC.Boolean.missingAddressNode` (lane RC1, tex 5665–5727). What remains as hypotheses: the printed
leaves `Prints` (BCDT Theorem A, Dokchitser–Dokchitser Theorem 1.8, Cai–Shu–Tian Theorem 1.1)
with Kolyvagin Theorem 1 (also in `Prints`; a cited statement, GLUE),
the Kummer-sequence statement `KummerCorankZero`, and, for each admissible `ℓ` with
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` (the hypothesis under which the text proves them), Elliot's thirteen
steps `RCSteps (D ℓ)` (each named after the manuscript, with its tex lines, in `RC/Skeleton/Steps.lean`).
-/

namespace ZInQ.Manuscript.RC

open ZInQ.Contrib.CloudB3RC53

/-- **Theorem 5.3** (`diophantine_zq.tex` lines 1005–1011, proved in Sections 7–9 and Appendices E–G) from the printed
leaves, the Kummer sequence in rank zero and Elliot's steps; the missing-address argument (tex 5665–5727) is proved. -/
theorem restrictedConverseGenuine_of_steps' (P : Prints) (hKum : KummerCorankZero)
    (D : ∀ ℓ : ℕ, RCData ℓ)
    (hS : ∀ ℓ : ℕ, Adm ℓ → ZInQ.Manuscript.SelmerTwoPower.SelmerCorankOne (Ecurve ℓ) → RCSteps (D ℓ)) :
    ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_steps P hKum D hS ZInQ.Manuscript.RC.Boolean.missingAddressNode

/-- **Theorem 5.3 from the printed leaves and Elliot's steps alone**: `restrictedConverseGenuine_of_steps'` with the
Kummer sequence in rank zero proved (`CloudB3RC53.KummerCorankZero.kummerCorankZero_proof`). -/
theorem restrictedConverseGenuine_of_prints_steps (P : Prints)
    (D : ∀ ℓ : ℕ, RCData ℓ)
    (hS : ∀ ℓ : ℕ, Adm ℓ → ZInQ.Manuscript.SelmerTwoPower.SelmerCorankOne (Ecurve ℓ) → RCSteps (D ℓ)) :
    ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_steps' P
    ZInQ.Contrib.CloudB3RC53.KummerCorankZero.kummerCorankZero_proof D hS

end ZInQ.Manuscript.RC
