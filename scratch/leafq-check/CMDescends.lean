import TailK

/-!
# leafq-check: `CMDescends` (LEAF?) — verbatim copy over leaf-fold4's chain

The Prop `HDec.HSyn.G0Split.FibreQM.PeriodMapH.CMDescends` is copied verbatim (docstring and body) from `scratch/leaf-fold4/Leaves4.lean`
(def at line 114469), inside the sub-namespace `HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheckCopy` with the `open`s in force at its
location; what it depends on is imported from leaf-fold4's olean chain (`import TailK`, the same
constants as the flat file). `copy_iff` checks that the copy is the chain's Prop. Verdict, published
statement and decomposition: docs/research/leafq-check.md §2.3. Check: `scratch/leafq-check/chk.sh scratch/leafq-check/CMDescends.lean`.
-/

namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH

open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

namespace LeafQCheckCopy

/-- **LEAF candidate (QM abelian surfaces with CM are defined over `ℚ̄`).** A level-3 QM surface
`Q/ℂ` with CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) is, as a QM pair, isomorphic to the base change
along some `ι : ℚ̄ → ℂ` of a level-3 QM surface `P/ℚ̄` with the same CM.

Sources: Shimura–Taniyama, *Complex multiplication of abelian varieties* (1961), and Shimura 1967:
abelian varieties with CM are defined over `ℚ̄` (a CM point of `X₆` is algebraic; its fibre has a
model over the field of moduli); the CM descends because endomorphisms of `P_ℂ` come from `P`
(the kernel's textbook leaf T11b, `Hom_ℚ̄ = Hom_ℂ`); the level structure also descends because
`A[3] ⊆ A(ℚ̄)` (locators UNVERIFIED). A consequence of those published statements; size of the glue
around them: small-medium. -/
def CMDescends : Prop :=
  ∀ Q : QML3 ℂ,
    (HasCM4 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM4 P.q ∧ Nonempty (QMIso Q.q Q'.q)) ∧
    (HasCM3 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM3 P.q ∧ Nonempty (QMIso Q.q Q'.q)) ∧
    (HasCM24 Q.q → ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ HasCM24 P.q ∧ Nonempty (QMIso Q.q Q'.q))

end LeafQCheckCopy

theorem LeafQCheckCopy.copy_iff : LeafQCheckCopy.CMDescends ↔ CMDescends := Iff.rfl

end HDec.HSyn.G0Split.FibreQM.PeriodMapH
