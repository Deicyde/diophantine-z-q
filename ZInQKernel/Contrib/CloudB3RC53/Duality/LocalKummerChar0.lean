import ZInQKernel.Contrib.CloudB3RC53.Duality.LocalKummer

/-!
# Duality area: the local Kummer annihilator in Milne's scope (characteristic zero)

`MilneLocalTateDualityKummer` (`LocalKummer.lean`) is stated for every nonarchimedean local field
`F` with `m` invertible in `F`. Milne, *Arithmetic Duality Theorems*, I.3.2–I.3.5, is stated for
`p`-adic fields (finite extensions of `ℚ_p`), and the manuscript only uses `F = K_v` for a number
field `K`. This file states the print in that scope, with `[CharZero F]` in the type:

* `MilneLocalTateDualityKummerCharZero` (PRINT; locators checked against the ADT PDF (I.2.3 p. 28;
  I.3.2 p. 41, diagram pp. 41–43; I.3.4 p. 43; I.3.5 p. 44); Milne I.3.2–I.3.5, as cited at tex
  L3439–3441): for every nonarchimedean local field `F` of characteristic zero (a finite extension
  of some `ℚ_p`), every elliptic curve `B/F` and every `m` invertible in `F`, the data of
  `MilneLocalTateDualityKummer B m hm` exist;
* `KummerAnnihilatorNodeCharZero`: Lemma `ex:arith-local-kummer` (tex L3423) in that scope;
* `kummerAnnihilatorNodeCharZero_of_print` (PROVED): the lemma from the print, through
  `kummerAnnihilatorNode_proof`.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

/-- **PRINT** (locators checked against the ADT PDF (I.2.3 p. 28; I.3.2 p. 41, diagram pp. 41–43;
I.3.4 p. 43; I.3.5 p. 44); Milne, *Arithmetic Duality Theorems*, I.3.2–I.3.5, as cited at tex
L3439–3441), in Milne's scope: for a nonarchimedean local field `F` of characteristic zero, an
elliptic curve `B` over `F` and `m` invertible in `F`, Tate's local pairing
`B(F) × H¹(F, B) → ℚ/ℤ` is nondegenerate on `H¹(F, B)[m]` and the Kummer map is adjoint to
`H¹(F, B[m]) → H¹(F, B)` for it and `localTatePairing` (`MilneLocalTateDualityKummer`). -/
def MilneLocalTateDualityKummerCharZero : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ)
    (hm : IsUnit (m : F)), MilneLocalTateDualityKummer B m hm

/-- **The Kummer image is its exact local annihilator, in characteristic zero** (Lemma
`ex:arith-local-kummer`, tex L3423, L3439–3443, for `F = K_v`). -/
def KummerAnnihilatorNodeCharZero : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ)
    (hm : IsUnit (m : F)),
    ∀ y : H1 (AbsoluteGaloisGroup F) (B.TorsionCoeff m),
      y ∈ (B.kummerMap m hm).range ↔
        ∀ x ∈ (B.kummerMap m hm).range, localTatePairing B m hm x y = 0

/-- **The lemma from the print in Milne's scope** (PROVED). -/
theorem kummerAnnihilatorNodeCharZero_of_print (hM : MilneLocalTateDualityKummerCharZero) :
    KummerAnnihilatorNodeCharZero := by
  intro F _ _ _ _ _ _ B _ m hm
  exact kummerAnnihilatorNode_proof F B m hm (hM F B m hm)

end ZInQ.Contrib.CloudB3RC53.Duality
