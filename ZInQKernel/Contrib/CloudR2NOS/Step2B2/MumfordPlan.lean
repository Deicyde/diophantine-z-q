/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B2/MumfordPlan.lean (sha256 e6f7d3659c004d1b9b87fa87a5dec13246fa1b2b2e3fbeca4755907ab826c281).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B2.d `MumfordContractedCombinatorics` (Plan.lean 09cbbfbe): REFINED
decomposition (d.1)–(d.3). 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED; it states Props only.
Universe u.

Notation: additive, since `A` is commutative (Mathlib
`isCommMonObj_of_isProper_of_geometricallyIntegral`). `Z := supp D` with components `D_k`
(finitely many). `Q := ⋂_{c ∈ C(K)} t_c⁻¹ Z`, which is closed, and `-Q := ι⁻¹ Q`.

(d.3) case assembly (lane3, in progress):
* For `d ∈ D_k(K)` and `c ∈ C(K)`: `c + (d - c) = d ∈ Z`, so `C` meets `W_{d-c}`. By H, `C ⊆ W_{d-c}`,
  and since `C` is irreducible, `d - c ∈ Q` or `-(d - c) ∈ Q`.
* By (d.1) the closure of `D_k(K) - C(K)` is irreducible, and it lies in `Q ∪ -Q`. So
  case `A_k` (all in `Q`) or case `B_k` (all in `-Q`).
* `A_k`: `D_k + (c' - c) ⊆ Z` (Jacobson closure). Each translate is irreducible, so it lies in a
  component. Apply (d.2) with `φ = t_{-(c'-c)}`, then the component trick (`C` irreducible; the
  component is constant in `c'`, and `c' = c` gives `D_k`). Hence `D_k + (c' - c) = D_k`.
* `B_k`: `(c + c') - D_k ⊆ Z`. By the component trick in `c` and in `c'`, it lies in one component
  `D_m`. Apply (d.2) with the involution `φ(a) = (c + c') - a`, so `(c + c') - D_k = D_m` for all
  `c, c'`. Comparing `c` with `c₁` gives `D_k + (c - c₁) = D_k`.
* Hence every component is fixed by `C(K) - c₀`, so `Z + (c - c₀) = Z`, and the support
  stabilizer contains the infinite set `C(K) - c₀`.
(d.2) PurityTranslateEquality: C5, frozen in PurityInterface.lean 51b21aaf.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.PurityInterface

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

/-- (d.1), TRUE. The closure of the rational-point Minkowski difference of two irreducible closed
sets is irreducible. It is the closure of the image of the irreducible `E_red ×_K F_red` (C5
`GeomIrreducibleOverAlgClosed` and Mathlib products) under `(e, f) ↦ e - f`, whose rational points
are dense (Jacobson). -/
def MinkowskiIrreducible : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A] (E F : Set A.X.left),
    IsClosed E → IsIrreducible E → IsClosed F → IsIrreducible F →
      IsIrreducible (closure {a : A.X.left | ∃ e f : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
        e.left (IsLocalRing.closedPoint K) ∈ E ∧ f.left (IsLocalRing.closedPoint K) ∈ F ∧
          a = (e * f⁻¹).left (IsLocalRing.closedPoint K)})

end ZInQ.Contrib.CloudR2NOS.Step2B2
