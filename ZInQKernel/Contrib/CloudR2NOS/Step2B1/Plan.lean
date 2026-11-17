/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B1/Plan.lean (sha256 205980f8b6a633c6a65ccec82ef39faace6bc93bed1570d836867e34d7f4e26d).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B1 `FiniteSupportStabilizer` (Step2DelegatedInterfaces 4d5c8dce):
DECOMPOSITION into exact native sub-obligations, with truth sketches. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

Assembly plan. `S :=` the support stabilizer and `H(D) :=` the divisor stabilizer (finite by
hypothesis).
(B1.a) `S` is a subgroup of the rational-point group. This uses `support_comap`
  (`supp(D.comap φ) = φ⁻¹ supp D`) and `t_{xy} = t_x ≫ t_y`.
(B1.b) `S` acts on the FINITE set of irreducible components of `supp D` (Noetherian), since
  `t_x` is a homeomorphism preserving `supp D`.
(B1.c) KEY, the multiplicity step: a rational point whose translation fixes EVERY component of
  `supp D` lies in `H(D)`.
(B1.d) Finite index (pure group theory): `x ↦ (C ↦ t_x⁻¹ C)` lands in the finite set
  `Comp → Comp`. Points with the same image differ by an element of the kernel `S₀`, and
  `S₀ ⊆ H(D)` is finite, so `S` is a finite union of finite cosets.

TRUTH SKETCHES:
* (B1.a), (B1.b), (B1.d): TRUE and elementary.
* (B1.c) TRUE. `A` is regular (smooth over a field), hence normal Noetherian integral. An
  invertible ideal on such a scheme is determined by its localizations at the codimension-1
  points: for local principal `(g)`, `f ∈ (g)` iff `v_η(f) ≥ v_η(g)` for every height-one `η`.
  This is the Krull-domain property; equivalently, factor in the UFD stalks via C5's A1/A2.
  - If `t_x` fixes each component `C` of `supp D`, it fixes each generic point `η_C`, and
    `t_x^♯` is an automorphism of the DVR `O_{A,η_C}`. So `v_{η_C}(t_x^*D) = v_{η_C}(D)`.
  - At codimension-1 points off `supp D`, both localizations are the unit ideal.
  - Hence `t_x^*D = D`.
  The examples `(t)` vs `(t²)` show support alone does not determine `D`, which is why
  multiplicities are used.
-/
import Step2DelegatedInterfaces

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

/-- (B1.c) KEY (TRUE; multiplicities at codimension-1 points). A translation that fixes every
irreducible component of the support of an invertible ideal preserves the ideal. -/
def ComponentFixingPreservesDivisor : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
      (∀ C : Set A.X.left, C ⊆ (D.support : Set A.X.left) →
        Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) C →
        (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x) ⁻¹' C = C) →
      D.comap (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x) = D

end ZInQ.Contrib.CloudR2NOS.Step2B1
