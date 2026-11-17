/-
H5 FIX EDITION STEP-F3 (NEW edition, 2026-11-17, H5 lane3 cc97cb4b). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/Extraction.lean (sha256 98b8e3339abe00f347959aaeab23709ffb824bf6b1b69a0e3b8c3b1dcb33a740).
Body change relative to the base: ONLY P6, a local `(Msbar Hs Ms).IsInvertible` instance (explicit W07 `Scheme.Modules.isInvertible_pullback`) after each of the 1 `intro k _ Hs _ Ms _ hinf` lines (record step-fix3/FIX_RECORD_STEP_F3.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: E `InfiniteStabilizerExtraction`, its non-openness parts PROVED. 2026-11-17.
v2, interface v2: E3's output is the internal smoothness-free class, and GM3.lean reduces E3.
v1 578af42c is in history/.
New file. SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic.

PROVED, modulo compile:
* `stab_one`, `stab_mul`, `stab_inv`: the stabilizer `K(M) = {x | t_x^*M ≅ M}` is a subgroup of
  the point group, in the SAME transported group law and right-translation convention. The proofs
  use `transl_one`/`transl_mul` (TwistSelection.lean) and native pullback composition.
* `infiniteStabilizerExtraction (hE1 hE3) : InfiniteStabilizerExtraction`, from E1 and E3 below,
  applied to `H̄` and `M̄` (`isAbelianVariety_baseChange`).

Explicit UNPROVED inputs, each true:
* `StabilizerClosedLocus` (E1): `K(M)` is the set of rational points of a closed subset. This is
  the role of the seesaw closedness theorem for `Λ = μ^*M ⊗ pr₁^*Mᵛ` over the second factor,
  whose slice at `x` is `t_x^*M ⊗ Mᵛ`. It is the H71 `Cube.SeesawClosed` role, a Cube4 body
  pending L5; any Stacks-vs-W07 mismatch is to be recorded when that body is read.
* `InfiniteClosedSubgroupContainsAbelian` (E3 = GM3): an infinite subgroup of rational points cut
  out by a closed subset contains the points of a positive-dimensional abelian subvariety (the
  reduced identity component of its closure). This needs group-scheme theory:
  - reduced closed subgroups over an algebraically closed field;
  - smoothness of reduced group schemes over perfect fields;
  - identity components.
  No held provider is known.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.TwistSelection
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1Assembly

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

section Stabilizer

variable {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K)))) (M : A.X.left.Modules)

/-- The stabilizer of `M` under right translation by rational points. -/
def stab : Set (Pt K ⟶ A.X) :=
  {x | Nonempty ((Scheme.Modules.pullback (transl A x)).obj M ≅ M)}

theorem stab_one : (1 : Pt K ⟶ A.X) ∈ stab A M :=
  (iso'_pb_congr (transl_one A) M).trans (iso'_pb_id M)

theorem stab_mul {x y : Pt K ⟶ A.X} (hx : x ∈ stab A M) (hy : y ∈ stab A M) :
    x * y ∈ stab A M :=
  (iso'_pb_congr (transl_mul A x y).symm M).trans <|
    (iso'_pb_comp _ _ M).symm.trans <| (Iso'.pb (transl A x) hy).trans hx

theorem stab_inv {x : Pt K ⟶ A.X} (hx : x ∈ stab A M) : x⁻¹ ∈ stab A M :=
  (Iso'.pb (transl A x⁻¹) hx).symm.trans <|
    (iso'_pb_comp _ _ M).trans <|
      (iso'_pb_congr ((transl_mul A x⁻¹ x).trans (by rw [inv_mul_cancel])) M).trans <|
        (iso'_pb_congr (transl_one A) M).trans (iso'_pb_id M)

end Stabilizer

/-- E1 (UNPROVED; seesaw closedness role): the stabilizer is closed. -/
def StabilizerClosedLocus : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (M : A.X.left.Modules) [M.IsInvertible],
    ∃ Z : Set A.X.left, IsClosed Z ∧ ∀ x : Pt K ⟶ A.X,
      (Nonempty ((Scheme.Modules.pullback (transl A x)).obj M ≅ M) ↔
        x.left.base (IsLocalRing.closedPoint K) ∈ Z)

/-- E3 = GM3 (UNPROVED here; reduced in GM3.lean): an infinite closed subgroup contains a
positive-dimensional, proper, geometrically integral closed subgroup. This is the
smoothness-free, interface-v2 output. -/
def InfiniteClosedSubgroupContainsIntegral : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (Z : Set A.X.left), IsClosed Z →
    ∀ (S : Set (Pt K ⟶ A.X)), (∀ x, x ∈ S ↔ x.left.base (IsLocalRing.closedPoint K) ∈ Z) →
      (1 : Pt K ⟶ A.X) ∈ S → (∀ x y, x ∈ S → y ∈ S → x * y ∈ S) → (∀ x, x ∈ S → x⁻¹ ∈ S) →
        S.Infinite →
          ∃ (Y : Grp (Over (Spec (CommRingCat.of K)))) (_ : IsProperIntegralGroup Y)
            (j : Y.X ⟶ A.X) (_ : IsMonHom j),
            IsClosedImmersion j.left ∧ ¬ IsFinite Y.X.hom ∧ ∀ y : Pt K ⟶ Y.X, y ≫ j ∈ S

/-- E, PROVED from E1 and E3. -/
theorem infiniteStabilizerExtraction (hE1 : StabilizerClosedLocus.{u})
    (hE3 : InfiniteClosedSubgroupContainsIntegral.{u}) : InfiniteStabilizerExtraction.{u} := by
  intro k _ Hs _ Ms _ hinf
  haveI : (Msbar Hs Ms).IsInvertible :=
    Scheme.Modules.isInvertible_pullback
      (pullback.fst Hs.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) Ms
  obtain ⟨Z, hZ, hZiff⟩ := hE1 (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms)
  exact hE3 (PkgI2.baseChange Hs (AlgebraicClosure k)) Z hZ (stabilizerSet Hs Ms) hZiff
    (stab_one _ _) (fun _ _ hx hy => stab_mul _ _ hx hy) (fun _ hx => stab_inv _ _ hx) hinf

end ZInQ.Contrib.CloudR2NOS.Step1
