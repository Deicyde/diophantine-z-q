import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Central.Coordinate
import ZInQKernel.Contrib.OneProof.RC.Central.Smith

/-!
# Lane RC15 (central): Lemma `ex:arith-base-zero`, the DVR core

The 11/5 manuscript (`diophantine_zq.tex`, lines 4319–4373; V19 lines 20410–20460):

> Use the base `h₀ = 1` […] with `L(E^{(k)},1) ≠ 0` and full two-primary Selmer corank one for `E/K`.
> If `L'(E/K,1) = 0`, then `u_{prim,0}(0) = ũ₀(0) = 0` […]. The primitive coordinate is regular
> at `(t)` […], and its corrected relaxed coordinate has the same property.

This file proves, over an arbitrary DVR `A` (the manuscript's `A = Λ_{(t)}`, residue field `ℚ₂`),
the part of the proof after "the specialization of the actual cycle `z` [is] zero": the two
generic possibilities, regularity at `(t)` and vanishing at the centre, for the primitive
coordinate and for the corrected coordinate `ũ₀ = ε₀ u_{prim,0}` with `ε₀` a unit.

**Form (DEPARTURE, recorded in the report).** The primitive complex is represented by its two-term
model `[A^{m+1} --D--> A^{m+1}]` in degrees one and two: the actual bounded finite free complex after
cancelling its unit disks outside degrees one and two, which Nakayama's lemma permits because the
central cohomology vanishes there (V19 tex 20064–20067; GLUE, textbook minimal-complex reduction
over a local ring; the cancellation multiplies the coordinate by a unit, absorbed into `ε₀`). The
dichotomy for an arbitrary bounded complex is `bounded_complex_dichotomy` (`Smith.lean`); on the
model it is `twoTerm_dichotomy` below.

Every declaration in this file is `PROVED`.

* `twoTerm_dichotomy` (tex 4350–4358): with central dimensions `(1,1)` (`rank D̄ = m`), the
  generic complex is acyclic (`det D` a unit of `F`) or has dimensions `(1,1)` with
  `rank_F D = rank_k D̄` (no disk with `r > 0`).
* `baseZero_core` (tex 4359–4373): if moreover the central cycle vanishes, `z̄ = 0`, then the
  generic coordinate `u_{prim,0}` is regular, `u_{prim,0} = ι u₀`, with `ρ u₀ = 0`, and the
  corrected coordinate `ũ₀ = ι(ε₀) u_{prim,0}` is regular with value `0` at the centre.
* `simpleZero_specialization` (V19 tex 20063–20079): at a known simple zero the generic coordinate
  is regular and specializes to the central tensor (the V19 justification behind (4.6)).
* `kummer_eq_zero_of_isOfFinAddOrder` (tex 4337–4338): a torsion point has zero rational Kummer
  class (any additive map into a `ℚ₂`-vector space kills torsion).
-/

namespace ZInQ.Manuscript.RC.Central

open Matrix

/-- Over a field, a square matrix of full rank is invertible. PROVED. -/
theorem isUnit_det_of_rank_eq {𝕜 : Type*} [Field 𝕜] {n : ℕ} (D : Matrix (Fin n) (Fin n) 𝕜)
    (hr : D.rank = n) : IsUnit D.det := by
  have hsurj : Function.Surjective D.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank 𝕜 (LinearMap.range D.mulVecLin) = D.rank from rfl, hr]
    simp
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) 𝕜, D * B = 1 := by
    choose f hf using hsurj
    refine ⟨Matrix.of fun i j => f (Pi.single j 1) i, ?_⟩
    ext i j
    have := congrFun (hf (Pi.single j 1)) i
    rw [mulVecLin_apply] at this
    rw [mul_apply, one_apply]
    simp only [mulVec, dotProduct, of_apply] at this ⊢
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have := congrArg det hB
  rw [det_mul, det_one] at this
  exact isUnit_iff_exists_inv.mpr ⟨_, this⟩

variable {A F : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F] {k : Type*} [Field k]

/-- **The two generic possibilities on the two-term model** (tex 4350–4358): if the central
dimensions are `(1,1)` (`rank_k D̄ = m` for `D̄ = D mod 𝔪`), then either the generic complex is
acyclic (`det D` is a unit of `F`), or `rank_F D = m = rank_k D̄`: generic dimensions `(1,1)` and no
disk `[A --t^r--> A]` with `r > 0`. PROVED (semicontinuity `rank_map_residue_le`). -/
theorem twoTerm_dichotomy (ρ : A →+* k) {m : ℕ} (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hcentral : (D.map ρ).rank = m) :
    IsUnit (D.map (algebraMap A F)).det ∨
      ((D.map (algebraMap A F)).rank = m ∧ (D.map (algebraMap A F)).det = 0) := by
  have hsemi := rank_map_residue_le (F := F) ρ D
  have hle : (D.map (algebraMap A F)).rank ≤ m + 1 := by
    simpa using rank_le_card_width (D.map (algebraMap A F))
  rcases Nat.lt_or_ge (D.map (algebraMap A F)).rank (m + 1) with hlt | hge
  · right
    refine ⟨by omega, ?_⟩
    by_contra hdet
    have hunit : IsUnit (D.map (algebraMap A F)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have := rank_of_isUnit _ hunit
    simp only [Fintype.card_fin] at this
    omega
  · left
    exact isUnit_det_of_rank_eq _ (by omega)

/-- **Lemma `ex:arith-base-zero`, the DVR core** (tex 4330–4373). Let `A` be a DVR with fraction
field `F` (`ι = algebraMap A F`) and a residue map `ρ` to a field killing the maximal ideal.
Let `[A^{m+1} --D--> A^{m+1}]` be the two-term model of the primitive complex at the base, with
central dimensions `(1,1)` (`hcentral`, from full Selmer corank one: tex 4346–4348), an integral
cycle `z` and an integral closed functional `λ` (`w`; integral by the paired-functional
proposition, tex 4334–4336), and let `uprim` be the generic class-functional coordinate. If the
central cycle vanishes (`hz0`, tex 4336–4340), then `uprim` is regular at the centre and zero
there; and for the `Λ`-unit `ε₀` of (4.7) at the base (tex 4365–4368; only `ε₀ ∈ A` is used here)
the corrected coordinate `ũ₀ = ι(ε₀) uprim` is regular and zero at the centre. The two cases are those of the text:
acyclic (coordinate `0` by definition) and `(1,1)` (no positive disk, integral base change).
PROVED. -/
theorem baseZero_core (ρ : A →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (D.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : D *ᵥ z = 0) (uprim : F)
    (hu : IsClassFunctionalCoord (D.map (algebraMap A F)) (fun i => algebraMap A F (z i))
      (fun i => algebraMap A F (w i)) uprim)
    (hz0 : ∀ i, ρ (z i) = 0) (ε₀ : A) :
    (∃ u₀ : A, algebraMap A F u₀ = uprim ∧ ρ u₀ = 0) ∧
      (∃ a : A, algebraMap A F a = algebraMap A F ε₀ * uprim ∧ ρ a = 0) := by
  have hι := IsFractionRing.injective A F
  have hprim : ∃ u₀ : A, algebraMap A F u₀ = uprim ∧ ρ u₀ = 0 := by
    rcases twoTerm_dichotomy (F := F) ρ D hcentral with hacyc | ⟨_, _⟩
    · -- the generic complex is acyclic: the coordinate is zero by definition
      have hzF : (D.map (algebraMap A F)) *ᵥ (fun i => algebraMap A F (z i)) = 0 := by
        ext i
        have := congrFun hz i
        simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at this ⊢
        rw [← map_zero (algebraMap A F), ← this, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
      have h0 := isClassFunctionalCoord_zero_of_isUnit_det (w := fun i => algebraMap A F (w i))
        hacyc hzF
      have hadj : (D.map (algebraMap A F)).adjugate ≠ 0 := by
        intro hadj0
        have := mul_adjugate (D.map (algebraMap A F))
        rw [hadj0, mul_zero] at this
        have h1 := congrFun (congrFun this 0) 0
        simp only [Matrix.zero_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
          at h1
        exact hacyc.ne_zero h1.symm
      have := isClassFunctionalCoord_unique hadj hu h0
      exact ⟨0, by rw [map_zero, this], map_zero ρ⟩
    · -- generic dimensions `(1,1)` and no positive disk: integral determinant base change
      have hadj : (D.map ρ).adjugate ≠ 0 := adjugate_ne_zero_of_rank _ hcentral
      obtain ⟨u₀, hu₀, hcoord⟩ := coord_specializes (algebraMap A F) hι ρ hρ D z w uprim hu hadj
      exact ⟨u₀, hu₀, coord_central_eq_zero hcoord hadj (funext hz0)⟩
  obtain ⟨u₀, hu₀, hρu₀⟩ := hprim
  refine ⟨⟨u₀, hu₀, hρu₀⟩, ⟨ε₀ * u₀, by rw [map_mul, hu₀], by rw [map_mul, hρu₀, mul_zero]⟩⟩

/-- **The generic coordinate specializes at a known simple zero** (V19, proof of
`ex:arith-central-calibration`, tex 20063–20079; ELLIOT gap of the 11/5 text filled from V19, which
also makes "regular" part of the statement of (4.6)). On the two-term model with central
dimensions `(1,1)`, if the retained cycle has nonzero central class (`z̄ ≠ 0`, from (4.5) and the
height formula at the known simple zero), the generic kernel is nonzero, so the generic complex is
not acyclic (`det D = 0` over `F`: generic dimensions `(1,1)`), and the generic coordinate is
regular and specializes to the coordinate of the central tensor `z̄ ⊗ λ̄` computed by Lemma
`ex:arith-central-specialization`. PROVED. -/
theorem simpleZero_specialization (ρ : A →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    {m : ℕ} (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (D.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : D *ᵥ z = 0) (hz0 : ∃ i, ρ (z i) ≠ 0) (uprim : F)
    (hu : IsClassFunctionalCoord (D.map (algebraMap A F)) (fun i => algebraMap A F (z i))
      (fun i => algebraMap A F (w i)) uprim) :
    (D.map (algebraMap A F)).det = 0 ∧
      ∃ u₀ : A, algebraMap A F u₀ = uprim ∧
        IsClassFunctionalCoord (D.map ρ) (fun i => ρ (z i)) (fun i => ρ (w i)) (ρ u₀) := by
  have hι := IsFractionRing.injective A F
  have hzF : (D.map (algebraMap A F)) *ᵥ (fun i => algebraMap A F (z i)) = 0 := by
    ext i
    have := congrFun hz i
    simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at this ⊢
    rw [← map_zero (algebraMap A F), ← this, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
  have hne : (fun i => algebraMap A F (z i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz0
    intro h0
    have : z i = 0 := hι (by rw [map_zero]; exact congrFun h0 i)
    exact hi (by rw [this, map_zero])
  refine ⟨Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hzF⟩, ?_⟩
  exact coord_specializes (algebraMap A F) hι ρ hρ D z w uprim hu
    (adjugate_ne_zero_of_rank _ hcentral)

/-- **A torsion point has zero rational Kummer class** (tex 4337–4338: "Thus its rational Kummer
class vanishes"): an additive map from the point group into a `ℚ₂`-vector space (here any
`ℚ`-vector space) kills every point of finite order. PROVED. -/
theorem kummer_eq_zero_of_isOfFinAddOrder {G V : Type*} [AddCommGroup G] [AddCommGroup V]
    [Module ℚ V] (κ : G →+ V) {P : G} (hP : IsOfFinAddOrder P) : κ P = 0 := by
  obtain ⟨n, hn, hnP⟩ := hP.exists_nsmul_eq_zero
  have h : n • κ P = 0 := by rw [← map_nsmul, hnP, map_zero]
  have hq : ((n : ℚ) • κ P) = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h
  exact (smul_eq_zero.mp hq).resolve_left (by exact_mod_cast hn.ne')

end ZInQ.Manuscript.RC.Central
