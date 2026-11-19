import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG
import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeCoord

/-!
# Retained comparison, including zero coordinates

Manuscript ex:arith-coordinate, TeX 3877–3892, and
ex:limits-fixed-field-clearing, TeX 5509–5516 and 5605–5617.

A retained comparison is allowed at a zero coordinate: it is the cone of the
comparison map that must be exact, not the augmented source or target.
The results below extend the existing cone-coordinate comparison to this case.
For a two-term complex with nonzero adjugate, the adjugate coordinate agrees
with the Knudsen–Mumford coordinate even when the class or functional vanishes.

The final constructors are conditional on an actual retained model of the
relaxed coordinate.  That model, with its same class, functional, scalar, and
basis, is a provenance obligation, not a printed proposition.  None of these
results requires a power-series-unit correction or adds a printed leaf.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordLink

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Wiring (UTildeRep OrigCoordLink)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

section Cone

variable {k : Type*} [Field k]
  {ιe ιo ιe' ιo' : Type*}
  [Fintype ιe] [Fintype ιo] [Fintype ιe'] [Fintype ιo']
  [DecidableEq ιe] [DecidableEq ιo] [DecidableEq ιe'] [DecidableEq ιo']
  {C : BasedCx k ιe ιo} {D : BasedCx k ιe' ιo'}

/-- Over a field, nonzero torsion is equivalent to the existence of a contraction. -/
theorem torsion_ne_zero_iff_contraction (C : BasedCx k ιe ιo) (σ : ιe ≃ ιo) :
    torsion C σ ≠ 0 ↔ Nonempty (Contraction C) := by
  constructor
  · intro h
    by_contra hn
    exact h (by simp [torsion, hn])
  · rintro ⟨h⟩
    rw [← tau_eq_torsion C h σ]
    exact (isUnit_tau C h σ).ne_zero

omit [DecidableEq ιe] [DecidableEq ιo] [DecidableEq ιe'] [DecidableEq ιo'] in
/-- Exactness of a comparison cone reflects exactness from target to source.
The proof is the cycle-and-boundary calculation for the two parity components. -/
theorem exact_source_of_exact_cone (f : ChainMapB C D)
    (hcone : (BasedCx.cone f).IsExact) (hD : D.IsExact) : C.IsExact := by
  constructor
  · intro x hx
    have hfx : D.dOE *ᵥ (f.fE *ᵥ x) = 0 := by
      rw [mulVec_mulVec, f.commOE, ← mulVec_mulVec, hx, mulVec_zero]
    obtain ⟨y, hy⟩ := hD.1 _ hfx
    have hcy : (BasedCx.cone f).dEO *ᵥ (Sum.elim y (-x)) = 0 := by
      change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ (Sum.elim y (-x)) = 0
      rw [fromBlocks_mulVec, zero_mulVec, zero_add]
      funext i
      rcases i with i | i
      · change (D.dEO *ᵥ y + f.fE *ᵥ (-x)) i = 0
        rw [mulVec_neg, hy, add_neg_cancel]
        rfl
      · change ((-C.dOE) *ᵥ (-x)) i = 0
        rw [neg_mulVec, mulVec_neg, hx]
        simp
    obtain ⟨v, hv⟩ := hcone.2 _ hcy
    change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ v = Sum.elim y (-x) at hv
    rw [fromBlocks_mulVec, zero_mulVec, zero_add, neg_mulVec] at hv
    have h := congrArg (fun w => w ∘ Sum.inr) hv
    exact ⟨v ∘ Sum.inr, neg_injective h⟩
  · intro y hy
    have hfy : D.dEO *ᵥ (f.fO *ᵥ y) = 0 := by
      rw [mulVec_mulVec, f.commEO, ← mulVec_mulVec, hy, mulVec_zero]
    obtain ⟨x, hx⟩ := hD.2 _ hfy
    have hcx : (BasedCx.cone f).dOE *ᵥ (Sum.elim x (-y)) = 0 := by
      change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ (Sum.elim x (-y)) = 0
      rw [fromBlocks_mulVec, zero_mulVec, zero_add]
      funext i
      rcases i with i | i
      · change (D.dOE *ᵥ x + f.fO *ᵥ (-y)) i = 0
        rw [mulVec_neg, hx, add_neg_cancel]
        rfl
      · change ((-C.dEO) *ᵥ (-y)) i = 0
        rw [neg_mulVec, mulVec_neg, hy]
        simp
    obtain ⟨v, hv⟩ := hcone.1 _ hcx
    change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ v = Sum.elim x (-y) at hv
    rw [fromBlocks_mulVec, zero_mulVec, zero_add, neg_mulVec] at hv
    have h := congrArg (fun w => w ∘ Sum.inr) hv
    exact ⟨v ∘ Sum.inr, neg_injective h⟩

omit [DecidableEq ιe] [DecidableEq ιo] [DecidableEq ιe'] [DecidableEq ιo'] in
/-- Exactness of a comparison cone also transports exactness from source to target. -/
theorem exact_target_of_exact_cone (f : ChainMapB C D)
    (hcone : (BasedCx.cone f).IsExact) (hC : C.IsExact) : D.IsExact := by
  constructor
  · intro x hx
    have hcx : (BasedCx.cone f).dOE *ᵥ (Sum.elim x 0) = 0 := by
      change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ (Sum.elim x 0) = 0
      rw [fromBlocks_mulVec, zero_mulVec, zero_add]
      funext i
      rcases i with i | i
      · change (D.dOE *ᵥ x + f.fO *ᵥ 0) i = 0
        rw [hx, mulVec_zero, add_zero]
        rfl
      · simp
    obtain ⟨v, hv⟩ := hcone.1 _ hcx
    change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ v = Sum.elim x 0 at hv
    rw [fromBlocks_mulVec, zero_mulVec, zero_add, neg_mulVec] at hv
    have hvR : C.dOE *ᵥ (v ∘ Sum.inr) = 0 := by
      have h := congrArg (fun w => w ∘ Sum.inr) hv
      exact neg_eq_zero.mp h
    obtain ⟨s, hs⟩ := hC.1 _ hvR
    refine ⟨(v ∘ Sum.inl) + f.fO *ᵥ s, ?_⟩
    rw [mulVec_add, mulVec_mulVec, f.commEO, ← mulVec_mulVec, hs]
    exact congrArg (fun w => w ∘ Sum.inl) hv
  · intro y hy
    have hcy : (BasedCx.cone f).dEO *ᵥ (Sum.elim y 0) = 0 := by
      change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ (Sum.elim y 0) = 0
      rw [fromBlocks_mulVec, zero_mulVec, zero_add]
      funext i
      rcases i with i | i
      · change (D.dEO *ᵥ y + f.fE *ᵥ 0) i = 0
        rw [hy, mulVec_zero, add_zero]
        rfl
      · simp
    obtain ⟨v, hv⟩ := hcone.2 _ hcy
    change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ v = Sum.elim y 0 at hv
    rw [fromBlocks_mulVec, zero_mulVec, zero_add, neg_mulVec] at hv
    have hvR : C.dEO *ᵥ (v ∘ Sum.inr) = 0 := by
      have h := congrArg (fun w => w ∘ Sum.inr) hv
      exact neg_eq_zero.mp h
    obtain ⟨s, hs⟩ := hC.2 _ hvR
    refine ⟨(v ∘ Sum.inl) + f.fE *ᵥ s, ?_⟩
    rw [mulVec_add, mulVec_mulVec, f.commOE, ← mulVec_mulVec, hs]
    exact congrArg (fun w => w ∘ Sum.inl) hv

omit [DecidableEq ιe] [DecidableEq ιo] [DecidableEq ιe'] [DecidableEq ιo'] in
/-- An exact comparison cone makes source and target exactness equivalent. -/
theorem exact_iff_of_exact_cone (f : ChainMapB C D)
    (hcone : (BasedCx.cone f).IsExact) : C.IsExact ↔ D.IsExact :=
  ⟨exact_target_of_exact_cone f hcone, exact_source_of_exact_cone f hcone⟩

end Cone

section FourMap

variable {k : Type*} [Field k]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']
  {C : FourCx k ι0 ι1 ι2 ι3} {D : FourCx k ι0' ι1' ι2' ι3'}

/-- The cone-coordinate formula, with no exactness premise on the augmented
complexes.  If they are not exact, both coordinates vanish. -/
theorem kmCoord_eq_of_fourMap_total (F : FourMap C D)
    (zC : ι1 → k) (lC : ι2 → k) (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (zD : ι1' → k) (lD : ι2' → k) (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (hz : F.f1 *ᵥ zC = zD) (hl : lD ᵥ* F.f2 = lC)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (F.augMap zC lC hzC hlC zD lD hzD hlD hz hl))
      (σD.sumCongr σC.symm) ≠ 0) :
    kmCoord C zC lC hzC hlC σC =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
        (torsion (BasedCx.cone (F.augMap zC lC hzC hlC zD lD hzD hlD hz hl))
          (σD.sumCongr σC.symm))⁻¹ := by
  obtain ⟨hc⟩ := (torsion_ne_zero_iff_contraction _ _).mp hcone
  have he := exact_iff_of_exact_cone (F.augMap zC lC hzC hlC zD lD hzD hlD hz hl)
    (BasedCx.isExact_of_contraction _ hc)
  by_cases hC : (C.aug zC lC hzC hlC).toBased.IsExact
  · obtain ⟨cC⟩ := exists_contraction _ hC
    obtain ⟨cD⟩ := exists_contraction _ (he.mp hC)
    exact kmCoord_eq_of_fourMap F zC lC hzC hlC zD lD hzD hlD hz hl cC cD σC σD
  · have hD : ¬ (D.aug zD lD hzD hlD).toBased.IsExact := fun h => hC (he.mpr h)
    have hnC : ¬ Nonempty (Contraction (C.aug zC lC hzC hlC).toBased) :=
      fun h => hC (BasedCx.isExact_of_contraction _ h.some)
    have hnD : ¬ Nonempty (Contraction (D.aug zD lD hzD hlD).toBased) :=
      fun h => hD (BasedCx.isExact_of_contraction _ h.some)
    simp only [kmCoord, torsion, hnC, hnD, dite_false, neg_zero, mul_zero, zero_mul]

/-- A retained cone basis identifies the coordinates at every constituent,
including degenerate and generically acyclic constituents. -/
theorem kmCoord_eq_of_fourMap_retained_total (F : FourMap C D)
    (zC : ι1 → k) (lC : ι2 → k) (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (zD : ι1' → k) (lD : ι2' → k) (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (hz : F.f1 *ᵥ zC = zD) (hl : lD ᵥ* F.f2 = lC)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (F.augMap zC lC hzC hlC zD lD hzD hlD hz hl))
      (σD.sumCongr σC.symm) = (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) :
    kmCoord C zC lC hzC hlC σC = kmCoord D zD lD hzD hlD σD := by
  have hs : (-1 : k) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h := kmCoord_eq_of_fourMap_total F zC lC hzC hlC zD lD hzD hlD hz hl σC σD
    (by rw [hcone]; exact hs)
  rw [hcone] at h
  calc
    kmCoord C zC lC hzC hlC σC =
        (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
          ((-1 : k) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)))⁻¹ := h
    _ = kmCoord D zD lD hzD hlD σD *
        ((-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) *
          ((-1 : k) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)))⁻¹) := by ring
    _ = kmCoord D zD lD hzD hlD σD := by rw [mul_inv_cancel₀ hs, mul_one]

end FourMap

section TwoTerm

variable {k : Type*} [Field k]

/-- The coordinate of a zero functional vanishes, with no exactness assumption. -/
theorem kmCoord_zero_functional {ι0 ι1 ι2 ι3 : Type*}
    [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
    [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    (C : FourCx k ι0 ι1 ι2 ι3) (z : ι1 → k)
    (hz : C.d1 *ᵥ z = 0) (hl : (0 : ι2 → k) ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z 0 hz hl σ = 0 := by
  have hn : ¬ Nonempty (Contraction (C.aug z 0 hz hl).toBased) := by
    rintro ⟨h⟩
    have he := BasedCx.isExact_of_contraction _ h
    let y : ι1 ⊕ (ι3 ⊕ Unit) → k := Pi.single (Sum.inr (Sum.inr ())) 1
    obtain ⟨v, hv⟩ := he.2 y (by
      funext i
      rcases i with (i | i) | i <;>
        simp [y, FourCx.toBased_dEO, FourCx.aug, mulVec, dotProduct, Pi.single_apply])
    have htop := congrFun hv (Sum.inr (Sum.inr ()))
    simp [y, FourCx.toBased_dOE, FourCx.aug, mulVec, dotProduct,
      Fintype.sum_sum_type] at htop
  simp [kmCoord, torsion, hn]

/-- For a corank-one matrix, nonzero class and functional make the augmented
complex exact.  This assertion is used only in the nonzero-coordinate case. -/
theorem twoTerm_aug_exact_of_nonzero {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (z w : Fin (m + 1) → k)
    (hdet : D.det = 0) (hadj : D.adjugate ≠ 0)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0) : ((twoTerm D).aug z w hz hw).IsExact := by
  classical
  change D *ᵥ z = 0 at hz
  change w ᵥ* D = 0 at hw
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (funext h)
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  let wl : (Fin (m + 1) → k) →ₗ[k] k :=
    { toFun := fun v => w ⬝ᵥ v
      map_add' := by intro a b; simp [dotProduct, Finset.sum_add_distrib, mul_add]
      map_smul' := by intro a v; simp [dotProduct, Finset.mul_sum, mul_left_comm] }
  have hsurj : Function.Surjective wl := by
    intro a
    refine ⟨Pi.single j (a / w j), ?_⟩
    change w ⬝ᵥ Pi.single j (a / w j) = a
    simp [dotProduct, Pi.single_apply]
    field_simp
  have hker : Module.finrank k (LinearMap.ker wl) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker wl
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp at h
    omega
  have hle : LinearMap.range D.mulVecLin ≤ LinearMap.ker wl := by
    rintro y ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    change w ⬝ᵥ (D *ᵥ v) = 0
    rw [dotProduct_mulVec, hw, zero_dotProduct]
  have hr : LinearMap.range D.mulVecLin = LinearMap.ker wl := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    change D.rank = Module.finrank k (LinearMap.ker wl)
    rw [Central.rank_eq_of_adjugate_ne_zero hdet hadj, hker]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvi : z i * v (Sum.inr ()) = 0 := by
      have h := congrFun hv i
      simpa [FourCx.aug, twoTerm, mulVec, dotProduct, Fintype.sum_sum_type] using h
    have hv0 : v (Sum.inr ()) = 0 := (mul_eq_zero.mp hvi).resolve_left hi
    funext a
    rcases a with a | a
    · exact a.elim
    · cases a
      exact hv0
  · intro y hy
    obtain ⟨a, ha⟩ := Central.ker_proportional D (Central.le_rank_of_adjugate_ne_zero hadj)
      hz hz0 hy
    refine ⟨Sum.elim Empty.elim (fun _ => a), ?_⟩
    funext i
    simpa [FourCx.aug, twoTerm, mulVec, dotProduct, Fintype.sum_sum_type,
      Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun ha.symm i
  · intro y hy
    have hyw : wl y = 0 := by
      have h := congrFun hy (Sum.inr ())
      simpa [wl, FourCx.aug, twoTerm, mulVec, dotProduct] using h
    have hym : y ∈ LinearMap.range D.mulVecLin := by
      rw [hr, LinearMap.mem_ker]
      exact hyw
    obtain ⟨v, hv⟩ := hym
    exact ⟨v, hv⟩
  · intro y
    refine ⟨Pi.single j (y (Sum.inr ()) / w j), ?_⟩
    funext a
    rcases a with a | a
    · exact a.elim
    · cases a
      simp [FourCx.aug, twoTerm, mulVec, dotProduct, Pi.single_apply]
      field_simp

/-- The adjugate and Knudsen–Mumford coordinates agree without an exact
augmentation premise.  A nonzero adjugate ensures that the adjugate coordinate
is well-defined; zero classes and zero functionals are included. -/
theorem kmCoord_twoTerm_of_adjugate {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (z w : Fin (m + 1) → k) (u : k)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (hadj : D.adjugate ≠ 0) (hu : Central.IsClassFunctionalCoord D z w u) :
    kmCoord (twoTerm D) z w hz hw (σ₀ (m + 1)) = u := by
  classical
  by_cases hu0 : u = 0
  · have hzw : z = 0 ∨ w = 0 := by
      by_cases hz0 : z = 0
      · exact Or.inl hz0
      · right
        obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
          by_contra h
          push Not at h
          exact hz0 (funext h)
        funext j
        have h := congrFun (congrFun hu i) j
        simp only [vecMulVec_apply, hu0, Matrix.smul_apply, zero_smul] at h
        exact (mul_eq_zero.mp h).resolve_left hi
    rcases hzw with hz0 | hw0
    · subst z
      rw [kmCoord_zero_class, hu0]
    · subst w
      rw [kmCoord_zero_functional, hu0]
  · obtain ⟨i, j, hij⟩ := Central.exists_entry_ne_zero hadj
    have hz0 : z ≠ 0 := by
      intro h
      have he := congrFun (congrFun hu i) j
      simp only [vecMulVec_apply, h, Pi.zero_apply, zero_mul,
        Matrix.smul_apply, smul_eq_mul] at he
      exact (mul_ne_zero hu0 hij) he.symm
    have hw0 : w ≠ 0 := by
      intro h
      have he := congrFun (congrFun hu i) j
      simp only [vecMulVec_apply, h, Pi.zero_apply, mul_zero,
        Matrix.smul_apply, smul_eq_mul] at he
      exact (mul_ne_zero hu0 hij) he.symm
    have hd : D.det = 0 := by
      by_contra hn
      have hzero := Central.isClassFunctionalCoord_zero_of_isUnit_det (w := w)
        (isUnit_iff_ne_zero.mpr hn) hz
      exact hu0 (Central.isClassFunctionalCoord_unique hadj hu hzero)
    obtain ⟨hc⟩ := exists_contraction _ (FourCx.isExact_toBased _
      (twoTerm_aug_exact_of_nonzero D z w hd hadj hz hw hz0 hw0))
    exact kmCoord_twoTerm D z w u hz hw hc hu

end TwoTerm

section Original

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
/-- Explicit provenance data at one constituent.  The core's scalar is the
relaxed coordinate; the chain map carries the original class and functional,
and its cone carries the retained determinant basis.  No exactness of either
augmented complex, integral-unit correction, or coordinate equality is assumed. -/
structure RetainedCoordinateModelG
    (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) (urel : FractionRing OO) where
  m : ℕ
  D : Matrix (Fin (m + 1)) (Fin (m + 1)) (FractionRing OO)
  zc : Fin (m + 1) → FractionRing OO
  wc : Fin (m + 1) → FractionRing OO
  hzc : (twoTerm D).d1 *ᵥ zc = 0
  hwc : wc ᵥ* (twoTerm D).d1 = 0
  hadj : D.adjugate ≠ 0
  coord : Central.IsClassFunctionalCoord D zc wc urel
  f : FourMap (PreComplex'.toFour (Cev (M.C.map (φO b)) x)) (twoTerm D)
  class_map : f.f1 *ᵥ (evK (sgnChar x) ∘ z) = zc
  functional_map : wc ᵥ* f.f2 = evK (sgnChar x) ∘ lam
  cone_basis : torsion (BasedCx.cone (f.augMap _ _ (hzev (hzC M.isUnit_B hz) x)
      (hlamev hlam x) zc wc hzc hwc class_map functional_map))
      ((σ₀ (m + 1)).sumCongr (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N).symm) =
    (-1) ^ Fintype.card ((Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) ⊕
      ((Fin M.C.m2 ⊕ M.C.N) ⊕ Unit))

/-- The unit-free direct constructor of the original relaxed-coordinate link.
The only remaining input is the construction of the actual retained models. -/
theorem relIsKMG_of_retained_models
    (M : Identification2G K S S' hS b dK hK cE tK)
    (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (models : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      Nonempty (RetainedCoordinateModelG M z lam hz hlam x (urel x))) :
    ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel z lam hz hlam := by
  intro x hΔ
  obtain ⟨c⟩ := models x hΔ
  have hcomp := kmCoord_eq_of_fourMap_retained_total c.f _ _
    (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x) c.zc c.wc c.hzc c.hwc
    c.class_map c.functional_map (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N)
    (σ₀ (c.m + 1)) c.cone_basis
  exact (hcomp.trans (kmCoord_twoTerm_of_adjugate c.D c.zc c.wc (urel x)
    c.hzc c.hwc c.hadj c.coord)).symm

/-- Combining an actual retained model with the existing correction comparison
supplies the clearing interface, with the original completed-ring correction. -/
theorem origCoordLink_of_retained_models {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (urel : Addr F.b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (hη : CorrectedIsEta D F η urel)
    (models : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
      Nonempty (RetainedCoordinateModelG M z lam hz hlam x (urel x))) :
    OrigCoordLink D F M z lam hz hlam η :=
  ZInQ.Manuscript.RC.Wiring.origCoordLink_of_eta_rel hη
    (relIsKMG_of_retained_models M urel z lam hz hlam models)

end Original

set_option pp.universes false

end ZInQ.Contrib.RC53Assist.CoordLink
