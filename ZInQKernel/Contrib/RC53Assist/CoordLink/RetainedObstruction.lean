import ZInQKernel.Contrib.RC53Assist.CoordLink.Comparison

/-! # Strict functional transport excludes coboundary cases

`RetainedCoordinateModelG` asks for literal cochain equalities transporting the class and the
functional, and for the torsion of the fixed diagonal augmented map to be the retained sign. When the
functional is a nonzero coboundary `lam = β d²`, no such retained model exists
(`StrictFunctionalTransport.no_retained_model_of_coboundary`), although the original coordinate is
zero there; `ContractibleTail` is an explicit example over `ℚ` (a contractible disk in degrees two and
three). So the retained-model route needs a homotopy-aware comparison (for a coboundary functional the
augmented degree-three map can carry the off-diagonal term `(r, a) ↦ a - β r`) before it can serve as
the faithful replacement of the coordinate link. These results were found and checked in an
independent review.
-/

namespace ZInQ.Contrib.RC53Assist.CoordLink.ContractibleTail

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.CoordLink

/-- A contractible disk in degrees two and three. -/
def tailCx : FourCx ℚ Empty Empty (Fin 1) (Fin 1) where
  d0 := 0
  d1 := 0
  d2 := 1
  d10 := by simp
  d21 := by simp

theorem tail_hz : tailCx.d1 *ᵥ (0 : Empty → ℚ) = 0 := mulVec_zero _
theorem tail_hl : (1 : Fin 1 → ℚ) ᵥ* tailCx.d1 = 0 := by
  ext e
  exact e.elim

def sigmaTail : (Empty ⊕ Unit) ⊕ Fin 1 ≃ Empty ⊕ (Fin 1 ⊕ Unit) :=
  ((Equiv.sumCongr (Equiv.emptySum Empty Unit) (Equiv.refl (Fin 1))).trans
    (Equiv.sumComm Unit (Fin 1))).trans (Equiv.emptySum Empty (Fin 1 ⊕ Unit)).symm

theorem tail_exact : tailCx.IsExact := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    ext e
    exact e.elim
  · intro y hy
    refine ⟨0, ?_⟩
    ext e
    exact e.elim
  · intro y hy
    have hy0 : y = 0 := by simpa [tailCx] using hy
    refine ⟨0, ?_⟩
    simp [tailCx, hy0]
  · intro y
    exact ⟨y, by simp [tailCx]⟩

theorem tail_coordinate_zero : kmCoord tailCx 0 1 tail_hz tail_hl sigmaTail = 0 :=
  ZInQ.Contrib.CloudB3RC53.CoordLink.kmCoord_zero_class _ _ _ _ _

/-- Strict pullback of this nonzero coboundary functional to a two-term core cannot
have an exact augmented cone, even though the original coordinate is zero. -/
theorem tail_aug_cone_not_exact {n : ℕ} (D : Matrix (Fin n) (Fin n) ℚ)
    (z w : Fin n → ℚ) (hz : (twoTerm D).d1 *ᵥ z = 0)
    (hw : w ᵥ* (twoTerm D).d1 = 0) (F : FourMap tailCx (twoTerm D))
    (hzc : F.f1 *ᵥ (0 : Empty → ℚ) = z) (hlc : w ᵥ* F.f2 = (1 : Fin 1 → ℚ)) :
    ¬ (BasedCx.cone (F.augMap 0 1 tail_hz tail_hl z w hz hw hzc hlc)).IsExact := by
  intro hc
  let f := F.augMap 0 1 tail_hz tail_hl z w hz hw hzc hlc
  let C := (tailCx.aug 0 1 tail_hz tail_hl).toBased
  let W := ((twoTerm D).aug z w hz hw).toBased
  let y : Empty ⊕ (Fin 1 ⊕ Unit) → ℚ :=
    Sum.elim Empty.elim (Sum.elim (fun _ => 1) (fun _ => 0))
  have hfo : f.fO *ᵥ y = 0 := by
    funext i
    rcases i with i | (i | i)
    · simp [f, FourMap.augMap, mulVec, dotProduct, Fintype.sum_sum_type, y]
    · exact i.elim
    · cases i
      simp [f, FourMap.augMap, mulVec, dotProduct, Fintype.sum_sum_type, y]
  have heo : C.dEO = 0 := by
    ext ((i | i) | j) (i' | (j' | u')) <;>
      simp [C, FourCx.toBased_dEO, FourCx.aug, tailCx]
  have hcy : (BasedCx.cone f).dOE *ᵥ (Sum.elim 0 y) = 0 := by
    change fromBlocks W.dOE f.fO 0 (-C.dEO) *ᵥ (Sum.elim 0 y) = 0
    rw [fromBlocks_mulVec]
    simp [heo, hfo, Function.comp_def]
    funext i
    rcases i with i | i <;> simp [mulVec, dotProduct]
  obtain ⟨v, hv⟩ := hc.1 _ hcy
  change fromBlocks W.dEO f.fE 0 (-C.dOE) *ᵥ v =
    Sum.elim (0 : (Empty ⊕ Unit) ⊕ Fin n → ℚ) y at hv
  rw [fromBlocks_mulVec, zero_mulVec, zero_add] at hv
  have hsrc := congrArg (fun a => a ∘ Sum.inr) hv
  have e0 := congrFun hsrc (Sum.inr (Sum.inl (0 : Fin 1)))
  have e1 := congrFun hsrc (Sum.inr (Sum.inr ()))
  simp [C, FourCx.toBased_dOE, FourCx.aug, tailCx, mulVec, dotProduct,
    Fintype.sum_sum_type, y] at e0 e1
  linarith

end ZInQ.Contrib.RC53Assist.CoordLink.ContractibleTail

namespace ZInQ.Contrib.RC53Assist.CoordLink.StrictFunctionalTransport

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)
open ZInQ.Contrib.RC53Assist.CoordLink

/-- A strict pullback of a degree-three coboundary functional to a two-term model
cannot have an exact augmented cone when the coboundary functional has a nonzero
value on some degree-three vector. -/
theorem augmented_cone_not_exact_of_coboundary
    {k : Type*} [Field k] {ι0 ι1 ι2 ι3 : Type*}
    [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
    [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    (C0 : FourCx k ι0 ι1 ι2 ι3) (zc : ι1 → k) (lc : ι2 → k)
    (hzc : C0.d1 *ᵥ zc = 0) (hlc : lc ᵥ* C0.d1 = 0)
    (β r : ι3 → k) (hcb : lc = β ᵥ* C0.d2) (hr : β ⬝ᵥ r ≠ 0)
    {n : ℕ} (D : Matrix (Fin n) (Fin n) k) (z w : Fin n → k)
    (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (F : FourMap C0 (twoTerm D)) (hzmap : F.f1 *ᵥ zc = z) (hlmap : w ᵥ* F.f2 = lc) :
    ¬ (BasedCx.cone (F.augMap zc lc hzc hlc z w hz hw hzmap hlmap)).IsExact := by
  intro hc
  let f := F.augMap zc lc hzc hlc z w hz hw hzmap hlmap
  let C := (C0.aug zc lc hzc hlc).toBased
  let W := ((twoTerm D).aug z w hz hw).toBased
  let y : ι1 ⊕ (ι3 ⊕ Unit) → k := Sum.elim 0 (Sum.elim r 0)
  have hfo : f.fO *ᵥ y = 0 := by
    funext i
    rcases i with i | (i | i)
    · simp [f, FourMap.augMap, mulVec, dotProduct, Fintype.sum_sum_type, y]
    · exact i.elim
    · cases i
      simp [f, FourMap.augMap, mulVec, dotProduct, Fintype.sum_sum_type, y]
  have heo : C.dEO *ᵥ y = 0 := by
    funext i
    rcases i with (i | i) | i <;>
      simp [C, FourCx.toBased_dEO, FourCx.aug, mulVec, dotProduct,
        Fintype.sum_sum_type, y]
  have hcy : (BasedCx.cone f).dOE *ᵥ (Sum.elim 0 y) = 0 := by
    change fromBlocks W.dOE f.fO 0 (-C.dEO) *ᵥ (Sum.elim 0 y) = 0
    rw [fromBlocks_mulVec, zero_mulVec, zero_add]
    change Sum.elim (W.dOE *ᵥ (0 : (Empty ⊕ Unit) ⊕ Fin n → k) + f.fO *ᵥ y)
      ((-C.dEO) *ᵥ y) = 0
    rw [mulVec_zero, hfo, zero_add, neg_mulVec, heo, neg_zero]
    funext i
    rcases i with i | i <;> rfl
  obtain ⟨v, hv⟩ := hc.1 _ hcy
  change fromBlocks W.dEO f.fE 0 (-C.dOE) *ᵥ v =
    Sum.elim (0 : (Empty ⊕ Unit) ⊕ Fin n → k) y at hv
  rw [fromBlocks_mulVec, zero_mulVec, zero_add] at hv
  have hsrc := congrArg (fun a => a ∘ Sum.inr) hv
  let q : ι2 → k := fun j => v (Sum.inr (Sum.inr j))
  have htop : -(C0.d2 *ᵥ q) = r := by
    funext i
    have h := congrFun hsrc (Sum.inr (Sum.inl i))
    simpa [C, FourCx.toBased_dOE, FourCx.aug, mulVec, dotProduct,
      Fintype.sum_sum_type, y, q] using h
  have hread : -(lc ⬝ᵥ q) = 0 := by
    have h := congrFun hsrc (Sum.inr (Sum.inr ()))
    simpa [C, FourCx.toBased_dOE, FourCx.aug, mulVec, dotProduct,
      Fintype.sum_sum_type, y, q] using h
  have hlq : β ⬝ᵥ (C0.d2 *ᵥ q) = 0 := by
    rw [dotProduct_mulVec, ← hcb]
    exact neg_eq_zero.mp hread
  have hb := congrArg (fun a => β ⬝ᵥ a) htop
  rw [dotProduct_neg, hlq, neg_zero] at hb
  exact hr hb.symm

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
/-- The same obstruction applies to the exact retained-model record used by the
new constructor. This is conditional on a given identification and actual
coboundary data, not an arithmetic non-vacuity assertion. -/
theorem no_retained_model_of_coboundary
    {K : Type} [Field K] [NumberField K]
    {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
    [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
    {b dK hK cE tK : ℕ}
    (M : Identification2G K S S' hS b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) (u : FractionRing OO)
    (β r : Fin M.C.m2 ⊕ M.C.N → FractionRing OO)
    (hcb : evK (sgnChar x) ∘ lam =
      β ᵥ* (PreComplex'.toFour (Cev (M.C.map (φO b)) x)).d2)
    (hr : β ⬝ᵥ r ≠ 0) :
    ¬ Nonempty (RetainedCoordinateModelG M z lam hz hlam x u) := by
  rintro ⟨c⟩
  have hn := augmented_cone_not_exact_of_coboundary
    (PreComplex'.toFour (Cev (M.C.map (φO b)) x)) _ _
    (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x) β r hcb hr
    c.D c.zc c.wc c.hzc c.hwc c.f c.class_map c.functional_map
  have hs : (-1 : FractionRing OO) ^ Fintype.card ((Fin M.C.m0 ⊕ Unit ⊕ Fin M.C.m1) ⊕
      ((Fin M.C.m2 ⊕ M.C.N) ⊕ Unit)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hcone := c.cone_basis
  unfold torsion at hcone
  split_ifs at hcone with hcontr
  · exact hn (@BasedCx.isExact_of_contraction _ _ _ _ _ _ _ _ _ hcontr.some)
  · exact hs hcone.symm

end ZInQ.Contrib.RC53Assist.CoordLink.StrictFunctionalTransport
