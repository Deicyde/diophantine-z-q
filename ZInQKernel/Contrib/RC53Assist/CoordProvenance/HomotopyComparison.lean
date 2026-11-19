import ZInQKernel.Contrib.RC53Assist.CoordLink.Comparison

/-!
# Homotopy-aware comparison in the original determinant basis

The class and the paired functional are compared as cohomology classes, with
specified boundary witnesses.  The induced map of augmented complexes has
non-diagonal entries on the augmentation lines.  A dual boundary β d² is
retained by the degree-three entry (r, a) ↦ a − β(r), rather than discarded.

The coordinate formula below uses the actual augmented cone and its torsion.
It requires neither exactness of the augmented source and target nor a
nonzero class or functional.  Its retained-basis factor is computed from the
cone; no original-coordinate equality is a field of the comparison data.

The locators are ex:arith-paired-functional, TeX 3837–3862;
ex:arith-coordinate, TeX 3877–3892; ex:arith-common-coordinate, TeX 4159–4194;
and ex:limits-fixed-field-clearing, TeX 5509–5516.  No additional printed
proposition is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.Homotopy

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.CoordLink (torsion_ne_zero_iff_contraction exact_iff_of_exact_cone)

section Comparison

variable {K : Type*} [Field K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']
  (C : FourCx K ι0 ι1 ι2 ι3) (D : FourCx K ι0' ι1' ι2' ι3')
  (zC : ι1 → K) (lC : ι2 → K) (zD : ι1' → K) (lD : ι2' → K)

/-- A comparison of the same class and functional class, with their retained
boundary witnesses.  It does not contain a coordinate identity. -/
structure HomotopyComparison where
  f : FourMap C D
  classBoundary : ι0' → K
  functionalBoundary : ι3 → K
  class_map : f.f1 *ᵥ zC = zD + D.d0 *ᵥ classBoundary
  functional_map : lD ᵥ* f.f2 = lC + functionalBoundary ᵥ* C.d2

variable {C D zC lC zD lD}

omit [Fintype ι0] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The image of the original cycle differs from the target cycle by the
specified boundary in the target complex. -/
theorem HomotopyComparison.class_discrepancy (H : HomotopyComparison C D zC lC zD lD) :
    H.f.f1 *ᵥ zC - zD = D.d0 *ᵥ H.classBoundary := by
  rw [H.class_map]
  abel

omit [Fintype ι0] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The two functionals have the same value on corresponding cohomology
classes: the dual-boundary discrepancy vanishes on degree-two cocycles. -/
theorem HomotopyComparison.functional_on_cycles (H : HomotopyComparison C D zC lC zD lD)
    (w : ι2 → K) (hw : C.d2 *ᵥ w = 0) : lD ⬝ᵥ (H.f.f2 *ᵥ w) = lC ⬝ᵥ w := by
  rw [dotProduct_mulVec, H.functional_map, add_dotProduct, ← dotProduct_mulVec, hw,
    dotProduct_zero, add_zero]

/-- The degree-zero map carries the class homotopy in its augmentation column. -/
def HomotopyComparison.f0aug (H : HomotopyComparison C D zC lC zD lD) :
    Matrix (ι0' ⊕ Unit) (ι0 ⊕ Unit) K :=
  fromBlocks H.f.f0 (replicateCol Unit H.classBoundary) 0 1

/-- The degree-three map carries the functional homotopy in its augmentation row. -/
def HomotopyComparison.f3aug (H : HomotopyComparison C D zC lC zD lD) :
    Matrix (ι3' ⊕ Unit) (ι3 ⊕ Unit) K :=
  fromBlocks H.f.f3 0 (replicateRow Unit H.functionalBoundary) 1

omit [Fintype ι0] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- Explicit off-diagonal degree-three value. -/
theorem HomotopyComparison.f3aug_value (H : HomotopyComparison C D zC lC zD lD)
    (r : ι3 → K) (a : K) :
    H.f3aug *ᵥ Sum.elim r (fun _ => a) =
      Sum.elim (H.f.f3 *ᵥ r) (fun _ => a + H.functionalBoundary ⬝ᵥ r) := by
  rw [HomotopyComparison.f3aug, fromBlocks_mulVec, zero_mulVec, add_zero, one_mulVec]
  funext i
  cases i with
  | inl i => rfl
  | inr u =>
    cases u
    simp [replicateRow, mulVec, dotProduct, add_comm]

omit [Fintype ι0] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The class boundary is precisely the chain-map identity in degree zero. -/
theorem HomotopyComparison.comm0_aug (H : HomotopyComparison C D zC lC zD lD) :
    fromCols D.d0 (replicateCol Unit zD) * H.f0aug =
      H.f.f1 * fromCols C.d0 (replicateCol Unit zC) := by
  unfold HomotopyComparison.f0aug
  erw [fromCols_mul_fromBlocks, mul_fromCols]
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero]
  congr 1
  · exact H.f.c0
  · ext i u
    cases u
    simpa [mul_apply, replicateCol, mulVec, dotProduct, add_comm] using
      (congrFun H.class_map i).symm

omit [Fintype ι0] [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The functional boundary is precisely the chain-map identity in degree two. -/
theorem HomotopyComparison.comm2_aug (H : HomotopyComparison C D zC lC zD lD) :
    fromRows D.d2 (replicateRow Unit lD) * H.f.f2 =
      H.f3aug * fromRows C.d2 (replicateRow Unit lC) := by
  unfold HomotopyComparison.f3aug
  erw [fromRows_mul, fromBlocks_mul_fromRows]
  simp only [Matrix.zero_mul, Matrix.one_mul, add_zero]
  congr 1
  · exact H.f.c2
  · ext u j
    cases u
    simpa [mul_apply, replicateRow, vecMul, dotProduct, add_comm] using
      congrFun H.functional_map j

/-- The homotopy-aware map of the original augmented complexes.  The
augmentation lines have identity diagonal entries and retained off-diagonal
class and functional homotopies. -/
def HomotopyComparison.augMap (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0) :
    ChainMapB (C.aug zC lC hzC hlC).toBased (D.aug zD lD hzD hlD).toBased where
  fE := fromBlocks H.f0aug 0 0 H.f.f2
  fO := fromBlocks H.f.f1 0 0 H.f3aug
  deg_fE := by
    rintro ((i | i) | i) ((j | j) | j) h
    all_goals first | rfl | exact absurd rfl h
  deg_fO := by
    rintro (i | (i | i)) (j | (j | j)) h
    all_goals first | rfl | exact absurd rfl h
  commOE := by
    change fromBlocks (fromCols D.d0 (replicateCol Unit zD)) 0 0
        (fromRows D.d2 (replicateRow Unit lD)) * fromBlocks H.f0aug 0 0 H.f.f2 =
      fromBlocks H.f.f1 0 0 H.f3aug *
        fromBlocks (fromCols C.d0 (replicateCol Unit zC)) 0 0
          (fromRows C.d2 (replicateRow Unit lC))
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [H.comm0_aug, H.comm2_aug]
  commEO := by
    change fromBlocks 0 0 D.d1 0 * fromBlocks H.f.f1 0 0 H.f3aug =
      fromBlocks H.f0aug 0 0 H.f.f2 * fromBlocks 0 0 C.d1 0
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [H.f.c1]

/-- The original coordinate formula for any map of the augmented complexes.
Only the comparison cone is required to be exact; zero coordinates are
included. -/
theorem kmCoord_eq_of_augmented_comparison
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (f : ChainMapB (C.aug zC lC hzC hlC).toBased (D.aug zD lD hzD hlD).toBased)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone f) (σD.sumCongr σC.symm) ≠ 0) :
    kmCoord C zC lC hzC hlC σC =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
        (torsion (BasedCx.cone f) (σD.sumCongr σC.symm))⁻¹ := by
  obtain ⟨hc⟩ := (torsion_ne_zero_iff_contraction _ _).mp hcone
  have he := exact_iff_of_exact_cone f (BasedCx.isExact_of_contraction _ hc)
  by_cases hC : (C.aug zC lC hzC hlC).toBased.IsExact
  · obtain ⟨cC⟩ := exists_contraction _ hC
    obtain ⟨cD⟩ := exists_contraction _ (he.mp hC)
    exact kmCoord_eq_of_cone C D zC lC hzC hlC zD lD hzD hlD f cC cD σC σD
  · have hD : ¬ (D.aug zD lD hzD hlD).toBased.IsExact := fun h => hC (he.mpr h)
    have hnC : ¬ Nonempty (Contraction (C.aug zC lC hzC hlC).toBased) :=
      fun h => hC (BasedCx.isExact_of_contraction _ h.some)
    have hnD : ¬ Nonempty (Contraction (D.aug zD lD hzD hlD).toBased) :=
      fun h => hD (BasedCx.isExact_of_contraction _ h.some)
    simp only [kmCoord, torsion, hnC, hnD, dite_false, neg_zero, mul_zero, zero_mul]

/-- The homotopy-aware cone comparison of the same class and functional class,
in the specified original and target bases. -/
theorem HomotopyComparison.coordinate_formula (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) ≠ 0) :
    kmCoord C zC lC hzC hlC σC =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
        (torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm))⁻¹ :=
  kmCoord_eq_of_augmented_comparison hzC hlC hzD hlD _ σC σD hcone

/-- The retained-basis comparison factor is the actual cone-torsion factor.
It is a definition in the coefficient field, not a coordinate-equality input. -/
def HomotopyComparison.retainedFactor (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) : K :=
  (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) *
    (torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm))⁻¹

/-- The retained determinant-basis transport is invertible when its cone is exact. -/
theorem HomotopyComparison.retainedFactor_ne_zero (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) ≠ 0) :
    H.retainedFactor hzC hlC hzD hlD σC σD ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (inv_ne_zero hcone)

/-- The same cohomology tensor expressed in the original retained determinant
basis is the target coordinate multiplied by the computed transport factor. -/
theorem HomotopyComparison.coordinate_in_original_basis (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) ≠ 0) :
    kmCoord C zC lC hzC hlC σC = H.retainedFactor hzC hlC hzD hlD σC σD *
      kmCoord D zD lD hzD hlD σD := by
  rw [H.coordinate_formula hzC hlC hzD hlD σC σD hcone]
  unfold HomotopyComparison.retainedFactor
  ring

/-- Canonically retained cone bases give equality of coordinates, with the
homotopies still present in the comparison map. -/
theorem HomotopyComparison.coordinate_eq_of_retained_basis (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) :
    kmCoord C zC lC hzC hlC σC = kmCoord D zD lD hzD hlD σD := by
  have hs : (-1 : K) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h := H.coordinate_in_original_basis hzC hlC hzD hlD σC σD (by rw [hcone]; exact hs)
  have hf : H.retainedFactor hzC hlC hzD hlD σC σD = 1 := by
    unfold HomotopyComparison.retainedFactor
    rw [hcone, mul_inv_cancel₀ hs]
  simpa only [hf, one_mul] using h

end Comparison

section CoboundaryExample

variable {K : Type*} [Field K]

/-- A contractible tail with a nonzero closed coboundary functional. -/
def tailComplex : FourCx K Empty Empty Unit Unit where
  d0 := 0
  d1 := 0
  d2 := 1
  d10 := by simp
  d21 := by simp

/-- A contractible two-term target. -/
def tailTarget : FourCx K Empty Unit Unit Empty where
  d0 := 0
  d1 := 1
  d2 := 0
  d10 := by simp
  d21 := by simp

/-- The original retained orientation for the contractible-tail example. -/
def tailOrientation : (Empty ⊕ Unit) ⊕ Unit ≃ Empty ⊕ (Unit ⊕ Unit) where
  toFun
    | .inl (.inl e) => e.elim
    | .inl (.inr ()) => .inr (.inr ())
    | .inr () => .inr (.inl ())
  invFun
    | .inl e => e.elim
    | .inr (.inl ()) => .inr ()
    | .inr (.inr ()) => .inl (.inr ())
  left_inv := by
    intro x
    rcases x with x | u
    · rcases x with e | u
      · exact e.elim
      · cases u; rfl
    · cases u; rfl
  right_inv := by
    intro x
    rcases x with e | x
    · exact e.elim
    · rcases x with u | u
      · cases u; rfl
      · cases u; rfl

/-- The functional homotopy is minus the coboundary primitive.  No original
coordinate equality or vanishing-functional premise is used. -/
def tailComparison : HomotopyComparison (tailComplex (K := K)) tailTarget 0 1 0 0 where
  f :=
    { f0 := 0
      f1 := 0
      f2 := 0
      f3 := 0
      c0 := by simp [tailComplex, tailTarget]
      c1 := by simp [tailComplex, tailTarget]
      c2 := by simp [tailComplex, tailTarget] }
  classBoundary := 0
  functionalBoundary := -1
  class_map := by simp
  functional_map := by simp [tailComplex]

/-- The explicit augmentation retains the nonzero coboundary representative:
its degree-three component sends (r, a) to a − r. -/
theorem tailComparison_off_diagonal (r a : K) :
    (tailComparison (K := K)).f3aug *ᵥ Sum.elim (fun _ => r) (fun _ => a) =
      Sum.elim (fun e : Empty => e.elim) (fun _ => a - r) := by
  have h := (tailComparison (K := K)).f3aug_value (fun _ => r) a
  have he : (0 : Empty → K) = fun e => e.elim := funext fun e => e.elim
  simpa [tailComparison, dotProduct, sub_eq_add_neg, he] using h

/-- The homotopy-aware cone is contractible, even though the original
functional is a nonzero coboundary. -/
def tailConeContraction : Contraction (BasedCx.cone ((tailComparison (K := K)).augMap
    (mulVec_zero _) (by simp [tailComplex]) (mulVec_zero _) (zero_vecMul _))) where
  hOE := Matrix.of fun o e => match o, e with
    | .inr (.inl (.inr ())), .inl (.inl (.inr ())) => 1
    | .inl (.inl ()), .inl (.inr ()) => 1
    | .inr (.inr ()), .inr (.inr (.inl ())) => -1
    | _, _ => 0
  hEO := Matrix.of fun e o => match e, o with
    | .inr (.inr (.inr ())), .inl (.inr (.inr ())) => 1
    | _, _ => 0
  deg_hOE := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [BasedCx.cone, FourCx.toBased, tailComplex, tailTarget] at h ⊢
  deg_hEO := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [BasedCx.cone, FourCx.toBased, tailComplex, tailTarget] at h ⊢
  htpy_E := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [BasedCx.cone, HomotopyComparison.augMap, HomotopyComparison.f0aug,
        HomotopyComparison.f3aug, tailComparison, tailComplex, tailTarget,
        FourCx.toBased, FourCx.aug, mul_apply, Fintype.sum_sum_type]
  htpy_O := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [BasedCx.cone, HomotopyComparison.augMap, HomotopyComparison.f0aug,
        HomotopyComparison.f3aug, tailComparison, tailComplex, tailTarget,
        FourCx.toBased, FourCx.aug, mul_apply, Fintype.sum_sum_type]

/-- Nonzero cone torsion is now constructed in the obstructed representative
case, rather than assumed. -/
theorem tailComparison_cone_torsion_ne_zero :
    torsion (BasedCx.cone ((tailComparison (K := K)).augMap (mulVec_zero _)
      (by simp [tailComplex]) (mulVec_zero _) (zero_vecMul _)))
      ((Equiv.sumComm (Empty ⊕ Unit) Unit).sumCongr tailOrientation.symm) ≠ 0 :=
  (torsion_ne_zero_iff_contraction _ _).mpr ⟨tailConeContraction⟩

/-- The even cone basis, with its original order retained explicitly. -/
def tailEvenEquiv : Fin 4 ≃ ((Empty ⊕ Unit) ⊕ Unit) ⊕ (Empty ⊕ (Unit ⊕ Unit)) where
  toFun i := match i.val with
    | 0 => .inl (.inl (.inr ()))
    | 1 => .inl (.inr ())
    | 2 => .inr (.inr (.inl ()))
    | _ => .inr (.inr (.inr ()))
  invFun
    | .inl (.inl (.inl e)) => e.elim
    | .inl (.inl (.inr ())) => 0
    | .inl (.inr ()) => 1
    | .inr (.inl e) => e.elim
    | .inr (.inr (.inl ())) => 2
    | .inr (.inr (.inr ())) => 3
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The obstructed coboundary representative admits a homotopy-aware
comparison in exactly the retained cone basis: its torsion is one. -/
theorem tailComparison_retained_cone_basis :
    torsion (BasedCx.cone ((tailComparison (K := K)).augMap (mulVec_zero _)
      (by simp [tailComplex]) (mulVec_zero _) (zero_vecMul _)))
      ((Equiv.sumComm (Empty ⊕ Unit) Unit).sumCongr tailOrientation.symm) = 1 := by
  let X := BasedCx.cone ((tailComparison (K := K)).augMap (mulVec_zero _)
    (by simp [tailComplex]) (mulVec_zero _) (zero_vecMul _))
  let σ := (Equiv.sumComm (Empty ⊕ Unit) Unit).sumCongr tailOrientation.symm
  have hM : ((X.dOE + (tailConeContraction (K := K)).hOE).submatrix σ id).submatrix
      tailEvenEquiv tailEvenEquiv =
      (!![0, 0, -1, 1; 0, 1, 0, 0; 0, 0, -1, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, σ, tailConeContraction, tailEvenEquiv, tailOrientation,
        BasedCx.cone, HomotopyComparison.augMap, HomotopyComparison.f0aug,
        HomotopyComparison.f3aug, tailComparison, tailComplex, tailTarget,
        FourCx.toBased, FourCx.aug]
  rw [← tau_eq_torsion _ tailConeContraction]
  unfold tau
  rw [← det_submatrix_equiv_self tailEvenEquiv, hM]
  norm_num [det_succ_row_zero, det_fin_three, Fin.sum_univ_succ, Fin.succAbove]

/-- The original functional is not the zero cochain. -/
theorem tail_functional_ne_zero : (1 : Unit → K) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h ())

end CoboundaryExample

section FiniteModels

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom coneCx)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic coneCx_acyclic_of_quasiIso)

variable {K : Type} [Field K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

/-- The degreewise basis types of a four-term finite free model. -/
abbrev quadIndex (ι0 ι1 ι2 ι3 : Type) : ℤ → Type
  | 0 => ι0
  | 1 => ι1
  | 2 => ι2
  | 3 => ι3
  | _ => Empty

/-- The differentials of a four-term model as linear maps. -/
def quadD (C : FourCx K ι0 ι1 ι2 ι3) :
    (n : ℤ) → (quadIndex ι0 ι1 ι2 ι3 n → K) →ₗ[K] (quadIndex ι0 ι1 ι2 ι3 (n + 1) → K)
  | 0 => C.d0.mulVecLin
  | 1 => C.d1.mulVecLin
  | 2 => C.d2.mulVecLin
  | _ => 0

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- The finite matrix model has square-zero differential in every degree. -/
theorem quadD_square (C : FourCx K ι0 ι1 ι2 ι3) (n : ℤ)
    (v : quadIndex ι0 ι1 ι2 ι3 n → K) : quadD C (n + 1) (quadD C n v) = 0 := by
  match n with
  | 0 => exact show C.d1 *ᵥ (C.d0 *ᵥ v) = 0 from by rw [mulVec_mulVec, C.d10, zero_mulVec]
  | 1 => exact show C.d2 *ᵥ (C.d1 *ᵥ v) = 0 from by rw [mulVec_mulVec, C.d21, zero_mulVec]
  | 2 => rfl
  | Int.ofNat (n + 3) => rfl
  | Int.negSucc n =>
    change quadD C (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- The actual degreewise cochain complex of the four-term model. -/
abbrev quadCx (C : FourCx K ι0 ι1 ι2 ι3) : GCx K where
  X n := ModuleCat.of K (quadIndex ι0 ι1 ι2 ι3 n → K)
  d i j h := by subst h; exact quadD C i
  d_d i j l hij hjl v := by
    subst hij hjl
    exact quadD_square C i v

/-- A linear family of cycles in an acyclic complex has a linear family of
boundary witnesses when its parameter module is finite free. -/
theorem lift_linear_cycles {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : GCx K) (hE : GAcyclic E) (n : ℤ) (M : (ι → K) →ₗ[K] E.X n)
    (hM : ∀ v, E.d n (n + 1) rfl (M v) = 0) :
    ∃ L : (ι → K) →ₗ[K] E.X (n - 1), ∀ v, E.d (n - 1) n (by omega) (L v) = M v := by
  have hs : ∀ i : ι, ∃ y : E.X (n - 1),
      E.d (n - 1) n (by omega) y = M (Pi.single i 1) := fun i =>
    hE (n - 1) n (n + 1) (by omega) rfl _ (hM _)
  choose y hy using hs
  let L := (Pi.basisFun K ι).constr K y
  have he : (E.d (n - 1) n (by omega)).comp L = M := by
    apply (Pi.basisFun K ι).ext
    intro i
    change E.d (n - 1) n (by omega) (L ((Pi.basisFun K ι) i)) = M ((Pi.basisFun K ι) i)
    rw [show L ((Pi.basisFun K ι) i) = y i from (Pi.basisFun K ι).constr_basis K y i]
    simpa only [Pi.basisFun_apply] using hy i
  exact ⟨L, fun v => LinearMap.congr_fun he v⟩

/-- Matrix entries of an actual linear map in the given original bases. -/
def matrixOf {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → K) →ₗ[K] (κ → K)) : Matrix κ ι K := fun i j => F (Pi.single j 1) i

/-- The original-basis matrix represents the given linear map without rescaling. -/
theorem matrixOf_mulVec {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → K) →ₗ[K] (κ → K)) (v : ι → K) : matrixOf F *ᵥ v = F v := by
  conv_rhs => rw [show v = ∑ i, v i • Pi.single i (1 : K) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  ext i
  simp [matrixOf, mulVec, dotProduct, map_sum, map_smul, Finset.sum_apply, mul_comm]

/-- Chain-map identities of the actual linear maps are the identities of their
original-basis matrices. -/
theorem matrixOf_chain {a b c d : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (A : Matrix d c K) (B : Matrix b a K)
    (F : (a → K) →ₗ[K] (c → K)) (G : (b → K) →ₗ[K] (d → K))
    (h : ∀ v, A *ᵥ F v = G (B *ᵥ v)) : A * matrixOf F = matrixOf G * B := by
  ext i j
  have hj := h (Pi.single j 1)
  rw [← matrixOf_mulVec F, ← matrixOf_mulVec G, mulVec_mulVec, mulVec_mulVec] at hj
  simpa [mulVec, dotProduct, Pi.single_apply] using congrFun hj i

/-- A comparison of two actual finite models through one cochain complex,
with a retained cochain homotopy of their maps. -/
structure ModelComparison (C : FourCx K ι0 ι1 ι2 ι3) (D : FourCx K ι0' ι1' ι2' ι3')
    (S : GCx K) (ψC : GHom (quadCx C) S) (ψD : GHom (quadCx D) S) where
  f : FourMap C D
  h0 : (ι0 → K) →ₗ[K] S.X (-1)
  h1 : (ι1 → K) →ₗ[K] S.X 0
  h2 : (ι2 → K) →ₗ[K] S.X 1
  h3 : (ι3 → K) →ₗ[K] S.X 2
  hom0 : ∀ v, ψC.f 0 0 rfl v - ψD.f 0 0 rfl (f.f0 *ᵥ v) =
    S.d (-1) 0 (by decide) (h0 v) + h1 (C.d0 *ᵥ v)
  hom1 : ∀ v, ψC.f 1 1 rfl v - ψD.f 1 1 rfl (f.f1 *ᵥ v) =
    S.d 0 1 rfl (h1 v) + h2 (C.d1 *ᵥ v)
  hom2 : ∀ v, ψC.f 2 2 rfl v - ψD.f 2 2 rfl (f.f2 *ᵥ v) =
    S.d 1 2 rfl (h2 v) + h3 (C.d2 *ᵥ v)
  hom3 : ∀ v, ψC.f 3 3 rfl v - ψD.f 3 3 rfl (f.f3 *ᵥ v) = S.d 2 3 rfl (h3 v)

/-- Construct an actual model comparison through an acyclic comparison cone.
The input is a quasi-isomorphic finite target model, not a coordinate identity.
Boundary witnesses are lifted linearly, degree by degree. -/
theorem exists_model_comparison (C : FourCx K ι0 ι1 ι2 ι3) (D : FourCx K ι0' ι1' ι2' ι3')
    (S : GCx K) (ψC : GHom (quadCx C) S) (ψD : GHom (quadCx D) S)
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD)) : Nonempty (ModelComparison C D S ψC ψD) := by
  let E := coneCx ψD
  have hE : GAcyclic E := coneCx_acyclic_of_quasiIso ψD hD
  let uC0 : (ι0 → K) →ₗ[K] S.X 0 := ψC.f 0 0 rfl
  let uC1 : (ι1 → K) →ₗ[K] S.X 1 := ψC.f 1 1 rfl
  let uC2 : (ι2 → K) →ₗ[K] S.X 2 := ψC.f 2 2 rfl
  let uC3 : (ι3 → K) →ₗ[K] S.X 3 := ψC.f 3 3 rfl
  let P3 : (ι3 → K) →ₗ[K] E.X 4 :=
    (0 : (ι3 → K) →ₗ[K] (quadCx D).X 4).prod (ψC.f 3 3 rfl)
  have hp3 : ∀ v, E.d 4 5 rfl (P3 v) = 0 := by
    intro v
    apply Prod.ext
    · rfl
    · change ψD.f 4 4 rfl 0 - S.d 3 4 rfl (ψC.f 3 3 rfl v) = 0
      have hc := ψC.comm 3 4 3 4 rfl rfl rfl rfl v
      change ψC.f 4 4 rfl 0 = S.d 3 4 rfl (ψC.f 3 3 rfl v) at hc
      rw [← hc]
      simp only [map_zero, sub_self]
  obtain ⟨N3, hn3⟩ := lift_linear_cycles E hE 4 P3 hp3
  let F3 : (ι3 → K) →ₗ[K] (ι3' → K) := (LinearMap.fst K _ _).comp N3
  let H3 : (ι3 → K) →ₗ[K] S.X 2 := (-LinearMap.snd K _ _).comp N3
  have h3 : ∀ v, ψC.f 3 3 rfl v - ψD.f 3 3 rfl (F3 v) = S.d 2 3 rfl (H3 v) := by
    intro v
    have h := congrArg Prod.snd (hn3 v)
    change ψD.f 3 3 rfl (F3 v) - S.d 2 3 rfl (N3 v).2 = ψC.f 3 3 rfl v at h
    change _ = S.d 2 3 rfl (-(N3 v).2)
    rw [map_neg, ← h]
    abel
  let P2 : (ι2 → K) →ₗ[K] E.X 3 :=
    (F3.comp C.d2.mulVecLin).prod (uC2 - H3.comp C.d2.mulVecLin)
  have hp2 : ∀ v, E.d 3 4 rfl (P2 v) = 0 := by
    intro v
    apply Prod.ext
    · rfl
    · change ψD.f 3 3 rfl (F3 (C.d2 *ᵥ v)) -
        S.d 2 3 rfl (ψC.f 2 2 rfl v - H3 (C.d2 *ᵥ v)) = 0
      rw [map_sub]
      have hc := ψC.comm 2 3 2 3 rfl rfl rfl rfl v
      change ψC.f 3 3 rfl (C.d2 *ᵥ v) = S.d 2 3 rfl (ψC.f 2 2 rfl v) at hc
      rw [← hc, ← h3]
      abel
  obtain ⟨N2, hn2⟩ := lift_linear_cycles E hE 3 P2 hp2
  let F2 : (ι2 → K) →ₗ[K] (ι2' → K) := (LinearMap.fst K _ _).comp N2
  let H2 : (ι2 → K) →ₗ[K] S.X 1 := (-LinearMap.snd K _ _).comp N2
  have c2 : ∀ v, D.d2 *ᵥ F2 v = F3 (C.d2 *ᵥ v) := by
    intro v
    exact congrArg Prod.fst (hn2 v)
  have h2 : ∀ v, ψC.f 2 2 rfl v - ψD.f 2 2 rfl (F2 v) =
      S.d 1 2 rfl (H2 v) + H3 (C.d2 *ᵥ v) := by
    intro v
    have h := congrArg Prod.snd (hn2 v)
    change ψD.f 2 2 rfl (F2 v) - S.d 1 2 rfl (N2 v).2 =
      ψC.f 2 2 rfl v - H3 (C.d2 *ᵥ v) at h
    have he := (sub_eq_iff_eq_add).mp h.symm
    change _ = S.d 1 2 rfl (-(N2 v).2) + H3 (C.d2 *ᵥ v)
    rw [map_neg, he]
    abel
  let P1 : (ι1 → K) →ₗ[K] E.X 2 :=
    (F2.comp C.d1.mulVecLin).prod (uC1 - H2.comp C.d1.mulVecLin)
  have hp1 : ∀ v, E.d 2 3 rfl (P1 v) = 0 := by
    intro v
    apply Prod.ext
    · change D.d2 *ᵥ F2 (C.d1 *ᵥ v) = 0
      rw [c2, mulVec_mulVec, C.d21, zero_mulVec, map_zero]
    · change ψD.f 2 2 rfl (F2 (C.d1 *ᵥ v)) -
        S.d 1 2 rfl (ψC.f 1 1 rfl v - H2 (C.d1 *ᵥ v)) = 0
      rw [map_sub]
      have hc := ψC.comm 1 2 1 2 rfl rfl rfl rfl v
      change ψC.f 2 2 rfl (C.d1 *ᵥ v) = S.d 1 2 rfl (ψC.f 1 1 rfl v) at hc
      have hh := h2 (C.d1 *ᵥ v)
      rw [mulVec_mulVec, C.d21, zero_mulVec, map_zero, add_zero] at hh
      rw [← hc, ← hh]
      abel
  obtain ⟨N1, hn1⟩ := lift_linear_cycles E hE 2 P1 hp1
  let F1 : (ι1 → K) →ₗ[K] (ι1' → K) := (LinearMap.fst K _ _).comp N1
  let H1 : (ι1 → K) →ₗ[K] S.X 0 := (-LinearMap.snd K _ _).comp N1
  have c1 : ∀ v, D.d1 *ᵥ F1 v = F2 (C.d1 *ᵥ v) := by
    intro v
    exact congrArg Prod.fst (hn1 v)
  have h1 : ∀ v, ψC.f 1 1 rfl v - ψD.f 1 1 rfl (F1 v) =
      S.d 0 1 rfl (H1 v) + H2 (C.d1 *ᵥ v) := by
    intro v
    have h := congrArg Prod.snd (hn1 v)
    change ψD.f 1 1 rfl (F1 v) - S.d 0 1 rfl (N1 v).2 =
      ψC.f 1 1 rfl v - H2 (C.d1 *ᵥ v) at h
    have he := (sub_eq_iff_eq_add).mp h.symm
    change _ = S.d 0 1 rfl (-(N1 v).2) + H2 (C.d1 *ᵥ v)
    rw [map_neg, he]
    abel
  let P0 : (ι0 → K) →ₗ[K] E.X 1 :=
    (F1.comp C.d0.mulVecLin).prod (uC0 - H1.comp C.d0.mulVecLin)
  have hp0 : ∀ v, E.d 1 2 rfl (P0 v) = 0 := by
    intro v
    apply Prod.ext
    · change D.d1 *ᵥ F1 (C.d0 *ᵥ v) = 0
      rw [c1, mulVec_mulVec, C.d10, zero_mulVec, map_zero]
    · change ψD.f 1 1 rfl (F1 (C.d0 *ᵥ v)) -
        S.d 0 1 rfl (ψC.f 0 0 rfl v - H1 (C.d0 *ᵥ v)) = 0
      rw [map_sub]
      have hc := ψC.comm 0 1 0 1 rfl rfl rfl rfl v
      change ψC.f 1 1 rfl (C.d0 *ᵥ v) = S.d 0 1 rfl (ψC.f 0 0 rfl v) at hc
      have hh := h1 (C.d0 *ᵥ v)
      rw [mulVec_mulVec, C.d10, zero_mulVec, map_zero, add_zero] at hh
      rw [← hc, ← hh]
      abel
  obtain ⟨N0, hn0⟩ := lift_linear_cycles E hE 1 P0 hp0
  let F0 : (ι0 → K) →ₗ[K] (ι0' → K) := (LinearMap.fst K _ _).comp N0
  let H0 : (ι0 → K) →ₗ[K] S.X (-1) := (-LinearMap.snd K _ _).comp N0
  have c0 : ∀ v, D.d0 *ᵥ F0 v = F1 (C.d0 *ᵥ v) := by
    intro v
    exact congrArg Prod.fst (hn0 v)
  have h0 : ∀ v, ψC.f 0 0 rfl v - ψD.f 0 0 rfl (F0 v) =
      S.d (-1) 0 (by decide) (H0 v) + H1 (C.d0 *ᵥ v) := by
    intro v
    have h := congrArg Prod.snd (hn0 v)
    change ψD.f 0 0 rfl (F0 v) - S.d (-1) 0 (by decide) (N0 v).2 =
      ψC.f 0 0 rfl v - H1 (C.d0 *ᵥ v) at h
    have he := (sub_eq_iff_eq_add).mp h.symm
    change _ = S.d (-1) 0 (by decide) (-(N0 v).2) + H1 (C.d0 *ᵥ v)
    rw [map_neg, he]
    abel
  refine ⟨{ f := { f0 := matrixOf F0, f1 := matrixOf F1, f2 := matrixOf F2, f3 := matrixOf F3,
                    c0 := matrixOf_chain D.d0 C.d0 F0 F1 c0,
                    c1 := matrixOf_chain D.d1 C.d1 F1 F2 c1,
                    c2 := matrixOf_chain D.d2 C.d2 F2 F3 c2 },
            h0 := H0, h1 := H1, h2 := H2, h3 := H3,
            hom0 := ?_, hom1 := ?_, hom2 := ?_, hom3 := ?_ }⟩
  · intro v; simpa only [matrixOf_mulVec] using h0 v
  · intro v; simpa only [matrixOf_mulVec] using h1 v
  · intro v; simpa only [matrixOf_mulVec] using h2 v
  · intro v; simpa only [matrixOf_mulVec] using h3 v

/-- The actual model comparison as a map of degreewise cochain complexes. -/
def quadMapLinear {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    (F : FourMap C D) : (n : ℤ) → (quadCx C).X n →ₗ[K] (quadCx D).X n
  | 0 => F.f0.mulVecLin
  | 1 => F.f1.mulVecLin
  | 2 => F.f2.mulVecLin
  | 3 => F.f3.mulVecLin
  | _ => 0

omit [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- Matrix chain-map identities give genuine cochain-map identities. -/
theorem quadMapLinear_comm {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    (F : FourMap C D) (n : ℤ) (v : (quadCx C).X n) :
    quadMapLinear F (n + 1) (quadD C n v) = quadD D n (quadMapLinear F n v) := by
  match n with
  | 0 => change F.f1 *ᵥ (C.d0 *ᵥ v) = D.d0 *ᵥ (F.f0 *ᵥ v)
         rw [mulVec_mulVec, mulVec_mulVec, F.c0]
  | 1 => change F.f2 *ᵥ (C.d1 *ᵥ v) = D.d1 *ᵥ (F.f1 *ᵥ v)
         rw [mulVec_mulVec, mulVec_mulVec, F.c1]
  | 2 => change F.f3 *ᵥ (C.d2 *ᵥ v) = D.d2 *ᵥ (F.f2 *ᵥ v)
         rw [mulVec_mulVec, mulVec_mulVec, F.c2]
  | 3 => exact map_zero _
  | Int.ofNat (n + 4) => rfl
  | Int.negSucc n => exact map_zero _

/-- The cochain map attached to the constructed original-basis matrices. -/
def quadMap {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    (F : FourMap C D) : GHom (quadCx C) (quadCx D) where
  f i j h := by subst h; exact quadMapLinear F i
  comm i i₁ j j₁ hij h₁ h₂ hj v := by
    subst hij hj h₁
    exact quadMapLinear_comm F i v

/-- The retained cochain homotopy, including its degree-three component. -/
def ModelComparison.homotopyComponent
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD) :
    ∀ i j : ℤ, (quadCx C).toCC.X i ⟶ S.toCC.X j
  | 0, -1 => ModuleCat.ofHom H.h0
  | 1, 0 => ModuleCat.ofHom H.h1
  | 2, 1 => ModuleCat.ofHom H.h2
  | 3, 2 => ModuleCat.ofHom H.h3
  | _, _ => 0

/-- The constructed comparison comes with an actual Mathlib cochain homotopy
through the same target complex. -/
def ModelComparison.toCCHomotopy
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD) :
    Homotopy (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC)
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f) ≫
        ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD) where
  hom := H.homotopyComponent
  zero := by
    intro i j hij
    rcases i with (_ | _ | _ | _ | n) | n <;>
      rcases j with (_ | _ | _ | n) | (_ | n)
    all_goals first | rfl | exact False.elim (hij (by norm_num [ComplexShape.up_Rel]))
  comm := by
    intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from by simp)]
    match i with
    | 0 =>
      ext v
      change ψC.f 0 0 rfl v = H.h1 (C.d0 *ᵥ v) + S.d (-1) 0 (by decide) (H.h0 v) +
        ψD.f 0 0 rfl (H.f.f0 *ᵥ v)
      exact ((sub_eq_iff_eq_add).mp (H.hom0 v)).trans (by abel)
    | 1 =>
      ext v
      change ψC.f 1 1 rfl v = H.h2 (C.d1 *ᵥ v) + S.d 0 1 rfl (H.h1 v) +
        ψD.f 1 1 rfl (H.f.f1 *ᵥ v)
      exact ((sub_eq_iff_eq_add).mp (H.hom1 v)).trans (by abel)
    | 2 =>
      ext v
      change ψC.f 2 2 rfl v = H.h3 (C.d2 *ᵥ v) + S.d 1 2 rfl (H.h2 v) +
        ψD.f 2 2 rfl (H.f.f2 *ᵥ v)
      exact ((sub_eq_iff_eq_add).mp (H.hom2 v)).trans (by abel)
    | 3 =>
      ext v
      change ψC.f 3 3 rfl v = 0 + S.d 2 3 rfl (H.h3 v) + ψD.f 3 3 rfl (H.f.f3 *ᵥ v)
      simpa only [zero_add] using (sub_eq_iff_eq_add).mp (H.hom3 v)
    | Int.ofNat (n + 4) =>
      ext v
      have hv : v = 0 := funext fun e => e.elim
      subst v
      simp
    | Int.negSucc n =>
      ext v
      have hv : v = 0 := funext fun e => e.elim
      subst v
      simp

omit [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- If the two finite models are models of the same actual cochain complex,
the constructed comparison is a quasi-isomorphism. -/
theorem ModelComparison.quasiIso
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD)
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD)) :
    QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) := by
  rw [quasiIso_iff] at hC hD ⊢
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hn := H.toCCHomotopy.homologyMap_eq n
  have hiC := (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hC n)
  have hiD := (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hD n)
  let f := HomologicalComplex.homologyMap
    (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) n
  let g := HomologicalComplex.homologyMap
    (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD) n
  have : IsIso g := hiD
  have : IsIso (f ≫ g) := by
    change IsIso (HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n)
    rw [← HomologicalComplex.homologyMap_comp, ← hn]
    exact hiC
  change IsIso f
  have he : f = (f ≫ g) ≫ inv g := by simp
  rw [he]
  infer_instance

end FiniteModels

section AugmentedConeExactness

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom coneCx)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic coneCx_acyclic_of_quasiIso)

variable {K : Type} [Field K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

/-- The degree-zero and degree-two coordinates of an augmented cone. -/
abbrev evenVector (d0 : ι0' → K) (a : K) (d2 : ι2' → K)
    (c1 : ι1 → K) (c3 : ι3 → K) (b : K) :
    ((ι0' ⊕ Unit) ⊕ ι2') ⊕ (ι1 ⊕ (ι3 ⊕ Unit)) → K :=
  Sum.elim (Sum.elim (Sum.elim d0 (fun _ => a)) d2)
    (Sum.elim c1 (Sum.elim c3 (fun _ => b)))

/-- The degree-minus-one, degree-one and degree-three coordinates of an augmented cone. -/
abbrev oddVector (d1 : ι1' → K) (d3 : ι3' → K) (b : K)
    (c0 : ι0 → K) (a : K) (c2 : ι2 → K) :
    (ι1' ⊕ (ι3' ⊕ Unit)) ⊕ ((ι0 ⊕ Unit) ⊕ ι2) → K :=
  Sum.elim (Sum.elim d1 (Sum.elim d3 (fun _ => b)))
    (Sum.elim (Sum.elim c0 (fun _ => a)) c2)

variable {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
  {zC : ι1 → K} {lC : ι2 → K} {zD : ι1' → K} {lD : ι2' → K}

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The even differential includes both retained homotopy corrections. -/
theorem HomotopyComparison.cone_even_differential (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (d0 : ι0' → K) (a : K) (d2 : ι2' → K) (c1 : ι1 → K) (c3 : ι3 → K) (b : K) :
    (BasedCx.cone (H.augMap hzC hlC hzD hlD)).dOE *ᵥ evenVector d0 a d2 c1 c3 b =
      oddVector (D.d0 *ᵥ d0 + a • zD + H.f.f1 *ᵥ c1) (D.d2 *ᵥ d2 + H.f.f3 *ᵥ c3)
        (lD ⬝ᵥ d2 + H.functionalBoundary ⬝ᵥ c3 + b) 0 0 (-(C.d1 *ᵥ c1)) := by
  funext i
  rcases i with (i | (i | u)) | ((i | u) | i)
  all_goals simp [BasedCx.cone, HomotopyComparison.augMap, HomotopyComparison.f0aug,
    HomotopyComparison.f3aug, evenVector, oddVector, FourCx.toBased, FourCx.aug,
    mulVec, dotProduct, Fintype.sum_sum_type, smul_eq_mul, mul_comm]
  all_goals ring

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The odd differential retains identity maps on the two augmentation lines. -/
theorem HomotopyComparison.cone_odd_differential (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (d1 : ι1' → K) (d3 : ι3' → K) (b : K) (c0 : ι0 → K) (a : K) (c2 : ι2 → K) :
    (BasedCx.cone (H.augMap hzC hlC hzD hlD)).dEO *ᵥ oddVector d1 d3 b c0 a c2 =
      evenVector (H.f.f0 *ᵥ c0 + a • H.classBoundary) a (D.d1 *ᵥ d1 + H.f.f2 *ᵥ c2)
        (-(C.d0 *ᵥ c0) - a • zC) (-(C.d2 *ᵥ c2)) (-(lC ⬝ᵥ c2)) := by
  funext i
  rcases i with ((i | u) | i) | (i | (i | u))
  all_goals simp [BasedCx.cone, HomotopyComparison.augMap, HomotopyComparison.f0aug,
    HomotopyComparison.f3aug, evenVector, oddVector, FourCx.toBased, FourCx.aug,
    mulVec, dotProduct, Fintype.sum_sum_type, smul_eq_mul, mul_comm]
  all_goals ring

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- A quasi-isomorphism of the original complexes gives an exact homotopy-aware
augmented comparison cone.  The proof retains the boundary terms, including
at zero class and zero functional class. -/
theorem HomotopyComparison.aug_cone_exact (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (hq : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f))) :
    (BasedCx.cone (H.augMap hzC hlC hzD hlD)).IsExact := by
  let E := coneCx (quadMap H.f)
  have hE : GAcyclic E := coneCx_acyclic_of_quasiIso (quadMap H.f) hq
  constructor
  · intro x hx
    let d0 : ι0' → K := fun i => x (.inl (.inl (.inl i)))
    let a : K := x (.inl (.inl (.inr ())))
    let d2 : ι2' → K := fun i => x (.inl (.inr i))
    let c1 : ι1 → K := fun i => x (.inr (.inl i))
    let c3 : ι3 → K := fun i => x (.inr (.inr (.inl i)))
    let b : K := x (.inr (.inr (.inr ())))
    have he : x = evenVector d0 a d2 c1 c3 b := by
      funext i; rcases i with ((i | u) | i) | (i | (i | u)) <;> rfl
    rw [he, H.cone_even_differential hzC hlC hzD hlD] at hx
    have hc1 : C.d1 *ᵥ c1 = 0 := by
      apply neg_eq_zero.mp
      exact funext fun i => congrFun hx (.inr (.inr i))
    have hd0 : D.d0 *ᵥ d0 + a • zD + H.f.f1 *ᵥ c1 = 0 :=
      funext fun i => congrFun hx (.inl (.inl i))
    have hd2 : D.d2 *ᵥ d2 + H.f.f3 *ᵥ c3 = 0 :=
      funext fun i => congrFun hx (.inl (.inr (.inl i)))
    have hb : lD ⬝ᵥ d2 + H.functionalBoundary ⬝ᵥ c3 + b = 0 :=
      congrFun hx (.inl (.inr (.inr ())))
    have hcy0 : E.d 1 2 rfl (c1 + a • zC, -d0 + a • H.classBoundary) = 0 := by
      apply Prod.ext
      · change C.d1 *ᵥ (c1 + a • zC) = 0
        rw [mulVec_add, mulVec_smul, hc1, hzC, smul_zero, add_zero]
      · change H.f.f1 *ᵥ (c1 + a • zC) - D.d0 *ᵥ (-d0 + a • H.classBoundary) = 0
        rw [mulVec_add, mulVec_smul, H.class_map, mulVec_add, mulVec_neg, mulVec_smul, smul_add]
        linear_combination (norm := module) hd0
    obtain ⟨p, hp⟩ := hE 0 1 2 rfl rfl (c1 + a • zC, -d0 + a • H.classBoundary) hcy0
    have hp0 : C.d0 *ᵥ p.1 = c1 + a • zC := congrArg Prod.fst hp
    have hpf : H.f.f0 *ᵥ p.1 = -d0 + a • H.classBoundary := by
      have h := congrArg Prod.snd hp
      change H.f.f0 *ᵥ p.1 - (0 : ι0' → K) = -d0 + a • H.classBoundary at h
      simpa only [sub_zero] using h
    have hcy2 : E.d 3 4 rfl (-c3, d2) = 0 := by
      apply Prod.ext
      · rfl
      · change H.f.f3 *ᵥ (-c3) - D.d2 *ᵥ d2 = 0
        rw [mulVec_neg]
        linear_combination (norm := module) -hd2
    obtain ⟨q, hq2⟩ := hE 2 3 4 rfl rfl (-c3, d2) hcy2
    have hqc : C.d2 *ᵥ q.1 = -c3 := congrArg Prod.fst hq2
    have hqd : H.f.f2 *ᵥ q.1 - D.d1 *ᵥ q.2 = d2 := congrArg Prod.snd hq2
    have hfunD : lD ⬝ᵥ (D.d1 *ᵥ q.2) = 0 := by
      rw [dotProduct_mulVec, hlD, zero_dotProduct]
    have hfunValue : lD ⬝ᵥ d2 = lC ⬝ᵥ q.1 - H.functionalBoundary ⬝ᵥ c3 := by
      rw [← hqd, dotProduct_sub, hfunD, sub_zero, dotProduct_mulVec, H.functional_map,
        add_dotProduct, ← dotProduct_mulVec, hqc, dotProduct_neg]
      abel
    have hbq : -(lC ⬝ᵥ q.1) = b := by
      rw [hfunValue] at hb
      linear_combination -hb
    refine ⟨oddVector (-q.2) 0 0 (-p.1) a q.1, ?_⟩
    rw [H.cone_odd_differential hzC hlC hzD hlD, he]
    have hv0 : H.f.f0 *ᵥ (-p.1) + a • H.classBoundary = d0 := by
      rw [mulVec_neg, hpf]
      module
    have hv2 : D.d1 *ᵥ (-q.2) + H.f.f2 *ᵥ q.1 = d2 := by
      rw [mulVec_neg]
      exact (by module : -(D.d1 *ᵥ q.2) + H.f.f2 *ᵥ q.1 = H.f.f2 *ᵥ q.1 - D.d1 *ᵥ q.2).trans hqd
    have hc1v : -(C.d0 *ᵥ (-p.1)) - a • zC = c1 := by
      rw [mulVec_neg, neg_neg, hp0]
      module
    have hc3v : -(C.d2 *ᵥ q.1) = c3 := by rw [hqc, neg_neg]
    rw [hv0, hv2, hc1v, hc3v, hbq]
  · intro y hy
    let d1 : ι1' → K := fun i => y (.inl (.inl i))
    let d3 : ι3' → K := fun i => y (.inl (.inr (.inl i)))
    let b : K := y (.inl (.inr (.inr ())))
    let c0 : ι0 → K := fun i => y (.inr (.inl (.inl i)))
    let a : K := y (.inr (.inl (.inr ())))
    let c2 : ι2 → K := fun i => y (.inr (.inr i))
    have he : y = oddVector d1 d3 b c0 a c2 := by
      funext i; rcases i with (i | (i | u)) | ((i | u) | i) <;> rfl
    rw [he, H.cone_odd_differential hzC hlC hzD hlD] at hy
    have ha : a = 0 := congrFun hy (.inl (.inl (.inr ())))
    have hcf : H.f.f0 *ᵥ c0 = 0 := by
      have h : H.f.f0 *ᵥ c0 + a • H.classBoundary = 0 :=
        funext fun i => congrFun hy (.inl (.inl (.inl i)))
      simpa only [ha, zero_smul, add_zero] using h
    have hc0 : C.d0 *ᵥ c0 = 0 := by
      have h : -(C.d0 *ᵥ c0) - a • zC = 0 :=
        funext fun i => congrFun hy (.inr (.inl i))
      simpa only [ha, zero_smul, sub_zero, neg_eq_zero] using h
    have hc2 : C.d2 *ᵥ c2 = 0 := by
      apply neg_eq_zero.mp
      exact funext fun i => congrFun hy (.inr (.inr (.inl i)))
    have hd1 : D.d1 *ᵥ d1 + H.f.f2 *ᵥ c2 = 0 :=
      funext fun i => congrFun hy (.inl (.inr i))
    have hcy0 : E.d 0 1 rfl (c0, (0 : (quadCx D).X (-1))) = 0 := by
      apply Prod.ext
      · exact hc0
      · change H.f.f0 *ᵥ c0 - 0 = 0
        rw [hcf, sub_self]
    obtain ⟨p0, hp0⟩ := hE (-1) 0 1 (by decide) rfl (c0, (0 : (quadCx D).X (-1))) hcy0
    have hc0zero : c0 = 0 := by
      have h := congrArg Prod.fst hp0
      change (0 : ι0 → K) = c0 at h
      exact h.symm
    have hcy1 : E.d 2 3 rfl (-c2, d1) = 0 := by
      apply Prod.ext
      · change C.d2 *ᵥ (-c2) = 0
        rw [mulVec_neg, hc2, neg_zero]
      · change H.f.f2 *ᵥ (-c2) - D.d1 *ᵥ d1 = 0
        rw [mulVec_neg]
        linear_combination (norm := module) -hd1
    obtain ⟨p, hp⟩ := hE 1 2 3 rfl rfl (-c2, d1) hcy1
    have hpc : C.d1 *ᵥ p.1 = -c2 := congrArg Prod.fst hp
    have hpd : H.f.f1 *ᵥ p.1 - D.d0 *ᵥ p.2 = d1 := congrArg Prod.snd hp
    have hcy3 : E.d 4 5 rfl ((0 : (quadCx C).X 4), d3) = 0 := by
      apply Prod.ext
      · rfl
      · change 0 - 0 = (0 : (quadCx D).X 4)
        exact sub_self _
    obtain ⟨q, hq3⟩ := hE 3 4 5 rfl rfl ((0 : (quadCx C).X 4), d3) hcy3
    have hqd : H.f.f3 *ᵥ q.1 - D.d2 *ᵥ q.2 = d3 := congrArg Prod.snd hq3
    let b0 := b - lD ⬝ᵥ (-q.2) - H.functionalBoundary ⬝ᵥ q.1
    refine ⟨evenVector (-p.2) 0 (-q.2) p.1 q.1 b0, ?_⟩
    rw [H.cone_even_differential hzC hlC hzD hlD, he, hc0zero, ha]
    have hv1 : D.d0 *ᵥ (-p.2) + (0 : K) • zD + H.f.f1 *ᵥ p.1 = d1 := by
      rw [mulVec_neg, zero_smul, add_zero]
      exact (by module : -(D.d0 *ᵥ p.2) + H.f.f1 *ᵥ p.1 = H.f.f1 *ᵥ p.1 - D.d0 *ᵥ p.2).trans hpd
    have hv3 : D.d2 *ᵥ (-q.2) + H.f.f3 *ᵥ q.1 = d3 := by
      rw [mulVec_neg]
      exact (by module : -(D.d2 *ᵥ q.2) + H.f.f3 *ᵥ q.1 = H.f.f3 *ᵥ q.1 - D.d2 *ᵥ q.2).trans hqd
    have hvc2 : -(C.d1 *ᵥ p.1) = c2 := by rw [hpc, neg_neg]
    have hb0 : lD ⬝ᵥ (-q.2) + H.functionalBoundary ⬝ᵥ q.1 + b0 = b := by
      dsimp [b0]
      ring
    rw [hv1, hv3, hvc2, hb0]

/-- Nonzero torsion of the homotopy-aware augmented cone is a consequence of
the actual quasi-isomorphic model comparison, not an extra premise. -/
theorem HomotopyComparison.aug_cone_torsion_ne_zero (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (hq : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)))
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) ≠ 0 := by
  obtain ⟨h⟩ := exists_contraction _ (H.aug_cone_exact hzC hlC hzD hlD hq)
  exact (torsion_ne_zero_iff_contraction _ _).mpr ⟨h⟩

/-- The original retained determinant-basis factor is now fully constructed
from the model comparison.  No source-coordinate identity or cone-exactness
premise remains. -/
theorem HomotopyComparison.coordinate_formula_of_quasiIso (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (hq : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)))
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    kmCoord C zC lC hzC hlC σC = H.retainedFactor hzC hlC hzD hlD σC σD *
      kmCoord D zD lD hzD hlD σD :=
  H.coordinate_in_original_basis hzC hlC hzD hlD σC σD
    (H.aug_cone_torsion_ne_zero hzC hlC hzD hlD hq σC σD)

end AugmentedConeExactness

section ActualClassAndFunctional

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom coneCx)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GAcyclic coneCx_acyclic_of_quasiIso)

variable {K : Type} [Field K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- The actual class lifts through a genuine finite model, with a retained
cochain boundary.  It is not chosen independently of the actual class. -/
theorem actual_cycle_lift (C : FourCx K ι0 ι1 ι2 ι3) (S : GCx K)
    (ψ : GHom (quadCx C) S)
    (hψ : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψ))
    (z : S.X 1) (hz : S.d 1 2 rfl z = 0) :
    ∃ zC : ι1 → K, C.d1 *ᵥ zC = 0 ∧ ∃ b : S.X 0,
      ψ.f 1 1 rfl zC - z = S.d 0 1 rfl b := by
  have hE := coneCx_acyclic_of_quasiIso ψ hψ
  have hc : (coneCx ψ).d 2 3 rfl ((0 : (quadCx C).X 2), z) = 0 := by
    apply Prod.ext
    · exact mulVec_zero _
    · change ψ.f 2 2 rfl 0 - S.d 1 2 rfl z = 0
      rw [map_zero, hz, sub_self]
  obtain ⟨y, hy⟩ := hE 1 2 3 rfl rfl ((0 : (quadCx C).X 2), z) hc
  have h1 := congrArg Prod.fst hy
  have h2 := congrArg Prod.snd hy
  refine ⟨y.1, h1, y.2, ?_⟩
  change ψ.f 1 1 rfl y.1 - S.d 0 1 rfl y.2 = z at h2
  rw [← h2]
  abel

/-- Values of the actual functional on the original model basis. -/
def modelRow (C : FourCx K ι0 ι1 ι2 ι3) (S : GCx K) (ψ : GHom (quadCx C) S)
    (L : S.X 2 →ₗ[K] K) : ι2 → K := fun i => L (ψ.f 2 2 rfl (Pi.single i 1))

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι3] in
/-- The row represents the pullback of the same actual functional, with no
additional scalar multiplier. -/
theorem modelRow_value (C : FourCx K ι0 ι1 ι2 ι3) (S : GCx K) (ψ : GHom (quadCx C) S)
    (L : S.X 2 →ₗ[K] K) (v : ι2 → K) : modelRow C S ψ L ⬝ᵥ v = L (ψ.f 2 2 rfl v) := by
  conv_rhs => rw [show v = ∑ i, v i • Pi.single i (1 : K) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [modelRow, dotProduct, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι3] in
/-- Closedness of the actual paired functional gives a closed row on its
finite model. -/
theorem modelRow_closed (C : FourCx K ι0 ι1 ι2 ι3) (S : GCx K) (ψ : GHom (quadCx C) S)
    (L : S.X 2 →ₗ[K] K) (hL : ∀ v, L (S.d 1 2 rfl v) = 0) :
    modelRow C S ψ L ᵥ* C.d1 = 0 := by
  ext j
  have h := hL (ψ.f 1 1 rfl (Pi.single j 1))
  have hc := ψ.comm 1 2 1 2 rfl rfl rfl rfl (Pi.single j 1)
  change ψ.f 2 2 rfl (C.d1 *ᵥ Pi.single j 1) = S.d 1 2 rfl (ψ.f 1 1 rfl (Pi.single j 1)) at hc
  rw [← hc, ← modelRow_value, dotProduct_mulVec] at h
  simpa [dotProduct, Pi.single_apply] using h

/-- The functional homotopy is computed from the actual cochain homotopy and
the same actual functional. -/
def ModelComparison.functionalPrimitive
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD) (L : S.X 2 →ₗ[K] K) : ι3 → K :=
  fun i => -L (H.h3 (Pi.single i 1))

omit [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- A computed primitive for the dual-boundary discrepancy. -/
theorem ModelComparison.functionalPrimitive_value
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD) (L : S.X 2 →ₗ[K] K) (v : ι3 → K) :
    H.functionalPrimitive L ⬝ᵥ v = -L (H.h3 v) := by
  conv_rhs => rw [show v = ∑ i, v i • Pi.single i (1 : K) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [ModelComparison.functionalPrimitive, dotProduct, map_sum, map_smul, smul_eq_mul,
    neg_mul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι3'] in
/-- The model comparison preserves the same functional class.  The dual
boundary is derived from the actual cochain homotopy, not supplied as a
coordinate identity. -/
theorem ModelComparison.actual_functional_discrepancy
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD) (L : S.X 2 →ₗ[K] K)
    (hL : ∀ v, L (S.d 1 2 rfl v) = 0) :
    modelRow D S ψD L ᵥ* H.f.f2 = modelRow C S ψC L + H.functionalPrimitive L ᵥ* C.d2 := by
  have hv : ∀ v : ι2 → K,
      modelRow D S ψD L ⬝ᵥ (H.f.f2 *ᵥ v) = modelRow C S ψC L ⬝ᵥ v +
        H.functionalPrimitive L ⬝ᵥ (C.d2 *ᵥ v) := by
    intro v
    rw [modelRow_value, modelRow_value, H.functionalPrimitive_value]
    have hh := congrArg L (H.hom2 v)
    simp only [map_sub, map_add, hL, zero_add] at hh
    rw [← hh]
    ring
  ext j
  have h := hv (Pi.single j 1)
  rw [dotProduct_mulVec, dotProduct_mulVec] at h
  simpa [dotProduct, Pi.single_apply] using h

omit [Fintype ι3'] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3'] in
/-- The actual class discrepancy is a boundary in the finite target model.
Its primitive is recovered from that model's genuine comparison cone. -/
theorem ModelComparison.actual_class_discrepancy
    {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
    {S : GCx K} {ψC : GHom (quadCx C) S} {ψD : GHom (quadCx D) S}
    (H : ModelComparison C D S ψC ψD)
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD))
    (z : S.X 1) (zC : ι1 → K) (zD : ι1' → K)
    (hzC : C.d1 *ᵥ zC = 0) (hzD : D.d1 *ᵥ zD = 0)
    (bC bD : S.X 0) (hbC : ψC.f 1 1 rfl zC - z = S.d 0 1 rfl bC)
    (hbD : ψD.f 1 1 rfl zD - z = S.d 0 1 rfl bD) :
    ∃ b : ι0' → K, H.f.f1 *ᵥ zC = zD + D.d0 *ᵥ b := by
  have hc : D.d1 *ᵥ (H.f.f1 *ᵥ zC - zD) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, H.f.c1, ← mulVec_mulVec, hzC, mulVec_zero, hzD, sub_self]
  have hh := H.hom1 zC
  rw [hzC, map_zero, add_zero] at hh
  have he : ψD.f 1 1 rfl (H.f.f1 *ᵥ zC - zD) =
      S.d 0 1 rfl (bC - bD - H.h1 zC) := by
    rw [map_sub, map_sub, map_sub, ← hbC, ← hbD, ← hh]
    abel
  have hcone : (coneCx ψD).d 1 2 rfl
      (H.f.f1 *ᵥ zC - zD, bC - bD - H.h1 zC) = 0 := by
    apply Prod.ext
    · exact hc
    · change ψD.f 1 1 rfl (H.f.f1 *ᵥ zC - zD) - S.d 0 1 rfl (bC - bD - H.h1 zC) = 0
      rw [he, sub_self]
  obtain ⟨b, hb⟩ := (coneCx_acyclic_of_quasiIso ψD hD) 0 1 2 rfl rfl
    (H.f.f1 *ᵥ zC - zD, bC - bD - H.h1 zC) hcone
  have hf := congrArg Prod.fst hb
  refine ⟨b.1, ?_⟩
  change D.d0 *ᵥ b.1 = H.f.f1 *ᵥ zC - zD at hf
  rw [hf]
  abel

/-- Homotopy-aware comparison of the same actual class, actual functional
class and the original finite model bases.  The augmentation homotopies are
constructed from genuine cochain data, not from a scalar-coordinate equality. -/
theorem exists_actual_homotopy_comparison (C : FourCx K ι0 ι1 ι2 ι3)
    (D : FourCx K ι0' ι1' ι2' ι3') (S : GCx K)
    (ψC : GHom (quadCx C) S) (ψD : GHom (quadCx D) S)
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD))
    (z : S.X 1) (hz : S.d 1 2 rfl z = 0) (L : S.X 2 →ₗ[K] K)
    (hL : ∀ v, L (S.d 1 2 rfl v) = 0) :
    ∃ (zC : ι1 → K) (zD : ι1' → K) (bC bD : S.X 0),
      C.d1 *ᵥ zC = 0 ∧ D.d1 *ᵥ zD = 0 ∧
      ψC.f 1 1 rfl zC - z = S.d 0 1 rfl bC ∧
      ψD.f 1 1 rfl zD - z = S.d 0 1 rfl bD ∧
      Nonempty (HomotopyComparison C D zC (modelRow C S ψC L) zD (modelRow D S ψD L)) := by
  obtain ⟨zC, hzC, bC, hbC⟩ := actual_cycle_lift C S ψC hC z hz
  obtain ⟨zD, hzD, bD, hbD⟩ := actual_cycle_lift D S ψD hD z hz
  obtain ⟨H⟩ := exists_model_comparison C D S ψC ψD hD
  obtain ⟨b, hb⟩ := H.actual_class_discrepancy hD z zC zD hzC hzD bC bD hbC hbD
  exact ⟨zC, zD, bC, bD, hzC, hzD, hbC, hbD,
    ⟨{ f := H.f, classBoundary := b, functionalBoundary := H.functionalPrimitive L,
       class_map := hb, functional_map := H.actual_functional_discrepancy L hL }⟩⟩

/-- Fully constructed retained comparison of the same actual class and
functional, through two actual finite model maps.  The cone's nonvanishing
and the original-basis coordinate formula are conclusions, not inputs. -/
theorem exists_actual_retained_comparison (C : FourCx K ι0 ι1 ι2 ι3)
    (D : FourCx K ι0' ι1' ι2' ι3') (S : GCx K)
    (ψC : GHom (quadCx C) S) (ψD : GHom (quadCx D) S)
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD))
    (z : S.X 1) (hz : S.d 1 2 rfl z = 0) (L : S.X 2 →ₗ[K] K)
    (hL : ∀ v, L (S.d 1 2 rfl v) = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    ∃ (zC : ι1 → K) (lC : ι2 → K) (zD : ι1' → K) (lD : ι2' → K)
      (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
      (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0),
      (∃ bC : S.X 0, ψC.f 1 1 rfl zC - z = S.d 0 1 rfl bC) ∧
      (∃ bD : S.X 0, ψD.f 1 1 rfl zD - z = S.d 0 1 rfl bD) ∧
      (∀ v, lC ⬝ᵥ v = L (ψC.f 2 2 rfl v)) ∧
      (∀ v, lD ⬝ᵥ v = L (ψD.f 2 2 rfl v)) ∧
      ∃ H : HomotopyComparison C D zC lC zD lD,
        QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) ∧
        H.retainedFactor hzC hlC hzD hlD σC σD ≠ 0 ∧
        kmCoord C zC lC hzC hlC σC = H.retainedFactor hzC hlC hzD hlD σC σD *
          kmCoord D zD lD hzD hlD σD := by
  obtain ⟨zC, hzC, bC, hbC⟩ := actual_cycle_lift C S ψC hC z hz
  obtain ⟨zD, hzD, bD, hbD⟩ := actual_cycle_lift D S ψD hD z hz
  obtain ⟨M⟩ := exists_model_comparison C D S ψC ψD hD
  obtain ⟨b, hb⟩ := M.actual_class_discrepancy hD z zC zD hzC hzD bC bD hbC hbD
  let H : HomotopyComparison C D zC (modelRow C S ψC L) zD (modelRow D S ψD L) :=
    { f := M.f, classBoundary := b, functionalBoundary := M.functionalPrimitive L,
      class_map := hb, functional_map := M.actual_functional_discrepancy L hL }
  have hlC := modelRow_closed C S ψC L hL
  have hlD := modelRow_closed D S ψD L hL
  have hq : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) :=
    M.quasiIso hC hD
  have hn := H.aug_cone_torsion_ne_zero hzC hlC hzD hlD hq σC σD
  exact ⟨zC, modelRow C S ψC L, zD, modelRow D S ψD L, hzC, hlC, hzD, hlD,
    ⟨bC, hbC⟩, ⟨bD, hbD⟩, modelRow_value C S ψC L, modelRow_value D S ψD L,
    H, hq, H.retainedFactor_ne_zero hzC hlC hzD hlD σC σD hn,
    H.coordinate_formula_of_quasiIso hzC hlC hzD hlD hq σC σD⟩

end ActualClassAndFunctional

section AdjugateCoordinate

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Manuscript.RC.Central (IsClassFunctionalCoord)
open ZInQ.Contrib.RC53Assist.CoordLink (kmCoord_twoTerm_of_adjugate)

variable {K : Type} [Field K]

/-- The scalar is constructed from the same core cycle and functional, both
at rank-one and acyclic constituents.  No exact augmentation is required. -/
theorem exists_unique_adjugate_coordinate {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (z w : Fin (m + 1) → K)
    (hz : D *ᵥ z = 0) (hw : w ᵥ* D = 0) (hadj : D.adjugate ≠ 0) :
    ∃! u : K, IsClassFunctionalCoord D z w u := by
  obtain ⟨u, hu⟩ : ∃ u : K, IsClassFunctionalCoord D z w u := by
    by_cases hdet : D.det = 0
    · exact ZInQ.Manuscript.RC.Central.exists_isClassFunctionalCoord hdet hadj hz hw
    · exact ⟨0, ZInQ.Manuscript.RC.Central.isClassFunctionalCoord_zero_of_isUnit_det
        (isUnit_iff_ne_zero.mpr hdet) hz⟩
  exact ⟨u, hu, fun u' hu' => ZInQ.Manuscript.RC.Central.isClassFunctionalCoord_unique hadj hu' hu⟩

variable {ι0 ι1 ι2 ι3 : Type}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- Construct the actual adjugate scalar of a genuine two-term core and its
transport into the original retained determinant basis.  All classes and
functional rows are derived from the same supplied cochain class and functional.
The scalar identity in the original basis is a conclusion, not an input. -/
theorem exists_actual_adjugate_coordinate {m : ℕ} (C : FourCx K ι0 ι1 ι2 ι3)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hadj : D.adjugate ≠ 0)
    (S : GCx K) (ψC : GHom (quadCx C) S) (ψD : GHom (quadCx (twoTerm D)) S)
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD))
    (z : S.X 1) (hz : S.d 1 2 rfl z = 0) (L : S.X 2 →ₗ[K] K)
    (hL : ∀ v, L (S.d 1 2 rfl v) = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    ∃ (zC : ι1 → K) (lC : ι2 → K) (zD lD : Fin (m + 1) → K)
      (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
      (hzD : (twoTerm D).d1 *ᵥ zD = 0) (hlD : lD ᵥ* (twoTerm D).d1 = 0),
      (∃ bC : S.X 0, ψC.f 1 1 rfl zC - z = S.d 0 1 rfl bC) ∧
      (∃ bD : S.X 0, ψD.f 1 1 rfl zD - z = S.d 0 1 rfl bD) ∧
      (∀ v, lC ⬝ᵥ v = L (ψC.f 2 2 rfl v)) ∧
      (∀ v, lD ⬝ᵥ v = L (ψD.f 2 2 rfl v)) ∧
      ∃ (H : HomotopyComparison C (twoTerm D) zC lC zD lD) (u : K),
        IsClassFunctionalCoord D zD lD u ∧
        QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) ∧
        H.retainedFactor hzC hlC hzD hlD σC (σ₀ (m + 1)) ≠ 0 ∧
        kmCoord C zC lC hzC hlC σC = H.retainedFactor hzC hlC hzD hlD σC (σ₀ (m + 1)) * u := by
  obtain ⟨zC, lC, zD, lD, hzC, hlC, hzD, hlD, hbC, hbD, hvalC, hvalD, H, hq, hn, hcoord⟩ :=
    exists_actual_retained_comparison C (twoTerm D) S ψC ψD hC hD z hz L hL σC (σ₀ (m + 1))
  obtain ⟨u, hu, _⟩ := exists_unique_adjugate_coordinate D zD lD hzD hlD hadj
  have hkm := kmCoord_twoTerm_of_adjugate D zD lD u hzD hlD hadj hu
  exact ⟨zC, lC, zD, lD, hzC, hlC, hzD, hlD, hbC, hbD, hvalC, hvalD, H, u, hu, hq, hn,
    hcoord.trans (congrArg (H.retainedFactor hzC hlC hzD hlD σC (σ₀ (m + 1)) * ·) hkm)⟩

end AdjugateCoordinate

section GenuinePairedClass

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (coneCx_acyclic_of_quasiIso)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (pairedFun)
open ZInQ.Manuscript.RC.SelmerComplex

variable {R : Type} [Field R]

/-- The specified conjugate class has a closed lift through the actual
orthogonal comparison.  Its cochain boundary is retained explicitly. -/
theorem lift_conjugate_actual_class {A B T : GCx R} (j : GHom A T) (c : GHom B T)
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : B.X 1) (hz : B.d 1 2 rfl z = 0) :
    ∃ zperp : A.X 1, A.d 1 2 rfl zperp = 0 ∧ ∃ b : T.X 0,
      j.f 1 1 rfl zperp - c.f 1 1 rfl z = T.d 0 1 rfl b := by
  have hcz : T.d 1 2 rfl (c.f 1 1 rfl z) = 0 := by
    rw [← c.comm 1 2 1 2 rfl rfl rfl rfl z, hz, map_zero]
  have hc : (coneCx j).d 2 3 rfl ((0 : A.X 2), c.f 1 1 rfl z) = 0 := by
    apply Prod.ext
    · exact map_zero _
    · change j.f 2 2 rfl 0 - T.d 1 2 rfl (c.f 1 1 rfl z) = 0
      rw [map_zero, hcz, sub_self]
  obtain ⟨v, hv⟩ := (coneCx_acyclic_of_quasiIso j hj) 1 2 3 rfl rfl
    ((0 : A.X 2), c.f 1 1 rfl z) hc
  have h1 := congrArg Prod.fst hv
  have h2 := congrArg Prod.snd hv
  refine ⟨v.1, h1, v.2, ?_⟩
  change j.f 1 1 rfl v.1 - T.d 0 1 rfl v.2 = c.f 1 1 rfl z at h2
  rw [← h2]
  abel

/-- The traced cup functional of the lifted actual dual class is closed. -/
theorem cup_actual_functional_closed {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx P.resE).d 2 3 rfl v) = 0)
    (zperp : (selCx D).X 1) (hzperp : (selCx D).d 1 2 rfl zperp = 0)
    (v : (selCx D').X 1) :
    pairedFun P tr zperp ((selCx D').d 1 2 rfl v) = 0 := by
  have hl := selmerCupLeibniz_proof R D D' P 1 2 1 2 2 3 rfl rfl rfl rfl zperp v
  rw [hzperp] at hl
  erw [map_zero, LinearMap.zero_apply, zero_add, sgn_one, neg_smul, one_smul] at hl
  have h0 := htr (selCup P 1 1 2 rfl zperp v)
  rw [hl] at h0
  exact neg_eq_zero.mp ((map_neg tr _).symm.trans h0)

section Galois

variable (N : Type) [Field N] [NumberField N] (S₀ : Set (HeightOneSpectrum (𝓞 N)))
  {A B T : Type}
  [AddCommGroup A] [Module R A] [DistribMulAction (GKS N S₀) A] [SMulCommClass (GKS N S₀) R A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul R A] [ContinuousSMul (GKS N S₀) A]
  [AddCommGroup B] [Module R B] [DistribMulAction (GKS N S₀) B] [SMulCommClass (GKS N S₀) R B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul R B] [ContinuousSMul (GKS N S₀) B]
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS N S₀) T] [SMulCommClass (GKS N S₀) R T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul R T] [ContinuousSMul (GKS N S₀) T]
  (β : A →ₗ[R] B →ₗ[R] T)
  (hβ : ∀ (g : GKS N S₀) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun p : A × B => β p.1 p.2)
  (Δperp Δconj : GaloisLocalConditions N S₀ R A)
  (Δ : GaloisLocalConditions N S₀ R B)
  (I : IsotropyData R (GKS N S₀) (fun v : Places N S₀ => Gloc N v.1)
    (fun v => locMap N S₀ v.1) β hβ hβc Δperp Δ)

/-- The actual continuous-cochain pairing, with the specified local
orthogonality homotopies. -/
abbrev actualCupData :
    SelPairData (galoisSelData N S₀ R A Δperp) (galoisSelData N S₀ R B Δ) :=
  genuinePairData R (GKS N S₀) (fun v : Places N S₀ => Gloc N v.1)
    (fun v => locMap N S₀ v.1) β hβ hβc Δperp Δ I

/-- The construction uses the genuine Selmer cochains, the specified actual
class and conjugation map, and a lift through the actual orthogonal comparison.
Both model rows are the traced cup functional of that same lifted class.
Neither a relaxed scalar nor an original-coordinate identity is an input. -/
theorem exists_genuine_paired_model_comparison
    (j : GHom (selCx (galoisSelData N S₀ R A Δperp)) (selCx (galoisSelData N S₀ R A Δconj)))
    (c : GHom (selCx (galoisSelData N S₀ R B Δ)) (selCx (galoisSelData N S₀ R A Δconj)))
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : (selCx (galoisSelData N S₀ R B Δ)).X 1)
    (hz : (selCx (galoisSelData N S₀ R B Δ)).d 1 2 rfl z = 0)
    (tr : (coneCx (actualCupData N S₀ β hβ hβc Δperp Δ I).resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx (actualCupData N S₀ β hβ hβc Δperp Δ I).resE).d 2 3 rfl v) = 0)
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type}
    [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
    [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
    [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']
    (C : FourCx R ι0 ι1 ι2 ι3) (D : FourCx R ι0' ι1' ι2' ι3')
    (ψC : GHom (quadCx C) (selCx (galoisSelData N S₀ R B Δ)))
    (ψD : GHom (quadCx D) (selCx (galoisSelData N S₀ R B Δ)))
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD)) :
    ∃ (zperp : (selCx (galoisSelData N S₀ R A Δperp)).X 1)
      (bperp : (selCx (galoisSelData N S₀ R A Δconj)).X 0),
      (selCx (galoisSelData N S₀ R A Δperp)).d 1 2 rfl zperp = 0 ∧
      j.f 1 1 rfl zperp - c.f 1 1 rfl z =
        (selCx (galoisSelData N S₀ R A Δconj)).d 0 1 rfl bperp ∧
      ∃ (zC : ι1 → R) (zD : ι1' → R)
        (bC bD : (selCx (galoisSelData N S₀ R B Δ)).X 0),
        C.d1 *ᵥ zC = 0 ∧ D.d1 *ᵥ zD = 0 ∧
        ψC.f 1 1 rfl zC - z = (selCx (galoisSelData N S₀ R B Δ)).d 0 1 rfl bC ∧
        ψD.f 1 1 rfl zD - z = (selCx (galoisSelData N S₀ R B Δ)).d 0 1 rfl bD ∧
        Nonempty (HomotopyComparison C D zC
          (modelRow C _ ψC (pairedFun (actualCupData N S₀ β hβ hβc Δperp Δ I) tr zperp)) zD
          (modelRow D _ ψD (pairedFun (actualCupData N S₀ β hβ hβc Δperp Δ I) tr zperp))) := by
  obtain ⟨zperp, hzperp, bperp, hbperp⟩ := lift_conjugate_actual_class j c hj z hz
  let L := pairedFun (actualCupData N S₀ β hβ hβc Δperp Δ I) tr zperp
  have hL : ∀ v, L ((selCx (galoisSelData N S₀ R B Δ)).d 1 2 rfl v) = 0 :=
    cup_actual_functional_closed _ tr htr zperp hzperp
  exact ⟨zperp, bperp, hzperp, hbperp,
    exists_actual_homotopy_comparison C D _ ψC ψD hC hD z hz L hL⟩

end Galois
/-- The manuscript's pairing order: the degree-two cochain is paired on the
right with the lifted degree-one dual class. -/
def rightPairedFun {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R) (zperp : (selCx D').X 1) :
    (selCx D).X 2 →ₗ[R] R :=
  (traceComp (selPair P) tr 2 1 rfl).flip zperp

/-- The functional PD(-, zperp) is closed for the lifted same dual class. -/
theorem rightPairedFun_closed {D D' : SelData R} (P : SelPairData D D')
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx P.resE).d 2 3 rfl v) = 0)
    (zperp : (selCx D').X 1) (hzperp : (selCx D').d 1 2 rfl zperp = 0)
    (v : (selCx D).X 1) : rightPairedFun P tr zperp ((selCx D).d 1 2 rfl v) = 0 := by
  have hl := selmerCupLeibniz_proof R D D' P 1 2 1 2 2 3 rfl rfl rfl rfl v zperp
  rw [hzperp] at hl
  erw [map_zero, smul_zero, add_zero] at hl
  have h0 := htr (selCup P 1 1 2 rfl v zperp)
  rw [hl] at h0
  exact h0

section RightGalois

variable (N : Type) [Field N] [NumberField N] (S₀ : Set (HeightOneSpectrum (𝓞 N)))
  {A B T : Type}
  [AddCommGroup A] [Module R A] [DistribMulAction (GKS N S₀) A] [SMulCommClass (GKS N S₀) R A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul R A] [ContinuousSMul (GKS N S₀) A]
  [AddCommGroup B] [Module R B] [DistribMulAction (GKS N S₀) B] [SMulCommClass (GKS N S₀) R B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul R B] [ContinuousSMul (GKS N S₀) B]
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS N S₀) T] [SMulCommClass (GKS N S₀) R T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul R T] [ContinuousSMul (GKS N S₀) T]
  (β : A →ₗ[R] B →ₗ[R] T)
  (hβ : ∀ (g : GKS N S₀) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun p : A × B => β p.1 p.2)
  (Δ : GaloisLocalConditions N S₀ R A)
  (Δperp Δconj : GaloisLocalConditions N S₀ R B)
  (I : IsotropyData R (GKS N S₀) (fun v : Places N S₀ => Gloc N v.1)
    (fun v => locMap N S₀ v.1) β hβ hβc Δ Δperp)

/-- The genuine continuous-cochain cup pairing in the order PD(-, zperp). -/
abbrev actualRightCupData :
    SelPairData (galoisSelData N S₀ R A Δ) (galoisSelData N S₀ R B Δperp) :=
  genuinePairData R (GKS N S₀) (fun v : Places N S₀ => Gloc N v.1)
    (fun v => locMap N S₀ v.1) β hβ hβc Δ Δperp I

/-- Retained comparison constructed from genuine Selmer cochains and
PD(-, zperp), where zperp lifts the specified conjugate of the same actual
class.  The augmented cone and its basis factor are derived.  No relaxed
scalar, original-coordinate identity, or cone-basis identity is an input. -/
theorem exists_genuine_retained_PD_comparison
    (j : GHom (selCx (galoisSelData N S₀ R B Δperp)) (selCx (galoisSelData N S₀ R B Δconj)))
    (c : GHom (selCx (galoisSelData N S₀ R A Δ)) (selCx (galoisSelData N S₀ R B Δconj)))
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : (selCx (galoisSelData N S₀ R A Δ)).X 1)
    (hz : (selCx (galoisSelData N S₀ R A Δ)).d 1 2 rfl z = 0)
    (tr : (coneCx (actualRightCupData N S₀ β hβ hβc Δ Δperp I).resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx (actualRightCupData N S₀ β hβ hβc Δ Δperp I).resE).d 2 3 rfl v) = 0)
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type}
    [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
    [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
    [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']
    (C : FourCx R ι0 ι1 ι2 ι3) (D : FourCx R ι0' ι1' ι2' ι3')
    (ψC : GHom (quadCx C) (selCx (galoisSelData N S₀ R A Δ)))
    (ψD : GHom (quadCx D) (selCx (galoisSelData N S₀ R A Δ)))
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD))
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    ∃ (zperp : (selCx (galoisSelData N S₀ R B Δperp)).X 1)
      (bperp : (selCx (galoisSelData N S₀ R B Δconj)).X 0),
      (selCx (galoisSelData N S₀ R B Δperp)).d 1 2 rfl zperp = 0 ∧
      j.f 1 1 rfl zperp - c.f 1 1 rfl z =
        (selCx (galoisSelData N S₀ R B Δconj)).d 0 1 rfl bperp ∧
      ∃ (zC : ι1 → R) (lC : ι2 → R) (zD : ι1' → R) (lD : ι2' → R)
        (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
        (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0),
        (∃ bC : (selCx (galoisSelData N S₀ R A Δ)).X 0,
          ψC.f 1 1 rfl zC - z = (selCx (galoisSelData N S₀ R A Δ)).d 0 1 rfl bC) ∧
        (∃ bD : (selCx (galoisSelData N S₀ R A Δ)).X 0,
          ψD.f 1 1 rfl zD - z = (selCx (galoisSelData N S₀ R A Δ)).d 0 1 rfl bD) ∧
        (∀ v, lC ⬝ᵥ v = rightPairedFun (actualRightCupData N S₀ β hβ hβc Δ Δperp I) tr zperp
          (ψC.f 2 2 rfl v)) ∧
        (∀ v, lD ⬝ᵥ v = rightPairedFun (actualRightCupData N S₀ β hβ hβc Δ Δperp I) tr zperp
          (ψD.f 2 2 rfl v)) ∧
        ∃ H : HomotopyComparison C D zC lC zD lD,
          QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) ∧
          H.retainedFactor hzC hlC hzD hlD σC σD ≠ 0 ∧
          kmCoord C zC lC hzC hlC σC = H.retainedFactor hzC hlC hzD hlD σC σD *
            kmCoord D zD lD hzD hlD σD := by
  obtain ⟨zperp, hzperp, bperp, hbperp⟩ := lift_conjugate_actual_class j c hj z hz
  let L := rightPairedFun (actualRightCupData N S₀ β hβ hβc Δ Δperp I) tr zperp
  have hL : ∀ v, L ((selCx (galoisSelData N S₀ R A Δ)).d 1 2 rfl v) = 0 :=
    rightPairedFun_closed _ tr htr zperp hzperp
  exact ⟨zperp, bperp, hzperp, hbperp,
    exists_actual_retained_comparison C D _ ψC ψD hC hD z hz L hL σC σD⟩

/-- The relaxed scalar is reconstructed from the same genuine class,
PD-functional and actual two-term core, then expressed in the original
retained determinant basis by the computed cone factor.  Identifying this
construction with an independently supplied correction-family scalar remains
a separate arithmetic dictionary obligation. -/
theorem exists_genuine_adjugate_PD_coordinate
    (j : GHom (selCx (galoisSelData N S₀ R B Δperp)) (selCx (galoisSelData N S₀ R B Δconj)))
    (c : GHom (selCx (galoisSelData N S₀ R A Δ)) (selCx (galoisSelData N S₀ R B Δconj)))
    (hj : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC j))
    (z : (selCx (galoisSelData N S₀ R A Δ)).X 1)
    (hz : (selCx (galoisSelData N S₀ R A Δ)).d 1 2 rfl z = 0)
    (tr : (coneCx (actualRightCupData N S₀ β hβ hβc Δ Δperp I).resE).X 3 →ₗ[R] R)
    (htr : ∀ v, tr ((coneCx (actualRightCupData N S₀ β hβ hβc Δ Δperp I).resE).d 2 3 rfl v) = 0)
    {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
    [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] {m : ℕ}
    (C : FourCx R ι0 ι1 ι2 ι3) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hadj : D.adjugate ≠ 0)
    (ψC : GHom (quadCx C) (selCx (galoisSelData N S₀ R A Δ)))
    (ψD : GHom (quadCx (twoTerm D)) (selCx (galoisSelData N S₀ R A Δ)))
    (hC : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψC))
    (hD : QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC ψD))
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    ∃ (zperp : (selCx (galoisSelData N S₀ R B Δperp)).X 1)
      (bperp : (selCx (galoisSelData N S₀ R B Δconj)).X 0),
      (selCx (galoisSelData N S₀ R B Δperp)).d 1 2 rfl zperp = 0 ∧
      j.f 1 1 rfl zperp - c.f 1 1 rfl z =
        (selCx (galoisSelData N S₀ R B Δconj)).d 0 1 rfl bperp ∧
      ∃ (zC : ι1 → R) (lC : ι2 → R) (zD lD : Fin (m + 1) → R)
        (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
        (hzD : (twoTerm D).d1 *ᵥ zD = 0) (hlD : lD ᵥ* (twoTerm D).d1 = 0),
        (∃ bC : (selCx (galoisSelData N S₀ R A Δ)).X 0,
          ψC.f 1 1 rfl zC - z = (selCx (galoisSelData N S₀ R A Δ)).d 0 1 rfl bC) ∧
        (∃ bD : (selCx (galoisSelData N S₀ R A Δ)).X 0,
          ψD.f 1 1 rfl zD - z = (selCx (galoisSelData N S₀ R A Δ)).d 0 1 rfl bD) ∧
        (∀ v, lC ⬝ᵥ v = rightPairedFun (actualRightCupData N S₀ β hβ hβc Δ Δperp I) tr zperp
          (ψC.f 2 2 rfl v)) ∧
        (∀ v, lD ⬝ᵥ v = rightPairedFun (actualRightCupData N S₀ β hβ hβc Δ Δperp I) tr zperp
          (ψD.f 2 2 rfl v)) ∧
        ∃ (H : HomotopyComparison C (twoTerm D) zC lC zD lD) (u : R),
          ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D zD lD u ∧
          QuasiIso (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC (quadMap H.f)) ∧
          H.retainedFactor hzC hlC hzD hlD σC (σ₀ (m + 1)) ≠ 0 ∧
          kmCoord C zC lC hzC hlC σC = H.retainedFactor hzC hlC hzD hlD σC (σ₀ (m + 1)) * u := by
  obtain ⟨zperp, hzperp, bperp, hbperp⟩ := lift_conjugate_actual_class j c hj z hz
  let L := rightPairedFun (actualRightCupData N S₀ β hβ hβc Δ Δperp I) tr zperp
  have hL : ∀ v, L ((selCx (galoisSelData N S₀ R A Δ)).d 1 2 rfl v) = 0 :=
    rightPairedFun_closed _ tr htr zperp hzperp
  exact ⟨zperp, bperp, hzperp, hbperp,
    exists_actual_adjugate_coordinate C D hadj _ ψC ψD hC hD z hz L hL σC⟩

end RightGalois

end GenuinePairedClass

end ZInQ.Contrib.RC53Assist.CoordProvenance.Homotopy
