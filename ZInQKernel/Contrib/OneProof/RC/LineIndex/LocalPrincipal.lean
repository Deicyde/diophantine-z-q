import ZInQKernel.Contrib.OneProof.RC.LineIndex.Reduction

/-!
# Lifting the column spaces

Tex 9040–9042. The completion of an integral preimage and its local generators are
on-the-spot (c). In the two slope charts the generators have determinant `p`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LineIndex

open Eichler

variable {a b : ℚ} {R : Order a b} {I : RightIdeal R}
variable {p : ℕ} [Fact p.Prime]

/-- The two columns of this matrix are a basis of the integral preimage of the line. -/
def basisMatrix (p : ℕ) [Fact p.Prime] : Option (ZMod p) → Mat ℤ_[p]
  | none => !![(p : ℤ_[p]), 0; 0, 1]
  | some t => !![1, 0; (t.val : ℤ_[p]), (p : ℤ_[p])]

theorem basisMatrix_det (L : Option (ZMod p)) : (basisMatrix p L).det = p := by
  cases L <;> simp [basisMatrix, Matrix.det_fin_two_of]

private theorem reduce_slope (t : ZMod p) : PadicInt.toZMod (t.val : ℤ_[p]) = t := by
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- The single linear condition on the residue of a column. -/
def columnEquation (p : ℕ) [Fact p.Prime] (L : Option (ZMod p)) :
    Vec ℤ_[p] →+ ZMod p where
  toFun v := match L with
    | none => PadicInt.toZMod (v 0)
    | some t => PadicInt.toZMod (v 1) - t * PadicInt.toZMod (v 0)
  map_zero' := by cases L <;> simp
  map_add' v w := by
    cases L <;> simp only [Pi.add_apply, map_add, mul_add]
    ring

/-- The index-`p` column lattice is the inverse image of the specified line. -/
theorem mem_columnLattice (L : Option (ZMod p)) (v : Vec ℤ_[p]) :
    v ∈ (columnEquation p L).ker ↔ (fun i => PadicInt.toZMod (v i)) ∈ line L := by
  rw [AddMonoidHom.mem_ker, mem_line_iff]
  cases L <;> simp [columnEquation, sub_eq_zero]

theorem columnLattice_index (L : Option (ZMod p)) : (columnEquation p L).ker.index = p := by
  have hs : Function.Surjective (columnEquation p L) := by
    intro x
    cases L with
    | none => exact ⟨![(x.val : ℤ_[p]), 0], reduce_slope x⟩
    | some t =>
      refine ⟨![0, (x.val : ℤ_[p])], ?_⟩
      change PadicInt.toZMod (x.val : ℤ_[p]) - t * PadicInt.toZMod 0 = x
      simp
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs]
  rw [Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The integral preimage consists precisely of matrices in this principal right ideal. -/
theorem reduce_mem_columns_iff (L : Option (ZMod p)) (A : Mat ℤ_[p]) :
    reduce p A ∈ columns (line L) ↔ ∃ B : Mat ℤ_[p], A = basisMatrix p L * B := by
  cases L with
  | none =>
    have hm (B : Mat ℤ_[p]) (j : Fin 2) :
        (basisMatrix p none * B) 0 j = (p : ℤ_[p]) * B 0 j ∧
          (basisMatrix p none * B) 1 j = B 1 j := by
      constructor <;> simp [basisMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    change (∀ j, (fun i => reduce p A i j) ∈ line none) ↔ _
    simp only [mem_line_iff]
    constructor
    · intro h
      have h' (j : Fin 2) : (p : ℤ_[p]) ∣ A 0 j := padic_reduce_eq_zero.mp (h j)
      choose v hv using h'
      let B : Mat ℤ_[p] := fun i j => if i = 0 then v j else A 1 j
      refine ⟨B, Matrix.ext fun i j => ?_⟩
      fin_cases i
      · change A 0 j = (basisMatrix p none * B) 0 j
        rw [(hm B j).1]
        simpa [B] using hv j
      · change A 1 j = (basisMatrix p none * B) 1 j
        rw [(hm B j).2]
        simp [B]
    · rintro ⟨B, rfl⟩ j
      change PadicInt.toZMod ((basisMatrix p none * B) 0 j) = 0
      rw [(hm B j).1, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  | some t =>
    have hm (B : Mat ℤ_[p]) (j : Fin 2) :
        (basisMatrix p (some t) * B) 0 j = B 0 j ∧
          (basisMatrix p (some t) * B) 1 j = (t.val : ℤ_[p]) * B 0 j + (p : ℤ_[p]) * B 1 j := by
      constructor <;> simp [basisMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    change (∀ j, (fun i => reduce p A i j) ∈ line (some t)) ↔ _
    simp only [mem_line_iff]
    constructor
    · intro h
      have h' (j : Fin 2) : (p : ℤ_[p]) ∣ A 1 j - (t.val : ℤ_[p]) * A 0 j := by
        apply padic_reduce_eq_zero.mp
        rw [map_sub, map_mul, reduce_slope, sub_eq_zero]
        exact h j
      choose v hv using h'
      let B : Mat ℤ_[p] := fun i j => if i = 0 then A 0 j else v j
      refine ⟨B, Matrix.ext fun i j => ?_⟩
      fin_cases i
      · change A 0 j = (basisMatrix p (some t) * B) 0 j
        rw [(hm B j).1]
        simp [B]
      · change A 1 j = (basisMatrix p (some t) * B) 1 j
        rw [(hm B j).2]
        simpa [B] using sub_eq_iff_eq_add'.mp (hv j)
    · rintro ⟨B, rfl⟩ j
      change PadicInt.toZMod ((basisMatrix p (some t) * B) 1 j) =
        t * PadicInt.toZMod ((basisMatrix p (some t) * B) 0 j)
      rw [(hm B j).1, (hm B j).2, map_add, map_mul, map_mul, reduce_slope, map_natCast,
        ZMod.natCast_self, zero_mul, add_zero]

theorem basisMatrix_isUnit (L : Option (ZMod p)) : IsUnit (matrixCast p (basisMatrix p L)) := by
  rw [Matrix.isUnit_iff_isUnit_det, matrixCast, ← RingHom.map_det, basisMatrix_det, map_natCast,
    isUnit_iff_ne_zero]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private theorem localLattice_mono {q : ℕ} [Fact q.Prime] {T U : Submodule ℤ (B a b)}
    (h : T ≤ U) : localLattice q T ≤ localLattice q U :=
  Submodule.span_mono (Set.image_mono h)

omit [Fact p.Prime] in
/-- If the integral lattice contains `pI`, its local span contains
`p` times every element of the local span of `I`. -/
theorem smul_mem_localLattice {q : ℕ} [Fact q.Prime] {J : Submodule ℤ (B a b)}
    (hp : p ≠ 0) (h : (I.translate (RightIdeal.scalarUnit p hp)).lattice ≤ J)
    {x : Bp q a b} (hx : x ∈ localLattice q I.lattice) :
    (p : ℤ_[q]) • x ∈ localLattice q J := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : p • z ∈ J := h ⟨z, hz, RightIdeal.scalar_mul _ _ _⟩
    have ht := Submodule.subset_span (R := ℤ_[q])
      (Set.mem_image_of_mem (toLocal q) hz')
    rw [map_nsmul, Nat.cast_smul_eq_nsmul] at *
    exact ht
  | zero => simp
  | add x y _ _ hx hy => simpa only [smul_add] using (localLattice q J).add_mem hx hy
  | smul r y _ hy =>
    rw [smul_comm]
    exact (localLattice q J).smul_mem r hy

/-- The local spans agree away from the prime of the modification. -/
theorem localLattice_eq_away {J : Submodule ℤ (B a b)} (hp : p ≠ 0)
    (h₁ : (I.translate (RightIdeal.scalarUnit p hp)).lattice ≤ J) (h₂ : J ≤ I.lattice)
    (q : ℕ) [Fact q.Prime] (hq : q ≠ p) : localLattice q J = localLattice q I.lattice := by
  refine le_antisymm (localLattice_mono h₂) fun x hx => ?_
  have hu : IsUnit (p : ℤ_[q]) := by
    by_contra h
    have hn : (p : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] :=
      (IsLocalRing.mem_maximalIdeal _).mpr h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at hn
    exact hq (((Nat.dvd_prime (Fact.out : p.Prime)).mp hn).resolve_left
      (Fact.out : q.Prime).ne_one)
  obtain ⟨u, hu⟩ := hu
  have hg := (localLattice q J).smul_mem (↑u⁻¹ : ℤ_[q]) (smul_mem_localLattice hp h₁ hx)
  simpa [← hu, smul_smul] using hg

namespace Chart

variable (C : Chart I p)

set_option maxHeartbeats 500000 in
/-- Reducing the local span of an integral preimage gives the same column condition,
and that condition cuts out the entire local span. -/
theorem localLattice_preimage {J : Submodule ℤ (B a b)} (hp : p ≠ 0)
    (h₁ : (I.translate (RightIdeal.scalarUnit p hp)).lattice ≤ J) (h₂ : J ≤ I.lattice)
    (S : Submodule (ZMod p) (Mat (ZMod p)))
    (hJ : ∀ x : I.lattice, x.val ∈ J ↔ C.residue x ∈ S) (A : Mat ℤ_[p]) :
    C.embed A ∈ localLattice p J ↔ reduce p A ∈ S := by
  have hmono := localLattice_mono (q := p) h₂
  have hlocal (x : Bp p a b) (hx : x ∈ localLattice p J) :
      C.localResidue ⟨x, hmono hx⟩ ∈ S := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      exact (hJ ⟨z, h₂ hz⟩).mp hz
    | zero =>
      change C.localResidue 0 ∈ S
      rw [C.localResidue.map_zero]
      exact S.zero_mem
    | add x y hxJ hyJ hx hy =>
      let x' : localLattice p I.lattice := ⟨x, hmono hxJ⟩
      let y' : localLattice p I.lattice := ⟨y, hmono hyJ⟩
      change C.localResidue (x' + y') ∈ S
      rw [C.localResidue.map_add]
      exact S.add_mem hx hy
    | smul r y hyJ hy =>
      let y' : localLattice p I.lattice := ⟨y, hmono hyJ⟩
      change C.localResidue (r • y') ∈ S
      rw [C.localResidue_smul]
      exact S.smul_mem _ hy
  have hres : C.localResidue (C.localEquiv A) = reduce p A := by simp [localResidue]
  constructor
  · intro hA
    rw [← hres]
    exact hlocal _ hA
  · intro hA
    obtain ⟨x, hx⟩ := C.residue_surjective (reduce p A)
    have hxJ : x.val ∈ J := (hJ x).mpr (hx ▸ hA)
    have hxloc : toLocal p x.val ∈ localLattice p J :=
      Submodule.subset_span (Set.mem_image_of_mem _ hxJ)
    let D := C.localEquiv.symm (diagonal I.lattice x)
    have hD : C.embed D = toLocal p x.val :=
      congrArg Subtype.val (C.localEquiv.apply_symm_apply (diagonal I.lattice x))
    have h : reduce p (A - D) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hx.symm
    obtain ⟨B, hB⟩ := reduce_eq_zero.mp h
    have hdiff : C.embed A - toLocal p x.val = (p : ℤ_[p]) • C.embed B := by
      rw [← hD, ← map_sub, hB, map_smul]
    have hpB := smul_mem_localLattice hp h₁ (C.localEquiv B).prop
    rw [C.localEquiv_val, ← hdiff] at hpB
    exact ((localLattice p J).sub_mem_iff_left hxloc).mp hpB

/-- The integral preimage of any column line is locally principal at `p`. -/
theorem localPrincipal_at {J : Submodule ℤ (B a b)} (hp : p ≠ 0)
    (h₁ : (I.translate (RightIdeal.scalarUnit p hp)).lattice ≤ J) (h₂ : J ≤ I.lattice)
    (L : Option (ZMod p))
    (hJ : ∀ x : I.lattice, x.val ∈ J ↔ C.residue x ∈ columns (line L)) :
    ∃ u : (Bp p a b)ˣ, (localLattice p J : Set (Bp p a b)) =
      (fun x : Bp p a b => (u : Bp p a b) * x) '' (R.completion p : Set (Bp p a b)) := by
  obtain ⟨v, hv⟩ := (basisMatrix_isUnit L).map C.split.alg.symm.toRingHom
  change (v : Bp p a b) = C.split.embed (basisMatrix p L) at hv
  refine ⟨C.gen * v, ?_⟩
  ext x
  rw [← C.split.range_embed]
  constructor
  · intro hx
    have hxI : x ∈ LinearMap.range C.embed := C.range_embed.symm ▸ localLattice_mono h₂ hx
    obtain ⟨A, rfl⟩ := hxI
    obtain ⟨B, rfl⟩ := (reduce_mem_columns_iff L A).mp
      ((C.localLattice_preimage hp h₁ h₂ _ hJ A).mp hx)
    refine ⟨_, ⟨B, rfl⟩, ?_⟩
    change ((C.gen : Bp p a b) * (v : Bp p a b)) * C.split.embed B =
      (C.gen : Bp p a b) * C.split.embed (basisMatrix p L * B)
    rw [map_mul, hv, mul_assoc]
  · rintro ⟨_, ⟨B, rfl⟩, rfl⟩
    have he : (↑(C.gen * v) : Bp p a b) * C.split.embed B =
        C.embed (basisMatrix p L * B) := by
      change ((C.gen : Bp p a b) * (v : Bp p a b)) * C.split.embed B =
        (C.gen : Bp p a b) * C.split.embed (basisMatrix p L * B)
      rw [map_mul, hv, mul_assoc]
    change (↑(C.gen * v) : Bp p a b) * C.split.embed B ∈ localLattice p J
    rw [he, C.localLattice_preimage hp h₁ h₂ _ hJ, reduce_mem_columns_iff]
    exact ⟨B, rfl⟩

end Chart

#print axioms basisMatrix_det
#print axioms reduce_slope
#print axioms mem_columnLattice
#print axioms columnLattice_index
#print axioms reduce_mem_columns_iff
#print axioms basisMatrix_isUnit
#print axioms localLattice_mono
#print axioms smul_mem_localLattice
#print axioms localLattice_eq_away
#print axioms Chart.localLattice_preimage
#print axioms Chart.localPrincipal_at

end ZInQ.Manuscript.RC.LineIndex
