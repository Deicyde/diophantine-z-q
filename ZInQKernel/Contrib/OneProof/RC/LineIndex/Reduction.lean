import ZInQKernel.Contrib.OneProof.RC.Eichler.Indexed
import ZInQKernel.Contrib.OneProof.RC.LineIndex.Matrix

/-!
# Reduction of a locally principal right ideal

Tex 9040–9042. The integral-to-local reduction argument is proved here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LineIndex

open Eichler Module

variable {a b : ℚ} {R : Order a b} {I : RightIdeal R}
variable {p : ℕ} [Fact p.Prime]

/-- The good-prime splitting, retaining its extension to the ambient algebra. -/
structure Split (R : Order a b) (p : ℕ) [Fact p.Prime] where
  alg : Bp p a b ≃ₐ[ℚ_[p]] Mat ℚ_[p]
  order_eq : alg '' (R.completion p : Set (Bp p a b)) = Set.range (matrixCast p)

/-- The ambient version of `IsEichler.local_split` used to transport local generators. -/
theorem nonempty_split {ell N : ℕ} (h : IsEichler ell N R) (hp : ¬ p ∣ N * ell) :
    Nonempty (Split R p) := by
  have hN : ¬ p ∣ N := fun h' => hp (dvd_mul_of_dvd_left h' ell)
  have he : p ≠ ell := by
    intro h'
    apply hp
    rw [h']
    exact dvd_mul_left ell N
  obtain ⟨f, hf⟩ := h.split_profile p he
  exact ⟨⟨f, by simpa only [Nat.factorization_eq_zero_of_not_dvd hN, standardLevel_zero] using hf⟩⟩

/-- Matrices over the residue field are obtained by reducing each entry. -/
def reduce (p : ℕ) [Fact p.Prime] : Mat ℤ_[p] →+* Mat (ZMod p) :=
  (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix

theorem reduce_surjective : Function.Surjective (reduce p) := by
  intro M
  refine ⟨fun i j => (M i j).val, ?_⟩
  ext i j
  change PadicInt.toZMod ((M i j).val : ℤ_[p]) = M i j
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem padic_reduce_eq_zero {x : ℤ_[p]} :
    PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem reduce_smul (r : ℤ_[p]) (A : Mat ℤ_[p]) :
    reduce p (r • A) = PadicInt.toZMod r • reduce p A := by
  ext i j
  exact map_mul PadicInt.toZMod r (A i j)

theorem reduce_eq_zero {A : Mat ℤ_[p]} :
    reduce p A = 0 ↔ ∃ B : Mat ℤ_[p], A = (p : ℤ_[p]) • B := by
  constructor
  · intro h
    have hdiv (i j : Fin 2) : (p : ℤ_[p]) ∣ A i j :=
      padic_reduce_eq_zero.mp (congrFun (congrFun h i) j)
    choose B hB using hdiv
    exact ⟨B, Matrix.ext hB⟩
  · rintro ⟨B, rfl⟩
    rw [reduce_smul, map_natCast, ZMod.natCast_self, zero_smul]

theorem card_residueMatrices : Nat.card (Mat (ZMod p)) = p^4 := by
  change Nat.card (Fin 2 → Fin 2 → ZMod p) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod p), ZMod.card,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, ← pow_mul]

/-- A local generator and a simultaneous matrix chart for the order and right ideal. -/
structure Chart (I : RightIdeal R) (p : ℕ) [Fact p.Prime] where
  split : Split R p
  gen : (Bp p a b)ˣ
  ideal_eq : (localLattice p I.lattice : Set (Bp p a b)) =
    (fun x : Bp p a b => (gen : Bp p a b) * x) '' (R.completion p : Set (Bp p a b))

namespace Split

variable (S : Split R p)

/-- Pull integral matrices back into the local algebra. -/
def embed : Mat ℤ_[p] →+* Bp p a b :=
  S.alg.symm.toRingHom.comp (matrixCast p)

theorem embed_injective : Function.Injective S.embed :=
  S.alg.symm.injective.comp
    (Matrix.map_injective (show Function.Injective (algebraMap ℤ_[p] ℚ_[p]) from Subtype.val_injective))

theorem range_embed : Set.range S.embed = (R.completion p : Set (Bp p a b)) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    have h : S.alg (S.embed A) ∈ S.alg '' (R.completion p : Set (Bp p a b)) := by
      rw [S.order_eq]
      exact ⟨A, S.alg.apply_symm_apply _ |>.symm⟩
    obtain ⟨y, hy, he⟩ := h
    exact S.alg.injective he ▸ hy
  · intro hx
    have h := Set.mem_image_of_mem S.alg hx
    rw [S.order_eq] at h
    obtain ⟨A, hA⟩ := h
    exact ⟨A, S.alg.injective (by simpa [embed] using hA)⟩

theorem embed_smul (r : ℤ_[p]) (A : Mat ℤ_[p]) :
    S.embed (r • A) = r • S.embed A := by
  change S.alg.symm (matrixCast p (r • A)) = _
  have h : matrixCast p (r • A) = (r : ℚ_[p]) • matrixCast p A := by
    ext i j
    exact map_mul (algebraMap ℤ_[p] ℚ_[p]) r (A i j)
  rw [h, map_smul]
  rfl

end Split

namespace Chart

variable (C : Chart I p)

def embed : Mat ℤ_[p] →ₗ[ℤ_[p]] Bp p a b where
  toFun A := (C.gen : Bp p a b) * C.split.embed A
  map_add' A B := by rw [map_add, mul_add]
  map_smul' r A := by rw [C.split.embed_smul, mul_smul_comm]; rfl

theorem embed_injective : Function.Injective C.embed :=
  (C.gen.mulLeftLinearEquiv ℚ_[p] _).injective.comp C.split.embed_injective

theorem range_embed : LinearMap.range C.embed = localLattice p I.lattice := by
  ext x
  change (∃ A, C.embed A = x) ↔ x ∈ (localLattice p I.lattice : Set (Bp p a b))
  rw [C.ideal_eq, ← C.split.range_embed]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, rfl⟩

/-- Integral matrices are coordinates on the completed ideal. -/
def localEquiv : Mat ℤ_[p] ≃ₗ[ℤ_[p]] localLattice p I.lattice :=
  (LinearEquiv.ofInjective C.embed C.embed_injective).trans
    (LinearEquiv.ofEq _ _ C.range_embed)

theorem localEquiv_val (A : Mat ℤ_[p]) : (C.localEquiv A).val = C.embed A := rfl

/-- The diagonal map into the local span. -/
def diagonal (L : Submodule ℤ (B a b)) : L →+ localLattice p L where
  toFun x := ⟨toLocal p x.val, Submodule.subset_span (Set.mem_image_of_mem _ x.prop)⟩
  map_zero' := Subtype.ext (map_zero (toLocal p))
  map_add' x y := Subtype.ext (map_add (toLocal p) x.val y.val)

/-- Reduction on the local span in the generator's coordinates. -/
def localResidue : localLattice p I.lattice →+ Mat (ZMod p) :=
  (reduce p).toAddMonoidHom.comp C.localEquiv.symm.toAddEquiv.toAddMonoidHom

/-- The integral reduction map on the right ideal. -/
def residue : I.lattice →+ Mat (ZMod p) :=
  C.localResidue.comp (diagonal I.lattice)

theorem localResidue_smul (r : ℤ_[p]) (x : localLattice p I.lattice) :
    C.localResidue (r • x) = PadicInt.toZMod r • C.localResidue x := by
  change reduce p (C.localEquiv.symm (r • x)) = _
  rw [map_smul, reduce_smul]
  rfl

/-- The completed span adds no residue classes: scalars modulo `p` lift to integers. -/
theorem residue_surjective : Function.Surjective C.residue := by
  have lift (x : Bp p a b) (hx : x ∈ localLattice p I.lattice) :
      ∃ y : I.lattice, C.residue y = C.localResidue ⟨x, hx⟩ := by
    induction hx using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨⟨y, hy⟩, rfl⟩
    | zero =>
      refine ⟨0, ?_⟩
      change C.residue 0 = C.localResidue 0
      rw [map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      obtain ⟨x', hx'⟩ := ihx
      obtain ⟨y', hy'⟩ := ihy
      exact ⟨x' + y', by rw [map_add, hx', hy', ← map_add]; rfl⟩
    | smul r x hx ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective (PadicInt.toZMod r)
      refine ⟨n • y, ?_⟩
      change C.residue (n • y) = C.localResidue (r • (⟨x, hx⟩ : localLattice p I.lattice))
      rw [C.localResidue_smul, ← hy, map_zsmul, ← hn, Int.cast_smul_eq_zsmul]
  intro A
  obtain ⟨M, hM⟩ := reduce_surjective A
  obtain ⟨y, hy⟩ := lift _ (C.localEquiv M).prop
  exact ⟨y, hy.trans (by simpa [localResidue] using hM)⟩

/-- The additive subgroup `pI` as a subgroup of the type of elements of `I`. -/
def scalarSubgroup (I : RightIdeal R) (hp : p ≠ 0) : AddSubgroup I.lattice :=
  (I.translate (RightIdeal.scalarUnit p hp)).lattice.toAddSubgroup.comap I.lattice.subtype.toAddMonoidHom

omit [Fact p.Prime] in
theorem mem_scalarSubgroup (hp : p ≠ 0) (x : I.lattice) :
    x ∈ scalarSubgroup I hp ↔ ∃ y : I.lattice, x = p • y := by
  change (∃ y ∈ I.lattice, _ = x.val) ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change (↑(RightIdeal.scalarUnit (a := a) (b := b) p hp) : B a b) * y = x.val at he
    rw [RightIdeal.scalar_mul] at he
    exact he.symm
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, y.prop, RightIdeal.scalar_mul _ _ _⟩

omit [Fact p.Prime] in
theorem scalarSubgroup_index (hp : p ≠ 0) :
    (scalarSubgroup I hp).index = p^4 :=
  I.relIndex_scalar p hp

/-- The reduction kernel is exactly `pI`. -/
theorem ker_residue (hp : p ≠ 0) : C.residue.ker = scalarSubgroup I hp := by
  have hle : scalarSubgroup I hp ≤ C.residue.ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_scalarSubgroup hp x).mp hx
    rw [AddMonoidHom.mem_ker, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p),
      ZMod.natCast_self, zero_smul]
  have hc : C.residue.ker.index = p^4 := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr C.residue_surjective]
    rw [Nat.card_congr AddSubgroup.topEquiv.toEquiv, card_residueMatrices]
  have h := AddSubgroup.relIndex_mul_index hle
  rw [hc, scalarSubgroup_index] at h
  apply le_antisymm _ hle
  apply AddSubgroup.relIndex_eq_one.mp
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (h.trans (one_mul _).symm)

/-- As an additive quotient, `I/pI` is the matrix space over the residue field. -/
def quotientEquiv (hp : p ≠ 0) : (I.lattice ⧸ scalarSubgroup I hp) ≃+ Mat (ZMod p) :=
  (QuotientAddGroup.quotientAddEquivOfEq (C.ker_residue hp).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective C.residue C.residue_surjective)

end Chart

end ZInQ.Manuscript.RC.LineIndex

namespace ZInQ.Manuscript.RC.LineIndex

open Eichler

variable {a b : ℚ} {R : Order a b} {I : RightIdeal R}
variable {p : ℕ} [Fact p.Prime]

namespace Split

variable (S : Split R p)

/-- The good-prime local ring equivalence, in the chosen ambient chart. -/
def orderEquiv : Mat ℤ_[p] ≃+* R.completion p :=
  RingEquiv.ofBijective (S.embed.codRestrict (R.completion p).toSubring
    (fun A => show S.embed A ∈ (R.completion p : Set (Bp p a b)) from
      S.range_embed ▸ Set.mem_range_self A))
    ⟨fun _ _ h => S.embed_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨A, hA⟩ : x.val ∈ Set.range S.embed := S.range_embed.symm ▸ x.prop
        exact ⟨A, Subtype.ext hA⟩⟩

def orderDiagonal : R.ring →+* R.completion p :=
  ((toLocal p).comp R.ring.subtype).codRestrict (R.completion p).toSubring
    (fun r => Algebra.subset_adjoin (Set.mem_image_of_mem (toLocal p) r.prop))

/-- Reduction of the order as a ring. -/
def orderResidue : R.ring →+* Mat (ZMod p) :=
  (reduce p).comp (S.orderEquiv.symm.toRingHom.comp (orderDiagonal (R := R)))

private def selfChart : Chart (RightIdeal.self R) p :=
  ⟨S, 1, by
    change (localLattice p R.lattice : Set (Bp p a b)) =
      (fun x : Bp p a b => ((1 : (Bp p a b)ˣ) : Bp p a b) * x) ''
        (R.completion p : Set (Bp p a b))
    rw [← R.completion_toSubmodule]
    simp
    rfl⟩

theorem self_residue (r : R.ring) :
    S.selfChart.residue r = S.orderResidue r := by
  change reduce p (S.selfChart.localEquiv.symm (Chart.diagonal R.lattice r)) =
    reduce p (S.orderEquiv.symm (orderDiagonal r))
  congr 1
  apply S.selfChart.embed_injective
  have h₁ := congrArg Subtype.val (S.selfChart.localEquiv.apply_symm_apply (Chart.diagonal R.lattice r))
  have h₂ := congrArg Subtype.val (S.orderEquiv.apply_symm_apply (orderDiagonal (p := p) r))
  change S.selfChart.embed _ = toLocal p r.val at h₁
  change S.embed _ = toLocal p r.val at h₂
  exact h₁.trans (by simpa [Chart.embed, selfChart] using h₂.symm)

theorem orderResidue_surjective : Function.Surjective S.orderResidue := by
  intro A
  obtain ⟨r, hr⟩ := S.selfChart.residue_surjective A
  exact ⟨r, (S.self_residue r).symm.trans hr⟩

/-- The ring kernel is (pR), so the quotient ring is the full matrix ring. -/
theorem orderResidue_eq_zero (hp : p ≠ 0) (r : R.ring) :
    S.orderResidue r = 0 ↔ ∃ s : R.ring, r = p • s := by
  rw [← S.self_residue]
  let t : (RightIdeal.self R).lattice := ⟨r.val, r.prop⟩
  change t ∈ S.selfChart.residue.ker ↔ _
  rw [S.selfChart.ker_residue hp]
  exact Chart.mem_scalarSubgroup hp t

/-- The quotient by the reduction kernel, which is `pR` by `orderResidue_eq_zero`. -/
def orderQuotientEquiv : (R.ring ⧸ RingHom.ker S.orderResidue) ≃+* Mat (ZMod p) :=
  RingHom.quotientKerEquivOfSurjective S.orderResidue_surjective

end Split

namespace Chart

variable (C : Chart I p)

/-- The residue identification respects the right action, in the same ring chart. -/
theorem residue_mul (x : I.lattice) (r : R.ring) :
    C.residue ⟨x.val * r.val, I.mul_mem x.prop r.prop⟩ =
      C.residue x * C.split.orderResidue r := by
  let y : I.lattice := ⟨x.val * r.val, I.mul_mem x.prop r.prop⟩
  let A := C.localEquiv.symm (diagonal I.lattice x)
  let B := C.split.orderEquiv.symm (Split.orderDiagonal (p := p) r)
  change reduce p (C.localEquiv.symm (diagonal I.lattice y)) = reduce p A * reduce p B
  rw [← map_mul]
  congr 1
  apply C.embed_injective
  have h (z : I.lattice) : C.embed (C.localEquiv.symm (diagonal I.lattice z)) = toLocal p z.val :=
    congrArg Subtype.val (C.localEquiv.apply_symm_apply (diagonal I.lattice z))
  have hB : C.split.embed B = toLocal p r.val :=
    congrArg Subtype.val (C.split.orderEquiv.apply_symm_apply (Split.orderDiagonal (p := p) r))
  rw [h]
  change toLocal p (x.val * r.val) = (C.gen : Bp p a b) * C.split.embed (A * B)
  rw [map_mul, map_mul, ← mul_assoc, hB]
  exact congrArg (· * toLocal p r.val) (h x).symm

/-- Multiplication of representatives descends to the regular right module.
Together with `Split.orderResidue_eq_zero`, this identifies `I/pI` as free of rank one over
`R/pR`, with generator the inverse image of the identity matrix. -/
theorem quotientEquiv_mul (hp : p ≠ 0) (x : I.lattice) (r : R.ring) :
    C.quotientEquiv hp (QuotientAddGroup.mk (⟨x.val * r.val, I.mul_mem x.prop r.prop⟩ :
      I.lattice)) =
    C.quotientEquiv hp (QuotientAddGroup.mk x) * C.split.orderResidue r := by
  simp only [quotientEquiv, AddEquiv.trans_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  exact C.residue_mul x r

/-- The right module `I/pI` is the regular module, expressed as a left module over
the opposite of `R/pR`. The transported action agrees with multiplication of representatives
by `quotientEquiv_mul` and the quotient ring identification `Split.orderQuotientEquiv`. -/
def quotientRightRegular (hp : p ≠ 0) :
    let A := R.ring ⧸ RingHom.ker C.split.orderResidue
    let E := ((C.quotientEquiv hp).trans C.split.orderQuotientEquiv.symm.toAddEquiv).trans
      MulOpposite.opAddEquiv
    letI := E.module Aᵐᵒᵖ
    (I.lattice ⧸ scalarSubgroup I hp) ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ :=
  (((C.quotientEquiv hp).trans C.split.orderQuotientEquiv.symm.toAddEquiv).trans
    MulOpposite.opAddEquiv).linearEquiv _

end Chart


end ZInQ.Manuscript.RC.LineIndex
