import ZInQKernel.Contrib.OneProof.RC.Adelic.Patch

/-!
# Local-to-global patching of fractional lattices
On-the-spot (c) for tex 8464–8468. Clear a common denominator, then apply
the prime-power patching lemma for sublattices.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler Module QuaternionAlgebra

variable {a b : ℚ}

theorem isLattice_map {A K V : Type*} [CommRing A] [CommRing K] [Algebra A K]
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    {L : Submodule A V} (hL : L.IsLattice K) (f : V ≃ₗ[K] V) :
    (L.map (f.restrictScalars A).toLinearMap).IsLattice K := by
  refine ⟨hL.fg.map _, ?_⟩
  rw [Submodule.map_coe]
  change Submodule.span K (f.toLinearMap '' (L : Set V)) = ⊤
  rw [← Submodule.map_span, hL.span_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr f.surjective]

theorem localLattice_map (p : Prime) (L : Submodule ℤ (B a b))
    (f : B a b →ₗ[ℤ] B a b) (g : Bp p.val a b →ₗ[ℤ_[p.val]] Bp p.val a b)
    (h : ∀ x, toLocal p.val (f x) = g (toLocal p.val x)) :
    localLattice p.val (L.map f) = (localLattice p.val L).map g := by
  rw [localLattice, localLattice, Submodule.map_coe, Submodule.map_span, Set.image_image, Set.image_image]
  congr 2
  exact funext h

theorem localLattice_full (p : Prime) {L : Submodule ℤ (B a b)} (hL : FullLattice L) :
    (localLattice p.val L).IsLattice ℚ_[p.val] := by
  let e := hL.ratBasis (basisOneIJK a 0 b)
  rw [← hL.span_ratBasis (basisOneIJK a 0 b), localLattice_basis]
  exact ⟨Submodule.fg_span (Set.finite_range _), by
    rw [Submodule.span_span_of_tower, Basis.span_eq]⟩

/-- For two full local lattices, a sufficiently high power of the local prime
takes the first into the second. -/
theorem local_pow_into (p : Prime) {L M : Submodule ℤ_[p.val] (Bp p.val a b)}
    (hL : L.IsLattice ℚ_[p.val]) (hM : M.IsLattice ℚ_[p.val]) :
    ∃ n : ℕ, ∀ x ∈ L, (p.val : ℤ_[p.val]) ^ n • x ∈ M := by
  classical
  let _ := hM
  let c := Module.Free.chooseBasis ℤ_[p.val] M
  let e := c.extendOfIsLattice ℚ_[p.val]
  have he : Submodule.span ℤ_[p.val] (Set.range e) = M := by
    have heq : (e : _ → _) = M.subtype ∘ c := funext (Basis.extendOfIsLattice_apply _ _)
    rw [heq]
    rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]
  obtain ⟨s, hs, hLs⟩ := Submodule.fg_def.mp hL.fg
  let _ := hs.to_subtype
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ_[p.val]) (fun t : s × Module.Free.ChooseBasisIndex ℤ_[p.val] M =>
      e.repr t.1.val t.2)
  have hdz : (d : ℤ_[p.val]) ≠ 0 := nonZeroDivisors.ne_zero d.prop
  refine ⟨(d : ℤ_[p.val]).valuation, fun x hx => ?_⟩
  have hsmul : (d : ℤ_[p.val]) • x ∈ M := by
    rw [← hLs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [← he]
      apply (e.mem_span_iff_repr_mem ℤ_[p.val] _).mpr
      intro i
      obtain ⟨z, hz⟩ := hd (⟨y, hy⟩, i)
      refine ⟨z, ?_⟩
      rw [← IsScalarTower.algebraMap_smul ℚ_[p.val], map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact hz
    | zero => simp
    | add y z _ _ hy hz => simpa only [smul_add] using M.add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact M.smul_mem _ hy
  have ht := M.smul_mem (↑(PadicInt.unitCoeff hdz)⁻¹ : ℤ_[p.val]) hsmul
  have hmul : (↑(PadicInt.unitCoeff hdz)⁻¹ : ℤ_[p.val]) * d.val =
      (p.val : ℤ_[p.val]) ^ (d.val : ℤ_[p.val]).valuation := by
    calc
      _ = (↑(PadicInt.unitCoeff hdz)⁻¹ : ℤ_[p.val]) *
          ((PadicInt.unitCoeff hdz : ℤ_[p.val]) * (p.val : ℤ_[p.val]) ^ d.val.valuation) :=
        congrArg ((↑(PadicInt.unitCoeff hdz)⁻¹ : ℤ_[p.val]) * ·) (PadicInt.unitCoeff_spec hdz)
      _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rwa [smul_smul, hmul] at ht

private def natScale (m : ℕ) {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] :
    V →ₗ[R] V :=
  m • LinearMap.id

private theorem natScale_apply (m : ℕ) {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (x : V) : natScale (R := R) m x = m • x := rfl

set_option maxHeartbeats 2000000 in
/-- Arbitrary full local lattices which differ from a fixed completion only
at finitely many places are exactly the completions of their rational intersection. -/
theorem patch {L : Submodule ℤ (B a b)} (hL : FullLattice L)
    (A : (p : Prime) → Submodule ℤ_[p.val] (Bp p.val a b))
    (hA : ∀ p, (A p).IsLattice ℚ_[p.val])
    (hs : {p : Prime | A p ≠ localLattice p.val L}.Finite) :
    FullLattice (intersection A) ∧ ∀ p, localLattice p.val (intersection A) = A p := by
  classical
  let s := hs.toFinset
  choose k hk using fun p => local_pow_into p (hA p) (localLattice_full p hL)
  let m : ℕ := ∏ p ∈ s, p.val ^ k p
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.prop.ne_zero
  let C (p : Prime) := (A p).map (natScale m)
  have hmU (p : Prime) (hp : p ∉ s) : IsUnit (m : ℤ_[p.val]) := by
    apply nat_isUnit
    intro hd
    change p.val ∣ ∏ q ∈ s, q.val ^ k q at hd
    rw [p.prop.prime.dvd_finsetProd_iff] at hd
    obtain ⟨q, hq, hd⟩ := hd
    have he : p = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.prop q.prop).mp
      (p.prop.dvd_of_dvd_pow hd))
    exact hp (he.symm ▸ hq)
  have hCeq (p : Prime) (hp : p ∉ s) : C p = localLattice p.val L := by
    have he : A p = localLattice p.val L := by simpa [s] using hp
    obtain ⟨u, hu⟩ := hmU p hp
    unfold C
    rw [he]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (localLattice p.val L).toAddSubmonoid.nsmul_mem hx m
    · intro x hx
      refine ⟨(↑u⁻¹ : ℤ_[p.val]) • x, (localLattice p.val L).smul_mem _ hx, ?_⟩
      rw [natScale_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p.val], ← hu,
        smul_smul, Units.mul_inv, one_smul]
  have hCle (p : Prime) : C p ≤ localLattice p.val L := by
    by_cases hp : p ∈ s
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun q : Prime => q.val ^ k q) hp
      rw [natScale_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p.val], show m = p.val ^ k p * r from hr,
        Nat.cast_mul, Nat.cast_pow,
        mul_comm, mul_smul]
      exact (localLattice p.val L).smul_mem _ (hk p x hx)
    · exact (hCeq p hp).le
  have hCf (p : Prime) : (C p).IsLattice ℚ_[p.val] := by
    let f := LinearEquiv.smulOfNeZero ℚ_[p.val] (Bp p.val a b) (m : ℚ_[p.val])
      (Nat.cast_ne_zero.mpr hm)
    have he : (f.restrictScalars ℤ_[p.val]).toLinearMap = natScale m := by
      apply LinearMap.ext
      intro x
      change (m : ℚ_[p.val]) • x = m • x
      exact Nat.cast_smul_eq_nsmul ℚ_[p.val] m x
    rw [show C p = (A p).map (f.restrictScalars ℤ_[p.val]).toLinearMap by rw [he]]
    exact isLattice_map (hA p) f
  choose n hn using fun p => local_pow_into p (localLattice_full p hL) (hCf p)
  let d (p : Prime) := if p ∈ s then n p else 0
  have hpatch := patch_inside hL C s d (fun p hp => ite_eq_right hp) hCle (by
    intro p x hx
    by_cases hp : p ∈ s
    · simpa only [d, ite_eq_left hp] using hn p x hx
    · simpa only [d, ite_eq_right hp, pow_zero, one_smul, hCeq p hp] using hx)
  let f := LinearEquiv.smulOfNeZero ℚ (B a b) (m : ℚ) (Nat.cast_ne_zero.mpr hm)
  have f_eq (x : B a b) : f x = m • x := Nat.cast_smul_eq_nsmul ℚ m x
  have injective_nsmul (p : Prime) : Function.Injective (fun x : Bp p.val a b => m • x) := by
    let g := LinearEquiv.smulOfNeZero ℚ_[p.val] (Bp p.val a b) (m : ℚ_[p.val])
      (Nat.cast_ne_zero.mpr hm)
    intro x y h
    apply g.injective
    change (m : ℚ_[p.val]) • x = (m : ℚ_[p.val]) • y
    simpa only [Nat.cast_smul_eq_nsmul] using h
  have hf : (intersection A).map (f.restrictScalars ℤ).toLinearMap = intersection C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ p
      refine ⟨toLocal p.val y, hy p, ?_⟩
      change m • toLocal p.val y = toLocal p.val (f y)
      rw [f_eq, map_nsmul]
    · intro hx
      refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
      intro p
      obtain ⟨y, hy, he⟩ := hx p
      have hfy : m • toLocal p.val (f.symm x) = toLocal p.val x := by
        rw [← map_nsmul, ← f_eq, LinearEquiv.apply_symm_apply]
      exact (injective_nsmul p (hfy.trans he.symm)).symm ▸ hy
  constructor
  · have hf' := isLattice_map hpatch.1 f.symm
    have hid : (f.symm.restrictScalars ℤ).toLinearMap.comp
        (f.restrictScalars ℤ).toLinearMap = (LinearMap.id : B a b →ₗ[ℤ] B a b) := by
      apply LinearMap.ext
      exact f.symm_apply_apply
    rwa [← hf, ← Submodule.map_comp, hid, Submodule.map_id] at hf'
  · intro p
    have he := hpatch.2 p
    rw [← hf, localLattice_map p _ _ (natScale m) (fun x => by
      change toLocal p.val (f x) = m • toLocal p.val x
      rw [f_eq, map_nsmul])] at he
    apply le_antisymm
    · exact localLattice_intersection_le A p
    · intro x hx
      have hmX : m • x ∈ C p := ⟨x, hx, rfl⟩
      rw [← he] at hmX
      obtain ⟨y, hy, hxy⟩ := hmX
      exact injective_nsmul p hxy ▸ hy

#print axioms isLattice_map
#print axioms localLattice_map
#print axioms localLattice_full
#print axioms local_pow_into
#print axioms natScale_apply
#print axioms patch

end ZInQ.Manuscript.RC.Adelic
