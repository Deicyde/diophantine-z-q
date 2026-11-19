import ZInQKernel.Contrib.OneProof.RC.Eichler.Local

/-!
# Rational lattice coordinates at every prime
The lattice correspondence behind tex 8464–8468, proved here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler Module QuaternionAlgebra

abbrev Prime := {p : ℕ // p.Prime}

instance (p : Prime) : Fact p.val.Prime := ⟨p.property⟩

variable {a b : ℚ}

/-- The rational basis, transported by the same change-of-basis matrix over the local field. -/
def localCoordinates (p : Prime) (e : Basis (Fin 4) ℚ (B a b)) :
    Bp p.val a b ≃ₗ[ℚ_[p.val]] (Fin 4 → ℚ_[p.val]) := by
  let d := (linearEquivTuple a 0 b).symm.trans e.equivFun
  let M : Matrix (Fin 4) (Fin 4) ℚ := LinearMap.toMatrix' d.toLinearMap
  let P : Matrix (Fin 4) (Fin 4) ℚ := LinearMap.toMatrix' d.symm.toLinearMap
  have hMP : M * P = 1 := by
    rw [← LinearMap.toMatrix'_mul]
    have h : d.toLinearMap * d.symm.toLinearMap = 1 := by ext x i; simp
    rw [h, LinearMap.toMatrix'_one]
  have hPM : P * M = 1 := by
    rw [← LinearMap.toMatrix'_mul]
    have h : d.symm.toLinearMap * d.toLinearMap = 1 := by ext x i; simp
    rw [h, LinearMap.toMatrix'_one]
  let f : Matrix (Fin 4) (Fin 4) ℚ →+* Matrix (Fin 4) (Fin 4) ℚ_[p.val] :=
    (algebraMap ℚ ℚ_[p.val]).mapMatrix
  exact (linearEquivTuple (a : ℚ_[p.val]) 0 (b : ℚ_[p.val])).trans
    (Matrix.toLin'OfInv (by rw [← map_mul, hPM, map_one] : f P * f M = 1)
      (by rw [← map_mul, hMP, map_one] : f M * f P = 1))

theorem localCoordinates_toLocal (p : Prime) (e : Basis (Fin 4) ℚ (B a b)) (x : B a b) :
    localCoordinates p e (toLocal p.val x) = fun i => (e.repr x i : ℚ_[p.val]) := by
  let d := (linearEquivTuple a 0 b).symm.trans e.equivFun
  let M : Matrix (Fin 4) (Fin 4) ℚ := LinearMap.toMatrix' d.toLinearMap
  have hv : linearEquivTuple (a : ℚ_[p.val]) 0 (b : ℚ_[p.val]) (toLocal p.val x) =
      (algebraMap ℚ ℚ_[p.val]) ∘ linearEquivTuple a 0 b x := by
    funext i
    fin_cases i <;> rfl
  change Matrix.mulVec (M.map (algebraMap ℚ ℚ_[p.val]))
    (linearEquivTuple (a : ℚ_[p.val]) 0 (b : ℚ_[p.val]) (toLocal p.val x)) = _
  rw [hv]
  have he : Matrix.mulVec M (linearEquivTuple a 0 b x) = e.equivFun x := by
    change Matrix.toLin' M (linearEquivTuple a 0 b x) = _
    rw [Matrix.toLin'_toMatrix']
    simp [d]
  funext i
  rw [← RingHom.map_mulVec, he]
  rfl

/-- Completion commutes with taking integral spans on a rational basis. -/
theorem localLattice_basis (p : Prime) (e : Basis (Fin 4) ℚ (B a b)) :
    localLattice p.val (Submodule.span ℤ (Set.range e)) =
      Submodule.span ℤ_[p.val] (Set.range (Basis.ofEquivFun (localCoordinates p e))) := by
  let f : B a b →ₗ[ℤ] Bp p.val a b :=
    { toFun := toLocal p.val, map_add' := map_add _, map_smul' := map_zsmul _ }
  change Submodule.span ℤ_[p.val] (f '' (Submodule.span ℤ (Set.range e) : Set _)) = _
  rw [← Submodule.map_coe, ← Submodule.span_image, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext i
  apply (localCoordinates p e).injective
  rw [Function.comp_apply, show f (e i) = toLocal p.val (e i) from rfl,
    localCoordinates_toLocal]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply, Basis.repr_self]
  ext j
  simp [Finsupp.single_apply, Pi.single_apply, apply_ite, eq_comm]

theorem mem_localLattice_basis (p : Prime) (e : Basis (Fin 4) ℚ (B a b)) (x : Bp p.val a b) :
    x ∈ localLattice p.val (Submodule.span ℤ (Set.range e)) ↔
      ∀ i, ∃ t : ℤ_[p.val], (t : ℚ_[p.val]) = localCoordinates p e x i := by
  rw [localLattice_basis]
  exact (Basis.ofEquivFun (localCoordinates p e)).mem_span_iff_repr_mem ℤ_[p.val] x

/-- A rational number integral at every prime is an integer. -/
theorem rat_integral_of_local (x : ℚ)
    (hx : ∀ p : Prime, ∃ t : ℤ_[p.val], (t : ℚ_[p.val]) = (x : ℚ_[p.val])) :
    ∃ t : ℤ, (t : ℚ) = x := by
  by_cases h : x.den = 1
  · exact ⟨x.num, by simpa [h] using x.num_div_den⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
  let q : Prime := ⟨p, hp⟩
  let _ : Fact q.val.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hx q
  have hv := PadicInt.valuation_coe_nonneg (x := t)
  rw [ht, Padic.valuation_ratCast] at hv
  have hden : 0 < padicValNat p x.den :=
    (padicValNat_dvd_iff_le_of_ne_one hp.ne_one x.den_ne_zero).mp (by simpa using hd : p ^ 1 ∣ x.den)
  have hnum := (Rat.num_or_den_zero_padicVal x hp).resolve_right (ne_of_gt hden)
  change 0 ≤ padicValRat p x at hv
  rw [padicValRat_def, hnum] at hv
  omega

/-- A full rational lattice is exactly the intersection of its local completions. -/
theorem mem_iff_all_local {L : Submodule ℤ (B a b)} (hL : FullLattice L) (x : B a b) :
    x ∈ L ↔ ∀ p : Prime, toLocal p.val x ∈ localLattice p.val L := by
  constructor
  · intro hx p
    exact Submodule.subset_span (Set.mem_image_of_mem _ hx)
  · intro hx
    let e := hL.ratBasis (basisOneIJK a 0 b)
    have he : Submodule.span ℤ (Set.range e) = L := hL.span_ratBasis _
    rw [← he] at hx ⊢
    apply (e.mem_span_iff_repr_mem ℤ x).mpr
    intro i
    apply rat_integral_of_local
    intro p
    have hp := (mem_localLattice_basis p e (toLocal p.val x)).mp (hx p) i
    rwa [localCoordinates_toLocal] at hp


end ZInQ.Manuscript.RC.Adelic
