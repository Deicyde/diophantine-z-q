import ZInQKernel.Contrib.OneProof.C8TwistFinite.TensorEigen

/-! # C8 without Conrad, global part: the twist has finite image

Let `ψ : G_ℚ → ℚ̄_p^×` be a continuous character whose restriction to `G_{ℚ_p}` takes values in a
finite `E/ℚ_p` and is Hodge–Tate of weight `0` there (`PureHT'`). Then `ψ` has finite image, given
the class field theory statement `NoRamUnits` (a character of `G_ℚ` trivial on the Artin symbols of
the units of `ℤ_p` has finite image; in the tree it is
`C8Conrad.finiteOfLocAlgTrivialQNoRam_of_dicts` at `k = 0`). Proof (diophantine_zq.tex L758-766,
with Conrad's local algebraicity replaced by the global argument):

1. `φ := unitChar (ψ ∘ decomp)` is the continuous character of `ℤ_p^×` with
   `ψ(decomp σ) = φ(χ σ)` on representatives of Artin symbols of units (`LocalUnits`).
2. `β := ψ · (φ ∘ χ_ℚ)⁻¹`, with `χ_ℚ` the cyclotomic character of `G_ℚ`, is a continuous
   character trivial on those representatives (`χ_ℚ ∘ decomp = χ`, Tau Ceti's naturality of the
   cyclotomic character), so `β^d = 1` for some `d > 0` (`NoRamUnits`).
3. Then `ψ_E^d = (φ ∘ χ)^d` on `G_{ℚ_p}` is trivial on the kernel of `χ`, so Tate's theorem
   gives `ψ_E^N = 1` (`TensorEigen`).
4. Hence `φ^{Nd} = 1` (`χ` is onto `ℤ_p^×`) and `ψ^{Nd} = β^{Nd} (φ ∘ χ_ℚ)^{Nd} = 1`. -/

noncomputable section

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.C8TwistFinite

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-! ## The cyclotomic character of `G_ℚ` and its restriction along `decomp` -/

/-- The `p`-adic cyclotomic character of `G_ℚ`. -/
def chiQ : PkgI4.GQ →* ℤ_[p]ˣ :=
  (cyclotomicCharacter PkgI4.Qbar p).comp (MulSemiringAction.toRingAut PkgI4.GQ PkgI4.Qbar)

theorem continuous_chiQ : Continuous (chiQ p) :=
  cyclotomicCharacter.continuous p ℚ PkgI4.Qbar

/-- The embedding `ℚ̄ → ℚ̄_p` that `PkgI4.decomp` restricts along. -/
def embQ : PkgI4.Qbar →+* PadicAlgCl p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

theorem embQ_decomp (σ : PkgI4.GQp p) (x : PkgI4.Qbar) :
    embQ p (PkgI4.decomp p σ x) = σ (embQ p x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- `χ_ℚ ∘ decomp = χ` (Tau Ceti's naturality of the cyclotomic character). -/
theorem chiQ_decomp (σ : PkgI4.GQp p) : chiQ p (PkgI4.decomp p σ) = cycL p σ := by
  have h := TauCeti.cyclotomicCharacter_eq_of_injective p (f := embQ p) (embQ p).injective
    (g := (PkgI4.decomp p σ).toRingEquiv) (h := σ.toRingEquiv)
    (fun x => (embQ_decomp p σ x).symm)
    (fun _ i => HasEnoughRootsOfUnity.exists_isPrimitiveRoot PkgI4.Qbar (p ^ i))
  exact h.symm

/-! ## The splitting `ψ = β · (φ ∘ χ_ℚ)` -/

section Split

variable (ψ : PkgI4.GaloisChar p)

/-- `ψ ∘ decomp`. -/
def locChar : PkgI4.GQp p →* (PadicAlgCl p)ˣ := ψ.toHom.comp (PkgI4.decomp p)

theorem continuous_locChar : Continuous (locChar p ψ) :=
  ψ.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

/-- The unit part `φ` of `ψ ∘ decomp`. -/
def phi : ℤ_[p]ˣ →* (PadicAlgCl p)ˣ := unitChar p (locChar p ψ) (continuous_locChar p ψ)

theorem continuous_phi : Continuous (phi p ψ) :=
  continuous_unitChar p (locChar p ψ) (continuous_locChar p ψ)

/-- `β = ψ · (φ ∘ χ_ℚ)⁻¹`. -/
def beta : PkgI4.GaloisChar p where
  toHom := ψ.toHom * ((phi p ψ).comp (chiQ p))⁻¹
  continuous_toHom := by
    change Continuous fun g => ψ.toHom g * ((phi p ψ) (chiQ p g))⁻¹
    exact ψ.continuous_toHom.mul ((continuous_phi p ψ).comp (continuous_chiQ p)).inv

theorem beta_apply (g : PkgI4.GQ) :
    (beta p ψ).toHom g = ψ.toHom g * ((phi p ψ) (chiQ p g))⁻¹ := rfl

theorem toHom_eq_beta_mul (g : PkgI4.GQ) :
    ψ.toHom g = (beta p ψ).toHom g * (phi p ψ) (chiQ p g) := by
  rw [beta_apply, inv_mul_cancel_right]

/-- `β` is trivial on the representatives of the Artin symbols of units. -/
theorem beta_decomp_eq_one {u : ℤ_[p]ˣ} {σ : PkgI4.GQp p}
    (hσ : IsArtinLift' p σ (unitsQp' p u)) : (beta p ψ).toHom (PkgI4.decomp p σ) = 1 := by
  rw [beta_apply, chiQ_decomp, phi,
    unitChar_cycL_of_isArtinLift p (locChar p ψ) (continuous_locChar p ψ) hσ]
  exact mul_inv_cancel _

end Split

/-! ## Finiteness -/

/-- **Class field theory over `ℚ` at `p`, unit form**: a continuous character of `G_ℚ` trivial on
the representatives of the Artin symbols of the units of `ℤ_p` has finite image (the case `k = 0`
of `C8Conrad.FiniteOfLocAlgTrivialQNoRam`, which the tree proves). -/
def NoRamUnits : Prop :=
  ∀ β : PkgI4.GaloisChar p, (∀ (u : ℤ_[p]ˣ) (σ : PkgI4.GQp p),
    IsArtinLift' p σ (unitsQp' p u) → β.toHom (PkgI4.decomp p σ) = 1) →
    (Set.range β.toHom).Finite

theorem exists_pow_eq_one_of_finite {G : Type*} [Group G] (β : G →* (PadicAlgCl p)ˣ)
    (h : (Set.range β).Finite) : ∃ d : ℕ, 0 < d ∧ ∀ g, β g ^ d = 1 := by
  have : Finite β.range := by
    rw [← MonoidHom.coe_range] at h
    exact h.to_subtype
  refine ⟨Nat.card β.range, Nat.card_pos, fun g => ?_⟩
  have hx := pow_card_eq_one' (G := β.range) (x := ⟨β g, g, rfl⟩)
  exact congrArg Subtype.val hx

/-- **The twist has finite image**: from the Hodge–Tate splitting of weight `0` of its local
restriction and `NoRamUnits`. -/
theorem range_finite_of_pureHT (hNR : NoRamUnits p) (ψ : PkgI4.GaloisChar p)
    {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (j : E →+* PadicAlgCl p) (ψE : PkgI4.GQp p →* Eˣ)
    (hlift : ∀ σ, j ((ψE σ : Eˣ) : E) =
      ((ψ.toHom (PkgI4.decomp p σ) : (PadicAlgCl p)ˣ) : PadicAlgCl p))
    (hP : PureHT' p ψE (-0)) : (Set.range ψ.toHom).Finite := by
  -- powers of `ψ_E` and of `ψ ∘ decomp` vanish together
  have hj : ∀ σ (n : ℕ), ψE σ ^ n = 1 ↔ ψ.toHom (PkgI4.decomp p σ) ^ n = 1 := by
    intro σ n
    rw [Units.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_one, Units.val_one, ← hlift, ← map_pow]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      apply j.injective
      rw [h, map_one]
  -- step 2: `β` has finite order `d`
  obtain ⟨d, hd0, hd⟩ := exists_pow_eq_one_of_finite p (beta p ψ).toHom
    (hNR (beta p ψ) fun u σ hσ => beta_decomp_eq_one p ψ hσ)
  -- step 3: Tate's theorem
  obtain ⟨t, ht0, ht⟩ := exists_eigen_of_pureHT p ψE hP
  have hd' : ∀ σ, cycL p σ = 1 → (ψE⁻¹) σ ^ d = 1 := by
    intro σ hσ
    rw [MonoidHom.inv_apply, inv_pow, inv_eq_one, hj, toHom_eq_beta_mul, chiQ_decomp, hσ,
      map_one, mul_one]
    exact hd _
  obtain ⟨N, hN0, hN⟩ := pow_eq_one_of_eigen p (ψE⁻¹) t ht0 (fun σ => by
    rw [ht σ, MonoidHom.inv_apply]) hd0 hd'
  have hψN : ∀ σ, ψ.toHom (PkgI4.decomp p σ) ^ N = 1 := by
    intro σ
    rw [← hj]
    have h := hN σ
    rwa [MonoidHom.inv_apply, inv_pow, inv_eq_one] at h
  -- step 4: `φ^{Nd} = 1`, then `ψ^{Nd} = 1`
  have hφ : ∀ u, (phi p ψ) u ^ (N * d) = 1 := by
    intro u
    obtain ⟨σ, rfl⟩ := cycL_surjective p u
    have h := toHom_eq_beta_mul p ψ (PkgI4.decomp p σ)
    rw [chiQ_decomp] at h
    have h' : (phi p ψ) (cycL p σ) =
        ((beta p ψ).toHom (PkgI4.decomp p σ))⁻¹ * ψ.toHom (PkgI4.decomp p σ) := by
      rw [h, inv_mul_cancel_left]
    rw [h', mul_pow, inv_pow, mul_comm N d, pow_mul, hd, one_pow, inv_one, one_mul, mul_comm,
      pow_mul, hψN, one_pow]
  have hψ : ∀ g, ψ.toHom g ^ (N * d) = 1 := by
    intro g
    rw [toHom_eq_beta_mul p ψ g, mul_pow, hφ, mul_one, mul_comm N d, pow_mul, hd, one_pow]
  have hNd : NeZero (N * d) := ⟨(Nat.mul_pos hN0 hd0).ne'⟩
  have hfinR : (rootsOfUnity (N * d) (PadicAlgCl p) : Set (PadicAlgCl p)ˣ).Finite :=
    Set.finite_coe_iff.mp (inferInstance : Finite (rootsOfUnity (N * d) (PadicAlgCl p)))
  refine hfinR.subset ?_
  rintro _ ⟨g, rfl⟩
  change _ ∈ rootsOfUnity (N * d) (PadicAlgCl p)
  rw [mem_rootsOfUnity]
  exact hψ g

end ZInQ.Contrib.C8TwistFinite
