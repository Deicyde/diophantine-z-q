import ZInQKernel.Contrib.LocalSquareRoot.FiniteComplex

/-!
# Necessity of the finite cyclotomic obstruction, conditional on local KW

A locally constant absolute-Galois square root cuts out a finite abelian extension.
The actual `PkgI6.LocalKroneckerWeber` hypothesis puts that extension inside a finite
cyclotomic field. After adjoining the original character level, its character descends
through the actual normal restriction map. A finite involution with coordinates `(-1,1)`
is then lifted to the absolute Galois group. Its square is killed by the descended square
root, and its lower restriction is the exact original `tau_-1`.

No infinite involution, reciprocity map, or assumed square-root criterion is used.
-/

namespace ZInQ.Contrib.LocalSquareRoot

open GlueSqrtDisj

/-- Local KW is used only for the necessity direction, to control the finite field
cut out by an arbitrary locally constant square-root character. -/
theorem finite_obstruction_of_squareRoot (p : ℕ) [hp : Fact p.Prime]
    (hKW : PkgI6.LocalKroneckerWeber p)
    (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    (τ : Gal(muField p (p ^ k * m)/ℚ_[p]))
    (hτ : galToProd (p := p) (L := muField p (p ^ k * m)) k m τ = (-1, 1))
    (χ : Gal(muField p (p ^ k * m)/ℚ_[p]) →* ℂˣ)
    (φ : Field.absoluteGaloisGroup ℚ_[p] →* ℂˣ) (hφ : IsLocallyConstant φ)
    (hsq : ∀ g, φ g ^ 2 = χ (g.restrictNormal (muField p (p ^ k * m)))) :
    χ τ = 1 := by
  obtain ⟨M, hMfin, hMab, hMker⟩ := exists_finite_abelian_kernel ℚ_[p] φ hφ
  haveI : FiniteDimensional ℚ_[p] M := hMfin
  haveI : IsAbelianGalois ℚ_[p] M := hMab
  obtain ⟨n, hn, hMn⟩ := hKW M inferInstance inferInstance
  have hb0 : n * (p ^ k * m) ≠ 0 :=
    mul_ne_zero hn.ne' (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m))
  obtain ⟨k', m', hpm', hb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0 p hp.out.one_lt.ne'
  have hm'0 : m' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hb
    exact hb0 hb
  haveI : NeZero m' := ⟨hm'0⟩
  have hcop' : p.Coprime m' := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm'
  have hdiv : p ^ k * m ∣ p ^ k' * m' := by
    rw [← hb]
    exact ⟨n, mul_comm _ _⟩
  have hndiv : n ∣ p ^ k' * m' := by
    rw [← hb]
    exact ⟨p ^ k * m, rfl⟩
  obtain ⟨hk, hm⟩ := normalized_level_dvd p k m k' m' hcop hcop' hdiv
  let K := muField p (p ^ k * m)
  let L := muField p (p ^ k' * m')
  have hML : M ≤ L := hMn.trans (muField_mono p hndiv)
  have hKL : K ≤ L := muField_mono p hdiv
  letI : Algebra K L := fieldInclusionAlgebra K L hKL
  letI : IsScalarTower ℚ_[p] K L := fieldInclusion_scalarTower_base K L hKL
  letI : IsScalarTower K L (PadicAlgCl p) := fieldInclusion_scalarTower_top K L hKL
  have hker : L.fixingSubgroup ≤ φ.ker :=
    (IntermediateField.fixingSubgroup_le hML).trans hMker
  let φL : Gal(L/ℚ_[p]) →* ℂˣ := descendCharacter ℚ_[p] L φ hker
  obtain ⟨σ, hσ⟩ := exists_tau (p := p) (L := L) k' m' hcop'
  have hσ2 : σ ^ 2 = 1 := tau_square_eq_one p L k' m' hcop' σ hσ
  have hres : σ.restrictNormal K = τ := by
    apply galToProd_injective (p := p) (L := K) k m hcop
    exact (tau_restrict_acts p K L k m k' m' hk hm σ hσ).trans hτ.symm
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p) σ
  change g.restrictNormal L = σ at hg
  have hgK : g.restrictNormal K = τ := by
    rw [← restrictNormal_trans (K := K) (L := L) g, hg, hres]
  have hφLg : φL σ = φ g := by
    have h := descendCharacter_apply ℚ_[p] L φ hker g
    change φL (g.restrictNormal L) = φ g at h
    rwa [hg] at h
  have hφL2 : φL σ ^ 2 = 1 := by
    rw [← map_pow, hσ2, map_one]
  calc
    χ τ = φ g ^ 2 := by rw [← hgK]; exact (hsq g).symm
    _ = φL σ ^ 2 := by rw [hφLg]
    _ = 1 := hφL2

end ZInQ.Contrib.LocalSquareRoot
