import ZInQKernel.Contrib.LocalSquareRoot.Criterion

/-!
# Local T30 statement, endpoint, and axiom readback

This is an author-side compile/readback check, not independent acceptance or the parent
project's full kernel replay. The first example spells out the exact frozen T30 body,
with only the actual T16(a) premise prepended. Endpoint examples exercise `N = 1`,
unramified `k = 0`, and the dyadic level `p = 2, k = 2`.
-/

open GlueDescent.B2Q ZInQ.Contrib.LocalSquareRoot

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local notation "p₂" => (Subtype.mk 2 Nat.prime_two : Nat.Primes)

-- Exact expanded frozen T30 statement: no hidden target, class, or universe premise.
example :
    (∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) →
    ∀ (p : Nat.Primes) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ),
      ((u : ZMod N).cast : ZMod ((p : ℕ) ^ N.factorization p)) = -1 →
      ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1 →
      ((∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
          ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔ χ.toUnitHom u = 1) :=
  localKroneckerWeber_implies_leafSqrtCrit

-- N = 1 and k = 0, for every prime, with no local-KW assumption.
example (p : Nat.Primes) (χ : DirichletCharacter ℂ 1) :
    ∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
      ∀ x, φ x ^ 2 = galChar χ (resp p x) := by
  exact dirichlet_squareRoot_at_level p 0 1 (by simp) χ 1
    (by
      haveI : Subsingleton (ZMod ((p : ℕ) ^ 0)) := by
        rw [Nat.pow_zero]
        infer_instance
      exact Subsingleton.elim _ _)
    (Subsingleton.elim _ _) (map_one χ.toUnitHom)

-- A nontrivial prime-to-2 character level; the half character is inflated from a larger level.
example (χ : DirichletCharacter ℂ 3) :
    ∃ φ : GQp p₂ →* ℂˣ, IsLocallyConstant φ ∧
      ∀ x, φ x ^ 2 = galChar χ (resp p₂ x) := by
  exact dirichlet_squareRoot_at_level p₂ 0 3 (by norm_num) χ 1
    (by
      haveI : Subsingleton (ZMod ((p₂ : ℕ) ^ 0)) := by
        rw [Nat.pow_zero]
        infer_instance
      exact Subsingleton.elim _ _)
    (by simp) (map_one χ.toUnitHom)

-- The dyadic obstruction is retained, not dropped by an odd-prime hypothesis.
example (hKW : PkgI6.LocalKroneckerWeber 2) (χ : DirichletCharacter ℂ 4) :
    (∃ φ : GQp p₂ →* ℂˣ, IsLocallyConstant φ ∧
      ∀ x, φ x ^ 2 = galChar χ (resp p₂ x)) ↔ χ.toUnitHom (-1) = 1 := by
  exact local_squareRoot_criterion_normalized p₂ hKW 4 2 1 (by norm_num)
    (by simp) χ (-1) (by simp) (Subsingleton.elim _ _)

#check ZInQ.Contrib.LocalSquareRoot.localKroneckerWeber_implies_leafSqrtCrit

#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.exists_half_iff_of_baer
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.complexUnitsDivisible
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.complexUnits_baer
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.exists_half_iff
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.exists_squareRoot_iff
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.isIntegral_iff_spectralNorm_le_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.spectralNorm_mul'
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.isLocalRing_integralClosure
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.card_quotient_maximalIdeal
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.exists_frobenius
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.eq_of_pow_eq_one_of_sub_mem
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.pow_frobenius_of_isLocalRing
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.autToPow_eq_of_apply
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.range_autToPow_eq_zpowers
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.range_autToPow_eq_zpowers'
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.exists_half_iff
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.dvd_sub_or_add_of_dvd_sq_sub_one_odd
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.dvd_sub_or_add_of_dvd_sq_sub_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.redU
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.redU_val
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.redU_neg_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.intCast_eq_one_or_neg_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.dvd_of_sq_eq_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtLocal.redU_sq_eq_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.prime_mem_pow_totient
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.totient_mul_orderOf_le_finrank
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.card_subgroup_prod
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.zeta_pow_m
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.zeta_pow_pk
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.galToProd
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.fix_of_autToPow_eq_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.galToProd_injective
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.range_galToProd
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.galToProd_fst_spec
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.galToProd_snd_spec
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.galToProd_restrict
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.galCommGroup
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.sqrt_criterion_level
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.coprime_pow_sub_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.orderOf_unit_pow_sub_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.dvd_pow_orderOf_sub_one
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.exists_tau
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.sqrt_criterion_level_pow
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.muField
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.isCyclotomicExtension_muField
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.muField_mono
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.le_muField_of_lkw
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.muField_le_level
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.level_dvd
#print axioms ZInQ.Contrib.LocalSquareRoot.GlueSqrtDisj.enlarged_level_pos
#print axioms ZInQ.Contrib.LocalSquareRoot.exists_finite_abelian_kernel
#print axioms ZInQ.Contrib.LocalSquareRoot.descendCharacter
#print axioms ZInQ.Contrib.LocalSquareRoot.descendCharacter_apply
#print axioms ZInQ.Contrib.LocalSquareRoot.inflatedCharacter_isLocallyConstant
#print axioms ZInQ.Contrib.LocalSquareRoot.restrictNormal_trans
#print axioms ZInQ.Contrib.LocalSquareRoot.fieldInclusionAlgebra
#print axioms ZInQ.Contrib.LocalSquareRoot.fieldInclusion_scalarTower_base
#print axioms ZInQ.Contrib.LocalSquareRoot.fieldInclusion_scalarTower_top
#print axioms ZInQ.Contrib.LocalSquareRoot.restrictNormal_inclusion_trans
#print axioms ZInQ.Contrib.LocalSquareRoot.canonical_cyclotomic_level
#print axioms ZInQ.Contrib.LocalSquareRoot.normalized_level_dvd
#print axioms ZInQ.Contrib.LocalSquareRoot.tau_square_eq_one
#print axioms ZInQ.Contrib.LocalSquareRoot.tau_restrict_acts
#print axioms ZInQ.Contrib.LocalSquareRoot.exists_inflated_squareRoot
#print axioms ZInQ.Contrib.LocalSquareRoot.finite_obstruction_of_squareRoot
#print axioms ZInQ.Contrib.LocalSquareRoot.autToPow_map
#print axioms ZInQ.Contrib.LocalSquareRoot.autToPow_eq_of_primitiveRoots
#print axioms ZInQ.Contrib.LocalSquareRoot.absoluteGalois_map_intertwines
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteGalChar
#print axioms ZInQ.Contrib.LocalSquareRoot.cyc_eq_autToPow
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc_restrict_eq_cyc
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteGalChar_restrict_eq_galChar
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc_components
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc_tau_eq
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteGalChar_tau_eq
#print axioms ZInQ.Contrib.LocalSquareRoot.dirichlet_squareRoot_at_level
#print axioms ZInQ.Contrib.LocalSquareRoot.local_squareRoot_criterion_normalized
#print axioms ZInQ.Contrib.LocalSquareRoot.localKroneckerWeber_implies_leafSqrtCrit
