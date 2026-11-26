import ZInQKernel.Contrib.OneProof.C8CFT
import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map

/-! # Cyclotomic factorization of a locally algebraic global character

Arithmetic local reciprocity sends the cyclotomic character of an Artin lift of
`u` to `u⁻¹`. Thus the residual character is `ψ · χ_cyc^w` and the factorization
of `ψ` uses `χ_cyc^(-w)`. No specialization of the exponent is required.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

variable (p : ℕ) [Fact p.Prime]

/-- The coefficient inclusion `ℤ_pˣ → ℚ̄_pˣ` used by the global cyclotomic character. -/
def cyclotomicUnitInclusion : ℤ_[p]ˣ →* (PadicAlgCl p)ˣ :=
  Units.map ((algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom).toMonoidHom

/-- The actual global cyclotomic character restricts to the actual local one. -/
theorem cycQ_decomp (σ : PkgI4.GQp p) :
    cycQ p (PkgI4.decomp p σ) = cyclotomicUnitInclusion p (PkgI4.cyc p σ) := by
  change cyclotomicUnitInclusion p
    (TauCeti.localCyclotomicCharacter p ℚ
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) σ)) =
    cyclotomicUnitInclusion p (TauCeti.localCyclotomicCharacter p ℚ_[p] σ)
  exact congrArg (cyclotomicUnitInclusion p)
    (TauCeti.localCyclotomicCharacter_map p (algebraMap ℚ ℚ_[p])
      (show Field.absoluteGaloisGroup ℚ_[p] from σ))

/-- Continuity of the actual global cyclotomic character in its `ℚ̄_p` coefficients. -/
theorem continuous_cycQ : Continuous (cycQ p) := by
  have hQ : Continuous (algebraMap ℚ_[p] (PadicAlgCl p)) := by
    refine Isometry.continuous (Isometry.of_dist_eq fun x y => ?_)
    simpa only [dist_eq_norm, map_sub] using PadicAlgCl.norm_extends p (x - y)
  have hZ : Continuous (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) := continuous_subtype_val
  have hj : Continuous (cyclotomicUnitInclusion p) := Continuous.units_map _ (hQ.comp hZ)
  exact hj.comp (TauCeti.localCyclotomicCharacter_continuous p ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- Remove the global cyclotomic power, as in the manuscript. The finite-image
conclusion uses the project's proved finite-inertia criterion over `ℚ`. -/
theorem exists_finite_cyclotomic_factor
    (hB : InertiaAtPDecomp) (hM : MinkowskiInertiaQ)
    (ψ : PkgI4.GaloisChar p) (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψE : PkgI4.GQp p →* Eˣ) (w : ℤ)
    (hlift : ∀ σ, (((ψE σ : Eˣ) : E) : PadicAlgCl p) =
      (ψ.toHom (PkgI4.decomp p σ) : PadicAlgCl p))
    (hLA : IsLocallyAlgebraic p ψE w) :
    ∃ η : PkgI4.GaloisChar p, (Set.range η.toHom).Finite ∧
      ψ.toHom = η.toHom * cycQ p ^ (-w) := by
  let η : PkgI4.GaloisChar p :=
    { toHom := ψ.toHom * cycQ p ^ w
      continuous_toHom := ψ.continuous_toHom.mul ((continuous_cycQ p).zpow w) }
  refine ⟨η, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hLA
    refine finiteOfLocAlgTrivialQNoRam_of_dicts hB hM p η ⟨k, ?_⟩
    intro u hu σ hσ
    have hψ : ψ.toHom (PkgI4.decomp p σ) = cyclotomicUnitInclusion p u ^ w := by
      apply Units.ext
      rw [← hlift σ]
      change algebraMap E (PadicAlgCl p) ((ψE σ : Eˣ) : E) =
        ((cyclotomicUnitInclusion p u ^ w : (PadicAlgCl p)ˣ) : PadicAlgCl p)
      rw [hk u hu σ hσ]
      have hcoe : ((cyclotomicUnitInclusion p u : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
          algebraMap E (PadicAlgCl p) (algebraMap ℚ_[p] E (((u : ℤ_[p]) : ℚ_[p]))) := rfl
      exact (map_zpow₀ (algebraMap E (PadicAlgCl p)) _ _).trans (by
        rw [Units.val_zpow_eq_zpow_val, hcoe])
    change ψ.toHom (PkgI4.decomp p σ) * cycQ p (PkgI4.decomp p σ) ^ w = 1
    rw [hψ, cycQ_decomp, cyc_of_isArtinLift p σ u hσ, map_inv,
      ← mul_zpow, mul_inv_cancel, one_zpow]
  · apply MonoidHom.ext
    intro σ
    change ψ.toHom σ = ((ψ.toHom * cycQ p ^ w) * cycQ p ^ (-w)) σ
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply]
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

end HDec.G0Galois.C8Conrad.Manuscript
