import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Hensel lifting of residue points of étale algebras

Let `R` be a henselian local ring with residue field `k`. Every `R`-algebra map from an étale
`R`-algebra `S` to `k` lifts to a unique `R`-algebra map `S → R` (EGA IV 18.5.11, Stacks 04GG in
its affine form). The proof goes through the local structure theorem for étale algebras
(`Algebra.IsEtaleAt.exists_isStandardEtale`, Stacks 00UE): first standard étale algebras, where the
lift is Hensel's lemma for the monic defining polynomial together with uniqueness of a simple root
in a residue class (`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`), then a principal
localization of an arbitrary étale algebra. No finiteness of `S` over `R` is assumed or used: this
is what makes the statement apply to quasi-finite étale torsion schemes whose generic fibre has
points that do not specialize.

Edition V005: three tactic-level corrections of V004; statements unchanged.
-/

open Polynomial IsLocalRing

namespace HenselDivision

universe u v

variable {R : Type u} [CommRing R]

/-- The residue map as an `R`-algebra map. -/
noncomputable abbrev resₐ (R : Type u) [CommRing R] [IsLocalRing R] : R →ₐ[R] ResidueField R :=
  IsScalarTower.toAlgHom R R (ResidueField R)

lemma resₐ_apply [IsLocalRing R] (a : R) : resₐ R a = residue R a := rfl

lemma residue_eval [IsLocalRing R] (p : R[X]) (b : R) :
    residue R (p.eval b) = aeval (residue R b) p := by
  rw [← Polynomial.coe_aeval_eq_eval, ← ResidueField.algebraMap_eq,
    Polynomial.aeval_algebraMap_apply]

/-- Hensel's lemma in residue-field form, from the definition of a henselian local ring. -/
lemma exists_root_residue_eq [HenselianLocalRing R] (f : R[X]) (hf : f.Monic)
    (x₀ : ResidueField R) (h0 : aeval x₀ f = 0) (h1 : IsUnit (aeval x₀ (derivative f))) :
    ∃ a : R, f.IsRoot a ∧ residue R a = x₀ := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective x₀
  have hm : f.eval a₀ ∈ maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_eval, h0]
  have hu : IsUnit (f.derivative.eval a₀) := by
    rw [← isUnit_map_iff (residue R), residue_eval]; exact h1
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian f hf a₀ hm hu
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact ham

/-- **Standard étale case.** -/
theorem standardEtalePair_existsUnique_lift [HenselianLocalRing R] (P : StandardEtalePair R)
    (ψ : P.Ring →ₐ[R] ResidueField R) :
    ∃! φ : P.Ring →ₐ[R] R, (resₐ R).comp φ = ψ := by
  set x₀ : ResidueField R := ψ P.X with hx₀def
  have hx₀ : P.HasMap x₀ := StandardEtalePair.hasMap_X.map ψ
  have hder : IsUnit (aeval x₀ (derivative P.f)) := hx₀.isUnit_derivative_f
  obtain ⟨a, ha, hres⟩ := exists_root_residue_eq P.f P.monic_f x₀ hx₀.1 hder
  have hga : IsUnit (aeval a P.g) := by
    have : residue R (aeval a P.g) = aeval x₀ P.g := by
      rw [← hres, ← ResidueField.algebraMap_eq, Polynomial.aeval_algebraMap_apply]
    exact (isUnit_map_iff (residue R) _).mp (this ▸ hx₀.2)
  have hfa : aeval a P.f = 0 := by
    rw [Polynomial.coe_aeval_eq_eval]; exact ha
  have hA : P.HasMap a := ⟨hfa, hga⟩
  refine ⟨P.lift a hA, ?_, ?_⟩
  · apply StandardEtalePair.hom_ext
    simp only [AlgHom.comp_apply, StandardEtalePair.lift_X, resₐ_apply, hres]
    exact hx₀def
  · intro φ' hφ'
    apply StandardEtalePair.hom_ext
    rw [StandardEtalePair.lift_X]
    have hB : P.HasMap (φ' P.X) := StandardEtalePair.hasMap_X.map φ'
    have hresB : residue R (φ' P.X) = x₀ := by
      rw [hx₀def, ← hφ']; rfl
    have hfb : P.f.eval (φ' P.X) = 0 := by
      rw [← Polynomial.coe_aeval_eq_eval]; exact hB.1
    have hda : IsUnit (P.f.derivative.eval a) := by
      rw [← Polynomial.coe_aeval_eq_eval]; exact hA.isUnit_derivative_f
    have hnu : ¬ IsUnit (a - φ' P.X) := by
      intro hu
      have h0 : residue R (a - φ' P.X) = 0 := by
        rw [map_sub, hres, hresB, sub_self]
      exact ((isUnit_map_iff (residue R) _).mpr hu).ne_zero h0
    exact (IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha hfb hnu hda).symm

/-- **Standard étale algebras** (any presentation). -/
theorem isStandardEtale_existsUnique_lift [HenselianLocalRing R] {S : Type v} [CommRing S]
    [Algebra R S] [Algebra.IsStandardEtale R S] (ψ : S →ₐ[R] ResidueField R) :
    ∃! φ : S →ₐ[R] R, (resₐ R).comp φ = ψ := by
  let Pr : StandardEtalePresentation R S := Classical.choice inferInstance
  let e : S ≃ₐ[R] Pr.Ring := Pr.equivRing
  obtain ⟨φ₀, hφ₀, huniq⟩ :=
    standardEtalePair_existsUnique_lift Pr.P (ψ.comp e.symm.toAlgHom)
  refine ⟨φ₀.comp e.toAlgHom, ?_, ?_⟩
  · ext s
    have := AlgHom.congr_fun hφ₀ (e s)
    simpa using this
  · intro φ' hφ'
    have h1 : φ'.comp e.symm.toAlgHom = φ₀ := huniq _ (by
      beta_reduce
      rw [← AlgHom.comp_assoc, hφ'])
    ext s
    have := AlgHom.congr_fun h1 (e s)
    simpa using this

/-- **Hensel lifting for étale algebras.** `R` henselian local, `S` étale over `R`: every
`R`-algebra map `S → k` to the residue field lifts to a unique `R`-algebra map `S → R`. -/
theorem etale_existsUnique_lift [HenselianLocalRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (ψ : S →ₐ[R] ResidueField R) :
    ∃! φ : S →ₐ[R] R, (resₐ R).comp φ = ψ := by
  let Q : Ideal S := RingHom.ker ψ
  have : Q.IsPrime := RingHom.ker_isPrime ψ
  have : Algebra.IsEtaleAt R Q := inferInstance
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hψf : IsUnit (ψ f) := by
    rw [isUnit_iff_ne_zero]
    intro h
    exact hfQ (RingHom.mem_ker.mpr h)
  let Sf := Localization.Away f
  let ι : S →ₐ[R] Sf := IsScalarTower.toAlgHom R S Sf
  have hunit : ∀ y : Submonoid.powers f, IsUnit (ψ (y : S)) := by
    rintro ⟨y, n, rfl⟩
    simpa using hψf.pow n
  let ψf : Sf →ₐ[R] ResidueField R := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  have hψf_comp : ψf.comp ι = ψ := by
    ext s
    simp only [ψf, ι, AlgHom.comp_apply, IsLocalization.coe_liftAlgHom,
      IsScalarTower.toAlgHom_apply, IsLocalization.lift_eq, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
  obtain ⟨φf, hφf, huniq⟩ := isStandardEtale_existsUnique_lift (R := R) (S := Sf) ψf
  refine ⟨φf.comp ι, ?_, ?_⟩
  · show (resₐ R).comp (φf.comp ι) = ψ
    rw [← AlgHom.comp_assoc, hφf, hψf_comp]
  · intro φ' hφ'
    have hφ'unit : ∀ y : Submonoid.powers f, IsUnit (φ' (y : S)) := by
      rintro ⟨y, n, rfl⟩
      have hf' : IsUnit (φ' f) := by
        have : residue R (φ' f) = ψ f := by
          rw [← hφ']; rfl
        exact (isUnit_map_iff (residue R) _).mp (this ▸ hψf)
      simpa using hf'.pow n
    let φ'f : Sf →ₐ[R] R := IsLocalization.liftAlgHom (M := Submonoid.powers f) hφ'unit
    have hφ'f_comp : φ'f.comp ι = φ' := by
      ext s
      simp only [φ'f, ι, AlgHom.comp_apply, IsLocalization.coe_liftAlgHom,
        IsScalarTower.toAlgHom_apply, IsLocalization.lift_eq, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom]
    have hres' : (resₐ R).comp φ'f = ψf := by
      apply IsLocalization.algHom_ext (Submonoid.powers f)
      change (resₐ R).comp (φ'f.comp ι) = ψf.comp ι
      rw [hφ'f_comp, hφ', hψf_comp]
    rw [← hφ'f_comp, huniq φ'f hres']

end HenselDivision

#check @HenselDivision.exists_root_residue_eq
#check @HenselDivision.standardEtalePair_existsUnique_lift
#check @HenselDivision.isStandardEtale_existsUnique_lift
#check @HenselDivision.etale_existsUnique_lift
#print axioms HenselDivision.etale_existsUnique_lift
