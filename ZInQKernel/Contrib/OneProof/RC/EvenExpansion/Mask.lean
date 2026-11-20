import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Source
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.ThetaTransform
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.MaskCore

/-! The actual App E cusp form after the all-index squareclass projection. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open AddressGenuine AppE AuxInputs EvenBudget HalfIntegral PrintsAnalytic Wiring
open ZInQ.Manuscript.RC.Even
open BlocksPerU CongruenceSubgroup UpperHalfPlane Filter
open ZInQ.Contrib.CloudB3RC53
open scoped BigOperators Manifold MatrixGroups

/-- The analytic and Fourier conventions for the two half-integral interfaces agree. -/
theorem threeHalves_of_cusp {N : ℕ} {ψ : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsHalfIntegralWeightCuspForm 3 N ψ g) :
    HalfIntegralThreeHalves N ψ.toUnitHom g := by
  refine ⟨hiwForm_mdiff hg, fun γ z => ?_, fun γ => ?_⟩
  · simpa only [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply] using
      hg.2.1 γ γ.property z
  · have ht : IsZeroAtImInfty (cuspNorm (3 / 2) g γ) := by
      change Tendsto (cuspNorm (3 / 2) g γ) atImInfty (nhds 0)
      convert hg.2.2 γ using 1
      funext z
      norm_num [cuspNorm, ModularGroup.denom_apply]
    exact ht.boundedAtFilter

/-- A cusp form gives an everywhere convergent period-one expansion. -/
theorem hasThreeHalves_of_cusp {N : ℕ} {ψ : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsHalfIntegralWeightCuspForm 3 N ψ g) :
    HasThreeHalvesExpansion (RingHom.id ℂ) N ψ.toUnitHom (hiwCoeff g) :=
  ⟨g, threeHalves_of_cusp hg,
    hasSum_qExpansion one_pos (hiwForm_periodic_comp hg) (hiwForm_mdiff hg)
      (hiwForm_isZeroAtImInfty hg).boundedAtFilter⟩

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}

/-- A fixed old level with the original support. All quadratic twists have
this same level before the finite character projector is formed. -/
def maskedLevel (P : EvenSource W L τ) : ℕ := (P.phaseData.N * conductor W.S) ^ 3

/-- The old level's character is the lift of the App E nebentypus. -/
def maskedCharacter (P : EvenSource W L τ) : DirichletCharacter ℂ (maskedLevel P) :=
  P.phaseData.ψ.changeLevel ((dvd_mul_right _ _).trans (dvd_pow_self _ (by decide)))

/-- Project to the prescribed unit squareclass at all indices and normalize
by the original, nonzero reference coefficient. The character does not
change on units, since each of the finite twists is quadratic. -/
theorem evenMasked (P : EvenSource W L τ) (hS : SupportSpec W) :
    4 ∣ maskedLevel P ∧
    (∀ p : ℕ, p.Prime → p ∣ maskedLevel P → p ∈ W.S) ∧
    ∃ G, IsHalfIntegralWeightCuspForm 3 (maskedLevel P) (maskedCharacter P) G ∧
      ∀ n, hiwCoeff G n = P.sievedCoeff n := by
  classical
  let m := conductor W.S
  let M := P.phaseData.N * m
  have hm : m ∣ M := dvd_mul_left _ _
  have hNM : P.phaseData.N ∣ M := dvd_mul_right _ _
  have hM4 := P.phaseData.hN.trans hNM
  have hMP : M ∣ M ^ 3 := dvd_pow_self _ (by decide)
  letI : NeZero m := ⟨(conductor_pos hS.1).ne'⟩
  letI : NeZero M := ⟨mul_ne_zero (even_level_ne_zero P) (NeZero.ne m)⟩
  have hsupp (p : ℕ) (hp : p.Prime) (h : p ∣ M) : p ∈ W.S :=
    (hp.dvd_mul.mp h).elim (P.phaseData.hNS p hp) (conductor_support hS.1 hS.2.1 hp).mp
  have hcop (n : ℕ) : n.Coprime M ↔ n.Coprime m := by
    refine ⟨fun h => h.coprime_dvd_right hm, fun h => coprime_of_support hsupp ?_⟩
    exact (coprime_conductor hS.1 hS.2.1 _).mp h
  let label := (QuotientGroup.mk' (sqSub m)).comp (ZMod.unitsMap hm)
  have hQ (q : (ZMod m)ˣ ⧸ sqSub m) : q ^ 2 = 1 := by
    have h := sqClass_add_self (Additive.ofMul q : SqClass m)
    change q * q = 1 at h
    simpa only [pow_two] using h
  let g := P.phaseData.g
  obtain ⟨G, hG, hq⟩ := quadraticProjection P.phaseData.hg.1 hNM hM4 hQ label τ.toMul
    (hiwCoeff g P.D₀)⁻¹
  refine ⟨hM4.trans hMP, fun p hp hd => hsupp p hp (hp.dvd_of_dvd_pow hd), G, hG, fun n => ?_⟩
  rw [hq n]
  by_cases hn : n.Coprime m
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      have h1 := (coprime_conductor hS.1 hS.2.1 0).mp hn 2 hS.2.1
      exact h1 (dvd_zero 2)
    have hu : IsUnit (n : ZMod M) := (ZMod.isUnit_iff_coprime n M).2 ((hcop n).2 hn)
    have he : ((n : ℤ) : ZMod m) = (ZMod.unitsMap hm hu.unit : ZMod m) := by
      change ((n : ℤ) : ZMod m) = ZMod.castHom hm (ZMod m) (hu.unit : ZMod M)
      rw [hu.unit_spec, map_natCast, Int.cast_natCast]
    have hlabel : Additive.ofMul (label hu.unit) = sqClassOf m (n : ℤ) :=
      (sqClassOf_eq_sqMk _ he).symm
    by_cases hsel : label hu.unit = τ.toMul
    · have hsq : sqClassOf m (n : ℤ) = τ := hlabel.symm.trans (congrArg Additive.ofMul hsel)
      rw [dite_eq_left hu, ite_eq_left hsel, EvenSource.sievedCoeff,
        ite_eq_left ⟨hn0, hn, hsq⟩, div_eq_mul_inv, mul_comm]
    · rw [dite_eq_left hu, ite_eq_right hsel, EvenSource.sievedCoeff, ite_eq_right]
      intro h
      exact hsel (congrArg Additive.toMul (hlabel.trans h.2.2))
  · have hu : ¬ IsUnit (n : ZMod M) := by rw [ZMod.isUnit_iff_coprime, hcop]; exact hn
    rw [dite_eq_right hu, EvenSource.sievedCoeff, ite_eq_right (fun h => hn h.2.1)]

/-- The all-index projection leaves the normalizing reference coefficient equal to one. -/
theorem evenMasked_reference (P : EvenSource W L τ) : P.sievedCoeff P.D₀ = 1 := by
  rw [EvenSource.sievedCoeff,
    ite_eq_left ⟨P.reference.1.ne', P.reference.2.2.1, P.reference.2.2.2⟩,
    div_self P.phaseData.ha₀]

/-- The masked App E form in the interface used by ordinary theta multiplication. -/
theorem evenMasked_expansion (P : EvenSource W L τ) (hS : SupportSpec W) :
    HasThreeHalvesExpansion (RingHom.id ℂ) (maskedLevel P) (maskedCharacter P).toUnitHom
      P.sievedCoeff := by
  obtain ⟨_, _, G, hG, hq⟩ := evenMasked P hS
  rw [← funext hq]
  exact hasThreeHalves_of_cusp hG


end ZInQ.Manuscript.RC.EvenExpansion
