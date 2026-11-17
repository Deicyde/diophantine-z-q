/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): the generic limit of an unramified DVR extension

New glue (no vendored source in this file).

Let `O` be a DVR with fraction field `K`, `P` a DVR with fraction field `E`, and `O → P` an
injective local homomorphism, compatible with `K → E` (no henselian, residue, separability or
characteristic hypothesis).  Then `E` is the pushout `P ⊗_O K`:
`isPushout_of_dvr : Algebra.IsPushout O P K E`, hence `Spec E = Spec P ×_{Spec O} Spec K`
(`isPullback_spec_of_dvr`).  The point is that for a nonzero nonunit `x` of a DVR, the fraction
field is the localization away from `x` (`isLocalization_powers_of_dvr`), and a uniformizer of `O`
maps to a nonzero nonunit of `P`.

`phiOfIsPullback` transports a group-object isomorphism of generic fibres along any pullback
square identifying a scheme `Z` with the generic limit `Spec S ×_{Spec R} Spec K` of a presentation;
`exists_spread_stage_field` combines this with `exists_spread_stage`, so that the generic group
isomorphism may be supplied over `Spec (Frac P)` (for the ordinary henselization: H4's field
`E ⊆ Ω`, with `P = w.comap (algebraMap E Ω)`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.Assembly

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

open ZInQ.Contrib.SpreadOut (pbNat)

/-! ### Ring theory -/

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- In a DVR, every nonzero element divides a power of any nonzero nonunit. -/
theorem exists_dvd_pow_of_dvr {x y : O} (hx : x ≠ 0) (hxu : ¬ IsUnit x) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have hm : m ≠ 0 := by
    rintro rfl
    exact hxu (by simp)
  refine ⟨n, ?_⟩
  have h1 : (↑u : O) * ϖ ^ n ∣ ϖ ^ n := ⟨↑u⁻¹, by rw [mul_comm (↑u : O), _root_.mul_assoc,
    Units.mul_inv, _root_.mul_one]⟩
  have h2 : ϖ ^ n ∣ (↑v * ϖ ^ m) ^ n := by
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm))) _
  exact h1.trans h2

/-- **The fraction field of a DVR is its localization away from any nonzero nonunit.** -/
theorem isLocalization_powers_of_dvr (E : Type*) [CommRing E] [Algebra O E] [IsFractionRing O E]
    {x : O} (hx : x ≠ 0) (hxu : ¬ IsUnit x) : IsLocalization (Submonoid.powers x) E := by
  have hmem : ∀ n : ℕ, x ^ n ∈ nonZeroDivisors O :=
    fun n => mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hx)
  refine (isLocalization_iff_isLocalizationMap _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    exact IsLocalization.map_units E (⟨x ^ n, hmem n⟩ : nonZeroDivisors O)
  · intro z
    obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors O) z
    obtain ⟨n, t, ht⟩ := exists_dvd_pow_of_dvr hx hxu (nonZeroDivisors.ne_zero s.2)
    refine ⟨⟨a * t, ⟨x ^ n, n, rfl⟩⟩, ?_⟩
    have hz' : z * algebraMap O E (s : O) = algebraMap O E a := hz
    change z * algebraMap O E (x ^ n) = algebraMap O E (a * t)
    rw [ht, map_mul, map_mul, ← _root_.mul_assoc, hz']
  · intro a b h
    exact ⟨1, by rw [IsFractionRing.injective O E h]⟩

end DVR

section Pushout

variable {O K P E : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [CommRing P] [IsDomain P] [IsDiscreteValuationRing P]
  [Field E] [Algebra P E] [IsFractionRing P E] [Algebra O P] [Algebra K E] [Algebra O E]
  [IsScalarTower O K E] [IsScalarTower O P E]

/-- **`E = P ⊗_O K`** for an injective local homomorphism of DVRs `O → P` with fraction fields
`K → E`. -/
theorem isPushout_of_dvr (hloc : IsLocalHom (algebraMap O P))
    (hinj : Function.Injective (algebraMap O P)) : Algebra.IsPushout O P K E := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖu : ¬ IsUnit ϖ := hϖ.not_isUnit
  haveI : IsLocalization (Submonoid.powers ϖ) K := isLocalization_powers_of_dvr K hϖ0 hϖu
  have hx0 : algebraMap O P ϖ ≠ 0 := fun h => hϖ0 (hinj (by rw [h, map_zero]))
  have hxu : ¬ IsUnit (algebraMap O P ϖ) := fun h => hϖu ((isUnit_map_iff (algebraMap O P) ϖ).1 h)
  haveI hE : IsLocalization (Submonoid.powers (algebraMap O P ϖ)) E :=
    isLocalization_powers_of_dvr E hx0 hxu
  have hsub : Algebra.algebraMapSubmonoid P (Submonoid.powers ϖ) =
      Submonoid.powers (algebraMap O P ϖ) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid P (Submonoid.powers ϖ)) E := by
    rw [hsub]
    exact hE
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers ϖ) K P E

/-- **`Spec E = Spec P ×_{Spec O} Spec K`.** -/
theorem isPullback_spec_of_dvr (hloc : IsLocalHom (algebraMap O P))
    (hinj : Function.Injective (algebraMap O P)) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap P E)))
      (Spec.map (CommRingCat.ofHom (algebraMap K E)))
      (Spec.map (CommRingCat.ofHom (algebraMap O P)))
      (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  haveI := isPushout_of_dvr (K := K) (E := E) hloc hinj
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout O P K E)

end Pushout

/-! ### The valuation-subring case -/

section ValuationSubring

variable {K E : Type u} [Field K] [Field E] [Algebra K E] {O : ValuationSubring K}
  {P : ValuationSubring E} [Algebra O P]

/-- A homomorphism `O → P` of valuation subrings compatible with `K → E` and with
`P.comap (algebraMap K E) = O` is injective. -/
theorem injective_of_comap (hcomp : ∀ x : O, ((algebraMap O P x : P) : E) = algebraMap K E x) :
    Function.Injective (algebraMap O P) := by
  intro x y h
  have h' := congrArg (fun z : P => (z : E)) h
  simp only [hcomp] at h'
  exact Subtype.ext ((algebraMap K E).injective h')

/-- ... and local. -/
theorem isLocalHom_of_comap (hP : P.comap (algebraMap K E) = O)
    (hcomp : ∀ x : O, ((algebraMap O P x : P) : E) = algebraMap K E x) :
    IsLocalHom (algebraMap O P) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := hx
  have hx0 : (x : K) ≠ 0 := by
    intro h0
    have : ((v : P) : E) = 0 := by rw [hv, hcomp, h0, map_zero]
    exact v.ne_zero (Subtype.ext this)
  have hmul : ((v : P) : E) * ((↑v⁻¹ : P) : E) = 1 := by
    have h : ((((v : P) * (↑v⁻¹ : P) : P)) : E) = ((1 : P) : E) := by rw [Units.mul_inv]
    exact h
  have hinvP : algebraMap K E ((x : K)⁻¹) ∈ P := by
    rw [map_inv₀, ← hcomp, ← hv, inv_eq_of_mul_eq_one_right hmul]
    exact (↑v⁻¹ : P).2
  have hinvO : (x : K)⁻¹ ∈ O := by
    have h1 : (x : K)⁻¹ ∈ P.comap (algebraMap K E) := hinvP
    rw [hP] at h1
    exact h1
  exact ⟨⟨x, ⟨(x : K)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hx0),
    Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

end ValuationSubring

/-! ### Transport of generic group isomorphisms along a pullback square -/

section Transport

variable {R : Type u} [CommRing R] {S : CommAlgCat.{u} R} {J : Type u} [SmallCategory J]
  (pres : ColimitPresentation J S) (K : Type u) [CommRing K] [Algebra R K]

/-- **Transport of a generic group isomorphism along a pullback square** `Z ≅ Spec S ×_R Spec K`. -/
def phiOfIsPullback {Z : Scheme.{u}} {fst' : Z ⟶ (specCone pres).pt}
    {snd' : Z ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback fst' snd' (Spec.map (CommRingCat.ofHom (algebraMap R S))) (genMap K))
    (N : Grp (Over (specCone pres).pt)) (A : Grp (Over (Spec (CommRingCat.of K))))
    (φZ : (Over.pullback fst').mapGrp.obj N ≅ (Over.pullback snd').mapGrp.obj A) :
    (Over.pullback (genFstLim pres K)).mapGrp.obj N ≅
      (Over.pullback (genSndLim pres K)).mapGrp.obj A :=
  let θ := h.isoPullback.inv
  have hfst : θ ≫ fst' = genFstLim pres K := h.isoPullback_inv_fst
  have hsnd : θ ≫ snd' = genSndLim pres K := h.isoPullback_inv_snd
  let e₁ := ((pbNat θ fst' (genFstLim pres K) hfst).app N.X).symm
  let e₂ := (Over.pullback θ).mapIso (grpIsoX φZ)
  let e₃ := (pbNat θ snd' (genSndLim pres K) hsnd).app A.X
  have h₁ := isMonHom_app_to_comp (pbNat θ fst' (genFstLim pres K) hfst).inv N.X
  have h₂ := isMonHom_map' (Over.pullback θ) (inferInstanceAs (IsMonHom φZ.hom.hom.hom))
  have h₃ := isMonHom_app_comp (pbNat θ snd' (genSndLim pres K) hsnd).hom A.X
  @Grp.mkIso' _ _ _ _ _ (e₁ ≪≫ e₂ ≪≫ e₃) _ _ (isMonHom_comp' h₁ (isMonHom_comp' h₂ h₃))

end Transport

/-! ### The spreading theorem with the generic isomorphism over the fraction field -/

/-- **`exists_spread_stage` with the generic group isomorphism supplied over `Spec (Frac P)`.** -/
theorem exists_spread_stage_field {O K P E : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing P]
    [IsDomain P] [IsDiscreteValuationRing P] [Field E] [Algebra P E] [IsFractionRing P E]
    [Algebra O P] [Algebra K E] [Algebra O E] [IsScalarTower O K E] [IsScalarTower O P E]
    (hloc : IsLocalHom (algebraMap O P)) (hinj : Function.Injective (algebraMap O P))
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J (CommAlgCat.of O P))
    (hpr : ProperDescendsFor (specDiagram pres) (specCone pres))
    (N : Grp (Over (specCone pres).pt)) [Smooth N.X.hom] [IsProper N.X.hom]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFinitePresentation A.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom]
    (φE : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P E)) :
        Spec (CommRingCat.of E) ⟶ (specCone pres).pt)).mapGrp.obj N ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E)))).mapGrp.obj A) :
    ∃ (j : Jᵒᵖ) (G : Grp (Over ((specDiagram pres).obj j))),
      Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Nonempty ((Over.pullback ((specCone pres).π.app j)).mapGrp.obj G ≅ N) ∧
      Nonempty ((Over.pullback (genFst pres K j)).mapGrp.obj G ≅
        (Over.pullback (genSnd pres K j)).mapGrp.obj A) :=
  exists_spread_stage pres K hpr N A
    (phiOfIsPullback pres K (isPullback_spec_of_dvr (K := K) (E := E) hloc hinj) N A φE)

end ZInQ.Contrib.CloudR2NOS.Spreadout
