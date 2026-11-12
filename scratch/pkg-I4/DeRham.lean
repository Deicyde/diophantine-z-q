import Mathlib

/-!
# Toward a genuine de Rham predicate: naturality of `untilt` and of Fontaine's `θ`

Draft for `docs/research/pkg-I4.md` §3.3 (task pkg-I4). The `G_{ℚ_p}`-action on Mathlib's
`BDeRham (𝓞_ℂ_[p]) p` is to be obtained by functoriality of the construction
`R ↦ AdicCompletion (ker θ[1/p]) (W(R♭)[1/p])`. Its mathematical core is the naturality of
Fontaine's `θ` in `R`; this file proves it for any ring map between `p`-adically complete rings.
-/

noncomputable section

namespace PkgI4.DR

open Ideal

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem span_p_le_comap (f : R →+* S) :
    span {(p : R)} ≤ (span {(p : S)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/-- `R/p → S/p` induced by `f`. -/
def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap _ f (span_p_le_comap p f)

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]

/-- The tilt is functorial: `R♭ → S♭`. -/
def preTiltMap (f : R →+* S) : PreTilt R p →+* PreTilt S p :=
  Perfection.map p (modPMap p f)

theorem coeff_preTiltMap (f : R →+* S) (x : PreTilt R p) (n : ℕ) :
    Perfection.coeff _ p n (preTiltMap p f x) = modPMap p f (Perfection.coeff _ p n x) :=
  rfl

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- Naturality of `untilt`. -/
theorem untilt_preTiltMap (f : R →+* S) (x : PreTilt R p) :
    PreTilt.untilt (preTiltMap p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  refine ⟨f w, ?_, ?_⟩
  · rw [coeff_preTiltMap, ← hw]
    rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := w) hw
    rw [SModEq.sub_mem] at h ⊢
    have h' := Ideal.mem_map_of_mem f h
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast, map_sub,
      map_pow] at h'
    have h'' := neg_mem h'
    rw [neg_sub] at h''
    exact h''

/-- **Naturality of Fontaine's `θ`**: `θ_S ∘ W(f♭) = f ∘ θ_R`. -/
theorem fontaineTheta_naturality (f : R →+* S) :
    (WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f)) =
      f.comp (WittVector.fontaineTheta R p) := by
  ext x
  refine (IsHausdorff.eq_iff_smodEq (I := span {(p : S)})).mpr fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  have key : (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp
      ((WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f))) =
      (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (WittVector.fontaineTheta R p)) := by
    refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ fun y => ?_
    · rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    · simp only [RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun g => g x) key


/-! ### Functoriality of adic completions of rings -/

section AdicMap

variable {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B) (g : A →+* B)
  (hg : J ≤ J'.comap g)

include hg in
theorem pow_le_comap (n : ℕ) : J ^ n ≤ (J' ^ n).comap g := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hg) n

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk J hle]
  rfl

/-- `A ⧸ J^n`-components of the map `Â_J → B̂_{J'}`. -/
def adicMapAux (n : ℕ) : AdicCompletion J A →+* B ⧸ J' ^ n :=
  (Ideal.quotientMap (J' ^ n) g (pow_le_comap J J' g hg n)).comp
    (AdicCompletion.evalₐ J n : AdicCompletion J A →+* A ⧸ J ^ n)

/-- The ring map `Â_J → B̂_{J'}` induced by `g` with `g(J) ⊆ J'`. -/
def adicMap : AdicCompletion J A →+* AdicCompletion J' B :=
  AdicCompletion.liftRingHom J' (adicMapAux J J' g hg) fun {m n} hle => by
    ext x
    simp only [RingHom.comp_apply, adicMapAux]
    erw [← factorPow_evalₐ J hle x]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    erw [← ha]
    rfl

end AdicMap

/-! ### Functoriality of `B_dR^+` -/

section BdR

/-- `W(R♭)[1/p] → W(S♭)[1/p]`. -/
def locMap (f : R →+* S) :
    Localization.Away (p : WittVector p (PreTilt R p)) →+*
      Localization.Away (p : WittVector p (PreTilt S p)) :=
  Localization.awayLift ((algebraMap _ _).comp (WittVector.map (preTiltMap p f))) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- `R[1/p] → S[1/p]`. -/
def locMapBase (f : R →+* S) : Localization.Away (p : R) →+* Localization.Away (p : S) :=
  Localization.awayLift ((algebraMap _ _).comp f) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- Naturality of `θ[1/p]`. -/
theorem fontaineThetaInvertP_naturality (f : R →+* S) :
    (fontaineThetaInvertP S p).comp (locMap p f) =
      (locMapBase p f).comp (fontaineThetaInvertP R p) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, locMap, locMapBase, fontaineThetaInvertP,
    Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq]
  rw [← RingHom.comp_apply (WittVector.fontaineTheta S p), fontaineTheta_naturality]
  rfl

theorem ker_le_comap_locMap (f : R →+* S) :
    RingHom.ker (fontaineThetaInvertP R p) ≤
      (RingHom.ker (fontaineThetaInvertP S p)).comap (locMap p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
    fontaineThetaInvertP_naturality, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

/-- **Functoriality of `B_dR^+`**: `B_dR^+(R) → B_dR^+(S)` for `f : R →+* S`. -/
def bdrPlusMap (f : R →+* S) : BDeRhamPlus R p →+* BDeRhamPlus S p :=
  adicMap _ _ (locMap p f) (ker_le_comap_locMap p f)

end BdR

end PkgI4.DR

end

#print axioms PkgI4.DR.fontaineTheta_naturality
#print axioms PkgI4.DR.bdrPlusMap
