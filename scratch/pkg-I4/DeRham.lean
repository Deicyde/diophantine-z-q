import Mathlib

/-!
# Toward a genuine de Rham predicate: naturality of `untilt` and of Fontaine's `θ`

Draft for `docs/research/pkg-I4.md` §3.3 (task pkg-I4). The `G_{ℚ_p}`-action on Mathlib's
`BDeRham (𝓞_ℂ_[p]) p` is to be obtained by functoriality of the construction
`R ↦ AdicCompletion (ker θ[1/p]) (W(R♭)[1/p])`. Its mathematical core is the naturality of
Fontaine's `θ` in `R`; this file proves it for any ring map between `p`-adically complete rings.

* `PkgI4.Cp`: `𝓞_ℂ_[p]` is `p`-adically complete and `p` is not a unit in it (instances missing
  from Mathlib v4.35, so `BDeRham (𝓞_ℂ_[p]) p` did not typecheck before).
* `PkgI4.DR`: functoriality of `R♭`, naturality of `untilt` and `θ`, ring maps of adic
  completions, functoriality of `B_dR^+`.
-/

noncomputable section

namespace PkgI4.Cp

open Ideal

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_O_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def]
  change (PadicComplex.valued p).v x ≤ 1 ↔ _
  rw [← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one, NNReal.coe_le_one] using
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
    IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p]; exact inv_pos.mpr (by exact_mod_cast hp.1.pos)

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.1.one_lt)

/-- `x ∈ p^n 𝓞` iff `‖x‖ ≤ ‖p‖^n`. -/
theorem mem_span_pow_iff (x : 𝓞_ℂ_[p]) (n : ℕ) :
    x ∈ span {(p : 𝓞_ℂ_[p])} ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖(z : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp z.2
    have e : ((z * (p : 𝓞_ℂ_[p]) ^ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (z : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
      push_cast; rfl
    rw [e, norm_mul, norm_pow]
    calc ‖(z : ℂ_[p])‖ * ‖(p : ℂ_[p])‖ ^ n ≤ 1 * ‖(p : ℂ_[p])‖ ^ n := by gcongr
      _ = _ := one_mul _
  · intro h
    have hpn : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp (norm_p_pos p))
    refine ⟨⟨(x : ℂ_[p]) / (p : ℂ_[p]) ^ n, (mem_O_iff p _).mpr ?_⟩, ?_⟩
    · rw [norm_div, norm_pow, div_le_one (pow_pos (norm_p_pos p) n)]
      exact h
    · apply Subtype.ext
      push_cast
      field_simp


theorem smodEq_iff (x y : 𝓞_ℂ_[p]) (n : ℕ) :
    x ≡ y [SMOD (span {(p : 𝓞_ℂ_[p])} ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow_iff]
  push_cast
  rfl

instance notIsUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := ⟨fun h => by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  have hv' : (p : ℂ_[p]) * (v : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hv
    push_cast at this
    exact this
  have h1 : ‖(v : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp v.2
  have h2 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ = 1 := by rw [← norm_mul, hv', norm_one]
  have h3 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ < 1 :=
    calc ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact norm_p_lt_one p
  linarith⟩

theorem tendsto_norm_p_pow :
    Filter.Tendsto (fun n : ℕ => ‖(p : ℂ_[p])‖ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_p_lt_one p)

instance isHausdorff : IsHausdorff (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  haus' x hx := by
    have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun n => by
      have := (smodEq_iff p x 0 n).mp (hx n)
      simpa using this
    have h0 : ‖(x : ℂ_[p])‖ ≤ 0 := ge_of_tendsto' (tendsto_norm_p_pow p) h
    exact Subtype.ext (by simpa using norm_le_zero_iff.mp h0)

instance isPrecomplete : IsPrecomplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  prec' f hf := by
    set g : ℕ → ℂ_[p] := fun n => (f n : ℂ_[p])
    have hmn : ∀ m n, m ≤ n → ‖g m - g n‖ ≤ ‖(p : ℂ_[p])‖ ^ m := fun m n h =>
      (smodEq_iff p _ _ m).mp (hf h)
    have hcs : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ‖(p : ℂ_[p])‖ ^ N) (fun n m N hn hm => ?_) ?_
      · rw [dist_eq_norm]
        calc ‖g n - g m‖ = ‖(g N - g m) - (g N - g n)‖ := by congr 1; ring
          _ ≤ ‖g N - g m‖ + ‖g N - g n‖ := norm_sub_le _ _
          _ ≤ ‖(p : ℂ_[p])‖ ^ N + ‖(p : ℂ_[p])‖ ^ N := add_le_add (hmn N m hm) (hmn N n hn)
          _ = 2 * ‖(p : ℂ_[p])‖ ^ N := by ring
      · simpa using (tendsto_norm_p_pow p).const_mul 2
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' (hL.norm) fun n => (mem_O_iff p _).mp (f n).2
    refine ⟨⟨L, (mem_O_iff p L).mpr hL1⟩, fun n => (smodEq_iff p _ _ n).mpr ?_⟩
    have ht : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨n, fun k hk => hmn n k hk⟩)

instance isAdicComplete : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where

end PkgI4.Cp

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

#print axioms PkgI4.Cp.isAdicComplete
#print axioms PkgI4.DR.fontaineTheta_naturality
#print axioms PkgI4.DR.bdrPlusMap
