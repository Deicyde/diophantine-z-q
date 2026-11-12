import Mathlib

/-!
# Package I4 (modularity): leaves statable over Mathlib today

Draft for `docs/research/pkg-I4.md` (task pkg-I4, 2026-11-11). Check with
`lake env lean scratch/pkg-I4/I4.lean`.

* `PkgI4.Cp`, `PkgI4.DR` (first): `𝓞_ℂ_[p]` is `p`-adically complete (instances missing in
  Mathlib), and Mathlib's `BDeRhamPlus`/`BDeRham` are functorial (naturality of `untilt` and of
  Fontaine's `θ`, maps of adic completions, generators of `ker θ`). Used in §1b for the action of
  `G_{ℚ_p}` on `B_dR` and the **de Rham predicate**.
* §0 Galois side over `ℚ̄`: copied, with small changes, from `scratch/hdec-faithful/Leaves.lean`
  §0 (places as valuation subrings, inertia, arithmetic Frobenius, complex conjugation,
  continuous `GL_n(ℚ̄_ℓ)`-representations, characters).
* §1 **new**: the local Galois group `G_{ℚ_p}`, its action on Mathlib's `ℂ_[p]`, the
  `p`-adic cyclotomic character, and **Hodge–Tate multiplicities** (Tate–Sen definition through
  `(ℂ_p(i) ⊗ V)^{G_{ℚ_p}}`, written as a space of equivariant `ℚ_p`-linear maps `V → ℂ_p`).
* §2 modular side: cusp forms on `Γ₁(N)`, nebentypus, normalized eigenforms (Hecke recursion of
  the q-coefficients, as hdec-faithful), representations attached to eigenforms (trace form),
  and **new**: the old space and newforms.
* §1b **new**: the action of `G_{ℚ_p}` on `B_dR = BDeRham 𝓞_ℂ_[p] p`, `ℚ_p ⊆ B_dR` fixed by it,
  `D_dR`, and the **de Rham predicate** `IsDeRham` / `LocalIsDeRham` (genuine; no `sorry`).
* §3 the leaves of I4 that are statable now, as `def … : Prop` (none proved).
* §4 templates — functions of a missing predicate (`IsPst`, the conductor exponent) — and the
  leaf **`PanBerger`** = `PanFor LocalIsDeRham`, statable now. A template is **not** a leaf:
  `PanFor P` says nothing until `P` is the genuine potentially-semistable predicate.
* §5 small glue facts, proved.

Faithfulness caveat: `IsDeRham` and `htMult` are genuine definitions, but no theorem about them is
proved here (e.g. `B_dR^{G_{ℚ_p}} = ℚ_p`, Tate's `ℂ_p(i)^G = 0`). A definitional slip could make a
hypothesis unsatisfiable and a leaf vacuous; the standard non-vacuity checks are listed in
`docs/research/pkg-I4.md` §3.4.
-/

noncomputable section

set_option linter.unusedSectionVars false

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

theorem adicMapAux_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J' hle).comp (adicMapAux J J' g hg n) = adicMapAux J J' g hg m := by
  ext x
  simp only [RingHom.comp_apply, adicMapAux]
  erw [← factorPow_evalₐ J hle x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

/-- The ring map `Â_J → B̂_{J'}` induced by `g` with `g(J) ⊆ J'`. -/
def adicMap : AdicCompletion J A →+* AdicCompletion J' B :=
  AdicCompletion.liftRingHom J' (adicMapAux J J' g hg) (adicMapAux_compat J J' g hg)

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


/-! ### Inverse pairs, generators of `ker θ`, and the map on `B_dR` -/

section Inverse

variable (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x)

include hgf in
theorem modPMap_comp_eq_id (y : ModP R p) : modPMap p g (modPMap p f y) = y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.mk _ (g (f x)) = _
  rw [hgf]

include hgf in
theorem preTiltMap_comp_eq_id (y : PreTilt R p) : preTiltMap p g (preTiltMap p f y) = y :=
  Perfection.ext fun n => by
    rw [coeff_preTiltMap, coeff_preTiltMap, modPMap_comp_eq_id p f g hgf]

include hgf in
theorem wittMap_comp_eq_id (y : WittVector p (PreTilt R p)) :
    WittVector.map (preTiltMap p g) (WittVector.map (preTiltMap p f) y) = y := by
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff, preTiltMap_comp_eq_id p f g hgf]

include hgf in
theorem locMap_comp_eq_id (y : Localization.Away (p : WittVector p (PreTilt R p))) :
    locMap p g (locMap p f y) = y := by
  have h : (locMap p g).comp (locMap p f) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
    ext w
    simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
      IsLocalization.Away.lift, IsLocalization.lift_eq]
    rw [wittMap_comp_eq_id p f g hgf]
  exact congrArg (fun φ => φ y) h


include hgf in
/-- If `ker θ_R[1/p] = (a)`, then `ker θ_S[1/p] = (locMap f a)` (for an isomorphism `f`). -/
theorem ker_eq_span_locMap (hfg : ∀ y, f (g y) = y)
    (a : Localization.Away (p : WittVector p (PreTilt R p)))
    (ha : RingHom.ker (fontaineThetaInvertP R p) = Ideal.span {a}) :
    RingHom.ker (fontaineThetaInvertP S p) = Ideal.span {locMap p f a} := by
  apply le_antisymm
  · intro x hx
    have h1 : locMap p g x ∈ RingHom.ker (fontaineThetaInvertP R p) :=
      ker_le_comap_locMap p g hx
    rw [ha, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    rw [Ideal.mem_span_singleton']
    refine ⟨locMap p f c, ?_⟩
    rw [← map_mul, hc, locMap_comp_eq_id p g f hfg]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ker_le_comap_locMap p f ?_
    rw [ha]
    exact Ideal.mem_span_singleton_self a

end Inverse

section AdicOf

variable {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B) (g : A →+* B)
  (hg : J ≤ J'.comap g)

theorem adicMap_evalₐ (n : ℕ) (x : AdicCompletion J A) :
    AdicCompletion.evalₐ J' n (adicMap J J' g hg x) = adicMapAux J J' g hg n x := by
  unfold adicMap
  exact AdicCompletion.evalₐ_liftRingHom _ _ (adicMapAux_compat J J' g hg) n x

theorem adicMap_of (x : A) :
    adicMap J J' g hg (AdicCompletion.of J A x) = AdicCompletion.of J' B (g x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ, AdicCompletion.evalₐ_of]
  simp only [adicMapAux, RingHom.comp_apply]
  erw [AdicCompletion.evalₐ_of]

end AdicOf

section BdRMap


/-- The submonoid of `B_dR^+(R)` inverted in Mathlib's `BDeRham R p`. -/
def genMonoid (T : Type*) [CommRing T] [Fact ¬IsUnit (p : T)]
    [IsAdicComplete (span {(p : T)}) T] : Submonoid (BDeRhamPlus T p) :=
  Submonoid.closure <| AdicCompletion.of (RingHom.ker (fontaineThetaInvertP T p)) _ ''
    {a | RingHom.ker (fontaineThetaInvertP T p) = Ideal.span {a}}

theorem genMonoid_le_comap (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) :
    genMonoid p R ≤ (genMonoid p S).comap (bdrPlusMap p f) := by
  rw [genMonoid, Submonoid.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  apply Submonoid.subset_closure
  refine ⟨locMap p f a, (ker_eq_span_locMap p f g hgf hfg a ha), ?_⟩
  exact (adicMap_of _ _ _ _ a).symm

/-- **The map on `B_dR`** induced by a ring isomorphism `f` (with inverse `g`). Mathlib's
`BDeRham R p` is by definition `Localization (genMonoid p R)`. -/
def bdrMap (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    Localization (genMonoid p R) →+* Localization (genMonoid p S) :=
  IsLocalization.map (M := genMonoid p R) (T := genMonoid p S) (Localization (genMonoid p S))
    (bdrPlusMap p f) (genMonoid_le_comap p f g hgf hfg)

end BdRMap

end PkgI4.DR

/-! ## Abelian varieties and Tate modules: copied from pkg-I3

Lines 26-335 of `scratch/pkg-I3/I3.lean` on `origin/wip/pkg-I3` (commit 7406c0ae), unchanged:
`PkgI3.Tate.T`, `PkgI3.AbVar`, `AbVar.Pt`, `AbVar.V`, `AbVar.galRep`. Used only by the statement
`DeRhamComparison` (§3). -/

/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- `T_ℓ(M) = lim_n M[ℓⁿ]` (transition maps: multiplication by `ℓ`), realized as the
sequences `(xₙ)` with `x₀ = 0` and `ℓ • xₙ₊₁ = xₙ`; then `xₙ ∈ M[ℓⁿ]`. -/
def T : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp [smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp [hx n]

variable {ℓ M}

omit hℓ in
lemma pow_smul_eq_zero {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) : (ℓ ^ n) • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih => rw [pow_succ, mul_smul, hx.2 n, ih]

omit hℓ in
lemma nsmul_congr {y : M} {n : ℕ} (hy : (ℓ ^ n) • y = 0) {c d : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = (d : ZMod (ℓ ^ n))) : c • y = d • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div' c (ℓ ^ n), ← Nat.mod_add_div' d (ℓ ^ n), add_smul, add_smul,
    mul_smul, mul_smul, hy, smul_zero, smul_zero, h]

instance (n : ℕ) : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

lemma val_cast (a : ℤ_[ℓ]) (n : ℕ) :
    (((PadicInt.toZModPow (n + 1) a).val : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, ZMod.natCast_val]

/-- The `ℤ_ℓ`-action: `(a • x)ₙ = (a mod ℓⁿ) • xₙ`. -/
def smulSeq (a : ℤ_[ℓ]) (x : ℕ → M) : ℕ → M :=
  fun n => (PadicInt.toZModPow n a).val • x n

lemma smulSeq_mem (a : ℤ_[ℓ]) {x : ℕ → M} (hx : x ∈ T ℓ M) : smulSeq a x ∈ T ℓ M := by
  refine ⟨by simp [smulSeq, hx.1], fun n => ?_⟩
  simp only [smulSeq]
  rw [smul_comm, hx.2 n]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [val_cast, ZMod.natCast_zmod_val]

lemma smulSeq_congr {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) {a : ℤ_[ℓ]} {c : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) : smulSeq a x n = c • x n := by
  simp only [smulSeq]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [ZMod.natCast_zmod_val, h]

instance : Module ℤ_[ℓ] (T ℓ M) where
  smul a x := ⟨smulSeq a x.1, smulSeq_mem a x.2⟩
  one_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 1 x.1 n = x.1 n
    rw [smulSeq_congr x.2 n (c := 1) (by simp), one_smul]
  mul_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a * b) x.1 n = smulSeq a (smulSeq b x.1) n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n b).val)
      (by push_cast; simp), mul_smul]
    rfl
  smul_zero a := Subtype.ext <| funext fun n => by
    change smulSeq a 0 n = 0
    simp [smulSeq]
  smul_add a x y := Subtype.ext <| funext fun n => by
    change smulSeq a (x.1 + y.1) n = smulSeq a x.1 n + smulSeq a y.1 n
    simp [smulSeq, smul_add]
  add_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a + b) x.1 n = smulSeq a x.1 n + smulSeq b x.1 n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val + (PadicInt.toZModPow n b).val)
      (by push_cast; simp), add_smul]
    rfl
  zero_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 0 x.1 n = 0
    simp [smulSeq]

@[simp] lemma smul_apply (a : ℤ_[ℓ]) (x : T ℓ M) (n : ℕ) :
    (a • x).1 n = (PadicInt.toZModPow n a).val • x.1 n := rfl

variable {N : Type*} [AddCommGroup N]

/-- Functoriality: a group homomorphism `M → N` induces a `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N`. -/
def map (φ : M →+ N) : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ N where
  toFun x := ⟨fun n => φ (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_add' x y := Subtype.ext <| funext fun n => by simp
  map_smul' a x := Subtype.ext <| funext fun n => by simp [map_nsmul]

@[simp] lemma map_apply (φ : M →+ N) (x : T ℓ M) (n : ℕ) : (map φ x).1 n = φ (x.1 n) := rfl

end PkgI3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The homomorphisms `A → B` of group schemes over `K`, as a subgroup of the commutative group
of all `K`-morphisms `A → B` (pointwise product, `Hom.commGroup`). -/
def homGroup (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  one_mem' := by
    change IsMonHom (toUnit A.X ≫ η[B.X])
    infer_instance
  mul_mem' := by
    rintro f g (hf : IsMonHom f) (hg : IsMonHom g)
    change IsMonHom (lift f g ≫ μ[B.X])
    infer_instance
  inv_mem' := by
    rintro f (hf : IsMonHom f)
    change IsMonHom f⁻¹
    infer_instance

/-- `Hom_K(A, B)`, written additively (a `ℤ`-module). -/
abbrev Hom (A B : AbVar K) : Type u := Additive (homGroup A B)

/-- The underlying morphism of schemes. -/
def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul f).2

lemma Hom.ext' {A B : AbVar K} {f g : Hom A B} (h : f.hom = g.hom) : f = g :=
  Additive.toMul.injective (Subtype.ext h)

/-- Package a homomorphism. -/
def Hom.mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : Hom A B :=
  Additive.ofMul ⟨f, ‹_›⟩

@[simp] lemma Hom.hom_mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] :
    (Hom.mk' f).hom = f := rfl
@[simp] lemma Hom.hom_add {A B : AbVar K} (f g : Hom A B) : (f + g).hom = f.hom * g.hom := rfl
@[simp] lemma Hom.hom_zero {A B : AbVar K} : (0 : Hom A B).hom = 1 := rfl

/-- The endomorphism ring `End_K(A)`, with multiplication `f * g = f ∘ g`. -/
abbrev End (A : AbVar K) : Type u := Hom A A

instance (A : AbVar K) : Ring (End A) :=
  { (inferInstance : AddCommGroup (End A)) with
    mul := fun f g => Hom.mk' (g.hom ≫ f.hom)
    one := Hom.mk' (𝟙 _)
    mul_assoc := fun f g h => Hom.ext' (by simp [HMul.hMul, Mul.mul])
    one_mul := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    mul_one := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    left_distrib := fun f g h => Hom.ext' (by
      change (g + h).hom ≫ f.hom = g.hom ≫ f.hom * h.hom ≫ f.hom
      simp [MonObj.mul_comp])
    right_distrib := fun f g h => Hom.ext' (by
      change h.hom ≫ (f + g).hom = h.hom ≫ f.hom * h.hom ≫ g.hom
      simp [MonObj.comp_mul])
    zero_mul := fun f => Hom.ext' (by
      change f.hom ≫ (1 : A.X ⟶ A.X) = 1
      simp)
    mul_zero := fun f => Hom.ext' (by
      change (1 : A.X ⟶ A.X) ≫ f.hom = 1
      simp) }

/-- The endomorphism algebra `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 (A : AbVar K) : Type u := TensorProduct ℤ ℚ (End A)

/-- A morphism of `K`-schemes is an isogeny-type map: finite and surjective. -/
def IsIsogenyMor {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left ∧ Surjective f.left

/-! ### Points over a field extension and the Galois action -/

variable (L : Type u) [Field L] [Algebra K L]

/-- `Spec L` as a `K`-scheme. -/
def ptObj : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The group `A(L)` of `L`-points: `K`-morphisms `Spec L → A`. -/
abbrev Pt (A : AbVar K) : Type u := ptObj (K := K) L ⟶ A.X

variable {L}

/-- `σ ∈ Aut_K(L)` acting on `Spec L` over `K`. -/
def galHom (σ : L ≃ₐ[K] L) : ptObj (K := K) L ⟶ ptObj L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

lemma galHom_one : galHom (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) = 𝟙 (Spec (CommRingCat.of L))
  rw [show CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

lemma galHom_mul (σ τ : L ≃ₐ[K] L) : galHom (σ * τ) = galHom σ ≫ galHom τ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))
  rw [← Spec.map_comp]
  congr 1

/-- The Galois action on `A(L)`: `σ • P = P ∘ Spec(σ)`, i.e. `σ` applied to coordinates. -/
def galAct (A : AbVar K) (σ : L ≃ₐ[K] L) : A.Pt L →* A.Pt L where
  toFun P := galHom σ ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- A homomorphism `f : A → B` acting on `L`-points. -/
def ptMap {A B : AbVar K} (f : Hom A B) : A.Pt L →* B.Pt L := IsMonHom.monoidHom f.hom _

/-! ### `T_ℓ(A)`, `V_ℓ(A)` and the Galois representation -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) = lim A(K̄)[ℓⁿ]`, a `ℤ_ℓ`-module. -/
abbrev T (A : AbVar K) : Type u := Tate.T ℓ (Additive (A.Pt (AlgebraicClosure K)))

/-- `V_ℓ(A) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A)`. -/
abbrev V (A : AbVar K) : Type u := TensorProduct ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)

variable {ℓ}

/-- Galois action on `T_ℓ(A)`. -/
def galT (A : AbVar K) (σ : Field.absoluteGaloisGroup K) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ :=
  Tate.map (MonoidHom.toAdditive (A.galAct σ))

/-- A homomorphism acting on Tate modules. -/
def homT {A B : AbVar K} (f : Hom A B) : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ :=
  Tate.map (MonoidHom.toAdditive (ptMap f))

/-- Galois-equivariance of a `ℤ_ℓ`-linear map of Tate modules. -/
def IsGalEquivariant {A B : AbVar K} (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) : Prop :=
  ∀ (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ), φ (A.galT σ x) = B.galT σ (φ x)

variable (ℓ)

/-- The Galois representation `ρ_ℓ : G_K → GL(V_ℓ(A))`. -/
def galRep (A : AbVar K) : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (A.V ℓ) where
  toFun σ := (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ]
  map_one' := by
    have : A.galT (ℓ := ℓ) 1 = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (galHom (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = x.1 n
      rw [galHom_one, Category.id_comp]; rfl
    change (A.galT (ℓ := ℓ) 1).baseChange ℚ_[ℓ] = LinearMap.id
    rw [this, LinearMap.baseChange_id]
  map_mul' σ τ := by
    have : A.galT (ℓ := ℓ) (σ * τ) = A.galT σ ∘ₗ A.galT τ := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      have h := galHom_mul (K := K) (L := AlgebraicClosure K) σ τ
      change Additive.ofMul (galHom (σ * τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = Additive.ofMul (galHom σ ≫ galHom τ ≫ Additive.toMul (x.1 n))
      exact (congrArg (fun g => Additive.ofMul (g ≫ Additive.toMul (x.1 n))) h).trans
        (by rw [Category.assoc])
    change (A.galT (ℓ := ℓ) (σ * τ)).baseChange ℚ_[ℓ] =
      (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (A.galT τ).baseChange ℚ_[ℓ]
    rw [this, LinearMap.baseChange_comp]

/-- The action of `Hom(A, B)` on Tate modules, as a group homomorphism. -/
def tateHom (A B : AbVar K) : Hom A B →+ (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) where
  toFun f := homT f
  map_zero' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom]
  map_add' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom, MonObj.comp_mul]

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗_ℤ Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, `a ⊗ f ↦ a · T_ℓ(f)`. -/
def tateHomZl (A B : AbVar K) :
    TensorProduct ℤ ℤ_[ℓ] (Hom A B) →ₗ[ℤ] (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun (a : ℤ_[ℓ]) (f : Hom A B) => a • tateHom ℓ A B f)
      (fun a b f => add_smul a b _)
      (fun n a f => by rw [smul_assoc])
      (fun a f g => by rw [map_add, smul_add])
      (fun n a f => by rw [map_zsmul, smul_comm]))

end AbVar

end PkgI3

namespace PkgI4

open scoped MatrixGroups ModularForm

/-! ## §0. Galois side over `ℚ̄` -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (`PadicAlgCl ℓ` with its
spectral norm). As in Pan's paper, the coefficients are `ℚ̄_ℓ`. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

/-- A continuous character `G_ℚ → ℚ̄_ℓ^×`. -/
structure GaloisChar (ℓ : ℕ) [Fact ℓ.Prime] where
  toHom : GQ →* (PadicAlgCl ℓ)ˣ
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The matrix of `ρ(σ)`. -/
def GaloisRep.mat (ρ : GaloisRep ℓ n) (σ : GQ) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
  (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- `ρ` is ramified at only finitely many primes. -/
def GaloisRep.FinitelyRamified (ρ : GaloisRep ℓ n) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ρ.UnramifiedAt p

/-- `c` is a complex conjugation: it is `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c` (Pan, Conj. 1.0.1). -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → (ρ.mat c).det = -1

/-- `ρ` is irreducible over the algebraically closed `ℚ̄_ℓ`, in Burnside's form: the image spans
`M_n(ℚ̄_ℓ)`. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W) →
    ∃ W', IsCompl W W' ∧ ∀ σ, W'.map (Matrix.toLin' (ρ.mat σ)) ≤ W'

/-! ## §1. The local Galois group, `ℂ_p`, and Hodge–Tate multiplicities -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- `G_{ℚ_p} = Gal(ℚ̄_p/ℚ_p)`, with `ℚ̄_p = PadicAlgCl p`; this is Mathlib's
`Field.absoluteGaloisGroup ℚ_[p]`. -/
abbrev GQp := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

/-- The decomposition map `G_{ℚ_p} → G_ℚ` (restriction along an embedding `ℚ̄ → ℚ̄_p`, Mathlib's
`Field.absoluteGaloisGroup.map`). Its image is a decomposition group at a place above `p`; the
choice of embedding changes it by conjugation, which no property below depends on. -/
def decomp : GQp p →* GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
    Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ)

/-- `ρ|_{G_{ℚ_p}}`. -/
def GaloisRep.restrictLocal (ρ : GaloisRep ℓ n) : GQp p →* GL (Fin n) (PadicAlgCl ℓ) :=
  ρ.toHom.comp (decomp p)

/-- Every `σ ∈ G_{ℚ_p}` is an isometry of `ℚ̄_p` (Mathlib: `spectralNorm_eq_of_equiv`). -/
theorem norm_gqp_apply (σ : GQp p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem continuous_gqp (σ : GQp p) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_gqp_apply p σ)).continuous

/-- `σ ∈ G_{ℚ_p}` as a continuous ring endomorphism of `ℚ̄_p`. -/
def gqpRingHom (σ : GQp p) : PadicAlgCl p →+* PadicAlgCl p := σ.toAlgHom.toRingHom

theorem continuous_gqpRingHom (σ : GQp p) : Continuous (gqpRingHom p σ) :=
  continuous_gqp p σ

/-- The action of `σ ∈ G_{ℚ_p}` on `ℂ_p = ℂ_[p]`: the extension of `σ` to the completion. -/
def cpAct (σ : GQp p) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom (gqpRingHom p σ) (continuous_gqpRingHom p σ)

theorem cpAct_coe (σ : GQp p) (x : PadicAlgCl p) :
    cpAct p σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem cpAct_algebraMap (σ : GQp p) (c : ℚ_[p]) :
    cpAct p σ (algebraMap ℚ_[p] ℂ_[p] c) = algebraMap ℚ_[p] ℂ_[p] c := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    cpAct_coe, AlgEquiv.commutes]

/-- The `p`-adic cyclotomic character `χ : G_{ℚ_p} → ℤ_p^×` (Mathlib's `cyclotomicCharacter`
on `ℚ̄_p`, which contains all `p`-power roots of unity). -/
def cyc (σ : GQp p) : ℤ_[p]ˣ :=
  cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv

/-- `χ(σ)^i ∈ ℚ_p` for `i ∈ ℤ`. -/
def cycPow (σ : GQp p) (i : ℤ) : ℚ_[p] :=
  ((((cyc p σ) ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]

/-- For an `E`-linear representation `ρ` of `G_{ℚ_p}` on `V = E^n` (`E/ℚ_p` finite), the space
`H_i(ρ) = { φ : V →ₗ[ℚ_p] ℂ_p | φ(ρ(σ)v) = χ(σ)^i · σ(φ(v)) }`. It is
`(ℂ_p(i) ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}` written as equivariant maps. -/
def htSpace (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = cycPow p σ i • cpAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- **Hodge–Tate multiplicity** of the weight `w`, in the convention of N5 and Pan: the
cyclotomic character has weight `−1`. It is `dim_E (ℂ_p(−w) ⊗ V^∨)^{G}` =
`dim_E (ℂ_p(w) ⊗ V)^{G}`·, computed as `dim_{ℚ_p} H_{−w}(ρ) / [E : ℚ_p]`. (Check: for `V = ℚ_p(1)`,
`H_i ≠ 0` iff `ℂ_p(1−i)^G ≠ 0` iff `i = 1`, i.e. weight `−1`, by Tate's theorem.) -/
def htMult (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpace p ρ (-w)) / Module.finrank ℚ_[p] E

/-- `ρ` is Hodge–Tate with weight multiset `S` (`card S = n` makes it Hodge–Tate). -/
def HasHTWeights (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) : Prop :=
  ∀ w : ℤ, htMult p ρ w = S.count w

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` has Hodge–Tate weights `S`: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation has weights `S`. (The
multiplicities do not depend on `E`, by base change; STANDARD.) -/
def LocalHasHTWeights (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) (S : Multiset ℤ) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    HasHTWeights p ρE S

/-- `ρ|_{G_{ℚ_p}}` has Hodge–Tate weights `S` (for `ρ` with `ℚ̄_p` coefficients). -/
def GaloisRep.HasHTWeightsAtSelf (ρ : GaloisRep p n) (S : Multiset ℤ) : Prop :=
  LocalHasHTWeights p (ρ.restrictLocal p) S

/-- `ρ|_{G_{ℚ_p}}` has distinct Hodge–Tate weights (2-dimensional case). -/
def GaloisRep.DistinctHTWeights (ρ : GaloisRep p 2) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ρ.HasHTWeightsAtSelf p {a, b}


/-! ### Sanity check of the Hodge–Tate convention (given Tate's theorem as a hypothesis) -/

/-- `σ ↦ σ` as ring automorphisms, multiplicatively. -/
def toRingEquivHom : GQp p →* (PadicAlgCl p ≃+* PadicAlgCl p) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `ℚ_p(1)` as a one-dimensional representation over `ℚ_p`. -/
def cycRep : GQp p →* GL (Fin 1) ℚ_[p] :=
  (Units.map (algebraMap ℚ_[p] (Matrix (Fin 1) (Fin 1) ℚ_[p])).toMonoidHom).comp
    ((Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom).comp
      ((cyclotomicCharacter (PadicAlgCl p) p).comp (toRingEquivHom p)))

theorem cycPow_add_one (σ : GQp p) (j : ℤ) :
    cycPow p σ (j + 1) = cycPow p σ 1 * cycPow p σ j := by
  simp only [cycPow, zpow_add, zpow_one, Units.val_mul, PadicInt.coe_mul]
  ring

theorem cycPow_one_ne_zero (σ : GQp p) : cycPow p σ 1 ≠ 0 := by
  simp only [cycPow, zpow_one]
  intro h
  have := (cyc p σ).ne_zero
  exact this (PadicInt.ext (by simp at h))

/-- **Convention check.** If `ℂ_p(j)^{G_{ℚ_p}} = 0` for `j ≠ 0` (Tate's theorem, here a
hypothesis), then `H_i(ℚ_p(1)) = 0` for `i ≠ 1`; so `htMult` of `ℚ_p(1)` vanishes outside the
weight `−1`, which is N5's and Pan's convention. -/
theorem htSpace_cycRep_eq_bot
    (tate : ∀ j : ℤ, j ≠ 0 → ∀ c : ℂ_[p], (∀ σ : GQp p, cycPow p σ j • cpAct p σ c = c) → c = 0)
    (i : ℤ) (hi : i ≠ 1) : htSpace p (cycRep p) i = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  set e : Fin 1 → ℚ_[p] := fun _ => 1
  have hc : φ e = 0 := by
    refine tate (i - 1) (by omega) (φ e) fun σ => ?_
    have h := hφ σ e
    have hmv : Matrix.mulVec ((cycRep p σ : GL (Fin 1) ℚ_[p]) : Matrix (Fin 1) (Fin 1) ℚ_[p]) e =
        cycPow p σ 1 • e := by
      ext k
      fin_cases k
      simp [cycRep, e, Matrix.mulVec, dotProduct, cycPow, toRingEquivHom, cyc,
        Algebra.algebraMap_eq_smul_one, PadicInt.Coe.ringHom_apply]
      rfl
    rw [hmv, map_smul] at h
    have h2 : cycPow p σ 1 • φ e = (cycPow p σ 1 * cycPow p σ (i - 1)) • cpAct p σ (φ e) := by
      rw [← cycPow_add_one]; simpa using h
    rw [mul_smul] at h2
    exact (smul_right_injective _ (cycPow_one_ne_zero p σ) h2).symm
  refine LinearMap.ext fun v => ?_
  have hv : v = v 0 • e := by
    ext k; fin_cases k; simp [e]
  rw [LinearMap.zero_apply, hv, map_smul, hc, smul_zero]

theorem htMult_cycRep_eq_zero
    (tate : ∀ j : ℤ, j ≠ 0 → ∀ c : ℂ_[p], (∀ σ : GQp p, cycPow p σ j • cpAct p σ c = c) → c = 0)
    (w : ℤ) (hw : w ≠ -1) : htMult p (cycRep p) w = 0 := by
  rw [htMult, htSpace_cycRep_eq_bot p tate (-w) (by omega), finrank_bot, Nat.zero_div]

end Local

/-! ## §1b. The action of `G_{ℚ_p}` on `B_dR` and the de Rham predicate -/

section DeRham

variable (p : ℕ) [Fact p.Prime]

theorem continuous_cpAct (σ : GQp p) : Continuous (cpAct p σ) :=
  UniformSpace.Completion.continuous_map

theorem norm_cpAct (σ : GQp p) (x : ℂ_[p]) : ‖cpAct p σ x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (continuous_cpAct p σ)) continuous_norm
  | ih a => rw [cpAct_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_gqp_apply]

theorem cpAct_inv_apply (σ : GQp p) (x : ℂ_[p]) : cpAct p σ⁻¹ (cpAct p σ x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_cpAct p _).comp (continuous_cpAct p σ)) continuous_id
  | ih a =>
    rw [cpAct_coe, cpAct_coe, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- `σ` acting on `𝓞_ℂ_[p]`. -/
def oAct (σ : GQp p) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
  (cpAct p σ).restrict 𝓞_ℂ_[p] 𝓞_ℂ_[p] fun x hx => by
    rw [Cp.mem_O_iff, norm_cpAct]
    exact (Cp.mem_O_iff p x).mp hx

theorem oAct_inv_apply (σ : GQp p) (x : 𝓞_ℂ_[p]) : oAct p σ⁻¹ (oAct p σ x) = x :=
  Subtype.ext (cpAct_inv_apply p σ x)

theorem oAct_apply_inv (σ : GQp p) (x : 𝓞_ℂ_[p]) : oAct p σ (oAct p σ⁻¹ x) = x := by
  simpa using oAct_inv_apply p σ⁻¹ x

/-- `B_dR = B_dR(𝓞_ℂ_p)`: Mathlib's `BDeRham (𝓞_ℂ_[p]) p`, unfolded (see `bdR_eq`). -/
abbrev BdR := Localization (DR.genMonoid p 𝓞_ℂ_[p])

example : BdR p = BDeRham 𝓞_ℂ_[p] p := rfl

/-- **The action of `G_{ℚ_p}` on `B_dR`**, by functoriality of Mathlib's construction. -/
def bdrAct (σ : GQp p) : BdR p →+* BdR p :=
  DR.bdrMap p (oAct p σ) (oAct p σ⁻¹) (oAct_inv_apply p σ) (oAct_apply_inv p σ)

/-! ### `ℚ_p ⊆ B_dR`, fixed by `G_{ℚ_p}` -/

instance isLocalization_padic : IsLocalization (Submonoid.powers (p : ℤ_[p])) ℚ_[p] where
  map_units := by
    rintro ⟨_, k, rfl⟩
    exact IsUnit.mk0 _ (by simp [Fact.out (p := p.Prime) |>.ne_zero])
  surj z := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (‖z‖ + 1))
      (by simpa using (Padic.norm_p_lt_one (p := p)))
    refine ⟨⟨⟨(p : ℚ_[p]) ^ k * z, ?_⟩, ⟨(p : ℤ_[p]) ^ k, k, rfl⟩⟩, ?_⟩
    · change ‖(p : ℚ_[p]) ^ k * z‖ ≤ 1
      rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : (p : ℝ)⁻¹ ^ k * (‖z‖ + 1) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg z, pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)) k]
    · change z * (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * z
      push_cast
      ring
  exists_of_eq {x y} h := ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact PadicInt.ext h⟩

/-- `ℤ_p = W(𝔽_p) → W(𝓞_ℂ_p♭)`. -/
def zpToW : ℤ_[p] →+* WittVector p (PreTilt 𝓞_ℂ_[p] p) :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

/-- `ℚ_p → W(𝓞_ℂ_p♭)[1/p]`. -/
def qpToLoc : ℚ_[p] →+* Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :=
  IsLocalization.lift (M := Submonoid.powers (p : ℤ_[p]))
    (g := (algebraMap _ _).comp (zpToW p)) (by
      rintro ⟨_, k, rfl⟩
      have := (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
        (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))).pow k
      rw [map_natCast] at this
      simpa only [RingHom.comp_apply, map_pow, map_natCast] using this)

/-- `W(R♭)[1/p] → B_dR^+`. -/
def ofLoc : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) →+*
    BDeRhamPlus 𝓞_ℂ_[p] p :=
  algebraMap _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))))

/-- `ℚ_p → B_dR`. -/
def qpToBdR : ℚ_[p] →+* BdR p :=
  (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp ((ofLoc p).comp (qpToLoc p))

theorem wittMap_zpToW (f : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p) (z : ℤ_[p]) :
    WittVector.map f (zpToW p z) = zpToW p z := by
  ext n
  simp only [zpToW, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) _)) _

theorem qpToLoc_algebraMap (z : ℤ_[p]) :
    qpToLoc p (algebraMap ℤ_[p] ℚ_[p] z) = algebraMap _ _ (zpToW p z) :=
  IsLocalization.lift_eq _ _

theorem locMap_algebraMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (w : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :
    DR.locMap p f (algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) w) =
      algebraMap _ _ (WittVector.map (DR.preTiltMap p f) w) := by
  unfold DR.locMap Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_eq]
  rfl

theorem bdrPlusMap_ofLoc (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p])
    (y : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    DR.bdrPlusMap p f (ofLoc p y) = ofLoc p (DR.locMap p f y) := by
  have e : ∀ y', ofLoc p y' = AdicCompletion.of _ _ y' := fun y' => by
    rw [ofLoc]
    erw [AdicCompletion.algebraMap_apply]
  rw [e, e]
  exact DR.adicMap_of _ _ _ _ y

/-- `G_{ℚ_p}` fixes `ℚ_p ⊆ B_dR`. -/
theorem bdrAct_qpToBdR (σ : GQp p) (c : ℚ_[p]) : bdrAct p σ (qpToBdR p c) = qpToBdR p c := by
  have h : (bdrAct p σ).comp (qpToBdR p) = qpToBdR p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToBdR]
    rw [qpToLoc_algebraMap, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_ofLoc,
      locMap_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

/-- `B_dR` as a `ℚ_p`-algebra (through `qpToBdR`). -/
instance : Algebra ℚ_[p] (BdR p) := (qpToBdR p).toAlgebra

theorem bdrAct_smul (σ : GQp p) (c : ℚ_[p]) (x : BdR p) :
    bdrAct p σ (c • x) = c • bdrAct p σ x := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  exact bdrAct_qpToBdR p σ c

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `D_dR(V^∨) = (B_dR ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}`, written as `G_{ℚ_p}`-equivariant `ℚ_p`-linear maps
`V → B_dR`, for `V = E^n` with `E`-linear action `ρ`. -/
def ddrSpace (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = bdrAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v, bdrAct_smul]

/-- **`ρ` is de Rham** (Fontaine): `dim_{ℚ_p} D_dR = dim_{ℚ_p} V`. Stated for `V^∨` (equivalent:
`V` is de Rham iff `V^∨` is; Fontaine, Astérisque 223, Thm 3.8; STANDARD), with `K = ℚ_p`. -/
def IsDeRham (ρ : GQp p →* GL (Fin n) E) : Prop :=
  Module.finrank ℚ_[p] (ddrSpace p ρ) = n * Module.finrank ℚ_[p] E

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is de Rham: it takes values in `GL_n(E)` for a
finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation is de Rham. -/
def LocalIsDeRham (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsDeRham p ρE


/-! ### Sanity check of `IsDeRham` (given `B_dR^{G_{ℚ_p}} = ℚ_p` as a hypothesis) -/

/-- **Normalization check.** If every `G_{ℚ_p}`-invariant of `B_dR` lies in `ℚ_p` (Fontaine's
`B_dR^{G_{ℚ_p}} = ℚ_p`, here a hypothesis) and `ℚ_p → B_dR` is injective, then the trivial
one-dimensional representation is de Rham in the sense of `IsDeRham`. -/
theorem isDeRham_trivial
    (hfix : ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p))
    (hinj : Function.Injective (qpToBdR p)) :
    IsDeRham p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
  set e : Fin 1 → ℚ_[p] := fun _ => 1
  -- the evaluation-at-`0` functional, followed by `ℚ_p → B_dR`
  set φ₀ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] BdR p :=
    (LinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin 1 => ℚ_[p]) 0).smulRight (1 : BdR p)
  have hφ₀ : ∀ v, φ₀ v = qpToBdR p (v 0) := fun v => by
    simp [φ₀, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hmem : φ₀ ∈ ddrSpace p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
    intro σ v
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec, hφ₀, bdrAct_qpToBdR]
  have hne : φ₀ ≠ 0 := by
    intro h
    have h1 := congrArg (fun ψ => ψ e) h
    simp only [hφ₀, LinearMap.zero_apply, e] at h1
    exact one_ne_zero (hinj (h1.trans (map_zero _).symm))
  have hspan : ddrSpace p (1 : GQp p →* GL (Fin 1) ℚ_[p]) = ℚ_[p] ∙ φ₀ := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := hfix (φ e) fun σ => by
        have := hφ σ e
        simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec] at this
        exact this.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨c, LinearMap.ext fun v => ?_⟩
      have hv : v = v 0 • e := by ext k; fin_cases k; simp [e]
      rw [LinearMap.smul_apply, hφ₀, hv, map_smul, ← hc]
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hmem
  rw [IsDeRham, hspan, finrank_span_singleton hne, Module.finrank_self]


/-! ### Over a finite extension `F/ℚ_p`, for any `ℚ_p`-linear representation

These forms take a Mathlib `Representation` of `G_F = Field.absoluteGaloisGroup F`, which is the
shape of pkg-I3's `AbVar.galRep` (the Galois action on `V_p(A)`); with them the comparison leaf of
C3 can be stated over genuine definitions (note §1.2). -/

section Over

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `G_F → G_{ℚ_p}` (restriction along an embedding `ℚ̄_p → F̄`; Mathlib's
`Field.absoluteGaloisGroup.map`). It is injective with image `G_{F'}`, `F'` the image of `F`. -/
def gfToGqp : Field.absoluteGaloisGroup F →* GQp p :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ_[p] F) :
    Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup ℚ_[p])

variable {F} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `D_dR,F(V^∨)` as `G_F`-equivariant `ℚ_p`-linear maps `V → B_dR`. -/
def ddrSpaceOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ σ v, φ (ρ σ v) = bdrAct p (gfToGqp p F σ) (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v, bdrAct_smul]

/-- `V` (finite-dimensional over `ℚ_p`) is de Rham as a `G_F`-representation:
`dim_F D_dR,F = dim_{ℚ_p} V`, i.e. `dim_{ℚ_p} D_dR,F = [F:ℚ_p] · dim_{ℚ_p} V`. -/
def IsDeRhamOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) : Prop :=
  Module.finrank ℚ_[p] (ddrSpaceOver p ρ) = Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] V

/-- `H_i` over `F`: `G_F`-equivariant maps `V → ℂ_p(i)`. -/
def htSpaceOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    Submodule ℚ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ σ v,
    φ (ρ σ v) = cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- Hodge–Tate multiplicity of `w` for a `G_F`-representation on a `ℚ_p`-space (cyclotomic
weight `−1`): `dim_F (ℂ_p(−w) ⊗ V^∨)^{G_F}`. For `V_p(A)`, `dim A = g`, the multiplicities are
`g` at `0` and `g` at `−1`. -/
def htMultOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpaceOver p ρ (-w)) / Module.finrank ℚ_[p] F

end Over

end DeRham

/-! ## §2. Modular side -/

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators `T_n` with nebentypus `χ`, through its
coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}`. Equivalent to the
Hecke definition for forms with nebentypus `χ` (Diamond–Shurman Prop. 5.3.1 and §5.8; locator
UNVERIFIED). Same as hdec-faithful. -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `τ ↦ dτ` on `ℍ`, for `d ≥ 1`. -/
def scaleH (d : ℕ+) (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(d : ℂ) * (τ : ℂ), by
    have h := τ.coe_im_pos
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast d.pos) h⟩

/-- The **old space** of level `N`, weight `k`: the span of the functions `τ ↦ f(dτ)` with
`f ∈ S_k(Γ₁(M))`, `M ∣ N`, `M < N`, `d ∣ N/M` (Atkin–Lehner, Li 1975 §1). -/
def oldSpace (N : ℕ) (k : ℤ) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ {F | ∃ (M : ℕ) (d : ℕ+) (f : CF M k), 0 < M ∧ M ∣ N ∧ M < N ∧
    (d : ℕ) * M ∣ N ∧ F = fun τ => f (scaleH d τ)}

/-- `f` is a **newform** of level `N`: a normalized eigenform of all `T_n` not lying in the old
space. For an eigenform of all `T_n` this is equivalent to Li's definition (orthogonal to the
old space for the Petersson product): the new and old spaces are stable under all `T_n` and, by
strong multiplicity one, share no eigensystem away from `N` (Li 1975, Thms 3 and 5;
Diamond–Shurman Thm 5.8.2; locators UNVERIFIED). The Petersson definition needs the Petersson
integral over `Γ₁(N)\ℍ`, which Mathlib lacks (it has the integrand, `petersson`). -/
def IsNewform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  IsNormalizedEigenform f χ ∧ (⇑f : UpperHalfPlane → ℂ) ∉ oldSpace N k

/-- `ρ` is attached to the eigenform `g` (through `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`), in the
Tate-module normalization (arithmetic Frobenius, `tr = a_p`): for `p ∤ Nℓ`, `ρ` is unramified at
`p` and every arithmetic Frobenius above `p` has trace `ιL(α)` with `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = ιL α

/-- `ρ` is attached to `g` **up to the twist** `ψ`, outside a finite set `S`: Pan's conclusion
"comes from a cuspidal eigenform up to twist", in trace form (see `PanFor`). -/
def GaloisRep.AttachedUpToTwist (ρ : GaloisRep ℓ 2) (ψ : GaloisChar ℓ) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (g : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl ℓ) * ιL α

/-! ## §3. Leaves of I4 statable now (statements only; none is proved) -/

/-- **I4-L0. de Rham comparison for abelian varieties, with Hodge–Tate weights** (C3; Fontaine,
LNM 1016 (1983) and Fontaine–Messing (1987) for abelian varieties; Faltings 1989; Tsuji 1999 with
de Jong; Scholze 2013 Cor. 1.8 with Thms 9.1, 9.3 and the 2016 corrigendum; with
`V_p(A) ≅ H¹_et(A_F̄, ℚ_p)^∨`, Mumford §§19-20 / Milne 1986 Thm 15.1(a); numbers UNVERIFIED except
Scholze's wording, VERIFIED by h-leaves §3.1). For an abelian variety `A` of dimension `g` over a
finite extension `F` of `ℚ_p`, `V_p(A)` (pkg-I3's `galRep`) is de Rham as a
`G_F`-representation, with Hodge–Tate weight `0` and `−1` each of multiplicity `g`. Consequence
form. Statable now over genuine definitions: pkg-I3's abelian varieties and Tate modules, and
§1b's `IsDeRhamOver`, `htMultOver`. -/
def DeRhamComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
      htMultOver p (A.galRep p) (-1) = g

/-- **I4-L1. Galois representations of eigenforms** (Eichler–Shimura and Shimura 1971 Thm 7.14
for `k = 2`; Deligne 1971 for `k ≥ 2`; Deligne–Serre 1974 Thm 6.1 for `k = 1`; theorem numbers
UNVERIFIED). Consequence form (the published statements also give the determinant
`ε_g χ^{k−1}`). Same as hdec-faithful L27(a). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **I4-L2. Hodge–Tate weights of eigenform representations, every level** (Faltings, Math.
Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level); Kato, Astérisque 295 (2004) §9.4 (de Rham, every level); Scholl 1990
with Scholze 2013 and Fontaine's closure). A semisimple `ρ` attached to a normalized eigenform of
weight `k ≥ 2` and any level `N` (including `ℓ ∣ N`) is Hodge–Tate at `ℓ` with weights
`{0, 1 − k}` in the Tate normalization (cyclotomic weight `−1`; h-trust C8). Consequence form
(the published theorems give de Rham or pst, which imply Hodge–Tate with the same weights). -/
def EigenformHT : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

/-- **I4-L3. Deligne–Serre** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with Chebotarev and
Brauer–Nesbitt): a semisimple `ρ` attached to a weight-one eigenform has finite image.
Consequence form. Same as hdec-faithful L27(b). -/
def DeligneSerreFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **I4-L4. Twisting an eigenform** (Shimura 1971 Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978)
Prop. 3.1; locators UNVERIFIED). Consequence form. Same as hdec-faithful L28(a). -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p

/-- **I4-L5. Newform attached to an eigensystem** (Li, Math. Ann. 212 (1975), Thm 5 (strong
multiplicity one) with the decomposition `S_k = S_k^new ⊕ S_k^old`; Miyake Thm 4.6.19; locators
UNVERIFIED). Every normalized eigenform of level `M` has the Hecke eigenvalues away from `M` of a
newform of level dividing `M`. Consequence form. -/
def NewformOfEigenform : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p

/-- **I4-L6. Carayol at unramified primes** (Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), the
case "conductor exponent 0"; theorem letter VERIFIED from N5 L9778's locator, content
UNVERIFIED). For a newform `f` of weight 2 and level `N` and a semisimple `ρ` attached to it, a
prime `p ≠ ℓ` at which `ρ` is unramified does not divide `N`. Consequence form (Théorème (A)
gives `v_p(N) =` the conductor exponent, which is 0 exactly when `ρ` is unramified). -/
def CarayolUnramified : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → ρ.UnramifiedAt p → ¬ p ∣ N

/-! ## §4. Templates (not leaves) and the statable Pan∘Berger leaf

`PanFor IsPst` is Pan's theorem once `IsPst` is the genuine "potentially semistable in the sense
of Fontaine" predicate on `ℚ̄_p`-representations of `G_{ℚ_p}`; for any other argument it means
nothing. Likewise for `BergerFor`, `CarayolFor`. -/

/-- A predicate on `ℚ̄_p`-valued representations of `G_{ℚ_p}`, for every `p` and `n`. -/
abbrev LocalPred := ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), (GQp p →* GL (Fin n) (PadicAlgCl p)) → Prop

/-- **Template for I4-L7, Pan's theorem** (Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169,
Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 from the arXiv
source; JAMS numbering UNVERIFIED)), for `p ≥ 5` (which drops the `p = 3` residual clause):
a continuous irreducible `ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially
semistable at `p`, odd, with distinct Hodge–Tate weights at `p`, comes from a cuspidal eigenform
up to twist. The conclusion is in trace form: some normalized eigenform `g`, continuous `ψ` and
embeddings with `tr ρ(Frob_q) = ψ(Frob_q) ι(a_q(g))` for almost all `q`. Every reading of
"comes from … up to twist" implies it, in either Frobenius normalization, since
`U^∨ ≅ U ⊗ det U⁻¹` in dimension 2 (h-trust C8; pkg-I4 note §2.1). -/
def PanFor (IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ρ : GaloisRep p 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → IsPst p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    ρ.DistinctHTWeights p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl p) (S : Finset ℕ),
        ρ.AttachedUpToTwist ψ ιC ιL g S

/-- **I4-L7′. Pan∘Berger — statable now, over genuine definitions.** Pan's Theorem 1.0.4
(`PanFor`, `p ≥ 5`) with "de Rham at `p`" (`LocalIsDeRham`, built in §1b on Mathlib's `BDeRham`)
in place of "potentially semistable at `p`". It is a consequence of Pan 2022 Thm 1.0.4 together
with Berger 2002 Thm 0.7 (de Rham ⇒ pst), and it is the form N5 uses (N5 L734-741 proves de Rham
and then applies Berger). Needs no `B_st`. -/
def PanBerger : Prop :=
  PanFor fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsDeRham p n ρ

/-- **Template for I4-L8, Berger's theorem** (Invent. Math. 148 (2002), Théorème 0.7 in the
published numbering (ASTRA-READ), = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3 (VERIFIED by
rv-h-a011)): de Rham ⇒ potentially semistable. -/
def BergerFor (IsDR IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → IsDR p n ρ → IsPst p n ρ

/-- **I4-L8′. Berger with the genuine de Rham predicate** (template only in `IsPst`). -/
def BergerDR (IsPst : LocalPred) : Prop :=
  BergerFor (fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsDeRham p n ρ) IsPst

/-- A conductor-exponent function: `a ℓ ρ p` is the Artin conductor exponent at `p ≠ ℓ` of the
`ℓ`-adic representation `ρ` (Weil–Deligne / Serre's definition). Missing in every library. -/
abbrev CondExp := ∀ (ℓ : ℕ) [Fact ℓ.Prime], GaloisRep ℓ 2 → ℕ → ℕ

/-- **Template for I4-L9, Carayol's Théorème (A)** at `F = ℚ`, weight 2 (the case N5 uses):
for a newform `f` of level `N` and a semisimple `ρ` attached to it, `v_p(N) = a(ρ, p)` for every
prime `p ≠ ℓ`. -/
def CarayolFor (a : CondExp) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → a ℓ ρ p = N.factorization p

/-! ## §5. Glue facts, proved -/

/-- **C8 weight comparison** (Tate normalization). If `ρ ≅ ρ_g ⊗ ψ` with `ψ` Hodge–Tate of
weight `n`, the weights of `ρ` are `{n, n + 1 − k}`; if they are `{0, −1}` and `k ≥ 1`, then
`n = 0` and `k = 2`. Stated on multisets. -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) : n = 0 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

/-- The same comparison in Pan's cohomological normalization (weights of `ρ_g` are `{0, k−1}`):
`{n, n + k − 1} = {0, −1}` with `k ≥ 1` forces `k = 2`, `n = −1` (twist by `χ¹`; h-trust C8,
rv-h-c8 `weights.py`). -/
theorem weight_match_coh (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + k - 1} : Multiset ℤ) = {0, -1}) : n = -1 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

end PkgI4

end

#print axioms PkgI4.Cp.isAdicComplete
#print axioms PkgI4.DR.fontaineTheta_naturality
#print axioms PkgI4.DR.bdrMap
#print axioms PkgI4.bdrAct_qpToBdR
#print axioms PkgI4.IsDeRham
#print axioms PkgI4.PanBerger
#print axioms PkgI4.htMult_cycRep_eq_zero
#print axioms PkgI4.isDeRham_trivial
#print axioms PkgI4.DeRhamComparison
#print axioms PkgI4.weight_match
#print axioms PkgI4.weight_match_coh
#print axioms PkgI4.cpAct_algebraMap
