/- leaf-push: T23 (Fontaine's closure properties) over pkg-I4's de Rham predicate.
Lines 1-1108 are copied verbatim from scratch/pkg-I4/I4.lean (scratch files cannot import each
other); the new statement is at the end. No sorry, no axiom. -/
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



end DeRham

/-! ## leaf-push: T23, Fontaine's closure properties of de Rham representations -/

section Fontaine

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ ρ(σ)` is continuous for the Krull topology and the `p`-adic topology on matrices. -/
def ContRep {n : ℕ} (ρ : GQp p →* GL (Fin n) ℚ_[p]) : Prop :=
  Continuous fun σ => (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])

/-- **T23. Fontaine's closure properties.** Published statement: Fontaine, *Représentations
p-adiques des corps locaux I*, Astérisque 223 (1994), Exp. III, §1.5 (admissible representations
for a regular period ring form a Tannakian subcategory: stable under subobjects, quotients, direct
sums, tensor products, duals) applied to `B = B_dR` (regular, Exp. II §3 / Exp. III Thm 3.8;
numbering UNVERIFIED; also Brinon–Conrad, CMI notes, Thm 5.2.1, Prop. 6.3.3, 6.3.8). Lean form,
for continuous `ℚ_p`-linear representations of `G_{ℚ_p}` on `ℚ_pⁿ` and pkg-I4's predicate
`IsDeRham` (`dim_{ℚ_p} D_dR = n`, `D_dR` computed on `V^∨`, which is equivalent by the dual
clause): (i) invariance under change of basis; (ii) duals (`σ ↦ ρ(σ)⁻ᵀ`); (iii) subquotients:
if `ρ` is block upper triangular with diagonal blocks `ρ₁, ρ₂` (`ρ₁` the subrepresentation on
the first `a` coordinates, `ρ₂` the quotient), then `ρ` de Rham ⇒ `ρ₁, ρ₂` de Rham; (iv) direct
sums (block diagonal); (v) tensor products (Kronecker product, reindexed by `Fin a × Fin b ≃
Fin (a * b)`). Every clause is a special case of the published statement (matrix form of the
same representations); (i) is the basis independence of `dim D_dR`, a triviality included so
that the leaf is basis-free. Exact. -/
def T23_FontaineClosure : Prop :=
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]) (P : GL (Fin n) ℚ_[p]),
    (∀ σ, ρ' σ = P * ρ σ * P⁻¹) → (IsDeRham p ρ ↔ IsDeRham p ρ')) ∧
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose) →
    IsDeRham p ρ → IsDeRham p ρ') ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]) (X : GQp p → Matrix (Fin a) (Fin b) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) (X σ) 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ → IsDeRham p ρ₁ ∧ IsDeRham p ρ₂) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ₁ → IsDeRham p ρ₂ → IsDeRham p ρ) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a * b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a * b)) (Fin (a * b)) ℚ_[p]) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ₁ → IsDeRham p ρ₂ → IsDeRham p ρ)

end Fontaine

end PkgI4

open Lean Elab Command in
elab "#rvw17_check_axioms" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut cnt : Nat := 0
  for (n, _) in env.constants.map₂.toList do
    if n.isInternal then continue
    cnt := cnt + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.any (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]) then
      bad := bad.push n
      logInfo m!"BAD {n}: {axs}"
  logInfo m!"rvw17: {cnt} declarations checked, {bad.size} with nonstandard axioms"

#rvw17_check_axioms
