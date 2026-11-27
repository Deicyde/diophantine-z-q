import ZInQKernel.Contrib.OneProof.HeightModelM3.Spans

/-! # The `𝒪_S(V)`-action on the Hodge line and the one-factor wedge identity

The Hodge line is `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`; its scalars are `L`, acting
on the left factor. The generic stalk `𝒪_{S,η}` of `S = Spec 𝓞_L` is a localization of `𝓞_L` at
the zero ideal, so it is identified with `L` (`etaFieldEquiv : 𝒪_{S,η} ≃ₐ[𝓞_L] L`). A function
`c ∈ 𝒪_S(V)` on an open `V ∋ η` restricts to `c|_η = germEta V hV c ∈ 𝒪_{S,η}`, hence to an element
of `L` (`germEtaField V hV c`). This is the natural action of `𝒪_S(V)` on the Hodge line
(`hodgeAction`: `c • y = c|_η • y`).

What is proved:

* `smul_cotangent_eq_of_algebraMap_eq`: `x ∈ 𝒪_{𝒢,ξ}` acts on `𝔪_ξ/𝔪_ξ²` through its image
  `e^♯(x) ∈ 𝒪_{S,η}` (two elements with the same image act in the same way, since
  `ker e^♯ = 𝔪_ξ` kills `𝔪_ξ/𝔪_ξ²`);
* `etaFieldEquiv_smul_wedge`, the wedge identity: for every `x ∈ 𝒪_{𝒢,ξ}`, every `v₁, …, v_g` and
  every index `i`, `e^♯(x) • (1 ⊗ v₁ ∧ ⋯ ∧ v_g) = 1 ⊗ v₁ ∧ ⋯ ∧ (x • v_i) ∧ ⋯ ∧ v_g` (by
  multilinearity: write `e^♯(x) = a/t`, then `x` acts as `a · t⁻¹`);
* `germEtaField_smul_wedge`: hence, for a lift `x` of `c ∈ 𝒪_S(V)`,
  `c|_η • (1 ⊗ v₁ ∧ ⋯ ∧ v_g) = 1 ⊗ v₁ ∧ ⋯ ∧ (x • v_i) ∧ ⋯ ∧ v_g`;
* `germEtaField_smul_mem_detSec` and `detSecSubmodule`: for `g ≥ 1`, `detSec V W` is an
  `𝒪_S(V)`-submodule of the Hodge line for this action;
* `germEtaField_smul_mem_detSecNear`, `germEtaField_smul_mem_globalDetLattice` and
  `globalDetLatticeSubmodule`: the sections near `s ∈ V` are stable under `𝒪_S(V)`, and the global
  lattice `globalDetLattice` is a `Γ(S, 𝒪_S)`-submodule.

The closure statements assume `g ≥ 1`. For `g = 0` they are not claimed: `⋀^0 e*Ω¹ = 𝒪_S` has
sections `𝒪_S(V)` over `V`, while the tree's `detSec` is the `𝓞_L`-span of the empty wedge. -/
open CategoryTheory AlgebraicGeometry
open NumberField
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal ZInQ.HeightModelM2
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM4

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

/-! ## The scalars of the Hodge line: `𝒪_{S,η} ≅ L` -/

/-- In the domain `𝓞_L`, the complement of the zero ideal is the set of non-zero-divisors. -/
theorem primeCompl_bot_eq_nonZeroDivisors :
    (⊥ : Ideal (𝓞 L)).primeCompl = nonZeroDivisors (𝓞 L) := by
  ext a
  rw [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero, Ideal.mem_bot]

/-- `L` is the localization of `𝓞_L` at the zero ideal. -/
theorem isLocalization_bot_field : IsLocalization (⊥ : Ideal (𝓞 L)).primeCompl L := by
  rw [primeCompl_bot_eq_nonZeroDivisors]; infer_instance

/-- **`𝒪_{S,η} ≅ L`**: both are localizations of `𝓞_L` at the zero ideal. -/
noncomputable def etaFieldEquiv : Reta L ≃ₐ[𝓞 L] L :=
  haveI := ZInQ.HeightDict.Conormal.isLocalization_Reta (L := L)
  haveI := isLocalization_bot_field (L := L)
  IsLocalization.algEquiv (⊥ : Ideal (𝓞 L)).primeCompl (Reta L) L

theorem etaFieldEquiv_algebraMap (a : 𝓞 L) :
    etaFieldEquiv (algebraMap (𝓞 L) (Reta L) a) = algebraMap (𝓞 L) L a :=
  AlgEquiv.commutes _ a

/-! ## The action of `𝒪_S(V)` -/

/-- **Restriction to the generic point**, `c ↦ c|_η ∈ 𝒪_{S,η} ≅ L`, for an open `V ∋ η`. -/
noncomputable def germEtaField (V : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (hV : genericPt L ∈ V) : Γ(Spec (CommRingCat.of (𝓞 L)), V) →+* L :=
  (etaFieldEquiv (L := L) : Reta L →+* L).comp
    ((Spec (CommRingCat.of (𝓞 L))).presheaf.germ V (genericPt L) hV).hom

theorem germEtaField_apply (V : (Spec (CommRingCat.of (𝓞 L))).Opens) (hV : genericPt L ∈ V)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) :
    germEtaField V hV c = etaFieldEquiv (germEta V hV c) :=
  rfl

/-- Restriction to the generic point commutes with restriction to a smaller open. -/
theorem germEtaField_res {V V' : (Spec (CommRingCat.of (𝓞 L))).Opens} (h : V' ≤ V)
    (hV' : genericPt L ∈ V') (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) :
    germEtaField V' hV' ((Spec (CommRingCat.of (𝓞 L))).presheaf.map (homOfLE h).op c) =
      germEtaField V (h hV') c := by
  simp only [germEtaField_apply, germEta]
  rw [TopCat.Presheaf.germ_res_apply]

variable (𝒢 : GroupModel A L)

/-- **The natural action of `𝒪_S(V)` on the Hodge line**: `c` acts as the scalar
`c|_η ∈ 𝒪_{S,η} ≅ L`. -/
noncomputable def hodgeAction (g : ℕ) (V : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (hV : genericPt L ∈ V) : Module Γ(Spec (CommRingCat.of (𝓞 L)), V) (𝒢.hodgeSpace g) :=
  Module.compHom (𝒢.hodgeSpace g) (germEtaField V hV)

theorem hodgeAction_smul (g : ℕ) (V : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (hV : genericPt L ∈ V) (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) (y : 𝒢.hodgeSpace g) :
    letI := hodgeAction 𝒢 g V hV
    c • y = germEtaField V hV c • y :=
  rfl

/-! ## `𝒪_{𝒢,ξ}` acts on `𝔪_ξ/𝔪_ξ²` through `e^♯` -/

/-- `𝔪_ξ` kills `𝔪_ξ/𝔪_ξ²`. -/
theorem smul_eq_zero_of_mem_maximalIdeal {z : 𝒢.genStalk}
    (hz : z ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) (m : 𝒢.cotangent) : z • m = 0 := by
  have key : ∀ m : IsLocalRing.CotangentSpace 𝒢.genStalk, z • m = 0 := by
    intro m
    obtain ⟨w, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective m
    rw [← map_smul, Ideal.toCotangent_eq_zero, Submodule.coe_smul, smul_eq_mul, pow_two]
    exact Ideal.mul_mem_mul hz w.2
  exact key m

/-- **`x ∈ 𝒪_{𝒢,ξ}` acts on `𝔪_ξ/𝔪_ξ²` through `e^♯(x) ∈ 𝒪_{S,η}`**: elements with the same
image under `e^♯ : 𝒪_{𝒢,ξ} → 𝒪_{S,η}` act in the same way. -/
theorem smul_cotangent_eq_of_algebraMap_eq {x y : 𝒢.genStalk}
    (h : algebraMap 𝒢.genStalk (Reta L) x = algebraMap 𝒢.genStalk (Reta L) y)
    (m : 𝒢.cotangent) : x • m = y • m := by
  have hz : x - y ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    rw [← ZInQ.HeightDict.Conormal.ker_eq_maximalIdeal 𝒢, RingHom.mem_ker, map_sub, h,
      sub_self]
  rw [← sub_eq_zero, ← sub_smul]
  exact smul_eq_zero_of_mem_maximalIdeal 𝒢 hz m

/-! ## The wedge identity -/

/-- **The one-factor wedge identity in the Hodge line**: for `x ∈ 𝒪_{𝒢,ξ}`,
`e^♯(x) • (1 ⊗ v₁ ∧ ⋯ ∧ v_g) = 1 ⊗ v₁ ∧ ⋯ ∧ (x • v_i) ∧ ⋯ ∧ v_g`, with `e^♯(x) ∈ 𝒪_{S,η} ≅ L`.
Write `e^♯(x) = a/t` with `a, t ∈ 𝓞_L`, `t ≠ 0`; then `t` is a unit of `𝒪_{𝒢,ξ}`, `x` acts on
`𝔪_ξ/𝔪_ξ²` as `a · t⁻¹`, and both sides are `a ⊗ v₁ ∧ ⋯ ∧ (t⁻¹ v_i) ∧ ⋯ ∧ v_g` by
multilinearity. -/
theorem etaFieldEquiv_smul_wedge {g : ℕ} (v : Fin g → 𝒢.cotangent) (i : Fin g)
    (x : 𝒢.genStalk) :
    etaFieldEquiv (algebraMap 𝒢.genStalk (Reta L) x) •
        ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (Function.update v i (x • v i)) := by
  haveI := ZInQ.HeightDict.Conormal.isLocalization_Reta (L := L)
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (⊥ : Ideal (𝓞 L)).primeCompl
    (algebraMap 𝒢.genStalk (Reta L) x)
  have ht : (t : 𝓞 L) ≠ 0 := fun h =>
    (Ideal.mem_primeCompl_iff.mp t.2) (by rw [h]; exact Ideal.zero_mem _)
  have hu := ZInQ.HeightDict.Conormal.structMap_isUnit 𝒢 t ht
  have hr : algebraMap 𝒢.genStalk (Reta L) x * algebraMap (𝓞 L) (Reta L) t =
      algebraMap (𝓞 L) (Reta L) a := by
    rw [← hat]; exact IsLocalization.mk'_spec (Reta L) a t
  have e : ∀ c : 𝓞 L, algebraMap 𝒢.genStalk (Reta L) (𝒢.structMap c) =
      algebraMap (𝓞 L) (Reta L) c :=
    fun c => ZInQ.HeightDict.Conormal.unitStalk_stalkAlg 𝒢 (genericPt L) c
  have hxt : algebraMap 𝒢.genStalk (Reta L) (x * 𝒢.structMap t) =
      algebraMap 𝒢.genStalk (Reta L) (𝒢.structMap a) := by
    rw [map_mul, e, e, hr]
  have h1 : (t : 𝓞 L) • ((↑hu.unit⁻¹ : 𝒢.genStalk) • v i) = v i := by
    show 𝒢.structMap t • ((↑hu.unit⁻¹ : 𝒢.genStalk) • v i) = v i
    rw [smul_smul, hu.mul_val_inv, one_smul]
  generalize (↑hu.unit⁻¹ : 𝒢.genStalk) • v i = m' at h1
  have h2 : x • v i = a • m' := by
    rw [← h1]
    show x • (𝒢.structMap t • m') = 𝒢.structMap a • m'
    rw [smul_smul]
    exact smul_cotangent_eq_of_algebraMap_eq 𝒢 hxt m'
  have hl : etaFieldEquiv (algebraMap 𝒢.genStalk (Reta L) x) * algebraMap (𝓞 L) L t =
      algebraMap (𝓞 L) L a := by
    rw [← etaFieldEquiv_algebraMap, ← etaFieldEquiv_algebraMap, ← map_mul, hr]
  have hv : v = Function.update v i ((t : 𝓞 L) • m') := by
    rw [h1, Function.update_eq_self]
  rw [h2, AlternatingMap.map_update_smul, ← TensorProduct.smul_tmul]
  conv_lhs => rw [hv, AlternatingMap.map_update_smul, ← TensorProduct.smul_tmul,
    TensorProduct.smul_tmul']
  congr 1
  rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
  simp only [mul_one]
  exact hl

variable {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {W : 𝒢.G.left.Opens}
  (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W)

/-- **The wedge identity for `c ∈ 𝒪_S(V)`**: for a lift `x ∈ 𝒪_{𝒢,ξ}` of `c|_η`,
`c|_η • (1 ⊗ v₁ ∧ ⋯ ∧ v_g) = 1 ⊗ v₁ ∧ ⋯ ∧ (x • v_i) ∧ ⋯ ∧ v_g`. -/
theorem germEtaField_smul_wedge {g : ℕ} (v : Fin g → 𝒢.cotangent) (i : Fin g)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) (x : 𝒢.genStalk)
    (hx : algebraMap 𝒢.genStalk (Reta L) x = germEta V hV c) :
    germEtaField V hV c • ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (Function.update v i (x • v i)) := by
  rw [germEtaField_apply, ← hx]
  exact etaFieldEquiv_smul_wedge 𝒢 v i x

/-- The same identity for the action `hodgeAction`. -/
theorem hodgeAction_smul_wedge {g : ℕ} (v : Fin g → 𝒢.cotangent) (i : Fin g)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) (x : 𝒢.genStalk)
    (hx : algebraMap 𝒢.genStalk (Reta L) x = germEta V hV c) :
    letI := hodgeAction 𝒢 g V hV
    c • ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (Function.update v i (x • v i)) :=
  germEtaField_smul_wedge 𝒢 hV v i c x hx

/-! ## `detSec V W` is an `𝒪_S(V)`-submodule -/

/-- **`detSec V W` is stable under `𝒪_S(V)`** (for `g ≥ 1`): on a generating wedge, `c|_η` acts
by multiplying one factor by a lift of `c` (`germEtaField_smul_wedge`), which stays in `detSec`
(`smul_wedge_mem_detSec`). -/
theorem germEtaField_smul_mem_detSec {g : ℕ} (hg : 0 < g)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) {y : 𝒢.hodgeSpace g}
    (hy : y ∈ detSec 𝒢 g V W hV hVW) : germEtaField V hV c • y ∈ detSec 𝒢 g V W hV hVW := by
  obtain ⟨x, hx⟩ := ZInQ.HeightModelM3.exists_lift_germEta 𝒢 hV c
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [germEtaField_smul_wedge 𝒢 hV _ ⟨0, hg⟩ c x hx]
    exact ZInQ.HeightModelM3.smul_wedge_mem_detSec 𝒢 hV hVW g v ⟨0, hg⟩ c x hx
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ a hy

/-- **`detSec V W` as an `𝒪_S(V)`-submodule of the Hodge line** (for `g ≥ 1`), for the action
`hodgeAction`. -/
noncomputable def detSecSubmodule {g : ℕ} (hg : 0 < g) :
    @Submodule Γ(Spec (CommRingCat.of (𝓞 L)), V) (𝒢.hodgeSpace g) _ _
      (hodgeAction 𝒢 g V hV) :=
  letI := hodgeAction 𝒢 g V hV
  { carrier := detSec 𝒢 g V W hV hVW
    add_mem' := fun ha hb => Submodule.add_mem _ ha hb
    zero_mem' := Submodule.zero_mem _
    smul_mem' := fun c _ hy => germEtaField_smul_mem_detSec 𝒢 hV hVW hg c hy }

theorem mem_detSecSubmodule {g : ℕ} (hg : 0 < g) (y : 𝒢.hodgeSpace g) :
    y ∈ detSecSubmodule 𝒢 hV hVW hg ↔ y ∈ detSec 𝒢 g V W hV hVW :=
  Iff.rfl

/-! ## Sections near a point and the global lattice -/

/-- **The sections of `ε*Ω^g` near `s ∈ V` are stable under `𝒪_S(V)`** (for `g ≥ 1`). -/
theorem germEtaField_smul_mem_detSecNear {g : ℕ} (hg : 0 < g)
    {s : Spec (CommRingCat.of (𝓞 L))} {V : (Spec (CommRingCat.of (𝓞 L))).Opens} (hs : s ∈ V)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) {y : 𝒢.hodgeSpace g}
    (hy : y ∈ detSecNear 𝒢 g s) : germEtaField V (genericPt_mem hs) c • y ∈ detSecNear 𝒢 g s := by
  obtain ⟨V', W', hs', hVW', hy'⟩ := hy
  have hs'' : s ∈ V ⊓ V' := ⟨hs, hs'⟩
  have hVW'' : V ⊓ V' ≤ 𝒢.unitSection ⁻¹ᵁ W' := fun z hz => hVW' hz.2
  have hy'' : y ∈ detSec 𝒢 g (V ⊓ V') W' (genericPt_mem hs'') hVW'' :=
    detSec_mono 𝒢 g _ _ _ _ inf_le_right le_rfl hy'
  refine ⟨V ⊓ V', W', hs'', hVW'', ?_⟩
  rw [← germEtaField_res inf_le_left (genericPt_mem hs'') c]
  exact germEtaField_smul_mem_detSec 𝒢 (genericPt_mem hs'') hVW'' hg _ hy''

/-- **The global lattice `globalDetLattice = Γ(S, ε*Ω^g)` is stable under `Γ(S, 𝒪_S)`** (for
`g ≥ 1`). -/
theorem germEtaField_smul_mem_globalDetLattice {g : ℕ} (hg : 0 < g)
    (c : Γ(Spec (CommRingCat.of (𝓞 L)), ⊤)) {y : 𝒢.hodgeSpace g}
    (hy : y ∈ globalDetLattice 𝒢 g) : germEtaField ⊤ trivial c • y ∈ globalDetLattice 𝒢 g := by
  rw [globalDetLattice, Submodule.mem_iInf] at hy ⊢
  intro s
  exact germEtaField_smul_mem_detSecNear 𝒢 hg (show s ∈ (⊤ : (Spec (CommRingCat.of (𝓞 L))).Opens)
    from trivial) c (hy s)

/-- **`globalDetLattice` as a `Γ(S, 𝒪_S)`-submodule of the Hodge line** (for `g ≥ 1`). -/
noncomputable def globalDetLatticeSubmodule {g : ℕ} (hg : 0 < g) :
    @Submodule Γ(Spec (CommRingCat.of (𝓞 L)), ⊤) (𝒢.hodgeSpace g) _ _
      (hodgeAction 𝒢 g ⊤ trivial) :=
  letI := hodgeAction 𝒢 g ⊤ trivial
  { carrier := globalDetLattice 𝒢 g
    add_mem' := fun ha hb => Submodule.add_mem _ ha hb
    zero_mem' := Submodule.zero_mem _
    smul_mem' := fun c _ hy => germEtaField_smul_mem_globalDetLattice 𝒢 hg c hy }

theorem mem_globalDetLatticeSubmodule {g : ℕ} (hg : 0 < g) (y : 𝒢.hodgeSpace g) :
    y ∈ globalDetLatticeSubmodule 𝒢 hg ↔ y ∈ globalDetLattice 𝒢 g :=
  Iff.rfl

end ZInQ.HeightModelM4
