import ZInQKernel.Contrib.OneProof.HeightModelM2.GlobalDet
import ZInQKernel.Contrib.OneProof.HeightModelM3.Theta

/-! # Spans over `𝓞_L` and over `𝒪_S(V)`, and wedges of images of `θ`

`secOmega`, `detSec` and `printedOmegaAt` are `𝓞_L`-spans, while the sections of the sheaf over
`V` form an `𝒪_S(V)`-module. What is proved:

* `germEta_smul_mem_secOmega`: `secOmega V W` is stable under every `c ∈ 𝒪_S(V)`;
* `smul_mem_comap_secOmega`, `smul_wedge_mem_detSec`: a lift `x ∈ 𝒪_{𝒢,ξ}` of `c`
  (`exists_lift_germEta`) acts on `θ⁻¹(secOmega V W)`, so a generating wedge of `detSec` with one
  factor multiplied by `x` is again a wedge of sections. That this element is
  `c|_η · (v₁ ∧ ⋯ ∧ v_g)` in the Hodge line is README reading 2.

`detSec` wedges sections in the image of `θ`; by `theta_surjective` this is every section
(`map_comap_secOmega`). -/
open CategoryTheory AlgebraicGeometry
open NumberField KaehlerDifferential
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal ZInQ.HeightModelM2
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM3

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

variable {V : (Spec (CommRingCat.of (𝓞 L))).Opens} {W : 𝒢.G.left.Opens}
  (hV : genericPt L ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W)

/-- **`secOmega V W` is an `𝒪_S(V)`-module**: the `𝓞_L`-span is stable under the functions on
`V`, because its generators `c|_η · (1 ⊗ d(b|_ξ))` already range over all `c ∈ 𝒪_S(V)`. -/
theorem germEta_smul_mem_secOmega (c : Γ(Spec (CommRingCat.of (𝓞 L)), V))
    {t : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]} (ht : t ∈ secOmega 𝒢 V W hV hVW) :
    germEta V hV c • t ∈ secOmega 𝒢 V W hV hVW := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c', b⟩, rfl⟩ := hx
    rw [smul_smul]
    apply Submodule.subset_span
    refine ⟨⟨c * c', b⟩, ?_⟩
    simp only [germEta, map_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul (Reta L) a x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

/-- Every function on `V` lifts, at `η`, to an element of `𝒪_{𝒢,ξ}`. -/
theorem exists_lift_germEta (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) :
    ∃ x : 𝒢.genStalk, algebraMap 𝒢.genStalk (Reta L) x = germEta V hV c :=
  algebraMap_surjective 𝒢 _

/-- **The `𝒪_S(V)`-action on the sections of `e*Ω¹` in `𝔪_ξ/𝔪_ξ²`**: a lift `x` of `c` acts on
`θ⁻¹(secOmega V W)`. -/
theorem smul_mem_comap_secOmega (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) (x : 𝒢.genStalk)
    (hx : algebraMap 𝒢.genStalk (Reta L) x = germEta V hV c) {m : 𝒢.cotangent}
    (hm : m ∈ (secOmega 𝒢 V W hV hVW).comap (theta' 𝒢)) :
    x • m ∈ (secOmega 𝒢 V W hV hVW).comap (theta' 𝒢) := by
  show ZInQ.HeightDict.Conormal.theta 𝒢 (x • m) ∈ secOmega 𝒢 V W hV hVW
  rw [map_smul, ← algebraMap_smul (Reta L) x, hx]
  exact germEta_smul_mem_secOmega 𝒢 hV hVW c hm

/-- **The generating wedges of `detSec` are closed under multiplying one factor by a lift `x` of
`c ∈ 𝒪_S(V)`**: the wedge with `v_i` replaced by `x • v_i` is again a wedge of sections over `V`.
(That this element is `c|_η · (v₁ ∧ ⋯ ∧ v_g)` in the Hodge line is README reading 2.) -/
theorem smul_wedge_mem_detSec (g : ℕ) (v : Fin g → (secOmega 𝒢 V W hV hVW).comap (theta' 𝒢))
    (i : Fin g) (c : Γ(Spec (CommRingCat.of (𝓞 L)), V)) (x : 𝒢.genStalk)
    (hx : algebraMap 𝒢.genStalk (Reta L) x = germEta V hV c) :
    (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g
        (Function.update (fun j => (v j : 𝒢.cotangent)) i (x • (v i : 𝒢.cotangent))) ∈
      detSec 𝒢 g V W hV hVW := by
  classical
  let w : Fin g → (secOmega 𝒢 V W hV hVW).comap (theta' 𝒢) :=
    Function.update v i ⟨x • (v i : 𝒢.cotangent), smul_mem_comap_secOmega 𝒢 hV hVW c x hx (v i).2⟩
  have hw : (fun j => (w j : 𝒢.cotangent)) =
      Function.update (fun j => (v j : 𝒢.cotangent)) i (x • (v i : 𝒢.cotangent)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [w]
    · simp [w, Function.update_of_ne hj]
  rw [← hw]
  exact Submodule.subset_span ⟨w, rfl⟩

/-- **Every section of `e*Ω¹` over `V` is in the image of `θ`** (`θ` is surjective), so wedging
the sections of `θ⁻¹(secOmega V W)` in `detSec` wedges all sections. -/
theorem map_comap_secOmega :
    ((secOmega 𝒢 V W hV hVW).comap (theta' 𝒢)).map (theta' 𝒢) = secOmega 𝒢 V W hV hVW :=
  Submodule.map_comap_eq_of_surjective (f := theta' 𝒢) (theta_surjective 𝒢) _

end ZInQ.HeightModelM3
