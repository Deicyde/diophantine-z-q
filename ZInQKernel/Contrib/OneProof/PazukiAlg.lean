import ZInQKernel.Contrib.OneProof.PazukiCor13Upper
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-!
# pazuki-alg: the analytic half of `AnalyticPPAlgebraic` from Riemann's theorem and GAGA for morphisms

Task pazuki-alg (2026-11-16), docs/research/pazuki-alg.md.

pazuki-dict reduced the field `pazukiCor13Upper` to Pazuki's printed corollary for algebraic `(A, L)`
(`PazukiDict.PazukiCor13UpperPP`) and the composite glue `PazukiDict.AnalyticPPAlgebraic`, which splits (proved
there) into an analytic half over `ℂ` (`PazukiDict.ThetaDivisorAlgebraicC`: the theta divisor of an analytic
principal polarization of a given complex abelian variety `B` is the divisor of an algebraic symmetric principal
polarization of `B`) and an arithmetic half (`PazukiDict.SymmPrincipalDescends`: descent from `ℂ` to a number
field).

This file
* states the classical algebraicity of a principally polarized complex torus, for `g = 2`, as one statement about
  `Ω ∈ 𝔥₂` only (`RiemannPPAV`: there is a complex abelian surface `B₀` with a biholomorphic uniformization by
  `ℂ²/(Ωℤ² + ℤ²)` and a symmetric principal `L₀` whose section vanishes exactly on the zero set of `θ(·, Ω)`);
* proves the analytic half `ThetaDivisorAlgebraicC` from `RiemannPPAV`, the existing field `GAGAMorphism` (applied
  twice, to get an isomorphism `B ≅ B₀` of abelian varieties compatible with the uniformizations) and the transport
  of symmetric principal polarizations along an isomorphism of abelian varieties (`SymmPrincipalTransport`, project
  glue, proved below);
* proves the discreteness of `Ωℤ² + ℤ²` for `Ω ∈ 𝔥₂`, which GAGA's hypothesis needs.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace PazukiAlg

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open ZInQ.LeafPush2 (CPts IsSiegel)
open BPAnalytic (Torus proj)
open PazukiDict (riemannTheta OnZeroLocus IsSymmPrincipal ThetaDivisorAlgebraicC)

/-! ## §1. The period lattice `Ωℤ² + ℤ²` -/

/-- The lattice `Ωℤ² + ℤ² ⊂ ℂ²`. -/
def periodLattice (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Submodule ℤ (Fin 2 → ℂ) where
  carrier := {v | ∃ m n : Fin 2 → ℤ, v = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)}
  add_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    refine ⟨m + m', n + n', ?_⟩
    have h1 : (fun i => ((m + m') i : ℂ)) = (fun i => (m i : ℂ)) + fun i => (m' i : ℂ) := by
      funext i; simp
    have h2 : (fun i => ((n + n') i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (n' i : ℂ) := by
      funext i; simp
    rw [h1, h2, Matrix.mulVec_add]
    abel
  zero_mem' := ⟨0, 0, by funext i; simp⟩
  smul_mem' := by
    rintro c _ ⟨m, n, rfl⟩
    refine ⟨c • m, c • n, ?_⟩
    have h1 : (fun i => ((c • m) i : ℂ)) = (c : ℂ) • fun i => (m i : ℂ) := by
      funext i; simp
    have h2 : (fun i => ((c • n) i : ℂ)) = (c : ℂ) • fun i => (n i : ℂ) := by
      funext i; simp
    rw [h1, h2, Matrix.mulVec_smul, ← smul_add]
    funext i
    simp

theorem mem_periodLattice {Ω : Matrix (Fin 2) (Fin 2) ℂ} {v : Fin 2 → ℂ} :
    v ∈ periodLattice Ω ↔ ∃ m n : Fin 2 → ℤ, v = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ) :=
  Iff.rfl


/-- The imaginary part of `Ωm + n` is `(Im Ω) m`. -/
theorem im_periodVec (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m n : Fin 2 → ℤ) :
    (fun i => ((Ω.mulVec (fun j => (m j : ℂ)) + fun j => (n j : ℂ)) i).im) =
      (Ω.map Complex.im).mulVec (fun j => (m j : ℝ)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im]

/-- **`Ωℤ² + ℤ²` has no nonzero vectors near `0`** for `Ω ∈ 𝔥₂` (`Im Ω` is invertible). -/
theorem exists_eq_zero_of_norm_lt {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : IsSiegel Ω) :
    ∃ ε > 0, ∀ v ∈ periodLattice Ω, ‖v‖ < ε → v = 0 := by
  set Y := Ω.map Complex.im with hYdef
  have hdet : IsUnit Y.det := isUnit_iff_ne_zero.mpr (hΩ.2.det_pos).ne'
  have hc : Continuous (fun x : Fin 2 → ℝ => Y⁻¹.mulVec x) :=
    Continuous.matrix_mulVec continuous_const continuous_id
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hc.continuousAt 1 one_pos
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  rintro v ⟨m, n, rfl⟩ hv
  have hvδ : ‖Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)‖ < δ := hv.trans_le (min_le_left _ _)
  have hv1 : ‖Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)‖ < 1 := hv.trans_le (min_le_right _ _)
  set x : Fin 2 → ℝ := fun i => ((Ω.mulVec (fun j => (m j : ℂ)) + fun j => (n j : ℂ)) i).im with hx
  have hxn : ‖x‖ < δ := by
    refine lt_of_le_of_lt ?_ hvδ
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm _ i)
  have hxY : x = Y.mulVec (fun j => (m j : ℝ)) := im_periodVec Ω m n
  have hm' : Y⁻¹.mulVec x = fun j => (m j : ℝ) := by
    rw [hxY, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Y hdet, Matrix.one_mulVec]
  have hlt := hδ' (x := x) (by simpa [dist_eq_norm] using hxn)
  simp only [Matrix.mulVec_zero, dist_zero_right] at hlt
  rw [hm'] at hlt
  have hm0 : m = 0 := by
    funext i
    have hi : ‖(m i : ℝ)‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (fun j => (m j : ℝ)) i) hlt
    rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at hi
    exact hi
  subst hm0
  have hn0 : n = 0 := by
    funext i
    have hv1' : ‖(fun i => (n i : ℂ))‖ < 1 := by simpa using hv1
    have hi : ‖(n i : ℂ)‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (fun j => (n j : ℂ)) i) hv1'
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at hi
    exact hi
  subst hn0
  funext i
  simp

/-- **`Ωℤ² + ℤ²` is discrete** for `Ω ∈ 𝔥₂`. -/
theorem discreteTopology_periodLattice {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : IsSiegel Ω) :
    DiscreteTopology (periodLattice Ω) := by
  obtain ⟨ε, hε, h⟩ := exists_eq_zero_of_norm_lt hΩ
  refine DiscreteTopology.of_forall_le_dist hε fun x y hxy => ?_
  by_contra hlt
  push_neg at hlt
  apply hxy
  have hmem : (x : Fin 2 → ℂ) - y ∈ periodLattice Ω := sub_mem x.2 y.2
  have hn : ‖(x : Fin 2 → ℂ) - y‖ < ε := by
    rwa [Subtype.dist_eq, dist_eq_norm] at hlt
  exact Subtype.ext (sub_eq_zero.mp (h _ hmem hn))

/-! ## §2. The new statements -/

/-- **LEAF candidate (published): the principally polarized abelian surface of `Ω ∈ 𝔥₂`** (Riemann's theorem;
the algebraicity of a principally polarized complex torus with its theta divisor). For `Ω ∈ 𝔥₂` there are a complex
abelian surface `B₀` (`PkgI3.AbVar ℂ`), a biholomorphic uniformization `φ₀ : ℂ² ⧸ (Ωℤ² + ℤ²) ≃ B₀(ℂ)`
(bp-analytic's `IsUniformization`), a symmetric principal polarization `L₀` of `B₀` (`IsSymmPrincipal`: ample,
symmetric, `h⁰ = 1`) and a section `s₀` of `L₀` whose divisor is, through `φ₀`, the zero set of Riemann's theta
function `θ(·, Ω)`.

Sources (locators UNVERIFIED, no copy of the books on this host): Mumford, *Abelian varieties*, §§2-3 (the complex
torus `X_Ω = ℂ^g ⧸ (Ωℤ^g + ℤ^g)` with the Riemann form `E_Ω` is an abelian variety; `θ(·, Ω)` is, up to a scalar,
the unique section of the line bundle `L(H_Ω, α₀)`, which is symmetric and ample); Mumford, *Tata Lectures on Theta
I*, Ch. II §1 and §3 (the theta embedding of `X_Ω`; the divisor `Θ = (θ)`); Birkenhake–Lange, *Complex abelian
varieties*, §8.1 (the principally polarized abelian variety `(X_Z, H_Z)` of `Z ∈ 𝔥_g`) and §8.5 (Riemann's theta
function is the canonical theta function of `L(H_Z, χ₀)`). The books state this in the analytic category
(abelian variety = complex torus with a positive line bundle); reading it as a statement about a scheme
`PkgI3.AbVar ℂ` and an algebraic line bundle uses Chow's theorem and GAGA, which those books invoke (Mumford §3). -/
def RiemannPPAV : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω →
    ∃ (B₀ : PkgI3.AbVar ℂ) (φ₀ : Torus (periodLattice Ω) ≃+ Additive (B₀.Pt ℂ)),
      BPAnalytic.Uniformization.IsUniformization B₀ (periodLattice Ω) φ₀ ∧
      ∃ (L₀ : B₀.X.left.Pic)
        (s₀ : 𝟙_ B₀.X.left.Modules ⟶ (fromSkeleton B₀.X.left.Modules).obj L₀.val),
        IsSymmPrincipal B₀ L₀ ∧
        ∀ v : Fin 2 → ℂ, OnZeroLocus s₀ (Additive.toMul (φ₀ (proj (periodLattice Ω) v))).left ↔
          riemannTheta Ω v = 0

/-- **GLUE (project; scheme functoriality): a symmetric principal polarization transports along an isomorphism of
abelian varieties.** If `u : B → B₀` is an isomorphism of abelian varieties over `ℂ` commuting with the inverse maps
and `L₀` is a symmetric principal polarization of `B₀` with a section `s₀`, then the pullback gives a symmetric
principal polarization of `B` with a section whose divisor is the preimage of that of `s₀`. -/
def SymmPrincipalTransport : Prop :=
  ∀ (B B₀ : PkgI3.AbVar ℂ) (u : B.X ⟶ B₀.X) [IsIso u], u ≫ GrpObj.inv = GrpObj.inv ≫ u →
    ∀ (L₀ : B₀.X.left.Pic)
      (s₀ : 𝟙_ B₀.X.left.Modules ⟶ (fromSkeleton B₀.X.left.Modules).obj L₀.val),
      IsSymmPrincipal B₀ L₀ →
      ∃ (L : B.X.left.Pic) (s : 𝟙_ B.X.left.Modules ⟶ (fromSkeleton B.X.left.Modules).obj L.val),
        IsSymmPrincipal B L ∧
        ∀ q : Spec (CommRingCat.of ℂ) ⟶ B.X.left, OnZeroLocus s q ↔ OnZeroLocus s₀ (q ≫ u.left)

/-! ## §2b. `SymmPrincipalTransport` (proved): pullback along an isomorphism -/

section Transport

open Scheme.Modules

variable {X Y : Scheme.{0}}

/-- `(f^*M)^{⊗n} ≅ f^*(M^{⊗n})` (pullback is monoidal). -/
def tensorPowPullbackIso (f : X ⟶ Y) (M : Y.Modules) :
    ∀ n : ℕ, ((Modules.pullback f).obj M).tensorPow n ≅ (Modules.pullback f).obj (M.tensorPow n)
  | 0 => Functor.Monoidal.εIso (Modules.pullback f)
  | n + 1 => (Iso.refl _ ⊗ᵢ tensorPowPullbackIso f M n) ≪≫
      Functor.Monoidal.μIso (Modules.pullback f) M (M.tensorPow n)

/-- `M ≅ N ⟹ M^{⊗n} ≅ N^{⊗n}`. -/
def tensorPowMapIso {M N : X.Modules} (i : M ≅ N) : ∀ n : ℕ, M.tensorPow n ≅ N.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => i ⊗ᵢ tensorPowMapIso i n

/-- The pulled-back section `𝟙 ≅ f^*𝟙 ⟶ f^*N ≅ N'`. -/
def pullbackSec (f : X ⟶ Y) {N : Y.Modules} {N' : X.Modules} (iN : N' ≅ (Modules.pullback f).obj N)
    (t : 𝟙_ Y.Modules ⟶ N) : 𝟙_ X.Modules ⟶ N' :=
  (Functor.Monoidal.εIso (Modules.pullback f)).hom ≫ (Modules.pullback f).map t ≫ iN.inv

/-- **The divisor of the pulled-back section is the preimage.** -/
theorem support_zeroLocus_pullbackSec (f : X ⟶ Y) {N : Y.Modules} {N' : X.Modules} [N.IsInvertible]
    [N'.IsInvertible] (iN : N' ≅ (Modules.pullback f).obj N) (t : 𝟙_ Y.Modules ⟶ N) :
    (Hom.zeroLocus (pullbackSec f iN t)).support = (Hom.zeroLocus t).support.preimage f.continuous := by
  have h1 : Hom.zeroLocus (pullbackSec f iN t) = Hom.zeroLocus ((Modules.pullback f).map t) := by
    refine Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (Functor.Monoidal.εIso (Modules.pullback f)) iN ?_)
    simp [pullbackSec]
  rw [h1, ← Hom.comap_zeroLocus, IdealSheafData.support_comap]

/-- **Ampleness transports along an isomorphism.** -/
theorem isAmple_map (f : X ⟶ Y) [IsIso f] (L₀ : Y.Pic) (h : T09Pic.IsAmple Y L₀) :
    T09Pic.IsAmple X (Scheme.Pic.map f L₀) := by
  obtain ⟨hc, h2⟩ := h
  refine ⟨f.homeomorph.symm.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, t, hxt, haff⟩ := h2 (f x)
  let M₀ := (fromSkeleton Y.Modules).obj L₀.val
  let iE : (fromSkeleton X.Modules).obj (Scheme.Pic.map f L₀).val ≅ (Modules.pullback f).obj M₀ :=
    Scheme.Pic.mkIso ((Modules.pullback f).obj M₀)
  let iN := tensorPowMapIso iE n ≪≫ tensorPowPullbackIso f M₀ n
  have hsupp := support_zeroLocus_pullbackSec f iN t
  have hopen : (Hom.zeroLocus (pullbackSec f iN t)).support.compl =
      f ⁻¹ᵁ (Hom.zeroLocus t).support.compl := by
    ext y
    simp only [TopologicalSpace.Closeds.mem_compl, hsupp]
    rfl
  refine ⟨n, hn, pullbackSec f iN t, ?_, ?_⟩
  · rw [hopen]
    exact hxt
  · rw [hopen]
    exact haff.preimage f

/-- **`h⁰` transports along an isomorphism**: pulling back global sections along `f` is a bijection, semilinear
over the ring isomorphism `f^* : Γ(Y, 𝒪) → Γ(X, 𝒪)`. -/
theorem finrank_map (f : X ⟶ Y) [IsIso f] (L₀ : Y.Pic) :
    Module.finrank Γ(X, ⊤) Γ((fromSkeleton X.Modules).obj (Scheme.Pic.map f L₀).val, ⊤) =
      Module.finrank Γ(Y, ⊤) Γ((fromSkeleton Y.Modules).obj L₀.val, ⊤) := by
  let M₀ := (fromSkeleton Y.Modules).obj L₀.val
  let iE : (fromSkeleton X.Modules).obj (Scheme.Pic.map f L₀).val ≅ (Modules.pullback f).obj M₀ :=
    Scheme.Pic.mkIso ((Modules.pullback f).obj M₀)
  have hrange : (⊤ : Y.Opens) ≤ f.opensRange := by
    intro y _
    exact ⟨(inv f).base y, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl⟩
  have hb1 : Function.Bijective ((pullbackUnit f M₀).app ⊤) :=
    bijective_pullbackUnit_app_of_isOpenImmersion M₀ hrange
  have hb2 : Function.Bijective (iE.inv.app (f ⁻¹ᵁ ⊤)) := by
    refine ⟨fun a b hab => ?_, fun b => ⟨iE.hom.app _ b, ?_⟩⟩
    · have := congrArg (iE.hom.app (f ⁻¹ᵁ ⊤)) hab
      rwa [← Hom.comp_app_apply, ← Hom.comp_app_apply, iE.inv_hom_id] at this
    · rw [← Hom.comp_app_apply, iE.hom_inv_id]
      rfl
  let j : Γ(M₀, ⊤) ≃+ Γ((fromSkeleton X.Modules).obj (Scheme.Pic.map f L₀).val, ⊤) :=
    AddEquiv.ofBijective
      { toFun := fun m => iE.inv.app (f ⁻¹ᵁ ⊤) ((pullbackUnit f M₀).app ⊤ m)
        map_zero' := by simp
        map_add' := fun a b => by simp } (hb2.comp hb1)
  have hi : Function.Bijective (f.app ⊤) := ConcreteCategory.bijective_of_isIso (f.app ⊤)
  have hr := rank_eq_of_equiv_equiv (f.app ⊤) j hi (fun r m => by
    show iE.inv.app (f ⁻¹ᵁ ⊤) ((pullbackUnit f M₀).app ⊤ (r • m)) =
      f.app ⊤ r • iE.inv.app (f ⁻¹ᵁ ⊤) ((pullbackUnit f M₀).app ⊤ m)
    rw [Hom.app_smul, Hom.app_smul])
  unfold Module.finrank
  rw [hr]

/-- **`SymmPrincipalTransport` (proved).** -/
theorem symmPrincipalTransport : SymmPrincipalTransport := by
  intro B B₀ u _ hu L₀ s₀ hL₀
  haveI : IsIso u.left := (Over.forget _).map_isIso u
  let M₀ := (fromSkeleton B₀.X.left.Modules).obj L₀.val
  let iE : (fromSkeleton B.X.left.Modules).obj (Scheme.Pic.map u.left L₀).val ≅
      (Modules.pullback u.left).obj M₀ :=
    Scheme.Pic.mkIso ((Modules.pullback u.left).obj M₀)
  refine ⟨Scheme.Pic.map u.left L₀, pullbackSec u.left iE s₀,
    ⟨isAmple_map _ _ hL₀.1, ?_, ?_⟩, fun q => ?_⟩
  · rw [← Scheme.Pic.map_comp, ← Over.comp_left, ← hu, Over.comp_left, Scheme.Pic.map_comp, hL₀.2.1]
  · rw [finrank_map]
    exact hL₀.2.2
  · unfold OnZeroLocus
    rw [support_zeroLocus_pullbackSec]
    rfl

end Transport

/-! ## §3. The isomorphism `B ≅ B₀` from GAGA for morphisms (proved) -/

open ZInQ.HomLattice (IsAnalyticHom isAnalyticHom_of_unif isAnalyticHom_lin isStrongUnif_of_bp)

/-- Every complex point is `φ(proj w)` for some `w`. -/
theorem exists_proj_eq {A : PkgI3.AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)) (p : A.Pt ℂ) : ∃ w, Additive.toMul (φ (proj Λ w)) = p := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (φ.symm (Additive.ofMul p))
  refine ⟨w, ?_⟩
  show Additive.toMul (φ (QuotientAddGroup.mk w)) = p
  rw [hw, AddEquiv.apply_symm_apply]
  rfl

/-- `φ ∘ proj` turns `-w` into the inverse. -/
theorem toMul_proj_neg {A : PkgI3.AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)) (w : Fin g → ℂ) :
    Additive.toMul (φ (proj Λ (-w))) = (Additive.toMul (φ (proj Λ w)))⁻¹ := by
  rw [show proj Λ (-w) = -proj Λ w from rfl, map_neg, toMul_neg]

/-- **The analytic half from Riemann's theorem (proved).** Given `B` with biholomorphic uniformization
`φ : ℂ^g ⧸ Λ ≃ B(ℂ)` and `T : ℂ^g ≃ ℂ²` with `T(Λ) = Ωℤ² + ℤ²`: `RiemannPPAV` gives `(B₀, φ₀, L₀, s₀)`; GAGA for
morphisms, applied to `φ₀ ∘ proj ∘ T` (source `B`) and to `φ ∘ proj ∘ T⁻¹` (source `B₀`), gives morphisms
`h : B → B₀` and `f : B₀ → B` that are mutually inverse on complex points, hence inverse isomorphisms
(`hom_ext_of_cpts`), compatible with the inverse maps; `SymmPrincipalTransport` pulls `(L₀, s₀)` back along `h`. -/
theorem thetaDivisorAlgebraicC_of_riemann (hR : RiemannPPAV) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hT : SymmPrincipalTransport) : ThetaDivisorAlgebraicC := by
  intro B g Λ φ hφ Ω hΩ T hTΛ
  obtain ⟨B₀, φ₀, hφ₀, L₀, s₀, hL₀, hz₀⟩ := hR Ω hΩ
  haveI hdisc₀ : DiscreteTopology (periodLattice Ω) := discreteTopology_periodLattice hΩ
  have hmem : ∀ w, w ∈ Λ ↔ T w ∈ periodLattice Ω := fun w => hTΛ w
  -- `Λ` is discrete: `w ↦ T w` is a continuous injection of `Λ` into the discrete `Ωℤ² + ℤ²`.
  haveI hdisc : DiscreteTopology Λ := by
    let F : Λ → periodLattice Ω := fun w => ⟨T w, (hmem w).1 w.2⟩
    have hFc : Continuous F :=
      Continuous.subtype_mk ((LinearMap.continuous_of_finiteDimensional
        (T : (Fin g → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).comp continuous_subtype_val) _
    have hFi : Function.Injective F := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hFc hFi
  -- the two analytic homomorphisms
  let ψ : (Fin g → ℂ) → CPts B₀ (RingHom.id ℂ) := fun w =>
    Additive.toMul (φ₀ (proj (periodLattice Ω) (T w)))
  have hψ : IsAnalyticHom (RingHom.id ℂ) ψ :=
    isAnalyticHom_lin (isAnalyticHom_of_unif (ZInQ.LeafPush2.isUniformization_of_bp B₀ hφ₀))
      (T : (Fin g → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
  have hψΛ : ∀ z ∈ Λ, ψ z = 1 := by
    intro z hz
    show Additive.toMul (φ₀ (proj (periodLattice Ω) (T z))) = 1
    rw [show proj (periodLattice Ω) (T z) = 0 from
      (QuotientAddGroup.eq_zero_iff (T z)).mpr ((hmem z).1 hz), map_zero]
    rfl
  obtain ⟨h, hh⟩ := hG B B₀ g Λ φ (isStrongUnif_of_bp hφ) ψ hψ hψΛ
  let ψ' : (Fin 2 → ℂ) → CPts B (RingHom.id ℂ) := fun v =>
    Additive.toMul (φ (proj Λ (T.symm v)))
  have hψ' : IsAnalyticHom (RingHom.id ℂ) ψ' :=
    isAnalyticHom_lin (isAnalyticHom_of_unif (ZInQ.LeafPush2.isUniformization_of_bp B hφ))
      (T.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  have hψ'Λ : ∀ z ∈ periodLattice Ω, ψ' z = 1 := by
    intro z hz
    show Additive.toMul (φ (proj Λ (T.symm z))) = 1
    have : T.symm z ∈ Λ := (hmem _).2 (by rwa [LinearEquiv.apply_symm_apply])
    rw [show proj Λ (T.symm z) = 0 from (QuotientAddGroup.eq_zero_iff _).mpr this, map_zero]
    rfl
  obtain ⟨f, hf⟩ := hG B₀ B 2 (periodLattice Ω) φ₀ (isStrongUnif_of_bp hφ₀) ψ' hψ' hψ'Λ
  -- values on points
  have hhw : ∀ w, Additive.toMul (φ (proj Λ w)) ≫ h = Additive.toMul (φ₀ (proj (periodLattice Ω) (T w))) :=
    fun w => (hh w).symm
  have hfv : ∀ v, Additive.toMul (φ₀ (proj (periodLattice Ω) v)) ≫ f = Additive.toMul (φ (proj Λ (T.symm v))) :=
    fun v => (hf v).symm
  have hhf : h ≫ f = 𝟙 _ := by
    refine ZInQ.HomUnify.hom_ext_of_cpts _ _ fun p => ?_
    obtain ⟨w, rfl⟩ := exists_proj_eq φ p
    rw [← Category.assoc, hhw, hfv, LinearEquiv.symm_apply_apply, Category.comp_id]
  have hfh : f ≫ h = 𝟙 _ := by
    refine ZInQ.HomUnify.hom_ext_of_cpts _ _ fun p => ?_
    obtain ⟨v, rfl⟩ := exists_proj_eq φ₀ p
    rw [← Category.assoc, hfv, hhw, LinearEquiv.apply_symm_apply, Category.comp_id]
  haveI : IsIso h := ⟨⟨f, hhf, hfh⟩⟩
  have hinv : h ≫ GrpObj.inv = GrpObj.inv ≫ h := by
    refine ZInQ.HomUnify.hom_ext_of_cpts _ _ fun p => ?_
    obtain ⟨w, rfl⟩ := exists_proj_eq φ p
    have e1 : Additive.toMul (φ (proj Λ w)) ≫ h ≫ GrpObj.inv =
        (Additive.toMul (φ₀ (proj (periodLattice Ω) (T w))))⁻¹ := by
      rw [← Category.assoc, hhw, Hom.inv_def]
    have e2 : Additive.toMul (φ (proj Λ w)) ≫ GrpObj.inv ≫ h =
        (Additive.toMul (φ₀ (proj (periodLattice Ω) (T w))))⁻¹ := by
      rw [← Category.assoc, ← Hom.inv_def, ← toMul_proj_neg φ w, hhw, map_neg T w,
        toMul_proj_neg φ₀ (T w)]
    rw [e1, e2]
  obtain ⟨L, s, hL, hs⟩ := hT B B₀ h hinv L₀ s₀ hL₀
  refine ⟨L, s, 0, hL, fun w => ?_⟩
  rw [hs, add_zero, ← hz₀ (T w), ← hhw w]
  rfl

end PazukiAlg
