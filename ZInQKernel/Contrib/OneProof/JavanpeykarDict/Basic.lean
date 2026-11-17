import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

/-! # javanpeykar-dict (part 1): Jacobian and genus dictionary, the printed leaf, the Belyi glue

Task javanpeykar-dict (2026-11-16), report `docs/research/javanpeykar-dict.md`, scratch
`scratch/javanpeykar-dict/`.

**Target.** The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound`
(`ZInQKernel/OneProof/H/TailY.lean`). The 11-16 dictionary pass rated it a consequence of
Javanpeykar 2014 Thm 1.1.1 through three dictionary steps: (1) the kernel's Jacobian (`IsJacobian`, an
Albanese predicate over `PkgI3.AbVar`) against the print's `Jac(X)`; (2) `dim J` against the genus;
(3) the kernel's `K`-rational `IsBelyiFunction` against a Belyi map of `X` over `ℚ̄`.

**Results.**
* §1 `isStableFaltingsHeight_of_iso`: the published stable height is invariant under isomorphism of
  abelian varieties (transport of Néron models and metrized models through `e_L`). Proved.
* §2 `abVarIso_picZero_of_isJacobian` (copied from isj1-dict, `R16IsJ1Dict.lean`): every kernel Jacobian
  is isomorphic to every tensor-compatible representative of `Pic⁰_{X/K}` (vendored Jacobian-Challenge
  library: Milne's Albanese property of the Abel–Jacobi map). Step (1), proved.
* §3 `dim_eq_genusK`, `genusBar_eq`: `dim J = dim_K H¹(X, 𝒪) = dim_ℚ̄ H¹(X_ℚ̄, 𝒪)` (vendored: `Pic⁰` is
  smooth of genus dimension, smooth schemes have the expected Krull dimension, flat base change of
  cohomology). Step (2), proved.
* §4 the restated leaf `JavanpeykarPrinted` (the print for `X = X₀ ×_K ℚ̄`: `Jac(X)` as `Pic⁰`, `g` the
  genus of `X_ℚ̄`, a Belyi function of `X_ℚ̄` over `ℚ̄`), the glue `BelyiBaseChange` (step (3): a
  `K`-rational Belyi function stays a Belyi function over `ℚ̄`, same degree; proved in `FunctionField.lean` from Stichtenoth's theorem), and
  `javanpeykarBound_of_printed : JavanpeykarPrinted → BelyiBaseChange → JavanpeykarBound`.

No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace JavanpeykarDict

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.HeightSplit
open LeafModCurves (IsCurve IsJacobian IsBelyiFunction)
open ZInQ.LeafPush2 (ffAlgebra javanpeykarBound)

/-! ## 1. The published stable height is an isomorphism invariant -/

section HeightIso

variable {K : Type} [Field K] {J J' : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- `e_L : J_L ≅ J'_L`, the base change of an isomorphism `e : J ≅ J'`. -/
def bcIso (e : J.X ≅ J'.X) : (J.baseChange L).X ≅ (J'.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e

theorem bcIso_isMonHom (e : J.X ≅ J'.X) [IsMonHom e.hom] : IsMonHom (bcIso (L := L) e).hom := by
  exact Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (f := e.hom)

/-- A group model of `J_L` is a group model of `J'_L` through `e_L` (same scheme over `𝓞_L`). -/
def transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom] : GroupModel J' L where
  G := 𝒢.G
  grp := 𝒢.grp
  smooth := 𝒢.smooth
  separated := 𝒢.separated
  qc := 𝒢.qc
  gen := 𝒢.gen ≪≫ bcIso e
  gen_hom := by
    let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    have := 𝒢.gen_hom
    have := bcIso_isMonHom (L := L) e
    show IsMonHom (𝒢.gen.hom ≫ (bcIso e).hom)
    infer_instance

/-- A metrized model of `J_L` is one of `J'_L` (same Hodge data). -/
def transportM {g : ℕ} (M : MetrizedModel J L g) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    MetrizedModel J' L g where
  model := transport M.model e
  hodge := M.hodge
  lattice_eq := M.lattice_eq
  arch := M.arch

theorem bcIso_trans_symm (e : J.X ≅ J'.X) : bcIso (L := L) e ≪≫ bcIso e.symm = Iso.refl _ := by
  have h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e ≪≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e.symm =
      Iso.refl ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj J.X) := by
    rw [Functor.mapIso_symm, Iso.self_symm_id]
  exact h

theorem transport_transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom]
    [IsMonHom e.symm.hom] : transport (transport 𝒢 e) e.symm = 𝒢 := by
  cases 𝒢
  simp only [transport]
  congr 1
  rw [Iso.trans_assoc, bcIso_trans_symm, Iso.trans_refl]

theorem height_transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    (transport 𝒢 e).height = 𝒢.height := by
  have : IsMonHom e.symm.hom := by change IsMonHom e.inv; infer_instance
  unfold GroupModel.height
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
    refine iInf_le_of_le g (iInf_le_of_le (transportM M e) (iInf_le_of_le ?_ le_rfl))
    show transport M.model e = transport 𝒢 e
    rw [hM]
  · refine le_iInf fun g => le_iInf fun M' => le_iInf fun hM' => ?_
    refine iInf_le_of_le g (iInf_le_of_le (transportM M' e.symm) (iInf_le_of_le ?_ le_rfl))
    show transport M'.model e.symm = 𝒢
    rw [hM', transport_transport]

theorem bijective_comp_iso {Y Z W : Over (Spec (CommRingCat.of L))} (i : Z ≅ W) :
    Function.Bijective fun u : Y ⟶ Z => u ≫ i.hom :=
  ⟨fun a b h => by simpa using congrArg (· ≫ i.inv) h, fun b => ⟨b ≫ i.inv, by simp⟩⟩

theorem isNeronModel_transport (𝒩 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom]
    (h : 𝒩.IsNeronModel) : (transport 𝒩 e).IsNeronModel := by
  intro Y _
  have h1 := (bijective_comp_iso (Y := (Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) L)))).obj Y) (bcIso (L := L) e)).comp (h Y)
  refine (congrArg Function.Bijective ?_).mpr h1
  funext f
  change (Over.pullback _).map f ≫ (𝒩.gen.hom ≫ (bcIso e).hom) =
    ((Over.pullback _).map f ≫ 𝒩.gen.hom) ≫ (bcIso e).hom
  exact (Category.assoc _ _ _).symm

theorem isSemistable_transport (𝒩 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom]
    (h : IsSemistable 𝒩) : IsSemistable (transport 𝒩 e) := h

/-- **The published stable height is invariant under isomorphism of abelian varieties (glue,
proved).** -/
theorem isStableFaltingsHeight_of_iso (e : J.X ≅ J'.X) [IsMonHom e.hom] {x : ℝ}
    (h : IsStableFaltingsHeight J x) : IsStableFaltingsHeight J' x := by
  obtain ⟨L, _, _, _, 𝒩, hN, hS, hx⟩ := h
  exact ⟨L, _, _, _, transport 𝒩 e, isNeronModel_transport 𝒩 e hN,
    isSemistable_transport 𝒩 e hS, by rw [height_transport]; exact hx⟩

end HeightIso

/-! ## 2. `Pic⁰` is the Albanese (copied from isj1-dict, `R16IsJ1Dict.lean` §3, verbatim up to names) -/

section PicZero

open LeafModCurves

/-- A vendored abelian variety (commutative group scheme, smooth, proper, geometrically
irreducible) as a kernel `AbVar` (isj1-dict `R16IsJ1Dict.ofVendored`). -/
def ofVendored {K : Type} [Field K] (V : AbelianVariety K) : PkgI3.AbVar K :=
  haveI : GeometricallyIntegral V.group.X.hom := Smooth.geometricallyIntegral V.group.X.hom
  { X := V.group.X
    grp := V.group.grp
    proper := V.proper
    smooth := V.smooth
    geomInt := inferInstance }

/-- The Abel–Jacobi map into a tensor-compatible representative of `Pic⁰_{X/K}` is a Jacobian in
the kernel's sense (isj1-dict `R16IsJ1Dict.isJacobian_picZero`). -/
theorem isJacobian_picZero {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    (hX : IsCurve X) (V : AbelianVariety K)
    (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (htc : PicardTensorCompatible X.hom V.group rep)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) :
    ∃ aj : X ⟶ (ofVendored V).X, IsJacobian X P₀ (ofVendored V) aj := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible X.hom := inferInstance
  let aj : X ⟶ V.group.X :=
    Curve.abelJacobiMap (⟨X⟩ : Curve K) P₀.left (by simp) rep
  have alb : IsAlbanese P₀ V aj := Curve.isAlbanese_abelJacobiMap ⟨X⟩ P₀ V rep htc
  refine ⟨aj, ⟨alb.1, ?_⟩⟩
  intro A f hf
  obtain ⟨g, hg, huniq⟩ := alb.existsUnique_schemeMap f hf
  have pointed : η[V.group.X] ≫ g = η[A.X] := by
    rw [← alb.1, Category.assoc, ← hg, hf]
  have : GeometricallyIntegral V.group.X.hom := Smooth.geometricallyIntegral V.group.X.hom
  have hmon : IsMonHom g := isMonHom_of_isProper_of_geometricallyIntegral g pointed
  exact ⟨g, ⟨hmon, hg.symm⟩, fun φ hφ => huniq φ hφ.2.symm⟩

/-- **Every kernel Jacobian is `Pic⁰` (glue, proved; isj1-dict
`R16IsJ1Dict.abVarIso_picZero_of_isJacobian`).** -/
theorem abVarIso_picZero_of_isJacobian {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    (hX : IsCurve X) {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J : PkgI3.AbVar K}
    {aj : X ⟶ J.X} (h : IsJacobian X P₀ J aj) (V : AbelianVariety K)
    (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (htc : PicardTensorCompatible X.hom V.group rep) :
    ∃ e : J.X ≅ (ofVendored V).X, IsMonHom e.hom := by
  obtain ⟨aj', h'⟩ := isJacobian_picZero X hX V rep htc P₀
  obtain ⟨e, he, -, -⟩ := h.unique h'
  exact ⟨e, he⟩

end PicZero

/-! ## 3. `dim J` is the genus of `X_ℚ̄` -/

section Genus

variable {K : Type} [Field K]

/-- `X_L = X ×_K L`, the base change of a `K`-scheme to a field extension `L`. -/
def baseChangeCurve (X : Over (Spec (CommRingCat.of K))) (L : Type) [Field L] [Algebra K L] :
    Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X

/-- The genus of `X` over `K`: the arithmetic genus `dim_K H¹(X, 𝒪_X)` (vendored
`Scheme.arithmeticGenus`). -/
def genusK (X : Over (Spec (CommRingCat.of K))) : ℕ :=
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  X.left.arithmeticGenus K

/-- **The genus of `X_ℚ̄`**: `dim_{K̄} H¹(X_{K̄}, 𝒪)` for an algebraic closure `K̄` of `K` (for a number
field `K`, an algebraic closure of `ℚ`). For a smooth projective connected curve this is its genus. -/
def genusBar (X : Over (Spec (CommRingCat.of K))) : ℕ :=
  letI : (baseChangeCurve X (AlgebraicClosure K)).left.Over
      (Spec (CommRingCat.of (AlgebraicClosure K))) := ⟨(baseChangeCurve X (AlgebraicClosure K)).hom⟩
  (baseChangeCurve X (AlgebraicClosure K)).left.arithmeticGenus (AlgebraicClosure K)

/-- The genus does not change under extension of the ground field (vendored
`Scheme.arithmeticGenus_pullback`, flat base change of cohomology). -/
theorem genusBar_eq {X : Over (Spec (CommRingCat.of K))} (hX : IsCurve X) :
    genusBar X = genusK X := by
  have : IsProper X.hom := hX.proper
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  have : QuasiCompact (X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (QuasiCompact X.hom)
  have : QuasiSeparated (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiSeparated X.hom)
  exact Scheme.arithmeticGenus_pullback (AlgebraicClosure K)

/-- **`dim J = genus` (glue, proved).** The kernel's Jacobian of a curve has dimension the arithmetic
genus: it is isomorphic to the vendored `Pic⁰` representative, which is smooth of relative dimension
`arithmeticGenus` (vendored `exists_abelianVariety_picardDegreeZero`), and a nonempty smooth scheme of
relative dimension `n` over a field has Krull dimension `n` (vendored
`topologicalKrullDim_eq_of_smoothOfRelativeDimension`). -/
theorem dim_eq_genusK {X : Over (Spec (CommRingCat.of K))} (hX : IsCurve X)
    {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J : PkgI3.AbVar K} {aj : X ⟶ J.X}
    (h : IsJacobian X P₀ J aj) : J.dim = ((genusK X : ℕ) : WithBot ℕ∞) := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨V, rep, htc, hdim⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  obtain ⟨e, -⟩ := abVarIso_picZero_of_isJacobian hX h V rep htc
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hne : Nonempty V.group.X.left :=
    ⟨(η[V.group.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ V.group.X).left
      (IsLocalRing.closedPoint K)⟩
  have h1 := AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension
    V.group.X.hom (X.left.arithmeticGenus K)
  unfold PkgI3.AbVar.dim genusK
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.left.homeomorph.isHomeomorph]
  exact h1

end Genus

/-! ## 4. The restated leaf, the glue, and the old field -/

/-- **Leaf R18-Javanpeykar, printed form** (A. Javanpeykar, *Polynomial bounds for Arakelov invariants
of Belyi curves*, Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90; arXiv:1403.6404v1 p. 1; height
identification p. 98 / arXiv §2.3 p. 9; read by the locator audit, docs/research/locators.md).
Printed: for a smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1`,
`h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where `h_Fal(X)` is the stable Faltings height of `Jac(X)` and
`deg_B(X)` the least degree of a Belyi map `X → ℙ¹_ℚ̄` (a finite morphism unramified outside
`{0, 1, ∞}`).

Stated for `X = X₀ ×_K ℚ̄`, `X₀` a smooth proper geometrically connected curve over a number field `K`
(`ℚ̄ = AlgebraicClosure K`), in the print's terms:
* `Jac(X)`: `V`, an abelian variety over `K` representing the degree-zero Picard functor `Pic⁰_{X₀/K}`
  with the tensor-product group law (vendored Jacobian-Challenge `picardFunctorDegree`,
  `PicardTensorCompatible`); `V_ℚ̄` represents `Pic⁰_{X/ℚ̄}` (the Picard functor commutes with base
  change), so `V_ℚ̄ = Jac(X)`, and `x` is the published stable height of `V`
  (`IsStableFaltingsHeight`), which is `h_F(Jac X)` (the stable height of an abelian variety over
  `ℚ̄` is that of any model over a number field);
* `g`: `genusBar X₀ = dim_ℚ̄ H¹(X, 𝒪_X)`, the genus of `X`;
* a Belyi map of `X` of degree `d`, in function-field form: `t ∈ ℚ̄(X)` transcendental over `ℚ̄`, with
  ramification index `1` at every place of `ℚ̄(X)/ℚ̄` over a point `a ∈ 𝔸¹(ℚ̄) ∖ {0, 1}` (kernel
  `IsBelyiFunction` over `ℚ̄`, where the monic irreducible `q ≠ T, T − 1` are the `T − a`), and
  `d = [ℚ̄(X) : ℚ̄(t)]`; the morphism `X → ℙ¹_ℚ̄` defined by `t` is then a Belyi map of degree `d`
  (curves over `ℚ̄` and their function fields, Hartshorne I.6, UNVERIFIED number), so
  `deg_B(X) ≤ d`, and the printed bound is increasing in `deg_B`.
Faltings' normalization: the weaker reading if the paper used Deligne's (`h_D ≥ h_F`). -/
def JavanpeykarPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    (V : AbelianVariety K) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
    PicardTensorCompatible X.hom V.group rep →
    1 ≤ genusBar X →
    ∀ [IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left]
      (t : (baseChangeCurve X (AlgebraicClosure K)).left.functionField),
      letI := ffAlgebra (baseChangeCurve X (AlgebraicClosure K))
      IsBelyiFunction (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)).left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin (AlgebraicClosure K) {t})
        (baseChangeCurve X (AlgebraicClosure K)).left.functionField = d → 0 < d →
      ∀ x : ℝ, IsStableFaltingsHeight (ofVendored V) x → x ≤ javanpeykarBound (genusBar X) d

/-- **Glue (proved in `JavanpeykarDict/FunctionField.lean`, `belyiBaseChange_of_unramified`, from the leaf `ConstantFieldExtensionUnramified`): a `K`-rational Belyi function stays a Belyi function over `ℚ̄`, of
the same degree.** For a smooth proper geometrically connected integral curve `X/K` over a number
field and `t ∈ K(X)` a Belyi function over `K` (`IsBelyiFunction K`) of degree
`d = [K(X) : K(t)] > 0`, the base change `X_ℚ̄` is integral and some `t' ∈ ℚ̄(X_ℚ̄)` (the image of `t`)
is a Belyi function over `ℚ̄` of degree `d`.

Proof outline (formalized in `FunctionField.lean` and `BelyiAlgebra.lean`): `ℚ̄(X_ℚ̄) = K(X) ⊗_K ℚ̄` (`X` geometrically integral), so
`[ℚ̄(X_ℚ̄) : ℚ̄(t)] = [K(X) : K(t)]`; a place `w` of `ℚ̄(X_ℚ̄)/ℚ̄` with `t − a ∈ 𝔪_w`, `a ≠ 0, 1`, lies over
the place `w₀ = w ∩ K(X)`, where `p(t) ∈ 𝔪_{w₀}` for `p` the minimal polynomial of `a` over `K`
(`p ≠ T, T − 1`), so `p(t)` is a uniformizer at `w₀`; a constant field extension is unramified
(Stichtenoth, *Algebraic Function Fields and Codes*, Thm 3.6.3, UNVERIFIED number; `K` perfect), so
`p(t)` is a uniformizer at `w`, and `t − a` is too (the other factors `t − a'`, `a' ≠ a` conjugate,
are units at `w`). -/
def BelyiBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral X.left] (t : X.left.functionField),
    letI := ffAlgebra X
    IsBelyiFunction K X.left.functionField t →
    ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
    ∃ (_ : IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left)
      (t' : (baseChangeCurve X (AlgebraicClosure K)).left.functionField),
      letI := ffAlgebra (baseChangeCurve X (AlgebraicClosure K))
      IsBelyiFunction (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)).left.functionField
        t' ∧
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure K) {t'})
        (baseChangeCurve X (AlgebraicClosure K)).left.functionField = d

/-- **The old field from the printed leaf and the Belyi glue.** Steps (1) Jacobian = `Pic⁰`
(`abVarIso_picZero_of_isJacobian`, `isStableFaltingsHeight_of_iso`) and (2) `dim J = genus of X_ℚ̄`
(`dim_eq_genusK`, `genusBar_eq`) are proved; step (3) is `BelyiBaseChange`. -/
theorem javanpeykarBound_of_printed (hJ : JavanpeykarPrinted) (hB : BelyiBaseChange) :
    ZInQ.HeightSplit.JavanpeykarBound := by
  intro K _ _ X _ _ P₀ J aj hJac g hg hg1 t ht d hd hd0 x hx
  have hX : IsCurve X := inferInstance
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  letI : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  obtain ⟨e, he⟩ := abVarIso_picZero_of_isJacobian hX hJac V rep htc
  have hx' := isStableFaltingsHeight_of_iso e hx
  have hgen : g = genusBar X := by
    have h2 := dim_eq_genusK hX hJac
    rw [hg] at h2
    rw [genusBar_eq hX]
    exact_mod_cast h2
  obtain ⟨hint, t', ht', hd'⟩ := hB K X t ht d hd hd0
  subst hgen
  exact hJ K X V rep htc hg1 t' ht' d hd' hd0 x hx'

end JavanpeykarDict
