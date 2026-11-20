import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import ZInQKernel.Contrib.OneProof.R16Used
import ZInQKernel.Contrib.OneProof.DSThm965Weak

/-! # isj1-dict: the `IsJ1` dictionary behind `AfTateCharPoly`, and the leaf under the weak reading

Task isj1-dict (2026-11-16), report `docs/research/isj1-dict.md`, scratch `scratch/isj1-dict/`.

**Target.** The bundle field `r16CoreY : R16Split.R16CoreY` (Eichler–Shimura for `A_f`, consumed by
`G0ModNewform.g13` at `ℓ = 5`). r16-used (`R16Used.lean`) discharges it from the leaf
`R16Used.AfTateCharPoly` (Diamond–Shurman Lemma 9.5.3 + Thm 9.5.4, existence form) quantified over
every `J` with `LeafModCurves.IsJ1 N J`.

**Part 1 (the dictionary, proved).** The kernel's `IsJ1 N J` says: `J` has the Albanese property
for some pointed model `X` of `X₁(N)` over `ℚ` (smooth proper geometrically connected integral, function
field `ℚ(j)(x(P))`, `P` of exact order `N`). Proved here:
* `abVarIso_picZero_of_isJacobian`: every kernel Jacobian is isomorphic to every tensor-compatible
  representative of `Pic⁰_{X/ℚ}` (vendored Jacobian-Challenge library): "`Pic⁰` is the Albanese";
* `abVarIso_of_isJacobian`: independence of the base point; `IsJacobian.of_iso`: transport along curve
  isomorphisms; `AfTateAt.of_iso`: the conclusion of the leaf is invariant under isomorphism of `J`;
* `curveIsoOfFunctionFieldIso_proof`: a smooth proper curve over `ℚ` is determined by its function field
  (vendored valuative extension of rational maps and valuation stalks of smooth curves);
* `abVarIso_of_isJ1'`: any two `IsJ1 N` abelian varieties are isomorphic, from the leaf
  `X1PointsConjugate` (Igusa);
* `afTateCharPoly_of_picZero`: `AfTateCharPoly` from its form over `Pic⁰` of one model.

**Part 2 (the weak reading, proved).** `AfTateWeakOdd` replaces "characteristic polynomial" by
"Frobenius satisfies `X² − a_p X + χ(p)p`" and adds oddness on each `ι`-component;
`component_charpoly` recovers the characteristic polynomial on each `ι`-component (ds965-weak's
trace-and-determinant method with Chebotarev, T18, and the scalar case excluded by complex conjugation);
`weakOdd_of_afTate` shows the new statement is a consequence of `AfTateCharPoly`.

**Discharge.** `r16CoreY_of_picZero_igusa : AfTateCharPolyPicZero → X1PointsConjugate →
AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY`; under the weak reading
`r16CoreY_of_weakPicZero_igusa` with `AfTateWeakOddPicZero`.

No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.unusedSectionVars false

namespace R16IsJ1Dict

section DictPart


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct

/-! ## 1. Isomorphic abelian varieties -/

/-- `J` and `J'` are isomorphic abelian varieties over `K`: an isomorphism of `K`-schemes which is
a homomorphism. -/
def AbVarIso {K : Type} [Field K] (J J' : AbVar K) : Prop :=
  ∃ e : J.X ≅ J'.X, IsMonHom e.hom

theorem AbVarIso.symm {K : Type} [Field K] {J J' : AbVar K} (h : AbVarIso J J') : AbVarIso J' J := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by change IsMonHom e.inv; infer_instance⟩

theorem AbVarIso.trans {K : Type} [Field K] {J J' J'' : AbVar K} (h : AbVarIso J J')
    (h' : AbVarIso J' J'') : AbVarIso J J'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e ≪≫ e', by change IsMonHom (e.hom ≫ e'.hom); infer_instance⟩

/-! ## 2. The body of `AfTateCharPoly` at one Jacobian, and its transport -/

/-- The conclusion of `R16Used.AfTateCharPoly` for one abelian variety `J` (verbatim). -/
def AfTateAt (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ) : Prop :=
  ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
    AlgebraicGeometry.Surjective π.hom.left ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      ∃ b : (letI := R16Used.tensorModule ℓ A θ;
          Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
            (R16Used.frobMat ℓ A θ b σ).charpoly =
              R16Used.esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)
                (c * (p : coeffField f))

theorem afTateCharPoly_iff : R16Used.AfTateCharPoly ↔
    ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
      0 < N → IsNewform f χ → IsJ1 N J → AfTateAt N χ f J := Iff.rfl

/-- **Transport (glue).** The body only depends on `J` up to isomorphism: compose `π` with the
inverse isomorphism. -/
theorem AfTateAt.of_iso {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J J' : AbVar ℚ}
    (h : AfTateAt N χ f J) (e : AbVarIso J J') : AfTateAt N χ f J' := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := h
  obtain ⟨e, he⟩ := e
  refine ⟨A, Hom.mk' (e.inv ≫ π.hom), θ, ?_, hrest⟩
  rw [Hom.hom_mk', Over.comp_left]
  have : AlgebraicGeometry.Surjective π.hom.left := hπ
  infer_instance


/-! ## 3. `Pic⁰` is the Albanese: every Jacobian in the kernel's sense is the degree-zero Picard
scheme (vendored Jacobian-Challenge library) -/

/-- A vendored abelian variety (commutative group scheme, smooth, proper, geometrically
irreducible) as a kernel `AbVar`. -/
def ofVendored {K : Type} [Field K] (V : AbelianVariety K) : AbVar K :=
  haveI : GeometricallyIntegral V.group.X.hom := Smooth.geometricallyIntegral V.group.X.hom
  { X := V.group.X
    grp := V.group.grp
    proper := V.proper
    smooth := V.smooth
    geomInt := inferInstance }

@[simp] theorem ofVendored_X {K : Type} [Field K] (V : AbelianVariety K) :
    (ofVendored V).X = V.group.X := rfl

/-- **The Abel–Jacobi map into `Pic⁰` is a Jacobian in the kernel's sense (glue, from the
vendored library).** For a curve `X` over `K` (`IsCurve`), a representation `rep` of the
degree-zero Picard functor `Pic⁰_{X/K}` by an abelian variety `V` whose group law is the tensor
product of line bundles, and any `K`-point `P₀`, the Abel–Jacobi map `X → V` based at `P₀` has
the Albanese property `IsJacobian`. -/
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

/-- **Every kernel Jacobian is `Pic⁰` (glue).** If `(J, aj)` is a Jacobian of `(X, P₀)` in the
kernel's sense (`IsJacobian`, the Albanese property), then `J` is isomorphic, as an abelian
variety, to every tensor-compatible representing object of `Pic⁰_{X/K}`. -/
theorem abVarIso_picZero_of_isJacobian {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    (hX : IsCurve X) {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J : AbVar K}
    {aj : X ⟶ J.X} (h : IsJacobian X P₀ J aj) (V : AbelianVariety K)
    (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X)
    (htc : PicardTensorCompatible X.hom V.group rep) : AbVarIso J (ofVendored V) := by
  obtain ⟨aj', h'⟩ := isJacobian_picZero X hX V rep htc P₀
  obtain ⟨e, he, -, -⟩ := h.unique h'
  exact ⟨e, he⟩

/-- `Pic⁰_{X/K}` of a curve is represented by a tensor-compatible abelian variety (vendored
`exists_abelianVariety_picardDegreeZero`). -/
theorem exists_picZero {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) (hX : IsCurve X) :
    ∃ (V : AbelianVariety K) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
      PicardTensorCompatible X.hom V.group rep := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨V, rep, htc, -⟩ := exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  exact ⟨V, rep, htc⟩

/-- **Base-point independence (glue).** Two Jacobians of the same curve, for any two base points,
are isomorphic abelian varieties (both are `Pic⁰_{X/K}`). -/
theorem abVarIso_of_isJacobian {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    (hX : IsCurve X) {P₀ P₁ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J J' : AbVar K}
    {aj : X ⟶ J.X} {aj' : X ⟶ J'.X} (h : IsJacobian X P₀ J aj) (h' : IsJacobian X P₁ J' aj') :
    AbVarIso J J' := by
  obtain ⟨V, rep, htc⟩ := exists_picZero X hX
  exact (abVarIso_picZero_of_isJacobian hX h V rep htc).trans
    (abVarIso_picZero_of_isJacobian hX h' V rep htc).symm

/-- **Transport of a Jacobian along an isomorphism of curves (glue).** -/
theorem IsJacobian.of_iso {K : Type} [Field K] {X X' : Over (Spec (CommRingCat.of K))}
    (e : X ≅ X') {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X'} {J : AbVar K} {aj : X' ⟶ J.X}
    (h : IsJacobian X' P₀ J aj) : IsJacobian X (P₀ ≫ e.inv) J (e.hom ≫ aj) := by
  refine ⟨by rw [Category.assoc, e.inv_hom_id_assoc, h.base], ?_⟩
  intro A f hf
  obtain ⟨φ, ⟨hφ, hφf⟩, hu⟩ := h.univ A (e.inv ≫ f) (by rw [← Category.assoc, hf])
  refine ⟨φ, ⟨hφ, by rw [Category.assoc, hφf, e.hom_inv_id_assoc]⟩, ?_⟩
  rintro ψ ⟨hψ, hψf⟩
  refine hu ψ ⟨hψ, ?_⟩
  rw [← hψf, Category.assoc, e.inv_hom_id_assoc]

/-! ## 4. Uniqueness of `J₁(N)` from two printed leaves -/

/-- **LEAF (Igusa: the Galois group of the `N`-division field of the generic elliptic curve acts
transitively on the `x`-coordinates of the points of exact order `N`).** For `N ≥ 1` and points `P, P'`
of exact order `N` of `E_j` over `\overline{ℚ(j)}`, some `σ ∈ Aut(\overline{ℚ(j)}/ℚ(j))` maps `x(P)` to
`x(P')`.

Printed form: for `E` over `ℚ(j)` with transcendental `j`, `Gal(ℚ(j)(E[N])/ℚ(j)) ≅ GL₂(ℤ/N)` (Igusa,
*Fibre systems of Jacobian varieties III*, Amer. J. Math. 81 (1959); Shimura 1971, Thm 6.6 for the field
`F_N = ℚ(j, f_a)` of Weber functions with group `GL₂(ℤ/N)/±1`; Lang, *Elliptic Functions*, Ch. 6 §3;
Diamond–Shurman §7.5 for `y² = 4x³ − g(j)x − g(j)`; all numbers UNVERIFIED), and `GL₂(ℤ/N)` (indeed
`SL₂(ℤ/N)`) acts transitively on the vectors of order `N` of `(ℤ/N)²`. The statement here is for the
kernel's model `E_j = ofJNe0Or1728 j`; any two Weierstrass models over `ℚ(j)` with `j`-invariant `j`
differ by a twist and a `ℚ(j)`-affine change `x ↦ u²x + r` (`u² ∈ ℚ(j)`), which preserves the Galois
action on `x`-coordinates. `N ≥ 1` is needed: for `N = 0` (`addOrderOf P = 0`, infinite order) the
statement is false (`x(P) ∈ ℚ(j)` for some points of infinite order, not for others). -/
def X1PointsConjugate : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, σ (xCoord P) = xCoord P'

/-- **A smooth proper curve over `ℚ` is determined by its function field** (stated as a `Prop`; proved below,
`curveIsoOfFunctionFieldIso_proof`). Two integral
smooth proper geometrically connected curves over `ℚ` with isomorphic function fields are isomorphic
over `ℚ` (a ring isomorphism of fields of characteristic `0` is `ℚ`-linear).

Printed form: Stacks Project, *Algebraic Curves*, section "Curves and function fields" (the functor
`X ↦ k(X)` from normal proper curves over `k` with nonconstant morphisms to finitely generated field
extensions of `k` of transcendence degree 1 is an equivalence; tag UNVERIFIED); Hartshorne, *Algebraic
Geometry*, I Cor. 6.12 over an algebraically closed field (its proof, through I Prop. 6.8, the extension of
a rational map from a nonsingular curve to a projective variety, works over any field); numbers
UNVERIFIED. -/
def CurveIsoOfFunctionFieldIso : Prop :=
  ∀ (X X' : Over SpecQ) [IsIntegral X.left] [IsIntegral X'.left], IsCurve X → IsCurve X' →
    Nonempty (X.left.functionField ≃+* X'.left.functionField) → Nonempty (X ≅ X')

/-! ### The curve leaf, proved -/

/-- Any two morphisms `Spec K → Spec ℚ` agree. -/
theorem spec_to_specQ_eq {K : Type} [Field K] (a b : Spec (CommRingCat.of K) ⟶ SpecQ) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b]
  congr 1
  ext1
  exact RingHom.ext_rat _ _

/-- The generic point is dense: `Spec K(X) → X` is dominant. -/
theorem isDominant_fromSpecFunctionField (X : Scheme) [IsIntegral X] :
    IsDominant X.fromSpecFunctionField := by
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have h : genericPoint X ∈ Set.range X.fromSpecFunctionField :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have := closure_mono (Set.singleton_subset_iff.mpr h)
  rw [(genericPoint_spec X).def] at this
  exact this

/-- A scheme proper over `Spec ℚ` is separated. -/
theorem isSeparated_of_over (Y : Scheme) (f : Y ⟶ SpecQ) [IsSeparated f] : Y.IsSeparated := by
  constructor
  rw [show terminal.from Y = f ≫ terminal.from SpecQ from (terminal.hom_ext _ _)]
  infer_instance

/-- The morphism `X → X'` extending a function-field isomorphism (vendored
`exists_hom_of_valuationRing_stalk`). -/
theorem exists_hom (X X' : Over SpecQ) [IsIntegral X.left] [IsIntegral X'.left] (hX : IsCurve X)
    (hX' : IsCurve X') (φ : X'.left.functionField →+* X.left.functionField) :
    ∃ f : X ⟶ X', X.left.fromSpecFunctionField ≫ f.left =
      Spec.map (CommRingCat.ofHom φ) ≫ X'.left.fromSpecFunctionField := by
  have : IsProper X'.hom := hX'.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let _ : X.left.Over SpecQ := ⟨X.hom⟩
  let _ : X'.left.Over SpecQ := ⟨X'.hom⟩
  have : IsProper (X'.left ↘ SpecQ) := inferInstanceAs (IsProper X'.hom)
  have : X'.left.IsSeparated := isSeparated_of_over X'.left X'.hom
  have hval : ∀ x : X.left, ValuationRing (X.left.presheaf.stalk x) := fun x =>
    AlgebraicGeometry.Scheme.valuationRing_stalk X.hom x
  obtain ⟨f, hfo, hf⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := SpecQ) hval
    (Spec.map (CommRingCat.ofHom φ) ≫ X'.left.fromSpecFunctionField) (spec_to_specQ_eq _ _)
  exact ⟨Over.homMk f hfo.comp_over, hf⟩

theorem curveIsoOfFunctionFieldIso_proof : CurveIsoOfFunctionFieldIso := by
  intro X X' _ _ hX hX' ⟨e⟩
  obtain ⟨f, hf⟩ := exists_hom X X' hX hX' e.symm.toRingHom
  obtain ⟨g, hg⟩ := exists_hom X' X hX' hX e.toRingHom
  have : IsProper X.hom := hX.proper
  have : IsProper X'.hom := hX'.proper
  let _ : X.left.Over SpecQ := ⟨X.hom⟩
  let _ : X'.left.Over SpecQ := ⟨X'.hom⟩
  have : IsSeparated (X.left ↘ SpecQ) := inferInstanceAs (IsSeparated X.hom)
  have : IsSeparated (X'.left ↘ SpecQ) := inferInstanceAs (IsSeparated X'.hom)
  have : IsDominant X.left.fromSpecFunctionField := isDominant_fromSpecFunctionField X.left
  have : IsDominant X'.left.fromSpecFunctionField := isDominant_fromSpecFunctionField X'.left
  have hfg : f ≫ g = 𝟙 X := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.id_left]
    have : f.left.IsOver SpecQ := ⟨Over.w f⟩
    have : g.left.IsOver SpecQ := ⟨Over.w g⟩
    refine ext_of_isDominant_of_isSeparated' SpecQ X.left.fromSpecFunctionField ?_
    rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc,
      ← Spec.map_comp, Category.comp_id]
    conv_rhs => rw [← Category.id_comp X.left.fromSpecFunctionField]
    congr 1
    rw [← Spec.map_id]
    congr 1
    ext x
    simp
    rfl
  have hgf : g ≫ f = 𝟙 X' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.id_left]
    have : g.left.IsOver SpecQ := ⟨Over.w g⟩
    have : f.left.IsOver SpecQ := ⟨Over.w f⟩
    refine ext_of_isDominant_of_isSeparated' SpecQ X'.left.fromSpecFunctionField ?_
    rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc,
      ← Spec.map_comp, Category.comp_id]
    conv_rhs => rw [← Category.id_comp X'.left.fromSpecFunctionField]
    congr 1
    rw [← Spec.map_id]
    congr 1
    ext x
    simp
    rfl
  exact ⟨⟨f, g, hfg, hgf⟩⟩

/-- `K_N` does not depend on the point (glue): a `ℚ(j)`-automorphism carrying `x(P)` to `x(P')`
carries `ℚ(j)(x(P))` onto `ℚ(j)(x(P'))`. -/
def fieldX1Equiv {P P' : EjBar.toAffine.Point} (σ : Kbar ≃ₐ[Qj] Kbar)
    (hσ : σ (xCoord P) = xCoord P') : fieldX1 P ≃+* fieldX1 P' :=
  ((IntermediateField.equivMap (fieldX1 P) (σ : Kbar →ₐ[Qj] Kbar)).trans
    (IntermediateField.equivOfEq (by
      rw [fieldX1, fieldX1, IntermediateField.adjoin_map, Set.image_singleton]
      exact congrArg (fun x => IntermediateField.adjoin Qj {x}) hσ))).toRingEquiv

/-- **Uniqueness of `J₁(N)` (glue, from the two leaves).** Any two abelian varieties satisfying
`IsJ1 N` (`N ≥ 1`) are isomorphic. -/
theorem abVarIso_of_isJ1 (hI : X1PointsConjugate) (hC : CurveIsoOfFunctionFieldIso) {N : ℕ}
    (hN : 0 < N) {J J' : AbVar ℚ} (h : IsJ1 N J) (h' : IsJ1 N J') : AbVarIso J J' := by
  obtain ⟨X, P₀, aj, ⟨hXc, hXi, P, hP, ⟨eX⟩⟩, hJ⟩ := h
  obtain ⟨X', P₀', aj', ⟨hXc', hXi', P', hP', ⟨eX'⟩⟩, hJ'⟩ := h'
  obtain ⟨σ, hσ⟩ := hI N P P' hN hP hP'
  obtain ⟨e⟩ := @hC X X' hXi hXi' hXc hXc' ⟨(eX.trans (fieldX1Equiv σ hσ)).trans eX'.symm⟩
  exact abVarIso_of_isJacobian hXc hJ (IsJacobian.of_iso e hJ')

/-! ## 5. The leaf restated over one Jacobian, and over `Pic⁰` -/

/-- `AfTateCharPoly`, existence form over one Jacobian of one model. -/
def AfTateCharPolyJ1Exists : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ J : AbVar ℚ, IsJ1 N J ∧ AfTateAt N χ f J

/-- **`AfTateCharPoly` from its form over one Jacobian (glue).** -/
theorem afTateCharPoly_of_exists (h : AfTateCharPolyJ1Exists) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) : R16Used.AfTateCharPoly := by
  intro N χ f J hN hf hJ
  obtain ⟨J₀, hJ₀, hA⟩ := h N χ f hN hf
  exact hA.of_iso (abVarIso_of_isJ1 hI hC hN hJ₀ hJ)

/-- **LEAF candidate: `AfTateCharPoly` over `Pic⁰` of one model of `X₁(N)`.** For `N ≥ 1` and a
newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ` there is a model `X` of `X₁(N)` over `ℚ` (`IsX1Model`:
smooth proper geometrically connected integral, function field `ℚ(j)(x(P))`, `P` of exact order
`N`) such that the degree-zero Picard scheme `J₁(N) = Pic⁰_{X/ℚ}` (some representing abelian
variety with the tensor group law) satisfies the conclusion of `AfTateCharPoly`. -/
def AfTateCharPolyPicZero : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∃ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep ∧ AfTateAt N χ f (ofVendored V)

/-- **`AfTateCharPoly` from its `Pic⁰` form (glue).** No rational point is assumed on the model:
it is transported from the one carried by `IsJ1`. -/
theorem afTateCharPoly_of_picZero (h : AfTateCharPolyPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) : R16Used.AfTateCharPoly := by
  intro N χ f J hN hf hJ
  obtain ⟨X₀, ⟨hXc₀, hXi₀, P₀', hP₀', ⟨eX₀⟩⟩, V, rep, htc, hA⟩ := h N χ f hN hf
  obtain ⟨X, P₀, aj, ⟨hXc, hXi, P, hP, ⟨eX⟩⟩, hJac⟩ := hJ
  obtain ⟨σ, hσ⟩ := hI N P₀' P hN hP₀' hP
  obtain ⟨e⟩ := @hC X₀ X hXi₀ hXi hXc₀ hXc ⟨(eX₀.trans (fieldX1Equiv σ hσ)).trans eX.symm⟩
  exact hA.of_iso
    (abVarIso_picZero_of_isJacobian hXc₀ (IsJacobian.of_iso e hJac) V rep htc).symm

/-- The `Pic⁰` form is a consequence of `AfTateCharPoly` and the existence of a model with a
rational point (so it is never stronger than the current leaf, given `X1ModelExists`-type input). -/
theorem afTateCharPolyPicZero_of_afTate (h : R16Used.AfTateCharPoly)
    (hx : ∀ N : ℕ, 0 < N → ∃ (X : Over SpecQ) (_ : RatPt X), IsX1Model N X) :
    AfTateCharPolyPicZero := by
  intro N χ f hN hf
  obtain ⟨X, P₀, hX⟩ := hx N hN
  obtain ⟨V, rep, htc⟩ := exists_picZero X hX.1
  refine ⟨X, hX, V, rep, htc, ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact h N χ f (ofVendored V) hN hf ⟨X, P₀, aj, hX, hJ⟩


end DictPart

section WeakPart


open Polynomial
open PkgI3 PkgI3.AbVar LeafModCurves
open scoped TensorProduct

/-! ## 1. Frobenius in the sense of `GlueC10.IsFrobAt` on roots of unity -/

section RootsOfUnity

open ZInQ.Contrib.G9.PkgI4

/-- At a Frobenius `σ` in the sense of `IsFrobAt` (a prime `𝔓` of `ℤ̄` over `p` with
`σ x ≡ x^p mod 𝔓`), roots of unity of order prime to `p` are raised to the `p`-th power. -/
theorem frobAt_pow_of_rootOfUnity {σ : GQ} {p : ℕ} (hp : p.Prime) (hσ : GlueC10.IsFrobAt σ p)
    {ζ : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) (hpm : ¬ p ∣ m) : σ ζ = ζ ^ p := by
  obtain ⟨P, hP, hPp, hcong⟩ := hσ
  have hint : ∀ x : Qbar, x ^ m = 1 → IsIntegral ℤ x := fun x hx =>
    ⟨Polynomial.X ^ m - 1, monic_X_pow_sub_C 1 hm, by simp [hx]⟩
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp [hm] at hζ
  have hσζm : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  set ξ := σ ζ * (ζ ^ p)⁻¹ with hξ
  have hξm : ξ ^ m = 1 := by
    rw [hξ, mul_pow, hσζm, inv_pow, ← pow_mul, mul_comm p m, pow_mul, hζ, one_pow, inv_one, one_mul]
  -- elements of `ℤ̄`
  let z : GlueC10.Zbar := ⟨ζ, hint ζ hζ⟩
  let zi : GlueC10.Zbar := ⟨(ζ ^ p)⁻¹, hint _ (by rw [inv_pow, ← pow_mul, mul_comm p m, pow_mul, hζ,
    one_pow, inv_one])⟩
  let w : GlueC10.Zbar := ⟨ξ, hint ξ hξm⟩
  let d : GlueC10.Zbar := ⟨σ ζ - ζ ^ p, by
    have h1 : IsIntegral ℤ (σ ζ) := hint _ hσζm
    exact h1.sub ((hint ζ hζ).pow p)⟩
  have hd : d ∈ P := hcong z d rfl
  have hw1 : w - 1 ∈ P := by
    have : w - 1 = d * zi := by
      apply Subtype.ext
      change ξ - 1 = (σ ζ - ζ ^ p) * (ζ ^ p)⁻¹
      rw [hξ, sub_mul, mul_inv_cancel₀ (pow_ne_zero _ hζ0)]
    rw [this]
    exact P.mul_mem_right _ hd
  by_contra hne
  have hξne : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ, mul_inv_eq_one₀ (pow_ne_zero _ hζ0)] at h
    exact h
  have hwne : w ≠ 1 := fun h => hξne (congrArg Subtype.val h)
  have hgeom : ∑ j ∈ Finset.range m, w ^ j = 0 := by
    have := geom_sum_mul w m
    have hwm : w ^ m = 1 := Subtype.ext (by
      change ξ ^ m = 1
      exact hξm)
    rw [hwm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hwne)
  have hj : ∀ j, w ^ j - 1 ∈ P := by
    intro j
    have : w ^ j - 1 = (w - 1) * ∑ i ∈ Finset.range j, w ^ i := by rw [mul_comm, geom_sum_mul]
    rw [this]
    exact P.mul_mem_right _ hw1
  have hmP : (m : GlueC10.Zbar) ∈ P := by
    have : (m : GlueC10.Zbar) = -∑ j ∈ Finset.range m, (w ^ j - 1) := by
      rw [Finset.sum_sub_distrib, hgeom]; simp
    rw [this]
    exact P.neg_mem (P.sum_mem fun j _ => hj j)
  have hpP : (p : GlueC10.Zbar) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.subset_span rfl
    simpa using this
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * p = 1 := by
    obtain ⟨a, b, h⟩ := Nat.Coprime.isCoprime hcop.symm
    exact ⟨a, b, by exact_mod_cast h⟩
  have h1 : (1 : GlueC10.Zbar) ∈ P := by
    have : (1 : GlueC10.Zbar) = (a : GlueC10.Zbar) * m + (b : GlueC10.Zbar) * p := by
      exact_mod_cast hab.symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hmP) (P.mul_mem_left _ hpP)
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

/-- The cyclotomic character at a Frobenius (`IsFrobAt`) at `p ≠ ℓ` is `p`. -/
theorem cycQ_frobAt {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {p : ℕ} (hp : p.Prime) (hpl : p ≠ ℓ)
    (hσ : GlueC10.IsFrobAt σ p) :
    ((ZInQ.Contrib.HodgeSplit.G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (p : PadicAlgCl ℓ) := by
  have hc : ((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_natCast]
    have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
    have : NeZero (ℓ ^ n) := ⟨hl⟩
    refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
    have htn : (t : Qbar) ^ (ℓ ^ n) = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hpm : ¬ p ∣ ℓ ^ n := fun h =>
      hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h))
    change σ (t : Qbar) = ((t ^ ((p : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
    rw [frobAt_pow_of_rootOfUnity hp hσ hl htn hpm, Units.val_pow_eq_pow_val, ZMod.val_natCast,
      ← ZInQ.Contrib.HodgeSplit.pow_eq_pow_mod_of htn]
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [hc]
  simp

/-- `ε₀` at a Frobenius (`IsFrobAt`) at `p ∤ N`. -/
theorem eps0_frobAt {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : GQ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hσ : GlueC10.IsFrobAt σ p) :
    ∃ γ : Qbar, ιC γ = χ (p : ZMod N) ∧
      ((ZInQ.Contrib.HodgeSplit.eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  obtain ⟨γ, hγ, hval⟩ := ZInQ.Contrib.HodgeSplit.chiL_spec ιC ιL χ
    (ZInQ.Contrib.HodgeSplit.modCycQ σ)
  refine ⟨γ, ?_, hval⟩
  rw [hγ]
  congr 1
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ N = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  change σ (t : Qbar) = ((t ^ ((p : ZMod N)).val : Qbarˣ) : Qbar)
  rw [frobAt_pow_of_rootOfUnity hp hσ (NeZero.ne N) htn hpN, Units.val_pow_eq_pow_val,
    ZMod.val_natCast, ← ZInQ.Contrib.HodgeSplit.pow_eq_pow_mod_of htn]

end RootsOfUnity

/-! ## 2. An `ℓ`-adic embedding of `ℚ̄` extending a given embedding of `F ⊆ ℂ` -/

theorem exists_iotaL (ℓ : ℕ) [Fact ℓ.Prime] (F : IntermediateField ℚ ℂ)
    (emb : F →+* PadicAlgCl ℓ) (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) :
    ∃ ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ,
      ∀ (γ : ZInQ.Contrib.G9.PkgI4.Qbar) (c : F), (c : ℂ) = ιC γ → ιL γ = emb c := by
  let L : IntermediateField ℚ ZInQ.Contrib.G9.PkgI4.Qbar := F.comap ιC
  let g : L →ₐ[ℚ] F :=
    { toFun := fun x => ⟨ιC (x : ZInQ.Contrib.G9.PkgI4.Qbar), x.2⟩
      map_one' := Subtype.ext (map_one ιC)
      map_mul' := fun x y => Subtype.ext (map_mul ιC (x : ZInQ.Contrib.G9.PkgI4.Qbar) y)
      map_zero' := Subtype.ext (map_zero ιC)
      map_add' := fun x y => Subtype.ext (map_add ιC (x : ZInQ.Contrib.G9.PkgI4.Qbar) y)
      commutes' := fun q => Subtype.ext (ιC.commutes q) }
  let f : L →ₐ[ℚ] PadicAlgCl ℓ := (emb.toRatAlgHom).comp g
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (K := PadicAlgCl ℓ)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) f
  refine ⟨φ, fun γ c hc => ?_⟩
  have hγ : γ ∈ L := by
    change ιC γ ∈ F
    rw [← hc]; exact c.2
  have h1 := congrArg (fun h => h ⟨γ, hγ⟩) hφ
  simp only [AlgHom.coe_comp, Function.comp_apply, IntermediateField.coe_val] at h1
  rw [h1]
  change emb ⟨ιC γ, hγ⟩ = emb c
  congr 1
  exact Subtype.ext hc.symm

/-! ## 3. Complex conjugation -/

/-- Complex conjugations exist in `G_ℚ` (copied from `ZInQ.LeafPush2.exists_isComplexConj`). -/
theorem exists_isComplexConj : ∃ c : ZInQ.Contrib.G9.PkgI4.GQ, ZInQ.Contrib.G9.PkgI4.IsComplexConj c := by
  obtain ⟨emb⟩ : Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra (AlgebraicClosure ℚ) ℂ := emb.toRingHom.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq (fun x => (emb.commutes x).symm)
  let χ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  refine ⟨χ.restrictNormal (AlgebraicClosure ℚ), emb, fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes χ (AlgebraicClosure ℚ) x

theorem IsComplexConj.mul_self {c : ZInQ.Contrib.G9.PkgI4.GQ}
    (hc : ZInQ.Contrib.G9.PkgI4.IsComplexConj c) : c * c = 1 := by
  obtain ⟨ι, hι⟩ := hc
  ext x
  apply ι.toRingHom.injective
  change ι (c (c x)) = ι x
  rw [hι, hι, Complex.conj_conj]


/-! ## 4. Matrices of Galois on a free rank-two `ℚ_ℓ ⊗ F`-module and its `ι`-components -/

section Mat

variable (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F]
  (θ : F →+* A.End0)

/-- `frobMat` is multiplicative (`G_ℚ` acts `ℚ_ℓ ⊗ F`-linearly). -/
theorem frobMat_mul
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (σ τ : PkgI4.GQ) :
    R16Used.frobMat ℓ A θ b (σ * τ) = R16Used.frobMat ℓ A θ b σ * R16Used.frobMat ℓ A θ b τ := by
  let _ := R16Used.tensorModule ℓ A θ
  ext i j
  simp only [R16Used.frobMat, Matrix.of_apply, Matrix.mul_apply]
  have h : A.galRep ℓ (σ * τ) (b j) = A.galRep ℓ σ (A.galRep ℓ τ (b j)) :=
    LinearMap.congr_fun (map_mul (A.galRep ℓ) σ τ) (b j)
  rw [h]
  conv_lhs => rw [← b.sum_repr (A.galRep ℓ τ (b j))]
  rw [map_sum]
  simp_rw [R16Used.galRep_tsmul]
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem frobMat_one
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ)) :
    R16Used.frobMat ℓ A θ b 1 = 1 := by
  let _ := R16Used.tensorModule ℓ A θ
  ext i j
  have h1 : A.galRep ℓ 1 (b j) = b j := LinearMap.congr_fun (map_one (A.galRep ℓ)) (b j)
  simp only [R16Used.frobMat, Matrix.of_apply]
  erw [h1]
  rw [b.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-- The matrix of `σ` on the `ι`-component: `ι_R` applied to `frobMat`. -/
def compMat
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ : PkgI4.GQ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) :=
  (R16Used.frobMat ℓ A θ b σ).map (R16Used.liftHom (k := ℚ_[ℓ]) emb)

theorem compMat_mul
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ τ : PkgI4.GQ) :
    compMat ℓ A θ b emb (σ * τ) = compMat ℓ A θ b emb σ * compMat ℓ A θ b emb τ := by
  rw [compMat, frobMat_mul, Matrix.map_mul]; rfl

theorem compMat_one
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) : compMat ℓ A θ b emb 1 = 1 := by
  rw [compMat, frobMat_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trace_det_frobOn
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ : PkgI4.GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = (compMat ℓ A θ b emb σ).trace ∧
      LinearMap.det (frobOn ℓ A θ emb σ) = (compMat ℓ A θ b emb σ).det := by
  obtain ⟨-, h⟩ := R16Used.iota_component ℓ A θ b emb
  obtain ⟨h1, h2⟩ := h σ
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · exact AddMonoidHom.map_trace (R16Used.liftHom (k := ℚ_[ℓ]) emb).toAddMonoidHom _
  · exact RingHom.map_det _ _

theorem esPoly_map (emb : F →+* PadicAlgCl ℓ) (a d : F) :
    (R16Used.esPoly ℓ a d).map (R16Used.liftHom (k := ℚ_[ℓ]) emb) =
      Polynomial.X ^ 2 - C (emb a) * Polynomial.X + C (emb d) := by
  simp [R16Used.esPoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, R16Used.liftHom_one_tmul]

/-- The weak relation over `ℚ_ℓ ⊗ F` gives the weak relation on each `ι`-component. -/
theorem aeval_compMat
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (σ : PkgI4.GQ) (a d : F)
    (h : aeval (R16Used.frobMat ℓ A θ b σ) (R16Used.esPoly ℓ a d) = 0) :
    aeval (compMat ℓ A θ b emb σ) (Polynomial.X ^ 2 - C (emb a) * Polynomial.X + C (emb d)) = 0 := by
  set φ := R16Used.liftHom (k := ℚ_[ℓ]) emb
  have hcomp : φ.mapMatrix.comp (algebraMap (ℚ_[ℓ] ⊗[ℚ] F) (Matrix (Fin 2) (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F))) =
      (algebraMap (PadicAlgCl ℓ) (Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))).comp φ := by
    refine RingHom.ext fun r => ?_
    ext i j
    simp only [RingHom.comp_apply, Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.diagonal_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    split_ifs <;> simp
  have key : ∀ P : (ℚ_[ℓ] ⊗[ℚ] F)[X],
      aeval (compMat ℓ A θ b emb σ) (P.map φ) = φ.mapMatrix (aeval (R16Used.frobMat ℓ A θ b σ) P) := by
    intro P
    rw [aeval_def, aeval_def, eval₂_map, hom_eval₂, hcomp]
    rfl
  have hmap : (R16Used.esPoly ℓ a d).map φ = Polynomial.X ^ 2 - C (emb a) * Polynomial.X + C (emb d) := by
    simp [R16Used.esPoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, φ, R16Used.liftHom_one_tmul]
  rw [← hmap, key, h, map_zero]

end Mat


/-! ## 5. Continuity, and the trace-and-determinant argument on one `ι`-component -/

section Main

variable (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F]
  (θ : F →+* A.End0)

theorem continuous_orbit (hT : TateModuleFree) (v : A.V ℓ) :
    Continuous (fun σ : Field.absoluteGaloisGroup ℚ => A.galRep ℓ σ v) := by
  have hℓ : ((ℓ : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨h1, h2, -⟩ := hT ℚ A ℓ hℓ
  have hc := PkgI3.RhoCont.continuous_galRep ℓ A
  have h0 : Continuous (fun σ : Field.absoluteGaloisGroup ℚ => (σ, v)) :=
    Continuous.prodMk continuous_id continuous_const
  refine (hc.comp h0).congr fun σ => ?_
  simp only [Function.comp_apply]

theorem continuous_compMat_entry (hT : TateModuleFree)
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] F) (A.V ℓ))
    (emb : F →+* PadicAlgCl ℓ) (i j : Fin 2) :
    Continuous (fun σ : PkgI4.GQ => compMat ℓ A θ b emb σ i j) := by
  let _ := R16Used.tensorModule ℓ A θ
  let crd : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ :=
    { toFun := fun v => R16Used.liftHom (k := ℚ_[ℓ]) emb (b.repr v i)
      map_add' := fun u v => by simp only [map_add, Finsupp.add_apply]
      map_smul' := fun x v => by
        rw [RingHom.id_apply, ← R16Used.tsmul_left (R16Split.rhoV ℓ A θ) x v, LinearEquiv.map_smul,
          Finsupp.smul_apply, smul_eq_mul, map_mul, R16Used.liftHom_tmul_one, Algebra.smul_def] }
  have hcrd : Continuous crd := IsModuleTopology.continuous_of_linearMap crd
  have hρ := continuous_orbit ℓ A hT (b j)
  refine (hcrd.comp hρ).congr fun σ => ?_
  rfl

open ZInQ.Contrib.HodgeSplit in
/-- **The trace-and-determinant argument on one `ι`-component (glue).** Let `V_ℓ(A)` be free of
rank 2 over `ℚ_ℓ ⊗ F` (basis `b`), `ι : F → ℚ̄_ℓ`, and suppose (weak reading) that every arithmetic
Frobenius at `p ∤ Nℓ` satisfies `X² − a_p X + χ(p)p` over `ℚ_ℓ ⊗ F`, and (oddness) that complex
conjugation has determinant `−1` on the `ι`-component. Then on the `ι`-component every such Frobenius has
characteristic polynomial `X² − ι(a_p) X + ι(χ(p)p)`. Proof: complex conjugation is non-scalar on
the component; on the open non-scalar locus the determinant agrees with `ε₀ χ_ℓ` at Frobenius
elements, hence everywhere there (Chebotarev, T18), hence on `G_ℚ` (translate by complex
conjugation); a `2 × 2` matrix satisfying a monic quadratic whose constant term is its nonzero
determinant has it as characteristic polynomial. -/
theorem component_charpoly (hT : TateModuleFree) (Fd : IntermediateField ℚ ℂ)
    (θ : Fd →+* A.End0)
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] Fd) (A.V ℓ))
    (emb : Fd →+* PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (a : ℕ → Fd)
    (hodd : ∀ c : ZInQ.Contrib.G9.PkgI4.GQ, ZInQ.Contrib.G9.PkgI4.IsComplexConj c →
      (compMat ℓ A θ b emb c).det = -1)
    (hweak : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : PkgI4.GQ, IsFrobAt σ p →
      ∃ c : Fd, (c : ℂ) = χ (p : ZMod N) ∧
        aeval (R16Used.frobMat ℓ A θ b σ) (R16Used.esPoly ℓ (a p) (c * (p : Fd))) = 0) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : PkgI4.GQ, IsFrobAt σ p → ∀ c : Fd,
      (c : ℂ) = χ (p : ZMod N) →
      (compMat ℓ A θ b emb σ).charpoly =
        Polynomial.X ^ 2 - C (emb (a p)) * Polynomial.X + C (emb (c * (p : Fd))) := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ιC⟩ : Nonempty (ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  obtain ⟨ιL, hιL⟩ := exists_iotaL ℓ Fd emb ιC
  set M := compMat ℓ A θ b emb with hM
  let Fc : PkgI4.GQ → PadicAlgCl ℓ := fun σ =>
    ((eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) *
      ((G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)
  have hFmul : ∀ σ τ, Fc (σ * τ) = Fc σ * Fc τ := by
    intro σ τ; simp only [Fc, map_mul, Units.val_mul]; ring
  have hFne : ∀ σ, Fc σ ≠ 0 := fun σ => mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have hFc : Continuous Fc :=
    (Units.continuous_val.comp (eps0_continuous ιC ιL χ)).mul
      (Units.continuous_val.comp (continuous_cycQ ℓ))
  have hFfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : PkgI4.GQ, IsFrobAt σ p → ∀ c : Fd,
      (c : ℂ) = χ (p : ZMod N) → Fc σ = emb (c * (p : Fd)) := by
    intro p hp hpN σ hσ c hc
    have hpN' : ¬ p ∣ N := fun h => hpN (dvd_mul_of_dvd_left h ℓ)
    have hpl : p ≠ ℓ := by rintro rfl; exact hpN (dvd_mul_left p N)
    obtain ⟨γ, hγ, he⟩ := eps0_frobAt ιC ιL χ hp hpN' hσ
    simp only [Fc, he, cycQ_frobAt hp hpl hσ, hιL γ c (hc.trans hγ.symm), map_mul, map_natCast]
  have hMmul : ∀ σ τ, M (σ * τ) = M σ * M τ := compMat_mul ℓ A θ b emb
  have hMone : M 1 = 1 := compMat_one ℓ A θ b emb
  have hMc : ∀ i j, Continuous fun σ => M σ i j := continuous_compMat_entry ℓ A θ hT b emb
  let D : PkgI4.GQ → PadicAlgCl ℓ := fun σ => (M σ).det
  have hDc : Continuous D := by
    have : D = fun σ => M σ 0 0 * M σ 1 1 - M σ 0 1 * M σ 1 0 := by
      funext σ; exact Matrix.det_fin_two _
    rw [this]
    exact ((hMc 0 0).mul (hMc 1 1)).sub ((hMc 0 1).mul (hMc 1 0))
  have hDmul : ∀ σ τ, D (σ * τ) = D σ * D τ := fun σ τ => by
    simp only [D, hMmul, Matrix.det_mul]
  have hDne : ∀ σ, D σ ≠ 0 := by
    intro σ h
    have h1 : D σ * D σ⁻¹ = 1 := by
      rw [← hDmul, mul_inv_cancel]; simp only [D, hMone, Matrix.det_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  let W : Set PkgI4.GQ := {σ | DS965Weak.NonScalar (M σ)}
  have hWo : IsOpen W := by
    have : W = {σ | M σ 0 1 ≠ 0} ∪ ({σ | M σ 1 0 ≠ 0} ∪ {σ | M σ 0 0 ≠ M σ 1 1}) := by
      ext σ; simp [W, DS965Weak.NonScalar]
    rw [this]
    exact (isOpen_ne_fun (hMc 0 1) continuous_const).union
      ((isOpen_ne_fun (hMc 1 0) continuous_const).union (isOpen_ne_fun (hMc 0 0) (hMc 1 1)))
  obtain ⟨c0, hc0⟩ := exists_isComplexConj
  have hc0sq : c0 * c0 = 1 := IsComplexConj.mul_self hc0
  have hdc0 : D c0 = -1 := hodd c0 hc0
  have hNS0 : DS965Weak.NonScalar (M c0) := by
    by_contra hns
    simp only [DS965Weak.NonScalar, not_or, not_not] at hns
    obtain ⟨h01, h10, h0011⟩ := hns
    have hsq : M c0 * M c0 = 1 := by rw [← hMmul, hc0sq, hMone]
    have e00 := congrFun (congrFun hsq 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_zero, add_zero,
      Matrix.one_apply_eq] at e00
    have h1 : D c0 = 1 := by
      simp only [D, Matrix.det_fin_two, h01, h10, ← h0011, mul_zero, sub_zero, e00]
    rw [hdc0] at h1
    have h2 : (2 : PadicAlgCl ℓ) = 0 := by linear_combination -h1
    exact two_ne_zero h2
  have hDW : ∀ σ ∈ W, D σ = Fc σ := by
    refine DS965Weak.eq_on_open_of_eq_on_arithFrob (N * ℓ).primeFactors D Fc hDc hFc W hWo ?_
    intro p hp hpS v τ hv hτ hτW
    have hpN : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr
      ⟨hp, h, Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero⟩)
    have hτ' : IsFrobAt τ p := isFrobAt_of_isArithFrob τ v p hp hv hτ
    obtain ⟨c, hc, hae⟩ := hweak p hp hpN τ hτ'
    have h2 := aeval_compMat ℓ A θ b emb τ _ _ hae
    have hcp := DS965Weak.charpoly_of_aeval_nonScalar hτW h2
    obtain ⟨-, hdet⟩ := R16Used.trace_det_of_charpoly _ _ _ hcp
    rw [hFfrob p hp hpN τ hτ' c hc]
    exact hdet
  have hD : ∀ σ, D σ = Fc σ := by
    intro σ
    by_cases hσ : σ ∈ W
    · exact hDW σ hσ
    · have hσc : σ * c0 ∈ W := by
        show DS965Weak.NonScalar (M (σ * c0))
        rw [hMmul]
        exact DS965Weak.nonScalar_mul hσ (hDne σ) hNS0
      have h1 := hDW _ hσc
      rw [hDmul, hFmul, hDW c0 hNS0] at h1
      exact mul_right_cancel₀ (hFne c0) h1
  intro p hp hpN σ hσ c hc
  obtain ⟨c', hc', hae⟩ := hweak p hp hpN σ hσ
  have hcc : c' = c := Subtype.ext (hc'.trans hc.symm)
  subst hcc
  have h2 := aeval_compMat ℓ A θ b emb σ _ _ hae
  refine DS965Weak.charpoly_of_aeval_det h2 ?_ ?_
  · exact (hD σ).trans (hFfrob p hp hpN σ hσ c' hc)
  · rw [← hFfrob p hp hpN σ hσ c' hc]; exact hFne σ

end Main


/-! ## 6. The leaf under the weak reading, and `r16CoreY` from it -/

section Leaf

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ CF coeff IsNewform)

/-- The conclusion of the weak-reading leaf at one abelian variety `J`: a quotient `π : J ↠ A`
with `θ : K_f → End⁰(A)` such that, for every prime `ℓ`, `V_ℓ(A)` is free of rank 2 over
`ℚ_ℓ ⊗ K_f`, complex conjugation has determinant `−1` on every `ι`-component (oddness), and every
arithmetic Frobenius at `p ∤ Nℓ` **satisfies** `X² − a_p X + χ(p) p` over `ℚ_ℓ ⊗ K_f`. -/
def AfTateWeakOddAt (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ) : Prop :=
  ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
    AlgebraicGeometry.Surjective π.hom.left ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      ∃ b : (letI := R16Used.tensorModule ℓ A θ;
          Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)),
        (∀ (emb : coeffField f →+* PadicAlgCl ℓ) (c : GQ), ZInQ.Contrib.G9.PkgI4.IsComplexConj c →
          LinearMap.det (frobOn ℓ A θ emb c) = -1) ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
            aeval (R16Used.frobMat ℓ A θ b σ)
              (R16Used.esPoly ℓ (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)
                (c * (p : coeffField f))) = 0

/-- **The weak-reading leaf over every Jacobian of `X₁(N)`** (`IsJ1`). -/
def AfTateWeakOdd : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J → AfTateWeakOddAt N χ f J

/-- **R16 from the weak-reading leaf (glue, proved).** -/
theorem r16_of_weakOdd (h : AfTateWeakOdd) (hT : PkgI3.TateModuleFree) :
    LeafModCurves.R16_EichlerShimuraJ1' := by
  intro N χ f J hN hf hJ
  obtain ⟨A, π, θ, hπ, hb⟩ := h N χ f J hN hf hJ
  have hfin : FiniteDimensional ℚ (coeffField f) := by
    obtain ⟨b, -⟩ := hb 2
    obtain ⟨hfree, hfinT, -⟩ := hT ℚ A 2 (by norm_num)
    have := hfree; have := hfinT
    exact R16Used.finiteDimensional_of_basis (R16Split.rhoV 2 A θ) b
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
      Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : PkgI4.GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p) := by
    intro ℓ _ emb
    obtain ⟨b, hodd, hweak⟩ := hb ℓ
    obtain ⟨h2, -⟩ := R16Used.iota_component ℓ A θ b emb
    refine ⟨h2, fun p hp hpN σ hσ => ?_⟩
    obtain ⟨c, hc, -⟩ := hweak p hp hpN σ hσ
    have hodd' : ∀ c : ZInQ.Contrib.G9.PkgI4.GQ, ZInQ.Contrib.G9.PkgI4.IsComplexConj c →
        (compMat ℓ A θ b emb c).det = -1 := fun c hc =>
      (trace_det_frobOn ℓ A θ b emb c).2.symm.trans (hodd emb c hc)
    have hcp := component_charpoly ℓ A hT (coeffField f) θ b emb N hN χ
      (fun p => ⟨PkgI4.coeff f p, coeff_mem_coeffField f p⟩) hodd' hweak p hp hpN σ hσ c hc
    obtain ⟨htr, hdet⟩ := R16Used.trace_det_of_charpoly _ _ _ hcp
    obtain ⟨htr', hdet'⟩ := trace_det_frobOn ℓ A θ b emb σ
    refine ⟨fun a ha => ?_, fun c' hc' => ?_⟩
    · have : a = ⟨PkgI4.coeff f p, coeff_mem_coeffField f p⟩ := Subtype.ext ha
      rw [htr', htr, this]
    · have : c' = c := Subtype.ext (hc'.trans hc.symm)
      rw [hdet', hdet, this, map_mul, map_natCast]
  refine ⟨hfin, A, π, θ, hπ, ?_, key⟩
  exact R16Split.dim_eq_of_rank_two hT A θ (fun emb => (key 2 emb).1)

/-- **The field `r16CoreY` from the weak-reading leaf and the bundle's
`mumfordTorsionAlgClosed`.** -/
theorem r16CoreY_of_weakOdd (h : AfTateWeakOdd) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  R16Split.coreY_of_r16 (r16_of_weakOdd h
    (T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.torsionStructure_of_mumford hM)))

end Leaf

/-! ## 7. The weak-reading leaf is a consequence of the strong-reading leaf `AfTateCharPoly` -/

section Strong

variable (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ)

open scoped MatrixGroups ModularForm
open PkgI4 (CF coeff IsNewform)

/-- For a weight-2 newform with nebentypus `χ`, `χ(−1) = 1` (`−1 ∈ Γ₀(N)` acts trivially in even
weight, and `f ≠ 0`). -/
theorem chi_neg_one_of_newform {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2}
    (hf : IsNewform f χ) : χ (-1) = 1 := by
  obtain ⟨⟨hneb, h1, -⟩, -⟩ := hf
  have hmem : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp
  have h := hneb (-1) hmem
  have hd : ((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = -1 := by simp
  rw [hd] at h
  by_contra hχ
  have hz : (⇑f : UpperHalfPlane → ℂ) = 0 := by
    funext τ
    have e := congrFun h τ
    rw [ModularForm.SL_slash_apply] at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    have hden : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -1 := by
      simp [UpperHalfPlane.denom]
    have hact : ((-1 : SL(2, ℤ)) • τ) = τ := by
      rw [ModularGroup.SL_neg_smul, one_smul]
    rw [hact] at e
    rw [show UpperHalfPlane.denom (-1 : SL(2, ℤ)) τ = -1 from hden] at e
    have e2 : (1 - χ (-1)) * f τ = 0 := by
      have : ((-1 : ℂ) ^ (-(2 : ℤ))) = 1 := by norm_num
      rw [this, mul_one] at e
      linear_combination e
    exact (mul_eq_zero.mp e2).resolve_left (sub_ne_zero.mpr (Ne.symm hχ))
  have : PkgI4.coeff f 1 = 0 := by
    simp only [PkgI4.coeff]
    rw [hz, UpperHalfPlane.qExpansion_zero]
    simp
  rw [this] at h1
  exact zero_ne_one h1

open ZInQ.Contrib.G9.PkgI4 in
/-- Complex conjugation inverts roots of unity. -/
theorem complexConj_rootOfUnity {c : GQ} (hc : IsComplexConj c) {ζ : Qbar} {m : ℕ} (hm : m ≠ 0)
    (hζ : ζ ^ m = 1) : c ζ = ζ⁻¹ := by
  obtain ⟨ι, hι⟩ := hc
  apply ι.toRingHom.injective
  change ι (c ζ) = ι ζ⁻¹
  rw [hι, map_inv₀]
  have hn : ‖ι ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) hm
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem pow_neg_one_val {M : Type*} [Group M] {t : M} {n : ℕ} [NeZero n] (ht : t ^ n = 1) :
    t ^ ((-1 : ZMod n)).val = t⁻¹ := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by have := NeZero.ne n; omega
    subst hn1
    have : t = 1 := by simpa using ht
    simp [this]
  · have : Fact (1 < n) := ⟨by omega⟩
    have hv : ((-1 : ZMod n)).val = n - 1 := by
      rw [ZMod.neg_val, ite_eq_right_iff.mpr (fun h => absurd h one_ne_zero), ZMod.val_one]
    rw [hv, eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (by omega), ht]

open ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit in
theorem cycQ_complexConj {ℓ : ℕ} [Fact ℓ.Prime] {c : GQ} (hc : IsComplexConj c) :
    ((G0Galois.cycQ ℓ c : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = -1 := by
  have hcy : ((cyclotomicCharacter Qbar ℓ c.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = -1 := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, map_neg, map_one]
    have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
    have : NeZero (ℓ ^ n) := ⟨hl⟩
    refine (modularCyclotomicCharacter.unique Qbar _ c.toRingEquiv fun t ht => ?_).symm
    have htn : t ^ (ℓ ^ n) = 1 := (mem_rootsOfUnity _ _).mp ht
    have htn' : (t : Qbar) ^ (ℓ ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, htn, Units.val_one]
    change c (t : Qbar) = ((t ^ ((-1 : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
    rw [complexConj_rootOfUnity hc hl htn', pow_neg_one_val htn, Units.val_inv_eq_inv_val]
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ c.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [hcy]
  simp

open ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit in
theorem eps0_complexConj {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ (-1) = 1) {c : GQ}
    (hc : IsComplexConj c) :
    ((eps0 ιC ιL χ c : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = 1 := by
  obtain ⟨γ, hγ, hval⟩ := chiL_spec ιC ιL χ (modCycQ c)
  have hm : ((modCycQ (N := N) c : (ZMod N)ˣ) : ZMod N) = -1 := by
    refine (modularCyclotomicCharacter.unique Qbar _ c.toRingEquiv fun t ht => ?_).symm
    have htn : t ^ N = 1 := (mem_rootsOfUnity _ _).mp ht
    have htn' : (t : Qbar) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, htn, Units.val_one]
    change c (t : Qbar) = ((t ^ ((-1 : ZMod N)).val : Qbarˣ) : Qbar)
    rw [complexConj_rootOfUnity hc (NeZero.ne N) htn', pow_neg_one_val htn,
      Units.val_inv_eq_inv_val]
  rw [hm, hχ] at hγ
  have hγ1 : γ = 1 := ιC.toRingHom.injective (by rw [map_one]; exact hγ)
  change ((chiL ιC ιL χ (modCycQ c) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = 1
  rw [hval, hγ1, map_one]

open ZInQ.Contrib.HodgeSplit in
/-- **Oddness from the characteristic-polynomial reading (glue).** If every arithmetic Frobenius
at `p ∤ Nℓ` has characteristic polynomial `X² − a_p X + χ(p)p` over `ℚ_ℓ ⊗ F` and `χ(−1) = 1`,
then complex conjugation has determinant `−1` on every `ι`-component: the determinant is the
character `ε₀ χ_ℓ` (Chebotarev, T18), which is `χ(−1) · (−1) = −1` at complex conjugation. -/
theorem odd_of_charpoly (hT : TateModuleFree) (Fd : IntermediateField ℚ ℂ) (θ : Fd →+* A.End0)
    (b : letI := R16Used.tensorModule ℓ A θ; Module.Basis (Fin 2) (ℚ_[ℓ] ⊗[ℚ] Fd) (A.V ℓ))
    (emb : Fd →+* PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (a : ℕ → Fd)
    (hχ : χ (-1) = 1)
    (hstrong : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : PkgI4.GQ, IsFrobAt σ p →
      ∃ c : Fd, (c : ℂ) = χ (p : ZMod N) ∧
        (R16Used.frobMat ℓ A θ b σ).charpoly = R16Used.esPoly ℓ (a p) (c * (p : Fd))) :
    ∀ c : ZInQ.Contrib.G9.PkgI4.GQ, ZInQ.Contrib.G9.PkgI4.IsComplexConj c →
      (compMat ℓ A θ b emb c).det = -1 := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ιC⟩ : Nonempty (ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  obtain ⟨ιL, hιL⟩ := exists_iotaL ℓ Fd emb ιC
  set M := compMat ℓ A θ b emb with hM
  let Fc : PkgI4.GQ → PadicAlgCl ℓ := fun σ =>
    ((eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) *
      ((G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)
  have hFc : Continuous Fc :=
    (Units.continuous_val.comp (eps0_continuous ιC ιL χ)).mul
      (Units.continuous_val.comp (continuous_cycQ ℓ))
  have hMc : ∀ i j, Continuous fun σ => M σ i j := continuous_compMat_entry ℓ A θ hT b emb
  let D : PkgI4.GQ → PadicAlgCl ℓ := fun σ => (M σ).det
  have hDc : Continuous D := by
    have : D = fun σ => M σ 0 0 * M σ 1 1 - M σ 0 1 * M σ 1 0 := by
      funext σ; exact Matrix.det_fin_two _
    rw [this]
    exact ((hMc 0 0).mul (hMc 1 1)).sub ((hMc 0 1).mul (hMc 1 0))
  have hDF : ∀ σ ∈ (Set.univ : Set PkgI4.GQ), D σ = Fc σ := by
    refine DS965Weak.eq_on_open_of_eq_on_arithFrob (N * ℓ).primeFactors D Fc hDc hFc _
      isOpen_univ ?_
    intro p hp hpS v τ hv hτ _
    have hpN : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr
      ⟨hp, h, Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero⟩)
    have hτ' : IsFrobAt τ p := isFrobAt_of_isArithFrob τ v p hp hv hτ
    obtain ⟨c, hc, hcp⟩ := hstrong p hp hpN τ hτ'
    have hcp' : (M τ).charpoly =
        Polynomial.X ^ 2 - C (emb (a p)) * Polynomial.X + C (emb (c * (p : Fd))) := by
      rw [hM, compMat, Matrix.charpoly_map, hcp, esPoly_map]
    obtain ⟨-, hdet⟩ := R16Used.trace_det_of_charpoly _ _ _ hcp'
    have hpN' : ¬ p ∣ N := fun h => hpN (dvd_mul_of_dvd_left h ℓ)
    have hpl : p ≠ ℓ := by rintro rfl; exact hpN (dvd_mul_left p N)
    obtain ⟨γ, hγ, he⟩ := eps0_frobAt ιC ιL χ hp hpN' hτ'
    change (M τ).det = _ * _
    rw [hdet, he, cycQ_frobAt hp hpl hτ', hιL γ c (hc.trans hγ.symm), map_mul, map_natCast]
  intro c hc
  have h := hDF c (Set.mem_univ _)
  change (M c).det = -1
  change (M c).det = _ at h
  rw [h]
  change ((eps0 ιC ιL χ c : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) *
      ((G0Galois.cycQ ℓ c : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = -1
  rw [eps0_complexConj ιC ιL χ hχ hc, cycQ_complexConj hc, one_mul]

/-- **The weak-reading leaf is never stronger than `AfTateCharPoly` (glue, proved).** The weak
relation is Cayley–Hamilton; oddness follows from the characteristic polynomials at Frobenius by
`odd_of_charpoly` and `χ(−1) = 1`. -/
theorem weakOdd_of_afTate (h : R16Used.AfTateCharPoly) (hT : TateModuleFree) : AfTateWeakOdd := by
  intro N χ f J hN hf hJ
  obtain ⟨A, π, θ, hπ, hb⟩ := h N χ f J hN hf hJ
  refine ⟨A, π, θ, hπ, fun ℓ _ => ?_⟩
  obtain ⟨b, hcp⟩ := hb ℓ
  refine ⟨b, fun emb c hc => ?_, fun p hp hpN σ hσ => ?_⟩
  · rw [(trace_det_frobOn ℓ A θ b emb c).2]
    exact odd_of_charpoly ℓ A hT (coeffField f) θ b emb N hN χ
      (fun p => ⟨PkgI4.coeff f p, coeff_mem_coeffField f p⟩) (chi_neg_one_of_newform hf) hcp c hc
  · obtain ⟨c, hc, hch⟩ := hcp p hp hpN σ hσ
    exact ⟨c, hc, by rw [← hch]; exact Matrix.aeval_self_charpoly _⟩

end Strong


end WeakPart

/-! ## Final: the leaf over `Pic⁰` of one model under the weak reading, and the discharge -/

section Final

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (CF IsNewform)

/-- The weak-reading conclusion is invariant under isomorphism of `J` (glue). -/
theorem AfTateWeakOddAt.of_iso {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J J' : AbVar ℚ}
    (h : AfTateWeakOddAt N χ f J) (e : AbVarIso J J') : AfTateWeakOddAt N χ f J' := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := h
  obtain ⟨e, he⟩ := e
  refine ⟨A, Hom.mk' (e.inv ≫ π.hom), θ, ?_, hrest⟩
  rw [Hom.hom_mk', Over.comp_left]
  have : AlgebraicGeometry.Surjective π.hom.left := hπ
  infer_instance

/-- **LEAF (Eichler–Shimura for `A_f` over `J₁(N) = Pic⁰(X₁(N))`, weakest reading of
Diamond–Shurman 9.5.4, with oddness).** For `N ≥ 1` and a newform `f ∈ S₂(Γ₁(N))` with nebentypus
`χ`, there is a model `X` of `X₁(N)` over `ℚ` (`IsX1Model`) such that for the degree-zero Picard
scheme `J₁(N) = Pic⁰_{X/ℚ}` (some representing abelian variety `V` with the tensor group law) there are
a quotient `π : J₁(N) ↠ A` over `ℚ` and `θ : K_f → End⁰(A)` with, for every prime `ℓ`: `V_ℓ(A)` free
of rank 2 over `ℚ_ℓ ⊗ K_f` (Diamond–Shurman Lemma 9.5.3); complex conjugation of determinant `−1` on
every `ι`-component (`ρ_{A_f,ℓ}` odd); and every arithmetic Frobenius at `p ∤ Nℓ` satisfying
`X² − a_p X + χ(p) p` over `ℚ_ℓ ⊗ K_f` (Diamond–Shurman Thm 9.5.4, weakest reading). The witness is
Diamond–Shurman's `X₁(N)_alg`, `J₁(N) = Pic⁰`, `A = A_f`. Locators UNVERIFIED. -/
def AfTateWeakOddPicZero : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ X : Over SpecQ, IsX1Model N X ∧
      ∃ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep ∧ AfTateWeakOddAt N χ f (ofVendored V)

/-- **`AfTateWeakOdd` from its `Pic⁰` form over one model (glue).** -/
theorem weakOdd_of_picZero (h : AfTateWeakOddPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) : AfTateWeakOdd := by
  intro N χ f J hN hf hJ
  obtain ⟨X₀, ⟨hXc₀, hXi₀, P₀', hP₀', ⟨eX₀⟩⟩, V, rep, htc, hA⟩ := h N χ f hN hf
  obtain ⟨X, P₀, aj, ⟨hXc, hXi, P, hP, ⟨eX⟩⟩, hJac⟩ := hJ
  obtain ⟨σ, hσ⟩ := hI N P₀' P hN hP₀' hP
  obtain ⟨e⟩ := @hC X₀ X hXi₀ hXi hXc₀ hXc ⟨(eX₀.trans (fieldX1Equiv σ hσ)).trans eX.symm⟩
  exact hA.of_iso
    (abVarIso_picZero_of_isJacobian hXc₀ (IsJacobian.of_iso e hJac) V rep htc).symm

/-- **The discharge of `r16CoreY` (glue, proved).** From the weak-reading leaf over `Pic⁰` of one model,
the two dictionary leaves, and the bundle's published leaf `mumfordTorsionAlgClosed`. -/
theorem r16CoreY_of_dict (h : AfTateWeakOddPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  r16CoreY_of_weakOdd (weakOdd_of_picZero h hI hC) hM

/-- The same discharge under the strong reading (r16-used's leaf, over `Pic⁰` of one model). -/
theorem r16CoreY_of_picZero (h : AfTateCharPolyPicZero) (hI : X1PointsConjugate)
    (hC : CurveIsoOfFunctionFieldIso) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  R16Used.r16CoreY_of_printed (afTateCharPoly_of_picZero h hI hC) hM

/-- **The new leaf is never stronger than r16-used's `AfTateCharPoly`** (given the existence of a
pointed model, the bundle's `X1ModelExists`, and `T_ℓ` free, from `mumfordTorsionAlgClosed`). -/
theorem weakOddPicZero_of_afTate (h : R16Used.AfTateCharPoly) (hT : PkgI3.TateModuleFree)
    (hx : LeafModCurves.X1ModelExists) : AfTateWeakOddPicZero := by
  intro N χ f hN hf
  obtain ⟨X, P₀, hX⟩ := hx N hN
  obtain ⟨V, rep, htc⟩ := exists_picZero X hX.1
  refine ⟨X, hX, V, rep, htc, ?_⟩
  obtain ⟨aj, hJ⟩ := isJacobian_picZero X hX.1 V rep htc P₀
  exact weakOdd_of_afTate h hT N χ f (ofVendored V) hN hf ⟨X, P₀, aj, hX, hJ⟩

/-- **Uniqueness of `J₁(N)` from Igusa alone** (the curve leaf is proved). -/
theorem abVarIso_of_isJ1' (hI : X1PointsConjugate) {N : ℕ} (hN : 0 < N) {J J' : AbVar ℚ}
    (h : IsJ1 N J) (h' : IsJ1 N J') : AbVarIso J J' :=
  abVarIso_of_isJ1 hI curveIsoOfFunctionFieldIso_proof hN h h'

/-- **The discharge of `r16CoreY`** from the `Pic⁰` form of r16-used's leaf, Igusa's theorem, and the
bundle's `mumfordTorsionAlgClosed` (the curve leaf is proved, `curveIsoOfFunctionFieldIso_proof`). -/
theorem r16CoreY_of_picZero_igusa (h : AfTateCharPolyPicZero) (hI : X1PointsConjugate)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY :=
  r16CoreY_of_picZero h hI curveIsoOfFunctionFieldIso_proof hM

/-- The same under the weak reading of DS 9.5.4 (with oddness). -/
theorem r16CoreY_of_weakPicZero_igusa (h : AfTateWeakOddPicZero) (hI : X1PointsConjugate)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY :=
  r16CoreY_of_dict h hI curveIsoOfFunctionFieldIso_proof hM

end Final

end R16IsJ1Dict
