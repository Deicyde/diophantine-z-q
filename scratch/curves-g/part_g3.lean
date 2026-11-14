
/-! ## curves-g (part g3): T38's point clause proved, T38 and T34 split; leaf-fold3's bundle refolded -/

namespace HDec

namespace CurvesG3

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory LeafModCurves X1Belyi

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory LeafModCurves X1Belyi

/-- Any two morphisms to `Spec ℚ` agree. -/
theorem hom_to_specQ_ext {S : Scheme} (f g : S ⟶ SpecQ) : f = g :=
  ext_to_Spec (CommRingCat.hom_ext (Subsingleton.elim _ _))

section residue

variable {F : Type} [Field F] (r : ℚ →+* F) (w : ValuationSubring F)
  (hw : ∀ c : ℚ, r c ∈ w)

/-- `ℚ → w`. -/
def ratToW : ℚ →+* w := r.codRestrict w.toSubring hw

/-- `ℚ → κ(w)`. -/
def ratToResidue : ℚ →+* IsLocalRing.ResidueField w :=
  (IsLocalRing.residue w).comp (ratToW r w hw)

theorem ratToResidue_bijective (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) :
    Function.Bijective (ratToResidue r w hw) := by
  refine ⟨(ratToResidue r w hw).injective, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hres x x.2
  refine ⟨c, ?_⟩
  show IsLocalRing.residue w (ratToW r w hw c) = IsLocalRing.residue w x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have h : x - ratToW r w hw c ∈ IsLocalRing.maximalIdeal w :=
    ValuationSubring.coe_mem_nonunits_iff.mp hc
  rw [← neg_sub]
  exact neg_mem h

/-- The residue map `w → κ(w) ≅ ℚ` of a place of degree one. -/
def residueToRat (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) : w →+* ℚ :=
  (RingEquiv.ofBijective _ (ratToResidue_bijective r w hw hres)).symm.toRingHom.comp
    (IsLocalRing.residue w)

end residue

/-- **Glue (proved).** Let `X` be a proper integral scheme over `ℚ`, `F` a field isomorphic to its
function field, and `w` a valuation subring of `F` containing `ℚ` with residue field `ℚ` (every
element of `w` is congruent to a rational modulo `𝔪_w`). Then `X` has a `ℚ`-point: the valuative
criterion lifts `Spec F → X` to `Spec w → X`, and the closed point `Spec ℚ = Spec κ(w) → Spec w`
gives the point. -/
theorem nonempty_ratPt_of_place (X : Over SpecQ) [IsProper X.hom] [IsIntegral X.left]
    {F : Type} [Field F] (e : X.left.functionField ≃+* F) (r : ℚ →+* F)
    (w : ValuationSubring F) (hw : ∀ c : ℚ, r c ∈ w)
    (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) : Nonempty (RatPt X) := by
  let i₁ : Spec (CommRingCat.of F) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.left.fromSpecStalk (genericPoint X.left)
  let i₂ : Spec (CommRingCat.of w) ⟶ SpecQ := Spec.map (CommRingCat.ofHom (ratToW r w hw))
  let S : ValuativeCommSq X.hom :=
    { R := w, K := F, i₁ := i₁, i₂ := i₂, commSq := ⟨hom_to_specQ_ext _ _⟩ }
  have hUC : UniversallyClosed X.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hUC
  obtain ⟨l⟩ := (hUC.1 S).exists_lift
  let pt : SpecQ ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (residueToRat r w hw hres)) ≫ l.l
  exact ⟨Over.homMk pt (hom_to_specQ_ext _ _)⟩

/-- **T38 without the point clause** (published; the leaf `X1Belyi.CurveOfFunctionFieldQ` minus
its clause "`X` has a `ℚ`-point when `F` has a place of degree 1", which is proved here). Let `F`
be a finite extension of `ℚ(T)` in which `ℚ` is algebraically closed. Then there is a smooth
proper geometrically connected integral curve `X` over `ℚ` with function field `F`. Source:
the Stacks Project, *Algebraic Curves*, section "Curves and function fields" (Tag 0BXX,
UNVERIFIED tag: a finitely generated field extension of transcendence degree 1 is the function
field of a normal projective curve, unique up to isomorphism); normal of dimension 1 over a
perfect field implies smooth (Stacks 0B8X, UNVERIFIED); `H⁰(X, 𝒪_X)` is the algebraic closure of
`ℚ` in `F` and proper with `H⁰ = k` implies geometrically connected (Stacks 0BUG, UNVERIFIED);
Hartshorne I.6.7-6.12, II.6.7 over an algebraically closed field (UNVERIFIED numbers). -/
def CurveOfFunctionFieldQNoPoint : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
    ∃ X : Over SpecQ, IsCurve X ∧ ∃ (_ : IsIntegral X.left), Nonempty (X.left.functionField ≃+* F)

/-- **Reduction (proved): T38 from its point-free form.** -/
theorem curveOfFunctionFieldQ_of_noPoint (h : CurveOfFunctionFieldQNoPoint) :
    CurveOfFunctionFieldQ := by
  intro F _ _ _ hF
  obtain ⟨X, hX, hI, ⟨e⟩⟩ := h F hF
  refine ⟨X, hX, ?_, hI, ⟨e⟩⟩
  rintro ⟨w, -, hw, hres⟩
  have := hX.proper
  exact nonempty_ratPt_of_place X e (ratHom F) w hw hres



open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi

/-- A scheme is normal: every stalk is an integrally closed domain (Mathlib has no normal schemes;
for an integral scheme the stalks are domains, so this is the usual notion, Stacks 033H). -/
def IsNormalScheme (X : Scheme) : Prop := ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/-- **Leaf (A): the normal model of a function field.** A finite extension `F` of `ℚ(T)` is the
function field of a normal proper integral scheme `X` of dimension 1 over `ℚ`. Published: the
normalization of `ℙ¹_ℚ` in `F` (finite over `ℙ¹_ℚ` because `F/ℚ(T)` is separable and finite);
Stacks Project, *Algebraic Curves*, section "Curves and function fields" (Tag 0BXX, UNVERIFIED tag);
Hartshorne I.6.7-6.9 and II.6.7 (UNVERIFIED numbers). -/
def NormalModelOfFunctionFieldQ : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ∃ X : Over SpecQ, IsProper X.hom ∧ ∃ (_ : IsIntegral X.left), IsNormalScheme X.left ∧
      topologicalKrullDim X.left = 1 ∧ Nonempty (X.left.functionField ≃+* F)

/-- **Leaf (B): normal curves in characteristic 0 are smooth.** A normal integral scheme of dimension
1, locally of finite type over `ℚ`, is smooth of relative dimension 1 over `ℚ`. Published: its local
rings at closed points are one-dimensional normal noetherian local domains, i.e. discrete valuation
rings (Atiyah–Macdonald Prop. 9.2), so it is regular; a regular scheme locally of finite type over a
perfect field is smooth, of relative dimension the local dimension (Stacks Tag 00TV / Lemma 0B8X for
curves, UNVERIFIED tags). -/
def NormalCurveSmoothQ : Prop :=
  ∀ (X : Over SpecQ), LocallyOfFiniteType X.hom → ∀ (_ : IsIntegral X.left), IsNormalScheme X.left →
    topologicalKrullDim X.left = 1 → SmoothOfRelativeDimension 1 X.hom

/-- **Leaf (C): constant field `ℚ` gives geometric connectedness.** A normal proper integral scheme
`X` over `ℚ` whose function field is isomorphic to a field `F ⊇ ℚ(T)` in which `ℚ` is algebraically
closed is geometrically connected over `ℚ`. Published: `Γ(X, 𝒪_X)` is a finite `ℚ`-algebra and a
domain inside the function field, hence a field algebraic over `ℚ`, hence `ℚ`; a proper scheme over
a field `k` with `Γ(X, 𝒪_X) = k` is geometrically connected (Stacks Tag 0FD1, UNVERIFIED tag; EGA III
4.3.4 via Stein factorization). -/
def GeomConnectedOfConstantFieldQ : Prop :=
  ∀ (X : Over SpecQ), IsProper X.hom → ∀ (_ : IsIntegral X.left), IsNormalScheme X.left →
    ∀ (F : Type) [Field F] [Algebra Qj F], ConstantFieldIsQ F →
      Nonempty (X.left.functionField ≃+* F) → GeometricallyConnected X.hom

/-- **Reduction (proved): T38 without its point clause from (A), (B), (C).** -/
theorem curveOfFunctionFieldQNoPoint_of_split (hA : NormalModelOfFunctionFieldQ)
    (hB : NormalCurveSmoothQ) (hC : GeomConnectedOfConstantFieldQ) :
    CurveOfFunctionFieldQNoPoint := by
  intro F _ _ _ hF
  obtain ⟨X, hP, hI, hN, hd, he⟩ := hA F
  have : IsProper X.hom := hP
  have hS := hB X (by infer_instance) hI hN hd
  have hG := hC X hP hI hN F hF he
  exact ⟨X, ⟨hP, hS, hG⟩, hI, he⟩

/-- **Reduction (proved): T38 (`X1Belyi.CurveOfFunctionFieldQ`) from (A), (B), (C).** -/
theorem curveOfFunctionFieldQ_of_split (hA : NormalModelOfFunctionFieldQ)
    (hB : NormalCurveSmoothQ) (hC : GeomConnectedOfConstantFieldQ) :
    CurveOfFunctionFieldQ :=
  curveOfFunctionFieldQ_of_noPoint (curveOfFunctionFieldQNoPoint_of_split hA hB hC)



open AlgebraicGeometry CategoryTheory LeafModCurves

/-- The differentials of `F/ℚ` regular at the place `w`: the additive subgroup of `Ω_{F/ℚ}`
generated by the `a · db` with `a, b ∈ w` (the image of `Ω_{w/ℚ}`). -/
def regularAt (F : Type) [Field F] [Algebra ℚ F] (w : ValuationSubring F) :
    AddSubgroup (Ω[F⁄ℚ]) :=
  AddSubgroup.closure {ω | ∃ a b : F, a ∈ w ∧ b ∈ w ∧ ω = a • KaehlerDifferential.D ℚ F b}

/-- The holomorphic differentials of `F/ℚ`: the `ℚ`-span of the differentials regular at every
place of `F/ℚ` (every valuation subring of `F` containing `ℚ`). For the function field of a
smooth proper curve `X/ℚ` this is `H⁰(X, Ω¹_{X/ℚ})` (the set is already a `ℚ`-subspace; the span
only packages it). -/
def holoDiff (F : Type) [Field F] [Algebra ℚ F] : Submodule ℚ (Ω[F⁄ℚ]) :=
  Submodule.span ℚ {ω | ∀ w : ValuationSubring F, (∀ c : ℚ, algebraMap ℚ F c ∈ w) →
    ω ∈ regularAt F w}

/-- **The genus of a function field over `ℚ`**: `g(F) = dim_ℚ` of the holomorphic differentials
(Chevalley's definition; for the function field of a smooth proper geometrically connected curve
`X/ℚ`, `g(F) = dim_ℚ H⁰(X, Ω¹) = dim_ℚ H¹(X, 𝒪_X)`, the genus of `X`). -/
def fieldGenus (F : Type) [Field F] [Algebra ℚ F] : ℕ := Module.finrank ℚ (holoDiff F)

/-- **Leaf (T34, first half): the dimension of a Jacobian is the genus.** For a smooth proper
geometrically connected curve `X/ℚ` with a rational point `P₀`, a Jacobian `(J, aj)` of
`(X, P₀)` (Albanese property, `IsJacobian`) and any field `F` isomorphic to the function field of
`X`: `dim J = g(F)`. Published: Milne, *Jacobian varieties* (in Arithmetic Geometry, 1986),
Prop. 2.1 (`T_0 J ≅ H¹(X, 𝒪_X)`, so `dim J = g`) with Thm 1.1 / Prop. 6.1 (the Jacobian is the
Albanese variety), UNVERIFIED numbers; `dim H¹(X, 𝒪_X) = dim H⁰(X, Ω¹)` by Serre duality
(Hartshorne III.7.12, UNVERIFIED); `H⁰(X, Ω¹)` is the space of rational differentials regular at
every closed point, i.e. at every place of `F/ℚ` (Hartshorne II.8, II.6.7, UNVERIFIED). The
published statement specialized to `K = ℚ`. -/
def DimJacobianEqGenus : Prop :=
  ∀ (X : Over SpecQ) (_ : IsCurve X) (P₀ : RatPt X) (J : PkgI3.AbVar ℚ) (aj : X ⟶ J.X),
    IsJacobian X P₀ J aj → ∀ (_ : IsIntegral X.left) (F : Type) [Field F] [Algebra ℚ F],
      Nonempty (X.left.functionField ≃+* F) → J.dim = ((fieldGenus F : ℕ) : WithBot ℕ∞)

/-- **Leaf (T34, second half): the genus of `K_N` is the genus of `Γ₁(N)`.** For `N ≥ 1` and `P`
a point of exact order `N` of `E_j`, the genus of `K_N = ℚ(j)(x(P))` is
`1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` for `Γ₁(N)` (`LeafModCurves.genus`). Published: `K_N` is the
function field of Shimura's canonical model of `X₁(N)` (Shimura 1971 §6.7, leaf MC9 of
bp-modcurves, UNVERIFIED), `X₁(N)_ℂ ≅ Γ₁(N)\ℍ*` and the genus formula for `Γ\ℍ*` (Shimura 1971
Prop. 1.40, UNVERIFIED); the genus is unchanged by the extension of constants `ℚ → ℂ`. (Equivalently:
Riemann–Hurwitz for the Belyi map `j : X₁(N) → ℙ¹`, whose ramification over `0, 1728, ∞` is
given by the `ST`-, `S`- and `T`-orbits on `SL₂(ℤ)/±Γ₁(N)`.) -/
def GenusX1Field : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    ((fieldGenus (fieldX1 P) : ℕ) : ℚ) = genus (CongruenceSubgroup.Gamma1 N)

/-- **Reduction (proved): T34 from its two halves.** -/
theorem dimJ1Genus_of_split (h1 : DimJacobianEqGenus) (h2 : GenusX1Field) : DimJ1Genus := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, h2 N P hN hP⟩


end

end CurvesG3

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-- **leaf-fold3's `OpenTextbookLeaves3` with `t34` and `t38` split** (curves-g). -/
structure OpenTextbookLeavesG : Prop where
  /-- T3 = I2-NMP: Néron mapping property of abelian schemes over a DVR (BLR §1.2 Prop. 8,
  UNVERIFIED locator; kernel `PkgI2.NeronMappingAbelianScheme`). -/
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  /-- T4 = I2-Red: reduction is bijective on prime-to-`p` torsion for good reduction (kernel
  `PkgI2.ReductionTorsionBijective`). -/
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  /-- hom-unify: the analytic representation `Hom(A, B) → {M : MΛ_A ⊆ Λ_B}` (lifting for every
  `K`, bijective over `ℂ`); Birkenhake–Lange §1.2, Mumford §1, §3, GAGA (UNVERIFIED numbers).
  Replaces T11(a) and `HomLinearLift`. -/
  homLatticeCorr : HomUnify.HomLatticeCorr
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  /-- T34, first half (curves-g): `dim Jac X = g(X)`. -/
  t34a : CurvesG3.DimJacobianEqGenus
  /-- T34, second half (curves-g): `g(K_N) = genus Γ₁(N)`. -/
  t34b : CurvesG3.GenusX1Field
  t35 : ZInQ.LeafPush2.UniformizationExists
  /-- T38 (A) (curves-g): the normal proper model of a function field. -/
  t38a : CurvesG3.NormalModelOfFunctionFieldQ
  /-- T38 (B) (curves-g): normal curves over `ℚ` are smooth. -/
  t38b : CurvesG3.NormalCurveSmoothQ
  /-- T38 (C) (curves-g): constant field `ℚ` gives geometric connectedness. -/
  t38c : CurvesG3.GeomConnectedOfConstantFieldQ
  /-- T40 (x1-belyi): `K_N` has a degree-one place (in the kernel: from `X0Transitive`). -/
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

/-- The curves-g bundle gives leaf-fold3's bundle. -/
theorem textbookLeaves3_of_G (t : OpenTextbookLeavesG) : OpenTextbookLeaves3 where
  t3 := t.t3
  t4 := t.t4
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  homLatticeCorr := t.homLatticeCorr
  t11b := t.t11b
  t23 := t.t23
  t24 := t.t24
  t26 := t.t26
  t27 := t.t27
  t33 := t.t33
  t34 := CurvesG3.dimJ1Genus_of_split t.t34a t.t34b
  t35 := t.t35
  t38 := CurvesG3.curveOfFunctionFieldQ_of_split t.t38a t.t38b t.t38c
  t40 := t.t40
  t41 := t.t41

/-- **`SixContactMin` from the curves-g bundle** (leaf-fold3's `sixContactMin_of_open3`). -/
theorem sixContactMin_of_openG (r : OpenResearchLeaves2) (t : OpenTextbookLeavesG)
    (l : OpenAddedLeaves3) (g : OpenGlue3) : ZInQ.SixContactMin :=
  sixContactMin_of_open3 r (textbookLeaves3_of_G t) l g

/-- The proved types are the bundle's field types (the flat file's own `t34`, `t38` Props). -/
example : CurvesG3.CurveOfFunctionFieldQNoPoint → X1Belyi.CurveOfFunctionFieldQ :=
  CurvesG3.curveOfFunctionFieldQ_of_noPoint
example : CurvesG3.NormalModelOfFunctionFieldQ → CurvesG3.NormalCurveSmoothQ →
    CurvesG3.GeomConnectedOfConstantFieldQ → X1Belyi.CurveOfFunctionFieldQ :=
  CurvesG3.curveOfFunctionFieldQ_of_split
example : CurvesG3.DimJacobianEqGenus → CurvesG3.GenusX1Field → LeafModCurves.DimJ1Genus :=
  CurvesG3.dimJ1Genus_of_split

end HSyn

end HDec

example : ∀ (_ : HDec.HSyn.OpenResearchLeaves2) (_ : HDec.HSyn.OpenTextbookLeavesG)
    (_ : HDec.HSyn.OpenAddedLeaves3) (_ : HDec.HSyn.OpenGlue3), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_openG

#print axioms HDec.CurvesG3.nonempty_ratPt_of_place
#print axioms HDec.CurvesG3.curveOfFunctionFieldQ_of_noPoint
#print axioms HDec.CurvesG3.curveOfFunctionFieldQNoPoint_of_split
#print axioms HDec.CurvesG3.curveOfFunctionFieldQ_of_split
#print axioms HDec.CurvesG3.dimJ1Genus_of_split
#print axioms HDec.HSyn.textbookLeaves3_of_G
#print axioms HDec.HSyn.sixContactMin_of_openG
