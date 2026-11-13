import HConj

/-! ## hom-unify: `HomLinearLift` in place of `G10Glue`

* `G0Galois.g10Glue_of_homLinearLift`: g0-assemble's `G10Glue` from T5, T26, T35 and conj-twist's
  leaf `HomLinearLift` (conj-twist's `conjTwistNontrivial_of_leaves`, then g10-odd's reduction
  `g10Glue_of_conjTwist_new` as re-checked by rv-gluepieces2 for g0-assemble's statement).
* `G0Galois.GaloisPiecesHom`: g0-mod-galois' `GaloisPieces` with `odd : G10Glue` replaced by
  `homLift : HomLinearLift`; `G0Galois.galoisPieces_of_hom` gives `GaloisPieces` from it and the
  textbook bundle (fields `t5`, `t26`, `t35`).
* `HSyn.GluePieces3Hom`: linked-tate's `GluePieces3` (29 fields, copied verbatim with their
  docstrings) with `g10Glue` replaced by `homLinearLift`; `HSyn.sixContactMin_of_leaves3Hom`.
* `HomUnify.HomLatticeCorr`: the single proposed leaf (text identical to
  `ZInQKernel/Contrib/HomUnify/Corr.lean`, here over `Leaves.lean`'s copies of `PkgI3.AbVar`, `CPts`,
  `IsUniformization`), and `HomUnify.homLinearLift_of_corr`. -/

section HomUnifyBundleSec

noncomputable section

namespace G0Galois

/-- **g0-assemble's `G10Glue` from T5, T26, T35 and `HomLinearLift` (proved).** conj-twist's
`conjTwistNontrivial_of_leaves` gives `ConjTwistNontrivial`; g10-odd's reduction (rv-gluepieces2,
check c1) gives `G10Glue` in g0-assemble's form (hypotheses `T11a_RiemannEnd`, `T11b_Rigidity`,
`FaltingsTate`). This is conj-twist's `g10Glue_of_leaves` for the assembly's `G10Glue`. -/
theorem g10Glue_of_homLinearLift (h5 : PkgI2.TorsionStructure.{0}) (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : HomLinearLift) : G10Glue :=
  g10Glue_of_conjTwist_new (conjTwistNontrivial_of_leaves h5 hT h35 hN2)

/-- **`GaloisPieces` with `HomLinearLift` in place of `G10Glue`** (hom-unify): Burnside, R14's
determinant clause, `G9Glue`, conj-twist's textbook leaf `HomLinearLift` (T11(a) in `Hom` form),
`G12Weight`, `DetTate`, `ResQFiniteIndex`. -/
structure GaloisPiecesHom : Prop where
  burnside : BurnsideAbsIrred
  r14det : R14Det
  deRham : G9Glue
  homLift : HomLinearLift
  weight : G12Weight
  detTate : DetTate
  finIndex : ResQFiniteIndex

/-- **`GaloisPieces` from `GaloisPiecesHom` and the textbook bundle (proved):** `odd` is
`g10Glue_of_homLinearLift t.t5 t.t26 t.t35`. -/
theorem galoisPieces_of_hom (t : HSyn.TextbookLeaves) (m : GaloisPiecesHom) : GaloisPieces where
  burnside := m.burnside
  r14det := m.r14det
  deRham := m.deRham
  odd := g10Glue_of_homLinearLift t.t5 t.t26 t.t35 m.homLift
  weight := m.weight
  detTate := m.detTate
  finIndex := m.finIndex

end G0Galois

namespace HSyn

open G0Split

/-- **linked-tate's `GluePieces3` with `g10Glue` replaced by `homLinearLift`** (hom-unify). The
other 28 fields and their docstrings are copied verbatim from
`scratch/linked-tate/parts/99_bundle3.lean`. -/
structure GluePieces3Hom : Prop where
  /-- g0-fibresimple, LEAF (textbook; Mumford §4 Application 2, Milne Thm 8.2, UNVERIFIED
  locators): `[n]` is finite and surjective for `n ≠ 0` (characteristic 0). -/
  mulIsogeny : G0FibreSimple.MulIsogeny
  /-- g0-fibresimple, LEAF (textbook; Mumford §4 Cor. 1, Milne Cor. 2.2, UNVERIFIED locators):
  rigidity, a pointed morphism of abelian varieties is a homomorphism. -/
  rigidityHom : G0FibreSimple.RigidityHom
  /-- g0-fibresimple FS1b′, GLUE (EGA IV₂ 2.7.1, UNVERIFIED): `IsFinite` descends along
  `Spec L → Spec K`. -/
  finiteDescends : G0FibreSimple.FiniteDescends
  /-- g0-fibresimple FS5, GLUE, **QM-PIN**: NoCM on the fibre, `End_𝒪(P.A) = ℤ`. -/
  fibreComTrivial : G0FibreSimple.FibreComTrivial
  /-- g0-heightadd (stated in def-faltings), GLUE: uniqueness of analytic uniformizations. -/
  analyticUniformizationUnique : ZInQ.DefFaltings.AnalyticUniformizationUnique
  /-- g0-heightadd, GLUE: two metrizations of one group model have the same dimension. -/
  metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique
  /-- g0-heightadd, GLUE: every group model has a metrization. -/
  metrizationExists : ZInQ.G0HeightAdd.MetrizationExists
  /-- g0-heightadd P2a-geo, GLUE: the product metrization with multiplicative index,
  coefficients and covolumes. -/
  productMetrizationGeo : ZInQ.G0HeightAdd.ProductMetrizationGeo
  /-- g0-stablebc, GLUE (geometric half of h5-neron's H4a): the natural map on `⋀^g ω` under base
  change of group models. -/
  hodgeLineBaseChange : G0StableBC.HodgeLineBaseChange
  /-- g0-thetapoint, GLUE, **QM-PIN**: a uniformization lattice of the fibre is a QM lattice
  `ι(𝒪)(τ,1)ᵀ` with `j_θ(Ω(τ)) = J(u)`. -/
  fibreQMPeriod : G0Split.ThetaPt.FibreQMPeriod
  /-- g0-thetapoint, LEAF candidate (composite of published results: Shimura 1976 / Mumford Tata
  II; UNVERIFIED locators): theta-constant ratios at a period matrix of an abelian surface over a
  number field are algebraic. -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- g0-mod-field G2, GLUE (Prop. TS + Lemma NV on the actual fibre): a separable `f`,
  `deg f ≤ 324`, whose splitting field is unramified outside `T` and carries a rational fibre. -/
  fibreCoverExists : G0ModField.FibreCoverExists
  /-- g0-mod-field G4 + B1, GLUE, **QM-PIN**: the kernel field and the conjugacy data. -/
  kernelFieldExists : G0ModField.KernelFieldExists
  /-- g0-mod-field, GLUE (STANDARD, Neukirch I §8, UNVERIFIED): a compositum of finite Galois
  extensions of `ℚ` unramified at `p` is unramified at `p`. -/
  unramifiedSup : G0ModField.UnramifiedSup
  /-- g0-mod-galois, LEAF (textbook; Burnside, Lang *Algebra* XVII §3, UNVERIFIED locator). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- g0-mod-galois, LEAF: R14 with its published determinant clause (Shimura 1971 Thm 7.14,
  Deligne 1971; UNVERIFIED locators). Used instead of the bundle's `r14` alone, whose statement
  omits the determinant (g0-mod-galois' finding). -/
  r14Det : G0Galois.R14Det
  /-- g0-mod-galois G9, GLUE (N5's de Rham descent lemma, appendix). -/
  g9Glue : G0Galois.G9Glue
  /-- **hom-unify: in place of `g10Glue`.** conj-twist's textbook LEAF N2 (T11(a) in `Hom` form;
  Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1, with holomorphy of algebraic
  morphisms; UNVERIFIED numbers): homomorphisms lift along analytic uniformizations to `ℂ`-linear
  maps. `G10Glue` follows from it and the bundle's T5, T26, T35 (`g10Glue_of_homLinearLift`). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- g0-mod-galois G12, GLUE (Hodge–Tate weight comparison). -/
  g12Weight : G0Galois.G12Weight
  /-- g0-mod-galois, GLUE (from T9): `det V_ℓ(A) = χ_ℓ^{dim A}`. -/
  detTate : G0Galois.DetTate
  /-- g0-mod-newform, GLUE (from Kronecker–Weber): finite-image characters are Dirichlet
  characters at Frobenius. -/
  dirichletOfFinite : G0ModNewform.DirichletOfFinite
  /-- R17 as a concrete statement (kernel `LadicCond.CarayolR17'`), LEAF (Carayol 1986,
  Théorème (A); faithful per the locator audit). The bundle's `r17` is still an `opaque`
  placeholder, unused on this route. -/
  carayolR17 : LadicCond.CarayolR17'
  /-- kernel glue (Serre–Tate §2, Herbrand): the Swan conductor does not depend on the level. -/
  swanIndependent : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)
  /-- kernel glue L8: `Sw = ∫ codim V^{G^u}`. -/
  swanIntegral : LadicCond.SwanIntegral
  /-- kernel glue: an adapted level exists (`ρ(P_p)` finite for `ℓ ≠ p`). -/
  adaptedExists : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)
  /-- linked-tate, GLUE (given the leaf R7a): good reduction at every DVR with `3` a unit makes
  inertia above `p ∉ {3, ℓ}` fix the `ℓ`-power torsion points of base changes (the point-level
  transport half of G3). -/
  goodRedTorsion : LinkedTate.GoodRedTorsion
  /-- linked-tate, GLUE (literature-backed: Mumford §19 Thm 3, Albert's classification): the QM
  model with `EndDivision` has `rank_ℤ End = 4`. -/
  qmEndRank : LinkedTate.QMEndRank
  /-- linked-tate, GLUE (N5 L777-786): `FrobTraceLink` for the canonical operators `tmOf`. -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-tate, GLUE (N5 L819-852, D1-D4): Glazer's wild ramification (`RhoRamWild`) for the
  canonical descended operators, with `γ₀ = β/a` under an embedding `ℚ̄ → ℂ`. -/
  linkedRam : UnramTate.LinkedRam

/-- **`GluePieces3` from `GluePieces3Hom` (proved):** `g10Glue` from the bundle's T5, T26, T35 and
the field `homLinearLift`; every other field is copied. -/
theorem gluePieces3_of_hom (t : TextbookLeaves) (gp : GluePieces3Hom) : GluePieces3 where
  mulIsogeny := gp.mulIsogeny
  rigidityHom := gp.rigidityHom
  finiteDescends := gp.finiteDescends
  fibreComTrivial := gp.fibreComTrivial
  analyticUniformizationUnique := gp.analyticUniformizationUnique
  metrizationDimUnique := gp.metrizationDimUnique
  metrizationExists := gp.metrizationExists
  productMetrizationGeo := gp.productMetrizationGeo
  hodgeLineBaseChange := gp.hodgeLineBaseChange
  fibreQMPeriod := gp.fibreQMPeriod
  thetaRatiosAlgebraic := gp.thetaRatiosAlgebraic
  fibreCoverExists := gp.fibreCoverExists
  kernelFieldExists := gp.kernelFieldExists
  unramifiedSup := gp.unramifiedSup
  burnsideAbsIrred := gp.burnsideAbsIrred
  r14Det := gp.r14Det
  g9Glue := gp.g9Glue
  g10Glue := G0Galois.g10Glue_of_homLinearLift t.t5 t.t26 t.t35 gp.homLinearLift
  g12Weight := gp.g12Weight
  detTate := gp.detTate
  dirichletOfFinite := gp.dirichletOfFinite
  carayolR17 := gp.carayolR17
  swanIndependent := gp.swanIndependent
  swanIntegral := gp.swanIntegral
  adaptedExists := gp.adaptedExists
  goodRedTorsion := gp.goodRedTorsion
  qmEndRank := gp.qmEndRank
  linkedFrob := gp.linkedFrob
  linkedRam := gp.linkedRam

/-- **G0 after hom-unify (end to end):** the leaf bundles and `GluePieces3Hom` imply
`ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves3Hom (r : ResearchLeaves) (t : TextbookLeaves)
    (gp : GluePieces3Hom) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves3 r t (gluePieces3_of_hom t gp)

end HSyn

namespace HomUnify

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- **The analytic representation of homomorphisms (textbook LEAF; the single leaf proposed by
hom-unify for T11(a) in `Hom` form).** Let `A`, `B` be abelian varieties over a field `K`,
`σ : K → ℂ`, and `Φ_A : ℂ^g → A(ℂ)_σ`, `Φ_B : ℂ^h → B(ℂ)_σ` analytic uniformizations with kernels
`Λ_A`, `Λ_B` (`g = dim A`, `h = dim B`).
1. (lifting) every homomorphism `f : A → B` lifts to a `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `Φ_B(Mz) = f(Φ_A(z))`;
2. (realization, over `ℂ`) if `K = ℂ` and `σ = id`, every `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `MΛ_A ⊆ Λ_B` is induced in this way by a unique homomorphism `f : A → B`.

Together: `Hom(A_ℂ, B_ℂ) ≅ {M ∈ Hom_ℂ(ℂ^g, ℂ^h) : MΛ_A ⊆ Λ_B}`, `f ↦ ρ_a(f)`, and for general `K`
the analytic representation of `f` is that of `f_ℂ`. Sources (all UNVERIFIED numbers):
Birkenhake–Lange, *Complex abelian varieties*, §1.2 (Prop. 1.2.1: homomorphisms of complex tori
`ℂ^g/Λ → ℂ^h/Λ'` are exactly the maps induced by `ℂ`-linear `M` with `MΛ ⊆ Λ'`, and the analytic
representation is injective); Mumford, *Abelian varieties*, §1 (the complex torus `A(ℂ)`) and
§3 (`A ↦ A^an` is fully faithful on abelian varieties); Serre, GAGA (1956) / Chow, for
"holomorphic ⇒ algebraic" in 2.; holomorphy of algebraic morphisms for 1. -/
def HomLatticeCorr : Prop :=
  (∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom) ∧
  (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom)

/-- **`HomLinearLift` from `HomLatticeCorr` (proved):** its first clause. -/
theorem homLinearLift_of_corr (h : HomLatticeCorr) : G0Galois.HomLinearLift := h.1

/-- **`G10Glue` from T5, T26, T35 and the single leaf `HomLatticeCorr` (proved).** -/
theorem g10Glue_of_corr (h5 : PkgI2.TorsionStructure.{0}) (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (h : HomLatticeCorr) : G0Galois.G10Glue :=
  G0Galois.g10Glue_of_homLinearLift h5 hT h35 (homLinearLift_of_corr h)

end HomUnify

end

end HomUnifyBundleSec

#print axioms G0Galois.conjTwistNontrivial_of_leaves
#print axioms G0Galois.conjTwistFromLeaves_of_homLinearLift
#print axioms G0Galois.twistCEval
#print axioms G0Galois.g10Glue_of_conjTwist_new
#print axioms G0Galois.g10Glue_of_homLinearLift
#print axioms G0Galois.galoisPieces_of_hom
#print axioms HSyn.gluePieces3_of_hom
#print axioms HSyn.sixContactMin_of_leaves3Hom
#print axioms HomUnify.homLinearLift_of_corr
#print axioms HomUnify.g10Glue_of_corr
