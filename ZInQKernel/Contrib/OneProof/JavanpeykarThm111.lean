import ZInQKernel.Contrib.OneProof.JavanpeykarRebase

/-! # javanpeykar-steps: `javanpeykarPrintedMapHF` as a direct instance of Javanpeykar's Thm 1.1.1

Task javanpeykar-steps (2026-11-17), report `docs/research/javanpeykar-steps.md`, scratch
`scratch/javanpeykar-steps/`.

**Target.** The bundle field `javanpeykarPrintedMapHF : JavanpeykarRebase.JavanpeykarPrintedMap`
(javanpeykar-rebase; kind consequence, GLUE): Javanpeykar's bound read at `X = X₀ ×_K K̄` with `deg_B`
replaced by the degree of one given Belyi map and `h_Fal(Jac X)` by the printed stable height of one model
`V` over `K`.

**Result.** `javanpeykarPrintedMap_of_thm111 : JavanpeykarThm111 → JavanpeykarPrintedMap`, no other
hypothesis, where `JavanpeykarThm111` is Thm 1.1.1 as printed (any smooth projective connected curve over
an algebraic closure of `ℚ`, `deg_B` the least degree of a Belyi morphism, unramified in Mathlib's sense
over `ℙ¹ ∖ {0, 1, ∞}`) together with the identification printed on p. 9 of the same paper:
`h_Fal(X)` is the stable Faltings height of `Jac(X)`, i.e. of any model of `Jac(X)` over a number field.
Steps proved here:
* (1) `X₀ ×_K K̄` is a smooth projective integral curve over `K̄`, an algebraic closure of `ℚ`;
* (2) a Belyi map of degree `d` gives `deg_B ≤ d`, and the bound `13·10⁶ g d⁵` is monotone in `d`;
* (3) `isBelyiMorphism_of_isBelyiMap`: ramification index `1` at the closed points over `ℙ¹ ∖ {0, 1, ∞}`
  (the maximal ideal of `𝒪_{ℙ¹, β x}` generates that of `𝒪_{C, x}`) makes `β` unramified over
  `ℙ¹ ∖ {0, 1, ∞}` (Mathlib's `FormallyUnramified` and `LocallyOfFiniteType` of the restriction);
* (H2) `isPrintedStableHeight_of_iso`: the printed stable height is invariant under isomorphism;
  `V` is a `K`-form of `W` by hypothesis;
* (H3) `isPrintedStableHeight_unique`: two printed stable heights of one abelian variety over a number
  field coincide (given T35, Stacks 04KV, N1 and SS2), so quantifying over every witness is the print's
  single value.

No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace JavanpeykarSteps

open CategoryTheory AlgebraicGeometry Limits
open JavanpeykarDict JavanpeykarFix
open LeafModCurves (IsCurve)
open ZInQ.LeafPush2 (javanpeykarBound)

/-! ## §1. The printed objects -/

/-- **A Belyi morphism of degree `d`, as printed** (Javanpeykar 2014 §1, p. 90: a finite morphism
`X → ℙ¹_ℚ̄` unramified over `ℙ¹ ∖ {0, 1, ∞}`; degree as in Hartshorne II.6.8): `β : C → ℙ¹_k` over `k`,
finite, unramified over `U = ℙ¹ ∖ {0, 1, ∞}` in Mathlib's sense (the restriction `β⁻¹ U → U` is locally of
finite type and formally unramified, EGA IV 17.3.1 / Stacks 02G3), of degree
`d = [k(C) : k(ℙ¹)]`, the rank of `k(C)` over the local ring of `ℙ¹` at the image of the generic point
(which is the generic point of `ℙ¹`, `β` being finite and `C` a curve). -/
def IsBelyiMorphism {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    (β : C.left ⟶ P1 k) (d : ℕ) : Prop :=
  β ≫ P1.toSpec k = C.hom ∧ IsFinite β ∧
  LocallyOfFiniteType (β ∣_ P1.threePointsCompl k) ∧ FormallyUnramified (β ∣_ P1.threePointsCompl k) ∧
  @Module.finrank ((P1 k).presheaf.stalk (β (genericPoint C.left))) C.left.functionField _ _
    (β.stalkMap (genericPoint C.left)).hom.toModule = d

/-- **`deg_B(C)`, the Belyi degree** (Javanpeykar 2014, p. 90): the least degree of a Belyi morphism
`C → ℙ¹_k` (degrees are positive; `IsLeast`, so no value is asserted when `C` has no Belyi morphism). -/
def IsBelyiDegree {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
    (dB : ℕ) : Prop :=
  IsLeast {d : ℕ | 0 < d ∧ ∃ β : C.left ⟶ P1 k, IsBelyiMorphism C β d} dB

/-- The genus `dim_k H¹(C, 𝒪_C)` of a curve `C` over a field `k` (vendored `Scheme.arithmeticGenus`; the
genus of a smooth projective connected curve). -/
def genus {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) : ℕ :=
  letI : C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩
  C.left.arithmeticGenus k

/-- **The stable Faltings height of an abelian variety over `ℚ̄`** (Javanpeykar 2014 §2.3, p. 9 of
arXiv:1403.6404v1, citing Moret-Bailly, *Pinceaux de variétés abéliennes*, Lemme 3.2.1; Faltings 1983 §1):
`h` is the stable height of `W` if it is the printed stable height (height-fix's
`ZInQ.HeightFix.IsPrintedStableHeight`, computed over a field of semistable reduction) of a model `V` of `W`
over some number field `L ⊆ ℚ̄` (`V ×_L ℚ̄ ≅ W`). -/
def IsStableHeightBar {Qbar : Type} [Field Qbar] (W : AbelianVariety Qbar) (h : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Qbar) (V : AbelianVariety L),
    Nonempty ((AbelianVariety.baseChange L Qbar).obj V ≅ W) ∧
      ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) h

/-! ## §2. The leaf -/

/-- **Leaf R18-Javanpeykar, printed form** (A. Javanpeykar, *Polynomial bounds for Arakelov invariants of
Belyi curves*, Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90 (arXiv:1403.6404v1 p. 1), with the
height identification printed in the same paper, p. 98 (arXiv §2.3 p. 9); locators recorded by the
locator audit, docs/research/locators.md row R18). Printed: for a smooth projective connected curve `X`
over `ℚ̄` of genus `g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`; p. 9: `h_Fal(X)` is the stable Faltings
height of the Jacobian of `X`.

In Lean, over any algebraic closure `ℚ̄` of `ℚ` (an algebraically closed field algebraic over `ℚ`):
* `X` smooth of relative dimension `1`, proper and integral over `ℚ̄` (so connected), projective (a closed
  immersion into a projective space over `ℚ̄`);
* `g = dim H¹(X, 𝒪_X) ≥ 1` (`genus`);
* `Jac(X)`: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with the
  tensor-product group law (vendored `picardFunctorDegree`, `PicardTensorCompatible`);
* `h_Fal(X)`: any `h` with `IsStableHeightBar W h` (the printed stable height of a model of `W` over a
  number field; p. 9);
* `deg_B(X)`: any `dB` with `IsBelyiDegree X dB` (least degree of a Belyi morphism). -/
def JavanpeykarThm111 : Prop :=
  ∀ (Qbar : Type) [Field Qbar] [IsAlgClosed Qbar] [CharZero Qbar] [Algebra.IsAlgebraic ℚ Qbar]
    (X : Over (Spec (CommRingCat.of Qbar))) [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
    [IsIntegral X.left],
    (∃ (n : Type) (_ : Finite n) (i : X.left ⟶ ℙ(n; Spec (CommRingCat.of Qbar))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of Qbar)) ↘ Spec (CommRingCat.of Qbar) = X.hom) →
    1 ≤ genus X →
    ∀ (W : AbelianVariety Qbar) (repW : (picardFunctorDegree X.hom 0).obj.RepresentableBy W.group.X),
      PicardTensorCompatible X.hom W.group repW →
    ∀ h : ℝ, IsStableHeightBar W h →
    ∀ dB : ℕ, IsBelyiDegree X dB →
    h ≤ javanpeykarBound (genus X) dB

/-! ## §3. Step (3): ramification index `1` at closed points means unramified -/

section Unramified

variable {k : Type} [Field k] [CharZero k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]

/-- The residue field of a stalk of a `k`-scheme has characteristic `0`. -/
theorem charZero_residueField_stalk (x : C.left) :
    CharZero (IsLocalRing.ResidueField (C.left.presheaf.stalk x)) :=
  charZero_of_injective_ringHom
    ((IsLocalRing.residue (C.left.presheaf.stalk x)).comp (iotaX C x).hom).injective

/-- **Stalkwise unramifiedness at a point over `ℙ¹ ∖ {0, 1, ∞}`.** For a Belyi map in the
ramification-index sense, the stalk map `𝒪_{ℙ¹, β y} → 𝒪_{C, y}` is formally unramified at every
`y` over `ℙ¹ ∖ {0, 1, ∞}`: the residue field extension is finite (`β` is quasi-finite) hence separable
(characteristic `0`), and `𝔪_{β y} 𝒪_{C, y} = 𝔪_y` (the hypothesis at closed points; at the generic point
`𝒪_{C, η} = k(C)` is a field). -/
theorem stalkMap_formallyUnramified {β : C.left ⟶ P1 k} {d : ℕ} (hβ : IsBelyiMap C β d) (y : C.left)
    (hy : β y ∈ P1.threePointsCompl k) : (β.stalkMap y).hom.FormallyUnramified := by
  have hfin : IsFinite β := hβ.2.1
  set R := (P1 k).presheaf.stalk (β y)
  set S := C.left.presheaf.stalk y
  algebraize [(β.stalkMap y).hom]
  have : IsLocalHom (algebraMap R S) := inferInstanceAs <| IsLocalHom (β.stalkMap y).hom
  have : Algebra.EssFiniteType R S := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap β y
  have hqf : Algebra.QuasiFinite R S := β.quasiFiniteAt y
  have : Algebra.QuasiFinite R (IsLocalRing.ResidueField S) :=
    inferInstanceAs (Algebra.QuasiFinite R (S ⧸ IsLocalRing.maximalIdeal S))
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.of_restrictScalars R _ _
  have : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Module.Finite.of_quasiFinite
  have : CharZero (IsLocalRing.ResidueField S) := charZero_residueField_stalk C y
  have : CharZero (IsLocalRing.ResidueField R) :=
    RingHom.charZero (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
  have : Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  refine RingHom.formallyUnramified_algebraMap.mpr (Algebra.FormallyUnramified.of_map_maximalIdeal ?_)
  by_cases hη : y = genericPoint C.left
  · subst hη
    have hS : IsLocalRing.maximalIdeal S = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField C.left.functionField)
    rw [hS, Ideal.map_eq_bot_iff_le_ker]
    intro r hr
    have hnu : algebraMap R S r ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr (map_nonunit (algebraMap R S) r hr)
    rw [hS] at hnu
    exact hnu
  · exact hβ.2.2.1 y (isClosed_of_ne_genericPoint C y hη) hy

/-- **Step (3): a Belyi map in the ramification-index sense is a Belyi morphism as printed.** -/
theorem isBelyiMorphism_of_isBelyiMap {β : C.left ⟶ P1 k} {d : ℕ} (hβ : IsBelyiMap C β d) :
    IsBelyiMorphism C β d := by
  have hfin : IsFinite β := hβ.2.1
  refine ⟨hβ.1, hfin, inferInstance, ?_, hβ.2.2.2⟩
  haveI : (RingHom.toMorphismProperty RingHom.FormallyUnramified).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FormallyUnramified.respectsIso
  refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_
  exact ((RingHom.toMorphismProperty RingHom.FormallyUnramified).arrow_mk_iso_iff
    (morphismRestrictStalkMap β _ x)).mpr
    (stalkMap_formallyUnramified C hβ x.1 x.2)

end Unramified

/-! ## §4. Steps (1), (2): the instance -/

/-- The bound `13·10⁶ · g · d⁵` is monotone in `d`. -/
theorem javanpeykarBound_mono (g : ℕ) {d d' : ℕ} (h : d ≤ d') :
    javanpeykarBound g d ≤ javanpeykarBound g d' := by
  unfold javanpeykarBound
  gcongr

/-- **Step (2): `deg_B` exists and is at most the degree of any Belyi map.** -/
theorem exists_isBelyiDegree_le {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] {β : C.left ⟶ P1 k} {d : ℕ} (hβ : IsBelyiMorphism C β d) (hd : 0 < d) :
    ∃ dB, IsBelyiDegree C dB ∧ dB ≤ d := by
  classical
  have hne : ∃ d, 0 < d ∧ ∃ β : C.left ⟶ P1 k, IsBelyiMorphism C β d := ⟨d, hd, β, hβ⟩
  refine ⟨Nat.find hne, ⟨Nat.find_spec hne, fun e he => Nat.find_min' hne he⟩,
    Nat.find_min' hne ⟨hd, β, hβ⟩⟩

/-- **`javanpeykarPrintedMapHF` is an instance of Javanpeykar's Thm 1.1.1 as printed.** Steps:
(1) `X₀ ×_K K̄` is a smooth proper integral curve over `K̄ = AlgebraicClosure K`, an algebraic closure of
`ℚ`, projective by hypothesis, with `genus = genusBar X₀` (definitionally); (H2) `V` is a model of `W`
over the number field `K`, so its printed height is a stable height of `W`; (3) the Belyi map is a Belyi
morphism as printed; (2) `deg_B ≤ d` and the bound is monotone in the degree. -/
theorem javanpeykarPrintedMap_of_thm111 (hJ : JavanpeykarThm111) :
    JavanpeykarRebase.JavanpeykarPrintedMap := by
  intro K _ _ X _ _ hproj W repW htcW V hVW hg1 β d hβ hd0 x hx
  have hX : IsCurve X := inferInstance
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  -- (1) the curve over `ℚ̄`
  have : IsProper (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (IsProper ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  have : SmoothOfRelativeDimension 1 (baseChangeCurve X (AlgebraicClosure K)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      ((AlgebraicGeometry.baseChange K (AlgebraicClosure K)).obj X).hom)
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  -- (3) the Belyi map is a Belyi morphism; (2) `deg_B ≤ d`
  obtain ⟨dB, hdB, hle⟩ := exists_isBelyiDegree_le _ (isBelyiMorphism_of_isBelyiMap _ hβ) hd0
  -- (H2) the height of the `K`-form `V` is a stable height of `W`
  have hh : IsStableHeightBar W x := ⟨K, inferInstance, inferInstance, inferInstance, V, hVW, hx⟩
  exact (hJ (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)) hproj hg1 W repW htcW x hh
    dB hdB).trans (javanpeykarBound_mono _ hle)

/-! ## §5. (H2), (H3): the height of the leaf is the print's single value -/

section Height

open ZInQ.HeightFix

variable {K : Type} [Field K] {J J' : PkgI3.AbVar K}

/-- The dimension of an abelian variety is invariant under isomorphism. -/
theorem dim_eq_of_iso (e : J.X ≅ J'.X) : J.dim = J'.dim := by
  unfold PkgI3.AbVar.dim
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).isHomeomorph

/-- **(H2) The printed stable height is invariant under isomorphism of abelian varieties (glue,
proved).** A group model of `J_L` is one of `J'_L` through `e_L` (javanpeykar-dict's `transport`, same
scheme over `𝓞_L`), so the Néron property, semistability and the printed metric data carry over. -/
theorem isPrintedStableHeight_of_iso (e : J.X ≅ J'.X) [IsMonHom e.hom] {x : ℝ}
    (h : IsPrintedStableHeight J x) : IsPrintedStableHeight J' x := by
  obtain ⟨L, i1, i2, i3, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r, hr, hx⟩ := h
  exact ⟨L, i1, i2, i3, transport 𝒩 e, g, isNeronModel_transport 𝒩 e hN, hS,
    (dim_eq_of_iso e).symm.trans hdim, eta, hetaM, heta0, hsec, r, hr, hx⟩

/-- **(H2) for the leaf's height**: a stable height of `W` over `ℚ̄` is one of every `W' ≅ W`. -/
theorem isStableHeightBar_of_iso {Qbar : Type} [Field Qbar] {W W' : AbelianVariety Qbar}
    (e : W ≅ W') {h : ℝ} (hW : IsStableHeightBar W h) : IsStableHeightBar W' h := by
  obtain ⟨L, i1, i2, i3, V, ⟨f⟩, hV⟩ := hW
  exact ⟨L, i1, i2, i3, V, ⟨f ≪≫ e⟩, hV⟩

/-- **(H3) The printed stable height has one value** (given T35, Stacks 04KV, N1 and SS2): two witnesses
of `IsPrintedStableHeight A` coincide, since both are kernel stable heights
(`ZInQ.HeightFix.isStableFaltingsHeight_of_printed`) and the published stable height does not depend on
the field of semistable reduction (`ZInQ.HeightSplit.isStableFaltingsHeight_unique`). So the leaf's
`∀ x, IsPrintedStableHeight (ofVendored V) x → …` asserts the bound for the print's single value only. -/
theorem isPrintedStableHeight_unique (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hGC : AVGlue.GeomConnOfRationalPoint) (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS2 : ZInQ.HeightSplit.SemistableNeronBaseChange) [NumberField K] {A : PkgI3.AbVar K} {x y : ℝ}
    (hx : IsPrintedStableHeight A x) (hy : IsPrintedStableHeight A y) : x = y :=
  ZInQ.HeightSplit.isStableFaltingsHeight_unique hN1 hSS2
    (isStableFaltingsHeight_of_printed hT35 hGC hx) (isStableFaltingsHeight_of_printed hT35 hGC hy)

end Height

end JavanpeykarSteps
