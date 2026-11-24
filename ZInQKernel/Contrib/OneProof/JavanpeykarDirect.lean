import ZInQKernel.Contrib.OneProof.JavanpeykarRebase

/-! # javanpeykar-direct: Javanpeykar 2014 Thm 1.1.1 over the print's objects

Task javanpeykar-direct (2026-11-17), report `docs/research/javanpeykar-direct.md`, scratch
`scratch/javanpeykar-direct/`. Base `wip/leaf-fold33b` fe2f0d4a.

**Target.** The research field `javanpeykarPrintedMapHF : JavanpeykarRebase.JavanpeykarPrintedMap`
(javanpeykar-rebase; kinds row consequence / GLUE, "pending reading"). Its recorded reading gap has two
theorem steps between the print and the Lean statement:
(i) `deg_B(X)` (the least degree of a Belyi map) is replaced by the degree `d` of a given Belyi map;
(ii) `h_Fal(Jac X)` (the stable Faltings height of the Jacobian of `X/ℚ̄`) is replaced by the printed stable
height of a model `V` over the number field `K` over which `X = X₀ ×_K ℚ̄` is defined.

**Result.** `JavanpeykarThm111` states the print over its own objects:
* `X` is any smooth proper connected curve over any algebraic closure `ℚ̄` of `ℚ`, integral, projective;
* `deg_B(X) = belyiDegree X hB`, the least `d > 0` with a Belyi map `X → ℙ¹` of degree `d` (`Nat.find`;
  the hypothesis `hB` that some Belyi map exists replaces Belyi's theorem);
* `h_Fal(Jac X)`: `IsStableHeightBar W x`, the stable Faltings height of the abelian variety `W` over `ℚ̄`
  is the printed stable height (height-fix's `IsPrintedStableHeight`) of a model of `W` over a number field
  `L ⊆ ℚ̄` (Faltings' definition of the stable height of an abelian variety over `ℚ̄`);
* `g = genusK X = dim_ℚ̄ H¹(X, 𝒪_X)`.

`javanpeykarPrintedMap_of_thm111 : JavanpeykarThm111 → JavanpeykarRebase.JavanpeykarPrintedMap` is proved:
the specialization `ℚ̄ = AlgebraicClosure K`, `X = X₀ ×_K ℚ̄` (`IsCurve` by base change), `L = K`
(∃-introduction, bridge (ii)), and `belyiDegree X hB ≤ d` with the bound increasing in `deg_B` (bridge (i)).

No `sorry`, no `axiom`. -/

noncomputable section

namespace JavanpeykarDirect

open CategoryTheory AlgebraicGeometry Limits
open JavanpeykarDict JavanpeykarFix
open LeafModCurves (IsCurve)
open ZInQ.LeafPush2 (javanpeykarBound)

/-! ## §1. The print's objects -/

/-- `X` (an integral curve over a field `k`) has a **Belyi map of degree `d`** (Javanpeykar 2014 §1): `d > 0`
and there is a finite morphism `β : X → ℙ¹_k` over `k`, unramified over `ℙ¹ ∖ {0, 1, ∞}`, of degree `d`
(javanpeykar-fix's `IsBelyiMap`). The degree of a finite morphism of curves is positive, so `d > 0` removes
nothing; it is stated so that the minimum below is the print's. -/
def HasBelyiMapOfDegree {k : Type} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsIntegral X.left]
    (d : ℕ) : Prop :=
  0 < d ∧ ∃ β : X.left ⟶ P1 k, IsBelyiMap X β d

open Classical in
/-- **The Belyi degree `deg_B(X)`** (Javanpeykar 2014 §1, p. 90): the least degree of a Belyi map of `X`
(`Nat.find`). It is defined given one Belyi map `hB`; over `ℚ̄` every smooth projective connected curve has one
(Belyi's theorem), which a consumer that supplies a Belyi map does not need. -/
def belyiDegree {k : Type} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsIntegral X.left]
    (hB : ∃ d, HasBelyiMapOfDegree X d) : ℕ :=
  Nat.find hB

/-- **The stable Faltings height of an abelian variety over `ℚ̄`** (Faltings 1983 §1, Deligne Sém. Bourbaki
616 §1: the stable height of `W/ℚ̄` is that of a model over a number field `L ⊆ ℚ̄`; locators UNVERIFIED):
`x` is the stable height of `W` if `W ≅ V ×_L ℚ̄` for an abelian variety `V` over a number field `L` with an
embedding `L → ℚ̄` and `x` is the printed stable height of `V` (height-fix's `IsPrintedStableHeight`: Néron
model over a number field `L' ⊇ L` of semistable reduction, `ω = ⋀^g Γ(e*Ω¹)`, metric `(i/2)^g ∫ η ∧ η̄`,
normalized by `[L' : ℚ]`). -/
def IsStableHeightBar {Kbar : Type} [Field Kbar] (W : AbelianVariety Kbar) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Kbar) (V : AbelianVariety L),
    Nonempty ((AbelianVariety.baseChange L Kbar).obj V ≅ W) ∧
      ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x

/-! ## §2. The leaf -/

/-- **Leaf R18-Javanpeykar, the print** (A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi
curves*, Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90 (arXiv:1403.6404v1, Thm 1.1.1, p. 1); the
Faltings height of `X` is the stable Faltings height of `Jac(X)`, p. 98 (arXiv §2.3); locators recorded by the
locator audit, docs/research/locators.md row R18). Printed: for a smooth projective connected curve `X` over
`ℚ̄` of genus `g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`.

Over the print's objects:
* `ℚ̄`: `Kbar`, any algebraic closure of `ℚ`;
* `X`: a smooth (relative dimension 1) proper geometrically connected curve over `ℚ̄` (`IsCurve`), integral,
  projective (a closed immersion into `ℙ(n; Spec ℚ̄)` over `ℚ̄`);
* `g = genusK X = dim_ℚ̄ H¹(X, 𝒪_X)` (vendored `arithmeticGenus`);
* `Jac(X)`: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with the
  tensor-product group law (vendored `picardFunctorDegree`, `PicardTensorCompatible`);
* `h_Fal(X) = h_Fal(Jac X)`: any `x` with `IsStableHeightBar W x`;
* `deg_B(X) = belyiDegree X hB` for a given proof `hB` that `X` has a Belyi map (Belyi's theorem says it
  always has one). -/
def JavanpeykarThm111 : Prop :=
  ∀ (Kbar : Type) [Field Kbar] [Algebra ℚ Kbar] [IsAlgClosure ℚ Kbar]
    (X : Over (Spec (CommRingCat.of Kbar))) [IsCurve X] [IsIntegral X.left],
    (∃ (n : Type) (_ : Finite n) (i : X.left ⟶ ℙ(n; Spec (CommRingCat.of Kbar))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of Kbar)) ↘ Spec (CommRingCat.of Kbar) = X.hom) →
    1 ≤ genusK X →
    ∀ (W : AbelianVariety Kbar)
      (repW : (picardFunctorDegree X.hom 0).obj.RepresentableBy W.group.X),
      PicardTensorCompatible X.hom W.group repW →
    ∀ (hB : ∃ d, HasBelyiMapOfDegree X d),
    ∀ x : ℝ, IsStableHeightBar W x → x ≤ javanpeykarBound (genusK X) (belyiDegree X hB)

/-! ## §3. The two bridges -/

/-- **Bridge (i), part 1**: `deg_B(X)` is at most the degree of any given Belyi map. -/
theorem belyiDegree_le {k : Type} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
    {β : X.left ⟶ P1 k} {d : ℕ} (hβ : IsBelyiMap X β d) (hd : 0 < d) :
    belyiDegree X ⟨d, hd, β, hβ⟩ ≤ d := by
  classical
  unfold belyiDegree
  exact Nat.find_min' _ ⟨hd, β, hβ⟩

/-- `deg_B(X)` is a degree of a Belyi map (so it is positive). -/
theorem hasBelyiMapOfDegree_belyiDegree {k : Type} [Field k] {X : Over (Spec (CommRingCat.of k))}
    [IsIntegral X.left] (hB : ∃ d, HasBelyiMapOfDegree X d) :
    HasBelyiMapOfDegree X (belyiDegree X hB) := by
  classical
  unfold belyiDegree
  exact Nat.find_spec hB

/-- `belyiDegree` does not depend on the proof of existence. -/
theorem belyiDegree_congr {k : Type} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
    (h₁ h₂ : ∃ d, HasBelyiMapOfDegree X d) : belyiDegree X h₁ = belyiDegree X h₂ := rfl

/-- **Bridge (i), part 2**: the print's bound `13·10⁶ · g · d⁵` is increasing in `d`. -/
theorem javanpeykarBound_mono (g : ℕ) {d d' : ℕ} (h : d ≤ d') :
    javanpeykarBound g d ≤ javanpeykarBound g d' := by
  unfold javanpeykarBound
  have : ((d : ℝ)) ^ 5 ≤ ((d' : ℝ)) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) 5
  have hg : (0 : ℝ) ≤ 13 * 10 ^ 6 * (g : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left this hg

/-- **Bridge (ii)**: the printed stable height of a model `V` over `K` of `W` (over `K̄`) is the stable height
of `W` (∃-introduction at `L = K`). -/
theorem isStableHeightBar_of_model {K : Type} [Field K] [NumberField K] (Kbar : Type) [Field Kbar]
    [Algebra K Kbar] {W : AbelianVariety Kbar} (V : AbelianVariety K)
    (hVW : Nonempty ((AbelianVariety.baseChange K Kbar).obj V ≅ W)) {x : ℝ}
    (hx : ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x) : IsStableHeightBar W x :=
  ⟨K, inferInstance, inferInstance, inferInstance, V, hVW, hx⟩

/-- An algebraic closure of a number field is an algebraic closure of `ℚ`. -/
instance isAlgClosure_rat (K : Type) [Field K] [NumberField K] : IsAlgClosure ℚ (AlgebraicClosure K) where
  isAlgClosed := inferInstance
  isAlgebraic := Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)

/-- `X₀ ×_K L` is a curve over `L` when `X₀` is a curve over `K` (smooth, proper and geometrically connected are
stable under base change). -/
theorem isCurve_baseChange {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) [hX : IsCurve X]
    (L : Type) [Field L] [Algebra K L] : IsCurve (baseChangeCurve X L) := by
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  refine ⟨?_, ?_, ?_⟩
  · exact inferInstanceAs (IsProper ((AlgebraicGeometry.baseChange K L).obj X).hom)
  · exact inferInstanceAs (SmoothOfRelativeDimension 1 ((AlgebraicGeometry.baseChange K L).obj X).hom)
  · exact inferInstanceAs (GeometricallyConnected
      (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))))

/-- `genusK (X₀ ×_K K̄) = genusBar X₀` (definitional). -/
theorem genusK_baseChange {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) :
    genusK (baseChangeCurve X (AlgebraicClosure K)) = genusBar X := rfl

/-! ## §4. The old field from the new leaf -/

/-- **`javanpeykarPrintedMapHF` from the print** (`JavanpeykarThm111`): specialize `ℚ̄ := AlgebraicClosure K`
and `X := X₀ ×_K ℚ̄`; the model `V` over `K` gives the stable height of `W` (bridge (ii)); `deg_B(X) ≤ d` and
the bound is increasing (bridge (i)). -/
theorem javanpeykarPrintedMap_of_thm111 (h : JavanpeykarThm111) :
    JavanpeykarRebase.JavanpeykarPrintedMap := by
  intro K _ _ X _ _ hproj W repW htcW V hVW hg1 β d hβ hd0 x hx
  have := isCurve_baseChange X (AlgebraicClosure K)
  have hB : ∃ d, HasBelyiMapOfDegree (baseChangeCurve X (AlgebraicClosure K)) d := ⟨d, hd0, β, hβ⟩
  have h1 := h (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)) hproj
    (by rw [genusK_baseChange]; exact hg1) W repW htcW hB x
    (isStableHeightBar_of_model (AlgebraicClosure K) V hVW hx)
  rw [genusK_baseChange] at h1
  exact h1.trans (javanpeykarBound_mono _ (belyiDegree_le hβ hd0))

end JavanpeykarDirect

end

#print axioms JavanpeykarDirect.javanpeykarPrintedMap_of_thm111
