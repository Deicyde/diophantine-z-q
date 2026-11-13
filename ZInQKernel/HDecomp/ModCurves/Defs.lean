import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.Conductor.LadicCond

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/leaf-modcurves/ModCurveLeaves.lean`, §B-§E.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

noncomputable section

/-! ## §B. Galois side and modular forms (copied from `Leaves.lean`, namespace `PkgI4`) -/

namespace LeafModCurves

open scoped MatrixGroups ModularForm

/-! `ℚ̄`, `G_ℚ`, `LiesOver`, `IsArithFrob` and the cusp-form definitions (copied in the
draft from `Leaves.lean`) are `PkgI4`'s, from `ZInQKernel.HDecomp.Conductor.LadicCond`. -/
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)



/-- Arithmetic Frobenius at `p` is the kernel's `GlueC10.IsFrobAt` (a prime `𝔓` of `ℤ̄` over
`p` with `g x ≡ x^p mod 𝔓` on `ℤ̄`), the predicate consumed by C10. It is equivalent to
`PkgI4.IsArithFrob` at the place `ℤ̄_𝔓` of `Leaves.lean` (valuation rings of `ℚ̄` containing `ℤ̄`
are its localizations), so the choice does not change the leaf. -/
abbrev IsFrobAt (g : GQ) (p : ℕ) : Prop := GlueC10.IsFrobAt g p



/-- `ℤ̄` lies in every valuation subring of `ℚ̄` (valuation rings are integrally closed). -/
theorem zbar_mem (v : ValuationSubring Qbar) (x : GlueC10.Zbar) : (x : Qbar) ∈ v := by
  have hx : IsIntegral ℤ (x : Qbar) := x.2
  have hx' : IsIntegral v (x : Qbar) := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v) (K := Qbar)).mp hx'
  rw [← hy]
  exact y.2

/-- **Bridge (proved)**: an arithmetic Frobenius in the sense of `Leaves.lean` (`PkgI4`) is one in
the sense of the kernel (`GlueC10.IsFrobAt`), with `𝔓 = 𝔪_v ∩ ℤ̄`. So R16 below, stated with
`IsFrobAt`, implies its `IsArithFrob` form. (The converse, which shows `IsFrobAt` is the
standard notion: `g x ≡ x^p mod 𝔓` on `ℤ̄` forces `g𝔓 = 𝔓`, take `v = ℤ̄_𝔓`.) -/
theorem isFrobAt_of_isArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime)
    (hv : LiesOver v p) (h : IsArithFrob σ v p) : IsFrobAt σ p := by
  let ι : GlueC10.Zbar →+* v :=
    { toFun := fun x => ⟨x, zbar_mem v x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hP : ((IsLocalRing.maximalIdeal v).comap ι).IsPrime := Ideal.IsPrime.comap ι
  refine ⟨(IsLocalRing.maximalIdeal v).comap ι, hP, ?_, ?_⟩
  · have hU : (((IsLocalRing.maximalIdeal v).comap ι).under ℤ).IsPrime := Ideal.IsPrime.comap _
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine (hmax.eq_of_le hU.ne_top ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show ι (algebraMap ℤ GlueC10.Zbar p) ∈ IsLocalRing.maximalIdeal v
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa [ι, LiesOver] using hv
  · intro x y hy
    show ι y ∈ IsLocalRing.maximalIdeal v
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    change (y : Qbar) ∈ v.nonunits
    rw [hy]
    exact h.2 _ (zbar_mem v x)








/-- **The coefficient field** `K_f = ℚ(a_n(f) : n ≥ 0) ⊆ ℂ`. (Its finiteness over `ℚ` is part of
the conclusion of R16, not of the definition.) -/
def coeffField {N : ℕ} {k : ℤ} (f : CF N k) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range (coeff f))

theorem coeff_mem_coeffField {N : ℕ} {k : ℤ} (f : CF N k) (n : ℕ) : coeff f n ∈ coeffField f :=
  IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩

/-! ## §C. The `j`-line and `K_N = ℚ(j)(x(P))` (copied from bp-modcurves) -/

open WeierstrassCurve AlgebraicGeometry

/-- The function field `ℚ(j)` of the `j`-line. -/
abbrev Qj := RatFunc ℚ

/-- The elliptic curve over `ℚ(j)` with `j`-invariant `j` (Mathlib v4.35 `ofJNe0Or1728`:
`y² + (j−1728)xy = x³ − 36(j−1728)³x − (j−1728)⁵`, with `Δ = j²(j−1728)⁹`). -/
def Ej : WeierstrassCurve Qj := ofJNe0Or1728 (RatFunc.X : Qj)

theorem X_sub_1728_ne_zero : (RatFunc.X : Qj) - 1728 ≠ 0 := by
  intro h
  have h' : (algebraMap (Polynomial ℚ) Qj) (Polynomial.X - Polynomial.C 1728) = 0 := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    simpa using h
  rw [map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) Qj)] at h'
  exact Polynomial.X_sub_C_ne_zero 1728 h'

instance : Fact (IsUnit (RatFunc.X : Qj)) := ⟨isUnit_iff_ne_zero.2 RatFunc.X_ne_zero⟩
instance : Fact (IsUnit ((RatFunc.X : Qj) - 1728)) := ⟨isUnit_iff_ne_zero.2 X_sub_1728_ne_zero⟩

instance : Ej.IsElliptic := by unfold Ej; infer_instance

/-- `j(E_j) = j`. -/
theorem Ej_j : Ej.j = RatFunc.X := by unfold Ej; exact ofJNe0Or1728_j _

/-- An algebraic closure of `ℚ(j)`. -/
abbrev Kbar := AlgebraicClosure Qj

instance : DecidableEq Kbar := Classical.decEq _

/-- `E_j` over `\overline{ℚ(j)}`. -/
def EjBar : WeierstrassCurve Kbar := Ej.baseChange Kbar

/-- The `x`-coordinate of an affine point (junk value `0` at the origin). -/
def xCoord {F : Type*} [Field F] {W : WeierstrassCurve F} : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

/-- **`K_N = ℚ(j)(x(P))`**, for `P` a point of `E_j` over `\overline{ℚ(j)}`. For `P` of exact
order `N` this is the function field of `X₁(N)` over `ℚ` (§D). `x(P)` may be replaced by the
Weber function `h(P)`, a `ℚ(j)^×`-multiple of `x(P)`, so `K_N` does not depend on the model
`E_j` among the quadratic twists (STANDARD). -/
def fieldX1 (P : EjBar.toAffine.Point) : IntermediateField Qj Kbar :=
  IntermediateField.adjoin Qj {xCoord P}

/-- The structure map `ℚ[j] → ℚ(j)(x(P))`. -/
def jLineToField (P : EjBar.toAffine.Point) : Polynomial ℚ →+* fieldX1 P :=
  (algebraMap Qj (fieldX1 P)).comp (algebraMap (Polynomial ℚ) Qj)

/-- `X₁(N)` minus the cusps, as Mathlib's relative normalization of `Spec ℚ[j]` in `K_N`. Not
used by the leaves; recorded as the affine chart of the algebraic construction (MC4). -/
def Y1j (P : EjBar.toAffine.Point) : Scheme :=
  (Spec.map (CommRingCat.ofHom (jLineToField P))).normalization

/-- The `j`-map `Y₁(N) → 𝔸¹_j`. -/
def jMap (P : EjBar.toAffine.Point) : Y1j P ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  (Spec.map (CommRingCat.ofHom (jLineToField P))).fromNormalization

/-! ## §D. Curves over a field and the function-field definition of `X₁(N)/ℚ` -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- A smooth proper geometrically connected curve over `K` (proper curves are projective). -/
class IsCurve {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) : Prop where
  proper : IsProper X.hom
  smooth : SmoothOfRelativeDimension 1 X.hom
  geomConnected : GeometricallyConnected X.hom

/-- `Spec ℚ`. -/
abbrev SpecQ : Scheme := Spec (CommRingCat.of ℚ)

/-- **`X` is a model of `X₁(N)` over `ℚ`**: a smooth proper geometrically connected curve over
`ℚ`, integral, whose function field is isomorphic to `K_N = ℚ(j)(x(P))` for a point `P` of exact
order `N` of `E_j`.

* A ring isomorphism of fields of characteristic `0` is `ℚ`-linear, so `≃+*` is a
  `ℚ`-isomorphism of function fields. A smooth proper curve over `ℚ` is determined up to
  `ℚ`-isomorphism by its function field (Hartshorne I.6.12 with II.6.7; UNVERIFIED numbers), so
  any two models are `ℚ`-isomorphic, and every statement about "the" `X₁(N)` invariant under
  `ℚ`-isomorphism may be quantified over all models.
* The points `P` of exact order `N` are permuted transitively up to `±` by `Gal(ℚ(j)ˢᵉᵖ/ℚ(j))`
  (Igusa; Shimura 1971 Thm 6.6, UNVERIFIED), so the choice of `P` does not matter.
* Which `ℚ`-form: this is the field of the moduli problem `(E, P)`, `P` of exact order `N`
  (`ℤ/N ↪ E`). The other common form, `μ_N ↪ E`, is `ℚ`-isomorphic to it (as curves, not as
  covers of the `j`-line) by `(E, P) ↦ (E/⟨P⟩, E[N]/⟨P⟩)` (STANDARD; Diamond–Im §9.3,
  UNVERIFIED). So the definition does not prefer one of the two.
* Existence (`X1ModelExists`, §H) is a separate statement, which the main theorem must consume. -/
def IsX1Model (N : ℕ) (X : Over SpecQ) : Prop :=
  IsCurve X ∧ ∃ (_ : IsIntegral X.left) (P : EjBar.toAffine.Point), addOrderOf P = N ∧
    Nonempty (X.left.functionField ≃+* fieldX1 P)

/-- A `ℚ`-point of a `ℚ`-scheme (a section of the structure morphism). -/
abbrev RatPt (X : Over SpecQ) : Type := 𝟙_ (Over SpecQ) ⟶ X

/-! ## §E. The Jacobian as an Albanese predicate over `PkgI3.AbVar` -/

open PkgI3 PkgI3.AbVar

/-- **`J` is the Jacobian of the pointed curve `(X, P₀)`, with Abel–Jacobi map `aj`** (the
Albanese property; for a curve the Albanese variety is the Jacobian: Milne, *Jacobian
varieties*, in Arithmetic Geometry (1986), Prop. 6.1, UNVERIFIED number). Every pointed
`K`-morphism to an abelian variety factors uniquely through a homomorphism `J → A`. -/
structure IsJacobian {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X) : Prop where
  base : P₀ ≫ aj = η[J.X]
  univ : ∀ (A : AbVar K) (f : X ⟶ A.X), P₀ ≫ f = η[A.X] →
    ∃! φ : J.X ⟶ A.X, IsMonHom φ ∧ aj ≫ φ = f

/-- **Leaf MC6' (existence of the Jacobian).** Every smooth proper geometrically connected curve
over a field `K` with a `K`-point `P₀` has a Jacobian with base point `P₀`. Weil 1948 (via
Chow's construction over any field); Milne 1986, Thm 1.1 (Jacobian representing `Pic⁰`) with
Prop. 6.1 (Albanese property) (UNVERIFIED numbers). The published statement, specialized to
`P₀ ∈ X(K)`. -/
def JacobianExists (K : Type) [Field K] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of K))) (_ : IsCurve X)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X),
    ∃ (J : AbVar K) (aj : X ⟶ J.X), IsJacobian X P₀ J aj

/-- **Uniqueness of the Jacobian** (glue, proved; from bp-modcurves). -/
theorem IsJacobian.unique {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X} {J J' : AbVar K} {aj : X ⟶ J.X}
    {aj' : X ⟶ J'.X} (h : IsJacobian X P₀ J aj) (h' : IsJacobian X P₀ J' aj') :
    ∃ e : J.X ≅ J'.X, IsMonHom e.hom ∧ aj ≫ e.hom = aj' ∧
      ∀ φ : J.X ⟶ J'.X, IsMonHom φ → aj ≫ φ = aj' → φ = e.hom := by
  obtain ⟨φ, ⟨hφ, eφ⟩, uφ⟩ := h.univ J' aj' h'.base
  obtain ⟨ψ, ⟨hψ, eψ⟩, -⟩ := h'.univ J aj h.base
  have hid : φ ≫ ψ = 𝟙 _ :=
    (h.univ J aj h.base).unique (y₁ := φ ≫ ψ) (y₂ := 𝟙 _)
      ⟨inferInstance, by rw [← Category.assoc, eφ, eψ]⟩ ⟨inferInstance, Category.comp_id _⟩
  have hid' : ψ ≫ φ = 𝟙 _ :=
    (h'.univ J' aj' h'.base).unique (y₁ := ψ ≫ φ) (y₂ := 𝟙 _)
      ⟨inferInstance, by rw [← Category.assoc, eψ, eφ]⟩ ⟨inferInstance, Category.comp_id _⟩
  exact ⟨⟨φ, ψ, hid, hid'⟩, hφ, eφ, fun χ hχ eχ => uφ χ ⟨hχ, eχ⟩⟩

/-- **`J` is `J₁(N)`**: the Jacobian of some model of `X₁(N)` over `ℚ` with some rational base
point. (Any two such are isomorphic abelian varieties: the models are `ℚ`-isomorphic (§D),
Jacobians are unique (`IsJacobian.unique`), and a change of base point composes `aj` with a
translation.) -/
def IsJ1 (N : ℕ) (J : AbVar ℚ) : Prop :=
  ∃ (X : Over SpecQ) (P₀ : RatPt X) (aj : X ⟶ J.X), IsX1Model N X ∧ IsJacobian X P₀ J aj


end LeafModCurves
