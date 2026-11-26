import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelDeuringInjective
import ZInQKernel.Contrib.AbsFrob.Basic
import ZInQKernel.Contrib.AbsFrob.Sanity

/-! **The reach from a reference with a model over `F_q`.**

For a reference `E₀ = A_k` with `A` an abelian variety over `F_q`, every
supersingular `E` over `k = F_q^al` is reached from `E₀` by a separable isogeny
(`separableReach_of_primeModel`). The route (ON THE SPOT, provenance (c)):

* the invertibility clause of the Theorem 42.3.2 candidate, applied with `E` as
  the reference, places `Hom(E₀, E)` as a full lattice, so there is a nonzero
  `α : E₀ → E`;
* a nonzero homomorphism is nonconstant (`isNonconstant_of_ne_zero`);
* Silverman Cor. II.2.12 in its prime-model form (`SilvermanII212PrimeModel`,
  the one new printed candidate) writes `α` as a power of the `q`-power
  Frobenius `E₀ → E₀^(q^r) = E₀` followed by a separable map `g`; here
  `E₀^(q^r) = E₀` because `E₀` comes from `F_q`, and the Frobenius is
  `primeFrobBC`, the base change of the absolute Frobenius of `A`;
* `g` fixes the origin and is multiplicative, because the Frobenius is a
  surjective homomorphism (`isMonHom_of_frob_comp`), and it is nonconstant
  because `α` is.

This replaces Voight's unproved sentence on p. 786 for such a reference.
Baker, González-Jiménez, González and Poonen take the same step inside the
proof of their Lemma 3.21 (arXiv math/0211394v2; journal version unread,
UNVERIFIED). -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Eichler PkgI3.AbVar
open scoped CategoryTheory.MonObj

set_option linter.style.haveILetI false

/-! ## 1. The absolute Frobenius of an abelian variety over `F_q` -/

section Frob

variable (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
theorem natCast_over (X : Over (Spec (CommRingCat.of (ZMod q)))) : (q : Γ(X.left, ⊤)) = 0 :=
  AbsFrobDef.natCast_of_hom q (R := CommRingCat.of (ZMod q)) (ZMod.natCast_self q) X.hom

/-- The absolute Frobenius of an `F_q`-scheme, as a morphism over `Spec F_q` (the absolute
Frobenius of `Spec F_q` is the identity, `AbsFrobDef.fr_Spec_zmod`). -/
def frO (X : Over (Spec (CommRingCat.of (ZMod q)))) : X ⟶ X :=
  Over.homMk (AbsFrobDef.fr q X.left (natCast_over q X)) (by
    have h := AbsFrobDef.fr_naturality q X.hom
      (AbsFrobDef.natCast_Spec q (CommRingCat.of (ZMod q)) (ZMod.natCast_self q))
      (natCast_over q X)
    rw [AbsFrobDef.fr_Spec_zmod, Category.comp_id] at h
    exact h.symm)

@[simp] theorem frO_left (X : Over (Spec (CommRingCat.of (ZMod q)))) :
    (frO q X).left = AbsFrobDef.fr q X.left (natCast_over q X) := rfl

theorem frO_naturality {X Y : Over (Spec (CommRingCat.of (ZMod q)))} (f : X ⟶ Y) :
    f ≫ frO q Y = frO q X ≫ f := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, frO_left]
  exact AbsFrobDef.fr_naturality q f.left _ _

theorem frO_unit : frO q (𝟙_ (Over (Spec (CommRingCat.of (ZMod q))))) = 𝟙 _ :=
  toUnit_unique _ _

theorem frO_tensor (X Y : Over (Spec (CommRingCat.of (ZMod q)))) :
    frO q (X ⊗ Y) = frO q X ⊗ₘ frO q Y := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [← frO_naturality, tensorHom_fst]
  · rw [← frO_naturality, tensorHom_snd]

instance (A : PkgI3.AbVar (ZMod q)) : IsMonHom (frO q A.X) where
  one_hom := by rw [frO_naturality, frO_unit, Category.id_comp]
  mul_hom := by rw [frO_naturality, frO_tensor]

/-- The absolute (`q`-power) Frobenius of an abelian variety over `F_q`, as an endomorphism. -/
def primeFrob (A : PkgI3.AbVar (ZMod q)) : A.End := Hom.mk' (frO q A.X)

/-- The Frobenius of `A_k`: the base change of `primeFrob` to `k`. -/
def primeFrobBC (k : Type) [Field k] [Algebra (ZMod q) k] (A : PkgI3.AbVar (ZMod q)) :
    (A.baseChange k).End :=
  ZInQ.Contrib.AVB1.bcHom k A A (primeFrob q A)

variable {q}

theorem primeFrobBC_left_fst (k : Type) [Field k] [Algebra (ZMod q) k]
    (A : PkgI3.AbVar (ZMod q)) :
    (primeFrobBC q k A).hom.left ≫ pullback.fst A.X.hom (ZInQ.Contrib.AbVarBC.sK (ZMod q) k) =
      pullback.fst A.X.hom (ZInQ.Contrib.AbVarBC.sK (ZMod q) k) ≫
        AbsFrobDef.fr q A.X.left (natCast_over q A.X) := by
  rw [primeFrobBC, ZInQ.Contrib.AVB1.bcHom_hom]
  exact pullback.lift_fst _ _ _

theorem natCast_field (k : Type) [Field k] [Algebra (ZMod q) k] : (q : k) = 0 := by
  rw [← map_natCast (algebraMap (ZMod q) k), ZMod.natCast_self, map_zero]

/-- **`primeFrobBC` acts on `k`-points by the `q`-power map.** For a `k`-point
`P : Spec k → A_k`, read in `A` through the projection `A_k → A`, the point
`Frob ∘ P` is `P` precomposed with `Spec` of `x ↦ x ^ q`: its coordinates are the
`q`-th powers of those of `P`. This is the identification of Silverman's
coordinatewise `q`-power map with `primeFrobBC`. -/
theorem primeFrobBC_pt (k : Type) [Field k] [Algebra (ZMod q) k] (A : PkgI3.AbVar (ZMod q))
    (P : Spec (CommRingCat.of k) ⟶ (A.baseChange k).X.left) :
    P ≫ (primeFrobBC q k A).hom.left ≫ pullback.fst A.X.hom (ZInQ.Contrib.AbVarBC.sK (ZMod q) k) =
      Spec.map (CommRingCat.ofHom (AbsFrobDef.powHom q k (natCast_field k))) ≫
        P ≫ pullback.fst A.X.hom (ZInQ.Contrib.AbVarBC.sK (ZMod q) k) := by
  rw [primeFrobBC_left_fst]
  have h := AbsFrobDef.fr_naturality q
    (P ≫ pullback.fst A.X.hom (ZInQ.Contrib.AbVarBC.sK (ZMod q) k)) (natCast_over q A.X)
    (AbsFrobDef.natCast_Spec q (CommRingCat.of k) (natCast_field k))
  rw [AbsFrobDef.fr_Spec q _ (natCast_field k)] at h
  exact (Category.assoc _ _ _).symm.trans h

/-! ## 2. Surjectivity of the Frobenius -/

instance surjective_frO (X : Over (Spec (CommRingCat.of (ZMod q)))) :
    Surjective (frO q X).left := by
  constructor
  intro x
  exact ⟨x, rfl⟩

theorem surjective_primeFrobBC (k : Type) [Field k] [Algebra (ZMod q) k]
    (A : PkgI3.AbVar (ZMod q)) : Surjective (primeFrobBC q k A).hom.left := by
  rw [primeFrobBC, ZInQ.Contrib.AVB1.bcHom_hom]
  exact MorphismProperty.overPullbackMap (P := @Surjective.{0}) _ (frO q A.X)
    (surjective_frO (q := q) A.X)

theorem surjective_pow_hom {k : Type} [Field k] {B : PkgI3.AbVar k} (F : B.End)
    (hF : Surjective F.hom.left) (r : ℕ) : Surjective (F ^ r).hom.left := by
  induction r with
  | zero =>
    rw [pow_zero]
    change Surjective (Over.Hom.left (𝟙 B.X))
    rw [Over.id_left]
    infer_instance
  | succ r ih =>
    rw [pow_succ]
    change Surjective (F.hom ≫ (F ^ r).hom).left
    rw [Over.comp_left]
    haveI := hF
    haveI := ih
    infer_instance

theorem surjective_tensorHom {k : Type} [Field k] {X Y X' Y' : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : Surjective f.left) (hg : Surjective g.left) :
    Surjective (f ⊗ₘ g).left := by
  haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Surjective.{0}) hf hg (Over.w f).symm (Over.w g).symm

end Frob

/-! ## 3. Nonconstant maps -/

section Nonconstant

variable {k : Type} [Field k]

/-- **A nonzero homomorphism is nonconstant** (over an algebraically closed field):
a homomorphism constant on points takes every point to the origin, and two maps
from the reduced `A` to the separated `B` agreeing on closed points are equal
(Mathlib's `ext_of_apply_eq`). -/
theorem isNonconstant_of_ne_zero [IsAlgClosed k] {A B : PkgI3.AbVar k} (α : Hom A B)
    (hα : α ≠ 0) : IsNonconstant α.hom := by
  by_contra hc
  simp only [IsNonconstant, not_exists, not_not] at hc
  apply hα
  apply Hom.ext'
  rw [Hom.hom_zero]
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  haveI : LocallyOfFiniteType (α.hom.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  apply Over.OverMorphism.ext
  refine ext_of_apply_eq B.X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (by rw [Over.w, Over.w])
  intro x _ _
  let o : A.X.left := (η[A.X]).left (IsLocalRing.closedPoint k)
  have h1 : α.hom.left.base o = (η[B.X]).left.base (IsLocalRing.closedPoint k) := by
    change (η[A.X] ≫ α.hom).left.base _ = _
    rw [IsMonHom.one_hom]
  rw [hc x o, h1]
  change _ = (toUnit A.X ≫ η[B.X]).left.base x
  haveI : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- **Teeth (a).** A nonconstant map between one-dimensional abelian varieties
sends the generic point to the generic point, so `IsSeparableMor f` is the
separability of the extension of function fields `k(A) / f^* k(B)`. -/
theorem base_genericPoint_of_isNonconstant {A B : PkgI3.AbVar k} (hB : B.dim = 1)
    (f : A.X ⟶ B.X) (hf : IsNonconstant f) :
    haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
    haveI : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
    f.left.base (genericPoint A.X.left) = genericPoint B.X.left := by
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  haveI : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  set ζ := f.left.base (genericPoint A.X.left)
  by_contra hne
  have hmem : ∀ x : A.X.left, ζ ⤳ f.left.base x := fun x =>
    (genericPoint_specializes x).map f.left.continuous
  have hgen : ∀ w : B.X.left, closure ({w} : Set B.X.left) = Set.univ →
      w = genericPoint B.X.left := fun w hw =>
    (show IsGenericPoint w (⊤ : Set B.X.left) from hw).eq (genericPoint_spec B.X.left)
  obtain ⟨x, y, hxy⟩ := hf
  have hw : ∃ w : B.X.left, ζ ⤳ w ∧ w ≠ ζ := by
    by_cases hx : f.left.base x = ζ
    · exact ⟨f.left.base y, hmem y, fun h => hxy (hx.trans h.symm)⟩
    · exact ⟨f.left.base x, hmem x, hx⟩
  obtain ⟨w, hζw, hwζ⟩ := hw
  let Z1 : TopologicalSpace.IrreducibleCloseds B.X.left :=
    ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z2 : TopologicalSpace.IrreducibleCloseds B.X.left :=
    ⟨closure {ζ}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z3 : TopologicalSpace.IrreducibleCloseds B.X.left :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have h12 : Z1 < Z2 := by
    refine lt_of_le_of_ne ?_ ?_
    · change closure {w} ⊆ closure {ζ}
      exact hζw.closure_subset
    · intro h
      have h' : closure ({w} : Set B.X.left) = closure {ζ} :=
        congrArg TopologicalSpace.IrreducibleCloseds.carrier h
      exact hwζ ((show IsGenericPoint w (closure {ζ}) from h').eq
        (isGenericPoint_closure (x := ζ)))
  have h23 : Z2 < Z3 := by
    refine lt_of_le_of_ne (fun _ _ => trivial) ?_
    intro h
    exact hne (hgen ζ (congrArg TopologicalSpace.IrreducibleCloseds.carrier h))
  let p : LTSeries (TopologicalSpace.IrreducibleCloseds B.X.left) :=
    { length := 2
      toFun := ![Z1, Z2, Z3]
      step := by
        intro i
        fin_cases i
        · exact h12
        · exact h23 }
  have hlen := Order.LTSeries.length_le_krullDim p
  have hdim : Order.krullDim (TopologicalSpace.IrreducibleCloseds B.X.left) = 1 := hB
  rw [hdim] at hlen
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := hlen
  exact absurd h2 (by decide)

end Nonconstant

/-! ## 4. The printed candidate and the factor lemma -/

/-- **Printed candidate, UNVERIFIED; rating UNCERTAIN.** Silverman, *The Arithmetic
of Elliptic Curves* (2nd ed., GTM 106), Cor. II.2.12 (§II.2, pp. 19-27; the
author's errata corrects a notation in the last line of its proof, p. 27, line 1;
locators from memory, UNVERIFIED until the owner's page check). Paraphrase (no
quotation; wording UNVERIFIED): every map `ψ : C₁ → C₂` of smooth curves over a
field of characteristic `p > 0` factors as the `q`-th power Frobenius map
`C₁ → C₁^(q)` followed by a separable map `C₁^(q) → C₂`, where `q = deg_i ψ`.

The reading desk decides (two-lens pass) whether this form is a direct instance
of II.2.12 or GLUE (a consequence of one theorem): it uses `C₁^(q^r) = C₁` for a
curve with coefficients in `F_q`, and the identification of Silverman's
coordinatewise `q^r`-power map with `primeFrobBC ^ r` (`primeFrobBC_pt`). No fall
in the GLUE count is claimed.

Specializations (each only weakens the candidate):
* `C₁` and `C₂` are one-dimensional `PkgI3.AbVar` (elliptic curves); the dimension
  hypothesis is on `C₁ = A.baseChange k` itself;
* `C₁` is defined over `F_q`, as `C₁ = A.baseChange k`;
* "`q = deg_i ψ`" is weakened to "some `r`", and `ψ` is nonconstant (Silverman's
  statement is for nonconstant maps).

Representations:
* Silverman's `q`-power Frobenius map `C₁ → C₁^(q^r) = C₁` is `primeFrobBC ^ r`
  (Silverman's `q`, a power of the characteristic, is the project's `q^r`; the
  project's `q` is the prime `ℓ₀`); `primeFrobBC_pt` shows that `primeFrobBC` acts
  on `k`-points by the `q`-power map;
* "separable" is `IsSeparableMor` and "nonconstant" is `IsNonconstant`.

Since `r = 0` is allowed, the candidate is only as strong as `IsSeparableMor`
(teeth: `base_genericPoint_of_isNonconstant`; that `primeFrobBC` itself is not
`IsSeparableMor` is open, see the report). -/
def SilvermanII212PrimeModel : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (A : PkgI3.AbVar (ZMod q)) (E : PkgI3.AbVar k),
    (A.baseChange k).dim = 1 → E.dim = 1 →
    ∀ ψ : (A.baseChange k).X ⟶ E.X, IsNonconstant ψ →
      ∃ (r : ℕ) (g : (A.baseChange k).X ⟶ E.X),
        (haveI : IsIntegral (A.baseChange k).X.left :=
          GeometricallyIntegral.isIntegral_of_subsingleton (A.baseChange k).X.hom
         IsSeparableMor g) ∧ ψ = (primeFrobBC q k A ^ r).hom ≫ g

section Factor

variable {k : Type} [Field k]

/-- **The factor lemma.** If a homomorphism `α` is `Φ ≫ g` for a surjective
endomorphism-homomorphism `Φ` of the source, then `g` is a homomorphism: the unit
is preserved since `Φ` fixes it, and multiplicativity holds after precomposing
with the dominant `Φ × Φ` on the reduced `A × A`, so it holds (the target is
separated, Mathlib's `ext_of_isDominant_of_isSeparated`). -/
theorem isMonHom_of_frob_comp {A E : PkgI3.AbVar k} (Φ : A.End) (hΦ : Surjective Φ.hom.left)
    (α : Hom A E) (g : A.X ⟶ E.X) (hα : α.hom = Φ.hom ≫ g) : IsMonHom g := by
  constructor
  · have h1 := IsMonHom.one_hom α.hom
    rw [hα, ← Category.assoc, IsMonHom.one_hom] at h1
    exact h1
  · haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
    haveI : Finite (irreducibleComponents A.X.left) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    haveI : IsReduced (A.X ⊗ A.X).left :=
      GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
        (pullback.fst A.X.hom A.X.hom)
    haveI : Surjective (Φ.hom ⊗ₘ Φ.hom).left := surjective_tensorHom _ _ hΦ hΦ
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated E.X.hom (by rw [Over.w, Over.w])
      (Φ.hom ⊗ₘ Φ.hom).left ?_
    have key : (Φ.hom ⊗ₘ Φ.hom) ≫ μ ≫ g = (Φ.hom ⊗ₘ Φ.hom) ≫ (g ⊗ₘ g) ≫ μ := by
      rw [← Category.assoc, ← IsMonHom.mul_hom Φ.hom, Category.assoc, ← hα,
        IsMonHom.mul_hom α.hom, hα, ← tensorHom_comp_tensorHom, Category.assoc]
    have h3 := congrArg Over.Hom.left key
    simpa only [Over.comp_left] using h3

theorem isNonconstant_of_comp {X Y Z : Over (Spec (CommRingCat.of k))} (Φ : X ⟶ Y) (g : Y ⟶ Z)
    (h : IsNonconstant (Φ ≫ g)) : IsNonconstant g := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨Φ.left.base x, Φ.left.base y, by simpa [Over.comp_left] using hxy⟩

end Factor

/-! ## 5. The reach and its corollaries -/

/-- **The reach from a prime model** (ON THE SPOT, provenance (c)). For a reference
`A_k` with `A` over `F_q`, every supersingular `E` is reached from `A_k` by a
separable isogeny. Sketch: a frame of `E` and the invertibility clause (with `E` as
the reference and `A_k` as the curve) place `Hom(A_k, E)` as a nonzero lattice, so
there is `α ≠ 0`; it is nonconstant; the prime-model form of Silverman II.2.12
gives `α = Frob^r ≫ g` with `g` separable; the factor lemma makes `g` a
nonconstant homomorphism. -/
theorem separableReach_of_primeModel (hS : SilvermanII212PrimeModel)
    (hInv : VoightThm4232Invertible) (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3)
    {k : Type} [Field k] [Algebra (ZMod q) k] [IsAlgClosure (ZMod q) k]
    (A : PkgI3.AbVar (ZMod q)) (h₀ : IsSupersingular (A.baseChange k)) :
    SeparableReach (A.baseChange k) := by
  haveI := isAlgClosed_of_isAlgClosure q k
  intro E hE
  obtain ⟨SE, ⟨jE⟩, -⟩ := exists_referenceFrame hT hV q hq E hE
  obtain ⟨P⟩ := hInv q k E hE _ _ SE jE (A.baseChange k) h₀
  obtain ⟨y, hy, hy0⟩ := P.ideal.val.exists_ne_zero
  obtain ⟨α, rfl⟩ := P.exists_of_mem hy
  have hα : α ≠ 0 := fun h => hy0 (by rw [h, map_zero])
  obtain ⟨r, g, hsep, hfac⟩ := hS q k A E h₀.1 hE.1 α.hom (isNonconstant_of_ne_zero α hα)
  haveI : IsMonHom g := isMonHom_of_frob_comp _ (surjective_pow_hom _
    (surjective_primeFrobBC k A) r) α g hfac
  refine ⟨Hom.mk' g, ?_, ?_⟩
  · rw [Hom.hom_mk']
    exact isNonconstant_of_comp _ g (hfac ▸ isNonconstant_of_ne_zero α hα)
  · exact hsep

section Corollaries

variable {q : ℕ} [Fact q.Prime] (h : q % 4 = 3) {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {N : ℕ} (hN : 0 < N) (hcop : N.Coprime q)
  (A : PkgI3.AbVar (ZMod q)) (h₀ : IsSupersingular (A.baseChange k))
  {P₀ : (A.baseChange k).Pt k} (hP₀ : orderOf P₀ = N)
  {S : Order (-1) (-(q : ℚ))} (j : (A.baseChange k).End ≃+* S.ring)
  (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)

/-- **Injectivity for a reference with a model over `F_q`.** `levelDeuringClass_injective`
at `E₀ := A_k`, with the reach supplied by `separableReach_of_primeModel`. Rests on
`SilvermanII212PrimeModel`, `hEt`, `hInv`, `hT` and `hV`. -/
theorem levelDeuringClass_injective_primeModel (hS : SilvermanII212PrimeModel)
    (hInv : VoightThm4232Invertible) (hEt : VoightThm4232Etale) (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) :
    Function.Injective (levelDeuringClass h hN hcop h₀ hP₀ j hmax hInv) :=
  levelDeuringClass_injective h hN hcop h₀ hP₀ j hmax hInv hEt
    (separableReach_of_primeModel hS hInv hT hV h A h₀)

end Corollaries

end ZInQ.Manuscript.RC.HCMV21
