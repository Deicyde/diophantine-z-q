import ZInQKernel.Contrib.OneProof.RC.HCMV21.EnhancedObjects
import ZInQKernel.Contrib.OneProof.RC.HCMV21.LeftIdealMirror

/-! Printed-form candidates from Voight, *Quaternion Algebras*, GTM 288
(Springer numbering), Ch. 42, in Voight's convention: `O₀ := End(E₀)` acts on
`Hom(E, E₀)` by postcomposition, so `Hom(E, E₀)` is a left `O₀`-module, and the
functor `E ↦ Hom(E, E₀)` is contravariant (`φ ↦ φ*`, `φ*(ψ) = ψφ`, 42.3.4).
None is mirrored. Each is UNVERIFIED until the reading desk's two-lens pass.

Separable scope (the lead's ruling). Voight's inseparable case rests on one
sentence of 42.2.4, p. 787, asserted with no proof or citation: "Then the map
E → E_P ≃ E^(p) is the p-Frobenius map, and rk ker φ_P = p = deg φ even though
(ker φ)(F) = {0}." The inseparable case of Lemma 42.2.7 relies on it, and
Theorem 42.3.2, Lemma 42.2.9 and Cor. 42.3.7 use Lemma 42.2.7. The candidates
below are therefore stated only on étale isogenies and on invertible ideals
containing an integer prime to `q`, and, where the proof reaches a curve `E` as
`E₀,I`, with a premise that `E` is reached from `E₀` by a separable isogeny
(`IsSeparableIsogeny`, Silverman §II.2). This is a specialization of the print.
`IsNonconstant`, `IsSeparableMor`, `IsSeparableIsogeny`, `IsEtaleIsogeny` and
`HomPlacement` are representations, not candidates. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k]

/-- The left action of `O₀ = End(E₀)` on `Hom(E, E₀)` by postcomposition:
`o · α = o ∘ α`, written `α ≫ o` in Lean's diagrammatic order. -/
def postcomp {E E₀ : PkgI3.AbVar k} (o : E₀.End) (α : Hom E E₀) : Hom E E₀ :=
  Hom.mk' (α.hom ≫ o.hom)

/-- The contravariant action `φ* : Hom(E', E₀) → Hom(E, E₀)`, `ψ ↦ ψ ∘ φ`
(Voight 42.3.4). -/
def homPull {E E' E₀ : PkgI3.AbVar k} (φ : Hom E E') : Hom E' E₀ →+ Hom E E₀ where
  toFun ψ := Hom.mk' (φ.hom ≫ ψ.hom)
  map_zero' := Hom.ext' (by rw [Hom.hom_mk', Hom.hom_zero, MonObj.comp_one, Hom.hom_zero])
  map_add' f g := Hom.ext' (by simp only [Hom.hom_mk', Hom.hom_add, MonObj.comp_mul])

@[simp] theorem homPull_hom {E E' E₀ : PkgI3.AbVar k} (φ : Hom E E') (ψ : Hom E' E₀) :
    (homPull φ ψ).hom = φ.hom ≫ ψ.hom := rfl

@[simp] theorem postcomp_hom {E E₀ : PkgI3.AbVar k} (o : E₀.End) (α : Hom E E₀) :
    (postcomp o α).hom = α.hom ≫ o.hom := rfl

/-- A finite, étale, surjective homomorphism. For elliptic curves a separable
isogeny is the same as an étale one; this is the Lean representation of
"separable isogeny" in the morphism clauses of the candidates below (the maps
`φ` of `VoightThm4232Etale`). How a curve is reached from `E₀` uses the other
representation, `IsSeparableIsogeny` (Silverman's §II.2 definitions). -/
def IsEtaleIsogeny {A B : PkgI3.AbVar k} (f : Hom A B) : Prop :=
  IsFinite f.hom.left ∧ Etale f.hom.left ∧ Surjective f.hom.left

/-- **Representation (not a candidate): Silverman's "nonconstant map"** (Silverman,
*The Arithmetic of Elliptic Curves*, §II.2; UNVERIFIED locator). A morphism of
`k`-schemes is nonconstant when it takes two different values on points. -/
def IsNonconstant {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) : Prop :=
  ∃ x y : X.left, f.left.base x ≠ f.left.base y

/-- **Representation (not a candidate): Silverman's "separable map"** (Silverman,
§II.2; UNVERIFIED locator): the extension of function fields `k(C₁) / f^* k(C₂)`
is separable. It is read on the stalks at the generic point of the source:
`f^* : 𝒪_{Y, f(η)} → 𝒪_{X, η} = k(X)`, following the pattern of `degEnd`
(`ZInQKernel/Contrib/OneProof/CharPolyIndepOfEllAlgClosed.lean:150-156`). For a
nonconstant map of curves `f(η)` is the generic point of the target, so the
source of `f^*` is `k(Y)`. -/
def IsSeparableMor {X Y : Over (Spec (CommRingCat.of k))} [IrreducibleSpace X.left]
    (f : X ⟶ Y) : Prop :=
  letI := (f.left.stalkMap (genericPoint X.left)).hom.toAlgebra
  Algebra.IsSeparable (Y.left.presheaf.stalk (f.left.base (genericPoint X.left)))
    (X.left.presheaf.stalk (genericPoint X.left))

/-- **Representation (not a candidate): Voight's "separable isogeny"**, the word
in the proofs of Theorem 42.3.2 and Cor. 42.3.7: a homomorphism that is a
nonconstant (`IsNonconstant`) and separable (`IsSeparableMor`) map in
Silverman's sense (§II.2). Where Voight defines the term is not yet located, so
the match with Silverman's §II.2 definition is UNVERIFIED. The integrality of
`A`'s underlying scheme, needed for its generic point, comes from geometric
integrality over the field. -/
def IsSeparableIsogeny {A B : PkgI3.AbVar k} (f : Hom A B) : Prop :=
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  IsNonconstant f.hom ∧ IsSeparableMor f.hom

/-- Every supersingular curve is reached from `E₀` by a separable isogeny
`E₀ → E` (the source-fixed instance of `SeparableIsogenyExists`). -/
def SeparableReach (E₀ : PkgI3.AbVar k) : Prop :=
  ∀ E : PkgI3.AbVar k, IsSupersingular E → ∃ φ : Hom E₀ E, IsSeparableIsogeny φ

/-- A one-dimensional abelian variety has two distinct points (a subsingleton
space has Krull dimension at most zero). -/
theorem exists_ne_of_dim_eq_one {A : PkgI3.AbVar k} (h : A.dim = 1) :
    ∃ x y : A.X.left, x ≠ y := by
  by_contra! hxy
  have hss : Subsingleton A.X.left := ⟨hxy⟩
  have hle : A.dim ≤ 0 := by
    unfold PkgI3.AbVar.dim topologicalKrullDim
    rw [Order.krullDim_nonpos_iff_forall_isMax]
    intro Z W _ x hx
    obtain ⟨z, hz⟩ := Z.isIrreducible'.nonempty
    rwa [Subsingleton.elim x z]
  rw [h] at hle
  exact absurd hle (by decide)

theorem isNonconstant_id {A : PkgI3.AbVar k} (h : A.dim = 1) : IsNonconstant (𝟙 A.X) := by
  obtain ⟨x, y, hxy⟩ := exists_ne_of_dim_eq_one h
  exact ⟨x, y, hxy⟩

theorem isSeparableMor_id {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left] :
    IsSeparableMor (𝟙 X) := by
  unfold IsSeparableMor
  have h : ∀ (f : X.left ⟶ X.left), f = 𝟙 X.left →
      letI := (f.stalkMap (genericPoint X.left)).hom.toAlgebra
      Algebra.IsSeparable (X.left.presheaf.stalk (f.base (genericPoint X.left)))
        (X.left.presheaf.stalk (genericPoint X.left)) := by
    rintro f rfl
    letI : Field (X.left.presheaf.stalk (genericPoint X.left)) :=
      inferInstanceAs (Field X.left.functionField)
    rw [Scheme.Hom.stalkMap_id]
    exact Algebra.isSeparable_self (X.left.presheaf.stalk (genericPoint X.left))
  exact h _ (Over.id_left X)

/-- The identity of a one-dimensional abelian variety is a separable isogeny, so
the predicate `IsSeparableIsogeny` can hold. -/
theorem isSeparableIsogeny_id {A : PkgI3.AbVar k} (h : A.dim = 1) :
    IsSeparableIsogeny (Hom.mk' (𝟙 A.X) : Hom A A) := by
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  exact ⟨isNonconstant_id h, isSeparableMor_id⟩

/-- **Representation choice for "invertible left `O₀`-module".** Given a
presentation `j : End(E₀) ≃+* S.ring` of `O₀` as an order `S` of `(a, b)_ℚ`,
`Hom(E, E₀)` is invertible when it embeds additively and `O₀`-linearly into
`B = (a, b)_ℚ` with image a locally principal full left ideal of `S`. Such an
embedding gives the `ℤ`-basis of rank four used in the Tate comparison.

Equivalence with invertibility: an invertible left `O₀`-module `M` has
`M ⊗ ℚ ≅ B` as a left `B`-module (`B` is a division algebra, and `M ⊗ ℚ` is a
nonzero `B`-module of `ℚ`-dimension four), so `M` embeds `O₀`-linearly into `B`
with image a locally principal full left ideal of `O₀`, which is a placement;
conversely the image of a placement is such an ideal, which is invertible. The
placement fixes no embedding or basis: any two differ by a right unit of `B`
(`HomPlacement.exists_unit`). -/
structure HomPlacement {a b : ℚ} {E₀ : PkgI3.AbVar k} (S : Order a b)
    (j : E₀.End ≃+* S.ring) (E : PkgI3.AbVar k) where
  emb : Hom E E₀ →+ B a b
  injective : Function.Injective emb
  map_postcomp : ∀ (o : E₀.End) (α : Hom E E₀), emb (postcomp o α) = (j o : B a b) * emb α
  ideal : LPLeftIdeal S
  range_eq : (ideal.val.lattice : Set (B a b)) = Set.range emb

/-- **Printed candidate, UNVERIFIED; invertibility clause.** Voight, Theorem
42.3.2, p. 791 (proved pp. 791–792), in the setting (42.3.1): `F = F_p^al`,
`E₀` any fixed supersingular curve, `O₀ := End(E₀)`. Print, typo included:
"The association E ↦ Hom(E, E₀) is functorial and defines and equivalence
between the category of supersingular elliptic curves over F, under isogenies
and invertible left O₀-modules, under nonzero left O₀-module homomorphisms."
("defines and" is a printed typo for "defines an".) Stated through the standard
characterization of an equivalence; this is the clause "Hom(E, E₀) is an
invertible left O₀-module", kept as printed and unrestricted (the proof takes it
from Lemma 42.1.11 with `E′ = E₀`). Invertibility is represented by
`HomPlacement` in any presentation `(S, j)` of `O₀`. -/
def VoightThm4232Invertible : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k), IsSupersingular E₀ →
    ∀ (a b : ℚ) (S : Order a b) (j : E₀.End ≃+* S.ring) (E : PkgI3.AbVar k),
      IsSupersingular E → Nonempty (HomPlacement S j E)

/-- **Printed candidate, UNVERIFIED; bijection clause in separable scope.**
Voight, Theorem 42.3.2, p. 791 (print quoted at `VoightThm4232Invertible`).
The functor is fully faithful: `φ ↦ φ*` is a bijection from nonzero maps
`E → E′` onto nonzero left `O₀`-module maps `Hom(E′, E₀) → Hom(E, E₀)`. In
separable scope it is stated for étale maps only: `φ ↦ φ*` is injective on
étale maps, and every bijective left `O₀`-module map is `φ*` for an étale `φ`.

The bijective-map form follows from the print as follows. Given a bijective
`O₀`-linear `F`, full faithfulness lifts `F` to `φ : E → E′` and `F⁻¹` to
`ψ : E′ → E`. Then `(ψφ)* = φ*ψ* = F F⁻¹ = id = (id)*` and likewise
`(φψ)* = id`, so injectivity of `φ ↦ φ*` on `ψφ` and `id` (and on `φψ` and `id`)
gives `ψφ = id` and `φψ = id`: `φ` is an isomorphism, hence étale.

Reach premises. In separable scope Voight's proof reaches a curve `E` as
`E₀,I` through a separable isogeny `E₀ → E`; the premises
`∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀` and the same for `E′` record that this
part of the proof is relied on, and only narrow where the candidate applies.
The candidate thus carries two representations of "separable isogeny":
`IsSeparableIsogeny` (Silverman §II.2: nonconstant, separable on function
fields) for how `E` and `E′` are reached, and `IsEtaleIsogeny` in the
conclusions.

Separable-scope dependencies (Voight's proof in this scope rests on):
* the reach premise (`SeparableReach E₀` for the ∀-statements, `rX`/`rY` per
  curve); as a statement it is a specialization of Voight p. 786 (GLUE,
  `SeparableIsogenyExists`), and it stays the binder of the part (2) theorems.
  Rating of `SeparableReach`: derivable in Lean from `SilvermanII212PrimeModel`
  (UNVERIFIED, rating UNCERTAIN) for a reference `A_k` with `A` over `F_q`
  (`separableReach_of_primeModel`, `RC/HCMV21/PrimeModelReach.lean`), together
  with `VoightThm4232Invertible`, `VoightThm4219` and
  `QuaternionRamificationUniqueness`;
* Voight Prop. 42.2.16 (GLUE, Nehrkorn);
* Voight Exercise 16.11 (step 8(b), not built);
* the Silverman III.4.11 reading of Lemma 42.2.7;
* the step of 42.2.21's separable branch "for separable φ, ker φ is étale and
  deg φ = #ker φ is prime to q" (a reading-desk inference: Silverman III.4.10(c),
  and `E₀[q](k) = 0` from Voight 42.1.7(ii), proved there only by citing
  Silverman V.3.1). -/
def VoightThm4232Etale : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k), IsSupersingular E₀ →
    ∀ E E' : PkgI3.AbVar k, IsSupersingular E → IsSupersingular E' →
      (∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀) → (∃ φ₀' : Hom E₀ E', IsSeparableIsogeny φ₀') →
      (∀ φ ψ : Hom E E', IsEtaleIsogeny φ → IsEtaleIsogeny ψ →
        homPull (E₀ := E₀) φ = homPull ψ → φ = ψ) ∧
      (∀ F : Hom E' E₀ ≃+ Hom E E₀,
        (∀ (o : E₀.End) (α : Hom E' E₀), F (postcomp o α) = postcomp o (F α)) →
          ∃ φ : Hom E E', IsEtaleIsogeny φ ∧ ∀ α, F α = homPull φ α)

/-- **Printed candidate, UNVERIFIED; essential surjectivity in separable scope.**
Voight, Theorem 42.3.2, p. 791 (print quoted at `VoightThm4232Invertible`):
every invertible left `O₀`-module is isomorphic to some `Hom(E, E₀)`. Stated for
invertible integral left ideals of `S` (contained in `S`) containing an integer
prime to `q`, so that `nrd(I)` is prime to `q` and `E[I]` is étale (every left
ideal class has such a representative, `LeftIdeal.exists_integral_primeTo`, so
the full subcategory on these objects is equivalent and the class-set statement
loses nothing). -/
def VoightThm4232EssSurj : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k), IsSupersingular E₀ →
    ∀ (a b : ℚ) (S : Order a b) (j : E₀.End ≃+* S.ring) (I : LPLeftIdeal S),
      I.val.lattice ≤ S.lattice → (∃ m : ℕ, m.Coprime q ∧ (m : B a b) ∈ I.val.lattice) →
        ∃ E : PkgI3.AbVar k, IsSupersingular E ∧ ∃ P : HomPlacement S j E, P.ideal = I

/-- **GLUE; stated, on no path.** For supersingular `E, E′` over `F_q^al` there
is a separable isogeny `E → E′`. Source: the sentence after Lemma 42.1.11,
Voight p. 786 (Springer printing): "In particular, if E, E′ are supersingular
elliptic curves over F_p^al, then there exists a separable isogeny E → E′".
Voight asserts it without proof: the proof after Lemma 42.1.11 covers only the
rank and invertibility, never separability. The conclusion uses the print's
word, `IsSeparableIsogeny`.

Editions. In the Springer printing the sentence is on p. 786. Voight's errata
and addenda (the author's PDF of 2026-08-05, Addenda item 17; UNVERIFIED, one
reader) delete it; in the online v1.0.7u that the manuscript cites
(tex 11241-11245) it is replaced by Cor. 42.2.28 (p. 777). The proof of
Cor. 42.2.28 uses Cor. 42.2.21 (whose inseparable branch goes through 42.2.15 to
the asserted 42.2.4), Lemma 42.2.7 and Exercise 17.5 (Nehrkorn). So the sentence
is GLUE in every Voight version.

Nehrkorn's density argument is not a re-cite candidate: it needs a link between
degree and `nrd` at `q`, which is not printed for a general `Hom`.

Its source-fixed instance `SeparableReach E₀`
(`separableReach_of_separableIsogenyExists`) is the reach binder of the part (2)
theorems; this Prop itself is never a binder of a part (2) theorem. -/
def SeparableIsogenyExists : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E E' : PkgI3.AbVar k), IsSupersingular E → IsSupersingular E' →
      ∃ φ : Hom E E', IsSeparableIsogeny φ

/-- The specialization of `SeparableIsogenyExists` to the source `E₀`. -/
theorem separableReach_of_separableIsogenyExists (hS : SeparableIsogenyExists) {q : ℕ}
    [Fact q.Prime] {k : Type} [Field k] [Algebra (ZMod q) k] [IsAlgClosure (ZMod q) k]
    {E₀ : PkgI3.AbVar k} (h₀ : IsSupersingular E₀) : SeparableReach E₀ :=
  fun E hE => hS q k E₀ E h₀ hE

/-- **Printed candidate, UNVERIFIED; order statement in separable scope.**
Voight, Cor. 42.3.7, p. 792: `End(E) ≃ O_R(I)` under `E ↔ [I]`; the ring
statement rests on Lemma 42.2.9, p. 788 (`ι(End(E_I)) = O_R(I)`). Here `I` is
the image of a placement of `Hom(E, E₀)` (the class `[I]` attached to `E` by the
42.3.2 functor), `O_R(I)` its right order, and the identification sends
`γ ∈ End(E)` to the element `x` with `ι(α ∘ γ) = ι(α) x` for all `α`; that this
is an injective ring map into `O_R(I)` is proved in Lean, and the candidate is
its surjectivity. Separable scope: `I` is integral (contained in `S`) and
contains an integer prime to `q`, so `nrd(I)` is prime to `q`. The right order
of `I` and the element attached to `γ` both change by the same conjugation when
the placement is moved by a right unit, so the statement for one placement of a
class gives it for every placement of that class
(`LeftIdeal.exists_integral_primeTo` supplies an admissible one).

Reach premise. The print gets `End(E)` from Lemma 42.2.9 on `φ_I : E₀ → E_I`,
so applying it to the given `E` needs `E ≅ E_I`: in separable scope `E` is
reached from `E₀` by a separable isogeny. The premise
`∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀` records this and only narrows where the
candidate applies.

Separable-scope dependencies: the reach premise, and the Silverman III.4.11
reading of Lemma 42.2.7 through Lemma 42.2.9.

Status: stated but unused. The order lemma (`exists_endRight_eq_level`) is proved
by inclusion plus maximality (Voight's own proof of Lemma 42.2.9, done on the
placement, ON THE SPOT), from `VoightThm4232Invertible`, `VoightThm4219` and
`QuaternionRamificationUniqueness`. -/
def VoightCor4237 : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k), IsSupersingular E₀ →
    ∀ (a b : ℚ) (S : Order a b) (j : E₀.End ≃+* S.ring) (E : PkgI3.AbVar k),
      IsSupersingular E → (∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀) → ∀ P : HomPlacement S j E,
        P.ideal.val.lattice ≤ S.lattice →
          (∃ m : ℕ, m.Coprime q ∧ (m : B a b) ∈ P.ideal.val.lattice) →
          ∀ x ∈ P.ideal.val.rightRing, ∃ gam : E.End, ∀ α : Hom E E₀,
            P.emb (homPull gam α) = P.emb α * x

end ZInQ.Manuscript.RC.HCMV21
