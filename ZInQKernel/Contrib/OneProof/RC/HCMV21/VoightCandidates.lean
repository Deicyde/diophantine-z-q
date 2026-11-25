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
containing an integer prime to `q`. This is a specialization of the print. -/

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

/-- A separable isogeny: a finite, étale, surjective homomorphism. For
elliptic curves a separable isogeny is the same as an étale one; this is the
Lean representation of "separable isogeny" used below. -/
def IsEtaleIsogeny {A B : PkgI3.AbVar k} (f : Hom A B) : Prop :=
  IsFinite f.hom.left ∧ Etale f.hom.left ∧ Surjective f.hom.left

/-- **Representation choice for "invertible left `O₀`-module".** Given a
presentation `j : End(E₀) ≃+* S.ring` of `O₀` as an order `S` of `(a, b)_ℚ`,
`Hom(E, E₀)` is invertible when it embeds additively and `O₀`-linearly into
`B = (a, b)_ℚ` with image a locally principal full left ideal of `S`. Such an
embedding gives the `ℤ`-basis of rank four used in the Tate comparison. -/
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
étale maps, and every bijective left `O₀`-module map is `φ*` for an étale `φ`
(isomorphisms are étale). It reaches an arbitrary `E` only through an étale
isogeny `E₀ → E`, which is `SeparableIsogenyExists` (GLUE), never this
candidate. -/
def VoightThm4232Etale : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k), IsSupersingular E₀ →
    ∀ E E' : PkgI3.AbVar k, IsSupersingular E → IsSupersingular E' →
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

/-- **GLUE.** For supersingular `E, E′` over `F_q^al` there is a separable
isogeny `E → E′`. Source: the sentence after Lemma 42.1.11, Voight p. 786:
"In particular, if E, E′ are supersingular elliptic curves over F_p^al, then
there exists a separable isogeny E → E′". Voight asserts it without proof: the
proof after Lemma 42.1.11 covers only the rank and invertibility, never
separability. Re-cite candidate: Nehrkorn (Deuring, Algebren, 1935, p. 106)
through a density argument, pending the owner's page check. -/
def SeparableIsogenyExists : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E E' : PkgI3.AbVar k), IsSupersingular E → IsSupersingular E' →
      ∃ φ : Hom E E', IsEtaleIsogeny φ

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
(`LeftIdeal.exists_integral_primeTo` supplies an admissible one). -/
def VoightCor4237 : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (ZMod q) k]
    [IsAlgClosure (ZMod q) k] (E₀ : PkgI3.AbVar k), IsSupersingular E₀ →
    ∀ (a b : ℚ) (S : Order a b) (j : E₀.End ≃+* S.ring) (E : PkgI3.AbVar k),
      IsSupersingular E → ∀ P : HomPlacement S j E,
        P.ideal.val.lattice ≤ S.lattice →
          (∃ m : ℕ, m.Coprime q ∧ (m : B a b) ∈ P.ideal.val.lattice) →
          ∀ x ∈ P.ideal.val.rightRing, ∃ gam : E.End, ∀ α : Hom E E₀,
            P.emb (homPull gam α) = P.emb α * x

end ZInQ.Manuscript.RC.HCMV21
