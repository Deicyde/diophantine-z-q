import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OrderMod
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ActionRelation
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Printed leaves, second batch (statements only)

Adjusted leaves B1', B2' (frame torsor), B3', B4'' (zero-preserving maps are
homomorphisms), the projectivity leaf B6 and the
descent leaves B7(a) to B7(d), with projective space over `Z[1/30]` as `Proj` of a
polynomial ring. Every leaf is a `def ... : Prop`; nothing here is proved, except that the
descent leaf B7(a) is discharged by the Mathlib lemma it restates.

Sources: K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997);
J. S. Milne, *Abelian Varieties*, course notes v2.0 (2008); D. Mumford, J. Fogarty,
F. Kirwan, *Geometric Invariant Theory*, 3rd ed. (GIT); A. Grothendieck, EGA II and IV;
P. Deligne and M. Rapoport, *Les schemas de modules de courbes elliptiques* (1973);
The Stacks Project (tags cited per leaf).
-/

/-! ## Projective space over `Z[1/30]` -/

/-- The homogeneous coordinate ring `Z[x_0, ..., x_N]` of projective `N`-space over `Z`.
Source: EGA II, §4.1 (projective space as `Proj` of a polynomial ring); Hartshorne,
*Algebraic Geometry*, II.2. -/
abbrev PNRingZ (N : ℕ) : Type := MvPolynomial (Fin (N + 1)) ℤ

/-- The grading of `PNRingZ N` by total degree. Source: EGA II, §4.1. -/
abbrev PNGradingZ (N : ℕ) : ℕ → Submodule ℤ (PNRingZ N) :=
  MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ

/-- The polynomial ring is a graded algebra for the total-degree grading. Source: EGA II, §2.1
and §4.1; this is the Mathlib grading of `MvPolynomial` by `homogeneousSubmodule`. -/
instance instGradedAlgebraPNZ (N : ℕ) : GradedAlgebra (PNGradingZ N) := by
  first
    | exact inferInstance
    | exact MvPolynomial.gradedAlgebra
    | exact MvPolynomial.weightedGradedAlgebra ℤ (1 : Fin (N + 1) → ℕ)
    | exact MvPolynomial.weightedGradedAlgebra (R := ℤ) (w := (1 : Fin (N + 1) → ℕ))

/-- Projective `N`-space over `Z`: `Proj Z[x_0, ..., x_N]`. Source: EGA II, §4.1. -/
abbrev PNZ (N : ℕ) : Scheme.{0} := AlgebraicGeometry.Proj (PNGradingZ N)

/-- Projective `N`-space over `Z[1/30]`, as the base change of `PNZ N` along
`Spec Z[1/30] ⟶ Spec Z`. Base change commutes with `Proj` of a polynomial ring, so this is
`Proj Z[1/30][x_0, ..., x_N]`. Source: EGA II, (2.8.10) and §4.1. The grading is taken over `Z`
because the submodule grading over the localization `Z[1/30]` meets an instance diamond. -/
noncomputable def PN (N : ℕ) : Scheme.{0} :=
  pullback (specZIsTerminal.from (PNZ N)) (specZIsTerminal.from Z30Base)

/-- The structure map of projective space over `Z[1/30]` to the base. -/
noncomputable def toBase (N : ℕ) : PN N ⟶ Z30Base :=
  pullback.snd _ _

/-- The projection of projective space over `Z[1/30]` to projective space over `Z`. -/
noncomputable def toPNZ (N : ℕ) : PN N ⟶ PNZ N :=
  pullback.fst _ _

/-! ## B1', the moduli scheme with a projective embedding over the base -/

/-- B1'. B1 with the projectivity conjunct made relative: the fine moduli scheme for false
elliptic curves with `V₁(5)`-structure over `Z[1/30]` is proper and smooth of relative
dimension 1, admits a closed immersion into some projective space `PN N` over the base, and
carries a universal family.

Fidelity note: `V15Fibre` does not ask the comparison map `h` to be a homomorphism.
`ι`-compatibility makes `h` unit preserving, and a morphism from an abelian scheme to a group
scheme taking the identity to the identity is a homomorphism (K.-W. Lan, Harvard thesis (2008),
Cor. 1.3.1.6, over an arbitrary base), so the uniqueness clause agrees with Buzzard's.
The last clause says the comparison map is unique. This is the absence of nontrivial
automorphisms of objects of `X_D(U)`, which the proof of Cor. 2.3 establishes (Lem. 2.2 at
geometric points, with Deligne-Rapoport II 1.14 over the base).
`V15` is Buzzard's `V₁(5)`-structure for a choice of his fixed isomorphism `κ` with
`κ(e5) ≡ diag(1, 0)` mod 5: `V₁(5)` is the stabilizer of `diag(0, 1)` under right multiplication,
and Buzzard fixes `κ` arbitrarily, so his results hold for that choice.
Source: K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §2,
read in the author's preprint (Thm 2.1, p. 5, and Cor. 2.3, p. 7, of its pagination; the Duke
pages are UNVERIFIED), at `U = V₁(5)`, where `M_U d = 30`.
Thm 2.1: "X_D(U) is an algebraic stack over Z[1/M_U d].
Moreover, the morphism X_D(U) → Spec(Z[1/M_U d]) is proper and smooth of relative dimension 1."
Cor. 2.3: "X_D(U) is the stack associated to a regular scheme, and the morphism
X_D(U) → Spec(Z[1/M_U d]) is projective." Projective over the affine base gives the closed
immersion into `PN N` (Stacks, Lemma 37.50.1, tag 0B45). -/
def BuzzardThm21Cor23V15' : Prop :=
  ∃ (X : Over Z30Base) (A : FEC X.left) (α : V15 A),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧
    (∃ (N : ℕ) (i : X.left ⟶ PN N), IsClosedImmersion i ∧ i ≫ toBase N = X.hom) ∧
    (∀ (S : Over Z30Base) (A' : FEC S.left) (α' : V15 A'),
      ∃! g : S ⟶ X, V15Fibre A α g.left A' α') ∧
    ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : V15 A') (g : S ⟶ X)
      (h h' : A'.F.left ⟶ A.F.left),
      (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
        α'.Q ≫ h = g.left ≫ α.Q) →
      (IsPullback h' A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h' = h' ≫ A.iota a) ∧
        α'.Q ≫ h' = g.left ≫ α.Q) →
      h = h'

/-! ## B2', the frame scheme as a torsor -/

/-- B2'. B2 together with the torsor structure: the representing scheme `Z` of full
level-`M` frames carries an action `ρ` of `G M = (O / M O)ˣ`, compatible with `ι` through the
chosen lifts `σ`, whose action relation is the kernel pair of `q = i ≫ A.F.hom`.

On generators `P = α(1)` the action `α ↦ α ∘ r_δ` of Buzzard is `P ↦ ι(δ) P`; this is a left
action, matching the composition order of `Aut`. The map `ρ` is determined by the other
clauses (`i` is a monomorphism and `ι(σ g)` preserves generators), so the new content is the
kernel-pair square.
Source: K. Buzzard, Duke Math. J. 87 (1997), §1, the paragraph after Def. 1.1, read in the
author's preprint (pages UNVERIFIED), for M prime to d = 6 and S a Z[1/Md]-scheme: "Then
F_{A/S,M} is represented by a closed subscheme of A[M], and this representing scheme is an étale
(O_D ⊗ Z/MZ)^×-torsor." The paper gives no proof of this sentence. -/
def BuzzardFrameRepTorsor (M : ℕ) : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left),
    ∃ (Z : Scheme.{0}) (i : Z ⟶ A.F.left), IsClosedImmersion i ∧
      AlgebraicGeometry.IsFinite (i ≫ A.F.hom) ∧ AlgebraicGeometry.Etale (i ≫ A.F.hom) ∧
      AlgebraicGeometry.Surjective (i ≫ A.F.hom) ∧
      (∀ (T : Scheme.{0}) (P : T ⟶ A.F.left), (∃ f : T ⟶ Z, f ≫ i = P) ↔ IsGen M A P) ∧
      ∃ ρ : Y3OrderMod.G M →* Aut Z,
        (∀ g : Y3OrderMod.G M, (ρ g).asIso.hom ≫ i = i ≫ A.iota (Y3OrderMod.σ g)) ∧
        IsPullback (Y3QuotientDescent.actS ρ) (Y3QuotientDescent.actT Z (Y3OrderMod.G M))
          (i ≫ A.F.hom) (i ≫ A.F.hom)

/-! ## B3' and B4'', rigidity -/

/-- B3'. B3 without the `IsMonHom` hypothesis, keeping only `ι`-compatibility: an `O`-linear
automorphism of a false elliptic curve that fixes a point generating the three-torsion of a
geometric fibre, in characteristic not 2 or 3, is the identity on that fibre.

Why the hypothesis can be dropped: `ι(0)` is the zero map (by `iota_add`,
`ι(0) = ι(0) * ι(0)` in the group of endomorphisms), so the compatibility at `a = 0`,
precomposed with the unit section, gives `η ≫ θ = η`: `θ` preserves the unit. Over the
algebraically closed field `k`, rigidity then makes `θ` on the fibre a homomorphism: J. S.
Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic Geometry*,
Springer (1986), Cor. 2.2, p. 3:
"Every morphism f : A → B of abelian varieties is the composite of a homomorphism with a
translation." Then Serre's lemma applies: ibid., Prop. 17.5(b), p. 37: "For any integer n ≥ 3,
an automorphism of (A, λ) acting as the identity on A_n(k̄) is equal to the identity." (Pages
of the author's retyped edition; the 1986 printing's pages are UNVERIFIED. The same statements
are Cor. 1.2, p. 9, and Prop. 14.4(b), p. 62, of Milne's course notes v2.0 (2008).) Here `λ` is
the canonical principal polarization of K. Buzzard, Duke Math. J. 87 (1997), §1 (p. 3 of the
author's preprint): the unique principal polarization whose Rosati involution induces `∗` on
`O`. An `O`-linear automorphism `θ` preserves it, since `θ^∨ λ θ` is again such a polarization.
Fixing a generator of the 3-torsion and commuting with `O`, `θ` acts as the identity on the
3-torsion. -/
def SerreRigidityLevel3' : Prop :=
  ∀ (S : Scheme.{0}) (A : FEC S),
    ∀ θ : A.F ≅ A.F,
      (∀ a : O, A.iota a ≫ θ.hom.left = θ.hom.left ≫ A.iota a) →
      ∀ (k : Type) [Field k] [IsAlgClosed k], ringChar k ≠ 2 → ringChar k ≠ 3 →
        ∀ (s : Spec (CommRingCat.of k) ⟶ S) (P : Over.mk s ⟶ A.F),
          IsGenAt 3 A s P → P ≫ θ.hom = P → ∀ x : Over.mk s ⟶ A.F, x ≫ θ.hom = x

/-- B4''. A morphism of abelian schemes carrying the zero section to the zero section is a
homomorphism, stated for false elliptic curves over any base.
Source: K.-W. Lan, Harvard thesis (2008), Cor. 1.3.1.6 (citing GIT, Cor. 6.4), over an arbitrary
base. Also J. S. Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.),
*Arithmetic Geometry*, Springer (1986), Section 20, Cor. 20.2(a) (p. 43 of the author's retyped
edition), proved from the rigidity lemma Prop. 20.1, which is stated for a connected base. -/
def ZeroPreservingIsHom : Prop :=
  ∀ (S : Scheme.{0}) (A A' : FEC S) (f : A.F ⟶ A'.F),
    letI := A.grp
    letI := A'.grp
    (MonObj.one : 𝟙_ (Over S) ⟶ A.F) ≫ f = MonObj.one → IsMonHom f

/-! ## B6, projectivity of false elliptic curves over a projective base -/

/-- B6. If `X` over `Z[1/30]` admits a closed immersion into some projective space over the
base, then the total space of every false elliptic curve over `X` admits a closed immersion
into some projective space.

Source chain, each step a printed statement:
1. K. Buzzard, Duke Math. J. 87 (1997), §1, p. 3 of the author's preprint: "if (A/S, i) is a
   false elliptic curve, then there
   is a unique principal polarisation on A such that if s is a geometric point of S, then the
   corresponding Rosati involution on End(A_s) induces ∗ on O_D";
2. K.-W. Lan, Harvard thesis (2008), Prop. 1.3.2.18 with Def. 1.3.2.20: for a polarization `λ`
   the invertible sheaf `(Id_A, λ)^* P_A` is relatively ample (the 2021 revision of the thesis,
   Prop. 1.3.2.15 and Def. 1.3.2.16, prints "relatively ample over S"). Buzzard's polarization
   is one: at geometric points it is `λ_L` with `L` ample
   (J. S. Milne, *Abelian Varieties* (1986), Section 20, p. 46), and it is symmetric by
   Lan, Lemma 1.3.2.16, and rigidity, Lan, Cor. 1.3.1.5, on connected components;
3. Stacks, Lemma 29.40.4 (tag 01VT): `O_X(1)` is ample on `X`, as `Spec Z[1/30]` is affine;
4. Stacks, Lemma 29.38.8 (tag 0C4K): `(Id_A, λ)^* P_A ⊗ f^* O_X(1)^{⊗ a}` is ample relative to
   `Spec Z[1/30]` for `a ≫ 0`;
5. Stacks, Lemma 37.50.1 (tag 0B45): `A → Spec Z[1/30]` is proper with a relatively ample
   sheaf, hence H-projective: it has a closed immersion into some `P^N` over `Z[1/30]`. -/
def ProjectiveFEC : Prop :=
  ∀ X : Over Z30Base,
    (∃ (N : ℕ) (i : X.left ⟶ PN N), IsClosedImmersion i ∧ i ≫ toBase N = X.hom) →
      ∀ A : FEC X.left, ∃ (N' : ℕ) (j : A.F.left ⟶ PN N'), IsClosedImmersion j

/-! ## B7, descent statements -/

/-- B7(a). Universal closedness descends along a surjection: if `f` is surjective and
`f ≫ q` is universally closed, then `q` is universally closed.
Source: Stacks, Morphisms, Lemma 29.42.9, tag 03GN. -/
def DescentUniversallyClosed : Prop :=
  ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z),
    AlgebraicGeometry.Surjective f → UniversallyClosed (f ≫ q) → UniversallyClosed q

/-- B7(a) holds: it is the Mathlib lemma `UniversallyClosed.of_comp_surjective`.
Source: Stacks, Morphisms, Lemma 29.42.9, tag 03GN. -/
theorem descentUniversallyClosed : DescentUniversallyClosed := by
  unfold DescentUniversallyClosed
  intro X Y Z f q hf hfq
  first
    | exact UniversallyClosed.of_comp_surjective f q
    | exact UniversallyClosed.of_comp_surjective (f := f) (g := q)
    | exact AlgebraicGeometry.universallyClosed_of_comp_surjective f q

/-- B7(b). Smoothness of relative dimension `n` descends along an étale surjection: if `f` is
étale and surjective and `f ≫ q` is smooth of relative dimension `n`, then so is `q`.
Source: Stacks, Descent, Lemma 35.14.4, tag 02KM (smoothness descends along surjective
smooth, in particular étale, maps), and Lemma 35.14.5, tag 05B5 (along surjective flat
locally finitely presented maps); smoothness is smooth local on the source, Lemma 35.30.1,
tag 036U. The relative dimension is preserved because an étale map does not change the
dimension of fibres (Stacks, Morphisms, Section 29.28, tag to be verified). -/
def DescentSmoothOfRelativeDimension : Prop :=
  ∀ (n : ℕ) (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z),
    AlgebraicGeometry.Etale f → AlgebraicGeometry.Surjective f →
      SmoothOfRelativeDimension n (f ≫ q) → SmoothOfRelativeDimension n q

/-- B7(c), finite presentation. If `f` is flat, surjective and locally of finite
presentation and `f ≫ q` is locally of finite presentation, then so is `q`.
Source: Stacks, Descent, Lemma 35.14.3, tag 02KL (after EGA IV 17.7.5); the property is
fppf local on the source, Lemma 35.28.1, tag 036N. -/
def DescentLocallyOfFinitePresentation : Prop :=
  ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z),
    AlgebraicGeometry.Flat f → AlgebraicGeometry.Surjective f →
      LocallyOfFinitePresentation f → LocallyOfFinitePresentation (f ≫ q) →
        LocallyOfFinitePresentation q

/-- B7(c), finite type. If `f` is flat, surjective and locally of finite presentation and
`f ≫ q` is locally of finite type, then so is `q`.
Source: Stacks, Descent, Lemma 35.14.3, tag 02KL (the finite type case, after
EGA IV 17.7.5); the property is fppf local on the source, Lemma 35.28.2, tag 036O. -/
def DescentLocallyOfFiniteType : Prop :=
  ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z),
    AlgebraicGeometry.Flat f → AlgebraicGeometry.Surjective f →
      LocallyOfFinitePresentation f → LocallyOfFiniteType (f ≫ q) →
        LocallyOfFiniteType q

/-- B7(d). Being a closed immersion is fppf local on the base, stated for a single flat,
surjective, locally finitely presented base change `g` (an fppf covering by one map): if the
base change of `q` along `g` is a closed immersion, then `q` is a closed immersion.
Source: Stacks, Descent, Lemma 35.23.21, tag 02L6 (fpqc local on the base, hence fppf local);
see also Remark 65.4.3, tag 02WH, item 1. -/
def DescentClosedImmersion : Prop :=
  ∀ (X Y Y' : Scheme.{0}) (q : X ⟶ Y) (g : Y' ⟶ Y),
    AlgebraicGeometry.Flat g → AlgebraicGeometry.Surjective g →
      LocallyOfFinitePresentation g → IsClosedImmersion (pullback.snd q g) →
        IsClosedImmersion q

/-! ## The bundle -/

/-- The second batch of printed leaves, bundled: B1', the frame torsor B2' at `M = 3` and
`M = 5`, B3', B4'', B6 and the descent leaves B7(a) to B7(d). Sources as in each leaf. -/
def Y3PrintedLeaves : Prop :=
  BuzzardThm21Cor23V15' ∧ BuzzardFrameRepTorsor 3 ∧ BuzzardFrameRepTorsor 5 ∧
    SerreRigidityLevel3' ∧ ZeroPreservingIsHom ∧ ProjectiveFEC ∧
    DescentUniversallyClosed ∧ DescentSmoothOfRelativeDimension ∧
    DescentLocallyOfFinitePresentation ∧ DescentLocallyOfFiniteType ∧
    DescentClosedImmersion

end Y3Buzzard
