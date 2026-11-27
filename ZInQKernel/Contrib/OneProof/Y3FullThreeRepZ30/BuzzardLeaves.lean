import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard
import ZInQKernel.Contrib.OneProof.ShimuraY3PrintedLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Printed leaves for the level-three representability step (statements only)

Definitions D1 to D5 and the propositions B1 to B4. Every leaf is a `def ... : Prop`;
nothing here is proved. Sources: K. Buzzard, *Integral models of certain Shimura curves*,
Duke Math. J. 87 (1997); J. S. Milne, *Abelian Varieties*, course notes v2.0 (2008);
P. Deligne and M. Rapoport, *Les schemas de modules de courbes elliptiques* (1973).
-/

/-- D1. A false elliptic curve over `S`: a proper smooth geometrically connected group
scheme of relative dimension 2 with a left action of the maximal order `O` of the
quaternion algebra of discriminant 6, without level data.
Source: K. Buzzard, Duke Math. J. 87 (1997), §1, p. 2 of the author's preprint: "A false
elliptic curve over S is a pair (A/S, i) where A/S is an abelian surface (that is, A is an
abelian scheme over S of relative dimension two), and i : O_D ↪ End_S(A) is an injective ring
homomorphism". An abelian scheme
is a proper smooth group scheme with connected geometric fibres (J. S. Milne, *Abelian
Varieties* (1986), Section 20, p. 42). Injectivity of `ι` is automatic over a nonempty base: a
nonzero ideal of `O` contains a nonzero integer `n`, and `ι(n)` is multiplication by `n`, which
is surjective (ibid., Prop. 20.7). `O` is maximal: its reduced discriminant is 6 (J. Voight,
*Quaternion Algebras*, GTM 288, Thm. 15.5.5). -/
structure FEC (S : Scheme.{0}) where
  F : Over S
  proper : IsProper F.hom
  smooth : SmoothOfRelativeDimension 2 F.hom
  iota : O → (F.left ⟶ F.left)
  iota_over : ∀ a : O, iota a ≫ F.hom = F.hom
  [grp : GrpObj F]
  geomConn : GeometricallyConnected F.hom
  iota_hom : ∀ a : O, IsMonHom (Over.homMk (iota a) (iota_over a) : F ⟶ F)
  iota_one : iota 1 = 𝟙 _
  iota_mul : ∀ a b : O, iota (a * b) = iota b ≫ iota a
  iota_add : ∀ a b : O, (Over.homMk (iota (a + b)) (iota_over _) : F ⟶ F) =
    Over.homMk (iota a) (iota_over a) * Over.homMk (iota b) (iota_over b)

/-- D1, forgetful map. The false elliptic curve underlying a level-three family: forget the
sections `eta`. Source: Buzzard 1997, §1, Def. 1.1 (a full level structure is extra data on
the false elliptic curve). -/
def _root_.Y3Fix.QMAbSchemeNL.toFEC {S : Scheme.{0}} (𝒜 : Y3Fix.QMAbSchemeNL S) : FEC S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota := 𝒜.iota
  iota_over := 𝒜.iota_over
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  iota_hom := 𝒜.iota_hom
  iota_one := 𝒜.iota_one
  iota_mul := 𝒜.iota_mul
  iota_add := 𝒜.iota_add

/-- D2, at a geometric point. A `k`-point `P` of `A` over `s` generates the `M`-torsion of the
fibre: `a ↦ ι(a) P` induces a bijection from `O / M O` onto the `M`-torsion points over `s`.
A full level-`M` structure `α` is determined by `P = α(1)` by `O`-linearity.
Source: Buzzard 1997, §1, Def. 1.1. -/
def IsGenAt (M : ℕ) {S : Scheme.{0}} (A : FEC S) {k : Type} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (P : Over.mk s ⟶ A.F) : Prop :=
  letI := A.grp
  (∀ a : O, P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F) = 1 ↔
      ∃ b : O, a = (M : O) * b) ∧
    ∀ x : Over.mk s ⟶ A.F, x ^ M = 1 →
      ∃ a : O, x = P ≫ (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F)

/-- D2. `P` is a generator of a full level-`M` structure: `P` is `M`-torsion and generates the
`M`-torsion at every geometric point of `T`.
Source: Buzzard 1997, §1, Def. 1.1. -/
def IsGen (M : ℕ) {S : Scheme.{0}} (A : FEC S) {T : Scheme.{0}} (P : T ⟶ A.F.left) : Prop :=
  letI := A.grp
  (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1 ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsGenAt M A (s ≫ P ≫ A.F.hom)
      (Over.homMk (U := Over.mk (s ≫ P ≫ A.F.hom)) (s ≫ P) (Category.assoc _ _ _))

/-- D3. The element `3 + 2k` of `O`, written `ofInt ![3, -2, 0, 4]`. Its reduced trace is 6
and its reduced norm is -15, so it reduces to a rank-one idempotent of `O / 5 O`, which is
used to state the level structure `V₁(5)` concretely.
Source: Buzzard 1997, §1, Def. 1.2 (the fixed isomorphism of `O ⊗ Z_5` with `M₂(Z_5)`). -/
def e5 : O := ⟨ofInt ![3, -2, 0, 4], show InO (ofInt ![3, -2, 0, 4]) from ⟨![3, -2, 0, 4], rfl⟩⟩

/-- D4. A `V₁(5)`-structure on `A` in concrete form: a section `Q` of order dividing 5, killed
by `ι(e5)`, and nonzero at every geometric point of `S`.
Source: Buzzard 1997, §1, Def. 1.2 at `U = V₁(5)`. -/
structure V15 {S : Scheme.{0}} (A : FEC S) where
  Q : S ⟶ A.F.left
  Q_sec : Q ≫ A.F.hom = 𝟙 S
  order : letI := A.grp
    (Over.homMk (U := 𝟙_ (Over S)) Q Q_sec : 𝟙_ (Over S) ⟶ A.F) ^ 5 = 1
  inKer : letI := A.grp
    (Over.homMk (U := 𝟙_ (Over S)) (Q ≫ A.iota e5)
        (by rw [Category.assoc, A.iota_over]; exact Q_sec) : 𝟙_ (Over S) ⟶ A.F) = 1
  nonzero : letI := A.grp
    ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      (Over.homMk (s ≫ Q)
          (by simp only [Category.assoc, Q_sec, Category.comp_id, Over.mk_hom] <;> rfl) :
          Over.mk s ⟶ A.F) ≠ 1

/-- D5. `A'` over `S'` is the base change of `A` along `g`, compatibly with the `O`-actions.
Source: Buzzard 1997, §1, Def. 1.2 (the moduli functor and its base change). -/
def FECFibre {S : Scheme.{0}} (A : FEC S) {S' : Scheme.{0}} (g : S' ⟶ S) (A' : FEC S') :
    Prop :=
  ∃ h : A'.F.left ⟶ A.F.left, IsPullback h A'.F.hom A.F.hom g ∧
    ∀ a : O, A'.iota a ≫ h = h ≫ A.iota a

/-- D5. `(A', α')` over `S'` is the base change of `(A, α)` along `g`: the `O`-compatible
cartesian square also carries the section `α'.Q` to `α.Q`.
Source: Buzzard 1997, §1, Def. 1.2 at `U = V₁(5)`. -/
def V15Fibre {S : Scheme.{0}} (A : FEC S) (α : V15 A) {S' : Scheme.{0}} (g : S' ⟶ S)
    (A' : FEC S') (α' : V15 A') : Prop :=
  ∃ h : A'.F.left ⟶ A.F.left, IsPullback h A'.F.hom A.F.hom g ∧
    (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧ α'.Q ≫ h = g ≫ α.Q

/-- The base `Spec Z[1/30]`. For `U = V₁(5)` and discriminant 6, the base `Z[1/(M_U d)]` of
Buzzard 1997, §2, Thm 2.1 is `Z[1/30]`. -/
abbrev Z30Base : Scheme.{0} := Spec (CommRingCat.of Y3RouteA.Z30)

/-- B1. The fine moduli scheme for false elliptic curves with `V₁(5)`-structure over
`Z[1/30]`: it exists, is proper and smooth of relative dimension 1, embeds as a closed
subscheme of a `Proj`, and carries a universal family.
Source: Buzzard 1997, §2, Thm 2.1 and Cor. 2.3, at `U = V₁(5)`. -/
def BuzzardThm21Cor23V15 : Prop :=
  ∃ (X : Over Z30Base) (A : FEC X.left) (α : V15 A),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧
    (∃ (R : Type) (_ : CommRing R) (𝒜 : ℕ → AddSubgroup R) (_ : GradedRing 𝒜)
        (i : X.left ⟶ AlgebraicGeometry.Proj 𝒜), IsClosedImmersion i) ∧
    ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : V15 A'),
      ∃! g : S ⟶ X, V15Fibre A α g.left A' α'

/-- B2. Full level-`M` frames on a false elliptic curve over a `Z[1/30]`-scheme are
represented by a closed subscheme of `A`, finite, étale and surjective over the base, whose
points are exactly the generators of full level-`M` structures.
Source: Buzzard 1997, §1, the paragraph after Def. 1.1 (representability of full level
structures). -/
def BuzzardFrameRep (M : ℕ) : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left),
    ∃ (Z : Scheme.{0}) (i : Z ⟶ A.F.left), IsClosedImmersion i ∧
      AlgebraicGeometry.IsFinite (i ≫ A.F.hom) ∧ AlgebraicGeometry.Etale (i ≫ A.F.hom) ∧
      AlgebraicGeometry.Surjective (i ≫ A.F.hom) ∧
      ∀ (T : Scheme.{0}) (P : T ⟶ A.F.left), (∃ f : T ⟶ Z, f ≫ i = P) ↔ IsGen M A P

/-- B3. Rigidity at full level three on geometric fibres, in characteristic not 2 or 3: an
`O`-linear automorphism of a false elliptic curve that fixes a point generating the
three-torsion of a geometric fibre is the identity on that fibre.
This is Serre's lemma for the fibre over `s`: J. S. Milne, *Abelian Varieties*, course notes v2.0
(2008), Prop. 14.4(b), p. 62, with Buzzard 1997, §1 (uniqueness of the canonical principal
polarization, so `O`-linear automorphisms preserve it; this needs 6 invertible). -/
def SerreRigidityLevel3 : Prop :=
  ∀ (S : Scheme.{0}) (A : FEC S),
    letI := A.grp
    ∀ θ : A.F ≅ A.F, IsMonHom θ.hom →
      (∀ a : O, A.iota a ≫ θ.hom.left = θ.hom.left ≫ A.iota a) →
      ∀ (k : Type) [Field k] [IsAlgClosed k], ringChar k ≠ 2 → ringChar k ≠ 3 →
        ∀ (s : Spec (CommRingCat.of k) ⟶ S) (P : Over.mk s ⟶ A.F),
          IsGenAt 3 A s P → P ≫ θ.hom = P → ∀ x : Over.mk s ⟶ A.F, x ≫ θ.hom = x

/-- B4. Rigidity over a base: an endomorphism of group schemes of a false elliptic curve
that is the identity on every geometric point is the identity.
Source: Deligne-Rapoport, II 1.14, as cited in Buzzard 1997, §2, proof of Cor. 2.3. -/
def RigidityOverBase : Prop :=
  ∀ (S : Scheme.{0}) (A : FEC S),
    letI := A.grp
    ∀ θ : A.F ⟶ A.F, IsMonHom θ →
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S)
          (x : Over.mk s ⟶ A.F), x ≫ θ = x) →
        θ = 𝟙 _

end Y3Buzzard
