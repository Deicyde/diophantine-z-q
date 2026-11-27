import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.Defs

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Rigidity at level three from Buzzard's Lemma 2.2 and Milne's Theorem 12.5

Two printed statements over an algebraically closed field, and the fibre form of rigidity at
level three that the level-three moduli argument uses.
-/

attribute [local instance] FEC.grp

/-- Leaf (Buzzard, Lemma 2.2, at `N = 5`, for a full level-5 structure). Over an algebraically
closed field `k` of characteristic prime to `30`, an automorphism of a false elliptic curve
`(A/k, i)` that fixes a full level-5 structure is the identity.

Source: K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §2,
Lemma 2.2, read in the author's preprint (p. 6 of its pagination; the Duke page is not verified):
"Let N ≥ 4 be an integer prime to d, and let k be an algebraically closed field of either
characteristic 0 or of characteristic p prime to Nd. Let (A/k, i) be a false elliptic curve over k,
and let α be a V1(N)-structure on A/k. Then the only automorphism of (A/k, i) which fixes α is the
identity." Here `N = 5`, which is at least 4 and prime to `d = 6`, and the characteristic of `k`
is prime to `Nd = 30`, which is `(30 : k) ≠ 0` (this covers characteristic 0).
Standing hypotheses of Buzzard's §1: `B = (2, -3)_Q` is indefinite (`2 > 0`) and non-split,
ramified exactly at 2 and 3, so `d = 6`; `O = Z⟨1, i, (1+j)/2, (i+k)/2⟩` has reduced discriminant
6, so it is a maximal order (J. Voight, *Quaternion Algebras*, GTM 288, Thm 15.5.5, p. 241). The
identification of `O` with this order is part of the definitions (`LeafQM.O`, `LeafQM.ofInt`). The
leaf assumes `ι` injective, as Buzzard's definition of a false elliptic curve does.
How the `V₁(5)`-structure arises: `IsGenAt 5 A (𝟙 _) P` says that `x̄ ↦ ι(x) P` is an `O`-linear
bijection from `O / 5O` onto the 5-torsion points `A[5](k)`; `ι(x) P` depends only on `x` modulo
`5O`, since `ι(5a) P = 0` by its first clause. Since 5 is invertible in `k`, `A[5]` is finite étale
over `k` (Milne 1986, Prop. 20.7, p. 44), hence constant because `k` is algebraically closed. So
this bijection is an `O`-linear isomorphism of `k`-schemes `(O_D ⊗ Z/5Z)_k ≅ A[5]`, that is, a full
level-5 structure `β` (Buzzard, Def. 1.1, p. 3). For every choice of Buzzard's `κ` the `H`-orbit
of `β` is a `V₁(5)`-structure α (p. 6: "the V1(N)-structure α can be thought of as an orbit of full
level N structures under the action of the group H"). If `θ` fixes `P` then `θ ∘ β = β`, so `θ`
fixes α, and the lemma gives `θ = 1`. -/
def BuzzardLemma22Full5 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k], (30 : k) ≠ 0 →
    ∀ (A : FEC (Spec (CommRingCat.of k))), Function.Injective A.iota →
      ∀ θ : A.F ≅ A.F, IsMonHom θ.hom →
        (∀ a : O, A.iota a ≫ θ.hom.left = θ.hom.left ≫ A.iota a) →
        ∀ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F, IsGenAt 5 A (𝟙 _) P →
          P ≫ θ.hom = P → θ.hom = 𝟙 A.F

/-- Leaf (Milne, Theorem 12.5, on points). Over an algebraically closed field `k`, two
endomorphisms of an abelian surface (a false elliptic curve over `k`; the `O`-action plays no
part) that agree on every point of `l`-power order, for a prime `l` not equal to the
characteristic, are equal.

Source: J. S. Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic
Geometry*, Springer (1986), Theorem 12.5, p. 21 of the author's retyped edition: "For all abelian
varieties A and B, Hom(A,B) is a free Z-module of finite rank ≤ 4 dim A dim B; for each prime
l ≠ char(k), the natural map Z_l ⊗ Hom(A,B) → Hom(T_l A, T_l B) is injective with torsion-free
cokernel." Only the following is used. For `k` separably closed and `l ≠ char k`,
`T_l A = lim A_{l^n}(k)` (ibid., Remark 8.4, p. 14). If `f` and `g` agree on `A_{l^n}(k)` for every
`n`, then `f - g` is zero on every `A_{l^n}(k)`, so `T_l(f - g) = 0`; by the injectivity in the
theorem, `1 ⊗ (f - g) = 0` in `Z_l ⊗ End(A)`; and `End(A)` is a free `Z`-module (printed in the same
theorem), so `End(A) → Z_l ⊗ End(A)` is injective and `f = g`. The difference `f - g` is taken in
the commutative group `End(A)` (ibid., Cor. 2.4, p. 3: the group law on an abelian variety is
commutative; also Cor. 20.2(c), p. 43). -/
def MilneThm125Pts : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : FEC (Spec (CommRingCat.of k))) (l : ℕ), l.Prime →
    (l : k) ≠ 0 → ∀ (f g : A.F ⟶ A.F), IsMonHom f → IsMonHom g →
      (∀ (n : ℕ) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F), x ^ (l ^ n) = 1 →
        x ≫ f = x ≫ g) → f = g

/-- Rigidity at level three on a geometric fibre over `Z[1/30]`: an `O`-linear automorphism of
a false elliptic curve over an algebraically closed field of characteristic prime to `30` that
fixes a point generating its 3-torsion fixes every point. (Proved here from the two leaves above
and Milne's statements; it replaces the composite `SerreRigidityLevel3'`, which went through
Buzzard's principal polarization.) -/
def SerreRigidityFibreZ30 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (_φ : Spec (CommRingCat.of k) ⟶ Z30Base)
    (A : FEC (Spec (CommRingCat.of k))) (θ : A.F ≅ A.F),
    (∀ a : O, A.iota a ≫ θ.hom.left = θ.hom.left ≫ A.iota a) →
    ∀ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F, IsGenAt 3 A (𝟙 _) P →
      P ≫ θ.hom = P → ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.F, x ≫ θ.hom = x

end Y3Buzzard
