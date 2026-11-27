import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.LitFrames
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Kappa5
import Mathlib

/-!
# The literal leaf for `X^D(V₁(5))`

Source: K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §§1–2,
read in the author's preprint; page numbers are those of the preprint. Quotations are verbatim,
with subscripts and superscripts transcribed.

The leaf `BuzzardXDV15Lit` states Buzzard's Thm 2.1 and Cor. 2.3 at `U = V₁(5)` (so `M_U = 5`,
`d = 6` and `M_U d = 30`) with his own definitions, as far as Mathlib allows:

* literal naive full level-5 structures `LitFrame` (Def. 1.1, p. 3), with his left action
  `α ↦ α ∘ r_δ` (pp. 3–4);
* the group `H = V15Group`, the image of `V₁(5)` in `(O/5O)ˣ` (§2, p. 4), through the fixed
  isomorphism `κ` given by `kappa5`;
* the orbit spaces `H\F_{A/S,5}(T)` and their étale sheafification `F_{A/S,H}` on `S`-schemes
  (p. 4), and level structures as elements of `F_{A/S,H}(S)` (Def. 1.2, p. 4);
* the morphisms of the category `X^D(U)` (p. 5), and Thm 2.1 with Cor. 2.3 in fine-moduli form.

The theorem `buzzardXDV15_of_lit` shows that, given Milne's Prop. 20.7 at `n = 5`, the literal
leaf implies the generator-encoded leaf `BuzzardXDV15`: evaluation of literal frames at `1`
identifies the two orbit presheaves, hence their sheafifications, the level structures and the
morphism conditions.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite
open LeafQM LeafQM.AV

namespace Y3Buzzard.XDV15

/-! ## 1. The group `H = u₅(V₁(5))` -/

/-- Buzzard's matrix group for `V₁(5)`. Buzzard, §2, p. 4: "Let V₁(M) denote the preimage of
{(a b; c d) ∈ GL₂(ℤ/Mℤ) | c = 0 and d = 1} under u_M." This is that set of matrices at `M = 5`,
a subgroup of `GL₂(ℤ/5ℤ)`. -/
def V1GL5 : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) where
  carrier := {γ | (γ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0 ∧
    (γ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1}
  mul_mem' {γ γ'} hγ hγ' := by
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨h3, h4⟩ := hγ'
    refine ⟨?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  inv_mem' {γ} hγ := by
    obtain ⟨h1, h2⟩ := hγ
    have e := Units.mul_inv γ
    have e10 := congrFun (congrFun e 1) 0
    have e11 := congrFun (congrFun e 1) 1
    exact ⟨by simpa [Matrix.mul_apply, Fin.sum_univ_two, h1, h2] using e10,
      by simpa [Matrix.mul_apply, Fin.sum_univ_two, h1, h2] using e11⟩

/-- The isomorphism `κ` on units, `(O/5O)ˣ ≃* GL₂(ℤ/5ℤ)`, `δ ↦ κ(δ)` with `κ = kappa5⁻¹`.

Buzzard, p. 2: "Fix once and for all an isomorphism κ : O_D ⊗_Z R → M_2(R)", where `R` is the
limit of `ℤ/Mℤ` over `M` prime to `d`, that is `∏_{p ∤ 6} ℤ_p`. Here `κ` mod 5 is fixed through
`kappa5`: it sends the classes of `E = e5`, `X`, `Y`, `1 - E` to the matrix units `e₁₁`, `e₁₂`,
`e₂₁`, `e₂₂`, so `κ(E) = e₁₁`. This is the reduction of an admissible `κ`: a ring isomorphism
`O/5O ≅ M₂(F₅)` differs from the reduction of a given `κ` by a ring automorphism of `M₂(F₅)`,
which is `F₅`-linear (`F₅` is the prime field) and hence inner (Skolem–Noether); lifting its
conjugating matrix to `GL₂(ℤ₅)`, and taking the identity at the other primes of `R`, gives an
admissible `κ` whose reduction mod 5 is `kappa5.symm`. Buzzard's results hold for every `κ`. -/
def kappaGL5 : Y3OrderMod.G 5 ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) :=
  Units.mapEquiv kappa5.symm.toMulEquiv

/-- Buzzard's group `H = u₅(V₁(5)) ⊂ (O/5O)ˣ` (§2, p. 4): the units `δ` such that `κ(δ)` is of
the form `(a b; 0 1)`, i.e. the preimage of `V1GL5` under `κ`. As `u₅` is surjective, this is the
image of `V₁(5)`, and `V₁(5)` is the preimage of `H` (Def. 1.2 "depends only on U"). -/
def V15Group : Subgroup (Y3OrderMod.G 5) := V1GL5.comap kappaGL5.toMonoidHom

/-- Membership in `H`: the second row of `κ(δ)` is `(0, 1)`. -/
theorem mem_V15Group_iff (δ : Y3OrderMod.G 5) :
    δ ∈ V15Group ↔ kappa5.symm (δ : Y3OrderMod.OMod 5) 1 0 = 0 ∧
      kappa5.symm (δ : Y3OrderMod.OMod 5) 1 1 = 1 := Iff.rfl

/-- Membership in `H`, in Buzzard's form: `κ(δ) = (a b; 0 1)` for some `a`, `b`. -/
theorem mem_V15Group_iff_exists (δ : Y3OrderMod.G 5) :
    δ ∈ V15Group ↔ ∃ a b : ZMod 5,
      kappa5.symm (δ : Y3OrderMod.OMod 5) = Matrix.of ![![a, b], ![0, 1]] := by
  rw [mem_V15Group_iff]
  constructor
  · rintro ⟨h10, h11⟩
    refine ⟨kappa5.symm (δ : Y3OrderMod.OMod 5) 0 0, kappa5.symm (δ : Y3OrderMod.OMod 5) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h11]
  · rintro ⟨a, b, h⟩
    rw [h]
    simp

/-- `H` is the group `H5` of the generator-encoded leaf. -/
theorem V15Group_eq_H5 : V15Group = H5 := by
  ext δ
  rw [mem_V15Group_iff, mem_H5_iff]

/-! ## 2. The action and the orbit spaces `H\F_{A/S,5}(T)` -/

/-- Buzzard's left action on literal full level-5 structures (pp. 3–4): "The map α ↦ α ∘ r_δ
defines a left action of (O_D ⊗ ℤ/Mℤ)^× on the set of full level M structures on A." Here
`δ • α = α ∘ r_δ = LitFrame.act α δ`, with `r_δ` the right multiplication `q ↦ q δ` on the
constant scheme `(O/5O)_T`.

The literal frames are those of `LitFrame`, after Def. 1.1 (p. 3): "A naïve full level M
structure on a false elliptic curve (A/S, i) is an isomorphism α : (O_D ⊗ ℤ/Mℤ)_S ≅ A[M] of
schemes which preserves the left action of O_D." -/
instance litFrameAction {S : Scheme.{0}} {A : FEC S} {T : Over S} :
    MulAction (Y3OrderMod.G 5) (LitFrame A T) where
  smul δ x := x.act δ
  one_smul x := x.act_one
  mul_smul δ ε x := (x.act_act ε δ).symm

section Orbits

variable {S : Scheme.{0}} (A : FEC S)

/-- The functor `T ↦ H\F_{A/S,5}(T)` on `S`-schemes, for `H = V15Group`. Buzzard, p. 4:
"Consider the contravariant functor F_{A/S,M} from S-schemes to sets, sending T/S to the set of
full level M structures on A_T. ... If H\F_{A/S,M}(T) denotes the orbit space, then define
F_{A/S,H} to be the sheafification with respect to the étale topology of the functor
T ↦ H\F_{A/S,M}(T) from S-schemes to sets."

`F_{A/S,5}` is `LitFrames5 A`, with restriction along `T' ⟶ T` by precomposition; its value at
`T` is the set `LitFrame A T`, and the value here is the orbit space of the action of `H` on it.
The representability statements of the same paragraph (a closed subscheme of `A[M]`, an étale
torsor, a quotient finite étale over `S`) are results, not definitions, and are not used. -/
def LitOrbitsV : (Over S)ᵒᵖ ⥤ Type where
  obj T := MulAction.orbitRel.Quotient V15Group (LitFrame A T.unop)
  map {T T'} f := ↾(Quot.map (fun x : LitFrame A T.unop => x.restrict f.unop) (by
    rintro x _ ⟨δ, rfl⟩
    exact ⟨δ, LitFrame.ext rfl⟩))
  map_id T := by
    ext q
    induction q using Quot.ind with
    | mk x => exact congrArg (Quot.mk _) (LitFrame.ext (funext fun q => Category.id_comp (x.α q)))
  map_comp f g := by
    ext q
    induction q using Quot.ind with
    | mk x =>
      exact congrArg (Quot.mk _) (LitFrame.ext (funext fun q => Category.assoc g.unop f.unop _))

/-- `F_{A/S,H}` as a presheaf on `S`-schemes (Buzzard, p. 4, quoted at `LitOrbitsV`): the étale
sheafification of `T ↦ H\F_{A/S,5}(T)`, for the étale topology `etaleOver S` on `S`-schemes. The
orbit spaces are lifted to `Type 1`, the universe in which Mathlib sheafifies on the large site
`Over S`. -/
abbrev LevelPreLit : (Over S)ᵒᵖ ⥤ Type 1 :=
  sheafify (etaleOver S) (LitOrbitsV A ⋙ uliftFunctor.{1, 0})

/-- Def. 1.2 (p. 4): "A naïve level H structure on (A/S, i) is an element of F_{A/S,H}(S)."
Buzzard writes `F_{A/S,U}` for `F_{A/S,H}` when `U` is the preimage of `H`; here `U = V₁(5)`. -/
abbrev LevelStrLit : Type 1 :=
  (LevelPreLit A).obj (op (Over.mk (𝟙 S)))

end Orbits

/-! ## 3. Morphisms of `X^D(U)` and the leaf -/

/-- The third bullet of the morphisms of `X^D(U)` (p. 5), with literal level structures.

Buzzard, p. 5: the objects of `X^D(U)` are false elliptic curves `(A/S/ℤ[1/M_U d], i_A)` with
`α ∈ F_{A/S,U}(S)`, and a morphism from `(A/S, α)` to `(B/T, β)` is a square `A → B` over
`S → T` such that
* "The induced morphism A → B_S = B ×_T S is an isomorphism";
* "The induced map a : End_T(B) → End_S(A) satisfies i_A = a ∘ i_B";
* "α is the image of β under the natural map F_{B/T,U}(T) → F_{B_S/S,U}(S) = F_{A/S,U}(S)".

For the square `h : A' → A` over `g : S' ⟶ S` (the first two bullets are `IsPullback` and
`O`-linearity of `h` in `BuzzardXDV15Lit`), the third bullet says: there is an isomorphism of
étale sheaves `ψ : F_{A'/S',H} ≅ F_{A_{S'}/S',H}` (the target being `F_{A/S,H}` restricted to
`S'`-schemes along `g`) induced by the transport of literal frames `α ↦ (q ↦ h ∘ α q)`, and it
carries `α'` to the restriction of `α` along `g`.

Why a cartesian, `O`-linear `h` is what the first two bullets ask for: `O`-linearity at `a = 0`
gives `h ∘ e' = e ∘ g`, since `ι(0)` is the zero endomorphism, so the induced `S'`-isomorphism
`A' → A ×_S S'` preserves the zero section and is therefore an isomorphism of abelian schemes
(J. S. Milne, *Abelian Varieties* (1986), Cor. 20.2(a), p. 43: "Every morphism of abelian schemes
carrying the zero section into the zero section is a homomorphism", stated in §20 for abelian
schemes over any scheme `S`). Milne proves 20.2 through the rigidity of his Prop. 20.1; a proof
over an arbitrary base is in Mumford's GIT, Cor. 6.4, which is not read here. Hence the uniqueness
clauses of `BuzzardXDV15Lit` quantify over exactly Buzzard's morphisms. -/
def LevelFibreLit {S S' : Scheme.{0}} (A : FEC S) (α : LevelStrLit A) (g : S' ⟶ S) (A' : FEC S')
    (α' : LevelStrLit A') (h : A'.F.left ⟶ A.F.left) : Prop :=
  ∃ ψ : LevelPreLit A' ≅ (Over.map g).op ⋙ LevelPreLit A,
    (∀ (T : Over S') (x' : LitFrame A' T) (x : LitFrame A ((Over.map g).obj T)),
        (∀ q, (x.α q).left = (x'.α q).left ≫ h) →
        ψ.hom.app (op T) ((toSheafify (etaleOver S') (LitOrbitsV A' ⋙ uliftFunctor.{1, 0})).app
            (op T) (ULift.up (Quot.mk _ x'))) =
          (toSheafify (etaleOver S) (LitOrbitsV A ⋙ uliftFunctor.{1, 0})).app
            (op ((Over.map g).obj T)) (ULift.up (Quot.mk _ x))) ∧
    ψ.hom.app (op (Over.mk (𝟙 S'))) α' =
      (LevelPreLit A).map (Over.homMk (U := (Over.map g).obj (Over.mk (𝟙 S'))) (V := Over.mk (𝟙 S))
        g (by simp)).op α

/-- The literal leaf: Buzzard's Thm 2.1 and Cor. 2.3 at `U = V₁(5)`, base `ℤ[1/M_U d] = ℤ[1/30]`,
with his own level structures.

Thm 2.1 (p. 5): "X^D(U) is an algebraic stack over ℤ[1/M_U d]. Moreover, the morphism
X^D(U) → Spec(ℤ[1/M_U d]) is proper and smooth of relative dimension 1."

Cor. 2.3 (p. 7): "... X^D(U) is the stack associated to a regular scheme, and the morphism
X^D(U) → Spec(ℤ[1/M_U d]) is projective." Its proof: "it suffices by Example 4.9 of [DM] to
show that the objects of the category X^D(U) have no non-trivial automorphisms."

Fine-moduli form. `X^D(U)` is the stack associated to the scheme `X` exactly when there is an
object `(A, α)` over `X` such that every object `(A', α')` over `S` has a morphism to `(A, α)`
over a unique `g : S ⟶ X` (the `∃!` clause), and that morphism is unique given `g` (the last
clause: objects have no non-trivial automorphisms). Morphisms are those of p. 5, see
`LevelFibreLit`.

Dropped: "algebraic stack" (Mathlib has no algebraic stacks; a stack associated to a scheme is
one) and "regular" (it follows from smoothness over the regular base `Spec ℤ[1/30]`, which is
kept). "Projective" is stated as a closed immersion into some `PN N` over the base, as in
`BuzzardThm21Cor23V15'` (Mathlib has no projective morphisms); over the affine base this is EGA's
"projective" (EGA II (5.5.4)(ii), with the ampleness of `O_Y` on an affine scheme `Y`).

The empty base: Buzzard's `i` is injective, which excludes `S = ∅` (`End(∅)` is the zero ring),
while `FEC` admits the empty curve. Over `S = ∅` every clause of the leaf holds trivially (a
unique `g`, a unique `h`, and the sheaves are singletons), so the leaf is not stronger than the
print. -/
def BuzzardXDV15Lit : Prop :=
  ∃ (X : Over Z30Base) (A : FEC X.left) (α : LevelStrLit A),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧
    (∃ (N : ℕ) (i : X.left ⟶ PN N), IsClosedImmersion i ∧ i ≫ toBase N = X.hom) ∧
    (∀ (S : Over Z30Base) (A' : FEC S.left) (α' : LevelStrLit A'),
      ∃! g : S ⟶ X, ∃ h : A'.F.left ⟶ A.F.left, IsPullback h A'.F.hom A.F.hom g.left ∧
        (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧ LevelFibreLit A α g.left A' α' h) ∧
    ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : LevelStrLit A') (g : S ⟶ X)
      (h h' : A'.F.left ⟶ A.F.left),
      (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
        LevelFibreLit A α g.left A' α' h) →
      (IsPullback h' A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h' = h' ≫ A.iota a) ∧
        LevelFibreLit A α g.left A' α' h') →
      h = h'

/-! ## 4. Transport to the generator-encoded leaf -/

section Transport

variable {S : Scheme.{0}} (A : FEC S)

/-- The `H`-orbit relation is `LitOrbRel`, as `V15Group = H5`. -/
theorem orbitRelV_iff (T : (Over S)ᵒᵖ) (x x' : LitFrame A T.unop) :
    MulAction.orbitRel V15Group (LitFrame A T.unop) x x' ↔ LitOrbRel A T x x' := by
  rw [Setoid.comm', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨δ, hδ⟩, h⟩
    exact ⟨δ, V15Group_eq_H5 ▸ hδ, h.symm⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨⟨δ, V15Group_eq_H5 ▸ hδ⟩, h.symm⟩

/-- The orbit presheaves for `V15Group` and for `H5` agree. -/
def litOrbitsVIso : LitOrbitsV A ≅ LitOrbits5 A :=
  NatIso.ofComponents (fun T => (Quot.congr (Equiv.refl _) (orbitRelV_iff A T)).toIso)
    (fun f => by
      ext q
      induction q using Quot.ind
      rfl)

end Transport

section Milne

variable {S : Over Z30Base} (A : FEC S.left)

/-- Under Milne's Prop. 20.7 at `n = 5`: `H\F_{A/S,5} ≅ Orbits5 A`, by evaluation at `1`. -/
def orbitsVIsoMilne (hM5 : MilneProp207 5) : LitOrbitsV A ≅ Orbits5 A :=
  litOrbitsVIso A ≪≫ litOrbitsIsoMilne A hM5

/-- `F_{A/S,H} ≅ LevelPre A`: the sheafification of `orbitsVIsoMilne`. -/
def levelPreLitIso (hM5 : MilneProp207 5) : LevelPreLit A ≅ LevelPre A :=
  (sheafification (etaleOver S.left) (Type 1)).mapIso
    (Functor.isoWhiskerRight (orbitsVIsoMilne A hM5) uliftFunctor.{1, 0})

/-- Level structures: `LevelStrLit A ≃ LevelStr A`. -/
def levelStrLitEquiv (hM5 : MilneProp207 5) : LevelStrLit A ≃ LevelStr A :=
  ((levelPreLitIso A hM5).app (op (Over.mk (𝟙 S.left)))).toEquiv

theorem levelStrLitEquiv_apply (hM5 : MilneProp207 5) (α : LevelStrLit A) :
    levelStrLitEquiv A hM5 α = (levelPreLitIso A hM5).hom.app (op (Over.mk (𝟙 S.left))) α := rfl

/-- On the image of a literal frame `x`, the isomorphism is evaluation at `1`. -/
theorem levelPreLitIso_hom_mk (hM5 : MilneProp207 5) (T : (Over S.left)ᵒᵖ)
    (x : LitFrame A T.unop) :
    (levelPreLitIso A hM5).hom.app T
        ((toSheafify (etaleOver S.left) (LitOrbitsV A ⋙ uliftFunctor.{1, 0})).app T
          (ULift.up (Quot.mk _ x))) =
      (toSheafify (etaleOver S.left) (Orbits5 A ⋙ uliftFunctor.{1, 0})).app T
        (ULift.up (Quot.mk _ (evalEquiv A (hM5 S A).2 T x))) := by
  have h := congrArg (fun φ => φ.app T (ULift.up (Quot.mk _ x)))
    (toSheafify_naturality (etaleOver S.left)
      (Functor.isoWhiskerRight (orbitsVIsoMilne A hM5) uliftFunctor.{1, 0}).hom)
  exact h.symm

/-- The inverse on the image of a frame `evalEquiv x`. -/
theorem levelPreLitIso_inv_mk (hM5 : MilneProp207 5) (T : (Over S.left)ᵒᵖ)
    (x : LitFrame A T.unop) :
    (levelPreLitIso A hM5).inv.app T
        ((toSheafify (etaleOver S.left) (Orbits5 A ⋙ uliftFunctor.{1, 0})).app T
          (ULift.up (Quot.mk _ (evalEquiv A (hM5 S A).2 T x)))) =
      (toSheafify (etaleOver S.left) (LitOrbitsV A ⋙ uliftFunctor.{1, 0})).app T
          (ULift.up (Quot.mk _ x)) := by
  rw [← levelPreLitIso_hom_mk A hM5]
  simp

end Milne

/-- The literal transport along an `O`-linear `h` is determined by its value at `1`: literal
frames are `O`-linear, `α [r] = ι(r) (α 1)`. -/
theorem transport_of_one {S S' : Scheme.{0}} {A : FEC S} {A' : FEC S'} {g : S' ⟶ S}
    {h : A'.F.left ⟶ A.F.left} (hlin : ∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) {T : Over S'}
    (x' : LitFrame A' T) (x : LitFrame A ((Over.map g).obj T))
    (h1 : (x.α 1).left = (x'.α 1).left ≫ h) (q : Y3OrderMod.OMod 5) :
    (x.α q).left = (x'.α q).left ≫ h := by
  obtain ⟨r, rfl⟩ := Y3OrderMod.coe_surjective 5 q
  rw [x.α_coe, x'.α_coe]
  simp only [Over.comp_left, iotaO, Over.homMk_left, Category.assoc]
  rw [h1, Category.assoc, hlin]

/-- The morphism conditions agree: for `O`-linear `h`, `LevelFibreLit` is `LevelFibre` after
the identification of level structures. The literal transport `α ↦ (q ↦ h ∘ α q)` evaluates at
`1` to `P ↦ h ∘ P`; conversely, literal frames over `A'` and `A` whose values at `1` correspond
under `h` correspond at every `q`, because `h` is `O`-linear. -/
theorem levelFibreLit_iff (hM5 : MilneProp207 5) {X S : Over Z30Base} (A : FEC X.left)
    (α : LevelStrLit A) (g : S.left ⟶ X.left) (A' : FEC S.left) (α' : LevelStrLit A')
    (h : A'.F.left ⟶ A.F.left) (hlin : ∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) :
    LevelFibreLit A α g A' α' h ↔
      LevelFibre A (levelStrLitEquiv A hM5 α) g A' (levelStrLitEquiv A' hM5 α') h := by
  constructor
  · rintro ⟨ψ, hfr, hα⟩
    refine ⟨(levelPreLitIso A' hM5).symm ≪≫ ψ ≪≫
      Functor.isoWhiskerLeft (Over.map g).op (levelPreLitIso A hM5), ?_, ?_⟩
    · intro T P' P hP
      obtain ⟨x', rfl⟩ := (evalEquiv A' (hM5 S A').2 (op T)).surjective P'
      obtain ⟨x, rfl⟩ := (evalEquiv A (hM5 X A).2 (op ((Over.map g).obj T))).surjective P
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, types_comp_apply]
      rw [levelPreLitIso_inv_mk A' hM5 (op T) x', hfr T x' x (transport_of_one hlin x' x hP)]
      exact levelPreLitIso_hom_mk A hM5 (op ((Over.map g).obj T)) x
    · simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, types_comp_apply, levelStrLitEquiv_apply, Iso.hom_inv_id_app_apply]
      rw [hα]
      exact NatTrans.naturality_apply (levelPreLitIso A hM5).hom _ α
  · rintro ⟨ψ, hfr, hα⟩
    refine ⟨levelPreLitIso A' hM5 ≪≫ ψ ≪≫
      Functor.isoWhiskerLeft (Over.map g).op (levelPreLitIso A hM5).symm, ?_, ?_⟩
    · intro T x' x hx
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, types_comp_apply]
      rw [levelPreLitIso_hom_mk A' hM5 (op T) x',
        hfr T (evalEquiv A' (hM5 S A').2 (op T) x')
          (evalEquiv A (hM5 X A).2 (op ((Over.map g).obj T)) x) (hx 1)]
      exact levelPreLitIso_inv_mk A hM5 (op ((Over.map g).obj T)) x
    · simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, types_comp_apply]
      rw [← levelStrLitEquiv_apply A' hM5 α', hα, levelStrLitEquiv_apply,
        ← NatTrans.naturality_apply (levelPreLitIso A hM5).hom]
      simp

/-- The transport: given Milne's Prop. 20.7 at `n = 5`, the literal leaf implies the
generator-encoded leaf `BuzzardXDV15`. The universal object keeps `X` and `A`, with the level
structure carried by `levelStrLitEquiv`; each clause is transported through `levelFibreLit_iff`,
the comparison maps `h` being `O`-linear in every clause. -/
theorem buzzardXDV15_of_lit (hM5 : MilneProp207 5) : BuzzardXDV15Lit → BuzzardXDV15 := by
  rintro ⟨X, A, α, hprop, hsmooth, hproj, huniv, huniq⟩
  have key : ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : LevelStrLit A') (g : S ⟶ X)
      (h : A'.F.left ⟶ A.F.left),
      (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
        LevelFibreLit A α g.left A' α' h) ↔
      (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
        LevelFibre A (levelStrLitEquiv A hM5 α) g.left A' (levelStrLitEquiv A' hM5 α') h) := by
    intro S A' α' g h
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (levelFibreLit_iff hM5 A α g.left A' α' h h2).1 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (levelFibreLit_iff hM5 A α g.left A' α' h h2).2 h3⟩
  refine ⟨X, A, levelStrLitEquiv A hM5 α, hprop, hsmooth, hproj, fun S A' α' => ?_,
    fun S A' α' g h h' hh hh' => ?_⟩
  · obtain ⟨g, ⟨h, hg⟩, hgu⟩ := huniv S A' ((levelStrLitEquiv A' hM5).symm α')
    refine ⟨g, ⟨h, ?_⟩, fun g' ⟨h', hg'⟩ => hgu g' ⟨h', (key S A' _ g' h').2 ?_⟩⟩
    · have e := (key S A' _ g h).1 hg
      rwa [Equiv.apply_symm_apply] at e
    · rwa [Equiv.apply_symm_apply]
  · refine huniq S A' ((levelStrLitEquiv A' hM5).symm α') g h h' ((key S A' _ g h).2 ?_)
      ((key S A' _ g h').2 ?_)
    · rwa [Equiv.apply_symm_apply]
    · rwa [Equiv.apply_symm_apply]

end Y3Buzzard.XDV15
