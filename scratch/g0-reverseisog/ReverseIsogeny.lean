import Mathlib

noncomputable section

/-! # g0-reverseisog: the glue piece `ReverseIsogeny` (G17 after Poincaré)

Self-contained (imports only Mathlib). Sections 1-2 are verbatim copies from
`scratch/g0-split/Split.lean` (branch `wip/g0-split`, commit c20fa62b): `PkgI3.AbVar` with `dim`,
`homGroup`, `Hom`, `IsIsogenyMor` (Split.lean lines 2514-2611), def-faltings' `AbVar`, `AbVar.dim`,
`IsIsogeny` (lines 17798-17820, 18538-18542), `LeafAdopt.abVarEquiv` (18773-18778),
`G0Split.IsProductOf` and `G0Split.ReverseIsogeny` (verbatim). Section 3 proves
`G0Split.ReverseIsogeny` from one leaf (`IsogenyQuasiInverse`, Mumford/Milne) and proved glue. -/

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The homomorphisms `A → B` of group schemes over `K`, as a subgroup of the commutative group
of all `K`-morphisms `A → B` (pointwise product, `Hom.commGroup`). -/
def homGroup (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  one_mem' := by
    change IsMonHom (toUnit A.X ≫ η[B.X])
    infer_instance
  mul_mem' := by
    rintro f g (hf : IsMonHom f) (hg : IsMonHom g)
    change IsMonHom (lift f g ≫ μ[B.X])
    infer_instance
  inv_mem' := by
    rintro f (hf : IsMonHom f)
    change IsMonHom f⁻¹
    infer_instance

/-- `Hom_K(A, B)`, written additively (a `ℤ`-module). -/
abbrev Hom (A B : AbVar K) : Type u := Additive (homGroup A B)

/-- The underlying morphism of schemes. -/
def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul f).2

lemma Hom.ext' {A B : AbVar K} {f g : Hom A B} (h : f.hom = g.hom) : f = g :=
  Additive.toMul.injective (Subtype.ext h)

/-- Package a homomorphism. -/
def Hom.mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : Hom A B :=
  Additive.ofMul ⟨f, ‹_›⟩

@[simp] lemma Hom.hom_mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] :
    (Hom.mk' f).hom = f := rfl
@[simp] lemma Hom.hom_add {A B : AbVar K} (f g : Hom A B) : (f + g).hom = f.hom * g.hom := rfl
@[simp] lemma Hom.hom_zero {A B : AbVar K} : (0 : Hom A B).hom = 1 := rfl

/-- The endomorphism ring `End_K(A)`, with multiplication `f * g = f ∘ g`. -/
abbrev End (A : AbVar K) : Type u := Hom A A

instance (A : AbVar K) : Ring (End A) :=
  { (inferInstance : AddCommGroup (End A)) with
    mul := fun f g => Hom.mk' (g.hom ≫ f.hom)
    one := Hom.mk' (𝟙 _)
    mul_assoc := fun f g h => Hom.ext' (by simp [HMul.hMul, Mul.mul])
    one_mul := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    mul_one := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    left_distrib := fun f g h => Hom.ext' (by
      change (g + h).hom ≫ f.hom = g.hom ≫ f.hom * h.hom ≫ f.hom
      simp [MonObj.mul_comp])
    right_distrib := fun f g h => Hom.ext' (by
      change h.hom ≫ (f + g).hom = h.hom ≫ f.hom * h.hom ≫ g.hom
      simp [MonObj.comp_mul])
    zero_mul := fun f => Hom.ext' (by
      change f.hom ≫ (1 : A.X ⟶ A.X) = 1
      simp)
    mul_zero := fun f => Hom.ext' (by
      change (1 : A.X ⟶ A.X) ≫ f.hom = 1
      simp) }

/-- The endomorphism algebra `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 (A : AbVar K) : Type u := TensorProduct ℤ ℚ (End A)

/-- A morphism of `K`-schemes is an isogeny-type map: finite and surjective. -/
def IsIsogenyMor {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left ∧ Surjective f.left

end AbVar

end PkgI3

/-! ## 1b. def-faltings' copy of the abelian-variety structure (verbatim from Split.lean) -/

namespace ZInQ.DefFaltings

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K`, proper, smooth and geometrically integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) The dimension of `A` (Krull dimension of the
underlying space). -/
noncomputable def AbVar.dim {K : Type} [Field K] (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left


variable {K : Type} [Field K]

/-- An isogeny: a homomorphism of group schemes, finite and surjective. -/
def IsIsogeny {A B : AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ IsFinite φ.left ∧ Surjective φ.left


end ZInQ.DefFaltings

namespace LeafAdopt

/-- **Bridge (proved)**: def-faltings' copy of the abelian-variety structure and this file's
`PkgI3.AbVar` (= the kernel's) are the same data (for `K : Type`), so R19-R21 and H5 transfer to
`PkgI3.AbVar` along this equivalence; unifying the two declarations is WP1 work. -/
def abVarEquiv (K : Type) [Field K] : ZInQ.DefFaltings.AbVar K ≃ PkgI3.AbVar K where
  toFun A := { X := A.X }
  invFun A := { X := A.X }
  left_inv _ := rfl
  right_inv _ := rfl

theorem abVarEquiv_dim (K : Type) [Field K] (A : ZInQ.DefFaltings.AbVar K) :
    (abVarEquiv K A).dim = A.dim := rfl


end LeafAdopt

/-! ## 2. The piece (verbatim from Split.lean, namespace `G0Split`) -/

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)


/-- **Missing piece 8 (glue G17, after Poincaré).** If `(f, g) : A × Z → J` is finite and surjective
(T8's output) and `P ≅ A × Z`, there is an isogeny `J → P` in the other direction, and
`dim J = dim P` (Mumford §8, Thm 4 / Remark, UNVERIFIED: an isogeny of degree `n` has a
quasi-inverse `ψ` with `φψ = [n]`). Needs finite group schemes and quotients, not in Mathlib. -/
def ReverseIsogeny : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (P : ZInQ.DefFaltings.AbVar L)
    (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J), IsProductOf P.X A.X Z.X →
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X, ZInQ.DefFaltings.IsIsogeny φ ∧ J.dim = P.dim

end G0Split

/-! ## 3. `ReverseIsogeny` from the leaf `IsogenyQuasiInverse` and proved glue (task g0-reverseisog) -/

namespace G0RevIsog

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Topology

/-- **LEAF (Mumford; Milne).** An isogeny `φ : A → B` of abelian varieties over a field `K` (a
homomorphism of group schemes that is finite and surjective) has a quasi-inverse: an isogeny
`ψ : B → A` and an integer `n ≥ 1` (the degree of `φ`) with `ψ ∘ φ = [n]_A` and `φ ∘ ψ = [n]_B`.
Here `[n]_A` is `(𝟙 A)ⁿ` in Mathlib's group of morphisms into the group object `A`.
Sources (numbers UNVERIFIED, from memory, no network): Mumford, *Abelian Varieties*, §7 Remark after
Thm 4 / §8 (over an algebraically closed field); Milne, *Abelian Varieties* (in Cornell-Silverman,
*Arithmetic Geometry*, 1986), §8, Prop. 8.1/Remark 8.2? and Milne's course notes *Abelian
Varieties* (2008) I, Prop. 7.1 and Remark 7.2 (over an arbitrary field `k`). The proof there: `ker φ`
is a finite group scheme of order `n = deg φ`, hence killed by `n` (Deligne, commutative case), so
`[n]_A` factors through the quotient `A/ker φ ≅ B` (Mumford §7 Thm 4 / §12). -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ ZInQ.DefFaltings.IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n

/-- **Glue interface (the property `ReverseIsogeny` actually uses).** Over a number field, an
isogeny `A → B` of abelian varieties has an isogeny `B → A` in the other direction. It follows from
the textbook leaf `IsogenyQuasiInverse` (`isogenyReverseExists_of_quasiInverse`) and, in
`SplitRev.lean`, from the bundle's research leaf R19 (Gaudron-Rémond) with H5's finiteness and
`DimFinite` (`isogenyReverseExists_of_r19`). -/
def IsogenyReverseExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ → ∃ ψ : B.X ⟶ A.X, ZInQ.DefFaltings.IsIsogeny ψ

/-- **Proved.** The leaf gives the interface. -/
theorem isogenyReverseExists_of_quasiInverse (hQ : IsogenyQuasiInverse) : IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨ψ, -, -, hψ, -, -⟩ := hQ K A B φ hφ
  exact ⟨ψ, hψ⟩

/-! ### Glue (proved): a closed surjective map does not lower the Krull dimension -/

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `closure {x}` as an irreducible closed set. -/
def closureIC (x : X) : TopologicalSpace.IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- Chains of irreducible closed sets lift along a continuous, specializing map, ending at the
closure of any point over the generic point of the last member. -/
theorem lift_series [QuasiSober Y] (f : X → Y) (hc : Continuous f) (hs : SpecializingMap f)
    (p : LTSeries (TopologicalSpace.IrreducibleCloseds Y)) :
    ∀ x : X, IsGenericPoint (f x) (p.last : Set Y) →
      ∃ q : LTSeries (TopologicalSpace.IrreducibleCloseds X), q.length = p.length ∧
        q.last = closureIC x := by
  induction p using RelSeries.inductionOn' with
  | singleton W =>
    intro x _
    exact ⟨RelSeries.singleton _ (closureIC x), rfl, rfl⟩
  | snoc p W hW ih =>
    intro x hx
    rw [RelSeries.last_snoc] at hx
    obtain ⟨w', hw'⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
    have hsub : (p.last : Set Y) ⊆ W := SetLike.coe_subset_coe.mpr hW.le
    have hspec : f x ⤳ w' := hx.specializes (hsub hw'.mem)
    obtain ⟨x', hxx', hfx'⟩ := hs hspec
    obtain ⟨q, hql, hqlast⟩ := ih x' (hfx' ▸ hw')
    have hlt : q.last < closureIC x := by
      rw [hqlast]
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {x}
        exact specializes_iff_closure_subset.mp hxx'
      · intro heq
        have h1 : closure ({x'} : Set X) = closure {x} := congrArg SetLike.coe heq
        have h2 : x' ⤳ x := specializes_iff_closure_subset.mpr h1.symm.le
        have h3 : w' ⤳ f x := hfx' ▸ h2.map hc
        have h4 : (W : Set Y) ⊆ p.last := by
          rw [← hx.def, ← hw'.def]
          exact specializes_iff_closure_subset.mp h3
        exact hW.ne (SetLike.coe_injective (subset_antisymm hsub h4))
    refine ⟨q.snoc (closureIC x) hlt, ?_, RelSeries.last_snoc _ _ _⟩
    simp [hql]

/-- **Glue (proved).** A continuous, specializing (e.g. closed), surjective map `f : X → Y` to a
quasi-sober space does not lower the Krull dimension: `dim Y ≤ dim X`. -/
theorem topologicalKrullDim_le_of_specializing [QuasiSober Y] (f : X → Y) (hc : Continuous f)
    (hs : SpecializingMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨q, hql, -⟩ := lift_series f hc hs p x hy
  rw [← hql]
  exact le_iSup (fun q : LTSeries (TopologicalSpace.IrreducibleCloseds X) =>
    ((q.length : ℕ∞) : WithBot ℕ∞)) q

end Topo

/-- **Glue (proved).** A finite surjective morphism of schemes does not lower the dimension of the
target: `dim Y ≤ dim X` (finite ⇒ integral ⇒ universally closed ⇒ closed, Mathlib). -/
theorem dim_le_of_finite_surjective {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  topologicalKrullDim_le_of_specializing f f.continuous f.isClosedMap.specializingMap f.surjective

/-- **Glue (proved).** Two isogenies in opposite directions force equal dimensions. -/
theorem dim_eq_of_isogenies {K : Type} [Field K] {A B : ZInQ.DefFaltings.AbVar K}
    (φ : A.X ⟶ B.X) (ψ : B.X ⟶ A.X) (hφ : ZInQ.DefFaltings.IsIsogeny φ)
    (hψ : ZInQ.DefFaltings.IsIsogeny ψ) : B.dim = A.dim := by
  obtain ⟨-, hφf, hφs⟩ := hφ
  obtain ⟨-, hψf, hψs⟩ := hψ
  exact le_antisymm (dim_le_of_finite_surjective φ.left) (dim_le_of_finite_surjective ψ.left)

/-- **Glue (proved): the map `P → J`.** If `(p₁, p₂) : P → A × Z` is an isomorphism of group
schemes and `(f, g) : A × Z → J` is finite and surjective, then `h = f ∘ p₁ + g ∘ p₂ : P → J` is an
isogeny. -/
theorem isogeny_of_product {L : Type} [Field L] (A J Z : PkgI3.AbVar L)
    (P : ZInQ.DefFaltings.AbVar L) (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J)
    (hP : G0Split.IsProductOf P.X A.X Z.X)
    (hiso : PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)) :
    ∃ h : P.X ⟶ J.X, IsMonHom h ∧ IsFinite h.left ∧ Surjective h.left := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hlift⟩ := hP
  obtain ⟨hfin, hsurj⟩ := hiso
  have hm : lift p₁ p₂ ≫ (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) =
      p₁ ≫ f.hom * p₂ ≫ g.hom := by
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have hmon : IsMonHom (p₁ ≫ f.hom * p₂ ≫ g.hom) := by
    change IsMonHom (lift (p₁ ≫ f.hom) (p₂ ≫ g.hom) ≫ μ[J.X])
    infer_instance
  refine ⟨lift p₁ p₂ ≫ (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom), ?_, ?_, ?_⟩
  · rw [hm]; exact hmon
  · rw [Over.comp_left]
    infer_instance
  · rw [Over.comp_left]
    infer_instance

/-- **`ReverseIsogeny` (G17 after Poincaré), proved from the interface `IsogenyReverseExists`.**
The map `h = f ∘ p₁ + g ∘ p₂ : P → J` is an isogeny (`isogeny_of_product`); the interface gives an
isogeny `ψ : J → P`; `h` and `ψ` give `dim J = dim P` (`dim_eq_of_isogenies`). -/
theorem reverseIsogeny_of_exists (hE : IsogenyReverseExists) : G0Split.ReverseIsogeny := by
  intro L _ _ A J Z P f g hP hiso
  obtain ⟨h, hh⟩ := isogeny_of_product A J Z P f g hP hiso
  replace hh : ZInQ.DefFaltings.IsIsogeny (A := P) (B := (LeafAdopt.abVarEquiv L).symm J) h := hh
  obtain ⟨ψ, hψ⟩ := hE L P ((LeafAdopt.abVarEquiv L).symm J) h hh
  exact ⟨ψ, hψ, dim_eq_of_isogenies h ψ hh hψ⟩

/-- **`ReverseIsogeny`, proved from the textbook leaf `IsogenyQuasiInverse`.** -/
theorem reverseIsogeny (hQ : IsogenyQuasiInverse) : G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_quasiInverse hQ)

end G0RevIsog

/-! ## 4. Checks -/

namespace G0RevIsog

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

/-- Sanity: in the leaf, `(𝟙 A.X) ^ n` is multiplication by `n` for the group-object structure
(`[2]_A = μ ∘ (id, id)`). -/
example {K : Type} [Field K] (A : ZInQ.DefFaltings.AbVar K) :
    (𝟙 A.X) ^ 2 = lift (𝟙 A.X) (𝟙 A.X) ≫ μ[A.X] := by
  rw [pow_two]; rfl

end G0RevIsog

#print axioms G0RevIsog.reverseIsogeny
#print axioms G0RevIsog.topologicalKrullDim_le_of_specializing
