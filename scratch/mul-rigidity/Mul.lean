import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace

/-!
# mul-rigidity: the textbook leaf `MulIsogeny` reduced to smaller named Props

`MulIsogeny` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4″). Mathlib
proves "finite and surjective" from local properties of `[n]`: proper (`A` proper) and locally
quasi-finite give finite (Zariski's main theorem, Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite`,
Stacks 02LS); open (flat + locally of finite presentation, `UniversallyOpen.of_flat`) and closed
(proper) with `A` irreducible and nonempty give surjective.
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Formally unramified and locally of finite type implies locally quasi-finite (Mathlib's algebra
instance `Algebra.QuasiFinite` from `EssFiniteType` and `FormallyUnramified`, made affine-local). -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : (f.appLE U V e).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance U V e
  have h2 : (f.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

variable {K : Type} [Field K]

/-- A `K`-morphism between abelian varieties is proper (source proper, target separated). -/
theorem isProper_left (A B : PkgI3.AbVar K) (f : A.X ⟶ B.X) : IsProper f.left := by
  have : IsProper (f.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp f.left B.X.hom

/-- **Glue.** A locally quasi-finite open `K`-endomorphism of an abelian variety is finite and
surjective. -/
theorem isIsogenyMor_of_lqf_of_isOpenMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    [LocallyQuasiFinite f.left] (ho : IsOpenMap f.left.base) : PkgI3.AbVar.IsIsogenyMor f := by
  have := isProper_left A A f
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite f.left, ⟨?_⟩⟩
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have hcl : IsClopen (Set.range f.left.base) :=
    ⟨f.left.isClosedMap.isClosed_range, ho.isOpen_range⟩
  have hne : (Set.range f.left.base).Nonempty :=
    ⟨_, ⟨η[A.X].left (IsLocalRing.closedPoint K), rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Under a locally quasi-finite morphism, a strict specialization maps to two distinct points
(the fibres are discrete, Mathlib `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem ne_of_specializes_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : f x ≠ f y := by
  intro heq
  have hd := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  let x' : (f.base ⁻¹' {f y} : Set X) := ⟨x, heq⟩
  let y' : (f.base ⁻¹' {f y} : Set X) := ⟨y, rfl⟩
  have h' : x' ⤳ y' := (subtype_specializes_iff x' y').mpr hxy
  exact hne (congrArg Subtype.val h'.eq)

/-- **A locally quasi-finite closed self-map of an irreducible Noetherian scheme is
surjective.** If `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ f ξ ⤳ f² ξ ⤳ ⋯` are strict
specializations (continuity, and `ne_of_specializes_of_lqf`), so the closures `cl{fᵐ ξ}` form a
strictly decreasing chain of closed sets, contradicting Noetherianity. So `ξ ∈ range f`, which is
closed, hence everything. -/
theorem surjective_of_lqf_self {X : Scheme} [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    Function.Surjective f.base := by
  set ξ := genericPoint X
  have hξ : ∀ x : X, ξ ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hfix : f ξ = ξ := by
    by_contra hne
    let s : ℕ → X := fun m => (f.base)^[m] ξ
    have hs : ∀ m, s m ⤳ s (m + 1) ∧ s m ≠ s (m + 1) := by
      intro m
      induction m with
      | zero => exact ⟨hξ _, fun h => hne h.symm⟩
      | succ m ih =>
        have e1 : s (m + 1) = f (s m) := Function.iterate_succ_apply' _ _ _
        have e2 : s (m + 1 + 1) = f (s (m + 1)) := Function.iterate_succ_apply' _ _ _
        rw [e1, e2]
        exact ⟨ih.1.map f.base.hom.continuous, ne_of_specializes_of_lqf f ih.1 ih.2⟩
    let c : ℕ → TopologicalSpace.Closeds X := fun m => ⟨closure {s m}, isClosed_closure⟩
    have hc' : StrictAnti c := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      refine lt_of_le_of_ne ?_ ?_
      · change closure {s (m + 1)} ⊆ closure {s m}
        exact specializes_iff_closure_subset.mp (hs m).1
      · intro h
        have h2 : closure {s (m + 1)} = closure {s m} := congrArg SetLike.coe h
        exact (hs m).2 (inseparable_iff_closure_eq.mpr h2.symm).eq
    exact not_strictAnti_of_wellFoundedLT c hc'
  intro y
  have hy : y ∈ closure {ξ} := specializes_iff_mem_closure.mp (hξ y)
  exact (hc.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨ξ, hfix⟩)) hy

end MulRigidity

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end G0FibreSimple

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Leaf (Mumford, *Abelian varieties*, §4 Application 2 and §6: `n_X` is separable when
`char k ∤ n`; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2: `n_A` is étale iff
`char k ∤ n`; locators UNVERIFIED).** In characteristic `0`, `[n]` is étale for `n ≠ 0`. A
consequence of the published statement (only characteristic `0`). -/
def MulEtale : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    Etale ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (the infinitesimal half of `MulEtale`; Mumford §4: `d(n_X) = n` on the tangent space
at `0`, so `n_X^* ω = n ω` for invariant differentials; locator UNVERIFIED).** In characteristic
`0`, `[n]` is formally unramified (`Ω_{[n]} = 0`) for `n ≠ 0`. Implied by `MulEtale`
(`mulUnramified_of_mulEtale`). -/
def MulUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    FormallyUnramified ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (dimension theory; Mumford §4 / Milne, *Abelian varieties*, Prop. 8.1: a homomorphism
of abelian varieties of the same dimension with finite kernel is surjective, an isogeny; locators
UNVERIFIED).** A locally quasi-finite endomorphism of an abelian variety is surjective
(any characteristic). -/
def QuasiFiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : PkgI3.AbVar.End A),
    LocallyQuasiFinite f.hom.left → Surjective f.hom.left

theorem mulUnramified_of_mulEtale (h : MulEtale) : MulUnramified := by
  intro k _ _ A n hn
  have := h k A n hn
  infer_instance

/-- **`MulIsogeny` from `MulEtale`** (glue proved here). -/
theorem mulIsogeny_of_mulEtale (h : MulEtale) : G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact isIsogenyMor_of_lqf_of_isOpenMap A _ (Scheme.Hom.isOpenMap _)

/-- **`MulIsogeny` from `MulUnramified` and `QuasiFiniteEndSurjective`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified (h1 : MulUnramified) (h2 : QuasiFiniteEndSurjective) :
    G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h1 k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, h2 k A _ inferInstance⟩

/-- **`QuasiFiniteEndSurjective` holds** (proved from Mathlib; it is not a leaf). -/
theorem quasiFiniteEndSurjective : QuasiFiniteEndSurjective := by
  intro k _ A f hf
  have := isProper_left A A f.hom
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsNoetherian A.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.X.hom }
  exact ⟨surjective_of_lqf_self f.hom.left f.hom.left.isClosedMap⟩

/-- **`MulIsogeny` from the single leaf `MulUnramified`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified' (h : MulUnramified) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified h quasiFiniteEndSurjective

end MulRigidity

#print axioms MulRigidity.mulIsogeny_of_mulEtale
#print axioms MulRigidity.mulIsogeny_of_mulUnramified
#print axioms MulRigidity.mulIsogeny_of_mulUnramified'
