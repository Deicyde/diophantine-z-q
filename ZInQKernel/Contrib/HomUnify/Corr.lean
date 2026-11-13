import ZInQKernel.HDecomp.LeafPush2.T
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# hom-unify: the two `Hom` forms of T11(a), and the single leaf `HomLatticeCorr`

Two leaf candidates state halves of one textbook theorem in `Hom` form. Both are over the same
layer: the build's `PkgI3.AbVar`, `ZInQ.LeafPush2.CPts` and `ZInQ.LeafPush2.IsUniformization`.

* `T11aHom` (task r1b-state, `scratch/r1b-state/Part8b_Hom.part`, namespace `R1bState`): over `ℂ`,
  for `A, B` of the same dimension `g`, every `ℂ`-linear `M` with `MΛ_A ⊆ Λ_B` is induced by a
  unique homomorphism `f : A → B`. This is the **realization** half: lattice maps give
  homomorphisms. Its content is GAGA/Chow (a holomorphic homomorphism of the tori is algebraic).
* `HomLinearLift` (task conj-twist, `scratch/conj-twist/ConjTwist.lean`, namespace `G0Galois`):
  over any field `K` with `σ : K → ℂ`, every homomorphism `f : A → B` lifts to a `ℂ`-linear `M`
  with `Φ_B(Mz) = f(Φ_A(z))`. This is the **lifting** half: homomorphisms give lattice maps. Its
  content is that algebraic maps are holomorphic, plus Birkenhake–Lange 1.2.1 (a holomorphic
  homomorphism of complex tori lifts to a linear map).

The two statements go in opposite directions, so neither is a consequence of the other. Both are
true. `T11aHom` says nothing about a homomorphism that is not given by a lattice map, which is
exactly what `HomLinearLift` asserts. `HomLinearLift` gives no homomorphism at all, which is
exactly what `T11aHom` asserts. `T11aHom` is also only over `ℂ`, while `HomLinearLift` is used over
number fields (G10). The single leaf `HomLatticeCorr` below is both halves at once (the analytic
representation `Hom(A, B) → {M : MΛ_A ⊆ Λ_B}` is defined, and over `ℂ` it is bijective). It implies
`T11aHom`, `HomLinearLift` and leaf-push2's `T11a_RiemannEnd` (all proved below).

The statements `T11aHom` and `HomLinearLift` are copied verbatim (checked by
`scratch/hom-unify/py/verbatim_check.py`); only the namespace and the `open` lines differ.
-/

namespace ZInQ.HomUnify

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- **T11(a) in `Hom` form (textbook leaf candidate; the same theorem as leaf-push2's
`T11a_RiemannEnd`, which is its case `A = B`).** For complex abelian varieties `A`, `B` of
dimension `g` with uniformizations `Φ_A`, `Φ_B` (kernels `Λ_A`, `Λ_B`), every `ℂ`-linear `M` with
`MΛ_A ⊆ Λ_B` is induced by a unique homomorphism `f : A → B` (`Φ_B(Mz) = f(Φ_A(z))`).
Mumford, *Abelian varieties*, §1-§2; Birkenhake–Lange, Prop. 1.2.1 (for complex tori); GAGA,
Serre 1956, for "holomorphic ⇒ algebraic" (UNVERIFIED numbers).
(Verbatim copy of `R1bState.T11aHom`, `scratch/r1b-state/Part8b_Hom.part`.) -/
def T11aHom : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (ΛA ΛB : Submodule ℤ (Fin g → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin g → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (g : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- **N2. T11(a) in Hom form (textbook LEAF; Birkenhake–Lange, *Complex abelian varieties*,
Prop. 1.2.1, with holomorphy of algebraic morphisms; Mumford §1; UNVERIFIED numbers).** For
abelian varieties `A, B` over `K`, `σ : K → ℂ` and uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ`,
`B(ℂ)_σ`, every homomorphism `f : A → B` lifts to a `ℂ`-linear map `M` with
`Φ_B(Mz) = f(Φ_A(z))`. (`T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`.)
(Verbatim copy of `G0Galois.HomLinearLift`, `scratch/conj-twist/ConjTwist.lean`.) -/
def HomLinearLift : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- **The analytic representation of homomorphisms (textbook LEAF; the single leaf proposed by
hom-unify for T11(a) in `Hom` form).** Let `A`, `B` be abelian varieties over a field `K`,
`σ : K → ℂ`, and `Φ_A : ℂ^g → A(ℂ)_σ`, `Φ_B : ℂ^h → B(ℂ)_σ` analytic uniformizations with kernels
`Λ_A`, `Λ_B` (`g = dim A`, `h = dim B`).
1. (lifting) every homomorphism `f : A → B` lifts to a `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `Φ_B(Mz) = f(Φ_A(z))`;
2. (realization, over `ℂ`) if `K = ℂ` and `σ = id`, every `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `MΛ_A ⊆ Λ_B` is induced in this way by a unique homomorphism `f : A → B`.

Together: `Hom(A_ℂ, B_ℂ) ≅ {M ∈ Hom_ℂ(ℂ^g, ℂ^h) : MΛ_A ⊆ Λ_B}`, `f ↦ ρ_a(f)`, and for general `K`
the analytic representation of `f` is that of `f_ℂ`. Sources (all UNVERIFIED numbers):
Birkenhake–Lange, *Complex abelian varieties*, §1.2 (Prop. 1.2.1: homomorphisms of complex tori
`ℂ^g/Λ → ℂ^h/Λ'` are exactly the maps induced by `ℂ`-linear `M` with `MΛ ⊆ Λ'`, and the analytic
representation is injective); Mumford, *Abelian varieties*, §1 (the complex torus `A(ℂ)`) and
§3 (`A ↦ A^an` is fully faithful on abelian varieties); Serre, GAGA (1956) / Chow, for
"holomorphic ⇒ algebraic" in 2.; holomorphy of algebraic morphisms for 1. -/
def HomLatticeCorr : Prop :=
  (∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom) ∧
  (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom)

/-- **`HomLinearLift` from `HomLatticeCorr` (proved):** its first clause, verbatim. -/
theorem homLinearLift_of_corr (h : HomLatticeCorr) : HomLinearLift := h.1

/-- **`T11aHom` from `HomLatticeCorr` (proved):** the second clause at `h = g`. -/
theorem t11aHom_of_corr (h : HomLatticeCorr) : T11aHom :=
  fun A B g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM => h.2 A B g g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM

/-- **leaf-push2's `T11a_RiemannEnd` from `HomLatticeCorr` (proved):** both clauses at `B = A`,
`Φ_B = Φ_A`, `K = ℂ`, `σ = id` (`End A` is `Hom A A`). -/
theorem t11a_riemannEnd_of_corr (h : HomLatticeCorr) : ZInQ.LeafPush2.T11a_RiemannEnd :=
  fun A g Λ Φ hA hU =>
    ⟨fun M hM => h.2 A A g g Λ Λ Φ Φ hA hA hU hU M hM,
     fun f => h.1 ℂ A A (RingHom.id ℂ) g g Λ Λ Φ Φ hA hA hU hU f⟩

/-- **`HomLatticeCorr` from `HomLinearLift` and the realization clause (proved):** the leaf is
exactly the two halves. -/
theorem corr_iff : HomLatticeCorr ↔ HomLinearLift ∧
    (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
      (ΛB : Submodule ℤ (Fin h → ℂ))
      (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
      A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
      IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
      ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
        ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom) :=
  Iff.rfl

/-! ### The uniqueness in the realization half is automatic

Over `ℂ`, a morphism of abelian varieties is determined by its values on `ℂ`-points
(`hom_ext_of_cpts`: `A` is reduced and of finite type, `B` separated; Mathlib's
`ext_of_apply_eq` with the closed points, which are the `ℂ`-points by the Nullstellensatz). Since a
uniformization is onto `A(ℂ)`, at most one `f` induces a given `M`. So `T11aHom` and the second
clause of `HomLatticeCorr` are equivalent to their existence forms. -/

/-- **Morphisms of abelian varieties over `ℂ` agreeing on `ℂ`-points are equal (proved).** -/
theorem hom_ext_of_cpts {A B : PkgI3.AbVar ℂ} (f f' : A.X ⟶ B.X)
    (h : ∀ p : CPts A (RingHom.id ℂ), p ≫ f = p ≫ f') : f = f' := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  apply Over.OverMorphism.ext
  have hw : f.left ≫ B.X.hom = f'.left ≫ B.X.hom := by rw [Over.w f, Over.w f']
  have : LocallyOfFiniteType (f.left ≫ B.X.hom) := by rw [Over.w f]; infer_instance
  refine ext_of_apply_eq B.X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => ?_) hw
  let p0 := pointOfClosedPoint A.X.hom x hx
  let p : CPts A (RingHom.id ℂ) := Over.homMk p0 (by
    simp only [ZInQ.LeafPush2.cptObj, Over.mk_hom, CommRingCat.ofHom_id, Spec.map_id]
    exact pointOfClosedPoint_comp A.X.hom x hx)
  have hp : p0 ≫ f.left = p0 ≫ f'.left := congrArg CommaMorphism.left (h p)
  have key : (p0 ≫ f.left) (A.X.hom x) = (p0 ≫ f'.left) (A.X.hom x) := by rw [hp]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at key
  exact key

/-- **At most one homomorphism induces a given `M` (proved),** for a uniformization `Φ_A` of
`A(ℂ)` (only its surjectivity is used). -/
theorem induces_unique {A B : PkgI3.AbVar ℂ} {g h : ℕ} {ΛA : Submodule ℤ (Fin g → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)} (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ))
    (hU : IsUniformization (RingHom.id ℂ) ΛA ΦA) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    {f f' : PkgI3.AbVar.Hom A B} (hf : ∀ z, ΦB (M z) = ΦA z ≫ f.hom)
    (hf' : ∀ z, ΦB (M z) = ΦA z ≫ f'.hom) : f = f' := by
  apply PkgI3.AbVar.Hom.ext'
  apply hom_ext_of_cpts
  intro p
  obtain ⟨z, rfl⟩ := hU.2.2.1 p
  rw [← hf z, hf' z]

/-- The existence form of `T11aHom`. -/
def T11aHomEx : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (ΛA ΛB : Submodule ℤ (Fin g → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin g → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (g : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃ f : AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- **`T11aHom` is equivalent to its existence form (proved).** -/
theorem t11aHom_iff_ex : T11aHom ↔ T11aHomEx := by
  constructor
  · intro H A B g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM
    exact (H A B g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM).exists
  · intro H A B g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM
    obtain ⟨f, hf⟩ := H A B g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM
    exact ⟨f, hf, fun f' hf' => induces_unique ΦB hUA M hf' hf⟩

/-- The realization half of `HomLatticeCorr`, existence form (no uniqueness, all `g`, `h`). -/
def HomRealize : Prop :=
  ∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃ f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- **`HomLatticeCorr` is `HomLinearLift` plus the existence form of realization (proved).** -/
theorem corr_iff_lift_realize : HomLatticeCorr ↔ HomLinearLift ∧ HomRealize := by
  constructor
  · intro H
    exact ⟨H.1, fun A B g h ΛA ΛB ΦA ΦB hA hB hUA hUB M hM =>
      (H.2 A B g h ΛA ΛB ΦA ΦB hA hB hUA hUB M hM).exists⟩
  · rintro ⟨H1, H2⟩
    refine ⟨H1, fun A B g h ΛA ΛB ΦA ΦB hA hB hUA hUB M hM => ?_⟩
    obtain ⟨f, hf⟩ := H2 A B g h ΛA ΛB ΦA ΦB hA hB hUA hUB M hM
    exact ⟨f, hf, fun f' hf' => induces_unique ΦB hUA M hf' hf⟩

/-- **`T11aHom` from `HomRealize` (proved):** the equal-dimension case, uniqueness automatic. -/
theorem t11aHom_of_realize (H : HomRealize) : T11aHom :=
  t11aHom_iff_ex.2 fun A B g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM =>
    H A B g g ΛA ΛB ΦA ΦB hA hB hUA hUB M hM

end ZInQ.HomUnify

#print axioms ZInQ.HomUnify.homLinearLift_of_corr
#print axioms ZInQ.HomUnify.t11aHom_of_corr
#print axioms ZInQ.HomUnify.t11a_riemannEnd_of_corr
#print axioms ZInQ.HomUnify.corr_iff
#print axioms ZInQ.HomUnify.hom_ext_of_cpts
#print axioms ZInQ.HomUnify.induces_unique
#print axioms ZInQ.HomUnify.t11aHom_iff_ex
#print axioms ZInQ.HomUnify.corr_iff_lift_realize
#print axioms ZInQ.HomUnify.t11aHom_of_realize
