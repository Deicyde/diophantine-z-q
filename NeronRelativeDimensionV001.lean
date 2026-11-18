import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# `dim A = a + t` from relative dimension along a smooth group model

Let `N` be a smooth group scheme over a valuation ring `O ⊆ K` with an isomorphism of its generic
fibre with the abelian variety `A`, let `φ : O → k` be a map to a field and `G = N ×_O k`, and let
`U ⊆ G` be an open subscheme with a morphism `π : U → B` to an abelian variety `B` over `k` of
dimension `a`. The argument:

* a smooth group scheme over a local ring has a single relative dimension `d`
  (`SmoothGroupRelDimLocal`, statement form);
* relative dimension is stable under base change, so both `A` (generic fibre) and `G` (any
  fibre) are smooth of relative dimension `d`; the open subscheme `U` is too;
* if `π` is smooth of relative dimension `t`, then `U → Spec k` is smooth of relative dimension
  `t + a'` where `a'` is the relative dimension of `B`;
* over a field, a nonempty scheme smooth of relative dimension `n` has Krull dimension `n`
  (`SmoothRelDimKrullDim`, statement form); applied to `A`, `B` and `U` this gives `a' = a`,
  `d = t + a`, and `dim A = d = a + t`.

Generic and special dimensions are not assumed equal: they are compared through the single
relative dimension of the model. The two statement forms are standard results; the hypothesis
`hπ` (the quotient map of the semi-abelian identity component is smooth of relative dimension `t`)
is the remaining geometric input.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace NeronRelativeDimension

/-- Statement form: a nonempty scheme smooth of relative dimension `n` over a field has Krull
dimension `n`. -/
def SmoothRelDimKrullDim : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty X], topologicalKrullDim X = (n : WithBot ℕ∞)

/-- Statement form: a smooth group scheme over a local ring is smooth of a single relative
dimension. -/
def SmoothGroupRelDimLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Smooth G.hom], ∃ d : ℕ, SmoothOfRelativeDimension d G.hom

/-- A group scheme over a field has a point. -/
theorem nonempty_of_grp {k : Type} [Field k] (X : Over (Spec (CommRingCat.of k))) [GrpObj X] :
    Nonempty X.left := by
  let p : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  exact ⟨(η[X] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X).left p⟩

/-- Precomposition with an isomorphism keeps the relative dimension. -/
theorem relDim_comp_iso {X Y S : Scheme.{0}} (i : X ⟶ Y) [IsIso i] (g : Y ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (i ≫ g) := by
  have : SmoothOfRelativeDimension (0 + n) (i ≫ g) := inferInstance
  rwa [zero_add] at this

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- `Spec K → Spec O`. -/
abbrev jO (O : ValuationSubring K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O K))

/-- **The generic fibre has the model's relative dimension.** -/
theorem generic_relDim (N : Over (Spec (CommRingCat.of O))) (d : ℕ)
    [SmoothOfRelativeDimension d N.hom] (e : (Over.pullback (jO O)).obj N ≅ A.X) :
    SmoothOfRelativeDimension d A.X.hom := by
  have h1 : SmoothOfRelativeDimension d ((Over.pullback (jO O)).obj N).hom := by
    change SmoothOfRelativeDimension d (pullback.snd N.hom (jO O))
    infer_instance
  have : IsIso e.inv.left := (inferInstance : IsIso ((Over.forget _).map e.inv))
  have h2 : e.inv.left ≫ ((Over.pullback (jO O)).obj N).hom = A.X.hom := Over.w e.inv
  rw [← h2]
  exact relDim_comp_iso _ _ d

/-- **Every fibre has the model's relative dimension.** -/
theorem fibre_relDim (N : Over (Spec (CommRingCat.of O))) (d : ℕ)
    [SmoothOfRelativeDimension d N.hom] {k : Type} [Field k] (φ : O →+* k) :
    SmoothOfRelativeDimension d ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N).hom := by
  change SmoothOfRelativeDimension d (pullback.snd N.hom _)
  infer_instance

/-- An open subscheme keeps the relative dimension. -/
theorem open_relDim {S : Scheme.{0}} {G U : Over S} (inc : U ⟶ G) [IsOpenImmersion inc.left]
    (d : ℕ) [SmoothOfRelativeDimension d G.hom] : SmoothOfRelativeDimension d U.hom := by
  have h : inc.left ≫ G.hom = U.hom := Over.w inc
  rw [← h]
  have : SmoothOfRelativeDimension (0 + d) (inc.left ≫ G.hom) := inferInstance
  rwa [zero_add] at this

/-- Relative dimensions add along `U → B → S`. -/
theorem extension_relDim {S : Scheme.{0}} {U B : Over S} (π : U ⟶ B) (t a : ℕ)
    [SmoothOfRelativeDimension t π.left] [SmoothOfRelativeDimension a B.hom] :
    SmoothOfRelativeDimension (t + a) U.hom := by
  have h : π.left ≫ B.hom = U.hom := Over.w π
  rw [← h]
  infer_instance

/-- **`dim A = a + t`**, with generic and special dimensions compared through the single relative
dimension of the smooth group model. -/
theorem dim_eq_add (hV1 : SmoothGroupRelDimLocal) (hV3 : SmoothRelDimKrullDim)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N) [IsOpenImmersion inc.left]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) (t a : ℕ)
    (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    (hπ : SmoothOfRelativeDimension t π.left) :
    topologicalKrullDim A.X.left = ((a + t : ℕ) : WithBot ℕ∞) ∧
      SmoothOfRelativeDimension (a + t) N.hom := by
  obtain ⟨d, hd⟩ := hV1 O N
  obtain ⟨a', ha'⟩ := hV1 k B.X
  have hA : SmoothOfRelativeDimension d A.X.hom := generic_relDim N d e
  have hG := fibre_relDim N d φ
  have hU : SmoothOfRelativeDimension d U.hom := open_relDim inc d
  have hU' : SmoothOfRelativeDimension (t + a') U.hom := extension_relDim π t a'
  have neA : Nonempty A.X.left := nonempty_of_grp A.X
  have neB : Nonempty B.X.left := nonempty_of_grp B.X
  have neU : Nonempty U.left := nonempty_of_grp U
  have dA := hV3 K A.X.left A.X.hom d
  have dB := hV3 k B.X.left B.X.hom a'
  have dU := @hV3 k _ U.left U.hom d hU neU
  have dU' := @hV3 k _ U.left U.hom (t + a') hU' neU
  have haa : a' = a := by
    rw [hB] at dB
    exact_mod_cast dB.symm
  have hdd : d = t + a' := by
    rw [dU] at dU'
    exact_mod_cast dU'
  have hda : d = a + t := by rw [hdd, haa, add_comm]
  refine ⟨?_, ?_⟩
  · rw [dA, hda]
  · rw [← hda]
    exact hd

/-- In the presence of the special count `2a + t`, the generic Tate rank `2g` splits as
`(2a + t) + t`. -/
theorem two_mul_dim_split {g a t : ℕ} (h : g = a + t) : 2 * g = (2 * a + t) + t := by
  omega

end NeronRelativeDimension
