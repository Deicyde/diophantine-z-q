import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The canonical base-change comparison of Néron models, from the mapping property

Let `S' → S` be a morphism of schemes, `E → S` and `E' → S'` the inclusions of generic fibres, and
`g : E' → E` with `j' ≫ h = g ≫ j`. Let `N/S` be smooth with an identification
`gen : N ×_S E ≅ A_E`, and let `N'/S'` have the Néron mapping property for smooth `S'`-schemes with
respect to `gen' : N' ×_{S'} E' ≅ A_E ×_E E'`. Then:

* `genIso`: the generic fibre of `N ×_S S'` is identified with `A_E ×_E E'` (pseudo-functoriality
  of base change along the square);
* `exists_unique_comparison`: there is a unique `S'`-morphism `u : N ×_S S' → N'` inducing this
  identification on generic fibres; it is derived from the mapping property of `N'` applied to the
  smooth `S'`-scheme `N ×_S S'`, nothing about `u` is assumed;
* `comparison_generic_isIso`: `u` is an isomorphism on generic fibres;
* `comparison_valuationSubring`: the case `S = Spec O`, `S' = Spec O'`, `E = Spec K`, `E' = Spec L`
  for valuation subrings `O ⊆ K`, `O' ⊆ L` of a field extension `L/K` with `O' ∩ K = O`, and
  `A_E = A` an abelian variety over `K`, `A_E ×_E E' = A_L`. No hypothesis on the ramification of
  `O'/O` (tame or wild), on the residue field extension, or on the finiteness of `L/K` enters.

The special fibre of `u` is obtained by further base change along `Spec κ(O') → Spec O'`; this file
does not claim that `u` is an isomorphism, an open immersion, or that the full Néron model commutes
with base change (it does not under ramified base change in general).
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace ToricBaseChange.Comparison

section General

variable {S S' E E' : Scheme.{0}} (h : S' ⟶ S) (j : E ⟶ S) (j' : E' ⟶ S') (g : E' ⟶ E)
  (hsq : j' ≫ h = g ≫ j)

/-- The base change `N ×_S S'` as an `S'`-scheme. -/
abbrev bc (N : Over S) : Over S' := (Over.pullback h).obj N

instance smooth_bc (N : Over S) [Smooth N.hom] : Smooth (bc h N).hom := by
  change Smooth (pullback.snd N.hom h); infer_instance

/-- **The generic fibre of `N ×_S S'`** is `A_E ×_E E'`: base change along `j' ≫ h = g ≫ j`
followed by `gen`. -/
def genIso (N : Over S) (AX : Over E) (gen : (Over.pullback j).obj N ≅ AX) :
    (Over.pullback j').obj (bc h N) ≅ (Over.pullback g).obj AX :=
  ((Over.pullbackComp j' h).app N).symm ≪≫
    (eqToIso (congrArg (fun f : E' ⟶ S => Over.pullback f) hsq)).app N ≪≫
    (Over.pullbackComp g j).app N ≪≫ (Over.pullback g).mapIso gen

/-- **The canonical comparison morphism, from the Néron mapping property of `N'`**: a unique
`u : N ×_S S' → N'` over `S'` whose generic fibre, followed by `gen'`, is `genIso`. -/
theorem exists_unique_comparison (N : Over S) [Smooth N.hom] (AX : Over E)
    (gen : (Over.pullback j).obj N ≅ AX) (N' : Over S')
    (gen' : (Over.pullback j').obj N' ≅ (Over.pullback g).obj AX)
    (hN' : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' => (Over.pullback j').map f ≫ gen'.hom) :
    ∃! u : bc h N ⟶ N',
      (Over.pullback j').map u ≫ gen'.hom = (genIso h j j' g hsq N AX gen).hom := by
  obtain ⟨u, hu⟩ := (hN' (bc h N)).2 (genIso h j j' g hsq N AX gen).hom
  exact ⟨u, hu, fun v hv => (hN' (bc h N)).1 (hv.trans hu.symm)⟩

/-- **The comparison is an isomorphism on generic fibres.** -/
theorem comparison_generic_isIso (N : Over S) (AX : Over E) (gen : (Over.pullback j).obj N ≅ AX)
    (N' : Over S') (gen' : (Over.pullback j').obj N' ≅ (Over.pullback g).obj AX)
    (u : bc h N ⟶ N')
    (hu : (Over.pullback j').map u ≫ gen'.hom = (genIso h j j' g hsq N AX gen).hom) :
    IsIso ((Over.pullback j').map u) := by
  have e : (Over.pullback j').map u = (genIso h j j' g hsq N AX gen).hom ≫ gen'.inv := by
    rw [← hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

end General

/-! ## Valuation subrings of a field extension -/

section Valuation

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- `O → O'` for valuation subrings with `O' ∩ K = O`. -/
def iota (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) : O →+* O' :=
  ((algebraMap K L).comp O.subtype).codRestrict O' (fun x => by
    have hx : (x : K) ∈ O'.comap (algebraMap K L) := by rw [hO]; exact x.2
    exact hx)

theorem iota_square (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) :
    Spec.map (CommRingCat.ofHom (algebraMap O' L)) ≫ Spec.map (CommRingCat.ofHom (iota O O' hO)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **The canonical comparison `N ⊗_O O' → N'` for valuation subrings** (any extension `L/K`, any
ramification): `N` a smooth `O`-model of the abelian variety `A` (`gen : N_K ≅ A`), `N'` an
`O'`-scheme with `gen' : N'_L ≅ A_L` and the Néron mapping property (in the form of the kernel's
Néron models over a valuation ring). Then a unique `O'`-morphism `u` induces the canonical
identification on generic fibres, and `u_L` is an isomorphism. -/
theorem comparison_valuationSubring (O : ValuationSubring K) (O' : ValuationSubring L)
    (hO : O'.comap (algebraMap K L) = O) (A : PkgI3.AbVar K)
    (N : Over (Spec (CommRingCat.of O))) [Smooth N.hom]
    (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj N ≅ A.X)
    (N' : Over (Spec (CommRingCat.of O')))
    (gen' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).obj N' ≅ (A.baseChange L).X)
    (hN' : ∀ (Y : Over (Spec (CommRingCat.of O'))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map f ≫ gen'.hom) :
    ∃ u : (Over.pullback (Spec.map (CommRingCat.ofHom (iota O O' hO)))).obj N ⟶ N',
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map u ≫ gen'.hom =
        (genIso (Spec.map (CommRingCat.ofHom (iota O O' hO)))
          (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O' L)))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) (iota_square O O' hO) N A.X gen).hom) ∧
      (∀ v : (Over.pullback (Spec.map (CommRingCat.ofHom (iota O O' hO)))).obj N ⟶ N',
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map v ≫ gen'.hom =
          (genIso (Spec.map (CommRingCat.ofHom (iota O O' hO)))
            (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O' L)))
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) (iota_square O O' hO) N A.X gen).hom → v = u) ∧
      IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O' L)))).map u) := by
  obtain ⟨u, hu, huniq⟩ := exists_unique_comparison (Spec.map (CommRingCat.ofHom (iota O O' hO)))
    (Spec.map (CommRingCat.ofHom (algebraMap O K))) (Spec.map (CommRingCat.ofHom (algebraMap O' L)))
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) (iota_square O O' hO) N A.X gen N' gen' hN'
  exact ⟨u, hu, huniq, comparison_generic_isIso _ _ _ _ _ N A.X gen N' gen' u hu⟩

end Valuation

end ToricBaseChange.Comparison
