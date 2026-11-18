import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sober

/-!
# Vanishing of an étale kernel with trivial generic fibre

Let `S` be an irreducible scheme (for example `Spec O'`, `O'` a discrete valuation ring) with
generic point `η`.

* `isClosed_range_section`: a section `e` of a separated morphism `f : P → S` is a closed immersion,
  so its image is closed.
* `etale_section`, `isOpen_range_etale_section`: a section of an étale morphism is étale, hence an
  open map, so its image is open.
* `subset_range_section_of_generic`: if `f : P → S` is flat, locally of finite presentation and
  separated, `e` is a section, and `W ⊆ P` is open with every point of `W` over `η` in `e(S)`, then
  `W ⊆ e(S)`. Proof: `W \ e(S)` is open; its image under the open map `f` is open in `S`; a nonempty
  open of the irreducible `S` contains `η`; so `W \ e(S)` has a point over `η`, which lies in `e(S)`.
* `kernel_subset_section`: for `v : P → P'` with `P'` étale over `S` with section `e'`, if every point
  of `P` over `η` mapping into `e'(S)` lies in `e(S)` (trivial generic kernel), then every point of `P`
  mapping into `e'(S)` lies in `e(S)` (trivial kernel). Here `P`, `P'` are the `m`-torsion of the two
  models and `v` the comparison: the kernel `v⁻¹(e'(S))` is open, and the step above applies.

No ramification hypothesis, no henselization, no semistability.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology

namespace ToricBaseChange.Vanishing

universe u

variable {S P P' : Scheme.{u}}

/-- A section of a separated morphism has closed image. -/
theorem isClosed_range_section (f : P ⟶ S) [IsSeparated f] (e : S ⟶ P) (he : e ≫ f = 𝟙 S) :
    IsClosed (Set.range e) := by
  haveI : IsClosedImmersion (e ≫ f) := by rw [he]; infer_instance
  haveI : IsClosedImmersion e := IsClosedImmersion.of_comp e f
  exact e.isClosedEmbedding.isClosed_range

/-- A section of an étale morphism is étale. -/
theorem etale_section (f : P ⟶ S) [Etale f] (e : S ⟶ P) (he : e ≫ f = 𝟙 S) : Etale e := by
  have h1 : Etale (e ≫ f) := by rw [he]; infer_instance
  exact MorphismProperty.of_postcomp @Etale (W' := @Etale) e f (inferInstanceAs (Etale f)) h1

/-- A flat morphism locally of finite presentation has open image. -/
theorem isOpen_range_of_flat (g : S ⟶ P) [Flat g] [LocallyOfFinitePresentation g] :
    IsOpen (Set.range g) :=
  (isOpenMap_of_generalizingMap g (Flat.generalizingMap g)).isOpen_range

/-- A section of an étale morphism has open image. -/
theorem isOpen_range_etale_section (f : P ⟶ S) [Etale f] (e : S ⟶ P) (he : e ≫ f = 𝟙 S) :
    IsOpen (Set.range e) := by
  obtain ⟨hfl, -, hlfp⟩ := (Etale.iff_flat_and_formallyUnramified (f := e)).mp (etale_section f e he)
  haveI := hfl
  haveI := hlfp
  exact isOpen_range_of_flat e

/-- **Vanishing**: an open subset of a flat, locally finitely presented, separated `S`-scheme whose
generic-fibre points all lie on a section is contained in the section. -/
theorem subset_range_section_of_generic [IrreducibleSpace S] (f : P ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (e : S ⟶ P) (he : e ≫ f = 𝟙 S)
    (W : Set P) (hW : IsOpen W) (hgen : ∀ w ∈ W, f w = genericPoint S → w ∈ Set.range e) :
    W ⊆ Set.range e := by
  intro w hw
  by_contra hne
  have hWo : IsOpen (W ∩ (Set.range e)ᶜ) := hW.inter (isClosed_range_section f e he).isOpen_compl
  have himg : IsOpen (f '' (W ∩ (Set.range e)ᶜ)) :=
    isOpenMap_of_generalizingMap f (Flat.generalizingMap f) _ hWo
  have hgp : genericPoint S ∈ f '' (W ∩ (Set.range e)ᶜ) :=
    ((genericPoint_spec S).mem_open_set_iff himg).mpr ⟨f w, Set.mem_univ _, w, ⟨hw, hne⟩, rfl⟩
  obtain ⟨w', ⟨hw'W, hw'e⟩, hw'f⟩ := hgp
  exact hw'e (hgen w' hw'W hw'f)

/-- **Trivial generic kernel implies trivial kernel**, for `v : P → P'` with `P` flat, locally of
finite presentation and separated over the irreducible `S` and `P'` étale over `S`. -/
theorem kernel_subset_section [IrreducibleSpace S] (f : P ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (f' : P' ⟶ S) [Etale f']
    (e : S ⟶ P) (he : e ≫ f = 𝟙 S) (e' : S ⟶ P') (he' : e' ≫ f' = 𝟙 S) (v : P ⟶ P')
    (hgen : ∀ x : P, f x = genericPoint S → v x ∈ Set.range e' → x ∈ Set.range e) :
    ∀ x : P, v x ∈ Set.range e' → x ∈ Set.range e := by
  have hW : IsOpen (v ⁻¹' Set.range e') :=
    (isOpen_range_etale_section f' e' he').preimage v.continuous
  intro x hx
  exact subset_range_section_of_generic f e he _ hW (fun w hw hwf => hgen w hwf hw) hx

/-- The same over `Spec R`, `R` a domain (e.g. a discrete valuation ring). -/
theorem kernel_subset_section_spec {R : Type u} [CommRing R] [IsDomain R]
    (f : P ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (f' : P' ⟶ Spec (CommRingCat.of R)) [Etale f']
    (e : Spec (CommRingCat.of R) ⟶ P) (he : e ≫ f = 𝟙 _) (e' : Spec (CommRingCat.of R) ⟶ P')
    (he' : e' ≫ f' = 𝟙 _) (v : P ⟶ P')
    (hgen : ∀ x : P, f x = genericPoint (Spec (CommRingCat.of R)) → v x ∈ Set.range e' →
      x ∈ Set.range e) :
    ∀ x : P, v x ∈ Set.range e' → x ∈ Set.range e := by
  haveI : IrreducibleSpace (Spec (CommRingCat.of R)) := by
    change IrreducibleSpace (PrimeSpectrum R); infer_instance
  exact kernel_subset_section f f' e he e' he' v hgen

end ToricBaseChange.Vanishing
