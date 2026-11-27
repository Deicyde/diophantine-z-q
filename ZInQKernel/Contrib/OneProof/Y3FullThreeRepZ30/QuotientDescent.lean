import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Quotient adapters for integral Y3 descent

Category-level steps used after a free finite quotient:

* freeness of the total action relation from freeness of the base relation, along an
  equivariant map;
* the self kernel pair of a quotient map from the canonical comparison map;
* descent of maps along an effective epimorphism with a given kernel pair, in the
  orientation used by `SGRSplit.QMFamFibre` for endomorphisms and sections.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Y3QuotientDescent

variable {C : Type u} [Category.{v} C]

/-! ### Relations -/

/-- Freeness passes from the base relation to the total relation along an
equivariant map. `uA`, `uX` are the group coordinates, `prA`, `prX` the projections,
`aA`, `aX` the actions, and `t` the map induced by the identity of the group and the
family map. -/
theorem jointlyMono_total_of_base {G A X RA RX : C} (p : A ⟶ X)
    (uA : RA ⟶ G) (aA prA : RA ⟶ A) (uX : RX ⟶ G) (aX prX : RX ⟶ X)
    (t : RA ⟶ RX) (htu : t ≫ uX = uA) (hta : t ≫ aX = aA ≫ p)
    (htp : t ≫ prX = prA ≫ p)
    (hRA : ∀ {T : C} (x y : T ⟶ RA), x ≫ uA = y ≫ uA → x ≫ prA = y ≫ prA → x = y)
    (hX : ∀ {T : C} (x y : T ⟶ RX), x ≫ aX = y ≫ aX → x ≫ prX = y ≫ prX → x = y)
    {T : C} (x y : T ⟶ RA) (ha : x ≫ aA = y ≫ aA) (hp : x ≫ prA = y ≫ prA) :
    x = y := by
  have hxt : x ≫ t = y ≫ t := by
    apply hX
    · rw [Category.assoc, Category.assoc, hta, ← Category.assoc, ← Category.assoc, ha]
    · rw [Category.assoc, Category.assoc, htp, ← Category.assoc, ← Category.assoc, hp]
  refine hRA x y ?_ hp
  rw [← htu, ← Category.assoc, ← Category.assoc, hxt]

/-- Joint monicity of the legs gives a monic comparison map. -/
theorem mono_lift_of_jointlyMono {R A S : C} (s : A ⟶ S) [HasPullback s s]
    (a pr : R ⟶ A) (h : a ≫ s = pr ≫ s)
    (hj : ∀ {T : C} (x y : T ⟶ R), x ≫ a = y ≫ a → x ≫ pr = y ≫ pr → x = y) :
    Mono (pullback.lift a pr h) := by
  constructor
  intro T x y hxy
  apply hj x y
  · simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun k => k ≫ pullback.fst s s) hxy
  · simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (fun k => k ≫ pullback.snd s s) hxy

/-- A monic comparison map makes the legs jointly monic. -/
theorem jointlyMono_of_mono_lift {R A S : C} (s : A ⟶ S) [HasPullback s s]
    (a pr : R ⟶ A) (h : a ≫ s = pr ≫ s) [Mono (pullback.lift a pr h)]
    {T : C} (x y : T ⟶ R) (ha : x ≫ a = y ≫ a) (hp : x ≫ pr = y ≫ pr) : x = y := by
  apply (cancel_mono (pullback.lift a pr h)).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using ha
  · simpa only [Category.assoc, pullback.lift_snd] using hp

/-- The canonical comparison map, not an arbitrary isomorphism, gives the self
kernel pair with the action first and the projection second. -/
theorem selfKernelPair_of_comparison {R A B : C} (q : A ⟶ B) [HasPullback q q]
    (a pr : R ⟶ A) (hq : a ≫ q = pr ≫ q) [IsIso (pullback.lift a pr hq)] :
    IsPullback a pr q q :=
  IsPullback.of_iso_pullback ⟨hq⟩ (asIso (pullback.lift a pr hq)) (by simp) (by simp)

/-! ### Descent along an effective epimorphism with a kernel pair -/

/-- A map equalizing a kernel pair satisfies the hypothesis of `EffectiveEpi.desc`. -/
theorem compat_of_kernelPair {R A B Z : C} {a pr : R ⟶ A} {q : A ⟶ B}
    (hK : IsPullback a pr q q) (e : A ⟶ Z) (he : a ≫ e = pr ≫ e)
    {T : C} (g₁ g₂ : T ⟶ A) (hg : g₁ ≫ q = g₂ ≫ q) : g₁ ≫ e = g₂ ≫ e :=
  calc g₁ ≫ e = (hK.lift g₁ g₂ hg ≫ a) ≫ e := by rw [hK.lift_fst]
    _ = hK.lift g₁ g₂ hg ≫ a ≫ e := Category.assoc _ _ _
    _ = hK.lift g₁ g₂ hg ≫ pr ≫ e := by rw [he]
    _ = (hK.lift g₁ g₂ hg ≫ pr) ≫ e := (Category.assoc _ _ _).symm
    _ = g₂ ≫ e := by rw [hK.lift_snd]

/-- Maps out of the target of an effective epimorphism agree once they agree after
precomposition. -/
theorem eq_of_effectiveEpi {X Y W : C} (q : Y ⟶ X) [EffectiveEpi q] {m₁ m₂ : X ⟶ W}
    (h : q ≫ m₁ = q ≫ m₂) : m₁ = m₂ := by
  have hc : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ q ≫ m₁ = g₂ ≫ q ≫ m₁ := by
    intro Z g₁ g₂ hg
    rw [← Category.assoc, hg, Category.assoc]
  exact (EffectiveEpi.uniq q (q ≫ m₁) hc m₁ rfl).trans
    (EffectiveEpi.uniq q (q ≫ m₁) hc m₂ h.symm).symm

/-- Descend a map that equalizes the kernel pair. -/
noncomputable def descend {R A B Z : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) (e : A ⟶ Z) (he : a ≫ e = pr ≫ e) : B ⟶ Z :=
  EffectiveEpi.desc q e fun g₁ g₂ hg => compat_of_kernelPair hK e he g₁ g₂ hg

@[reassoc]
theorem descend_fac {R A B Z : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) (e : A ⟶ Z) (he : a ≫ e = pr ≫ e) :
    q ≫ descend hK e he = e :=
  EffectiveEpi.fac q e fun g₁ g₂ hg => compat_of_kernelPair hK e he g₁ g₂ hg

theorem eq_descend {R A B Z : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) (e : A ⟶ Z) (he : a ≫ e = pr ≫ e) (m : B ⟶ Z)
    (hm : q ≫ m = e) : m = descend hK e he :=
  eq_of_effectiveEpi q (hm.trans (descend_fac hK e he).symm)

/-- An equivariant map followed by a quotient map equalizes the source relation. -/
theorem equivariant_compat {R₁ R₂ X A B : C} {a₁ p₁ : R₁ ⟶ X} {a₂ p₂ : R₂ ⟶ A}
    {q : A ⟶ B} (hq : a₂ ≫ q = p₂ ≫ q) (φ : X ⟶ A) (t : R₁ ⟶ R₂)
    (ha : t ≫ a₂ = a₁ ≫ φ) (hp : t ≫ p₂ = p₁ ≫ φ) :
    a₁ ≫ φ ≫ q = p₁ ≫ φ ≫ q :=
  calc a₁ ≫ φ ≫ q = (a₁ ≫ φ) ≫ q := (Category.assoc _ _ _).symm
    _ = (t ≫ a₂) ≫ q := by rw [ha]
    _ = t ≫ a₂ ≫ q := Category.assoc _ _ _
    _ = t ≫ p₂ ≫ q := by rw [hq]
    _ = (t ≫ p₂) ≫ q := (Category.assoc _ _ _).symm
    _ = (p₁ ≫ φ) ≫ q := by rw [hp]
    _ = p₁ ≫ φ ≫ q := Category.assoc _ _ _

/-- Endomorphism clause, in the orientation `f ≫ q = q ≫ f'`. -/
theorem endo_clause {R A B : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) (f : A ⟶ A) (he : a ≫ f ≫ q = pr ≫ f ≫ q) :
    f ≫ q = q ≫ descend hK (f ≫ q) he :=
  (descend_fac hK (f ≫ q) he).symm

/-- Section clause, in the orientation `η ≫ q = qX ≫ η'`. -/
theorem section_clause {RX X A B Y : C} {aX pX : RX ⟶ X} {qX : X ⟶ Y}
    [EffectiveEpi qX] (hKX : IsPullback aX pX qX qX) {q : A ⟶ B} (η : X ⟶ A)
    (he : aX ≫ η ≫ q = pX ≫ η ≫ q) :
    η ≫ q = qX ≫ descend hKX (η ≫ q) he :=
  (descend_fac hKX (η ≫ q) he).symm

/-- A descended endomorphism of the total space lies over the base. -/
theorem descend_over {R A B X Y : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) {π : A ⟶ X} {b : B ⟶ Y} {qX : X ⟶ Y}
    (hb : q ≫ b = π ≫ qX) (f : A ⟶ A) (hf : f ≫ π = π)
    (he : a ≫ f ≫ q = pr ≫ f ≫ q) :
    descend hK (f ≫ q) he ≫ b = b := by
  apply eq_of_effectiveEpi q
  calc q ≫ descend hK (f ≫ q) he ≫ b = (q ≫ descend hK (f ≫ q) he) ≫ b :=
        (Category.assoc _ _ _).symm
    _ = (f ≫ q) ≫ b := by rw [descend_fac hK (f ≫ q) he]
    _ = f ≫ π ≫ qX := by rw [Category.assoc, hb]
    _ = π ≫ qX := by rw [← Category.assoc, hf]
    _ = q ≫ b := hb.symm

/-- A descended section of the total-space map is a section of the quotient map. -/
theorem descend_section {RX X A B Y : C} {aX pX : RX ⟶ X} {qX : X ⟶ Y}
    [EffectiveEpi qX] (hKX : IsPullback aX pX qX qX) {π : A ⟶ X} {q : A ⟶ B}
    {b : B ⟶ Y} (hb : q ≫ b = π ≫ qX) (η : X ⟶ A) (hη : η ≫ π = 𝟙 X)
    (he : aX ≫ η ≫ q = pX ≫ η ≫ q) :
    descend hKX (η ≫ q) he ≫ b = 𝟙 Y := by
  apply eq_of_effectiveEpi qX
  calc qX ≫ descend hKX (η ≫ q) he ≫ b = (qX ≫ descend hKX (η ≫ q) he) ≫ b :=
        (Category.assoc _ _ _).symm
    _ = (η ≫ q) ≫ b := by rw [descend_fac hKX (η ≫ q) he]
    _ = η ≫ π ≫ qX := by rw [Category.assoc, hb]
    _ = qX := by rw [← Category.assoc, hη, Category.id_comp]
    _ = qX ≫ 𝟙 Y := (Category.comp_id _).symm

/-- Descent respects composition of endomorphisms. -/
theorem descend_comp {R A B : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) (f₁ f₂ : A ⟶ A)
    (h₁ : a ≫ f₁ ≫ q = pr ≫ f₁ ≫ q) (h₂ : a ≫ f₂ ≫ q = pr ≫ f₂ ≫ q)
    (h₁₂ : a ≫ (f₁ ≫ f₂) ≫ q = pr ≫ (f₁ ≫ f₂) ≫ q) :
    descend hK ((f₁ ≫ f₂) ≫ q) h₁₂ =
      descend hK (f₁ ≫ q) h₁ ≫ descend hK (f₂ ≫ q) h₂ := by
  apply eq_of_effectiveEpi q
  calc q ≫ descend hK ((f₁ ≫ f₂) ≫ q) h₁₂ = (f₁ ≫ f₂) ≫ q := descend_fac hK _ h₁₂
    _ = f₁ ≫ f₂ ≫ q := Category.assoc _ _ _
    _ = f₁ ≫ q ≫ descend hK (f₂ ≫ q) h₂ := by rw [descend_fac hK (f₂ ≫ q) h₂]
    _ = (f₁ ≫ q) ≫ descend hK (f₂ ≫ q) h₂ := (Category.assoc _ _ _).symm
    _ = (q ≫ descend hK (f₁ ≫ q) h₁) ≫ descend hK (f₂ ≫ q) h₂ := by
        rw [descend_fac hK (f₁ ≫ q) h₁]
    _ = q ≫ descend hK (f₁ ≫ q) h₁ ≫ descend hK (f₂ ≫ q) h₂ := Category.assoc _ _ _

/-- Descent sends the identity to the identity. -/
theorem descend_id {R A B : C} {a pr : R ⟶ A} {q : A ⟶ B} [EffectiveEpi q]
    (hK : IsPullback a pr q q) (h : a ≫ 𝟙 A ≫ q = pr ≫ 𝟙 A ≫ q) :
    descend hK (𝟙 A ≫ q) h = 𝟙 B := by
  apply eq_of_effectiveEpi q
  rw [descend_fac hK (𝟙 A ≫ q) h, Category.id_comp, Category.comp_id]

end Y3QuotientDescent
