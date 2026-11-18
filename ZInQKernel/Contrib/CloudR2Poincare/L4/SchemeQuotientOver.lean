import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientAction
import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Recovering the actual Over-k quotient from a native scheme coequalizer

All hypotheses here are ordinary native data supplied by a scheme quotient.
No provider theorem is assumed or copied. The structure map descends through
its genuine IsColimit cofork; the kernel pair is reflected by Over.forget.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- A jointly monic pair over S is jointly monic on ALL underlying morphisms.
The equal second component forces equal structure maps on the arbitrary test. -/
theorem jointlyMono_forget_over {S : Scheme} {R X : Over S} (a b : R ⟶ X)
    (h : JointlyMono₂ a b) : JointlyMono₂ a.left b.left := by
  constructor
  intro T f g ha hb
  let T₀ := Over.mk (f ≫ R.hom)
  have hw : g ≫ R.hom = f ≫ R.hom := by
    rw [← Over.w b]
    simpa only [Category.assoc] using congrArg (· ≫ X.hom) hb.symm
  let f₀ : T₀ ⟶ R := Over.homMk f rfl
  let g₀ : T₀ ⟶ R := Over.homMk g hw
  have h₀ : f₀ = g₀ := h.right_cancellation f₀ g₀
    (Over.OverMorphism.ext ha) (Over.OverMorphism.ext hb)
  exact congrArg Over.Hom.left h₀

/-- The actual Over relation yields a native Scheme equivalence relation. -/
def schemeRelationOfOver {S : Scheme} {R X : Over S} {a b : R ⟶ X}
    (e : EquivalenceRelation a b) : EquivalenceRelation a.left b.left :=
  let F := Over.forget S
  haveI : JointlyMono₂ (F.map a) (F.map b) := jointlyMono_forget_over a b e.toJointlyMono₂
  { __ := e.toReflexiveRelation.map F
    __ := e.toSymmetricRelation.map F
    __ := e.toTransitiveRelation.map F }

/-- The ALL-scheme Hom relation induced by a native internal relation is an equivalence. -/
theorem homRelation_equivalence {R X : Scheme} {a b : R ⟶ X}
    (e : EquivalenceRelation a b) (T : Scheme) :
    Equivalence (fun x y : T ⟶ X => ∃ r : T ⟶ R, r ≫ a = x ∧ r ≫ b = y) := by
  let F := coyoneda.obj (Opposite.op T)
  haveI : JointlyMono₂ (F.map a) (F.map b) := by
    constructor
    intro Y f g ha hb
    ext y
    exact e.right_cancellation (f y) (g y) (congr($(ha) y)) (congr($(hb) y))
  let E : EquivalenceRelation (F.map a) (F.map b) :=
    { __ := e.toReflexiveRelation.map F
      __ := e.toSymmetricRelation.map F
      __ := e.toTransitiveRelation.map F }
  exact TypeCat.equivalence_of_equivalenceRelation E

/-- Swapping the actual two projections swaps Hom pairs but preserves equivalence. -/
theorem homRelation_equivalence_swap {R X : Scheme} {a b : R ⟶ X}
    (e : EquivalenceRelation a b) (T : Scheme) :
    Equivalence (fun x y : T ⟶ X => ∃ r : T ⟶ R, r ≫ b = x ∧ r ≫ a = y) := by
  have h := homRelation_equivalence e T
  constructor
  · intro x
    obtain ⟨r, ha, hb⟩ := h.refl x
    exact ⟨r, hb, ha⟩
  · intro x y hxy
    obtain ⟨r, hb, ha⟩ := hxy
    obtain ⟨r', ha', hb'⟩ := h.symm (show ∃ r : T ⟶ R, r ≫ a = y ∧ r ≫ b = x from ⟨r, ha, hb⟩)
    exact ⟨r', hb', ha'⟩
  · intro x y z hxy hyz
    obtain ⟨r, hb, ha⟩ := hxy
    obtain ⟨s, sb, sa⟩ := hyz
    obtain ⟨q, qa, qb⟩ := h.trans
      (show ∃ r : T ⟶ R, r ≫ a = z ∧ r ≫ b = y from ⟨s, sa, sb⟩)
      (show ∃ r : T ⟶ R, r ≫ a = y ∧ r ≫ b = x from ⟨r, ha, hb⟩)
    exact ⟨q, qb, qa⟩

/-- Forgetting then reflecting the ACTUAL scheme kernel pair recovers the Over diagram. -/
theorem over_kernelPair_of_scheme {S : Scheme} {R X Y : Over S}
    (a b : R ⟶ X) (p : X ⟶ Y)
    (h : IsPullback a.left b.left p.left p.left) : IsPullback a b p p := by
  exact IsPullback.of_map_of_faithful (Over.forget S) h

/-- Native scheme coequalizer + finite-flat quotient data produces the actual L1 record. -/
theorem stabilizerQuotient_of_scheme_coequalizer
    {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : L1.FiniteStabilizerScheme A L) {Y : Scheme} (p : A.X.left ⟶ Y)
    (w : (snd H.K A.X).left ≫ p = (quotientTarget A L H).left ≫ p)
    (hcol : IsColimit (Cofork.ofπ p w))
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hpb : IsPullback (snd H.K A.X).left (quotientTarget A L H).left p p) :
    Nonempty (L1.StabilizerQuotient A L H) := by
  have hbase : (snd H.K A.X).left ≫ A.X.hom =
      (quotientTarget A L H).left ≫ A.X.hom := by rw [Over.w, Over.w]
  let qbase : Y ⟶ Spec (.of k) := Cofork.IsColimit.desc hcol A.X.hom hbase
  have hqbase : p ≫ qbase = A.X.hom := Cofork.IsColimit.π_desc' hcol A.X.hom hbase
  let Q : Over (Spec (.of k)) := Over.mk qbase
  let q : A.X ⟶ Q := Over.homMk p hqbase
  exact ⟨{
    Q := Q
    q := q
    flat := inferInstanceAs (Flat p)
    finite := inferInstanceAs (IsFinite p)
    surjective := inferInstanceAs (Surjective p)
    finitePresentation := inferInstanceAs (LocallyOfFinitePresentation p)
    kernelPair := over_kernelPair_of_scheme (quotientTarget A L H) (snd H.K A.X) q hpb.flip }⟩

end ZInQ.Contrib.CloudR2Poincare.L4
