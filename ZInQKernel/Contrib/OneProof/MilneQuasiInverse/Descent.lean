-- Vendored from openai/math (https://github.com/openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae),
-- Apache-2.0; see LICENSE and NOTICE.md in ZInQKernel/Contrib/OneProof/MilneQuasiInverse/.
-- Source files (all at that commit; Git blob SHA-1 / SHA-256 / upstream line count):
--   lean/OAI/AlgebraicGeometry/FormalGeometry/Completion/OverEffectiveDescent.lean
--     8732be16cd8087897d1f78d67c053607cff71977 /
--     f438ccf0407e2dc9ed6472d46fdd0228a08bb26d14fa873ecd57ea8869a7e81a / 44 lines (whole proof body kept)
--   lean/OAI/AlgebraicGeometry/Picard/Homomorphisms/GroupDescent.lean
--     09aa0c686a95d8d2bb8f624e91bba2b663154d1c /
--     e32a098eded998cec64db44ce33762944e0691519b5ab2d9a7349fc38ba85a4d / 122 lines
--     (cut: only `overRelations_left`, `effectiveEpi_over_of_fpqc`, `groupHom_pow_isMonHom`,
--     `effectiveEpi_tensor_over_of_fpqc`, upstream lines 15, 23-51, 79-107)
--   lean/OAI/AlgebraicGeometry/AbelianScheme/IsogenyQuotient/GroupKernelPowerDescent.lean
--     af69877b23c79f93a7114ec55b17b4198eaf5aab /
--     1ce80408aeee6ad89f9746308ab74cca2c26afa327096688cde41203f7bf5a67 / 51 lines (whole proof body kept)
--   lean/OAI/AlgebraicGeometry/AbelianScheme/IsogenyQuotient/FppfPowerComplement.lean
--     c6f1a83a70cc672a27210a4cbf1969fca17e2cf6 /
--     82d4d3f5db1634ca7e40af16a7a60a58767e7681fd5d9b2b5ee09f980c2b639d / 39 lines
--     (cut: `exists_fppf_power_complement`, upstream lines 16-28)
-- Changed for this repository: this banner; the four upstream files are concatenated into one
-- module, each in its own section with its upstream namespace tail kept as a sub-namespace of
-- `ZInQ.Contrib.MilneQuasiInverse.Descent`; the upstream imports of other `OAI` modules
-- (`GroupDescent` imports `KernelGroup`, which pulls in the Picard/Frobenius kernel forest) are
-- replaced by named Mathlib imports, since the cut declarations use none of that forest;
-- qualified cross-references are re-pointed to the new namespaces; the local `let` instance
-- `IsStableUnderComposition @Surjective` in `effectiveEpi_tensor_over_of_fpqc` is dropped
-- because pinned Mathlib already provides it (`MorphismProperty.IsMultiplicative @Surjective`,
-- Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean); the GroupDescent file-level
-- `set_option backward.isDefEq.respectTransparency.types false` is kept, scoped to the
-- GroupDescent section. Proof bodies are otherwise verbatim.
-- Status: compiled by milne-compile on 2026-11-16 at Lean 4.35.0 / Mathlib v4.35.0
-- (no change to this file needed); upstream was written against Lean 4.34.1 / Mathlib d13f23b.
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# fpqc descent of group homomorphisms and the power complement

Ported cut of four openai/math files (see the banner). For a homomorphism `f : A ⟶ B` of group
objects over a scheme `S`, with `A` commutative and `f.left` flat, surjective and quasi-compact,
and `n` killing every test-object point of the kernel of `f`, there is a homomorphism
`r : B ⟶ A` with `f ≫ r = (𝟙 A) ^ n` and `r ≫ f = (𝟙 B) ^ n`. The descent is along the actual
scheme morphism `f.left` (Mathlib's fpqc `EffectiveEpi` instance), for arbitrary test schemes.
-/

namespace ZInQ.Contrib.MilneQuasiInverse.Descent

/-! ## Upstream `FormalGeometry/Completion/OverEffectiveDescent.lean` (whole) -/

/-! # Over Effective Descent -/

namespace OverEffectiveDescent.Construction

noncomputable section

/-! Effective descent of actual morphisms while retaining their map to the base.
The argument is the base-preserving form of the scheme effective-epimorphism property. -/

open _root_.CategoryTheory

universe u v

/-- A scheme effective epimorphism gives unique descent in the category over a fixed base. -/
theorem over_existsUnique_desc_of_effectiveEpi
    {C : Type u} [Category.{v} C] {S : C} {A B T : Over S}
    (q : A ⟶ B) [EffectiveEpi q.left] (f : A ⟶ T)
    (hf : ∀ (U : Over S) (a b : U ⟶ A), a ≫ q = b ≫ q → a ≫ f = b ≫ f) :
    ∃! g : B ⟶ T, q ≫ g = f := by
  have hleft : ∀ {Z : C} (a b : Z ⟶ A.left),
      a ≫ q.left = b ≫ q.left → a ≫ f.left = b ≫ f.left := by
    intro Z a b hab
    have hb : b ≫ A.hom = a ≫ A.hom := by
      rw [← q.w, ← Category.assoc, ← Category.assoc, hab]
    let a' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk a rfl
    let b' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk b hb
    exact congrArg (fun e => e.left) (hf _ a' b' (Over.OverMorphism.ext hab))
  let g := EffectiveEpi.desc q.left f.left hleft
  have hg : q.left ≫ g = f.left := EffectiveEpi.fac _ _ _
  have hbase : g ≫ T.hom = B.hom := by
    apply (cancel_epi q.left).mp
    rw [← Category.assoc, hg, f.w, q.w]
  refine ⟨Over.homMk g hbase, Over.OverMorphism.ext hg, ?_⟩
  intro g' hg'
  apply Over.OverMorphism.ext
  exact EffectiveEpi.uniq q.left f.left hleft g'.left
    (congrArg (fun e => e.left) hg')

end

end OverEffectiveDescent.Construction

/-! ## Upstream `Picard/Homomorphisms/GroupDescent.lean` (cut) -/

/-! # Group Descent -/

namespace GroupDescent

noncomputable section

/-! Descent of actual group morphisms through the Frobenius quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B C : Over S}

theorem overRelations_left (f : A ⟶ B) (g : A ⟶ C)
    (hg : ∀ {T : Over S} (x y : T ⟶ A), x ≫ f = y ≫ f → x ≫ g = y ≫ g) :
    ∀ {T : Scheme.{u}} (x y : T ⟶ A.left),
      x ≫ f.left = y ≫ f.left → x ≫ g.left = y ≫ g.left := by
  intro T x y hxy
  let T' : Over S := Over.mk (x ≫ A.hom)
  let x' : T' ⟶ A := Over.homMk x rfl
  let y' : T' ⟶ A := Over.homMk y (by
    change y ≫ A.hom = x ≫ A.hom
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hxy])
  exact congrArg Over.Hom.left (hg x' y' (Over.OverMorphism.ext hxy))

/-- The fpqc effective epimorphism property also holds in the slice. -/
theorem effectiveEpi_over_of_fpqc (f : A ⟶ B)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left] : EffectiveEpi f := by
  constructor
  refine ⟨{ desc := ?_, fac := ?_, uniq := ?_ }⟩
  · intro W g hg
    let d := EffectiveEpi.desc f.left g.left (overRelations_left f g hg)
    refine Over.homMk d ?_
    apply (cancel_epi f.left).mp
    rw [← Category.assoc, EffectiveEpi.fac, Over.w g, Over.w f]
  · intro W g hg
    apply Over.OverMorphism.ext
    exact EffectiveEpi.fac f.left g.left (overRelations_left f g hg)
  · intro W g hg m hm
    apply Over.OverMorphism.ext
    exact EffectiveEpi.uniq f.left g.left (overRelations_left f g hg)
      m.left (congrArg Over.Hom.left hm)

variable [GrpObj A] [GrpObj B] [GrpObj C]

theorem groupHom_pow_isMonHom [IsCommMonObj C]
    (g : A ⟶ C) [IsMonHom g] (n : ℕ) : IsMonHom (g ^ n) := by
  induction n with
  | zero =>
      change IsMonHom (toUnit A ≫ η[C])
      infer_instance
  | succ n ih =>
      have : IsMonHom (g ^ n) := ih
      rw [pow_succ, Hom.mul_def]
      infer_instance

omit [GrpObj A] [GrpObj B] in
theorem effectiveEpi_tensor_over_of_fpqc {X Y : Over S}
    (f : A ⟶ B) (g : X ⟶ Y)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    [Flat g.left] [Surjective g.left] [QuasiCompact g.left] :
    EffectiveEpi (f ⊗ₘ g) := by
  have hprop (P : MorphismProperty Scheme.{u})
      [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
      (hf : P f.left) (hg : P g.left) : P (f ⊗ₘ g).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap hf hg (Over.w f).symm (Over.w g).symm
  have : Flat (f ⊗ₘ g).left := hprop (@Flat) inferInstance inferInstance
  have : Surjective (f ⊗ₘ g).left :=
    hprop (@AlgebraicGeometry.Surjective) inferInstance inferInstance
  have : QuasiCompact (f ⊗ₘ g).left := hprop (@QuasiCompact) inferInstance inferInstance
  exact effectiveEpi_over_of_fpqc (f ⊗ₘ g)

end Construction

end

end GroupDescent

/-! ## Upstream `AbelianScheme/IsogenyQuotient/GroupKernelPowerDescent.lean` (whole) -/

/-! # Group Kernel Power Descent -/

namespace GroupKernelPowerDescent.Construction

noncomputable section

/-! A multiplication map descends through a faithfully flat group
quotient when its actual kernel is killed by that multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (q : A ⟶ B) [IsMonHom q] [EffectiveEpi q.left]
  [Epi (q ⊗ₘ q)]

theorem groupHom_descends_of_kernel (f : A ⟶ C) [IsMonHom f]
    (hf : ∀ (T : Over S) (x : T ⟶ A), x ≫ q = 1 → x ≫ f = 1) :
    ∃ g : B ⟶ C, IsMonHom g ∧ q ≫ g = f := by
  obtain ⟨g, hg, _⟩ := OverEffectiveDescent.Construction.over_existsUnique_desc_of_effectiveEpi q f (by
    intro T a b hab
    have hkill := hf T (a / b) (by rw [GrpObj.div_comp, hab, div_self'])
    rw [GrpObj.div_comp] at hkill
    exact div_eq_one.mp hkill)
  have : IsMonHom g := {
    one_hom := by
      rw [← IsMonHom.one_hom q, Category.assoc, hg, IsMonHom.one_hom f]
    mul_hom := by
      apply (cancel_epi (q ⊗ₘ q)).mp
      rw [← Category.assoc, ← IsMonHom.mul_hom q, Category.assoc, hg,
        IsMonHom.mul_hom f, ← Category.assoc, tensorHom_comp_tensorHom, hg]
  }
  exact ⟨g, inferInstance, hg⟩

omit [GrpObj C] in
theorem exists_groupKernel_power_complement [IsCommMonObj A] (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), x ≫ q = 1 → x ^ n = 1) :
    ∃ v : B ⟶ A, IsMonHom v ∧ q ≫ v = (𝟙 A) ^ n := by
  have : IsMonHom ((𝟙 A) ^ n) := GroupDescent.Construction.groupHom_pow_isMonHom _ _
  apply groupHom_descends_of_kernel q ((𝟙 A) ^ n)
  intro T x hx
  simpa only [MonObj.comp_pow, Category.comp_id] using hn T x hx

end

end GroupKernelPowerDescent.Construction

/-! ## Upstream `AbelianScheme/IsogenyQuotient/FppfPowerComplement.lean` (cut) -/

/-! # Fppf Power Complement -/

namespace FppfPowerComplement.Construction

noncomputable section

/-! The actual multiplication map descends through an fpqc group
quotient, with both complementary composition identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A]
  (f : A ⟶ B) [IsMonHom f] [Flat f.left] [Surjective f.left] [QuasiCompact f.left]

theorem exists_fppf_power_complement (n : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    ∃ r : B ⟶ A, IsMonHom r ∧ f ≫ r = (𝟙 A) ^ n ∧ r ≫ f = (𝟙 B) ^ n := by
  have : EffectiveEpi f := GroupDescent.Construction.effectiveEpi_over_of_fpqc f
  have : EffectiveEpi (f ⊗ₘ f) := GroupDescent.Construction.effectiveEpi_tensor_over_of_fpqc f f
  obtain ⟨r, hrmon, hfr⟩ := GroupKernelPowerDescent.Construction.exists_groupKernel_power_complement f n hn
  refine ⟨r, hrmon, hfr, ?_⟩
  apply (cancel_epi f).mp
  rw [← Category.assoc, hfr, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, Category.comp_id]

end

end FppfPowerComplement.Construction

end ZInQ.Contrib.MilneQuasiInverse.Descent
