import ZInQKernel.Contrib.CloudR2Poincare.L3.B2RationalDetection

/-! Actual Mumford coefficient: all p1 direct images vanish, and all p2 direct
images have finite closed support, from rational vanishing and real model data.
The finiteness parameter here is later supplied by L2's proved hA reduction. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The actual finite set of base-scheme points supplied by rational stabilizers. -/
def stabilizerPointSet {k : Type u} [Field k] (B : PkgI3.AbVar k)
    (M : B.X.left.Modules) [M.IsInvertible] : Set B.X.left :=
  (fun b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X => b.left (IsLocalRing.closedPoint k)) ''
    (L1.translationStabilizer B.X (Scheme.Pic.mk M) : Set _)

/-- Finiteness is transported to the actual base-point image, not a surrogate scheme. -/
theorem stabilizerPointSet_finite {k : Type u} [Field k] (B : PkgI3.AbVar k)
    (M : B.X.left.Modules) [M.IsInvertible]
    (hfinite : (L1.translationStabilizer B.X (Scheme.Pic.mk M)).Finite) :
    (stabilizerPointSet B M).Finite := hfinite.image _

/-- Every support point is genuinely closed on the original abelian variety. -/
theorem stabilizerPointSet_closed_points {k : Type u} [Field k] [IsAlgClosed k]
    (B : PkgI3.AbVar k) (M : B.X.left.Modules) [M.IsInvertible] :
    ∀ y ∈ stabilizerPointSet B M, IsClosed ({y} : Set B.X.left) := by
  rintro y ⟨b, hb, rfl⟩
  exact (pointEquivClosedPoint B.X.hom ⟨b.left, Over.w b⟩).property

/-- A finite set of closed points is closed without a T1 hypothesis. -/
theorem isClosed_of_finite_closed_points {X : Type u} [TopologicalSpace X]
    (S : Set X) (hS : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    IsClosed S := by
  convert hS.isClosed_biUnion (fun x hx => hclosed x hx) using 1
  ext x
  simp

/-- B1 and the one square, under the actual non-image assumption, force every
higher direct image of the actual Mumford coefficient under p1 to be zero. -/
theorem higherDirectImages_fst_zero_of_not_in_image
    (hB1 : NativePicZeroVanishing.{u}) (hSquare : L2.NativeTheoremOfTheSquare.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (M N : B.X.left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hN : TranslationInvariant B (Scheme.Pic.mk N))
    (hnot : ¬ ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X,
      Scheme.Pic.mk N = L1.translationClass B.X (Scheme.Pic.mk M) b) :
    ∀ q : ℕ, IsZero ((Scheme.Modules.higherDirectImage (fst B.X B.X).left q).obj
      (mumfordKernelBundle B M N)) := by
  let f := (fst B.X B.X).left
  haveI : IsProper f := inferInstanceAs (IsProper (pullback.fst B.X.hom B.X.hom))
  haveI : Flat f := inferInstanceAs (Flat (pullback.fst B.X.hom B.X.hom))
  intro q
  apply Scheme.Modules.isZero_of_forall_exists_isZero_restrict
  intro y
  obtain ⟨W, hy, hW⟩ := exists_zero_higherDirectImage_restriction_of_rational_fibres B f
    (mumfordKernelBundle B M N) (fun b => (firstSlice B b).left)
    (isPullback_firstSlice B) ⊤
    (fun b _ i => firstSlice_cohomology_vanish_of_not_in_image B M N hB1 hSquare hN hnot b i)
    y (by trivial)
  exact ⟨W, hy, hW q⟩

/-- B1 and the one square force the actual p2 higher-direct-image stalks to
vanish off the finite closed stabilizer-point set. -/
theorem higherDirectImages_snd_supported_on_stabilizer
    (hB1 : NativePicZeroVanishing.{u}) (hSquare : L2.NativeTheoremOfTheSquare.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (M N : B.X.left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hfinite : (L1.translationStabilizer B.X (Scheme.Pic.mk M)).Finite) :
    ∀ q : ℕ, ∀ y : B.X.left, y ∉ stabilizerPointSet B M →
      Subsingleton (((Scheme.Modules.higherDirectImage (snd B.X B.X).left q).obj
        (mumfordKernelBundle B M N)).presheaf.stalk y) := by
  let f := (snd B.X B.X).left
  haveI : IsProper f := inferInstanceAs (IsProper (pullback.snd B.X.hom B.X.hom))
  haveI : Flat f := inferInstanceAs (Flat (pullback.snd B.X.hom B.X.hom))
  have hclosed : IsClosed (stabilizerPointSet B M) :=
    isClosed_of_finite_closed_points _ (stabilizerPointSet_finite B M hfinite)
      (stabilizerPointSet_closed_points B M)
  let V : B.X.left.Opens := ⟨(stabilizerPointSet B M)ᶜ, hclosed.isOpen_compl⟩
  intro q y hy
  obtain ⟨W, hyW, hW⟩ := exists_zero_higherDirectImage_restriction_of_rational_fibres B f
    (mumfordKernelBundle B M N) (fun b => (secondSlice B b).left)
    (isPullback_secondSlice B) V
    (fun b hb i => secondSlice_cohomology_vanish_off_stabilizer B M N hB1 hSquare b
      (by intro h; exact hb ⟨b, h, rfl⟩) i) y hy
  exact subsingleton_stalk_of_isZero_restrict _ W y hyW (hW q)

end ZInQ.Contrib.CloudR2Poincare.L3
