import ZInQKernel.Contrib.CloudR2Poincare.L2.GraphMorphism
import ZInQKernel.Contrib.CloudR2Poincare.L2.RestrictionFromEmbedding
import ZInQKernel.Contrib.CloudR2Poincare.L4.B3
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Leray

/-!
# INTERNAL PolarizationRetract assembly with EVERY input a named proposition

The actual quotient, bundle and graph are used; the final target is unchanged.
A, B2, B3, ONE square, ONE Leray, quotient-bundle compatibility, the separately
owned C4 embedding output, and the still-unproved generic graph geometry
criterion are ordinary explicit hypotheses. No desired Fact/axiom/instance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj Opposite

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- Literal separately-owned C4 output. This statement does not construct or
assert a projective embedding; an actual C4 theorem can supply the argument. -/
def NativeProjectiveEmbeddingExists : Prop :=
  ∀ (k : Type) [Field k] (J : PkgI3.AbVar k),
    ∃ (coordinates : Type) (_ : Finite coordinates)
      (embedding : J.X.left ⟶ ℙ(coordinates; Spec (.of k))),
      IsClosedImmersion embedding ∧
      embedding ≫ ℙ(coordinates; Spec (.of k)) ↘ Spec (.of k) = J.X.hom

/-- ONE labelled compatibility input in L1's exact quotient-bundle descent form. -/
def NativeQuotientDescentCompatibility : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (B : PkgI3.AbVar k) (M : B.X.left.Pic)
    (H : L1.FiniteStabilizerScheme B M) (Q : L1.StabilizerQuotient B M H),
    (picardFunctor B.X.hom).obj.map (((fst H.K B.X ≫ H.j) * snd H.K B.X).op)
        ((toPicardFunctor B.X.hom).app (.op B.X)
          (L1.normalizedPolarizationFamily B.X M (𝟙 B.X))) =
      (picardFunctor B.X.hom).obj.map (snd H.K B.X).op
        ((toPicardFunctor B.X.hom).app (.op B.X)
          (L1.normalizedPolarizationFamily B.X M (𝟙 B.X)))

/-- B2's agreed point-surjectivity target can be supplied by its upstream
proof conditional on the SAME square and ONE Leray statement. This is not a
second B2 target: the output is literally L3.PicZeroPointSurjectivity. -/
def PicZeroPointSurjectivityFromLeray : Prop :=
  NativeTheoremOfTheSquare.{0} → L3.NativeLerayDegeneration.{0} → L3.PicZeroPointSurjectivity.{0}

/-- An actual proof of the agreed raw B2 statement supplies the above input.
This adapter installs no vanishing/Leray/square Fact and changes no B2 target. -/
theorem picZeroPointSurjectivityFromLeray_of_B2
    (hB2 : L3.PicZeroPointSurjectivity.{0}) : PicZeroPointSurjectivityFromLeray :=
  fun _ _ => hB2

/-- Simplified B2 input after the ONE native Leray theorem has been proved. -/
def PicZeroPointSurjectivityFromSquare : Prop :=
  NativeTheoremOfTheSquare.{0} → L3.PicZeroPointSurjectivity.{0}

/-- Genuine discharge of the Leray premise with the ACTUAL L3 proof. -/
theorem picZeroPointSurjectivityFromSquare_of_LerayRecipe
    (h : PicZeroPointSurjectivityFromLeray) : PicZeroPointSurjectivityFromSquare :=
  fun hs => h hs L3.NativeLerayDegeneration_proof

/-- Direct agreed B2 also supplies the simplified square-only input. -/
theorem picZeroPointSurjectivityFromSquare_of_B2
    (h : L3.PicZeroPointSurjectivity.{0}) : PicZeroPointSurjectivityFromSquare := fun _ => h

/-- **Single conditional assembly, fixed full target.** Every unproved input
is a named ordinary proposition. In particular the generic normal graph
criterion is retained explicitly until its native geometric proof is supplied.
No Φ-extension or desired PolarizationRetract hypothesis is used. -/
theorem polarizationRetract_of_B3_output
    (hA : ReducedGlobalNormalizedSeesaw)
    (hB2 : PicZeroPointSurjectivityFromSquare)
    (hB3 : L4.StabilizerAbVarQuotientExists)
    (hSquare : NativeTheoremOfTheSquare.{0})
    (hCompatibility : NativeQuotientDescentCompatibility)
    (hEmbedding : NativeProjectiveEmbeddingExists)
    (hGeometry : NativeNormalGraphProjectionCriterion) :
    ZInQ.Contrib.CloudR2Poincare.PolarizationRetract := by
  intro k _ _ J B i hi
  obtain ⟨L, hL, hLvery, hM, hMvery⟩ :=
    exists_veryAmple_closedRestriction_of_projectiveEmbedding J B i hi (hEmbedding k J)
  letI : L.IsInvertible := hL
  let M := (Scheme.Modules.pullback i.hom.left).obj L
  letI : M.IsInvertible := hM
  obtain ⟨H, Q, q, hflat, hfinite, hsurj, hfp, hkp, hdim⟩ := hB3 hA B M hMvery
  letI : Flat q.hom.left := hflat
  letI : IsFinite q.hom.left := hfinite
  letI : Surjective q.hom.left := hsurj
  letI : LocallyOfFinitePresentation q.hom.left := hfp
  let quotient : L1.StabilizerQuotient B (Scheme.Pic.mk M) H :=
    { Q := Q.X, q := q.hom, kernelPair := hkp }
  obtain ⟨P, hP, hnormalized, hpull⟩ := L1.exists_quotientPolarizationBundle B (Scheme.Pic.mk M)
    H quotient (hCompatibility k B (Scheme.Pic.mk M) H quotient)
  letI : P.IsInvertible := hP
  obtain ⟨φ, hφ⟩ := exists_polarization_extension_of_graph_inputs (hB2 hSquare)
    hSquare hGeometry J B Q i (Scheme.Pic.mk L) M hMvery
    (Scheme.Pic.map_mk i.hom.left L).symm H q hkp (Scheme.Pic.mk P) hnormalized hpull
  refine ⟨Q, φ, ?_, hdim.le⟩
  rw [hφ]
  exact ⟨hfinite, hsurj⟩

/-- **Final reduced input assembly:** B3 geometry and the ONE Leray theorem
are supplied by their ACTUAL L4/L3 proofs. Only generic quotient existence,
A seesaw, B2/square, bundle compatibility, C4's embedding output, and the
explicit normal-graph criterion remain named ordinary inputs. -/
theorem polarizationRetract_of_inputs
    (hA : ReducedGlobalNormalizedSeesaw)
    (hB2 : PicZeroPointSurjectivityFromSquare)
    (hQuotient : L4.FiniteStabilizerQuotientExists)
    (hSquare : NativeTheoremOfTheSquare.{0})
    (hCompatibility : NativeQuotientDescentCompatibility)
    (hEmbedding : NativeProjectiveEmbeddingExists)
    (hGeometry : NativeNormalGraphProjectionCriterion) :
    ZInQ.Contrib.CloudR2Poincare.PolarizationRetract :=
  polarizationRetract_of_B3_output hA hB2
    (L4.stabilizerAbVarQuotientExists_of_quotient hQuotient)
    hSquare hCompatibility hEmbedding hGeometry

end ZInQ.Contrib.CloudR2Poincare.L2
