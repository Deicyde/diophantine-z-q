import ZInQKernel.Contrib.OneProof.CMBranch.Localize

/-! # cm-branch: A8 for every fibre, and `CMFibreSplit` from the matrix-unit glue alone

The manuscript's CM paragraph works over A8's field `L` (L520-562: `[L:ℚ] ≤ D`, every geometric
endomorphism defined over `L`), whose construction precedes the case split. The chain's A8 is G2
(`FibreCoverExists`) followed by the kernel field of `Res_{K/ℚ} A` (`kernelField_of_model_hf`) and the
degree bound (`GlueRepo.Numerics.a8_field`); none of these uses NoCM (only the descent datum of B1 does).
`homFieldModel_of` assembles them for every fibre context. `CMFibreSplit` is then proved from the smaller
glue `CMHomFieldSplit` (manuscript L582-586: matrix units on the Hom-field model).
-/

namespace HDec
set_option maxHeartbeats 1000000
noncomputable section

section A8
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField

/-- **A8's output for one fibre** (N5 L520-562): a finite Galois `L ⊆ ℚ̄` with `[L:ℚ] ≤ D`, a rational
fibre `PK/K` with `K ≤ L` (a model of `P`'s surface), and `G_L` fixing every homomorphism between the
conjugates of `PK.A` (`G4WeilRes.conjAction`: `L` is a Hom field). -/
def HomFieldModel (_u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L), Module.finrank ℚ L ≤ heightD ∧
    ∃ (K : IF) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K) (hKL : K ≤ L) (PK : QML3 K),
      IsModelOver K PK.A P ∧ ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1

/-- **A8 for every fibre context, without NoCM** (`kernelFieldExists_of_pieces_hf`'s first half and
`g4Out_of_kernelField`'s degree bound). -/
theorem homFieldModel_of (hCover : FibreCoverExists)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left) (u : ℚ) (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : HomFieldModel u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  have hK' : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf hHFF hNOS K hK PK.A (conj_dim K PK.A PK.surface) (T u) hK'
      (good_of_QML3 hNOS hRay hTors K PK (T u) (three_mem_T u))
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hK hE hr
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  exact ⟨E ⊔ K, inferInstance, inferInstance, hdeg, K, hfK, hgK, le_sup_right, PK, hPK.2, hfix⟩

end G0ModField.KernelField
end A8

namespace CMBranch
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Glue (manuscript L582-586): matrix units on the Hom-field model.** For a fibre context whose
object `P` has CM (`End_𝒪(P.A) ≠ ℤ`, i.e. `End⁰(A_ℚ̄) = M₂(k)` by the QM dichotomy) and A8's Hom-field
model `(PK.A)_L` (`HomFieldModel`): an elliptic curve `E/L` with `End(E_{L̄})` an order `R` of an
imaginary quadratic `k`, the product `E² = E × E`, and an `L`-isogeny `E² → (PK.A)_L`. ("All its
elements are defined over `L`. Multiples of matrix units therefore give an elliptic curve `E/L` with
complex multiplication and an `L`-isogeny `E² → A`.") -/
def CMHomFieldSplit : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 LeafQM.AV.Qbar), FibreCtx Y Φ π u P →
    ¬ (∀ φ ∈ LeafQM.AV.com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (K : IF) [FiniteDimensional ℚ K]
      [IsGalois ℚ K] (hKL : K ≤ L) (PK : LeafQM.AV.QML3 K), IsModelOver K PK.A P →
      (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
      letI : NumberField L := numberField_of_fd L
      ∃ (E Pr : ZInQ.DefFaltings.AbVar L) (k : Type) (_ : Field k) (_ : NumberField k)
        (R : Subring k),
        E.dim = 1 ∧ Pr.dim = (2 : ℕ) ∧ HSyn.G0Split.IsProductOf Pr.X E.X E.X ∧
        (∃ φ : Pr.X ⟶ ((LeafAdopt.abVarEquiv L).symm
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))).X, ZInQ.DefFaltings.IsIsogeny φ) ∧
        IsImagQuadOrder k R ∧ IsCMBy E k R

/-- **`CMFibreSplit` from A8 (proved, no NoCM) and the matrix-unit glue.** -/
theorem cmFibreSplit_of (hCover : FibreCoverExists)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hS : CMHomFieldSplit) : CMFibreSplit := by
  intro Y Φ π h1 h2 u hu hno
  unfold NoCMAt at hno
  push_neg at hno
  obtain ⟨y, P, hP, hy, φ, hφ, hne⟩ := hno
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hP, hy⟩
  obtain ⟨L, hfL, hgL, hdeg, K, hfK, hgK, hKL, PK, hPK, hfix⟩ :=
    G0ModField.KernelField.homFieldModel_of hCover hHFF hNOS hRay hTors Y Φ π u P hctx
  letI : NumberField L := numberField_of_fd L
  obtain ⟨E, Pr, k, _, _, R, hE1, hPr2, hprod, hiso, hR, hCM⟩ :=
    hS Y Φ π u P hctx (fun h => by
      obtain ⟨n, hn⟩ := h φ hφ
      exact hne n hn) L K hKL PK hPK hfix
  refine ⟨⟨L⟩, (LeafAdopt.abVarEquiv L).symm (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
    E, Pr, k, inferInstance, inferInstance, R, ?_, hdeg, hE1, hPr2, hprod, hiso, hR, hCM⟩
  exact ⟨algebraMap L LeafQM.AV.Qbar, y, P, hP, hy, isModelOver_baseChange hKL PK.A P hPK⟩

end CMBranch

end
end HDec
