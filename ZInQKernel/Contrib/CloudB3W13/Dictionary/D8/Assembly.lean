/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.OneProof.H.TailW
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D0
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D8.ModelFields

/-!
# D8: ORIGINAL TailW model wrapper and conditional final-H119 assembly

Original W01/Metamate source, 2026-11-15. OWN D8 source only; original
TailW/TailL/Root/dictionaries/pins/providers remain unchanged.

IMPORTANT: this file is drafted while the original TailW facets and two
canonical FLT companion conclusions are not yet available in this private
node view. No cold TailW/SourceAll build is permitted. Until a source-paired
existing view is provided and this file is actually compiled/kernel checked,
it is UNVERIFIED source, not a target certificate.

The conditional theorem exposes every pending native dictionary and the two
EXACT project-specialized companion statements as ordinary explicit arguments.
No desired H119/IsShimuraModel Fact or fabricated model is assumed. The final
unconditional supplier will apply actual canonical proofs only once available,
then require full kernel/AX3/data/circularity and non-author review.
-/

noncomputable section
namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
open CategoryTheory AlgebraicGeometry Limits
open ZInQ.Contrib.CloudW03NeronSurj
open LeafQM.AV
open HDec.VertWitness

/-- The unchanged ORIGINAL IsShimuraModelNoGuard predicate is exactly the
literal seven fields already assembled, on the actual fine-moduli source. -/
theorem original_model_of_data (hD2 : D2_Obligation) (hD34 : D34_Obligation)
    (hD5 : D5_Obligation) (hD6 : D6_Obligation) (hD7 : D7_Obligation)
    (hD9 : D9_Obligation) (hD10 : D10_Obligation) (hUnique : FibreUnique_Obligation)
    (p : ℕ) [Fact p.Prime] (h2 : IsUnit ((2 : ℕ) : Zloc p)) (h3 : IsUnit ((3 : ℕ) : Zloc p))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of (Zloc p))) (ptF : PtF (Zloc p) πM)
    (hM : FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) (hlft : LocallyOfFiniteType πM)
    (hAF : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hproper : IsProper πM) (hsmooth : SmoothOfRelativeDimension 1 πM) :
    ∃ 𝒜 : QMFamily M, HDec.CurveSplitGR.IsShimuraModelNoGuard p (Over.mk πM) 𝒜 := by
  let s0 : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (Zloc p)) :=
    Spec.map (CommRingCat.ofHom ((algebraMap ℚ Qbar).comp (HDec.ModelGlue.zlocToRat p)))
  obtain ⟨𝒜, hfields⟩ := model_exists_of_dict hD2 hD34 hD5 hD6 hD7 hD9 hD10 hUnique
    (Zloc p) h2 h3 M πM ptF hM hsep hqc hlft hAF hproper hsmooth
    (fun _ _ => HDec.ModelGlue.spec_to_zloc_eq _ _) s0
  exact ⟨𝒜, hfields⟩

/-- CONDITIONAL H119, never counted as an unconditional proof. The two
companion arguments are exactly the canonical exists-fine-moduli/properness
statements specialized to q=2,q'=3,a=2,b=-3,Λ=oLattice,N=1,m=3. -/
theorem shimuraGoodReductionNoGuard_of_dict
    (hD2 : D2_Obligation) (hD34 : D34_Obligation) (hD5 : D5_Obligation)
    (hD6 : D6_Obligation) (hD7 : D7_Obligation) (hD9 : D9_Obligation)
    (hD10 : D10_Obligation) (hUnique : FibreUnique_Obligation)
    (hExistsFine : ∀ (𝒪 : Type) [CommRing 𝒪]
      (hN : IsUnit ((1 : ℕ) : 𝒪)) (hm : IsUnit ((3 : ℕ) : 𝒪))
      (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪)),
      ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM),
        FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF ∧
        IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFiniteType πM ∧
        (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
        (IsUnit ((2 * 3 : ℕ) : 𝒪) → SmoothOfRelativeDimension 1 πM))
    (hProperFine : ∀ (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
      (hN : IsUnit ((1 : ℕ) : 𝒪)) (hm : IsUnit ((3 : ℕ) : 𝒪))
      (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
      (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM),
      FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF → IsProper πM) :
    HDec.CurveSplitGR.ShimuraGoodReductionNoGuard := by
  intro p _ hp
  obtain ⟨h2, h3, h6⟩ := d0_units p (by omega : 3 < p)
  have hN : IsUnit ((1 : ℕ) : Zloc p) := by simpa using (isUnit_one : IsUnit (1 : Zloc p))
  obtain ⟨M, πM, ptF, hM, hsep, hqc, hlft, hAF, hsm⟩ := hExistsFine (Zloc p) hN h3 h2 h3
  haveI : CharZero (Zloc p) := (HDec.ModelGlue.zlocToRat p).charZero
  have hproper := hProperFine (Zloc p) hN h3 h2 h3 M πM ptF hM
  have h6' : IsUnit ((2 * 3 : ℕ) : Zloc p) := by simpa using h6
  obtain ⟨𝒜, hmodel⟩ := original_model_of_data hD2 hD34 hD5 hD6 hD7 hD9 hD10 hUnique
    p h2 h3 M πM ptF hM hsep hqc hlft hAF hproper (hsm h6')
  exact ⟨Over.mk πM, 𝒜, hmodel⟩

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D8
