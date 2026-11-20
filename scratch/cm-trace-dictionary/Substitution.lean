import ZInQKernel.Contrib.OneProof.CMTraceDictionary.TraceDescent
import ZInQKernel.Contrib.OneProof.HKGZ.HKGZAssembly

/-! Dry run starting at the actual algebraic image, with the remaining pole
premise visible in the assembly. -/

namespace ZInQ.Manuscript.CMTraceDictionary

open WeierstrassCurve NumberField TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.CloudB3RC53.ModularWeil (LiCarayolNewformOfModular)
open scoped BigOperators

open Classical in
/-- The same sum, indexed by the ideal class group through the actual Artin map.
This only reindexes the sum; the analytic description of each conjugate is a
separate reciprocity statement. -/
theorem hilbert_sum_eq_class_sum (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K]
    (y : (E.baseChange (hilbertClassField K)).toAffine.Point) :
    (∑ σ : hilbertClassField K ≃ₐ[K] hilbertClassField K,
      Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y) =
    ∑ a : ClassGroup (𝓞 K),
      Affine.Point.map (W' := E.toAffine) (((hilbertClassArtinEquiv K) a).toAlgHom.restrictScalars ℚ) y := by
  symm
  exact Equiv.sum_comp (hilbertClassArtinEquiv K).toEquiv
    (fun σ => Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y)

set_option maxHeartbeats 1200000 in
open Classical in
/-- This is the algebraic trace operation also needed off the pole family. -/
theorem existsUnique_hilbert_trace (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K]
    (y : (E.baseChange (hilbertClassField K)).toAffine.Point) :
    ∃! P : (E.baseChange K).toAffine.Point,
      Affine.Point.map (W' := E.toAffine) (IsScalarTower.toAlgHom ℚ K (hilbertClassField K)) P =
        ∑ σ : hilbertClassField K ≃ₐ[K] hilbertClassField K,
          Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y :=
  existsUnique_point_of_sum_conjugates (K := K) (L := hilbertClassField K) E y

open Classical in
/-- The exact pole predicate after the point and the comparison have been supplied.
No new Heegner-point predicate is used. -/
theorem existing_trace_of_hilbert_image
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (c : ℚ)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (hc : IsParamScale (newformLevel E) f Lat (c : ℂ))
    (A B C : ℤ) (hForm : IsHeegnerForm (newformLevel E) (discr K) A B C)
    (ι : hilbertClassField K →ₐ[ℚ] ℂ) (y : (E.baseChange (hilbertClassField K)).toAffine.Point)
    (hy : Affine.Point.map (W' := E.toAffine) ι y = phiAn E f Lat c (cmPoint A B (discr K))) :
    ∃ P : (E.baseChange K).toAffine.Point, HKRefereed.IsHeegnerTrace E K P := by
  obtain ⟨P, hP, _⟩ := existsUnique_hilbert_trace E K y
  exact ⟨P, f, Lat, c, hf, hLat, hNC, hc, A, B, C, ι, y, hForm, hy, hP⟩

/-- The assembly still takes the exact frozen pole dictionary and the separate sign input. -/
theorem hkConsumed_dry_run
    (hB : PoleS12.BCDTThmA) (hNew : LiCarayolNewformOfModular)
    (hCM : HKGZ.PoleCMTraceDictionary) (hBFH : HKGZ.BFHTwistNonvanishingDraft)
    (hGZ : HKGZ.GrossZagierTraceDraft) (hSign : HKGZ.HeegnerTraceConjugationDraft) :
    HKRefereed.HKConsumed :=
  HKGZ.hkConsumed_of_grossZagier hB hNew hCM hBFH hGZ hSign

end ZInQ.Manuscript.CMTraceDictionary

#print axioms ZInQ.Manuscript.CMTraceDictionary.existsUnique_point_of_sum_conjugates
#print axioms ZInQ.Manuscript.CMTraceDictionary.hilbert_sum_eq_class_sum
#print axioms ZInQ.Manuscript.CMTraceDictionary.existsUnique_hilbert_trace
#print axioms ZInQ.Manuscript.CMTraceDictionary.existing_trace_of_hilbert_image
#print axioms ZInQ.Manuscript.CMTraceDictionary.hkConsumed_dry_run
