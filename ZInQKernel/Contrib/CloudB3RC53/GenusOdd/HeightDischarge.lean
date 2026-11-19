import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Witness
import ZInQKernel.Contrib.OneProof.RC.Height.Isomorphism
import ZInQKernel.Contrib.OneProof.RC.Height.BaseChange

/-!
# GenusOdd: `NeronTateTwist` discharged from the RC height results

`NeronTateTwist` (stated in `Glue.lean`) is PROVED here from the height results of
`ZInQ.Manuscript.RC.Height`: a change of variables preserves `ĥ`
(`canonicalHeight_addEquivVariableChange`), transport along an equality of curves preserves `ĥ`
(`canonicalHeight_cast`), and base change from `ℚ` multiplies `ĥ` by the degree
(`canonicalHeight_baseChange`). Hence the GLUE of (3.4) reduces to `ArtinFactorization` (the
factorization `L(E/K, s) = L(E, s) L(E^{(k)}, s)` in its ring-class form), `GenusTheory` and
`SplittingCriterion`.

Naming: `ArtinFactorization` is the ring-class generalization (character `χ_{d₁} ∘ N` on `Pic(O_c)`)
of the GLUE `ZInQ.Manuscript.RC.Height.LFactorizationConductorOne` (character one, `c = 1`), which
is its case `d₁ = 1` up to the model `qtwist E 1` of `E`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Contrib.CloudB3RC53.CST

/-- **`NeronTateTwist`, PROVED** from the height functoriality of `RC/Height`. -/
theorem neronTateTwist_proof : NeronTateTwist := by
  intro E _ h₁ h₃ d H _ _ _ s hs hsd P
  have hd : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsd
    exact hs ((pow_eq_zero_iff two_ne_zero).mp hsd)
  have hEd : (qtwist E d).IsElliptic := qtwist_isElliptic E hd
  unfold twistEmb
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  rw [ZInQ.Manuscript.RC.Height.canonicalHeight_addEquivVariableChange, AddEquiv.cast_apply,
    ZInQ.Manuscript.RC.Height.canonicalHeight_cast]
  · have hbc := ZInQ.Manuscript.RC.Height.canonicalHeight_baseChange (K := H) (qtwist E d)
      (Point.equivBaseChangeSelf (qtwist E d).toAffine P)
    refine hbc.trans ?_
    congr 1
  · exact (twistVC_smul E h₁ h₃ hs hsd).symm

/-- The remaining GLUE of (3.4) after `neronTateTwist_proof`: `ArtinFactorization`, `GenusTheory`,
`SplittingCriterion` (each a `Prop` of `Glue.lean`; `SplittingCriterion` has since been PROVED,
`Splitting/Criterion.lean`, and the current route is `Artin34.lean` / `LocalFinal.lean`). -/
structure GlueAfterRC19 : Prop where
  artin : ArtinFactorization
  genus : GenusTheory
  split : SplittingCriterion

theorem glueReduced_of_RC19 (G : GlueAfterRC19) : GlueReduced :=
  ⟨G.artin, neronTateTwist_proof, G.genus, G.split⟩

/-- **(3.4)** from the printed leaves and the GLUE left after `neronTateTwist_proof`. -/
theorem genusLower34_of_RC19 (P : Prints) (G : GlueAfterRC19) : GenusLower34 :=
  genusLower34_of_reduced P (glueReduced_of_RC19 G)

/-- **The fixed witness** from the printed leaves and the GLUE left after `neronTateTwist_proof`. -/
theorem fixedWitness_of_RC19 (P : Prints) (G : GlueAfterRC19) : FixedWitness :=
  fixedWitness_proof P (glueReduced_of_RC19 G)

/-- **(3.4) at every `(h, k')`** (AppGEndpoints `FinalFamilyField` form) from the printed leaves
and the GLUE left after `neronTateTwist_proof`. -/
theorem gzEveryCompanion_of_RC19 (P : Prints) (G : GlueAfterRC19) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel E) f Lat κ) {hstar : ℤ} (hgp : GenusPartner E hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum E f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared E hstar h → AnalyticRank (qtwist E h) 1 → (selG h).isSome)
    (hselR : ∀ h k', Prepared E hstar h → AnalyticRank (qtwist E h) 1 →
      Companion E Lat hstar h k' → (selR h k').isSome) :
    GzEveryCompanion (Prepared E hstar) (fun h => AnalyticRank (qtwist E h) 1) (LstarQ E Lat)
      (jgenOf E f Lat κ hstar selG) (jrcOf E f Lat κ selR) hstar (Companion E Lat hstar) 0 :=
  gzEveryCompanion_genuine P (glue34_of_reduced (glueReduced_of_RC19 G)) h₁ h₃ hf hLat hNC hκ hgp
    hElkikMD selG selR hselG hselR

/-- **`RCSteps.gz_comparison`** from the printed leaves and the GLUE left after
`neronTateTwist_proof`. The conditions on `kfin` (odd, `≡ 1 mod 4`, unit square at `2N`, prime to
`h_*`) are NOT derivable from the other `RCData`/`RCSteps` fields (`RCSteps.companion` gives only
`kfin < 0`, squarefree, `≠ -1, -3`, primes in `S`, `L(E^{(k)},1) ≠ 0`); they are the manuscript's
conditions on the final companion (tex L2595–2603 with L2349–2352) and stay hypotheses. -/
theorem gzComparison_of_RC19 (P : Prints) (G : GlueAfterRC19) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) {hstar kfin : ℤ}
    (hgp : GenusPartner (Ecurve ℓ) hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar (Ecurve ℓ) Lat hstar)
    (hk0 : kfin < 0) (hk4 : kfin % 4 = 1) (hksq : Squarefree kfin)
    (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p kfin)
    (hkcop : IsCoprime kfin hstar) (S : Finset ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      (selG h).isSome)
    (hselR : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      Companion (Ecurve ℓ) Lat hstar h kfin → (selR h kfin).isSome) :
    GzComparisonText ℓ (Prepared (Ecurve ℓ) hstar) (LstarQ (Ecurve ℓ) Lat)
      (jgenOf (Ecurve ℓ) f Lat κ hstar selG) (jrcOf (Ecurve ℓ) f Lat κ selR) hstar kfin S :=
  gzComparison_genuine P (glue34_of_reduced (glueReduced_of_RC19 G)) hf hLat hNC hκ hgp hElkikMD
    hk0 hk4 hksq hk2N hkcop S selG selR hselG hselR

end ZInQ.Contrib.CloudB3RC53.GenusOdd
