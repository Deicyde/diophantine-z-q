import ZInQKernel.Contrib.OneProof.CarayolPrintedIrr

/-! # r17-rebase: Carayol's printed leaf supersedes modular-split's `CarayolRealization` (Scenario F)

`CarayolRealization` is copied verbatim from `scratch/modular-split/R17.lean` (L127, namespace
`ModularSplit.R17`; scratch files cannot import each other). It is proved here from r17-print's leaf
`CarayolPrinted.CarayolThmA` (hence from `CarayolThmAIrr`) and the bundle field
`DSCoeffExt.EigenformCoeffFieldFinite`. -/

noncomputable section

namespace ModularSplit.R17

open LadicCond

/-- Verbatim copy (modular-split, `scratch/modular-split/R17.lean` L127). -/
def CarayolRealization : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2), 0 < N → PkgI4.IsNewform f χ →
    ∃ ρ : PkgI4.GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ → condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

end ModularSplit.R17

namespace CarayolPrinted

open PkgI4 LadicCond HeckeRing.GL2 NumberField IsDedekindDomain

theorem carayolRealization_of_printed (h : CarayolThmA) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    ModularSplit.R17.CarayolRealization := by
  intro ℓ _ ιC ιL N χ f hN hf
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, rfl, hχ⟩ := NewformDict.exists_newform_of_isNewform hf
  set K := DSCoeffExt.coeffField (g.toCuspForm : CF N 2) with hKdef
  have : FiniteDimensional ℚ K :=
    hK N 2 χ (g.toCuspForm : CF N 2) le_rfl (DSCoeffExt.isNormalizedEigenformDS_of hf.1)
  have : NumberField K := ⟨⟩
  set τ := DSCoeffExt.emb ιC K ιL with hτ
  obtain ⟨ρ', hρc, hirr, hatt, hcond⟩ :=
    h N g ℓ (DSCoeffExt.place τ) (DSCoeffExt.natCast_mem_placeIdeal _)
  set ρL := mapRep (DSCoeffExt.τhat τ) (DSCoeffExt.continuous_τhat τ) ρ' hρc with hρL
  have hsL : ρL.IsSemisimple := by
    apply isSemisimple_of_adjoin
    exact adjoin_map_eq_top (DSCoeffExt.τhat τ) _ hirr
  have haL : ρL.AttachedTo ιC ιL (g.toCuspForm : CF N 2) := by
    intro q hq hqN
    obtain ⟨hun, htr⟩ := hatt q hq hqN
    refine ⟨?_, DSCoeffExt.pre ιC K ⟨coeff (g.toCuspForm : CF N 2) q,
      DSCoeffExt.coeff_mem_coeffField _ q⟩, DSCoeffExt.ιC_pre _ _ _, ?_⟩
    · intro v hv σ hσ
      show mapGL _ (ρ' _) = 1
      rw [hun v hv σ hσ, map_one]
    · intro v σ hv hσ
      show ((ρ' σ : Matrix (Fin 2) (Fin 2) _).map (DSCoeffExt.τhat τ)).trace = _
      rw [← AddMonoidHom.map_trace, htr v σ hv hσ, DSCoeffExt.τhat_algebraMap]
      rfl
  refine ⟨ρL, hsL, haL, fun p _ hp => ?_⟩
  have h2 : ρL.restrictLocal p = (mapGL (DSCoeffExt.τhat τ)).comp (ρ'.comp (decomp p)) := rfl
  rw [h2, condExp_map]
  exact hcond p hp

theorem carayolRealization_of_printedIrr (h : CarayolThmAIrr)
    (hK : DSCoeffExt.EigenformCoeffFieldFinite) : ModularSplit.R17.CarayolRealization :=
  carayolRealization_of_printed (carayolThmA_of_irr h) hK

end CarayolPrinted

#print axioms CarayolPrinted.carayolRealization_of_printed
#print axioms CarayolPrinted.carayolRealization_of_printedIrr
