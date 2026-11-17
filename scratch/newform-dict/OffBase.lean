import ZInQKernel.Contrib.OneProof.NewformDict

/-! newform-dict: the dictionary applied to the new leaves proposed on other branches (not on this base).
Definitions copied verbatim (namespaces renamed to `OffBase.*`), sources:
* `NewformRepConductor`: origin/wip/r17-bypass 3e6e5017, ZInQKernel/Contrib/OneProof/CarayolLevel.lean:230
  (namespace `CarayolLevel`, `open PkgI4 LadicCond C9Rhof`).
* `KatoHTExists`: origin/wip/ht-exists 7088f9ed, ZInQKernel/Contrib/OneProof/EigenformHTExists.lean:492
  (namespace `EigenformHTExists`, `open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module`).
* `AfTateCharPoly` (origin/wip/r16-used dcf24ac6, R16Used.lean:368) and `R16Trace` (:388) need R16Used's
  module structure `tensorModule`; they have the shape `∀ N χ f J, 0 < N → IsNewform f χ → IsJ1 N J → Q`, covered by
  `shapeJ_iff` below with `Q` arbitrary. -/

noncomputable section
open HeckeRing.GL2

namespace OffBase.CarayolLevel
open PkgI4 LadicCond

def NewformRepConductor : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- Over the printed newform. -/
def NewformRepConductorNewform : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N 2), f.χ = MulChar.toUnitHom χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL (f.toCuspForm : CF N 2) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

theorem iff_newform : NewformRepConductor ↔ NewformRepConductorNewform := by
  constructor
  · intro h ℓ _ ιC ιL
    exact (NewformDict.forall_isNewform_iff _).mp (h ℓ ιC ιL)
  · intro h ℓ _ ιC ιL
    exact (NewformDict.forall_isNewform_iff _).mpr (h ℓ ιC ιL)

end OffBase.CarayolLevel

namespace OffBase.EigenformHTExists
open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

def KatoHTExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

/-- Over the printed newform. -/
def KatoHTExistsNewform : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : HeckeRing.GL2.Newform N k),
    2 ≤ k → f.χ = MulChar.toUnitHom χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar,
        ιC α = coeff (f.toCuspForm : CF N k) p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

theorem iff_newform : KatoHTExists ↔ KatoHTExistsNewform := by
  constructor
  · intro h ℓ _ ιC ιL N _ k χ f hk hfχ
    exact h ℓ ιC ιL N k χ f.toCuspForm (Nat.pos_of_neZero N) hk
      ((NewformDict.g9_isNewform_iff (Nat.pos_of_neZero N)).mpr ⟨inferInstance, f, rfl, hfχ⟩)
  · intro h ℓ _ ιC ιL N k χ f hN hk hf
    obtain ⟨_, g, rfl, hgχ⟩ := (NewformDict.g9_isNewform_iff hN).mp hf
    exact h ℓ ιC ιL N k χ g hk hgχ

end OffBase.EigenformHTExists

namespace OffBase.R16Used
open PkgI4 (CF IsNewform)

/-- The shape of `R16Used.AfTateCharPoly` and `R16Used.R16Trace` (and of `R16Split.R16CoreY`), with the
conclusion `Q` arbitrary. -/
theorem shapeJ_iff (Q : (N : ℕ) → DirichletCharacter ℂ N → CF N 2 → PkgI3.AbVar ℚ → Prop) :
    (∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : PkgI3.AbVar ℚ),
        0 < N → IsNewform f χ → LeafModCurves.IsJ1 N J → Q N χ f J) ↔
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N 2) (J : PkgI3.AbVar ℚ),
        f.χ = MulChar.toUnitHom χ → LeafModCurves.IsJ1 N J → Q N χ f.toCuspForm J := by
  constructor
  · intro h N _ χ f J hfχ hJ
    exact h N χ f.toCuspForm J (Nat.pos_of_neZero N)
      ((NewformDict.isNewform_iff (Nat.pos_of_neZero N)).mpr ⟨inferInstance, f, rfl, hfχ⟩) hJ
  · intro h N χ f J hN hf hJ
    obtain ⟨_, g, rfl, hgχ⟩ := (NewformDict.isNewform_iff hN).mp hf
    exact h N χ g J hgχ hJ

end OffBase.R16Used

#print axioms OffBase.CarayolLevel.iff_newform
#print axioms OffBase.EigenformHTExists.iff_newform
#print axioms OffBase.R16Used.shapeJ_iff
