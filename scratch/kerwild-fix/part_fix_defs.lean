
section KWFixSec

noncomputable section

namespace KWFix

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField
  UnramTate FrobTrace

/-! ### §1. The bridges in Glazer's normalization -/

/-- **Bridge 2 in Glazer's normalization (GLUE; proved below from I3.M0,
`tateBridgeE_of_tateModuleFree`).** g0-mod-field's `TateBridge`, with the scalars of the output
fixed: for some field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ`, `β' = Φ ∘ β` and `ε' = Φ ∘ ε`, where `β`, `ε`
are `G7Data`'s cochain and sign cocycle (N5 L651-660, L719-727: `ν = aμ`, `ν_σ ^σν_τ = ε ν_{στ}`,
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ`). The real factor `a_σ = (deg μ_σ)^{-1/4}` is carried by `a`
(`a_g a_h c(g,h) = ε'(g,h) a_{gh}` with `c = n/d`), not by `ε'`. -/
def TateBridgeE : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
      (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu

/-- **`TateBridgeE` contains `TateBridge` (proved).** -/
theorem tateBridge_of_E (h : TateBridgeE) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Φ, Tm, c, a, uu, h7⟩ := h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  exact ⟨Tm, c, _, a, _, uu, h7⟩

/-- **g14-trace's `TateBridge35` in Glazer's normalization (GLUE; proved below from I3.M0 and
frob-trace's `AlgFrobLink`, `tateBridge35E_of_algFrobLink`).** As `TateBridge35`, with the
embeddings `j_ℓ = Φ_ℓ ∘ ι_ℂ` for field isomorphisms `Φ_ℓ : ℂ ≃ ℚ̄_ℓ`, so that `β'_ℓ = Φ_ℓ ∘ β`
and `ε'_ℓ = Φ_ℓ ∘ ε` (`ℓ = 5, 3`); `a_ℓ = Φ_ℓ ∘ ι_ℂ ∘ aQ`. -/
def TateBridge35E : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
      (Φ5 : ℂ ≃+* PadicAlgCl 5) (Φ3 : ℂ ≃+* PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      (∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5
        (fun g h => Φ5 (ε g h : ℂ)) (fun g => Φ5 (ιC (aQ g))) (fun g => Φ5 (β g : ℂ)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3
        (fun g h => Φ3 (ε g h : ℂ)) (fun g => Φ3 (ιC (aQ g))) (fun g => Φ3 (β g : ℂ)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3

/-- **G7's output with the twist, keeping G4's degree bound `[L:ℚ] ≤ D`** (the hypothesis `hLD` of
the theorems below; g0-mod-field's `G7OutUnr` drops it, `G4Out` has it). Proved from `G4Out` and
the four B2 leaves (`g7OutUnrD_of_g4Out`, a copy of g0-mod-field's `g7OutUnr_of_g4Out`, which
keeps G4's `L`). -/
def G7OutUnrD (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    Module.finrank ℚ L ≤ ZInQ.heightD ∧ G7Data u P L A ε N χ β L' hLL'

/-- `G7OutUnrD` gives g0-mod-field's `G7OutUnr` (proved). -/
theorem g7OutUnr_of_D {u : ℚ} {P : QML3 Qbar} (h : G7OutUnrD u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hLL', -, hD⟩ := h
  exact ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hLL', hD⟩

/-- The embedding `Φ ∘ ι_ℂ : ℚ̄ → ℚ̄_ℓ`. -/
def jOf {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) :
    PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ :=
  ((Φ : ℂ →+* PadicAlgCl ℓ).comp (ιC : PkgI4.Qbar →+* ℂ)).toRatAlgHom

theorem jOf_apply {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (x : PkgI4.Qbar) : jOf Φ ιC x = Φ (ιC x) := rfl

/-- `G7Out`'s `ε` is determined by `β` (`∂β = ε`, `β ≠ 0`): any `ε₂` with `∂β = ε₂` may replace it
(proved). -/
theorem g7Out_eps_congr {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (c ε ε₂ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (h : GaloisCopy.G7Out A ℓ Tm c ε a β u)
    (h₂ : ∀ g g₂, β g * β g₂ = ε₂ g g₂ * β (g * g₂)) :
    GaloisCopy.G7Out A ℓ Tm c ε₂ a β u := by
  have he : ε₂ = ε := by
    funext g g₂
    have h1 := h.2.2.2.2.1 g g₂
    have h0 := h.2.2.2.2.2.1 (g * g₂)
    exact mul_right_cancel₀ h0 ((h₂ g g₂).symm.trans h1)
  subst he
  exact h

/-- `G7Out` respects pointwise equality of `β` (proved). -/
theorem g7Out_beta_congr {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β β₂ : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (h : GaloisCopy.G7Out A ℓ Tm c ε a β u) (hβ : ∀ g, β₂ g = β g) :
    GaloisCopy.G7Out A ℓ Tm c ε a β₂ u := by
  have he : β₂ = β := funext hβ
  subst he
  exact h

/-- `∂(Φ ∘ β) = Φ ∘ ε` from `∂β = ε` (proved). -/
theorem cocycle_map {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) (β : GQ → ℂˣ)
    (ε : GQ → GQ → ℂˣ) (hβe : ∀ x y, β x * β y = ε x y * β (x * y)) (g g₂ : PkgI4.GQ) :
    Φ (β g : ℂ) * Φ (β g₂ : ℂ) = Φ (ε g g₂ : ℂ) * Φ (β (g * g₂) : ℂ) := by
  have := congrArg (fun z : ℂˣ => Φ (z : ℂ)) (hβe g g₂)
  simp only [Units.val_mul, map_mul] at this
  exact this

