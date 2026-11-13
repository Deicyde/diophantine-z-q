
/-! ## kerwild-fix: `LocalGlue` at every `ℓ` with all of `G7Clauses` discharged

Task kerwild-fix (2026-11-13). rv-fast (docs/research/rv-fast.md §1) found that lg-kerwild's
`exists_localGlue_of_tateModuleFree` concludes `G7Clauses β' ε' L → LocalGlue …` for data hidden
behind `∃` in `TateBridgeK`, and that for unram-tate's witness (`a' = 1`, `ε' = c = n/d`) the
hypothesis `G7Clauses` forces `c² = 1`, false as soon as a descent factor `a_σ ≠ 1`.

The fix: Glazer's normalization. The scalars of `G7Out` are taken as
`β' = Φ ∘ β`, `ε' = Φ ∘ ε` for a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ` (Steinitz; g8-tate's
`exists_complex_equiv`), where `β`, `ε` are `G7Data`'s cochain and sign cocycle; the real factor
`a_σ` stays in `a` (`a·a·c = ε'·a` with `ε'` a sign). The construction is frob-trace's (`key` in
`tateBridge35_of_algFrobLink`: unram-tate's operators, `scalarsQbar`, `g7Out_rescale`) with the
embedding `j := Φ ∘ ι_ℂ`, so that `j ∘ βQ = Φ ∘ β`. Then `G7Clauses (Φ ∘ β) (Φ ∘ ε) L` is
g8-tate's `g7Clauses_of_g7Data` (given `[L:ℚ] ≤ D`, a property of the input `L`, not of hidden data),
and `KerWild` is local-glue's `kerWild_of_g7Data` with `ι = Units.map Φ`.

* §0 copied tools (verbatim from scratch/g8-tate/part_tools.lean, part_local.lean).
* §1 `TateBridgeE` (every `ℓ`) and `TateBridge35E` (`ℓ = 5, 3`, with `FrobTraceLink`): bridges whose
  output is in Glazer's normalization; `TateBridgeE → TateBridge`, `TateBridge35E → TateBridge35`.
* §2 `tateBridgeE_of_tateModuleFree : PkgI3.TateModuleFree → TateBridgeE` and
  `tateBridge35E_of_algFrobLink : TateModuleFree → AlgFrobLink → TateBridge35E` (proofs: copies of
  frob-trace's `tateBridge35_of_algFrobLink` with `j_ℓ := Φ_ℓ ∘ ι_ℂ`).
* §3 `LocalGlue` at every `p ≠ ℓ`, with `G7Clauses` and `KerWild` proved for the witness.
-/

section G8TateToolsSec

/-! ### §0. Verbatim copies from scratch/g8-tate/part_tools.lean (l.20-61) and part_local.lean
(l.28-63) -/

noncomputable section

namespace G8Tate

open Cardinal LadicCond

/-- `#ℚ_p ≤ 𝔠`: `x ↦ (rational approximations of x within 1/(n+1))` is injective into `ℕ → ℚ`. -/
theorem padic_card_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- `#ℚ̄_ℓ = 𝔠`. -/
theorem padicAlgCl_card (ℓ : ℕ) [Fact ℓ.Prime] : #(PadicAlgCl ℓ) = 𝔠 := by
  apply le_antisymm
  · calc #(PadicAlgCl ℓ) ≤ max #ℚ_[ℓ] ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[ℓ] (PadicAlgCl ℓ)
      _ ≤ 𝔠 := max_le (padic_card_le ℓ) aleph0_le_continuum
  · calc 𝔠 ≤ #ℚ_[ℓ] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ #(PadicAlgCl ℓ) := mk_le_of_injective (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- **`ℂ ≃+* ℚ̄_ℓ` (proved; Steinitz, Mathlib's `IsAlgClosed.ringEquiv_of_equiv_of_charZero`).** -/
theorem exists_complex_equiv (ℓ : ℕ) [Fact ℓ.Prime] : Nonempty (ℂ ≃+* PadicAlgCl ℓ) := by
  have : CharZero (PadicAlgCl ℓ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective
  exact IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [mk_complex]; exact aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [mk_complex, padicAlgCl_card]))

end G8Tate

namespace G8Tate

open PkgI4 (GQ GQp decomp)
open LadicCond G0ModField
open ZInQ LeafQM.AV GlueDescent.B2
open CategoryTheory MonObj

/-- `T u` consists of primes (the argument inside g0-mod-field's `g7OutUnr_of_g4Out`). -/
theorem T_prime (u : ℚ) : ∀ q ∈ T u, q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- **`G7Data`'s cochain clauses, transported to `ℚ̄_ℓ` along a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ`,
are local-data's `G7Clauses` (proved).** -/
theorem g7Clauses_of_g7Data {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) :
    G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L := by
  obtain ⟨-, hDD, -, -, ⟨Tm, hTmT, hN⟩, hβlc, hβsq, hβε, -⟩ := h
  refine ⟨inferInstance, hLD, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    have := congrArg (fun z : ℂˣ => Φ (z : ℂ)) (hβε g h)
    simp only [Units.val_mul, map_mul] at this
    exact this
  · intro g
    exact (map_ne_zero Φ).mpr (Units.ne_zero _)
  · exact hβlc.comp (fun z : ℂˣ => Φ (z : ℂ))
  · have hT : ∀ q ∈ Tm, q.Prime := fun q hq => T_prime u q (hTmT hq)
    subst hN
    refine ⟨Tm, hT, inferInstance, χ, Units.map Φ.toRingHom.toMonoidHom, fun g => ?_⟩
    show Φ (β g : ℂ) ^ 2 = Φ ((GlueDescent.B2Q.galChar χ g : ℂˣ) : ℂ)
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hβsq g]
  · intro g h hg _
    obtain ⟨hε, hinf, h11, -⟩ := hDD
    have h1 := GlueDescent.B3Q.inflatedNormalized_of L ε hε hinf h11 g h
      (Or.inl (GlueDescent.B3Q.mem_GQL.mpr hg))
    show Φ (ε g h : ℂ) = 1
    rw [h1, Units.val_one, map_one]

end G8Tate

end

end G8TateToolsSec

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


end KWFix

end

end KWFixSec

section KWFixCopySec

/-! ### §2. The bridges proved: two copies of frob-trace's `tateBridge35_of_algFrobLink`
(scratch/frob-trace/FrobTrace.lean l.2562-2755, verbatim except the header and the choice of the
embeddings `j_ℓ := Φ_ℓ ∘ ι_ℂ` at the end; made by mk_fix.py) -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

set_option maxHeartbeats 4000000 in
/-- (kerwild-fix copy A) **`TateBridge35` from the leaf I3.M0 (`TateModuleFree`) and the glue `AlgFrobLink`.**
`Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (unram-tate's operators, built from the one
points-level descent datum `m` of `G7Data`), `aQ g = βQ g / γQ(hgh⁻¹)`, `βQ` with `ιC ∘ βQ = β`
(`scalarsQbar`), `j_ℓ = IsAlgClosed.lift`. `G7Out` at `ℓ` is unram-tate's construction with
`γ = j_ℓ ∘ γQ`, rescaled by `φ = j_ℓ(βQ)/j_ℓ(γQ(h·h⁻¹))` (`g7Out_rescale`). `FrobTraceLink`
comes from `AlgFrobLink` (applied to `m` with `g = h`) via `frobCompare_opV_conjE`, with
`S ∪ {3, 5}`. -/
theorem _root_.KWFix.tateBridgeE_of_tateModuleFree (hT : PkgI3.TateModuleFree) :
    KWFix.TateBridgeE := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, hFalg⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gamQ, βQ, ιC, hg0, hgc, hg1, hιβ⟩ := scalarsQbar L' a β ε n d hd hna hβe hεc.2.1 ha0
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hβQ0 : ∀ g, βQ g ≠ 0 := by
    intro g h0
    have := hιβ g
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k, k ∈ GQL L' → βQ k = 1 := by
    intro k hk
    apply ιC.toRingHom.injective
    show ιC (βQ k) = ιC 1
    rw [hιβ, hβL' k hk, map_one, Units.val_one]
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  -- the operators and `G7Out` at one `ℓ`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        @GaloisCopy.G7Out L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _
          (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
            (conjE Θ (m (h * g * h⁻¹)))) c ε'
          (fun g => j (βQ g / gamQ (h * g * h⁻¹))) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let gam : GQ → PadicAlgCl ℓ := fun σ => j (gamQ σ)
    have hgam0 : ∀ σ, gam σ ≠ 0 := fun σ => (map_ne_zero j).mpr (hg0 σ)
    have hgamc : ∀ σ τ, gam σ * gam τ =
        ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ) := by
      intro σ τ
      show j _ * j _ = _ * j _
      rw [← map_mul, hgc, map_mul, map_div₀, map_intCast, map_intCast]
    have hgam1 : ∀ k ∈ GQL L', gam k = 1 := by
      intro k hk; show j _ = 1; rw [hg1 k hk, map_one]
    -- (from here: unram-tate's `tateBridge_of_pieces`, with this `gam`)
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
    have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
      show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
      group
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    have hTm : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
    have hnorm : (L'.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
    have hres : ∀ σ : Field.absoluteGaloisGroup L',
        cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact hnorm.conj_mem _ this h
    have hres0 : ∀ σ : Field.absoluteGaloisGroup L',
        (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact this
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
    have hG7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c' c' a' β' uu := by
      refine ⟨_hdim, _hrank, hTm, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
        fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
      intro f v
      rw [continuous_iff_continuousAt]
      intro g₀
      let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
      have he₀ : Topology.IsOpenEmbedding e₀ :=
        (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
      have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
      have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
          fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
        funext σ
        simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
        rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hTm ha hβ hβ0, hrho1, Module.End.mul_apply]
      have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
        rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
      rw [he₀.continuousAt_iff, he₀1] at hc
      exact hc
    -- rescale by `φ = j(βQ)/γ(h·h⁻¹)`
    let φ : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g) / gam (cj g)
    have hφ0 : ∀ g, φ g ≠ 0 := fun g =>
      div_ne_zero ((map_ne_zero j).mpr (hβQ0 g)) (hgam0 _)
    have hφ1 : ∀ σ, φ (@GaloisCopy.resQ L' _ hNF σ) = 1 := by
      intro σ
      show j (βQ _) / gam (cj _) = 1
      rw [hβQ1 _ (hres0 σ), hgam1 _ (hres σ), map_one, div_one]
    refine ⟨c', _, uu, g7Out_rescale _ ℓ Tm c' c' a' β' _ _ φ uu hφ0 hφ1 (fun g => ?_)
      (fun g => ?_) hG7⟩
    · show j (βQ g / gamQ (cj g)) = j (βQ g) / j (gamQ (cj g)) * 1
      rw [map_div₀, _root_.mul_one]
    · show j (βQ g) = j (βQ g) / gam (cj g) * gam (cj g)
      rw [div_mul_cancel₀ _ (hgam0 _)]
  -- kerwild-fix: `j := Φ ∘ ι_ℂ`, so `j ∘ βQ = Φ ∘ β` and `∂(Φ ∘ β) = Φ ∘ ε`
  intro ℓ _
  obtain ⟨Φ⟩ := G8Tate.exists_complex_equiv ℓ
  obtain ⟨c, ε', uu, hG7⟩ := key ℓ (KWFix.jOf Φ ιC)
  exact ⟨Φ, _, c, _, uu, KWFix.g7Out_eps_congr _ ℓ _ _ _ _ _ _ _
    (KWFix.g7Out_beta_congr _ ℓ _ _ _ _ _ _ _ hG7 fun g => congrArg Φ (hιβ g).symm)
    (KWFix.cocycle_map Φ β ε hβe)⟩

set_option maxHeartbeats 4000000 in
/-- (kerwild-fix copy B) **`TateBridge35` from the leaf I3.M0 (`TateModuleFree`) and the glue `AlgFrobLink`.**
`Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (unram-tate's operators, built from the one
points-level descent datum `m` of `G7Data`), `aQ g = βQ g / γQ(hgh⁻¹)`, `βQ` with `ιC ∘ βQ = β`
(`scalarsQbar`), `j_ℓ = IsAlgClosed.lift`. `G7Out` at `ℓ` is unram-tate's construction with
`γ = j_ℓ ∘ γQ`, rescaled by `φ = j_ℓ(βQ)/j_ℓ(γQ(h·h⁻¹))` (`g7Out_rescale`). `FrobTraceLink`
comes from `AlgFrobLink` (applied to `m` with `g = h`) via `frobCompare_opV_conjE`, with
`S ∪ {3, 5}`. -/
theorem _root_.KWFix.tateBridge35E_of_algFrobLink (hT : PkgI3.TateModuleFree)
    (hF : AlgFrobLink) : KWFix.TateBridge35E := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, hFalg⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gamQ, βQ, ιC, hg0, hgc, hg1, hιβ⟩ := scalarsQbar L' a β ε n d hd hna hβe hεc.2.1 ha0
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hβQ0 : ∀ g, βQ g ≠ 0 := by
    intro g h0
    have := hιβ g
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k, k ∈ GQL L' → βQ k = 1 := by
    intro k hk
    apply ιC.toRingHom.injective
    show ιC (βQ k) = ιC 1
    rw [hιβ, hβL' k hk, map_one, Units.val_one]
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  -- the operators and `G7Out` at one `ℓ`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        @GaloisCopy.G7Out L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _
          (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
            (conjE Θ (m (h * g * h⁻¹)))) c ε'
          (fun g => j (βQ g / gamQ (h * g * h⁻¹))) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let gam : GQ → PadicAlgCl ℓ := fun σ => j (gamQ σ)
    have hgam0 : ∀ σ, gam σ ≠ 0 := fun σ => (map_ne_zero j).mpr (hg0 σ)
    have hgamc : ∀ σ τ, gam σ * gam τ =
        ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ) := by
      intro σ τ
      show j _ * j _ = _ * j _
      rw [← map_mul, hgc, map_mul, map_div₀, map_intCast, map_intCast]
    have hgam1 : ∀ k ∈ GQL L', gam k = 1 := by
      intro k hk; show j _ = 1; rw [hg1 k hk, map_one]
    -- (from here: unram-tate's `tateBridge_of_pieces`, with this `gam`)
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
    have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
      show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
      group
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    have hTm : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
    have hnorm : (L'.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
    have hres : ∀ σ : Field.absoluteGaloisGroup L',
        cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact hnorm.conj_mem _ this h
    have hres0 : ∀ σ : Field.absoluteGaloisGroup L',
        (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact this
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
    have hG7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c' c' a' β' uu := by
      refine ⟨_hdim, _hrank, hTm, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
        fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
      intro f v
      rw [continuous_iff_continuousAt]
      intro g₀
      let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
      have he₀ : Topology.IsOpenEmbedding e₀ :=
        (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
      have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
      have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
          fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
        funext σ
        simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
        rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hTm ha hβ hβ0, hrho1, Module.End.mul_apply]
      have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
        rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
      rw [he₀.continuousAt_iff, he₀1] at hc
      exact hc
    -- rescale by `φ = j(βQ)/γ(h·h⁻¹)`
    let φ : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g) / gam (cj g)
    have hφ0 : ∀ g, φ g ≠ 0 := fun g =>
      div_ne_zero ((map_ne_zero j).mpr (hβQ0 g)) (hgam0 _)
    have hφ1 : ∀ σ, φ (@GaloisCopy.resQ L' _ hNF σ) = 1 := by
      intro σ
      show j (βQ _) / gam (cj _) = 1
      rw [hβQ1 _ (hres0 σ), hgam1 _ (hres σ), map_one, div_one]
    refine ⟨c', _, uu, g7Out_rescale _ ℓ Tm c' c' a' β' _ _ φ uu hφ0 hφ1 (fun g => ?_)
      (fun g => ?_) hG7⟩
    · show j (βQ g / gamQ (cj g)) = j (βQ g) / j (gamQ (cj g)) * 1
      rw [map_div₀, _root_.mul_one]
    · show j (βQ g) = j (βQ g) / gam (cj g) * gam (cj g)
      rw [div_mul_cancel₀ _ (hgam0 _)]

  -- kerwild-fix: `j_ℓ := Φ_ℓ ∘ ι_ℂ`
  obtain ⟨Φ5⟩ := G8Tate.exists_complex_equiv 5
  obtain ⟨Φ3⟩ := G8Tate.exists_complex_equiv 3
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 (KWFix.jOf Φ5 ιC)
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 (KWFix.jOf Φ3 ιC)
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, ιC, Φ5, Φ3, _, c5, u5, _, c3, u3, hιβ,
    KWFix.g7Out_eps_congr _ 5 _ _ _ _ _ _ _
      (KWFix.g7Out_beta_congr _ 5 _ _ _ _ _ _ _ h5 fun g => congrArg Φ5 (hιβ g).symm)
      (KWFix.cocycle_map Φ5 β ε hβe),
    KWFix.g7Out_eps_congr _ 3 _ _ _ _ _ _ _
      (KWFix.g7Out_beta_congr _ 3 _ _ _ _ _ _ _ h3 fun g => congrArg Φ3 (hιβ g).symm)
      (KWFix.cocycle_map Φ3 β ε hβe), ?_⟩
  -- `FrobTraceLink` from `AlgFrobLink`
  obtain ⟨S, hS⟩ := hF L A m hmL hmLL hFalg
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  exact ⟨k, _, hk, Ab, α, N', hN',
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3,
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5⟩

end FrobTrace

end

end KWFixCopySec

section KWFixCopyCSec

/-! ### §2b. G7 with `[L:ℚ] ≤ D` kept: a copy of g0-mod-field's `g7OutUnr_of_g4Out`
(scratch/frob-trace/FrobTrace.lean l.636-662, verbatim except the header and `hLD` inserted in the
final `refine`; made by mk_fix.py). The `open` lines are FrobTrace.lean's l.53-54. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

theorem _root_.KWFix.g7OutUnrD_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo)
    (hSq : LeafSqrtCrit) (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) :
    KWFix.G7OutUnrD u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hLD, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

end G0ModField

end

end KWFixCopyCSec

section KWFixFinalSec

/-! ### §3. `LocalGlue` on the data of the bridges in Glazer's normalization -/

noncomputable section

namespace KWFix

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

/-- **`TateBridge35E` contains g14-trace's `TateBridge35` (proved)**, with `j_ℓ = Φ_ℓ ∘ ι_ℂ`. -/
theorem tateBridge35_of_E (h : TateBridge35E) : G14Bridge.TateBridge35 := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, h5, h3, hF⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨aQ, βQ, jOf Φ5 ιC, jOf Φ3 ιC, Tm5, c5, _, u5, Tm3, c3, _, u3,
    g7Out_beta_congr _ 5 _ _ _ _ _ _ _ h5 fun g => congrArg Φ5 (hιβ g),
    g7Out_beta_congr _ 3 _ _ _ _ _ _ _ h3 fun g => congrArg Φ3 (hιβ g), hF, ιC, hιβ⟩

/-- **`KerWild` for `Φ ∘ β` (proved)**: local-glue's `kerWild_of_g7Data` with the injective
`ι = Units.map Φ` and G7Data's kernel-field clause. -/
theorem kerWild_of_equiv {ℓ : ℕ} [Fact ℓ.Prime] (Φ : ℂ ≃+* PadicAlgCl ℓ) {u : ℚ}
    {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL') :
    @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L :=
  G15Ram.kerWild_of_g7Data β (LGKerWild.g7Data_ker hD)
    (Units.map (Φ : ℂ →+* PadicAlgCl ℓ).toMonoidHom) (Units.map_injective Φ.injective)
    (fun _ => rfl)

/-- **`LocalGlue` on `G7Out` in Glazer's normalization (proved).** For G7's data with
`[L:ℚ] ≤ D`, `G7Out` at `ℓ` on `A_{L'}` with `β' = Φ ∘ β`, `ε' = Φ ∘ ε`, and `p ≠ ℓ`:
`LocalGlue p Tm a (Φ ∘ β) L`, from R6, I2-Tors and `UnramRoots`. `G7Clauses` is
`g7Clauses_of_g7Data`, `KerWild` is `kerWild_of_equiv`, `DescentPts` is `descentPts_of_g7`. -/
theorem localGlue_of_E (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (Φ : ℂ ≃+* PadicAlgCl ℓ)
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L :=
  LGKerWild.localGlue_of_kerWild hR6 hTors hU hpℓ hLL' A h7 (kerWild_of_equiv Φ hD)
    (G8Tate.g7Clauses_of_g7Data Φ hD hLD)

/-- **`LocalGlue` at every `ℓ` from `TateBridgeE` (proved; replaces lg-kerwild's
`exists_localGlue_of_tateBridgeK`).** For G7's data with `[L:ℚ] ≤ D`, `dim A_{L'} = 2`,
`rank End(A_{L'}) = 4` and every coefficient prime `ℓ`: operator data with `G7Out` at `ℓ` in
Glazer's normalization, and for these data `G7Clauses`, `KerWild` and `LocalGlue p` at every
`p ≠ ℓ` hold. No hypothesis on the hidden data. -/
theorem exists_localGlue_of_tateBridgeE (hB : TateBridgeE) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
      (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu ∧
      G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L := by
  obtain ⟨Φ, Tm, c, a, uu, h7⟩ := hB u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Φ, Tm, c, a, uu, h7, G8Tate.g7Clauses_of_g7Data Φ hD hLD, kerWild_of_equiv Φ hD,
    fun p hp hpℓ => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact localGlue_of_E hR6 hTors (hU p ℓ) hpℓ hD hLD Φ h7

/-- **Main result (every `ℓ`): `LocalGlue` from the leaves I3.M0, R6, I2-Tors and the textbook
Prop `UnramRoots` (proved).** `TateBridgeE` is `tateBridgeE_of_tateModuleFree`. -/
theorem exists_localGlue_of_leaves (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
      (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu ∧
      G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L :=
  exists_localGlue_of_tateBridgeE (tateBridgeE_of_tateModuleFree hT) hR6 hTors hU
    u P L A ε N χ β L' hLL' hD hdim hrk hLD ℓ

/-- **`LocalGlue` at `ℓ = 5` and `ℓ = 3` on `TateBridge35E`'s data (proved)**: the operators
`Tm₅`, `Tm₃` are linked by `FrobTraceLink`, and `LocalGlue` holds at every `p ≠ 5` for `Tm₅` and
every `p ≠ 3` for `Tm₃`, with `G7Clauses` and `KerWild` discharged. -/
theorem exists_localGlue35_of_tateBridge35E (hB : TateBridge35E)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) :
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
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      G15Ram.G7Clauses (fun g => Φ5 (β g : ℂ)) (fun g h => Φ5 (ε g h : ℂ)) L ∧
      G15Ram.G7Clauses (fun g => Φ3 (β g : ℂ)) (fun g h => Φ3 (ε g h : ℂ)) L ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5
        (fun g => Φ5 (ιC (aQ g))) (fun g => Φ5 (β g : ℂ)) L) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 → @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3
        (fun g => Φ3 (ιC (aQ g))) (fun g => Φ3 (β g : ℂ)) L) := by
  obtain ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, h5, h3, hF⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  refine ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, h5, h3, hF,
    G8Tate.g7Clauses_of_g7Data Φ5 hD hLD, G8Tate.g7Clauses_of_g7Data Φ3 hD hLD,
    fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_E hR6 hTors (hU p 5) hp5 hD hLD Φ5 h5
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_E hR6 hTors (hU p 3) hp3 hD hLD Φ3 h3

/-- **In Glazer's normalization `a` carries the real factor (proved):** if `a ≡ 1` then
`c = ε' = Φ ∘ ε` is a sign, i.e. every `n/d = ±1`. (unram-tate's witness had `a ≡ 1`, `ε' = c`.) -/
theorem c_eq_of_a_one {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ}
    [Fact ℓ.Prime] {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a β' : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ)}
    (h7 : GaloisCopy.G7Out A ℓ Tm c ε' a β' uu) (ha : ∀ g, a g = 1) (g h : PkgI4.GQ) :
    c g h = ε' g h := by
  have := h7.2.2.2.1 g h
  rw [ha, ha, ha, _root_.one_mul, _root_.one_mul, _root_.mul_one] at this
  exact this

/-- **Main result (every `ℓ`), leaves only: `LocalGlue` from I3.M0, R6 and I2-Tors (proved).**
`UnramRoots` is unram-roots' theorem `UnramRootsTask.unramRoots_all` (Mathlib + vendored Tau Ceti). -/
theorem exists_localGlue_of_leaves' (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
      (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
        (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu ∧
      G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L :=
  exists_localGlue_of_leaves hT hR6 hTors UnramRootsTask.unramRoots_all
    u P L A ε N χ β L' hLL' hD hdim hrk hLD ℓ

/-- **From G4's output (proved):** G4's data give G7's data with `[L:ℚ] ≤ D` (four B2 leaves,
`g7OutUnrD_of_g4Out`), and on these data, given `dim A_{L'} = 2` and `rank End(A_{L'}) = 4`, every
`ℓ` has operator data in Glazer's normalization with `G7Clauses`, `KerWild` and `LocalGlue` at
every `p ≠ ℓ` (leaves I3.M0, R6, I2-Tors). -/
theorem exists_localGlue_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo)
    (hSq : LeafSqrtCrit) (hUnr : LeafUnramified) (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (u : ℚ) (P : QML3 Qbar) (h4 : G4Out u P) :
    ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
      (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
      Module.finrank ℚ L ≤ ZInQ.heightD ∧ G7Data u P L A ε N χ β L' hLL' ∧
      ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
        Module.finrank ℤ
          (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
        ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Φ : ℂ ≃+* PadicAlgCl ℓ)
          (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
            (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
          (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a : PkgI4.GQ → PadicAlgCl ℓ)
          (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
            (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
          @GaloisCopy.G7Out L' _ (numberField_of_fd L')
            (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c
            (fun g h => Φ (ε g h : ℂ)) a (fun g => Φ (β g : ℂ)) uu ∧
          G15Ram.G7Clauses (fun g => Φ (β g : ℂ)) (fun g h => Φ (ε g h : ℂ)) L ∧
          @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') (fun g => Φ (β g : ℂ)) L ∧
          ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ →
            @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a (fun g => Φ (β g : ℂ)) L) := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hLL', hLD, hD⟩ :=
    g7OutUnrD_of_g4Out hHasse hTwo hSq hUnr u P h4
  exact ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hLL', hLD, hD,
    fun hdim hrk ℓ _ => exists_localGlue_of_leaves' hT hR6 hTors u P L A ε N χ β L' hLL' hD
      hdim hrk hLD ℓ⟩

/-- **`ℓ = 5, 3` with `FrobTraceLink`, from I3.M0, frob-trace's glue `AlgFrobRed`, R6 and I2-Tors
(proved).** -/
theorem exists_localGlue35_of_algFrobRed (hT : PkgI3.TateModuleFree)
    (hR : FrobTrace.AlgFrobRed) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) :
    TateBridge35E ∧ ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
      (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
      G7Data u P L A ε N χ β L' hLL' →
      (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
      Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
      Module.finrank ℚ L ≤ ZInQ.heightD →
      ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
        (Φ5 : ℂ ≃+* PadicAlgCl 5) (Φ3 : ℂ ≃+* PadicAlgCl 3)
        (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
        (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
        (∀ g, ιC (βQ g) = (β g : ℂ)) ∧
        @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5
          (fun g => Φ5 (ιC (aQ g))) (fun g => Φ5 (β g : ℂ)) L) ∧
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 → @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3
          (fun g => Φ3 (ιC (aQ g))) (fun g => Φ3 (β g : ℂ)) L) := by
  have hB := tateBridge35E_of_algFrobLink hT
    (FrobTrace.algFrobLink_of_one (FrobTrace.algFrobOne_of_red hR))
  refine ⟨hB, fun u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk hLD => ?_⟩
  obtain ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, c5, u5, Tm3, c3, u3, hιβ, -, -, hF, -, -, h5, h3⟩ :=
    exists_localGlue35_of_tateBridge35E hB hR6 hTors UnramRootsTask.unramRoots_all
      u P L A ε N χ β L' hLL' hD hdim hrk hLD
  exact ⟨aQ, βQ, ιC, Φ5, Φ3, Tm5, Tm3, hιβ, hF, h5, h3⟩

end KWFix

end

end KWFixFinalSec

#print axioms G8Tate.exists_complex_equiv
#print axioms G8Tate.g7Clauses_of_g7Data
#print axioms KWFix.tateBridge_of_E
#print axioms KWFix.g7Out_eps_congr
#print axioms KWFix.tateBridgeE_of_tateModuleFree
#print axioms KWFix.tateBridge35E_of_algFrobLink
#print axioms KWFix.tateBridge35_of_E
#print axioms KWFix.kerWild_of_equiv
#print axioms KWFix.localGlue_of_E
#print axioms KWFix.exists_localGlue_of_tateBridgeE
#print axioms KWFix.exists_localGlue_of_leaves
#print axioms KWFix.exists_localGlue35_of_tateBridge35E
#print axioms KWFix.g7OutUnrD_of_g4Out
#print axioms KWFix.g7OutUnr_of_D
#print axioms KWFix.c_eq_of_a_one
#print axioms UnramRootsTask.unramRoots_all
#print axioms KWFix.exists_localGlue_of_leaves'
#print axioms KWFix.exists_localGlue_of_g4Out
#print axioms KWFix.exists_localGlue35_of_algFrobRed
