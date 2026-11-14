
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
