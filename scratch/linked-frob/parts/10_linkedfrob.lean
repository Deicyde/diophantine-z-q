/-! # linked-frob: linked-tate's glue `UnramTate.LinkedFrob`, reduced to frob-trace's `AlgFrobLink`

`UnramTate.LinkedFrob` (scratch/linked-tate/parts/97_linkeddata.lean, compiled above, unchanged) asks
g14-trace's `FrobTraceLink` for the canonical operators `tmOf … ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at
`ℓ = 5, 3`. frob-trace's `AlgFrobLink` (copied above, verbatim) gives, outside a finite set `S` of
primes, at every arithmetic Frobenius `τ` above `p ∉ S` and for every `g` (here `g = h`), one abelian
variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)`, `N ≠ 0` and, for every `ℓ ≠ p`, a
`ℚ_ℓ`-isomorphism carrying `N·V_ℓ(m_{gτg⁻¹})` to `V_ℓ(α')`. frob-trace's `frobCompare_opV_conjE`
turns that into the kernel's `FrobCompare` for `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)`, which is `tmOf … ℓ τ`.
The set is `S ∪ {3, 5}`, so that `ℓ ≠ p` at `ℓ = 3, 5`. -/

section LinkedFrobSec

noncomputable section

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

namespace LinkedFrobRed

/-- `tmOf … ℓ τ` is `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)` (definitional). -/
theorem tmOf_eq {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (ℓ : ℕ) [Fact ℓ.Prime] (τ : PkgI4.GQ) :
    tmOf hLL' A Θ h m ℓ τ =
      opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m (h * τ * h⁻¹))) :=
  rfl

/-- **`LinkedFrob` from frob-trace's `AlgFrobLink` (proved).** Only three of the descent-datum
clauses are used (`m_σ` is the Galois action on `G_L`, the coset rule, algebraicity `F_σ`). -/
theorem linkedFrob_of_algFrobLink (hF : FrobTrace.AlgFrobLink) : UnramTate.LinkedFrob := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨S, hS⟩ := hF L A m h3 h4 h8
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  refine ⟨k, inferInstance, hk, Ab, α, N', hN', ?_, ?_⟩
  · rw [tmOf_eq]
    exact FrobTrace.frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3
  · rw [tmOf_eq]
    exact FrobTrace.frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5

/-- **`LinkedFrob` from frob-trace's `AlgFrobRed` (proved):** frob-trace's
`AlgFrobRed → AlgFrobOne → AlgFrobLink`. -/
theorem linkedFrob_of_algFrobRed (hR : FrobTrace.AlgFrobRed) : UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobLink (FrobTrace.algFrobLink_of_one (FrobTrace.algFrobOne_of_red hR))

end LinkedFrobRed

end

end LinkedFrobSec
