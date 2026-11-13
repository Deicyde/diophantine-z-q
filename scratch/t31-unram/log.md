# t31-unram results log

## Target (VERIFIED, read in ZInQKernel/HDecomp/Descent/B2Glue.lean:318)
`GlueDescent.B2Q.LeafUnramified : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ), IsSignCocycle ε → InflatedFrom L ε →
    ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε)`

## Plan (chosen route; avoids Brauer groups / Kummer)
1. Abstract lemma (Cyclic.lean): G top. group, ψ : G →* H with open kernel, every ψ σ a power
   of φ, φ = ψ g₁, orderOf φ = 2f, η sign cocycle on G depending only on ψ-classes modulo
   ⟨φ^f⟩ ⇒ SignCob η. (H²(ℤ/f,±1) dies on inflation to ℤ/2f.)
2. Global (Good.lean): w prime of 𝓞L over p with e=1 (inertia trivial, Mathlib
   card_inertia_eq_ramificationIdxIn) ⇒ ∃ b ∈ 𝓞L with g'(b) ∉ w (g = minpoly), for all b in a
   coset b₀ + p𝓞L.
3. Local (Local.lean): ι : ℚ̄ → ℚ̄_p (the embedding of absoluteGaloisGroup.map); w := {x | ‖ι x‖<1}
   (spectral norm); TC criterion isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative ⇒
   ℚ_p(ι b) unramified ⇒ ι b ∈ ℚ_p^ur (TC le_maximalUnramifiedExtension_iff) ⇒ ι(L) ⊆ K^ur ⇒
   ι(L) ⊆ K_f (TC unramifiedExtension).
4. Assembly with ψ = restriction G_{ℚ_p} → Gal(K_{2f}/ℚ_p) (cyclic of order 2f, TC).

## Compile log
- 04:14 Cyclic.lean `T31.signCob_of_cyclic_even` compiles (VERIFIED, lake env lean).
- 04:3x Good.lean `T31.exists_base` compiles (VERIFIED). Uses Mathlib
  `Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.ramificationIdxIn_eq_ramificationIdx`,
  `Splits.eval_root_derivative`, `Normal.minpoly_eq_iff_mem_orbit`.
- 04:4x Local.lean `T31.exists_unramifiedExtension` compiles (VERIFIED). Uses TC
  `isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative`,
  `IntermediateField.le_maximalUnramifiedExtension`, `mem_maximalUnramifiedExtension_iff`,
  `finiteIntermediateField*`, `IntermediateField.valuativeExtension`,
  `Valuation.Integers.isIntegral_iff_valuation_le_one`.
- 04:3x Main.lean `ZInQ.Contrib.T31.leafUnramified : GlueDescent.B2Q.LeafUnramified` compiles
  (VERIFIED, `lake build ZInQKernel.Contrib.T31.Main`, 9129 jobs). `#print axioms`:
  [propext, Classical.choice, Quot.sound] (VERIFIED, scratch/t31-unram/Axioms.lean).
  TC inputs: `isUnramified_unramifiedExtension`, `finrank_unramifiedExtension`,
  `unramifiedExtension_le_of_dvd`, `isCyclic_algEquiv`, `algebraicExtensionValuativeRel`,
  `algebraicExtension_valuativeExtension`, `Padic.irreducible_natCast_self`.
- Namespace renamed `T31` → `ZInQ.Contrib.T31` (rebuilt, axioms re-checked: VERIFIED).
- Leaves.lean blocks GlueDescent.B2 (8544-8737) and GlueDescent.B2Q (8749-8837) are textually
  identical to ZInQKernel/HDecomp/Descent/B2Glue.lean (VERIFIED, diff).
- Wired.lean: `b2_of_leaves_T31`, `b3_degree_le_QM_of_T14_T15_T31` compile, standard axioms
  (VERIFIED).
- Not used / not vendored: Brauer/Torsion.lean and its 7 missing modules, Brauer/Unramified.lean,
  decompositionEquiv, the continuous-cohomology comparison. Reason: elementary route (cyclic
  inflation lemma) suffices once ι₀(L) ⊆ K_f.

## Findings
- T31 is TRUE as stated; no extra hypothesis needed (VERIFIED by the compiled proof).
- `Ideal.card_inertia_eq_ramificationIdxIn` instance requirements (HasSeparableResidueFieldsAt,
  Flat ℤ (𝓞 L)) resolve automatically for `𝓞 L` over `ℤ` (VERIFIED).
- Pitfall: in a section with `variable (K)`, a theorem whose statement mentions `K` only through
  instances needs `include K`.
- Pitfall: `GQp p = Field.absoluteGaloisGroup ℚ_[p]` has no `CoeFun`; use a wrapper
  `actp σ : ℚ̄_p ≃ₐ[ℚ_p] ℚ̄_p := σ`.
