# kummer-comp results log

Task: prove `KummerCompositum` (scratch/ts-kummer/KummerTS.lean, merged from origin/wip/ts-kummer),
the last open piece under `KummerMeetGlue` (`TsKummer.kummerMeetGlue_of_compositum`).

## Step 0: setup
- Merged origin/wip/ts-kummer (clean). Built ZInQKernel.HDecomp.QM.Pin and
  ZInQKernel.HDecomp.Descent.B2Glue (the imports of KummerTS.lean) in this worktree: success.
- B2Glue imports `Mathlib`, so the final environment is full Mathlib; the dev file
  scratch/kummer-comp/Core.lean uses `import Mathlib` with verbatim dev copies of `Qbar`,
  `KummerShape`, `KummerCompositum`.

## Step 1: abstract core `KummerComp.compositum_core`, compiled
- Statement: `A` domain, `B` domain free and integral over `A`, `f : A → O` injective into a
  domain, `α : O → F`, `β : B → F` (`F` a domain) with `α ∘ f = β ∘ algebraMap`, `β` surjective ⟹
  a field `E'` with `Algebra O E'` (injective), `h : B → E'` injective with
  `h ∘ algebraMap = algebraMap ∘ f`, `Subfield.closure (range h ∪ range (algebraMap O E')) = ⊤`, a
  prime `𝔐` of `integralClosure O E'` with `𝔐 ∩ O = ker α`, and an injective
  `ψ : F → integralClosure O E' ⧸ 𝔐` with `ψ ∘ α = mk ∘ algebraMap`.
- Proof: `T = O ⊗_A B`, `χ : T → F` (`o ⊗ b ↦ α o β b`, surjective), `N = ker χ`; a minimal prime
  `𝔫 ≤ N` (`Ideal.exists_minimalPrimes_le`); nonzero `o` are non-zero-divisors of `T` (`T` is
  `O`-free), so `𝔫 ∩ O = 0` (`notMem_nonZeroDivisors_of_mem_mem_minimalPrimes`); `E' = Frac(T/𝔫)`;
  `B → E'` injective via `Ideal.under_ne_bot_of_integral_mem`; image of `T` integral over `O`;
  lying over (`Ideal.exists_ideal_over_prime_of_isIntegral`) for `T → integralClosure O E'`;
  `ψ = quotientMap ∘ (T/N ≃ F)⁻¹`.
- `lake env lean scratch/kummer-comp/Core.lean`: 0 errors (VERIFIED).

## Step 2: `KummerComp.kummerCompositum : KummerCompositum` PROVED (dev file), compiled
- `compositum_finrank`: `ι : E → E'` with `ι ∘ algebraMap K E = algebraMap K' E' ∘ σ` and
  `Subfield.closure (range ι ∪ range (algebraMap K' E')) = ⊤` ⟹ `FiniteDimensional K' E'` and
  `finrank K' E' ≤ finrank K E` (primitive element `a`; `ι a` is a root of `(minpoly K a).map σ`;
  `K'⟮ι a⟯ = ⊤`; `IntermediateField.adjoin.finrank`).
- `extend_along`: `ψ : F → R` injective integral map of domains, `φ : F → ℚ̄` injective ⟹
  `φ'' : R → ℚ̄` with `φ'' ∘ ψ = φ` (`IsAlgClosed.lift`).
- `kummerCompositum`: `O = ℚ[s][1/Q]`, `f : ℚ[X] → O`, `X ↦ P/Q` (injective: `P/Q` is
  transcendental, `RatFunc.transcendental_of_ne_C`); `F = B/𝔓`, `α = (eval at s₀)` into `F`,
  `β = mk`; `compositum_core`; `E'` gets `Algebra ℚ[X] E'` through `O` and `Algebra (RatFunc ℚ) E'`
  by `IsFractionRing.lift`; `ι = IsFractionRing.lift h`; `σ = IsFractionRing.lift (θ ∘ f)`
  (`θ : O → ℚ(s)`); `KummerShape` from generation; `𝔓' = 𝔐 ∩ B'`, `𝔓' ∩ ℚ[s] = (s − s₀)`;
  `φ' = φ'' ∘ (B'/𝔓' → C/𝔐)`; `range φ ⊆ ℚ(range φ')` because each `c ∈ C = intCl O E'` has
  `Q^k c ∈ B'` (`IsIntegral.exists_multiple_integral_of_isLocalization`) and `Q^k ≡ Q(s₀)^k ∈ ℚ^×`
  mod `𝔐`.
- `lake env lean scratch/kummer-comp/Core.lean` (~19 s): 0 errors; `#print axioms` of
  `compositum_core` and `kummerCompositum`: `[propext, Classical.choice, Quot.sound]` (VERIFIED).
- Lean pitfalls: (1) `RatFunc.transcendental_of_ne_C` uses `RatFunc.instAlgebraOfPolynomial ℚ ℚ`,
  the goal `Transcendental ℚ r` uses `DivisionRing.toRatAlgebra`: `convert` then
  `Subsingleton.elim`; (2) `Module F R` not found for `let R := C' ⧸ 𝔐` with a `letI` algebra:
  moved to a lemma (`extend_along`) over variable types; (3) `rw [injective_iff_map_eq_zero]` on
  `φ : B/𝔓 →+* AlgebraicClosure ℚ` timed out in typeclass search (raised
  `synthInstance.maxHeartbeats` to 200000); (4) `((m : ℚ[X]).eval s₀ : Qbar)` elaborates the
  cast inward; write `(((m : ℚ[X]).eval s₀ : ℚ) : Qbar)`.

## Step 3: final file, compiled
- `scratch/kummer-comp/KummerComp.lean` = `scratch/ts-kummer/KummerTS.lean` verbatim + the
  appendix of Core.lean (dev copies removed, `Qbar` written as `(AlgebraicClosure ℚ)`) +
  `FinalTail.lean.part`; built by `make_final.py`; `check_identical.py` prints PREFIX IDENTICAL
  (VERIFIED).
- New final statements (namespace `KummerComp`):
  - `kummerCompositum_final : PropTSGlue.KummerCompositum`;
  - `kummerMeetGlue : KummerMeetGlue` (= `TsKummer.kummerMeetGlue_of_compositum
    kummerCompositum_final`);
  - `propTSAll_kc`: `PropTSAll` from T2, `R1R2fp`, `MobiusGlue`, `SNSpecialize` and the five
    Hecke Props (`KummerCompositum` removed from `TsKummer.propTSAll_ts`).
- `lake env lean scratch/kummer-comp/KummerComp.lean` (1 min 05 s): 0 errors; all 81
  `#print axioms` lines `[propext, Classical.choice, Quot.sound]` (VERIFIED,
  scratch/kummer-comp/compile_out.txt).
