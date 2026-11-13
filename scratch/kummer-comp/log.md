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
