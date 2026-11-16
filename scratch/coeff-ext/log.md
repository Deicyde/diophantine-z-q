# coeff-ext results log

Base origin/main 2880fef1. Build copied from ~/dzq-check2 (same commit) 2026-11-16 06:40.

## Targets (copied verbatim)
- `DS965Weak.DSThm965Weak` (ZInQKernel/Contrib/OneProof/DSThm965Weak.lean l.56), bundle field
  `HDec.HSyn.OpenResearchLeaves26.dsThm965Weak` (TailZ41.lean l.67).
- `ZInQ.Contrib.HodgeSplit.DSThm966` (TailS.lean l.1128), field `OpenResearchLeaves26.dsThm966` (TailZ41 l.22).

## Plan (leaves)
- L1 DS 9.6.5 over K_{f,λ} = `λ.adicCompletion (coeffField f)`, DS-form eigenform (Tau Ceti `HeckeRing.GL2.Eigenform`,
  DS Def 5.8.1), hypothesis `NumberField (coeffField f)`.
- L2 `K_f` is a number field (needed: L1's statement presupposes it; DSThm965Weak quantifies over all g).
- L3 DSThm966 with DS-form eigenform, locator Deligne-Serre 1974 Thm 4.1.
- Glue: coefficient form -> DS form (U_p part for p | N); K_f -> ℚ̄_ℓ via ιL∘ιC⁻¹, λ from the norm, continuous
  extension to K_{f,λ} (completion), charpoly_map.

## Findings / compile outcomes
- VERIFIED (compiled, Dict.lean): `IsNormalizedEigenformDS` (Tau Ceti `HeckeRing.GL2.Eigenform`, DS Def 5.8.1, a_1 = 1)
  ⟺ kernel `IsNormalizedEigenform`; the `U_p` part (`heckeTCuspNat_eq_coeff_smul_all`, every prime p) via Tau Ceti
  `heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom`. Axioms standard.
- VERIFIED (compiled, Transfer.lean §1-4): algebraic elements of ℂ lie in ιC(ℚ̄); place λ_τ = {a ∈ 𝓞_K : ‖τ a‖ < 1}
  is a HeightOneSpectrum over ℓ; v_λ(x) ≤ v_λ(y) ⇒ ‖τx‖ ≤ ‖τy‖; τ continuous on WithVal v_λ; finite ℚ_ℓ-field
  tgt τ ⊇ τ(K) is complete; continuous extension τhat : K_λ → ℚ̄_ℓ with τhat ∘ algebraMap = τ.
- VERIFIED (compiled, scratch/coeff-ext/DSCoeffExt.lean, 2026-11-16 ~07:30): `DSCoeffExt.dsThm965Weak_of_printed
  (h1 : DSThm965Printed) (h2 : EigenformCoeffFieldFinite) : DS965Weak.DSThm965Weak` and
  `DSCoeffExt.dsThm966_of_printed (h : DSThm966Printed) : ZInQ.Contrib.HodgeSplit.DSThm966`; converse
  `dsThm966Printed_of_dsThm966`. Axioms [propext, Classical.choice, Quot.sound].
- VERIFIED: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DSCoeffExt`
  succeeded (13699 jobs; DSCoeffExt 14 s). `#discharges` (scratch/coeff-ext/discharges-output.txt):
  `OpenResearchLeaves26.dsThm965Weak` by `DSCoeffExt.dsThm965Weak_of_printed`, still assumes
  [DSCoeffExt.DSThm965Printed, DSCoeffExt.EigenformCoeffFieldFinite]; `OpenResearchLeaves26.dsThm966` by
  `DSCoeffExt.dsThm966_of_printed`, still assumes [DSCoeffExt.DSThm966Printed]; axioms standard.
- VERIFIED (Check.lean): verbatim copies of both targets equal the originals by rfl.
- VERIFIED: autofold dry run (scratch/coeff-ext/autofold-dryrun.txt): strict 34/11 on 45 -> 35/11 on 46, strictest
  34/11 -> 35/11 (GLUE unchanged, one more LEAF: `eigenformCoeffFieldFinite`). The generated fold (line 1 stripped,
  scratch/coeff-ext/FoldCheck.lean) compiles: `HDec.HSyn.sixContactMin_of_open36` standard axioms.
- Locator move (dsThm966 -> Deligne-Serre 1974 Thm 4.1 (4.1.1), p. 514): 6 comment-only docstring edits by
  scratch/coeff-ext/locator_patch.py in TailS (l.1120), TailT (l.1531, l.1991), TailX (l.30, l.101), TailZ6 (l.122).
  VERIFIED: `lake env lean` on each of the four files, no errors.
- Report docs/research/coeff-ext.md written.
