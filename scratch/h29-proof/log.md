# h29-proof results log

Task h29-proof, started 2026-11-16 14:35 PST. Base 0caafe66 (fork main w80).
Target: hL29 = `ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3`
(`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean:455`).

## Step 0. Setting (VERIFIED by reading files)
* `~/tyz-src/Period7.tex` is NOT on this host (ls fails). All TYZ line numbers below are quoted from
  h29-split.md, h29-fix.md, h29-ne3.md, rv-tyz-inputs.md (which read it), not re-read.
* `~/pyenv` absent; Python with cypari2 run through `uv run --offline --with cypari2 python -I`.
* Genus theory is already proved in Lean in the project: `ZInQ.RouteK.Redei.chi n q :
  ClassGroup (𝓞 (QNeg n)) →* Multiplicative (ZMod 2)` (χ_q([𝔞]) = (N𝔞/q)),
  `range_sq_eq_ker_chi` (Cl² = ⋂ ker χ_q, odd squarefree n > 1), `card_ker_sq_eq`
  (#Cl[2] = 2^{t-1}), `exists_chi_eq` (image of the genus map) — RouteK/Redei/{Genus,FourRank,Dirichlet}.lean.

## Step 1. Verdict on an outright proof (analysis)
* hL29 relates Q(n) (a finite Brandt-module sum) to 𝓛(d₁)𝓛(d₂) (L-values `lcalSq`, defined from the
  continuation of Mathlib's L-series). For a prime p ≡ 3 (mod 8), p ≠ 3, it says ℓ(p)ℓ(1) = ±Q(p), i.e. an
  exact evaluation of L(E_p,1)/Ω_p for infinitely many p. No open leaf among TYZProp23Printed,
  TYZTestVectorExists, LegendreThreeSquares, JonesPallX2Y2Z16 mentions `lcalSq`; any proof needs the explicit
  Waldspurger formula (TYZ Theorem 2.1 / 4.2, from Yuan–Zhang–Zhang). Not provable here.

## Step 2. Numerical check of the fallback leaves (VERIFIED, computed)
`genus_check.py` (uses brandt.py, brandt2.py of h29-fix, copied unchanged), output `genus_check-output.txt`.
n ∈ {11,17,33,35,41,51,57,73,105,113,123,145,195,219}, 2 admissible τ each (28 runs): for every set T of
primes of n, P_T = Σ_{t∈Cl_n} χ_T(t) f_n(t), d₂ = ∏T, d₁ = n/d₂:
(V) d₁, d₂ ≢ 1 (8) ⇒ P_T = 0; (F) d₂ ≡ 1 (8) ⇒ P_T² = 4^{k-1} w_K² 𝓛(d₁)²𝓛(d₂)²;
(S) n ≡ 1 (8) ⇒ P_T = P_{T^c}; (C) n ≡ 3 (8) ⇒ χ_T = χ_{T^c}; (PQ) Σ_T P_T = 2^k Q(n). ALL OK.

## Step 3. Lean: hL29 from TYZThm21Pairs + TYZLemma28Sym (VERIFIED, compiled)
`scratch/h29-proof/TYZLemma29Genus.lean` (namespace `ZInQ.Contrib.TYZDecomp.H29Genus`), checked with
`lake env lean` against the build tree copied (reflink) from ~/dzq-check2 (same sources for every imported
module: TYZLemma29Mod2, Redei/{Genus,FourRank}, TYZChain/Thm35, TYZDecomp/Leaves — `cmp` VERIFIED).
`H29GenusCheck.lean` (= the file + `#print axioms`): all of
`tyzLemma29PrintedNe3_of_genus : TYZThm21Pairs → TYZLemma28Sym → TYZLemma29PrintedNe3`,
`tyzLemma29Printed_of_genus` (w_K form, all n incl. 3), `tyzThm21At31_of_thm21Pairs`,
`tyzLemma29Mod2_of_genusLeaves`, `torsionOrder_qNeg_eq_two` depend on [propext, Classical.choice, Quot.sound].
Glue proved: `sum_gchar_cl` (Σ_T χ_T = 2^k·[Cl²], from Redei.range_sq_eq_ker_chi), `sum_quadPeriod` ((PQ):
Σ_{d∣n} P = 2^k Q), `quadPeriod_div` (n≡3 (4): P(d₁,d₂) = P(d₂,d₁), product formula), `unit_eq_one_or_neg_one`
and `torsionOrder_qNeg_eq_two` (#μ(ℚ(√−n)) = 2 for squarefree 1 < n ≠ 3), `sum_divisors_three`,
`sum_divisors_one` (the pairings), `sum_formula` (sign choice), `lemma29_core`.

## Step 4. #discharges (VERIFIED)
* Base 0caafe66 (Main rebuilt from base sources, 13698 jobs): `DISCHARGES [hL29] by
  H29Genus.tyzLemma29PrintedNe3_of_genus still assumes [TYZThm21Pairs, TYZLemma28Sym]`, standard axioms;
  also `[hT21] by tyzThm21At31_of_thm21Pairs`. Output DischargesH29Proof-output.txt (56 open hypotheses).
* Merged origin/main 5e235a40 (leaf-fold32b) into the branch; Main rebuilt (14102 jobs); same hL29 line
  (DischargesH29Proof-main-output.txt, 45 open hypotheses). H29GenusCheck: verbatim copy `rfl`, axioms standard.

## Step 5. Independent review (model agent, read-only)
Both leaves faithful consequences of the print as quoted; no false/vacuous/too-strong clause. Two docstring
nits applied (convention-insensitivity reason; χ₀ relation attributed to rv-tyz-inputs). Reviewer's extra
numerics (scratch/h29-proof/review/: n = 561 all 64 τ, 697, all τ at 51, 105; sweep 3 < n < 700, 552 runs) all OK.
NOTE: the sweep exceeded the 30-input limit of the task rules; recorded, not repeated.

## Step 6. chi0 support (VERIFIED, chi0_support.py)
f_n supported on χ₀(nrd) = +1 on the 8 classes for all 18 runs with n ≡ 1 (8); not for n ≡ 3 (8).
Supports the χ₀-twist proof of Lemma 2.8 from Prop 2.3 + uniqueness (report §4; not in Lean).
