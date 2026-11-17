# h11-reduce results log

Base origin/main 0caafe66. TYZ source Period7.tex: NOT on this host (~/tyz-src absent; searched ~/dzq, ~/notes,
~/local, ~/persistent, ~/dzq-runs, /tmp). TYZ line numbers below are quoted from earlier notes.

## Findings (before Lean)

1. VERIFIED (read in Leaves.lean / TYZLemma29Mod2.lean): the open leaves TYZLemma29PrintedNe3 and TYZThm21At31
   quantify over integer sign choices `ℓ : ℕ → ℤ` with `ℓ(m)^2 = lcalSq m` on all classes 1, 3. If h11 failed at
   one m, no such ℓ exists and both leaves are vacuously true. So h11 cannot be derived from the open leaves as
   stated; a form of Lemma 2.9 over real/complex square roots of 𝓛² (TYZ's 𝓛 is a real number) is needed.
2. TYZ's integrality argument (induction on divisors through Lemma 2.9, L1082-1088 per rv-pn-encoding) fails at
   n = 3 (w_K = 3: gives 3𝓛(3) ∈ ℤ only) and needs 𝓛(1) = ±1 (L1082, asserted).
3. Plan: n = 1 and n = 3 from Tunnell's formula (Invent. Math. 72 (1983); theorem number UNVERIFIED):
   L(C_n,1) = β (B(n) − A(n)/2)² / (4√n), n odd squarefree, β = ∫₁^∞ dx/√(x³−x) = omegaInt,
   A(n) = #{2x²+y²+8z² = n}, B(n) = #{2x²+y²+32z² = n}. A(1) = B(1) = 2, A(3) = B(3) = 4 give
   lcalSq 1 = lcalSq 3 = 1. Then h11 by strong induction from Lemma 2.9 (complex ℓ, n ≠ 3).
   The n = 3 case of h29 is also covered by Tunnell, so TYZThm21At31 is no longer needed.

## Computations

* `tunnell_check.py` (cypari2 via `uv run --offline --with cypari2`): Tunnell's formula on 30 odd squarefree n
  (1..187, all classes mod 8): max |L(C_n,1) − β(B−A/2)²/(4√n)| = 2.2e-19 at 38-digit precision. VERIFIED
  (numerically). Also lcalSq(n) = ((A−2B)/2^{k+1})² on the sample (1, 1, 4, 1, 1, ..., 16 at n = 113, 9 at 131).

## Lean

* Build tree: copied ~/dzq-check2/.lake/build (and lean/.lake/build); the dependency closure of
  TYZLemma29Mod2 is unchanged between 0caafe66 and dzq-check2 HEAD (git diff empty on those dirs);
  `lake build ZInQKernel.Contrib.OneProof.TYZLemma29Mod2` replayed (9196 jobs, nothing rebuilt).
* `ZInQKernel/Contrib/OneProof/TYZThm11Integral.lean` (namespace `ZInQ.Contrib.TYZDecomp.H11Reduce`):
  compiles, no errors, no warnings, no sorry (VERIFIED, `lake env lean`, second attempt after two one-line
  fixes). `#print axioms` (scratch/h11-reduce/Axioms.lean, output Axioms-output.txt): standard three for
  `tyzThm11Integral_of_leaves`, `tyzLemma29Mod2_of_tunnellR`, `tyzLemma29PrintedNe3_of_R`.
  - leaves: `TunnellOddL1` (new, published: Tunnell 1983), `TYZLemma29PrintedNe3R` (real-ℓ form of the open
    leaf `TYZLemma29PrintedNe3`, which it implies).
  - `tyzThm11Integral_of_leaves hL3s hJP hfx hL29R hTun : TYZThm11Integral`.
  - `tyzLemma29Mod2_of_tunnell(R) hL3s hJP hfx hL29(R) hP23 hTun : TYZLemma29Mod2` (no `TYZThm21At31`).
  - `lcalSq_one_of_tunnell`, `lcalSq_three_of_tunnell` (A(1)=B(1)=2, A(3)=B(3)=4 computed in Lean).
* `lake build +Main +Discharges +Contrib.OneProof.TYZThm11Integral`: success, 13699 jobs, 11m55s (TailK, TailS and
  downstream rebuilt over the copied tree). VERIFIED.
* `MainEdit.lean` (`h11reduce_frozenTarget`: frozenTarget minus h11, hL29, hT21, plus hL29R, hTun): compiles,
  standard axioms (MainEdit-output.txt). VERIFIED.
* `#discharges` (DischargesH11-output.txt): `DISCHARGES [h11] by tyzThm11Integral_of_leaves` (still assumes
  LegendreThreeSquares, JonesPallX2Y2Z16, TYZTestVectorExists, TYZLemma29PrintedNe3R, TunnellOddL1) and
  `DISCHARGES [hL29] by tyzLemma29PrintedNe3_of_R` (still assumes TYZLemma29PrintedNe3R); standard axioms.
  VERIFIED. Net: frozenTarget TYZ arguments 9 -> 8 (h11, hL29, hT21 out; hL29R, hTun in), all LEAF.
