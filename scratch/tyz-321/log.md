# tyz-321 results log

Target: `CMBridge.Lemma321Five` (TYZ Lemma 3.21(1)), copied verbatim with all of
`scratch/cm-bridge/Bridge.lean` (§0–§15) into `scratch/tyz-321/L321.lean`; new work in §16.

## 2026-11-13 22:40 start
- Merged origin/wip/cm-bridge: already contained in base (no-op).
- Build: `lake build ZInQKernel.Contrib.TYZGenus.ShimuraFricke` started (no build artifacts in worktree).

## Numerics (wlat.py, exact arithmetic in K = Q(sqrt(-n)))
- For b = a ∩ O4, a = (m, sqrt(-n) - 1), m = (n+1)/2, Q = [16(n+1), -8, 1] (tau = (1+w)/(8m)):
  the word `WT` (tau'' = W(tau + 1/4) = -1/(32 tau + 8)) satisfies
  b·(<1,tau''>, <1/32,tau''>) = c·(<1,tau>, <1/32,tau>) with c = (-1 + ((n+3)/2) w)/(n+4),
  for all 10 tested n = 5, 13, 21, 29, 37, 53, 61, 69, 77, 85. VERIFIED (computed).

## 2026-11-13 23:20 compile 1 (VERIFIED, `lake env lean scratch/tyz-321/L321.lean`, 0 errors, no sorry)
- `T321.lemma321Five_of (hβ : BetaOneLiftExists) (hz : ZnOverH4) (hc : TYZThm36ConjFive)
   (hw : TYZThm36OneFive) (hk : KerFixesZnMod) (hg : BetaOnGenus5) : Lemma321Five` — the core glue
   (TYZ's proof of Lemma 3.21(1), for any lift σ, every e | n, e ≡ 5 (8)).
- `znOverH4_of : Shimura.ShimuraReciprocityModFn → ZnOverH4`.
- `tyzThm36ConjFive_of : CMAlgebraic → TYZThm36ConjFive` (z̄_n = −z_n + τ(1)), via
  `yC_add_quarter : yC (z + 1/4) = I * yC z` (eta), `xC_add_quarter : xC (τ + 1/4) = −xC τ` (theta form),
  `toC_iPt_of_quarter` (φ(τ+1/4) = [i]φ(τ)), `tyzForm_conj_tauH` (τ_{Q̄} = W T₄ W τ_Q), Fricke (tyz-cm).
- helper: `exists_acts4_of_fix` (an automorphism of Q̄ fixing K_d acts on H_{d,4} as an Artin symbol).

## 2026-11-14 00:0x compile 2 (VERIFIED, 0 errors, no sorry)
- `tyzThm36OneFive_of (hS : Shimura.ShimuraReciprocityPic) (hA : CMAlgebraic) (hneg : WNegatesI) :
   TYZThm36OneFive` — σ_w(z_n) = z_n + τ((1+i)/2) mod ℤτ(1), from Shimura reciprocity with
   𝔟 = 𝔞 ∩ O4 = ℤ⟨m, −4+4√−n⟩ (`idealMeetOrder_varpi`), Q'' = [32(n+4), 8(n+2), (n+1)/2] (`tyzFormW`),
   τ_{Q''} = W(τ_Q + 1/4) (`tyzFormW_tauH`), lattice identities `latKW`, `latNKW` (coefficients from
   wcoef.py), `heegnerPt_tyzFormW : f₀(P_{Q''}) = T − [i]f₀(P_n)`, orientation `normalized_cases`.
- New named glue `WNegatesI` (σ_w(i) = −i; genus character computation), still open.

## 2026-11-14 ~00:15 compile 3 (VERIFIED, 0 errors, no sorry)
- `artinPstarChi_odd` (port of cm-bridge GT-ART to odd n: n % 4 = 3 was only used to get `Odd n`).
- `p2_sq : 𝔭₂² = (2)`, `a_mul_p2 : 𝔞𝔭₂ = (√−n − 1)`, `absNorm_p2 : N𝔭₂ = 2`, `picToMax_picClass`,
  `chi_wClass : χ_q(π w) = (2/q)`, `prod_sign_two : Π_{q|n} (2/q) = −1` (χ₈), `prod_pstar : Π q* = n` (χ₄).
- `wNegatesI : WNegatesI` and `betaOnGenus5 : BetaOnGenus5` proved.
- `lemma321Five_of_shimuraModFn (hS : Shimura.ShimuraReciprocityModFn) (hβ : BetaOneLiftExists)
   (hk : KerFixesZnMod) : Lemma321Five`.
- Remaining inputs: `KerFixesZnMod` (Gal(H_{n,4}/H_n) moves z_n by ℤτ(1)) and `BetaOneLiftExists`.

## 2026-11-14 ~00:55 compile 4 (VERIFIED, 0 errors, no sorry)
- Kernel of Pic(O4) → Cl: `span_elt_mem`, `picClass_congr` (x ≡ a·y mod 4𝓞 ⇒ same class),
  `odd_of_mem` (u+v even ⇒ (x)+𝔣 ⊆ 𝔭₂ ≠ ⊤), `pic_one`, `pic_sigma`, `pic_w2` (𝔞² = ((ω−1)²/2), `a_sq`),
  `pic_omega`, `ker_cases : picToMax k = 1 → k ∈ {1, σ, w², σw²}`.
- `kerFixesZnMod (hs : TYZSigmaFixesZn) (hw : TYZThm36OneFive) (hz : ZnOverH4) : KerFixesZnMod`.
- **`lemma321Five_of_shimuraModFn_betaOneLift (hS : Shimura.ShimuraReciprocityModFn)
   (hβ : BetaOneLiftExists) : Lemma321Five`.** Only remaining input: `BetaOneLiftExists`.

## 2026-11-14 ~00:40 compile 5 (VERIFIED, 0 errors, no sorry; axioms [propext, Classical.choice, Quot.sound])
- §16a `T321B.betaOneLiftExists : ∃ σ : GalQ, IsBetaOneLift σ` proved:
  `oddPart_facts`, `betaOneSign_eq_if`, `legendre_eq_betaOneSign` (Jacobi reciprocity, p ≡ 1 mod 8,
  p ≡ −2 mod odd part ⇒ (D/p) = betaOneSign D), `exists_prime_beta` (Mathlib's Dirichlet
  `Nat.forall_exists_prime_gt_and_zmodEq`, a = 3M² − 2), absolute Frobenius (copied from
  ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean), `frob_sqrt` (Frobenius at p acts on √D by
  (D/p), Euler's criterion), compactness of Gal(Q̄/Q) (`IsCompact.nonempty_iInter_of_directed_...`).
- **`T321.lemma321Five_of_shimuraModFn' (hS : Shimura.ShimuraReciprocityModFn) : Lemma321Five`.**
- **`T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First`** (cm-bridge's headline without h5).
- Axiom audit: scratch/tyz-321/audit-out.txt.

## 2026-11-14 00:05 final check (VERIFIED)
- `diff` of L321.lean lines 1–3213 against scratch/cm-bridge/Bridge.lean lines 1–3213: identical
  (verbatim copy of Lemma321Five and its dependencies).
- `lake env lean scratch/tyz-321/L321.lean`: exit 0, 0 errors, 0 sorry, 11 `#print axioms` lines all
  `[propext, Classical.choice, Quot.sound]`.
- Dev files WTest.lean, G5Test.lean, Beta.lean removed (superseded by L321.lean).
