# hcm-g1: `hCM` (`T5Glue.ShimuraMainCM`) from a g = 1 leaf

Task hcm-g1, 2026-11-15. Scratch: `scratch/hcm-g1/` (log `log.md`). Lean:
`ZInQKernel/Contrib/OneProof/ShimuraMainCMG1.lean`, namespace `HcmG1`. It imports only
`ZInQKernel.Contrib.OneProof.RingClassLattice`, the module that defines the statement, so it does not need
qmrec-printed or hcm-printed to be merged first.

## 1. Result

```lean
theorem HcmG1.shimuraMainCM_of_g1 (hS : ShimuraThm54) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) : T5Glue.ShimuraMainCM
```

The theorem compiles with only the standard axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED: `#discharges`,
section 4). `hCM` itself is unchanged. All glue is proved. The final theorem no longer uses any of the following:
`MainTheoremCMArith`, `WeierstrassAbVar`, `HomLatticeCorr`, the abelian-variety layer (`PkgI3.AbVar`, `bcC`, `dd`,
`eval_conj`), the adelic dictionary `adelic`, or `artinCondC_of_artinCond`. The new leaf is stated directly in
`T5Glue`'s adelic terms (`ArtinCond`, `sInvLat`, `latHat`, `finPart`), so no translation step is needed.
`WeierstrassParam` stays because the glue needs the parametrization `z ↦ (℘, ℘'/2)` of `E_P` as a group homomorphism.

**Normalization (VERIFIED by computation; section 3).** The direction that `ShimuraMainCM` and the new leaf fix is
`σ = [s, K]` with Tau Ceti's arithmetic Artin map, and `E^σ ≅ ℂ/s⁻¹𝔞`. It is correct at `K = ℚ(√−23)`, `𝔭 | 2`. There,
the arithmetic Frobenius at `𝔭` sends `j(𝒪_K)` to `j(𝔭⁻¹)`, and not to `j(𝔭)`.

## 2. The leaf and the proof

**`HcmG1.IsAnalyticIso L W ξ`**, for `W : WeierstrassCurve ℂ` and `ξ : ℂ →+ W.toAffine.Point`, holds when:

* `ξ` is surjective;
* `ξ z = 0 ↔ z ∈ L`;
* there are `X Y : ℂ → ℂ`, holomorphic on `ℂ ∖ L`, with `ξ z = (X z, Y z)` for `z ∉ L`.

Here `ξ` is a group homomorphism for Mathlib's group law on the points of `W`.

**LEAF `HcmG1.ShimuraThm54`.** Let:

* `m` be squarefree and `K = ℚ(√−m)`, embedded in `ℂ` by `κ`;
* `e : Kˢ → ℚ̄` be normalized;
* `σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` satisfy `T5Glue.ArtinCond m e σ s`;
* `𝔞 ⊂ K` be a lattice, meaning `κ(𝔞)` is the lattice of some `PeriodPair`, so `𝔞` may belong to any order;
* `W : WeierstrassCurve ℂ` satisfy `[W.IsElliptic]`;
* `ξ` satisfy `IsAnalyticIso (κ''𝔞) W ξ`.

Then there is `ξ' : ℂ →+ (W.map σ).toAffine.Point` with `IsAnalyticIso (κ''(sInvLat m s 𝔞)) (W.map σ) ξ'` and
`mapPt W σ (ξ (κ u)) = ξ' (κ v)` whenever `s_f v − u ∈ latHat m 𝔞`.

In Shimura's notation, `ξ(u)^σ = ξ'(s⁻¹u)` for `u ∈ K/𝔞`. The element `v` represents `s⁻¹u ∈ K/s⁻¹𝔞` exactly when
`v_p − s_p⁻¹u_p ∈ s_p⁻¹𝔞_p` for all `p`, and that is the condition `s_f v − u ∈ 𝔞̂`.

| step | Lean | content |
| --- | --- | --- |
| `E_P` and `ξ` | `wc`, `wPt`, `wHom`, `delta_wc` | `E_P = wc g₂ g₃` (`y² = x³ − (g₂/4)x − g₃/4`); `Δ(wc a b) = a³ − 27b²`, so `IsElliptic` follows from `WeierstrassParam`; `ξ = wHom P` is `z ↦ (℘_P z, ℘'_P z / 2)`, and its coordinates are holomorphic by Mathlib's `differentiableOn_weierstrassP` and `differentiableOn_derivWeierstrassP` |
| the leaf | `ShimuraThm54` | gives `ξ'` on `ℂ/κ(s⁻¹𝔞) = ℂ/Λ_{P'}` |
| `Λ''` | `WeierstrassUniformization`, `map_wc` | `Λ''` with `g₂ = σg₂(P)` and `g₃ = σg₃(P)`, so that `E_P^σ = wc g₂(Λ'') g₃(Λ'')` |
| `ψ₀` | `WeierstrassParam` for `Λ''` | `ψ₀(z)` is a preimage of `ξ'(z)` under `wPt_{Λ''}`; it induces a group isomorphism `ℂ/Λ_{P'} → ℂ/Λ''` whose Weierstrass coordinates are `(X, 2Y)`, which are holomorphic |
| analysis | `lin` (copied from hcm-printed) | `ψ₀(z) ≡ αz (mod Λ'')` |
| scaling | `T5Glue.IsScale` lemmas | `Λ'' = αΛ_{P'}`; `μ = α⁻¹` gives `IsConjModel σ P P' μ` and the identities for `℘` and `℘'` at `(κu, κv)` |

The order `∃ μ, ∀ u v` holds because `μ` comes from the single global map `ξ'`. `κv ∉ Λ_{P'}` follows from
`ξ'(κv) = σ(ξ(κu)) ≠ 0`.

### Is `IsAnalyticIso` the printed notion?

* **As a hypothesis.** `IsAnalyticIso` implies that `ξ` induces a biholomorphism `ℂ/L → E(ℂ)` taking `0` to `O`. The
  induced map is holomorphic off `L`. It is holomorphic at `L` by translation: `ξ(z) = ξ(z + a) − ξ(a)`, and the group
  law is algebraic. A bijective holomorphic map between compact Riemann surfaces is biholomorphic. Requiring `ξ` to
  be a homomorphism only narrows the hypothesis.
* **As a conclusion.** The print's `ξ'` is biholomorphic, and `ξ'(0) = ξ(0)^σ = O`. A holomorphic map of complex tori
  that fixes `0` is a homomorphism. So `ξ'` is a surjective homomorphism with kernel `s⁻¹𝔞` and holomorphic
  coordinates off the lattice.

These are STANDARD facts (Riemann surfaces; Silverman, AEC, VI.4.1 and VI.3.6; numbers UNVERIFIED). The leaf is
therefore a consequence of the print, with uniqueness of `ξ'` dropped.

## 3. The leaves, rated

| leaf | source | rating |
| --- | --- | --- |
| `HcmG1.ShimuraThm54` | Shimura 1971, *Introduction to the arithmetic theory of automorphic functions*, Thm 5.4; Lang, *Elliptic functions*, Ch. 10 §2 Thm 3; Silverman, *Advanced topics*, II.8.2 (`𝒪_K` only). Locators and wording are from memory (UNVERIFIED). | **printed form**, flag *unread* (locator). Consequence of the print: uniqueness dropped; `IsAnalyticIso` is equivalent to the print's analytic isomorphism (section 2); the only objects are Mathlib's (`WeierstrassCurve ℂ`, `IsElliptic`, `Point`, `WeierstrassCurve.map`, finite adeles) plus Tau Ceti's Artin map through `ArtinCond`. g = 1 with CM by `K`, so there is no polarization question. The theorem is stated for every lattice of `K`, so there is no order question. This removes the objections the statement review raised against Shimura 1998 Thm 18.6. |
| `HcmG1.WeierstrassUniformization` | Silverman, AEC, Thm VI.5.1; Serre, *Course*, VII §3 (UNVERIFIED) | **printed form**. It is gz-weil's statement, verbatim, and the same as `HcmPrinted.WeierstrassUniformization`. |
| `HcmG1.WeierstrassParam` | Silverman, AEC, Prop. VI.3.6 (a), (b) (UNVERIFIED) | **printed form**, weaker than the print because the analytic clause is dropped. It is the same as `HcmPrinted.WeierstrassParam`, verbatim. |

**The `[s, K]` normalization.** I have not read Shimura 1971 §5.2, because there is no network. The direction is
settled by the following evidence.

1. **Tau Ceti (VERIFIED, read in the source).** `globalArtinMap_isArithFrobAt` (`LocalArtin/Frobenius.lean:154`)
   shows that Tau Ceti's Artin map sends the prime idele class at `v` to an arithmetic Frobenius.
2. **The computation (VERIFIED, `scratch/hcm-g1/frob_check.py`, output in `frob_check_output.txt`).** The setting is
   `K = ℚ(√−23)` (class number 3), `H = K(j(𝒪_K))`, and `𝔭₀ = (2, (1+√−23)/2)`, with the embedding fixed by
   `√−23 ↦ i√23`.
   * PARI's `idealfrobenius` is arithmetic: the script checks that `Frob(b) ≡ b² mod 𝔓` for each integral basis
     element `b`.
   * `Frob_{𝔭₀}(j(𝒪_K))` agrees with `j(𝔭₀⁻¹) = j((−1+i√23)/4)` to about 1e−61.
   * It differs from `j(𝔭₀) = j((1+i√23)/4)` by 3528.
3. **What the computation decides.** Take `s` with `s_𝔭₀ = π` and all other components `1`. Then `s⁻¹𝒪_K = 𝔭₀⁻¹`.
   The j-part of the leaf, and of `ShimuraMainCM`, says `j(𝒪_K)^{Frob} = j(𝔭₀⁻¹)`, and this is what the computation
   finds. Suppose Shimura's `[s, K]` were the geometric symbol. Then his true theorem, in the form recalled above,
   would assert `j(𝒪_K)^{Frob_𝔭₀} = j(𝔭₀)`, which the computation refutes. So either Shimura's symbol is arithmetic
   (then the leaf is the print), or the printed wording differs from my recollection.

A reading of §5.2 can only change the textual match. It cannot make the leaf false.

**GLUE count.** `hCM` is being re-rated GLUE. The fold replaces it with one new printed leaf, `ShimuraThm54`, and two
textbook leaves (`WeierstrassUniformization`, `WeierstrassParam`). Compared with the re-rated count, the strict GLUE
count drops by one. If hcm-printed's or gz-weil's fold lands first, the two textbook leaves are already present up to
namespace; the integrator can alias them, since the bodies are byte-identical.

## 4. Checks (all VERIFIED)

* `scratch/hcm-g1/G1.lean` (the development) compiles in about 7 s with `scratch/hcm-g1/chk.sh`, against
  hcm-printed's build tree, read only. `#print axioms`: standard.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraMainCMG1`
  reported "Build completed successfully (12995 jobs)" (`scratch/hcm-g1/build1.txt`, tail). It ran on a copy of
  hcm-printed's build tree, which has the same base commit.
* `#discharges` (`scratch/hcm-g1/Discharges.lean`; output in `discharges_output.txt`):

```
DISCHARGES [hCM] by HcmG1.shimuraMainCM_of_g1
  still assumes: [HcmG1.ShimuraThm54, HcmG1.WeierstrassUniformization, HcmG1.WeierstrassParam]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1859 theorems checked, 8 discharge one
```

* **Autofold.** The spec is `scratch/hcm-g1/autofold.json`: field `hCM`, proof `shimuraMainCM_of_g1` with the three
  leaves, each with its kind and flag. `autofold.py --dry-run` refuses it with "not a field of the current bundles:
  ['hCM']", because `hCM` is a direct argument of `frozenTarget`. The fold is therefore manual.
  `scratch/hcm-g1/FoldCheck.lean` proves `frozenTarget_hcmG1`, which is `frozenTarget` with `hCM` replaced by the
  three leaves. Axioms: standard (`foldcheck_output.txt`).
* Rows for `kinds.tsv` and `locators.md`, for the integrator, are the three leaf entries of `autofold.json`. This task
  does not edit shared notes.

## 5. What remains

* A reading of Shimura 1971 Thm 5.4 and §5.2, to clear the locator and the textual match of the `[s, K]`
  normalization. Section 3 shows the direction is right.
* Integration: the manual fold of `hCM` per `FoldCheck.lean`. hcm-printed's `ShimuraMainCMPrinted.lean` is
  superseded for the fold. Its `MainTheoremCMArith` and `WeierstrassAbVar` are no longer needed.
