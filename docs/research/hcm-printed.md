# hcm-printed: `hCM` (`T5Glue.ShimuraMainCM`) proved from printed leaves

Task hcm-printed, 2026-11-15. Scratch: `scratch/hcm-printed/` (log `log.md`). Lean:
`ZInQKernel/Contrib/OneProof/ShimuraMainCMPrinted.lean`, which imports `ZInQKernel.Contrib.OneProof.QMRecPrinted`.
It depends on the merge of qmrec-printed (`wip/qmrec-printed` a05c57ef, merged into this branch), which brings
`ShimuraSplit2.lean` and `QMRecPrinted.lean`.

## 1. Result

```lean
theorem HcmPrinted.shimuraMainCM_of_printed (hM : MainTheoremCMArith) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM

theorem HcmPrinted.shimuraMainCM_of_textbook (hM : MainTheoremCMArith) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    T5Glue.ShimuraMainCM
```

Both compile with only the standard axioms (VERIFIED: `#print axioms`, section 4). `hCM` itself is unchanged.
`shimuraMainCM_of_textbook` uses the bundle's current textbook fields `uniformizationLeafAll` and `gagaMorphism`, which
give `HomLatticeCorr` through the chain's `AvSplit.Final.h69`. The dictionary step that re-rated `hCM` to GLUE is now
proved in Lean: the adelic main theorem of CM gives the Weierstrass-coordinate form for every lattice of every order.

**A finding about the source leaf (VERIFIED, read in the Lean source).** qmrec-printed's `QMRecPrinted.MainTheoremCM` is
`∃ ε : ℤˣ, …`: the lattice of `A^σ` is `N(s)^{-ε}𝔞` for some unspecified sign. `ShimuraMainCM` fixes the direction: the
lattice is `s⁻¹𝔞 = K ∩ s_f⁻¹𝔞̂` for Tau Ceti's arithmetic Artin map. The existential form cannot decide that direction.
Ruling out `ε = −1` would need arithmetic input: a class group with an element of order at least 3 and the injectivity
of `j`. The reduction therefore uses the `ε = 1` instance, `MainTheoremCMArith := MainTheoremCMSign 1`:

* `MainTheoremCMSign ε` is the body of `MainTheoremCM`, copied verbatim; `mainTheoremCM_iff : MainTheoremCM ↔ ∃ ε,
  MainTheoremCMSign ε` is proved by `Iff.rfl`, which checks the copy;
* `mainTheoremCM_of_arith : MainTheoremCMArith → MainTheoremCM`.

This is the printed statement in Shimura's normalization (section 3). `ShimuraMainCM` already assumes that
normalization (its docstring: `E^{Frob_𝔭} ≅ ℂ/𝔭⁻¹𝔞`), so the reduction adds no new sign risk.

## 2. The proof

`T5Glue.ShimuraMainCM` is stated in coordinates: for `m`, `e`, `σ = [s, K]` (`ArtinCond`), a lattice `𝔞 ⊂ K`, and
period pairs `P` (lattice `κ𝔞`) and `P'` (lattice `κ(s⁻¹𝔞)`), there is `μ` with `σ(g₂(P)) = μ⁴g₂(P')`,
`σ(g₃(P)) = μ⁶g₃(P')`, and `σ(℘_P(κu)) = μ²℘_{P'}(κv)`, `σ(℘'_P(κu)) = μ³℘'_{P'}(κv)` for `u ∉ 𝔞` and
`s_f v − u ∈ 𝔞̂`. All of the glue below is proved in the file.

| step | Lean | content |
| --- | --- | --- |
| E_Λ as an abelian variety | leaf `WeierstrassAbVar` | `A/ℂ` of dimension 1, `θ : ℂ¹/Λ ≅ A(ℂ)`, coordinates `x, y` on `U = A ∖ O` with `x∘θ = ℘`, `y∘θ = ℘'` |
| specialization of the main theorem | `artinCondC_of_artinCond`, `isCMField_QNeg`, `type_inj`, `reflex_range`, `model`, `reflexNorm_rhoQ`, `cmLat_eq`, `isOfType_of_corr` | `E = Er = K`, `g = n = 1`, `Φ = (κ)`, `ρ` = scalars, reflex norm `= (𝔸_{K,f} ≅ 𝔸_f ⊗ K)`; `ArtinCond` (subfields of `Kˢ` through `ιC ∘ e`) gives `ArtinCondC` (every abelian `L/K` with a `K`-embedding into `ℂ`), via Tau Ceti's `of_ideleClassArtinMap`, `globalArtinMap_eq_of_mk_eq_absoluteArtinMap` and `exists_iota`; the CM endomorphisms (`IsOfType`) come from `HomLatticeCorr` (realization) |
| adelic dictionary | `adelic` | for `𝔞 = ℤb₁ + ℤb₂`: `w ∈ 𝔞 ⊗ ℤ̂ ↔ e(w) ∈ closure(𝔞) ⊂ 𝔸_{K,f}`, from compactness of `ℤ̂` (Tau Ceti `isCompact_integralAdeles`), strong approximation (`closure_range_algebraMap`) and continuity of `𝔸_f → 𝔸_{K,f}`; hence `latAct t 𝔞 = sInvLat m s 𝔞` and the torsion hypothesis transfers |
| `A^σ` | `isPullback_bc`, `one_left_bc`, `dd`, `eval_conj` | `A^σ = bcC A σ` (Mathlib's `Over.pullback`), de-conjugation of points `A^σ(ℂ) ≅ A(ℂ)` as a group isomorphism, and `x^σ(p^σ) = σ(x(p))` for regular functions |
| σ on points | `mapPt` | `W(ℂ) → W^σ(ℂ)`, a group homomorphism (Mathlib's `map_addX`, `map_addY`, `map_negY`) |
| analysis | `lin` | a homomorphism `ψ : ℂ/Λ' → ℂ/Λ''` (injective, surjective) whose Weierstrass coordinates `(℘''∘ψ, ℘''′∘ψ)` are holomorphic off `Λ'` is `z ↦ αz`: local inverse of `℘''` at a point with `℘''′ ≠ 0` (Mathlib's inverse function theorem), sign of `℘'` by continuity, local increments constant by discreteness of `Λ''`, derivative constant, then additivity |
| coordinates on `A^σ` | `core` | `F = x^σ∘θ'` and `G = y^σ∘θ'` are holomorphic off `Λ'` (`IsUniformization` of `θ'`) and equal `σ∘℘_P∘w`, `σ∘℘'_P∘w` (`w = θ⁻¹∘dd∘θ'`); `Λ''` with `g₂ = σg₂(P)`, `g₃ = σg₃(P)` from `WeierstrassUniformization`; `ψ₀ = wPt_{Λ''}⁻¹∘σ∘wPt_P∘w` is a homomorphism by `WeierstrassParam` and `mapPt`; `lin` gives `α` with `Λ'' = αΛ'`, and t5-glue's `IsScale` lemmas give `μ = α⁻¹` |
| assembly | `shimuraMainCM_of_printed` | the main theorem's `θ'` uniformizes `A^σ` by `κ(s⁻¹𝔞) = Λ_{P'}`, so `core` gives `μ` and the coordinate identities at `(κu, κv)` |

One point of the target needed care, and it holds. `ShimuraMainCM` asks for one `μ` that works for every pair
`(u, v)`. `core` produces a single `ν` from the global map `θ'`, so the order `∃ μ, ∀ u v` is met. The sign of `℘'` is
not chosen pointwise.

## 3. The leaves, rated

| leaf | statement | source | rating |
| --- | --- | --- | --- |
| `HcmPrinted.MainTheoremCMArith` | `QMRecPrinted.MainTheoremCM` at `ε = 1` (verbatim body) | Shimura 1971 Thm 5.15 / Thm 5.4 (`ξ(u)^σ = ξ'(N(s)⁻¹u)`, `σ = [s, K]`); Shimura 1998 Thm 18.6; Lang, *Elliptic functions*, Ch. 10 Thm 3; Silverman, *Advanced topics*, II.8.2 and II.4.3 (`F(𝔞)j(E) = j(𝔞 * E)`, `𝔞 * E_Λ = E_{𝔞⁻¹Λ}`); numbers UNVERIFIED | **printed form**, with the sign flag below. It is the printed theorem in the arithmetic normalization, not stronger: qmrec-printed's weakenings are kept (no uniqueness of `θ'`, no type and polarization clauses). Flag: *pending reading of the normalization of `[s, K]`* (Shimura §5.2 against Tau Ceti's arithmetic Artin map). If Shimura's symbol were the geometric one, `ε = −1` would be the print, and `ShimuraMainCM` itself would be false as stated. |
| `HcmPrinted.WeierstrassUniformization` | `∀ a b, a³ − 27b² ≠ 0 → ∃ L, g₂(L) = a ∧ g₃(L) = b` | Silverman, AEC, Thm VI.5.1; Serre, *Course*, VII §3 (UNVERIFIED) | **printed form** (gz-weil's statement, verbatim) |
| `HcmPrinted.WeierstrassParam` | for every `PeriodPair`: `Δ ≠ 0`, and `z ↦ (℘(z), ℘'(z)/2)` is a surjective homomorphism `ℂ → E_Λ(ℂ)` with kernel `Λ` (Mathlib's `WeierstrassCurve` `y² = x³ − (g₂/4)x − g₃/4` and its group law) | Silverman, AEC, Prop. VI.3.6 (a), (b); Lang, *Elliptic functions*, Ch. 1 §3 (UNVERIFIED) | **printed form**, weaker than the print (the analytic-isomorphism clause is dropped). The scaling `y ↦ 2y` to Mathlib's normal form is a linear change of coordinates that preserves the chord–tangent law. |
| `HcmPrinted.WeierstrassAbVar` | for every `PeriodPair` there are `A : PkgI3.AbVar ℂ` of dimension 1, `θ` with `IsUniformization (lat1 P) θ`, and `x, y ∈ Γ(U)` with `θ(z) ∈ U ↔ z ∉ Λ`, `x(θ z) = ℘(z)`, `y(θ z) = ℘'(z)` | Silverman, AEC, Prop. VI.3.6 (b) (`[℘, ℘', 1] : ℂ/Λ ≅ E_Λ(ℂ)`, an analytic isomorphism of Lie groups) with III.3.1 / III.3.6 (`E_Λ` is a group variety; `U = E ∖ O` affine with coordinates `x, y`) (UNVERIFIED) | **printed form, flagged**: this is VI.3.6 (b) with `E_Λ` written in the project's abelian-variety layer. `A` is existential because Mathlib v4.35.0 cannot construct a projective group scheme (`PkgI3.AbVar.zero`'s docstring). Holomorphy of regular functions along `θ` is the "analytic" half of VI.3.6 (b). Suggested flag: *pending reading: whether the AbVar presentation of `E_Λ` with coordinates is accepted as printed form*. |
| `ZInQ.HomUnify.HomLatticeCorr` | (existing leaf) | Birkenhake–Lange 1.2.1, GAGA | already in the bundles; the `_of_textbook` form uses the current fields `uniformizationLeafAll`, `gagaMorphism` instead |

GLUE count. `hCM` is being re-rated GLUE (a consequence). Folding replaces it with the leaves above, so the strict GLUE
count drops by one.

* If qmrec-printed's `mainTheoremCM` is folded first, `MainTheoremCMArith` is a new leaf that implies it.
* If gz-weil's `WeierstrassUniformization` is folded, the two statements are identical up to namespace.

## 4. Checks

* `scratch/hcm-printed/chk.sh` compiles each piece against qmrec-printed's build tree (read only). Pieces: `Lin.lean`
  (`lin`, standard axioms) and `Core.lean` (the full development, about 60–150 s; `#print axioms
  HcmPrinted.shimuraMainCM_of_printed`: `[propext, Classical.choice, Quot.sound]`). VERIFIED.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraMainCMPrinted`
  and `#discharges`: see section 5.

## 5. Build, `#discharges`, autofold

The checks ran on a copy of the r16-used build tree (main plus one unrelated Contrib file) in this worktree. All of
the following are VERIFIED.

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ShimuraMainCMPrinted`:
  "Build completed successfully (12997 jobs)" (`scratch/hcm-printed/build1.txt`). After `shimuraMainCM_of_textbook`
  was added, rebuilding the file gave 12230 jobs, successful (`build2.txt`).
* `#discharges` (`scratch/hcm-printed/Discharges.lean`, output `discharges_output.txt`):

```
DISCHARGES [hCM] by HcmPrinted.shimuraMainCM_of_printed
  still assumes: [HcmPrinted.MainTheoremCMArith,
 HcmPrinted.WeierstrassUniformization,
 HcmPrinted.WeierstrassParam,
 HcmPrinted.WeierstrassAbVar,
 ZInQ.HomUnify.HomLatticeCorr]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hCM] by HcmPrinted.shimuraMainCM_of_textbook
  still assumes: [HcmPrinted.MainTheoremCMArith,
 HcmPrinted.WeierstrassUniformization,
 HcmPrinted.WeierstrassParam,
 HcmPrinted.WeierstrassAbVar,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 2141 theorems checked, 9 discharge one
```

  The other seven discharges come from the merged qmrec-printed and shimura-split2 files.
* **Autofold.** The spec is `scratch/hcm-printed/autofold.json`: field `hCM`, proof `shimuraMainCM_of_textbook` with the
  four new leaves and `{t}.uniformizationLeafAll`, `{t}.gagaMorphism`; each leaf has its kind and flag. `autofold.py
  --dry-run` refuses it: "not a field of the current bundles: ['hCM']". `hCM` is a direct argument of `frozenTarget`,
  not a bundle field, and the script folds only bundle fields. The fold is therefore manual, as leaf-fold25 did when it
  replaced `hS` by `hCM` and `hX`. `scratch/hcm-printed/FoldCheck.lean` proves `frozenTarget_hcmPrinted`, which is
  `frozenTarget` with `hCM` replaced by the four leaves. It compiles with axioms `[propext, Classical.choice,
  Quot.sound]` (`foldcheck_output.txt`).
* Rows for `docs/research/locators.md` and `kinds.tsv`, for the integrator; this task does not edit shared notes. They
  are the four leaf entries of `autofold.json`: kind `published`, with the flags of section 3.

## 6. What remains

* A reading of Shimura 1971 §5.2 for the normalization of `[s, K]`. The same reading clears `ShimuraMainCM`'s own
  sign claim.
* A reviewer's ruling on `WeierstrassAbVar` as printed form. It is the only new leaf stated over the project's
  abelian-variety layer and not over Mathlib's elliptic functions alone.
* Order of integration: this branch contains qmrec-printed (which contains shimura-split2), and the Contrib file
  imports `QMRecPrinted`, so those two files must reach main first or together.
