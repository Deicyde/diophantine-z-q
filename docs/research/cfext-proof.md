# cfext-proof: `ConstantFieldExtensionUnramifiedFinite` proved outright

Task cfext-proof, 2026-11-17. Base `wip/leaf-fold33b` d879bb73. Scratch `scratch/cfext-proof/` (results log
`log.md`). Marks: **VERIFIED** (compiled or read in a file), **STANDARD** (published, exact reference),
**UNVERIFIED** (theorem number from memory).

## 1. Result

`JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite` (ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean:48,
Stichtenoth 3.6.3(a) for a finite constant field extension, a research-bundle field rated published / pending
review, strict GLUE) is **proved from Mathlib alone, with no new leaf and no change of statement**:

```lean
theorem CFExtProof.constantFieldExtensionUnramifiedFinite_proof :
    JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite
```

* scratch copy: `scratch/cfext-proof/CFExt.lean` (`import Mathlib`, the definition copied verbatim, the proof,
  `#print axioms` = [propext, Classical.choice, Quot.sound]) — VERIFIED (`lake env lean`, 7.7 s).
* contributor-kit file: `ZInQKernel/Contrib/OneProof/ConstantFieldExtensionUnramifiedFinite.lean` (new file;
  imports `JavanpeykarRebase` and seven targeted Mathlib modules, not all of Mathlib); builds, and
  `#discharges` reports it discharges the field with `still assumes: []` — VERIFIED (§3).
* fold spec: `scratch/cfext-proof/autofold.json` (field `constantFieldExtensionUnramifiedFinite :=
  _root_.CFExtProof.constantFieldExtensionUnramifiedFinite_proof`). Dry run: strict **16/18 on 34 → 16/17 on
  33** (strictest 16/18 → 16/17): one field and one strict GLUE removed, no new leaf — VERIFIED (§3).

The statement is true as written (in particular the uniformizer clause is fine), so no corrected statement or
reroute is needed.

## 2. The proof

Notation: `O = w ∩ F` (the valuation subring `w.comap ι`), `π` the given generator of `m_O`, `A = O ⊗_K L`,
`φ : A → FL`, `r ⊗ l ↦ ι r · l` (lands in `w` since `O, L ⊆ w`), `p = φ⁻¹(m_w)` (a prime of `A`).

1. **Unramified step** (`unram_step`). `L/K` is separable (characteristic 0), so `Algebra.FormallyUnramified K L`
   (`FormallyUnramified.of_isSeparable`), hence `FormallyUnramified O A` (base change instance) and
   `FormallyUnramified O A_p` (localization, `comp`); `A_p` is essentially of finite type over `O`, and
   `O → A_p` is local because `p ∩ O = m_O`. Mathlib's `Algebra.FormallyUnramified.map_maximalIdeal`
   (Stacks 00UW(1)) gives `m_O A_p = m_{A_p}`, and `m_O = (π)`. Unwinding the localization: for every `a ∈ p`
   there are `s ∉ p` and `b ∈ A` with `s a = π b`. VERIFIED.
2. **Decomposition.** Every `x ∈ FL` is `ι c · φ a` with `c ∈ F`, `a ∈ A`: by surjectivity of
   `F ⊗_K L → FL` and induction on tensors, factoring out the coefficient of least valuation. VERIFIED.
3. **Archimedean step** (`isAlgebraic_adjoin_of_transcendental`, `exists_pow_eq_mul`). If `π ≠ 0` it is
   transcendental over `K` (an algebraic `π` lies in `K` by the full-constant-field clause, hence is a unit of
   `O`). `{t}` is a transcendence basis (`F` finite over `K(t)`), so `trdeg_K F = 1` and `{π}` is a transcendence
   basis too (`isTranscendenceBasis_of_trdeg_le_of_finite`); every `d ∈ O \ 0` is algebraic over `K[π]`. Taking
   an algebraic relation with nonzero constant coefficient `P(π)` (`P ∈ K[X]`), `P(π) ∈ d O` and
   `P(π) = π^m · (unit of O)`, so `π^m ∈ d O`. VERIFIED.
4. **Iteration.** Keep `ι c · φ a = x · φ s` with `s ∉ p` (so `φ s` is a unit of `w`). If `c ∈ m_O`, then
   `c = π y₀` and `x = ι π · (ι y₀ φ a / φ s)` with the bracket in `w`. Otherwise `c⁻¹ ∈ O`, so
   `φ a = ι c⁻¹ x φ s ∈ m_w`, i.e. `a ∈ p`; step 1 gives `s' a = π b`, and `(c, a, s) ↦ (c π, b, s s')`
   keeps the invariant. By step 3, `c π^k ∈ m_O` for some `k` (for `π = 0`, `k = 1`), so after at most `k`
   steps the first case applies. VERIFIED.

Hypotheses actually used: `CharZero K` only through separability of `L/K`; the function-field clause only for
`trdeg_K F = 1`; the full-constant-field clause only for "π transcendental"; of the bijectivity only
surjectivity. (Injectivity, i.e. `F ⊗_K L` a field, is not needed.)

## 3. Build, `#discharges`, dry-run fold

Prebuilt tree copied from `~/dzq-check2` (at d879bb73, `ZInQKernel/OneProof/Main.lean` byte-identical).

| check | outcome |
| --- | --- |
| `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ConstantFieldExtensionUnramifiedFinite` | success, 14274 jobs, the new module 38 s; only the "designed for the module system" import warnings — VERIFIED |
| `#discharges` (`scratch/cfext-proof/Discharges.lean`, output `discharges-output.txt`) | `DISCHARGES [OpenResearchLeaves38.constantFieldExtensionUnramifiedFinite] by CFExtProof.constantFieldExtensionUnramifiedFinite_proof`, `still assumes: []`, axioms [propext, Classical.choice, Quot.sound] — VERIFIED |
| `autofold.py scratch/cfext-proof/autofold.json --dry-run` (`FoldDryRun.lean.txt`) | strict count 16/18 on 34 → 16/17 on 33, strictest 16/18 → 16/17; generates `OpenResearchLeaves39` (38 minus the field) and `sixContactMin_of_open56` — VERIFIED |
| dry-run module, line 1 stripped, `lake env lean` | compiles (6.5 s); `sixContactMin_of_open56` axioms standard — VERIFIED |

For the lead: fold with `python3 scripts/one_proof/autofold.py scratch/cfext-proof/autofold.json` (no
`--allow-rise` needed), then the usual post-fold checks. `kinds.tsv` loses the row
`research constantFieldExtensionUnramifiedFinite`. Since `full_of_finite` already derives javanpeykar-fix's
`ConstantFieldExtensionUnramifiedFull` from the finite case, Stichtenoth 3.6.3(a) in both forms is now a theorem.
