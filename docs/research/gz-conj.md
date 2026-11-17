# gz-conj: Gross's conjugation relation on the curves `C_d` is a Lean theorem (no new leaf)

Status: research note (task gz-conj, 2026-11-16), branch `wip/gz-conj`. The base is fork main 60a3fac7
(leaf-fold28b), merged with wip/gz-weil ad22e947. Lean: one new contributor file,
`ZInQKernel/Contrib/OneProof/GrossConjugationCd.lean` (namespace `ZInQ.GZConj`, about 830 lines). Nothing else
under `ZInQKernel/` was edited. Development files, checks and log: `scratch/gz-conj/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with
an exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Gross 1984 or of
Gross–Zagier 1986, so **every literature locator below is UNVERIFIED**.

---

## 0. Main result

```lean
-- ZInQKernel/Contrib/OneProof/GrossConjugationCd.lean
theorem ZInQ.GZConj.grossConjugationCd : ZInQ.GZHL3.GrossConjugationCd
```

The statement is unchanged: `ZInQ.GZHL3.GrossConjugationCd` is defined in
`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean`. The proof depends only on
`[propext, Classical.choice, Quot.sound]` (VERIFIED, `#print axioms` in `scratch/gz-conj/Main.lean`).
`lake build +ZInQKernel.Contrib.OneProof.GrossConjugationCd` succeeds (VERIFIED). The proof adds no new leaf and
needs no hypothesis. Its inputs are Mathlib, Tau Ceti (the Fricke sign and the functional equation of a
newform), and these already proved results:
* `ZInQ.Contrib.functionalEquation5`;
* `ZInQ.Contrib.heckeContinuation`;
* `GZStatements.level_eq_of_coeff_cd` (the level is `32 d²`);
* gz-heegner's analytic lemmas in `Heegner.lean`: `hasDerivAt_eichler`, `weierPt_smul`, the `weierPt_eq_*` lemmas
  and `gcd_eq_one_of_squarefree`;
* gz-weil's `weierstrassP_surjective` and the related lemmas in `WeilParam.lean`;
* gz-fh's `completedL_newform_sub`.

**Effect on `hL3`.** gz-weil split `hL3` on the route (`C_d`) into three Heegner-point leaves:
`HeegnerPointRationalCd`, `GrossZagierFormulaCd` and `GrossConjugationCd`. Two of them remain:

```lean
theorem ZInQ.GZConj.grossZagierHeegnerCd_of_twoLeaves (hHP : GZHL3.HeegnerPointRationalCd)
    (hGZ : GZHL3.GrossZagierFormulaCd) : GZStatements.GrossZagierHeegnerCd
theorem ZInQ.GZConj.grossZagierHeegnerCd_of_printed (hCM : T5Glue.ShimuraMainCM)
    (hX : GZHeegner.X0ModuliGaloisMero) (hGZ : GZHL3.GrossZagierFormulaCd) :
    GZStatements.GrossZagierHeegnerCd
```

`scratch/gz-conj/MainEdit.lean` proves `ZInQ.FrozenTarget` from `frozenTarget`'s hypotheses at 60a3fac7, with
`hL3` replaced. There are two forms:
* `frozenTarget_gzconj` replaces `hL3` by `HeegnerPointRationalCd` and `GrossZagierFormulaCd`;
* `frozenTarget_gzconj_printed` replaces it by `X0ModuliGaloisMero` and `GrossZagierFormulaCd` (`hCM` is already
  a hypothesis).

Whether these compiled is in §5.

**GLUE count (SPECULATIVE rating, as in the statement review).** The statement review rated
`GrossConjugationCd` a *consequence* (counted GLUE). It is now a theorem, so the group's count drops by one GLUE
leaf outside H. It adds nothing. That is the −1 the task asked for.

**A by-product for every curve.** The `ε = −1` half of `GrossConjugationAt` holds for every elliptic curve
`E/ℚ`, and exactly, not just up to torsion: `conj_clause` proves `σ y − y = 0` whenever the Fricke sign of `f`
is `+1`. The `ε = +1` half is not proved here (§4). It is not needed, because on `C_d` that clause is vacuous.

---

## 1. The statement (VERIFIED, read)

The source is `GrossZagierHeegner.lean` §2, `GrossConjugationAt E`. For every newform `f` (level `N`, trivial
character, `aₙ(f) = aₙ(E)`) and every Heegner datum (`D`, `β`, a set `S` of representatives of residue `β`), with
`L` the period lattice and `c ∈ ℚ^×` such that `c Λ_f ⊆ L`, take any quadratic field `K`, `δ² = D`, an embedding
`ι` with `ι δ = i√|D|`, a point `y ∈ E(K)` with `ι(y) = Σ_{Q ∈ S} weierPt(c φ_f(τ_Q))`, and `σ` with
`σ δ = −δ`. The conclusion has two clauses:
* if `rootNumber f = 1`, then `σ y + y` is torsion;
* if `rootNumber f = −1`, then `σ y − y` is torsion.

`GrossConjugationCd` is this statement for `E = C_d`, with `d ≡ 5 (mod 8)` squarefree. The statement is neither
false nor vacuous. Its hypotheses can be met: Heegner representatives, a period lattice with `c Λ_f ⊆ L`, and `y`
all exist, by `heegnerRepsExist`, `exists_isPeriodLattice_cd`, `shimuraCMParamCd_proved` and gz-heegner's
`HeegnerPointRationalCd`. The proof shows the second clause in the stronger form `σ y = y`.

---

## 2. The proof (all in Lean, VERIFIED compiled)

| § | Lean | content |
| --- | --- | --- |
| 1 | `lattice_eq_of_g` | **A lattice is determined by `g₂, g₃`** (any `PeriodPair`). Take `z₀ ∉ L` with `℘'_L(z₀) ≠ 0` (otherwise `℘_L` would be constant on the connected set `ℂ ∖ L`). Since `℘_{L'}` is surjective (gz-weil), and `℘` is even and `℘'` odd, there is `z₁` with `(℘_{L'}, ℘'_{L'})(z₁) = (℘_L, ℘'_L)(z₀)`. Then `Ψ(z) = ℘_{L'}(z + δ) − ℘_L(z)` satisfies `Ψ' = hΨ` near `z₀`, with `h` analytic, by `℘'² = 4℘³ − g₂℘ − g₃`; since `Ψ(z₀) = 0`, its order of vanishing is infinite. By the identity theorem `Ψ = 0` on `ℂ ∖ (L ∪ (L' − δ))`, which is connected because the removed set is countable. Comparing poles gives `L = L' − δ` and `δ ∈ L'`. |
| 2 | `conjPP`, `G_conjPP`, `conj_mem_iff_of_isPeriodLattice`, `weierstrassP_conj`, `map_conj_weierPt` | `G_n(L̄) = conj G_n(L)`. For `E/ℚ`, `g₂ = c₄/12` and `g₃ = c₆/216` are real, so `L̄ = L` by §1. Then `℘(z̄) = conj ℘(z)` and `℘'(z̄) = conj ℘'(z)` (reindex the lattice sums by `l ↦ l̄`), hence `conj(weierPt E L z) = weierPt E L z̄` on `E(ℂ)`. |
| 3 | `fricke_apply`, `eichler_fricke`, `conj_eichler`, `conj_eichler_psi` | `f(−1/(Nz)) = ε_N N z² f(z)`, from Tau Ceti's `normalizedFrickeOperatorCusp_eq_frickeSign_smul`, as in atkin-li's `newform_fricke_ne` but with the constant explicit. For `ε_N = 1`, the derivative of `φ_f(−1/(Nτ)) − φ_f(τ)` is `2πi(ε_N − 1) f(τ) = 0`, and at the fixed point `i/√N` the difference is `0`, so `φ_f ∘ W_N = φ_f`. The coefficients `aₙ(f) = aₙ(E) ∈ ℤ` are real, so `conj φ_f(τ) = φ_f(−τ̄) = φ_f(W_N(1/(Nτ̄))) = φ_f(1/(Nτ̄))`. |
| 4 | `starForm`, `star_tauH`, `psiH_psiH`, `psiH_smul`, `sum_star_eq` | For `Q = [A, B, C]`, set `Q* = [N C, B, A/N]`. It has the same discriminant and the same `B`, hence the same residue; it is primitive because `D` is squarefree; and `C > 0`. Its point is `τ_{Q*} = 1/(N τ̄_Q) =: ψ(τ_Q)`. The map `ψ` is an involution, and `ψ γ ψ ∈ Γ₀(N)` for `γ ∈ Γ₀(N)` (`[[a,b],[Nc₀,d]] ↦ [[d,c₀],[Nb,a]]`). So `Q ↦ Q*` is injective on `Γ₀(N)`-classes of residue `β`, hence a permutation of the representatives, and the sum of a `Γ₀(N)`-invariant function over `S` is unchanged. |
| 5 | `map_conj_heegnerC`, `iota_comp_sigma`, `conj_clause` | By §2, §3 and §4, `conj(Σ_{Q ∈ S} φ(τ_Q)) = Σ_{Q ∈ S} φ(τ_{Q*}) = Σ_{Q ∈ S} φ(τ_Q)`. Since `(1, δ)` is a `ℚ`-basis of `K` (`δ ∉ ℚ` because `δ² = D < 0`), we get `ι ∘ σ = conj ∘ ι`. Hence `ι(σ y − y) = conj(ι y) − ι y = 0`, and `σ y = y` because `map ι` is injective. |
| 6 | `rootNumber_cd` | `rootNumber f = −1` for every newform `f` of `C_d` with `d ≡ 5 (mod 8)`. The level is `N = 32 d²` (`level_eq_of_coeff_cd`). gz-fh's `completedL_newform_sub` gives Tau Ceti's `Λ_N(2 − s) = ε Λ_N(s)`, and the proved `functionalEquation5` gives `Λ(2 − s) = −Λ(s)`. If `ε ≠ −1`, then `Λ = 0` on the strip, so `L(f, s) = 0` there (the factors `N^{s/2}`, `(2π)^{−s}` and `Γ(s)` do not vanish), hence everywhere (identity theorem), hence `LSeries (aₙ) = 0` on `Re s > 2`. Mathlib's `LSeries_eventually_eq_zero_iff'` then gives `a₁ = 0`; this needs Tau Ceti's Hecke bound for a finite abscissa, and contradicts `a₁ = heckeCoeff d 1 = 1`. |
| 7 | `grossConjugationCd` | The clause `ε = +1` is vacuous by §6. For `ε = −1`, the Fricke sign is `+1` (`rootNumber = i² ε_N`), and §5 applies. |

The review's hints were used as follows:
* `ε = −1` on `C_d`: that is §6;
* `φ_f ∘ W_N = φ_f`, evaluated at `i/√N`: that is §3;
* conjugation and `W_N` each send residue `β` to `−β`. The proof uses only the composite `Q ↦ Q*`, which keeps
  `β`.

One change from the hints: conjugation commutes with `weierPt` through lattice uniqueness (§1, §2), not through
`paramQExpansion` and the identity theorem on `ℍ`. That way the poles of `x ∘ φ` in `ℍ` never come up.

---

## 3. Leaves

**No new leaf.** The only Prop discharged is `ZInQ.GZHL3.GrossConjugationCd`. Its print is Gross, *Heegner
points on X₀(N)* (1984), §5 (UNVERIFIED), restated in Gross–Zagier 1986, Ch. V §2 (UNVERIFIED). The statement
review rated it a consequence, because it is stated for the analytic Heegner sum and not for moduli Heegner
points. That rating no longer matters, since it is now a theorem.

The leaves of the `C_d` split of `hL3` that remain are unchanged, and are outside this task:
* `HeegnerPointRationalCd`: a composite, proved by gz-heegner from `hCM` and `X0ModuliGaloisMero`;
* `GrossZagierFormulaCd`: printed, with the constant forgotten; rated a consequence by the statement review.

---

## 4. What remains and what was not done

* **The general `GrossConjugationAt` (all `E/ℚ`), clause `ε = +1`: not proved.** For Fricke sign `−1`, §3 gives
  `φ_f(W_N τ) = −φ_f(τ) + 2φ_f(i/√N)`. So `conj y = −y + h·P₀`, where `P₀ = weierPt(2c φ_f(i/√N))` is the image
  of the cusp `0`. That `P₀` is torsion is Manin–Drinfeld (STANDARD; Drinfeld, Funct. Anal. Appl. 7 (1973),
  UNVERIFIED). It is not needed on the route, because there `ε = −1`.
* **Integration (for the integrator).** `hL3` is a top-level argument of `frozenTarget`, not a bundle field, so
  `autofold.py` cannot fold this directly. `scratch/gz-conj/autofold.json` is the spec for the field
  `grossConjugationCd` once the integrator has replaced `hL3` by gz-weil's `C_d` chain with its three Heegner
  fields. It adds no new leaves: `{"field": "grossConjugationCd", "proof": "_root_.ZInQ.GZConj.grossConjugationCd"}`.
  Without that step, `scratch/gz-conj/MainEdit.lean` shows the replacement directly (`frozenTarget_gzconj`).
* **`#discharges`** (§5): `GrossConjugationCd` is not an OPEN.md field at 60a3fac7, so `#discharges` cannot list
  it as discharged. The output is recorded for completeness.

---

## 5. Checks

* `lake build +ZInQKernel.Contrib.OneProof.GrossConjugationCd`: success; the only warnings are deprecations
  (VERIFIED).
* `scratch/gz-conj/Main.lean` (the same content as a scratch file): `#print axioms` for `grossConjugationCd`,
  `conj_clause` and `lattice_eq_of_g` gives `[propext, Classical.choice, Quot.sound]` (VERIFIED).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` at this branch: success, 13,667 jobs;
  `frozenTarget` uses only the standard axioms (VERIFIED).
* `scratch/gz-conj/MainEdit.lean` compiles. `frozenTarget_gzconj` (`hL3` replaced by `HeegnerPointRationalCd`
  and `GrossZagierFormulaCd`) and `frozenTarget_gzconj_printed` (`hL3` replaced by `X0ModuliGaloisMero` and
  `GrossZagierFormulaCd`) both use only the standard axioms, as do `grossConjugationCd`, `conj_clause`,
  `rootNumber_cd`, `lattice_eq_of_g` and `grossZagierHeegnerCd_of_printed`. Output:
  `scratch/gz-conj/out_mainedit.txt` (VERIFIED).
* `scratch/gz-conj/Discharges.lean` (`#discharges`, output in `scratch/gz-conj/discharges-output.txt`): "61 open
  hypotheses, 2958 theorems checked, 8 discharge one". None of the eight is a `ZInQ.GZConj` theorem, as expected:
  `GrossConjugationCd` is not a field of `frozenTarget` at 60a3fac7. The two `hL3` lines come from older files
  (gz-hl3's general split and gz-heegner's). The discharge appears only once `hL3` has been replaced by the
  `C_d` chain, as in `MainEdit.lean` (VERIFIED).
