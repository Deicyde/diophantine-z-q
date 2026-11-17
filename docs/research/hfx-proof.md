# hfx-proof: `TYZTestVectorExists` proved outright

**Result (VERIFIED, compiled).** The top hypothesis `hfx : H29Split.TYZTestVectorExists` of
`ZInQ.OneProof.frozenTarget` is a theorem, with no new hypothesis:

```lean
theorem ZInQ.Contrib.HfxProof.tyzTestVectorExists : ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists
```

The theorem is in `ZInQKernel/Contrib/OneProof/TYZTestVectorExists.lean`. Its helpers are in
`ZInQKernel/Contrib/OneProof/HfxProof/` (15 files, 180 KB). The statement is unchanged and no leaf is
added, so the single proof loses one top hypothesis. Finite computations are checked by the kernel with
`decide +kernel` only. The new files contain no `native_decide`, `sorry`, `axiom`, `#eval`, or new syntax
(checked by grep). The `#discharges` output is in §4.

Base: origin/main 0caafe66, with two merges:
* origin/wip/t21-proof f597c34c, for the `T21Proof` helpers: Hurwitz coordinates, `piQ`, `global_step`,
  `two_adic_step`;
* origin/proof/hp23-hurwitz-ab-20261116 84a9f2e6 (fork PR #39), for `exists_hurwitz_coordinates_norm_lt_one`.

So the deliverable depends on those two branches being integrated.

## 1. The statement

`TYZTestVectorExists` (TYZ arXiv:1411.4728v1, L542–550; Theorem 2.6 at χ = 1) says: for squarefree
`1 < n ≡ 1, 3 (mod 8)` and every admissible `τ : ℚ(√−n) → ℍ[ℚ]`, there is `f : ℍ[𝔸ᶠ_ℚ] → ℤ` that generates
`π_ℤ^{U_n}` (`IsTestVector`: `InPiZ` plus every `InPiZ` function is an integer multiple on units), and
`f(x) ≠ 0` for some unit `x`. The theorem proves it as stated. So the statement is true, and since a
generator exists it is not vacuous.

## 2. Route (as proposed in the task, carried out)

Throughout, `v` is the place 2, `H = ⟨U_n, ℚ̂^×⟩`, and `DC x = B^× x H`.

1. **Assembly** (`Assembly.lean`, `testVector_of_partition`). Suppose four things hold:
   * every unit lies in some `DC(twoRep v t)`;
   * `F : {0,1}³ → ℤ` has the classes as its level sets (merges and separations);
   * `F` is orthogonal to `1` and `χ₀`;
   * `F` spans the functions that are constant on its level sets and orthogonal to `1` and `χ₀`.

   Then the function equal to `F t` on `DC(twoRep v t)` is a nonzero test vector. Its invariances hold by
   construction, because it is defined on double cosets. For generation, any `g ∈ π_ℤ^{U_n}` is
   `H`-invariant (by closure induction over the generators of `H`), so it is determined by its 8 values.
2. **`B̂^× = B^× Ô_B^×`** (`Euclid.lean`, `ClassOne.lean`, `exists_global_mul_unit`).
   * The Hurwitz order is right Euclidean (PR #39's approximation, with norm error below 1). From this,
     `βO_B + pO_B = γO_B` with `nrd γ = p` (`euclid_prime`).
   * Proof: multiply `x` by a common denominator (Tau Ceti's `mul_nonZeroDivisor_mem_integralAdeles`).
     Then induct on `m`, where `m / nrd(y_w)` is integral at every place.
   * At a place where `nrd y` is not a unit, approximate `y_p` mod `p` by a global `β ∈ O_B`. Divide by the
     `γ` of `euclid_prime`, or by `p` itself if `β ≡ 0`.
   * `Ô_B` is read place by place. `mem_hurwitzHat_of_LH` converts back to the repository's `hurwitzHat`.
3. **TYZ Lemma 2.5, surjectivity** (`Finite25.lean`, `Lemma25.lean`, `exists_twoRep`).
   * Every residue in `(O_B/4)^×` is `±μβ_t`, with `μ` a Hurwitz unit (`lemma25_check`, decide, 13 s).
   * Then `(±μ twoRep t)⁻¹ u ∈ 1 + 4Ô_B ⊂ R̂_n^× ⊂ U_n`. This holds for every `n` and `τ`.
4. **The orbits of `K_{n,2}^×` on the 8 classes.** Write `τ(√−n) = ai + bj + ck` with `a, b, c ∈ ℤ`
   (`exists_abc`; for `n ≡ 3` this uses `τ(O_K) ⊂ O_B` and `τ(√−n)² = −n`). Then
   `τ(O_K) ⊂ ℤ + ℤω` (`tau_span1`, `tau_span3`), with `ω = τ(√−n)` for `n ≡ 1` and `ω = (1 + τ(√−n))/2`
   for `n ≡ 3`.
   * **Merges** (`Merge.lean`, `twoRep_mem_DC_of`).
     * Suppose `α ∈ K^×` (commuting with `τ(√−n)`) and `ρ ∈ O_B` of norm 1 or 2 satisfy
       `β_t α ∈ ρβ_{t'}(1 + 4O_{B,2})`. Then `twoRep t ∈ DC(twoRep t')`, using `ιAt(α) ∈ K_{n,2}^×` and
       `1 + 4Ô_B ⊂ R̂_n^×`.
     * The condition at 2 follows from the integer congruence `Ā(B − A) ≡ 0 mod 4·2^b`
       (`local_merge_cond`).
   * **Separations** (`Order.lean`, `TwoAdic.lean`, `Sg.lean`, `twoRep_not_mem_DC`). This generalizes
     t21-proof's argument for the class of 1 at `n = 3`.
     * A local condition `C` at 2, closed under products and inverses, defines `SgC`, and `H ≤ SgC`.
     * If `twoRep t = γ twoRep t' h` with `h ∈ SgC`, then `γ = q·n` with `nrd n = 2^k` (t21's
       `global_step`).
     * At 2 the relation reduces to a finite congruence:
       * `μβ_t ≡ β_{t'}(X + Yω) (mod 4)` (`two_adic_b1`);
       * in the ramified case also `(1 − i)β_t(1 + ω) ≡ 2μβ_{t'}(X + Yω) (mod 8)` (`two_adic_b2`).
   * **n ≡ 3 (mod 8)** (`Finite3.lean`, `Case3.lean`, `testVector_three`).
     * Here `K_2^× = ℚ_2^× R_2^×`, and `C3` is `Loc2OK` for `ω² = ω − (n+1)/4`. The centralizer of
       `τ(√−n)` lies in `C3` (`loc2OK_of_commute3`).
     * Table `tab3` covers the 64 residues of `hc(ω) mod 4`. For each it gives the 2-orbit and the
       6-orbit, with merge witnesses. One separation per residue suffices (roots plus merges); decide
       takes 27 s.
     * `F = −3` on the 2-orbit and `1` on the 6-orbit.
   * **n ≡ 1 (mod 8)** (`Finite1.lean`, `Order1.lean`, `Case1.lean`, `testVector_one8`).
     * `K_2 = ℚ_2(ω)` is ramified with uniformizer `ϖ = 1 + ω`. `C1` is `y ∈ ℚ_2^× R_2^×` or
       `yϖ ∈ ℚ_2^× R_2^×`.
     * `C1` is a group because conjugation by `ϖ` preserves `O_{B,2}`: `ϖ̄aϖ ∈ 2O_{B,2}`, checked mod 2
       by decide. Also `ϖ² ∈ 2R_2^×`.
     * The centralizer lies in `C1` by a case analysis mod 2 (`core1`, `loc_of_commute1`).
     * Table `tab1` covers the 32 residues of `hc(ω) mod 8`. The three orbits have roots `000`, `110`,
       `101`; merges may use the uniformizer. There are three root separations, in both branches;
       decide takes 2 min.
     * `F = 1, −1, 0` on the three orbits.
   * Rank one: `rank1_two` and `rank1_three`, by counting over the level sets.

## 3. Findings (VERIFIED: computed in python `scratch/hfx-proof/orbits.py`, `gen_tables.py`, and compiled)

* **n ≡ 3 (mod 8).** `K_{n,2}^×` has two orbits on TYZ's 8 classes, of sizes 2 and 6. Which pair is the
  2-orbit depends on `τ(√−n) mod 8`, and it need not contain the class of 1: for `τ(√−n) ≡ 3i + j + k`
  (e.g. n = 11) the 2-orbit is `{(1,0,0), (0,0,1)}`. The generator takes the values `−3, 1`, as h29-fix's
  `brandt.py` found for n = 3, 11, 19.
* **n ≡ 1 (mod 8).** There are three orbits, of sizes 2, 2 and 4. With `x = ai + bj + cζ` (`ζ` TYZ's), the
  orbit of 1 is `{000, 100}` or `{000, 010}`, according to whether the odd one of `a, b` in `τ(√−n)` is
  the `i`- or the `j`-coordinate. The size-4 orbit is the classes with `χ₀ = −1`.
  * The uniformizer is needed: the units of `O_{K,2}` alone give orbits of sizes (2, 2, 2, 2), and then
    `π^{U_n}` would have dimension 2.
  * The generator takes the values `1, −1, 0`. In particular `f_n` vanishes on half of the classes. The
    docstring of `TYZTestVectorExists` reports only the `n ≡ 3` computations ("the values `{1, −3}`"). For
    `n ≡ 1` the values are `{1, −1, 0}`. This is not a contradiction and does not affect any statement.
* For every residue, `π^{U_n}` is free of rank one over ℤ, as TYZ L545–547 say.

## 4. `#discharges`

The output is in `scratch/hfx-proof/Discharges-output.txt`, from `scratch/hfx-proof/Discharges.lean`
(`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.TYZTestVectorExists`, then `lake env lean`):

```
DISCHARGES [hfx] by ZInQ.Contrib.HfxProof.tyzTestVectorExists
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 56 open hypotheses, 3456 theorems checked, 8 discharge one
'ZInQ.Contrib.HfxProof.tyzTestVectorExists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The build took 72 minutes wall-clock (13,726 Lake jobs; a partial rebuild on this host). `FoldCheck.lean`
(`scratch/hfx-proof/FoldCheck-output.txt`):

```
'ZInQ.Contrib.TYZChain.frozenTarget_noHfx' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZChain.frozenTarget_noHfxT21' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`autofold.py scratch/hfx-proof/autofold.json --dry-run` refuses with `not a field of the current bundles:
['hfx']`, as expected (§5).

## 5. Fold

`hfx` is a top-level argument of `frozenTarget`, not a bundle field, so `autofold.py` refuses it, as it
refused `hT21` (t21-proof). The spec is in `scratch/hfx-proof/autofold.json`.

The manual fold is checked in `scratch/hfx-proof/FoldCheck.lean`:
* `frozenTarget_noHfx` is `frozenTarget` without `hfx`, passing `ZInQ.Contrib.HfxProof.tyzTestVectorExists`;
* `frozenTarget_noHfxT21` also drops `hT21`, using t21-proof's theorem.

Both compile with the standard axioms (§4). For the integrator:
* import `ZInQKernel.Contrib.OneProof.TYZTestVectorExists` in `Main.lean`;
* drop the binder `(hfx : H29Split.TYZTestVectorExists)` and pass the theorem where it was used;
* remove the `hfx` rows from kinds.tsv and claims.tsv, and regenerate OPEN.md.

## 6. Leaves

There is no new leaf, so nothing needs a printed-form rating. The proof uses Mathlib, Tau Ceti's finite
adeles (`mul_nonZeroDivisor_mem_integralAdeles`, `algebraMap_mem_integralAdeles_iff`, `tauHat`), the
definitions of `TYZLemma29Mod2.lean`, t21-proof's helpers, and fork PR #39's Hurwitz approximation. All
are proved with the standard axioms.

## 7. Consequences for the other TYZ leaves

`IsTestVector` determines `f_n` up to sign (`f = ±F` on units), so the hypotheses that quantify over test
vectors become statements about the explicit `F`. Two of them (SPECULATIVE, not attempted in Lean):
* **`hP23 = TYZProp23Printed`** (`f_n(h²)` is odd).
  * For `n ≡ 3` it is immediate, since `F ∈ {−3, 1}` is odd everywhere.
  * For `n ≡ 1` it needs `h²` to avoid the size-4 orbit, where `F = 0`. Squares have `χ₀(nrd) = 1`, and
    that orbit is exactly `χ₀ = −1`. An invariant `nrd mod 4` at 2, read through the same global step,
    should give this.
* **`hL29 = TYZLemma29PrintedNe3`.** This becomes a statement about `Σ_{t ∈ 2Cl_n} F(τ̂(t))`. It still
  involves the L-values, so it remains a leaf.

## 8. Files

* `ZInQKernel/Contrib/OneProof/TYZTestVectorExists.lean`: the theorem.
* `ZInQKernel/Contrib/OneProof/HfxProof/`:
  * `Assembly`;
  * `Euclid`, `ClassOne` (`B̂^× = B^×Ô_B^×`);
  * `Finite25`, `Lemma25` (Lemma 2.5);
  * `Order`, `TwoAdic`, `TauData`, `Sg`, `Merge` (the local theory);
  * `Finite3`, `Case3` (n ≡ 3);
  * `Order1`, `Finite1`, `Case1` (n ≡ 1).
* `scratch/hfx-proof/`:
  * `log.md`;
  * `orbits.py`, `gen_tables.py`, `gen_lean3.py`, `gen_lean1.py` (orbit computation and table generators),
    with `tab3.lean.txt` and `tab1.lean.txt`;
  * `Discharges.lean` and its output, `FoldCheck.lean`, `autofold.json`, `DecideTest.lean`.
