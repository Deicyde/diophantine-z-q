# hp23-proof: `TYZProp23Printed` proved outright

**Result (VERIFIED, compiled).** The top hypothesis `hP23 : H29Split.TYZProp23Printed` of
`ZInQ.OneProof.frozenTarget` is now a theorem. The proof adds no hypothesis:

```lean
theorem ZInQ.Contrib.HP23Proof.tyzProp23Printed : ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed
```

The theorem is in `ZInQKernel/Contrib/OneProof/TYZProp23Printed.lean`. Its helpers are in
`ZInQKernel/Contrib/OneProof/HP23Proof/` (four files: `Good`, `Generic`, `Case1`, `Case3`).

* The statement is unchanged. It is true, and it is not vacuous, because hfx-proof's test vectors exist.
* No leaf is added, so the single proof loses one LEAF (`hP23`, kinds.tsv row 41).
* Every finite computation is checked by the kernel with `decide +kernel`. There are three such checks,
  each small: `nrdH_βZ_mod4`, `nrd4_check` and `tab1_c_ne_two`.
* A grep of the new files finds no `native_decide`, `sorry`, `axiom`, `#eval`, `run_cmd`, `syntax`,
  `macro` or `notation`.

The theorem depends only on the standard axioms. The `#discharges` output and the manual fold are in §4.

Base: wip/hfx-proof 779d0d7d, merged with origin/main c1e4ed1b (merge ee2f8a65). The proof uses hfx-proof's
files `HfxProof/*` (in origin/main through the hfx-proof branch) and t21-proof's files `T21Proof/*`.

## 1. The statement

`TYZProp23Printed` is TYZ (arXiv:1411.4728v1) Proposition 2.3, L580–586, first assertion. Fix a
squarefree `n` with `1 < n` and `n ≡ 1, 3 (mod 8)`. Then for every admissible `τ`, every test vector `f`
(`IsTestVector n τ f`) and every unit `h` of `B̂ = ℍ[𝔸ᶠ_ℚ]`, the value `f(h²)` is odd. The theorem proves
exactly this statement.

## 2. Proof

This follows the sketch in hfx-proof's report, §7. Notation:
* `H = ⟨U_n, ℚ̂^×⟩`, and `DC x = B^× x H`;
* `T8 = {0,1}³` indexes TYZ's 8 classes `twoRep t = 1 + 2(a i + b j + c ζ)`, read at the place `2`.

### 2.1 Every test vector is `±F` (`Generic.lean`, `tv_eq_sign`)

Let `PartData n τ v F` be the hypotheses of hfx-proof's `testVector_of_partition`:
* surjectivity onto the 8 double cosets;
* the level sets of `F` are the classes (merges and separations);
* orthogonality to `1` and `χ₀`;
* rank one;
* `F ≠ 0`.

Assume `PartData` and let `f` be any test vector. Then:
* by the merges and rank one, `f(twoRep t) = c F t`;
* `fOf F` lies in `π_ℤ^{U_n}` (`inPiZ_fOf`, the first half of `testVector_of_partition`), and `f`
  generates, so `fOf F = d f` on units;
* evaluating at a class where `F ≠ 0` gives `dc = 1`, so `c = ±1`.

Hence `f x = ±F t` whenever `x ∈ DC(twoRep t)`.

### 2.2 The partition data and the values of `F`

`Case3.lean` and `Case1.lean` are copies of hfx-proof's `testVector_three` and `testVector_one8`. The only
change to the existing proof is the conclusion: they return the partition data instead of the test vector
built from it. They also add new facts:
* **n ≡ 3 (mod 8)** (`partition_three`): `F ∈ {−3, 1}`, so `F` is odd everywhere.
* **n ≡ 1 (mod 8)** (`partition_one8`):
  * `F = val1 ∘ e.c ∈ {1, −1, 0}`. For every entry of hfx-proof's table `tab1`, the size-4 orbit (`F = 0`)
    lies inside `{t.2.2 = 1}` (`tab1_c_ne_two`, decide). So `F` is odd on the classes with `t.2.2 = 0`.
  * The group `SgC v C1` contains `H`, by hfx-proof's local condition `C1`
    (`ℚ₂^× R₂^× ∪ ℚ₂^× R₂^× ϖ⁻¹`). Its reduced norms at `2` lie in `2^ℤ(1 + 4ℤ₂)` (`Good`):
    * on `R₂^×`, `nrd(x + zω + 4a) ≡ x² + z²(a² + b²) ≡ 1 (mod 4)` whenever it is a unit (`good_of_loc2OK`,
      with `nrd4_check` by decide);
    * `nrd ϖ = 2(4k + 1)`.

### 2.3 Squares avoid `χ₀ = −1` (`Generic.lean`, `sq_class`)

Suppose `h² = γ · twoRep t · u` with `γ ∈ B^×` and `u ∈ H ≤ SgC`.
* **Odd primes `p`.** The component of `twoRep t` is `1`, and the component of `u` is `c u₀` with `u₀` a
  unit. Taking reduced norms gives `nrd(h_p)² = nrd γ · c² · nrd u₀`. So the valuation of `nrd γ` at `p`
  is even (`even_padicValRat_of_eq`).
* **The rational `nrd γ`.** It is positive, and by the previous step its valuations at the odd primes are
  even, so it lies in `2^ℤ(1 + 4ℤ₂)` (`good_rat`). The proof is by strong induction on the numerator and
  the denominator, splitting off `2` or `q²` with `q` an odd prime.
* **The place 2.** Here `nrd(h₂)² = nrd γ · nrd(twoRep t) · nrd u₂`, and three of these factors lie in the
  group `Good = 2^ℤ(1 + 4ℤ₂)`:
  * `nrd(h₂)²`, which is a square (`good_sq`);
  * `nrd γ`, by the previous step;
  * `nrd u₂`, by §2.2.

  So `nrd(twoRep t) = nrdH(βZ t)` lies in `Good` too. If `t.2.2 = 1`, this is an integer `≡ 3 (mod 4)`
  (`nrdH_βZ_mod4`, decide), which is not in `Good` (`not_good_int`). Hence `t.2.2 = 0`.

`Good` is defined by `x ≠ 0 ∧ ∃ m : ℤ, ‖x 2^m − 1‖ ≤ 1/4`. It is closed under products and inverses and
contains `2`. Its elementary properties are proved in `Good.lean`; local class field theory is not used.

### 2.4 Assembly (`TYZProp23Printed.lean`)

By surjectivity, `h² ∈ DC(twoRep t)` for some `t`. By §2.1, `f(h²) = ±F t`.
* For `n ≡ 3`, `F t` is odd.
* For `n ≡ 1`, `t.2.2 = 0` by §2.3, so `F t` is odd by §2.2.

## 3. Findings

* `TYZProp23Printed` is true as stated (VERIFIED, compiled). It holds for every test vector, not only
  for TYZ's: by §2.1, the test vectors are exactly `±F`.
* For `n ≡ 1 (mod 8)` the oddness rests on a global argument, not only on local ones. The classes where
  `f_n = 0` are exactly those with `χ₀(nrd) = −1`. Squares avoid them because `χ₀ ∘ nrd` is trivial on
  `B^×` (positive norms, with even valuations at the odd primes) and on `H`. This is TYZ's orthogonality
  to `χ₀` read as an invariant (VERIFIED, compiled).

## 4. `#discharges` and the fold

`#discharges` output, from `scratch/hp23-proof/Discharges.lean` (full output in `Discharges-output.txt`). The
build was `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.TYZProp23Printed +ZInQKernel.Contrib.OneProof.TYZTestVectorExists`: 14,123
jobs, about 8 s, because the build tree was a reflink copy of a worktree with the same `Main.lean`. Then
`lake env lean`:

```
DISCHARGES [hP23] by ZInQ.Contrib.HP23Proof.tyzProp23Printed
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 45 open hypotheses, 7058 theorems checked, 14 discharge one
'ZInQ.Contrib.HP23Proof.tyzProp23Printed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

FoldCheck output (`scratch/hp23-proof/FoldCheck.lean`, full output in FoldCheck-output.txt):

```
'ZInQ.Contrib.TYZChain.frozenTarget_noP23' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZChain.frozenTarget_noHfxP23' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`hP23` is a top-level argument of `frozenTarget`, not a bundle field, so autofold cannot fold it; the fold is
manual. `FoldCheck.lean` proves two theorems:
* `frozenTarget_noP23`: `frozenTarget` without `hP23`, passing `ZInQ.Contrib.HP23Proof.tyzProp23Printed`;
* `frozenTarget_noHfxP23`: `frozenTarget` without `hfx` and without `hP23`, also passing hfx-proof's
  `ZInQ.Contrib.HfxProof.tyzTestVectorExists`.

For the integrator:
* import `ZInQKernel.Contrib.OneProof.TYZProp23Printed` (and `TYZTestVectorExists`) in `Main.lean`;
* drop the binder `(hP23 : H29Split.TYZProp23Printed)` (and `hfx`), and pass the theorems where they were
  used;
* remove the `hP23` rows from kinds.tsv and claims.tsv (and frontier-crosswalk T-23), and regenerate
  OPEN.md.

The LEAF count goes down by one (two with hfx), and GLUE is unchanged.

## 5. Leaves

There is no new leaf, so nothing needs a printed-form rating. The proof uses:
* Mathlib (p-adic valuations, `padicValNat`/`padicValRat`, `PadicInt.toZModPow`);
* the definitions of `TYZLemma29Mod2.lean`;
* hfx-proof's helpers (`HfxProof/*`) and t21-proof's helpers (`T21Proof/*`).

All of these are proved with the standard axioms.

## 6. Files

* `ZInQKernel/Contrib/OneProof/TYZProp23Printed.lean`: the theorem.
* `ZInQKernel/Contrib/OneProof/HP23Proof/Good.lean`: the subgroup `2^ℤ(1 + 4ℤ₂)`, `good_sq`, `good_rat`,
  `not_good_int`, `even_padicValRat_of_eq`.
* `ZInQKernel/Contrib/OneProof/HP23Proof/Generic.lean`: `PartData`, `inPiZ_fOf`, `tv_eq_sign`, `sq_class`.
* `ZInQKernel/Contrib/OneProof/HP23Proof/Case3.lean`: `partition_three`.
* `ZInQKernel/Contrib/OneProof/HP23Proof/Case1.lean`: `partition_one8`, `good_of_loc2OK`,
  `tab1_c_ne_two`, `nrd4_check`.
* `scratch/hp23-proof/`: `log.md`, `Discharges.lean` and `FoldCheck.lean` with their outputs, and the
  build logs.
