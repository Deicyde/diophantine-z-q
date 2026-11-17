# htnew-det: the determinant argument does not remove `eigenformHTNew`

Task htnew-det, 2026-11-16. Base c7fbc273 (wip/leaf-fold33b; `git merge origin/main`: already up to date).
Lean: `ZInQKernel/Contrib/OneProof/HTNewDet.lean` (copy in `scratch/htnew-det/HTNewDet.lean`), with
`scratch/htnew-det/G12WeightCopy.lean`, `Discharges.lean` and `Discharges-output.txt`, `autofold.json`, `log.md`.
Nothing else under `ZInQKernel/` was edited. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file on this host. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a locator recalled without a source (no network on this host).

## 1. Verdict

**The argument does not close. `eigenformHTNew` stays; field count, GLUE count and leaf count are unchanged; no new
leaf.** No statement was changed. The proposed argument compares determinants at Frobenius elements, and that
comparison is circular in the chain as it stands:

- In `G0Galois.g12` (TailA l.2211, VERIFIED), Pan∘Berger (`PkgI4.PanBerger` = `PanFor LocalIsDeRham`, LPrefix
  l.2252) returns a weight `k ≥ 1`, an eigenform `g` and an **arbitrary continuous character** `ψ : G_ℚ → ℚ̄₅^×`.
  Pan's printed conclusion says only "cuspidal eigenform up to twist"; it gives no control of the weight or the twist
  (locators.md row R12, VERIFIED read). `g12` first calls `G12Weight` (which reads `r13`) to get `k = 2`. Only then
  does it use `G12Det` (stated and proved at weight 2: `g12Det_of`, TailA l.2447) and `GlueAssembly.twist_finite` to
  show that `ψ` has finite image.
- The proposal says "provided the chain identifies ρ_g with r₅ (or a twist by a finite-order character)". That
  proviso is exactly what is unknown: `r₅ ≅ ψ ⊗ ρ_g` with `ψ` not known to have finite order. Finite order of `ψ`
  follows from the determinants only once `k = 2` is known. So the argument needs `ψ` finite to get `k = 2`, and
  needs `k = 2` to get `ψ` finite.
- **The determinant data are sharp (VERIFIED, compiled).** Let `ε` be the nebentypus and `χ` the 5-adic cyclotomic
  character. Every identity the chain's leaves state is unchanged under
  `(k, ψ, a_q) ↦ (k + 2m, ψ χ^{−m}, q^m a_q)`. These identities are: R14/DS 9.6.5's
  `det ρ_g = ε χ^{k−1}` and Frobenius polynomial `x² − a_q x + ε(q) q^{k−1}`; Pan's trace form
  `tr r₅(Frob_q) = ψ(Frob_q) a_q`; and the Weil-pairing identity `(det r₅)² = χ²` on `G_K`. That last one is
  `weilPairingMumford` / T9 with `V₅(A) ⊗ ℚ̄₅ ≅ r₅ ⊕ r₅`, and it mentions neither `k` nor `ψ`. The shifted data are
  the Frobenius data of `θ^m f = Σ n^m a_n qⁿ`, which is a `p`-adic eigenform of weight `2 + 2m` with Galois
  representation `ρ_f ⊗ χ^m` (STANDARD: Serre, *Formes modulaires et fonctions zêta p-adiques*, LNM 350 (1973);
  Katz 1973; UNVERIFIED locators), but not a classical one. So any argument for `k = 2` must use that `g` is
  **classical**, beyond its Frobenius data. In the chain, that means the Hodge–Tate weights of `ρ_g`: Kato's theorem,
  the content of `eigenformHTNew`.
- What the determinants do give, in weight `k`, is that `ψ² χ^{k−2}` has finite image (`twist_sq_mul_cyc_finite`). At
  `k = 2` this is `twist_finite`. For `k = 2 + 2m` it allows `ψ = χ^{−m} · (finite)`, which has infinite image
  (`twist_shift_not_finite`).

ht-bypass judged that "determinants cannot tell k apart" (SPECULATIVE there). That judgement is now a Lean fact, in
the form above. weilPairingMumford and charpoly-charp's `M ⊕ M` decomposition supply the `(det r₅)² = χ²`
identity, which the chain already had through T9 (`G12Det`). They add no information about `k` or `ψ`.

**Smallest missing input.** `NoHighWeightTwist5` (§2) is exactly what `g12` needs beyond the proved pieces: no
eigenform of weight `≥ 3` is attached, up to any twist, to an irreducible `r : G_ℚ → GL₂(ℚ̄₅)` with Hodge–Tate weights
`{0, −1}`. `G12Weight` follows from it without `R13` (`g12Weight_of_noHighWeight`). It follows from the chain's route
through `r13` (`noHighWeightTwist5_of_g12Weight`), so it is no stronger than what is used now. **Rating: GLUE, not a
printed-form leaf.** It is a corollary of Kato, Astérisque 295 (2004) §§9.2-9.4 (locators.md R13), combined with Sen's
twist theorem, Chebotarev and Brauer–Nesbitt. No paper prints it in this form, and Kato's printed object `V_{F_λ}(f)`
cannot be defined in Mathlib. Swapping the field for it would leave the GLUE count unchanged, so no reroute is proposed
(`scratch/htnew-det/autofold.json`). The closest printed-form input is still ht-bypass's `EigenformHTNew5Ge3` (branch wip/ht-bypass, not in this tree)
(`ℓ = 5`, `k ≥ 3`).

## 2. The Lean (`ZInQ.Contrib.HTNewDet`, VERIFIED compiled)

| declaration | statement | role |
|---|---|---|
| `twist_sq_mul_cyc_finite` | `H` finite index, `r = ε χ^{k−1} ψ²`, `r² = χ²` on `H`, `ε` finite ⇒ `ψ² χ^{k−2}` finite image | all the weight-`k` determinant data give |
| `det_data_weight_shift` | `r = ε χ^{k−1} ψ²` ⇒ `r = ε χ^{k+2m−1} (ψ χ^{−m})²` | determinant identity is invariant under the shift |
| `twist_shift_not_finite` | `ψ` finite, `χ^m` infinite ⇒ `ψ χ^{−m}` infinite | finiteness of `ψ` does not follow from the data |
| `charpoly_smul_fin_two` | `charpoly M = X² − aX + b` ⇒ `charpoly (c • M) = X² − (ca)X + c²b` | Frobenius polynomials under a scalar twist |
| `frobPoly_weight_shift` | DS 9.6.5 polynomial `X² − a_q X + e q^{j}` for `M` ⇒ `X² − (q^m a_q) X + e q^{j+2m}` for `q^m M` | DS 9.6.5's form is invariant under the `θ^m` twist |
| `traceTwist_weight_shift` | `t = ψσ x` ⇒ `t = (ψσ χσ^{−m})(χσ^m x)` | Pan's trace form is invariant under the shift |
| `NoHighWeightTwist5` (def) | ∀ `r g k ψ ιC ιL S`, `0 < N`, `3 ≤ k`, `g` normalized eigenform, `r` irreducible, HT `{0,−1}` at 5, `r.AttachedUpToTwist ψ ιC ιL g S` ⇒ `False` | smallest missing input (GLUE) |
| `G12WeightNoR13` (def) | `G12Weight` with the `PkgI4.EigenformHT` hypothesis removed | |
| `g12Weight_of_noR13` | `G12WeightNoR13 → G12Weight` | |
| `g12WeightNoR13_of` | `SenTwist → FiniteImageHT → NoHighWeightTwist5 → G12WeightNoR13` (`k = 1` Deligne–Serre as in `g12Weight_of`; `k = 2`, `n = 0`; `k ≥ 3` by `NoHighWeightTwist5`) | `G12Weight` without `r13` |
| `g12Weight_of_noHighWeight` | `SenTwist → FiniteImageHT → NoHighWeightTwist5 → G12Weight` | |
| `noHighWeightTwist5_of_g12Weight` | `G12Weight → R14 → R13 → R15 → T18 → T19 → NoHighWeightTwist5` | implied by the current route |

`scratch/htnew-det/G12WeightCopy.lean` contains a verbatim copy of `G12Weight` (TailA l.2059), checked equal to the
chain's constant by `rfl`, and `copy_of_noHighWeight`.

## 3. Why no other input in the chain closes it (SPECULATIVE judgement, elementary computations)

- **Hodge–Tate of `ψ`.** `ψ² = det r₅ · ε⁻¹ · χ^{1−k}` is Hodge–Tate, so `ψ` is locally `χ^{(k−2)/2}` times a
  character of finite order for even `k`, and has Sen weight `(k−2)/2` for odd `k`. Then
  `ρ_g = ψ⁻¹ ⊗ r₅` would have weights with difference 1, and only Kato's theorem (difference `k − 1`) contradicts
  that.
- **Integrality and absolute values.** Eigenvalues of `r₅(Frob_q)` are algebraic integers of absolute value `√q`.
  For the shifted data they are `q^{−m}` times the eigenvalues of a weight-`(2+2m)` Frobenius, so this forces
  `q^m | a_q(g)` for `q` split in `K`. `θ^m f` satisfies that, and so do the Ramanujan bound and the Hecke relations
  `a_{q²} = a_q² − ε(q) q^{k−1}`. To exclude a classical `g` this way one needs Serre's density-zero theorem for
  `q | a_q` (non-CM case), which is deeper than Kato's theorem.
- **Other `ℓ`.** The twist ambiguity is the same at every coefficient prime.
- **A route without Pan∘Berger.** ser-ell's strong-Serre route produces a weight-2 form directly, so it needs neither
  `r11r12` nor `eigenformHTNew`. It is a restructuring with unchecked primary statements (docs/research/ser-ell.md),
  and it was not attempted here.

## 4. Compile log (VERIFIED)

- `lake env lean ZInQKernel/Contrib/OneProof/HTNewDet.lean`: OK, no errors, no warnings.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.HTNewDet`: OK
  (14226 jobs).
- `#discharges` (`scratch/htnew-det/Discharges.lean`, output `Discharges-output.txt`): `36 open hypotheses, 9806
  theorems checked, 33 discharge one`. All 33 come from contributions already in the tree. `HTNewDet` discharges none,
  as expected, since it proves no field.
- `#print axioms`: every theorem uses `[propext, Classical.choice, Quot.sound]` (`det_data_weight_shift` uses
  `[propext, Quot.sound]`).
- `lake env lean scratch/htnew-det/G12WeightCopy.lean`: OK (`copy_eq` by `rfl`; axioms standard).
- The contribution file has no code that runs at build time (no `#eval`, `run_cmd`, notation or macros).

## 5. Recommendation

Keep `eigenformHTNew`. In OPEN.md, record that its one use needs only `NoHighWeightTwist5`, i.e. `ℓ = 5`, `k ≥ 3`,
"not up to twist", and that determinants and Frobenius data provably cannot supply this (the `θ^m` shift). A
contributor who formalizes Kato's theorem (or Faltings/Saito/Scholl) at `ℓ = 5`, `k ≥ 3` closes it through
ht-bypass's `EigenformHTNew5Ge3` or directly through `NoHighWeightTwist5`.
