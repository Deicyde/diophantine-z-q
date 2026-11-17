# Numerical checks of the Tian–Yuan–Zhang hypotheses `h21C` and `h33`

Three scripts from the AI audit of 2026-11-17
([#64](https://github.com/Deicyde/diophantine-z-q/issues/64)). They recompute the two hypotheses of
`ZInQ.OneProof.frozenTarget` that come from Tian–Yuan–Zhang, *Genus periods, genus points and congruent number
problem*, directly from the Lean definitions, for small parameters. They are evidence for the statements as the
project repaired them, not proofs. An AI reviewer wrote them and no person has reviewed them.

Run every command from the repository root.

## `h21_check.py`: `TYZThm21PairsC` (`h21C`), exact arithmetic

```sh
xargs python3 -I scratch/audit-tyz-numerics/h21_check.py < scratch/audit-tyz-numerics/h21_ns.txt
```

For each squarefree `n ≡ 1, 3 (mod 8)` on the command line it builds every admissible embedding `τ`, checks that
the module of test vectors has rank one, and evaluates the quadratic period `P` for every factorisation
`n = d₁ d₂`. It follows `IsHurwitz`, `AdmissibleTau`, `RnHat`, `K2Units`, `Un`, `InPiZ`, `IsTestVector` and
`clLift` of `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` and `quadPeriod` of
`ZInQKernel/Contrib/OneProof/TYZLemma29Genus.lean`. `𝓛(m)` is taken from Tunnell's formula. It needs only the
Python standard library and prints `FAILED n: []` when both clauses of the hypothesis hold for every `n`.

* `h21_ns.txt` lists the 90 squarefree `1 < n < 460` with `n ≡ 1, 3 (mod 8)`; the run takes about 35 seconds and
  its output is `h21_all.txt`. `h21_big.txt` is the output for `969 1001 1105`.
* The run also shows why the hypothesis is weaker than the printed Theorem 2.1. The print says `P(d₁, d₂) ≠ 0`
  only if `d₂ ≡ 1 (mod 8)`; at `n = 3` the script finds `|P(1, 3)| = 3`, and at `n = 51` it finds
  `|P(17, 3)| = 4` (finding T3 of `docs/research/rv-tyz-inputs.md`).

## `eta_model_check.py`: the model of `X₀(32)`, exact arithmetic

```sh
python3 -I scratch/audit-tyz-numerics/eta_model_check.py
```

It checks with integer `q`-expansions, through `q^385`, that the eta quotients `x`, `y` of
`ZInQKernel/Contrib/TYZGenus/X0.lean` satisfy `y² = x³ + 4x` and `q dx/dq = 2 f y`.

## `h33_check.py`: `TYZThm33` (`h33`), 40-digit floating point

```sh
python3 scratch/audit-tyz-numerics/h33_check.py pairs
python3 scratch/audit-tyz-numerics/h33_check.py five2
```

It needs `mpmath`. Points are handled through elliptic logarithms on the eta model, and "torsion" means that
the logarithm is a rational combination of the periods with small denominator, to the working precision.

* `pairs` tests the second clause on 17 pairs `(d₀, d₁)`. Each output line lists every unit `u` and multiple `m`
  with `2^{h₂(d₀)} P_χ = u·m·P₁(d₀)` modulo torsion, next to what the hypothesis predicts: `u` in the stated unit
  class and `m = 2^{h₂(n)} 𝓛(d₁)`. In `h33_pairs.txt` the prediction is the only hit on all 17 lines, including
  `(7, 41)`, where `𝓛(41) = 0` and `P_χ` is torsion.
* `five2` tests the first clause and the sign of `[i]` for `n = 5, 13, 21, 29, 37, 53, 61, 85`
  (`h33_five2.txt`): with the project's choice `z_n = (1 − [i]) P` the excluded characters give torsion points,
  and with the other sign they do not.

## Limits

* Small parameters only: nothing here covers all `n`.
* `h33_check.py` is numerical. The constant `2^{h₂(n)} 𝓛(d₁)` of Theorem 3.3 has no printed derivation (finding
  T1 of `docs/research/rv-tyz-inputs.md`), and these runs are the only support for it in this repository.
* The scripts implement the reviewer's reading of the Lean definitions; a mistake shared by that reading and the
  Lean would not show up.
