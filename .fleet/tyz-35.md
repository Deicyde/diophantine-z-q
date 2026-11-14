# tyz-35 — `Thm35First ℓ tyzZ` (TYZ Thm 3.5, first assertion, pinned genus points)

**Result.** `Thm35First ℓ tyzZ` is proved in Lean for every `ℓ` with `ℓ 1 = 1` (so every
`IsTYZLcal ℓ`) from one leaf, `TYZThm33Pinned ℓ` = TYZ Theorem 3.3 with Lemma 3.14 for the pinned CM
points (character components `P_χ = Σ_c χ(c) z_n^{f c}` over every lift family `f`, genus characters
`χ_T = Π_{q∈T} χ_q`, `𝒫(d) = Q d / m d` one vector per `d` for all levels, `ε` in TYZ's classes,
`𝒫(n) = 0` when `𝓛(n) = 0`). Glue proved: character formula, genus product formula for n ≡ 3 (4),
subsets ↔ divisors, characters ↔ factorizations, a lift family with `f(2Cl) = Φ₀`, the level identity
and TYZ's induction (L2343–2380). Main theorems `thm35First_of_thm33`, `thm35First_of_lcal_thm33`
(scratch/tyz-35/Thm35.lean) and cm-bridge's headline with the new leaf,
`tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm33_lemma321Five` (scratch/tyz-35/Final.lean).

**Compiles.** Both files: 0 errors, no sorry; axioms `[propext, Classical.choice, Quot.sound]`
(audit-out.txt). Builds: `RingClassBridge`, `ShimuraFricke` (clean).

**Remains.** The leaf `TYZThm33Pinned` (needs heights + explicit Gross–Zagier/YZZ + Kolyvagin). HUMAN
CHECK against Period7.tex (not on this host): TYZ's choice of representatives Φ in `P_χ` (the `∀ f` form
relies on `σ_ϖ²` adding `τ(1)` to `z_n`, tyz-t1 §3.1), the convention for `χ_{d₀,d₁}` (pure-Python
check `convention.py`: 0 mismatches on 26 n), `h₂`. No PARI on this host (`~/pyenv` missing), so no new
Heegner-point numerics; the n ≡ 7 cross-level part of Theorem 3.3 has never been tested numerically.
Report: docs/research/tyz-35.md.
