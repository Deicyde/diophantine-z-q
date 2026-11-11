# el-e4 — frozen-Θ redesign (el-gadget E4 = el-cert M1): verdict

Note: `docs/research/el-e4.md`; log and scripts in `scratch/el-e4/`. No Lean was run, and nothing under
ZInQKernel/ or blueprint/ was edited.

**Soundness: holds** (VERIFIED). Φ(R₀a²/Θ₀²) gives 2v(Θ₀) < k + 2v(a) ≤ k. That is the existing
`pole_step`/`tests_small` (and `common_group_of`) argument at q = 0, plus 2v(a) ≤ 0, which holds because
x² − R₀y² is anisotropic. It costs no variables in FrozenTarget's budget. In Lean, `pole_step` needs a
restatement for a numerator that differs from the argument of W.

**Completeness curve.** C_m : h² = m(mΘ₀² − R₀(1 − R₀q²)²), via the θ = 1 witness. Its Jacobian is
E_J : y² = x(x² − 4mR₀²x + 4m³R₀³Θ₀²) (VERIFIED). C_m(ℚ) ≠ ∅ iff −mR₀ ∈ ⟨ac⟩·x(E(ℚ)) mod squares, where E is
the 2-isogenous curve. So the requirement is a prescribed φ-Selmer class, not just positive rank.

**Local** (VERIFIED, 30 real-data proxies from the Lean formulas): local solubility is not forced. The only
generic obstruction is p | num Θ₀ with (R₀/p) = −1, which needs (−m/p) = −1. Within m = m₀k² only m₀
matters, since k rescales Θ₀ and can only add obstructions. With the 64 Lean multipliers, 4/30 instances
are already obstructed by the primes found so far. The other counts are upper bounds, because cofactors of
195–1449 digits are unfactored. The L7 group (F₂-rank 68) solves every proxy but fails once there are more
than about 65 obstruction primes. So no fixed multiplier group works for all instances.

**Global** (VERIFIED, 240 everywhere locally soluble toy quartics, Lean R₀ with small Θ₀): only 2 provably
have a point, and none has a point of height ≤ 2000. 74 provably have none: rank E = 0, so each is a
nontrivial element of Ш(E_J)[φ]. 69 of those also show an unconditional Ш(E_J)[2] ≠ 0 in PARI. The other
164 are undecided because the rank-1 generators were not found. **The Hasse principle fails for this
family.**

**vs CR₃.** Formally incomparable (disjoint curve families), but much worse in substance. E4 needs a
specific Selmer class of a non-CM curve with uncontrolled conductor to come from E(ℚ). For a fixed choice
this is false in a positive proportion of cases, and no published theorem covers it. p-converse theorems
need a corank-1 Selmer group, which the gadget cannot force. CR₃^Rk (minimal Sel₂ for congruent-number
curves) is covered by published theorems: Kriz, or TYZ with Gross–Zagier.

**Chance that E4 replaces CR₃ by something better: very low (≲ 2%).** E4/M1 remains a sound,
budget-neutral cleanup.

**Single next step:** none for elimination. If M1 is adopted with CR₃ kept, check el-cert's field-2′
caveat (Lemma P smallness of R inside W is lost) before restating `pole_step` in Lean.
