# el-qfree: does freedom in q and in the multipliers eliminate CR₃?

**No. Chance: very low.** Full note: `docs/research/el-qfree.md`; log and scripts: `scratch/el-qfree/`.

- **New, VERIFIED.** `Test` and `SlopePred` quantify the witnesses existentially over all `q ∈ ℚ`,
  both signs `η`, and all integer shifts (`h, s₀`, resp. `h_g, z_g`). The open sets U and the
  admissibility conditions (square denominator, `0 < B < 1/2`, `S₀`-valuations) are needed only by
  the PC/DL route. So the completeness input can be weakened to "some witness tuple per instance
  gives `Loc N β ∧ Loc Nθ β`".
- **Multipliers (VERIFIED derivation).**
  - Soundness forces `v_p(m)` even and `≥ 0` at all `p > 324`.
  - Completeness forces `v_p(m) = 0` where `v_p(B) = 1`.
  - Input-dependent multipliers kill completeness. Unbounded `k` needs a definition of `ℤ[1/S]`
    in `ℚ`, which is the target problem.
  - So `M` is finite.
- **`θ = ±1`.**
  - Exact criterion: S-integral `k` would need a square prime-to-S denominator and doubly
    exponential `k`. With bounded `k` the condition is a union of genus-33/49 curves in `q`.
  - E2: 0 hits on 30 real test-site inputs (all admissible `m₀ | ±Π_{p≤324}p`, `k ≤ 256`).
- **Other θ classes / rational curves of q.** A `q`-uniform witness needs
  `Hom(Jac Y_θ, C₁) ≠ 0`; E3 shows it is `0` on 3 real instances (no supersingular Frobenius at
  `p ≡ 3 mod 4`). General rational curves of `q`-values have expected dimension `−48e − 1`.
- **Strongest obstruction.** All freedom enters through one number, `σ(q)`. For any single `q`,
  `Φ` is a positive-rank or Sha statement for `C_{Nθ(q)}`, which is CR₃'s shape again, with `θ`
  uncontrolled.

**Single next step.** Abandon elimination along this angle. Optionally, state the §1 narrowing
`CR3Free` (`U = ℚ`, free `η`/shifts/`κ`, no admissibility) as a Lean `Prop` and re-route
`test_complete` and `slope_complete_AP` through it. This is a weakening of the trusted
hypothesis, not a removal.
