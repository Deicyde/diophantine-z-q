# el-qfree: using the freedom in the witness `q` and in the multipliers to remove CR₃

Branch `wip/el-qfree` (from `wip/cr3-maps`). This note builds on cr3-map-needs (L1-L9, W0-W3) and
cr3-map-literature (R1-R7), and does not repeat them. Claims are marked **VERIFIED** (checked against the
Lean sources or by exact computation; scripts in `scratch/el-qfree/`, outcomes in
`scratch/el-qfree/log.md`), **STANDARD** (published, with reference) or **SPECULATIVE**. No Lean
was run, and no file under `ZInQKernel/` was edited.

## 0. Verdict

- **The angle does not eliminate CR₃. Chance: very low.**
- **The freedom is larger than the maps assumed.** The predicates `Test` and `SlopePred`
  quantify the witnesses existentially over all of `ℚ` (q), over both signs (η), and over all
  integer shifts (`h, s₀`, resp. `h_g, z_g`). The open sets `U_test` and `U_slope` come only from
  PC's hypotheses. (§1, VERIFIED)
- **That freedom is the wrong kind.** Every witness enters `θ` only through the single rational
  number `σ = a₀/Θ`, which is a value of a rational function of degree about 25 in
  `R = R₀a₀²` (100 in `q`). The set of `σ` with an explicit point is thin, and so is the image of `σ`.
- **Multipliers (§2).** Soundness together with completeness at the inputs where `v_p(B) = 1`
  pins `v_p(m) = 0` at the consumed primes, and `v_p(m)` must be even and `≥ 0` at every
  `p > 324`. So the multiplier set is finite, `{m₀k² : k < 2^K}`, unless one can define
  `ℤ[1/S]` in `ℚ`, which is the target problem.
  - With unbounded S-integral `k`, `θ = 1` would reduce to Legendre conditions, but `k` would be
    doubly exponential in the size of `B`.
- **Experiments.** `θ = ±1` with `m = m₀k²`, `m₀ | ±Π_{p≤324}p`, `k ≤ 256` never occurs on real
  test-site inputs (E2). The Jacobian of the `θ`-curve has no CM factor, so no `q`-uniform section
  exists (E3).
- **Strongest obstruction.** Any `q`-uniform or rational-curve witness is a rational curve on a
  variety of Kodaira dimension 1 whose canonical fibration is the `q`-line. Its expected dimension
  is `−48e − 1 < 0`. Any witness for a single `q` is a positive-rank statement for `C_{βθ(q)}`,
  which is the shape of CR₃ again.

(Sections 1-5 below.)
