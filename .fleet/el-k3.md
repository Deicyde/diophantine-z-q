# el-k3: Kummer-surface angle on CR₃

**Does the angle eliminate CR₃? No. Chance: very low.** Full note: `docs/research/el-k3.md`. Log
and scripts: `scratch/el-k3/`.

- **Exact Néron–Severi computation (VERIFIED).**
  - `Φ(B)` with multiplier `m` holds iff `X_{β,θ} : w² = θ(β²s⁴−1)(β²t⁴−1)` has a rational point.
  - The 40 curves (nodes, tropes, and the D4 graph curves that come from CM by ℤ[i] and the 2-torsion) generate
    `NS(X̄)`: rank 20, discriminant −16.
  - For every admissible `θ ≠ 1`, `NS(X̄)^G` has rank 8 and does not depend on θ. All its
    intersection numbers are even, and all self-intersections are `≡ 0 (mod 4)`.
- **Consequences:**
  - no smooth rational curve over ℚ;
  - no genus-one fibration over ℚ with a section;
  - every ℚ-fibration has generic fibre of even index, so points always come from a 2-covering
    fibre: the Ш[2] question that CR₃ encodes;
  - `H¹(G, NS) = 0`.
- **No deck-invariant rational curve over ℚ (VERIFIED, parity enumeration).** Such curves would
  be conics `w² = θh(z)`, decided by Hasse–Minkowski from local data, and they are the only
  θ-uniform source of points. The remaining rational curves each pin one θ class, so finding
  one is as hard as finding a point.
- **Realistic inputs (VERIFIED computation; heights SPECULATIVE, from BSD).**
  - 12/12 one-curve fibres have Selmer rank 1, and no point was found.
  - Generator heights are about `10^7`–`10^12`.
  - A point on any `X_{β,θ}` has log-height `≳ 10⁷`, so no explicit construction can reach it.
- **Strongest obstruction.** The Picard lattice over ℚ is 2-divisible in this sense and
  independent of θ. Every geometric route therefore reduces to the Hasse principle for
  2-coverings, which is CR₃ itself.

**Single next step.** Close this angle. The useful remaining work is the narrowing, not an elimination:
replace `CertifiedRank` by W3 (CR3DL of cr3-map-needs §2), or by the rank-≥1 statement already
reduced in `wip/integrate-wave8`, and check that the `poleCompleteness` adaptation compiles when a
Lean slot is free. A finer K3 test (transcendental Brauer classes) cannot help: X has points for
every DL-admissible pair by TYZ+GZ, so it can neither obstruct nor construct.
