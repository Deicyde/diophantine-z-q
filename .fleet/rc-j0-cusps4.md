# rc-j0-cusps4

**Proved the fixed projective Weierstrass group law over ℚ.**
`projectiveGroup_exists` proves the exact existence statement in the
previous report, including that multiplication evaluates to Weierstrass
addition on complex points. The two multiplication triples cover the
secant and tangent cases; affine localization and gluing give morphisms
for multiplication and inversion. The unit is the existing rational
section at infinity. The group diagrams follow from the field point laws
by reducedness and separatedness. The preceding period homeomorphism
therefore identifies the complex point law with addition in `ℂ/Lat`.

`hElkikMD_atScale` discharges the group input to
`hElkikMD_atScale_of_projectiveGroup`. At the given rational scale the
inherited comparison uses the represented `J₀(N)(Qbar)` and the actual
geometric cusp classes, and supplies the scaled cusp identity at every
nonzero quadratic weight. The wrapper still takes the existing newform,
periods, genus partner, and geometric cusp torsion print.

The scale witness `∃ c : ℚ, (c : ℂ) = κ` remains explicit. The independent
rational maps `q_f`, `α` and their comparison on the width one cusp tail
remain in the scale rationality lane. No new manuscript error was found.

The imports built and all seven new Lean files passed serial standalone
checks. All 61 axiom audits use only `propext`, `Classical.choice`, and
`Quot.sound`. No inherited file or printed input changed.

Result and report SHA: `61d2cb4e1932fa38177d187549467bc46e258e93`.
Report: `docs/research/rc-j0-cusps4.md`. Log: `scratch/rc-j0-cusps4/log.md`.
