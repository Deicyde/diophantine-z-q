# rc-pool-character

Implementation, report and results log SHA: 94d0dab9a7db2841a1ad41ce8c5c51a025398cc2.
The final branch SHA is the commit adding this handoff; read it with
`git log -1 --format=%H -- .fleet/rc-pool-character.md`.

The empty moving-set diamond scalar on the actual pool is the embedded
`Lift.η(d)` times `Jacobi(-1,d)`, with `d` the canonical unit residue of
the existing common level. `oldCharacter_comp_eq_bCharacter_of_phase`
supplies `hchar` to `oldStageLaw_of_finiteAction` when the pool uses the
phase constructed from the same local scaling characters and the genus
character of (O.5), with one coefficient embedding.

For the prescribed local factors at the extraction primes, their product
cancels the genus character. The exact remaining comparison for an
independently supplied lift is that its embedded phase on common units
equals the product of the root characters at the elliptic conductor and
the detecting-prime quadratic character. This is the manuscript's phase
definition (tex 8903–8923, 8982–8985), carried unchanged through the pool
(tex 9706–9710). The open comparison is in the stage interface: the given
`Lift.phase` only records reduction to the finite stage. The stage join can
choose the phase by construction and verify the existing reduction.
The local scaling data, conductor and depth bounds, stage grid, and finite
action stay with their existing inputs.

Both files in `ZInQKernel/Contrib/OneProof/RC/PoolCharacter/` pass serial
`lake env lean`. All six theorem audits use only `propext`,
`Classical.choice`, and `Quot.sound`. No print was added and no manuscript
error was found in scope. The exact statements and manuscript check are
in `docs/research/rc-pool-character.md`.
