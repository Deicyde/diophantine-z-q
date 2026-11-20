Scoped stop: the two theorems account for extension and reduction of
the fixed modular map once the integral geometry is identified. The
present Lean interfaces do not identify the supplied PM quotient with
the reduction of that map. The Néron property for the good target is
already proved. No new printed leaf was added; the Deligne–Rapoport
locator is UNVERIFIED.

`GoodReduction.Integral`, `GoodReduction.Row` and
`GoodReduction.Atkin` build. The new proofs give the unique extension
to a supplied good group model, lifts of the field points by properness,
and the specialization of the signed identity with cancellation of its
translation on degree-zero divisors. The pointwise reduction theorem
concludes the exact `hπ` goal once the diagram is supplied, as checked
at the actual row in the scratch consumer. The six theorem audits use
only `propext`, `Classical.choice`, and `Quot.sound`.

The missing geometry is the compactified coarse modular model aligned
with the rational normalization, the cusp and integral Atkin–Lehner
operator aligned with their coarse readings, and the good target group
scheme with its coordinate reduction. The PM based divisor value must
be read from that same specialized map. The chosen CM point and place,
generic sign, and cusp annihilation remain separate inputs. See
`docs/research/rc-good-reduction.md` for the exact comparisons and the
input table.

Inherited citation issues: the Jetchev–Kane passage at tex 8468–8474
omits level one, and the Milne locators at tex 1784–1788 do not supply
the newform and Hecke assertions. The Cornut–Jetchev citation is to a
preprint; no refereed replacement was verified.

Final implementation and report SHA:
`6097f7159095040488e998c1ef30361195ad7dba`.
The final handoff commit SHA is returned by
`git log -1 --format=%H -- .fleet/rc-good-reduction.md`.
