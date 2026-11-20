# Special-fibre quotient handoff

`PMQuotient.oddStagedOfGoodRows` constructs the (O.7) odd staged
instance with one fixed modular parametrization. At each detector prime,
`GoodRow` extends that map by the Néron property. The residue evaluation
defines the degree-zero quotient. The Hecke, Atkin–Lehner and Frobenius
equations, the selected CM point identity `hπ`, and the cusp annihilation
`hCusp` all use this quotient.

`Model`, `Operators`, `Cusps`, `CM` and `Assembly` each passed
`lake build`. The focused `#discharges` check matches
`Wiring.PreLeaves.odd_staged` and prints all 30 binders. The 25 axiom
checks, covering every new theorem, list only `propext`,
`Classical.choice` and `Quot.sound`. The first workspace build was stopped
after Lake launched uncached prerequisites in parallel; all passing
checks used a serial compiler in a 60 GB user scope.

The key remaining geometry is the good integral model with the actual
point and operator identifications. The constructor also needs the
generic signed and Hecke identities, the CM comparisons at the specified
place, the actual rational cuspidal classes and annihilator, and the
inherited theta coefficient and arithmetic inputs. No new printed
leaf. The two inherited citation errors are in
`.fleet/rc-pm-quotient2-verdict.md`; the theorem roadmap and exact
assumptions are in `docs/research/rc-pm-quotient.md` and
`scratch/rc-pm-quotient/log.md`.

Verified implementation and audit SHA: `57a0eb590bddbc942c422d3328f1d335eac1f490`.
Final SHA: `git log -1 --format=%H -- .fleet/rc-pm-quotient2.md`
(the handoff commit cannot contain its own literal hash).
