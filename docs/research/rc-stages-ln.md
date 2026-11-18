# Ring class field notation in the RC stages

At `ZInQKernel/Contrib/OneProof/RC/Stages/ExactGenus.lean:21` in the base revision,
the local notation `H` expanded to `ringClassField (conductorOrder K c)`.
The expansion was inlined in every affected statement and proof. The separate
`let H` bindings in `exact_twist_of_genusPoint` were left as they were.

`ExactGenus.lean` compiled before and after the edit with serial `lake env` Lean
runs. Both runs reported the same existing linter warnings. The output of
`scratch/rc-stages-ln/Check.lean` was byte-for-byte identical before and after
for all four theorems (`pp.notation false`, `pp.explicit true`). The four
`#print axioms` checks each reported only `propext`, `Classical.choice`, and
`Quot.sound`.

`git grep` found no remaining `local notation` under
`ZInQKernel/Contrib/OneProof/RC/Stages/`. It found no `local infix`, `local macro`,
`scoped notation`, or `notation3` declarations there. The existing `open scoped`
commands and the `local instance` at `ZInQKernel/Contrib/OneProof/RC/Stages/Lattice.lean:10`
were left unchanged.
