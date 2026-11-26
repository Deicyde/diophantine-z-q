# Cai–Chen–Liu retirement rebuild

Lean tree `f5299bb9d6f9ada2fcd170099f784f0e0945bf79` includes pinned main
`29bfbc3f6793d98b7c1ac637f9728fe51e701e5b` and the two review docstring
fixes. All 47 Lake targets passed, including the nine downstream modules.
The 21-declaration axiom check includes `ZInQ.OneProof.frozenTarget` and
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The import closures of `OneProof.Main` and the type of `hRC` contain
10,587 and 380 project modules respectively. Both sets match pinned main
and exclude every changed or deleted module. Count lowered **none**.
[Report](../docs/research/ccl-retire.md) ·
[Verification log](../scratch/ccl-retire4/log.md)
