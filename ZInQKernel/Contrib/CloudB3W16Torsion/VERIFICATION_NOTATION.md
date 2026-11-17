# Degree-source notation expansion

The local `⊚` infix declaration in
`S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero.lean`
is removed. All uses are expanded literally to
`NeronModelInfra.schemeHomOverComp`, with parentheses preserving the original
application and multiplication precedence. No definition, telescope or hypothesis
is replaced. The C32-owned finite-end-kernel module is cleaned by its own author,
not edited by the primary after ownership transfer.

An isolated scratch imports the actual relative-law, group-object, end-kernel,
endomorphism-extension and end-degree definitions, and recompiles the changed
point-composition proofs. `lake env lean -M16000 DegreeNoNotationCheck.lean`
returns0,4.75s,6903328KiB peak RSS. Actual kernel outputs:

```
'DegreeNoNotationCheck.compT_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'DegreeNoNotationCheck.compT_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DegreeNoNotationCheck.comp_idPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'DegreeNoNotationCheck.isHom_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This verifies the changed composition-prefix proofs, not the entire degree
provider or final Mumford leaf. The full degree/cardinality root remains pending
repair of later Picard/cube prerequisites. It is never made an extra hypothesis.
