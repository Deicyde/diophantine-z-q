# Scoped CM field of definition at general level

`cmFieldOfDefinitionScoped_of_values` proves
`CMFieldOfDefinitionScoped (X0Branch.model N)` for every nonzero level from
the single input `HeegnerValuesInRingClassField N`. The proof uses the
local ring and residue field on the normalized curve. Every residue is
represented by a regular rational function, and its value agrees with the
finite analytic value of that modular function. Containment in the
specified embedding of the ring class field gives the field point under
that same embedding. The level-one specialization gives the same
statement as the independent singular modulus proof.

The three files in `ZInQKernel/Contrib/OneProof/RC/BranchDescends/` and the
standalone audit passed serial Lean checks. The definition and all six
new theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
No existing Lean files changed.

The sole remaining hypothesis is the value print, **GLUE until read**.
Tex 2915–2916 does not cite its field-of-definition assertion. The reading
desk should check the exact finite-value clause, the coefficient field,
and the coverage of nonmaximal orders with conductor prime to the level
in Shimura (1971), Ch. 6, Thm. 6.31 and the following CM results
(**UNVERIFIED**), and Gross (1984), §1 (**UNVERIFIED**). See the
[report](../docs/research/rc-branch-descends.md) for the check list and
manuscript audit.

Final proof and verification SHA: `864238e2fa00693b094b82e539c710c7b2215c45`. This handoff is the following commit.
