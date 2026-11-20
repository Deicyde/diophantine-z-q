# Conductor-one CM trace

**Scoped stop.** The existing pole dictionary and the proposed general
dictionary remain open. Even with a conductor-one reciprocity reading,
two separate comparisons are outstanding: selecting and evaluating the
CM branch in the canonical modular curve model, and comparing the
normalized algebraic parametrization at the conductor with `CST.phiAn`.
This exceeds the one-GLUE limit. The pole predicate additionally needs a
non-CM period lattice; the general consumers include CM target curves.

No new manuscript error was found. The report records the preprint's
implicit weak Weil premise and the previously identified apparent typo
in the Shimura 1973 eigenvector relation. The proposed reciprocity and
conjugation locators remain unverified.

`TraceDescent.lean` proves that the unaveraged sum of the conjugates of
a supplied point descends uniquely. The Lean dry run specializes this
to the actual Hilbert class field, reindexes using Tau Ceti's Artin
equivalence, and checks the exact pole predicate and assembly. All five
checked declarations use only the three standard axioms. The rank-zero
forward substitution beyond the trace is a source audit. The headline
and both consumers are unchanged.

The initial dependency build bypassed the lock and violated the serial
worker constraint. It was stopped, and the final build and proof checks
used the corrected locking wrapper.

See [the report](../docs/research/cm-trace-dictionary.md) and
[the axiom output](../scratch/cm-trace-dictionary/axioms-output.txt).
