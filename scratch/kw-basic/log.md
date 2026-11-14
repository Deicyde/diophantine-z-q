# kw-basic results log

- 17:55 start. Plan: move the Mathlib-only declarations of Contrib/KroneckerWeber/Leaves.lean
  verbatim (same namespace, same names) into Basic.lean, add `KroneckerWeberCyclic` /
  `kroneckerWeber_cyclic` there; Leaves.lean imports Basic and proves the HDecomp statements by
  `Iff.rfl`. Downstream names (scratch/h-decomposition/Leaves.lean uses `kroneckerWeberCyclic`,
  `hSynKroneckerWeber`, `HSynKroneckerWeber`) unchanged.
- Tau Ceti closure of the TC KW module: 939 modules besides itself (task expected 5: the old
  `import`-only regex misses `public import`; see tc-closure.txt).
- Seeded TauCeti and HDecomp oleans from ../leaf-fold4 (cp -an, reflink).
