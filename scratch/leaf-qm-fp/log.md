# leaf-qm-fp results log

Compile command: `lake env lean scratch/leaf-qm-fp/QMLeaves.lean` (one Lean process at a time).

## 2026-11-12

- 16:41 QMLeaves.lean §0-§3 (order copied from bp-qmmoduli, QMStr, K-rational Level3, QML3,
  Iso refl/symm/trans, isoSetoid, M3, twist/rightMul on objects and classes): COMPILES, 17 s.
  Change from bp-qmmoduli: `Level3.eta : 𝒪 →+ A(K)` (K-rational points), kernel exactly 3𝒪,
  no ontoness clause (equivalent in char 0 for surfaces, docstring), so base change needs no
  counting leaf.
- 16:47 §4-§6 added: QMPair/QMIso/pairSetoid/forget, com + HasCM4/3/24, `com_twist` (proved),
  `IsBaseChangeOf` / `IsBaseChangeOfPair` (pullback-square relation; no `A_L` object, no
  dimension lemma needed), `stab3`, `fieldOfModuli3`, `stabPair`, `fieldOfModuliPair`,
  `UnramifiedAbove5` (`p ∤ NumberField.discr`), `ToP1` (morphism to P¹ by two charts) and
  `ToP1.val` (via Mathlib `Scheme.SpecToEquivOfField`, `Scheme.evaluation`): COMPILES, 17 s.
