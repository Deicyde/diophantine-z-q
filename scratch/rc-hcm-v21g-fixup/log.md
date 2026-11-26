# rc-hcm-v21g-fixup results log

## Setup
- merge-base check: 94cd18fe ancestor of 796582ac: OK; GoodRowWire/Assembly.lean and SamePlace.lean present at 796582ac: OK.
- merged 796582ac into wip/rc-hcm-v21g (commit 641c9eccc).

## Item 1 (O threading)
- RC/GoodRowWire/Assembly.lean: binder `O : ∀ i, PMAdelic.OperatorComparison … (J i)` after `J`; `Reference … J O …`, `referenceComparisons … J O …`; `(fun i => adaptOperators (O i))` after each `adaptComparison` (actualRows, actualRowFamily, pointInputs, actualFamily); `(O := O)` in hCuspAt and oddStagedOfGoodRows. Locator :220 -> :222.
- build GoodRowWire.Assembly: OK (13747 jobs), oddStagedOfSamePlace typechecks; axioms propext, Classical.choice, Quot.sound.
