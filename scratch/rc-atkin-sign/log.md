# Atkin sign results

- Base: `1171720c3a809ff7c790223517be48c77a90189a`.
- Finding: `O7Assemble.actualStage` and `ThetaClose.actualPmLocal` take `w : ℕ → ℤˣ` as data. `levelRoots_parity` uses that input.
- Finding: `HeckeRing.GL2.Newform.atkinLehnerSign` gives the analytic sign at an exact divisor. No theorem matching it with the rational parametrization and its specialization was found.
- Finding: uniqueness of ±1 on a reduced point would require `2 • P ≠ 0`, not only `P ≠ 0`. No such premise added.
- Case: (b). `SpecialFibreAtSigns … w` states the Atkin quotient identity at the same points, with `(w p : ℤ)` as scalar (ELLIOT, tex 8487–8489).
- `toSpecialFibre`: copies the other fields and sets `atkinSign p := (w p : ℤ)`. `atkinSign_eq`: the resulting equality holds by `rfl`. `ofSpecialFibre`: the old fibre and its level sign agreement give the new input.
- `actualRowFamily`: the same `DatumAt` for each admissible index and the same cusp and point inputs. `oddStagedActual`: `Nonempty (OddStagedInstance W)` with the same coefficient, torsion and odd-sign inputs.
- Builds: `AtkinSign.Geometry` PASS; `AtkinSign.Family` PASS. Separate `lake build` targets, using the unchanged base artifacts, serial within the 60 GB scope.
- Axioms: `SpecialFibreAtSigns`, `toSpecialFibre`, `atkinSign_eq`, `ofSpecialFibre`, `actualRowFamily`, and `oddStagedActual` each use `propext`, `Classical.choice`, `Quot.sound`.
- Inherited source issue: the Jetchev–Kane citation at tex 8468–8474 does not cover level one; source locators UNVERIFIED.
