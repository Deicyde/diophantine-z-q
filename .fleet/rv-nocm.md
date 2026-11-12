# rv-nocm (fleet report)

**Verdicts** (full report: `docs/research/rv-nocm.md`):

- **(1) NoCM (A10): HOLDS AFTER REPAIRS.** The leaf statements need repair; the argument does not.
  - Neither proof uses the unqualified count. h-cm uses `#CM = 2^b h`, with `W'×Pic` simply
    transitive. The adopted rv-h-cm §7.2 uses `#CM = h` only when `D(R) = 1`, where `b = 0`.
  - Every field claim is on `X₆ = X₀(6,1)`, never on `X₆/W` or `Y₃`.
  - But the leaf "`#CM(R) = h(R)` for `(f,6) = 1`" (h-decomposition R5, glue-repo L14,
    `R05_GonzalezRotger` docstring, hdec-elementary L3) is **false**. It fails in 15 of the 24
    rows of Elkies' table, and at `ℤ[i]` (`h = 1`, two points). It must be restated as
    `2^{b(R)} h(R)` before any Lean leaf is written. The exact text is in §3.1.
  - One justification is added to the case `D(R) ≠ 1`: `CM(ℤ[i])` is the fibre over `t = 1`.
- **(2) A5: HOLDS AFTER REPAIRS.** Again, only the supplier's wording.
  - A5 needs the indices of `Y₃ → P¹_j`. These are the orbifold orders `(4,6,2)` of `Γ*`,
    because `Γ₃` is torsion-free and normal (manuscript L480-482).
  - The audit's `(2,2,2)` are the indices of `X₆ → X₆/W`, which Lemma NV step 4 uses correctly.
  - The leaf texts "`X₆/W` branched with indices 4,6,2" (R2, glue-repo L2, `R02` docstring, A2
    rows) must say "orbifold orders", with the index of `Y₃ → P¹_j` as glue. The exact text is
    in §3.2.

**Compiles** (`lake env lean`, no sorry, standard axioms):

- `scratch/rv-nocm/OrbifoldIndex.lean`:
  - `ramification_eq_orbifold_order`: for a group action with `N` normal and torsion-free, the
    ramification index `[Stab(Nx) : N]` equals `|Stab(x)|`;
  - the Riemann–Hurwitz checks: genus 4 for indices `(4,6,2)`, and `(2,2,2)` impossible;
  - `labelling`: only `(4,6,2)` works for Lemma PR(i);
  - `inertia_trivial_of_dvd`: the needed direction is robust.
- `scratch/rv-nocm/Neat.lean`: `eq_zero_of_pow_eq_one`, i.e. `1 + 3𝒪` has no nontrivial
  torsion in `ℍ[ℚ,2,0,−3]`. This is the neatness hypothesis for `Γ₃`.

**Computed** (`scratch/rv-nocm/nocm_check.py`, pure Python, since PARI was unavailable):

- the count, with and without the orientation factor, on Elkies' table;
- the `X₆` fibre fields against GR Thm 5.12;
- the audit's `D = −24` example;
- `|(𝒪/3𝒪)^*| = 72`, `[Γ*:Γ₃] = 72`.

**Remains:**

- The primary texts (González–Rotger, Baba–Granath, Elkies) were not read here (no access).
- The signature `(0;2,4,6)` of `Γ*` is cited, not proved.
- Instantiating the group lemma on `Γ*` acting on `ℍ` needs R1's objects.
- The repairs in §3 are to be applied to the other tasks' files at integration.
