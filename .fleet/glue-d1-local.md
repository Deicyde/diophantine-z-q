# glue-d1-local (2026-11-11)

**Result.** D1's degree bound is proved in its local form, through the decomposition group,
and connected to glue-conductor's `D1_genuine`. File: `scratch/glue-d1-local/Local.lean`
(glue-conductor's `Breaks.lean` copied, plus namespace `GlueD1Local`). Compiles with no errors
or warnings; axioms only `propext`, `Classical.choice`, `Quot.sound` (VERIFIED, 23:49 PST).

What compiles (all over Mathlib's `Gal(L/ℚ)`, `MulAction.stabilizer`, `Ideal.inertia`,
`ramificationIdx`, `inertiaDeg`, `normalClosure`):
- `e(P|p) ≤ |D_P|`, `|D_P| = e·f`, and `[D_P : D_P ∩ Gal(L/K)] = e(w|p)·f(w|p)` for `w = P ∩ 𝓞K`
  (the local degree `[K_w:ℚ_p]`).
- `|D| ≤ [D:H]!` when `core_D(H) = ⊥` (the local Galois closure condition).
- `ramificationIdx_le_factorial_local`, `D1_local`, `D1_local'`: `L_P` is the Galois closure of `K_w`
  (trivial core) and `e(w|p) f(w|p) ≤ a` ⇒ `e(P|p) ≤ a!` and `φ(b) ≤ 4a²`.
- Krasner-type form `D1_krasner'`: `normalClosure ℚ K L = ⊤`, `K` has a single prime over `p`,
  `e(w|p) f(w|p) ≤ a` ⇒ the core condition holds, so `e(P|p) ≤ a!` and `φ(b) ≤ 4a²`.

What remains (STANDARD, not in Mathlib, prose in docs/research/glue-d1-local.md §2):
Krasner's choice of a global `K` with one prime over `p` and `K_w ≅ F`, and `D_P ≅ Gal(L_P/ℚ_p)`
with ramification filtrations (the second is already assumed by `D1_genuine`). Integration:
drop the copied `Breaks.lean` and place `GlueD1Local` after `D1_genuine`.

Report: docs/research/glue-d1-local.md. Log: scratch/glue-d1-local/log.md.
