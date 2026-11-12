# glue-rho-cont: summary

**Result: done, compiled, no sorry.** pkg-I3's `ρ_ℓ` (`galRep`) is continuous. This closes
the gap rv-leaves-b flagged for C10, over pkg-I3's unchanged definitions
(scratch/glue-rho-cont/RhoCont.lean; sections 1-2 are a verbatim copy of I3.lean lines 15-335).

What compiles (Lean 4.35 / Mathlib v4.35; 0 errors, 0 warnings; axioms propext,
Classical.choice, Quot.sound):
- `exists_openSubgroup_galAct_eq`: each point of `A(K̄)` is fixed by `Gal(K̄/E)` for some finite
  `E/K`, an open subgroup. The proof uses the stalk map at the point; stalk maps are essentially
  of finite type because `A → Spec K` is locally of finite type (`RingHom.EssFiniteType.ext`).
- `continuous_galT` (unconditional): `G_K × T_ℓ(A) → T_ℓ(A)` is continuous. `T_ℓ` carries the
  inverse-limit topology (subspace of `ℕ → A(K̄)`, discrete factors).
  `nhds_zero_hasBasis` / `coord_eq_zero_iff` show that this topology is the `ℓ`-adic one.
- `continuous_galRep`, `continuous_toMatrix_galRep` (any basis), `continuous_trace_galRep`:
  if `T_ℓ(A)` is free of finite rank, `ρ_ℓ` on `V_ℓ(A)` (Mathlib's module topology over `ℚ_ℓ`)
  is jointly continuous, continuous as a matrix-valued map, and has continuous traces.
- `continuous_galRep_of_tateModuleFree`: the same, from the existing leaf I3.M0, for
  `(ℓ : K) ≠ 0`. **No new leaf is needed for the continuity in C10.**

What remains: integration into the kernel together with pkg-I3, keeping the two topology
instances (discrete on `A(K̄)`, module topology on `V_ℓ`) scoped. C10 itself (Chebotarev,
Brauer–Nesbitt) is out of scope. Compactness of `T_ℓ(A)` is not needed and not proved.

Report: docs/research/glue-rho-cont.md; log: scratch/glue-rho-cont/log.md.
