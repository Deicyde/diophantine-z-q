# rv-wave17 results log

## Compile runs (VERIFIED, Lean 4.35.0 / Mathlib v4.35.0, `lake env lean`, one process at a time)

Each reviewed file was copied to `scratch/rv-wave17/chk/<task>_<file>.lean` with
`chk/tail.lean` appended. The tail is a command that runs `Lean.collectAxioms` on every
declaration of the file and reports any axiom other than propext, Classical.choice, Quot.sound.
Outputs are in `chk/*.out` and timings in `chk/status.txt`.

| File | exit | decls checked | nonstandard axioms | errors | warnings |
|---|---|---|---|---|---|
| leaf-push/Push.lean | 0 | 40 | 0 | 0 | 0 |
| leaf-push/PushDR.lean | 0 | 206 | 0 | 0 | 0 |
| glue-c10/C10.lean | 0 | 38 | 0 | 0 | 2 deprecations |
| glue-c10/Trace.lean | 0 | 68 | 0 | 0 | 1 unused variable |
| glue-a6-alg/A6.lean | 0 | 117 | 0 | 0 | 0 |
| glue-a6-alg/Quat.lean | 0 | 61 | 0 | 0 | 0 |
| glue-a6-alg/Extend.lean | 0 | 3 | 0 | 0 | 0 |
| glue-d1-local/Local.lean | 0 | 50 | 0 | 0 | 0 |
| glue-c10/Lift.lean (extra) | 0 | 22 | 0 | 0 | 0 |

The files' own `#print axioms` lines all print `[propext, Classical.choice, Quot.sound]`
(c10, iso_three_of_five, frobLift, frobDense, trace_indep_of_ell, quatUnipotentTrivial,
goodReduction_of_QM_rational3(') , exists_valuationSubring_algebraicClosure, D1_local('),
D1_krasner(') and the rest).

## Copy checks (VERIFIED, diff)
- A6.lean's leaves (NeronOggShafarevich ... TorsionStructure) are identical to pkg-I2/I2.lean.
- A6.lean's and Quat.lean's `QuatUnipotentTrivial` are the same definition.
- Local.lean's HilbertDifferentFormula, SerreDifferentBound, D1_genuine are identical to
  glue-conductor/Breaks.lean.
- Push.lean's `R08_GrothendieckMonodromy` has the same body as pkg-I2's `GrothendieckMonodromy`
  (read side by side).

## Probes (VERIFIED, scratch/rv-wave17/Probe.lean, compiles)
- P1: the topology on `G_ℚ` in T32a is `krullTopology ℚ ℚ̄` (`rfl`).
- P2: `ℤˣ` is discrete (instance found).
- P3: `ℍ[ℚ_p,a,b] = QuaternionAlgebra ℚ_p a 0 b` (`rfl`), and `i·i = a`.
- P4: `(-3) % 4 = 1`, so T32b admits negative `d` (the `ℚ(√-3)` case).
- P5: T32b at `d = 1` is consistent.
- Mathlib's `ValuationSubring.inertiaSubgroup` is the kernel of the action of the decomposition
  group on the residue field (read: RamificationGroup.lean L49-51).

## New Lean (VERIFIED, scratch/rv-wave17/T23i.lean, compiles, axioms standard)
- `RvW17.t23_clause_i`: clause (i) of `PkgI4.T23_FontaineClosure` (basis invariance of
  `IsDeRham`), proved for every homomorphism, continuous or not, from the definitions alone.
  So clause (i) is glue, not literature content.

## Findings (statement by statement)
- R8 `R08_GrothendieckMonodromy`: FAITHFUL (consequence of SGA 7 IX 3.6 + 3.5; identical to the
  already reviewed pkg-I2 leaf).
- T9 `T09_WeilPairing`: FAITHFUL (consequence). Every clause checked against `e^λ_n(x,y) =
  e_n(x, λy)`; compatibility direction `e_n(x^m,y^m) = e_{mn}(x,y)^m` correct; kernel clause
  correct via `λψ = [d]`. Not trivially true: `e ≡ 1` fails the kernel clause once `A[n] ≠ 0` with
  `(n,d) = 1`.
- T29a, T29b: FAITHFUL (exact). Division hypothesis satisfiable (e.g. `(u,p)` with `u` a
  nonsquare unit, `p` odd; `(-1,-1)` at 2).
- T32a, T32b: FAITHFUL (consequence). The topology is Krull (P1), and inertia is Mathlib's (read).
- T23: FAITHFUL; clause (i) is trivially true (proved here, T23i.lean), clauses (ii)-(v) carry
  the content. Inherits pkg-I4's `B_dR` and `bdrAct`: if those were degenerate, T23 would still
  be true but mean something else.
- C10 `GlueC10.c10` (+ `iso_three_of_five`, `iso_of_trace_eq_on_frob`, `frobLift`, `frobDense`):
  FAITHFUL to h-trust C10. Usage note: the trace hypotheses can be met only if `S` contains 3, 5
  and every prime where `r₃, r₅, ρ₃, ρ₅` ramify (otherwise the trace at different Frobenius lifts
  differs). `S` is a free parameter, so this is a usage condition, not a defect.
- `PkgI3.trace_indep_of_ell`: FAITHFUL (glue from Mumford §19 Thm 4).
- A6 `goodReduction_of_QM_rational3'`: FAITHFUL to Lemma PR(ii). `(2,-3)_ℚ` has discriminant 6
  (Hilbert symbols at 2 and 3 are -1), so the relations `I²=2, J²=-3, IJ=-JI` describe the order
  of N5's algebra up to conjugacy. The hypotheses need `I, J` defined over `K`; rv-a6-route L73
  records this as N5's data.
- `quatUnipotentTrivial`, `exists_valuationSubring_comap_eq`: theorems with no hypotheses
  (FAITHFUL; nothing to smuggle).
- D1 `D1_local`, `D1_local'`, `D1_krasner`, `D1_krasner'`: FAITHFUL to h-trust D1 (the bound
  `u_last ≤ 4a²` from local degree `≤ a`). The two transports (completion, Krasner) are not in
  Lean, as the note says.
- C10.lean's ChebotarevExists, BrauerNesbittChar0 identical to pkg-I6/I6.lean (VERIFIED, diff).
- glue-c10/Lift.lean (extra): exit 0, 22 decls, 0 nonstandard axioms (VERIFIED, chk/glue-c10_Lift.out).
