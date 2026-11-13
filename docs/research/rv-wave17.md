# rv-wave17: adversarial review of the wave-17 Lean statements

Status: review note (task rv-wave17, 2026-11-12). Lean: `scratch/rv-wave17/` (`Probe.lean`,
`T23i.lean`, the compile copies `chk/`), results log `scratch/rv-wave17/log.md`. No file under
`ZInQKernel/`, `blueprint/`, or another task's directory was edited.

Marks: **VERIFIED** = compiled, computed, or read in a source; **STANDARD** = published theorem;
**SPECULATIVE** = assessment. Theorem numbers from memory are UNVERIFIED (no network).

## Verdict

**Every statement reviewed is FAITHFUL.** No leaf is stronger than the published theorem. None is
vacuous, no glue hypothesis smuggles in its conclusion, and every glue hypothesis can be met. There
are two qualifications and one wording repair:

1. **T23 clause (i) is trivially true.** It is basis invariance of `IsDeRham`, and it has no
   continuity hypothesis. It is now proved in Lean from the definitions alone
   (`RvW17.t23_clause_i`, `scratch/rv-wave17/T23i.lean`, VERIFIED). It should be listed as glue,
   not as part of the literature leaf. Clauses (ii)-(v) carry Fontaine's content and are
   faithful. No Lean change to the leaf is required; dropping clause (i) is optional.
2. **C10's trace hypotheses need `S ⊇ {3, 5} ∪ {ramified primes}`.** The hypotheses
   `hr₃, hr₅, hρ₃, hρ₅` quantify over every Frobenius lift at `p ∉ S`. They can be met only when
   every `p ∉ S` is unramified for `r₃, r₅, ρ₃, ρ₅`; otherwise different lifts have different
   traces. `S` is a free parameter, so this is a usage condition, not a defect. It should be
   stated in the docstring.
3. **Wording repair, glue-c10's verdict.** "All of C10's glue is proved in Lean" overstates. The
   Galois-side glue is proved: Frobenius density, the transport from 5 to 3, and Brauer–Nesbitt in
   `G_ℚ`. The glue that links the ℓ-independent trace of `α_σ ∈ End⁰(Ā_v)` to `tr r_ℓ(g)` is not
   (`c_p = ½·β(σ)⁻¹a_σ·tr α_σ`; only the halving `trace_half` is in Lean). glue-c10's own §3
   item 3 says this. The headline should read: "C10's Galois-side glue is proved; the
   trace-linking computation remains (needs the Néron and Serre–Tate objects)."

All eight files compile with `lake env lean`, with no errors and no `sorry`. A command run over
every declaration of each file (`Lean.collectAxioms`, 583 declarations in total) finds only
`propext`, `Classical.choice` and `Quot.sound` (VERIFIED, `scratch/rv-wave17/chk/*.out`).

| Statement | File | Kind | Verdict |
|---|---|---|---|
| `LeafPush.R08_GrothendieckMonodromy` | leaf-push/Push.lean | leaf (C) | FAITHFUL |
| `LeafPush.T09_WeilPairing` | Push.lean | leaf (C) | FAITHFUL |
| `LeafPush.T29a_DivisionNormalizer` | Push.lean | leaf (E) | FAITHFUL |
| `LeafPush.T29b_SplitNormalizer` | Push.lean | leaf (E) | FAITHFUL |
| `LeafPush.T32a_TameQuadratic` | Push.lean | leaf (C) | FAITHFUL |
| `LeafPush.T32b_QuadraticRamification` | Push.lean | leaf (C) | FAITHFUL |
| `PkgI4.T23_FontaineClosure` | leaf-push/PushDR.lean | leaf (E) | FAITHFUL; clause (i) is glue (proved here) |
| `GlueC10.c10`, `iso_three_of_five` | glue-c10/C10.lean | glue | FAITHFUL to C10 (Galois side); usage note on `S` |
| `GlueC10.iso_of_trace_eq_on_frob`, `iso_of_trace_eq_frob_finite`, `eq_of_eq_on_frob`, `frobDense(_of_chebotarev)`, `frobLift` | C10.lean | glue | FAITHFUL |
| `GlueC10.trace_half`, `semisimple_of_le` | C10.lean | glue | FAITHFUL |
| `PkgI3.trace_indep_of_ell`, `trace_eq_trace_of_ell` | glue-c10/Trace.lean | glue | FAITHFUL |
| `GlueA6Alg.goodReduction_of_QM_rational3`, `…3'` | glue-a6-alg/A6.lean | glue | FAITHFUL to A6 = Lemma PR(ii) |
| `GlueA6Alg.quatUnipotentTrivial`, `core` | A6.lean, Quat.lean | glue | FAITHFUL (no hypotheses on the outside world) |
| `GlueA6Alg.exists_valuationSubring_comap_eq` | Extend.lean, A6.lean | glue | FAITHFUL |
| `GlueD1Local.D1_local`, `D1_local'`, `D1_krasner`, `D1_krasner'`, `ramificationIdx_le_factorial_local`, `index_localSub` | glue-d1-local/Local.lean | glue | FAITHFUL to D1 |

## 1. Leaves of leaf-push

**R8.** For every field `K` with a DVR `O`, every valuation ring `w` of `K̄` over `O`, and every
abelian variety `A/K`, there is a finite `K' ⊆ K̄` such that every inertia element of `w` fixing
`K'` satisfies `(σ−1)² = 0` on `A(K̄)[ℓⁿ]`, for every prime `ℓ` invertible in `O`.
- Published source: SGA 7 IX Thm 3.6 (semistable over a finite `K'`) with the direction
  "semistable ⇒ unipotent of echelon 2" of Prop. 3.5, applied over `K'` (numbers UNVERIFIED).
- The inertia group of `w ∩ K'` is `I_w ∩ Aut(K̄/K')`, because Mathlib's inertia is the kernel
  of the action of the stabilizer of `w` on the residue field of `w`, the same for `K` and `K'`
  (VERIFIED by reading `RamificationGroup.lean` L49-51).
- `IsUnit (ℓ : O)` is exactly "`ℓ` ≠ residue characteristic".
- One `K'` serves every `ℓ`, as semistability does.
- `galAct σ x = Spec(σ) ≫ x` has coordinates `σ ∘ x^*`, which is the classical `σ(P)`.
- `UnipSq` is `σ²x − 2σx + x = 0` written multiplicatively.
- Same body as pkg-I2's `GrothendieckMonodromy` (read side by side). Consequence, never stronger.

**T9.** Statement: `∃ d ≥ 1, ∃ e` such that, for every `n` invertible in `K`, on `A[n]` the
pairing has values in `μ_n`, is bimultiplicative and alternating, has left kernel killed by `d`,
is Galois-equivariant, and satisfies `e_n(x^m, y^m) = e_{mn}(x, y)^m`. Each clause is checked
for `e_n(x, y) := e_n(x, λy)` with `λ = φ_L`, `L` ample over `K` (Mumford §§20, 23; UNVERIFIED
numbers):
- *Compatibility.* `e_{mn}(x, y)^m = e_{mn}(x, my) = e_n(mx, my)`, by the rule
  `e_{mn}(x, z) = e_n(mx, z)` for `z ∈ Â[n]`. Correct direction.
- *Kernel.* If `ker λ ⊆ A[d]`, then `[d] = ψλ` for some `ψ`. Then `λψλ = λ[d] = [d]λ`, and
  `λ` is onto, so `λψ = [d]`. Hence `dÂ[n] ⊆ λ(A[n])`, and perfectness of `e_n` gives `dx = 0`.
- *Equivariance.* Holds because `λ` is defined over `K`.
- *Alternating.* `e^{φ_L}_n(x, x) = 1`.
- *Not trivially true.* `e ≡ 1` fails the kernel clause as soon as some `A[n] ≠ 0` with
  `gcd(n, d) = 1`.
- *Use at C8.* The limit `GSp` statement can be derived. Compatibility makes the pairings at
  levels `ℓᵏ` a system in `ℤ_ℓ(1)`. An element of the left kernel on `T_ℓ` has `d·x_k = 0` at
  every level, hence is zero, since `T_ℓ` is torsion-free and `T_ℓ → A[ℓᵏ]` is onto
  (TorsionStructure). (SPECULATIVE until written; glue.)

**T29a.** Hypothesis: the norm form of `ℍ[ℚ_p, a, b]` is anisotropic, i.e. the algebra is a
division algebra.
- The notation is right: `ℍ[ℚ_p, a, b] = QuaternionAlgebra ℚ_p a 0 b` with `i² = a`
  (VERIFIED, Probe P3).
- The hypothesis can be met: `(u, p)` with `u` a nonsquare unit (`p` odd); `(−1, −1)` at `2`.
- Each conclusion is true. Integral elements form the valuation ring of `v ∘ nrd`. For `π` with
  `v(nrd π) = 1`: `π ≠ c·u`, since `v(nrd(c·u)) = 2v(c)` is even. Every `x ≠ 0` is `π^k u`, and
  `π² = p·unit`. Exact.

**T29b.** The hypothesis `∀ m, m ∈ M₂(ℤ_p) ↔ g m g⁻¹ ∈ M₂(ℤ_p)` is "`g` normalizes
`M₂(ℤ_p)`". The conclusion `g ∈ ℚ_p^× GL₂(ℤ_p)` is the published statement. Exact.

**T32a.** For `p` odd and `w | p`: `#{continuous χ : I_w →* ℤˣ} = 2`.
- The topologies are right. `G_ℚ` carries `krullTopology ℚ ℚ̄` (`rfl`, Probe P1), and `ℤˣ` is
  discrete (P2).
- The count is true. A continuous character to `±1` kills the pro-`p` wild inertia (`p` odd)
  and factors through `∏_{ℓ≠p} ℤ_ℓ(1)`, where `Hom(−, ℤ/2) = ℤ/2`.
- `IsAtPrime` singles out `ℤ_(p)`. `ℚ` itself is not a DVR, and `p` is a unit in `ℤ_(q)` for
  `q ≠ p`.
- The identification `I_w ≅ I(ℚ̄_p/ℚ_p)` is part of the cited content, as leaf-push §4 says.
  Consequence.

**T32b.** Statement: for `d ≡ 1 mod 4` squarefree and `s² = d`, some inertia element moves `s`
iff `p | d`.
- `d % 4 = 1` admits negative `d`, e.g. `−3` (P4).
- `d = 1` is consistent (P5).
- At `p = 2`: `d` is odd and `≡ 1 mod 4`, so `2` is unramified in `ℚ(√d)`, and both sides are
  false.
- The statement follows from `disc ℚ(√d) = d`. Consequence.

**T23.**
- *Clause (i)* is a triviality. `RvW17.t23_clause_i` proves it for every homomorphism `ρ`,
  continuous or not: `φ ↦ φ ∘ P⁻¹` is a linear isomorphism `D(ρ) ≃ D(PρP⁻¹)` (VERIFIED,
  `T23i.lean`, axioms standard). Harmless, but it is glue.
- *Clauses (ii)-(v)* each assume continuity of the inputs; continuity of the outputs follows.
  `IsDeRham` is stated for `V^∨` (dimension of `Hom_G(V, B_dR)`). Clause (ii) uses
  "`V` de Rham ⇔ `V^∨` de Rham", which is part of the same closure theorem.
- *Block conventions checked.* `reindex finSumFinEquiv` puts the first `a` coordinates first.
  The zero block is the `(inr, inl)` corner. So `span(e₁, …, e_a)` is stable: `ρ₁` is the sub,
  `ρ₂` the quotient.
- *Faithful,* with one dependency. The content depends on pkg-I4's `B_dR` and `bdrAct` being the
  genuine ones; this review does not re-examine them. With a degenerate action, T23 would remain
  true but mean something else (e.g. a trivial action makes "de Rham" mean "trivial").

## 2. Glue

**C10 (`GlueC10.c10`).**
- What the step needs: h-trust C10 identifies `r₃` with `ρ_{f,ι₃}` through one compatible
  system: common `c_p` and `a_p` in the coefficient field, Chebotarev, then Brauer–Nesbitt.
- What `c10` proves: exactly that, as an isomorphism of `k[G_ℚ]`-modules. Its inputs are the
  trace identities at every Frobenius at `p ∉ S`, `C9`'s trace equality at 5, continuity and
  semisimplicity.
- Nothing is smuggled. The conclusion uses the 5-adic equality only through
  `ι₅(c_p) = ι₅(a_p) ⇒ c_p = a_p`, by injectivity of `ι₅`.
- The hypotheses can be met, with `S` as in qualification 2. `IsFrobAt g p` holds for some `g`
  at every `p` (glue-c10 §2.5), so the trace hypotheses are not empty.
- The copied leaves `ChebotarevExists` and `BrauerNesbittChar0` are verbatim from pkg-I6 (VERIFIED, `diff`). `BrauerNesbittChar0` for an arbitrary group `G` is true in
  characteristic 0: semisimple modules over the finite-dimensional image algebra are determined
  by their characters (STANDARD; Curtis–Reiner, locator UNVERIFIED).
- `PkgI3.trace_indep_of_ell` is a correct consequence of `CharPolyIndepOfEll`:
  `tr = −nextCoeff(charpoly)`.

**A6 (`goodReduction_of_QM_rational3'`).**
- Hypotheses: an abelian surface `A/K` (`hdim = 2`); `I, J ∈ End_K(A)` with `I² = 2`,
  `J² = −3` and `JI = −IJ` on `K̄`-points; `3 ∈ O^×`; `A[3] ⊆ A(K)`.
- Conclusion: `A` has good reduction at `O`. This is Lemma PR(ii) at a place `v ∤ 3`, including
  `v | 2`.
- The relations are those of N5's algebra. The Hilbert symbols `(2, −3)_2 = (2, −3)_3 = −1`
  give discriminant 6 (computed by hand: `(2/3) = −1`; `(2, 5)_2 = −1`). By Eichler, every
  maximal order of this indefinite algebra contains a conjugate of `ℤ⟨i, j⟩`. So
  `𝒪_B ⊆ End_K(A)` supplies `I, J`.
- That `ι` is defined over `K` is N5's data (rv-a6-route L73).
- The copied leaves are identical to pkg-I2 (VERIFIED, `diff`).
- `quatUnipotentTrivial` and `exists_valuationSubring_comap_eq` are theorems with no hypotheses
  about the outside world.

**D1 (`D1_local'`, `D1_krasner'`).**
- What the step needs: `u_last ≤ 4a²` from a local degree `[F:ℚ_p] ≤ a`, through
  `e ≤ |Gal(F̃/ℚ_p)| ≤ a!`, Serre's different bound and Herbrand.
- What the Lean proves: `D_P` plays `Gal(F̃/ℚ_p)`; trivial core of `D_P ∩ Gal(L/K)` plays
  "`L_P = F̃`"; `e(w|p)f(w|p) ≤ a` plays the local degree. The conclusion `φ(b) ≤ 4a²`, for every
  `b` with `G_b ≠ 1`, is the bound on the last upper break.
- The hypotheses can be met, e.g. `K = L` with `|D_P| ≤ a`, or the Krasner choice.
- The leaves are identical to glue-conductor's (VERIFIED, `diff`).
- As the note says, the completion and Krasner transports are not in Lean.

## 3. What remains (not done here)

- The faithfulness of the copied leaves of earlier packages (pkg-I2, pkg-I3, pkg-I4's `B_dR`,
  pkg-I6, glue-conductor) was taken from their reviews and not re-examined. Only the copies were
  diffed.
- T9's `GSp` limit and the C10 trace link are glue that is still unwritten.
