# T21 — INTEGRATION ADDENDUM: read-only proof-integration review of the author's frozen source packet

Preliminary non-author review. The reviewer is NOT a designated Astra agent; serving identity
unknown. Not acceptance, not registration, not a mathematical human approval. This addendum does
NOT replace or amend the historical files: `INITIAL.md` (SHA-256
`3650d9a0efd8aeff707e3384a0bf8d2feb412f4033d719c445f14c97f281b71d`) and `REPORT.md` (SHA-256
`4afd19a3a410a0cdc864ae03d03fcd6ea7a72792b64dc20ccf0235a00a1abfdb`) stand as written; their
statement/source verdicts are unchanged.

## 0. Object reviewed and integrity

* Author-frozen source archive, SHA-256 `586b4fc185695b637c46acc798f7008a233e77ad7dd7742875aa8265004d806c`
  (88 990 bytes, 32 entries) — digest re-verified. Internal `SHA256SUMS`: all 31 listed files OK.
  The 13 module fingerprints in the author note §7 match the files byte-for-byte.
* Packet `baseline/` copies of `Breaks.lean`, `Dyadic.lean`, `I6Base.lean` are byte-identical to the
  reviewed repo at `2757349`; `reference/PR41/.../T21.lean` is byte-identical to the reviewed target;
  `pins/` toolchain and Mathlib rev match (`v4.35.0`, `56a00585…`). Author's declared baseline commit
  is `a5937595…`; the three baseline files are identical, so the comparison is sound for T21.
* Order of reading: all 13 Lean modules (signatures and the global/transport proofs in full) were read
  before the author note `docs/research/t21-different-bound.md`.

## 1. Bottom line

| Item | Finding |
|---|---|
| Closed global provider of `GlueConductor.SerreDifferentBound` / `ZInQ.Targets.H.T21` | **ABSENT.** Confirmed: no declaration of that type in the packet. Global T21 remains **OPEN**. |
| Closed local leaf `PkgI6.DifferentBound` | **Closed** by `localDifferentBound` (independently recompiled; axioms ⊆ {propext, Classical.choice, Quot.sound}). It is NOT rfl-equal to and does NOT imply T21 by itself. |
| Global pieces proved unconditionally | normalization `v_P(n)=e·v_p(n)` (`n≠0`), `P≠⊥`, `e>0`, `𝔇≠0`, `P^n∣𝔇 ↔ n ≤ mult`, full `e=1`/unramified case (no Galois). |
| Pointwise global conclusions | Proved **only conditionally** on per-(L,p,P) model data incl. `hmapD : 𝔇_{𝓞L/ℤ}·B = 𝔇_{B/A}` — the multiplicity-mapping premise is **not discharged anywhere**. |
| Soundness of the conditional theorems | Sound as stated (proved for every model satisfying the hypotheses; fake models cannot be exploited). Closing T21 = exhibiting ANY such model for every `L,p,P`. |
| Batch readiness | Statement: unchanged (ready to propose). Proof: **NOT ready**; packet may be registered only as component/conditional evidence, never as the T21 provider. |

## 2. Independent reproduction (one compiler process at a time, `LEAN_NUM_THREADS=1`, private outputs)

Plain `lean -j1 -o <private>` on each module in the author's order, against existing pinned Mathlib
oleans and copies of the three baseline oleans (built from byte-identical sources); no `lake`, no
shared-cache writes. All 13 modules: exit 0, no errors/warnings (`SerreLocal`, `Comparison`,
`GlobalReduction`, `Audit` emit only their `#check`/`#print` output). Times 1.8–13.8 s each; peak RSS
≈ 7.0 GB. `Audit` output is identical to the author's `evidence/audit.txt` except the latter's
3-line command header. Across all module logs: 51 `#print axioms` reports, every one ⊆
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`. Source scan: no `sorry`/`admit`/`axiom`
declarations/`native_decide`/`implemented_by`/`extern`/`unsafe`/`opaque`; the only `Fact` is a local
`Fact (Irreducible …)` instance for `AdjoinRoot` (UnramifiedFactor L112), not a bound.

Separate narrow probe on pinned Mathlib (`T21G1Probe.lean`, `import Mathlib`):
present — `IsDiscreteValuationRing (v.adicCompletionIntegers L)`, `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]`,
`IsDiscreteValuationRing ℤ_[p]`, `Algebra (𝓞 L) (v.adicCompletionIntegers L)`,
`FaithfulSMul (𝓞 L) (v.adicCompletionIntegers L)`, `PerfectField (ResidueField ℤ_[p])` (via `ofFinite`),
`PadicInt.maximalIdeal_eq_span_p`;
**absent (synthesis fails)** — `Algebra ℤ_[p] (v.adicCompletionIntegers L)`, `Algebra ℚ_[p] (v.adicCompletion L)`,
`HenselianLocalRing (v.adicCompletionIntegers L)`. Hence the completion model cannot even be
*typed* (`Module.Finite A B` needs `Algebra A B`) without new construction.

## 3. Checklist G1–G6 (from REPORT §5) against the packet

* **G1 instances at the completion — OPEN.** The packet's `serreDifferentBound_atPrime_of_completeDVR_model`
  needs `Algebra A B`, `Module.Finite A B`, torsion-free, separable, `IsAdicComplete` and perfect
  residue on `A`. For `A=ℤ_[p]`, `B=adicCompletionIntegers L P`: completeness, DVR, perfect residue,
  `(𝓞 L)`-algebra and faithfulness exist; the `ℤ_[p]`-algebra, finiteness and separability do not
  (probe). Nothing in the packet constructs them (consistent with its README).
* **G2 ramification index — PROVED conditionally** (`ramificationIdx_local_model_eq_global`) from
  `hbase : maximalIdeal A = span{p}` and `hmapP : P·B = 𝔪_B`. Read in full: it uses
  `ramificationIdx_eq_multiplicity` locally, maps `span{p}` along the canonical `ℕ`-cast (no scalar-tower
  assumption needed: ℤ/ℕ-casts are canonical), `multiplicity_map_eq_of_prime_maps_to_maximal`, and
  `primeAbove_multiplicity_natCast` with `padicValNat p p = 1`. `hbase` is dischargeable for `ℤ_[p]`
  by `PadicInt.maximalIdeal_eq_span_p`; `hmapP` remains a model obligation.
* **G3 different identification — OPEN (main gap).** `hmapD` is a bare hypothesis in every global
  reduction (`…_of_local_ideal_model`, `…_of_generating_uniformizer_model`, `…_of_factor_model`,
  `…_of_unramified_tower_model`, `…_of_completeDVR_model`). Pinned Mathlib has no localization- or
  completion-compatibility lemma for `differentIdeal`; the nearest tools
  (`IsDedekindDomain.differentIdeal_dvd_map_differentIdeal` / `differentIdeal_eq_map_differentIdeal`
  in `RingTheory/DedekindDomain/LinearDisjoint.lean`) are for linearly disjoint intermediate fields of
  one ambient field with `Module.Free A R₂`, so they do not apply to a completion (ℚ_p ⊄ L).
* **G4 valuation of `e` — PROVED** on the global side (`primeAbove_multiplicity_natCast`) and carried
  to `B` by `hmapP` (`hEmult` in `Transport`); `(e:B)≠0` derived from faithfulness. Correct.
* **G5 DVR arithmetic and `+1` — PROVED** (`multiplicity_le_of_dvd_maximalIdeal_pow_mul_span`,
  `not_pow_dvd_global_different_iff`). The final exponent matches the target term exactly
  (verified in the elaborated `#check` of `…_completeDVR_model`).
* **G6 coverage — OPEN.** The conditional theorems are stated for all `L : Type*`, all `p`, all `P`
  (no Galois/tame/`f=1` restriction), and the local proof handles wild ramification with `p ∣ f`
  through the constructed étale factor (`UnramifiedFactor` + `Tower`), so no case is silently dropped
  *given a model*. Coverage fails only because no model family is supplied.

## 4. Checklist T1–T9 (from INITIAL §5)

T1 local hypotheses vs Serre: match (complete DVR, perfect residue, separable). ✔ local.
T2 normalization `v_L(p)=e`, `v_L(e)=e·v_p(e)`: ✔ proved. T3 `e` identification: ✔ conditional on
`hbase`,`hmapP`. T4 different identification: ✘ open (`hmapD`). T5 nat arithmetic/truncation: ✔.
T6 `P≠⊥`, maximal: ✔. T7 degenerate cases: `e=1` ✔ unconditionally; tame/wild ✔ only through the
conditional route. T8 universes: all packet theorems are universe-polymorphic (`Type*`), so they
specialize to the target's `L : Type`; completions of a `Type 0` field stay in `Type 0`. ✔.
T9 axioms: ✔ independently reproduced.

## 5. Precise boundary evidence for the remaining globalization

1. **Non-complete interfaces do not cover general `L` by direct localization.** For `A=ℤ_(p)`,
   `B=(𝓞L)_P`: `Module.Finite A B` fails whenever more than one prime lies over `p` (the author note
   says the same), and an unramified residue-surjective intermediate DVR `U ⊂ B` with
   `Algebra.IsUnramifiedAt A 𝔪_U` generally does not exist inside `L`. So the supplied-factor/tower
   interfaces need either a Henselian/complete `B` or the fixed-field route below.
2. **Packet's fixed-field proposal (author note §3, route 2) — bookkeeping re-derived independently,
   NOT formalized anywhere in the packet.** With `M` a Galois closure, `D ⊇ I` decomposition/inertia of
   a prime `Q | P`, `H = Gal(M/L)`, `H₀ = D∩H`: `F=M^D`, `E=M^{H₀}` (⊇ L), `U=M^{I·H₀}`. Then `Q` is
   the unique prime of `M` over `Q_F`; `e=f=1` for `Q_F|p` and `Q_E|P`; `U/F` unramified at `Q`
   (`U ⊆ M^I`); `e(Q_E|Q_U)=[E:U]=|I|/|I∩H₀|`, so `E/U` is totally ramified (residue degree 1).
   Hence with `A=(𝓞_F)_{Q_F}`, `B=(𝓞_E)_{Q_E}` (finite over `A` by uniqueness), `hbase` (from
   `e(Q_F|p)=1`), `hmapP` (from `e(Q_E|P)=1`) and `hmapD` (tower formula
   `differentIdeal_eq_differentIdeal_mul_differentIdeal` twice + unramified ⇒ unit at `Q_E` +
   **localization compatibility of `differentIdeal`**, still absent) are all mathematically true. This
   is consistent; it is the route the separately-owned shared-foundation work is pursuing. This review
   does not implement it.
3. **Alternative not needing completions or Galois closures** (REPORT §5, unchanged): reduce via
   `differentialIdeal_le_iff` and CRT to non-vanishing of the trace `𝓞_L/P^{e(1+v_p(e))} → ℤ/p^{1+v_p(e)}`.
   Recorded only as a fallback; not implemented.

## 6. Minor observations (non-blocking)

* README asks for `LEAN_NUM_THREADS=2` / ≤2 processes; this review used 1 thread, 1 process — results
  identical, no thread-dependence observed.
* `global_ramificationIdx_pos` holds for every prime `P` (including `⊥`, where the length-based index
  is 1); harmless here because `P≠⊥` is also proved.
* The author's nine obligations (§4 of their note) agree with this review's G1–G6/T1–T9 split; every
  item they mark open (model construction; global different-image equality) is open here too.
* Serre III §6 locator remains UNVERIFIED (REPORT §2); the packet does not rely on it.

## 7. Limits

Focused component evidence only: no full candidate kernel replay, no registration/gate check, no
review of the separately-owned transport/fixed-field work (not provided). No global proof was attempted.
