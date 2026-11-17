# homfree-proof: `homFreeFiniteAlgClosed` (Mumford §19 Thm 3) over every field that embeds into `ℂ`; the rest is one strictly smaller leaf

Task homfree-proof, 2026-11-16. Base origin/main `0caafe66` (w80, leaf-fold31, top `sixContactMin_of_open35`).
Lean: `ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosed.lean` (new, 18 KB). Scratch: `scratch/homfree-proof/`
(`log.md`; `HomFreeC.lean`, the same proofs with `#print axioms`; `Discharges.lean` with `discharges.txt`;
`autofold.json` with `FoldDryRun.lean`; `Closure.lean` with `closure_out.txt`; `Callers.lean` with `callers_out.txt`).

Marks: **VERIFIED** means read in a source, computed, or compiled. **STANDARD** means published, with a reference.
**SPECULATIVE** means an unchecked estimate. There was no network access, so every theorem number recalled from memory
is **UNVERIFIED**.

## 1. Result

1. **Everything except characteristic `p` (and huge fields) is proved.** The proof uses only two other fields of the
   same bundle (`OpenTextbookLeaves12`): `uniformizationLeafAll` (AN3, `A(ℂ) ≅ ℂ^g/Λ`) and `mumfordTorsionAlgClosed`
   (Mumford §4 App. 2 (iv)). It covers every algebraically closed field `k` that has a ring homomorphism
   `σ : k → ℂ`. Over such fields the field's full statement holds: free, finite, rank `≤ 4 dim A dim B`, and
   `ℤ_ℓ ⊗ Hom(A, B) ↪ Hom(T_ℓ A, T_ℓ B)` for every prime `ℓ`. The same holds for T6 (`PkgI3.HomFreeFinite`) over
   every field `k` with such a `σ`. This is VERIFIED: it compiles, and `#print axioms` gives only `propext`,
   `Classical.choice` and `Quot.sound`.

   ```lean
   theorem ZInQ.Contrib.OneProof.HomFreeC.homFreeConcl_of_emb (HL : UniformizationLeafAll)
       (HT : AvSplit.MumfordTorsionAlgClosed) (emb : AlgebraicClosure K →+* ℂ) (A B : PkgI3.AbVar K) :
       HomFreeConcl A B
   theorem homFreeFiniteC          (HL) (HT) : HomFreeFiniteC          -- T6 over k with σ : k →+* ℂ
   theorem homFreeFiniteAlgClosedC (HL) (HT) : HomFreeFiniteAlgClosedC -- the field, plus σ : k →+* ℂ
   theorem homFreeFiniteAlgQ       (HL) (HT) : HomFreeFiniteAlgQ       -- T6 over k algebraic over ℚ
   theorem homFreeFiniteNF         (HL) (HT) : HomFreeFiniteNF         -- T6 over number fields
   ```

2. **The field itself is discharged from those two fields and one new leaf that is strictly weaker than the field.**
   This is VERIFIED by `#discharges` (§3). The new leaf, `HomFreeFiniteAlgClosedNoEmb`, is the field's statement
   restricted to algebraically closed `k` with `IsEmpty (k →+* ℂ)`. By Steinitz, those are the fields of
   characteristic `p > 0` and the fields of characteristic `0` whose transcendence degree over `ℚ` exceeds the
   continuum (STANDARD).

   ```lean
   theorem homFreeFiniteAlgClosed_of_noEmb (HL : UniformizationLeafAll) (HT : AvSplit.MumfordTorsionAlgClosed)
       (HR : HomFreeFiniteAlgClosedNoEmb) : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed
   ```

   - The fold is count-neutral: strict count 34/11 on 45 goes to 34/11 on 45, and strictest 34/11 goes to 34/11. One
     published LEAF is replaced by a weaker published LEAF.
   - The autofold dry run compiles (VERIFIED, §3).

3. **The target "-1, no new leaf" is not reached as stated (finding).** Two facts block it.
   - The field quantifies over every algebraically closed field, including characteristic `p`. In characteristic `p`,
     Mumford's proof needs two inputs that no bundle provides:
     - the quotient of `A` by the finite subgroup scheme `A[ℓ]` (Mumford §7), which gives "φ kills `A[ℓ]` ⇒ `φ = ℓψ`";
     - a discreteness input: `deg` is a polynomial function on `End(A)` (§19 Thm 2), together with Poincaré reduction
       to simple factors (§19 Thm 1).

     The bundle's `poincareComplement` is stated in characteristic `0` only (VERIFIED, `Contrib/AVB1/Poincare.lean`
     L42). `milneIsogenyQuasiInverse` does not factor a homomorphism through `[ℓ]`. `ℓ`-adic data alone cannot give
     finite generation (§4.2).
   - **No consumer of T6 needs characteristic `p` or a field outside `ℂ`.** VERIFIED for the call graph; the fields
     come from reading (§5). Every concrete field on the route is a number field, `ℚ̄ = AlgebraicClosure ℚ`, or a
     number field inside `ℚ̄`. All of them embed into `ℂ`, and `homFreeFiniteAlgQ`/`homFreeFiniteNF` cover them.

     So the field can leave the list with no new leaf, but only if T6's consumers are rerouted to `HomFreeFiniteAlgQ`
     (§5.3). That is a re-assembly of the T6 branch of the base proof, not an autofold.

## 2. The proof (characteristic 0, `σ : K → ℂ`)

Notation:
- `σ = emb ∘ (K → K̄)`;
- `A(ℂ)_σ = CPts A σ`;
- `Φ_A : ℂ^g → A(ℂ)_σ` is the uniformization of T35 (`ZInQ.LeafPush2.UniformizationExists`), with kernel `Λ_A`
  and `g = dim A`.

T35 is already proved from the two fields (`AvSplit.Final.h38 HL HT`, `OneProof/H/TailQ.lean` L2371, VERIFIED).

1. **Linear lifts** (`HomLinearLift` from `HL` alone): `ZInQ.HomLattice.homLinearLift_of_analyticHomLift
   (AvSplit.HomLatticeAN3.analyticHomLift_of_C (ZInQ.HomLattice.analyticHomLiftC_of_leaf HL))`. Every `f : A → B`
   has a `ℂ`-linear `M_f` with `Φ_B(M_f z) = f(Φ_A z)`.
2. **Uniqueness and additivity of lifts** (`lift_unique`, `lift_add`, new). If `M` and `M'` lift the same map, then
   `(M − M')(tz) ∈ Λ_B` for every real `t`, so `(M − M')z = 0` (conj-twist's `eq_zero_of_real_smul_mem`). Hence
   `M_{f+f'} = M_f + M_{f'}`.
3. **The lattice representation is injective** (`eq_zero_of_lift_lattice`, `hom_eq_zero_of_cpts`, new).
   - If `M_f` vanishes on `Λ_A`, it vanishes on `span_ℝ Λ_A = ℂ^g`, so `f` kills `A(ℂ)_σ`.
   - Then `f_ℂ = bcHom ℂ f` kills `A_ℂ(ℂ)` (`bcPt_ptMap`), so `f_ℂ = 0` by hom-unify's `hom_ext_of_cpts` (Mathlib's
     `ext_of_apply_eq`).
   - Hence `f = 0` (`bcHom_injective`).
4. **Free, finite, rank.** `U : Hom(A, B) →ₗ[ℤ] Hom_ℤ(Λ_A, Λ_B)`, `f ↦ M_f|_{Λ_A}`, is injective, and
   `Hom_ℤ(Λ_A, Λ_B)` is free of rank `2g · 2h` (`ZLattice.rank`, `Module.finrank_linearMap`). So `Hom(A, B)` is
   finite and torsion-free, hence free (PID), with `finrank ≤ 4gh = 4 dim A dim B`.
5. **Tate injectivity.**
   - conj-twist's `TateLatticeInj` (proved from T5 = `AvSplit.Final.h25 HT`: `G0Galois.tateLatticeInj_of_T5`,
     `TailE.lean` L137) gives injective `α_A, α_B : ℤ_ℓ ⊗ Λ → T_ℓ` with `toC(α(1⊗λ))_n = Φ(ℓ^{-n}λ)`.
   - Naturality (`G0Galois.homT_tateLattice`): `T_ℓ(f)(α_A(1⊗λ)) = α_B(1 ⊗ M_f λ)`. So for `x ∈ ℤ_ℓ ⊗ Hom(A, B)`
     with image `0`, `α_B((1 ⊗ χ_λ)(x)) = 0`, where `χ_λ(f) = M_f λ`. Hence `(1 ⊗ χ_λ)(x) = 0` for every `λ`.
   - With a basis `(b_i)` of `Λ_A`, the map `f ↦ (M_f b_i)_i` is injective into `Λ_B^n`. `ℤ_ℓ` is flat over `ℤ`
     (`AVB1.flat_int_padicInt`), so `1 ⊗ (that map)` is injective. Its components (`TensorProduct.piRight`) are the
     `1 ⊗ χ_{b_i}`, so `x = 0`.

   No hypothesis `ℓ ≠ char K` is needed.
6. **Corollaries.**
   - `σ : k → ℂ` extends to `k̄ → ℂ` (`IsAlgClosed.lift`), which gives `homFreeFiniteC` and `homFreeFiniteAlgClosedC`.
   - A field algebraic over `ℚ` has `k →ₐ[ℚ] ℂ`, which gives `homFreeFiniteAlgQ` and `homFreeFiniteNF`.
   - `homFreeFiniteAlgClosed_of_noEmb` splits on `isEmpty_or_nonempty (k →+* ℂ)`.

## 3. Lean, checks (all VERIFIED)

- `lake build +ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosed` succeeds on the base build (11,760 jobs, the new
  file in 19 s).
- `scratch/homfree-proof/HomFreeC.lean` (`lake env lean`): every theorem's axioms are
  `[propext, Classical.choice, Quot.sound]`.
- `#discharges` (`scratch/homfree-proof/Discharges.lean`, output `discharges.txt`):

  ```
  DISCHARGES [OpenTextbookLeaves12.homFreeFiniteAlgClosed] by ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteAlgClosed_of_noEmb
    still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll,
   AvSplit.MumfordTorsionAlgClosed,
   ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteAlgClosedNoEmb]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 56 open hypotheses, 2879 theorems checked, 8 discharge one
  ```

  The first two assumptions are open fields of the same bundle. Only `HomFreeFiniteAlgClosedNoEmb` is new.
- `scratch/homfree-proof/autofold.json`:
  - `python3 scripts/one_proof/autofold.py … --dry-run` prints `strict count: 34/11 on 45 -> 34/11 on 45; strictest
    34/11 -> 34/11`.
  - The generated module (line 1 stripped, `FoldDryRun.lean`) compiles against `TailZ42`.
  - `HDec.HSyn.sixContactMin_of_open36` has standard axioms.
- The contribution imports `ZInQKernel.OneProof.H.TailE`, `ZInQKernel.OneProof.H.TailQ` and
  `ZInQKernel.Contrib.AVB1.AlgClosed` (the statement's module), not `Main`. It contains no `#eval`, `run_cmd`,
  notation or macros. (`Closure.lean` and `Callers.lean` use `run_cmd`, but only in scratch.)

## 4. Findings

### 4.1 The new leaf and its rating

`HomFreeFiniteAlgClosedNoEmb` (in the contribution file):

```lean
def HomFreeFiniteAlgClosedNoEmb : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) → ∀ (A B : PkgI3.AbVar k),
    Module.Free ℤ (Hom A B) ∧ Module.Finite ℤ (Hom A B) ∧ (finrank : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (tateHomZl ℓ A B)
```

- **Rating: LEAF, published, not the printed form.** It is Mumford, *Abelian varieties* (1970), §19 Thm 3
  (UNVERIFIED locator; the field `homFreeFiniteAlgClosed` cites the same theorem), specialized by a ∀-instance to the
  fields named in its hypothesis. It is a direct consequence of the printed statement, never stronger. It is stated
  over the repository's genuine `PkgI3.AbVar`, `Hom` and `tateHomZl`, the same objects as the field.
- **Why it is not the printed form:** Mumford states the theorem for every algebraically closed field. The hypothesis
  `IsEmpty (k →+* ℂ)` is not in the print.
- **Kind "published"**, with flag "specialization (forall-instance) of the printed theorem…". Precedent:
  `milneIsogenyQuasiInverse` is "published" with a specialization read off the same display. With kind
  "consequence" the strict GLUE count would rise by one and autofold would refuse without `--allow-rise`.
- **Proposed `locators.md` row** (not added, since the task rules forbid editing other notes): `HomFreeFiniteAlgClosedNoEmb`
  — Mumford, Abelian varieties, §19 Thm 3 (locator UNVERIFIED), restricted to algebraically closed `k` with no ring
  homomorphism `k → ℂ`. Unread.
- **No consumer uses it** (§5): every field on the route embeds into `ℂ`.

### 4.2 Why the characteristic-`p` case is out of reach of the listed inputs

STANDARD, with the argument given here:

- **Finite generation needs archimedean input.** Torsion-freeness, `H/ℓH ↪ Hom(A[ℓ], B[ℓ])` for every `ℓ`, and
  injectivity of `ℤ_ℓ ⊗ H → ℤ_ℓ^r` for every `ℓ` hold for non-finitely-generated `H`. Example: the subgroup of `ℚ`
  generated by `1/p` for all primes `p`. Rank-1 data are `ℤ/ℓ` for each `ℓ`, and the module is `ℓ`-adically
  separated.
- **What Mumford uses instead:** discreteness of `(ℚM) ∩ End(A)` in `ℝ ⊗ M` via `|deg| ≥ 1` on isogenies of a simple
  `A` (§19 Thm 2, Poincaré §19 Thm 1).
- **What the bundles give:**
  - `charPolyIndepOfEllAlgClosed` gives integral characteristic polynomials. A trace-form argument would still need
    `End⁰(A)` semisimple, that is, Poincaré reducibility in characteristic `p`.
  - `poincareComplement` is characteristic `0` only.
- **Divisibility "kills `A[ℓ]` ⇒ divisible by `ℓ`"** needs the quotient `A/A[ℓ] ≅ A` through `[ℓ]` (fppf descent
  along `[ℓ]`, plus étaleness of `A[ℓ]`), and no bundle field gives it.
- **In characteristic `0` with `σ`,** the uniformization supplies both missing inputs at once: the lattice
  `Hom_ℤ(Λ_A, Λ_B)` is the discreteness, and `Φ(ℓ^{-n}Λ)` gives the divisibility.
- Characteristic-`0` fields of transcendence degree above `𝔠` would need a Lefschetz argument: descend `A`, `B` and
  `Hom` to a countable algebraically closed subfield (EGA IV 8.8.2 spreading out, plus invariance of `Hom` under
  extension of algebraically closed fields). This is not attempted, since no consumer uses such a field.

### 4.3 No statement problem

The field's statement is true (Mumford §19 Thm 3; STANDARD), non-vacuous, and matches the print up to the
`WithBot ℕ∞` encoding of the rank bound.

## 5. Consumers, and the reroute that would remove the field outright

### 5.1 Call graph (VERIFIED, `Closure.lean`/`Callers.lean` over `ZInQ.OneProof.frozenTarget`'s closure, 259,568 constants)

The closure contains the targets `PkgI3.HomFreeFinite` and `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed`. Neither
`ObjBridge.HomFreeFinite` nor any `HomRankBound` is in it. The 37 non-bundle constants whose type mentions T6 are
listed in `closure_out.txt`: 35 consumers plus the two supply maps `t6_of_algClosed5` and
`AVB1.homFreeFinite_of_algClosed`. The field reaches them only through `HSyn.t6_of_algClosed5` → `TextbookLeaves4.t6`,
which `TailK`, `TailD`, `TailI` and `TailE` consume. The T6 call graph (`callers_out.txt`):

| top consumer (no T6-typed caller) | reaches T6 through | where the field becomes concrete (reading) |
|---|---|---|
| `FS5NoCM.fibreComTrivialFull_of_leaves''` | `comIntOrQuadOrder_of(_leaves)`, `com_int_of_end0_quat`, `comOfMatrixEnd0_of_homFree` | `FibreComTrivial`: fibres `P : QML3 ℚ̄` (`TailA.lean` L1159); `comIntOrQuadOrder_of` applies T6 through `hYu Qbar P.A` (`TailC` L1700) |
| `G0FibreSimple.fibreSimple_of_pieces''` | `centralizerOfMatrixEnd0_of_homFree`, `end0Division_of_homFree` (generic `[CharZero k]`) | applied at `LeafQM.AV.Qbar = AlgebraicClosure ℚ` (`TailA` L1182, L1186) |
| `G0Galois.g8_g12` | `g8_g11`, `g8`, `PkgI3.C2_absolutelyIrreducible`, `PkgI3.finrank_equivEnd` | `K` a number field (`TailA` L2110, L2236, L2263); `L'` a number field (`TailD` L162) |
| `G0ModField.KernelField.kernelFieldExists_of_split''` | `endEqOFibre_of`, `kernelFieldExists_of_*`, `kernelField_of_model`, `G4WeilRes.homLattice_free`, `inertiaFixesHomsMon(_of_leaves)`, `tateHom_injective` | `AbVar Qbar`, `K : IntermediateField ℚ Qbar` finite (`TailC` L4197, L5302); `endEqOFibre_of` at `Qbar` (`TailC` L6829) |
| `HSyn.linkedTateLocal_of_leaves3` | `qmEndRank_of_leaves3`, `LTGoodRed.QM.qmEndRank_of(_leaves)`, `qmSplitCaseRank`, `four_le_finrank`, `finrank_le_baseChange`, `finrank_end0` | `QMEndRank`: `L' : IntermediateField ℚ Qbar` finite, and `Ω = AlgebraicClosure L'` (`TailF` L2432, L4038) |

Two caveats on coverage:
- The fields in the last column were read in the sources, partly through a code-search pass that had no grep. So
  they are VERIFIED for the lines cited and SPECULATIVE as a complete enumeration of every instantiation inside the
  generic lemmas.
- Several lemmas state T6-derived Props over all fields of characteristic `0`: `CentralizerOfMatrixEnd0`,
  `EndDivisionOfEnd0Division` and `QMSplitCaseRank` (the last over every algebraically closed `Ω ⊇ k`). Their uses
  found on the route are at the fields above.

Conjuncts used:
- **free / finite:** all branches.
- **rank bound:** `G4WeilRes.homLattice_free`.
- **Tate injectivity:** `G4WeilRes.tateHom_injective`, at `ℚ̄`.

### 5.2 Pending fold elsewhere

faltings-cm's `r9b` discharge (`origin/wip/faltings-cm`, not on main) uses `{t}.homFreeFiniteAlgClosed` at number
fields. After this fold it can use
`homFreeFiniteAlgClosed_of_noEmb {t}.uniformizationLeafAll {t}.mumfordTorsionAlgClosed {t}.homFreeFiniteAlgClosedNoEmb`
unchanged. Better, it can use `homFreeFiniteNF`/`homFreeFiniteC` and not depend on the new leaf at all.

### 5.3 Reroute for "-1, no new leaf" (for the integrator; not done)

T6 has been a field of the base `TextbookLeaves` since the first assembly. Its consumers are inside the base and
early-fold conversions (`gluePieces_of_open4`, `afterG7_of3`, `g8_g12_of_leaves3`, `linkedTateLocal_of_leaves3`, …).
So no older bundle generation has the consumers as fields without `t6`, and the "weaker-leaf bypass" of leaf-fold14
does not apply.

Removing the field outright needs a re-assembly of the T6 branch:
1. Copy the 35 T6-typed consumer lemmas of §5.1. The 21 with substantive proofs measure about 1,200 lines. Replace `hHF : PkgI3.HomFreeFinite` by
   `hHF : HomFreeFiniteC` (robust) or `HomFreeFiniteAlgQ`. Add a `σ : k →+* ℂ` (or `[Algebra.IsAlgebraic ℚ k]`)
   binder to the generic `[CharZero k]` lemmas and Props (`CentralizerOfMatrixEnd0`, `EndDivisionOfEnd0Division`,
   `QMSplitCaseRank`, `tateHom_injective`, `four_le_finrank`, `finrank_le_baseChange`, `finrank_end0`).
2. Supply `σ` at the concrete fields:
   - number fields: `NumberField.Embeddings`;
   - `ℚ̄` and `AlgebraicClosure L'`: `IsAlgClosed.lift` over `ℚ`, as in `homFreeFiniteAlgQ`.
   With `HomFreeFiniteAlgQ`, beware that `Algebra ℚ K` for `K : IntermediateField ℚ Qbar` is not syntactically
   `DivisionRing.toRatAlgebra`. The `σ` form avoids that.
3. Rebuild the conversions that read `t.t6` with the new lemmas, from the generation of `TextbookLeaves4` upward.

The count then drops by one (the field), with no new leaf. SPECULATIVE estimate: one to two days of integrator
work. The count-neutral fold of §3 is available now and is compatible with doing this later.

## 6. What remains

- `HomFreeFiniteAlgClosedNoEmb` stays open as a leaf: characteristic `p`, and characteristic `0` beyond the continuum.
- The reroute of §5.3, if the project wants the field removed with no leaf.
- Optional: a complete instantiation scan (Meta-level, recording the field argument of every application of a
  T6-typed term). The call graph of §5.1 is complete. The field column rests on reading.
