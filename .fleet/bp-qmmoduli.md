# bp-qmmoduli (2026-11-12): summary

**Verdict.** H's proof never uses the Shimura curve `Y₃` as a moduli scheme over a general
base. It uses:
- field-valued points (objects `(A, ι, η)` over fields);
- `Y₃` through its function field and its morphism to `P¹_j` (Prop. TS needs only `ℚ(Y₃)/ℚ(j)`);
- the `Γ'` action, which changes `(ι, η)` but not `A`;
- reciprocity at CM points;
- for F1 only, the complex uniformization.

So R1, R2 and R5 can be crowdsourced as **field-point leaves**: R1fp, R1hecke, R2fp, R1rec, R5fp
(`docs/research/bp-qmmoduli.md` §2.3), over the kernel's `PkgI3.AbVar`. None of them needs
representability, abelian schemes over a base or finite flat group schemes. They need no
polarization either:
- for this datum a principal polarization with Rosati involution `μ⁻¹x̄μ` exists and is unique
  given `(A, ι)` (§2.2, argued; its lattice core is proved in Lean);
- Buzzard's "false elliptic curve" moduli are polarization-free (recalled, UNVERIFIED).

The only very large node is the analytification (period lattice) for F1 (R1an). It is shared
with R22 and T11. The weak statement "a point of the analytic quotient with the right Igusa
invariants" serves F1 only, not A5, A7 or A10.

**Compiles** (`scratch/bp-qmmoduli/`, no `sorry`, axioms propext/Classical.choice/Quot.sound).
- `QMOrder.lean`:
  - `𝒪` as a `Subring` of `QuaternionAlgebra ℚ 2 0 (−3)`;
  - the positive Rosati involution `†`;
  - `E₀` compatible and unimodular;
  - **every alternating `†`-compatible form is `r·E₀`, and a principal one is `±E₀`**;
  - Atkin–Lehner elements and their relations.
- `Units72.lean`: `|(𝒪/3𝒪)^×| = 72` (`decide +kernel`).
- `QMAbVar.lean` (imports the kernel's A6):
  - `QMStr`, `Level3`, the `Γ'` action (units `≡ 1 mod 3` act trivially);
  - `QML3`, isomorphisms with symm/trans, the setoid, `M3`;
  - centralizer and CM predicates;
  - base change of QM structures (`endBC`, injective by faithful pullback);
  - fields of moduli of QM pairs, and the leaf statement `R5fp` (González–Rotger, degree form);
  - **`QML3.goodReduction`: step A6 for every QM surface with level-3 structure**, from the
    kernel leaves NOS, Raynaud and TorsionStructure.

**Remains.**
- Base change of level structures. It needs `A(K̄)[3] ↠ A_L(L̄)[3]` (from `TorsionStructure`)
  and `dim A_L = dim A`, or a scheme-theoretic `A[3]`.
- `P¹_ℚ` with its points.
- Compiling R1fp, R2fp and R1rec (written in Lean syntax in the note, not compiled).
- Faithfulness reviews of all field-point leaves; review of §2.2.
- Checking Buzzard's Thm 2.1 for full level 3.
- The analytification node.
