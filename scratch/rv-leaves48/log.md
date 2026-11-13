# rv-leaves48 results log

Scope: the 48 concrete leaves of scratch/h-decomposition/Leaves.lean (bundles ResearchLeaves,
TextbookLeaves, lines 19109-19200) after leaf-adopt. Base 01267822.

## Setup
- 2026-11-12 22:58 `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`:
  needed before Leaves.lean compiles (first attempt: `unknown module prefix 'ZInQ'`). Build OK (9066 jobs).
- Reading split: cluster A (PkgI2/PkgI3/T9), B (PkgI4, HSyn §1, PkgI1), C (PkgI6, conductor,
  descent, T29), D (R16, T33, T34, R19-R21) delegated to reading-only sub-reviews
  (agentA..D.md here); the leaf-adopt QM leaves (R1R2fpRep, R1rec, R5fp, R5fpCount, H5) reviewed
  directly; all Lean probes run here, one process at a time.

## QM leaves (direct review, VERIFIED by reading Leaves.lean 14146-15634, 18605-18782)
- R1R2fpRep (18705): OK as a consequence (composite: Deligne PEL + Baba-Granath + Gonzalez-Rotger
  + Lemma P of rv-qm-polar). Checked: level structure on K-points <-> constant A[3] in char 0;
  A[3] free of rank 1 over O/3O even though 3 | disc B (T_3 A free over the local maximal order);
  Gamma(3) = O^1 ∩ (1+3O) torsion-free (nrd(zeta-1) in {1,2,3} for zeta of order 6,4,3, never in 9Z);
  Y_3 two geometric components (pi_0 = (Z/3)^x), not required connected: consistent;
  X_6 geometrically connected (nrd(O^^x) = Z^^x); fibre clause = W-orbits since Aut(O) = N(O)/Q^x and
  inner twists are isomorphic; CM clauses: phi^2=-1, phi^2-phi+1=0, phi^2=-6 each force the maximal
  order Z[i], Z[zeta6], Z[sqrt-6]; coordinate normalization (0, oo, -16/27) free by PGL2(Q).
- R1rec (15444): OK (consequence). fieldOfModuli3 ⊆ E(y) because Gal(Qbar/E(y)) ⊆ stab3; E(y)/E
  unramified outside 3 (K(3)_l = O_l^x for l != 3, optimal embedding of O_E); E unramified outside {2,3}.
- R5fp (15579), R5fpCount (15612): OK. Eichler count h(R) prod_{p|6}(1-(k/p)) = 2^{#inert} h(R)
  (type number 1); conductor = relIndex, 0 for non-orders so Coprime fails (R = Z excluded);
  b=0 field of moduli has degree h (e.g. Q(sqrt-6): degree 2, not containing k).

## Baseline compile (VERIFIED)
- `lake env lean scratch/h-decomposition/Leaves.lean`: EXIT 0, 3m39s, 0 errors, one `sorry`
  (line 19202, `glueOutputs_of_leaves`); `sixContactMin_of_leaves` axioms include `sorryAx`.

## Cluster A (agentA.md; I2, I3, T9, T27): all 17 OK
- I2/I3/T9 leaves byte-identical to pkg-I2/pkg-I3/leaf-push sources (textual diff, agent A); only T27
  changed (QMDichotomyYu with indefiniteness, rv-loc-leaves repair (i) applied).
- Lead re-read (VERIFIED by reading 1335-1620, 2766-2876, 11795-11912): NOS (a)<->(b)<->(c), R7b, R8, R6
  (m >= 3, A[m] K-rational), T4, T5 as stated are Serre-Tate / SGA 7 / Mumford consequences;
  T8 PoincareReducibility: A = 0 makes `f ≠ 0` impossible (no vacuity issue); T27 conclusion list
  complete for dim 2 (M2(Q) excluded since B division); T9 compatibility exponent `^m` correct
  (e_n(mx, m·λy) = e_{mn}(x, λy)^m), nondegeneracy-up-to-d clause excludes the trivial pairing.
## Cluster C (agentC.md; T14-T16, T20-T22, T29-T31): all 13 OK
- Documentation only: t16b docstring "the canonical reciprocity map is one such θ" holds in the
  arithmetic normalization only; rv-leaves-b's remark that θ ↦ θ⁻¹ preserves every clause is wrong for
  clause 3 (leaf still true); T31 citation of cd Ẑ = 1 inconsistent (Serre GC "I §3" vs "II §3").
- Lead re-check of t30 LeafSqrtCrit (VERIFIED by reading 8779): finite-order ψ of Q_p^x is a square iff
  ψ(-1) = 1 (p odd: μ_{p-1} cyclic of even order; p = 2: dual of 1+4Z_2 divisible); rec(-1) acts by
  ζ ↦ ζ^{-1} on μ_{p^k} in either normalization; k = 0 forces u = 1 (unramified χ has a sqrt): OK.
