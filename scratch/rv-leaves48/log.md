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
