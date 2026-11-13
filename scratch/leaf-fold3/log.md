# leaf-fold3 results log

## 11:44 start (fresh; no earlier log)
- Base 88dc9bd4. Merged origin/wip/kummer-comp (423d6b7c) and origin/wip/hecke-rest (e27601d8): both have reports.
- Copied leaf-fold2's build (parts/, scripts, root-module sources) into scratch/leaf-fold3/.
- mk_prefix.py: issue #2 items (2) kernel's strengthened `fibre_conjugates_isomorphic` (ZInQKernel/HDecomp/QM/Leaves.lean:500,
  with its proof; the weak one had no user), (5) second `#print axioms HSyn.sixContactMin_of_leaves` dropped, (8) QM "Lemma P"
  -> "Lemma QP" (25 occurrences; `lemmaP_lattice` keeps its Lean name, which lives in rv-qm-polar and the kernel, with a note).
- mk_g7bound.py: g0-assemble3's G7Data fix (`[L:ℚ] ≤ D` as last clause) in parts 75, z85, z86; diff against g0-assemble3's
  parts = HDec header/open lines only.
- mk_lf3.py: new parts partsF/c10 (Burnside), c20 (cpts-transport), c40 (kf-glue d20 lines 1-15, 431-end), c50 (twist-descent),
  c60 (hodge-bc2), c70 (linked-tate c10-c15), c75 (lt-goodred 99d); c30 (hom-unify) and d90 (fold) hand-written;
  root module LF3Cot (infra-stalks CotangentBaseChange lines 523-end).
- lake build of the kernel modules needed (Contrib T14 T28 RLeaf HeightBC HodgeBC2 Mobius Dim TwistDescent FrobPieces HomUnify
  AbVarBC, HDecomp QM.Pin etc.) started 11:47.
