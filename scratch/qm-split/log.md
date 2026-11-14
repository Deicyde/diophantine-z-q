# qm-split results log

Base cba8157f. Chain: leaf-fold4's olean chain (TailK), copied from leafq-check's ~/lqc-olean to ~/qms-olean;
check script `scratch/qm-split/chk.sh` (lean with leaf-fold4's LEAN_PATH). T0.lean: `import TailK` works (85 s cold).

Row sources (VERIFIED, read): definitions read in ~/dzq-wt/leaf-fold4/scratch/leaf-fold4/olean/*.lean
(the chain the frontier names for C4''), leafq-check rows in ~/dzq-wt/leafq-check/scratch/leafq-check/.

## H-46 `qmClassNumberOne`: PROVED, no leaf (VERIFIED, compiled)
- `scratch/qm-split/ClassNumberOne.lean` (import TailK): `HDec.QMSplit.CNO.qmClassNumberOne_proof :
  HDec.HSyn.G0Split.FibreQM.QMClassNumberOne` (the chain's own constant, imported). 0 errors, 8 s;
  `#print axioms` = [propext, Classical.choice, Quot.sound].
- Class number one computed: `euclid` (|nrd(x − q)| ≤ 7/8 by rounding in the basis 1, i, (1+j)/2, (i+k)/2;
  nrd = Eisenstein norm − 2·Eisenstein norm), `principal_of_lattice` (minimal |nrd| element of a left
  𝒪-stable subgroup I with dI ⊆ 𝒪 generates I). Eichler's theorem is no longer cited.
- Lattice glue: I = {x : ι(x)v ∈ Λ}; rank argument (Fin.cons family of 5 in rank-4 Λ), uniform denominator
  from `Submodule.annihilator_top_inter_nonZeroDivisors`; w = ι(α)v not c·real via finrank (range ≤ 2 < 4).
