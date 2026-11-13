# hodge-lattice results log

- 2026-11-12 23:00 `lake build ZInQKernel.HDecomp.Faltings.Models`: OK (1m51).
- 23:15 scratch/hodge-lattice/HodgeLattice.lean compiles (`lake env lean`), no errors; one
  deprecation warning (TensorProduct.induction_on). VERIFIED.
  - `alt_eq_smulRight`: top-degree alternating map on R^g with values in N equals det · F(e).
  - `exists_clear`: denominators in K ⊗_{O_K} M (via IsLocalizedModule from isBaseChange).
  - `tmul_ιMulti_mem_span`: 1 ⊗ ιMulti v ∈ K·(1 ⊗ ιMulti w).
  - `hodgeLattice_of_lattice`: ω FG, rank_K (K⊗M) = g, ω spans K⊗M ⇒ finrank_K (K ⊗ ⋀^g M) = 1
    ∧ ∃ s ∈ detLat ω g, s ≠ 0 ∧ secIndex ≠ 0.
  - `hodgeLatticeTheorem_of : OmegaFG → CotangentRank → OmegaSpans → HodgeLatticeTheorem`.
  - axioms of both: [propext, Classical.choice, Quot.sound].
