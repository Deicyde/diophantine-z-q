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
- 23:10 §3-§4 added, file compiles, no errors (deprecation warnings only). VERIFIED.
  - `exists_finset_cover`, `fg_iInf_of_local`, `exists_smul_mem_iInf_of_local` (local-to-global over Spec R).
  - `OmegaLocal` (Prop): near each s ∈ Spec 𝓞_L, on D(a) ∋ s, one f.g. N ⊆ cot spanning over L with
    N ≤ omegaAt s' and omegaAt s' ⊆ loc_{s'} N for s' ∈ D(a).
  - `omegaFG_of_omegaLocal`, `omegaSpans_of_omegaLocal`,
    `hodgeLatticeTheorem_of_local : OmegaLocal → CotangentRank → HodgeLatticeTheorem`; axioms standard.
