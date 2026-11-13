# t-purity2 results log

Base 883c4ddf. Continues t-brauer-purity (T2 already proved there: T2Full.lean, T2Kernel.lean).

- `EtaleLocal.lean` (Mathlib only): COMPILES (lake env lean, 1m42), standard axioms.
  `TPurity2.isEtaleAt_of_isUnramifiedAt_of_flat_local`: `R → S` finitely presented, `q` over `p`,
  `S_q` flat over `R_p` (via `Localization.AtPrime.algebraOfLiesOver`), `IsUnramifiedAt R q`
  ⇒ `IsEtaleAt R q`. (Mathlib's `IsEtaleAt.of_isUnramifiedAt_of_flat` needs global flatness.)
- `T1Dim1.lean` (Mathlib only; `PkgI2.PurityBranchLocus` copied verbatim from
  ZInQKernel/HDecomp/Objects.lean): COMPILES, no sorry, standard axioms.
  `TPurity2.purity_dim_one`: the leaf's conclusion when `dim S_q = 1` (hypotheses: regular `R_p`,
  domain `S_q`, quasi-finite at `q`, `dim S_q = dim R_p`, unramified at height-one `q' ≤ q`;
  integral closedness not needed). Proof: quasi-finiteness ⇒ `ker(R_p → S_q) ≠ 𝔪`
  (`QuasiFinite.eq_of_le_of_under_eq`); `eq_bot_of_isPrime_of_ne_maximalIdeal` (principal `𝔪`,
  Nakayama) ⇒ injective ⇒ `R_p` domain ⇒ DVR (TFAE) ⇒ torsion-free `S_q` flat ⇒ étale
  (`isEtaleAt_of_isUnramifiedAt_of_flat_local`).
  `TPurity2.PurityBranchLocusGe2` (leaf with `2 ≤ dim S_q` in place of `1 ≤`),
  `purityBranchLocus_of_ge2 : PurityBranchLocusGe2 → PkgI2.PurityBranchLocus`,
  `ge2_of_purityBranchLocus` (converse). So T1 = its dimension ≥ 2 case.
- `ProfiniteCochains.lean` (Mathlib only; `IsCocycle2`, `IsCoboundary2` copied verbatim from
  ZInQKernel/HDecomp/Conductor/I6Base.lean): COMPILES, standard axioms.
  `exists_nhds_one_invariant` (continuous `H → ZMod 2` on a compact group is right-invariant under
  a neighbourhood of 1; via `compact_open_separated_mul_right`), `exists_openNormalSubgroup_invariant₂`,
  `continuous_of_invariant(₂)`, `isCocycle2_iff` (IsCocycle2 ε ↔ cocycle identity ∧ ε bi-invariant
  under an open normal subgroup), `isCoboundary2_iff` (↔ ε = δf with f invariant under an open
  normal subgroup), instances `compactSpace_absoluteGaloisGroup`,
  `zeroDimensionalSpace_absoluteGaloisGroup` (char 0), `isCocycle2_iff_Qp`.
