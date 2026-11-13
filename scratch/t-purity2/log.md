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
- `T2Kernel.lean` of t-brauer-purity re-compiled at this base (after `lake build
  ZInQKernel.HDecomp.Objects ZInQKernel.HDecomp.Conductor.I6Base`): COMPILES, standard axioms;
  `TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}` holds here. T2 is fully proved (the
  task brief's "only L = K and the lower half" is out of date).
- `T1Kernel.lean` (imports ZInQKernel.HDecomp.Objects; kernel's `PkgI2.PurityBranchLocus`):
  COMPILES, standard axioms. `TPurity2K.purity_dim_one`, `TPurity2K.purityBranchLocus_of_ge2 :
  PurityBranchLocusGe2.{0} → PkgI2.PurityBranchLocus.{0}`, `objBridge_purityBranchLocus_of_ge2`.
- `ProfiniteCochains.lean` extended: `IsCocycle2Fin`, `IsCoboundary2Fin`, `H2TwoClassesFin`,
  `h2TwoClasses_iff_fin`, `localH2CardC_finite_iff_fin`. COMPILES, standard axioms.
- `ProfiniteKernel.lean` (imports ZInQKernel.HDecomp.Conductor.I6Base; kernel's PkgI6 defs):
  COMPILES, standard axioms. `TPurity2K.localH2CardC_iff_fin : PkgI6.LocalH2CardC ↔ (∀ p,
  H2TwoClassesFin G_{ℚ_p}) ∧ H2TwoClasses G_ℝ`, `brauerHasse2C_iff_fin : BrauerHasse2C ↔
  BrauerHasse2Fin`, `brauerReciprocity2C_iff_fin : BrauerReciprocity2C ↔ BrauerReciprocity2Fin`
  (all three T14/T15 Props restated with "inflated from G/N, N open normal" in place of
  continuity).
- `T1Finite.lean` (Mathlib only; `PkgI2.PurityBranchLocus` copied verbatim): COMPILES, no sorry,
  standard axioms. `TPurity2.PurityBranchLocusFinite` (the leaf with `[Module.Finite R S]` in place
  of `[Algebra.FiniteType R S]` and no quasi-finiteness hypothesis) and
  `TPurity2.purityBranchLocus_of_finite : PurityBranchLocusFinite → PkgI2.PurityBranchLocus`.
  Proof: Mathlib's Zariski Main Theorem
  (`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`: module-finite
  `S' ⊆ S`, `r ∈ S' ∖ q`, `S'[1/r] ≅ S[1/r]`); `exists_pow_mul_mem`, `isLocalization_atPrime_of_pow`,
  `locEquiv : S'_{P∩S'} ≃ₐ[R] S_P` (r ∉ P); primes `q'' ≤ q ∩ S'` of `S'` lifted to `S` as
  `comap ψ 𝔪` with `ψ : S → S[1/r] ≅ S'[1/r] → S'_{q''}`; heights, unramifiedness, regularity,
  normality, dimension transported along `locEquiv`.
- `T1Reduced.lean` (Mathlib only; copies of T1Dim1 + T1Finite): COMPILES, standard axioms.
  `TPurity2.PurityBranchLocusFiniteGe2` (leaf for module-finite `R → S`, `dim S_q = dim R_p ≥ 2`,
  no quasi-finiteness hypothesis), `purityBranchLocus_of_finiteGe2 : PurityBranchLocusFiniteGe2 →
  PkgI2.PurityBranchLocus`, `finiteGe2_of_purityBranchLocus` (converse: the two are equivalent).
- `T1Kernel.lean` now the kernel form of T1Reduced (imports ZInQKernel.HDecomp.Objects):
  COMPILES, standard axioms. `TPurity2K.purityBranchLocus_of_finiteGe2`,
  `objBridge_purityBranchLocus_of_finiteGe2`, `finiteGe2_of_purityBranchLocus`.
- `T1Local.lean` (Mathlib only; T1′ def copied from T1Reduced): COMPILES, standard axioms.
  `TPurity2.PurityBranchLocusLocal` (T1″: `[IsRegularLocalRing R]`, `[Module.Finite R S]`,
  `q.comap (algebraMap R S) = maximalIdeal R`, `S_q` normal domain, `dim S_q = dim R`,
  `2 ≤ dim R`, unramified at height-one `q' ≤ q` ⇒ `IsEtaleAt R q`).
  `finiteGe2_of_local : T1″ → T1′` (localize at `p`: `S_p` finite over `R_p`
  (`Module.Finite.of_isLocalization`), `Q = qS_p`, `locLocEquiv : (S_p)_Q ≃ₐ[R] S_{Q∩S}`,
  `Q ∩ R_p = 𝔪` via `IsLocalization.map_under`, heights via `IsLocalization.height_under`,
  étale over `R_p` ⇒ over `R` by `FormallyEtale.comp`); `local_of_finiteGe2 : T1′ → T1″`
  (`equivAtMaximal : A ≃ₐ[A] A_𝔪` for local `A`).
- `T1Reduced.lean` / `T1Kernel.lean` regenerated with T1Local appended: COMPILE, standard axioms.
  Kernel: `TPurity2K.purityBranchLocus_of_local : PurityBranchLocusLocal.{u} →
  PkgI2.PurityBranchLocus.{u}`, `local_of_purityBranchLocus` (converse),
  `objBridge_purityBranchLocus_of_local`; plus the T1′ versions. So T1 ⇔ T1′ ⇔ T1″.
- Read: the only consumer of bundle fields `t14a`, `t14b`, `t15` is
  `GlueWP3.b3_degree_le_QM_of_T14_T15` (ZInQKernel/HDecomp/Descent/WP3.lean:290-307), via
  `leafHasse_of_T14` / `leafLocalTwo_of_T15` into `GlueDescent.B3Q.b3_degree_le_QM` (takes
  `LeafHasse`, `LeafLocalTwo`); `cob_of_same_finite_support` (I6Base) has no consumer (grep).
  Reciprocity is used only via `real_of_finite` (parity with an empty set; finiteness conjunct unused).
- `T14Narrow.lean` (imports ZInQKernel.HDecomp.Descent.WP3, built with `lake build`): COMPILES,
  standard axioms. `TPurity2K.BrauerHasseFin2C` (cochain LeafHasse: coboundary at every finite p
  ⇒ coboundary), `LocalTwo2C` (T15 finite-place uniqueness half), `brauerHasseFin2C_of_T14`,
  `brauerHasse2C_of_fin`, `leafHasse_iff_brauerHasseFin2C`, `localTwo2C_of_T15`,
  `leafLocalTwo_iff_localTwo2C`, `leaves_of_narrow : BrauerHasseFin2C → LocalTwo2C → LeafHasse ∧
  LeafLocalTwo`.
