# neron-descent results log

Base: wip/leaf-fold33b d879bb73; merged origin/wip/dedekind-free 0718c946 (merge commit 80fa9f58).
Build: `.lake/build` and `lean/.lake/build` reflink-copied from ~/dzq-wt/dedekind-free (its base c0f3d085 + its
contribution `MumfordGroupLawDescent`), used only through `lake env lean` on scratch files.

## Target
`ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` (ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean:56),
research field `OpenResearchLeaves38.neronSchemeExtensionDedekind` (docs/one-proof/OPEN.md L179).

## Readers (VERIFIED: scratch/dedekind-free/readers.txt, closure of frozenTarget at c0f3d085; reread here)
1. GIT 6.14 (`MumfordGroupLawDVR`): proved with no Neron leaf by dedekind-free (`mumfordGroupLawDVR_proof`).
2. T41 height rows: `t41_of_extension5` (TailM L387) -> `H5Neron.NeronModelExists` (H5Neron.lean L205): a global
   `GroupModel A L` over Spec O_L with `IsNeronModel`, at every number field L; read by r18-r22,
   `exists_semistable_neron` (TailY L199), `stableFaltingsHeight_add_le` (H5Neron L210ff, uses hN1 at the arbitrary
   field E.L of an arbitrary model in the infimum).
3. r6/SS1/SS3: `GapNeron.neronSchemeModelExistsNF` (NeronDVR.lean L89) -> `NeronSchemeModelExistsDVRNF`: Neron
   models over every DVR O of a number field; `HasSemistableReduction A O` is defined through one.

## Descent tools available (VERIFIED by reading the sources)
- Mathlib 4.35: descent of morphism *properties* (FlatDescent.lean, LocalFlatDescent.lean, Morphisms/Descent.lean),
  descent of morphisms (fpqc maps are effective epis, Sites/Fpqc); RingTheory/Flat/FaithfullyFlat/Descent.lean only
  descends injective/surjective/bijective. No effective descent of objects (schemes, algebras, modules).
- Vendored FLT (NeronFLT/Vendor/AnthropicFLT/Theorems):
  * `DescentAction.effective_of_finiteEtale`: R -> R' finite etale faithfully flat, every finite subset of X' in an
    affine open => the descent action is effective.
  * `DescentAction.effective_of_isPullback_of_flat_surjective`: effectivity given the quotient Y already.
  * `exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing`: X smooth separated
    qc over a DVR: one affine open contains every point that is generic in its fibre.
  * `exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk`, `RelativeGroupLaw.exists_isAffineOpen_forall_
    mem_of_smooth_of_henselianLocalRing` (AF for smooth group schemes over a henselian DVR), quotients of affine
    schemes by finite locally free equivalence relations.
  * main theorem needs `[HenselianLocalRing R]`.

## Findings (math; marks in the report)
F1. Every finite extension of a non-henselian DVR is non-henselian; R^h and R^sh are not filtered colimits of finite
    R-algebras over which a Neron model is available. Hence FLT's finite etale descent cannot reach R from any
    ring over which a Neron model is known (VERIFIED reasoning, report section 3).
F2. Etale-neighbourhood descent R -> B' (B' DVR, residue extension trivial): the descent datum is the identity on
    the special fibre and the canonical generic one elsewhere; an open U of N' is stable iff U_eta is defined over K.
    Any open containing the whole generic fibre is stable, but none is affine (A proper, dim A > 0).
F3. Effectivity <=> every special-fibre point has an affine open neighbourhood whose generic fibre is defined over K
    (given affine descent + gluing, neither in Mathlib). Mathematically this is Raynaud's quasi-projectivity
    (BLR 6.4/1) + descent of quasi-projective schemes (BLR 6.1/7, SGA 1 VIII 7.7), numbers UNVERIFIED.
F4. Extending N' over the finite flat closure Spec C of the neighbourhood moves the same problem to the other primes
    q_i of C (their local models are again descents along etale neighbourhoods): circular.
F5. Consumer reroute: T41 needs global models over O_L for every L (the stable height is an infimum over all
    global group models, and `stableFaltingsHeight_add_le` applies hN1 at an arbitrary L); no henselian substitute
    without restating the height leaves. r6/SS1/SS3 read HasSemistableReduction over non-henselian DVRs.

## Verdict
Field not removable with no new leaf by the tools on this host; dedekind-free's count-neutral narrowing to
`NeronExt.NeronDVRLocal` stands as the best available fold.

## Compile log
C1 (00:45-00:48). `NeronDescent.lean` against oleans copied from ~/dzq-wt/dedekind-free: all `#check`s and the
   reductions elaborate; `copy_iff := Iff.rfl` FAILS. Cause (VERIFIED by `#print` with pp.explicit): the copied
   olean of `NeronSchemeExtensionDedekind` is the c0f3d085 version, *without* the hypothesis `¬ IsField D` that
   fork main added in 00f923e24 (reviewer fix). The copy matches the current source; the oleans were stale.
F6. Integration bug (VERIFIED by reading; build C2 below): dedekind-free's
   `GroupLawDescent.neronDVRLocal_of_dedekind` (MumfordGroupLawDescent.lean L844) applies the field as
   `h Rv L (A.baseChange L)` with no `¬ IsField Rv` argument, so it does not typecheck against the current statement.
   One-line fix: `h Rv L (A.baseChange L) (IsDiscreteValuationRing.not_isField Rv)`.
