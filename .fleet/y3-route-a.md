# y3-route-a: the Y₃ leaf stated as the manuscript's own conclusion

Task y3-route-a, 2026-11-17. Report: docs/research/y3-route-a.md. Log: scratch/y3-route-a/log.md.

## Main result

**New leaf** `Y3RouteA.Y3FullThreeRepZ30`, in `ZInQKernel/Contrib/OneProof/Y3FullThreeZ30.lean`. It is the
manuscript's L473-477 conclusion, stated over ℤ[1/30]: the full-three QM moduli problem is representable by a proper
smooth curve over ℤ[1/30] with a universal family.
* Bases: locally noetherian ℤ[1/30]-schemes.
* Objects: `QMAbSchemeP`, the Mumford-form 𝒪-linear level 3, equivalent to a section of `Isom_𝒪(𝒪/3𝒪, A[3])`.

The docstring gives the manuscript's derivation with line numbers:
* Buzzard Thm 2.1 / Cor 2.3 at V₁(5) (L443-446);
* the five-marking and the Isom sheaf (L447-462);
* the free G₅ action via 1+3M₄(ℤ₃) (L465-472);
* the quotient and descent (L472-477).

It replaces the Buzzard / Boutot-Carayol citation of `y3FineModuliAbP`.

**Proved, standard axioms only (VERIFIED):**
* `y3RepresentableQ_of_z30`: the generic fibre satisfies y3-audit's `Y3RepresentableQ` ("its generic fibre is Y₃");
* `y3FineModuliAbP_of_z30`;
* `shimuraMainThmIDeligneY3AbU_of_z30`.

The generic-fibre step uses y3-audit's `abBC` base change. Its GenFib copy did not compile and is fixed here.

**Rating: not printed form.** Kind consequence, flag "ELLIOT: ...". It counts GLUE/GLUE, as did the row it replaces,
so the counts are unchanged at 4/27 on 31.

**ON THE SPOT:** the polarization-free functor is equivalent to the manuscript's polarized one through the canonical
principal polarization (relative Lemma P). This is not in the tree, and nothing is built on it.

## Fold (VERIFIED)

* Spec: `scratch/y3-route-a/autofold.json`, which discharges `y3FineModuliAbP` with the new leaf.
* Dry run: `sixContactMin_of_open68` over `OpenResearchLeaves49`. It compiles after a full Main build, with standard
  axioms. The consumers, NoCM and Lemma NV included, go through the old generation and are unchanged.
* `#discharges`: `[OpenResearchLeaves48.y3FineModuliAbP] by Y3RouteA.y3FineModuliAbP_of_z30`, still assuming
  `[Y3RouteA.Y3FullThreeRepZ30]`, standard axioms.
* Exact kinds row: `scratch/y3-route-a/kinds-row.tsv`, also in report §3.

## Source issues (report §0)

1. The wrong level-3 citation was the kernel's, not the manuscript's.
2. The manuscript's freeness and descent use a "polarized automorphism" and the canonical principal polarization.
   Buzzard's problem is recalled (UNVERIFIED) as polarization-free, so the relative Lemma P is needed tacitly.
3. "Generic fibre is Y₃" uses the canonical-model identification, which is the separate Deligne leaf.

## What remains

* Formalizing the derivation: Isom schemes, A[3] over a base, free quotients, étale descent, polarizations over a
  base. None of these is in Mathlib 4.35.
* A level-5 Buzzard printed leaf. This needs a reading of Buzzard on the polarization question.
