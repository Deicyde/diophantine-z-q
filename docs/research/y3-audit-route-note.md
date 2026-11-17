# y3-audit: the route to Y₃, and where the citation fails (note for review)

Part (2) of y3-audit is paused here for review (2026-11-17), under the instruction to follow the manuscript and the
literature and to flag every argument written on the spot.

## What the chain needs

Part (1) (`.fleet/y3-audit-verdict.md`) found that the chain needs a fine moduli scheme `Y₃` over ℚ for abelian
surfaces with an action of the maximal order `𝒪` of `B = (2, −3 | ℚ)` and full `𝒪`-linear level-3 structure. It is
read on field points of every field `K ⊇ ℚ`, together with a universal family and classifying maps for families over
proper smooth ℚ-curves. No integral property is used.

## What the manuscript does (diophantine_zq.tex L443-478)

1. Buzzard, Duke Math. J. 87 (1997), Thm 2.1 and Cor. 2.3, is applied at `V₁(5)` over `ℤ[1/30]` (L444-446). The
   level 5 is prime to 6, so this is inside Buzzard's hypotheses.
2. A full five-marking is added, then the finite étale sheaf `Isom_𝒪(𝒪/3𝒪, A[3])` (L447-453). It is nonempty on
   every geometric fibre because the Tate lattice is free of rank one over `𝒪₃` (L454-462). The result `X₃₅` is
   smooth and projective (L464-465).
3. `G₅ = (𝒪/5𝒪)^×` acts freely (L466-472). A stabilizer would give a polarized automorphism preserving the full
   three-marking, hence a finite-order element of `1 + 3M₄(ℤ₃)`, and that group is torsion-free.
4. The quotient `X₃₅/G₅` is smooth and projective. The universal abelian scheme descends to it, with its canonical
   principal polarization, its `𝒪`-action and its three-marking. The quotient represents the full-three problem, and
   its generic fibre is `Y₃` (L473-477).

## Where the citation fails

Not in the manuscript. The manuscript cites Buzzard at level 5 and builds level 3 by the quotient. The kernel's
leaves `Y3FineModuliAb` (y3abu-print) and `Y3Fix.Y3FineModuliAbP` (y3-fix) were rated "printed form" with Buzzard
cited directly for full level 3. Buzzard requires the level to be prime to the discriminant, and `3 ∣ 6`, so that
rating is wrong. The statement is a consequence of Buzzard at level 5 plus steps 2-4 above.

## State at the pause (Lean, standard axioms)

* `Y3Audit.Y3RepresentableQ`: representability over ℚ of the level-3 problem in the kernel's objects
  (`ZInQKernel/Contrib/OneProof/Y3RepresentableQ.lean`).
* `y3FineModuliAbP_of_rep'` and `shimuraMainThmIDeligneY3AbU_of_rep'`: the chain's leaf and research field from it,
  by Yoneda at field points and at proper smooth curves.
* Unfinished and unused: `scratch/y3-audit/GenFib.lean`, a bridge from the sgr-split leaf
  `SGRSplit.ShimuraIntegralModelRep` (which cites Kottwitz) to `Y3RepresentableQ`.

## Items written on the spot (not in the manuscript)

* ON THE SPOT: the polarization-free form. The manuscript's moduli problem carries the canonical principal
  polarization. The kernel's objects (`QMAbSchemeP`, `R1fpPropsAbP`) drop it, and the equivalence needs the
  relative Lemma P.
* ON THE SPOT: route K, Kottwitz (J. AMS 5, 1992, §5) at `p = 5`, and the `GenFib` bridge. The manuscript uses
  Buzzard, not Kottwitz. Paused.
* ON THE SPOT (an alternative proof of a manuscript step): rigidity by Serre's lemma (`|u − 1|² ≤ 4 < 9`) in place of
  the manuscript's torsion-freeness of `1 + 3M₄(ℤ₃)` (L469-471). The conclusion is the same; the manuscript's argument
  is the one to formalize.

## Following the manuscript in Lean

Beyond a Buzzard leaf at level 5, steps 2-4 need:
* the torsion subgroup scheme `A[3]` and Isom schemes of finite étale group schemes over a base;
* quotients of schemes by free actions of finite groups;
* étale descent of abelian schemes with polarization, `𝒪`-action and markings;
* the polarized rigidity of step 3.

None of these is in Mathlib 4.35 or the kernel (`docs/research/y3-audit.md` §4.2). The options:
* (a) state the manuscript's L443-477 conclusion as the leaf, kind consequence (Buzzard at level 5 plus the quotient
  glue), GLUE until the glue is formalized;
* (b) formalize steps 2-4 (Mathlib-scale);
* (c) route K through the existing Kottwitz leaf. This is a deviation from the manuscript, and it needs a reading of
  Kottwitz §5 and the PEL comparison.
