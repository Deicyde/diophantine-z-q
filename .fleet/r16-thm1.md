# r16-thm1 (done 2026-11-17)

**Result.** Shimura 1973 Thm 1, restated to match the AI page read, replaces the Diamond-Shurman citations in
`afShimura` and `heckeJ1DS`:
* `R16Thm1.heckeJ1DS_of_bSh : BShStandardModel → HeckeJ1DS`. B-Sh (ON THE SPOT: Shimura's standard model with
  xi_p, <d> is the kernel's IsX1Gen/IsHeckeT/IsDiamond) has HeckeJ1DS's statement. Only the supplier changes, to
  the uncited Shimura 1971 section 7.3.
* `R16Thm1.afShimura_of_shimura73 : ShimuraThm1Printed → ShimuraQuotientIsAf → AfShimura`. IsAfAction is derived
  in Lean from clause (ii): T_p directly; <d> via xi_{p^2} = T_p^2 - p<p>, a Dirichlet prime p = d mod N, and
  a_p^2 - a_{p^2} = chi(p) p.
* Finding: the read's (i)-(iii) do not pin A as DS's J/I_f J, since (ii)-(iv) are isogeny-invariant. "Quotient"
  is read as connected kernel, and ker nu = I_f J still needs multiplicity one. Named as the glue
  `ShimuraQuotientIsAf`, with a proof sketch.
* Li plus ConjNewform supply the Fricke proviso (`euler_of_shimura73_li`). The total Euler identity still does not
  give per-embedding charpolys, so afCharpolyDS965 (DS 9.6.5) stays flagged. igusaGL2DS* untouched.
* Known issues: Shimura's Euler-clause misprint "a_n^sigma f" for "a_n^sigma f_sigma"; standard model only by
  citation; round-1 gap at tex L770-773 kept.

**Compiles:** ZInQKernel/Contrib/OneProof/R16Thm1.lean (standard axioms). Fold: scratch/r16-thm1/autofold.json, no
generation step. Dry run 4/27 on 31 -> 4/28 on 32 (+1 GLUE; --allow-rise). FoldCheck.lean compiles
(sixContactMin_of_open68 standard). #discharges shows afShimura and heckeJ1DS discharged by R16Thm1. Exact kinds
rows are in the report section 3 and in kinds-diff.txt.

**Remains:** the wording of Shimura's clause (i) and uniqueness (p. 527); if it says J/aJ, the glue follows from
the leaf. A reading of Shimura 1971 sections 7.2-7.3 for B-Sh. The owner's call on DS 9.6.5 vs total form +
Brauer-Nesbitt. Report: docs/research/r16-thm1.md (has the Manuscript check).
