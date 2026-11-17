# leaf-fold33 (staged on wip/leaf-fold33b, not landed)

**Result.** From fork main 5e235a40 (the w82 landing: 45 open hypotheses, 37 H with strict 16 LEAF / 21 GLUE, and 8
TYZ/GZ hypotheses of which hCM, h33 and hL3 were GLUE), this fold reaches **35 open hypotheses: 29 H (strict and
strictest 11/18) and 6 TYZ/GZ hypotheses (h11, hL29, hCM, h33, hBFH, hGZ; GLUE: h33 and hGZ)**. Over all hypotheses
the strict GLUE count goes from 24 to 20 (the strict LEAF count of H from 16 to 11), and no fold step raises a count. Every step was checked the same way
(scratch/leaf-fold33/log.md, steps 1-17): `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`,
`#print axioms ZInQ.OneProof.frozenTarget` standard, the DumpCompact hash guard (no existing constant of
`ZInQKernel.OneProof` changed except `frozenTarget`), a closure check of the removed Props, `OpenStatements.lean`,
`render_open.py --check`, `frontier_crosswalk.py --check`, the DischargesTest rerun and `autoform check blueprint`.
The integration chain (the repository's full check, as used for the autoland of w82) passed on the intermediate
states 25415c1c, 3091ccc7, 0e3c3125, 30674d98, 4da8d4f3, 49ce87a7, 667e0aed, 0595e253 and c7fbc273.

## What is folded

| step | hypothesis | how | source task |
|---|---|---|---|
| 2 | poincareComplement | proved from open fields (autofold, TailZ46) | poincare-proof |
| 2 | blr_7_2_1 | proved outright: `NeronSH.neronBaseChangeUnramifiedDVR_proof` | neron-sh-proof |
| 5 | hL3 | replaced by route A's C_d chain; its leaves hQ and hW were later proved, hGZ remains | gzopt-dict (period-odd, cd-optimal, gz-optimal) |
| 7 | mumfordKLFiniteSectionAC | proved from picRepresentableAbVar and picZeroAbVar (autofold, TailZ47) | phi-ample |
| 8 | homFreeFiniteAlgClosed | rerouted: T6 over fields with a ring hom to C (copy reroute, TailZ48) | homfree-noemb |
| 9 | hW, hfx | proved outright | etaw32-proof, hfx-proof |
| 10 | hQ | proved outright (q-expansion principle for Gamma0(N)) | gamma0-qexp |
| 11 | hP23 | proved outright | hp23-proof |
| 12 | sga3_VIB_3_10_Nbhd | rerouted (copy, NoSGA3Copy / TailZ49) | sga3-nbhd, integrated by fold33-copy |
| 12 | mumfordGroupLawConn, neronSchemeExtensionExists | replaced by the printed leaf neronSchemeExtensionDedekind (copy, GoodModelIsoCopy / TailZ50) | goodmodel-iso, group-law-dvr, integrated by fold33-copy |
| 13 | hCM | retyped to the printed Shimura 1971 Thm 5.4 (`HCMDict.ShimuraThm54`); GLUE to LEAF | hcm-dict |
| 14 | hGZ | re-flagged "pending reading" (GLUE) after review: steps D1-D3 between the print and the Lean form | fold33-review |
| 15 | weilPairingMumford, mumfordPhiSurjectiveAC | proved / rerouted from open fields (TailZ51, TailZ52) | phisurj, integrated by fold33-pic |
| 15 | picZeroAbVar | replaced by its characteristic-0 form from three printed leaves (TailZ53); GLUE -1, fields +2 | piczero-char0, integrated by fold33-pic |
| 16 | identityComponentLFT | proved outright (autofold, TailZ54) | idcomp-lft |
| 17 | picLocFinType | proved outright (autofold, TailZ55) | piclft |

Folds that remove a hypothesis by rerouting its readers are copies: the original declarations stay (the blueprint
names some of them as Lean targets, and an in-place prune made `autoform check` fail; see fold33-combine), and new
modules in `ZInQKernel/OneProof/H/` carry the copied chain. Copies with no reader left (NoSGA3Copy, TailZ49) can be
dropped at a cleanup. Scratch dry runs that redeclared `HDec.HSyn` bundles were renamed `.lean.txt` for the same reason.

## Results not folded, and why

- **Count-neutral or worse:** h11-reduce, h29-proof, degpoly-proof, nos-converse, neron-ext, neron-flt,
  charpoly-hf (charpoly-charp conflicts with the homfree reroute: it needs Mumford section 19 Thm 3 in characteristic
  p), group-law-dvr alone, sga735-narrow, kleiman-proper, htnew-det.
- **Lower GLUE but add a leaf, outside this fold's brief** (ready on their branches for the next integrator):
  coeff-rational (eigenformCoeffFieldFinite), h33-dict (h33), hodgetate-from-dr, derham-print, grx6ab-print with
  elkies-print, height-fix with semiab-descend and javanpeykar-rebase, sga33-shpre.
- **Pending a reading of a print:** y3abu-print / y3abu-strict (shimuraMainThmIDeligneY3AbU: the polarized moduli
  problem and the relative Lemma P), tyz-genus variant C (h11 + hL29 to TYZ Thm 2.1 including n = 1; -1 if the print
  covers n = 1), gz-dict2 (hGZ: D1 and D2 are proved; D3 depends on whether Gross-Zagier V section 2 is stated only for
  the strong Weil parametrization; LEAF, GLUE -1, if not).
