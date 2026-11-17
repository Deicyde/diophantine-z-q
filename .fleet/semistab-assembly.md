# semistab-assembly (11-17)

**Result.** Under the geometric and k(s) readings, the semistability clause of `bostLowerBoundAn` and
`gaudronRemondThm14An` is proved. New file `ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean`
(namespace `ZInQ.SemistabAssembly`; no sorry; standard axioms):

- `isClosed_range_openSubgroup_field`: an open subgroup scheme of a group scheme locally of finite type over
  any field is closed. Proof: base change to k̄; the projection is integral, hence closed, and surjective.
  It follows that an open connected subgroup is G⁰.
- (1) `isSemistableGeomPrinted_of_res`: from `IsSemistableRes`, G⁰ of every geometric special fibre is
  semi-abelian. (2) `isSemistableResPrinted_of_res`: the same over k(𝔭).
- New leaves `BostLowerBoundAnSS` and `GaudronRemondThm14AnSS`: the An rows verbatim, with semistability as
  printed (both readings at once). `bostLowerBoundAn_of_ss` and `gaudronRemondThm14An_of_ss` prove the
  fields from them.

**Checked.** The full build plus `#discharges` reports both fields DISCHARGED, still assuming the SS leaves
(`scratch/semistab-assembly/discharges-output.txt`). `autofold.json` passes the dry run and is
count-neutral (5/29 → 5/29).

**Remains.** R3' (étale coordinates are holomorphic charts), so the new leaves stay GLUE (kind
consequence). The SGA 7 IX 2.1.5 "no G_a" reading needs rigidity (task ga-rigidity). The Bost display is
UNVERIFIED. No field of frozenTarget was changed. Report: docs/research/semistab-assembly.md.
