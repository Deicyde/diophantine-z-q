# leaf-fold33 results log

Base: 6b7a45445 (lf32b: 37 H fields, strict 16 LEAF / 21 GLUE, top sixContactMin_of_open38 in TailZ45).

## Decisions before merging

* pic-fix2 (45945e9ce): fold B is `scratch/pic-fix2/narrow.patch` + `autofold-narrow.json` (README, report §1, §3).
  The patch edits the existing modules TailZ24, 26, 30, 31, 34 (field `phiAmpleIsogeny` renamed and retyped
  `phiVeryAmpleIsogeny`, and `addedLeaves12_of_open13` rewritten). In lf32b `phiAmpleIsogeny` is no longer a field:
  TailZ45 fills it by `PicFix.phiAmpleIsogeny_of_printed n.mumfordKLFiniteSectionAC n.mumfordPhiSurjectiveAC`.
  Fold B's leaves (`MumfordKLFiniteDivisorAC`, `MumfordPhiSurjectiveVAC`) assume `IsVeryAmple` in addition to
  `IsAmple`, so they are weaker than the open leaves `PicFix.MumfordKLFiniteSectionAC` (ample + nonzero section)
  and `PicDict.MumfordPhiSurjectiveAC` (ample) and cannot discharge them. Fold B therefore needs hand edits of
  existing H modules, which this task may not make. Decision: skip, do not merge.
