# igusa-drop: replaying the fold on a later head

The Contrib proof file `ZInQKernel/Contrib/OneProof/IgusaDrop.lean` is its own commit (159fcd50), separate from the
fold commit. The fold is produced by a script. From the repository root, on a head that has IgusaDrop.lean and whose top
research bundle still carries `igusaGL2DSGalSome`:

    python3 scratch/igusa-drop/gen_igusa_drop.py --dry-run   # prints the walk, the count change and the module
    python3 scratch/igusa-drop/gen_igusa_drop.py             # writes TailZ<j>, switches Main.lean, drops the kinds row
    lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
    bash scratch/igusa-drop/run_checks.sh <worktree with the pre-fold build>   # hash guard, closure, OpenStatements,
                                                                                # render_open, DischargesTest, crosswalk, autoform

The script follows Main.lean's current top theorem down its chain (let-steps and nested conversion composites allowed,
as in fold-b105) and stops at the first conversion whose result has no `igusaGL2DSGalSome`; later autofolds on top are
composed through. It rewrites exactly one reader shape:

    _root_.AfTateLam.r16CoreY_of_ds965 a b c (_root_.X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome X.igusaGL2DSGalSome) d
      ->  _root_.AfTateLam.r16CoreY_of_ds965_x0 a b c d

and aborts if any field of the stop bundle still mentions the field or `IgusaGL2DS`. If a later head reads the field
elsewhere (another shape), add a rule to `READERS`: every reader can take `AfTateLam.x1PointsConjugate_proof` or
`ZInQ.RLeaf.igusaTransitive_iff_x0Transitive.mpr FltCqj2.x0Transitive_proof`, provided it uses Igusa only through
`X1PointsConjugate` / `IgusaTransitive`.

`FoldCheck.lean` lists the removed constants (`X1Igusa.IgusaGL2DSGalSome`, `X1Igusa.IgusaGL2DS`,
`AfTateLam.r16CoreY_of_ds965`, the old top) and the replacement route; update the top names (`OpenResearchLeaves52/53`,
`sixContactMin_of_open71/72`) when replaying on a head with a different top.
