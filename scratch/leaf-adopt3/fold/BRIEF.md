# Common brief for fold agents (leaf-adopt3)

Worktree: ~/dzq-wt/leaf-adopt3 (git branch wip/leaf-adopt3). DO NOT run lean, lake, or any Lean
process (the orchestrator is the only one allowed to run Lean; it will compile your output).
Do not run git commands that change state (no commit, no checkout, no stash). Do not edit any
file except the ones named as your outputs under scratch/leaf-adopt3/fold/. No network.

Context. `scratch/h-decomposition/Leaves.lean` (21704 lines, imports only `Mathlib`,
`ZInQKernel.Hypotheses.JHeight`, `ZInQKernel.Compiler.Precision.HeightConstant`) is one big file
that contains *copies* of the definitions that also live, modularized, in the kernel
`ZInQKernel/HDecomp/**` (namespaces such as `PkgI3`, `PkgI6`, `GlueI3`, `GlueConductor`,
`GlueDescent`, `LeafModCurves`, `LeafQM`, `ZInQ.DefFaltings`, `LeafAdopt`, `ZInQ.LeafPush2`,
`GlueVigneras`, ...). At its end, namespace `HSyn` (from line ~21093) holds §0-§2 definitions
(`HSyn.SkolemNoether`, `HSyn.KroneckerWeber`, `HSyn.FrobeniusDense`, `HSyn.BrauerNesbitt`, the
`opaque` placeholders, ...) and §3 the bundles `structure ResearchLeaves` / `structure
TextbookLeaves` (line ~21437/21483), whose fields are the leaves.

Wave-25 tasks proved things in scratch files that `import` kernel modules (or only Mathlib).
The orchestrator will insert *your fragment* into Leaves.lean at this point:

    ... HSyn §2 (all HSyn definitions, incl. HSyn.SkolemNoether etc.) ...
    end HSyn
    end            -- closes HSyn's noncomputable section
    <<< YOUR FRAGMENT(S) HERE >>>
    noncomputable section
    namespace HSyn
    open scoped MatrixGroups ModularForm
    ... structure ResearchLeaves ... structure TextbookLeaves ... glue ...

So your fragment can use every declaration of Leaves.lean (all of it is before this point),
fully qualified (e.g. `HSyn.SkolemNoether`, `PkgI6.ChebotarevExists`).

Your job, per assigned task:
1. Read the task's report docs/research/<task>.md (main result) and its Lean file(s)
   scratch/<task>/*.lean.
2. Produce `scratch/leaf-adopt3/fold/<task>.lean`: a Lean fragment with NO `import` lines,
   wrapped in `section <Something>Sec ... end <Something>Sec` (and `noncomputable section ... end`
   if needed), keeping the task's own namespace for its new declarations (e.g. `TSkolemKW`, `C9Rhof`),
   with the task's statements and proofs copied verbatim, EXCEPT:
   - Delete every declaration that duplicates one already in Leaves.lean (same fully qualified
     name). Duplicates would be a redeclaration error. If the task's file re-states a Leaves.lean
     definition under a new name (a local copy), keep using the Leaves.lean original where possible;
     if the task's statement of a leaf differs AT ALL from the Leaves.lean statement, note it.
   - Every identifier the fragment uses must exist in Leaves.lean (or Mathlib) with the same
     meaning. The kernel module that the task imported is normally a copy of a section of
     Leaves.lean; for each kernel name the task uses, grep Leaves.lean for its `def`/`theorem`/
     `structure` and check the body is the same (python/diff on the text is fine). If a kernel
     declaration it needs is NOT in Leaves.lean, copy it from ZInQKernel/HDecomp/** into your
     fragment (before its use), under its kernel name, and list it.
   - Drop `#print axioms` lines (list them in your notes instead; the orchestrator adds some).
   - Watch for `open` / `variable` / `universe` statements and `set_option` the fragment needs.
3. At the end of the fragment add *bridging theorems* whose types are EXACTLY the Leaves.lean
   Props that become proved/reduced, e.g.
       theorem TSkolemKW.hsyn_t13 : HSyn.SkolemNoether := ...
   or, for a reduction, `theorem X.foo_of_leaves (h1 : NewLeaf1) (h2 : NewLeaf2) : HSyn.Old := ...`.
   New leaf Props (e.g. `PkgI6.ChebotarevExists` is already in Leaves.lean; x1-belyi's five new
   leaves are new) must be `def … : Prop` in the fragment, statement-identical to the task's file.
4. Write `scratch/leaf-adopt3/fold/<task>.notes.md` (short): which bundle field(s)/glue rows change,
   the exact names and types of the bridging theorems, new leaf Props (name, one-line meaning,
   reference), new glue Props (if a reduction leaves glue), what was deleted as duplicate, kernel
   declarations copied in, anything whose statement differs from Leaves.lean, and expected trouble
   spots for compilation. If the file is too long to copy fully, copy statements and proofs that
   are needed and say which parts were omitted.
Be precise; the orchestrator will compile your fragment against the real file and fix errors.
Lean 4.35 / Mathlib v4.35.0 sources are in .lake/packages/mathlib if you need to check names.
