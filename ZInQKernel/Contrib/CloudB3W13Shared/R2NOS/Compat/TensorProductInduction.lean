/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Lean 4.35 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 compatibility lemma for the H5 lane4
port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2 (source written
against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d).

Mathlib db584 `TensorProduct.induction_on` (Mathlib/LinearAlgebra/TensorProduct/Defs.lean,
Apache License 2.0, Mathlib authors) was an `@[elab_as_elim]` eliminator with cases
`zero`/`tmul`/`add`.  Mathlib 56a replaced it by `TensorProduct.inductionOn` (cases `tmul`/`add`)
and kept `induction_on` only as a deprecated, type-changed theorem WITHOUT `@[elab_as_elim]`, so
the source's `refine TensorProduct.induction_on z ?_ ?_ ?_` can no longer infer its motive.
This file restates the db584 statement and attribute under the port prefix
`ZInQ.Contrib.CloudW03NeronSurj.FLT`, proved from Mathlib 56a's `inductionOn`.  No axiom.
NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14: statement/attribute copied,
proof replaced by a one-line reference to the Mathlib 56a eliminator.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open scoped TensorProduct

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

@[elab_as_elim]
protected theorem induction_on {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  _root_.TensorProduct.inductionOn z tmul add

end TensorProduct

end ZInQ.Contrib.CloudW03NeronSurj.FLT
