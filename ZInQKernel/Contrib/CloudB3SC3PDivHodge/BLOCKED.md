# Blocked source checkpoint — not a verified theorem

Base: `c1e4ed1b8765f016c8fd5808e79bb0124b364952`.
Source: anthropics/fermats-last-theorem `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Toolchain: Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

This branch preserves a partial port only. It closes neither
`HodgeTateDecompAbVar` nor `DeRhamH1AbVarT`, and no pull request is requested.
The root p-divisible-group theorem is also **unverified**.

The exact blocker is `TP9.coe_trace_adjoin_simple_eq` in
`S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower`.
Elaboration succeeds, but kernel checking exceeds `-M16000`. The original
port failed after 411 seconds; an explicit scalar rewrite in place of one
`rfl` also failed after 12 minutes 19 seconds, peak RSS about 16.4 GB.
Its downstream continuous-cocycle chain, root solution/wrapper and final
restatement therefore remain uncompiled. No root axiom or discharge result
is available.

The record includes 216 successful prerequisite-module compiles before the
final provider rewire, not a final whole-cone pass. The checkpoint contains
209 source modules, one compatibility lemma module and the uncompiled root
restatement. It reuses the canonical Tate providers now present on main;
it does not republish the dependency merge or duplicate their root names.
Original licences/notices/credits are preserved, and all new files passed
the prohibited-code and public-hygiene scan. These source checks are not
kernel acceptance of the root theorem.

The work still needs the general bad-reduction case and the actual
AbVar/ring-of-integers/Tate-module/Galois transport to close the exact
abelian-variety field. The de Rham period comparison is separate.
Private evidence bundle available to the maintainer.
