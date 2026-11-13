# glue-t32a — report

**Verdict: T32(a) is glue; it is proved in Lean. B3 (v) now rests on no leaf.**

- `GlueB3Unram.t32a : LeafPush.T32a_TameQuadratic` (VERIFIED, compiled). This is the bundle's leaf
  T32(a), with its statement `diff`-identical to `scratch/h-decomposition/Leaves.lean`
  L11927-11932; the defs `GQ`, `IsAtPrime`, `inertiaQ` are identical too. It says: for odd `p` and
  `w` over `ℤ_(p)`, `Nat.card {χ : I_w →* ℤˣ // Continuous χ} = 2`.
- `GlueB3Unram.unramified_outside_noLeaf`: B3 (v) (N5 L702-712, `L'` unramified outside `T`) with
  no leaf hypothesis. It is glue-b3b's `unramified_outside_t32a` applied to `t32a`. Also
  `GlueB3Unram.leafB3a : LeafB3a`.
- Method: no ramification groups and no tame-inertia structure. A continuous `χ` has a Kummer
  generator `β` (`τβ = χ(τ)β`; Krull basis, primitive element, Vandermonde). `v(β)` is a rational
  power of `v(p)` (Newton polygon). glue-b3b's `exists_inertia_neg` gives an inertia element
  negating `√p`, which forces the least `n` with `v(β)^n ∈ v(√p)^ℤ` to be odd. Inertia acts
  trivially mod `w` on the unit `β^n/√p^k`, and `2` is a unit, so `χ = η_{√p}^k`.
- Compiles: `lake env lean scratch/glue-t32a/T32a.lean`, 0 errors, about 21 s. No `sorry`, no
  `axiom`. All 20 `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`.
- Files: `scratch/glue-t32a/T32a.lean` (glue-b3b's file plus about 450 new lines),
  `scratch/glue-t32a/log.md`, `docs/research/glue-t32a.md`.
- Effect: both Props of leaf T32 are now glue (T32(b) by glue-b3b), so T32 can leave
  `TextbookLeaves` once integrated.
- Remains: integration only. Move the file into `ZInQKernel/HDecomp/` as a module, import the
  `LeafPush` defs rather than copy them, and fill `TextbookLeaves.t32a`/`t32b`. No file under
  `ZInQKernel/` or `blueprint/` was edited.
