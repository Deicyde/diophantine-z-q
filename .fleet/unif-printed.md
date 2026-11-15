# unif-printed

**Result: `uniformizationLeafAll` proved in Lean from four printed leaves (-1 GLUE against the re-rated count).**
`UnifPrinted.uniformizationLeafAll_of_printed : MumfordComplexTorus → SmoothComplexManifold → ProperCompact →
ConnectedConnected → BPAnalytic.Uniformization.UniformizationLeafAll`, in
`ZInQKernel/Contrib/OneProof/UniformizationPrinted.lean` (imports only `ZInQKernel.HDecomp.Analytic.Uniformization`;
builds; axioms propext, Classical.choice, Quot.sound). Statement of the field unchanged; `gagaMorphism` not used.

Leaves (all rated printed form; locators UNVERIFIED, flag unread):
* `MumfordComplexTorus` — Mumford §1 literally, over Mathlib's `LieGroup 𝓘(ℂ, ℂ^g) ω` (compact, connected, T2) ⇒
  biholomorphic group iso with bp-analytic's `Torus Λ`.
* `SmoothComplexManifold` — X smooth proper irreducible over ℂ ⇒ X(ℂ) (classical topology) is an analytic manifold,
  regular functions holomorphic and giving local coordinates (Shafarevich VII §1.1; SGA 1 XII 1.1, 3.1).
* `ProperCompact` — X proper ⇒ X(ℂ) compact (GAGA §2 Prop 6; SGA 1 XII 3.2).
* `ConnectedConnected` — X proper irreducible ⇒ X(ℂ) connected (Shafarevich VII §2.1; SGA 1 XII 2.4).

Missing in Mathlib: analytification (no analytic spaces, no complex structure on X(ℂ)), so "A^an ≅ ℂ^g/Λ" cannot be
stated literally; the dictionary leaves are stated over a concrete `classicalTopology` (initial topology of regular
functions). Proved glue: coordinate form from Mumford + analytic Lie group structure; classical-topology
neighbourhoods; regular maps holomorphic; holomorphic right inverse via implicit + inverse function theorems; the
group law of A(ℂ) holomorphic via (A×A)(ℂ) ≅ A(ℂ)×A(ℂ).

Deliverables: docs/research/unif-printed.md, scratch/unif-printed/ (stage files, log.md, autofold.json, dry run).
