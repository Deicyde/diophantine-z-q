# Reduced products over the complex field

This supporting package proves that the existing product of two reduced complex schemes is reduced.

`ZInQ.Contrib.CloudB3W17bReduced.isReduced_complex_tensor` takes the original objects
`X Y : Over (Spec (CommRingCat.of ℂ))` and only their existing `IsReduced` instances. It proves
`IsReduced (X ⊗ Y).left`. The product is the category's original product, not a newly selected model.
No smoothness, group structure, finite-type or geometric-reducedness hypothesis is added.

The supporting import cone is a new-file port of 26 modules from AxiomMath/Stacks at revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, with proof-API compatibility for Lean 4.35.0 and
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
See `MODIFICATIONS.md` for the limited transformations and `LICENSE`/`NOTICE` for provenance.
No existing project module, object definition, toolchain or dependency pin is changed.

This is a supporting reducedness theorem. It does **not** claim analytic-to-algebraic GAGA,
construct an algebraic morphism realizing an analytic map, or discharge `gagaMorphism`.

A private evidence bundle containing source bindings, compiler logs, exact-type checks,
axiom queries and the prescribed discharge output is available to the maintainer.
