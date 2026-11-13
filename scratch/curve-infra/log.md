# curve-infra results log

## Scope (VERIFIED, read docs/research/image-plane.md §1, §7)
image-plane's `ImagePlaneFinal.lean` proves (IC) `ImageClosed`, (AD) `AlgDep`, C2K, (G1'), MobiusGlue-from-T5
with standard axioms; (L0) `FiniteGlobalSections` is used by no theorem of its §1.
=> image-plane's proof needs none of AD, IC, L0. Per task: prove AD in general
(dim = trdeg of function field for integral schemes locally of finite type over a field).

## Alg.lean
- `ringKrullDim_eq_of_isIntegral_of_injective`, `ringKrullDim_mvPolynomial_field`: verbatim from g0-dim.
- `exists_dim_eq_trdeg`: R domain, finite type over field K (same universe) ⇒ ∃ s, dim R = s ∧ trdeg K R = s.
- `trdeg_eq_of_isLocalization`: trdeg K F = trdeg K R for F = Frac R.
- compile: 0 errors, 0 warnings (VERIFIED, 09:20).
