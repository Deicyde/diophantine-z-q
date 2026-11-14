# Frobenius and rational trace: application proposal

**Source-only proposal. This application has not been compiled or kernel-checked
with the canonical trace supplier. It is not part of the verified proof branch
or a default build/import.**

`FrobeniusTracePairing.lean` proposes a direct application of the existing
rational EndTrace supplier to the same native finite-field Frobenius
endomorphism. The existing native action equality rewrites that endomorphism's
rationalized Tate map as the finite field's arithmetic-Galois action.

The intended result retains one rational-image witness in a supplied
characteristic-zero coefficient field C, before all allowed coefficient primes,
further scalar fields and actual C-to-L maps. The original guard `(ell : k) != 0`
remains. It is not the stronger integer-polynomial independence-of-ell theorem.

## Source bindings to reconcile before validation

- Checked native Frobenius source was compiled against fork Objects Git blob
  `2f4e4818392ffd810b3aaad227f71228febcedd3`, SHA-256
  `bf2519646471349e64f5e3069a69c6946ed8f3a7bbfb34123e681b8d581ba6f3`.
- The trace supplier uses canonical Objects Git blob
  `1816c72167afa5dc6a46b2e149d25586a589cf6b`, SHA-256
  `60178cdd4a2cbaaf44c18676b9677b85721ccc8efc04fdfe6ec0cf4a3a1fec1d`.
- The exact `NativeEndTrace.lean` source read for this proposal has SHA-256
  `2a3518cab2d90718d622b723aac6154cc443f37c2b5e7e78ed397f4e6d951a76`.
- The proposed application source has SHA-256
  `1fee5c215995dd84ed75e82b9b5f5ce0017bb64b28837c5cc765281aeb8976c0`.

The inspected native AbVar/Hom/Pt/Tate and object-bridge regions are
source-compatible. The QM leaf packages differ; no whole-package or
compiled-environment equivalence is asserted. Both inputs must be checked in
one source-bound canonical environment before adopting the application.

Use the agreed existing source-integration and validation lane. Preserve the
original supplier, all characteristic/scalar-map hypotheses, full type/body
checks, source/module origins and 3/5 same-object boundary cases. Do not copy a
compiled tree under a different binding or relax the audit to make this pass.

## Not supplied

This is a same-field application for a given abelian variety and endomorphism.
It does not construct the characteristic-zero reduction model, identify a GQ
Frobenius element, or supply the same A/A-sigma, mu, reduced varieties, F,
mu-bar and nonzero N with C10's three commuting squares at both 3 and 5.
H, TYZ reading A, Gross-Zagier, the unconditional frozen polynomial theorem,
and the end-to-end Hilbert10 consequence remain separate obligations.

No third-party trace implementation or compiled cache is copied into this
proposal. AI-assisted interface research and proposal preparation used
Metamate/Agentcloud. This branch is a proposal archive, not proof acceptance.
