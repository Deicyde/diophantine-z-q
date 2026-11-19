# Inner-limit switching objects: scope

`Objects.lean` builds the coefficient-stage inner limit of the switch coordinates along a
sequence of derivative data (manuscript, the inner limit along derivative primes with
q tending to one): limits taken on integral matrices before specialization, lift
independence, identification with the homology of the constructed limiting tame complex,
closed complementary rank-two finite and singular planes with the coefficient-precision
topology and its identification with the Tate topology, specialization at a fixed prime of
the coefficient ring, both quasi-switch sides without duality assumptions, the connecting
map of the change-of-condition sequence with its exactness, and a conditional
`QuasiNonquadStep (resAt P)` whose duality input is `FibreInnerLimitPairingCertificate`.

## Classification after independent review (2026-11-18)

This file is a **conditional algebraic helper**, not yet the arithmetic producer of the
inner-limit switch.

* **The derivative data are abstract.** `DerivativeMatrices` takes a sequence `ell` in the
  coefficient ring, not a sequence of rational primes, and records no primality,
  inertness, avoided primes, chosen Frobenius elements or the character constraint
  needed for the Frobenius matrices to tend to one. A constant sequence `ell = -1` with
  trivial Frobenius matrices and `J = 1` satisfies every field, so the arithmetic
  realization (actual primes and genuine Frobenius elements, the twisted coefficient
  action, the orientation `det J = -1`, and retained comparisons from the finite-stage
  continuous local cochains to the tame models) is still required.
* **The global and local diagram are abstract.** `fibreLimitNonquadStep` accepts an
  arbitrary stage diagram and an arbitrary localization map; neither is tied to the
  actual global model with its old local conditions or to a retained localization map.
  Its output is exactly `QuasiNonquadStep (resAt P) S₀ S₁`, not the stronger family
  supplier, which needs the side Selmer data to equal the selected family's fibres.
  The limit must not be identified with one fixed characteristic-zero fibre, where the
  singular kernel vanishes.
* **The certificate is real content.** With nonzero scalars and an involutive `J`, a
  pairing certificate forces a nonzero relaxed image and a nonzero trace, and an
  abstract diagram with the expected dimension drop admits no certificate; so the
  certificate is not a restatement of the consumer's dimension conclusion. It remains an
  unproved input for the realized diagram.
