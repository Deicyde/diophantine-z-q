# Detecting-prime local division algebra

**Result.** `RC/LocalDivision/Model.lean` supplies `coordinates p : DivisionCoordinates p (D p)` and `localModel p : DivisionLocalModel (coordinates p)` for primes \(p\equiv3\pmod4\). The quaternion algebra \((-1,-p)_{\mathbb Q_p}\) is division by norm anisotropy. Its integral basis spans the compact open maximal order; its reduction has kernel \(j\mathcal O\) and quotient \(\mathbb F_{p^2}\). Inverse conjugation by \(j\) induces Frobenius. The instantiated weight has the Legendre scaling factor, is fixed by order-unit conjugation, and changes sign under the uniformizer on the full trace-zero space.

**Verification.** All six new Lean files compile individually. All 95 axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`. No prints were added. See `docs/research/rc-local-division.md` for the theorem statements and manuscript check.

**Manuscript.** Tex 8559 needs a reduction bar on \(Q_B(x)\); the right side is in the residue field. The squareclass conclusion is unchanged.

**Remaining.** Supply `DivisionIdentification` at \(p=\ell_0\): the completed algebra and completed order equivalences, compatible with inclusion and preserving reduced trace and norm. The report gives the exact types and equalities.

Verified implementation and report: `14520ca694e4cd6f7854eefea0fbe345aeb0cd7e`. The handoff is the next commit; its SHA is available with `git log -1 --format=%H -- .fleet/rc-local-division.md`.
