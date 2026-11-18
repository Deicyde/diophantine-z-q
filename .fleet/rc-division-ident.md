# The detecting-prime join

**Result.** For \(p=\ell_0\equiv3\bmod 4\), `DivisionJoin.identification` supplies all fields of `DivisionIdentification` for the completion of `explicitOrderAt p h`. Its ambient map preserves the four quaternion coordinates, the reduced trace, and the reduced norm. Its restriction identifies the completed order with the integral span of \(1,i,j,ij\), compatibly with both inclusions.

**Maximality and weight.** `DivisionJoin.ramified_maximal` has the exact type of the detecting-prime clause of `IsEichler` for this order. The proof includes finiteness, full rational span, and maximality against each full finite overorder. On the completed order, the transported weight is fixed by order-unit conjugation, scales by the residue character on scalar units, and changes sign under the uniformizer on trace zero. Its nonzero trace-zero support has nonzero square norm residue.

**Verification.** `Ambient.lean`, `Order.lean`, and `Identification.lean` under `ZInQKernel/Contrib/OneProof/RC/DivisionJoin/` compile individually with `lake env lean`. All 30 axiom checks are within `propext`, `Classical.choice`, and `Quot.sound`. See `docs/research/rc-division-ident.md` and `scratch/rc-division-ident/log.md`.

**Manuscript and scope.** Tex 8559 needs a reduction bar on \(Q_B(x)\); its square and the character conclusion are in the residue field. No detecting-prime proof obligation in this join remains. The other places, the global level and adelic statements, and \(P_M\) are outside this proof.

Final proof and report SHA: `1f7f92435f16876b5bf220db4097654efba582b2`. The final branch commit is this handoff; its SHA is given by `git log -1 --format=%H -- .fleet/rc-division-ident.md`.
