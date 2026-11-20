The intrinsic unary law is proved. `ZInQ.Manuscript.RC.EvenUnary.evenUnaryStageLaw` in `ZInQKernel/Contrib/OneProof/RC/EvenUnary/Complete.lean` proves the unchanged proposition at `maskedLevel P * j` for every positive shell. It uses the actual convergent `unaryFun`, and on units gives the prescribed product of the phase character, the parity character, and the Kronecker symbol. The proof includes holomorphy and boundedness at every cusp.

`evenExpansion_of_unary` supplies the actual weight-two form and transfers its positive Fourier coefficients to the fixed-place lattice under the existing embedding and coordinate match. The moving sieve law and constituent coordinate match remain separate inputs. No existing Lean file or statement was changed.

All 13 proof modules and the scratch audit passed direct Lean checks. The 72 audited theorem declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Host load stopped the extra dependency rebuild after the direct checks. See `docs/research/rc-even-unary.md` and `scratch/rc-even-unary/axioms.txt`.

No new manuscript error was found in the unary passage. The inherited recurrence shorthand at tex 8162–8167 omits the reference coefficient; the explicit formula at tex 8168–8176 restores it. The unary proof uses neither formula.
