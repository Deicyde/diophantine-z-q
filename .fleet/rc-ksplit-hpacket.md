**Scoped result.** `hpacketTrace_of_packet` proves the singleton trace
reading at `p²`, the scalar action on the three weight-two blocks,
and the determinant congruence modulo integer two at the same Frobenius
lift. `hpacket_of_packets` supplies the seed's exact binder, and
`kSplitSeed_of_packets` applies the existing seed theorem.

**Manuscript verdict.** Tex 10329 holds on the stated ramified, old, and
Eisenstein blocks. The old-block argument for (O.12) at tex 9885–9889
only uses vanishing inertia differences. The singleton needs the good
polynomial on the two old degeneracy copies, proved here from their
Fourier action. The earlier support slip at tex 10393–10404 remains:
the zero branch uses the full stationary transported support. The
determinant calculation avoids that split and retains the actual sign
of the quadratic character of positive `p` at the chosen lift.

**Remaining.** The weight-two realization supplies the actual old pairs,
the two additional shifts at `p` and `p²`, and the three block Fourier
and determinant character comparisons on the selected Stage. The place
and budget lanes still supply the ring data and singleton divisions;
the trace lane supplies descent and the good coefficient formula. The
old-unit and companion inputs remain separate.

**Verified.** The five new Lean modules compile serially. The axiom
audit for all 24 new theorems lists only `propext`, `Classical.choice`,
and `Quot.sound`. No new print or leaf was added. See
`docs/research/rc-ksplit-hpacket.md` for exact inputs and the manuscript
check.

**Proof and report commit:** `ba53246e5d5efaa7c885305398c663b87c831b26`.
