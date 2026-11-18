# Local weights results log

- Base: 1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2.
- Split level quotient: lower coordinate of the column module modulo (p^e); multiplication by the bottom-right entry.
- Tex 8512–8515: conjugation by an order unit fixes the selected root; scalar multiplication gives the character multiplier.
- Hensel input: (F(T)=T^2-T+det y) at (y_{11}), (y=(1+x)/2), with derivative (2y_{11}-1). Tested without dividing by 2 in the dyadic order.
- Nilpotent orbit: first basis vector (Xe_i), second (e_i); determinant character independent of basis by `Odd.quadraticChar_det_eq_of_conj`.
- Coefficient ring contraction: nonunit 2 first forces evenness, then cancel and induct; valuation of 2 at a place above two is strictly less than 1.
- Checked with `lake env lean`: Models, Characters, Compact, Level, LevelRules, Nilpotent, NilpotentRules, Division, Product. Their printed theorem axioms are subsets of `propext`, `Classical.choice`, `Quot.sound`.
- Exact supports: determinant valuation one equals exact divisibility by p; affine split support equals x² a unit square; at the division prime the integral trace-zero weight is nonzero exactly on nonzero reduction.
- Ambient periods: good, integral lattice; nilpotent, zero mod p²; positive level, translations by twice the trace-zero order elements zero mod pᵏ for a character mod pᵏ; dyadic level zero, twice the trace-zero lattice zero mod two; division, trace-zero elements in the kernel of reduction.
- Division-prime input: `DivisionCoordinates`, `DivisionLocalModel`, `DivisionIdentification`. Uniformizer acts by Frobenius on reduction and weight multiplier −1 for p ≡ 3 (mod 4).
- Finite product: inverse order-unit norm multiplier and the product of the scale characters. Jacobi reciprocity identifies the ramified factors for h_* = −m.
- Coefficients: the character field is cyclotomic of two-power conductor parameter; the fixed characters lift to units at every finite place. For v above two, `coefficientRing_two` gives both directions of integer divisibility.
- Final `lake env lean`: Models, Characters, Compact, Level, LevelRules, LevelSupport, Nilpotent, NilpotentRules, Division, Product, Transport, SplitAmbient, Dyadic, SplitActions, DivisionAmbient, AmbientCongruence, SquareClass, Coefficients. All passed; 118 theorems and six additional rule definitions checked with `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound`. No new prints.
- Scoped stop: standalone construction and completion identification of the division maximal order and its Frobenius reduction. No `ThetaStage` join attempted.
