# Local weights results log

- Base: 1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2.
- Split level quotient: lower coordinate of the column module modulo (p^e); multiplication by the bottom-right entry.
- Tex 8512–8515: conjugation by an order unit fixes the selected root; scalar multiplication gives the character multiplier.
- Hensel input: (F(T)=T^2-T+det y) at (y_{11}), (y=(1+x)/2), with derivative (2y_{11}-1). Tested without dividing by 2 in the dyadic order.
- Nilpotent orbit: first basis vector (Xe_i), second (e_i); determinant character independent of basis by `Odd.quadraticChar_det_eq_of_conj`.
- Coefficient ring contraction: nonunit 2 first forces evenness, then cancel and induct; valuation of 2 at a place above two is strictly less than 1.
- Checked with `lake env lean`: Models, Characters, Compact, Level, LevelRules, Nilpotent, NilpotentRules, Division, Product. Their printed theorem axioms are subsets of `propext`, `Classical.choice`, `Quot.sound`.
