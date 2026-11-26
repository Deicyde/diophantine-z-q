# rc-model-generic6 results log

Base: 796582ac1 (main after GoodRow wiring). SamePlace.lean and ComplexPoints.lean present.

## Item 1 (doc fixes)
- Commit f636d6101: generic4/generic5/target reports and fleet notes; (c) per-theorem axiom refinement dropped (kept "a subset of propext, Classical.choice, Quot.sound").

## Item 2a — `RC/ModelGeneric6/Cyclicity.lean` (builds)
- `smulSubgroup m C := C.map (m • ·)`; `atkinSum Q C := A[Q] ⊔ C` (A[Q] = `Submodule.torsionBy ℤ A Q`).
- `isAddCyclic_map_atkinSum`: Q = q^e (q prime, e>0), N = Q*M ≠ 0, Q ⟂ M, #A[d] = d² ∀ d ∣ Q, C cyclic of order N, g with g.ker = M • C ⇒ g(A[Q] ⊔ C) cyclic of order N. Proof: ZMod (q^e)² coordinates on A[Q] (vendored nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq), complement of an order-Q vector (one coordinate is a unit), explicit generator g(w + Q•c), CRT.
- `isAddCyclic_map_atkinSum_curve`: curve version, needs (N : k) ≠ 0 and (2 : k) ≠ 0 (vendored card_torsionBy_eq_sq_of_isAlgClosed); any algebraically closed k, any characteristic.
- `atkinImage`: the image as `CyclicSubgroups _ N`.
- axioms: propext, Classical.choice, Quot.sound.
