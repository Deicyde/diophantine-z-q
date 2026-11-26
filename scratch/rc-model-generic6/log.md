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

## Item 2b(1) — `RC/ModelGeneric6/VariableChangeSeam.lean` (builds)
- `vcFunHom W C : W.FF →ₐ (C • W).FF` (vendored `mrtw60aVCFunHom`: X ↦ u²X + r, Y ↦ u³Y + u²sX + t), `vcFunHomInv`, inverse laws, integrality, finiteness, `vcFunHom_X`, `vcFunHom_Y`.
- `restrictAlong_vcFunHom` (ON THE SPOT (c)): for all centred gates on W and C • W, (place of P).restrictAlong vcFunHom = place of `Point.addEquivVariableChange W C P`. Characteristic-free. Proof: transported gate (`transportGate`) is centred (`transportGate_isCentred`); centred gates are unique (vendored `GenusOnePlaceGate.ext_of_isCentred`).
- axioms: propext, Classical.choice, Quot.sound.

## Item 2b(1) cont. — `RC/ModelGeneric6/SeamLift.lean` (builds)
- `isSeam_comp'` (generic4's private lemma, same proof); `isSeam_changePoints` (changePoints is a seam via vcFunHomInv); `isSeam_changePoints_symm` (its inverse via vcFunHom).
- `exists_lift_of_seam`: seam f between period curves of L₁, L₂ ⇒ ∃ α, f (toPoint z) = toPoint (α z). Vendored lift exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint + exists_smul_mem_and_apply_eq_of_forall_sub_mem + pointMapOfPushforward_eq_of_seam.
- axioms: propext, Classical.choice, Quot.sound.

## Item 2b — `RC/ModelGeneric6/ComplexStep.lean` (builds)
- `analyticCyclicPair_eq_of_scale'`: generic4's homothety lemma for an arbitrary period pair P with IsScale P (ofTau τ') α.
- `not_mem_span_half`, `mem_span_iff_atkin` (ℤτ + ℤ/Q = ω₂(ℤτ' + ℤ), ω₂ = Mcτ + d, Q(ad) − M(bc) = 1).
- `atkinPair_complex`: complex pair (E, C) with class analyticCyclicPair τ, every seam g : E → E.cyclicQuotientCurve C_Q Q with g.ker = C_Q = (N/Q)•C ⇒ class of (E', g(E[Q] ⊔ C)) = analyticCyclicPair (atkinGL hQ • τ). Q = q^e, Q ∥ N.
- `rationalPoints_atkinRat_complex_moduli`: target theorem of item 2 for k = ℂ (every representative, every seam).
- `atkinClass_independent`: independence corollary.
- Route: seams conjugated by variable-change seams; lift z ↦ αz; kernel ⟨τ, 1/Q⟩ ⇒ L₂ = α(ℤτ + ℤ/Q); AL matrix (exists_entries) ⇒ IsScale L₂ (ofTau W_Qτ) (αω₂); ω₂/N = cτ/Q + d/N generates ⟨τ/Q,1/N⟩ mod ℤτ+ℤ/Q (explicit: τ/Q = −Mb·ω₂/N + adτ + bd/Q, 1/N = Qa·ω₂/N − acτ − bc/Q).
- axioms: propext, Classical.choice, Quot.sound.
