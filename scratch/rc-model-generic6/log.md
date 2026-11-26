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

## Item 3a — `RC/ModelGeneric6/CharFreeSeam.lean`, `CharFreeSeamTwo.lean` (build)
- Copies of generic4's gate, gate_isCentred, gate_abel, pointPlace, IsSeam, StepSeam, isSeam_comp, exists_oddStep, stepSeam_of_odd, exists_quotientSeam_of_steps, twoFFHom_seam, stepSeam_two, exists_quotientSeam, without [CharZero k]. Gate uses vendored hasPrincipalDivisors_functionField_of_isElliptic (char-free).
- StepSeam now records finrankAlong k ι = ℓ; odd: vendored finrankAlong = 2m+1; two: `finrankAlong_twoFFHom_le` (≤ 2: K(x) = whole field, x quadratic over image) + `finrankAlong_ne_one_of_seam` (a seam with nonzero kernel point is not degree 1) + positivity.
- `finrankAlong_comp'` (tower law).
- `exists_quotientSeam n hn hchar E H hH`: separable seam (FiniteAlong, finrankAlong = n, g.ker = H) for E.cyclicQuotientCurve H n whenever every prime ℓ ∣ n has (ℓ : k) ≠ 0.
- `isSeam_iff_modelGeneric4` : in char 0 the notions agree by Iff.rfl (HasPrincipalDivisors is a Prop).
- axioms: propext, Classical.choice, Quot.sound.
- Deviation: the quadratic for x over the image is re-derived inside finrankAlong_twoFFHom_le (generic4's isIntegral_X_twoFFHom does not expose the polynomial).

## Scoped stop (items 2c, 3b, 3c)
- 2c open: T1 naturality of rationalPoints on classes (needs PairClasses.map), T2 Vélu composite under embeddings, T3 seams under base change, T4 descent (only for |k| > 𝔠), T5 injectivity of PairClasses.map. Vendored descent theorems transport kernels only.
- 3b open: Y0LevelPoints computation lemma at cover points (needs private detectorCoverAlgebra), Hensel lift over W(k) (EGA IV 18.5.17 UNVERIFIED), reading comparison.
- 3c open: order-two Vélu reduction (R2), composite (R3), seam image comparison (R4); odd reduction (R1) in tree.
- Report: docs/research/rc-model-generic6.md.
