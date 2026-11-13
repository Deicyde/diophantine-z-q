# g1-adelic2: G1-adelic over Mathlib's finite adeles `𝔸ᶠ[ℤ, ℚ]`

## Main result (VERIFIED: compiled, standard axioms only)

Files: `ZInQKernel/Contrib/G1Adelic/FiniteAdele.lean` and `ZInQKernel/Contrib/G1Adelic/Complements.lean`
(namespace `G1Adelic.FA`). They import t30-adelic's `ZInQKernel.HDecomp.Textbook.G1Adelic` from main
(namespace `G1Adelic`: `BA = Πʳ p : Nat.Primes, [Bp p, OpSub p]`, `Nhat`, `K0`, `Zhat`, `K3`, `gamma_order`).
Notation: `AF := FiniteAdeleRing ℤ ℚ` (= `𝔸ᶠ[ℤ, ℚ]`), `HA := ℍ[AF, 2, 0, -3]`, `pe := Rat.HeightOneSpectrum.primesEquiv`.

**The count over Mathlib's objects.**
```lean
theorem G1Adelic.FA.gamma_order_AF : (ZAF ⊔ K3AF).relIndex NAF = 144
theorem G1Adelic.FA.relIndex_eq_four_AF : (ZAF ⊔ K0AF).relIndex NAF = 4
theorem G1Adelic.FA.relIndex_K3_AF : ((ZAF ⊓ K0AF) ⊔ K3AF).relIndex K0AF = 36
theorem G1Adelic.FA.gamma_count_Zint_AF :
    (ZAF ⊔ K3AF).relIndex NAF = (ZAF ⊔ K0AF).relIndex NAF * (ZintAF ⊔ K3AF).relIndex K0AF ∧
      (ZAF ⊔ K0AF).relIndex NAF = 4 ∧ (ZintAF ⊔ K3AF).relIndex K0AF = 36
```
with the subgroups of `HAˣ` defined directly on Mathlib's objects:
- `ZhatAF : Set AF := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}` (ℤ̂);
  `ZhatAF_eq_range_structureMap`: it is the range of `RestrictedProduct.structureMap` (Mathlib's `∏_v ℤ_v → 𝔸ᶠ`).
- `qcoord x = ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]` (coordinates in N5's basis
  `1, i, (1+j)/2, (i+ij)/2` of `𝒪`); `OhatAF : Set HA := {x | ∀ k, qcoord x k ∈ ZhatAF}` (𝒪̂), as a subring `OhatSubAF`;
  `OhatAF_eq_span : OhatAF = {x | ∃ a : Fin 4 → AF, (∀ k, a k ∈ ZhatAF) ∧ x = ∑ k, a k • eAF k}` (𝒪̂ = 𝒪 ⊗ ℤ̂).
- `NAF : Subgroup HAˣ`, carrier `{x | ∀ y : HA, y ∈ OhatAF ↔ (x : HA) * y * ((x⁻¹ : HAˣ) : HA) ∈ OhatAF}` (normalizer of 𝒪̂);
- `K0AF := OhatSubAF.toSubmonoid.units`; `ZAF := (Units.map (algebraMap AF HA : AF →* HA)).range` (𝔸ᶠ^×);
- `K3AF`, carrier `{u | u ∈ K0AF ∧ ∃ w ∈ OhatAF, (u : HA) - 1 = 3 * w}`;
- `ZintAF := ZhatSubAF.toSubmonoid.units.map (Units.map (algebraMap AF HA : AF →* HA))` (ℤ̂^×),
  `ZAF_inf_K0AF : ZAF ⊓ K0AF = ZintAF`.

**The identifications.**
```lean
noncomputable def G1Adelic.FA.Theta : BA ≃+* HA          -- B̂ = Πʳ_p [B_p, 𝒪_p] ≃ ℍ[𝔸ᶠ[ℤ,ℚ],2,0,-3]
noncomputable def G1Adelic.FA.quatRP : HA ≃+* Πʳ v : HeightOneSpectrum ℤ, [ℍ[v.adicCompletion ℚ,2,0,-3], Hstd v]
noncomputable def G1Adelic.FA.baseChange (A : Type*) [CommRing A] [Algebra ℚ A] :
    A ⊗[ℚ] ℍ[ℚ, 2, 0, -3] ≃ₐ[A] ℍ[A, 2, 0, -3]
noncomputable def G1Adelic.FA.tensorEquivBA : AF ⊗[ℚ] ℍ[ℚ, 2, 0, -3] ≃+* BA   -- B ⊗_ℚ 𝔸ᶠ ≃ B̂
theorem G1Adelic.FA.map_Nhat : Nhat.map ThetaU.toMonoidHom = NAF     -- ThetaU := Units.mapEquiv Theta
theorem G1Adelic.FA.map_K0   : K0.map ThetaU.toMonoidHom = K0AF
theorem G1Adelic.FA.map_Zhat : Zhat.map ThetaU.toMonoidHom = ZAF
theorem G1Adelic.FA.map_K3   : K3.map ThetaU.toMonoidHom = K3AF
noncomputable def G1Adelic.FA.quotEquivAF : NAF ⧸ (ZAF ⊔ K0AF).subgroupOf NAF ≃*
    ((Bp 2)ˣ ⧸ Hloc P2 hP2) × ((Bp 3)ˣ ⧸ Hloc P3 hP3)
theorem G1Adelic.FA.Theta_re (y : BA) (v : HeightOneSpectrum ℤ) :
    (Theta y).re v = (phi v).symm (y (pe v)).re   -- rfl; likewise imI, imJ, imK
```
`phi v : v.adicCompletion ℚ ≃A[ℚ] ℚ_[((pe v : Nat.Primes) : ℕ)]` is Mathlib's
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv v` behind `irreducible_def`.

`#print axioms` (lake build output) of `Theta`, `gamma_order_AF`, `relIndex_eq_four_AF`, `relIndex_K3_AF`,
`ZhatAF_eq_range_structureMap`, `ZAF_inf_K0AF`, `gamma_count_Zint_AF`, `OhatAF_eq_span`, `quotEquivAF`,
`baseChange`, `tensorEquivBA`: each `[propext, Classical.choice, Quot.sound]`.

Build: `lake build ZInQKernel.Contrib.G1Adelic.FiniteAdele` (19 s) and
`lake build ZInQKernel.Contrib.G1Adelic.Complements` (6 s), both OK on the merged branch (origin/main merged at 03:35).

## How the two earlier obstacles were avoided (VERIFIED)

- Index by `v : HeightOneSpectrum ℤ` and use `adicCompletion.padicEquiv v : ℚ_v ≃A[ℚ] ℚ_[primesEquiv v]`, which needs
  no cast; never use `Padic.adicCompletionEquiv` or `PadicInt.adicCompletionIntegersEquiv` (the instance mismatch
  and the kernel timeouts of t30-adelic's log). The integers are handled by one lemma
  `mem_integers_iff : x ∈ v.adicCompletionIntegers ℚ ↔ ‖phi v x‖ ≤ 1` (from `padicEquiv_bijOn`), proved once
  with `phi` irreducible.
- The reindexing along `primesEquiv` is `RestrictedProduct.mapAlongRingHom`; its inverse comes from
  `RingEquiv.ofBijective`. For surjectivity the reindexed family is hidden behind `∃` (`exists_reindex`):
  a `let y₀ := Equiv.piCongrLeft …` followed by `change` makes the kernel reduce the cast along
  `pe.apply_symm_apply` and time out.
- `ℍ[AF, 2, 0, -3] ≃+* Πʳ_v [ℍ[ℚ_v], ℍ[ℤ_v]]` (`quatRP`) holds by `rfl` componentwise.
- Base change: `AlgHom.liftEquiv` gives `A ⊗[ℚ] ℍ[ℚ] →ₐ[A] ℍ[A]`. It sends `Algebra.TensorProduct.basis A basisOneIJK`
  to `basisOneIJK`, so it equals the linear equiv `Basis.equiv` and is bijective.

No Tau Ceti code was vendored or used.

## What remains

Nothing in the task scope. The quotient `Y₃/Γ' = P¹_j` in G1 still needs R1's objects (h-decomposition, G1 row).
No leaf `def … : Prop` in `Leaves.lean`/`HDecomp` is stated over `FiniteAdeleRing`, so these results close no leaf.
They make A3's adelic count a statement about Mathlib's `𝔸ᶠ[ℤ, ℚ]`.
