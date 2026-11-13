
/-! ## g0-assemble: g0-mod-galois' glue `ResQFiniteIndex`, proved

`[G_ℚ : G_K] < ∞` for a number field `K`, with `G_K → G_ℚ` Mathlib's `Field.absoluteGaloisGroup.map`
(g0-mod-galois' `resQ`). Proof: g0-mod-field's `resQ_comm'` gives the embedding `g : ℚ̄ → K̄`
that `map` uses; `g` is bijective. For a primitive element `α` of `K/ℚ` and `β = g⁻¹(α)`, every
`τ ∈ G_ℚ` fixing `β` is `resQ σ` for `σ = g τ g⁻¹ ∈ G_K` (it fixes `K = ℚ[α]`), so the stabilizer
of `β` lies in the range; its index is the size of the orbit of `β`, which lies in the finite set
of roots of the minimal polynomial of `β`. -/

section G0AssembleResQSec

namespace HSyn.G0AssembleMod

open G0ModField

theorem resQFiniteIndex : G0Galois.ResQFiniteIndex := by
  intro K _ _
  obtain ⟨g0, hcomm⟩ := resQ_comm' K
  let g : Qbar →ₐ[ℚ] AlgebraicClosure K := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := by
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
    haveI : Algebra.IsAlgebraic K (AlgebraicClosure K) := AlgebraicClosure.isAlgebraic K
    exact Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure K) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure K) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure K) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eg : Qbar ≃+* AlgebraicClosure K := RingEquiv.ofBijective g.toRingHom hgbij
  let ψ : K →ₐ[ℚ] AlgebraicClosure K := IsScalarTower.toAlgHom ℚ K (AlgebraicClosure K)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have hadj : Algebra.adjoin ℚ {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα]
    rfl
  let β : Qbar := eg.symm (ψ α)
  have hβ : g β = ψ α := eg.apply_symm_apply (ψ α)
  -- the stabilizer of `β` lies in the range of `resQ K`
  let H : Subgroup (Qbar ≃ₐ[ℚ] Qbar) := MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) β
  have hH : H ≤ (G0Galois.resQ K).range := by
    intro τ hτ
    have hτβ : τ β = β := hτ
    let σ₀ : AlgebraicClosure K ≃+* AlgebraicClosure K :=
      (eg.symm.trans τ.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ x) := by
      intro x
      show eg (τ (eg.symm (eg x))) = g (τ x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hext : ((σ₀ : AlgebraicClosure K →+* AlgebraicClosure K).toRatAlgHom.comp ψ) = ψ := by
      apply AlgHom.ext_of_adjoin_eq_top hadj
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      show σ₀ (ψ α) = ψ α
      rw [← hβ, hσ₀, hτβ]
    have hfix : ∀ y : K, σ₀ (algebraMap K (AlgebraicClosure K) y) =
        algebraMap K (AlgebraicClosure K) y := fun y => congrArg (fun f => f y) hext
    let σ : Field.absoluteGaloisGroup K := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ K σ) x) = g (τ x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x
  -- the stabilizer has finite index: the orbit of `β` consists of roots of its minimal polynomial
  have hint : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  have horb : (MulAction.orbit (Qbar ≃ₐ[ℚ] Qbar) β).Finite := by
    refine (Polynomial.rootSet_finite (minpoly ℚ β) Qbar).subset ?_
    rintro _ ⟨τ, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    show Polynomial.aeval (τ β) (minpoly ℚ β) = 0
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  haveI : H.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, MulAction.index_stabilizer]
    exact (Set.ncard_pos horb).mpr ⟨β, MulAction.mem_orbit_self β⟩ |>.ne'
  exact Subgroup.finiteIndex_of_le hH

end HSyn.G0AssembleMod

end G0AssembleResQSec

#print axioms HSyn.G0AssembleMod.resQFiniteIndex
