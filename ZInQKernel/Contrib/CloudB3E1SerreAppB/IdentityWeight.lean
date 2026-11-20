import ZInQKernel.Contrib.CloudB3E1SerreAppB.UnitBall

/-!
# Conrad's Proposition B.3 (identity line) from Serre's Appendix to Chapter III

`conradIdentityWeight_of_serre` proves the tree's `ConradIdentityWeight` (ConradBridges, the
B.3 half of `ConradAppBConcrete`) from `SerreA6Print` alone. That is Serre, *Abelian
`l`-adic representations*, 1989 ed., III-44 (A5, Theorem 2 (ii)) ⇔ III-49/50 (A6,
Proposition 6 (iv)), with (iv) read through norm functoriality of local class field theory
(GLUE, see `SerreA6.lean`).

The proof follows Conrad's p. 33 skeleton (Prop. B.3), with Serre's statement in place of
Conrad's own argument:

1. Suppose `ψ(i_{ℚ_p}(x)) = x^{-n}` near `1` (`ArtinNearOne`). For `u` in a small unit ball of
   `Kˣ`, `N_{K/ℚ_p}(u)` is near `1` (`norm_normUnits_sub_one_le`). Hence
   `ψ(i_{ℚ_p}(N u)) = N(u)^{-n} = ∏_σ σ⁻¹(u)^{-n}`, by Mathlib's
   `Algebra.norm_eq_prod_automorphisms`. This is Serre's (iv) with `n_σ = n` for all `σ`.
2. `SerreA6Print` gives (ii): `σ ∘ ψ|_{G_K} ∼ χ^n` for all `σ`. At `σ = id` this is the
   identity line `ℂ_p(ψ|_{G_K}) ≅ ℂ_p(n)` of Conrad p. 33 (`IdentityLine`).

Kind: proved from the named input `SerreA6Print`.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges
open Module
open scoped Topology Filter

/-- Serre's (ii) at `σ = id` is Conrad's identity line. Kind: proved. -/
theorem identityLine_of_serreTwistAdmissible (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ)
    (h : SerreTwistAdmissible p K ψ (AlgEquiv.refl) n) : IdentityLine p K ψ n := by
  obtain ⟨x, hx0, hx⟩ := h
  refine ⟨x⁻¹, inv_ne_zero hx0, fun g => ?_⟩
  show algebraMap K ℂ_[p] ((ψ (restrictGalois p K g) : Kˣ) : K) * x⁻¹ =
    _root_.ZInQ.Contrib.G9.PkgI4.cycPow p (restrictGalois p K g) n •
      _root_.ZInQ.Contrib.G9.PkgI4.cpAct p (restrictGalois p K g) x⁻¹
  have hg : _root_.ZInQ.Contrib.G9.PkgI4.cpAct p (restrictGalois p K g) x =
      (algebraMap K ℂ_[p] ((ψ (restrictGalois p K g) : Kˣ) : K))⁻¹ *
        algebraMap ℚ_[p] ℂ_[p] (_root_.ZInQ.Contrib.G9.PkgI4.cycPow p (restrictGalois p K g) n) *
          x := hx g
  have ha : algebraMap K ℂ_[p] ((ψ (restrictGalois p K g) : Kˣ) : K) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  have hc : algebraMap ℚ_[p] ℂ_[p]
      (_root_.ZInQ.Contrib.G9.PkgI4.cycPow p (restrictGalois p K g) n) ≠ 0 := by
    refine (map_ne_zero _).mpr ?_
    unfold _root_.ZInQ.Contrib.G9.PkgI4.cycPow
    rw [Ne, PadicInt.coe_eq_zero]
    exact Units.ne_zero _
  rw [map_inv₀, hg, Algebra.smul_def]
  field_simp

/-- **Conrad B.3, identity line, from Serre.** `SerreA6Print → ConradIdentityWeight`.
Kind: proved from the named input `SerreA6Print` (PRINT + GLUE). -/
theorem conradIdentityWeight_of_serre (h : SerreA6Print) : ConradIdentityWeight := by
  intro p _ K _ _ ψ n hc hn
  have hn' := (artinNearOnePrint_iff p ψ hc n).mpr hn
  unfold ArtinNearOnePrint at hn'
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hn'
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp hn'
  rw [Units.val_one] at hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hr0 : 0 < min ε 1 := lt_min hε one_pos
  have hr1 : min ε 1 ≤ 1 := min_le_right _ _
  have hiv : SerreA6NormForm p K ψ hc (fun _ => n) := by
    refine ⟨unitBall p K (min ε 1) hr0 hr1, isOpen_unitBall p K hr0 hr1, fun u hu => ?_⟩
    rw [mem_unitBall] at hu
    refine ⟨norm_eq_one_of_norm_sub_one_lt p (hu.trans_le hr1), ?_⟩
    have hN := norm_normUnits_sub_one_le p K u (hu.trans_le hr1).le
    have hmem : ((TauCeti.Algebra.normUnits ℚ_[p] u : ℚ_[p]ˣ) : ℚ_[p]) ∈ s := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      exact hN.trans_lt (hu.trans_le (min_le_left _ _))
    have hval := hsub (show TauCeti.Algebra.normUnits ℚ_[p] u ∈
      (fun x : ℚ_[p]ˣ => (x : ℚ_[p])) ⁻¹' s from hmem)
    simp only [Set.mem_ofPred_eq] at hval
    rw [hval, TauCeti.Algebra.coe_normUnits, Algebra.norm_eq_prod_automorphisms]
    have hprod : ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm ((u : Kˣ) : K) ^ n =
        (∏ σ : K ≃ₐ[ℚ_[p]] K, σ ((u : Kˣ) : K)) ^ n := by
      rw [Finset.prod_zpow]
      congr 1
      exact Fintype.prod_equiv (Equiv.inv (K ≃ₐ[ℚ_[p]] K)) _ _ (fun σ => rfl)
    rw [hprod]
    have hne : (∏ σ : K ≃ₐ[ℚ_[p]] K, σ ((u : Kˣ) : K)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun σ _ => (map_ne_zero σ).mpr (Units.ne_zero u)
    rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero n hne)]
  exact identityLine_of_serreTwistAdmissible p K ψ n
    ((h p K ψ hc (fun _ => n)).mpr hiv AlgEquiv.refl)

end HDec.G0Galois.C8Conrad.SerreAppB
