import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j

/-! # Point maps of the iterated Vélu quotient in characteristic zero -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric3

open ModularCurve
open P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {k : Type} [Field k] [CharZero k] [DecidableEq k] [IsAlgClosed k]

/-- The prime-kernel step in the vendored iteration comes with the actual
Vélu map on points, including its effect on the remaining subgroup. -/
theorem exists_stepPointMap (E : WeierstrassCurve k) [E.IsElliptic]
    (H : AddSubgroup E.toAffine.Point) {n p : ℕ}
    (hn : n ≠ 0) (hH : IsAddCyclic H ∧ Nat.card H = n) (hp : p.Prime) (hpn : p ∣ n) :
    (E.stepCurve H p).IsElliptic ∧
      ∃ f : E.toAffine.Point →+ (E.stepCurve H p).toAffine.Point,
        f.ker ≤ H ∧ Nat.card f.ker = p ∧ H.map f = E.stepSubgroup H p := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsAddCyclic H := hH.1
  let : Finite H := finite_of_mem_cycSub hn hH
  let : Fintype H := Fintype.ofFinite H
  let data := Classical.choice (nonempty_modularPolynomialData p)
  have hcast : (p : k) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨pkg⟩ := nonempty_stepPkg E hcast data
  let := pkg.fι
  have hcard : Nat.card (CycSub E.toAffine.Point p) = p + 1 := by
    have he : E.baseChange k = E := E.map_id
    have hc := natCard_cycSub (k := k) (Ω := k) E hcast
    rw [he, ModularCurve.dedekindPsi_prime hp] at hc
    exact hc
  let kernels : pkg.ι → CycSub E.toAffine.Point p := fun i =>
    ⟨(pkg.φ i).ker, isAddCyclic_of_prime_card (pkg.ker_card i), pkg.ker_card i⟩
  have hinj : Function.Injective kernels :=
    fun i j h => pkg.ker_inj i j (congrArg Subtype.val h)
  have : Finite (CycSub E.toAffine.Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hsurj := (hinj.bijective_of_nat_card_le
    (by rw [hcard, Nat.card_eq_fintype_card, pkg.card_ι])).2
  have hdvd : p ∣ Fintype.card H := by rw [Fintype.card_eq_nat_card, hH.2]; exact hpn
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have hq' : addOrderOf (q : E.toAffine.Point) = p :=
    (addOrderOf_injective H.subtype Subtype.coe_injective q).trans hq
  let D := AddSubgroup.zmultiples (q : E.toAffine.Point)
  have hD : D ∈ CycSub E.toAffine.Point p :=
    ⟨inferInstance, by rw [Nat.card_zmultiples, hq']⟩
  obtain ⟨i, hi⟩ := hsurj ⟨D, hD⟩
  have hker : (pkg.φ i).ker ≤ H :=
    (congrArg Subtype.val hi).le.trans (AddSubgroup.zmultiples_le.mpr q.property)
  have h := pkg.bridge H i hker
  have result (s : Σ V : WeierstrassCurve k, AddSubgroup V.toAffine.Point)
      (hs : s = ⟨pkg.W i, H.map (pkg.φ i)⟩) :
      s.1.IsElliptic ∧ ∃ f : E.toAffine.Point →+ s.1.toAffine.Point,
        f.ker ≤ H ∧ Nat.card f.ker = p ∧ H.map f = s.2 := by
    subst s
    exact ⟨pkg.hW i, pkg.φ i, hker, pkg.ker_card i, rfl⟩
  exact result _ h

/-- The vendored iterated quotient curve is elliptic and the composition of
its prime-degree Vélu maps has exactly the specified cyclic kernel. -/
theorem exists_cyclicQuotientPointMap (n : ℕ) (hn : n ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (hH : IsAddCyclic H ∧ Nat.card H = n) :
    (E.cyclicQuotientCurve H n).IsElliptic ∧
      ∃ f : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point, f.ker = H := by
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases h₁ : n = 1
    · subst n
      rw [cyclicQuotientCurve_one]
      exact ⟨inferInstance, AddMonoidHom.id _, by
        rw [AddMonoidHom.ker_id]; exact (AddSubgroup.card_eq_one.mp hH.2).symm⟩
    have h₂ : 2 ≤ n := by omega
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime h₁
    have hd : p ∣ n := Nat.minFac_dvd n
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hd
    obtain ⟨he, f, hf, hcard, hsub⟩ := exists_stepPointMap E H hn hH hp hd
    have hmap : H.map f ∈ CycSub _ (n / p) :=
      map_mem_cycSub f hp.ne_zero (hmul.symm ▸ hH) hf hcard
    have hm : n / p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hmul
      exact hn hmul.symm
    have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt
    let := he
    obtain ⟨hW, g, hg⟩ := ih (n / p) hlt hm (E.stepCurve H p) (H.map f) hmap
    rw [cyclicQuotientCurve_eq_of_two_le E H h₂, ← hsub]
    refine ⟨hW, g.comp f, ?_⟩
    rw [← AddMonoidHom.comap_ker, hg]
    exact comap_map_eq_of_ker_le f hf

/-- Compose the actual prime-kernel Vélu maps in the order used by
the vendored quotient curve. The map has kernel H. -/
noncomputable def cyclicQuotientPointMap (n : ℕ) (hn : n ≠ 0) (E : WeierstrassCurve k)
    [E.IsElliptic] (H : AddSubgroup E.toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = n) :
    { f : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point // f.ker = H } :=
  ⟨(exists_cyclicQuotientPointMap n hn E H hH).2.choose,
    (exists_cyclicQuotientPointMap n hn E H hH).2.choose_spec⟩

#print axioms exists_stepPointMap
#print axioms exists_cyclicQuotientPointMap
#print axioms cyclicQuotientPointMap

end WeierstrassCurve.ModelLevels.ModelGeneric3
