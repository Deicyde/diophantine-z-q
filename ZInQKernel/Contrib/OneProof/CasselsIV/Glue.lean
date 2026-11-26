import ZInQKernel.Contrib.OneProof.CasselsIV.Row
import ZInQKernel.Contrib.OneProof.CasselsTatePS.Basic

/-!
# Glue: Cassels (1962), Theorem 1.1, gives the form printed by Poonen–Stoll

`SelmerTwoPower.casselsTatePairingPS_of_casselsIV : CasselsIVThm11 E → CasselsTatePairingPS E`,
clause by clause, with the same pairing `l`:

* alternating: Cassels's (viii), directly;
* `l` kills the maximal divisible subgroup: every class of `sha E` has finite order `N`
  (`exists_nsmul_eq_zero_H1`), and an element `x` of `divisiblePart (sha E)` is `N • g`, so
  `l x y = l g (N • y) = 0` by biadditivity;
* kernel elements are infinitely divisible: if `l x y = 0` for every `y`, then `l ξ x = 0` for
  every `ξ` (skew-symmetry, from alternation), so the hypothesis of Theorem 1.1 holds for `x` at
  every `m > 0`, and `x = m • H`.

No finiteness of `Ш/qШ` or `Ш[q]` is needed: the target clause is element-wise divisibility, not
membership in `divisiblePart`.

Then, at the curves `E_ℓ` (elliptic for `ℓ ≠ 0`, `PoleRC.curve_isElliptic`):

* `PoleS12.casselsTatePairingCurvesPS_of_casselsIV : CasselsIVThm11Elliptic →
  CasselsTatePairingCurvesPS`;
* `PoleS12.SilvermanRank.poleCompleteness_of_rankOne_casselsIV`: the consumer
  `poleCompleteness_of_rankOne_PS` fed by it.

No statement is changed.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology

/-- **Cassels's Theorem 1.1 gives the form printed by Poonen–Stoll**, with the same pairing. -/
theorem casselsTatePairingPS_of_casselsIV {E : WeierstrassCurve ℚ} (h : CasselsIVThm11 E) :
    CasselsTatePairingPS E := by
  obtain ⟨l, halt, hdiv⟩ := h
  have hskew : ∀ x y, l x y = -l y x := fun x y => by
    have := halt (x + y)
    simp only [map_add, AddMonoidHom.add_apply, halt, zero_add, add_zero] at this
    rw [eq_neg_iff_add_eq_zero]
    rwa [add_comm] at this
  refine ⟨l, halt, fun x hx y => ?_, fun x hx n hn => ?_⟩
  · obtain ⟨N, hN0, hN⟩ :=
      exists_nsmul_eq_zero_H1 E (y : H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff)
    have hNy : N • y = 0 :=
      Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hN)
    obtain ⟨g, rfl⟩ := exists_nsmul_eq_of_mem_divisiblePart hx hN0
    rw [map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul (l g), hNy, map_zero]
  · obtain ⟨H, hH⟩ := hdiv n (Nat.pos_of_ne_zero hn) x
      (fun ξ _ => by rw [hskew, hx ξ, neg_zero])
    exact ⟨H, hH.symm⟩

end ZInQ.Manuscript.SelmerTwoPower

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.SelmerTwoPower

/-- **The printed form at the curves `E_ℓ` from Cassels's Theorem 1.1**: `E_ℓ` is elliptic for
`ℓ > 0`, so the instance of `CasselsIVThm11Elliptic` at `E_ℓ` gives `CasselsTatePairingPS`. -/
theorem casselsTatePairingCurvesPS_of_casselsIV (h : CasselsIVThm11Elliptic) :
    CasselsTatePairingCurvesPS := by
  intro ℓ hℓ _ _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  exact casselsTatePairingPS_of_casselsIV (h _ (PoleRC.curve_isElliptic hℓ0))

end ZInQ.Manuscript.PoleS12

namespace ZInQ.Manuscript.PoleS12.SilvermanRank

/-- **The consumer `poleCompleteness_of_rankOne_PS` from Cassels's Theorem 1.1**, with the same
conclusion as `poleCompleteness_of_rankOne`. -/
theorem poleCompleteness_of_rankOne_casselsIV
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : SelmerTwoPower.CasselsIVThm11Elliptic)
    (hRank : PoleRC.KolyvaginRankOne) : PoleCompleteness :=
  poleCompleteness_of_rankOne_PS hRC (casselsTatePairingCurvesPS_of_casselsIV hCT) hRank

end ZInQ.Manuscript.PoleS12.SilvermanRank

end

#print axioms ZInQ.Manuscript.SelmerTwoPower.casselsTatePairingPS_of_casselsIV
#print axioms ZInQ.Manuscript.PoleS12.casselsTatePairingCurvesPS_of_casselsIV
#print axioms ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne_casselsIV
