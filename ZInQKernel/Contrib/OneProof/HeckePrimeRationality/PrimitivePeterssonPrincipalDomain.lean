import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonCosetUnfolding
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex

/-!
# The actual principal-group fundamental domain in weight k≥3

For N≥3 the principal group has trivial intersection with the centre. Its
actual image in PSL₂ therefore acts through a genuine group equivalence.
The centre-corrected standard-domain tiling is transported to a fundamental
domain for Γ(N) itself and used in the proved parabolic-coset unfolding.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set UpperHalfPlane Complex Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

lemma principal_neg_one_not_mem (N : ℕ) (hN : 3 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma N := by
  intro hg
  have h00 := (CongruenceSubgroup.Gamma_mem.mp hg).1
  have he : (-1 : ZMod N) = 1 := by simpa using h00
  have h2 : (2 : ZMod N) = 0 := by
    have ht : (1 : ZMod N)+(1 : ZMod N) = 0 :=
      (congrArg (fun z : ZMod N => z+1) he.symm).trans (neg_add_cancel 1)
    convert ht using 1 <;> ring
  have hd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp h2
  have hn := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- The actual image in the group that acts effectively on ℍ. -/
abbrev principalPSL (N : ℕ) := (CongruenceSubgroup.Gamma N).map
  (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- Actual principal group to its effective image. -/
def principalToPSL (N : ℕ) (g : CongruenceSubgroup.Gamma N) : principalPSL N :=
  ⟨QuotientGroup.mk' _ g, g, g.2, rfl⟩

lemma principalToPSL_bijective (N : ℕ) (hN : 3 ≤ N) : Function.Bijective (principalToPSL N) := by
  constructor
  · intro a b hab
    have he : (QuotientGroup.mk (a : SL(2, ℤ)) : PSL(2, ℤ)) = QuotientGroup.mk (b : SL(2, ℤ)) :=
      congrArg Subtype.val hab
    have hc := QuotientGroup.eq.mp he
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with hc | hc
    · exact Subtype.ext (inv_mul_eq_one.mp hc)
    · exact (principal_neg_one_not_mem N hN
        (hc ▸ (CongruenceSubgroup.Gamma N).mul_mem
          ((CongruenceSubgroup.Gamma N).inv_mem a.2) b.2)).elim
  · rintro ⟨g,γ,hγ,hg⟩
    exact ⟨⟨γ,hγ⟩,Subtype.ext hg⟩

/-- The concrete centre-corrected union of standard-domain translates. -/
def principalDomain (N : ℕ) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma N).withCenter, (q.out)⁻¹ • ModularGroup.fdo

/-- The actual geometric fundamental-domain proof; no given-domain input. -/
theorem principalDomain_fundamental (N : ℕ) (hN : 3 ≤ N) :
    IsFundamentalDomain (CongruenceSubgroup.Gamma N) (principalDomain N) volume := by
  have hP := ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter
    (CongruenceSubgroup.Gamma N)
  let e : (CongruenceSubgroup.Gamma N) ≃ principalPSL N :=
    Equiv.ofBijective (principalToPSL N) (principalToPSL_bijective N hN)
  have ha (g : principalPSL N) (τ : ℍ) : (e.symm g) • τ = g • τ := by
    have he := congrArg (fun j : principalPSL N => j • τ) (e.apply_symm_apply g)
    exact he
  have h := hP.preimage_of_equiv (f := id) (QuasiMeasurePreserving.id volume)
    e.symm.bijective (fun g τ => ha g τ)
  exact h

/-- Every transported term is integrable and its norm integrals are summable
on the actual principal-domain construction. -/
theorem actual_domain_periodizedSeed_integrable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    (∀ q : parabolicQuotient N, IntegrableOn (periodizedSeedTerm N k f q) (principalDomain N) volume) ∧
      Summable (fun q : parabolicQuotient N =>
        ∫ τ in principalDomain N, ‖periodizedSeedTerm N k f q τ‖) :=
  periodizedSeed_integrable_summable N k hk f _ (principalDomain_fundamental N hN)

/-- Actual-domain absolutely convergent unfolding zero, with all geometric
and analytic prerequisites produced. This does not identify the sum with an
actual primitive Eisenstein modular form. -/
theorem actual_domain_periodizedSeed_integral_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    ∫ τ in principalDomain N, (∑' q : parabolicQuotient N, periodizedSeedTerm N k f q τ) = 0 :=
  periodizedSeed_integral_zero N k hk f _ (principalDomain_fundamental N hN)

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
