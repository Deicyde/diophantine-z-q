import ZInQKernel.Contrib.OneProof.HP23Proof.Generic
import ZInQKernel.Contrib.OneProof.HfxProof.Case3

/-!
# hp23-proof: the partition data for `n ≡ 3 (mod 8)`

Task hp23-proof. A copy of hfx-proof's `HfxProof.testVector_three` (`HfxProof/Case3.lean`) whose
conclusion is the partition data (`PartData`) instead of the test vector built from it, together with
the parity of the generator: `F` takes the values `−3` and `1` (two orbits, sizes 2 and 6), both odd.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.HP23Proof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

-- contrib-clashes: `private`, so that the auto-generated instance name does not collide with the
-- identical local instance of a sibling module when both are imported.
private local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- **The partition data for `n ≡ 3 (mod 8)`** (hfx-proof's `testVector_three`, with the conclusion
`testVector_of_partition` replaced by its hypotheses), and `F ∈ {−3, 1}` is odd. -/
theorem partition_three {n : ℕ} [NeZero n] (hsq : Squarefree n) (h3 : n % 8 = 3)
    {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ∃ hv : IsPlaceTwo v, ∃ F : T8 → ℤ,
      PartData n τ v F ∧ ∀ t, Odd (F t) := by
  classical
  obtain ⟨v, hv⟩ := exists_isPlaceTwo
  obtain ⟨a, b, c, hvq, hn, -⟩ := exists_abc hτ (Or.inr h3)
  have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 3 := by
    have := Nat.div_add_mod n 8; rw [h3] at this; exact_mod_cast this.symm
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := odd_of_three (hk ▸ hn)
  set ωZ := ωH3 a' b' c' with hωZ
  set ω : ℍ[ℚ] := hurZ ωZ with hωdef
  set N : ℤ := a' ^ 2 + a' + b' ^ 2 + b' + c' ^ 2 + c' + 1 with hNdef
  have hN : 4 * N = (2 * a' + 1) ^ 2 + (2 * b' + 1) ^ 2 + (2 * c' + 1) ^ 2 + 1 := by rw [hNdef]; ring
  have hNo : Odd N := odd_N3 a' b' c'
  have hω2 : ω * ω = ω - (N : ℚ) • 1 := by
    rw [hωdef, hurZ_ωH3, hNdef]; ext <;> simp <;> ring
  have hst : star ω = 1 - ω := by rw [hωdef, hurZ_ωH3]; ext <;> simp <;> ring
  have hωv : ω = (1 / 2 : ℚ) • (1 + τ (sqrtNeg n)) := by rw [hvq, hωdef, hurZ_ωH3]
  have hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ω := by
    intro x; rw [hωv]; exact tau_span3 hsq h3 τ x
  set C := C3 ω N (isHurZ_hurZ _) hω2 hst with hCdef
  have hH : HgrpN n τ ≤ SgC v hv C := by
    refine HgrpN_le_SgC hv C (isHurZ_hurZ _) hspan ?_ ?_ ?_
    · intro p _ _ cc hcc; exact ⟨cc, hcc, 1, by simp, isHur_one, by simp, InR.one⟩
    · intro p _ _ u hu hnu hR; exact ⟨1, one_ne_zero, u, by simp, hu, hnu, hR⟩
    · intro p _ hp y hy hcomm
      rw [hvq] at hcomm
      exact loc2OK_of_commute3 hp hN hNo hy hcomm
  -- the table entry
  set r := mapH (Int.castRingHom (ZMod 4)) ωZ with hrdef
  obtain ⟨e, he, her⟩ := tab3_complete r.a0 r.a1 r.a2 r.a3
    (by show ((2 * c' + 1 : ℤ) : ZMod 4) = 1 ∨ ((2 * c' + 1 : ℤ) : ZMod 4) = 3
        push_cast; exact zmod4_odd_cases _)
    (by show 2 * ((c' + 1 : ℤ) : ZMod 4) = 1 + ((2 * c' + 1 : ℤ) : ZMod 4)
        push_cast; ring)
  have her' : e.r = r := her
  -- merges
  have hM0 : ∀ t, twoRep v t ∈ DC n τ (twoRep v (e.root t)) := by
    intro t
    obtain ⟨hm1, hm2, -⟩ := tab3_merge e he t
    set w := e.wit.getD (idx8 t) (0, 0, 0, 0)
    set μ := unitList.getD w.2.2.1.val ⟨1, 0, 0, 0⟩ with hμdef
    have hμ1 : nrdH μ = 1 := unitList_nrdH μ (getD_mem_unitList _)
    have hsg : (sg w.2.2.2 : ℤ) ^ 2 = 1 := by have := sg_sq w.2.2.2; exact_mod_cast this
    set αZ : H4 ℤ := ⟨(w.1.val : ℤ) + (w.2.1.val : ℤ) * ωZ.a0, (w.2.1.val : ℤ) * ωZ.a1,
      (w.2.1.val : ℤ) * ωZ.a2, (w.2.1.val : ℤ) * ωZ.a3⟩ with hαZ
    have hα4 : mapH (Int.castRingHom (ZMod 4)) αZ = alpha4 e.r w.1 w.2.1 := by
      rw [her', hrdef]; simp only [hαZ, mapH, alpha4, map_add, map_mul, eq_intCast, natCast_val_zmod4]
    set A : H4 ℤ := smulH (sg w.2.2.2) (mulH μ (βZ (e.root t))) with hAdef
    set B : H4 ℤ := mulH (βZ t) αZ with hBdef
    have hA4 : mapH (Int.castRingHom (ZMod 4)) A = rhoBeta4 w.2.2.1 w.2.2.2 (e.root t) := rfl
    have hE : mapH (Int.castRingHom (ZMod 4))
        (mulH (starH A) ⟨B.a0 - A.a0, B.a1 - A.a1, B.a2 - A.a2, B.a3 - A.a3⟩) = ⟨0, 0, 0, 0⟩ := by
      rw [mapH_mulH, mapH_starH, mapH_sub]
      have hB4 : mapH (Int.castRingHom (ZMod 4)) B =
          mulH (mapH (Int.castRingHom (ZMod 4)) (βZ t)) (alpha4 e.r w.1 w.2.1) := by
        rw [hBdef, mapH_mulH, hα4]
      show mulH (starH (mapH (Int.castRingHom (ZMod 4)) A))
        (sub4 (mapH (Int.castRingHom (ZMod 4)) B) (mapH (Int.castRingHom (ZMod 4)) A)) = _
      rw [hA4, hB4]; exact hm1
    obtain ⟨Cc, hCc⟩ := exists_smulH_of_mod hE
    have hα0 : (hurZ αZ : ℍ[ℚ]) ≠ 0 := by
      intro h0
      have := congrArg Quaternion.normSq h0
      rw [normSq_hurZ, map_zero] at this
      exact nrdH_odd_of_mod4 (by rw [hα4]; exact hm2) (by exact_mod_cast this)
    have hαω : (hurZ αZ : ℍ[ℚ]) = ((w.1.val : ℚ)) • 1 + ((w.2.1.val : ℚ)) • ω := by
      apply hc_injective
      rw [hc_hurZ, hc_add, hc_smul, hc_smul, hc_one, hωdef, hc_hurZ]
      ext <;> simp [hαZ, mapH]
    have hωc : ω * τ (sqrtNeg n) = τ (sqrtNeg n) * ω := by
      rw [hωv, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
    have hαc : (hurZ αZ : ℍ[ℚ]) * τ (sqrtNeg n) = τ (sqrtNeg n) * hurZ αZ := by
      rw [hαω, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
        one_mul, mul_one, hωc]
    have hρ : Quaternion.normSq (hurZ (smulH (sg w.2.2.2) μ) : ℍ[ℚ]) = 1 := by
      rw [normSq_hurZ, nrdH_smulH, hμ1, hsg]; simp
    have hρ0 : (hurZ (smulH (sg w.2.2.2) μ) : ℍ[ℚ]) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hρ; exact zero_ne_one hρ
    have hAq : hurZ (smulH (sg w.2.2.2) μ) * twoRepQ (e.root t) = (hurZ A : ℍ[ℚ]) := by
      rw [twoRepQ_eq, hAdef, hurZ_smulH, hurZ_smulH, hurZ_mulH, smul_mul_assoc]
    have hBq : twoRepQ t * hurZ αZ = (hurZ B : ℍ[ℚ]) := by rw [twoRepQ_eq, hBdef, hurZ_mulH]
    have hnA : nrdH A = 2 ^ 0 * nrdH (βZ (e.root t)) := by
      rw [hAdef, nrdH_smulH, nrdH_mulH, hμ1, hsg]; ring
    have hloc := local_merge_cond (p := (Pw v : ℕ)) (Pw_eq_two hv) A B Cc 0 _ (nrdH_βZ_odd _) hnA
      (by rw [hCc]; norm_num)
    rw [← hAq, ← hBq] at hloc
    exact twoRep_mem_DC_of hv hα0 hαc hρ0 (isHurZ_hurZ _) (Or.inl hρ) hloc
  -- the obstruction
  have hS0 : twoRep v e.p1 ∉ DC n τ (twoRep v e.rc) := by
    refine twoRep_not_mem_DC hv C hH ?_
    intro p _ hp q nn k hq hk y hy heq
    subst hp
    obtain ⟨cc, hcc, u, rfl, hu, hnu, hR⟩ := hy
    rw [qp_hurZ] at hR
    obtain ⟨μ, hμ, X, Y, hrel⟩ := two_adic_b1 q hq nn k hk (βZ e.p1) (βZ e.rc) ωZ (nrdH_βZ_odd _)
      (nrdH_βZ_odd _) cc hcc u hnu hR heq
    exact tab3_sep e he μ hμ X Y (by rw [her']; exact hrel)
  -- assembly
  have hroot : ∀ t t', e.F t = e.F t' → e.root t = e.root t' := by
    intro t t' h
    simp only [E3.F, E3.root] at h ⊢
    split_ifs at h ⊢ <;> first | rfl | (exfalso; norm_num at h)
  have hFv : ∀ t, e.F t = -3 ∨ e.F t = 1 := fun t => by
    simp only [E3.F]; split_ifs <;> simp
  have hrootF : ∀ t, e.F (e.root t) = e.F t := by
    intro t
    have h := tab3_sums e he
    simp only [E3.root]
    split_ifs with h1
    · rw [h.2.2.2]; simp only [E3.F, if_pos h1]
    · rw [h.2.2.1]; simp only [E3.F, if_neg h1]
  obtain ⟨hs1, hs2, hs3, hs4⟩ := tab3_sums e he
  refine ⟨v, hv, e.F, ⟨exists_twoRep τ hv, ?_, ?_, ⟨hs1, hs2⟩, ?_, ⟨e.rc, by rw [hs3]; norm_num⟩⟩, ?_⟩
  · intro t t' h
    have h2 := hM0 t'
    rw [← hroot t t' h] at h2
    exact DC_trans (DC_symm h2) (hM0 t)
  · intro t t' h hmem
    have h4 : twoRep v (e.root t) ∈ DC n τ (twoRep v (e.root t')) :=
      DC_trans (DC_trans (hM0 t') hmem) (DC_symm (hM0 t))
    simp only [E3.root] at h4
    simp only [E3.F] at h
    split_ifs at h4 h with h1 h2
    · exact h rfl
    · exact hS0 (DC_symm h4)
    · exact hS0 h4
    · exact h rfl
  · intro G hG hGs _
    exact rank1_two e.F G hFv hs1 hs3 hG hGs
  · intro t
    rcases hFv t with h | h <;> rw [h]
    · exact ⟨-2, by norm_num⟩
    · exact odd_one

end ZInQ.Contrib.HP23Proof
