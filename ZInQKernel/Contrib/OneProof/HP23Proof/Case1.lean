import ZInQKernel.Contrib.OneProof.HP23Proof.Generic
import ZInQKernel.Contrib.OneProof.HfxProof.Case1

/-!
# hp23-proof: the partition data for `n ≡ 1 (mod 8)`

Task hp23-proof. A copy of hfx-proof's `HfxProof.testVector_one8` (`HfxProof/Case1.lean`) whose
conclusion is the partition data (`PartData`) instead of the test vector built from it, with two
additions:
* the generator `F` (values `1, −1, 0` on the three orbits) is odd on the classes with `t.2.2 = 0`
  (`χ₀ = 1`): the size-4 orbit (`F = 0`) is exactly `t.2.2 = 1` for every table entry
  (`tab1_c_ne_two`, decide);
* the local condition `C1` at `2` (`ℚ₂^× R₂^× ∪ ℚ₂^× R₂^× ϖ⁻¹`) has reduced norms in `2^ℤ(1 + 4ℤ₂)`:
  `nrd(x + zω) = x² + n z² ≡ 1 (mod 4)` on `R₂^×` (`good_of_loc2OK`, `nrd4_check`) and
  `nrd ϖ = 2(4k + 1)`.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.HP23Proof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The size-4 orbit (`c = 2`, `F = 0`) of every table entry lies in `t.2.2 = 1`. -/
theorem tab1_c_ne_two : ∀ e ∈ tab1, ∀ t : T8, t.2.2 = 0 → e.c t ≠ 2 := by decide +kernel

/-- `nrd(X + Z(A i + B j)) = X² + Z²(A² + B²)` is `1` mod 4 when it is a unit and `A² + B² ≡ 1`. -/
theorem nrd4_check : ∀ X Z A B : ZMod 4, A ^ 2 + B ^ 2 = 1 →
    nrdH (⟨X + Z * 0, Z * A, Z * B, Z * 0⟩ : H4 (ZMod 4)) ≠ 0 →
    nrdH (⟨X + Z * 0, Z * A, Z * B, Z * 0⟩ : H4 (ZMod 4)) ≠ 2 →
    nrdH (⟨X + Z * 0, Z * A, Z * B, Z * 0⟩ : H4 (ZMod 4)) = 1 := by decide +kernel

/-- Units of `R₂ = ℤ₂ + ℤ₂ω + 4O_{B,2}` have reduced norm `≡ 1 (mod 4)` when the residues of `ω` force
it; so `ℚ₂^× R₂^×` has reduced norms in `2^ℤ(1 + 4ℤ₂)`. -/
theorem good_of_loc2OK {ωc : H4 ℤ}
    (hω : ∀ X Z : ZMod 4, nrdH (⟨X + Z * ((ωc.a0 : ℤ) : ZMod 4), Z * ((ωc.a1 : ℤ) : ZMod 4),
      Z * ((ωc.a2 : ℤ) : ZMod 4), Z * ((ωc.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) ≠ 0 →
      nrdH (⟨X + Z * ((ωc.a0 : ℤ) : ZMod 4), Z * ((ωc.a1 : ℤ) : ZMod 4),
      Z * ((ωc.a2 : ℤ) : ZMod 4), Z * ((ωc.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) ≠ 2 →
      nrdH (⟨X + Z * ((ωc.a0 : ℤ) : ZMod 4), Z * ((ωc.a1 : ℤ) : ZMod 4),
      Z * ((ωc.a2 : ℤ) : ZMod 4), Z * ((ωc.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) = 1)
    {y : ℍ[ℚ_[2]]} (hy : Loc2OK (hurZ ωc) y) : Good (Quaternion.normSq y) := by
  obtain ⟨c, hc, u, rfl, -, hnu, hR⟩ := hy
  rw [Quaternion.normSq_smul]
  refine (good_sq hc).mul (Good.of_norm ?_)
  obtain ⟨X, Z, A, hU⟩ := inR_coords hR
  set U : H4 ℤ_[2] := ⟨X + Z * cZ ωc.a0 + 4 * A.a0, Z * cZ ωc.a1 + 4 * A.a1, Z * cZ ωc.a2 + 4 * A.a2,
    Z * cZ ωc.a3 + 4 * A.a3⟩ with hUdef
  have hN : Quaternion.normSq u = ((nrdH U : ℤ_[2]) : ℚ_[2]) := by
    rw [normSq_eq_nrdH, hU, ← map_nrdH]; rfl
  have hred : red4 (nrdH U) = nrdH (⟨red4 X + red4 Z * ((ωc.a0 : ℤ) : ZMod 4),
      red4 Z * ((ωc.a1 : ℤ) : ZMod 4), red4 Z * ((ωc.a2 : ℤ) : ZMod 4),
      red4 Z * ((ωc.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) := by
    rw [map_nrdH]
    simp only [hUdef, mapH, map_add, map_mul, red4_four, zero_mul, add_zero, red4_cZ]
  have hunit : ‖((nrdH U : ℤ_[2]) : ℚ_[2])‖ = 1 := by rw [← hN]; exact hnu
  obtain ⟨h0, h2⟩ := red4_ne_zero_two_of_unit hunit
  rw [hred] at h0 h2
  have h1 : red4 (nrdH U) = 1 := by rw [hred]; exact hω _ _ h0 h2
  have hz : red4 (nrdH U - 1) = 0 := by rw [map_sub, h1, map_one, sub_self]
  have := red4_eq_zero_iff_norm hz
  rw [hN]
  rwa [PadicInt.coe_sub, PadicInt.coe_one] at this

/-- **The partition data for `n ≡ 1 (mod 8)`** (hfx-proof's `testVector_one8`, with the conclusion
`testVector_of_partition` replaced by its hypotheses); `F` is odd (`±1`) on the classes with `t.2.2 = 0`;
and the local-condition group `SgC ⊇ H` has reduced norms in `2^ℤ(1 + 4ℤ₂)` at `2`. -/
theorem partition_one8 {n : ℕ} [NeZero n] (hsq : Squarefree n) (h1 : n % 8 = 1)
    {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ∃ hv : IsPlaceTwo v, ∃ F : T8 → ℤ,
      PartData n τ v F ∧ (∀ t : T8, t.2.2 = 0 → Odd (F t)) ∧
      ∃ C : LocCond, HgrpN n τ ≤ SgC v hv C ∧
        ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], C.P p y → Good (Quaternion.normSq y) := by
  classical
  obtain ⟨v, hv⟩ := exists_isPlaceTwo
  obtain ⟨a, b, c, hvq, hn, h4⟩ := exists_abc hτ (Or.inl h1)
  obtain ⟨c', rfl⟩ := h4 h1
  set k := n / 8 with hkdef
  have hk : n = 8 * k + 1 := by have := Nat.div_add_mod n 8; rw [h1] at this; omega
  have hnk : ((8 * k + 1 : ℕ) : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + ((4 * c' : ℤ) : ℚ) ^ 2 := by
    rw [← hk]; exact_mod_cast hn
  set ωZ := ωH1 a b (4 * c') with hωZ
  set ω : ℍ[ℚ] := hurZ ωZ with hωdef
  have hωv : ω = τ (sqrtNeg n) := by rw [hvq, hωdef, hurZ_ωH1]
  have hω2 : ω * ω = -(((8 * k + 1 : ℕ) : ℚ)) • 1 := by
    rw [hωdef, hurZ_ωH1, hnk]; ext <;> simp <;> ring
  have hst : star ω = -ω := by rw [hωdef, hurZ_ωH1]; ext <;> simp
  have hϖn : Quaternion.normSq (1 + ω) = ((2 * (4 * k + 1) : ℕ) : ℚ) := by
    rw [hωdef, hurZ_ωH1, Quaternion.normSq_def']
    have : ((2 * (4 * k + 1) : ℕ) : ℚ) = 1 + ((8 * k + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [this, hnk]; simp; ring
  have hqω : qp 2 ω = ⟨0, ((a : ℚ) : ℚ_[2]), ((b : ℚ) : ℚ_[2]), (((4 * c' : ℤ) : ℚ) : ℚ_[2])⟩ := by
    rw [hωdef, hurZ_ωH1]; ext <;> simp [qp]
  have hABC : ((a : ℚ) : ℚ_[2]) ^ 2 + ((b : ℚ) : ℚ_[2]) ^ 2 + (((4 * c' : ℤ) : ℚ) : ℚ_[2]) ^ 2 =
      ((8 * k + 1 : ℕ) : ℚ_[2]) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[2])) hnk; push_cast at this ⊢; rw [this]
  have hnrd : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • qp 2 ω) =
      x ^ 2 + ((8 * k + 1 : ℕ) : ℚ_[2]) * z ^ 2 := by
    intro x z; rw [hqω, Quaternion.normSq_def', ← hABC]; simp; ring
  have hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ω := by
    intro x; rw [hωv]; exact tau_span1 hsq h1 τ x
  set C := C1 ω k (isHurZ_hurZ _) hω2 hst hϖn hnrd with hCdef
  have hH : HgrpN n τ ≤ SgC v hv C := by
    refine HgrpN_le_SgC hv C (isHurZ_hurZ _) hspan ?_ ?_ ?_
    · intro p _ _ cc hcc; exact Or.inl ⟨cc, hcc, 1, by simp, isHur_one, by simp, InR.one⟩
    · intro p _ _ u hu hnu hR; exact Or.inl ⟨1, one_ne_zero, u, by simp, hu, hnu, hR⟩
    · intro p _ hp y hy hcomm
      subst hp
      rw [← hωv, hqω] at hcomm
      have h := loc_of_commute1 hABC (by rw [← hqω]; exact isHur_qp_hurZ' (isHurZ_hurZ _)) hy hcomm
      show Loc2OK (qp 2 ω) y ∨ Loc2OK (qp 2 ω) (y * qp 2 (1 + ω))
      rw [map_add, map_one, hqω]; exact h
  -- the table entry
  set r := mapH (Int.castRingHom (ZMod 8)) ωZ with hrdef
  obtain ⟨e, he, her⟩ := tab1_complete r.a0 r.a1 r.a2 r.a3
    (by show ((2 * (4 * c') : ℤ) : ZMod 8) = 2 * ((4 * c' : ℤ) : ZMod 8); push_cast; ring)
    (by show ((4 * c' : ℤ) : ZMod 8) = 0 ∨ ((4 * c' : ℤ) : ZMod 8) = 4
        push_cast; exact zmod8_four_mul _)
    (by
      show (((a - 4 * c' : ℤ) : ZMod 8) + ((4 * c' : ℤ) : ZMod 8)) ^ 2 +
        (((b - 4 * c' : ℤ) : ZMod 8) + ((4 * c' : ℤ) : ZMod 8)) ^ 2 + ((4 * c' : ℤ) : ZMod 8) ^ 2 = 1
      have h8 : (((a ^ 2 + b ^ 2 + (4 * c') ^ 2 : ℤ)) : ZMod 8) = 1 := by
        rw [← hn, hk]; push_cast; rw [show (8 : ZMod 8) = 0 from rfl]; ring
      push_cast at h8 ⊢; linear_combination h8)
  have her' : e.r = r := her
  have hqω' : qp 2 ω = hurZ ωZ := qp_hurZ ωZ
  -- merges
  have hM0 : ∀ t, twoRep v t ∈ DC n τ (twoRep v (e.root t)) := by
    intro t
    obtain ⟨hm1, hm2⟩ := tab1_merge e he t
    set w := e.wit.getD (idx8 t) (0, 0, 0, 0, 0)
    set μ := unitList.getD w.2.2.1.val ⟨1, 0, 0, 0⟩ with hμdef
    have hμ1 : nrdH μ = 1 := unitList_nrdH μ (getD_mem_unitList _)
    have hsg : (sg w.2.2.2.1 : ℤ) ^ 2 = 1 := by have := sg_sq w.2.2.2.1; exact_mod_cast this
    set ρZ : H4 ℤ := if w.2.2.2.2 = 0 then smulH (sg w.2.2.2.1) μ
      else mulH oneI (smulH (sg w.2.2.2.1) μ) with hρZ
    set αZ : H4 ℤ := ⟨(w.1.val : ℤ) + (w.2.1.val : ℤ) * ωZ.a0, (w.2.1.val : ℤ) * ωZ.a1,
      (w.2.1.val : ℤ) * ωZ.a2, (w.2.1.val : ℤ) * ωZ.a3⟩ with hαZ
    have hα8 : mapH (Int.castRingHom (ZMod 8)) αZ = alpha8 e.r w.1 w.2.1 := by
      rw [her', hrdef]; simp only [hαZ, mapH, alpha8, map_add, map_mul, eq_intCast, natCast_val_zmod8]
    set A : H4 ℤ := rhoBetaZ w.2.2.1 w.2.2.2.1 w.2.2.2.2 (e.root t) with hAdef
    set B : H4 ℤ := mulH (βZ t) αZ with hBdef
    have hE : DivB w.2.2.2.2 (mapH (Int.castRingHom (ZMod 8))
        (mulH (starH A) ⟨B.a0 - A.a0, B.a1 - A.a1, B.a2 - A.a2, B.a3 - A.a3⟩)) := by
      rw [mapH_mulH, mapH_starH, mapH_sub]
      have hB8 : mapH (Int.castRingHom (ZMod 8)) B =
          mulH (mapH (Int.castRingHom (ZMod 8)) (βZ t)) (alpha8 e.r w.1 w.2.1) := by
        rw [hBdef, mapH_mulH, hα8]
      show DivB _ (mulH (starH (mapH (Int.castRingHom (ZMod 8)) A))
        (sub8 (mapH (Int.castRingHom (ZMod 8)) B) (mapH (Int.castRingHom (ZMod 8)) A)))
      rw [hB8]; exact hm1
    obtain ⟨Cc, hCc⟩ := exists_smulH_of_divB hE
    have hα0 : (hurZ αZ : ℍ[ℚ]) ≠ 0 := by
      intro h0
      have := congrArg Quaternion.normSq h0
      rw [normSq_hurZ, map_zero] at this
      apply hm2; rw [← hα8, ← map_nrdH]
      have : nrdH αZ = 0 := by exact_mod_cast this
      rw [this, map_zero]
    have hαω : (hurZ αZ : ℍ[ℚ]) = ((w.1.val : ℚ)) • 1 + ((w.2.1.val : ℚ)) • ω := by
      apply hc_injective
      rw [hc_hurZ, hc_add, hc_smul, hc_smul, hc_one, hωdef, hc_hurZ]
      ext <;> simp [hαZ, mapH]
    have hαc : (hurZ αZ : ℍ[ℚ]) * τ (sqrtNeg n) = τ (sqrtNeg n) * hurZ αZ := by
      rw [hαω, ← hωv, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
        one_mul, mul_one]
    have hρn : Quaternion.normSq (hurZ ρZ : ℍ[ℚ]) = 1 ∨ Quaternion.normSq (hurZ ρZ : ℍ[ℚ]) = 2 := by
      rw [normSq_hurZ, hρZ]
      split_ifs
      · left; rw [nrdH_smulH, hμ1, hsg]; simp
      · right; rw [nrdH_mulH, nrdH_smulH, hμ1, hsg, show nrdH oneI = 2 from rfl]; simp
    have hρ0 : (hurZ ρZ : ℍ[ℚ]) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hρn; rcases hρn with h | h <;> norm_num at h
    have hAq : hurZ ρZ * twoRepQ (e.root t) = (hurZ A : ℍ[ℚ]) := by
      rw [hAdef, hurZ_rhoBetaZ]
    have hBq : twoRepQ t * hurZ αZ = (hurZ B : ℍ[ℚ]) := by rw [twoRepQ_eq, hBdef, hurZ_mulH]
    have hnA : nrdH A = 2 ^ w.2.2.2.2.val * nrdH (βZ (e.root t)) := by
      rw [hAdef, rhoBetaZ]
      split_ifs with hb
      · rw [hb, nrdH_smulH, nrdH_mulH, hμ1, hsg]; simp
      · have hb1 : w.2.2.2.2 = 1 := by omega
        rw [hb1, nrdH_mulH, nrdH_smulH, nrdH_mulH, hμ1, hsg, show nrdH oneI = 2 from rfl]; simp
    have hloc := local_merge_cond (p := (Pw v : ℕ)) (Pw_eq_two hv) A B Cc w.2.2.2.2.val _
      (nrdH_βZ_odd _) hnA hCc
    rw [← hAq, ← hBq] at hloc
    exact twoRep_mem_DC_of hv hα0 hαc hρ0 (isHurZ_hurZ _) hρn hloc
  -- the obstruction, for the three pairs of roots
  have hS0 : ∀ pr ∈ pairs1, twoRep v pr.1 ∉ DC n τ (twoRep v pr.2) := by
    intro pr hpr
    refine twoRep_not_mem_DC hv C hH ?_
    intro p _ hp q nn k' hq hk' y hy heq
    subst hp
    rcases hy with hy | hy
    · obtain ⟨cc, hcc, u, rfl, hu, hnu, hR⟩ := hy
      rw [hqω'] at hR
      obtain ⟨μ, hμ, X, Y, hrel⟩ := two_adic_b1 q hq nn k' hk' (βZ pr.1) (βZ pr.2) ωZ (nrdH_βZ_odd _)
        (nrdH_βZ_odd _) cc hcc u hnu hR heq
      refine tab1_sep1 e he pr hpr μ hμ X Y ?_
      rw [her', hrdef]; simp only [mapH, eq_intCast, to4_intCast]; exact hrel
    · obtain ⟨cc, hcc, u, hyu, hu, hnu, hR⟩ := hy
      rw [hqω'] at hR
      set ϖZ : H4 ℤ := ⟨1 + 4 * c', a - 4 * c', b - 4 * c', 2 * (4 * c')⟩ with hϖZ
      have hϖq : qp 2 (1 + ω) = hurZ ϖZ := by
        rw [map_add, map_one, hqω']; apply hc_injective
        rw [hc_add, hc_one, hc_hurZ, hc_hurZ]; ext <;> simp [hϖZ, hωZ, ωH1, mapH]
      have hϖn' : nrdH ϖZ = 2 * ((4 * k + 1 : ℕ) : ℤ) := by
        have h := hϖn
        rw [show (1 + ω : ℍ[ℚ]) = hurZ ϖZ by
          apply hc_injective; rw [hc_add, hc_one, hωdef, hc_hurZ, hc_hurZ]
          ext <;> simp [hϖZ, hωZ, ωH1, mapH], normSq_hurZ] at h
        have : ((nrdH ϖZ : ℤ) : ℚ) = ((2 * ((4 * k + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by rw [h]; push_cast; ring
        exact_mod_cast this
      rw [hϖq] at hyu
      have heq' : qp 2 (q • hurZ nn) * hurZ (βZ pr.2) * (cc • u) = hurZ (βZ pr.1) * hurZ ϖZ := by
        rw [← hyu, ← heq]; simp only [mul_assoc]
      obtain ⟨μ, hμ, X, Y, hrel⟩ := two_adic_b2 q hq nn k' hk' (βZ pr.1) (βZ pr.2) ωZ ϖZ
        (nrdH_βZ_odd _) (nrdH_βZ_odd _) _ ⟨2 * k, by push_cast; ring⟩ hϖn' cc hcc u hnu hR heq'
      refine tab1_sep2 e he pr hpr μ hμ (to4 X) (to4 Y) ?_
      have hL : mulH (mapH (Int.castRingHom (ZMod 8)) oneMI) (mulH (mapH (Int.castRingHom (ZMod 8))
          (βZ pr.1)) ⟨1 + e.r.a0, e.r.a1, e.r.a2, e.r.a3⟩) =
          mapH (Int.castRingHom (ZMod 8)) (mulH oneMI (mulH (βZ pr.1) ϖZ)) := by
        rw [mapH_mulH, mapH_mulH]; congr 2
        rw [her', hrdef]; simp [mapH, hϖZ, hωZ, ωH1]
      have hR' : (⟨dbl (to4 X) + dbl (to4 Y) * e.r.a0, dbl (to4 Y) * e.r.a1, dbl (to4 Y) * e.r.a2,
          dbl (to4 Y) * e.r.a3⟩ : H4 (ZMod 8)) = ⟨2 * X + 2 * Y * (ωZ.a0 : ZMod 8),
          2 * Y * (ωZ.a1 : ZMod 8), 2 * Y * (ωZ.a2 : ZMod 8), 2 * Y * (ωZ.a3 : ZMod 8)⟩ := by
        rw [dbl_to4, dbl_to4, her', hrdef]; rfl
      rw [hL, hR']; exact hrel
  -- the reduced norm at 2 (hp23-proof)
  have hω4 : ∀ X Z : ZMod 4, nrdH (⟨X + Z * ((ωZ.a0 : ℤ) : ZMod 4), Z * ((ωZ.a1 : ℤ) : ZMod 4),
      Z * ((ωZ.a2 : ℤ) : ZMod 4), Z * ((ωZ.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) ≠ 0 →
      nrdH (⟨X + Z * ((ωZ.a0 : ℤ) : ZMod 4), Z * ((ωZ.a1 : ℤ) : ZMod 4),
      Z * ((ωZ.a2 : ℤ) : ZMod 4), Z * ((ωZ.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) ≠ 2 →
      nrdH (⟨X + Z * ((ωZ.a0 : ℤ) : ZMod 4), Z * ((ωZ.a1 : ℤ) : ZMod 4),
      Z * ((ωZ.a2 : ℤ) : ZMod 4), Z * ((ωZ.a3 : ℤ) : ZMod 4)⟩ : H4 (ZMod 4)) = 1 := by
    have h4z : (4 : ZMod 4) = 0 := rfl
    have e0 : ((ωZ.a0 : ℤ) : ZMod 4) = 0 := by
      simp only [hωZ, ωH1]; push_cast; rw [h4z, zero_mul]
    have e1 : ((ωZ.a1 : ℤ) : ZMod 4) = (a : ZMod 4) := by
      simp only [hωZ, ωH1]; push_cast; rw [h4z, zero_mul, sub_zero]
    have e2 : ((ωZ.a2 : ℤ) : ZMod 4) = (b : ZMod 4) := by
      simp only [hωZ, ωH1]; push_cast; rw [h4z, zero_mul, sub_zero]
    have e3 : ((ωZ.a3 : ℤ) : ZMod 4) = 0 := by
      simp only [hωZ, ωH1]; push_cast; rw [h4z, zero_mul, mul_zero]
    have hab : (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 = 1 := by
      have h8 : (((a ^ 2 + b ^ 2 + (4 * c') ^ 2 : ℤ)) : ZMod 4) = 1 := by
        rw [← hn, hk]; push_cast; rw [show (8 : ZMod 4) = 0 from rfl]; ring
      push_cast at h8; rw [h4z] at h8; linear_combination h8
    intro X Z
    rw [e0, e1, e2, e3]
    exact nrd4_check X Z _ _ hab
  have hϖgood : Good (Quaternion.normSq (qp 2 (1 + ω))) := by
    rw [normSq_qp, hϖn]
    have e4 : (((2 * (4 * k + 1) : ℕ) : ℚ) : ℚ_[2]) = 2 * (((4 * k : ℤ) : ℚ_[2]) + 1) := by
      push_cast; ring
    rw [e4]
    refine Good.two.mul (Good.of_norm ?_)
    rw [add_sub_cancel_right]
    have := (Padic.norm_int_le_pow_iff_dvd (p := 2) (4 * k : ℤ) 2).mpr (by norm_num)
    push_cast at this ⊢; norm_num at this; rw [norm_mul]; exact this
  have hC : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], C.P p y →
      Good (Quaternion.normSq y) := by
    intro p _ hp y hy
    subst hp
    rcases (hy : Loc2OK (qp 2 ω) y ∨ Loc2OK (qp 2 ω) (y * qp 2 (1 + ω))) with hy | hy
    · rw [hqω'] at hy
      exact good_of_loc2OK hω4 hy
    · rw [hqω'] at hy
      have := good_of_loc2OK hω4 hy
      rw [map_mul] at this
      exact this.of_mul_right hϖgood
  -- assembly
  obtain ⟨hs1, hs2, hN0, hN1, hN2, hM0', hM1, hM2, hc0, hc1, hc2⟩ := tab1_sums e he
  have hroot : ∀ t t', e.F t = e.F t' → e.root t = e.root t' := by
    intro t t' h
    simp only [E1.F] at h
    simp only [E1.root, val1_inj _ _ h]
  refine ⟨v, hv, e.F, ⟨exists_twoRep τ hv, ?_, ?_, ⟨hs1, hs2⟩, ?_,
    ⟨(0, 0, 0), by simp only [E1.F, hc0]; decide⟩⟩, ?_, C, hH, hC⟩
  · intro t t' h
    have h2 := hM0 t'
    rw [← hroot t t' h] at h2
    exact DC_trans (DC_symm h2) (hM0 t)
  · intro t t' h hmem
    have h4 : twoRep v (e.root t) ∈ DC n τ (twoRep v (e.root t')) :=
      DC_trans (DC_trans (hM0 t') hmem) (DC_symm (hM0 t))
    have hne : e.c t ≠ e.c t' := fun hc => h (by simp only [E1.F, hc])
    rcases pairs1_cover _ _ hne with hp | hp
    · exact hS0 _ hp h4
    · exact hS0 _ hp (DC_symm h4)
  · intro G hG hGs hGc
    exact rank1_three e.c G hc0 hc1 hc2 hN0 hN1 hN2 hM0' hM1 hM2 hG hGs hGc
  · intro t ht
    have hne := tab1_c_ne_two e he t ht
    simp only [E1.F]
    rcases fin3_cases (e.c t) with h | h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨-1, by simp [val1]⟩
    · exact absurd h hne

end ZInQ.Contrib.HP23Proof
