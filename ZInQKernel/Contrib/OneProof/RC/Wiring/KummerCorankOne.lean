import ZInQKernel.Contrib.OneProof.RC.Wiring.SignedCalibrationLeaf
import ZInQKernel.Contrib.OneProof.SelmerCorankFam
import ZInQKernel.Contrib.PoleRC.MordellWeilM

/-!
# Theorem 5.3, Lane RC37: the Kummer sequence in rank one

`KummerCorankOneGlue` (`SignedCalibrationLeaf.lean`; `lem:forward-rank`, tex 1098–1104: "the
ordinary Kummer sequence `0 → A(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(A/ℚ) → Ш(A/ℚ)[2^∞] → 0` gives the corank
assertion") is the rank-one companion of the proved `KummerCorankZero`: for an elliptic curve
`A/ℚ` with `rank A(ℚ) = 1` and `Ш(A/ℚ)` finite, `corank_{ℤ₂} Sel_{2^∞}(A/ℚ) = 1`.

* `z2Corank_selmerTwoPower_of_rank` (PROVED): for `A/ℚ` elliptic with `A(ℚ)` finitely generated
  of rank `r` and `Ш(A/ℚ)` finite, `corank_{ℤ₂} Sel_{2^∞}(A/ℚ) = r`. The proof is the Kummer
  sequence at finite levels: the `2ⁿ`-descent sequences (Silverman X.4.2) give
  `#Sel_{2ⁿ} = #(A(ℚ)/2ⁿ) · #Ш[2ⁿ] = 2^{nr} · #T[2ⁿ] · #Ш[2ⁿ]` for `A(ℚ) ≅ ℤ^r × T`; the map
  `Sel_{2ⁿ} → Sel_{2^∞}[2ⁿ]` is onto with kernel at most `#A(ℚ)[2^∞]`, and
  `Sel_{2^∞} ≅ (ℚ₂/ℤ₂)^t × F` with `F` finite (structure theorem for `2`-primary groups with
  finite `2`-torsion), so `#Sel_{2ⁿ} = #kerₙ · 2^{nt} · #F[2ⁿ]`. With `#Ш[2ⁿ] ≤ #Ш` bounded,
  comparing growth in `n` gives `t = r`. The counting is that of Lemma 5.4
  (`SelmerCorankFam.lean`), with the finiteness of `Ш` in place of the Cassels–Tate count.
  Neither the corank nor the finiteness of `Ш` is derived from the rank.
* Finite generation does not follow from `rank A(ℚ) = 1`: a rank-one group can be
  `2`-divisible modulo torsion, and then `A(ℚ) ⊗ ℚ₂/ℤ₂ = 0`. It is Mordell's theorem.
  `kummerCorankOneGlue_of_mordellWeil` derives the GLUE from the textbook statement
  `PoleRC.MordellWeil`. Mordell's theorem is PROVED in the tree for the curves
  `E_t : y² = x(x − t)(x + 3t)`, `t ≠ 0` (`PoleRC.mordellWeil_curve`), so the rank-one Kummer
  sequence holds unconditionally for them (`kummerCorankOne_curve`).
* `selmerCorankOneOverKSigned_of_forward_mw`, `centralRankOne_of_forward_ne_mw`: the two
  forward-theorem consumers of `KummerCorankOneGlue` in `SignedCalibrationLeaf.lean`, with that
  input removed; their curves are the twists `E_{ℓh} = E_t` with `t = ℓh ≠ 0`.

Every declaration below is PROVED (or a definition).
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Cofinite TauCeti TauCeti.ContCohomology

section Counting

open ZInQ.Manuscript.SelmerTwoPower.Fam

/-- `Sel₂(E/ℚ)` is finite when `E(ℚ)/2E(ℚ)` and `Ш(E/ℚ)` are finite: the `2`-descent sequence
`0 → E(ℚ)/2 → Sel₂ → Ш[2] → 0` (Silverman X.4.2, Tau Ceti's descent sequence). Kind: PROVED. -/
theorem finite_famSelmerAt_one_of_finite (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hq : Finite (E.toAffine.Point ⧸ (nsmulAddMonoidHom (α := E.toAffine.Point) (2 ^ 1)).range))
    (hsha : Finite (Fam.sha E)) : Finite (Fam.selmerAt E 1) := by
  classical
  let g := E.selmerShaMap Fam.emb (2 ^ 1)
  let f := E.kummerSelmerMap Fam.emb (isUnit_two_pow 1)
  have hker : g.ker = f.range := by
    ext c
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact E.exact_kummerSelmerMap_selmerShaMap Fam.emb (isUnit_two_pow 1) c
  have hk : Finite g.ker := by
    rw [hker]
    exact Finite.of_surjective _ f.rangeRestrict_surjective
  have : Finite (E.shafarevichTateGroup Fam.emb) := hsha
  exact finite_of_finite_ker g hk

/-- **Growth comparison**: if `b n · 2^{nt} · a n = 2^{nr} · c n · d n` for all `n`, with
`a, b, c, d` bounded between `1` and `C`, then `t = r`. Kind: PROVED. -/
theorem kc1_growth {t r C : ℕ} (a b c d : ℕ → ℕ)
    (ha : ∀ n, 1 ≤ a n ∧ a n ≤ C) (hb : ∀ n, 1 ≤ b n ∧ b n ≤ C)
    (hc : ∀ n, 1 ≤ c n ∧ c n ≤ C) (hd : ∀ n, 1 ≤ d n ∧ d n ≤ C)
    (key : ∀ n, b n * (2 ^ (n * t) * a n) = (2 ^ n) ^ r * c n * d n) : t = r := by
  refine eq_of_pow_mul_eq (b := 2) (C := C * C) (by norm_num) (fun n => a n * b n)
    (fun n => c n * d n) (fun n => ⟨?_, ?_⟩) (fun n => ⟨?_, ?_⟩) (fun n => ?_)
  · exact le_trans (le_of_eq (one_mul 1).symm) (Nat.mul_le_mul (ha n).1 (hb n).1)
  · exact Nat.mul_le_mul (ha n).2 (hb n).2
  · exact le_trans (le_of_eq (one_mul 1).symm) (Nat.mul_le_mul (hc n).1 (hd n).1)
  · exact Nat.mul_le_mul (hc n).2 (hd n).2
  · calc 2 ^ (n * t) * (a n * b n) = b n * (2 ^ (n * t) * a n) := by ring
      _ = (2 ^ n) ^ r * c n * d n := key n
      _ = 2 ^ (n * r) * (c n * d n) := by rw [← pow_mul]; ring

/-- **The corank of `Sel_{2^∞}(E/ℚ)` is the rank of `E(ℚ)`** (one-family groups), for
`E(ℚ) ≅ ℤ^r × T` with `T` finite and `Ш(E/ℚ)` finite. Kind: PROVED. -/
theorem famZ2Corank_of_addEquiv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hMW : AddGroup.FG E.toAffine.Point) {r : ℕ} {T : Type} [AddCommGroup T] [Finite T]
    (eMW : E.toAffine.Point ≃+ (Fin r → ℤ) × T) (hsha : Finite (Fam.sha E)) :
    Z2Corank (Fam.selmerTwoPower E) r := by
  classical
  have : Finite (Fam.sha E) := hsha
  -- `Sel₂` is finite, hence so is `Sel_{2^∞}[2]` (its image)
  have hq : Finite
      (E.toAffine.Point ⧸ (nsmulAddMonoidHom (α := E.toAffine.Point) (2 ^ 1)).range) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_quotient_nsmul_range_of_addEquiv eMW (pow_ne_zero 1 two_ne_zero)]
    exact Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) Nat.card_pos.ne'
  have hS1 := finite_famSelmerAt_one_of_finite E hq hsha
  have hfinSel : Finite (tors (Fam.selmerTwoPower E) 2) := by
    have hR : Finite (Fam.selmerAtToTwoPower E 1).range :=
      Finite.of_surjective _ (Fam.selmerAtToTwoPower E 1).rangeRestrict_surjective
    rw [range_selmerAtToTwoPower, torsionBy_eq_tors, pow_one] at hR
    exact hR
  have hH0 := finite_H0_twoPowerCoeff E hMW
  obtain ⟨t, F, _, hF, ⟨eS⟩⟩ :=
    exists_addEquiv_of_isPPrimary (p := 2) _ (isPPrimary_selmerTwoPower E) hfinSel
  -- the counting identity at level `2ⁿ`
  have key : ∀ n : ℕ, Nat.card (Fam.selmerAtToTwoPower E n).ker *
      (2 ^ (n * t) * Nat.card (tors F (2 ^ n))) =
      (2 ^ n) ^ r * Nat.card (tors T (2 ^ n)) *
        Nat.card (AddSubgroup.torsionBy (Fam.sha E) ((2 ^ n : ℕ) : ℤ)) := by
    intro n
    obtain ⟨hSn, hcard⟩ := card_selmerAt_eq E n hfinSel
    have h1 := card_selmerAt_eq_mul E n hSn
    rw [card_quotient_nsmul_range_of_addEquiv eMW (pow_ne_zero n two_ne_zero)] at h1
    rw [card_tors_of_addEquiv eS] at hcard
    rw [← hcard, h1]
  -- the bounded factors
  have hbF : ∀ n, 1 ≤ Nat.card (tors F (2 ^ n)) ∧ Nat.card (tors F (2 ^ n)) ≤ Nat.card F :=
    fun n => ⟨Nat.card_pos, Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  have hbT : ∀ n, 1 ≤ Nat.card (tors T (2 ^ n)) ∧ Nat.card (tors T (2 ^ n)) ≤ Nat.card T :=
    fun n => ⟨Nat.card_pos, Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  have hbSha : ∀ n, 1 ≤ Nat.card (AddSubgroup.torsionBy (Fam.sha E) ((2 ^ n : ℕ) : ℤ)) ∧
      Nat.card (AddSubgroup.torsionBy (Fam.sha E) ((2 ^ n : ℕ) : ℤ)) ≤ Nat.card (Fam.sha E) :=
    fun n => ⟨Nat.card_pos, Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  have hbK : ∀ n, 1 ≤ Nat.card (Fam.selmerAtToTwoPower E n).ker ∧
      Nat.card (Fam.selmerAtToTwoPower E n).ker ≤
        Nat.card (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) := fun n => by
    obtain ⟨hSn, -⟩ := card_selmerAt_eq E n hfinSel
    exact ⟨Nat.card_pos, card_ker_selmerAtToTwoPower_le E n⟩
  -- growth: `t = r`
  have ht : t = r := by
    refine kc1_growth (C := Nat.card F + Nat.card (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) +
        Nat.card T + Nat.card (Fam.sha E))
      (fun n => Nat.card (tors F (2 ^ n))) (fun n => Nat.card (Fam.selmerAtToTwoPower E n).ker)
      (fun n => Nat.card (tors T (2 ^ n)))
      (fun n => Nat.card (AddSubgroup.torsionBy (Fam.sha E) ((2 ^ n : ℕ) : ℤ)))
      (fun n => ⟨(hbF n).1, (hbF n).2.trans (by omega)⟩)
      (fun n => ⟨(hbK n).1, (hbK n).2.trans (by omega)⟩)
      (fun n => ⟨(hbT n).1, (hbT n).2.trans (by omega)⟩)
      (fun n => ⟨(hbSha n).1, (hbSha n).2.trans (by omega)⟩) key
  subst ht
  exact ⟨F, inferInstance, hF, ⟨eS⟩⟩

end Counting

section Rank

/-- The rank of `ℤ^r × T`, `T` finite, is `r` (rank-nullity for the projection to `ℤ^r`, whose
kernel is torsion). Kind: PROVED. -/
theorem rank_pi_int_prod_finite (r : ℕ) (T : Type) [AddCommGroup T] [Finite T] :
    Module.rank ℤ ((Fin r → ℤ) × T) = r := by
  have hker : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin r → ℤ) T)) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    refine ⟨(addOrderOf (x : (Fin r → ℤ) × T).2 : ℤ),
      Int.natCast_ne_zero.mpr (isOfFinAddOrder_of_finite _).addOrderOf_pos.ne', ?_⟩
    apply Subtype.ext
    have hx : (x : (Fin r → ℤ) × T).1 = 0 := LinearMap.mem_ker.mp x.2
    refine Prod.ext ?_ ?_
    · change ((addOrderOf (x : (Fin r → ℤ) × T).2 : ℤ) • (x : (Fin r → ℤ) × T)).1 = 0
      rw [Prod.smul_fst, hx, smul_zero]
    · change ((addOrderOf (x : (Fin r → ℤ) × T).2 : ℤ) • (x : (Fin r → ℤ) × T)).2 = 0
      rw [Prod.smul_snd, natCast_zsmul, addOrderOf_nsmul_eq_zero]
  rw [LinearMap.rank_eq_of_surjective (f := LinearMap.fst ℤ (Fin r → ℤ) T)
    LinearMap.fst_surjective, hker, add_zero, rank_fin_fun]

/-- **The corank of `Sel_{2^∞}(E/ℚ)` is the rank of `E(ℚ)`**, for `E/ℚ` elliptic with `E(ℚ)`
finitely generated and `Ш(E/ℚ)` finite (the Kummer sequence
`0 → E(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞} → Ш[2^∞] → 0`, tex 1098–1104, read at finite levels).
Kind: PROVED. -/
theorem z2Corank_selmerTwoPower_of_rank (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hMW : AddGroup.FG E.toAffine.Point) {r : ℕ} (hr : Module.rank ℤ E.toAffine.Point = r)
    (hsha : Finite (sha E)) : Z2Corank (selmerTwoPower E) r := by
  obtain ⟨r', T, _, hT, ⟨eMW⟩⟩ := Fam.exists_addEquiv_pi_int_prod_finite E.toAffine.Point
  have hrr : r' = r := by
    have h1 := eMW.toIntLinearEquiv.rank_eq
    rw [hr, rank_pi_int_prod_finite] at h1
    exact_mod_cast h1.symm
  subst hrr
  rw [Fam.selmerTwoPower_eq]
  rw [Fam.sha_eq] at hsha
  exact famZ2Corank_of_addEquiv E hMW eMW hsha

/-- **The Kummer sequence in rank one from Mordell's theorem**: the textbook statement
`PoleRC.MordellWeil` (every elliptic curve over `ℚ` has finitely generated rational points) gives
`KummerCorankOneGlue`. Kind: PROVED. -/
theorem kummerCorankOneGlue_of_mordellWeil (hMW : PoleRC.MordellWeil) : KummerCorankOneGlue := by
  intro A hA hr hsha
  have := hA
  exact z2Corank_selmerTwoPower_of_rank A (hMW A hA) (by rw [hr, Nat.cast_one]) hsha

/-- **The Kummer sequence in rank one for `E_t : y² = x(x − t)(x + 3t)`, `t ≠ 0`**,
unconditionally: Mordell's theorem is proved for these curves (`PoleRC.mordellWeil_curve`).
Kind: PROVED. -/
theorem kummerCorankOne_curve {t : ℚ} (ht : t ≠ 0) [(curve t).IsElliptic]
    (hr : Module.rank ℤ (curve t).toAffine.Point = 1) (hsha : Finite (sha (curve t))) :
    Z2Corank (selmerTwoPower (curve t)) 1 :=
  z2Corank_selmerTwoPower_of_rank (curve t) (PoleRC.mordellWeil_curve t ht)
    (by rw [hr, Nat.cast_one]) hsha

end Rank

/-! ### The forward-theorem consumers without `KummerCorankOneGlue` -/

section Forward

open ZInQ.Contrib.RC53Assist.CalibrationShape ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Manuscript.RC53Assist.CentralUniversal NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Wiring (not_isSquare_intCast_of_neg)

/-- **The signed Selmer input from the forward theorems, with the rank-one Kummer sequence
proved** (tex 4020–4021, `lem:forward-rank`, tex 1086–1108): `selmerCorankOneOverKSigned_of_forward`
without its `KummerCorankOneGlue` input. The rank-one curve is `E^{(h)} = E_{ℓh}`, where the Kummer
sequence holds by `kummerCorankOne_curve`. Kind: PROVED. -/
theorem selmerCorankOneOverKSigned_of_forward_mw (Pr : Prints)
    {ℓ : ℕ} {h k : ℤ} (hlh : (ℓ : ℚ) * h ≠ 0) (hk : k ≠ 0)
    (h1 : AnalyticRank (Etw ℓ h) 1) (h0 : AnalyticRank (Etw ℓ (h * k)) 0) :
    SelmerCorankOneOverKSigned ((ℓ : ℚ) * h) k := by
  rw [selmerCorankOneOverK_of_ne]
  have hE : (Etw ℓ h).IsElliptic := by
    rw [etw_eq_curve_mul]
    exact curve_isElliptic_of_ne hlh
  have hEk : (Etw ℓ (h * k)).IsElliptic := by
    rw [etw_eq_curve_mul]
    refine curve_isElliptic_of_ne ?_
    rw [Int.cast_mul, ← mul_assoc]
    exact mul_ne_zero hlh (Int.cast_ne_zero.mpr hk)
  obtain ⟨hr1, hs1⟩ := Pr.kolyvagin _ hE (Pr.bcdt _ hE) 1 le_rfl h1
  obtain ⟨hr0, hs0⟩ := Pr.kolyvagin _ hEk (Pr.bcdt _ hEk) 0 (Nat.zero_le 1) h0
  have hfg : AddGroup.FG (Etw ℓ h).toAffine.Point := by
    rw [etw_eq_curve_mul]
    exact PoleRC.mordellWeil_curve _ hlh
  refine ⟨z2Corank_selmerTwoPower_of_rank (Etw ℓ h) hfg (by exact_mod_cast hr1) hs1,
    kummerCorankZero_holds _ hEk (by exact_mod_cast hr0) hs0⟩

/-- **The calibration block's `rank_one` at an address of either sign, from the forward
theorems, with the rank-one Kummer sequence proved** (tex 3987–4141, 4006–4021):
`centralRankOne_of_forward_ne` without its `KummerCorankOneGlue` input. Kind: PROVED. -/
theorem centralRankOne_of_forward_ne_mw (Pr : Prints)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    {k : ℤ} {ℓ : ℕ} {h : ℤ} (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    [(curve ((ℓ : ℚ) * h)).IsElliptic]
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)),
      (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal → v ∈ G.S)
    (I : KummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S
      (arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)))
    (h1 : AnalyticRank (Etw ℓ h) 1) (h0 : AnalyticRank (Etw ℓ (h * k)) 0) :
    Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1 :=
  centralRankOne_of_arithmetic_ne G (centralCohomologyFinite G hloc hglob h2)
    (not_isSquare_intCast_of_neg hk) I
    (selmerCorankOneOverKSigned_of_forward_mw Pr (mul_ne_zero_of_genuineKummerData G) hk.ne h1
      h0)

end Forward

end ZInQ.Manuscript.RC
