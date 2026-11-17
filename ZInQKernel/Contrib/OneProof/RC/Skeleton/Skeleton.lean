import ZInQKernel.Contrib.OneProof.RC.Skeleton.Steps
import ZInQKernel.Contrib.CloudB3RC53.Assembly

/-!
# Theorem 5.3, Lane RC0: `BranchPackageNode` from Elliot's finer steps

`branchPackageNode_of_steps` proves the blueprint's node
`ZInQ.Contrib.CloudB3RC53.BranchPackageNode` (Branch 1, or the fixed-field package
`FixedFieldPackage` of Branch 2) from the blueprint's printed leaves `Prints` (BCDT, Kolyvagin),
the Kummer-sequence glue `KummerCorankZero`, and, for each admissible `ℓ`, the finer steps
`RCSteps (D ℓ)` about interface data `D ℓ` (`Steps.lean`), following Elliot's text:

1. **Branch split** (lines 2593–2602). If the intrinsic odd limit symbol is a unit at the empty
   configuration (`RCData.OddEmptyUnit`), choose an actual stage carrying that value with
   `M_θ > δ_o` (`oddEmptyUnit_stage`, PROVED from the ultrafilter); `D = 1` is in the support and
   `v₂ a_{M_θ}(1) = δ_o < M_θ`, so (O.8) gives `ord_{s=1} L(E,s) = 1` (`rc_of_oddEmptyUnit`).
2. **Remaining branch: the package** (`fixedFieldPackage_of_steps`). The final companion `k`
   (2604–2613) gives `k` and `L(E^{(k)},1) ≠ 0`; the forward theorem gives `s₂(E^{(k)}/ℚ) = 0`
   and `s₂(E/K) = 1` (2627–2647). The constants are fixed in Elliot's order (2704–2711,
   5650–5662, App G 10898–10905): `C_o, C_e` (3.9), `C_per` (3.4), `C_cal` (4.6), hence
   `B = 2C_o + C_e − v₂L_*(h_*) + C_per + 2 + C_cal` (`central_upper_bound`, from (3.9), (3.4),
   (4.6), (4.7)); then `c_det, d_K` (5.9, fixed with `K`) and `L_T(M) = 16(d_K + 5)M`. For each
   `M, b` allowed by (5.10), the family (3.9) of dimension `max(b, b₀)` and its coefficient data
   (5.9) are restricted to a subcube of dimension `b` (`restrictData`), and the base-zero lemma
   (4319–4373) gives the package's `BaseZero`.

The blueprint's `restrictedConverseGenuine_of_nodes` then gives Theorem 5.3 from `Prints`, this
node and `MissingAddressNode` (lane RC1-boolean); `restrictedConverseGenuine_of_steps` records the
composition.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology

attribute [local instance] Nat.fact_prime_two

/-! ## Branch 1 -/

/-- **An actual stage carrying the unit value** (PROVED; lines 2593–2596). If the odd symbol is
a unit at the empty configuration, some stage has `v₂ a_{M_θ}(1) = δ_o < M_θ`. -/
theorem oddEmptyUnit_stage {ℓ : ℕ} (D : RCData ℓ) (hU : D.OddEmptyUnit)
    (hM : Tendsto D.Mθ (D.stages : Filter ℕ) atTop) :
    ∃ θ : ℕ, vZ (D.aθ θ 1) = D.δo ∧ D.δo < (D.Mθ θ : ℤ) := by
  have hev : ∀ᶠ θ in (D.stages : Filter ℕ), D.δo.toNat + 1 ≤ D.Mθ θ :=
    tendsto_atTop.mp hM (D.δo.toNat + 1)
  obtain ⟨θ, h1, h2⟩ := (hU.and hev).exists
  refine ⟨θ, h1, ?_⟩
  have := Int.self_le_toNat D.δo
  omega

/-- **Branch 1** (lines 2593–2599, PROVED from (O.8)): if the intrinsic odd limit symbol is a unit
at the empty configuration, choose an actual stage carrying that value with `M_θ > δ_o`; the index
`D = 1` lies in every moving support and `v₂ a_{M_θ}(1) = δ_o < M_θ`, so (O.8) gives
`ord_{s=1} L(E,s) = 1`. No companion or determinant bound is used. -/
theorem rc_of_oddEmptyUnit {ℓ : ℕ} (D : RCData ℓ) (S : RCSteps D) (hU : D.OddEmptyUnit) :
    AnalyticRankOne (Ecurve ℓ) := by
  obtain ⟨θ, hval, hlt⟩ := oddEmptyUnit_stage D hU S.stages_advance
  obtain ⟨Cdet, hO8⟩ := S.visibility
  have hvis : vZ (D.aθ θ 1) < (D.Mθ θ : WithTop ℤ) := by
    rw [hval]
    exact_mod_cast hlt
  have h := (hO8 θ 1 (S.one_admissible θ) hvis).1
  have h1 : Etw ℓ 1 = Ecurve ℓ := by
    simp only [Etw, Ecurve, Int.cast_one, qtwist_one_curve]
  rw [h1] at h
  exact (analyticRank_one_iff _).mp h

/-! ## The upper bound `B` at the nonzero addresses -/

/-- **The upper bound `v₂ ũ_x(0) ≤ B` at every nonzero address** (PROVED from (3.9), (3.4), (4.6),
(4.7) and the normalization of `L_*`; lines 2713–2714, 5728–5732, App G 10868–10884):
`2j_rc(h_x,k) ≤ 4ω(h_x) + C_J` with `C_J = 2C_o + C_e − v₂L_*(h_*) + C_per + 2`, and the finite
`Ш` and companion terms of (4.6) are nonnegative, so `v₂ ũ_x(0) ≤ C_J + C_cal`. -/
theorem central_upper_bound {ℓ : ℕ} {D : RCData ℓ} (S : RCSteps D) (hk0 : D.kfin ≠ 0)
    {Cper Ccal : ℤ}
    (h34 : ∀ h : ℤ, D.prepared h → AnalyticRank (Etw ℓ h) 1 → D.Lstar (h * D.kfin) ≠ 0 →
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ D.S ∧ jacobiSym D.kfin q = 1) →
      ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * D.jrc h D.kfin - 2 * D.jgen h =
        padicValRat 2 (D.Lstar (h * D.kfin)) - padicValRat 2 (D.Lstar D.hstar) + Cper + ε)
    (hcal : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
        AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ Ccal ∧
          v2 (central (D.uPrim F x)) =
            ((2 * D.jrc (F.h x) D.kfin - 4 * omega (F.h x) - shaLength (Etw ℓ (F.h x)) -
              shaLength (Etw ℓ (F.h x * D.kfin)) -
                ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ))
    {Co Ce : ℤ} {F : Family} (hF : D.FinalFamilyAt Co Ce F) {x : Addr F.b} (hx : x ≠ 0) :
    v2 (central (D.uTilde F x)) ≤
      ((2 * Co + Ce - padicValRat 2 (D.Lstar D.hstar) + Cper + 2 + Ccal : ℤ) : WithTop ℤ) := by
  obtain ⟨hadm, hfx⟩ := hF
  obtain ⟨hprep, hsz, hLne, hjg, hvL⟩ := hfx x hx
  have hh0 : F.h x ≠ 0 := Family.h_ne_zero hadm x
  have hcn : AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 :=
    (S.lstar_ne_zero_iff _ (mul_ne_zero hh0 hk0)).mp hLne
  -- (3.4) at `(h_x, k)`
  have hprimes : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ F.h x → q ∉ D.S ∧ jacobiSym D.kfin q = 1 := by
    intro q hq hqd
    obtain ⟨-, -, hqS, hjac, -⟩ := hadm q (Family.mem_Q_of_prime_dvd hadm x hq hqd)
    exact ⟨hqS, hjac⟩
  obtain ⟨ε, hε, h34x⟩ := h34 (F.h x) hprep hsz hLne hprimes
  -- (4.6) at `(h_x, k)`
  obtain ⟨t, err, -, herr, h46⟩ := hcal Co Ce F ⟨hadm, hfx⟩ x hsz hcn
  -- (4.7)
  obtain ⟨ε', hε', h47⟩ := S.common_coordinate Co Ce F ⟨hadm, hfx⟩ x
  rw [h47, v2_central_lamUnit_mul hε', h46]
  apply WithTop.coe_le_coe.mpr
  have hT : 0 ≤ ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) :=
    Finset.sum_nonneg fun p _ => Int.natCast_nonneg _
  have hs1 : (0 : ℤ) ≤ shaLength (Etw ℓ (F.h x)) := Int.natCast_nonneg _
  have hs2 : (0 : ℤ) ≤ shaLength (Etw ℓ (F.h x * D.kfin)) := Int.natCast_nonneg _
  have hε2 := (abs_le.mp hε).2
  have herr2 := (abs_le.mp herr).2
  linarith

/-! ## The remaining branch: the fixed-field package -/

/-- **`s₂(E/K) = 1` in the remaining branch** (lines 2627–2647, PROVED from the blueprint's BCDT
and Kolyvagin leaves and the Kummer glue): the forward theorem at the known nonzero central value
`L(E^{(k)},1)` gives `corank Sel_{2^∞}(E^{(k)}/ℚ) = 0`. -/
theorem selmerCorankOneOverK_of {ℓ : ℕ} (hℓ : 0 < ℓ) (P : Prints) (hKum : KummerCorankZero)
    {k : ℤ} (hk0 : k ≠ 0) (hk : AnalyticRank (Etw ℓ k) 0) (hSel : SelmerCorankOne (Ecurve ℓ)) :
    SelmerCorankOneOverK ℓ k := by
  have hEk : (Etw ℓ k).IsElliptic := by
    rw [Etw, Ecurve, qtwist_curve]
    exact PoleRC.curve_isElliptic (mul_ne_zero (by exact_mod_cast hk0)
      (by exact_mod_cast hℓ.ne'))
  obtain ⟨hrank, hsha⟩ := P.kolyvagin (Etw ℓ k) hEk (P.bcdt _ hEk) 0 (Nat.zero_le 1) hk
  exact ⟨hSel, hKum _ hEk (by exact_mod_cast hrank) hsha⟩

/-- **The fixed-field package of the remaining branch** (PROVED from the inputs; Sections 7–9 as
Elliot orders them, see the module docstring). -/
theorem fixedFieldPackage_of_steps {ℓ : ℕ} (hℓ : 0 < ℓ) (P : Prints) (hKum : KummerCorankZero)
    (D : RCData ℓ) (S : RCSteps D) (hSel : SelmerCorankOne (Ecurve ℓ)) (hU : ¬ D.OddEmptyUnit) :
    Nonempty (FixedFieldPackage (Ecurve ℓ)) := by
  -- The final companion `k` (lines 2604–2613) and `s₂(E/K) = 1` (2627–2647).
  obtain ⟨hkneg, -, -, -, -, hkL⟩ := S.companion hU
  have hk0 : D.kfin ≠ 0 := hkneg.ne
  have hSelK : SelmerCorankOneOverK ℓ D.kfin := selmerCorankOneOverK_of hℓ P hKum hk0 hkL hSel
  -- Constants fixed before `b`: `C_o, C_e` (3.9), `C_per` (3.4), `C_cal` (4.6), hence `B`.
  obtain ⟨Co, Ce, b₀, hfam⟩ := S.final_family hU
  obtain ⟨Cper, h34⟩ := S.gz_comparison
  obtain ⟨Ccal, hcal⟩ := S.calibration
  set Bz : ℤ := 2 * Co + Ce - padicValRat 2 (D.Lstar D.hstar) + Cper + 2 + Ccal with hBz
  -- `K` fixes `c_det, d_K` (5.9).
  obtain ⟨cdet, dK, hclr⟩ := S.clearing
  -- The package: `k`, `L(E^{(k)},1) ≠ 0`, `B`, `c_det`, `L_T(M) = 16(d_K + 5)M`, and the data.
  refine ⟨⟨(D.kfin : ℚ), hkL, Bz.toNat, cdet, fun M => 16 * (dK + 5) * M, ?_⟩⟩
  intro M b _ _ _
  -- The family (3.9) of dimension `max(b, b₀)` and its coefficient data (5.9) at precision `M`.
  obtain ⟨F, hFb, hF⟩ := hfam (max b b₀) (le_max_right _ _)
  have hbF : b ≤ F.b := hFb ▸ le_max_left _ _
  obtain ⟨C, c, hCu, hc, hdec, hsum, hpole, hbase⟩ := hclr M Co Ce F hF
  -- `ũ_x ∈ Λ[1/2]`: one bound on the coefficients (height-one regularity).
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ x j, ‖C.u x j‖ ≤ (2 : ℝ) ^ e := by
    classical
    choose e g hg using fun x => S.height_one Co Ce F hF x
    refine ⟨Finset.univ.sup e, fun x j => ?_⟩
    rw [hCu x j]
    exact (InLamHalf.norm_coeff_le (hg x) j).trans
      (pow_le_pow_right₀ (by norm_num) (Finset.le_sup (Finset.mem_univ x)))
  have hCl : ClearingIdentity C := ⟨hdec, ⟨e, he⟩, hsum⟩
  -- The upper bound `B` at the nonzero addresses.
  have hUB : UpperBound C Bz.toNat := by
    intro x hx
    have hv := central_upper_bound S hk0 h34 hcal hF hx
    have hv' : v2 (central (D.uTilde F x)) ≤ ((Bz.toNat : ℤ) : WithTop ℤ) :=
      hv.trans (WithTop.coe_le_coe.mpr (Int.self_le_toNat Bz))
    rw [hCu x 0]
    exact norm_ge_of_v2_le hv'
  -- The base-zero lemma.
  have hBZ : BaseZero (Ecurve ℓ) (D.kfin : ℚ) C := by
    intro hP
    rw [hCu 0 0]
    exact S.base_zero hSelK hkL hP Co Ce F hF
  exact ⟨restrictData hbF C, c, hc, restrictData_clearing hbF hCl, restrictData_pole hbF hpole,
    restrictData_base hbF hbase, restrictData_upper hbF hUB, restrictData_baseZero hbF hBZ⟩

/-! ## The node -/

/-- **`BranchPackageNode` from Elliot's finer steps** (PROVED from the inputs). For every `ℓ` in
the domain of Theorem 5.3 with `corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1`: Branch 1 gives
`ord_{s=1} L(E_ℓ,s) = 1` (`rc_of_oddEmptyUnit`), and otherwise the fixed-field package exists
(`fixedFieldPackage_of_steps`). -/
theorem branchPackageNode_of_steps (P : Prints) (hKum : KummerCorankZero)
    (D : ∀ ℓ : ℕ, RCData ℓ) (hS : ∀ ℓ : ℕ, Adm ℓ → RCSteps (D ℓ)) : BranchPackageNode := by
  intro ℓ hadm hSel
  by_cases hU : (D ℓ).OddEmptyUnit
  · exact Or.inl (rc_of_oddEmptyUnit (D ℓ) (hS ℓ hadm) hU)
  · exact Or.inr (fixedFieldPackage_of_steps hadm.1 P hKum (D ℓ) (hS ℓ hadm) hSel hU)

/-- **Theorem 5.3 from the blueprint's assembly** (a composition, not a second skeleton):
`restrictedConverseGenuine_of_nodes` with `branchPackageNode_of_steps` and the missing-address node
of lane RC1-boolean. -/
theorem restrictedConverseGenuine_of_steps (P : Prints) (hKum : KummerCorankZero)
    (D : ∀ ℓ : ℕ, RCData ℓ) (hS : ∀ ℓ : ℕ, Adm ℓ → RCSteps (D ℓ))
    (hMA : MissingAddressNode) : RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_nodes P (branchPackageNode_of_steps P hKum D hS) hMA

/-! ## Non-vacuity of the interface

The inputs quantify over interface data. The checks below show that the quantifiers are not empty
and that the branch split is a genuine case distinction: `RCData ℓ` is inhabited; the families
quantified in (4.6), (4.7), (5.9), the height-one regularity and the base-zero lemma include an
actual family (`finalFamilyAt_trivial`), and admissible families with nonzero addresses exist
(`admissible_example`), so the conditions (3.9) imposes at `x ≠ 0` are not vacuous; the odd
empty-configuration symbol can be a unit or not (`toyData_oddEmptyUnit`,
`toyData_not_oddEmptyUnit`), with arbitrarily advanced stages along a nonprincipal ultrafilter
(`toyData_stages_advance`); and the conjunction of the package's predicates is satisfiable
(`coordData_witness`). -/

/-- Toy interface data, with constant odd coefficients `a`: the hyperfilter on stages, `M_θ = θ`. -/
def toyData (ℓ : ℕ) (a : ℤ) : RCData ℓ where
  S := ∅
  prepared := fun _ => True
  Lstar := fun _ => 1
  jgen := fun _ => 0
  jrc := fun _ _ => 0
  hstar := -1
  stages := Filter.hyperfilter ℕ
  Mθ := fun θ => θ
  aθ := fun _ _ => a
  admissible := fun _ _ => True
  δo := 0
  kfin := -7
  uPrim := fun _ _ => 1
  uTilde := fun _ _ => 1

instance (ℓ : ℕ) : Inhabited (RCData ℓ) := ⟨toyData ℓ 0⟩

/-- With unit odd coefficients the empty configuration is a unit (PROVED). -/
theorem toyData_oddEmptyUnit (ℓ : ℕ) : (toyData ℓ 1).OddEmptyUnit := by
  refine Filter.Eventually.of_forall fun θ => ?_
  simp [toyData, vZ, v2]

/-- With zero odd coefficients the empty configuration is not a unit (PROVED). -/
theorem toyData_not_oddEmptyUnit (ℓ : ℕ) : ¬ (toyData ℓ 0).OddEmptyUnit := by
  intro h
  have h' : ∀ᶠ _θ in ((toyData ℓ 0).stages : Filter ℕ), False := by
    filter_upwards [h] with θ hθ
    simp [toyData, vZ, v2] at hθ
  exact h'.exists.elim fun _ h => h

/-- The toy stages advance along the (nonprincipal) hyperfilter (PROVED). -/
theorem toyData_stages_advance (ℓ : ℕ) (a : ℤ) :
    Tendsto (toyData ℓ a).Mθ ((toyData ℓ a).stages : Filter ℕ) atTop := by
  have h : ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
    Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le
  exact tendsto_id.mono_left h

/-- The binary family of dimension `0` (`h_0 = 1` only). -/
def trivialFamily : Family := ⟨0, ∅, fun _ => 0⟩

/-- Every interface datum has a family satisfying (3.9) in dimension `0`, so the statements
quantified over final families are not vacuous (PROVED). -/
theorem finalFamilyAt_trivial {ℓ : ℕ} (D : RCData ℓ) (Co Ce : ℤ) :
    D.FinalFamilyAt Co Ce trivialFamily := by
  refine ⟨fun q hq => absurd hq (Finset.notMem_empty q), fun x hx => absurd ?_ hx⟩
  funext i
  exact i.elim0

/-- An admissible family with a nonzero address: `b = 1`, `Q = {11}`, `λ₁₁ = x ↦ x₀`, for the
companion `k = −7` (`(−7/11) = 1`) and empty support (PROVED). -/
theorem admissible_example :
    Family.Admissible ∅ (-7) ⟨1, {11}, fun _ => LinearMap.proj (R := ZMod 2)
      (φ := fun _ : Fin 1 => ZMod 2) 0⟩ := by
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst hq
  refine ⟨by norm_num, by norm_num, Finset.notMem_empty _, by norm_num, ?_⟩
  intro h
  have := LinearMap.congr_fun h (fun _ => 1)
  simp at this

/-- **The package's predicates are jointly satisfiable** (PROVED): in dimension `0`, `f = 1`,
`d = 0`, `ũ = 0` satisfy the clearing identity, every pole bound, a regular base with `c = 0`,
every upper bound and the base-zero conclusion. -/
theorem coordData_witness (E : WeierstrassCurve ℚ) (k : ℚ) (LT M B : ℕ) :
    ∃ C : CoordData 0, ClearingIdentity C ∧ PoleBound C LT M ∧ BaseRegular C 0 ∧
      UpperBound C B ∧ BaseZero E k C := by
  let C : CoordData 0 := ⟨fun _ i => if i = 0 then 1 else 0, fun _ _ => 0, fun _ _ => 0⟩
  have hx : ∀ x : Fin 0 → ZMod 2, x = 0 := fun x => funext fun i => i.elim0
  have hsF : ∀ (x : Fin 0 → ZMod 2) (i : ℤ), signEval C.F x i = if i = 0 then 1 else 0 := by
    intro x i
    simp [signEval, sgn, C]
  have hsD : ∀ (x : Fin 0 → ZMod 2) (i : ℤ), signEval C.D x i = 0 := by
    intro x i
    simp [signEval, C]
  refine ⟨C, ⟨fun g => ?_, ⟨0, fun x j => by simp [C]⟩, fun x n => ?_⟩, fun x i hi => ?_,
    ⟨fun i hi => ?_, ?_, ?_⟩, fun x hx' => absurd (hx x) hx', fun _ => rfl⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot 0] with i hi
    simp [C, hi.ne]
  · rw [hsD]
    simp [C]
  · rw [hsF]
    have : i ≠ 0 := by omega
    simp [this]
  · rw [hsF]; simp [hi.ne]
  · rw [hsF]; simp
  · rw [hsF]; simp

end ZInQ.Manuscript.RC
