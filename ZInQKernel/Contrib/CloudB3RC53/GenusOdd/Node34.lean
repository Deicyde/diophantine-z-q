import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusLower

/-!
# GenusOdd: the nodes (3.4), (3.6) and the stage filter, in the forms consumed downstream

* `GenusLower34` / `genusLower34_proof` (Proposition `ex:sec7-genus-lower`, (3.4), tex L2418–2439):
  PROVED from `Prints` and the GLUE `Glue34`, plus the rationality of the fixed `L_*(h_*)`
  (Birch–Manin rationality via modular symbols, with Manin–Drinfeld; explicit hypothesis
  `hElkikMD`). **Known issue K3**: `Prints.cst` is used as stated, not reconstructed.
* `GzEveryCompanion` / `gzEveryCompanion_genuine`: (3.4) at every `(h, k')`, the hypothesis of
  `AppGEndpoints.FinalFamilyField` (text copied from `AppGEndpoints/RCTarget.lean`), at
  the genuine `Prepared`, `AnalyticRank · 1`, `LstarQ`, `jgenOf`, `jrcOf`, `Companion`, `C_per = 0`.
* `GzComparisonText` / `gzComparison_genuine`: the field `RCSteps.gz_comparison` (text copied from
  `ZInQKernel/Contrib/OneProof/RC/Skeleton/Steps.lean` at commit 839ff728 of the RC integration
  branch, with `D.prepared, D.Lstar, D.jgen, D.jrc, D.hstar, D.kfin, D.S` as parameters).
* `GenusLower36Core`: (3.3) + (3.4) + (3.5) ⇒ (3.6) (tex L2440–2452), PROVED (inequality core).
* `StagesAdvance` / `stagesAdvance_of_nonprincipal`: the field `RCSteps.stages_advance` for a
  nonprincipal ultrafilter on a stage sequence with `M_θ ≥ θ` (tex L2491–2500, L2536–2551).
-/

noncomputable section

open NumberField Filter

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-! ### (3.4) over genuine objects -/

/-- **Proposition `ex:sec7-genus-lower`, identity (3.4)** (tex L2418–2439):
`2 j_rc(h,k') − 2 j_gen(h) = v₂ L_*(hk') − v₂ L_*(h_*) + ε`, `|ε| ≤ 2`, for `h` a known simple zero
in the prepared filter, `k'` a rough companion, and any genus and ring-class data (the analytic
model of the Heegner points). Both index valuations are finite. The fixed curve is any elliptic
`E/ℚ` with `a₁ = a₃ = 0` (such as `E_ℓ`) with its newform `f`, period lattice `Lat` (non-CM) and
parametrization scale `κ` ("the parametrization is the same", tex L2430). Hypothesis `hElkikMD`:
`L_*(h_*)` is rational (Manin–Drinfeld; the manuscript takes `v₂ L_*(h_*)` as a number). The
"fixed initial period convention" is the same `Ω⁻` on both sides, so the constant is `0`. -/
def GenusLower34 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.a₁ = 0 → E.a₃ = 0 →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2),
    (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
    ∀ (Lat : PeriodPair), IsLatticeOf E Lat → IsNonCMLattice Lat →
    ∀ κ : ℂ, IsParamScale (newformLevel E) f Lat κ →
    ∀ hstar : ℤ, GenusPartner E hstar → (∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar) →
    ∀ h k' : ℤ, Prepared E hstar h → AnalyticRank (qtwist E h) 1 → Companion E Lat hstar h k' →
    ∀ (datG : HeegnerDatum E f Lat κ (h * hstar) 1 hstar)
      (datR : HeegnerDatum E f Lat κ k' h.natAbs h),
      datG.index ≠ ⊤ ∧ datR.index ≠ ⊤ ∧ ∃ ε : ℤ, |ε| ≤ 2 ∧
        2 * (datR.index.toNat : ℤ) - 2 * (datG.index.toNat : ℤ) =
          padicValRat 2 (LstarQ E Lat (h * k')) - padicValRat 2 (LstarQ E Lat hstar) + ε

/-- **(3.4) PROVED** from the printed leaves and the GLUE of `Glue.lean`. -/
theorem genusLower34_proof (P : Prints) (G : Glue34) : GenusLower34 := by
  intro E _ h₁ h₃ f hf Lat hLat hNC κ hκ hstar hgp hElkikMD h k' hp hz hk datG datR
  exact core34 P G h₁ h₃ hf hLat hNC hκ hgp hElkikMD hp hz hk datG datR

/-! ### (3.4) at every `(h, k')`, in the form of `AppGEndpoints.FinalFamilyField` -/

/-- The (3.4) hypothesis of `AppGEndpoints.FinalFamilyField` (statement text copied verbatim from
`AppGEndpoints/RCTarget.lean`), with its data as parameters. -/
def GzEveryCompanion (prepared simpleZero : ℤ → Prop) (Lstar : ℤ → ℚ) (jgen : ℤ → ℤ)
    (jrc : ℤ → ℤ → ℤ) (hstar : ℤ) (companion : ℤ → ℤ → Prop) (Cper : ℤ) : Prop :=
  ∀ h k', prepared h → simpleZero h → companion h k' → ∃ ε : ℤ, |ε| ≤ 2 ∧
    2 * jrc h k' - 2 * jgen h =
      padicValRat 2 (Lstar (h * k')) - padicValRat 2 (Lstar hstar) + Cper + ε

/-- **(3.4) at every `(h, k')` at the genuine objects** (PROVED from `Prints`, `Glue34`): for any
selections of genus and ring-class data defined wherever `h` is a prepared simple zero and `k'` a
companion, with `C_per = 0`. -/
theorem gzEveryCompanion_genuine (P : Prints) (G : Glue34) {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel E) f Lat κ) {hstar : ℤ} (hgp : GenusPartner E hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum E f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared E hstar h → AnalyticRank (qtwist E h) 1 → (selG h).isSome)
    (hselR : ∀ h k', Prepared E hstar h → AnalyticRank (qtwist E h) 1 →
      Companion E Lat hstar h k' → (selR h k').isSome) :
    GzEveryCompanion (Prepared E hstar) (fun h => AnalyticRank (qtwist E h) 1) (LstarQ E Lat)
      (jgenOf E f Lat κ hstar selG) (jrcOf E f Lat κ selR) hstar (Companion E Lat hstar) 0 := by
  intro h k' hp hz hk
  obtain ⟨datG, hdG⟩ := Option.isSome_iff_exists.mp (hselG h hp hz)
  obtain ⟨datR, hdR⟩ := Option.isSome_iff_exists.mp (hselR h k' hp hz hk)
  obtain ⟨-, -, ε, hε, heq⟩ := core34 P G h₁ h₃ hf hLat hNC hκ hgp hElkikMD hp hz hk datG datR
  refine ⟨ε, hε, ?_⟩
  simp only [jgenOf, jrcOf, hdG, hdR]
  rw [heq]
  ring

/-! ### The field `RCSteps.gz_comparison` -/

/-- The field `RCSteps.gz_comparison` (statement text copied verbatim from
`ZInQKernel/Contrib/OneProof/RC/Skeleton/Steps.lean`, RC integration branch at 839ff728), with the
`RCData` fields as parameters and `Etw ℓ h = qtwist (Ecurve ℓ) h`. -/
def GzComparisonText (ℓ : ℕ) (prepared : ℤ → Prop) (Lstar : ℤ → ℚ) (jgen : ℤ → ℤ)
    (jrc : ℤ → ℤ → ℤ) (hstar kfin : ℤ) (S : Finset ℕ) : Prop :=
  ∃ Cper : ℤ, ∀ h : ℤ, prepared h → AnalyticRank (qtwist (Ecurve ℓ) (h : ℚ)) 1 →
    Lstar (h * kfin) ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ S ∧ jacobiSym kfin q = 1) →
    ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * jrc h kfin - 2 * jgen h =
      padicValRat 2 (Lstar (h * kfin)) - padicValRat 2 (Lstar hstar) + Cper + ε

theorem squareAt_of_jacobiSym {k : ℤ} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : jacobiSym k q = 1) : SquareAt q k := by
  have := Fact.mk hq
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have hne : ((k : ZMod q)) ≠ 0 := by
    intro h0
    rw [legendreSym, h0, quadraticChar_zero] at h
    exact zero_ne_one h
  refine ⟨fun hdvd => hne ((ZMod.intCast_zmod_eq_zero_iff_dvd k q).mpr hdvd), fun h2 => absurd h2 hq2,
    fun _ => (legendreSym.eq_one_iff q hne).mp h⟩

/-- **`RCSteps.gz_comparison` at the genuine objects** (PROVED from `Prints`, `Glue34`) for the
curve `E_ℓ`, at a final companion `k` that is a negative odd fundamental discriminant, a unit square
at every prime of `2N`, prime to `h_*` (tex L2595–2603 with L2349–2352), when `D.prepared` is the
genuine `Prepared` and `D.Lstar, D.jgen, D.jrc` are `LstarQ, jgenOf, jrcOf` (with `C_per = 0`). -/
theorem gzComparison_genuine (P : Prints) (G : Glue34) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) {hstar kfin : ℤ}
    (hgp : GenusPartner (Ecurve ℓ) hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar (Ecurve ℓ) Lat hstar)
    (hk0 : kfin < 0) (hk4 : kfin % 4 = 1) (hksq : Squarefree kfin)
    (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p kfin)
    (hkcop : IsCoprime kfin hstar) (S : Finset ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      (selG h).isSome)
    (hselR : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      Companion (Ecurve ℓ) Lat hstar h kfin → (selR h kfin).isSome) :
    GzComparisonText ℓ (Prepared (Ecurve ℓ) hstar) (LstarQ (Ecurve ℓ) Lat)
      (jgenOf (Ecurve ℓ) f Lat κ hstar selG) (jrcOf (Ecurve ℓ) f Lat κ selR) hstar kfin S := by
  refine ⟨0, fun h hp hz hL hq => ?_⟩
  have h₁ : (Ecurve ℓ).a₁ = 0 := rfl
  have h₃ : (Ecurve ℓ).a₃ = 0 := rfl
  have hodd : h % 2 = 1 := by
    have := (hp.2.2.1 2 Nat.prime_two (dvd_mul_right 2 _)).2.1 rfl
    omega
  have hk : Companion (Ecurve ℓ) Lat hstar h kfin := by
    refine ⟨hk0, hk4, hksq, fun p hp' hpd => ?_, hkcop, ?_⟩
    · have hp'' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp'
      rcases hp''.dvd_or_dvd hpd with h1 | h1
      · exact hk2N p hp' (by exact_mod_cast h1)
      · have hp2 : p ≠ 2 := by
          rintro rfl
          obtain ⟨m, hm⟩ := h1
          omega
        exact squareAt_of_jacobiSym hp' hp2 (hq p hp' h1).2
    · rw [← LstarQ_spec hL]
      exact_mod_cast hL
  obtain ⟨datG, hdG⟩ := Option.isSome_iff_exists.mp (hselG h hp hz)
  obtain ⟨datR, hdR⟩ := Option.isSome_iff_exists.mp (hselR h hp hz hk)
  obtain ⟨-, -, ε, hε, heq⟩ := core34 P G h₁ h₃ hf hLat hNC hκ hgp hElkikMD hp hz hk datG datR
  refine ⟨ε, hε, ?_⟩
  simp only [jgenOf, jrcOf, hdG, hdR]
  rw [heq]
  ring

/-! ### (3.3) + (3.4) + (3.5) ⇒ (3.6) -/

/-- **The inequality core of (3.6)** (tex L2440–2452): from (3.3)
`v₂L_*(hk') ≤ 2ω(h) + 2ω(k') + s(hk') + C_E`, (3.4) with its `ε`, `|ε| ≤ 2`, and (3.5)
`2j_rc ≥ 4ω(h) + s(h) + s(hk') − C_R` at a companion with `ω(k') ≤ A`, the term `s(hk')` cancels:
`2j_gen(h) ≥ 2ω(h) + s(h) − C` with `C = C_R + C_E + 2A + 2 − v₂L_*(h_*) + C_per`, independent of
`h` (`v₂L_*(h_*)` is fixed with `h_*`). -/
def GenusLower36Core : Prop :=
  ∀ (jg jr vk vs ωh ωk sh shk A CE CR Cper : ℤ), ωk ≤ A →
    vk ≤ 2 * ωh + 2 * ωk + shk + CE →
    (∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * jr - 2 * jg = vk - vs + Cper + ε) →
    4 * ωh + sh + shk - CR ≤ 2 * jr →
    2 * ωh + sh - (CR + CE + 2 * A + 2 - vs + Cper) ≤ 2 * jg

theorem genusLower36Core_proof : GenusLower36Core := by
  intro jg jr vk vs ωh ωk sh shk A CE CR Cper hA h33 ⟨ε, hε, h34⟩ h35
  have := (abs_le.mp hε).2
  linarith

/-- Non-vacuity of `GenusLower36Core`'s hypotheses: they hold simultaneously (all quantities `0`,
`A = 0`). -/
theorem genusLower36Core_hyps_nonvacuous :
    ∃ (jg jr vk vs ωh ωk sh shk A CE CR Cper : ℤ), ωk ≤ A ∧
      vk ≤ 2 * ωh + 2 * ωk + shk + CE ∧
      (∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * jr - 2 * jg = vk - vs + Cper + ε) ∧
      4 * ωh + sh + shk - CR ≤ 2 * jr :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, le_rfl, le_rfl, ⟨0, by norm_num, by norm_num⟩, le_rfl⟩

/-! ### The stage filter -/

/-- The field `RCSteps.stages_advance` (text of `Steps.lean` at 839ff728, data as parameters). -/
def StagesAdvance (stages : Ultrafilter ℕ) (Mθ : ℕ → ℕ) : Prop :=
  Tendsto Mθ (stages : Filter ℕ) atTop

/-- **`stages_advance`** (tex L2491–2500, L2536–2551; PROVED): (3.7) supplies arbitrarily advanced
stages, so the `θ`-th chosen stage can be taken with precision `M_θ ≥ θ`; along the chosen
nonprincipal ultrafilter the precision then tends to infinity. -/
theorem stagesAdvance_of_nonprincipal (stages : Ultrafilter ℕ)
    (hU : (stages : Filter ℕ) ≤ cofinite) (Mθ : ℕ → ℕ) (hM : ∀ θ, θ ≤ Mθ θ) :
    StagesAdvance stages Mθ := by
  have h1 : Tendsto Mθ atTop atTop := tendsto_atTop_mono hM tendsto_id
  have h2 : Tendsto Mθ cofinite atTop := by rw [Nat.cofinite_eq_atTop]; exact h1
  exact h2.mono_left hU

/-- Non-vacuity of the stage hypothesis: every free ultrafilter on `ℕ` is nonprincipal in the sense
used above, and the identity stage sequence `M_θ = θ` satisfies `M_θ ≥ θ`. -/
theorem stagesAdvance_example : ∃ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ cofinite :=
  ⟨Ultrafilter.of cofinite, Ultrafilter.of_le cofinite⟩

end ZInQ.Contrib.CloudB3RC53.GenusOdd
