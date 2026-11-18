import ZInQKernel.Contrib.OneProof.RC.AppE.Rational
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenLowerBound
import ZInQKernel.Contrib.PoleRC.CRM

/-!
# Appendix E, Proposition `ex:app-even-phase`: `EvenPhaseData` for `E_ℓ`

The 11/5 manuscript, Appendix E, tex 7792–8134. This file fills lane RC11's structure
`EvenPhaseData E L σ D₀` (`RC/Even/EvenPhase.lean`, imported, not restated) for any elliptic
`E/ℚ`, then for the fixed curve `E_ℓ = Ecurve ℓ` of section 7 with `S₀` the primes of `2N`
(`N` the level of the functional equation of `L(E_ℓ, s)`, which is the conductor).

* `WaldspurgerNonvanishingTwoPower` — lane RC8's PRINT `WaldspurgerNonvanishing` with the
  conclusion "`ψ` has two-power order" that the manuscript states for Elliot's construction
  (tex 7920–7922: "the resulting classical character has two-power order"; tex 7944: "Both have
  two-power order"). `waldspurgerNonvanishing_of_twoPower` shows it is the tree's print plus that
  one conjunct. The conjunct is needed: `EvenPhaseData` asks `z_D` to be a two-power root of unity
  with `z_D² = ψ(D)ψ(D₀)⁻¹`, which fails if `ψ(D/D₀)` has odd order > 1 (the twist of an eigenform
  by a cubic character is again in a good-Hecke eigenspace of `E`, with characters `ψν²`, `ην²`).
* `evenPhaseData_of_prints` — the fields: `N, ψ, η, g, a(D₀) ≠ 0` from the print (with
  `ord_{s=1} L(E^{(σD₀)}, s) = 0` from `L_*(σD₀) ≠ 0` by BCDT); `retained` = the whole `S₀` filter
  of `D₀` (`S0Filter`); `z` = the phase `z_D` (`phase`); `rational` from the Galois comparison
  (`rational_of_ramsey`). The result also records `retained = {D | S0Filter S₀ D₀ D}` and
  `z = phase N η D₀`: the structure alone would be satisfied by `retained = {D₀}`.
* `evenPhaseData_Ecurve` — the same for `E_ℓ` with `S₀ = primes(2N)`: the hypothesis of the print
  "every prime of the level of every functional equation lies in `S₀`" holds because the level
  of a functional equation of `L(E, s)` is unique (`rootNumberAt_unique`, from `ModularNewform`).

Inputs: the PRINTs `WaldspurgerNonvanishingTwoPower` (Waldspurger + Elliot's local construction),
`WaldspurgerCor2` (lane RC8), `RamseyAlgebraicModel` (this lane), `ModularNewform` and
`HasseConvergence` (lane RC8; BCDT via `bcdtThmA_of_modularNewform`), and the GLUE hypothesis
`HalfIntegralTwist` (not proved; see `Galois.lean`). Everything else is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane

/-- **Waldspurger's nonvanishing input with Elliot's two-power scalar type** (PRINT + ELLIOT;
lane RC8's `WaldspurgerNonvanishing` (JMPA 60 (1981), Prop. 18 and its proof, pp. 466–467;
ICM 1983, Thm. 1 and Prop. 1; Elliot's local construction, tex 7837–7940), with the additional
conclusion of that construction that the scalar character `ψ` has two-power order
(tex 7920–7922, 7944); print UNVERIFIED). -/
def WaldspurgerNonvanishingTwoPower : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
    ∀ S₀ : Finset ℕ, (∀ p ∈ S₀, p.Prime) → 2 ∈ S₀ →
      (∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) →
      ∀ D₀ : ℕ, 0 < D₀ → Squarefree D₀ → (∀ p ∈ S₀, ¬ p ∣ D₀) →
        AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 →
        ∃ N : ℕ, 4 ∣ N ∧ (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) ∧
          ∃ ψ η : DirichletCharacter ℂ N,
            (∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)) ∧
            (∃ k : ℕ, ψ ^ (2 ^ k) = 1) ∧
            ∃ g : ℍ → ℂ, IsInWaldspurgerEigenspace E N ψ η g ∧ hiwCoeff g D₀ ≠ 0

/-- **The two-power form is the tree's print plus one conjunct** (PROVED). -/
theorem waldspurgerNonvanishing_of_twoPower (h : WaldspurgerNonvanishingTwoPower) :
    WaldspurgerNonvanishing := by
  intro E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq hD₀S hA
  obtain ⟨N, hN, hNS, ψ, η, hψη, -, g, hg, ha⟩ := h E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq hD₀S hA
  exact ⟨N, hN, hNS, ψ, η, hψη, g, hg, ha⟩

/-- A nonzero `L_*(σD₀)` gives `F₀(1) ≠ 0` for every continuation `F₀` of `L(E^{(σD₀)}, s)`
(PROVED, from the anchor of `L_*`). -/
theorem F_one_ne_zero_of_lstar {E : WeierstrassCurve ℚ}
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {h : ℤ} (hh : h ≠ 0)
    (hL : L.Lstar h ≠ 0) (F : ℂ → ℂ) (hF : IsLContinuation (qtwist E (h : ℚ)) F) : F 1 ≠ 0 := by
  intro h0
  apply hL
  have := L.anchor h hh F hF
  rw [h0, mul_zero, zero_div] at this
  exact_mod_cast this

/-- **`EvenPhaseData` from the prints** (Proposition `ex:app-even-phase`, tex 7792–8134; PROVED
from the PRINTs `WaldspurgerNonvanishingTwoPower`, `WaldspurgerCor2`, `RamseyAlgebraicModel`,
`PoleS12.BCDTThmA`, the GLUE `HasseConvergence` (lane RC8) and the GLUE hypothesis
`HalfIntegralTwist`). For an elliptic `E/ℚ`, a sign `σ`, a finite set `S₀ ∋ 2` of primes containing
the primes of the level of every functional equation of `L(E, s)`, and a positive squarefree
`D₀` prime to `S₀` with `L_*(σD₀) ≠ 0`: there is `P : EvenPhaseData E L σ D₀` whose retained set is
the whole `S₀` filter of `D₀` and whose phase is `z_D = phase P.N P.η D₀ D`. -/
theorem evenPhaseData_of_prints (hWN : WaldspurgerNonvanishingTwoPower) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist) (hB : PoleS12.BCDTThmA)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (S₀ : Finset ℕ) (hS₀ : ∀ p ∈ S₀, p.Prime) (h2 : 2 ∈ S₀)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀,
      P.retained = {D | S0Filter S₀ D₀ D} ∧ P.z = phase P.N P.η D₀ := by
  have hσD₀ := ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀
  have hA : AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 :=
    (ZInQ.Manuscript.RC.GlueSweep.Even.lstar_ne_zero_iff_of_bcdt hB hH L hσD₀).mp hL₀
  obtain ⟨N, hN, hNS, ψ, η, hψη, ⟨k, hψk⟩, g, hg, ha₀⟩ :=
    hWN E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq₀ hD₀S hA
  -- the level is positive: a finite `S₀` cannot contain every prime
  have hN0 : N ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (S₀.sup id + 1)
    have hpS := hNS p hp (dvd_zero p)
    have := Finset.le_sup (f := id) hpS
    simp only [id] at this
    omega
  have : NeZero N := ⟨hN0⟩
  have hcont := ZInQ.Manuscript.RC.GlueSweep.Even.twistContinuation_of_bcdt hB hH E
  have hF₀ := F_one_ne_zero_of_lstar L hσD₀ hL₀
  have hself := S0Filter.self h2 hD₀ hsq₀ hD₀S
  refine ⟨{ N := N, hN := hN, ψ := ψ, η := η, hψη := hψη, g := g, hg := hg, ha₀ := ha₀,
            retained := {D | S0Filter S₀ D₀ D},
            retained_spec := fun D hD => S0Filter.spec hNS hD,
            D₀_mem := hself,
            z := phase N η D₀,
            z_root := fun D hD => ?_,
            z_sq := fun D hD => ?_,
            rational := fun D hD => ?_ }, rfl, rfl⟩
  · obtain ⟨-, -, hc, hcl⟩ := S0Filter.spec hNS hD
    obtain ⟨-, -, hc₀, -⟩ := S0Filter.spec hNS hself
    exact phase_root hN0 hN ψ η hσ hψη hψk hc₀ hc hcl
  · obtain ⟨-, -, hc, hcl⟩ := S0Filter.spec hNS hD
    obtain ⟨-, -, hc₀, -⟩ := S0Filter.spec hNS hself
    exact phase_sq hN0 hN ψ η hσ hψη hc₀ hc hcl
  · obtain ⟨hD0, hsq, hc, hcl⟩ := S0Filter.spec hNS hD
    obtain ⟨-, -, hc₀, -⟩ := S0Filter.spec hNS hself
    exact rational_of_ramsey hR hTw hW hE hcont hσ hF₀ hN ψ η hψη hg ha₀ hD₀ hsq₀ hc₀ hD0 hsq hc
      hcl

/-- **The same with the retained set the whole filter at the level** (PROVED, same inputs): the
retained set may be taken to be every positive squarefree `D` prime to the level `P.N` in the unit
squareclasses of `D₀` at the primes of `P.N` (a superset of the `S₀` filter, since the level has
prime support in `S₀`; the Galois comparison only uses the primes of the level). -/
theorem evenPhaseData_of_prints_levelFilter (hWN : WaldspurgerNonvanishingTwoPower)
    (hW : WaldspurgerCor2) (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist)
    (hB : PoleS12.BCDTThmA) (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization E) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (S₀ : Finset ℕ) (hS₀ : ∀ p ∈ S₀, p.Prime) (h2 : 2 ∈ S₀)
    (hcond : ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ S₀, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData E L σ D₀,
      P.retained = {D | 0 < D ∧ Squarefree D ∧ D.Coprime P.N ∧ SameUnitClassesAtLevel P.N D D₀} ∧
      (∀ p : ℕ, p.Prime → p ∣ P.N → p ∈ S₀) ∧ P.z = phase P.N P.η D₀ := by
  have hσD₀ := ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀
  have hA : AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 :=
    (ZInQ.Manuscript.RC.GlueSweep.Even.lstar_ne_zero_iff_of_bcdt hB hH L hσD₀).mp hL₀
  obtain ⟨N, hN, hNS, ψ, η, hψη, ⟨k, hψk⟩, g, hg, ha₀⟩ :=
    hWN E hE σ hσ S₀ hS₀ h2 hcond D₀ hD₀ hsq₀ hD₀S hA
  have hN0 : N ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (S₀.sup id + 1)
    have hpS := hNS p hp (dvd_zero p)
    have := Finset.le_sup (f := id) hpS
    simp only [id] at this
    omega
  have : NeZero N := ⟨hN0⟩
  have hcont := ZInQ.Manuscript.RC.GlueSweep.Even.twistContinuation_of_bcdt hB hH E
  have hF₀ := F_one_ne_zero_of_lstar L hσD₀ hL₀
  have hself := S0Filter.spec hNS (S0Filter.self h2 hD₀ hsq₀ hD₀S)
  refine ⟨{ N := N, hN := hN, ψ := ψ, η := η, hψη := hψη, g := g, hg := hg, ha₀ := ha₀,
            retained := {D | 0 < D ∧ Squarefree D ∧ D.Coprime N ∧ SameUnitClassesAtLevel N D D₀},
            retained_spec := fun D hD => hD,
            D₀_mem := hself,
            z := phase N η D₀,
            z_root := fun D hD => phase_root hN0 hN ψ η hσ hψη hψk hself.2.2.1 hD.2.2.1 hD.2.2.2,
            z_sq := fun D hD => phase_sq hN0 hN ψ η hσ hψη hself.2.2.1 hD.2.2.1 hD.2.2.2,
            rational := fun D hD => rational_of_ramsey hR hTw hW hE hcont hσ hF₀ hN ψ η hψη hg ha₀
              hD₀ hsq₀ hself.2.2.1 hD.1 hD.2.1 hD.2.2.1 hD.2.2.2 }, rfl, hNS, rfl⟩

/-- **The primes of the level of every functional equation of `L(E, s)` lie in `primes(2N₀)`**
(PROVED from `ModularNewform` via `rootNumberAt_unique`), for any level `N₀` of one functional
equation: the hypothesis `hcond` of the print for `S₀ = primes(2N₀)`. -/
theorem hcond_primeFactors (hM : ModularNewform) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    {N₀ : ℕ} {w₀ : ℤ} (h₀ : RootNumberAt E N₀ w₀) :
    ∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N →
      p ∈ (2 * N₀).primeFactors := by
  intro N w hNw p hp hpN
  obtain ⟨rfl, -⟩ := rootNumberAt_unique hM hE hNw h₀
  exact Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_right hpN 2,
    mul_ne_zero two_ne_zero h₀.1.ne'⟩

/-- **`EvenPhaseData` for the curve `E_ℓ` of section 7** (Proposition `ex:app-even-phase` for
`E = E_ℓ`, tex 7792–8134; PROVED from the PRINTs `WaldspurgerNonvanishingTwoPower`,
`WaldspurgerCor2`, `RamseyAlgebraicModel`, `ModularNewform`, the GLUE `HasseConvergence` and the
GLUE hypothesis `HalfIntegralTwist`). `S₀` is the set of primes of `2N₀`, `N₀` the level of a
functional equation of `L(E_ℓ, s)` (the conductor, `ModularNewform`); `D₀ > 0` is squarefree, prime
to `2N₀`, with `L_*(σD₀) ≠ 0`. The retained set is the whole `S₀` filter. -/
theorem evenPhaseData_Ecurve (hWN : WaldspurgerNonvanishingTwoPower) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist) (hM : ModularNewform)
    (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : ZInQ.Manuscript.RC.Even.CentralNormalization (Ecurve ℓ)) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {N₀ : ℕ} {w₀ : ℤ} (h₀ : RootNumberAt (Ecurve ℓ) N₀ w₀)
    {D₀ : ℕ} (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hD₀S : ∀ p ∈ (2 * N₀).primeFactors, ¬ p ∣ D₀)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    ∃ P : ZInQ.Manuscript.RC.Even.EvenPhaseData (Ecurve ℓ) L σ D₀,
      P.retained = {D | S0Filter (2 * N₀).primeFactors D₀ D} ∧ P.z = phase P.N P.η D₀ := by
  have hE : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  have h2 : 2 ∈ (2 * N₀).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 N₀, mul_ne_zero two_ne_zero h₀.1.ne'⟩
  exact evenPhaseData_of_prints hWN hW hR hTw (bcdtThmA_of_modularNewform hM) hH L hσ
    (2 * N₀).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) h2
    (hcond_primeFactors hM hE h₀) hD₀ hsq₀ hD₀S hL₀

/-- A functional equation of `L(E_ℓ, s)` exists (PROVED, `exists_rootNumber`), so
`evenPhaseData_Ecurve` applies with its level. -/
theorem exists_rootNumberAt_Ecurve (hM : ModularNewform) (hH : HasseConvergence) {ℓ : ℕ}
    (hℓ : 0 < ℓ) : ∃ (N₀ : ℕ) (w₀ : ℤ), RootNumberAt (Ecurve ℓ) N₀ w₀ := by
  have hE : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  obtain ⟨w, hw⟩ := exists_rootNumber hM hH hE
  obtain ⟨N, hN⟩ := rootNumber_iff_exists_rootNumberAt.mp hw
  exact ⟨N, w, hN⟩

end ZInQ.Manuscript.RC.AppE
