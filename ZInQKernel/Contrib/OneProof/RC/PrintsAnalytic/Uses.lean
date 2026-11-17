import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Parity
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.BFH
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Desjardins
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Waldspurger
import ZInQKernel.Contrib.CloudB3RC53.Assembly

/-!
# Lane RC8: the manuscript's uses of the analytic prints, derived from the leaves

Each theorem below is the exact form in which the manuscript uses one of the analytic prints,
PROVED in Lean from the leaf (and, where named, from the shared blueprint's proved nodes).

* tex L1792–1796 (with L5736–5741): "root number `-1`", i.e. **odd analytic order** —
  `analyticOrder_odd_of_selmerCorankOne` (from the blueprint's `rootNumberNode_proof`, i.e.
  Dokchitser–Dokchitser Theorem 1.8, and the parity lemma `rootNumber_odd_of_neg_one`).
* tex L1985–1991 and App G L10016–10027: Hoffstein–Luo for the twists `E_ℓ^{(q₀)} = E_{q₀ℓ}` of the
  family — `hoffsteinLuo_family`; BFH for them — `bfh_family`.
* tex L1994–2001: one root number per signed unit filter for `E_ℓ` — `rootNumber_family_filter`.
* App E L8017–8023, (E.10): the coefficient-square identity from Waldspurger's Corollary 2 —
  `coeff_sq_eq_of_waldspurgerCor2`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

/-! ### tex L1792–1796: root number `-1`, i.e. odd order -/

/-- **Root number `-1` gives odd analytic order** (PROVED; tex L1792–1796 with L5736–5741). From
the shared printed leaves (`Prints`, in particular Dokchitser–Dokchitser Theorem 1.8 through the
blueprint's `rootNumberNode_proof`): for `ℓ` in the domain of Theorem 5.3 with
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1`, every entire continuation of `L(E_ℓ, s)` vanishes at `s = 1` to
odd order. So (RC) amounts to excluding `ord ≥ 3`. -/
theorem analyticOrder_odd_of_selmerCorankOne (P : Prints) {ℓ : ℕ} (hℓ : Adm ℓ)
    (hSel : SelmerCorankOne (Ecurve ℓ)) {F : ℂ → ℂ} (hF : IsLContinuation (Ecurve ℓ) F)
    {m : ℕ} (hm : analyticOrderAt F 1 = m) : Odd m :=
  rootNumber_odd_of_neg_one (rootNumberNode_proof P ℓ hℓ hSel) hF hm

/-! ### tex L1985–1992: Hoffstein–Luo and BFH for the twists of `E_ℓ` -/

/-- **Hoffstein–Luo for the twist `E_ℓ^{(q₀)} = E_{q₀ℓ}`** (PROVED from `HoffsteinLuoCurve`;
tex L1985–1991, App G L10016–10027): for `q₀ℓ ≠ 0` and any finite set `S` of primes there are
infinitely many odd fundamental discriminants `d`, with `ω(d) ≤ 4`, split at every prime of `S`,
such that `L(E_{dq₀ℓ}, 1) ≠ 0`. -/
theorem hoffsteinLuo_family (hHL : HoffsteinLuoCurve) {ℓ q₀ : ℚ} (h : q₀ * ℓ ≠ 0)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    {d : ℤ | IsFundamentalDiscriminant d ∧ Odd d ∧ omega d ≤ 4 ∧
      (∀ p ∈ S, kronecker d p = 1) ∧ AnalyticRank (curve ((d : ℚ) * (q₀ * ℓ))) 0}.Infinite := by
  have := hHL (curve (q₀ * ℓ)) (PoleRC.curve_isElliptic h) S hS
  simpa only [qtwist_curve] using this

/-- **BFH for the twist `E_ℓ^{(q₀)} = E_{q₀ℓ}`** (PROVED from `BFHCurve`; tex L1985–1992): if
`L(E_{q₀ℓ}, s)` has the functional equation of level `N` and sign `w`, and `S` contains the primes of
`N`, then (i) some fundamental `D` with `wD < 0`, split on `S`, has `ord_{s=1} L(E_{Dq₀ℓ}, s) = 1` —
in the odd case (`w = -1`) this `D` is positive, as tex L1988 requires; (ii) some fundamental `D`
with `wD > 0`, split on `S`, has `L(E_{Dq₀ℓ}, 1) ≠ 0`. -/
theorem bfh_family (hB : BFHCurve) {ℓ q₀ : ℚ} (h : q₀ * ℓ ≠ 0) {N : ℕ} {w : ℤ}
    (hw : RootNumberAt (curve (q₀ * ℓ)) N w) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hN : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) :
    (∃ D : ℤ, IsFundamentalDiscriminant D ∧ w * D < 0 ∧ (∀ p ∈ S, kronecker D p = 1) ∧
        AnalyticRank (curve ((D : ℚ) * (q₀ * ℓ))) 1) ∧
      (∃ D : ℤ, IsFundamentalDiscriminant D ∧ 0 < w * D ∧ (∀ p ∈ S, kronecker D p = 1) ∧
        AnalyticRank (curve ((D : ℚ) * (q₀ * ℓ))) 0) := by
  have := hB (curve (q₀ * ℓ)) (PoleRC.curve_isElliptic h) N w hw S hS hN
  simpa only [qtwist_curve] using this

/-! ### tex L1994–2001: the root number of a signed unit filter, for `E_ℓ` -/

/-- **One root number per signed unit filter for `E_ℓ`** (PROVED from
`DesjardinsRootNumberFilter`; tex L1994–2001). Let `S ∋ 2, 3` contain the primes of `ℓ`. For
squarefree `D, D'` in one signed unit filter at `S`, the twists `E_{Dℓ}` and `E_{D'ℓ}` have the same
root number. -/
theorem rootNumber_family_filter (hDes : DesjardinsRootNumberFilter) {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hℓS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ℓ → p ∈ S) {D D' : ℤ} (hD : Squarefree D)
    (hD' : Squarefree D') (h : SameSignedUnitClasses S D D') {w w' : ℤ}
    (hw : RootNumber (curve ((D : ℚ) * ℓ)) w) (hw' : RootNumber (curve ((D' : ℚ) * ℓ)) w') :
    w = w' := by
  have hE : ((curveZ ℓ).map (Int.castRingHom ℚ)).IsElliptic := by
    rw [curveZ_map]; exact PoleRC.curve_isElliptic (by exact_mod_cast hℓ)
  have hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (curveZ ℓ).Δ → p ∈ S := by
    intro p hp hpd
    rw [curveZ_Δ] at hpd
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpz.dvd_or_dvd hpd with h1 | h1
    · -- `p ∣ 2304 = 2⁸ · 3²`
      have h2304 : (2304 : ℤ) = 2 ^ 8 * 3 ^ 2 := by norm_num
      rw [h2304] at h1
      rcases hpz.dvd_or_dvd h1 with h4 | h4
      · have := Int.natCast_dvd_natCast.mp (hpz.dvd_of_dvd_pow h4)
        rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this]; exact h2
      · have := Int.natCast_dvd_natCast.mp (hpz.dvd_of_dvd_pow h4)
        rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this]; exact h3
    · exact hℓS p hp (hpz.dvd_of_dvd_pow h1)
  refine rootNumber_eq_of_sameSignedUnitClasses hDes hE hS h2 h3 hbad hD hD' h ?_ ?_
  · rw [curveZ_map, qtwist_curve]; exact hw
  · rw [curveZ_map, qtwist_curve]; exact hw'

/-! ### App E (E.10): the coefficient-square identity -/

/-- **(E.10)** (PROVED from `WaldspurgerCor2`; App E L8017–8023): if `L(E^{(σD₀)}, 1) ≠ 0`, then
`a_g(D)² = ψ(D/D₀) · (√D L(E^{(σD)}, 1)) / (√D₀ L(E^{(σD₀)}, 1)) · a_g(D₀)²`. -/
theorem coeff_sq_eq_of_waldspurgerCor2 (hW : WaldspurgerCor2) {E : WeierstrassCurve ℚ}
    (hE : E.IsElliptic) {N : ℕ} (h4 : 4 ∣ N) {ψ η : DirichletCharacter ℂ N} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {g : UpperHalfPlane → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) {D₀ D : ℕ}
    (hD₀ : 0 < D₀) (hD : 0 < D) (hsD₀ : Squarefree D₀) (hsD : Squarefree D)
    (hcD₀ : D₀.Coprime N) (hcD : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀)
    {F₀ F : ℂ → ℂ} (hF₀ : IsLContinuation (qtwist E ((σ * D₀ : ℤ) : ℚ)) F₀)
    (hF : IsLContinuation (qtwist E ((σ * D : ℤ) : ℚ)) F) (hL₀ : F₀ 1 ≠ 0) :
    hiwCoeff g D ^ 2 =
      ψ D * (ψ D₀)⁻¹ * ((Real.sqrt D : ℂ) * F 1) / ((Real.sqrt D₀ : ℂ) * F₀ 1) *
        hiwCoeff g D₀ ^ 2 := by
  have key := hW E hE N h4 ψ η σ hσ hη g hg D₀ D hD₀ hD hsD₀ hsD hcD₀ hcD hcl F₀ F hF₀ hF
  have hs₀ : (Real.sqrt D₀ : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt D₀ := Real.sqrt_pos.mpr (by exact_mod_cast hD₀)
    exact_mod_cast this.ne'
  field_simp
  linear_combination -key

end ZInQ.Manuscript.RC.PrintsAnalytic
