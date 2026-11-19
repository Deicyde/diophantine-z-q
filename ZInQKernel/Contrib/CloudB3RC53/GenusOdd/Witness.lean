import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Final

/-!
# GenusOdd: the fixed nonzero witness `D_w` (tex L2460–2467)

"Choose one positive squarefree `D_w` in the odd filter containing one, after adjoining the primes
of `h_*` and their compatible unit tests. Section 7.3 supplies `L'(E^{(D_w)},1) ≠ 0`. The explicit
height formula makes `P_{D_w}^gen` nontorsion. Its unwanted `h_*` component has rank zero. One fixed
multiplier `L` kills the bounded-degree torsion and the projection denominator, so
`Q = L P_{D_w}^gen` is a rational nontorsion point on `E^{(D_w)}`."

`FixedWitness` states the first two sentences' conclusions over the genuine objects: the genus point
`P_{D_w}^gen` is nontorsion, and there is a nontorsion `Q ∈ E^{(D_w)}(ℚ)` with
`j(P) ≤ j(Q) ≤ j(P) + 1` (from `2P ≡ ψ(Q)` modulo torsion: Elliot's comparison, the "projection
denominator" `2`). DEPARTURE (form): the manuscript's `Q = L P` with one fixed multiplier `L`
killing the torsion of `E` over fields of degree `≤ 4` (tex L8274–8283, reduction at two good
primes) is not formalized; the consequence used, a nontorsion rational point on `E^{(D_w)}`
comparable with `P_{D_w}^gen`, is. `L'(E^{(D_w)},1) ≠ 0` enters as `ord_{s=1} L(E^{(D_w)}, s) = 1`
(odd sign). PROVED from `Prints` and the reduced GLUE.
-/

noncomputable section

open NumberField TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

theorem twoDivIndex_eq_top_of_torsion {A : Type*} [AddCommGroup A] {M : AddSubgroup A} {x : A}
    (hx : x ∈ M) (ht : IsOfFinAddOrder x) : twoDivIndex M x = ⊤ := by
  refine top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun e _ => ?_)
  exact (le_twoDivIndex_iff hx e).mpr ⟨0, M.zero_mem, by simpa using ht⟩

/-- **The fixed witness** (tex L2460–2467), consequence form (see the module docstring). -/
def FixedWitness : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.a₁ = 0 → E.a₃ = 0 →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2),
    (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
    ∀ (Lat : PeriodPair), IsLatticeOf E Lat → IsNonCMLattice Lat →
    ∀ κ : ℂ, IsParamScale (newformLevel E) f Lat κ →
    ∀ hstar : ℤ, GenusPartner E hstar →
    ∀ Dw : ℤ, Prepared E hstar Dw → AnalyticRank (qtwist E Dw) 1 →
    ∀ datW : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar,
      (letI := datW.field; letI := datW.nf
        letI := Classical.decEq (ringClassField (conductorOrder datW.K 1))
        ¬ IsOfFinAddOrder (heegnerSum E datW.χ datW.y)) ∧
      ∃ Q : (qtwist E Dw).toAffine.Point, ¬ IsOfFinAddOrder Q ∧
        datW.index ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ datW.index + 1

/-- **The fixed witness, PROVED** from `Prints` and the reduced GLUE. -/
theorem fixedWitness_proof (P : Prints) (G : GlueReduced) : FixedWitness := by
  intro E _ h₁ h₃ f hf Lat hLat hNC κ hκ hstar hgp Dw hp hz datW
  have G' := glue34_of_reduced G
  obtain ⟨C, hC0, hC⟩ := cst_formula P E f hf Lat hLat hNC κ hκ
  obtain ⟨h0, hsqh, hsqp, hcop⟩ := hp
  obtain ⟨hs0, hs4, hssq, hs5, hsp, har0⟩ := hgp
  have hN2 : ∀ p : ℕ, p ∣ newformLevel E → p ∣ 2 * newformLevel E :=
    fun p hp => dvd_mul_of_dvd_right hp 2
  have h2h : SquareAt 2 Dw := hsqp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h2s : SquareAt 2 hstar := hsp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h8 : Dw % 8 = 1 := h2h.2.1 rfl
  have s8 : hstar % 8 = 1 := h2s.2.1 rfl
  have hDg4 : 4 < |Dw * hstar| := by rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg hstar]
  have hs0' : (hstar : ℚ) ≠ 0 := by exact_mod_cast hs0.ne
  have htorS : ∀ Q : (qtwist E hstar).toAffine.Point, IsOfFinAddOrder Q := by
    have hE := qtwist_isElliptic E hs0'
    have := (P.kolyvagin (qtwist E hstar) hE (P.bcdt _ hE) 0 (by norm_num) har0).1
    exact torsion_of_rank_zero (by exact_mod_cast this)
  obtain ⟨FD, hFD, hFD1, hFD'⟩ := analyticRank_one hz
  obtain ⟨Fs, hFs, hFs1⟩ := analyticRank_zero_iff.mp har0
  have hsqhN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p Dw :=
    fun p hp hpN => hsqp p hp (hN2 p hpN)
  have hsqsN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p hstar :=
    fun p hp hpN => hsp p hp (hN2 p hpN)
  obtain ⟨Q, hder, hj1, hj2⟩ := by
    letI := datW.field; letI := datW.nf; letI := datW.nz
    exact datum_facts_core G' h₁ h₃ hC datW.K datW.finrank_two datW.totallyComplex datW.disc
      datW.χ datW.quad datW.prim datW.A datW.B datW.C datW.form datW.ι datW.y datW.hy
      (d₂ := Dw) (dR := Dw) (dT := hstar) (by push_cast; ring) hs4 hssq (by simp)
      (Nat.coprime_one_left _) (Int.odd_iff.mpr (by
        rw [Int.mul_emod, show Dw % 2 = 1 by omega, show hstar % 2 = 1 by omega]; norm_num))
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      (fun p hp hpN => (hsqhN p hp hpN).mul (hsqsN p hp hpN) hp) (Nat.coprime_one_left _)
      (coprime_of_squareAt fun p hp hpN => (hsqsN p hp hpN).mul (hsqhN p hp hpN) hp)
      (Or.inr ⟨rfl, rfl⟩) htorS hFs hFD
  have hDw0 : (Dw : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have hED : (qtwist E Dw).IsElliptic := qtwist_isElliptic E hDw0
  have dW : deriv (fun s => Fs s * FD s) 1 = Fs 1 * deriv FD 1 := by
    rw [show (fun s => Fs s * FD s) = Fs * FD from rfl, deriv_mul (hFs.1 1) (hFD.1 1), hFD1]; ring
  rw [dW] at hder
  have hQ0 : Q.canonicalHeight ≠ 0 := by
    intro h0'
    rw [h0', zero_div, Complex.ofReal_zero, mul_zero] at hder
    exact mul_ne_zero hFs1 hFD' hder
  have hQnt : ¬ IsOfFinAddOrder Q := fun ht =>
    hQ0 (WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_of_isOfFinAddOrder ht)
  have hJ : twoDivIndex ⊤ Q ≠ ⊤ :=
    twoDivIndex_ne_top (fun n x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul n x)
      (fun B => Northcott.finite_le (h := WeierstrassCurve.Affine.Point.canonicalHeight) B)
      (lt_of_le_of_ne (WeierstrassCurve.Affine.Point.canonicalHeight_nonneg Q) (Ne.symm hQ0))
  refine ⟨?_, Q, hQnt, hj1, hj2⟩
  let _ := datW.field; let _ := datW.nf
  let _ := Classical.decEq (ringClassField (conductorOrder datW.K 1))
  intro ht
  have hP := heegnerSum_mem_eigenLattice E datW.quad.1 datW.y
  have htop := twoDivIndex_eq_top_of_torsion hP ht
  have hj1' : datW.index ≤ twoDivIndex ⊤ Q := hj1
  have : datW.index = ⊤ := htop
  rw [this, top_le_iff] at hj1'
  exact hJ hj1'

end ZInQ.Contrib.CloudB3RC53.GenusOdd
