import ZInQKernel.Contrib.OneProof.SerreGAGA

open scoped Topology
open Filter Set CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

noncomputable section

namespace SerreGAGA

open UnifPrinted UnifTopology SGA1Printed SGA1Etale

variable {X : Over (Spec (CommRingCat.of ℂ))}

theorem xevalAt_algebraMap_basicOpen {U : X.left.Opens} (s : Γ(X.left, U)) (a : Γ(X.left, U))
    {Q : CPt X} (hQ : XPtIn X Q (X.left.basicOpen s)) :
    XevalAt X (X.left.basicOpen s) (algebraMap Γ(X.left, U) Γ(X.left, X.left.basicOpen s) a) Q =
      XevalAt X U a Q :=
  xevalAt_res (X.left.basicOpen_le s) a hQ

theorem xevalAt_eval₂ {U : X.left.Opens} {k : ℕ} (f : Fin k → Γ(X.left, U))
    (p : MvPolynomial (Fin k) ℂ) {Q : CPt X} (hQ : XPtIn X Q U) :
    XevalAt X U (MvPolynomial.eval₂Hom (algC X U) f p) Q =
      MvPolynomial.eval (fun i => XevalAt X U (f i) Q) p := by
  rw [xevalAt_eq_evP hQ, MvPolynomial.coe_eval₂Hom, evP_eval₂]
  simp only [xevalAt_eq_evP hQ]

theorem analyticAt_mvEval {k : ℕ} (p : MvPolynomial (Fin k) ℂ) (z : Fin k → ℂ) :
    AnalyticAt ℂ (fun v => MvPolynomial.eval v p) z := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ)
    (f := fun v : Fin k → ℂ => v) (z := z)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).analyticAt _) p
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

/-- Chart independence: a holomorphic function is holomorphic in the coordinates of every affine
chart. -/
theorem anFunAt_iff_forall_chart [LocallyOfFiniteType X.hom] (F : CPt X → ℂ) (P : CPt X) :
    AnFunAt X F P ↔ ∀ c : AffineChart X, XPtIn X P c.U → ∃ H : (Fin c.k → ℂ) → ℂ,
      AnalyticAt ℂ H (fun i => XevalAt X c.U (c.f i) P) ∧
      ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X c.U (c.f i) Q) := by
  letI := analyticTopology X
  constructor
  · rintro ⟨U, k, g, H, hPU, hH, hev⟩ c hPc
    obtain ⟨s, hsle, hPs⟩ := c.isAffine.exists_basicOpen_le (V := U)
      ⟨P.left.base default, (xPtIn_iff _ _).mp hPU⟩ ((xPtIn_iff _ _).mp hPc)
    set D := X.left.basicOpen s with hD
    have hPD : XPtIn X P D := (xPtIn_iff _ _).mpr hPs
    haveI := c.isAffine.isLocalization_basicOpen s
    have hloc : ∀ j, ∃ (a : Γ(X.left, c.U)) (m : ℕ),
        res hsle (g j) * algebraMap Γ(X.left, c.U) Γ(X.left, D) (s ^ m) =
          algebraMap Γ(X.left, c.U) Γ(X.left, D) a := by
      intro j
      obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) (res hsle (g j))
      exact ⟨a, m, ha⟩
    choose a m ha using hloc
    choose p hp using fun j => c.generates (a j)
    obtain ⟨q, hq⟩ := c.generates s
    have hDc : ∀ Q, XPtIn X Q D → XPtIn X Q c.U := fun Q hQ => xPtIn_mono (X.left.basicOpen_le s) hQ
    have hsQ : ∀ Q (hQ : XPtIn X Q D),
        MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) q ≠ 0 := by
      intro Q hQ
      rw [← xevalAt_eval₂ c.f q (hDc Q hQ), hq, xevalAt_eq_evP (hDc Q hQ)]
      exact (xPtIn_basicOpen_iff Q (hDc Q hQ) s).mp hQ
    have hval : ∀ Q, XPtIn X Q D → (fun j => XevalAt X U (g j) Q) =
        fun j => MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) (p j) /
          MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) q ^ m j := by
      intro Q hQ; funext j
      rw [eq_div_iff (pow_ne_zero _ (hsQ Q hQ))]
      have h1 := congrArg (fun x => XevalAt X D x Q) (ha j)
      simp only at h1
      rw [xevalAt_eq_evP hQ, map_mul, ← xevalAt_eq_evP hQ, ← xevalAt_eq_evP hQ,
        xevalAt_res hsle (g j) hQ, xevalAt_algebraMap_basicOpen s _ hQ,
        xevalAt_algebraMap_basicOpen s _ hQ, xevalAt_eq_evP (hDc Q hQ), map_pow,
        ← xevalAt_eq_evP (hDc Q hQ), ← xevalAt_eq_evP (hDc Q hQ)] at h1
      rw [h1, ← hp j, ← hq, xevalAt_eval₂ c.f _ (hDc Q hQ), xevalAt_eval₂ c.f _ (hDc Q hQ)]
    refine ⟨fun v => H (fun j => MvPolynomial.eval v (p j) / MvPolynomial.eval v q ^ m j), ?_, ?_⟩
    · refine AnalyticAt.comp (g := H)
        (f := fun v j => MvPolynomial.eval v (p j) / MvPolynomial.eval v q ^ m j) ?_
        (AnalyticAt.pi fun j => ?_)
      · rw [← hval P hPD]; exact hH
      · exact (analyticAt_mvEval (p j) _).div ((analyticAt_mvEval q _).pow _)
          (pow_ne_zero _ (hsQ P hPD))
    · filter_upwards [hev, (isOpen_ptIn_an D).mem_nhds hPD] with Q hQ hQD
      rw [hQ, hval Q hQD]
  · intro h
    obtain ⟨c, hPc⟩ := exists_affineChart P
    obtain ⟨H, hH, hev⟩ := h c hPc
    exact ⟨c.U, c.k, c.f, H, hPc, hH, hev⟩

#print axioms anFunAt_iff_forall_chart

end SerreGAGA
