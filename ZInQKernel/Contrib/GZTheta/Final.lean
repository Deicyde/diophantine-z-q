import ZInQKernel.Contrib.GZTheta.EtaTheta

/-!
# gz-theta: the leaf `HeckeThetaNewform` from newness alone

`CMForm32` is proved (`EtaTheta.lean`: `η(4τ)²η(8τ)² ∈ S₂(Γ₀(32))` has `q`-expansion
`∑ heckeCoeff 1 n qⁿ`). So the leaf `ZInQ.GZDecomp.HeckeThetaNewform` follows from the newness
of the theta series of `ψ_d` at level `32 d²` (`NewCM`), or from the bad-prime coefficients of
its newform (`BadCoeffCM`).
-/

namespace ZInQ.GZTheta

/-- **The leaf from newness.** -/
theorem heckeThetaNewform_of_newCM (hnew : NewCM) : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_cmForm32_newCM cmForm32 hnew

/-- **The leaf from the bad-prime coefficients.** -/
theorem heckeThetaNewform_of_badCoeffCM (hbad : BadCoeffCM) : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_cmForm32_badCoeffCM cmForm32 hbad

/-- **The theta series of `ψ_d` is a Hecke eigenform of level `32 d²`**, unconditionally: for
squarefree `d ≡ 1 (mod 4)` there is a cusp form on `Γ₁(32 d²)` with trivial nebentypus,
eigen for every Hecke operator `T_n`, with `q`-expansion `∑ heckeCoeff d n qⁿ`. -/
theorem exists_eigenform_heckeCoeff (d : ℕ) [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    ∃ E : HeckeRing.GL2.Eigenform (32 * d ^ 2) 2, E.χ = 1 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 E.toCuspForm).coeff n =
        ZInQ.Contrib.HeckeFE.heckeCoeff d n := by
  obtain ⟨F, hF⟩ := cmForm32
  obtain ⟨E, hE, hEχ⟩ := exists_eigenform_cmForm hF d hd4 hsq
  exact ⟨E, hEχ, fun n => by rw [hE, qExpansion_cmForm_coeff hF d n]⟩

end ZInQ.GZTheta
