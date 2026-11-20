import ZInQKernel.Contrib.OneProof.RC.CMScope.Field

open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMScope

/-- A form determines its conductor-one orientation: divide its middle
coefficient by the conductor modulo `4N` (on the spot, c). -/
private theorem orientation_of_form {N c : ℕ} {D A B C : ℤ}
    (hc : c.Coprime (2 * N)) (hf : IsHeegnerForm N (D * (c : ℤ) ^ 2) A B C) :
    ∃ β : ℤ, Int.ModEq (4 * (N : ℤ)) (β ^ 2) D ∧
      Int.ModEq (2 * (N : ℤ)) B ((c : ℤ) * β) := by
  have hc2 := hc.coprime_dvd_right (dvd_mul_right 2 N)
  have hcN := hc.coprime_dvd_right (dvd_mul_left N 2)
  have hc4 : c.Coprime (4 * N) := by
    rw [show 4 = 2 ^ 2 by decide]
    exact (hc2.pow_right 2).mul_right hcN
  obtain ⟨u, hu⟩ := Int.mod_coprime hc4
  push_cast at hu
  have hm : Int.ModEq (4 * (N : ℤ)) (B ^ 2) (D * (c : ℤ) ^ 2) := by
    obtain ⟨a, ha⟩ := hf.2.1
    apply Int.modEq_of_dvd
    refine ⟨-(a * C), ?_⟩
    rw [← hf.2.2.1, ha]
    ring
  refine ⟨u * B, ?_, ?_⟩
  · calc
      _ ≡ u ^ 2 * B ^ 2 [ZMOD 4 * (N : ℤ)] := by rw [mul_pow]
      _ ≡ u ^ 2 * (D * (c : ℤ) ^ 2) [ZMOD 4 * (N : ℤ)] := hm.mul_left _
      _ ≡ ((c : ℤ) * u) ^ 2 * D [ZMOD 4 * (N : ℤ)] := by
        rw [show u ^ 2 * (D * (c : ℤ) ^ 2) = ((c : ℤ) * u) ^ 2 * D by ring]
      _ ≡ D [ZMOD 4 * (N : ℤ)] := by simpa using (hu.pow 2).mul_right D
  · have hb : Int.ModEq (4 * (N : ℤ)) ((c : ℤ) * (u * B)) B := by
      simpa [mul_assoc] using hu.mul_right B
    exact hb.symm.of_dvd ⟨2, by ring⟩

/-- Specialize scoped descent at a supplied form, choosing the orientation
that its middle coefficient reads. For a family whose orientation is
already fixed, use `CMFieldOfDefinitionScoped` directly. -/
theorem CMFieldOfDefinitionScoped.atForm {N : ℕ} [NeZero N] {X : X0Model N}
    (hCM : CMFieldOfDefinitionScoped X)
    {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (hs : ∀ p : ℕ, p.Prime → p ∣ 2 * N → SplitsIn K p)
    (h4 : discr K ≠ -4) (h3 : discr K ≠ -3)
    {c : ℕ} [NeZero c] (hcop : Nat.Coprime c (2 * N * (discr K).natAbs))
    {A B C : ℤ} (hO : (conductorOrder K c).discr = discr K * (c : ℤ) ^ 2)
    (hd : discr K * (c : ℤ) ^ 2 < 0) (hn : IsCoprime (discr K * (c : ℤ) ^ 2) (N : ℤ))
    (hf : IsHeegnerForm N (discr K * (c : ℤ) ^ 2) A B C) :
    ∃ (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
      (x : FieldPoint X.overQ (ringClassField (conductorOrder K c))),
      x.map ι = X.complexPoint (cmPoint A B (discr K * (c : ℤ) ^ 2)) := by
  obtain ⟨β, hβ, hB⟩ := orientation_of_form
    (hcop.coprime_dvd_right (dvd_mul_right (2 * N) (discr K).natAbs)) hf
  exact hCM K hK hc hs h4 h3 β hβ c hcop _ A B C hO hd hn hf hB

end ZInQ.Manuscript.RC.CMScope
