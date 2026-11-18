import Mathlib

/-!
# App F: the printed-form leaf for the definite quaternion algebra (tex 8462–8463)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-theta-form`: "By [Voight, Main Theorem
14.6.1], there is a quaternion algebra `B/ℚ` ramified exactly at `ℓ₀` and infinity."

The printed theorem (Voight, *Quaternion algebras*, Main Theorem 14.6.1 — locator UNVERIFIED, no
network) says that for a global field, a finite set of noncomplex places of even cardinality is
the ramification set of a quaternion algebra, unique up to isomorphism. Elliot uses the instance
`Σ = {ℓ₀, ∞}` over `ℚ`, and this leaf states exactly that instance. Ramification of
`B = (a, b)_ℚ` at a place `v` is expressed as anisotropy over `ℚ_v` of the reduced norm form
`x² − a y² − b z² + ab t²` (`B_v` is a division algebra iff its reduced norm is anisotropic; this is
the definition of ramification used by Voight, Ch. 5 and 12 — UNVERIFIED locators). No Hilbert symbol
is in Mathlib, so we use the norm form directly. This leaf is a PRINT and is not proved here.
-/

namespace ZInQ.Manuscript.RC.AppF

/-- The reduced norm form `x² − a y² − b z² + ab t²` of `(a, b)_K` is anisotropic. -/
def NormFormAnisotropic (K : Type*) [Field K] (a b : K) : Prop :=
  ∀ x y z t : K, x ^ 2 - a * y ^ 2 - b * z ^ 2 + a * b * t ^ 2 = 0 →
    x = 0 ∧ y = 0 ∧ z = 0 ∧ t = 0

/-- `B = (a, b)_ℚ` is ramified exactly at `ℓ₀` and `∞`. -/
def RamifiedExactlyAtEll0Infty (ℓ₀ : ℕ) (a b : ℚ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ NormFormAnisotropic ℝ (a : ℝ) (b : ℝ) ∧
    ∀ (p : ℕ) [Fact p.Prime], (NormFormAnisotropic ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) ↔ p = ℓ₀)

/-- **PRINT (Voight, *Quaternion algebras*, Main Theorem 14.6.1, at `Σ = {ℓ₀, ∞}`; locator
UNVERIFIED), as Elliot uses it at tex 8462–8463.** For every prime `ℓ₀` there is a quaternion
algebra over `ℚ` ramified exactly at `ℓ₀` and `∞`. -/
def VoightMainThm1461 : Prop :=
  ∀ ℓ₀ : ℕ, ℓ₀.Prime → ∃ a b : ℚ, RamifiedExactlyAtEll0Infty ℓ₀ a b

end ZInQ.Manuscript.RC.AppF
