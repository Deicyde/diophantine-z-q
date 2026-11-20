import ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiPrint

/-!
# Corrected Kodai Theorem 0.8 application

Kato 1999, pp. 314-319, read (AI reading of the published pages).
This remains a draft over the tree's abstract cohomology, with the arithmetic
object identifications separate from the statement.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PrintsArith

/-- The full complex (C_S) uses the open with `NK` inverted. Its local
target is the sum, over **every** prime `q ∣ NK`, of
`lim_n H²(ℚ_q ⊗ ℚ(ζ_{2^n}), T)` (divisor parameter 1).
The finite product below is the finite direct sum. The restriction map
`iw.loc` represents the restrictions at all those primes. -/
structure KodaiFullOpen (NK : ℕ) where
  iw : IwasawaData KatoLambda2
  localH2 : {q // q ∈ NK.primeFactors} → Type
  [localAdd : ∀ q, AddCommGroup (localH2 q)]
  [localModule : ∀ q, Module KatoLambda2 (localH2 q)]
  allLocal : iw.H2loc ≃ₗ[KatoLambda2] (∀ q, localH2 q)

attribute [instance] KodaiFullOpen.localAdd KodaiFullOpen.localModule

/-- Section 0.9: kernel of restriction to the complete finite local sum,
including the odd primes. -/
abbrev KodaiFullOpen.H2zero {NK : ℕ} (full : KodaiFullOpen NK) :=
  LinearMap.ker (full.allLocal.toLinearMap.comp full.iw.loc)

/-- The retained Kato 2004 `j_*` complex (C_j). Its `iw.H2loc` is
the local cohomology at 2, and `iw.loc` is restriction at 2. This names
the second interpretation of the abstract modules. -/
structure KodaiJStar where
  iw : IwasawaData KatoLambda2

abbrev KodaiJStar.H2zero (retained : KodaiJStar) := retained.iw.H2zero

/-- The one-prime step (0.1.1). For a new prime, `P q = det(1 − φ_q t)`
for arithmetic Frobenius, evaluated at `q⁻¹ σ_q⁻¹`. -/
def KodaiPrimeNorm (es : EulerSystemData ℤ_[2]) (NK Np : ℕ)
    (P : ℕ → Polynomial ℤ_[2]) : Prop :=
  ∀ m q, q.Prime → KodaiIndex NK Np m → KodaiIndex NK Np (m * q) →
    es.cor m (m * q) (dvd_mul_right m q) (es.z (m * q)) =
      if q ∣ m then es.z m else eulerFactor (P q) (invNat ℤ_[2] q) (frobUnit m q) • es.z m

/-- Section 0.6(iii) in the rational-polynomial application. The complex
roots of `det(1 − φ_q t)` are the inverse Frobenius eigenvalues; their
squared absolute value is `q ^ w`. A common rational polynomial connects
the complex and dyadic realizations. Identifying `P` with the Frobenius
polynomial of the supplied representation is part of the object comparison. -/
def KodaiPurity (w : ℤ) (NK : ℕ) (P : ℕ → Polynomial ℤ_[2]) : Prop :=
  ∀ q, q.Prime → ¬ q ∣ NK → ∃ Q : Polynomial ℚ,
    Q.map (algebraMap ℚ ℚ_[2]) = (P q).map (algebraMap ℤ_[2] ℚ_[2]) ∧
    ∀ z : ℂ, (Q.map (algebraMap ℚ ℂ)).IsRoot z → ‖z‖ ^ 2 = (q : ℝ) ^ w

/-- The two primewise outputs needed from the print. These concern the
localization of the full H² and the length of its all-prime local kernel
respectively. There is no length claim for the entire full-open H². -/
def Kodai08AwayTwo {NK : ℕ} (full : KodaiFullOpen NK) : Prop :=
  ∀ (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime], 𝔭.height = 1 → (2 : KatoLambda2) ∉ 𝔭 →
    Module.IsTorsion (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl full.iw.H2) ∧
    Module.length (Localization.AtPrime 𝔭)
      (LocalizedModule 𝔭.primeCompl full.H2zero) ≤ classIndex full.iw 𝔭

/-- Draft specialization of Kato 1999, Theorem 0.8, over the abstract
cohomology, with the purity weight of Example 0.6.2. All the cohomology,
lattice, polynomials and Galois action refer to the same representation.
Only the results at primes away from two are taken here. -/
def KatoKodai99Thm08Print {V : Type} [AddCommGroup V] [Module ℚ_[2] V]
    (ρ : Representation ℚ_[2] GalQ V) (ι : GalQ)
    (es : EulerSystemData ℤ_[2]) (NK Np : ℕ) (P : ℕ → Polynomial ℤ_[2])
    (full : KodaiFullOpen NK) (t : KodaiTower es NK full.iw) : Prop :=
  0 < NK → 2 ∣ NK → Nat.Coprime NK Np →
  KodaiPrimeNorm es NK Np P →
  Module.finrank ℚ_[2] (LinearMap.ker (ρ ι + 1)) = 1 →
  KodaiAbsIrred ρ → KodaiUnipotent ρ → KodaiPurity (-1) NK P →
  t.IsClass07 → GenericNonzero full.iw → Kodai08AwayTwo full

end ZInQ.Manuscript.RC.KatoP2.Checked
