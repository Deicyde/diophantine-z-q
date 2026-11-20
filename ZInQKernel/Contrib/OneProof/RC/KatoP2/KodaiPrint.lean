import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Kato

/-!
# The 1999 dyadic Euler system input (draft)

Kato, *Euler systems, Iwasawa theory, and Selmer groups*, Kodai Math. J. 22
(1999), §§0.1, 0.4–0.7 and Theorem 0.8, pp. 314–318 (UNVERIFIED).
This is an application-shaped transcription over abstract cohomology, pending
the page checklist in `docs/research/rc-kato-p2-reroute.md`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open PrintsArith

/-- The §0.1 domain. `NK` is the base level; `Np` excludes smoother primes. -/
def KodaiIndex (NK Np m : ℕ) : Prop := 0 < m ∧ NK ∣ m ∧ Nat.Coprime m Np

/-- The dot action of (0.1.1), in arithmetic Frobenius conventions. -/
def KodaiNorm (es : EulerSystemData ℤ_[2]) (NK Np : ℕ)
    (P : ℕ → Polynomial ℤ_[2]) : Prop :=
  ∀ m m', KodaiIndex NK Np m → KodaiIndex NK Np m' → ∀ h : m ∣ m',
    es.cor m m' h (es.z m') =
      (∏ q ∈ m'.primeFactors \ m.primeFactors,
        eulerFactor (P q) (invNat ℤ_[2] q) (frobUnit m q)) • es.z m

/-- Membership in the cyclotomic kernel used in the rational irreducibility
condition. The abelian kernel below is a different subgroup. -/
def FixesDyadicRoots (g : GalQ) : Prop :=
  ∀ (n : ℕ) (z : Qbar), z ^ (2 ^ n) = 1 → g z = z

/-- Fix the maximal abelian extension, expressed by restrictions to all finite
abelian Galois subextensions. -/
def FixesAbelian (g : GalQ) : Prop :=
  ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F],
    (∀ u v : F ≃ₐ[ℚ] F, u * v = v * u) → ∀ x : F, g (x : Qbar) = x

/-- Rational fixed space of the element in §0.6(ii). This is the away-two
condition, with no assertion about an integral free cokernel. -/
def KodaiUnipotent {V : Type} [AddCommGroup V] [Module ℚ_[2] V]
    (ρ : Representation ℚ_[2] GalQ V) : Prop :=
  ∃ g : GalQ, FixesAbelian g ∧
    Module.finrank ℚ_[2] (LinearMap.ker (ρ g - 1)) = 1

open scoped TensorProduct in
/-- Absolute irreducibility of the rational representation over the dyadic
cyclotomic tower (on every extension of the coefficient field). -/
def KodaiAbsIrred {V : Type} [AddCommGroup V] [Module ℚ_[2] V]
    (ρ : Representation ℚ_[2] GalQ V) : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ_[2] K]
    (W : Submodule K (K ⊗[ℚ_[2]] V)),
    (∀ g : GalQ, FixesDyadicRoots g → ∀ v ∈ W, (ρ g).baseChange K v ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- The tower maps for §0.7 at divisor parameter 1. The target of each
projection uses the full open with the primes of `NK` inverted, even when the
index itself is a pure power of two. The additive maps are abstract. -/
structure KodaiTower (es : EulerSystemData ℤ_[2]) (NK : ℕ)
    (full : IwasawaData KatoLambda2) where
  proj : ∀ n : ℕ, full.H1 →+ es.H (2 ^ n)
  joint : ∀ x y : full.H1, (∀ n : ℕ, 1 ≤ n → proj n x = proj n y) → x = y
  corestrict : ∀ n : ℕ, es.H (NK * 2 ^ n) →+ es.H (2 ^ n)
  corestrict_eq : ∀ n, corestrict n = es.cor (2 ^ n) (NK * 2 ^ n) (dvd_mul_left _ _)

/-- The class `ξ(1)` of §0.7 is formed with corestriction, at every positive
dyadic exponent, of the supplied classes. -/
def KodaiTower.IsClass07 {es : EulerSystemData ℤ_[2]} {NK : ℕ}
    {full : IwasawaData KatoLambda2} (t : KodaiTower es NK full) : Prop :=
  ∀ n : ℕ, 1 ≤ n → t.proj n full.zIw = t.corestrict n (es.z (NK * 2 ^ n))

/-- One generic sign component is nonzero at every minimal prime. This is
stated for the class of §0.7, not the untwisted system. -/
def GenericNonzero (full : IwasawaData KatoLambda2) : Prop :=
  ∀ (𝔮 : Ideal KatoLambda2) [𝔮.IsPrime], 𝔮.height = 0 →
    LocalizedModule.mk full.zIw (1 : 𝔮.primeCompl) ≠ 0

/-- The length of the quotient by the ideal of evaluations of the actual class. -/
abbrev classIndex (D : IwasawaData KatoLambda2) (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime] :=
  Module.length (Localization.AtPrime 𝔭)
    (Localization.AtPrime 𝔭 ⧸ D.J.map (algebraMap KatoLambda2 (Localization.AtPrime 𝔭)))

/-- Away-two conclusion used in the draft: full-open global torsion and the
localized length bound for its dyadic localization kernel. Check the precise
printed controlled module and torsion statement. If the print bounds all
full-open H², the kernel version is a weakening. -/
def Kodai08AwayTwo (full : IwasawaData KatoLambda2) : Prop :=
  Module.IsTorsion KatoLambda2 full.H2 ∧
    ∀ (𝔭 : Ideal KatoLambda2) [𝔭.IsPrime], 𝔭.height = 1 → (2 : KatoLambda2) ∉ 𝔭 →
      Module.length (Localization.AtPrime 𝔭)
        (LocalizedModule 𝔭.primeCompl full.H2zero) ≤ classIndex full 𝔭

/-- **UNVERIFIED draft** of the away-two specialization of Theorem 0.8 on the
tree's abstract modules. The coefficient lattice, its rationalization,
Frobenius polynomials, and all cohomology objects must refer to the same
representation; the object comparison is outside this transcription.

The §0.4–0.6 rational sign condition is expressed by the chosen complex
conjugation `ι`; the source checklist includes the precise sign, nonvanishing,
purity and ramification conditions and the distinction between the away-two
and integral clauses. The latter clause is not asserted here. -/
def KatoKodai99Thm08Print {V : Type} [AddCommGroup V] [Module ℚ_[2] V]
    (ρ : Representation ℚ_[2] GalQ V) (ι : GalQ)
    (es : EulerSystemData ℤ_[2]) (NK Np : ℕ) (P : ℕ → Polynomial ℤ_[2])
    (full : IwasawaData KatoLambda2) (t : KodaiTower es NK full) : Prop :=
  0 < NK → 2 ∣ NK → Nat.Coprime NK Np →
  KodaiNorm es NK Np P →
  Module.finrank ℚ_[2] (LinearMap.ker (ρ ι + 1)) = 1 →
  KodaiAbsIrred ρ → KodaiUnipotent ρ →
  t.IsClass07 → GenericNonzero full → Kodai08AwayTwo full

end ZInQ.Manuscript.RC.KatoP2
