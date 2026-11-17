import ZInQKernel.Contrib.CloudB3RC53.Prints
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add

/-!
# Lane RC9 (arithmetic prints of Theorem 5.3): common vocabulary

The arithmetic printed theorems cited in the proof of Theorem 5.3 of the 11/5 manuscript
(`diophantine_zq.tex`, Sections 7–9 and Appendices E–G) are stated in the sibling files
`Serre.lean`, `Kato.lean`, `Heegner.lean` and `Local.lean`. This file fixes the genuine objects
they share.

* `Qbar`, `GalQ`: the algebraic closure `ℚ̄` of `ℚ` and `G_ℚ = Aut(ℚ̄/ℚ)`, with its Krull topology
  (Mathlib).
* `TateMod E ℓ`, `tateRep E ℓ`: the `ℓ`-adic Tate module `T_ℓ E = lim E(ℚ̄)[ℓ^n]` and the `ℓ`-adic
  Galois representation `ρ_ℓ : G_ℚ → End_{ℤ_ℓ}(T_ℓ E)` (vendored Tau Ceti,
  `WeierstrassCurve.tateModuleGaloisRepresentation`; free of rank two over `ℤ_ℓ` by
  `WeierstrassCurve.finrank_tateModule`).
* `HasNoCM E`: `End_{ℚ̄}(E) = ℤ`, every endomorphism of `E` over `ℚ̄` (vendored Tau Ceti
  `TauCeti.Isogeny.Hom`, the morphisms of elliptic curves including the zero map) is
  multiplication by an integer. This is Serre's hypothesis "`E` n'a pas de multiplication complexe
  sur `K̄`" (Serre 1972, Introduction, p. 259: complex multiplication means that the ring of
  `K̄`-endomorphisms has rank two over `ℤ`).
* The shared top layer's vocabulary (`ZInQ.Contrib.CloudB3RC53`, read-only): `AnalyticRank E r`,
  `IsLContinuation`, `qtwist`, `Ecurve`, `Adm`, and its printed leaves `PoleS12.BCDTThmA`,
  `KolyvaginThm1Printed`, `DokchitserThm18`, `CST.CSTThm11Split`, which this lane does not restate.
  `analyticRank_zero_iff` (PROVED): `AnalyticRank E 0` is `L(E, 1) ≠ 0` for an entire
  continuation.
* `twistedCoeffS`, `LSValueVanishes`: the partial twisted `L`-series
  `L_S(E, χ, s) = ∑_{(n, S) = 1} a_n(E) χ(n) n^{-s}` (Kato's `L_S(f, χ, s)` for the newform `f` of
  `E`, Euler factors at the primes of `S` removed) and the vanishing of its continuation at `1`.

Public hygiene: no internal names or paths; lane labels only.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve

/-! ### `ℚ̄`, `G_ℚ` and the `ℓ`-adic representation -/

/-- `ℚ̄`, the algebraic closure of `ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- Equality on `ℚ̄` is decided classically (needed by the point arithmetic of the Tate module
and of `TauCeti.Isogeny.Hom.pointMap`). -/
instance : DecidableEq Qbar := Classical.decEq _

/-- `G_ℚ = Aut(ℚ̄/ℚ)`, with its Krull topology. -/
abbrev GalQ : Type := Qbar ≃ₐ[ℚ] Qbar

/-- The `ℓ`-adic Tate module `T_ℓ E = lim_n E(ℚ̄)[ℓ^n]` of `E/ℚ`. -/
abbrev TateMod (E : WeierstrassCurve ℚ) (ℓ : ℕ) : Type :=
  TauCeti.TateModule ℓ (E⁄Qbar).toAffine.Point

/-- **The `ℓ`-adic Galois representation** `ρ_ℓ : G_ℚ → End_{ℤ_ℓ}(T_ℓ E)` of `E/ℚ`: `σ` acts on
the coordinates of every point of every level `E(ℚ̄)[ℓ^n]` (vendored Tau Ceti
`WeierstrassCurve.tateModuleGaloisRepresentation`). -/
abbrev tateRep (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation ℤ_[ℓ] GalQ (TateMod E ℓ) :=
  E.tateModuleGaloisRepresentation (K := Qbar) ℓ

/-- On the level `E[ℓ^n]` the representation is the coordinatewise Galois action on points. -/
theorem coe_proj_tateRep (E : WeierstrassCurve ℚ) (ℓ : ℕ) [Fact ℓ.Prime] (σ : GalQ)
    (x : TateMod E ℓ) (n : ℕ) :
    (TauCeti.TateModule.proj n (tateRep E ℓ σ x) : (E⁄Qbar).toAffine.Point) =
      WeierstrassCurve.Affine.Point.map σ.toAlgHom
        (TauCeti.TateModule.proj n x : (E⁄Qbar).toAffine.Point) :=
  WeierstrassCurve.coe_proj_tateModuleGaloisRepresentation σ x n

/-! ### Complex multiplication -/

/-- **`E` has no complex multiplication over `ℚ̄`**: `End_{ℚ̄}(E) = ℤ`. Every morphism of elliptic
curves `E_{ℚ̄} → E_{ℚ̄}` sending `O` to `O` (vendored Tau Ceti `TauCeti.Isogeny.Hom`, which contains
the zero map and the isogenies) is `[n]` for some `n ∈ ℤ`, i.e. an integer multiple of the
identity in the additive group of morphisms. -/
def HasNoCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∀ f : TauCeti.Isogeny.Hom (E⁄Qbar).toAffine (E⁄Qbar).toAffine,
    ∃ n : ℤ, f = n • TauCeti.Isogeny.Hom.id (E⁄Qbar).toAffine

/-! ### Central `L`-values -/

open ZInQ.Contrib.CloudB3RC53 in
/-- **`ord_{s=1} L(E, s) = 0` is `L(E, 1) ≠ 0`** for an entire continuation (PROVED): the shared
top layer's `AnalyticRank E 0` holds iff some entire continuation of Mathlib's `L`-series does not
vanish at `1`. -/
theorem analyticRank_zero_iff (E : WeierstrassCurve ℚ) :
    AnalyticRank E 0 ↔ ∃ F : ℂ → ℂ, IsLContinuation E F ∧ F 1 ≠ 0 := by
  constructor
  · rintro ⟨F, hF, hEq, h0⟩
    refine ⟨F, ⟨hF, hEq⟩, ?_⟩
    have h0' : analyticOrderAt F 1 = 0 := by exact_mod_cast h0
    rcases analyticOrderAt_eq_zero.mp h0' with h | h
    · exact absurd (hF.analyticAt 1) h
    · exact h
  · rintro ⟨F, ⟨hF, hEq⟩, h1⟩
    refine ⟨F, hF, hEq, ?_⟩
    have : analyticOrderAt F 1 = 0 := analyticOrderAt_eq_zero.mpr (Or.inr h1)
    exact_mod_cast this

/-- The product of a finite set `S` of primes (or of any natural numbers). -/
def primeProd (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- The coefficients of the **partial twisted `L`-series** `L_S(E, χ, s)`:
`n ↦ a_n(E) χ(n)` for `n` prime to every element of `S`, and `0` otherwise. Here `a_n(E)` are the
Dirichlet coefficients of Mathlib's `L`-function of `E` (for modular `E`, the Fourier coefficients
of its newform). Removing the terms not prime to `S` removes the Euler factors at `S`. -/
def twistedCoeffS (E : WeierstrassCurve ℚ) (S : Finset ℕ) {m : ℕ}
    (χ : DirichletCharacter ℂ m) (n : ℕ) : ℂ :=
  if n.Coprime (primeProd S) then (E.LFunction n : ℂ) * χ n else 0

/-- **`L_S(E, χ, 1) = 0`**: some entire function agrees with the partial twisted `L`-series
`∑_{(n,S)=1} a_n(E) χ(n) n^{-s}` on `Re s > 3/2` and vanishes at `s = 1`. -/
def LSValueVanishes (E : WeierstrassCurve ℚ) (S : Finset ℕ) {m : ℕ}
    (χ : DirichletCharacter ℂ m) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    (∀ s : ℂ, 3 / 2 < s.re → F s = LSeries (twistedCoeffS E S χ) s) ∧ F 1 = 0

/-- The function `n ↦ χ(n)` on integers prime to `S` (zero elsewhere). Two Dirichlet characters
whose moduli are supported on `S` are identified in Kato's union
`⋃_{prime(m) ⊆ S} Hom((ℤ/m)^×, ℂ^×)` (via `Hom((ℤ/m)^×,ℂ^×) ⊆ Hom((ℤ/m')^×,ℂ^×)` for `m ∣ m'`)
exactly when these functions agree. -/
def charOnPrimeToS (S : Finset ℕ) {m : ℕ} (χ : DirichletCharacter ℂ m) : ℕ → ℂ :=
  fun n => if n.Coprime (primeProd S) then χ n else 0

end ZInQ.Manuscript.RC.PrintsArith
