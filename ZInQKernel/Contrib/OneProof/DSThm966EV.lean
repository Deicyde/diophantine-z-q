import ZInQKernel.Contrib.OneProof.DSCoeffExt
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Parity

/-! # coeff-fix: Deligne–Serre 1974 Thm 4.1 as printed (trace over the `T_p`-eigenvalue, `ε(-1) = -1`)

Task coeff-fix (2026-11-16), report `docs/research/coeff-fix.md`, scratch `scratch/coeff-fix/`.

The field `ZInQ.Contrib.HodgeSplit.DSThm966` (bundle field `OpenResearchLeaves26.dsThm966`) is proved from
`DSThm966Printed`, Deligne–Serre's Thm 4.1 in its printed form:

* **hypothesis as printed**: a nonzero cusp form of type `(1, ε)` that is an eigenvector of the Hecke operators
  away from the level (Tau Ceti's `HeckeRing.GL2.EigenformAwayFromLevel N 1`, nebentypus `ε` by the diamond
  operators), no normalization `a₁ = 1`, nothing asked at the primes `p ∣ N`;
* **`ε(-1) = -1`** as a hypothesis, as Deligne–Serre assume;
* **trace over the eigenvalue**: `tr ρ(Frob_p) = a_p`, with `a_p` the `T_p`-eigenvalue `F.eigenvalue p`.

`DSThm966PrintedFull` is the same statement for Tau Ceti's full `Eigenform N 1`; it follows from
`DSThm966Printed`, and it is all that `dsThm966` uses.

The glue (proved here): a normalized eigenform in the kernel's coefficient form is a full eigenform
(`DSCoeffExt.isNormalizedEigenformDS_of`), hence an eigenform away from the level; its `T_p`-eigenvalue is its
coefficient `a_p` because `a₁ = 1` (`Eigenform.qExpansion_coeff_eq_eigenvalue`); `ε(-1) = -1` by the parity
lemma (`TauCeti.char_neg_one_of_mem_cuspFormCharSpace`, Parity.lean:113, weight `1`, nonzero form). -/

noncomputable section

namespace DSThm966EV

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.G9.PkgI4 (Qbar GQ CF coeff IsNormalizedEigenform LiesOver IsArithFrob)

/-- `p ∤ N` gives `p ⊥ N` for a prime `p`, the index condition of `EigenformAwayFromLevel.eigenvalue`. -/
theorem coprime_of_not_dvd {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Nat.Coprime (p.toPNat hp.pos).val N :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 hpN

/-- **LEAF (Deligne–Serre 1974 Thm 4.1, printed form).** Deligne–Serre, *Formes modulaires de poids 1*,
Ann. Sci. ÉNS (4) 7 (1974), Thm 4.1 with display (4.1.1), p. 514 (AI-read only: W24, cloud-checks 6912455099). Let `f ≠ 0` be a modular form of type `(1, ε)` on
`Γ₀(N)` (here a cusp form), with `ε(-1) = -1`, that is an eigenvector of the Hecke operators `T_p`, `p ∤ N`,
with eigenvalues `a_p`. There is a representation `ρ : G_ℚ → GL₂(ℂ)` (continuous, finite image), unramified
at every `p ∤ N`, with `tr ρ(Frob_p) = a_p` and `det ρ(Frob_p) = ε(p)` for `p ∤ N`.

Lean form: `f` is Tau Ceti's `EigenformAwayFromLevel N 1` (a nonzero cusp form on `Γ₁(N)` in the
`ε`-eigenspace of the diamond operators, an eigenvector of `T_n` for every `n` prime to `N`, which for
`p ∤ N` is the classical `T_p`), `ε` a Dirichlet character with `F.χ = ε` on units, `a_p = F.eigenvalue p`;
places of `ℚ̄` as valuation subrings, `Frob_𝔭` pkg-I4's arithmetic Frobenius `IsArithFrob`, "unramified"
trivial on every inertia group above `p`. -/
def DSThm966Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (F : EigenformAwayFromLevel N 1),
    F.χ = MulChar.toUnitHom ε → ε (-1) = -1 →
    ∃ ρ : GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace =
              F.eigenvalue (p.toPNat hp.pos) (coprime_of_not_dvd hp hpN) ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N)

/-- **Fallback form (full eigenforms).** `DSThm966Printed` restricted to Tau Ceti's full `Eigenform N 1`
(an eigenvector of every `T_n`, the `U_p`, `p ∣ N`, included). It follows from `DSThm966Printed`
(`printedFull_of_printed`). It is all that `dsThm966` needs. -/
def DSThm966PrintedFull : Prop :=
  ∀ (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (F : Eigenform N 1),
    F.χ = MulChar.toUnitHom ε → ε (-1) = -1 →
    ∃ ρ : GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ N →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace = F.eigenvalue (p.toPNat hp.pos) ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N)

theorem printedFull_of_printed (h : DSThm966Printed) : DSThm966PrintedFull := by
  intro N _ ε F hFχ hε
  obtain ⟨ρ, hc, hfin, hρ⟩ := h N ε F.toEigenformAwayFromLevel hFχ hε
  exact ⟨ρ, hc, hfin, hρ⟩

/-! ## Glue -/

/-- **The parity lemma in weight 1** (Parity.lean:113): a normalized eigenform of weight `1` and nebentypus
`χ` has `χ(-1) = -1`. -/
theorem char_neg_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {g : CF N 1}
    (hg : IsNormalizedEigenform g χ) : χ (-1) = -1 := by
  have hmem := T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1
  have h := TauCeti.char_neg_one_of_mem_cuspFormCharSpace hmem
    (DSCoeffExt.ne_zero_of_coeff_one hg.2.1)
  rw [MulChar.coe_toUnitHom, zpow_one] at h
  simpa using h

/-- A normalized eigenform (kernel coefficient form) as a full eigenform (Diamond–Shurman Def. 5.8.1),
with its `T_p`-eigenvalue equal to its coefficient `a_p` (from `a₁ = 1`). -/
theorem exists_eigenform {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {g : CF N 1}
    (hg : IsNormalizedEigenform g χ) :
    ∃ F : Eigenform N 1, F.χ = MulChar.toUnitHom χ ∧
      ∀ (p : ℕ) (hp : p.Prime), F.eigenvalue (p.toPNat hp.pos) = coeff g p := by
  obtain ⟨F, hFg, hFχ, h1⟩ := DSCoeffExt.isNormalizedEigenformDS_of hg
  refine ⟨F, hFχ, fun p hp => ?_⟩
  subst hFg
  exact (F.qExpansion_coeff_eq_eigenvalue h1 (p.toPNat hp.pos)).symm

/-- `dsThm966` from the full-eigenform form. -/
theorem dsThm966_of_printedFull (h : DSThm966PrintedFull) : ZInQ.Contrib.HodgeSplit.DSThm966 := by
  intro N χ g hN hg
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨F, hFχ, hev⟩ := exists_eigenform hg
  obtain ⟨ρ, hc, hfin, hρ⟩ := h N χ F hFχ (char_neg_one hg)
  refine ⟨ρ, hc, hfin, fun p hp hpN => ⟨(hρ p hp hpN).1, fun v σ hv hσ => ?_⟩⟩
  obtain ⟨htr, hdet⟩ := (hρ p hp hpN).2 v σ hv hσ
  exact ⟨htr.trans (hev p hp), hdet⟩

/-- **`dsThm966` from Deligne–Serre's Thm 4.1 as printed.** -/
theorem dsThm966_of_printed (h : DSThm966Printed) : ZInQ.Contrib.HodgeSplit.DSThm966 :=
  dsThm966_of_printedFull (printedFull_of_printed h)

end DSThm966EV
