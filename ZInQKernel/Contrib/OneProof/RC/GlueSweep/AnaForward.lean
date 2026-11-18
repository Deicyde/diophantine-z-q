import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaNonvanishing
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic
import ZInQKernel.Contrib.CloudB3RC53.Prints

/-!
# Lane RC22 (glue sweep): the forward rank lemma in rank zero, and lane RC13's rough companion

`lem:forward-rank` (tex 1086–1108) in rank zero: if `L(E, 1) ≠ 0` then
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 0`. Lane RC13's `roughCompanion` (tex 2373–2387) takes it as the
abstract hypothesis `hforward : ∀ d, CentralNonzero (qtwist E d) → CorankZero d` (labelled PRINT,
Kolyvagin Theorem 1 / Kato Corollary 14.3), with `CorankZero` a free predicate.

* `forwardRank_zero_of_prints` (PROVED): the rank-zero forward lemma from the shared top layer's
  printed leaves `Prints` (BCDT Theorem A and Kolyvagin Theorem 1 at `r = 0`: rank zero and finite
  `Ш`) and the proved Kummer sequence in rank zero of the shared top layer
  (`CloudB3RC53.KummerCorankZero.kummerCorankZero_proof`). Lane RC9's `forward_rank_zero` proves the
  same from Kato's Corollary 14.3 instead; this route needs no print beyond `Prints`.
* `roughCompanion_genuine` (PROVED): RC13's `roughCompanion` with `CorankZero d` the genuine
  "`d ≠ 0 → corank_{ℤ₂} Sel_{2^∞}(E^{(d)}/ℚ) = 0`" and `hforward` discharged by
  `forwardRank_zero_of_prints`. The guard `d ≠ 0` is needed because the zero twist is singular
  (Kolyvagin's theorem is for elliptic curves); the companion parameters `hk'` are nonzero.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Ana

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Nonvanishing

/-- **`lem:forward-rank` in rank zero** (PROVED from `Prints` and the proved Kummer sequence;
tex 1086–1108): an elliptic curve `E/ℚ` with `ord_{s=1} L(E, s) = 0` has
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 0`. Kolyvagin's Theorem 1 at `r = 0` (with BCDT for modularity) gives
rank zero and finite `Ш(E/ℚ)`; `kummerCorankZero_proof` gives the corank. -/
theorem forwardRank_zero_of_prints (P : ZInQ.Contrib.CloudB3RC53.Prints) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    (hL : AnalyticRank E 0) : Z2Corank (selmerTwoPower E) 0 := by
  obtain ⟨hr, hsha⟩ := P.kolyvagin E hE (P.bcdt E hE) 0 (by norm_num) hL
  exact KummerCorankZero.kummerCorankZero_proof E hE (by simpa using hr) hsha

/-- **The rough companion with the genuine Selmer corank** (tex 2373–2387; PROVED from `Prints`,
RC13's leaves `HoffsteinLuo` and `BFHTwistSign`, and RC13's remaining inputs `hdummy` (ELLIOT,
the dummy realization, lane RC2) and `h33b` (ELLIOT, (3.3b))): RC13's `roughCompanion` with
`CorankZero d := d ≠ 0 → corank_{ℤ₂} Sel_{2^∞}(E^{(d)}/ℚ) = 0` and its hypothesis `hforward`
discharged by `forwardRank_zero_of_prints`. The leaves come from the literal prints by
`hoffsteinLuo_of_prints` and `bfhTwistSign_of_prints`. -/
theorem roughCompanion_genuine (P : ZInQ.Contrib.CloudB3RC53.Prints) (hHL : HoffsteinLuo) (hTS : BFHTwistSign)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ S)
    (Partitionable : ℤ → Prop) (vL s : ℤ → ℤ) (C₁ : ℤ) (A₀ : ℕ)
    (hdummy : ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
      ∃ a : ℤ, 0 < a ∧ Squarefree a ∧ Nonvanishing.omega a = A₀ ∧
        (∀ p ∈ S ∪ X, ¬ (p : ℤ) ∣ a) ∧
        IsCoprime a h ∧ ∀ u : ℤ, a * u < 0 → (a * u) % 8 = 1 → Squarefree (a * u) →
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p ((a * u : ℤ) : ℚ)) →
          CentralNonzero (qtwist E ((h * (a * u) : ℤ) : ℚ)) →
            Partitionable (h * (a * u)))
    (h33b : ∀ d : ℤ, Partitionable d → (d ≠ 0 → Z2Corank (selmerTwoPower (qtwist E d)) 0) →
      vL d ≤ 2 * Nonvanishing.omega d + s d + C₁) :
    ∃ (A : ℕ) (CE : ℤ), ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      RootNumber (qtwist E h) (-1) → ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
        ∃ k' : ℤ, k' < 0 ∧ k' % 8 = 1 ∧ Nonvanishing.IsFundamentalDiscriminant k' ∧
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
          (∀ p ∈ X, ¬ (p : ℤ) ∣ k') ∧ Partitionable (h * k') ∧
          CentralNonzero (qtwist E ((h * k' : ℤ) : ℚ)) ∧ Nonvanishing.omega k' ≤ A ∧
          vL (h * k') ≤ 2 * Nonvanishing.omega h + 2 * Nonvanishing.omega k' + s (h * k') + CE :=
  roughCompanion hHL hTS P.bcdt hE hS h2 hbad Partitionable
    (fun d => d ≠ 0 → Z2Corank (selmerTwoPower (qtwist E d)) 0) vL s C₁ A₀ hdummy
    (fun d hL hd0 => forwardRank_zero_of_prints P (qtwist_isElliptic hE (by exact_mod_cast hd0)) hL)
    h33b

end ZInQ.Manuscript.RC.GlueSweep.Ana
