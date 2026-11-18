import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus

/-!
# AuxFactor, part 4: RC0's wiring leaf `AuxFactor`

Manuscript `diophantine_zq.tex`, App G, Proposition `ex:app-rough-companion`, tex 10055–10150.

RC0's wiring records the partitionable auxiliary factor as the leaf
`ZInQ.Manuscript.RC.Wiring.AuxFactor W A₀` (file `ZInQKernel/Contrib/OneProof/RC/Wiring/Genus.lean`,
the input `hdummy` of RC13's `roughCompanion`).  `auxFactor_wiring` (`PROVED`) produces it from:

* the dummy supply: `A₀` reduced residue classes `cls i` modulo `m` (`2 ∣ m`), fixed before `h`;
  their realization by distinct primes avoiding the support, the exclusions and `h` is
  `dummy_realization` (RC2's realization lemma: CRT and Dirichlet);
* the dictionary input `hDict` (named after the fact, tex 10096–10098, 10139: "for the total type
  that actually occurs, `hk'` is partitionable"): when the dummy primes realize the seed-anchor
  classes, every `k' = au` of the companion's shape makes `hk'` partitionable.  Its combinatorial
  core, for the typed graph of `hk'`, is `negative_partitionable` (`Pieces.lean`: negative types,
  minimum seeds, anchors plus a nonempty remainder);
* `hS`: the support consists of primes (`SupportSpec`).
-/

namespace ZInQ.Contrib.CloudB3RC53.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.RC Finset

/-- **RC0's leaf `AuxFactor W A₀`** (tex 10055–10150, 10131–10139), `PROVED` from the dummy
classes and the dictionary input `hDict`. -/
theorem auxFactor_wiring {ℓ : ℕ} (W : Wiring.WData ℓ) (hS : ∀ p ∈ W.S, p.Prime)
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ∣ m) (A₀ : ℕ) (cls : ℕ → ZMod m) (hcls : ∀ i, IsUnit (cls i))
    (hDict : ∀ (h : ℤ) (q : ℕ → ℕ), (∀ i < A₀, (q i).Prime ∧ ((q i : ℕ) : ZMod m) = cls i) →
      ∀ u : ℤ, (∏ i ∈ range A₀, (q i : ℤ)) * u < 0 → ((∏ i ∈ range A₀, (q i : ℤ)) * u) % 8 = 1 →
        Squarefree ((∏ i ∈ range A₀, (q i : ℤ)) * u) →
        (∀ p ∈ W.S ∪ h.natAbs.primeFactors,
          Nonvanishing.IsSquareAt p (((∏ i ∈ range A₀, (q i : ℤ)) * u : ℤ) : ℚ)) →
        W.Partitionable (h * ((∏ i ∈ range A₀, (q i : ℤ)) * u))) :
    Wiring.AuxFactor W A₀ := by
  intro h hh0 _ _ _ X hX
  obtain ⟨q, -, hq, ha0, hasf, haω, haSX, hah⟩ := dummy_realization m hm hm2 A₀ cls hcls W.S X h
  refine ⟨∏ i ∈ range A₀, (q i : ℤ), ha0, hasf, haω, fun p hp => ?_, hah hh0.ne', ?_⟩
  · have hpp : p.Prime := by
      rcases mem_union.mp hp with hp | hp
      · exact hS p hp
      · exact hX p hp
    exact haSX p hp hpp
  · exact fun u hu h8 hsf hsq _ =>
      hDict h q (fun i hi => ⟨(hq i hi).1, (hq i hi).2.2.2.2⟩) u hu h8 hsf hsq

open ZInQ.Manuscript.SelmerTwoPower in
/-- **RC0's leaf `EvenUpper33b W C₁` from (F.1)–(F.2)** (tex 10079–10129, 2273–2341), `PROVED`
from the inputs of `h33b_of_F` (App E's (E.11), (E.9), (E.8), the forward rank-zero theorem and the
Boolean comparison on the address cubes), with `v₂L_*(d) = padicValRat 2 (W.Lstar d)` and
`s(d) = sFun ℓ d`. -/
theorem evenUpper33b_wiring {ℓ : ℕ} (W : Wiring.WData ℓ)
    (aNZ Lnz : ℤ → Prop) (va : ℤ → ℤ) (u : ℤ → ℚ_[2]) (κ Cloc cE c : ℤ)
    (hE11 : ∀ D, (Lnz D ↔ aNZ D) ∧ (aNZ D → padicValRat 2 (W.Lstar D) = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - Nonvanishing.omega D) (href : ∃ D, aNZ D)
    (hfwdL : ∀ p, Lnz p → Z2Corank (selmerTwoPower (Etw ℓ p)) 0)
    (h32 : ∀ p, Z2Corank (selmerTwoPower (Etw ℓ p)) 0 → (u p = 0 ↔ ¬ Lnz p) ∧
      (Lnz p → |Padic.valuation (u p) - (padicValRat 2 (W.Lstar p) - 2 * Nonvanishing.omega p -
        (shaLength (Etw ℓ p) : ℤ))| ≤ Cloc))
    (hmiss : ∀ δ : ℤ, (∀ D, aNZ D → δ ≤ va D - Nonvanishing.omega D) →
      (∃ D, aNZ D ∧ va D - Nonvanishing.omega D = δ) →
      ∀ d, d ≠ 0 → W.Partitionable d → Z2Corank (selmerTwoPower (Etw ℓ d)) 0 → ∀ M : ℤ,
        ∃ x, (aNZ x ∧ va x - Nonvanishing.omega x = δ) ∧
          (u x = u d ∨ M - cE ≤ Padic.valuation (u x - u d))) :
    ∃ C₁ : ℤ, Wiring.EvenUpper33b W C₁ := by
  obtain ⟨C₁, h⟩ := h33b_of_F (fun d => d ≠ 0 ∧ W.Partitionable d)
    (fun d => Z2Corank (selmerTwoPower (Etw ℓ d)) 0) aNZ Lnz va (fun d => padicValRat 2 (W.Lstar d))
    (fun d => shaLength (Etw ℓ d)) u κ Cloc cE c hE11 hE9 href hfwdL h32
    (fun δ hmin hatt d hP hC => hmiss δ hmin hatt d hP.1 hP.2 hC)
  exact ⟨C₁, fun d hd hP hC => h d ⟨hd, hP⟩ hC⟩

end ZInQ.Contrib.CloudB3RC53.AuxFactor
