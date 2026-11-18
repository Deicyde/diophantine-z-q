import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Dummy

/-!
# AuxFactor, part 3: the partitionable auxiliary factor assembled (App G, (F.3))

Manuscript `diophantine_zq.tex`, App G, Proposition `ex:app-rough-companion`, tex L10055–10150.

`auxFactor` (`PROVED` from the inputs below) is lane RC13's `roughCompanion` with two of its
three inputs discharged by Elliot's steps proved here:

* `h33b` — (F.1)–(F.2), from `h33b_of_F` (`Pieces.lean`), whose inputs are App E's (E.11), (E.9),
  (E.8) (lane RC11's area), the forward rank-zero theorem (PRINT, as RC13 takes it) and the Boolean
  comparison on the address cubes of partitionable parameters (Section 9 / RC2);
* `hdummy` — the dummy anchors, from `dummy_realization` (`Dummy.lean`, RC2's realization lemma),
  together with the dictionary input `hDict` (named after the fact, tex 10096–10098 and 10139:
  "for the total type that actually occurs, `hk'` is partitionable" when the dummy primes realize
  the seed-anchor classes; its combinatorial core is `negative_partitionable`, read through the
  coefficient dictionary).

The prints (Hoffstein–Luo, the BFH twist sign, BCDT) are RC8/RC13's leaves, used as they are.
-/

namespace ZInQ.Contrib.CloudB3RC53.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Manuscript.RC.Nonvanishing Finset

/-- **The partitionable auxiliary factor** (Proposition `ex:app-rough-companion`, (F.3),
tex 10055–10150), `PROVED` from: the prints `hHL`, `hTS`, `hBCDT` (RC8/RC13); the dummy classes
`cls` modulo `m` (fixed before `h`) and the dictionary input `hDict`; the forward rank-zero
theorem `hforward` (PRINT); and the inputs of (F.1)–(F.2) (`hE11`, `hE9`, `href`, `h32`,
`hmiss`).  Conclusion: constants `A, C_E` fixed before `h` and the exclusions, and for every
admissible `h` and finite exclusion set a negative odd fundamental discriminant `k'` with
`hk'` partitionable, `L_*(hk') ≠ 0`, `ω(k') ≤ A` and
`v₂L_*(hk') ≤ 2ω(h) + 2ω(k') + s(hk') + C_E`. -/
theorem auxFactor (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ S)
    (Partitionable CorankZero : ℤ → Prop)
    -- the dummy supply and the dictionary
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ∣ m) (A₀ : ℕ) (cls : ℕ → ZMod m) (hcls : ∀ i, IsUnit (cls i))
    (hDict : ∀ (h : ℤ) (q : ℕ → ℕ), (∀ i < A₀, (q i).Prime ∧ ((q i : ℕ) : ZMod m) = cls i) →
      ∀ u : ℤ, (∏ i ∈ range A₀, (q i : ℤ)) * u < 0 → ((∏ i ∈ range A₀, (q i : ℤ)) * u) % 8 = 1 →
        Squarefree ((∏ i ∈ range A₀, (q i : ℤ)) * u) →
        (∀ p ∈ S ∪ h.natAbs.primeFactors,
          IsSquareAt p (((∏ i ∈ range A₀, (q i : ℤ)) * u : ℤ) : ℚ)) →
        Partitionable (h * ((∏ i ∈ range A₀, (q i : ℤ)) * u)))
    (hforward : ∀ d : ℤ, CentralNonzero (qtwist E d) → CorankZero d)
    -- (F.1)–(F.2)
    (aNZ Lnz : ℤ → Prop) (va vL : ℤ → ℤ) (sN : ℤ → ℕ) (u : ℤ → ℚ_[2]) (κ Cloc cE c : ℤ)
    (hE11 : ∀ D, (Lnz D ↔ aNZ D) ∧ (aNZ D → vL D = 2 * va D + κ))
    (hE9 : ∀ D, aNZ D → c ≤ va D - omega D) (href : ∃ D, aNZ D)
    (hfwdL : ∀ p, Lnz p → CorankZero p)
    (h32 : ∀ p, CorankZero p → (u p = 0 ↔ ¬ Lnz p) ∧
      (Lnz p → |Padic.valuation (u p) - (vL p - 2 * omega p - sN p)| ≤ Cloc))
    (hmiss : ∀ δ : ℤ, (∀ D, aNZ D → δ ≤ va D - omega D) → (∃ D, aNZ D ∧ va D - omega D = δ) →
      ∀ d, Partitionable d → CorankZero d → ∀ M : ℤ, ∃ x, (aNZ x ∧ va x - omega x = δ) ∧
        (u x = u d ∨ M - cE ≤ Padic.valuation (u x - u d))) :
    ∃ (A : ℕ) (CE : ℤ), ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      RootNumber (qtwist E h) (-1) → ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
        ∃ k' : ℤ, k' < 0 ∧ k' % 8 = 1 ∧ IsFundamentalDiscriminant k' ∧
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
          (∀ p ∈ X, ¬ (p : ℤ) ∣ k') ∧ Partitionable (h * k') ∧
          CentralNonzero (qtwist E ((h * k' : ℤ) : ℚ)) ∧ omega k' ≤ A ∧
          vL (h * k') ≤ 2 * omega h + 2 * omega k' + (sN (h * k') : ℤ) + CE := by
  obtain ⟨C₁, h33b⟩ := h33b_of_F Partitionable CorankZero aNZ Lnz va vL sN u κ Cloc cE c hE11 hE9
    href hfwdL h32 hmiss
  refine roughCompanion hHL hTS hBCDT hE hS h2 hbad Partitionable CorankZero vL
    (fun d => (sN d : ℤ)) C₁ A₀ ?_ hforward h33b
  intro h hh0 _ _ hhS X hX
  obtain ⟨q, -, hq, ha0, hasf, haω, haSX, hah⟩ := dummy_realization m hm hm2 A₀ cls hcls S X h
  refine ⟨∏ i ∈ range A₀, (q i : ℤ), ha0, hasf, haω, fun p hp => ?_, hah hh0.ne', ?_⟩
  · have hpp : p.Prime := by
      rcases mem_union.mp hp with hp | hp
      · exact hS p hp
      · exact hX p hp
    exact haSX p hp hpp
  · exact fun u hu h8 hsf hsq _ =>
      hDict h q (fun i hi => ⟨(hq i hi).1, (hq i hi).2.2.2.2⟩) u hu h8 hsf hsq

end ZInQ.Contrib.CloudB3RC53.AuxFactor
