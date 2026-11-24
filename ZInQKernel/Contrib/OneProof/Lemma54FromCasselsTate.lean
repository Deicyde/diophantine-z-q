import ZInQKernel.Contrib.OneProof.SelmerCorankFam
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal

/-!
# Lemma 5.4 from the Cassels–Tate square property, and Theorem 5.2 from it

The descent lane proves the manuscript's Theorem 5.2 (`Manuscript.PoleCompleteness`) from Theorem 5.3
over the genuine Selmer condition, Lemma 5.4 as a cited leaf (`PoleS12.Lemma54`, through its
consequence `PoleRC.Lemma54At SelmerCorankOne` at the curves `E_ℓ`), modularity and Kolyvagin's theorem
(`PoleS12.poleCompleteness_of_restrictedConverseGenuine_final`). This file proves Lemma 5.4 at the curves
`E_ℓ` (`lemma54At_of_casselsTate`), from the Cassels–Tate square property of these curves, over the
Selmer groups of `ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean` as they are defined there:

* `SelmerTwoPower.CasselsTateSquare E`: for every decomposition `Ш(E/ℚ)[2^∞] ≅ (ℚ₂/ℤ₂)^t × F` with `F`
  finite, `#F[2]` is a square (Cassels' theorem that the pairing on `Ш/div` is alternating and
  non-degenerate; the manuscript's proof of Lemma 5.4 uses it, `diophantine_zq.tex` lines 1076–1084);
* `PoleS12.CasselsTateSquareCurves`: that property for the curves `E_ℓ`, `ℓ > 0` squarefree,
  `ℓ ≡ 11 (mod 12)`;
* `lemma54_of_casselsTate`: the cited leaf `PoleS12.Lemma54` from Mordell–Weil and the Cassels–Tate
  square property for all elliptic curves over `ℚ`;
* `lemma54At_of_casselsTate`: `PoleRC.Lemma54At SelmerCorankOne` from `CasselsTateSquareCurves` (with
  Mordell–Weil for `E_ℓ`, `PoleRC.mordellWeil_curve`, the Kummer identification `PoleS12.kummerSelmerM`
  and `#E_ℓ(ℚ)[2] = 4`, `PoleRC.card_ker_two_nsmul_eq_four_M`);
* `poleCompleteness_of_restrictedConverseGenuine_casselsTate`: Theorem 5.2 from Theorem 5.3, the
  Cassels–Tate square property of the curves `E_ℓ`, modularity and Kolyvagin's theorem, by the proof of
  `poleCompleteness_of_restrictedConverseGenuine_mw` with `Lemma54At` from the Cassels–Tate property.

The proof of Lemma 5.4 is `SelmerTwoPower.Fam.selmerCorankOne_of_card_selmerAt_one`
(`SelmerCorankFam.lean`), over one family of completions; `Fam.sha_eq`, `Fam.selmerAt_eq` and
`Fam.selmerCorankOne_iff` (`SelmerFam.lean`) identify its groups with those of `SelmerTwoPower`.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology

variable (E : WeierstrassCurve ℚ)

/-- **The Cassels–Tate square property of `E/ℚ`** (Cassels, *Arithmetic on curves of genus 1, IV*,
J. reine angew. Math. 211 (1962): the pairing on `Ш(E/ℚ)` is alternating and non-degenerate modulo
the divisible part; Poonen–Stoll, Ann. of Math. 150 (1999)), in the form the manuscript's Lemma 5.4
uses: for every decomposition `Ш(E/ℚ)[2^∞] ≅ (ℚ₂/ℤ₂)^t × F` with `F` finite, `#F[2]` is a square (a
finite abelian group with an alternating non-degenerate pairing is `A × A`). `Ш(E/ℚ)` is `sha E`.
UNVERIFIED locator. -/
def CasselsTateSquare : Prop :=
  ∀ (t : ℕ) (F : Type) [AddCommGroup F] [Finite F],
    (AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F) →
      IsSquare (Nat.card (ZInQ.Cofinite.tors F 2))

/-- The Cassels–Tate square property over the groups of `SelmerTwoPower` is the one over the one-family
groups of `SelmerFam`. -/
theorem casselsTateSquare_iff_fam : CasselsTateSquare E ↔ Fam.CasselsTateSquare E := by
  unfold CasselsTateSquare Fam.CasselsTateSquare Fam.shaTwo
  rw [Fam.sha_eq]

end ZInQ.Manuscript.SelmerTwoPower

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.SelmerTwoPower

/-- **The Cassels–Tate square property for the curves `E_ℓ`**: `SelmerTwoPower.CasselsTateSquare`
at `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` for positive squarefree `ℓ ≡ 11 (mod 12)`, the curves of Theorem 5.3
and Lemma 5.4. -/
def CasselsTateSquareCurves : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → CasselsTateSquare (Manuscript.curve ℓ)

/-- **Lemma 5.4 (`lem:corank`) from Mordell–Weil and the Cassels–Tate square property**, in the form
of the cited leaf `PoleS12.Lemma54`. -/
theorem lemma54_of_casselsTate (hMW : PoleRC.MordellWeil)
    (hCT : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsTateSquare E) : Lemma54 := by
  intro E hE h2 h8
  haveI := hE
  rw [Fam.selmerCorankOne_iff]
  exact Fam.selmerCorankOne_of_card_selmerAt_one E (hMW E hE) ((casselsTateSquare_iff_fam E).mp (hCT E hE))
    h2 (by rw [← Fam.selmerAt_eq]; exact h8)

/-- **Lemma 5.4 at the curves `E_ℓ` from the Cassels–Tate square property** (`PoleRC.Lemma54At` with the
genuine corank condition): for positive squarefree `ℓ ≡ 11 (mod 12)`, `#SelM ℓ = 8` gives
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1`. -/
theorem lemma54At_of_casselsTate (hCT : CasselsTateSquareCurves) :
    PoleRC.Lemma54At SelmerTwoPower.SelmerCorankOne := by
  intro ℓ hℓ hsf hmod h8
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  haveI := PoleRC.curve_isElliptic hℓ0
  rw [Fam.selmerCorankOne_iff]
  refine Fam.selmerCorankOne_of_card_selmerAt_one _ (PoleRC.mordellWeil_curve _ hℓ0)
    ((casselsTateSquare_iff_fam _).mp (hCT ℓ hℓ hsf hmod)) (PoleRC.card_ker_two_nsmul_eq_four_M hℓ0) ?_
  rw [← Fam.selmerAt_eq, kummerSelmerM ℓ hℓ hsf, h8]

/-- **Theorem 5.2 from Theorem 5.3 over the genuine Selmer condition, with Lemma 5.4 proved from the
Cassels–Tate square property**: the remaining inputs are Theorem 5.3 (`RestrictedConverseGenuine`), the
Cassels–Tate square property of the curves `E_ℓ`, modularity (`BCDTThmA`) and Kolyvagin's theorem
(`KolyvaginThm1`, of which only the rank is used). -/
theorem poleCompleteness_of_restrictedConverseGenuine_casselsTate
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : CasselsTateSquareCurves)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (lemma54At_of_casselsTate hCT) (kolyvaginRankOne_of_printed hB hK))
    simultaneousConstruction

end ZInQ.Manuscript.PoleS12
