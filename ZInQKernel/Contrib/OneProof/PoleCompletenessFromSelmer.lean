import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuine
import ZInQKernel.Contrib.OneProof.SelmerExplicit

/-!
# Theorem 5.2 from Theorem 5.3 over the genuine Selmer groups: the remaining glue, proved

The descent lane (`ZInQKernel/Contrib/OneProof/PoleCompletenessFromRCGenuine.lean`) proves the
manuscript's Theorem 5.2 (`Manuscript.PoleCompleteness`) from Theorem 5.3 over the genuine Selmer
condition (`SelmerTwoPower.RestrictedConverseGenuine`) and the statements `PoleS12.Lemma54`,
`PoleS12.KummerSelmerM`, `PoleS12.BCDTThmA`, `PoleS12.KolyvaginThm1` and `PoleRC.MordellWeil`.
This file proves three of them:

* `kummerSelmerM`: `#Sel₂(E_ℓ/ℚ) = #SelM ℓ` (`SelmerTwoPower.card_selmerAt_curve_eq_ncard_selM`: Tau
  Ceti's comparison of the cohomological and explicit `2`-Selmer groups, and the explicit group of
  `E_ℓ` in the manuscript's Kummer coordinates; `SelmerSplit.SelM` is `PoleRC.SelM` by definition);
* `mordellWeil`: the Mordell–Weil theorem over `ℚ` (`SelmerTwoPower.mordellWeilQ`, Tau Ceti);
* `lemma54At_genuine`: Lemma 5.4 at the curves `E_ℓ` (`Lemma54At SelmerCorankOne`), from the
  Cassels–Tate square property of these curves (`SelmerTwoPower.lemma54At_selmerCorankOne`); and
  `lemma54_of_casselsTate`: the statement `Lemma54` for all curves, from Cassels–Tate for all
  curves.

So Theorem 5.2 follows from Theorem 5.3 (genuine), the Cassels–Tate square property and the printed
`BCDTThmA` and `KolyvaginThm1` (`poleCompleteness_of_restrictedConverseGenuine_casselsTate`).
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.SelmerTwoPower

/-- **`KummerSelmerM`, proved**: for every `ℓ > 0`, `#Sel₂(E_ℓ/ℚ) = #SelM ℓ`. -/
theorem kummerSelmerM : KummerSelmerM := fun ℓ hℓ _ => by
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  exact card_selmerAt_curve_eq_ncard_selM

/-- **Mordell's theorem, proved** (Tau Ceti's `WeierstrassCurve.Affine.fg_point_of_numberField`). -/
theorem mordellWeil : PoleRC.MordellWeil := fun E hE => by
  haveI := hE
  exact mordellWeilQ E

/-- **`Lemma54` from the Cassels–Tate square property**: Lemma 5.4 for every elliptic curve over `ℚ`
with full rational two-torsion. -/
theorem lemma54_of_casselsTate
    (hCT : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsTateSquare E) : Lemma54 :=
  fun E hE h2 h8 => by
    haveI := hE
    exact selmerCorankOne_of_card_selmerAt_one' E (hCT E hE) h2 h8

/-- **Lemma 5.4 at the curves `E_ℓ` over the genuine Selmer groups** (round 1's interface
`Lemma54At SelmerCorankOne`), from the Cassels–Tate square property of these curves. -/
theorem lemma54At_genuine
    (hCT : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
      CasselsTateSquare (Manuscript.curve ℓ)) :
    PoleRC.Lemma54At SelmerCorankOne :=
  lemma54At_selmerCorankOne hCT

/-- **Theorem 5.2 from Theorem 5.3 over the genuine Selmer condition**, with the Kummer
identification and Mordell–Weil proved: the remaining inputs are Theorem 5.3, the Cassels–Tate square
property of the curves `E_ℓ`, and the printed `BCDTThmA` and `KolyvaginThm1` (of which only the rank
statement is used). -/
theorem poleCompleteness_of_restrictedConverseGenuine_casselsTate
    (hRC : RestrictedConverseGenuine)
    (hCT : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
      CasselsTateSquare (Manuscript.curve ℓ))
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_abstract SelmerCorankOne hRC (lemma54At_genuine hCT)
    (kolyvaginRankOne_of_printed hB hK) mordellWeil

/-- The same, through the descent lane's final theorem, with `Lemma54` from Cassels–Tate for all
elliptic curves over `ℚ`. -/
theorem poleCompleteness_of_restrictedConverseGenuine_casselsTate'
    (hRC : RestrictedConverseGenuine)
    (hCT : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsTateSquare E)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverseGenuine hRC (lemma54_of_casselsTate hCT) kummerSelmerM hB hK
    mordellWeil

end ZInQ.Manuscript.PoleS12
