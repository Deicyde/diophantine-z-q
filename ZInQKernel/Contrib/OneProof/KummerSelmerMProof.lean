import ZInQKernel.Contrib.PoleRC.SelMTauCeti

/-!
# The Kummer identification `#Sel₂(E_ℓ/ℚ) = #SelM ℓ`, proved

Lane R7 of fork issue #83. The explicit `2`-Selmer system `SelM ℓ` (`ZInQKernel/Contrib/PoleRC/Defs.lean`)
has as many elements as the genuine `Sel₂(E_ℓ/ℚ) = selmerAt (curve ℓ) 1`
(`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean`, Tau Ceti's `2`-Selmer group with the local
conditions at every place of `ℚ`). The proof is the bijection `SelM ℓ ≃ Sel₂(E_ℓ/ℚ)` of
`ZInQKernel/Contrib/PoleRC/SelMTauCeti.lean` (Silverman, AEC 2nd ed., Prop. X.1.4, in the
manuscript's Kummer coordinates `(x + 3ℓ, x − ℓ)`, `diophantine_zq.tex` line 1058), which holds for
every positive integer `ℓ`.

`kummerSelmerM_proof` has exactly the type of the GLUE hypothesis `KummerSelmerM` of the
pole-from-restricted-converse assembly (`fun ℓ h1 h2 => kummerSelmerM_proof ℓ h1 h2` discharges it).
-/

namespace ZInQ.Manuscript.PoleRC

/-- **The Kummer identification for `E_ℓ`** (Silverman X.1.4), proved: for positive squarefree `ℓ`,
`#Sel₂(E_ℓ/ℚ) = #SelM ℓ` (squarefreeness is not needed). -/
theorem kummerSelmerM_proof : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ →
    Nat.card (ZInQ.Manuscript.SelmerTwoPower.selmerAt (ZInQ.Manuscript.curve (ℓ : ℚ)) 1) =
      (ZInQ.Manuscript.PoleRC.SelM ℓ).ncard :=
  fun ℓ hℓ _ => SelMTauCeti.card_selmerAt_curve ℓ hℓ.ne'

end ZInQ.Manuscript.PoleRC
