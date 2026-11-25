import ZInQKernel.Contrib.OneProof.R16Split
import ZInQKernel.Contrib.OneProof.AfTateLambda

/-!
# `r16CoreY` from Diamond–Shurman's printed Theorem 9.5.4 ("satisfies") and a determinant statement

Task r16-close. `R16Split.R16CoreY` (declared in `ZInQKernel/Contrib/OneProof/R16Split.lean`) is proved
from the leaves of aftate-fix2 (`ZInQKernel/Contrib/OneProof/AfTateLambda.lean`), with aftate-fix2's
single Eichler–Shimura leaf `AfTateLam.AfTateDSLambda` (characteristic polynomial of Frobenius on
`V_λ(A_f)`) replaced by the pair

* `AfTateLam.AfTateDSLambdaSat` (LEAF, printed form): Diamond–Shurman, *A First Course in Modular Forms*,
  GTM 228, Lemma 9.5.3 (`V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`) and Theorem 9.5.4 (`ρ_{f,λ}(Frob_𝔭)`
  **satisfies** `x² − a_p(f)x + χ(p)p = 0`), corrected fourth printing (2016), pp. 400–402
  (statements read by a human reader in a print copy for the `afCharpolyDS965` row, issue #14
  comment 7121091136; the proofs were not read);
* `AfTateLam.AfDetLambda` (GLUE): `det ρ_{f,λ}(Frob_p) = χ(p)p` for `p ∤ Nℓ`. Diamond–Shurman print the
  determinant only for the representation of Theorem 9.6.5 (Exercise 9.6.3(a)), not for the realization
  on `A_f` of Theorem 9.5.4; Shimura 1971 Thm 7.14 and Ribet, LNM 601 (1977) are candidate sources,
  unread (UNVERIFIED).

Diamond–Shurman's Theorem 9.5.4 states only that Frobenius *satisfies* the quadratic (VERIFIED in both
printings), so `AfTateDSLambda` alone is stronger than its print; the pair isolates the gap in the
determinant. The glue `AfTateLam.dsLambda_of_sat_det` (aftate-fix2, proved) recovers `AfTateDSLambda`.

No `sorry`, no `axiom`, no build-time code.
-/

namespace AfTateLam

/-- **`r16CoreY` from the printed leaves and the determinant glue (r16-close).** `HeckeJ1DS`
(Diamond–Shurman §6.3, §7.9), `AfShimura` (Shimura 1973 Thm 1), `AfTateDSLambdaSat` (Diamond–Shurman
Lemma 9.5.3 + Thm 9.5.4 as printed), `AfDetLambda` (the determinant of `ρ_{f,λ}` at Frobenius, glue),
`X1Igusa.IgusaGL2DS` (Diamond–Shurman Thm 7.6.3) and Mumford's torsion theorem. -/
theorem r16CoreY_of_sat_det (h1 : HeckeJ1DS) (h2 : AfShimura) (hS : AfTateDSLambdaSat)
    (hD : AfDetLambda) (hI : X1Igusa.IgusaGL2DS) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  r16CoreY_of_printed h1 h2 (dsLambda_of_sat_det hS hD) hI hM

end AfTateLam
