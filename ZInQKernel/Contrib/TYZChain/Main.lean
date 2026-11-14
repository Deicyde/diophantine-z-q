import ZInQKernel.Contrib.TYZChain.Thm35
import ZInQKernel.Contrib.TYZChain.L321
import ZInQKernel.Contrib.TYZChain.Lemma318
import ZInQKernel.Contrib.TYZChain.Lcal

/-!
# TYZ chain: reading A of TYZ Theorem 3.5 from the remaining TYZ-side leaves and glue

Task tyz-chain (2026-11-14). Report: `docs/research/tyz-chain.md`.

One theorem, `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves`, which combines

* tyz-321 (`TYZChain/L321.lean`, on top of cm-bridge, `TYZChain/Bridge.lean`):
  `T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First` (reading A from the three
  `𝓛`-leaves, `Shimura.ShimuraReciprocityModFn`, `Lemma318Literal HHprime` and `Thm35First`;
  `Lemma321Five` is proved from the CM leaf);
* tyz-lcal (`TYZChain/Lcal.lean`): `TYZLcal.tyzLcalOne_of_leaves` (`TYZLcalOne` from
  `TYZThm11Integral` and `TYZLemma29Mod2`);
* tyz-318 (`TYZChain/Lemma318.lean`): `T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn`
  (`Lemma318Literal HHprime` from the glue `SqrtTwoNotInHHprime`);
* tyz-35 (`TYZChain/Thm35.lean`): `TYZ35.thm35First_of_lcal_thm33` (`Thm35First ℓ tyzZ` from the
  pinned TYZ Theorem 3.3, `TYZThm33Pinned ℓ`).

No `sorry`, no `axiom`.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **TYZ reading A (`ZInQ.Literature.TYZThm35ReadingA`, Tian–Yuan–Zhang Theorem 3.5(2) in reading A)
from the remaining TYZ-side leaves and glue.** The hypotheses, with kind and source:

1. `h11 : TYZThm11Integral` — **LEAF**. TYZ Theorem 1.1, first assertion (odd case): `𝓛(m)` is an
   integer for odd squarefree `m ≡ 1, 3 (mod 8)` (TYZ L371–380). Defined in
   `ZInQKernel/Contrib/TYZDecomp/Leaves.lean` (task tyz-decomp).
2. `h29 : TYZLemma29Mod2` — **LEAF**. TYZ Lemma 2.9 with Proposition 2.3, modulo 2
   (L1062–1066, L580–586), for every sign choice of `𝓛` on classes 1, 3. Defined in
   `ZInQKernel/Contrib/TYZDecomp/Leaves.lean` (task tyz-decomp).
3. `hS : Shimura.ShimuraReciprocityModFn` — **LEAF** (textbook). The main theorem of complex
   multiplication for values of rational modular functions on `X₀(N)` at Heegner points, in Gross's
   form (Shimura 1971 Thm. 5.4 with the canonical model of `X₀(N)`; Gross 1984 §3; theorem numbers
   UNVERIFIED). Defined in `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean` (task tyz-cm); reviewed by
   task shimura-modfn, which recommends keeping it as the CM leaf.
4. `h2 : T318.SqrtTwoNotInHHprime` — **GLUE** (not yet proved in general). `√2 ∉ ℍ'_n` for squarefree
   `n ≡ 5 (mod 8)`: TYZ's Step 3 in the proof of Lemma `torsion2` (Lemma 3.18). Proved for `n` whose
   only divisor `≡ 5 (mod 8)` is `n` (`T318.sqrtTwo_not_mem_HHprime_of_single`). Defined in
   `TYZChain/Lemma318.lean` (task tyz-318).
5. `h33 : ∀ ℓ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ` — **LEAF**. TYZ Theorem 3.3 with Lemma 3.14
   (`char'`) for the pinned CM points (TYZ L1299–1311, proof L1865–2023), for every sign choice `ℓ`
   of `𝓛`. Defined in `TYZChain/Thm35.lean` (task tyz-35); its docstring lists the facts used to
   pass from the printed statement to the pinned one (HUMAN CHECK there).

Everything else on the TYZ side is proved: `TYZLcalOne` (tyz-lcal), `Lemma321Five` (tyz-321),
`Lemma318Literal HHprime` from `h2` (tyz-318), `Thm35First` from `h33` (tyz-35), and the class-7
branch, ring class rewiring and genus theory (cm-bridge, ring-class, tyz-cm). -/
theorem tyzThm35ReadingA_of_leaves
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h2 : T318.SqrtTwoNotInHHprime)
    (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ) :
    ZInQ.Literature.TYZThm35ReadingA :=
  T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First h11
    (ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves h11 h29) h29 hS
    (T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn h2)
    (TYZ35.thm35First_of_lcal_thm33 h33)

end ZInQ.Contrib.TYZChain
