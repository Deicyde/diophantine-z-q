# kolyv-cst-printed: Kolyvagin's Theorem 1 and Cai–Shu–Tian's Theorem 1.1 in printed form

Task kolyv-cst-printed, 2026-11-17. Base: fork main `d435851d` with `origin/wip/pc-from-rc`
(`5404a9fe`, fork issue #83) merged (clean). Lean 4.35.0, Mathlib v4.35.0. No network: **neither
print was read for this task.** Every clause of both statements is UNVERIFIED (pending reading),
so both leaves count GLUE under the owner's rule (kind published, flag "pending reading: ").

## Verdict

1. **Kolyvagin.** pc-s12's `PoleS12.KolyvaginThm1` states only the `r = 1` case. The manuscript
   cites Theorem 1 for both `r = 0` and `r = 1` (L1093), and the proof of Theorem 5.3 uses the
   `r = 0` case four times (L2386, L7626, L7780, L8267). New file
   `ZInQKernel/Contrib/OneProof/KolyvCST/Kolyvagin.lean` states `KolyvaginThm1Printed`
   (`r ≤ 1`: rank `= r` and `Ш` finite), proves that pc-s12's `KolyvaginThm1` follows from it, and
   states all of Lemma 5.5 (`ForwardRank`, `ForwardCorank`) with proved bridges from
   `BCDTThmA`, `KolyvaginThm1Printed`, `MordellWeil` and one textbook GLUE Prop (`KummerCorank`).
   No statement is false. One modelling issue (Known issue K1): over `PoleS12.IsModular` (the
   `L`-series form of modularity) `KolyvaginThm1` and `KolyvaginThm1Printed` are consequences of
   Kolyvagin's Theorem 1 together with BCDT Theorem A, not of Kolyvagin alone, because the print's
   hypothesis (as an earlier audit reports it) is a weak Weil parametrization `X₀(N) → E`.
2. **Cai–Shu–Tian.** New file `ZInQKernel/Contrib/OneProof/KolyvCST/CaiShuTian.lean` states
   `CSTThm11Split`: Theorem 1.1 in the case the manuscript uses (every prime of `N` split in `K`,
   no extra units, `E` without CM), over Mathlib's `L`-function machinery, Weierstrass `℘`, Tau
   Ceti's ring class fields with the Artin isomorphism, Tau Ceti's Néron–Tate pairing and Tau Ceti's
   Eichler integral. The stop rule applies to three objects, which are **not** in Mathlib or Tau
   Ceti: `X₀(N)` over `ℚ` with its algebraic Heegner points and the parametrization over `ℚ`; the
   Rankin–Selberg `L`-function; and `deg φ`. The statement uses the complex-analytic Heegner point
   and quantifies over every algebraic point with that complex image, the `χ`-twisted Euler product
   of `E/K`, and an existential constant `C > 0` in place of `8π²(f,f)/deg φ`. Each replacement
   keeps the statement a consequence of the print (modulo the dictionaries listed in §2.4), and the
   existential constant is all that both manuscript uses need (checked in §2.5).

(Sections 1–7 below are filled in after the compile; see the log.)
