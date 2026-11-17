# h21-lcal results log

Base: wip/leaf-fold33b 6b97a5c7 + merge origin/wip/h21c-steps (61db5238).
Build tree copied from ~/dzq-check2 (Main.lean byte-identical); `lake build` of TYZThm21Span, Main, HeckeAll,
GaussFE: OK (16074 jobs), frozenTarget standard axioms.

## Findings
1. TYZ source not on host (~/tyz-src absent). TYZ's definition of 𝓛 (L338–353) is taken from the project
   transcription `scratch/rv-tyz-inputs/tyzcalc.py` header and docs/research/h33-sign.md row 84,
   rv-tyz-inputs.md §1.7: 𝓛(n)=0 if ord_{s=1}>1; ord 0: 𝓛²=L(E_n,1)/(2^{2k-2-a}Ω); ord 1: 𝓛²=L'(E_n,1)/(2^{2k-2-a}ΩR_n).
   (UNVERIFIED against the print by this task.)
2. Plan: FE with sign +1 for d ≡ 1, 3 (mod 8) from the tree's HeckeFE machinery (DeuringCd 1 + quadratic twist
   + Fourier relation); then ord ≠ 1; then lcalSqPrinted R m = lcalSq m.

## Compile outcomes
- RootPlus.lean: `functionalEquationPlus_proof : FunctionalEquationPlus` (Λ(2−s) = +Λ(s), N = 32d², 0<Re s<2,
  squarefree d ≡ 1, 3 mod 8). VERIFIED compiled, axioms [propext, Classical.choice, Quot.sound].
  New pieces: `jacobi_unit_swap` (reciprocity on norm fibres), `lseries_eq_twistedL` (every odd squarefree d,
  from DeuringCd 1 + cdCoeff_twist), `fourierHat_cd_eq3`/`cdFourier3_of_oddGauss` (d ≡ 3 mod 4: κ = −4d(1+i)(2/d)),
  `fourierRel_plus` (κ = 4d(1+i) for d ≡ 1, 3 mod 8), so −iκ(1+i) = +8d.
