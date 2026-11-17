# charpoly-hf results log

## Setup (2026-11-16 18:30 PST)
- Base wip/leaf-fold33b 968b59ef8; origin/main c1e4ed1b8 already an ancestor (merge: "Already up to date").
- Build: reflink copy of ~/dzq-wt/leaf-fold33b/.lake/build and lean/.lake/build (that tree is at 4da8d4f32 =
  base + hP23 fold; H chain identical).
- Copied charpoly-charp's sources (origin/wip/charpoly-charp 512080e4) into scratch/charpoly-hf/cc/ for reference.

## Reading findings (VERIFIED by reading)
- charpoly-charp's only char-p input: `exists_minpoly_endE (hH : PkgI3.HomFreeFinite) (hT : TateModuleFree) Ab α`
  (CommonTraceHomFree.lean), applied at FrobTraceLink's `Ab : AbVar k`, `CharP k p`, for ℓ = 3, 5 and
  E = PadicAlgCl ℓ. It uses `hH k Ab Ab` (End free finite + ℤ_ℓ ⊗ End ↪ End T_ℓ) and `hT` (basis of T_ℓ).
- FrobTraceLink (TailC L8674) is existential in (k, Ab, α): no property of α beyond FrobCompare at 3, 5 is available.
- Blueprint names `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed`
  (blueprint/roadmap/height-decomposition/abelian-varieties/characteristic-polynomial.md L6).
