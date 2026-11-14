# tyz-split results log

## Setup (2026-11-14 07:00 PST)
- Base f70ec251. Copied `.lake/build/lib/lean/ZInQKernel/Contrib` from worktree tyz-chain, then
  `lake build ZInQKernel.Contrib.TYZChain.Main`: 10388 jobs, success (VERIFIED).

## T-11 (`TYZ35.TYZThm33Pinned`)
- Source read: Period7.tex L1171–1311 (§3.1: test vector, CM point, Prop 3.2 `CM point1`, Φ, P_χ,
  𝒫, Theorem 3.3 `GZ`), L1860–1935 (proof of Thm 3.3, Lemma 3.14 `char'`, Lemma 3.15), L325–400
  (𝓛, ρ), L992–998 (h₂). VERIFIED (read).
- Findings from the source (VERIFIED read):
  * Thm 3.3 (L1299–1311) itself contains the "non-torsion only if χ = χ_{d₀,d₁}" clause; Lemma 3.14
    (L1868–1877) is the first step of its proof (L1913: "Lemma 3.14 implies the first statement").
  * Φ is an arbitrary fixed set of representatives (L1279 "Fix a set Φ ⊂ Cl'_n ..."), so tyz-35's
    `∀ f` form is TYZ's own quantification (HUMAN CHECK (a) of tyz-35 resolved).
  * χ_{d₀,d₁} = character of K_n(√d₁) for n ≡ 5, 6; of K_n(√d₁*) for n ≡ 7 (L1304–1305): matches
    tyz-35's `pairSet` convention (HUMAN CHECK (b) resolved; now also a Lean theorem, below).
  * h₂(n) = dim_{F₂} Cl_n/2Cl_n (L992, L2354) (HUMAN CHECK (c) resolved; Lean `h2G_eq`).
  * Cl_n = Gal(H_n/K_n), Cl'_n = Gal(H'_n/K'_n), K'_n = K_n for n ≡ 5, 7; H'_n = H_n(z_n) (L1251, L1263).
  * 𝒫(n) = 2^{-1-ρ(n)} 𝓛(n) α_n (L1291); 𝓛(n) for n ≡ 5,6,7 involves the regulator R_n (L341).
- Lean `scratch/tyz-split/T11.lean`: leaf `TYZThm33` (printed form, n ≡ 5, 7; 𝒫 existential with
  `Q d ∈ A(K_d)^-` and the vanishing clause), glue proved, `tyzThm33Pinned_of_tyzThm33`,
  `tyzThm35ReadingA_of_printedThm33`. Compiled 07:40: 0 errors, no sorry; axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED, output `T11.out`).
