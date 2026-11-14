# qm-split (fleet summary)

**Result.** All 14 rows (H-1, H-2, H-20, H-35, H-42, H-43, H-44, H-46, H-59, H-61, H-63, H-86, H-87, H-88)
have compiled Lean proofs from stated hypotheses (no sorry, axioms standard; `scratch/qm-split/`, report
`docs/research/qm-split.md`).
- **H-46 `qmClassNumberOne` proved outright**: `𝒪` is left norm-Euclidean (`|nrd(x−q)| ≤ 7/8`), so class number
  one is a computation; plus the lattice glue.
- **From published-form leaves only**: H-35 (Yu Thm 1.1 with its splitting clause), H-2 (Igusa's ψ₄ and χ₁₀),
  H-86 (Shimura–Taniyama: CM ⇒ defined over ℚ̄), and H-42, H-61, H-63 from one leaf `QMCentralizerCMC`
  (End_𝒪(A) over ℂ is ℤ or an optimally embedded Φ⁻¹(𝒪)) + the bundle leaf T11(b): unit counts, Atkin–Lehner
  fixed points and the optimal-embedding row are computations in B and in imaginary quadratic fields.
- **Reduced**: H-44 (leaf: at most one even θ-null vanishes; glue: θ⁴ ratios algebraic), H-87 (leaf: valence
  formula for cocompact Fuchsian groups; glue: covolume π/6 of Γ*), H-88 (the Hauptmodul property is *proved*
  from the valence formula; `EllipticOrderDvd` proved; remaining glue: covolume and the single value
  j_θ = −16/27 at the disc −24 point), H-1/H-20/H-43/H-59 (existence leaf + per-clause glue = published
  statement + transport to every witness).

**Compiles**: `ClassNumberOne`, `YuLeaf`, `QMAut`, `STQM`, `ThetaSplit`, `ThetaRatios`, `Valence`, `Haupt`,
`ModuliSplit` (`scratch/qm-split/chk.sh` over leaf-fold4's olean chain `TailK`, 4-25 s each).

**Remains**: the glue of report §3; the most useful piece is the comparison isomorphism of fine witnesses
(would discharge all transports of the moduli rows). Theorem numbers in leaf docstrings are UNVERIFIED (no
network). No statement found false; H-35's row is a weakening of Yu's theorem (the leaf keeps the clause).
