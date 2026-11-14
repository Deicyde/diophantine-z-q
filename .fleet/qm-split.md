# qm-split (fleet summary)

**Result.** All 14 rows (H-1, H-2, H-20, H-35, H-42, H-43, H-44, H-46, H-59, H-61, H-63, H-86, H-87, H-88)
have compiled Lean proofs from stated hypotheses (no sorry, axioms standard; `scratch/qm-split/`, report
`docs/research/qm-split.md` with the row table).
- **H-46 `qmClassNumberOne` proved outright**: `𝒪` is left norm-Euclidean (`|nrd(x−q)| ≤ 7/8`), so class number
  one is a computation (Eichler not needed); plus the lattice glue.
- **From published-form leaves only**: H-35 (Yu Thm 1.1 with its splitting clause), H-2 (Igusa's ψ₄, χ₁₀),
  H-86 (Shimura–Taniyama: CM ⇒ defined over ℚ̄), H-42, H-61, H-63 (one leaf `QMCentralizerCMC` over ℂ +
  bundle leaf T11(b): unit counts, Atkin–Lehner fixed points, optimal embeddings are computations).
- **H-20** from one leaf candidate (`ShimuraFamily`): the comparison isomorphism of two fine witnesses
  (`compare_iso`, the chain's uncompiled `PinUnique` without π) is now compiled, and with it `HeckeOfFine`
  and `R1bTransport`.
- **Reduced**: H-44 (leaf: ≤ 1 even θ-null vanishes; glue: θ⁴ ratios algebraic); H-87 (valence formula +
  Shimizu covolume of 𝒪¹ as leaves; project glue `GammaStarFromO1` = index 4 + fundamental-domain comparison);
  H-88 (Hauptmodul property *proved* from the valence formula; `EllipticOrderDvd` proved; remaining: the same
  covolume glue and one number, j_θ = −16/27 at the disc −24 point); H-1, H-43, H-59 (existence leaf +
  per-clause published statements for every witness).

**Compiles** (`scratch/qm-split/chk.sh`, leaf-fold4's olean chain `TailK`): ClassNumberOne 8 s, YuLeaf 5 s,
QMAut 16 s, STQM 12 s, ThetaSplit 4 s, ThetaRatios 5 s, Valence 5 s, Haupt 24 s, ModuliSplit 43 s.

**Remains**: report §3 glue (θ⁴ algebraicity; index-4 covolume transfer; the CM value; coarse-witness
comparison for the moduli rows). Theorem numbers in docstrings are UNVERIFIED (no network). No row statement
found false; H-35's row is a weakening of Yu's theorem (the leaf keeps the clause).
