# hfx-proof results log

Target: `H29Split.TYZTestVectorExists` (hfx), `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L421.
Base: origin/main 0caafe66 + merged origin/wip/t21-proof f597c34c (T21Proof helpers) + origin/proof/hp23-hurwitz-ab-20261116 84a9f2e6 (fork PR #39, Hurwitz approximation).

## Computations (VERIFIED, python `scratch/hfx-proof/orbits.py`)
- Right action of `K_{n,2}^×` on TYZ's 8 classes `O_B^× \ (O_B/4)^× / {±1}`, for every residue of
  `τ(√−n) = ai+bj+ck` (mod 8) allowed by `AdmissibleTau`:
  - n ≡ 3 (mod 8) (a,b,c odd; 64 residues): orbits of sizes (2,6). The 2-orbit depends on the residue
    and need not contain the class of 1 (e.g. (3,1,1): 2-orbit {(1,0,0),(0,0,1)}).
  - n ≡ 1 (mod 8) (4|c, one of a,b odd, the other ≡ 0 mod 4; 32 residues): orbits {000,010}, {110,100},
    {101,111,001,011} for every residue, using the uniformizer 1+τ(√−n); without it (2,2,2,2).
  - Hence `π^{U_n}` is 1-dim in all cases; generator `−3/1` (n≡3), `1/−1/0` (n≡1).

## Lean (compiled with `lake env lean`)
- `HfxProof/Assembly.lean`: `testVector_of_partition` — hfx for (n,τ) from surjectivity onto the 8 double
  cosets, a function F on {0,1}³ whose level sets are the classes, and rank-one linear algebra. COMPILES.
- `HfxProof/Euclid.lean`: `euclid_prime` (βO_B + pO_B = γO_B, nrd γ = p). COMPILES.
- `HfxProof/ClassOne.lean`: `exists_global_mul_unit` (B̂^× = B^× Ô_B^×, Ô_B read place by place). COMPILES.
- `HfxProof/Finite25.lean`: `lemma25_check` (decide, 13 s): every residue of (O_B/4)^× is ±μβ_t. COMPILES.
- `HfxProof/Lemma25.lean`: `exists_twoRep` (TYZ Lemma 2.5 surjectivity: every unit of B̂ lies in some
  B^× twoRep(t) H, for every n, τ). COMPILES.
- `HfxProof/Order.lean`, `TwoAdic.lean`, `TauData.lean`, `Sg.lean`, `Merge.lean`: general local order R_2,
  2-adic obstruction (branches e = 1 mod 4 and uniformizer mod 8), data of admissible τ (τ(√−n) = ai+bj+ck,
  τ(O_K) ⊂ ℤ+ℤω), local-obstruction subgroup SgC and `twoRep_not_mem_DC`, merge lemma
  `twoRep_mem_DC_of` with integer-congruence criterion `local_merge_cond`. COMPILE.
- `HfxProof/Finite3.lean` (decide, 27 s) + `HfxProof/Case3.lean`: `testVector_three`: hfx for every
  squarefree n ≡ 3 (mod 8) and admissible τ. COMPILES (no sorry).
- `HfxProof/Finite1.lean` (decide, 2 min), `HfxProof/Order1.lean`, `HfxProof/Case1.lean`: `testVector_one8`:
  hfx for every squarefree n ≡ 1 (mod 8) and admissible τ. COMPILES (no sorry).
- `ZInQKernel/Contrib/OneProof/TYZTestVectorExists.lean`: `ZInQ.Contrib.HfxProof.tyzTestVectorExists :
  H29Split.TYZTestVectorExists`. COMPILES. No sorry/native_decide/axiom/#eval (grep).
- `#discharges` (scratch/hfx-proof/Discharges.lean): `DISCHARGES [hfx] by ZInQ.Contrib.HfxProof.tyzTestVectorExists`,
  still assumes [], axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- FoldCheck.lean: frozenTarget_noHfx and frozenTarget_noHfxT21 compile, standard axioms. VERIFIED.
- autofold --dry-run: refuses (`hfx` is a top-level argument, not a bundle field); manual fold needed.
