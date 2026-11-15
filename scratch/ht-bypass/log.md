# ht-bypass results log

Base 9a100aa7 (leaf-fold22). Field: `eigenformHTNew : ZInQ.Contrib.HodgeSplit.EigenformHTNew`
(`OpenResearchLeaves21`, TailZ34; type at TailX.lean l.96, def TailS.lean l.1275).

## Step 1: uses (VERIFIED by grep of ZInQKernel/OneProof/H and reading)

- Projections `.eigenformHTNew`: only bundle-to-bundle copies (TailZ4 … TailZ34) and one real use,
  TailX.lean l.205: `r13 := HodgeLF7.eigenformHT (eigenformHT_of_kato_ds r.eigenformHTNew newformOfEigenformG9
  r.dsThm965 r.dsThm966)` (old field `r13 : HDec.PkgI4.EigenformHT`).
- `.r13`: only copies (TailD l.103, TailE, LPrefix, TailN) and one real use, TailD l.139
  `G0Galois.g8_g12_of_leaves3` → `g8_g12` (TailA l.2255) → `g12` (TailA l.2211) → `hW hR14 hR13 …` where
  `hW : G12Weight` (TailA l.2059: `EigenformHT` is an antecedent).
- `G12Weight` is filled in TailK l.328 by `G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT`
  = `g12Weight_of` (TailB l.4998). There `hHT` is applied once:
  `hHT 5 ιC ιL N k χ g ρ hN (by omega) hg hss' hatt'` in the branch `1 < k`.
- Instance: ℓ = 5; `g` = the normalized eigenform (any level N, any weight k) that `r11r12` (PanBerger) returns
  for G8's `r₅ ⊂ ℚ̄₅ ⊗ V₅(A)` (A the QM abelian surface over L'); ρ = the semisimple ρ_g from R14.
- At k = 2 the conclusion `∃ n, {n, n+1−k} = {0,−1}` holds with n = 0 (`g12Weight_concl_iff`, TailB l.4985):
  the field is used only for k ≥ 3, to exclude eigenforms of weight ≥ 3. VERIFIED (compiled below).

## Step 2: weakest needed Prop

- `EigenformHTNew5Ge3`: EigenformHTNew at ℓ = 5, k ≥ 3 (newforms, any level including 5 | N).
- Consumers re-proved with it: `G12WeightWeak` (G12Weight with antecedent `EigenformHT5Ge3Chain`),
  `g12WeightWeak_of_senTwist`, `g12Weak`, `g8_g12Weak` (scratch/ht-bypass/HTBypass.lean §2).

## Step 3: bypass via abelian-variety fields

- Fails for the needed instances (k ≥ 3): see report §3 (argument: the determinant and Weil/Ramanujan absolute
  values are consistent with every k; only the *difference* of the Hodge–Tate weights of ρ_g separates k, and for
  k ≥ 3 ρ_g is not a constituent of V_ℓ of an abelian variety). STANDARD/SPECULATIVE as marked in the report.
- k = 2 (weight-2 newforms, the case r16 + DeRhamComparison could cover) is never used by the route.

## Compile log
