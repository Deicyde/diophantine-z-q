# heegner-32: the Heegner point of `C_d` without the canonical model of `X₀(32 d²)`

Status: research note (task heegner-32, 2026-11-16), branch `wip/heegner-32` (base 60a3fac7 + gz-weil ad22e947).
Lean: new files `ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd.lean` and
`ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd/{Used,Twist,Recip,Compose,Genus}.lean` (about 2,550 lines, each file under 60 KB).
Nothing else under `ZInQKernel/` was edited. Development copies, numerics, checks and log are in
`scratch/heegner-32/`.

Marks:
* **VERIFIED**: read in a source named here, computed, or compiled.
* **STANDARD**: a published theorem with an exact reference.
* **SPECULATIVE**: an assessment.

This host has no network. **Every theorem number and locator of the literature below is UNVERIFIED** (from memory).

---

## 0. Main result

**The Heegner-point step of the `C_d` chain needs no canonical model of `X₀(N)` at any level and no new leaf. `hL3`
on the route (`GZStatements.GrossZagierHeegnerCd`) follows from `hCM` and the two Gross–Zagier statements alone.**

```lean
-- ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd.lean
theorem ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (hCM : T5Glue.ShimuraMainCM)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd
theorem ZInQ.Heegner32.heegnerPointRationalCdEven_of_printed (hCM : T5Glue.ShimuraMainCM) :
    ZInQ.Heegner32.HeegnerPointRationalCdEven
```

Checks (all VERIFIED):

* Both theorems, and every intermediate theorem listed in §2, depend only on `[propext, Classical.choice, Quot.sound]`
  (`scratch/heegner-32/Check.lean`, output `out_check.txt`).
* `scratch/heegner-32/MainEdit.lean` proves `ZInQ.FrozenTarget` (`frozenTarget_heegner32`, standard axioms;
  `out_mainedit.txt`). It uses `frozenTarget`'s hypotheses, with `hL3` replaced by `GrossZagierFormulaCd` and
  `GrossConjugationCd`. `hCM` is already a hypothesis of `frozenTarget`.

**Effect on the counts (SPECULATIVE ratings).** On main 60a3fac7, `hL3` is one composite GLUE.

* gz-weil's chain replaced it by `HeegnerPointRationalCd` (composite or consequence) plus the two Gross–Zagier
  statements.
* gz-heegner reduced `HeegnerPointRationalCd` to `X0ModuliGaloisMero` (consequence), a new GLUE because `hX` is gone
  on main.
* This task removes that GLUE completely. The `C_d` chain is now `hL3` → {`GrossZagierFormulaCd`,
  `GrossConjugationCd`}: **−1 GLUE outside H** if those two count as printed leaves. The statement review rated both
  as consequences, because they are stated for the analytic Heegner sum. That rating is the subject of the sibling
  tasks of this group.

**Finding: the statement `GZHL3.HeegnerPointRationalCd` is stronger than the chain needs, and its odd-`c` part is not
reached.**

* `HeegnerPointRationalCd` quantifies over every `c ∈ ℚ^×` with `c Λ_f ⊆ L`.
* Odd `c` really occur. For `d = 5` and `d = 13`, the period lattice of `f_d` is all of `L(C_d)`, so `c = 1` is
  allowed (VERIFIED, numerical: `scratch/heegner-32/py/periods.py`).
* Any route through the level-32 parametrization reaches only `c ∈ 2ℤ`. The lattice of 32a1 is `((1+i)/2)·Λ(C₁)`. For
  odd `c`, the summands are determined only up to the kernel of a 2-isogeny.
* The chain uses a single `c`. **Corrected statement:** `HeegnerPointRationalCdEven` (the same statement for
  `c ∈ 2ℤ`). It suffices: `grossZagierHeegnerCd_of_even` replaces the `c` of the parametrization by `2·num(c)`.
* The all-`c` statement remains available from the smallest instance of the canonical model that is actually used
  (§3), but nothing needs it.

---

## 1. The route

The Heegner sum of `C_d` at even `c` is a twisted sum of Heegner points of `X₀(32)` of conductor `d`. Their Galois
action is already proved: the eta route at level 32 is hx-used's, completed by theta-wp8's `ThetaWeierstrass8`. The
twist then needs three more ingredients:

* the composition of conductor-`d` Heegner forms with an ideal;
* Chebotarev in the ring class field of conductor `d`;
* genus theory for `√d`.

All three are proved here.

1. **Twist identity** (`Twist.lean`, `weierPt_two_eichlerCd`). For `L` a lattice of `C_d`, `g = gaussD d` (`g² = d`)
   and `λ = (1+i)/2`:
   `weierPt C_d L (2Φ_d(τ)) = S_{λg}(Z(τ)) + S_{λ̄g}(Z(τ))`, where
   - `Z(τ) = Σ_{a mod d} (a/d)·(x, y)(τ + a/d)`, with `(x, y)` x0-32's eta-quotient parametrization of 32a1;
   - `S_μ(x, y) = (μ²x, μ³y)`.

   The ingredients:
   - gz-weil's twist formula `gΦ_d(τ) = Σ_a (a/d) Φ₁(τ + a/d)`;
   - `(x, y)(σ) = weierPt 32a1 L' (Φ₁(σ) + c₀)` for every lattice `L'` of 32a1 (`exists_c0`, from gz-weil's
     `global_eq`; the sign of `℘'` by differentiation). The constant `c₀` drops out because `Σ_a (a/d) = 0`;
   - the addition law of `weierPt` (`weierPt_short_add`), from the vendored uniformization theorem
     `PeriodPair.isUniformization_toPoint` (flt-cqj2's port of the Anthropic FLT project);
   - the two lattices `λ̄gL`, `λgL` of 32a1, with `2 = 2λ̄·λ + 2λ·λ̄`.

   Galois: `σ ∘ Ψ = Ψ ∘ (±σ)`, the sign being `σ(g)/g` (`map_psiMap`, where `Ψ = S_{λg} + S_{λ̄g}`).
2. **Reduction to `X₀(32)`** (`heegnerPointRationalCdEven_of_twist`, from `TwistTransportCd`): for `σ ∈ Aut(ℂ/K)`,
   `σ(Z(τ_Q)) = (σ(g)/g)·Z(τ_{πQ})` for a permutation `π` of the Heegner representatives.
3. **Conductor-`d` composition** (`Compose.lean`). For `Q = [A, B, C]` of level `32d²`,
   `J = ⟨a, (−b+√D)/2⟩`, gz-heegner's Dirichlet composite `Q' = [aA, B', C']` and `a·a' ≡ α (mod d)`:
   - `J_d·⟨1, τ_{Q'} + a'/d⟩ = ⟨1, τ_Q + α/d⟩`, and the same with `1/32` (`nb_lat`, `nb_latN`), where
     `J_d = J ∩ 𝒪_d = ⟨a, d(−b+√D)/2⟩`;
   - `τ_Q + α/d` is the root of the primitive form `[Ad, (B − 2Aα/d)d, dC − Bα + Aα²/d]`, of level 32 and discriminant
     `d²D` (`exists_nbForm`);
   - for `γ = [p, q; r, s] ∈ Γ₀(32d²)`, `(x, y)(τ + a'/d) = (x, y)(γτ + p²a'/d)` (`phiC_shift_gamma0`: the matrix
     `T_{p²a'/d} γ T_{−a'/d}` lies in `Γ₀(32)`).
4. **Level-32 reciprocity at conductor `d`.** This is hx-used's `srAt_x_theta`/`srAt_y_theta` (from `hCM` and
   `ThetaWP8.thetaWeierstrass8`), applied with the ideal `J` of conductor `d`.
5. **Chebotarev at conductor `d`** (`ringClassJd`). Every class of `Pic(𝒪_d)` contains a prime of degree one with a
   Hermite basis (or the class is trivial). This is gz-heegner's `heegnerClassJ'` with conductor `d`; the new lemma is
   `idealLat_eq_jLatd`.
6. **Genus theory** (`Genus.lean`, `genusSqrtD`):
   - `K(√d) ⊆ H_{𝒪_d}` (`adjSqrt_le_ringClassField`). This is Bauer's theorem through the kernel's
     `le_of_splitSet_diff_subset`. A principal prime `β𝒪_K`, `β ∈ 𝒪_d`, has `N(β) ≡ u² (mod d)` (`norm_mod_d`). The
     quadratic character of `𝒪_K/𝔭` at `d` equals the Jacobi symbol `(χ₄(q)q/d)`, which is `1`
     (`quadraticChar_natCast_eq_jacobi`, by induction on the factorization of `d`).
   - `Art(𝔭)(√d) = (p/d)√d` for a prime of degree one, `p ∤ 2d` (`artin_sqrtH`). This uses Euler's criterion in
     `𝓞_{H_{𝒪_d}}` modulo a prime above `𝔭`, with Tau Ceti's `isArithFrobAt_ringClassArtinEquiv_picClass`, and
     quadratic reciprocity for `d ≡ 1 (mod 4)`.
   - Then `σ(√d) = (N J/d)√d`, which matches `(a'/d) = (N J/d)(a/d)` from step 3.

The assembly is `twistTransportCd_of_genus hCM ringClassJd genusSqrtD`. The sign bookkeeping is `chiZ_mul` and
friends; the sum is reindexed by multiplication by the unit `p²a⁻¹` of `ℤ/d`.

**Numerical cross-check** of `TwistTransportCd` before the proof (VERIFIED, `py/twist_check.py`). For `d = 5`,
`D = −31` (h = 3), `∏_Q(X − x(Z_Q))` and `∏_Q(X − √5·y(Z_Q))` have rational coefficients to about 15 digits.

---

## 2. Lean inventory (all VERIFIED, compiled; namespace `ZInQ.Heegner32`)

| File | Main declarations |
| --- | --- |
| `Used.lean` | `X0ModuliGaloisHeegnerMeroAt`, `X0ModuliGaloisParamCd`, `x0ModuliGaloisParamCd_of_mero`, `point_transport3`, `heegnerC_fixed3`, `exists_point_of_fixed`, `heegnerPointRationalCd_of_used` |
| `Twist.lean` | `weierPt_short_add`, `weierHom`, `sMap`, `weierPt_scale`, `exists_c0`, `zTw`, `sum_char_eichler`, `weierPt_sum_eq_zTw`, `weierPt_two_eichlerCd`, `map_sMap`, `sMap_neg`, `psiMap`, `map_psiMap`, `TwistTransportCd`, `HeegnerPointRationalAtEven`, `HeegnerPointRationalCdEven`, `heegnerPointRationalCdEven_of_twist`, `periodsIn_two_num`, `heegner_at_even`, `grossZagierHeegnerCd_of_even`, `grossZagierHeegnerCd_of_twist` |
| `Recip.lean` | `phiC_nonsingular`, `map_phiC`, `phiC_gamma0`, `TwistLatticeCd` (an intermediate reduction, superseded), `phiC_transport`, `twistTransportCd_of` |
| `Compose.lean` | `jLatd`, `nb_lat`, `nb_latN`, `exists_compose'`, `exists_nbForm`, `phiC_add_int`, `phiC_shift_gamma0`, `chiZ` lemmas, `isCoprime_B_d`, `RingClassJd`, `GenusSqrtD`, `twistTransportCd_of_genus`, `exists_prime_picClass_eqf`, `idealLat_eq_jLatd`, `ringClassJd` |
| `Genus.lean` | `quadraticChar_natCast_eq_jacobi`, `norm_mod_d`, `adjSqrt_le_ringClassField`, `sqrtH`, `artin_sqrtH`, `genusSqrtD`, `grossZagierHeegnerCd_of_hCM`, `heegnerPointRationalCdEven_of_hCM` |
| `HeegnerPointRationalCd.lean` | `grossZagierHeegnerCd_of_printed`, `heegnerPointRationalCdEven_of_printed` |

`RingClassJd` and `GenusSqrtD` are `def … : Prop`, and both are proved (`ringClassJd`, `genusSqrtD`). They are stated
for the ideals the proof uses: primes of degree one, or `𝒪_K`.

---

## 3. The all-`c` statement: the smallest instance of the canonical model used

`HeegnerPointRationalCd` as stated (all `c`, odd ones included) is proved from `hCM` and `X0ModuliGaloisParamCd`
(`heegnerPointRationalCd_of_used`). `X0ModuliGaloisParamCd` is implied by gz-heegner's `X0ModuliGaloisMero`
(`x0ModuliGaloisParamCd_of_mero`). It is the canonical-model statement `σ(g(τ_Q)) = g(τ_{Q'})`, restricted as follows:

* `N` = the level of the newform of `C_d`, which is `32 d²`;
* `g ∈ {x∘φ, y∘φ, 1/(x∘φ − t)}`, for the parametrization `φ = weierPt C_d L (cφ_f)`;
* regularity at the two points;
* the moduli hypotheses of `X0ModuliGaloisMero`;
* `τ_Q`, `τ_{Q'}` Heegner points of level `N` and one odd fundamental discriminant.

**Rating:** consequence (GLUE). It is an instance of Shimura 1971 §6.7 / Thm 6.23 together with the `ℚ`-rationality of
the parametrization. It is **not printed** as such: the print is the canonical model for all of `ℚ(X₀(N))`. The chain
does not need it (§0).

---

## 4. Integration

* **Files.** `ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd.lean` imports `HeegnerPointRationalCd/Genus.lean`,
  which in turn imports `Compose` → `Recip` → `Twist` → `Used`. The imported modules defining the statements are
  `GrossZagierHeegner/{HeegnerCd,Cd,WeilJacobi,WeilLattice}`, `X0ModuliUsed/EtaRoute`, `ThetaWeierstrass8` and the
  vendored `Thm_PeriodPair_isUniformization_toPoint`. None of the files imports `OneProof.Main`. Build:
  `lake build ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd` (VERIFIED).
* **`#discharges`** (`scratch/heegner-32/discharges-output.txt`, VERIFIED): `61 open hypotheses, 3088 theorems
  checked, 8 discharge one`.
  - The new theorems discharge no field directly. They prove the `C_d` form `GZStatements.GrossZagierHeegnerCd`, not
    `hL3 = GZDecomp.GrossZagierHeegner` (all elliptic curves), exactly as for gz-weil.
  - The fold is the top-level `Main.lean` edit in `scratch/heegner-32/MainEdit.lean`.
* **Autofold spec:** `scratch/heegner-32/autofold.json`.
  - `hL3` is a top-level binder, so `autofold.py` does not apply. The spec records the edit and the kinds.tsv rows of
    the two remaining leaves.
  - `grossZagierFormulaCd` and `grossConjugationCd`: kind published, flag unread. The statement review's "consequence"
    rating is pending in the sibling tasks.
* **Leaves, rated:**

| Leaf | Printed form? | Reason |
| --- | --- | --- |
| `GZHL3.GrossZagierFormulaCd` (existing, gz-hl3) | printed form with the constant forgotten, pending the sibling tasks | Gross–Zagier I.6.3 / V.2.1 for `C_d`; stated for the analytic Heegner sum `Σ weierPt(cφ_f(τ_Q))`. This task proves that sum (at `2c`) is `Ψ` of a `(·/d)`-twisted sum of points of x0-32's eta-quotient model at conductor-`d` Heegner points, whose Galois action is the moduli one (hx-used's eta route), but not the identification with GZ's `y_K` |
| `GZHL3.GrossConjugationCd` (existing) | same | Gross 1984 §5 |
| `T5Glue.ShimuraMainCM` (existing `hCM`) | printed form (kinds.tsv) | unchanged |
| (no new leaf) | — | `RingClassJd` and `GenusSqrtD` are proved |

---

## 5. What remains

* The all-`c` `HeegnerPointRationalCd`, if a consumer ever needs it (§3).
* The identification of the analytic Heegner sum with Gross–Zagier's moduli `y_K`, so that `GrossZagierFormulaCd` and
  `GrossConjugationCd` count as printed. This belongs to the sibling tasks.

  The twist identity here may help. The analytic sum at `2c` equals `Ψ(Σ_Q Z(τ_Q))` with `Z` a twisted sum of moduli
  points of `X₀(32)` (SPECULATIVE usefulness).

## 6. Reproduction

```
lake build ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd
lake env lean scratch/heegner-32/Check.lean         # axioms → out_check.txt
lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
lake env lean scratch/heegner-32/MainEdit.lean      # frozenTarget_heegner32 → out_mainedit.txt
lake env lean scratch/heegner-32/Discharges.lean    # → discharges-output.txt
uv run --offline --with cypari2 python scratch/heegner-32/py/periods.py 5
uv run --offline --with cypari2 python scratch/heegner-32/py/twist_check.py 5 31
```
