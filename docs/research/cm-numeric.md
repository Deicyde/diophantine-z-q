# cm-numeric: TYZ's class-7 CM point pinned, Shimura reciprocity checked numerically, `GenusPointLeafCM` split

Task cm-numeric, 2026-11-13. Lean: `scratch/cm-numeric/Class7.lean` (imports the built
`ZInQKernel.Contrib.TYZGenus.Package`; no `sorry`, no `axiom`). Numerical scripts and outputs:
`scratch/cm-numeric/*.py`, `*.out` (PARI/GP 2.17.2 through cypari2, 400 significant digits). Results
log: `scratch/cm-numeric/log.md`. Marks: **VERIFIED** (computed, compiled, or read in a named source),
**STANDARD**, **SPECULATIVE**, **UNVERIFIED** (theorem numbers from memory).

## 0. Main results

1. **TYZ's class-7 base CM point, pinned (VERIFIED: read and computed).** In TYZ (arXiv:1411.4728v1,
   `Period7.tex` L1196, L1203–1205), for `n ≡ 7 (mod 8)` the test vector is `f_n = i₀ : X₀(32) → A`
   (the identity), and `√−n ↦ [[δ, 2], [−(n+δ²)/2, −δ]]`, `δ² ≡ −n (mod 128)`. The fixed point `h ∈ ℍ`
   solves `(n+δ²)h² + 4δh + 4 = 0`, so **`z_n = f_n(P_n)` is the Heegner point of the primitive form
   `[(n+δ²)/4, δ, 1]`** (level 32, discriminant `−n`, class of `[𝔞]` principal). In Lean:
   `CMNumeric.tyzForm7`, `CMNumeric.tyzZ7` (with `δ := tyzDelta n`, the least `δ ∈ [0,128)`; existence
   proved by `decide`). For n = 7, 15, 23, 31, 39, 47, 55, 71 the computed point lies on `A`, depends only
   on `δ mod 64` (`δ ↦ −δ` conjugates it), and its coordinates generate exactly the Hilbert class field
   `H_n` (TYZ Prop 3.2(3)); e.g. `z_7 = ((−1+√−7)/2, (3+√−7)/2)`.
2. **Lemma 3.21(4) holds for the pinned class-7 genus point** `Z(e) = Σ_{t∈2Cl_e} z_e^t` with β' acting
   through cm-points' `betaOneSign`: `Z(e)^{β'} + Z(e) = g(e)·(2,−4)` for all 12 tested `e` (7 ≤ e ≤ 103;
   g = 1, 1, 3, 3, 2, 5, 2, 7, 5, 3, 4, 5). VERIFIED (computed). This removes cm-points' worry that a
   guessed form could make Lemma 3.21(4) false.
3. **`CM.ShimuraReciprocity` has the right direction (VERIFIED: computed).** With `Q'` computed from the
   leaf's own lattice condition (`(⟨1,τ'⟩,⟨1/32,τ'⟩) = c·𝔭̄·(⟨1,τ⟩,⟨1/32,τ⟩)`) and Frobenius tested exactly
   as `g(X) ≡ X^p mod (F, p, √D − b)`, Frobenius at 𝔭 is multiplication by `𝔭̄` in 26/26 cases
   (D = −23, −47, −71, −31, −39, −320); multiplication by `𝔭` fails in all 24 cases where `[𝔭]` has order
   > 2. `B' ≡ B (mod 64)` comes out automatically. D = −320 is TYZ's conductor-4 order for n = 5.
4. **`TYZSigmaFixesZn` holds numerically, in a sharper form**: the Artin symbol of `sigmaClass n` maps
   `f₀(P_n)` to `f₀(P_n) + (0,0)` (n = 5, 13, 21, 29, 37; 15 cases), so it fixes
   `z_n = (1 − [i])f₀(P_n)`. Lemma 3.21(1) for class 5 (n = 5, 13, 37; both choices of Φ₀, 8 lifts each)
   also holds (30 cases), for either sign `1 ∓ [i]` in `z_n`.
5. **Lean (Class7.lean):** every genus point is pinned (`CMNumeric.tyzZ := tyzGenusPt Phi0 Z7`), and
   `GenusPointLeafCM` splits into closed leaves about pinned objects:

   ```lean
   theorem tyzThm35ReadingA_of_pinnedLeaves (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
       (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hi : IInH4) (hs : TYZSigmaFixesZn)
       (hN : HprimeNormal) (h318 : Lemma318Literal HHprime) (hcm7 : CMFieldOfDefinition7)
       (hg : GenusFieldLeLni) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
       (h5 : Lemma321Five) (h7' : Lemma321Seven) : ZInQ.Literature.TYZThm35ReadingA
   ```

   (VERIFIED compiled, standard axioms; §3.) `Phi0` is never junk: TYZ's `Φ₀` exists (`phi0_spec`,
   proved).

## 1. Statements (Lean, `namespace ZInQ.Contrib.TYZGenus.CMNumeric`)

Pinned objects (definitions):

* `tyzDelta n`, `tyzForm7 n hn : HeegnerForm 32 (−n)` = `[(n+δ²)/4, δ, 1]`, `tyzZ7 n = heegnerPt (tyzForm7 n)`.
* `ActsAsArtinO d O ρ c` (ρ acts on the ring class field of any order `O` of `ℚ(√−d)` as Tau Ceti's
  Artin symbol of `c`; `= ActsAsArtin4` for `O = O4 d` by `Iff.rfl`); `exists_actsAsArtinO` (proved);
  `liftMax d c` (a chosen lift for the maximal order); `sqClasses d = Cl(K_d)²`.
* `Z7 e = Σ_{c ∈ Cl(K_e)²} galPt (liftMax e c) (tyzZ7 e)` (TYZ L1316–1318 with σ = 1: Φ₀ = 2Cl_e).
* `IsPhi0 e T`, `Phi0 e` (class 5: a chosen set of lifts of elements of `2Cl'_e`, exactly one over
  each element of `2Cl_e`); `phi0_spec : IsPhi0 e (Phi0 e)` for `e ≠ 0` (proved, §9 of the file).
* `tyzZ = tyzGenusPt Phi0 Z7`, `hilbertBar d`, `genusBar d`.

Leaves (`def … : Prop`, about pinned objects):

| leaf | content | source | kind |
|---|---|---|---|
| `CMFieldOfDefinition7` | `tyzZ7 n ∈ A(H_n)` (n ≡ 7 squarefree) | Gross 1984 §1–3, Shimura 1971 Thm 5.7 (UNVERIFIED numbers); TYZ Prop 3.2(3) L1260 (VERIFIED read); numerically exact for 8 n | leaf (textbook) |
| `GenusFieldLeLni` | genus field of `ℚ(√−e)` ⊆ `ℚ(i, √p : p ∣ e)` (e ≡ 7) | Gauss / Cox Thm 6.1 (UNVERIFIED number) | leaf (textbook) |
| `Lemma321Seven` | ∀ β₁-lift σ: `Z7 e^σ + Z7 e = g(e)·τ(1/2)` | TYZ Lemma 3.21(4), L2514–2516 | leaf; VERIFIED numerically (12 e) |
| `Lemma321Five` | ∃ β₁-lift σ: `tyzZ e^σ + tyzZ e ∈ g(e)τ((1−i)/2) + ℤτ(1)` for e ∣ n, e ≡ 5 | TYZ Lemma 3.21(1), L2496–2512 (any lifting, any Φ₀) | leaf; numerically supported (n = 5, 13, 37 with Φ₀ = {1}, {σ}) |
| `Thm35First ℓ tyzZ` | cm-points' statement for the pinned `tyzZ` | TYZ Thm 3.3/3.5 | leaf (unchanged) |
| `Class7GenusPtDefined` | `Z7 e ∈ A(L_e(i))` | TYZ L2455–2458 | **glue**: `class7GenusPtDefined_of` from `CMFieldOfDefinition7` + `GenusFieldLeLni` |
| `IInHprime` | `i ∈ H'_n` (n ≡ 5) | genus theory + TYZ Prop 3.2(1) | leaf (textbook), only for §7's alternative |
| `TYZSigmaShiftsF0` | Artin(`sigmaClass`) `f₀(P_n) = f₀(P_n) + (0,0)` | **not printed**; VERIFIED numerically (15 cases) | computation, not a leaf |

## 2. Glue proved (Class7.lean)

* `Copy.*_eq`: the verbatim copies of `CMFieldOfDefinition`, `TYZSigmaFixesZn`, `Lemma318Literal`,
  `GenusPtsDefined`, `Thm35First`, `Lemma321`, `GenusPointLeafCM` are `rfl`-equal to cm-points'.
* `tyzDelta_spec`: `n ≡ 7 (mod 8) → 128 ∣ δ² + n`.
* `lemma321_of : Lemma321Five → Lemma321Seven → Lemma321 tyzZ`.
* `genusPtsDefined_tyzZ`, `genusPointLeafCM_of_pinned` (the split of cm-points' bundled leaf),
  `genusPointLeaf_of_pinned` (through cm-points' `genusPointLeaf_of_split`).
* `tyzThm35ReadingA_of_pinned`, `tyzThm35ReadingA_of_pinned'` (through cm-points'
  `tyzThm35ReadingA_of_cmLeaves`), `tyzThm35ReadingA_of_pinnedLeaves`.
* §7: `fixed_of_mem_Hprimebar` (easy half of the Galois correspondence for `H'_d`),
  `tyzSigmaFixesZn_of : TYZSigmaShiftsF0 → IInHprime → TYZSigmaFixesZn`.
* §9 `exists_restrict` (every element of `Gal(H_e/K_e)` extends to `Gal(H_{e,4}/K_e)`),
  `exists_phi0_elem`, `artinO_inj`, `exists_isPhi0`, `phi0_spec`.
* §8 Galois descent for class 7: `galPt_mul`, `galPt_congr`, `actsO_mem`, `actsO_agree`, `actsO_mul`,
  `sum_sqClasses_mul`, `Z7_mem`, `galPt_Z7` (lifts of `2Cl_e` fix `Z(e)`), `mem_genusBar_of_fixed`,
  `class7GenusPtDefined_of`.

## 3. Compile status

`lake build ZInQKernel.Contrib.TYZGenus.Package` (10092 jobs, clean), then
`lake env lean scratch/cm-numeric/Class7.lean`: no errors, no warnings (VERIFIED, 2026-11-13).
`#print axioms` (output `scratch/cm-numeric/audit-out.txt`) for `tyzDelta_spec`, `exists_actsAsArtinO`,
`lemma321_of`, `genusPointLeafCM_of_pinned`, `genusPointLeaf_of_pinned`, `tyzThm35ReadingA_of_pinned`,
`tyzThm35ReadingA_of_pinned'`, `tyzSigmaFixesZn_of`, `galPt_Z7`, `class7GenusPtDefined_of`,
`tyzThm35ReadingA_of_pinnedLeaves`, `Copy.genusPointLeafCM_eq`, `phi0_spec`: all
`[propext, Classical.choice, Quot.sound]`. The file sets `maxRecDepth 8000` (needed by the
generic-order Artin lemmas) and uses `decide +kernel` (no `native_decide`).

## 4. What the numerics do not settle

* `CMFieldOfDefinition H`, `TYZSigmaFixesZn`, `Lemma318Literal` stay unproved in Lean: they are
  theorems of CM theory / TYZ for all `n`, and no finite computation proves them. The computation made
  `TYZSigmaFixesZn` concrete (`TYZSigmaShiftsF0`, a statement about one explicit Heegner point and its
  Galois conjugate) but that sharper form is not printed anywhere, so it is not a leaf.
* `Lemma318Literal` (torsion of `A(ℍ'_n)`) is not testable with these tools (fields of degree ≥ 2^k·h).
* The sign of `[i]` in `tyzZn` (cm-points caveat 5) is not singled out by any of the checks here:
  `TYZSigmaFixesZn` and Lemma 3.21(1) hold for both `1 − [i]` and `1 + [i]`.
* `GenusFieldLeLni` stays a leaf: ring-class proves the genus field has degree `2^{t−1}` and is cut
  out by the genus characters (`genusField_eq_fixedField_chi`), but not that it equals `ℚ(√p*)`.
