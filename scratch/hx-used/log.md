# hx-used results log

Base: 43513d87 (leaf-fold25). Target: top hypothesis `hX : T5Glue.X0ModuliGalois` of `ZInQ.OneProof.frozenTarget`.

## 1. Consumers of hX on the route (VERIFIED, read at base)

* `ZInQKernel/OneProof/Main.lean:64,70`: `hX` enters only as
  `T5Glue.shimuraReciprocityModFn_of_printed hCM hX : Shimura.ShimuraReciprocityModFn` (argument `hS` of
  `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves`).
* `RingClassLattice.lean:3352` `shimuraReciprocityModFn_of_printed` → `:2762 _of_t5''` → `:2754 _of_t5'` → `:2741 _of_t5`
  → `shimuraReciprocityModFn_of_split (cmModuli_of_t5 ..) (x0RatStructure_of_leaf hX)` (:2686, :2716).
  `x0RatStructure_of` (:819) applies `hL` at `(N, g, σ₀, τ, τ)` and `(N, g, σ, τ, τ')`; `_of_split` instantiates
  `τ = Q.tauH`, `τ' = Q'.tauH` for Heegner forms `Q Q' : HeegnerForm N D` (same `D`).
* Consumers of `hS : ShimuraReciprocityModFn` (TYZChain/Main.lean:61 → L321.lean:2156 → :2137 → :2123 → Bridge.lean:3134):
  `Shimura.cmFieldOfDefinition_of_shimuraModFn hS`, `Shimura.shimuraReciprocityPic_of_shimuraModFn hS`,
  `Shimura.cmValueRingClass_of_modFn hS` (→ `cmAlgebraic_of_cmValue`), `T321.znOverH4_of hS`.
  Each of these uses `hS` only at `N = 32` and `g ∈ {X0.xC, X0.yC}`:
  ShimuraMain.lean:188-191 (`shimuraReciprocityPic_of` at 32, xC/yC), ShimuraMain.lean:55-59 and Bridge.lean:3102-3108
  (`CMValueRingClass` at 32, xC/yC), L321.lean:1988-1992 (via `cmFieldOfDefinition_of_shimuraModFn`).
* gz-heegner (origin/wip/gz-heegner) does not use the kernel's `hX`; it introduces `X0ModuliGaloisMero` (stronger) and
  proves `x0ModuliGalois_of_mero`.

=> used form: `X0ModuliGalois` at `N = 32`, `g ∈ {X0.xC, X0.yC}`, `τ, τ'` Heegner points of level 32 and equal discriminant.

## 2. Contributor file (VERIFIED: compiled with `lake env lean`, 2026-11-15)

`ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean` (copy: `scratch/hx-used/X0ModuliUsed.lean`):
* `X0ModuliUsed.X0ModuliGaloisHeegnerAt N g`, `X0ModuliUsed.X0ModuliGaloisX0_32` (used form).
* `x0ModuliGaloisX0_32_of : T5Glue.X0ModuliGalois → X0ModuliGaloisX0_32` — axioms [propext, Classical.choice, Quot.sound].
* `tyzThm35ReadingA_of_used h11 h29 hCM hXU h33 : TYZThm35ReadingA` — standard axioms.
* `frozenTarget_of_used r t l g h11 h29 hCM hXU h33 hFH hL3 : ZInQ.FrozenTarget` — standard axioms.
Fixes during compile: `T5Glue.heegnerForm_level_pos` (namespace), full names for `X0.*` and `Shimura.*` outside the
kernel namespaces, `set_option maxRecDepth 20000` (def `ShimuraReciprocityModFnAt`), `dsimp only at ha hb` in
`cmAlgebraic_of_at`.

## 3. Numerics (VERIFIED, mpmath 40 digits, `scratch/hx-used/num/`)

`search_x.py 8`: among weight-0 ratios `(℘(P1) − ℘(P2))/(℘(P3) − ℘(P2))` of `℘_{L16}`, `L16 = ⟨1/16, τ⟩`, at the points
of `E16[8]` (mod ±), exactly two match `x − 2` (up to the constant −1/4):
  (Ix)  `x(τ) = 2 − 4(℘16(1/32) − ℘16(1/32 + τ/8)) / (℘16(3τ/8) − ℘16(1/32 + τ/8))`, and the same with `τ/8 ↔ 3τ/8`.
`search_x.py 4` (4-torsion only): no match. `search_y.py` (℘'-ratio × ℘-ratio, points ⟨1/32, τ/8⟩): no match for y.
`check_xy.py` (12 random τ): (Ix), its 3τ/8 variant, (IxW) `x(−1/(32τ)) = 2 − 4(℘2(τ/2) − ℘2(τ/2 + 1/16))/(℘2(3/16) − ℘2(τ/2 + 1/16))`,
`℘2 = ℘_{⟨1/2,τ⟩}`, and (Iy) `y = (x³ + 4x + 16 − (x − 2)²(x(−1/(32τ)) + x + 2))/8` (chord through T = (2,−4) and −P,
i.e. the proved Fricke relation `Shimura.etaModelFricke`): worst relative errors 1e-36, 1e-37, 2e-40, 1e-33.
All points in (Ix), (IxW) are canonical for `(E_τ, ⟨1/32⟩)`: 1/32 generates C/C16 in E/C16, `⟨τ/8⟩ = φ(E[8])` in E/C16
(generators ±τ/8, ±3τ/8; both variants agree), `τ/2` = φ(E[2]) in E/C2, `1/16, 3/16 ∈ C/C2`.

## 4. Checks (VERIFIED)

* `scratch/hx-used/Copy.lean`: verbatim copies of `T5Glue.X0ModuliGalois` and `Shimura.ShimuraReciprocityModFn`, `rfl`
  against the kernel: compiles (`copy-output.txt`, needs `set_option maxRecDepth 20000`).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.X0ModuliUsed`: OK.
* `scratch/hx-used/Discharges.lean` → `discharges.txt`: `#discharges: 63 open hypotheses, 1845 theorems checked,
  7 discharge one` — all 7 are existing contributions in the import closure; none is from X0ModuliUsed (expected: the
  used form is weaker than `hX`, so nothing in this file proves an open hypothesis; the fold is manual).
  `frozenTarget_of_used`, `ZInQ.OneProof.frozenTarget`: axioms [propext, Classical.choice, Quot.sound].
* autofold: not applicable (`hX` is a plain argument of `frozenTarget`, not a bundle field; x0-moduli recorded
  `autofold: not a field of the current bundles: ['hX']`).

## 5. Eta route (VERIFIED: `scratch/hx-used/EtaRoute.lean` compiles, `lake env lean`, ~1 min)

`X0EtaRoute.srAt_x (hX : XEtaWeierstrass) (hCM : ShimuraMainCM) : ShimuraReciprocityModFnAt 32 (fun τ => X0.xC τ)`
`X0EtaRoute.srAt_y (hX : XEtaWeierstrass) (hCM : ShimuraMainCM) : ShimuraReciprocityModFnAt 32 (fun τ => X0.yC τ)`
axioms [propext, Classical.choice, Quot.sound]. So the consumers' needs follow from `hCM` and the explicit identity
(Ix) (glue `XEtaWeierstrass`, two forms), with no canonical-model input. Steps (all compiled):
* `latHat_inter_latM`: K ∩ 𝔟̂ = 𝔟 for 𝔟 = κ⁻¹⟨1/M, τ_Q⟩ (via the kernel's `latHat_inter_of_sandwich`).
* `exists_v1`: s⁻¹(1/32) ≡ c'(p₁/32 + q₁τ'), p₁ odd. `exists_vt`: s⁻¹(τ/n) ≡ c'(p/n + qτ'/n), q odd (n = 8, M = 16; n = 2, M = 2).
* `sInv_latM`: κ(s⁻¹⟨1/M, τ_Q⟩) = c'⟨1/M, τ_{Q'}⟩ for dM = 32 (from the kernel's `IdeleLatticeScale` at N = 32).
* `cm_point`: `ShimuraMainCM` at the lattice ⟨1/M, τ_Q⟩ with P' = c'·⟨1/M, τ_{Q'}⟩.
* `wp16_cases`, `wp2_cases`: the orbits of the torsion points under q odd (mod 8).
* `transport16`, `transport2`: σ maps the ℘-ratio of (Ix) at τ_Q to one of the two forms at τ_{Q'}.
* `xC_fricke_wp` (IxW from Ix by the scaling ⟨1/16, −1/(32τ)⟩ = (−1/(16τ))⟨1/2, τ⟩), `yC_formula`
  (8y = x³ + 4x + 16 − (x−2)²(x∘W + x + 2), from the proved `Shimura.etaModelFricke`).
* `x_conj`, `xW_conj`, `y_conj`, `srAt_of_conj` (algebraicity with s = 1; main case: AutExtends, ArtinLift
  (`artinLift_of_abs absArtinSurjectiveQNeg`), `ringClass_of_artin`, `ideleLatticeScale_of ringClassLattice invertibleColon`).

## 6. Glue reduced and in theta form; contributor file (VERIFIED: lake build, standard axioms)

* `X0EtaRoute.xEtaWeierstrassPair_of : XEtaWeierstrass → XEtaWeierstrassPair` (second form from x(γ₃τ) = x(τ),
  γ₃ = [[3,1],[32,11]] ∈ Γ₀(32), kernel `Shimura.etaModelInvariant`, and ⟨1/16, γ₃τ⟩ = (32τ+11)⁻¹⟨1/16, τ⟩).
* `X0EtaRoute.ThetaWeierstrass8` (θ(0;w)/(e^{πiw/4}θ(w/2;w)) = 1 − 2(℘(1/2) − ℘(1/2+w/8))/(℘(3w/8) − ℘(1/2+w/8)),
  ℘ of ⟨1,w⟩) and `xEtaWeierstrass_of_theta : ThetaWeierstrass8 → XEtaWeierstrass` (kernel `Shimura.xC_theta`).
  Numerics: `num/check_theta.py`, 12 random w, worst relative error 5e-41.
* Helper module `ZInQKernel/Contrib/OneProof/X0ModuliUsed/EtaRoute.lean` (copy `scratch/hx-used/EtaRoute.lean`);
  `X0ModuliUsed.lean` §5: `tyzThm35ReadingA_of_eta`, `frozenTarget_of_eta`, `tyzThm35ReadingA_of_theta`,
  `frozenTarget_of_theta`. `lake build ZInQKernel.Contrib.OneProof.X0ModuliUsed`: OK; all axioms standard.
* `discharges.txt` rerun: `63 open hypotheses, 1987 theorems checked, 7 discharge one` (none from this file: no
  theorem here concludes an open hypothesis; `hX` is replaced, not proved).
