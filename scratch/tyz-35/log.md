# tyz-35 results log

Target: `Thm35First ℓ tyzZ` for every `IsTYZLcal ℓ` (cm-bridge `Bridge.lean`, verbatim copy of
`Package.Thm35First`), `tyzZ` = cm-numeric/cm-bridge's pinned genus points.

## 2026-11-13 22:40 setup
- Merged origin/wip/cm-bridge: already contained in base (Already up to date). VERIFIED.
- `scratch/tyz-35/Thm35.lean`: §0–§9 = cm-bridge `Bridge.lean` lines 1–652 verbatim (namespace
  `CMBridge → TYZ35`, import of `ShimuraFricke` dropped: unused in §0–§9).

## What `Thm35First ℓ tyzZ` asks (VERIFIED by reading the Lean definitions)
For squarefree `n ≡ 5 (mod 8)`: ∃ `ε` in TYZ's classes (`±i` on (5,3), `±1` on (5,1),(7,1),(7,3),
only for `d₀d₁ ∣ n`) with: `ℓ n = 0 → P(n)` torsion, `P = Pseq ℓ ε tyzZ` = TYZ's recursion
`P(d) = Z(d) − Σ_{d₁∣d, d₁>1, d₁≡1,3 (8)} ε(d/d₁,d₁) ℓ(d₁) P(d/d₁)` with
`Z(e) = Σ_{ρ∈Φ₀(e)} ρ(z_e)` (e ≡ 5; `z_e = (1−[i])·Heegner pt of [16(e+1),−8,1]`, Φ₀ chosen lifts of
`2Cl_e`), `Z(e) = Σ_{c∈2Cl_e} liftMax(c)(z_e)` (e ≡ 7; `z_e` = Heegner pt of `[(e+δ²)/4, δ, 1]`).
Only classes 5, 7 occur in the recursion; ℓ is only read on classes 1, 3 (squarefree) and at `n`.
`ℓ n = 0` ⇔ no continuation of `L(E_n,s)` of order ≤ 1 at 1 (`IsTYZLcal`).
This is TYZ Theorem 3.5, first assertion (`P(n)` represents `𝒫(n)`, and `𝒫(n) = 0` if `𝓛(n) = 0`),
for the pinned points; TYZ prove it (L2343–2380) from Theorem 3.3 by the character formula and induction.

## 2026-11-13 23:40 leaf + glue drafted
- Leaf `TYZThm33Pinned ℓ` (TYZ Thm 3.3 + Lemma 3.14 for the pinned CM points; ∃ Q, m, ε global,
  `P_χ` over lift families `f`, characters `χ_T = Π_{q∈T} χ_q`, `T = primes of gmap(n,d₁)`).
- Glue `thm35First_of_thm33 : ℓ 1 = 1 → TYZThm33Pinned ℓ → Thm35First ℓ tyzZ` drafted (character
  formula, genus product formula for n ≡ 3 (4), divisor/subset bijection, level identity, induction).
- Python/PARI: `~/pyenv/bin/python` does not exist on this host and cypari2 is not in the uv cache
  (offline) → no Heegner-point numerics possible here. Pure-Python check instead:
  `convention.py` → `convention.out`: the leaf's χ_{d₀,d₁} (Jacobi `(m/gmap)`) equals tyz-t1's
  `χ_{d₁} ↔ K(√d₁)` for n ≡ 5, equals the character of the unramified `K(√±d₁)` for n ≡ 7, is a class
  invariant, and `χ_T = χ_{T^c}` for n ≡ 7: 0 mismatches over 26 values of n (VERIFIED computed).
- First `lake build ...RingClassBridge` killed by the 10-min background limit; restarted.
