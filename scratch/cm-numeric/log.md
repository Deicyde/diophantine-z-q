# cm-numeric results log

Task cm-numeric, 2026-11-13. Marks: VERIFIED (computed / compiled / read in a named source),
STANDARD, SPECULATIVE, UNVERIFIED. Scripts in this directory; outputs in `*.out`.

## 09:15 start
- No earlier log: fresh start. Branch wip/cm-numeric already contains origin/wip/cm-points
  (`git merge origin/wip/cm-points`: already up to date). Lean sources of cm-points are
  `ZInQKernel/Contrib/TYZGenus/{CM,Package,RingClass,X0}.lean` (not built yet on this worktree).
- `~/tyz-src/Period7.tex` present (read-only). Class-7 data read there (VERIFIED, L1196, L1203–1205):
  for `n ≡ 7 (mod 8)`, `f_n = i_0 : X_0(32) → A` (identity), and `K_n` embeds in `M_2(ℚ)` with
  `√−n ↦ [[δ, 2], [−(n+δ²)/2, −δ]]`, `δ² ≡ −n (mod 128)`; `P_n = [h, 1]`, `h` the fixed point in ℍ.
  For `n ≡ 5` the same recipe with `[[−1, 1/4], [−4(n+1), 1]]` gives `16(n+1)h² − 8h + 1 = 0`,
  i.e. cm-points' `tyzForm n = [16(n+1), −8, 1]` (consistency check, by hand).
- Fixed point for class 7 (by hand): `(δh+2)/(−(n+δ²)/2·h − δ) = h ⇔ (n+δ²)h² + 4δh + 4 = 0`, i.e.
  `h` is the CM point of the primitive form `[(n+δ²)/4, δ, 1]`, disc `δ² − (n+δ²) = −n`, and
  `32 ∣ (n+δ²)/4` since `128 ∣ n+δ²`. So `z_n = f_n(P_n)` is the Heegner point of
  `[(n+δ²)/4, δ, 1]` on `X_0(32) = A` (class `[𝔞] = [⟨A,(−δ+√−n)/2⟩]` = principal, since
  `[A, δ, 1] ~ [1, −δ, A]`).
- Class-7 genus point (VERIFIED, L1268, L1316–1318, L1260): `σ = 1`, `H'_n = H_n`, `Cl'_n = Cl_n`,
  so `Φ_0 = 2Cl_n` and `Z(n) = Σ_{t ∈ 2Cl_n} z_n^t ∈ A(H_n)`.

## 09:50 class-7 base point computed (`class7.py`, output `class7.out`; PARI 2.17.2 via cypari2, 400 digits)
- For n ∈ {7, 15, 23, 31, 39, 47, 55, 71}: `z_n` = image under x0-32's eta model `(xC, yC)` of
  `τ = (−δ + i√n)/(2A)`, `A = (n+δ²)/4`, δ least in [0,128) with δ² ≡ −n (mod 128). VERIFIED (computed):
  - the point is on `y² = x³ + 4x` (residual ≤ 1e−402);
  - δ and δ+64 give the same point; δ ↦ −δ (mod 128) gives the complex-conjugate point (so TYZ's
    "an integer δ" is well defined up to complex conjugation; `Z(n)` changes to its conjugate);
  - `Π (X − x)` over the 2h Heegner points (`h = h(−n)`, all classes, `B ≡ ±δ (mod 64)`) has integer
    coefficients and is irreducible over ℚ; its field (polredabs) is the Hilbert class field of
    `ℚ(√−n)` (PARI `bnrclassfield`, `nfisisom`): TYZ Prop 3.2(3) `H'_n = H_n` for all 8 values;
  - `Z(n) = Σ_{t∈2Cl_n} z_n^t` (sum over the classes in 2Cl with the same `B mod 64`) has coordinates of
    degree `2h/g(n) = [L_n:ℚ]`, i.e. lies in the genus field (TYZ L2458 for class 7).
  - Example: n = 7: `z_7 = ((−1+√−7)/2, (3+√−7)/2)`; n = 23: `Z(23)` has `9x² − 7x + 2 = 0`.

## 10:05 Lemma 3.21(4) for the pinned class-7 genus point (`lemma321_7.py`, `lemma321_7.out`)
- For e ∈ {7, 15, 23, 31, 39, 47, 55, 71, 79, 87, 95, 103} (12 values): coordinates of `Z(e)`
  recognized (lindep, residual ≤ 1e−300) in the basis `Π √(p*)` of the genus field; β' applied by
  cm-points' `betaOneSign` on each `√D`; then `Z(e)^{β'} + Z(e) = g(e)·T`, `T = (2,−4) = tauG 1`, holds
  in all 12 cases (|diff| < 1e−400; g = 1,1,3,3,2,5,2,7,5,3,4,5). VERIFIED (computed). So pinning
  `Z7` by `[(e+δ²)/4, δ, 1]` makes Lemma 3.21(4) true on this sample, independently of TYZ's text.
