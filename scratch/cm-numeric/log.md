# cm-numeric results log

Task cm-numeric, 2026-11-13. Marks: VERIFIED (computed / compiled / read in a named source),
STANDARD, SPECULATIVE, UNVERIFIED. Scripts in this directory; outputs in `*.out`.

## 09:03 start
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

## 09:07 class-7 base point computed (`class7.py`, output `class7.out`; PARI 2.17.2 via cypari2, 400 digits)
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

## 09:09 Lemma 3.21(4) for the pinned class-7 genus point (`lemma321_7.py`, `lemma321_7.out`)
- For e ∈ {7, 15, 23, 31, 39, 47, 55, 71, 79, 87, 95, 103} (12 values): coordinates of `Z(e)`
  recognized (lindep, residual ≤ 1e−300) in the basis `Π √(p*)` of the genus field; β' applied by
  cm-points' `betaOneSign` on each `√D`; then `Z(e)^{β'} + Z(e) = g(e)·T`, `T = (2,−4) = tauG 1`, holds
  in all 12 cases (|diff| < 1e−400; g = 1,1,3,3,2,5,2,7,5,3,4,5). VERIFIED (computed). So pinning
  `Z7` by `[(e+δ²)/4, δ, 1]` makes Lemma 3.21(4) true on this sample, independently of TYZ's text.

## 09:11 Shimura reciprocity direction (`shimura.py`, `shimura.out`)
- Test of cm-points' leaf `CM.ShimuraReciprocity` exactly as stated: `Q'` computed from the lattice
  condition `(⟨1,τ'⟩, ⟨1/32,τ'⟩) = c·𝔭̄·(⟨1,τ⟩, ⟨1/32,τ⟩)`, `𝔭̄ = ⟨p, (−b−√D)/2⟩` (exact arithmetic in
  `ℚ(√D)`, adapted basis of the pair); Frobenius tested as `g(X) ≡ X^p mod (F, p, √D − b)` with
  `F = Π_r (X − x_r) ∈ K[X]` over one Heegner point per class (`B ≡ β mod 64`) and `g ∈ K[X]`
  interpolating `x_r ↦ x(Q'_r)` (recognized in `K` with error 0 at 400 digits).
- D ∈ {−23, −47, −71, −31, −39, −320}, 26 pairs (D, p) (p ≤ 41 split): Frobenius = multiplication by
  `𝔭̄` in all 26; `B' ≡ B (mod 64)` holds automatically; `F mod 𝔓` squarefree; the opposite direction
  (multiplication by `𝔭`) fails for all 24 pairs where `[𝔭]` has order > 2 (orders 3, 4, 5, 7).
  VERIFIED (computed): the direction in `ShimuraReciprocity` (Art(𝔭) : [𝔞] ↦ [𝔭⁻¹𝔞] = [𝔭̄𝔞]) is right,
  including the case `D = −320` (TYZ's order of conductor 4 for n = 5, conductor not prime to N = 32).

## 09:12 TYZSigmaFixesZn and Prop 3.2(1) for class 5 (`sigma5.py`, `degrees5.py`, `*.out`)
- `sigmaClass n` (class of `(3+2√−n)𝒪_K ∩ O4`) contains `p𝒪 ∩ O4`-ideals for primes `p = a² + nb²`,
  `a` odd, `b ≡ 2 (mod 4)` (`a+b√−n ≡ 3a·(3+2√−n) mod 4𝒪_K`; by hand). Prime forms checked to lie in
  the order-2 class `(4,4,21)` for n = 5 (PARI `qfbred`).
- n ∈ {5, 13, 21, 29, 37}, 3 primes each (15 cases): `ShimuraReciprocity` gives
  `ρ(f₀(P_n)) = P_{Q'}` and numerically `P_{Q'} − f₀(P_n) = (0,0) = τ(1)` in all 15 cases, hence
  `ρ(z_n) = z_n` (|diff| = 0 at 400 digits) since `(1−[i])(0,0) = O`. VERIFIED (computed, modulo the
  leaf ShimuraReciprocity checked above). So `TYZSigmaFixesZn` is numerically true; sharper form:
  `Art(sigmaClass) f₀(P_n) = f₀(P_n) + (0,0)`.
- Degrees (n = 5, 13): `x, y` of `f₀(P_n)` have degree 16 = `[H_{n,4}:ℚ]`; `y(z_n)` degree 8 =
  `4h(−4n) = [H'_n:ℚ]`, `x(z_n)` degree 4 = `[H_n:ℚ]` (TYZ Prop 3.2(1),(4)). n = 21: algdep at
  400 digits too short for degree 32 (only lower bounds 27/29 found): precision-limited, not a finding.
- Bug caught and fixed during the run: first version used `(−b'−8√−n)/2` with coordinates in `√D`
  (factor 8 wrong); output regenerated.

## Lemma 3.21(1), class 5 (`lemma321_5.py`, `lemma321_5.out`)
- n ∈ {5, 13, 37} (h(−4n) = 2, g = 1). `β' = c∘u` (c = complex conjugation via ιC, u ∈ Gal(H'_n/K_n)
  with u(i) = −i, nontrivial on H_n; forced by betaOneSign on i, √n, √−n); `z_n^{β'} = (1−[i])·c(u f₀)`,
  `u f₀ = P_{𝔭̄Q}` (ShimuraReciprocity) for 4 primes per n in classes over the nontrivial class of
  Cl(K) (both 𝔭 and 𝔭̄: 8 lifts per n).
- Φ₀ = {1}: `Z^{β'} + Z − τ((1−i)/2) ∈ {O, (0,0)}` in all 24 cases, for both signs `(1∓[i])` in the
  definition of `z_n` (the check does not single out the sign). Φ₀ = {σ} (σ = σ_ϖ², realized by a prime
  a² + nb², a even, b odd): `σ(z_n) − z_n = (0,0)` and the inclusion holds in all 6 cases.
  VERIFIED (computed, modulo the leaves ShimuraReciprocity and the proved cmComplexConj).

## Lean: Class7.lean compiles (`lake env lean scratch/cm-numeric/Class7.lean`, no errors, no warnings)
- Needed `lake build ZInQKernel.Contrib.TYZGenus.Package` first (10092 jobs, built clean).
- Pitfalls fixed: `decide` on `tyzDelta` hits maxRecDepth → `decide +kernel`; generic-order version of
  cm-points' `exists_actsAsArtin4` and the `ActsAsArtinO` lemmas need `set_option maxRecDepth 8000`;
  `IntermediateField.map` membership shows `↑(embed d) y` vs `(embed d) y` (fix: `change`, and state
  `have h1 : ρ (embed d y) = … := hρ ⟨y, hy⟩` by defeq instead of `rw [hρ ⟨y,hy⟩]`).
- `#print axioms` for 12 declarations (incl. `tyzThm35ReadingA_of_pinnedLeaves`,
  `class7GenusPtDefined_of`, `tyzSigmaFixesZn_of`, `exists_actsAsArtinO`, `tyzDelta_spec`):
  `[propext, Classical.choice, Quot.sound]` (`audit-out.txt`). VERIFIED.

## Lean §9: existence of Φ₀ proved (`exists_restrict`, `exists_phi0_elem`, `exists_isPhi0`, `phi0_spec`)
- Every element of Gal(H_e/K_e) extends to Gal(H_{e,4}/K_e) (`AlgHom.liftNormal` to `K_eˢ`, then
  `AlgEquiv.restrictNormal` to `H_{e,4}`, normal by Tau Ceti's `isAbelianGalois_ringClassField`), so
  `Phi0 e` satisfies `IsPhi0` for every `e ≠ 0` (no junk value). Compiles; axioms standard (audit-out.txt).

## Independent review (AI subagent, statements only) and follow-ups
- No blocking finding. Reviewer re-derived the fixed point / form `[(n+δ²)/4, δ, 1]`, δ+64 = Γ₀(32) move
  (τ ↦ τ/(1−32τ)), betaOneSign, and the implication TYZ L2515 ⇒ `Lemma321Seven` (σ with IsBetaOneLift
  agrees with a genuine lift on `L_e(i)`). Notes: `IsPhi0`'s first clause (square in Pic(O4)) is
  stronger than TYZ's (restriction in 2Cl'), so the Lean choices are a nonempty subfamily of TYZ's —
  harmless under "any choice" (supported by TYZ's proof L2547–2554).
- Applied: `Class7GenusPtDefined` docstring now cites L2558 (VERIFIED read: "H_n' = H_n and thus Z(n)
  is already defined over L_n"); `Lemma321Five` docstring records the numerics.
- Finding (VERIFIED read, L1488–1490): TYZ's Proposition `heckeaction5`(1) prints `Q^{1+2ϖ} = Q + τ(1)`
  for every `Q ∈ X_U(ℂ)`; with Shimura reciprocity this is `TYZSigmaShiftsF0`, so that statement is a
  published consequence (now labelled a leaf), matching `sigma5.out`. `TYZSigmaFixesZn` itself is TYZ
  Thm 3.6(1) (L1411–1413, VERIFIED read).

## Sign of [i] in tyzZn settled by a printed identity (`conj5.py`, `conj5.out`)
- TYZ Thm 3.6(1) (L1413) prints `z̄_n = −z_n + τ(1)`. For n ∈ {5, 13, 21, 29, 37, 53, 61}:
  `conj(z) + z = (0,0)` holds for `z = (1 − [i])f₀(P_n)` (cm-points' `tyzZn`) in all 7 cases and fails
  for `(1 + [i])f₀(P_n)` in all 7 (x-coordinate 1, 1/9, …). VERIFIED (computed): cm-points' caveat (5)
  (the `[i]`-sign of `tyzZn`, under `ιC(i) = I`) agrees with a printed TYZ identity.
- Class7.lean recompiled after docstring edits: no errors/warnings, 13 audited declarations standard.
