# h33-sign results log

Task h33-sign (2026-11-15). Target: `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (ZInQKernel/OneProof/TYZSplit.lean),
pending-review flag: the sign of `[i]` in `tyzZn` (z_n for n ≡ 5 mod 8). Source: ~/tyz-src/Period7.tex (Lnnnn).

## Setup
- Build tree copied from ~/dzq-wt/r16-split (same ZInQKernel sources as base 24f97774; no diff). Probe
  `import ZInQKernel.OneProof.TYZSplit` compiles (2m10s). VERIFIED.

## Source reading (VERIFIED, read in Period7.tex)
- L1174: "Fix an identification i_0:(X_0(32),∞)→A" (arbitrary; Aut_Q(A,O) = ±1).
- L1191-1193: f_0 : X_U → X_0(32) natural projection; geometric components of X_U parametrized by Spec Q(i);
  X_U ≅ X_0(32)_{Q(i)} "easy to figure out" — no choice of the square root of −1 in Γ(X_U,O) is printed.
- L1198: f_n = f_0 − f_0∘[i] (n ≡ 5). By L1192 alone `[i]` is defined only up to `[i] ↔ [−i]`.
- L1203-1205: embedding n≡5: √−n ↦ [[−1,1/4],[−4(n+1),1]]; fixed point h: 16(n+1)h² − 8h + 1 = 0 = kernel tyzForm.
- L1245-1252: P_n = [h,1] ∈ X_U(C), h ∈ H the fixed point; z_n = f_n(P_n).
- L1379-1404: τ : C/(1+i)Z[i] → A(C) analytic (C-linear), normalized by τ(1/2)=[0], τ(i/2)=[1/4], τ(1)=[1/16],
  τ((1±i)/2)=[±1/8].
- L1408-1413 Thm 3.6(1): for n ≡ 5: z^{σ_ϖ} = z + τ((1+i)/2), z^{σ_{1+2ϖ}} = z, z̄ = −z + τ(1).
- L1484-1567 (proof of Prop 3.5 = heckeaction5): R,S,T,α,β,γ computed on the cusps [∞]=[∞,1], [0]=[∞,w]
  (w = [[0,1],[−1,0]], det 1: identity component, the component of P_n=[h,1]); equations solved with the
  C-linear τ ("τ((1−i)/2) = ατ(1/2) + τ(1/2)", L1564) give α = −i, β = 1, γ = i (L1566). So TYZ identify
  μ_4 ⊂ Aut_{Q(i)} with μ_4 ⊂ C through the identity component: there `[i]` is complex multiplication by +I.
- L1584: f_n = f_0∘[1−i]. L1636-1649: proof of z̄_n = −z_n + τ(1) via j = [[1,0],[8,−1]], P̄_n = P_n^j.

## Lean: scratch/h33-sign/Sign.lean (imports ZInQKernel.OneProof.TYZSplit) — VERIFIED compiled
- `lake env lean scratch/h33-sign/Sign.lean`: 0 errors; output in Sign.out; axioms of
  `tyzThm33With_iff_of_reading`, `basePt_reading`, `torsion_of_alt_thm36`, `tyzThm33Copy_iff`:
  [propext, Classical.choice, Quot.sound].
- `TYZThm33Copy` = verbatim copy of kernel L157–176 (diff-checked), `Iff.rfl`.
- `TYZThm33With z` (basePt replaced by z); `TYZThm33 ↔ TYZThm33With basePt` is `Iff.rfl`.
- `zAlt n = P + [i]P = iPt (tyzZn n)`; `conj_zAlt`: c(zAlt) = zAlt − τ(1) (from kernel T321.tyzThm36ConjFive_of,
  i.e. Fricke + τ↦τ+1/4, all proved; hypothesis CMAlgebraic only).
- `torsion_of_alt_thm36`: if zAlt satisfied TYZ Thm 3.6(1) (z̄ = −z + τ(1)) then f₀(P_n) is torsion.
- `tyzThm33With_imp`/`_iff`: TYZThm33With depends on z n only up to sign or "both torsion".
- MAIN `tyzThm33With_iff_of_reading (hA : CMAlgebraic) zT h5 h36 h7 : TYZThm33With zT ↔ TYZThm33`
  for any zT of TYZ's shape (±(P∓[i]P) for n≡5, ±f₀(P_n) for n≡7) satisfying TYZ Thm 3.6(1) conj part.
- `basePt_reading`: the kernel's basePt satisfies the hypotheses (non-vacuity).
- Recompiled after adding `iPt_pullback_differential` ((−x)'/(2·I·y) = I·x'/(2y): kernel [i] is CM by +I in the
  normalized sense) and replacing deprecated `if_false`: 0 errors, 0 warnings (Sign.out). VERIFIED.

## Exact q-expansion checks: qexp.py → qexp.out (PARI, exact rational series, O(q^~295)) — VERIFIED computed
- (E) y² − x³ − 4x = 0; (a) x(t+1/4) + x(t) = 0, y(t+1/4) − I·y(t) = 0; (a−) y(t+1/4) + I·y(t) ≠ 0 (val −3);
  (b) Fricke: (x(Wt), y(Wt)) = (2,−4) − (x(t), y(t)) with the eta forms of xC_fricke/yC_fricke.
  These are independent re-checks of identities the kernel proves in Lean (T321.xC_add_quarter,
  yC_add_quarter, Shimura.etaModelFricke).

## Numerics: cm.py → cm.out (200 digits, sample of 20 n ≡ 5 mod 8 squarefree, n ≤ 181) — VERIFIED computed
- (1) TYZ Prop 3.5(2) on the identity component, φ(τ/(1−8τ)) = [i]φ(τ) + τ((1−i)/2), τ((1−i)/2) = (2i,0):
  holds with [i] = +I at 5 random τ, fails with [i] = −I (5/5).
- (2) z̄ + z = (0,0) for z = P − [I]P (kernel tyzZn): 20/20; for z = P + [I]P: 0/20, and z̄ − z = (0,0) 20/20.
- (3) elliptic-log lattice coordinates of tyzZn are ≥ 5e-10 from every rational with denominator ≤ 10^4
  (torsion would give ~1e-190): z_n numerically non-torsion for all 20 n (TYZ's torsion lemma bounds
  A(ℍ'_n)_tors ⊂ A[4], so order ≤ 4 would suffice).

## Normalization checks of TYZThm33 against the source (step 3) — Iso.lean VERIFIED compiled
- `scratch/h33-sign/Iso.lean` (Mathlib only): `lake env lean` 0 errors, 0 warnings (Iso.out empty).
  `tyzA_to_kernelA`/`kernelA_to_tyzA` (2y²=x³+x ≅ y²=x³+4x by (2x,4y)), `iso_comm_i` (commutes with
  (x,y)↦(−x,iy)), `i_preserves_kernelA`, `tyzE_to_curveC` (ny²=x³−x ≅ y²=x³−n²x by (nx,n²y)),
  `fixed5`/`fixed7` (fixed points of TYZ's embeddings L1203-1205 = roots of tyzForm / tyzForm7),
  `disc5`/`disc7` (discriminants −64n, −n).
- Checks (all read in Period7.tex; VERIFIED): scope n≡5,7 ⊂ 5,6,7 (L1167); χ:Cl_n→{±1}, Cl_n=Gal(H_n/K_n)
  (L1263); Φ ⊂ Cl'_n reps, K'_n=K_n for 5,7 (L1263, L1279); P_χ=Σ_{t∈Φ} f_n(P_n)^t χ(t) (L1283);
  χ_{d0,d1} char of K_n(√d1) (n≡5,6) / K_n(√d1*) (n≡7), d1*=(−1)^{(d1−1)/2}d1 (L1304-1305) = radTYZ;
  classes 0<d0≡5,6,7, 0<d1≡1,2,3 (L1303); formula P_χ=ε 2^{h2(n)} 𝓛(d1) 𝒫(d0) in A(H'_n(i))⊗Q (L1306-1308);
  ε=±i iff (d0,d1)≡(5,3) else ±1 (L1309) = EpsTYZ; h2(n)=dim_F2 Cl_n/2Cl_n (L992) = h2G;
  𝒫(n)=2^{−1−ρ(n)}𝓛(n)α_n ∈ A(K_n)^-⊗Q, A(K_n)^-={ᾱ=−α}, 𝒫(n)=0 if 𝓛(n)=0 (L1291-1295) → (Q d, m d, InMinus);
  𝓛(n) def (L338-345): 0 iff ord>1, so ord≥2 ⇒ Q d torsion is implied; 𝓛² = L(E_n,1)/(2^{2k−2−a}Ω) with
  k = #odd primes, a=1 for odd n (L347-349) = lcalSq (2^{2k−3}); Ω_{n,∞}=(2/√n)∫₁^∞dx/√(x³−x) (L350-351) =
  omegaTYZ; 𝓛 defined up to sign (L364) → ∀ℓ, ε chosen after ℓ; E_n: ny²=x³−x (L312) ≅ curveC n;
  A: 2y²=x³+x (L1173) ≅ curveA.
- √d1 resp. √d1* lies in H_n in every case n≡5,7 (d1*≡1 mod 4; for n≡5, d1≡3: K_n(√d1)=K_n(√−d0),
  −d0≡1 mod 4), so IsChiPair is satisfiable for every pair in TYZ's list (STANDARD genus theory).
- P_χ mod torsion is independent of Φ: z^{σ} − z torsion (σ=σ_ϖ², Thm 3.6(1) L1411) — so quantifying ∀φ with
  ε=ε(d0,d1) is TYZ's statement.
- Mathlib's `WeierstrassCurve.LSeries` uses local minimal models (rv-lit.md L75), so model-independent.
