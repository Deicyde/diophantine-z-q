# el-global: global soundness through a label on `E(K₀)`

Branch `wip/el-global`, from `origin/main` 8718d41d. No Lean was run, and no file under `ZInQKernel/`,
`blueprint/` or another note was edited. Scripts are in `scratch/el-global/`, and the step log is
`scratch/el-global/log.md`. PARI 2.17 via cypari2. Computations ran one at a time, each under 10 minutes.

Marks:
- **VERIFIED**: proved here (from the inputs named), checked against the Lean sources, or computed exactly
  (script named).
- **STANDARD**: a published theorem (reference given).
- **SPECULATIVE**: a heuristic, or an unproved step.

## 0. Verdict

**The global door does not open. Chance that a label gadget eliminates CR₃: very low.**

The proposal was to give the pole predicate a label `L ∈ E(K₀)` as an extra witness, tied to the data by a
correspondence `Z`. Soundness would then come from the integer behind `L` being the same at every place, and
completeness might be free because the honest prover already holds a suitable label.

The first step, a global Theorem G, **goes through** for every label gadget whose completeness is free in a
precise sense (Theorem GG, §2). The mechanism is simple. The bad event is invisible to the labels: a bad
rational point can be built whose labels are *exactly* those of an honest point, or differ from them by a
multiple `δu` of a fixed integer `δ`. So whatever global property the honest label has (a Mordell–Weil
sieve, a descent class, a depth), the bad point has it too.

| Case of the honest rule | Outcome | Status |
| --- | --- | --- |
| Labels and the other witnesses algebraic over the data (finite correspondence; this includes reusing a test label, the only budget-free option) | bad **rational** witnesses exist, unconditionally (GG-B) | VERIFIED as a proof from STANDARD inputs (CDJLZ, Faltings, Serre–Lang) and E3 |
| Labels algebraic over the data labels, other witnesses from rationally connected (RC) fibres | bad rational witnesses exist under Colliot-Thélène's conjecture; unconditionally if the slice is ℚ-rational (GG-C) | VERIFIED as a proof from STANDARD inputs and the conjecture |
| Labels depending on `t` or `q` | the dependence is a twist of a constant isogeny; it either kills completeness for all `n` outside a thin set (rs-global C3 in general form), or reduces to the rows above, or leaves a genus ≥ 1 curve per instance (L4) | VERIFIED as a proof |
| Labels free over the data, RC fibres | the label can be frozen at a global point: bad points with rational data and rational labels exist locally (GG-A), and globally under CT | VERIFIED as a proof |
| Residual: non-RC witness fibres; honest rule valid only for sparse `κ`; isolated Mordell–Lang points | completeness needs, per instance, a rational point on a non-RC variety (a genus ≥ 1 curve in the column form). This is rv-barrier N1/N4, CR₃'s kind | SPECULATIVE whether any such statement is provable |

Further findings:
1. **The proposal's own label is dead.** The deep `κ` of `exists_common_smul_mem_Ek` is already a data
   label (`[h − κ]P₀ = [κ]P₀` is a test point), so reusing it makes `L` an algebraic function of the data
   (`δ = 1`). Replacing `κ` by `κ' = 1` keeps every equation of any such gadget satisfied and makes the
   data bad at every odd contact prime `p > 324`: `v_p(B) = −11` in 30/30 cases (E3). The depth property
   "`D_κ` contains every prime of `β`" is invisible to any algebraic `Z`.
2. **A Mordell–Weil sieve cannot be uniform in `p`** (Lemma MW). Local conditions on `L` at a fixed finite
   set of places are a congruence condition on the index `k` modulo a fixed `M`. Depth at a bad `π` only
   asks `m_π ∣ k`, and the two are compatible whenever `gcd(m_π, M) = 1`. That happens for a positive
   density of `π` (E2: 59% for `M = 2`, 28% for `M = 210`). So such soundness falls under rv-barrier N3.
3. **The only global information beyond the adelic closure is the height** (Remark H). `ℤ` is discrete in
   `Ẑ × ℝ`, so `L ∈ ℤP₀ + T` carries one more fact than its closure `ẐP₀ + T`: `ĥ(L) = k²ĥ(P₀)`. Using it
   needs an upper bound for `ĥ(L)` in terms of the data, which is a hypothesis of SixContactMin's kind, not
   a replacement for CR₃. Bad data can carry labels of any height.
4. **The hint in the brief needs a correction.** The closure of `⟨P₀⟩` in `E(K₀,π)` is open of finite index
   only when `K₀,π = ℚ_p` (`p` split). For inert `p`, `E₁(K₀,π) ≅ ℤ_p²` while the closure has `ℤ_p`-rank 1.
   For split `p`, the closure in `E(K₀,π) × E(K₀,π')` is a `ℤ_p`-line. The proof below does not use this
   closure. It uses slices on which the labels are global points.
5. **Budget.** The only budget-free variant (reusing a test label) is case GG-B with `δ = 1`, which is dead.
   Every other variant costs about 8.3 million variables per extra label (cr3-map-needs finding 7). A label
   that is *not* algebraic over the data (for example `[κ²]P₀`) also needs a new multiplication certificate,
   whose completeness uses PC itself (rs-global §1.3), so it is circular.

## 1. Setting

Notation as in cr3-map-needs and el-gadget: `B = R/Θ²`, `R = R₀a²`, `a = 1 − R₀q²`, `R₀ = η·2730⁶·F(t)`,
`Θ = Tr W⁻¹`, `W = Π_j(1 + R·C_j²)`, `C_j = D_j/F(t)`.

- `A = Res_{K₀/ℚ} E` is an abelian surface over ℚ with `A(ℚ) = E(K₀) = ℤP₀ + E[2]` (`mordellWeilE`,
  `index_two_E`). `A'` is the Zariski closure of `A(ℚ)`. Since `A'(ℚ) = A(ℚ)`, labels range over `A'`.
- **Data.** These are `t`, `q`, `η`, and the data labels `[n]P₀`, `[h]P₀`, `[s₀]P₀`, `[h − κ]P₀`,
  `[s₀ − κn]P₀`. The tests (`SixLocalTests.lean:40`) are `D₁ = w([h]P₀)`, `D₂ = w([s₀]P₀)`,
  `D₃ = w([h−κ]P₀)*`, `D₄ = w([s₀−κn]P₀)*`, `D₅ = z([s₀]P₀)/z([h]P₀) − t` and
  `D₆ = (z([s₀−κn]P₀)/z([h−κ]P₀))* − t`, with `w = 1/x` and `z = −x/y`. Honest values are `t = n`,
  `h = 2κ`, `s₀ = 2κn`, with `κ` deep. **For fixed `n`, every data label is a morphism of `Q = [κ]P₀`**:
  `[2]Q`, `[2n]Q`, `Q`, `[n]Q`.
- **A label gadget** is a ℚ-variety `X ⊂ Y × A^s × 𝔸^w` (with `s` extra labels and `w` further
  witnesses), and `Φ'(y) :⇔ X_y(ℚ) ≠ ∅`. A correspondence `Z ⊂ Y × A^s` is part of the equations of `X`.
  Since `E(K₀)` is *all* of `A(ℚ)`, "`L ∈ E(K₀)`" is no constraint beyond rationality. Mordell–Weil
  enters only through the structure of the set of rational points.
- **(H-mult).** For each honest `n`, the honest rule supplies witnesses for every `κ` in a finite-index
  coset of `κ₀(n)ℤ`, at a fixed `q₀`. Here `κ₀(n)` is the deep modulus. A "free" rule based on depth
  satisfies this, since every multiple of a deep `κ` is deep. `TestCompleteness` uses one `κ`, but any
  `κ ≠ 0` passes `hcomp`.
- **Soundness notions** at `p > p₀`: LUS (rv-barrier); *label-global* (no bad `ℚ_p`-point whose labels lie
  in `A(ℚ)`); *MW-adelic* (labels from one element of `ẐP₀ + T`); *global* (no bad rational point).

**(P11), VERIFIED (E1).** On a slice with fixed genuine labels and fixed `q`, `B` has a pole of order 11
along `t = c` for every contact `c`: 30/30 cases. rv-barrier C5 had checked this with arbitrary `D_j`.

## 2. Theorem GG (global Theorem G for label gadgets)

Let `Φ'` be a label gadget and assume (P11).

- **GG-A (labels free, RC fibres; local).** Suppose `X → Y × A'^s` has RC generic fibre (R1 of
  rv-barrier). Then for honest data labels `lab₀` and labels `L₀ ∈ A(ℚ)^s` outside a proper Zariski-closed
  set, there are `x ∈ X(ℚ_p)` over `Bad_p`, for a positive density of `p`, whose data (including `t`) and
  labels are *rational*. Only the remaining witnesses are `p`-adic. The globality of `L` adds nothing.
- **GG-B (algebraic completeness; global, unconditional).** Assume (H-mult). Suppose the honest labels and
  witnesses lie in a fixed correspondence `R ⊂ Y × A^s × 𝔸^w` that is generically finite over `Y`. Then
  `Φ'` holds at bad rational data. The bad data are honest except that `κ` is replaced by
  `κ' = κ₀j₀ + δu`, where `δ` is the degree of an isogeny determined by `R`.
- **GG-C (RC completeness; global under Colliot-Thélène's conjecture).** Suppose the label correspondence
  involves only the data labels (`Z ⊂ A'^m × A'^s`) and `X → 𝔸²_{t,q} × Z` has RC generic fibre. Then,
  under CT's conjecture, `Φ'` holds at bad rational data. These data agree with an honest instance in every
  label, and agree to any prescribed precision at any finite set of places other than the bad prime `p`;
  in particular `t` is real-close to `n`, so the `Close` conjunct still holds. The conclusion is
  unconditional when the slice is ℚ-rational.
- **GG-D (labels depending on `t`, `q`).** Assume (H-mult). If the honest labels are algebraic over
  `(t, q, lab)`, then one of three things holds:
  - completeness fails for all `n` outside a thin set;
  - the gadget reduces, on finitely many covers `T_i → 𝔸²_{t,q}`, to the cases GG-B/GG-C;
  - completeness needs, per instance, a rational point on a curve of genus ≥ 1 (the fibre of some `T_i`
    over `t = n`).

**Scope.** Together, GG-A–GG-D cover every label gadget whose honest witnesses are algebraic, or come from
RC fibres, over the label-augmented data. What is left (§4) is exactly rv-barrier N1/N4: per-instance
rational points on non-RC varieties.

## 3. Proofs

**L1 (rigidity; STANDARD).** A rational map from a rational variety to an abelian variety is constant (Milne,
*Abelian varieties*, Cor. 3.9). Hence `A'(ℚ(t, q)) = A'(ℚ)`.

**L2 (cyclic Mordell–Lang; STANDARD plus VERIFIED step).** If `A'` is connected, a proper closed subset of
`A'` contains only finitely many points of `ℤP₀`.
- By Faltings (Mordell–Lang), the intersection is a finite union of cosets of subgroups.
- An infinite coset `a + mℤP₀` has Zariski closure a coset of a finite-index closed subgroup, which is all
  of `A'`.
- If `A'` is disconnected, run every argument below on the coset `n ↦ n + e`, where `e` is the order of
  `P₀` in `A'/A'⁰`.

**L3 (the κ-direction dichotomy).** Fix honest `n` and `q₀`. Let `W_n ⊂ A' × A^s × 𝔸^w` be the closure of
the honest points `(Q, L_h, w_h)` over `Ω_n = (finite-index coset of κ₀(n)ℤ)·P₀`. Under GG-B,
`W_n → A'` is generically finite. Discard the components that carry only finitely many honest points:
- non-dominant components (L2);
- components that are not geometrically irreducible, whose rational points lie in a proper closed subset.

The remaining components are normal finite covers of `A'` after normalization. By the theorem of
Corvaja–Demeio–Javanpeykh–Lombardo–Zannier (Compositio Math. 158 (2022) 2109–2155, Thm. 1.3 as recalled
here: for ramified covers `Y_i → A` and a Zariski-dense finitely generated `Ω ⊂ A(k)`, some finite-index
coset of `Ω` misses every `π_i(Y_i(k))`; STANDARD, statement to be checked against the paper before it is
cited in a blueprint), some finite-index coset of `Ω_n` has all its honest lifts on **unramified**
components. An étale cover of an abelian variety with a rational point is an abelian variety (Serre–Lang;
Mumford, *Abelian varieties*, §18). So such a component `W°` is an abelian variety, with
`ψ = φ + c : W° → A'`, where `φ` is an isogeny of degree `δ` and `c ∈ A'(ℚ)`.

**Isogeny lifting (VERIFIED).**
- Let `φ'` be the isogeny with `φ ∘ φ' = [δ]`. Then `[δ]A'(ℚ) ⊂ φ(W°(ℚ))`.
- If `w₀ ∈ W°(ℚ)` lies over `Q₀ = [κ₀j₀]P₀`, then `w₀ + φ'([u]P₀)` lies over `Q₀ + [δu]P₀`, that is, over
  `κ' = κ₀j₀ + δu`.
- Take an odd contact prime `p > 324` of `n` and `π ∣ p` with `m_π ∤ δ`. This holds for all but finitely
  many `π`, because each `m` has finitely many `π` with `m_π = m` (they divide the denominator of
  `x([m]P₀)`). Take `u ∈ 1 + m_πℤ`. Then `m_π ∤ κ'`, so `[κ']P₀ ∉ E₁(π)`.
- The points `w₀ + φ'([1 + m_πv]P₀)` form a coset of an infinite cyclic group. They are Zariski dense in
  `W°`, so they meet the open set `V'°` on which the witness formula satisfies the equations and guards of
  `X`. `V'°` is open, and it contains the honest points.
- At such a point the data are `(t = n, κ', h = 2κ', s₀ = 2κ'n, q₀)`, every label is a genuine multiple of
  `P₀`, and the product label `[κ'n]P₀` is a true product. A test with `v_π(D_j) ≤ 0` gives
  `v_p(RC_j²) ≤ −v_p(F) < 0`, hence `v_p(Θ) ≥ v_p(F)` and `v_p(B) = v_p(R) − 2v_p(Θ)`, which is negative
  and odd (`v_p(R)` is odd). E3 confirms `v_p(B) = −11` in 30/30 cases with `κ' = 1`.

This proves **GG-B**. ∎

**GG-C.**
- Freeze an honest `(lab₀, L₀) ∈ Z(ℚ)` such that its slice `S = 𝔸²_{t,q} × {(lab₀, L₀)}` satisfies (P11)
  and meets the RC locus. Both are open conditions, nonempty by E1, and honest points are Zariski dense in
  their closure. Because `Z` does not involve `(t, q)`, all of `S` lies over `Z`.
- `X_S → S` is an RC fibration over a rational base. Its smooth proper model `X̃_S` is RC
  (Graber–Harris–Starr, JAMS 16 (2003), Cor. 1.3; STANDARD), and it contains the honest rational point
  `x_h`.
- Lemma G on `S` (rv-barrier R2) gives `x_p ∈ X_S(ℚ_p)` over a bad *rational* base point, for a positive
  density of `p`: take a transversal `t`-line through a general point of `{t = c}`, a GHS section over a
  number field `K`, and the value at `t = c + p` for `p` split in `K`. This already proves **GG-A**,
  applied to the slice `{lab₀} × {L₀}`.
- `Br X̃_S / Br ℚ` is finite. Each class extends over `ℤ_p` for `p` outside a finite set, so it vanishes on
  `X̃_S(ℚ_p)` (`Br ℤ_p = 0`) (Colliot-Thélène–Skorobogatov, *The Brauer–Grothendieck group*, 2021;
  STANDARD). Hence the adelic point (`x_h` at `v ≠ p`, `x_p` at `p`) lies in `X̃_S(𝔸)^Br`.
- Colliot-Thélène's conjecture (CT, "Points rationnels sur les fibrations", Bolyai Soc. Math. Stud. 12,
  2003) gives a rational point near `x_p` at `p`, which is still bad (an open condition), and near `x_h`
  elsewhere. If `X_S` is ℚ-rational, weak approximation is immediate. ∎

This is the step that rv-barrier R5 could not take. There the base contained an abelian factor. Here the
labels are frozen at global points, so the base `S` is rational.

**L4, the twist lemma (GG-D).** Apply L3 over the generic point of `(t, q)`. Under (H-mult), the components
that carry honest labels are torsors over `ℚ(t, q)` whose structure map is `φ + c`, where:
- `φ` is constant, because a finite subgroup scheme of `A'[N]` over `ℚ(t, q)` is constant (the Galois
  action on `A'[N]` factors through `Gal(ℚ̄/ℚ)`);
- `c ∈ A'(ℚ)` (L1).

So the only `(t, q)`-dependence is a twist class `ξ ∈ H¹(ℚ(t, q), ker φ)`. A rational point over `Q`
exists iff `ξ(t, q) = −δ_φ(Q − c)`, where `δ_φ(A'(ℚ))` is finite and unramified outside a fixed set `S_A`
(weak Mordell–Weil; STANDARD). There are three cases.
- **`ξ` unramified.** Then `ξ` is constant (`𝔸²` is geometrically simply connected in characteristic 0), `Z` does not involve
  `(t, q)`, and GG-B/GG-C apply.
- **`ξ` ramified only along vertical lines `t = c'`.** Then `ξ(n)` is ramified at every large `p` with
  `v_p(n − c')` odd, so completeness fails for every `n` outside a thin set. This is rs-global C3 in general
  form, and it covers every "abscissa class" or formal-depth relation of the shape `x(L) = f(t, …)`.
- **Otherwise.** The honest `(n, q)` lie in the images of `T_i(ℚ)` for finitely many covers
  `T_i → 𝔸²_{t,q}` on which `ξ` becomes trivial. On a ℚ-rational `T_i` where `{t = c}` pulls back with an
  odd component on a smooth model, the GG-B/GG-C slice argument runs on `T_i`. Example: `ξ = χ_{(t−c)q}`
  with `q = (t − c)r²` gives `T_i = 𝔸²_{t,r}`, where the line `t = c` has multiplicity 1. Every other
  `T_i` is LUS along that contact. Theorem G in column form then makes its fibre over `t = n` a curve of
  genus ≥ 1. ∎

**Lemma MW (VERIFIED, with E2).**
- Suppose a soundness argument uses `L = [k]P₀ + T` only through local conditions at the bad prime `p` and
  at a fixed finite set of auxiliary places. The auxiliary conditions restrict `k` to a nonempty union of
  classes modulo a fixed `M`.
- Depth at `π ∣ p` (`v_π(x(L)) = −2(v_p(k) + r_π)`, checked 10/10 in E2) needs `m_π ∣ k` and a power of
  `p`. By the Chinese remainder theorem this is compatible with the auxiliary conditions whenever
  `gcd(m_π, M) = 1`.
- The set of such `π` has positive density. For odd `ℓ ∣ M` this follows from Chebotarev in `K₀(E[ℓ])`,
  which gives a positive density of `π` with `ℓ ∤ #E(F_π)` (STANDARD). For `ℓ = 2` it is the
  odd-order density of Jones–Rouse type: empirically 0.589 here.
- Such soundness therefore excludes the bad event only at a Chebotarev set of primes (rv-barrier N3). ∎

**Remark H (SPECULATIVE only in its last clause).** The closure of `A(ℚ)` in `A(𝔸_f)` is `ẐP₀ + T`, and
`ℤ ⊂ Ẑ × ℝ` is discrete. So the one global fact about the integer behind `L` that no finite set of finite
places sees is archimedean: `ĥ(L) = k²ĥ(P₀)`. Depth `m_π ∣ k` at a bad prime gives `ĥ(L) ≥ m_π²ĥ(P₀)`, and
`m_π` is typically of size `p`. A contradiction would need `ĥ(L) ≪ h(data)`, but the adversary chooses the
labels in the data and hence their height. Bounding the height of the scalar from its support is the role
of SixContactMin. So this route trades CR₃ for a height hypothesis of the existing kind, and (last clause)
no version of it that removes CR₃ is in sight.

## 4. Where the proof breaks: the residual gadget

The proof of Theorem GG fails only in the following situations:
- **(D1)** the witnesses over the label-augmented data have non-RC fibres;
- **(D2)** (H-mult) fails, so the honest rule works only for a sparse, non-coset set of `κ`. By CDJLZ the
  honest points then lie on a ramified cover of `A'`, and in practice on finitely many curves of genus ≥ 2
  or a non-dense set (Faltings);
- **(D3)** the honest label is one of the isolated points of a Mordell–Lang intersection `Z_y ∩ A(ℚ)^s`.
  The coset part of such an intersection is free and is handled by slicing (GG-A/GG-C).

In each case completeness needs, per instance, a rational point on a variety that is not RC and is not
produced by any algebraic rule. In column form (L4, last case) it is a point on a genus ≥ 1 curve
`T_{i,n}`. The gadget that the break specifies is therefore the one already tested:
- el-cert M1 and el-gadget E4 give the genus-1 quartic `h² = m(mΘ₀² − R₀(1 − R₀q²)²)`;
- el-e4 shows that the Hasse principle fails for it (74 of 240 locally soluble toy quartics are
  nontrivial in Ш), and that no published theorem covers it.

The label adds only isogeny-type (unramified, rank-one) structure to such curves. By L3 and L4 that
structure never separates bad data from honest data. So the residual is rv-barrier N1/N4 with nothing new,
and it is worse than CR₃, which at least has Tian–Yuan–Zhang and Gross–Zagier behind it.

## 5. Experiments

| Exp | Script | Input | Outcome | Decides |
| --- | --- | --- | --- | --- |
| E1 | `e1_slice_pole.py` | 5 genuine label pairs `(n, κ)` × 6 contacts; exact `K₀` arithmetic, Laurent series in `t − c`; `q = 3/7` | `v(Θ) = 6` and `v(B) = −11` in 30/30 cases | (P11) with genuine labels, needed for every slice argument. VERIFIED |
| E2 | `e2_mw_sieve.py` | all 2258 primes `π` of `K₀` of norm `< 20000` (not over 2, 7); `m_π` by PARI | `gcd(m_π, M) = 1` for 58.8% (`M = 2`), 75.3% (3), 44.6% (6), 30.7% (30), 28.5% (210); depth identity 10/10 (`p`-adic, `p ≤ 47`) | Lemma MW: a sieve obstruction is not uniform in `p`. VERIFIED |
| E3 | `e3_nondeep_bad.py` | `t = n ∈ [271, 332]`, `κ' = 1`, `h = 2`, `s₀ = 2n`, `q = 0`; the first 30 pairs `(n, p)` with `p > 324` and `v_p(F(n))` odd; `p`-adic, precision `p^400` | `v_p(B) = −11` in 30/30 cases | data honest except for depth are bad: the κ-deformation of GG-B. VERIFIED |

A first run of E1 with the pairs `(−7, 3)` and `(11, 1)` hit the 600 s cap after 19 cases, all `−11`. Those
pairs were replaced by `(−3, 1)` and `(4, 1)`.

## 6. Relation to the earlier barriers

- rv-barrier §3 lists N2 (global soundness) as not excluded. **Theorem GG excludes N2 for label
  gadgets:** unconditionally when completeness is algebraic, and under Colliot-Thélène's conjecture when it
  is RC. What survives of N2 is the case where completeness is itself a per-instance point problem on a
  non-RC variety, which is N1/N4.
- R5 (global paragraph) failed because the base contains abelian factors. GG-C avoids this: the labels are
  rational points, so they can be frozen, and the slice is rational.
- el-cert L-B (no algebraic witness) is the case `δ = 1` of GG-B. GG-B extends it to labels that are
  multivalued algebraic functions of the data, via CDJLZ and isogeny lifting.
- rs-global C3 (finite Kummer image) is the second case of L4.

**Recommended wording:** "No label on `E(K₀)` gives the pole predicate a sound and freely complete variant.
If the honest label and witnesses are algebraic over the data, or the witnesses come from rationally
connected fibres (assuming Colliot-Thélène's conjecture), bad rational witnesses exist with the same labels
as an honest instance, up to an isogeny shift. Any surviving design needs per-instance rational points on
non-rationally-connected varieties, which is CR₃'s kind."

## Scripts (`scratch/el-global/`)

- `e1_slice_pole.py`: E1, the pole order of `B` along `t = c` with genuine labels (exact, standard library).
- `e2_mw_sieve.py`: E2, the reduction orders `m_π` and the depth identity (PARI).
- `e3_nondeep_bad.py`: E3, the badness of the κ-deformation at primes `p > 324` (PARI, `p`-adic).
- `log.md`: definitions, statements, proofs and outcomes, step by step.
