# Review of route B1 (h-b1.md): tame specialization in place of the integral model

Status: adversarial review (task rv-h-b1, 2026-11-11) of `docs/research/h-b1.md` on branch
`wip/h-b1` (commit d7d8d78f; below: *the note*), before it enters the trust statement of H.
"N5 Lxxx" refers to the frozen 11/5 manuscript `diophantine_zq.tex` (sha256 cb1148cd…, as in
`SHA256SUMS`). Scripts, outputs and the work log are in `scratch/rv-h-b1/`.

Marks:

- **VERIFIED**: checked here, against the manuscript or by a computation in `scratch/rv-h-b1/`
  (`rv_checks.py`, output `rv_checks.output.txt`; rerun of the note's script
  `b1_checks_rerun.py`, output `b1_checks_rerun.output.txt`).
- **STANDARD**: a published theorem, with a reference. No source outside the repository could be
  read in this task, so every locator is unread here, as in the note.
- **SPECULATIVE**: an assessment.

## Verdict

| Item | Verdict |
| --- | --- |
| Counterexample F1 (`y² = p·j(27j+16)`) | **Holds**, and shows a little more than the note says (§1) |
| Prop. TS (specialization from SGA 1) | **Holds as stated**; two cosmetic additions (§2) |
| Lemma NV (no vertical ramification, `p ≥ 5`) | **Holds as stated**. Every step checked (§3). Step 3 deserves a fuller sentence, and step 2 needs less than the note claims |
| M1–M10 (hypotheses for `Y₃ → P¹_j`) | **Hold**. M3 and M9 are now fully VERIFIED; M9 holds for every elliptic point, not just the three exhibited (§4) |
| Lemma PR (i) | **Holds as stated** (§5) |
| Lemma PR (ii) (Morita by SGA 7; Serre–Tate at `v ∤ 3`, including `v | 2`) | **Holds as stated** (§5) |
| Replacement table (§5 of the note) | **Holds after repairs**: one wrong locator, two omitted downstream uses (§6) |
| L814 never used b11 | **Confirmed** (§6) |
| `Y₃ = Sh_{K₃}` vs the moduli problem over `ℚ` | **Holds (STANDARD)**, once four citations are made explicit (§7) |

**Does B1 remove b11 from H's justification? Yes.** After the repairs below, N5 L441-530 and
everything downstream that used the integral model rest on published theorems (SGA 1, SGA 7,
Serre–Tate, Shimura–Deligne canonical models, the PEL moduli interpretation, Baba–Granath and
Lin–Yang) together with the reviewed short arguments Prop. TS and Lemma NV. No step needs the
integral model. The remaining risk is in the citations, not in the mathematics (SPECULATIVE):
the locators listed in the note's §6.2 are still unread.

**Most serious issue (not a gap).** Lemma NV takes its rational structure on `Y₃` from the
canonical model (Shimura reciprocity, Hecke action over `ℚ`). Lemma PR(ii) takes it from the
moduli problem (a `K`-point gives `(A, ι, λ, η)` over `K`). N5 takes it from Baba–Granath's `j`
on `X₆/W`. All three must be the same `ℚ`-structure. This is classical (Shimura 1967: the
moduli of QM abelian surfaces give the canonical model). Before B1 it was buried in b11's
sentence at N5 L476-477; after B1 it must be cited explicitly (§7).

## 1. The counterexample F1

- VERIFIED (rerun section D; `rv_checks.py` R5): for `p ∈ {331, 337, 347, 349, 353}` the fibre
  of `y² = p·j(27j+16)` at `j = 1` is `ℚ(√(43p))`, ramified at `p`, and the branch points `0`
  and `−16/27` stay distinct mod `p`.
- What it shows:
  - F1 is the quadratic twist by `p` of `y² = j(27j+16)`. That cover's `j = 1` fibre is `ℚ(√43)`
    (disc 172), which is unramified at `p`.
  - So hypotheses (a)–(c) of Beckmann (tame, branch points distinct mod `p`, branch points
    rational) do not imply (d) (no vertical ramification). Hypothesis (d) depends on the
    `ℚ`-model, not on the geometric cover. This is exactly what the note claims.
- What it does not show: anything about `Y₃`. Vertical ramification is a property of the given
  model. For `Y₃` it is ruled out by Lemma NV, or by the integral model that B1 avoids. The
  note's wording ("false in general") is accurate.
- Additional point (VERIFIED, R5). The residue fields of F1 over its branch points are `ℚ`,
  which is unramified at `p`. So unramified branch fibres, which is all that NV's step 2 gives,
  do not exclude vertical ramification by themselves. In F1, `I₀ = I_{−16/27}` is the whole
  group `ℤ/2`, and this is the configuration that NV's step 4 rules out for `Y₃`. So step 4 is
  essential, not decoration. It is worth adding this remark to the note.

## 2. Prop. TS

Checked line by line (log §5). **Holds as stated.**

- **Purity.**
  - `Z` is finite over `P¹_R` because `R = ℤ_(p)^{sh}` is excellent.
  - Being normal of dimension 2 over a regular base, `Z` is flat. So "unramified at the
    codimension-one points off `D`" upgrades to étale there.
  - Zariski–Nagata purity then gives that `Z` is étale off `D`.
  - Both points are worth one clause in the note (cosmetic).
- **Case 1.** The section misses `D`, so the pullback is finite étale over the strictly
  henselian `R`. It therefore splits, and `K_{j₀}` embeds in `k_p`.
- **Case 2.**
  - The section factors through `O^{sh}_{P_i}`. After Lemma NV, `D_i` is the only branch
    through `P_i`.
  - By Abhyankar, the local model is `⊔ O^{sh}[z^{1/e_i}]`.
  - With `z ↦ p^m w` and `w` an `e_i`-th power in `R^*`, the fibre is a product of copies of
    `k_p(p^{1/(e_i/g)})`, where `g = gcd(e_i, m)`.
- **Independent test on the `W`-layer (VERIFIED, R7).**
  - Elkies' model, as checked in `docs/research/rv-h-cm.md` §2, is
    `ℚ(X₆) = ℚ(j)(√j, √(−(27j+16)))`, with constants `−1` and `3`.
  - On 30 samples `(j₀, p)` with `5 ≤ p < 400`, ramification of `p` in the actual biquadratic
    fibre field agrees in every case with the Prop. TS prediction (ramified iff the contact
    multiplicity is odd, `e = 2` on this layer). The sample covers contact with `0`, with
    `−16/27` and with `∞`, and generic `j₀`.
  - The constants are `{−1, 3}`, so `X₆ → P¹_j` has no vertical ramification at any `p ≥ 5`.
    This is NV's conclusion on the `W`-quotient, obtained from Elkies' conductor computation
    rather than from NV.

## 3. Lemma NV

**Holds as stated.** Every step was checked (log §5). Points of detail:

1. **Tameness.**
   - Tameness along `V(p)` needs the residue extension of `F̄_p(j)` to be separable. That field
     is imperfect, but the degree of the extension divides `|Γ_M|`, which divides 144, so it is
     prime to `p`.
2. **Branch fibres.**
   - Shimura curve and level:
     - `G = B^*` with `B = (2,−3)` of discriminant 6;
     - `O = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`, maximal (VERIFIED, R1: `det trd(e_r e_s) = −36`, and
       `B` is ramified exactly at 2 and 3);
     - level `K₃ = ker(Ô^* → (O/3O)^*)`, neat (VERIFIED, R6: no non-central elliptic power lies
       in `ℚ^* K₃`).
   - Reduction to `[τ, 1]`: `G(𝔸_f) = G(ℚ)_+ K₀`, by strong approximation for `B¹` and
     `nrd(K₀) = ℤ̂^*`. So every point over `b_i` is a `Γ'`-translate of some `[τ, 1]`.
   - Reciprocity:
     - `art(s)` fixes `[h, 1]` when `r(s) ∈ K₃`;
     - `r(s) ∈ ∏_{ℓ≠3} O_{E,ℓ}^* ⊂ K₃` provided `ℚ(x) ∩ O` has conductor prime to `ℓ`;
     - so `E(y₀)` lies in the ray class field of conductor `3^∞` of `E`;
     - the convention `r = id` or conjugation does not matter, as the note says.
   - **Strengthening (VERIFIED, R2).** A complete enumeration of the elliptic elements of the
     normalizer (primitive `x ∈ O` with `nrd x | 6` and finite order mod `ℚ^*`) gives exactly
     the types:

     | `(|trd|, nrd)` | `ℚ(x) ∩ O` | `W`-image |
     | --- | --- | --- |
     | `(0,1)` | `ℤ[i]` | 1 |
     | `(1,1)` | `ℤ[ζ₃]` | 1 |
     | `(2,2)` | `ℤ[i]` (order 4) | `w₂` |
     | `(3,3)` | `ℤ[ζ₃]` (order 6) | `w₃` |
     | `(0,3)` | `ℤ[ζ₃]`, not `ℤ[√−3]` | `w₃` |
     | `(0,6)` | `ℤ[√−6]` | `w₆` |

     The type `(0,2)` is absent: `ℚ(√−2)` does not embed in `B`, because 3 splits in it. So
     every elliptic CM order is maximal, with discriminant `−3`, `−4` or `−24`. Step 2 needs
     only "conductor prime to `p`", and this holds for every elliptic point whatever the
     labelling of the branch values.
3. **Local analysis.** The note's sentence "`D_i ≅ Spec R` is already strictly henselian, so
   `c = 1`" is correct but compressed. Suggested replacement:
   - The closure of `Q_i` is `Spec A'`, where `A'` is local and finite over `R` with fraction
     field `k(Q_i) = k_p` (by step 2).
   - So `A'` is strictly henselian and unibranch, and its branch at `𝔓` has residue degree 1
     over `k_p`.
   - In the Kummer model `(O^{sh}[z^{1/n}, p^{1/n}])^H`, that degree equals `[I_𝔓 : I_{Q_i}]`.
     There is a unique branch over `z = 0`, and `I_{Q_i}` is the image of `μ_n × 1`.
   - The existence of `Q_i ⊂ 𝔓` and of a vertical prime `q ⊂ 𝔓` follows from going-down for
     the flat map `Z → P¹_R`. And `I_q ⊂ I_𝔓` holds because `σ ≡ id mod q` implies
     `σ ≡ id mod 𝔓`.
4. **Conclusion.**
   - `|I_V|` divides `gcd(6, 2) = 2`. A generator `g` is conjugate to `g_∞³ ↦ σ_∞` and to
     `g_{−16/27} ↦ σ_{−16/27}`.
   - `W` is abelian. Images of inertia are inertia: the horizontal divisors have residue
     characteristic 0, and `k_p(X₆) = ℚ(X₆) ⊗ k_p` is a field because `X₆` is geometrically
     connected.
   - Hence `σ_∞ = σ_{−16/27}`. This contradicts `g(X₆) = 0`, which forces three distinct
     nontrivial generators with product 1 (VERIFIED, R3: Riemann–Hurwitz gives `g = 0` for
     `X₆` and `g = 4` for a component of `Y₃`, and `χ(O¹) = −1/3 = 4·χ(2,4,6)`).
   - The `W`-images `w₂, w₃, w₆` at `j = 0, ∞, −16/27` agree with R2 and with `rv-h-cm` §1.3.
   - **Robustness.** Any pair of branch points gives the contradiction. At the order-4 point,
     `g₀² ↦ 1`, so pairing it with either of the other two points also works. The argument
     does not depend on the Baba–Granath labelling.

## 4. Hypotheses M1–M10

- **M3** (VERIFIED, R4):
  - `|(O/3O)^*| = 72` and `|(O/3O)^1| = 36`;
  - the image of `ℤ̂^*` is `{±1}`;
  - `|Γ'| = 4·72/2 = 144 = 2⁴3²`;
  - two geometric components (`π₀ = (ℤ/3)^*`), each of degree 72 over `P¹_j` and 18 over `X₆`.

  Tameness for all `p ≥ 5` follows. The local normalizer index 2 is STANDARD (Vignéras).
- **M2/M8.**
  - `Y₃` is `ℚ`-irreducible, with constant field `ℚ(√−3)`, so `M = ℚ(Y₃)` and
    `Gal(M/ℚ(j))` is the image of `Γ'`.
  - `Y₃ → P¹_j` is étale over `j₀`, so the fibre product with `P¹_u` is normal near `u`, and
    its fibre over `u` is the fibre of `Y₃` over `j₀`.
  - The residue fields are Galois over `ℚ` and all equal. So N5's `K` is `K_{j₀}`. Holds.
- **M5, M7** (VERIFIED, rerun section A, identical output).
- **M4** rests on Baba–Granath and Lin–Yang, as before. B1 adds nothing there.

## 5. Lemma PR

- **(i) Holds.**
  - At most one of `F(u), G(u), H(u)` is divisible by `p ≥ 17`: the resultants are supported
    on `{2,3,5}` and the leading coefficients on `{7, 11, 13}`.
  - The contact multiplicities are `2v` at `0`, `6w` at `∞` and `2w` at `−16/27`.
  - `J(∞)` and `J(∞) + 16/27` are `p`-units.
  - The 30-case sample (rerun section E) agrees. It checks the case analysis, not Prop. TS
    itself; R7 above tests Prop. TS on the `W`-layer with real fields.
- **(ii) Holds.**
  - Potentially good reduction:
    - `ι(O) ⊂ End_K(A)` acts on the semistable Néron model over `K'` (SGA 7 IX 3.6), hence on
      `X(T) ⊗ ℚ`;
    - `B` is a division algebra, so that space has `ℚ`-dimension divisible by 4;
    - `t ≤ 2` then forces `t = 0`.
  - Good reduction:
    - `A[3] ⊂ A(K)` gives `ρ₃(I_v) ⊂ 1 + 3M₄(ℤ₃)`, which is torsion-free;
    - by Serre–Tate Thm 2, `ρ₃(I_v)` is finite, hence trivial;
    - Néron–Ogg–Shafarevich then gives good reduction.

    This is valid at every `v ∤ 3`, **including `v | 2`**, because `ℓ = 3` is prime to the
    residue characteristic. There is no conflict with the bad (Čerednik–Drinfeld) reduction of
    the curve at 2 and 3: that concerns the curve, not the abelian surface at a point with
    rational 3-torsion.

## 6. Replacement table: repairs

VERIFIED by reading N5 and by a grep of N5 L1-1200 for "integral model", "proper model",
"good reduction", "stable model", "X_{35}", "universal abelian", "smooth projective",
"semistable" and "potentially good" (log §3).

- **Repair T1 (locator).** "Every conjugate has good reduction" at primes outside `T` is at N5
  **L557-558**, not L563-566. L563-566 is the Milne paragraph on Hodge endomorphisms. The task
  text inherited the same locator.
- **Repair T2 (completeness).** Two downstream uses are missing from the table:
  - L753: `r_ℓ` is unramified outside `T ∪ {ℓ}`, since `A` has good reduction there;
  - L781: `A` has good reduction at `p ∉ T ∪ {3,5}`, used for the Frobenius comparison.

  Both use only the conclusion of L529-530 at primes outside `T ∋ 3`. Lemma PR(ii) covers them.
  The note's sentence "nothing downstream of L530 uses the integral model" is true in substance
  but should name these lines.
- **L848-849** (`p > R`). Such `p` may lie in `supp M_S(u) ⊂ T`, where `K` can ramify. Lemma
  PR(ii) still applies, because it covers all `v ∤ 3`, ramified or not. The table entry is
  correct.
- **L814 never used b11: confirmed.** It adjoins `A[3]` (`A[5]` at `p = 3`) and invokes Raynaud's
  criterion (Silverberg–Zarhin Thm 3.5) for semistability. No model enters.
- The other rows (L441-478 deleted, L480-482 deleted, L482-507 → M1-M5 + NV + TS,
  L509-523 → M7/M8 + PR(i), L524-528, L529-530) were checked against the text and hold.

## 7. The identification of N5's `Y₃` with the moduli problem over `ℚ`

- N5 defines the level `K₃` (L423-424) and calls `Y₃` "the level-three curve with all its
  determinant components" (L434-435). Its only identification of `Y₃` with the full-three
  moduli problem is b11's sentence at L476-477.
- B1 deletes L441-478, so the identification must be cited directly. It holds, from the
  following STANDARD inputs, and the note's §4(ii) step 1 should list all of them:
  1. **Canonical model = moduli scheme.** The moduli of QM abelian surfaces with level
     structure is the canonical model `Sh_{K}(B^*, H^±)` over `ℚ` (Shimura, Ann. of Math. 85
     (1967); Deligne, Bourbaki 389, §4–6; Milne, *Introduction to Shimura varieties*, §8 and
     §14). There are no extra copies, since `ker¹(ℚ, B^*) = 1`.
  2. **The polarization is determined.** For a maximal order and `μ² = −6`, a QM surface
     `(A, ι)` has a unique principal polarization with Rosati involution `μ^{-1} x̄ μ` (Rotger,
     J. reine angew. Math. 2003, and Trans. AMS 2004; locators unread). So `λ` adds no data.
     VERIFIED (R1) that N5's form `Trd(μ^{-1} x ȳ)` has the matrix printed at N5 L414-416 and
     determinant 1.
  3. **The level structure.**
     - A `K₃`-structure is an `O`-linear `η: O/3O ≅ A[3]`. This uses that `T_ℓ A` is free of
       rank one over `O_ℓ`: N5 L454-459 at 3, and at `ℓ ∤ 6` because `O_ℓ = M₂(ℤ_ℓ)`.
     - Compatibility with the Weil pairing up to a scalar is automatic:
       `ψ(xu, yu) = nrd(u)·ψ(x, y)`.
  4. **Representability.** The moduli scheme is fine, by rigidity of level 3 (Serre's lemma;
     also N5 L466-470). So a `K`-point gives `(A, ι, λ, η)` over `K`, and the fibre of the
     universal family over `x` is N5's "fibre `A/K`".
- The same `ℚ`-structure is the one carrying the Hecke action of `Γ'` (Deligne) and
  Baba–Granath's `j` (they work on the QM moduli). This is the "most serious issue" above. It
  is a citation task, not a gap (SPECULATIVE).

## 8. Repairs to the note before it enters H's trust statement

1. §5 table: change L563-566 to L557-558 (T1). Add L753 and L781 (T2).
2. §3 step 3: replace the "`c = 1`" sentence with the argument in §3.3 above. §1.2: add
   "excellent, so finite" and "normal of dimension 2, so flat".
3. M9: cite the complete enumeration (`rv_checks.py` R2). State that NV needs only conductor
   prime to `p`.
4. Summary item 1: add that F1 also shows that unramified branch fibres are not enough, so the
   `W`-step of NV is needed (R5).
5. §4(ii) step 1: list inputs 1–4 of §7 above, including the explicit statement that NV, PR(ii)
   and Baba–Granath use one and the same `ℚ`-structure.
6. Optional: record the `W`-layer check (Elkies constants `−1`, `3`, which give no vertical
   ramification at `p ≥ 5`, and R7) as independent support for NV's conclusion.

None of these changes the argument.

## 9. Computations

- `scratch/rv-h-b1/b1_checks_rerun.py`: the note's `b1_checks.py`, verbatim. Its output is
  byte-identical to the saved `b1_checks.output.txt` (0.7 s).
- `scratch/rv-h-b1/rv_checks.py` (1.3 s). Sections:
  - R1: maximality of `O`, `μ² = −6`, N5's polarization matrix;
  - R2: complete list of elliptic normalizer types, their CM orders and `W`-images;
  - R3: Euler characteristics and Riemann–Hurwitz;
  - R4: `|Γ'|`, components and degrees;
  - R5: what F1 shows;
  - R6: neatness;
  - R7: Prop. TS on the `W`-layer with real fields (30 samples).
