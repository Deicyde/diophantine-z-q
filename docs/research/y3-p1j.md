# y3-p1j: the leaf `Y3ToP1j`, the N-action on the integral model, and the moduli row's R2 re-sourced to `Y₃ → P¹_j`

Task y3-p1j, 2026-11-17. Branch wip/y3-p1j, started at the tip of y3-route-a (6558e2ffa). Lean:
`ZInQKernel/Contrib/OneProof/Y3ToP1j.lean` (namespace `Y3P1j`) and `ZInQKernel/Contrib/OneProof/Y3ToP1jDescent.lean`
(the descent glue, proved). Scratch: `scratch/y3-p1j/` (log, computations,
axioms, `#discharges`, grep evidence, kinds rows).

Marks: **VERIFIED** means compiled, computed, or read in the source. **STANDARD** means a published argument with a
reference. **UNVERIFIED** means a locator recalled without network access. **ON THE SPOT** means an argument that
is in neither the manuscript nor a print read here.

## 0. Verdict

1. **Leaf `Y3ToP1j` (done).** It is stated as the manuscript states it at L425-440, using the identification of
   the normalizer quotient cited at L420-422. Kind: consequence. Flag: ELLIOT.
   * The statement is in Lean and every-witness: every fine witness `(Y, Φ)` of the level-3 moduli problem has a
     `π : Y → P¹` such that:
     * (quotient) the `ℚ̄`-fibres of `π` are the `N`-orbits, i.e. the `Aut(𝒪)`-twist classes of the underlying
       QM pairs;
     * (branch values) the CM points by `ℤ[i]`, `ℤ[ζ₃]` and `ℤ[√−6]` are exactly the fibres over `0`, `∞` and
       `−16/27`;
     * (quotient map) `π` is onto `P¹(ℚ̄)`;
     * (degree) every `ℚ̄`-fibre has at most `324` points.
   * Rating: **not printed form** (§2).
2. **(b) The N-action on the integral model (proved in Lean, standard axioms).** It is built from
   `Y3FullThreeRepZ30` alone.
   * The global generators of `N` act on the moduli problem over every base:
     * twists by `α ∈ Aut 𝒪`, which by Skolem–Noether are the normalizer of `𝒪` in `B^×` modulo `ℚ^×`;
     * right multiplication of the three-marking by `u ∈ 𝒪^×`.
   * By the uniqueness in the universal property, they act by automorphisms of `𝒴/ℤ[1/30]`, with the
     composition laws of the operations.
   * `−1` acts trivially (L430-434).
   * Summary theorem: `Y3P1j.action_of_z30`.
3. **(c) "The quotient is `P¹_j`" has a source.** The manuscript cites Baba–Granath and Lin–Yang at L420-422.
   * The quotient of `Y₃` by `N/(𝔸_f^×K₃)` is the normalizer quotient `V/W` (`V = X₆`). That step is implicit at
     L434-436 and is STANDARD for canonical models.
   * `V/W ≅ P¹_ℚ` is Baba–Granath Thm 2.1 and Lemma 3.1; locators.md grades this YES.
   * The coordinate `j` is fixed by its values at the three CM points: a Möbius normalization, already glue in the
     kernel.
   * Known caveats are listed in §6. There is no gap of the "stop here" kind.
4. **(d) R2 is re-sourced in Lean: R2 of the moduli row now follows from `Y3ToP1j`.**
   * `hauptmodulOfX6_of_y3ToP1j : Y3ToP1j → ToP1DescendsAlongSurj → PairsLift → HauptmodulOfX6`.
   * `r1r2W_of_y3ToP1j` builds the row `LeafAdopt.R1R2fpRepW` with R2 from `Y3ToP1j` instead of from Baba–Granath
     on `X₆`. `PairsLift` comes from the proved `mumfordTorsionAlgClosed_proof`.
   * The descent of a map to `P¹` along `Y₃ → X₆` was stated as glue (`ToP1DescendsAlongSurj`) and is
     **proved** in `ZInQKernel/Contrib/OneProof/Y3ToP1jDescent.lean` (`toP1DescendsAlongSurj_proof`, standard
     axioms). So `hauptmodulOfX6_of_y3ToP1j' : Y3ToP1j → HauptmodulOfX6` and `r1r2W_of_y3ToP1j'` rest on
     `Y3ToP1j` alone, with no new glue.
   * **Neither `x6CoarseModuliIdeal` nor `elkiesX6StarEveryIdeal` can be dropped on this base** (grep over the
     whole tree, §5.2). Re-sourcing R2 removes only the Baba–Granath use (through `babaGranathRationalAb`). Other
     readers remain, here and also on the cm-branch base (§5.2):
     * `x6CoarseModuliIdeal` still supplies the row's `X₆` witness (`X6Props`, `CoarseX6OfFineW`) and
       González–Rotger's `R5ptProps`;
     * `elkiesX6StarEveryIdeal` still supplies Elkies' model to `x6ConicModel` (→ NoCM) and to
       `HeckeSqrtBranchAny` (sgr-direct, the Lemma NV route).
   * No top field is discharged, so there is no autofold fold: no spec, no dry run. `#discharges` lists nothing for
     the new file, and the GLUE count is unchanged at 4/27 on 31 (§5.3).
5. **Consistency (proved).** `y3ToP1jAt_noDeg_of_row`: the row's `X₆` data already give every clause of
   `Y3ToP1jAt` except the degree bound, with `π = π₆ ∘ fY`. Against the leaves the chain already uses, the only
   new content of `Y3ToP1j` is the fibre bound `≤ 324` and the every-witness form.

## 1. Manuscript check

One row per manuscript step formalized or relied on (diophantine_zq.tex). Verdicts:
* **OK**: checked, correct as written;
* **gap filled**: the text omits a step, supplied here or elsewhere in the tree;
* **error**: something is wrong as written;
* **unverified**: depends on an unread print.

| tex lines | step | verdict | reason |
|---|---|---|---|
| L411-412 | `B = (2,−3)`, `𝒪 = ℤ[i,(1+j)/2]`, `μ = 2j+ij` | OK | `𝒪` closed under products in the basis `(1, i, (1+j)/2, (i+ij)/2)` (exact check, `units_mod3.py`, `gram.py`); `nrd μ = 6`, `μ² = −6` (VERIFIED, `gram.txt`) |
| L412-418 | Gram matrix of `Trd(μ⁻¹x ȳ)` and determinant one | OK | computed with exact rationals: equal to the printed matrix with the printed sign, determinant `1` (VERIFIED, `scratch/y3-p1j/gram.txt`) |
| L419-420 | Riemann form convention of Lin–Yang eq. (3), Lemma 3; Rosati `a ↦ μ⁻¹āμ` | unverified | Lin–Yang not read (no network); the Rosati formula is the standard one for `Trd(μ⁻¹xȳ)` (STANDARD) |
| L420-422 | normalizer quotient is `P¹_j`, branch values `0, ∞, −16/27`, indices `4,6,2` [BG, LY] | OK with caveats (§6 items 1-2) | BG Thm 2.1 and Lemma 3.1 give `V/W ≅ P¹_ℚ`, read by locators.md: YES. The indices are right as orbifold orders, and so as ramification indices of the torsion-free cover `Y₃ → P¹_j` (h-trust A2, loc-fix note); they are not the indices of `X₆ → X₆/W` (locators.md: NO as written). The numerical `j`-normalization is not in BG Thm 2.1/Lemma 3.1: a Möbius normalization (kernel glue `babaGranathX6'_of_rational`). The bibliography cites the BG 2005 preprint, not read. |
| L423-424 | `K₀ = 𝒪̂^×`, `K₃ = ker(K₀ → (𝒪/3𝒪)^×)` | OK | definitions |
| L425-426 | `N` normalizes `K₃` | OK | at `p ≠ 3`, `K₃,p = 𝒪_p^×`; at `p = 3`, `B₃` is a division algebra, `𝒪₃` its valuation ring, and `3𝒪₃ = Π²𝒪₃` is a two-sided ideal stable under conjugation by `B₃^×` (STANDARD) |
| L426-429 | local normalizers; `\|N/(𝔸_f^×K₀)\| = 4` | OK | split `p`: normalizer of `M₂(ℤ_p)` is `ℚ_p^× GL₂(ℤ_p)`; `p = 2, 3`: normalizer is `B_p^×`, quotient by `ℚ_p^×𝒪_p^×` of order 2 (parity of `v(nrd)`) (STANDARD; Vignéras LNM 800 Ch. II, UNVERIFIED, as in h-trust A3) |
| L430-434 | central finite ideles act trivially | OK | `z = q·w`, `q ∈ ℚ^×` with `w ∈ ℤ̂^×`, sign of `q` chosen so `w₃ ≡ 1 mod 3`, so `w ∈ K₃`. For the one central class not in `K₃` (image `−1 ∈ (𝒪/3𝒪)^×`), the moduli form is proved in Lean on the integral model: `sigmaR_neg_one` (`ι(−1) = [−1]` identifies `η(·(−1))` with `η`) |
| L434-436 | `Y₃` with all determinant components admits `N/(𝔸_f^×K₃)`, quotient `P¹_j` | gap filled (implicit standard step) | the text says "Consequently". It uses that `Sh_{K₃}/(N/𝔸_f^×K₃) = Sh_N` (the normalizer quotient), standard for finite right-translation quotients of canonical models (Deligne 1979 §2.7, UNVERIFIED, as h-trust A3 cites). In Lean the action is the moduli action: twists and `rightMul` act on `Y₃` by the proved `heckeOfFine_proof` and on the integral model by `action_of_z30` (proved here). The orbit description in the leaf's quotient clause is the moduli dictionary for that action (ON THE SPOT as a written argument, §2). |
| L437-440 | `deg(Y₃ → P¹_j) ≤ 4\|(𝒪/3𝒪)^×\| ≤ 4·81 = 324` | OK (not sharp) | `\|(𝒪/3𝒪)^×\| = 72` (exact count, VERIFIED, `units_mod3.txt`; also h-trust A3), so `4·72 = 288 ≤ 324`. The true degree is `\|N/(𝔸_f^×K₃)\| = 4·72/2 = 144`: the central `(ℤ/3)^× = {±1}` lies in `𝔸_f^×K₃`, and a generic point has trivial stabilizer. Also `2` components × `72` = `144` (`π₀ = (ℤ/3)^×`; per component `[𝒪¹/±1 : Γ(3)] = 18` times `\|W\| = 4`; 36 of the 72 units have norm `1 mod 3`, VERIFIED) |
| L443-446 | Buzzard Thm 2.1 / Cor. 2.3 at `V₁(5)` over `ℤ[1/30]` | unverified | relied on through y3-route-a's leaf `Y3FullThreeRepZ30`; Buzzard locator UNVERIFIED |
| L447-449 | full five-marking: finite étale cover | OK | standard (level structure on a finite étale group scheme) |
| L449-462 | `Isom_𝒪(𝒪/3𝒪, A[3])` finite étale, nonempty on geometric fibres | OK | lattice argument checked: for `L` an `𝒪₃`-lattice in `V ≅ B₃` and `x ∈ L` of least valuation, `yx⁻¹ ∈ 𝒪₃` for all `y ∈ L` (`𝒪₃` is the valuation ring), so `L = 𝒪₃x`. The alternative "check in characteristic zero and spread" is also fine |
| L464-472 | `X₃₅` smooth projective; `G₅` acts freely, via torsion-freeness of `1 + 3M₄(ℤ₃)` | OK; Known issue (polarization, from y3-route-a) | prime-order check: `g = 1 + 3^k A`, `A ≢ 0`. For `p ≠ 3`, `g^p ≡ 1 + p3^kA mod 3^{k+1}`. For `p = 3`, `g³ ≡ 1 + 3^{k+1}A mod 3^{k+2}` (needs `k ≥ 1`). Both contradict `g^p = 1`. "Polarized automorphism" (L467) presupposes the canonical polarization (y3-route-a §0 item 2) |
| L472-477 | free quotient `X₃₅/G₅`, descent, represents the full-three problem; generic fibre `Y₃` | OK (relied on, as the leaf `Y3FullThreeRepZ30`) | free quotient by a finite group is finite étale (SGA 1, STANDARD); the generic-fibre statement is proved in Lean by y3-route-a (`y3RepresentableQ_of_z30`) |
| L477-478 | five-marking contributes no degree factor | OK | the quotient represents the full-three problem exactly |
| L481-483 | normalizer action extends to the smooth proper model | not formalized here | uses uniqueness of the stable model; outside this task (the integral action proved here is on the `ℤ[1/30]` model of y3-route-a, by representability, not by stable models) |
| L531-536 | "Baba–Granath's polarized equivalence relation gives `V_ℤ = V/W`" (the use of R2 downstream) | OK as used | this is the fibre clause of `Y3ToP1jAt` / `R2X6PropsIff` |

## 2. The leaf

```lean
def Y3ToP1jAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  (∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar), Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some 0) ∧
      (HasCM3 P.q ↔ π.val (K := Qbar) y.left = OnePoint.infty) ∧
      (HasCM24 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))) ∧
  (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = t) ∧
  (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite ∧
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.ncard ≤ 324)

def Y3ToP1j : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → ∃ π : ToP1 Y.left, Y3ToP1jAt Y Φ π
```

All the objects are the kernel's genuine ones:
* `R1fpProps`: the fine moduli clause list of `Y₃`;
* `QML3`, `QMIso`, `QMStr.twist`, `HasCM*`;
* `ToP1`: a map to `P¹` by charts.

**Against the text.**
* The leaf states the quotient, the branch values and the degree of L420-440.
* The **action** of `N/(𝔸_f^×K₃)` is not a clause, for two reasons:
  * its generators are already automorphisms of `Y`: twists by `Aut 𝒪` and `rightMul` by `𝒪^×`. On every fine
    witness this is the proved glue `heckeOfFine_proof`; on the integral model it is `action_of_z30`;
  * the quotient clause characterizes the orbits.
* The **orbit dictionary** says that the `N`-orbit of `(A, ι, η)` on `ℚ̄`-points is the set of
  `(A, ι∘α, η')` up to isomorphism (all `α ∈ Aut 𝒪`, all three-markings `η'`). Its ingredients:
  * `N = N_{B^×}(𝒪)·𝔸_f^×·K₀`: each class of `N/𝔸_f^×K₀ ≅ (ℤ/2)²` contains a global normalizer element, an
    element of `𝒪` of reduced norm `±2, ±3, ±6`, e.g. the kernel's `X6ALIdeal.mu`;
  * `Aut 𝒪 = N_{B^×}(𝒪)/ℚ^×` (Skolem–Noether);
  * `K₀/K₃ = (𝒪/3𝒪)^×` acts simply transitively on the three-markings of a fixed `(A, ι)`.

  This is **ON THE SPOT** as a written argument. Each ingredient is STANDARD (Shimura–Deligne moduli
  interpretation of the Hecke action). Nothing in Lean is built on the dictionary: it only explains why the
  leaf's quotient clause is the manuscript's "quotient by `N/(𝔸_f^×K₃)`".
* **Branch values** are biconditional. "Branch values `0, ∞, −16/27`" (L421-422) is read, as the kernel reads
  Baba–Granath §3.1 (UNVERIFIED), as follows: each of `CM(−4)`, `CM(−3)`, `CM(−24)` is exactly the fibre over its
  value.
* The **indices** `4, 6, 2` are not in the leaf; the chain gets them elsewhere (h-trust A2, glue).
* **Degree.** The leaf states the consequence used on points: every `ℚ̄`-fibre has at most `324` points. A finite
  morphism of degree `d` between curves over `ℚ` has geometric fibres of at most `d` points. The bound is true
  with room to spare: the degree is `144` (§1).

**Rating: not printed form.** No print states this for the level-3 curve. The manuscript derives it from:
* the adelic computation L425-436;
* the identification of the normalizer quotient cited at L420-422 (Baba–Granath for `V/W ≅ P¹`; the
  `j`-normalization is a Möbius choice).

So the row is kind **consequence**, flag ELLIOT, and it counts GLUE in both columns.

**Consistency (proved, `y3ToP1jAt_noDeg_of_row`).** From the row `R1R2fpRepW`, `π := π₆ ∘ fY` satisfies the
quotient, branch-value and onto clauses on the row's witness. So the leaf is no stronger than the leaves the chain
already assumes, except for the degree bound and the every-witness form. Passing between witnesses is the
kernel's `compare_iso`.

## 3. (b) The N-action from the universal property of `Y3FullThreeRepZ30` (all proved)

* `opP α u : QMAbSchemeP S → QMAbSchemeP S` for every base `S`, with `ι' = ι∘α` and `η'(a) = η(α(a·u))`. All
  clauses are proved, including the printed level clause `LevelPrint`: injectivity mod `3𝒪` and surjectivity
  onto `A_s(k)[3]` at every geometric point.
  * `rightMulP u = opP (refl) u` is `K₀` acting through `𝒪^× → (𝒪/3𝒪)^×` on the marking.
  * `twistP α = opP α 1` is the global normalizer acting by `Ad(b)`.
* `qmFamFibreP_op`: the operations commute with pullback (they change only `ι` and `η`).
* **Yoneda.**
  * `sigmaR`, `sigmaT`: the unique `σ : 𝒴 → 𝒴` over `ℤ[1/30]` with `σ^*𝒜 ≅ T𝒜`. `𝒴` is locally noetherian,
    being smooth over `ℤ[1/30]` (`isLocallyNoetherian_of_smooth`).
  * Composition laws: `sigmaR_comp : σ_u ≫ σ_v = σ_{vu}`, `sigmaT_comp : σ_α ≫ σ_β = σ_{β.trans α}`.
  * Identities: `sigmaR_one`, `sigmaT_refl`.
  * Automorphisms: `isoR`, `isoT`.
* **Central element** `sigmaR_neg_one : σ_{−1} = 𝟙`, through `ι(−1)`.
* `action_of_z30 : Y3FullThreeRepZ30 → ∃ 𝒴 𝒜 σR σT, …` packages all of this.

Kept inside the leaf: the identification of this action with the manuscript's adelic action of `N` (the orbit
dictionary of §2), and the quotient. Mathlib 4.35 has no quotients of schemes by finite groups, so the quotient
`Y₃/(N/𝔸_f^×K₃)` cannot be formed in Lean; the leaf states its properties on points instead. The Atkin–Lehner
part as isogenies `A ↦ A/A[I_m]` is not needed here: on objects, `Aut 𝒪`-twists give the same classes as the
ideal quotients (the kernel's `X6ALIdeal.alIdeal_iff_alTwist`, from the textbook fields).

Pitfall (for later tasks): elaborating `rightMulP` or `twistP` directly as a structure instance of `QMAbSchemeNL`
loops in `whnf`, even with every proof field `sorry`. The combined `opP` with `α` a variable elaborates at once,
and the special cases are definitions on top of it.

## 4. (c) Source of "the quotient is `P¹_j`"

The manuscript has a source, and its argument is in three steps:
1. `Y₃ = Sh_{K₃}`. Quotient by `N/(𝔸_f^×K₃)` = `Sh_N`, the normalizer quotient. This is implicit at L434-436
   ("Consequently"). It is STANDARD for canonical models: right translation by an element normalizing `K` is
   defined over `ℚ`, and the quotient by a finite group of such translations is the canonical model at the larger
   level. Reference: Deligne 1979 §2.7, UNVERIFIED, as h-trust A3 cites it.
2. `Sh_N = V/W`, with `V = Sh_{K₀} = X₆` and `W = N/(𝔸_f^×K₀)`, of order 4 (L429).
3. `V/W ≅ P¹_ℚ`: Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 (p. 737) and Lemma 3.1 (pp. 739-740). The
   journal was read by the locator audit: YES (docs/research/locators.md, row "R2: polarized quotient
   identification"). The coordinate `j` is fixed by its values `0, ∞, −16/27` at the three CM points, which are
   rational by Lemma 3.1. That is a Möbius normalization, glue in the kernel (`exists_mobiusBG`,
   `babaGranathX6'_of_rational`).

No missing argument requires stopping. The caveats are under Known issues (§6).

## 5. (d) Re-sourcing R2

### 5.1 What is proved

```lean
def ToP1DescendsAlongSurj : Prop :=
  ∀ (Y X : Over (Spec (CommRingCat.of ℚ))), IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → ∀ (f : Y ⟶ X) (π : ToP1 Y.left),
    (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ f = x) →
    (∀ y y' : fieldPt Qbar ⟶ Y, y ≫ f = y' ≫ f → π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left) →
      ∃ π₆ : ToP1 X.left, ∀ y : fieldPt Qbar ⟶ Y, π₆.val (K := Qbar) (y ≫ f).left = π.val (K := Qbar) y.left

theorem hauptmodulOfX6_of_y3ToP1j (hY : Y3ToP1j) (hD : ToP1DescendsAlongSurj) (hL : PairsLift) :
    HauptmodulOfX6
theorem r1r2W_of_y3ToP1j (hE : CanonicalModelY3) (hX : CoarseX6OfFineW) (hY : Y3ToP1j)
    (hD : ToP1DescendsAlongSurj) (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : HDec.LeafAdopt.R1R2fpRepW

-- Y3ToP1jDescent.lean
theorem toP1DescendsAlongSurj_proof : Y3P1j.ToP1DescendsAlongSurj
theorem hauptmodulOfX6_of_y3ToP1j' (hY : Y3P1j.Y3ToP1j) : HauptmodulOfX6
theorem r1r2W_of_y3ToP1j' (hE : CanonicalModelY3) (hX : CoarseX6OfFineW) (hY : Y3P1j.Y3ToP1j)
    (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : HDec.LeafAdopt.R1R2fpRepW
```

How `hauptmodulOfX6_of_y3ToP1j` works:
1. The quotient clause with `α = id` shows that `π` is constant on the `ℚ̄`-fibres of the forgetful map
   `fY : Y₃ → X₆`. Two points with the same image have isomorphic underlying pairs, by `X6Props`.
2. `fY` is onto `X₆(ℚ̄)` by `PairsLift`.
3. Descend `π` to `π₆` with the glue.
4. Transport the fibre and CM clauses along `QMIso`s (`qmIsoTwist`, `HasCM*.of_iso`).

`r1r2W_of_y3ToP1j` is the kernel's `r1r2fpRep_of'W` (TailZ21), with `HauptmodulOfX6` now from `Y3ToP1j` instead of
from `BabaGranathX6`.

**`ToP1DescendsAlongSurj` is proved** (`Y3P1j.Descent.toP1DescendsAlongSurj_proof`,
`ZInQKernel/Contrib/OneProof/Y3ToP1jDescent.lean`, standard axioms, VERIFIED). The proof has three parts:
* **P¹ as a scheme.** p1-quot's `P1Scheme.lean` (origin/wip/p1-quot) is copied with namespace `Y3P1j.P1`. It
  gives the CloudW07 projective line `ℙ(ULift (Fin 2); Spec ℚ)`, proper and smooth of relative dimension 1 over
  `ℚ`, with standard charts `T₁/T₀` and `T₀/T₁` that make it `P¹` by charts (`IsP1CoordinateQ`). Every
  `σ : ToP1 Z` is the pullback of the standard chart along a morphism `m : Z → ℙ` (`p1SchemeQ_body`).
* **New here: `pt_eq_of_val`.** A `K`-point of a `P¹`-coordinatized `ℚ`-scheme is determined by its coordinate.
  * In the chart `U`, the ring map `Γ(U) → K` is fixed on `ℚ` (`RingHom.ext_rat`) and on the generator `f`;
    `ℚ[X] → Γ(U)` is surjective, and the kernel's `X6Glue.ev_injective` concludes.
  * At `∞` the same argument works in `V` with `g`, which vanishes there
    (`evaluation_eq_zero_iff_notMem_basicOpen`).
* **New here: `val_congr`.** `ToP1.val` reads only `(U, f)`.

Then `factorThroughSurj_proof` (TailZ20) factors `m` through `f`. The hypothesis "`m` is constant on the fibres of
`f`" comes from `pt_eq_of_val`, and `π₆` is the pullback of the standard chart.

### 5.2 Can `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` be dropped? No (VERIFIED by grep)

`scratch/y3-p1j/grep-x6.txt` greps the whole tree: every `.lean` file outside `.lake`, ZInQKernel/ and scratch/.
* Both fields are read only by the conversions at TailZ71:90-91 and TailZ74:1169-1170, into the old fields
  `x6CoarseModuli` and `elkiesX6StarEvery`.
* The readers below them (non-pass-through lines in ZInQKernel/):
  * `x6CoarseModuli` →
    * `gonzalezRotgerX6Ab` (TailZ59:78; the row's `X₆` witness and `R5ptProps`, through
      `x6Rows_of_open14_hf_gm_pz_eb`, EichlerBoundCopy:2948);
    * `elkiesX6StarFunctionField` (TailZ59:83).
  * `elkiesX6StarFunctionField` →
    * `elkiesX6StarPrinted` (TailZ36:102);
    * `babaGranathRationalAb` (TailZ37:91). **This is R2, the only use that the re-source replaces.**
  * `elkiesX6StarPrinted` →
    * `elkiesEquationsX6Ab` (TailZ29:106) → `x6ConicModel` → `x6KummerFibre` → NoCM (EichlerBoundCopy:2668);
    * `SGRDirect.heckeSqrtBranchAny_of_elkies` (EichlerBoundCopy:3221; Lemma NV route).

So after the re-source:
* `elkiesX6StarEveryIdeal` is still read through `x6ConicModel` and through `HeckeSqrtBranchAny`;
* `x6CoarseModuliIdeal` is still read through the row's `X₆` witness (`CoarseX6OfFineW` / `gonzalezRotgerX6Ab`,
  `X6Props`, `R5ptProps`) and through Elkies.

Neither field can be dropped on this base.

On the cm-branch base (origin/wip/cm-branch, not merged here), NoCM and `R5ptProps` are pruned.
* `elkiesX6StarEveryIdeal` would then still be read by `HeckeSqrtBranchAny`, unless sgr-direct is also re-routed.
  `SGRDirect.heckeSqrtBranchAny_of_elkies` (SGRDirectElkies.lean:167) reads Elkies' chart section `s` with
  `s² = −t_E`, the square root in `ℚ(X*(1))(√−t, …)` (Elkies p. 17). `Y3ToP1j` does not give it. The manuscript's
  own substitute is the tame local equation `u − c = z²` at L517-526.
* `x6CoarseModuliIdeal` would still supply the `X₆` witness of the row. The row is `X₆`-shaped: it asserts `∃ X Ψ`
  with a coarse bijection. Dropping it needs the row restated over `Y₃` alone, i.e. the kernel's `R2fpProps` on
  `Y`, and its consumers re-routed. That is a copy-based re-route of the cm-branch kind, not done here.

### 5.3 Fold, `#discharges`, kinds rows, GLUE count

* **No autofold spec and no dry run.** autofold discharges a field of the top bundle. No top field is provable from
  the new statements, and none becomes unread (§5.2): the row is built inside the chain
  (`x6Rows_of_open14_hf_gm_pz_eb`), not from a top field.
* A re-route dry run would replace that internal producer and thread `Y3ToP1j` up to the top. It would add one GLUE
  row and remove none, and it was not built.
* `#discharges` with the new module imported (`scratch/y3-p1j/discharges.txt`, VERIFIED) has no line mentioning
  `Y3P1j`. `HauptmodulOfX6` and `R1R2fpRepW` are not field types.
* **GLUE count against the base: unchanged, 4/27 on 31 (strict) and 4/27 (strictest)**, since nothing is folded. If
  `Y3ToP1j` entered the open list (only through a re-route), it would count GLUE/GLUE: 31 → 32 rows, 4/28. The
  descent glue is proved and adds no row.
* The exact kinds row for the new leaf, for when it is folded, in autofold's column format
  (`scratch/y3-p1j/kinds-rows.tsv`):

```
research	y3ToP1j	consequence	ELLIOT: the manuscript's own claim (diophantine_zq.tex L425-440: N/(A_f^* K_3) acts on Y_3 with all determinant components, central ideles trivially, quotient P^1_j, deg(Y_3 -> P^1_j) <= 4|(O/3O)^*| <= 324), with the normalizer quotient identified by Baba-Granath and Lin-Yang (L420-422); every-witness form over R1fpProps; quotient read on Qbar-points as Aut(O)-twist classes (orbit dictionary ON THE SPOT); CM branch values as the kernel's Baba-Granath section 3.1 reading, locator UNVERIFIED	GLUE	GLUE	diophantine_zq.tex L420-440 (Glazer, 11/5 manuscript); Baba-Granath, Canad. J. Math. 60 (2008) Thm 2.1 and Lemma 3.1 (V/W = P^1_Q, read by the locator audit) and section 3.1 table (UNVERIFIED); |(O/3O)^*| = 72 computed	y3-p1j; pending review				unverified-locator	elliotglazer/diophantine-z-q#86
```

## 6. Known issues (source issues; exact locations)

1. **L421-422, "indices 4, 6, 2" cited to Baba–Granath.** Already recorded in locators.md row "R2: branch values
   and indices" (NO as written) and h-trust A2 (loc-fix note). These are the orbifold orders of `Γ*`. They equal
   the ramification indices of `Y₃ → P¹_j`, because `Γ₃` is torsion-free and normal (compiled in the kernel,
   `RvNocm.ramification_eq_orbifold_order`). They are not the indices of `X₆ → X₆/W`, which are 2 at each branch
   value. No change here; the leaf does not state the indices.
2. **L421-422, the numerical `j`-normalization** (`0, ∞, −16/27`) is not located in Baba–Granath Thm 2.1 or
   Lemma 3.1 (locators.md). It is a definition of the coordinate by three rational CM values (kernel glue).
3. **Bibliography, `\bibitem{babagranath}` (L11027-11030)** cites the 2005 MPI preprint ("Sections 2.1, 3 and
   Proposition 10"). The audit read the 2008 journal version; the preprint was not located.
4. **L434-436, "Consequently … with quotient `P¹_j`"**: the identification `Sh_{K₃}/(N/𝔸_f^×K₃) = Sh_N` is used
   without comment. It is standard, so this is a gap of exposition, not of truth.
5. **L437-440, the degree bound is not sharp**: `4|(𝒪/3𝒪)^×| = 288`, while the degree is `144` because
   `−1 ∈ (𝒪/3𝒪)^×` is central and in `𝔸_f^×K₃`. The printed `≤ 324` is correct. Not an error.
6. Inherited from y3-route-a (L467, L474-475): the "polarized automorphism" and the "canonical principal
   polarization" presuppose the relative Lemma P (y3-route-a §0 item 2).

## 7. Compile record (VERIFIED)

* `lake build +ZInQKernel.Contrib.OneProof.Y3ToP1j` and `lake build +ZInQKernel.Contrib.OneProof.Y3ToP1jDescent`: OK.
* `scratch/y3-p1j/Axioms.lean` (`axioms.txt`): `action_of_z30`, `sigmaR_neg_one`, `isoT`,
  `hauptmodulOfX6_of_y3ToP1j`, `r1r2W_of_y3ToP1j`, `y3ToP1jAt_noDeg_of_row`, `Descent.toP1DescendsAlongSurj_proof`,
  `Descent.hauptmodulOfX6_of_y3ToP1j'`, `Descent.r1r2W_of_y3ToP1j'` all depend on
  `[propext, Classical.choice, Quot.sound]`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: OK, up to date (`build-main.tail.txt`).
* `#discharges` (`discharges.txt`): nothing for `Y3P1j` (see §5.3).
* Computations: `units_mod3.py` → `units_mod3.txt` (`|(𝒪/3𝒪)^×| = 72`); `gram.py` → `gram.txt` (L414-416 matrix,
  det 1).

## 8. What remains

* The re-route that would let the X₆ fields go: restate the row over `Y₃` (`R2fpProps`) and re-route its consumers
  (`cm_of_val`, the Kummer fibre, sgr-direct's `HeckeSqrtBranchAny`) on top of cm-branch.
* Optional: the moduli dictionary of §2 in Lean. The Atkin–Lehner normalizer elements realize the four classes of
  `N/𝔸_f^×K₀`; `X6ALIdeal.mu` gives the elements.
