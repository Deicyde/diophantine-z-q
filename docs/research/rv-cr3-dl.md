# rv-cr3-dl: adversarial review of CR₃^DL,Rk and of the rv-cr3-rank follow-up

Reviewed: `d549dabb` (main), in particular commit `feb18a7b` (task cr3-dl,
`ZInQKernel/RouteK/RankDL.lean`, merged in `0469e1fe`), the KERNEL_PLAN paragraph `fec256b4`, and commit
`350f7798` (the follow-up to the rv-cr3-rank review).

## Verdict

**Lean: no blocker.** `CertifiedRankDLRk` names exactly the two curves pole completeness applies CR₃ to,
its premise `Inputs β θ p₀` can be satisfied and `Slots` is nonempty whenever it holds, no slot choice is
degenerate, the main-theorem variant uses the same assembly as the existing ones with no extra
hypothesis, the build passes, and all 45 `#print axioms` entries show exactly
`[propext, Classical.choice, Quot.sound]`.

**Documentation: one blocker**, in a single sentence:

- **B1** (`KERNEL_PLAN.md:152–155`). "`CertifiedRankTYZRk` implies `CertifiedRankRk` …, so
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk` assumes the
  least." This is false since the next paragraph (`fec256b4`) adds `CertifiedRankDLRk`, which
  `CertifiedRankRk` implies (§1.4, proved in a scratch file, 12 lines). So the `…_certifiedRankDLRk`
  variant assumes no more than the `…_certifiedRankRk` variant. The sentence claims more than Lean
  proves (Lean has no comparison between `Rk` and `DLRk`), and the true comparison goes the other way.
  Fix: write "assumes the least of these three" (or "the least among the forms quantified over all
  `d`"), and preferably add `certifiedRankDLRk_of_certifiedRankRk` (§1.4) to `RankDL.lean` and say
  in the DL paragraph that `CertifiedRankRk → CertifiedRankDLRk`.

The non-blocking remarks are in §4.

## 1. `RouteK/RankDL.lean` (item 1)

### 1.1 Are these exactly the curves CR₃ is applied to?

`poleCompleteness_of_certifiedRank` (`RouteK/Assembly/PoleCompleteness.lean:23`) applies `hCR` twice
(lines 39 and 41), at `n.natAbs` and `(n * thetaOf B m).natAbs` with `a = betaOf B m`. Here `n`, `m` come
from `descent_lemma` (`RouteK/Assembly/DL.lean:59`), which sets `n = (D.d₁ : ℤ)`. That `D` is obtained by
`obtain ⟨D⟩ := hslots p₀ hp₀` from `exists_multiplier_and_slots`, so it is a choice-selected slot datum
for the `m`, `p₀` that lemma selects. So the two curves are `C_{D.d₁}` and `C_{|D.d₁ θ|}` with
`|D.d₁ θ| = D.d₁ · θ.natAbs` (`Int.natAbs_mul`, `Int.natAbs_natCast`; `rvdl_natAbs` in §5), which is
`D.d₂` by `Slots.d₂_eq`. `CertifiedRankDLRk` asks for points of infinite order on
`shortCurve (−(D.d₁)²)` and `shortCurve (−(D.d₁ · θ.natAbs)²)`, so the curves are the same (up to the
choice of `D`, below). Both `RankDL` and `RK9` (`loc_of_mem_sel2_of_infinite_order`) use the same
`shortCurve (-(d : ℚ) ^ 2)`, and the Lean proof turns the points into the `(x, y)` with
`y² = x³ − d²x`, `x ∈ βℚ*²` that `poleSoluble_of_points` consumes. A wrong curve would therefore not
typecheck.

The differences from the original use are in quantifiers only, and both point the safe way for a
hypothesis:

- **`∀ β θ p₀` with `Inputs`, instead of only the triples `(betaOf B m, thetaOf B m, p₀)` that come
  from admissible `B`.** This makes the hypothesis stronger than needed. `CertifiedRankDLAdmRk`
  quantifies over admissible `B` instead, and Lean proves `DLRk → DLAdmRk → PoleCompleteness`.
- **`∃ D` instead of the `D` chosen by `descent_lemma`.** This makes it weaker. It is legitimate because
  `poleSoluble_of_slots_infinite_order` accepts any slot choice `D`. The PC proof
  (`poleCompleteness_of_certifiedRankDLRk`) takes `D` from the hypothesis and never calls
  `descent_lemma`.

The docstring sentence "These are the two curves to which pole completeness applies CR₃"
(`RankDL.lean:66`) is accurate under the reading "the curves of a slot choice", which the next
sentence makes explicit ("The slot choice is existential …").

`CR₃` has no consumer other than pole completeness. Every main theorem in `Main.lean` /
`MainGreenTao.lean` passes `hCR` through `poleCompleteness_of_certifiedRank` (I grepped every `hCR`
use), so the module docstring's "The only consumer of CR₃ is pole completeness" is correct.

### 1.2 Vacuity

- **`Inputs β θ p₀` can hold.** `rvdl_inputs_example : Inputs (-7) 1 7` elaborates (§5). Also, for
  every admissible `B`, `exists_multiplier_and_slots` + `inputs_of_admissible` produce an `Inputs`
  triple, and admissible `B` exist (`Admissible B`: square denominator, `0 < B < 1/2`,
  `v_p(B) ≥ 4` on `poleS0`).
- **`Slots` is nonempty whenever `Inputs` holds.** `exists_slots hI.odd_β hI.odd_θ hI.coprime
  hI.p₀_mem` needs only fields of `Inputs`. `certifiedRankDLRk_of_certifiedRankTYZRk` uses exactly this,
  and `rvdl_slots_example : Nonempty (Slots (-7) 1 7)` instantiates it. For this input,
  `P ∖ {p₀} = T = ∅`, so a slot choice is just a prime `q₀ ≡ 3 (mod 8)` with `(q₀/7) = 1`
  (`q₀_sym_p₀`: `signBit(−7) + 1 = 0`), and `d₁ = 7q₀` (for example `q₀ = 11`, `d₁ = 77`). So
  `CertifiedRankDLRk` at `(−7, 1, 7)` asserts that `7q₀` is a congruent number for some such `q₀`: a real
  arithmetic claim.
- **No degenerate `D`.** `D.d₁ = ∏ k, D.f₁ k` is a product over `P ∪ {q₀} ∪ R_P ∪ R_T`
  (`FirstCurve.lean:37`), and under `Inputs`, every `D` has `d₁ ≡ 5 (mod 8)`, `d₁` squarefree,
  `β ∣ d₁` and `SelmerCertified d₁ β` (and the same for `d₂`). So `d₁ ≥ 7 · 3 = 21`, and both curves
  have `#Sel₂ = 8` (`sel_of_selmerCertified`), hence rank ≤ 1. The existential cannot be met by a
  trivial curve. Choosing a convenient `D` (one with known points) is the intended use: the docstring's
  "smaller target for partial results".
- **The hypothesis is not trivially provable,** since it would decide congruent numbers. It is not
  contradictory either: it follows from `CertifiedRankTYZRk` (proved), and so from the cited literature.

### 1.3 Main-theorem variant

`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk` is

```
Assembly.assembly_AP Compiler.NodeCheck.haltingAddMulBound hH
  (poleCompleteness_of_certifiedRankDLRk hCR)
  (Mult.slopeRepresentationAP_of_goodPrimeAP (goodPrimeAP_of_greenTaoDense greenTaoDense Density.goodPrimeDensity))
```

Unfolding `…_sixContactMin_certifiedRank` (MainGreenTao.lean:38) gives `…_of_goodPrimeDensity` →
`…_of_greenTaoDense hH hCR greenTaoDense goodPrimeDensity` → `…_of_goodPrimeAP hH hCR
(goodPrimeAP_of_greenTaoDense hGT hD)` → `assembly_AP haltingAddMulBound hH
(poleCompleteness_of_certifiedRank hCR) (slopeRepresentationAP_of_goodPrimeAP hAP)`. This is the same
term with only the PC argument changed. The only hypotheses are `SixContactMin` and
`CertifiedRankDLRk`, and `#print axioms` shows the three standard axioms. The docstring ("the rest of the
assembly is that of `…_sixContactMin_certifiedRank` (route AP, with Szemerédi's theorem in the primes and
Proposition D proved)") is accurate.

### 1.4 Docstrings

- No declaration or module text calls `CertifiedRankDLRk` or `CertifiedRankDLAdmRk` "the narrowest".
  Their dependence on internal definitions is stated: `CertifiedRankDLRk` names `RouteK.Inputs`,
  `RouteK.Slots` and `Slots.d₁`, and `CertifiedRankDLAdmRk` names `betaOf`, `thetaOf`, `Admissible` and
  `RouteK.Slots`. KERNEL_PLAN (lines 167–169) repeats this.
- `sel_of_selmerCertified`, `slots_d₂_facts`, `exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified`,
  `exists_point_of_selmerCertified_of_infinite_order`, `poleSoluble_of_slots_infinite_order` and the two
  PC theorems: each docstring matches its statement and proof.
- `CertifiedRankDLRk` docstring, `RankDL.lean:68–71`: "CR₃^DL,Rk is implied in Lean by CR₃^TYZ,Rk …,
  and so rests on the same literature (Tian–Yuan–Zhang with Gross–Zagier, or Kriz's 2-converse)". The
  implication from `TYZRk` justifies the TYZ route only, together with Rédei's formula, which this list
  leaves out. `TYZRk` has no Selmer premise, and its own trust statement cites only Rédei,
  Tian–Yuan–Zhang and Gross–Zagier. The Kriz route reaches `DLRk` through `CertifiedRankRk`, and
  `CertifiedRankRk → CertifiedRankDLRk` is true but not stated in Lean:

```lean
theorem rvdl_certifiedRankDLRk_of_certifiedRankRk (h : CertifiedRankRk) : CertifiedRankDLRk := by
  intro β θ p₀ hI
  obtain ⟨D⟩ := exists_slots hI.odd_β hI.odd_θ hI.coprime hI.p₀_mem
  obtain ⟨h₂5, h₂sq, h₂β, h₂c⟩ := slots_d₂_facts D hI
  refine ⟨D, ?_, ?_⟩
  · obtain ⟨h8, b, hb⟩ := sel_of_selmerCertified (D.d₁_mod hI) (D.squarefree_d₁ hI) hI.sqf_β
      (D.β_dvd_d₁ hI) (D.selmerCertified_d₁ hI)
    exact h _ (D.d₁_mod hI) (D.squarefree_d₁ hI) h8 ⟨(β, b), hb, hI.mod_β⟩
  · obtain ⟨h8, b, hb⟩ := sel_of_selmerCertified h₂5 h₂sq hI.sqf_β h₂β h₂c
    exact h _ h₂5 h₂sq h8 ⟨(β, b), hb, hI.mod_β⟩
```

  This elaborated against `d549dabb` with axioms `[propext, Classical.choice, Quot.sound]`
  (scratch/rv-cr3-dl/probe.txt). With it, the docstring's claim becomes correct, and B1 is resolved by
  rewording. See remark R1.

## 2. The rv-cr3-rank follow-up, `350f7798` (item 2)

### 2.1 `certifiedRankRk_of_certifiedRankTYZRk`

`fun d hd5 hsq h8 ⟨_, hab, h7⟩ => h d hd5 hsq ((det_M5b_eq_T5b hd5 hsq).symm.trans (det_M5b_eq_one hd5
hsq h8 hab h7))`. `det_M5b_eq_one` (`Rank5b/Row5b.lean:160`) is Corollary 4.4 in Lean: under
`#Sel₂ = 8`, `(a, b) ∈ Sel₂` and `|a| ≡ 7 (mod 8)`, `det M_5b = 1`. `det_M5b_eq_T5b`
(`Sec3/TYZ.lean:83`) is Theorem 3.6. The proof is genuine and in print_axioms. Its docstring ("so CR₃^Rk
is the weaker hypothesis") is correct.

### 2.2 The corank-lemma citation

Each of the three trust statements now reads: "Cassels–Tate: the pairing on `Ш/Ш_div` is nondegenerate
and alternating, so `dim (Ш/Ш_div)[2]` is even, with no finiteness of `Ш` assumed". The citation is
correct as stated, and it matches the manuscript's Lemma `lem:corank` (line 1072, proof lines 1076–1084).

- For an elliptic curve over a number field, the Cassels–Tate pairing on `Ш/Ш_div` is nondegenerate
  (Cassels for elliptic curves, Tate in general) and alternating. Cassels proved alternation for elliptic
  curves. Poonen–Stoll show that for a principally polarized abelian variety it is antisymmetric, and
  alternating when the polarization comes from a rational divisor, which holds for elliptic curves. The
  manuscript cites Poonen–Stoll for this, and the docstrings' "Cassels–Tate" names the pairing, not the
  paper. That is acceptable.
- `Ш[2^∞] ≅ (ℚ₂/ℤ₂)^t ⊕ F` with `F` finite (since `Sel_{2^∞}` is cofinitely generated), and the 2-primary
  part of `Ш/Ш_div` is `F`. An alternating nondegenerate pairing on a finite abelian 2-group forces
  `F ≅ A × A`, so `dim F[2] = dim (Ш/Ш_div)[2]` is even. Antisymmetry alone would not suffice at 2, so
  "alternating" is the necessary word, and it is there. No finiteness of `Ш` is used.
- Then `dim Sel₂ = 3`, `dim C_d(ℚ)[2] = 2` give `r + t + dim F[2] = 1`, so `F[2] = 0` and the corank
  `r + t` is 1, which is the input Kriz's Theorem 10.13 needs. Rank one and finite `Ш` then come from
  Kriz's conclusion (`ord_{s=1} = 1`) and Gross–Zagier–Kolyvagin, and `Ш[2] = 0` follows from
  `dim Sel₂ = 3`. "Giving `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0`" is a fair compression.

The old wording ("Poonen–Stoll: … `dim Ш[2]` even when `Ш` is finite") would have been circular, and it
has been removed from all three places (`git grep "when finite\|when \`Ш\` is finite"`: no hits in
`ZInQKernel/`).

### 2.3 The chain to Tian–Yuan–Zhang's hypothesis

TYZ's input (tyz-5b.md §1.2, Proposition 1.1) is: `T_5b(n)` odd, with `g(d) = #2Cl(ℚ(√−d))`. In Lean:

- **CR₃^Sel and CR₃^Rk** (Sel₂-premises): Corollary 4.4 (`det_M5b_eq_one`) gives `det M_5b = 1`, and
  Theorem 3.6 (`det_M5b_eq_T5b`) gives `T5b d = 1` (Rédei's `g` in Legendre symbols). Rédei's formula
  (the Prop `RedeiFormula`, not proved) identifies this with `T5bCl d`, the genus sum with TYZ's class
  numbers. This is what the Covering.lean and Statements.lean bullets say. Proposition 0 is not needed
  here because `det_M5b_eq_one` is stated with the textbook `Sel2`. The Covering bullet correctly omits
  it.
- **`ZInQ.CertifiedRank`** (system-premises): Proposition 0 (`prop0Statement`, a theorem) is needed first
  to turn `Σ(𝒞_d)` into `Sel₂(C_d)`, and the CertifiedRank.lean bullet includes it. "Proposition 0 …
  and Corollary 4.4 and Theorem 3.6 of `docs/research/tyz-5b.md`" could be misread as saying Proposition 0
  is in tyz-5b. It is in descent-alt §4.1, which tyz-5b §4.1 recalls, and the bullet's first line names
  descent-alt. This is harmless.
- In Statements.lean the parenthetical "(proved in Lean: `certifiedRankRk_of_certifiedRankTYZRk`)"
  points to the theorem that packages Corollary 4.4 and Theorem 3.6, not to them by name. This is
  accurate.

Hypothesis shape: Corollary 4.4 of tyz-5b needs `|β|_odd ≡ 3 (mod 4)`, and Lean's `|a| ≡ 7 (mod 8)` is a
special case. TYZ's Proposition 1.1 needs only `n ≡ 5 (mod 8)` squarefree, which matches
`CertifiedRankTYZRk` / `TYZClRk`.

### 2.4 KERNEL_PLAN.md paragraphs

- **CertifiedRankRk paragraph (lines 148–156).** "`CertifiedRankTYZRk` implies `CertifiedRankRk`
  (`certifiedRankRk_of_certifiedRankTYZRk`, by Corollary 4.4 and Theorem 3.6)" is proved. "so
  `…_certifiedRankRk` assumes the least" is **B1**. "`CertifiedRankTYZRk` is the form whose content is
  literally Tian–Yuan–Zhang's argument, Rédei's formula and Gross–Zagier, with no condition on `Sel₂`"
  is a description of the trust statement, not a Lean claim, and it is fine.
- **CertifiedRankDLRk paragraph (lines 158–169).** Each Lean claim checks:
  `CertifiedRankTYZRk → CertifiedRankDLRk` is `certifiedRankDLRk_of_certifiedRankTYZRk`,
  `CertifiedRankDLRk → PoleCompleteness` is `poleCompleteness_of_certifiedRankDLRk`, the main theorem is
  `…_certifiedRankDLRk`, "`CertifiedRankDLAdmRk` quantifies only over admissible `B`" matches its
  definition, `poleSoluble_of_slots_infinite_order` exists, and the dependence on `Inputs`/`Slots` is
  stated. "These forms rest on the same literature as `CertifiedRankTYZRk`" is true (they are implied
  by it). The paragraph does not mention `DLAdmRk`'s two Lean implications (`DLRk → DLAdmRk → PC`),
  which is harmless.
- `Main.lean:187`: the retitled docstring "Main theorem from H, CR₃^Sel and route AP's two inputs"
  removes the old "narrowest so far". This is fine.

## 3. Build and axioms (item 3)

- `lake build ZInQKernel` at `d549dabb`: `Build completed successfully (9913 jobs)`, exit 0, no errors
  and no `sorry` warnings (scratch/rv-cr3-dl/build-tail.txt).
- `lake env lean scripts/print_axioms.lean`: exit 0, 45 `#print axioms` lines, 45 entries, every one
  exactly `[propext, Classical.choice, Quot.sound]` (scratch/rv-cr3-dl/axioms.txt; parsed after joining
  wrapped lines, with the three primed names checked by hand). This includes
  `…_sixContactMin_certifiedRankDLRk`, `certifiedRankRk_of_certifiedRankTYZRk`, `sel_of_selmerCertified`,
  `certifiedRankDLRk_of_certifiedRankTYZRk`, `poleCompleteness_of_certifiedRankDLRk`,
  `poleCompleteness_of_certifiedRankDLAdmRk` and `certifiedRankDLAdmRk_of_certifiedRankDLRk`.
- Probe file (§5) elaborated with no errors, then deleted.

## 4. Non-blocking remarks

- **R1** (`RankDL.lean:68–71`). See §1.4: the literature list drops Rédei's formula, and the "or Kriz's
  2-converse" route does not follow from the cited `TYZRk → DLRk`. Adding
  `certifiedRankDLRk_of_certifiedRankRk` (above) and citing it fixes both this and B1.
- **R2** (`RankDL.lean:66`). "These are the two curves to which pole completeness applies CR₃" would be
  more precise as "… the curves of a slot choice, as in `descent_lemma`". The existing proof uses a
  choice-selected `D`, while the hypothesis lets its prover pick one.
- **R3** (`Hypotheses/CertifiedRank.lean:47–49`). "CR₃ is as narrow as the proof allows short of naming
  the slot configurations themselves" remains literally true, and `RankDL` is the "naming" form. A
  pointer to `RouteK.Rank.CertifiedRankDLRk` there would help readers.
- **R4** (`Hypotheses/CertifiedRank.lean:38–41`). "Proposition 0 … and Corollary 4.4 and Theorem 3.6 of
  `docs/research/tyz-5b.md`" could be read as placing Proposition 0 in tyz-5b. Writing "Proposition 0
  (descent-alt §4.1, `prop0Statement`)" would remove the ambiguity.

## 5. Probe file (deleted after use)

`scratch/rv-cr3-dl/Probe.lean`, run with `lake env lean` against the built tree. Output:
scratch/rv-cr3-dl/probe.txt (three axiom lines, all `[propext, Classical.choice, Quot.sound]`, no errors).

```lean
import ZInQKernel
open ZInQ ZInQ.RouteK ZInQ.RouteK.Rank ZInQ.RouteK.Selmer

theorem rvdl_inputs_example : Inputs (-7) 1 7 := by
  have h7 : primesOf (-7) = {7} := by
    rw [primesOf]; norm_num
  have h1 : primesOf 1 = ∅ := by simp [primesOf]
  have hleg : legBit 7 1 = 0 := by
    unfold legBit; simp [IsSquare.one]
  refine ⟨Int.squarefree_natAbs.mp (by simpa using (Nat.prime_iff.mp (by norm_num : Nat.Prime 7)).squarefree),
    by decide, by decide, by rw [h7]; simp, by decide, by decide,
    squarefree_one, isCoprime_one_right, ?_, ?_⟩
  · intro ℓ hℓ; rw [h1] at hℓ; simp at hℓ
  · intro p hp; rw [h7, Finset.mem_singleton] at hp; subst hp; exact hleg

theorem rvdl_slots_example : Nonempty (Slots (-7) 1 7) :=
  exists_slots rvdl_inputs_example.odd_β rvdl_inputs_example.odd_θ
    rvdl_inputs_example.coprime rvdl_inputs_example.p₀_mem

-- rvdl_certifiedRankDLRk_of_certifiedRankRk: see §1.4

theorem rvdl_natAbs (d₁ : ℕ) (θ : ℤ) : ((d₁ : ℤ) * θ).natAbs = d₁ * θ.natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
```
