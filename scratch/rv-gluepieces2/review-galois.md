# rv-gluepieces2: adversarial review of the Galois fields of `GluePieces2`

Reviewer: subagent, 2026-11-13. Read-only. No Lean was run. File: `scratch/g0-assemble/G0Assemble.lean`
(abbreviated "GA"). Fields: `BurnsideAbsIrred`, `R14Det`, `G9Glue`, `G10Glue`, `G12Weight`, `DetTate`
(namespace `G0Galois`, GA L37201-37909).

Marks: VERIFIED = read in a file or checked with `diff`. STANDARD = published, with a reference.
SPECULATIVE = my argument only. Theorem numbers from memory are marked UNVERIFIED.

## 0. Copies and consumption (VERIFIED)

- **Copies.** GA's `G0GaloisSec`, `G0GaloisMatrixSec` and `G0GaloisDetSec` (L37201-37909) were
  diffed against `scratch/g0-mod-galois/ModGalois.lean` L20047-20751. They are identical except for
  `G10Glue`'s first line, its docstring, and the hypothesis names in `g8_g11`/`g8_g12`.
  - GA's `PkgI3Sec`+`PkgI4Sec` (L1951-4759) equal ModGalois L1920-4728, up to one docstring line.
  - GA's `HSyn` block (`EigenformRepExists`, `DeligneSerreConseq`, `FrobeniusDense`, `BrauerNesbitt`,
    L21440-21500) has the same bodies as ModGalois L19106-19176.
- **Consumption.** `gluePieces_of_gluePieces2` (L42019) builds `GaloisPieces` from the six fields
  plus the proved `resQFiniteIndex`. `afterG7_of` (L41703) uses that bundle twice:
  - through `g8_g12_of_leaves` at ℓ = 5. There `g12` (L37590) uses G9Out and G10Out as Pan's
    hypotheses, `G12Weight` to force k = 2, and `g12Det_of` (L37840) uses `R14Det` (ℓ = 5, k = 2)
    and `DetTate` (ℓ = 5, g = 2);
  - through `g8_g11` at ℓ = 3. There the G9/G10 outputs are discarded (`-`), and only Burnside
    (via `g8Matrix_of_burnside`, L37689) is used.
  - Every field is used with real content. None is used only in a trivially true instance.

## 1. `BurnsideAbsIrred` (L37677), claimed LEAF: **TRUE**

```lean
∀ F G W [FiniteDimensional F W] n (b : Basis (Fin n) F W) (ρ : Representation F G W),
  (∀ F' [Field F'] [Algebra F F'], (repBaseChange F' ρ).IsIrreducible) →
  Algebra.adjoin F (range fun g => toMatrix b b (ρ g)) = ⊤
```

- **Definitions** (VERIFIED). `IsIrreducible` is Mathlib's `IsSimpleOrder (Subrepresentation ρ)`
  (Mathlib/RepresentationTheory/Irreducible.lean L29). It is false for `W = 0`. `repBaseChange`
  (GA L2175) is `(ρ g).baseChange E`. Both are genuine.
- **Argument** (STANDARD). Take `F' = AlgebraicClosure F`, which lives in `Type`, so the
  quantifier covers it. Then `W_{F̄}` is a simple `F̄[G]`-module. Burnside's theorem over an
  algebraically closed field gives `span_{F̄} ρ(G) = End(W_{F̄})`. The `F`-span of `ρ(G)` has the
  same dimension `n²` after base change, so it is `M_n(F)`, and that span lies in the `adjoin`.
- **Edge cases.** For `n = 0` the conclusion is trivial (subsingleton algebra). For `W = 0` the
  hypothesis fails. A monoid `G` is fine.
- **Strength.** It is slightly stronger than Lang's literal statement (Lang, *Algebra* XVII §3,
  Cor. 3.3/3.4: `k` algebraically closed, UNVERIFIED). The step from it is a dimension count under
  base change, and the absolute form is itself textbook: Isaacs, *Character theory*, Thm 9.2;
  Curtis–Reiner §29 (UNVERIFIED). It is also provable from Mathlib's `jacobson_density`. Low risk.
- **Recommendation.** Cite the absolute-irreducibility form, or demote the field to glue and prove it.

## 2. `R14Det` (L37777), claimed LEAF: **TRUE, not stronger than published**

```lean
∀ ℓ ιC ιL N k χ (g : CF N k), 0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
  ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
    ∃ ε : GQ →* (ℚ̄_ℓ)ˣ, (range ε).Finite ∧ ∀ σ, det (ρ.mat σ) = ε σ * cycQ ℓ σ ^ (k-1)
```

- **Definitions** (VERIFIED, GA L4469-4528, L37761-37771). `IsNormalizedEigenform` has three
  parts: nebentypus `f|γ = χ(d) f`, `a₁ = 1`, and the full Hecke relation with `χ(d) d^{k−1}`.
  `AttachedTo` uses an **arithmetic** Frobenius (`σx − x^p ∈ m_v`) and needs `tr = ιL(α)` with
  `ιC(α) = a_p`. `cycQ` is Mathlib's `cyclotomicCharacter ℚ̄ ℓ`, which satisfies `g ζ = ζ^{χ(g)}`
  (`cyclotomicCharacter.spec`, VERIFIED).
- **Normalization check** (SPECULATIVE, standard).
  - At an arithmetic Frobenius above `p ≠ ℓ`, `cycQ = p`: distinct ℓ-power roots of unity stay
    distinct mod `v`.
  - Suppose a published `ρ'` uses geometric Frobenius (Deligne's H¹ convention). Then
    `ρ := ρ'^∨` satisfies `tr ρ(Frob_arith) = a_p` and `det ρ(Frob_arith) = det ρ'(Frob_geom) = χ(p) p^{k−1}`.
    So the published determinant `χ(p) p^{k−1}` holds in this file's convention.
  - Then `ε := det ρ · cycQ^{1−k}` is continuous, and its values at a dense set of Frobenii lie in
    the closed finite group `μ_{ord χ}`, so `ε` has finite image.
  - `ε` is only existential. The statement does not even pin `ε = χ`, so it is weaker than the
    published `det ρ_f = χ · χ_ℓ^{k−1}`.
- **Edge cases.**
  - k = 1: Deligne–Serre's finite-image `ρ`, moved to ℓ-adic coefficients through
    `ιL ∘ ιC⁻¹` on a number field of definition, has `det = ε`.
  - ℓ | N is fine, because `AttachedTo` excludes `p | Nℓ`.
  - If `χ(−1) ≠ (−1)^k`, there is no nonzero `g`, so the hypotheses cannot hold.
- **Sources** (UNVERIFIED locators). Deligne, Sém. Bourbaki 355 (1971), Thm 6.1; Shimura 1971
  Thm 7.14 for k = 2; Deligne–Serre 1974 Thm 4.1. Semisimplicity: semisimplification keeps traces
  and determinant.
- **Consumption.** Used at ℓ = 5, k = 2 in `g12Det_of` (L37842).

## 3. `G9Glue` (L37395), GLUE: **TRUE**, but its proof needs content that is not among its hypotheses

```lean
DeRhamComparison → (∀ p, T23_FontaineClosure p) → ∀ K [NumberField K] (A : PkgI3.AbVar K) ℓ r e,
  A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r
-- G9Out r := LocalIsDeRham ℓ 2 (r.restrictLocal ℓ) ∧ r.HasHTWeightsAtSelf ℓ {0, -1}
```

- **Truth** (STANDARD).
  - `r|G_K ⊕ r|G_K ≅ V_ℓ(A)⊗ℚ̄_ℓ`. Restricted to `G_{K_v}`, `v | ℓ`, this is de Rham with
    weights 0 and −1, each of multiplicity 2 (Faltings 1988; the Hodge–Tate decomposition
    `ℂ_p⊗V = ℂ_p^g ⊕ ℂ_p(1)^g`).
  - Summands of de Rham representations are de Rham with the same weights. Being de Rham and the
    HT weights descend from `K_v` to `ℚ_ℓ` (Galois descent of `D_dR`).
- **Convention check** (VERIFIED, definitions read). `htMult w = dim H_{−w}/[E:ℚ_p]`, where
  `H_i = Hom_G(V, ℂ_p(i))`, gives `ℚ_p(1)` weight −1 (`htMult_cycRep_eq_zero`, L4190). So V_ℓ(A) has
  weights {0, −1}, the same convention as `htMultOver` in `DeRhamComparison`.
- **The floor division in `htMult`** (SPECULATIVE). It is harmless for G_{ℚ_p} representations: G_{ℚ_p}
  permutes the τ-components of `ℂ_p ⊗_{ℚ_p} V` transitively, so all τ-weights are equal and the
  average is exact.
- **Prior work** (VERIFIED by diff). g9-derham's `ZInQKernel/Contrib/G9/Statement.lean` L104 has
  `G9Glue` textually identical to GA's, and its `resQ`, `Vb`, `tate`, `Intertwines`, `G9Out`,
  `qEmbRing` bodies are identical too. `I3Layer.lean` and `I4Layer.lean` equal GA's `PkgI3`/`PkgI4`
  sections, except for one docstring line and the `ZInQ.Contrib.G9` namespace wrapper. So
  `g9Glue_of_abVarBaseChange : AbVarBaseChange → R10Weights → G9Glue` transfers textually (a
  re-elaboration is needed).
- **Defect (provability, not truth).** That proof needs two facts, and neither is a hypothesis of
  `G9Glue` or a bundle field:
  - **`R10Weights`**: `htMultOver w = 0` for `w ∉ {0, −1}`. This is Tate–Sen / Ax–Sen–Tate
    content, which is not in Mathlib. GA's `r10 : PkgI4.DeRhamComparison` (L33001) was **not**
    amended as g9-derham F1 recommended.
  - **`AbVarBaseChange`**: base change of `PkgI3.AbVar` to a local field, with `V_ℓ` and `dim`
    preserved.
  - As stated, the glue silently includes a published theorem (Faltings' HT decomposition, or Tate's
    `ℂ_p(j)^G = 0`).
  - **Recommendation:** add `R10Weights` to `r10`. The amendment is the published statement
    itself.

## 4. `G10Glue` (L37417), GLUE: **TRUE**. The g10-odd reduction transfers. A provability gap remains.

```lean
T11a_RiemannEnd → T11b_Rigidity → FaltingsTate → ∀ K [NumberField K] [IsGalois ℚ K] A ℓ r e,
  A.dim = 2 → finrank ℤ (End A) = 4 → EndDivision A → (∃ x y, x*y ≠ y*x) →
  Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → r.IsOdd
```

- **Diff** (VERIFIED). GA differs from ModGalois L20259 **only** in the first line: `T11a → T11b`
  replaces the opaque `HSyn.T11_RiemannGAGA → HSyn.T12_ArtinComparison`. The body and every
  dependency are identical.
- **Truth** (STANDARD).
  - Complex conjugation is an involution (`IsComplexConj`, L4012, makes `c` act as `z ↦ z̄`
    through some ι). So `r(c)² = 1`, and oddness is equivalent to `r(c) ≠ ±1`.
  - Suppose `r(c) = ±1`. Then `ρ_A(cσc⁻¹) = ρ_A(σ)` on `G_K` (base change is injective). So the
    `c`-semilinear transport `c_* : V_ℓ(A) → V_ℓ(A^c)` is `G_K`-equivariant.
  - By Faltings, `c_* ∈ Hom(A,A^c)⊗ℚ_ℓ`. By the Artin comparison, `c_* = F_*⊗1` with `F`
    antiholomorphic and ℚ-rational on H₁.
  - `(W⊗ℚ_ℓ) ∩ Hom_ℚ = W`, so `F_*` is holomorphic too, hence `F_* = 0`. This contradicts
    `H₁ ≠ 0` (dim A = 2).
  - The argument holds for any A of positive dimension. Rank, division and noncommutativity are
    unused.
  - `IsGalois` makes `A^c` a K-variety and keeps the quantifier non-vacuous (g10-odd §8,
    `exists_resQ_conj`).
- **Transfer of g10-odd** (VERIFIED by reading `scratch/g10-odd/G10Odd.lean` L200-254).
  `g10Glue_of_conjTwist` begins with `intro _ _ hF K _ _ _ A ℓ _ r e hdim _ _ _ hI` and ignores the
  first two binders. The new statement has the same binder shape (two Props, then
  `FaltingsTate`), so the same script proves **ConjTwistNontrivial → new G10Glue**. None of the
  helper names exist in GA (grep: 0 hits each), so they can be appended. Check snippet in §7(a).
  `G10GlueConcrete` (g10-odd L373) is *not* GA's statement: it has the extra hypotheses T35, T5, T26.
- **Defect (provability).** Proving `ConjTwistNontrivial` needs the Artin comparison, which needs
  the uniformization T35 (`t35`), T5 (`t5`) and T26 (`t26`). These are bundle leaves, but
  **`G10Glue` does not take them as hypotheses**, and `g8_g11` passes only `t.t11a t.t11b r.r9b`.
  Discharging `G10Glue` would therefore require proving T35 (complex uniformization, with GAGA)
  inside Lean.
  - **Recommendation:** use g10-odd's `G10GlueConcrete` form. Add
    `UniformizationExists → PkgI2.TorsionStructure → PkgI3.TateModuleFree →` and pass
    `t.t35 t.t5 t.t26` in `g8_g11`. This is a one-line change and stays a weaker requirement.

## 5. `G12Weight` (L37437), GLUE: **TRUE**, proved from two new leaves (copy identical)

```lean
R14 → R13 → R15 → T18 → T19 → ∀ (r : GaloisRep 5 2) N k χ g ψ ιC ιL S, 0 < N → 1 ≤ k →
  IsNormalizedEigenform g χ → r.IsIrreducible → r.HasHTWeightsAtSelf 5 {0,-1} →
  r.AttachedUpToTwist ψ ιC ιL g S → ∃ n, ({n, n+1-k} : Multiset ℤ) = {0,-1}
```

- **Conclusion.** Since `k ≥ 1`, the conclusion is equivalent to `k = 2` (`g12Weight_concl_iff`,
  compiled per g12-det).
- **Truth** (STANDARD).
  - Traces agree at Frobenius outside a finite set. By Chebotarev and Brauer–Nesbitt (r is
    irreducible, ρ_g semisimple), `r ≅ ψ⊗ρ_g`.
  - The Sen weights of `ψ⊗ρ_g` are `{s, s+1−k}` (or `{s, s}` for k = 1, finite image). If these
    equal `{0, −1}`, then `s = 0` and `k = 2`. For k = 1 it is impossible.
- **Averaged `htMult`** (SPECULATIVE). It is harmless for the same reason as in §3: for G_{ℚ_5}
  representations all τ-weights coincide. So a "half {0,0}, half {−1,−1}" split over τ cannot
  occur.
- **Prior work** (VERIFIED).
  - `scratch/g12-det/Integrate.lean` = ModGalois.lean minus `#print` lines (prefix match, 21006
    lines) + g12-det parts.
  - It proves `g12Weight_of_senTwist : SenTwist → FiniteImageHT → G12Weight` for ModGalois's own
    constant, which is textually identical to GA's, with identical dependencies (§0). So the proof
    transfers. Compilation is reported by g12-det; not re-run here.
- **Leaves outside the bundles.** `SenTwist` (Sen 1980) and `FiniteImageHT` (Tate 1967 /
  Ax–Sen–Tate) are not in `ResearchLeaves`/`TextbookLeaves`. `SenTwist` with full-size multisets
  looks faithful.

## 6. `DetTate` (L37787), GLUE: **TRUE**, proved from leaves (copy identical)

```lean
∀ K [NumberField K] (A : PkgI3.AbVar K) ℓ (g : ℕ), A.dim = g →
  ∀ σ, LinearMap.det (tate A ℓ σ) = (cycQ ℓ (resQ K σ) : ℚ̄_ℓ) ^ g
```

- **Direction of the action** (VERIFIED, L2683-2727). `galAct σ P = galHom σ ≫ P = P ∘ Spec(σ)`,
  so `σ` is applied to coordinates, and `galHom_mul` makes it a left action. With the inverse
  action the formula would be `χ^{−g}` and false. It is not.
- **Truth.** `e(σx, σy) = χ_ℓ(σ) e(x, y)`, and a symplectic similitude of `ℚ_ℓ^{2g}` with
  multiplier `c` has determinant `c^g` (STANDARD: Mumford §20, §23, UNVERIFIED). Moreover
  `χ^{ℚ̄}(resQ σ) = χ^{K̄}(σ)`.
- **Edge cases.** `A = AbVar.zero`: dim = 0, `V = 0`, det = 1 = χ⁰. ℓ is arbitrary (char 0).
  `Vb` is finite-dimensional because `T_ℓ` is free of rank 2g, so `LinearMap.det` is not the
  junk value 1.
- **Prior work** (VERIFIED by diff of the target). g12-det's `detTate_of_leaves`
  (T09_SymmIsogenyExists, IsogenyQuasiInverse, DivisiblePoints, TateModuleFree) targets
  ModGalois's `DetTate`, which is identical to GA's, and `cycQ`/`toRingEquivQ` are identical.
  The three weil-pairing leaves are **not** in the bundles; T9 in the bundle is the different
  `LeafPush.T09_WeilPairing`.

## 7. Lean checks to run later

(a) **G10Glue reduction transfers to the changed statement.** Append to GA, in this order:

```lean
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)
open scoped TensorProduct
-- paste `sed -n 102,239p scratch/g10-odd/G10Odd.lean` verbatim: §2 and §3 from
-- det_eq_neg_one_of_sq_eq_one through g10Out_of_conjTwist (ConjTwistNontrivial, galRep_eq_of_central
-- included), stopping before its own `g10Glue_of_conjTwist` (L241)
theorem g10Glue_of_conjTwist_new (h : ConjTwistNontrivial) : G10Glue := by
  intro _ _ hF K _ _ _ A ℓ _ r e hdim _ _ _ hI
  exact g10Out_of_conjTwist h hF K A ℓ r e hdim hI
end G0Galois
#print axioms G0Galois.g10Glue_of_conjTwist_new
```

(Line range checked: L102 is the docstring of `det_eq_neg_one_of_sq_eq_one`, and L239 ends the
proof of `g10Out_of_conjTwist`. `open scoped TensorProduct` is at G10Odd L100 and is repeated
above. Expected: compiles with the standard axioms only.)

(b) No refutation candidate was found, so there is no falsity snippet.

## 8. Summary table

| field | kind | verdict | evidence | issue |
|---|---|---|---|---|
| BurnsideAbsIrred | LEAF | TRUE | STANDARD; definitions VERIFIED | absolute form is a corollary of Lang's literal statement; cite Isaacs 9.2 / CR §29, or prove from `jacobson_density` |
| R14Det | LEAF | TRUE, weaker than published | definitions VERIFIED; normalization SPECULATIVE/STANDARD | none |
| G9Glue | GLUE | TRUE | STANDARD; g9-derham copy diff VERIFIED | proof needs `R10Weights` (published HT content) and `AbVarBaseChange`, neither available; amend `r10` |
| G10Glue | GLUE | TRUE | STANDARD; reduction transfer VERIFIED by reading, snippet §7(a) | proof needs T35/T5/T26, not hypotheses; adopt the `G10GlueConcrete` hypotheses |
| G12Weight | GLUE | TRUE (≡ k = 2) | g12-det proof of identical copy (diff VERIFIED, compile reported) | rests on new leaves SenTwist, FiniteImageHT |
| DetTate | GLUE | TRUE | g12-det proof of identical copy (diff VERIFIED, compile reported) | rests on three weil-pairing leaves outside the bundles |
