# leaf-review-a: statement review of leaf-fold3's groups A, A′ and F (21 fields)

Task leaf-review-a, 2026-11-13. Base: fork main 8ec80711 with origin/wip/leaf-fold3 (f7951690) merged.
Object of review: the 21 bundle fields of `HDec.HSyn.sixContactMin_of_open3` that leaf-fold3's report
(`docs/research/leaf-fold3.md` §3) puts in group A (Shimura curves with QM, 14 fields), A′ (theta functions
and Siegel modular forms of genus 2, 2 fields) and F (Galois representations of modular forms, 5 fields).
The statements were read in leaf-fold3's flat file `scratch/leaf-fold3/Leaves3.lean` (line numbers below
refer to it), with every definition they use. Results log: `scratch/leaf-review-a/log.md`.
Model work, no human review; no network (every theorem number from memory is marked UNVERIFIED).

Marks: **VERIFIED** = read in a file, computed, or compiled. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source.

Verdicts: **PUBLISHED-FORM** (the Lean text is a published statement, up to formalization of the
definitions); **CONSEQUENCE** (follows from published statements by the derivation given);
**STRONGER-THAN-SOURCE** (asserts more than the source gives); **NOT-A-PUBLISHED-STATEMENT** (neither a
published statement nor a derivable consequence of one, as stated).

## 1. Main result

**All 21 fields: CONSEQUENCE.** None is STRONGER-THAN-SOURCE or NOT-A-PUBLISHED-STATEMENT, so the
review proposes no statement repair. None is PUBLISHED-FORM in the strict sense either. Each needs a
short derivation from the cited published statements (normalization of Frobenius, passing from
newforms to eigenforms, Chebotarev with Brauer–Nesbitt, Lemma QP for the polarization-free QM objects,
or an explicit computation). §§3-5 give the derivation for each field.

| group | fields | CONSEQUENCE | other |
|---|---|---|---|
| A (Shimura curves with QM) | 14 | 14 | 0 |
| A′ (theta functions, genus-2 Siegel forms) | 2 | 2 | 0 |
| F (Galois representations of modular forms) | 5 | 5 | 0 |

Standing caveats. None of them changes a verdict; all are recorded in the fields' own docstrings
except (d).
- (a) **Lemma QP.** Every A-group field over QM objects (`QMStr`, `QML3`, `QMPair`) omits the
  polarization and rests on Lemma QP: for N5's `μ` there is exactly one principal polarization with
  Rosati involution `x ↦ μ⁻¹x̄μ`. Its published locators (Buzzard 1997, Rotger 2003/2004) are
  UNVERIFIED. If they print only uniqueness, the existence half is glue.
- (b) **R1, open human check.** The audit's open item stands: whether Deligne's PEL model specializes
  to the polarization-free level-3 functor of `R1fpProps` still needs a human check. It is
  inherited by `r1r2`, `r1b`, `y3Connected` and `x6ConicModel`.
- (c) **Existential witness forms.** `r1r2`, `y3Connected` and `x6ConicModel` assert that some
  object satisfying the clause lists exists. `r1b` is stated for the triple that `Classical.choice`
  extracts from `r1r2`. These fields are false, not vacuous, if the clause lists are unsatisfiable.
  `r1b` needs the comparison argument (an isomorphism on all field points of reduced separated
  curves is an isomorphism; §5.2), which is a project argument, not a printed statement.
- (d) **Docstring error, not a statement error** (VERIFIED, computed). `QMDenZeroCM3`'s docstring says
  `jDen(Ω(i√3))` has "a zero of order 30 in `τ`". The order is 10: `Σθ⁸` and `∏θ²` both vanish to
  order 2 at `i√3`. So `ψ₄` and `χ₁₀` do have a common zero at `P₋₃`, against the docstring's "unless
  `ψ₄` and `χ₁₀` had a common zero". Proposed docstring text (not applied): replace "Consistent with
  `QMHauptmodul` (`j_θ` has its only pole at `P₋₃`) unless `ψ₄` and `χ₁₀` had a common zero on
  `Ω(ℍ)`. Numerically: `jDen(Ω(i√3)) = 0` with a zero of order 30 in `τ` (pkg-I1's pole of order 6
  of `j_θ`)." by "Consistent with `QMHauptmodul` (`j_θ` has its only pole at `P₋₃`). Numerically:
  at `i√3` both `Σθ⁸` and `∏θ²` vanish to order 2 in `τ`, so `jDen` vanishes to order 10 and `jNum`
  to order 4, giving pkg-I1's pole of order 6 of `j_θ` (`scratch/leaf-review-a/py/hauptmodul_check.py`)."

No Lean declaration is proved by this task (a review). The only Lean file is the check file
`scratch/leaf-review-a/Check.lean` (`#print` of the kernel copies of seven reviewed statements), §6. Hence there are no exact types of proved declarations and no `#print axioms` output to report.

## 2. Verdict table (one row per field)

| # | field | Lean name (file: `scratch/leaf-fold3/Leaves3.lean`, line) | cited source (UNVERIFIED locators) | verdict | reason (section) |
|---|---|---|---|---|---|
| 1 | `r1r2` | `HDec.LeafAdopt.R1R2fpRep`, l.19168 | Shimura, Ann. Math. 85 (1967) Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971) §§2-4; Baba–Granath, Canad. J. Math. 60 (2008) Thm 2.1, §3.1; González–Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6, Thm 5.12 | CONSEQUENCE | every clause holds for `(Y₃, X₆, π₆)` with Lemma QP; the three CM fibres are single `W`-orbits; the values `0, ∞, −16/27` are a `PGL₂(ℚ)` normalization (§5.1) |
| 2 | `r1b` | `HDec.G0Split.FibreQM.R1bFamily` (l.62736) at `ownY/ownΦ/ownπ` (bundle l.83176) | Shimura 1967 Main Thm I; Deligne 1971 §4.15 | CONSEQUENCE | Main Thm I composed with `π`; carried over to the chosen witness by the `R1univ`/`R1fam` comparison (§5.2) |
| 3 | `r1rec` | `HDec.LeafQM.AV.R1rec`, l.15571 | Shimura reciprocity (Shimura 1967 Main Thm II; Deligne 1971 §3) | CONSEQUENCE | field of moduli inside the ray class field mod 3 of `E ∈ {ℚ(i), ℚ(√−3), ℚ(√−6)}`, which is unramified at `p ≥ 5` (§5.3) |
| 4 | `r3` | `HDec.ZInQ.LeafPush2.R03_LinYang`, l.21402 | Lin–Yang, Math. Z. 295 (2020), Ex. 29; Baba–Granath 2008 Prop. 3.6; Weil's dichotomy | CONSEQUENCE | the tuple is Igusa's `J`-tuple (numerically matched); existential in `C`; `J₁₀ = 0` gives the product case (§5.4) |
| 5 | `r5` | `HDec.LeafQM.AV.R5fp`, l.15712 | González–Rotger 2006 Thm 5.12 | CONSEQUENCE | `D(R) ≠ 1 ⇔ b ≥ 1` when `(f, 6) = 1`; `[H_R:ℚ] = 2h(R)` (§5.5) |
| 6 | `r5count` | `HDec.LeafQM.AV.R5fpCount`, l.15745 | González–Rotger 2006 Prop. 5.6; Eichler's count of optimal embeddings | CONSEQUENCE | `h(R)∏_{p|6}(1−(R/p)) = 2^b h(R)` (§5.6) |
| 7 | `cmOptimalEmbedding` | `HDec.FS5NoCM.CMOptimalEmbedding`, l.57321 | Shimura 1967; Jordan, thesis (1981) §3; Eichler class number one | CONSEQUENCE | `End_𝒪(ℂ²/ι(𝒪)v_τ) = φ_τ(k)∩𝒪`; extend the ring isomorphism to fraction fields (§5.7) |
| 8 | `qmHauptmodul` | `HDec.PkgI1.QMHauptmodul`, l.336 | Igusa 1964/1967; Baba–Granath 2008; Lin–Yang 2020; valence formula | CONSEQUENCE (composite) | period matrix correct (numerical); each CM clause is one `Γ*`-orbit; degree one from a single simple pole at `P₋₃` (§5.8) |
| 9 | `qmClassNumberOne` | `HDec.G0Split.FibreQM.QMClassNumberOne`, l.63070 | Eichler's class number one (Vignéras Cor. III.5.7; Voight Cor. 28.5.17) | CONSEQUENCE | a stable lattice is `ι(I)v`, `I` invertible, `I = 𝒪α` (§5.9) |
| 10 | `qmDenZeroCM3` | `HDec.G0Split.FibreQM.QMDenZeroCM3`, l.62628 | R4 + valence formula for cocompact groups (Shimura 1971 §2); signature `(0;2,2,3,3)` of `𝒪¹` | CONSEQUENCE | weight-8 form for `𝒪¹` with zero count `4/3`, used up at the two order-3 points (§5.10); docstring order 30 → 10 (§1(d)) |
| 11 | `x6ConicModel` | `HDec.X6Kummer.X6ConicModel`, l.75647 | Kurihara 1979; Elkies, ANTS-III (1998) §3 | CONSEQUENCE | `(ℤ/2)²`-cover of `X₆/W` branched at the three CM points; fibre fields fix the constants (§5.11) |
| 12 | `y3Connected` | `HDec.TSHecke.Y3Connected`, l.97457 | Shimura; Deligne, Bourbaki 389 §§2-3 and PSPM 33 §2.1, Thm 2.6.3 | CONSEQUENCE | `π₀(Y₃,ℚ̄) = (ℤ/3)^×`, swapped by `Gal(ℚ(ζ₃)/ℚ)` (Weil-pairing invariant) (§5.12) |
| 13 | `qmAutCard` | `HDec.HeckeRest.QMAutCard`, l.98696 | Shimura 1963; Rotger, Crelle 561 (2003) §2 (classification of `End⁰`); units of imaginary quadratic orders | CONSEQUENCE | `QMIso q q ≃ com(q)^×`, `com(q) ∈ {ℤ, order in one imaginary quadratic field}` (§5.13) |
| 14 | `alFixedPoints` | `HDec.HeckeRest.ALFixedPoints`, l.98722 | Ogg 1983; Rotger, Trans. AMS 356 (2004) | CONSEQUENCE | `φ ∘ ι(t)` lies in `com(q)` with norm `|nrd t|`; splitting of `B` fixes the field; optimality fixes the order (§5.14) |
| 15 | `r4` | `HDec.PkgI1.ThetaModularity`, l.295 | Igusa, *Theta functions* (1972) Ch. V; Igusa, Amer. J. Math. 84 (1962), 86 (1964) | CONSEQUENCE | theta transformation formula (eighth roots of unity); `χ₁₀ = −2⁻¹⁴∏θ_m²` of weight 10; checked numerically (§4.1) |
| 16 | `thetaRatiosAlgebraic` | `HDec.G0Split.ThetaPt.ThetaRatiosAlgebraic`, l.43206 | Shimura, Duke 43 (1976); Mumford, Invent. Math. 1 (1966) and *Tata II* IIIa §8; Igusa 1962/1967 | CONSEQUENCE (composite) | the polarization is algebraic over `ℚ̄` (NS invariance); algebraic theta-nulls; at most one even theta-null vanishes in genus 2 (§4.2) |
| 17 | `r14` | `HDec.G0Galois.R14Det`, l.35290 | Shimura 1971 Thm 7.14; Deligne, Bourbaki 355 (1971) Thm 6.1; Deligne–Serre 1974 Thm 4.1; Ribet 1977 | CONSEQUENCE | published for eigenforms of `T_p`, `p ∤ N`; dual for the Tate normalization; semisimplification (§3.1) |
| 18 | `r15` | `HDec.HSyn.DeligneSerreConseq`, l.21903 | Deligne–Serre, Ann. Sci. ÉNS 7 (1974) Thm 4.1; Chebotarev; Brauer–Nesbitt | CONSEQUENCE | Artin representation transported to `ℚ̄_ℓ`; traces agree on dense Frobenii; Brauer–Nesbitt (§3.2) |
| 19 | `r16` | `HDec.LeafModCurves.R16_EichlerShimuraJ1'`, l.16804 | Shimura, J. Math. Soc. Japan 25 (1973) Thm 1; Shimura 1971 §7.4, Thm 7.11; Diamond–Shurman Thm 9.5.4 | CONSEQUENCE | `A_f` quotient, rank 2 over `K_f ⊗ ℚ_ℓ`, char. poly. `X² − a_pX + χ(p)p`; `θ ∘ c` absorbs conventions; any `IsJ1` Jacobian ≅ Shimura's (§3.3) |
| 20 | `r17` | `HDec.LadicCond.CarayolR17'`, l.40239 | Carayol, Ann. Sci. ÉNS 19 (1986) Théorème (A); Casselman 1973 | CONSEQUENCE | `condExp` = Serre–Tate conductor = WD conductor (Grothendieck monodromy); local Langlands preserves conductors; `a(π_p) = v_p(N)` (§3.4) |
| 21 | `t24` | `HDec.HSyn.EigenformTwist`, l.21912 | Shimura 1971 Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978) | CONSEQUENCE | `g' = Σψ(n)a_nqⁿ` works for any `ψ` mod `m` (finite Fourier expansion); full eigen relation checked (§3.5) |

No row has repaired text: no field is STRONGER-THAN-SOURCE or NOT-A-PUBLISHED-STATEMENT.

## 3. Group F: Galois representations of modular forms

Shared definitions (VERIFIED, read: `HDec.HSyn` §0 l.21761-21859 and `HDec.PkgI4` §0 l.4003-4060,
l.4502-4555; the two copies agree in content). `GQ = Gal(ℚ̄/ℚ)` with `ℚ̄ = AlgebraicClosure ℚ`;
`GaloisRep ℓ n` = continuous `GQ →* GL_n(PadicAlgCl ℓ)`; `IsArithFrob σ v p` = `σ` in the decomposition
group of the valuation ring `v` above `p` and `σx ≡ x^p` on `v`; `UnramifiedAt` = inertia acts trivially;
`IsSemisimple` = every invariant subspace has an invariant complement; `CF N k` = Mathlib cusp forms of
weight `k` on `Γ₁(N)`; `coeff f m` = `m`-th coefficient of the period-1 `q`-expansion;
`IsNormalizedEigenform f χ` = nebentypus `χ` on `Γ₀(N)` (via `f ∣[k] γ = χ(d) f`), `a₁ = 1`, and
`a_m a_n = Σ_{d | (m,n)} χ(d) d^{k−1} a_{mn/d²}` for **all** `m, n ≥ 1` (so eigen for every `T_n`,
including `U_p`, `p | N`); `AttachedTo ρ ιC ιL g` = for `p ∤ Nℓ`, `ρ` unramified at `p` and every
arithmetic Frobenius has trace `ιL(α)` where `ιC(α) = a_p(g)` (Tate-module normalization).
`IsNewform f χ` = `IsNormalizedEigenform f χ` and `f ∉ oldSpace N k` (span of `f(dτ)`, `f` of level
`M | N`, `M < N`, `dM | N`).

Normalization remark (applies to F.1-F.4): the published constructions (Deligne's `H¹_ét`) give
`tr ρ(Frob_p^{geom}) = a_p`; the contragredient then has `tr ρ^∨(Frob_p^{arith}) = a_p` and
`det ρ^∨(Frob_p^{arith}) = χ(p)p^{k−1}`. So whichever convention a source uses, a representation in the
Lean normalization exists, and conductors, finiteness of image and semisimplicity are unchanged by
passing to the dual. STANDARD.

### F.1 `r14 : G0Galois.R14Det` — CONSEQUENCE

Statement (l.35290): for every prime `ℓ`, embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`, `N > 0`, `k ≥ 1`,
`χ` mod `N` and `g ∈ S_k(Γ₁(N))` with `IsNormalizedEigenform g χ`, there is a semisimple `ρ` attached to
`g` and a character `ε : GQ → ℚ̄_ℓ^×` of finite image with `det ρ(σ) = ε(σ) χ_ℓ(σ)^{k−1}` for all `σ`
(`cycQ ℓ` = Mathlib's `cyclotomicCharacter ℚ̄ ℓ`, so `χ_ℓ(Frob_p^{arith}) = p`).

Derivation. (i) `g` is an eigenform of all `T_p`, `p ∤ N`, with nebentypus `χ`; Deligne 1971 (Sém.
Bourbaki 355, Thm 6.1, UNVERIFIED number) for `k ≥ 2` (Eichler–Shimura–Igusa for `k = 2`) and
Deligne–Serre 1974 Thm 4.1 (UNVERIFIED) for `k = 1` are stated for such forms (if a reader takes them
for newforms only: by Atkin–Lehner–Li the eigenvalues of `g` away from `N` are those of a newform of
level `M | N`, whose representation serves, since `AttachedTo` only constrains `p ∤ Nℓ`). They give
`ρ_g : G_ℚ → GL₂(K_{g,λ})` unramified outside `Nℓ` with `tr = a_p`, `det = χ(p)p^{k−1}` at Frobenius
(geometric or arithmetic, see the remark). (ii) Take `λ` the place of the Hecke field
`K_g = ℚ(a_n) ⊂ ℂ` induced by `ιL ∘ ιC⁻¹` (the `a_n` are algebraic, so `α` exists and is unique);
`K_{g,λ} → ℚ̄_ℓ` is an isometric embedding, so continuity holds for the norm topology of `PadicAlgCl ℓ`.
For `k = 1` the image is finite, the representation is realized over `ℚ̄ ⊂ ℂ` and transported by
`ιL ∘ ιC⁻¹`. (iii) Semisimplicity: Ribet 1977 (irreducibility for `k ≥ 2`; UNVERIFIED) or replace `ρ` by
its semisimplification, which has the same traces and determinant. (iv) `det ρ_g = ε χ_ℓ^{k−1}` with
`ε` the finite-order character with `ε(Frob_p) = χ(p)` (Chebotarev: a continuous character is
determined by its Frobenius values). No hypothesis is missing and no quantifier is stronger than the
sources (the conclusion is existential in `ρ`, `ε`).

### F.2 `r15 : DeligneSerreConseq` — CONSEQUENCE

Statement (l.21903): every semisimple `ρ : GQ → GL₂(ℚ̄_ℓ)` attached (in the sense above) to a
normalized eigenform `g ∈ S₁(Γ₁(N))` with nebentypus has finite image.

Derivation (as the docstring says, and as I4-L3 `PkgI4.DeligneSerreFinite` l.4609, identical body).
Deligne–Serre Thm 4.1 gives an Artin representation `ρ₀ : G_ℚ → GL₂(ℂ)` with `tr ρ₀(Frob_p) = a_p` for
`p ∤ N` (its dual if the source's Frobenius is geometric; the dual is again Artin). Its finite image
makes it realizable over a number field `E ⊂ ℂ`, hence over `ιC(ℚ̄)`; transported by `ιL ∘ ιC⁻¹` it is a
continuous `ρ₀' : GQ → GL₂(ℚ̄_ℓ)` with finite image (open kernel), semisimple (Maschke), with Frobenius
traces equal to those of `ρ` at all `p ∤ Nℓ`. Arithmetic Frobenius elements at `p ∉ S` (`S` finite) are
dense in `GQ` (Chebotarev, e.g. Neukirch VII.13.4, UNVERIFIED number), traces are continuous, so
`tr ρ = tr ρ₀'` on `GQ`; Brauer–Nesbitt (char 0, both semisimple) gives `ρ ≅ ρ₀'`, so `ρ` has finite
image. Semisimplicity of `ρ` is needed (a non-split extension has the same traces) and is a hypothesis.
`HasNebentypus` at `k = 1` forces `χ(−1) = −1` (Mathlib's slash of `−I` in odd weight is `−f`), which is
consistent with `a₁ = 1`; no vacuity.

### F.3 `r16 : LeafModCurves.R16_EichlerShimuraJ1'` — CONSEQUENCE

Statement (l.16804): for `N > 0`, a newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ` and any `J` with
`IsJ1 N J` (a Jacobian, in the Albanese sense, of some smooth proper geometrically connected integral
curve over `ℚ` with function field `≅ ℚ(j)(x(P))`, `P` of exact order `N` on `E_j`, with some rational
base point): `K_f = ℚ(a_n(f)) ⊂ ℂ` is finite over `ℚ`, and there are `A`, a surjective `π : J → A`, and
`θ : K_f → End⁰(A)` with `dim A = [K_f : ℚ]` such that for every `ℓ` and every `emb : K_f → ℚ̄_ℓ` the
space `eigenFun` of `ℚ_ℓ`-linear `φ : V_ℓ(A) → ℚ̄_ℓ` with `φ ∘ θ(a) = emb(a) φ` has dimension 2, and for
`p ∤ Nℓ` and every arithmetic Frobenius `σ` (`IsFrobAt`, via a prime of `ℤ̄` over `p`), the transpose
action `φ ↦ φ ∘ ρ_ℓ(σ)` on `eigenFun` has trace `emb(a_p)` and determinant `emb(χ(p))·p`.

Definitions checked (VERIFIED, read l.16485-16700, l.11457): `eigenFun` is `Hom_{K_f ⊗ ℚ_ℓ}(V_ℓ A, ℚ̄_ℓ)`
(through `emb`), i.e. the dual of the `emb`-component of `V_ℓ(A) ⊗ ℚ̄_ℓ`; `frobOn` is the transpose of
`σ` on that component, so its trace and determinant are those of `σ` on the component.

Derivation. (i) Shimura 1973 Thm 1 (unconditional part; UNVERIFIED locator, as in the docstring): the
quotient `A_f = J₁(N)/I_f J₁(N)` over `ℚ` with `K_f ↪ End⁰(A_f)` and `dim A_f = [K_f:ℚ]`. (ii) `V_ℓ(A_f)`
is free of rank 2 over `K_f ⊗ ℚ_ℓ` (Shimura 1971 §7.4 / Ribet 1977, UNVERIFIED), which gives
`dim eigenFun = 2` for every `emb`. (iii) Characteristic polynomial `X² − a_pX + χ(p)p` of arithmetic
Frobenius on `V_ℓ(A_f)` over `K_f ⊗ ℚ_ℓ` for `p ∤ Nℓ` (Diamond–Shurman Thm 9.5.4 / Shimura 1971 Thm 7.11,
UNVERIFIED numbers), from the Eichler–Shimura relation. If the Hecke action convention (Albanese vs
Picard, `⟨p⟩` vs `⟨p⟩⁻¹`) gives `ā_p`, `χ̄(p)`, replace `θ` by `θ ∘ c` (`K_f` is CM or totally real, stable
under `c`); since `θ` is existential and `emb` universal, the statement is unaffected (VERIFIED by the
computation `eigenFun(θ∘c, emb) = eigenFun(θ, emb∘c)`). (iv) Every `J` with `IsJ1 N J` is isomorphic to
Shimura's `J₁(N)`: the `K_N` models are `ℚ`-isomorphic to Shimura's canonical model (function field
`ℚ(j, f_{(0,1/N)})`, Shimura 1971 §6.7, UNVERIFIED), Jacobians are unique (`IsJacobian.unique`, proved),
and the conclusion is invariant under isomorphism of `J`. For `N ≤ 4` there is no weight-2 newform, so
the statement is vacuous there; no other vacuity (`IsJ1` is satisfiable, cusps are rational).

### F.4 `r17 : LadicCond.CarayolR17'` — CONSEQUENCE

Statement (l.40239): for a weight-2 newform `f` of level `N > 0` with nebentypus, any semisimple `ρ`
attached to `f`, and any prime `p ≠ ℓ`: `condExp (ρ|_{G_{ℚ_p}}) = v_p(N)`.

Definitions checked (VERIFIED, read l.39965-40060, l.4062-4085). `condExp ρ = codim V^{I_p} + swan ρ`,
`I_p = {σ : |σx − x| < 1 for |x| ≤ 1}` on `ℚ̄_p`; `swan ρ = swanAt L ρ` at a chosen finite Galois `L`
adapted to `ρ` (`ρ` trivial on `P_p ∩ G_L`), `swanAt L ρ = Σ_{i≥1} (g_i/g_0) codim V^{G_i ∩ P}` with
`ramSet L i` = `{σ : v_L(σx − x) ≥ i + 1 on 𝓞_L}` and `g_i = #(ramSet L i)|_L`. These are Serre's
lower-numbering groups and the Swan conductor; for adapted `L` the set `ramSet L i ∩ P_p` (`i ≥ 1`) acts
through `G_i(L/ℚ_p)`, so `swanAt L` is the Swan conductor of `ρ|_{P_p}` (independence of `L`: Herbrand,
the docstring's `SwanIndependent`, true). `restrictLocal` = composition with Mathlib's restriction map
`G_{ℚ_p} → G_ℚ` (some embedding `ℚ̄ → ℚ̄_p`; conjugation does not change `condExp`).

Derivation. (i) Chebotarev + Brauer–Nesbitt: `ρ ≅ ρ_{f,λ}^∨ ⊗ ℚ̄_ℓ` (or `ρ_{f,λ}`, depending on the
source's convention), `λ` induced by `ιL ∘ ιC⁻¹`. (ii) `codim V^{ρ(I_p)} = codim (ker N)^{I_p}` for the
Weil–Deligne representation `(r, N)` of `ρ|_{G_{ℚ_p}}` (Grothendieck's monodromy theorem: on an open
subgroup of `I_p`, `ρ = exp(t_ℓ N)`, so invariants lie in `ker N`; STANDARD, Deligne 1973 §8 / Tate,
Corvallis, UNVERIFIED locators), and the Swan conductors agree, so `condExp` is the conductor exponent
of `WD(ρ|_{G_{ℚ_p}})`. Duals have the same conductor (`[ker N] = [coker N]` as `r(I)`-modules, `r(I)`
finite). (iii) Carayol 1986, Théorème (A) (local–global compatibility at `p ≠ ℓ`, all `p` including
`p | N` and all `ℓ` including 2, per the docstring's locator audit; UNVERIFIED here): `WD(ρ_{f,λ}|_{G_{ℚ_p}})`
corresponds to `π_{f,p}` under local Langlands, which preserves conductors; Casselman 1973: the conductor
of `π_{f,p}` for a newform is `v_p(N)` (UNVERIFIED). Hypotheses `IsNewform` (not just eigenform) and
`p ≠ ℓ` are present; the statement is not stronger than the source.

### F.5 `t24 : EigenformTwist` — CONSEQUENCE

Statement (l.21912): for `N, m > 0`, `χ` mod `N`, **any** Dirichlet character `ψ` mod `m` (not
necessarily primitive) and `g ∈ S_k(Γ₁(N))` with `IsNormalizedEigenform g χ`, there are `χ'` mod `Nm²`
and `g' ∈ S_k(Γ₁(Nm²))` with `IsNormalizedEigenform g' χ'` and `a_p(g') = ψ(p)a_p(g)` for primes `p ∤ Nm`.

Derivation. Shimura's Prop. 3.64 (UNVERIFIED number) is stated for primitive `ψ` mod `r`, giving
`g_ψ = Σ ψ(n)a_n qⁿ ∈ S_k(Nr², χψ²)`; for an arbitrary `ψ` mod `m` take the same `g' := Σ ψ(n) a_n qⁿ`:
(a) writing `ψ(n) = Σ_{u mod m} c_u e(un/m)` (finite Fourier expansion of any function on `ℤ/m`),
`g' = Σ_u c_u g(τ + u/m)`; conjugation by `(1 u/m; 0 1)` maps `Γ₁(Nm²)` into `Γ₁(N)` (VERIFIED by the
matrix computation: entries `a − uc/m ≡ 1 (N)`, `b + u(a−d)/m − u²c/m² ∈ ℤ`, `d + uc/m ≡ 1 (N)`), so
`g' ∈ S_k(Γ₁(Nm²))`; for `γ ∈ Γ₀(Nm²)` the same conjugation sends `u ↦ ud²` and
`c_{ud^{-2}} = ψ(d)²c_u`, giving nebentypus `χ' = χψ²` (changed to level `Nm²`); (b) `a₁(g') = ψ(1) = 1`;
(c) the coefficient relation for all `m', n'`: if `(m'n', m) = 1`, `ψ(d)²ψ(m'n'/d²) = ψ(m')ψ(n')`;
otherwise both sides vanish (`ψ(m')ψ(n') = 0`, and each term has `ψ(d) = 0` or `ψ(m'n'/d²) = 0`); and
`χ'(d) = 0` exactly when `(d, Nm) > 1` (VERIFIED, hand computation). So `g'` is a normalized eigenform
in the file's sense, with `a_p(g') = ψ(p)a_p(g)` for all `p`. The statement is weaker than this
(existential, only `p ∤ Nm`). Note: the docstring's "Consequence" is right; it is elementary given
Shimura's Prop. 3.64 or even without it.

## 4. Group A′: theta functions and Siegel modular forms of genus 2

### A′.1 `r4 : PkgI1.ThetaModularity` — CONSEQUENCE

Statement (l.295): for `M ∈ Matrix.symplecticGroup (Fin 2) ℤ` and `Ω` in the Siegel space,
`Σ_{m even} θ_m⁸(M·Ω) = det(CΩ+D)⁴ Σθ_m⁸(Ω)` and `∏_{m even} θ_m²(M·Ω) = det(CΩ+D)¹⁰ ∏θ_m²(Ω)`, with
`θ_m(Ω) = Σ_n exp(πi vᵀΩv + πi vᵀb)`, `v = n + a/2` (l.224).

Definitions checked (VERIFIED, read l.199-262): ten even characteristics (`card_evenChars`, decided);
`spAct`, `spFactor` the standard block formulas; Mathlib's `symplecticGroup` is `M J Mᵀ = J` with
`J = [[0, −1],[1, 0]]`, the same group as for the opposite sign convention.

Derivation. Igusa's theta transformation formula (Igusa, *Theta functions* (1972), Ch. V, Thm 5,
UNVERIFIED number): `θ_{M·m}(M·Ω) = κ(M) e(φ_m(M)) det(CΩ+D)^{1/2} θ_m(Ω)` with `κ(M)` and `e(φ_m(M))`
eighth roots of unity, and `M` permutes the even characteristics; eighth powers give the first identity.
The second: Igusa, *On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964) (UNVERIFIED
locator): `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²` is a Siegel modular form of weight 10 for `Sp₄(ℤ)` (trivial
character). Independent numerical check (VERIFIED, computed, `scratch/leaf-review-a/py/theta_mod_check.py`):
both ratios equal 1 to ≥ 24 digits at one `Ω` for five symplectic matrices (Mathlib's `J`, two symmetric
translations, `diag(U, U^{−T})`, a partial `J`).

### A′.2 `thetaRatiosAlgebraic : ThetaPt.ThetaRatiosAlgebraic` — CONSEQUENCE

Statement (l.43206): for `A` over a number field `K`, `σ : K → ℂ`, an analytic uniformization
`Φ : ℂ² → A(ℂ)_σ` with kernel `Λ`, and any `Ω ∈ 𝔥₂` with `IsPeriodMatrix Λ Ω` (some `ℂ`-linear `T` with
`T(Λ) = Ωℤ² + ℤ²`): some `θ_{m₀}(0, Ω) ≠ 0` and every `θ_m(0,Ω)/θ_{m₀}(0,Ω)` is algebraic.

Definitions checked (VERIFIED, read l.21078-21115): `thetaConst Ω m` is the standard theta constant
(odd `m` give 0, algebraic); `IsPeriodMatrix` encodes "a principal polarization with a symplectic basis".

Derivation. (i) The principal polarization of `ℂ²/(Ωℤ²+ℤ²)` pulled back by `T` is a class in
`NS(A_ℂ) = NS(A_ℚ̄)` (Néron–Severi is invariant under extension of algebraically closed fields of char 0;
Appell–Humbert + GAGA identify analytic and algebraic polarizations), so `(A_ℚ̄, λ)` is a principally
polarized abelian surface over `ℚ̄` and `Ω` is one of its period matrices. (ii) For a ppav over `ℚ̄`, the
ratios of the squares of theta constants are values of the algebraic theta-null coordinates of a
theta structure defined over `ℚ̄` (Mumford, *On the equations defining abelian varieties I*, Invent.
Math. 1 (1966), with the analytic comparison in *Tata lectures on theta III*; or Shimura, Duke 43 (1976);
for genus 2, Thomae's formula, Mumford *Tata II* IIIa §8, and for products Jacobi's formulas; UNVERIFIED
locators); square roots of algebraic numbers are algebraic. (iii) Nonvanishing: in genus 2 at most one
even theta constant vanishes (exactly on products of elliptic curves; Igusa 1962/1967, UNVERIFIED). The
docstring's own label "leaf candidate, composite" is accurate: it is not one printed theorem.

## 5. Group A: Shimura curves with QM

Shared objects (VERIFIED, read). `B = QuaternionAlgebra ℚ 2 0 (−3)` (discriminant 6) and its maximal
order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` (several verbatim copies: l.151/9382/14264/21238). `PkgI3.AbVar K`
(l.2587): a group object over `Spec K` that is proper, smooth and geometrically integral. `QMStr A`
(l.14323): an injective unital ring map `𝒪 → End_K(A)`. `Level3` (l.14362): an `𝒪`-linear
`η : 𝒪 → A(K)` with kernel `3𝒪`. `QML3`, `M3`: level-3 QM surfaces and their iso classes. `QMPair`,
`pairSetoid`: QM surfaces up to `𝒪`-equivariant isomorphism. `QMIso` (l.14837): an `𝒪`-equivariant
isomorphism (two inverse homs). `com q` (l.14899): the centralizer of `ι(𝒪)`. `HasCM4/3/24`
(l.14902-14906): `com` contains `φ` with `φ² = −1`, `φ² − φ + 1 = 0`, `φ² = −6`. `PtEquiv Y`
(l.15176): for every field `K ⊇ ℚ`, a bijection `Y(K) ≃ M3 K`. `R1fpProps` (l.15235): proper, smooth of
relative dimension 1, a `ℚ̄`-point, naturality in `K`, `R1famProps`, `R1univProps`. No polarization
appears anywhere (caveat (a)). Detailed notes for rows 1-11: `scratch/leaf-review-a/notes_A1.md`
(rows 1-3, 5-7) and `notes_A2.md` (rows 4, 8-11). Both were written by forks of this task, and I
checked them against the Lean text (log).

### 5.1 `r1r2 : LeafAdopt.R1R2fpRep` (l.19168) — CONSEQUENCE
`∃ Y Φ X Ψ fY π₆` with: `R1fpProps`; `R1heckeProps` (twists by `Aut 𝒪` and `rightMul u` are induced by
automorphisms of `Y`); `X6Props`; `R2X6PropsIff` (fibres of `π₆` = `Aut 𝒪`-twist classes, and
`HasCM4 ⇔ π₆ = 0`, `HasCM3 ⇔ ∞`, `HasCM24 ⇔ −16/27`); `R1recProps`; `X6Surj`; `R5ptProps`;
`R1pi0Props X` (`X₆` geometrically connected). Witnesses: `Y₃` (fine moduli at the neat level
`K₃ = (1+3𝒪̂)^×`), `X₆ = X₀⁶(1)` (Shimura's canonical model, coarse), and `π₆ : X₆ → X₆/W ≅ P¹`
(Baba–Granath Thm 2.1). Each CM set `CM(−4)`, `CM(−3)`, `CM(−24)` has `2^b h = 2` points and is one
`W`-orbit: for `ℤ[i]`, `ℤ[ζ₃]`, the `w_p` with `p` inert swaps the two points; for `ℤ[√−6]`, `w₂` acts as
the nonprincipal class `(2, √−6)`. The three images are rational and distinct, and `PGL₂(ℚ)` moves them
to `0, ∞, −16/27`, so the normalization costs nothing. `π₀(X₆,ℚ̄) = ℤ̂^×/nrd(𝒪̂^×) = 1` (Deligne §2).
Caveats (a), (b).

### 5.2 `r1b` (l.83176: `∀ h, R1bFamily (ownY h) (ownΦ h) (ownπ h)`; `R1bFamily` l.62736) — CONSEQUENCE
`∃ τ ↦ y_τ ∈ Y(ℂ)` such that the object at `y_τ` has an `ι`-compatible analytic uniformization with
kernel exactly `Λ_τ = ι(𝒪)(τ,1)ᵀ`, and `τ ↦ π(y_τ)` is continuous and holomorphic into `P¹(ℂ)`
(`IsR1bFamily`, l.62715). For the genuine `Y₃` this is Shimura's Main Thm I composed with the morphism
`π`, with `y_τ` on the component of `η_τ(a) = ι(a)v_τ/3`. For the triple chosen by `Classical.choice`:
both triples satisfy `R1fpProps` (`own_spec`, l.62507), so `R1univProps` applied to each other's
universal families (from `R1famProps`) gives `g : Y_own → Y₃` and `g'` back. Both composites are the
identity on all field points, hence the identity (reduced source, separated target). So `g` is an
isomorphism, and `y'_τ = g⁻¹(y_τ)` works. This comparison is a project argument (caveat (c)).

### 5.3 `r1rec : LeafQM.AV.R1rec` (l.15571) — CONSEQUENCE
For `P : QML3 ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`, `fieldOfModuli3 P` is a number field
unramified at all `p ≥ 5`. Shimura reciprocity on the canonical model: the stabilizer computation
`Ê^× ∩ g(1+3𝒪̂)g⁻¹ = 1 + 3𝒪̂_E` (optimal embedding) puts `E(y)` in the ray class field of `E` of
conductor 3. `E/ℚ` is ramified only at 2 and 3. The field of moduli is the residue field of the point
of the fine space `Y₃`.

### 5.4 `r3 : ZInQ.LeafPush2.R03_LinYang` (l.21402) — CONSEQUENCE
Every abelian surface over `ℂ` with QM by `𝒪` is either `≅ Jac C` (as group schemes), for a genus-2 curve
`C` with a sextic model whose Igusa `J`-tuple is weighted-projectively
`[12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]` for some `j ≠ 0`, or `≅ E₁ × E₂`. The `IC`/`IgJ` formulas
(l.21267-21304) are Igusa's 1960 formulas. The fork compared the tuple numerically with the
Hashimoto–Murabayashi discriminant-6 family (recalled from memory, UNVERIFIED) at 3 parameters, to 12
digits: it is the `J`-tuple, not an Igusa–Clebsch tuple (`py/linyang_tuple_check.py`). Derivation:
give `(A, ι)` the principal polarization of the type the family uses (Lemma QP, one per type); if
`J₁₀ = j³ ≠ 0` then `(A, L) ≅ (Jac C, Θ)`; if `j ∈ {0, ∞}` then `J₁₀ = 0`, and Weil's dichotomy gives a
product. The statement is existential and has no polarization, so it is no stronger than the source.

### 5.5 `r5 : LeafQM.AV.R5fp` (l.15712) — CONSEQUENCE
`k` imaginary quadratic, `R ⊆ 𝒪_k` of conductor prime to 6, and `P` with `com P.q ≅ R`: then
`[ℚ(x):ℚ] = (b = 0 ? 1 : 2)·#Pic R`, and `k ↪ ℚ(x)` if `b ≥ 1` (`b` = number of `p ∈ {2,3}` inert in
`k`). This is González–Rotger Thm 5.12 at `D = 6, N = 1`: `(f, 6) = 1` gives `(R/p) = (k/p)`, so
`D(R) ≠ 1 ⇔ b ≥ 1`. With `[H_R:ℚ] = 2h(R)`, the printed fields have exactly these degrees. If 2 or 3
splits in `k`, there are no such `P` and the statement is vacuous, which is correct.

### 5.6 `r5count : LeafQM.AV.R5fpCount` (l.15745) — CONSEQUENCE
The number of `ℚ̄`-classes with `com ≅ R` is `2^b·#Pic R`. This is Eichler's count
`h(R)∏_{p|6}(1 − (R/p))`: ramified `p` give 1 and inert `p` give 2. Embeddings modulo `𝒪¹` with a
fixed point in `ℍ` correspond to embeddings modulo `𝒪^×` (the unit `1+i` has norm `−1`), so the count
on `X₆ = 𝒪¹\ℍ` is González–Rotger's `#CM(R)`. Checked: `ℤ[i]`, `ℤ[ζ₃]` give 2, `ℤ[√−6]` gives 2, and
the disc −19 order gives 4.

### 5.7 `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` (l.57321) — CONSEQUENCE
If `com P.q ≅ R`, then there is `φ : k → B` with `φ⁻¹(𝒪) = R`. Over `ℂ`, `H₁(A)` is a free rank-one
`𝒪`-module (Eichler), so `A = ℂ²/ι(𝒪)v_τ`, `End_𝒪(A) ≅ φ_τ(k_τ) ∩ 𝒪`. Extending the ring isomorphism to
fraction fields gives `φ`. The names `B`, `O` in this block resolve to one of the verbatim copies; all
copies have the same meaning (Lean resolution not compiled here, because the flat file takes 1042 s).

### 5.8 `qmHauptmodul : PkgI1.QMHauptmodul` (l.336) — CONSEQUENCE (composite)
There is a continuous `f : ℍ → P¹(ℂ)` with: `f = jNum/jDen ∘ Ω` where `jDen ≠ 0`; fibres exactly the
`Γ*`-orbits; `f` surjective; values `0, ∞, −16/27` at the fixed points of `ι(x)`, `x ∈ 𝒪`,
`x² = −1`, `x² − x + 1 = 0`, `x² = −6`.
- Period matrix (VERIFIED, computed; my re-run of the fork's `py/hauptmodul_check.py`). `Ω(τ)` is
  symmetric with `Im Ω ≻ 0` (eigenvalues 0.5 and 1 at `√2+i`). `j_θ` is invariant to `≤ 3·10⁻³⁵` under
  `ι(j)` (det 3), `ι(2j+ij)` (det 6) and `ι((1+j)/2)` (det 1). `j_θ(√2+i) ≈ 10⁻¹⁶²` and
  `j_θ(i√(9+6√2)) = −0.592592592592593`.
- One orbit per clause. Each of `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` has 2 optimal embeddings modulo `𝒪¹`, and
  `X₆ → X₆/W` (degree 4) has `e = 2` over each branch point. So each clause concerns one `Γ*`-orbit.
- Degree one. By §5.10, `jDen ∘ Ω` vanishes only on the `P₋₃` orbit, to order 10 in `τ`, and `jNum`
  to order 4 there (computed). So `j_θ` has a single pole on the genus-0 curve `Γ*\ℍ`, of order
  `6/6 = 1` in the local coordinate `(τ−τ₀)⁶`. It therefore has degree 1, its fibres are the orbits,
  and it is surjective.
- The two steps that rest on computation, not on a printed statement, are `ord_{P₋₃}∏θ² = 2` and the
  exact value `−16/27`. Baba–Granath's CM values of the Hauptmodul normalized by `0` at `P₋₄` and `∞`
  at `P₋₃` would supply the latter. The docstring's own label ("composite, not printed as one
  theorem") is accurate.

### 5.9 `qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne` (l.63070) — CONSEQUENCE
Every full `ι(𝒪)`-stable lattice `Λ ⊂ ℂ²` equals `ι(𝒪)w` (`qmOrbit`), with `w` not a complex multiple of a
real vector. `ℚΛ = ι(B)v` and `Λ = ι(I)v` with `I` an invertible left `𝒪`-ideal; class number one gives
`I = 𝒪α`. A real `w` (up to a scalar) would give real rank 2.

### 5.10 `qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3` (l.62628) — CONSEQUENCE
`jDen(Ω(τ)) = 0 ⇒ τ` is fixed by `ι(x)`, `x² − x + 1 = 0`. Put `g(τ) = Σθ⁸(Ω(τ))/((τ−3)(τ+1))⁴`.
`det F₀(τ) = −√2(τ−3)(τ+1)/2` has no zero on `ℍ`. Since `Ω(γτ) = M_γΩ(τ)` with `M_γ ∈ Sp₄(ℤ)` for
`γ ∈ 𝒪¹` (a computation), R4 makes `g` a holomorphic weight-8 form for `𝒪¹`; the automorphy factor
`(cτ+d)⁸` was checked numerically. The valence formula for the cocompact group of signature `(0;2,2,3,3)`
(`vol/2π = 1/3`) gives a zero count `8/2·1/3 = 4/3`. At an elliptic point of order 3, a weight-8 form
vanishes to order `≡ 2 (mod 3)`. The two order-3 points (the `ℤ[ζ₃]` CM points) therefore use up `4/3`,
and there are no other zeros. The docstring error is in §1(d).

### 5.11 `x6ConicModel : X6Kummer.X6ConicModel` (l.75647) — CONSEQUENCE
Some witness of `R1R2fpFullProps` has a Galois-equivariant bijection `X(ℚ̄) ≃ C(ℚ̄)` with
`C : Y² + 3X² + 3Z² = 0` and `π₆ = −16(X²+Z²)/(27Z²)`. Derivation: `X₆ → X₆/W` is a `(ℤ/2)²`-cover over
`ℚ` branched at the three CM points with `e = 2`, so `ℚ(X₆) = ℚ(t)(√(αt), √(β(t−1)))`. The fibre fields
are `ℚ(i)` over the `ℤ[i]` points (R5: `b = 1`, `h = 1`) and `ℚ(√−3)` over the `ℤ[ζ₃]` points. This
forces `α = −1`, `β = 3`, i.e. this conic with `t = −X²/Z²`, `π₆ = 16(t−1)/27` (VERIFIED by hand:
`3(t−1) = Y²/Z²`). This matches Elkies 1998 §3 and Kurihara 1979 after a Möbius change of coordinate.
Caveat (c).

### 5.12 `y3Connected : TSHecke.Y3Connected` (l.97457) — CONSEQUENCE
Some `(Y, Φ)` with `R1fpProps` has `Y` connected. Derivation: `Y₃` satisfies `R1fpProps` (R1, §5.1).
Shimura/Deligne: `π₀(Y₃ ×_ℚ ℚ̄) = ℚ^×_{>0}\𝔸_f^×/nrd(K₃) = ℤ̂^×/(∏_{ℓ≠3}ℤ_ℓ^× × (1+3ℤ₃)) = (ℤ/3)^×`,
two points. A concrete invariant separates them. With the canonical polarization (Lemma QP), the Weil
pairing on `A[3] ≅ 𝒪/3𝒪` (via `η`) is `ζ^{c·Trd(μ⁻¹xȳ)}` for a primitive cube root of unity `ζ`
determined by `(A, ι, η)` (unchanged under `η ↦ −η`). `σ ∈ Gal(ℚ̄/ℚ)` sends `ζ` to `σ(ζ)`, so the two
geometric components are swapped by `Gal(ℚ(ζ₃)/ℚ)`, and `Y₃` is connected over `ℚ`. leaf-fold3's proved
transfer `connectedSpace_of_R1fp` then gives it for every triple. Caveats (a)-(c).

### 5.13 `qmAutCard : HeckeRest.QMAutCard` (l.98696) — CONSEQUENCE
For `A/ℚ̄` of dimension 2 with QM `q`: `#QMIso q q = 4` if `HasCM4`, `6` if `HasCM3`, `2` otherwise; and no
two of `HasCM4`, `HasCM3`, `HasCM24` hold together. Derivation: `QMIso q q ≃ com(q)^×` (a `QMIso` is
determined by `φ.hom`: `qmIso_ext`, l.98734, proved). In characteristic 0, `End⁰(A) ⊇ B` (`B` division)
forces `End⁰(A) = B`, with `com = ℤ`, or `A ~ E²`, `E` CM by `K` splitting `B`, `End⁰ = M₂(K)`, with
`com` an order `R` of `K` (Shimura 1963; Rotger 2003 §2). `ℤ[i]` and `ℤ[ζ₃]` are maximal, so `HasCM4 ⇒
R = ℤ[i]` (4 units) and `HasCM3 ⇒ R = ℤ[ζ₃]` (6 units); every other order, and `ℤ`, has units `±1`
(`−1 ≠ 1` since `A ≠ 0`). Disjointness holds because `ℚ(i)`, `ℚ(√−3)`, `ℚ(√−6)` are distinct and `com`
lies in one field. STANDARD.

### 5.14 `alFixedPoints : HeckeRest.ALFixedPoints` (l.98722) — CONSEQUENCE
If `(A, q ∘ rep k) ≅ (A, q)` for `k = 1, 2, 3` (`rep k` = conjugation by `t = i, j, ij`, `nrd t = −2, 3,
−6`; l.56001-56008), then `HasCM4`, `HasCM3`, `HasCM24` respectively. Derivation (my own; it matches
the docstring's sketch):
- From `φ ∘ ι(tat⁻¹) = ι(a) ∘ φ` (or the symmetric form), `ψ := φ ∘ ι(t)` commutes with `ι(𝒪)`, so
  `ψ ∈ com(q)`, with `deg ψ = deg ι(t) = nrd(t)² = m²` (`m = |nrd t|`). `ψ ∉ ℤ`, because `n⁴ = m²` has
  no integer solution for `m ∈ {2,3,6}`. So `com(q) = R` is an imaginary quadratic order containing an
  element of norm `m`, in a field `K` that splits `B` (2 and 3 not split in `K`).
- `m = 2`: the candidates `ℚ(i)`, `ℚ(√−2)`, `ℚ(√−7)`; only `ℚ(i)` splits `B`. `1+i ∈ R` gives
  `R = ℤ[i]`.
- `m = 3`: `ℚ(√−3)`, `ℚ(√−2)`, `ℚ(√−11)`; only `ℚ(√−3)`. Then `R ∈ {ℤ[ζ₃], ℤ[√−3]}`, and
  `ℤ[√−3]` is excluded because `R = φ_τ(K) ∩ 𝒪` is optimally embedded and `𝒪 ⊗ ℤ₂` is the maximal
  order of the local division algebra, which contains `ζ₃`.
- `m = 6`: the candidates `ℚ(√−6)`, `ℚ(√−5)`, `ℚ(√−2)`, `ℚ(√−15)`, `ℚ(√−23)`; only `ℚ(√−6)`. The
  norm-6 elements of `ℤ[√−6]` are `±√−6`, so `R = ℤ[√−6]`.
- Inputs: the classification used in §5.13, `deg ι(x) = nrd(x)²`, the local criterion for embedding
  quadratic fields in `B`, and `End_𝒪(A_τ) = φ_τ(K) ∩ 𝒪` (§5.7). All STANDARD (Shimura 1967; Jordan
  1981; Ogg 1983 for the fixed points of `w_m`).

## 6. Check file

`scratch/leaf-review-a/Check.lean` imports five kernel modules and `#print`s the kernel copies of
`R16_EichlerShimuraJ1'`, `CarayolR17'`, `PkgI4.EigenformTwist`, `LeafQM.AV.R1rec`, `R5fp`, `R5fpCount`,
`ZInQ.LeafPush2.R03_LinYang`. `lake env lean scratch/leaf-review-a/Check.lean`: exit 0, 0 errors,
133 s (VERIFIED, compiled; output `scratch/leaf-review-a/check_out.txt`). The printed bodies agree with the
`HDec` copies read in `Leaves3.lean`. The other 14 statements have no kernel copy outside leaf-fold3's
flat file (110 826 lines, 1042 s to compile), and a `#print` would add nothing to reading the source text,
so they were not compiled here. Numerical checks (Python, mpmath 1.3.0 from the local uv cache, no network):
`py/theta_mod_check.py` (R4), `py/hauptmodul_check.py` (`Ω`, `j_θ`, orders at `P₋₃`), and
`py/linyang_tuple_check.py` (R3, the fork's run).

## 7. What remains

- No field needs a statement change. The proposed **docstring** correction for `QMDenZeroCM3` (§1(d))
  is the only text proposed, and it is not applied.
- Caveats (a) Lemma QP locators and (b) R1's PEL specialization remain open human checks, as their
  docstrings already say.
- Not compiled: the name resolution of `B`, `O` in `FS5NoCM.CMOptimalEmbedding` (needs the 1042 s flat
  file). Every copy has the same meaning (VERIFIED, read).
- The theorem numbers cited are from memory (UNVERIFIED). A reader with library access should confirm
  Deligne–Serre Thm 4.1, Carayol's Théorème (A), Shimura 1973 Thm 1, González–Rotger Thm 5.12 and
  Prop. 5.6, Baba–Granath Thm 2.1, and Lin–Yang Ex. 29.
