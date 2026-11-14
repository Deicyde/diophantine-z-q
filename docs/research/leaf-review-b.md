# leaf-review-b: statement review of leaf-fold3's groups B, C, D, E and G (41 fields)

Task leaf-review-b, 2026-11-13. Base: fork main 8ec80711 with `origin/wip/leaf-fold3` (f7951690)
merged (428c8d22). Object of review: the 41 bundle fields of `HDec.HSyn.sixContactMin_of_open3`
(docs/research/leaf-fold3.md §2, §3) in groups B (16), C (7), D (8), E (6) and G (4); leaf-review-a
reviews A, A′ and F. Model work, no human review; no network, so every theorem number below that
is not quoted from a repository file is from memory and marked UNVERIFIED.

Marks: **VERIFIED** = compiled, or read in a file (for a literature claim: read in the repository's
locator audit docs/research/locators.md, which is itself an AI audit of the primary texts).
**STANDARD** = published, reference given. **SPECULATIVE** = a judgement. **UNVERIFIED** = a
theorem number or locator recalled without a source.

## 1. Main result

**No Lean declaration is proved by this task** (it is a review; the only Lean file is the check
`scratch/leaf-review-b/PrintFields.lean.tail`, see §5).

**Verdicts.** Of the 41 fields, **8 are PUBLISHED-FORM and 33 CONSEQUENCE**; **none is
STRONGER-THAN-SOURCE and none is NOT-A-PUBLISHED-STATEMENT**, so no repaired text is proposed.
Every CONSEQUENCE row gives the derivation from the published statement.

| group | fields | PUBLISHED-FORM | CONSEQUENCE | STRONGER | NOT-PUBLISHED |
|---|---|---|---|---|---|
| B (abelian varieties, textbook) | 16 | 2 | 14 | 0 | 0 |
| C (Néron models, reduction, monodromy) | 7 | 2 | 5 | 0 | 0 |
| D (Faltings 1983, Faltings heights) | 8 | 3 | 5 | 0 | 0 |
| E (p-adic Hodge theory) | 6 | 0 | 6 | 0 | 0 |
| G (modular and algebraic curves) | 4 | 1 | 3 | 0 | 0 |
| total | **41** | **8** | **33** | **0** | **0** |

What the verdicts rest on beyond the statements themselves (each one is a premise shared by several rows,
listed so that a reader can see where a residual risk sits; §3 has the details):
1. **(D) definition fidelity of `stableFaltingsHeight`.** All D rows except r9a, r9b read the
   height through the project's infimum over metrized smooth group models (def-faltings). The
   verdicts assume, as the rows' own docstrings do, that this infimum equals the published stable
   Faltings height in Faltings' normalization (H5; the half `NeronModelMinimal` is proved by
   h5-glue; the other half is the standard base-change behaviour of Faltings heights). I read the
   definition (§3.1) and found it to be the standard construction; I did not re-prove H5.
2. **Locators the repository's own audit could not read**: Faltings 1983 Lemma 5 (r20), Bost's
   display (r21; the Lean bound is weaker than Bost's in either normalization, §3.2), Pan's JAMS
   numbering (r11r12; the arXiv v2 statement was read by the audit). These are UNVERIFIED locators,
   not doubts about the mathematics.
3. **R22's theta coordinates**: the identification of Pazuki's level-2 theta constants with the
   classical `θ[a;b](0,Ω)` is marked UNVERIFIED in the leaf's own docstring; I agree with the
   reading but cannot check it without the paper.

## 2. One row per field

Lean names are the head definitions of the field types, as printed by the check of §5 (full names,
namespace `HDec` of the flat file `scratch/leaf-fold3/Leaves3.lean`; `l.` = line in that file;
"orig." = the file the text was copied from, verbatim per leaf-fold3 §5).

### 2.1 Group B: abelian varieties, the textbook theory (16)

| field | Lean name and file | cited source | verdict | reason | repaired text |
|---|---|---|---|---|---|
| `t5` | `HDec.PkgI2.TorsionStructure` (l.1611; orig. `ZInQKernel/HDecomp/Objects.lean`) | Mumford, *Abelian varieties* §4, Application 2 (UNVERIFIED) | CONSEQUENCE | Lean: `A/K` abelian variety, `dim A = g` (topological Krull dimension), `n ≥ 1`, `n ≠ 0` in `K` ⇒ `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. Mumford proves this over an algebraically closed field; apply it to `A_{K̄}`, using `A(K̄) = A_{K̄}(K̄)` and `dim A_{K̄} = dim A`. Hypotheses match (`char K ∤ n`). | — |
| `t6` | `HDec.PkgI3.HomFreeFinite` (l.2868; orig. `HDecomp/Objects.lean`) | Mumford §19, Thm 3; Milne, *Abelian varieties* (Cornell–Silverman 1986) Thm 12.5 (both UNVERIFIED) | CONSEQUENCE | Lean: for `A, B` over any field `k`, `Hom_k(A,B)` is ℤ-free of finite rank `≤ 4 dim A dim B`, and `ℤ_ℓ ⊗ Hom → Hom(T_ℓA, T_ℓB)` is injective for `ℓ ≠ char k`. Mumford's theorem over `k̄`; `Hom_k ⊆ Hom_{k̄}` (a subgroup of a free f.g. group is free of no larger rank) and `ℤ_ℓ` is ℤ-flat, so injectivity passes to the subgroup; `T_ℓ` is computed from `A(k̄)` in both. (Milne states it over any `k`.) | — |
| `t7` | `HDec.PkgI3.CharPolyIndepOfEll` (l.2877; orig. `HDecomp/Objects.lean`) | Mumford §19, Thm 4 (UNVERIFIED) | CONSEQUENCE | Lean: for `φ ∈ End_k(A)` one monic `P ∈ ℤ[X]` is the characteristic polynomial of `V_ℓ(φ)` in every finite basis, for every prime `ℓ ≠ char k`. Mumford: the char. poly. of `T_ℓ(φ)` is `P_φ(n) = deg(n − φ)`, integral and independent of `ℓ` (over `k̄`; `End_k ⊆ End_{k̄}` with the same `V_ℓ`). The charpoly of a matrix does not depend on the basis. | — |
| `t8` | `HDec.PkgI3.PoincareReducibility` (l.2890; orig. `HDecomp/Objects.lean`) | Mumford §19, Thm 1; Milne 1986 Prop. 12.1 (UNVERIFIED) | CONSEQUENCE | Lean: `char k = 0`, `End⁰(A)` a division algebra, `f : A → J` nonzero ⇒ `∃ Z, g : Z → J` with `(a,z) ↦ f(a)+g(z)` finite surjective. Derivation: `End⁰` division ⇒ `A` simple (a proper abelian subvariety and its Poincaré complement give a nonzero non-isogeny endomorphism); so `ker f` is finite (its identity component is an abelian subvariety in char 0), `f(A)` is an abelian subvariety; Poincaré over `k` gives `Z ⊆ J` with `f(A)+Z = J`, `f(A)∩Z` finite; then `A × Z → J` is surjective with finite kernel, hence finite surjective. | — |
| `t9` | `HDec.LeafPush.T09_WeilPairing` (l.11905; orig. `scratch/h-decomposition/Leaves.lean`) | Mumford §§6, 8, 20, 23; Milne 1986 §§13, 16 (UNVERIFIED) | CONSEQUENCE | Lean: `∃ d ≥ 1, e`, for all `n` invertible in `K`: on `A[n]`, `e_n` takes values in `μ_n`, is bimultiplicative, alternating, Galois-equivariant, `e_n(x^m,y^m) = e_{mn}(x,y)^m`, and `e_n(x,·) ≡ 1 ⇒ x^d = 1`. Take `L` ample over `K`, `λ = φ_L`, `e_n(x,y) := ē_n(x, λy)` (`ē` Mumford's pairing `A[n]×Â[n] → μ_n`), `d` with `ker λ ⊆ A[d]`. Alternating: `e^L_n(x,x) = 1` (Mumford §23). Compatibility: `ē_{mn}(x,λy)^m = ē_{mn}(x, mλy) = ē_n(mx, mλy)` (Mumford §20, `ē_{mn}(x,y') = ē_n(mx,y')` for `y' ∈ Â[n]`). Nondegeneracy up to `d`: `λψ = [d]` gives `d·Â[n] ⊆ λ(A[n])`, then perfectness of `ē_n`. Checked against the leaf's own derivation: correct. | — |
| `t10` | `HDec.T10Etale.T10_TateDuality` (l.27887; orig. `ZInQKernel/HDecomp/Textbook/T10Etale.lean`) | Milne 1986 Thm 15.1(a); Bhatt–Scholze 2015 §5.6 (UNVERIFIED) | CONSEQUENCE | Lean: `ℓ ≠ char K` ⇒ a `ℤ_ℓ`-linear iso `H¹_proét(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓA, ℤ_ℓ)` intertwining `galH σ` (transport along `s_σ = 1 × Spec σ⁻¹`) with `f ↦ f ∘ T_ℓ(σ⁻¹)`. Milne: `H¹_ét(A_K̄, ℤ/ℓⁿ) ≅ Hom(A[ℓⁿ], ℤ/ℓⁿ)`, natural; Bhatt–Scholze: `RΓ_proét(X, ℤ_ℓ) = R lim RΓ_ét(X, ℤ/ℓⁿ)` (no `lim¹` in degree 1: the `H⁰` system is `ℤ/ℓⁿ` with surjective maps); the limit is `Hom(T_ℓA, ℤ_ℓ)`. Direction (SPECULATIVE, by hand): `σ·P̃ = s_σ ∘ P̃ ∘ Spec σ` on sections of `A_K̄`, so `(s_σ)_* = s_{σ⁻¹}^*` corresponds to `f ↦ f ∘ T_ℓ(σ⁻¹)`; both sides are left actions. | — |
| `homLatticeCorr` | `HDec.HomUnify.HomLatticeCorr` (l.83816; orig. `ZInQKernel/Contrib/HomUnify/Corr.lean`) | Birkenhake–Lange, *Complex abelian varieties* Prop. 1.2.1; Mumford §1, §3; Serre GAGA (UNVERIFIED) | CONSEQUENCE | Lean (1): every hom `f : A → B` over `K` lifts along any uniformizations to a ℂ-linear `M`. (2) Over ℂ, every ℂ-linear `M` with `MΛ_A ⊆ Λ_B` comes from a unique hom. `IsUniformization` gives a holomorphic surjective homomorphism `ℂ^g → A(ℂ)` (`g = dim A`); by Sard its differential is onto, so its kernel `Λ` is discrete and it is a covering, i.e. the exponential up to a linear change of coordinates. (1): lift `f∘Φ_A` through the covering `Φ_B`; an additive holomorphic map is ℂ-linear. (2): BL 1.2.1 gives the holomorphic homomorphism, GAGA makes it algebraic, uniqueness since `A` is reduced and ℂ-points are dense. | — |
| `t11b` | `HDec.ZInQ.LeafPush2.T11b_Rigidity` (l.21477; orig. `ZInQKernel/HDecomp/LeafPush2/T.lean`) | Conrad, *Chow's K/k-image and K/k-trace*, Enseign. Math. 52 (2006) §3; Milne 1986 §20 (UNVERIFIED) | PUBLISHED-FORM | Lean: `k` algebraically closed of char 0, `L/k` any extension: every homomorphism `A_L → B_L` descends uniquely to a homomorphism `A → B`. This is the rigidity statement `Hom_k(A,B) = Hom_L(A_L,B_L)` for `k = k̄` (true in every characteristic; char 0 is an extra hypothesis). Uniqueness: base change is faithful. | — |
| `t26` | `HDec.PkgI3.TateModuleFree` (l.2861; orig. `HDecomp/Objects.lean`) | Mumford §18 (and §4 App. 2) (UNVERIFIED) | CONSEQUENCE | Lean: `ℓ ≠ char k` ⇒ `T_ℓA` is a free finite `ℤ_ℓ`-module of rank `2 dim A`. Mumford's `T_ℓ ≅ ℤ_ℓ^{2g}` over `k̄`, applied to `A_{k̄}`; `T_ℓ` here is the inverse limit of `A(k̄)[ℓⁿ]` (sequence model, `PkgI3.Tate.T`), the same module. | — |
| `t27` | `HDec.PkgI3.QMDichotomyYu` (l.2908; orig. `HDecomp/Objects.lean`) | C.-F. Yu, *Endomorphism algebras of QM abelian surfaces*, JPAA 217 (2013) Thm 1.1 (VERIFIED in locators.md: journal p. 907 read by the audit) | CONSEQUENCE | Lean: `k = k̄`, char 0, `dim A = 2`, `(a,b)_ℚ` indefinite division algebra (`ℍ[ℚ,a,b] = QuaternionAlgebra ℚ a 0 b`, `i² = a`, `j² = b`, VERIFIED in Mathlib) embedding in `End⁰(A)` ⇒ `End⁰(A) ≅ B` or `≅ M₂(ℚ(√d))`, `d < 0`. Yu's theorem with its clause "`ℚ(√d)` splits `B`" dropped; indefiniteness kept (`0 < a ∨ 0 < b`). | — |
| `t35` | `HDec.ZInQ.LeafPush2.UniformizationExists` (l.21454; orig. `HDecomp/LeafPush2/T.lean`) | Mumford §1; Serre GAGA (UNVERIFIED) | CONSEQUENCE | Lean: for `σ : K → ℂ` and `g = dim A`, `A(ℂ)_σ` has a uniformization by `ℂ^g` with kernel a full lattice (homomorphism, onto, kernel `Λ`, Zariski opens pull back to open sets, regular functions holomorphic). `A_σ(ℂ)` is a compact connected commutative complex Lie group of dimension `g`; `exp` is a surjective holomorphic homomorphism with kernel a full lattice; Zariski-open sets are open and regular functions holomorphic in the analytic topology. | — |
| `t09SymmIsogenyExists` | `HDec.WeilPairing.T09_SymmIsogenyExists` (l.49707; orig. `scratch/g12-det/DetLeaves.lean`) | Mumford §§6, 8, 13, 20, 23; Milne 1986 §§8-13, 16 (UNVERIFIED) | CONSEQUENCE | Lean: every `A/K` has a `SymmIsogeny`: some `WeilDual` `D` (an abelian variety `D.dual` with perfect, Galois-equivariant, compatible pairings `A[n]×D.dual[n] → μ_n` for `n` invertible in `K`, and duals of endomorphisms) and an isogeny `λ : A → D.dual` with `e^λ_n` alternating. Witness: `D.dual = Â = Pic⁰` with Mumford's `ē_n` (perfect, Galois-equivariant since defined over `K`, `ē_{mn}(x,y) = ē_n(mx,y)`, `f^∨` with `ē_n(x,f^∨y) = ē_n(fx,y)`), `λ = φ_L` for `L` ample over `K` (an isogeny), `e^L_n(x,x) = 1`. Existential in `D`, so no stronger than the published facts. | — |
| `isogenyQuasiInverse` | `HDec.WeilPairing.IsogenyQuasiInverse` (l.49720; orig. `scratch/g12-det/DetLeaves.lean`) | Mumford §7 (Remark after Thm 4), §8; Milne 1986 Prop. 7.1, Rem. 8.4 (UNVERIFIED) | CONSEQUENCE | Lean: for an isogeny `f : A → B` (finite, surjective) there are `d ≥ 1`, `g : B → A` with `fg = [d]`, `gf = [d]` on `K̄`-points. `ker f` is a finite group scheme killed by `d = deg f`, so `[d]_A` factors as `g ∘ f` with `g` over `K`; `f g f = f [d] = [d] f` and `f` is onto, so `fg = [d]_B`. | — |
| `divisiblePoints` | `HDec.WeilPairing.DivisiblePoints` (l.50148; orig. `scratch/g12-det/DetLeaves.lean`) | Mumford §4 App. 2, §6 (UNVERIFIED) | CONSEQUENCE | Lean: `A(K̄)` is divisible (every `n ≥ 1`, including `char K ∣ n`). `[n]` is an isogeny, hence surjective; a surjective morphism of finite-type `K̄`-schemes is surjective on `K̄`-points. | — |
| `serreRigidity3` | `HDec.HeckeRest.SerreRigidity3` (l.98709; orig. `scratch/hecke-rest/FibreSizes.lean`) | Serre, appendix to Sém. Cartan 13 (1960/61) exp. 17; Silverberg–Zarhin, JPAA 111 (1996) (UNVERIFIED) | PUBLISHED-FORM | Lean: `A/ℚ̄`, `φ ∈ End(A)` of finite order fixing every point of `A(ℚ̄)[3]` ⇒ `φ = 1`. This is Serre's lemma (finite-order endomorphism `≡ 1 mod n`, `n ≥ 3`, is `1`) at `n = 3`; the points are the `ℚ̄`-points over the algebraically closed base. | — |
| `t4` | `HDec.PkgI2.ReductionTorsionBijective` (l.1593; orig. `HDecomp/Objects.lean`) | Serre–Tate, *Good reduction of abelian varieties*, Ann. Math. 88 (1968) §1 (proof of Thm 1) (UNVERIFIED) | CONSEQUENCE | Lean: abelian scheme `𝒜/O` with `𝒜_K ≅ A`, `m ≥ 1` invertible in `O`, `w` a valuation ring of `K̄` over `O`: reduction `A(K̄)[m] → 𝒜(κ(w))[m]` is bijective (both `∃!` directions). `x ∈ A(K̄)` extends uniquely to `x' ∈ 𝒜(w)` (valuative criterion, any valuation ring); `w` is strictly henselian (integrally closed in the algebraically closed `K̄`, residue field algebraically closed); `𝒜[m]` is finite étale over `O` (`m` invertible), so `𝒜[m](w) → 𝒜[m](κ(w))` is bijective. | — |

### 2.2 Group C: Néron models, reduction and monodromy (7)

Common objects (`HDec.PkgI2`, l.1376-1520, orig. `ZInQKernel/HDecomp/Objects.lean`): `K` any field,
`O ⊆ K` a valuation subring that is a DVR, `w` a valuation subring of `K̄` with `w ∩ K = O`,
inertia = Mathlib's `ValuationSubring.inertiaSubgroup` of `w` in `Aut(K̄/K)` (= `Gal(K^sep/K)`),
Galois action `σ·x = Spec σ ≫ x`, `HasGoodReduction` = an abelian scheme over `O` (proper, smooth,
geometrically connected group object) with generic fibre `≅ A` as group objects. These are the
notions of Serre–Tate §1.

| field | Lean name and file | cited source | verdict | reason | repaired text |
|---|---|---|---|---|---|
| `r6` | `HDec.PkgI2.RaynaudCriterion` (l.1537) | SGA 7 I, Exp. IX, Prop. 4.7 (Raynaud) and Prop. 3.5 (UNVERIFIED numbers) | CONSEQUENCE | Lean: if `m ≥ 3` is invertible in `O` and all of `Gal` fixes `A(K̄)[m]`, every inertia `σ` satisfies `(σ−1)² = 0` on every `A(K̄)[ℓⁿ]`, `ℓ` invertible in `O`. Raynaud: `A[m]` rational (even: unramified) for some `m ≥ 3` prime to `p` ⇒ semistable reduction over `K`; IX 3.5: semistable ⟺ inertia unipotent of echelon `≤ 2` on `T_ℓ`; `T_ℓ → A[ℓⁿ]` is onto and equivariant. The Lean hypothesis (all of `Gal`) is at least as strong as the source's. | — |
| `r7a` | `HDec.PkgI2.NeronOggShafarevich` (l.1479) | Serre–Tate 1968, Thm 1 (UNVERIFIED number) | PUBLISHED-FORM | Lean: (a) good reduction at `O` ⟺ (b) inertia at `w` fixes `A(K̄)[m]` for every `m ≥ 1` invertible in `O` ⟺ (c) for infinitely many such `m`. This is Thm 1 (a)⟺(b)⟺(c) for any discretely valued `K`; "`m` invertible in `O`" = "`m` prime to the residue characteristic"; torsion prime to `p` lies in `K^sep`, and `Aut(K̄/K) → Gal(K^sep/K)` is an isomorphism respecting inertia. | — |
| `r7b` | `HDec.PkgI2.SerreTatePotentialGood` (l.1500) | Serre–Tate 1968, Thm 2 and §2 (UNVERIFIED) | CONSEQUENCE | Lean, for a prime `ℓ` invertible in `O`: `(∃ finite K' ⊆ K̄, A_{K'}` has good reduction at `w ∩ K')` ⟺ `(∃ finite K'`, every inertia `σ` fixing `K'` acts trivially on all `A(K̄)[ℓⁿ])`. Thm 2: potential good reduction ⟺ the image of inertia in `Aut T_ℓ` is finite. Finite image ⟺ some open subgroup `I ∩ G_{K'}` acts trivially (the kernel is closed of finite index, hence open, and open subgroups of `I` contain some `I ∩ G_{K'}`). Place: good reduction at one place of a finite `K'` gives it at all places of the Galois closure (base change; conjugate places), so the left side is "potential good reduction". The restriction of `w` to a finite `K'` is again discrete. One open subgroup is common to the two sides by construction (locators.md, note on potential good reduction). | — |
| `r8` | `HDec.PkgI2.GrothendieckMonodromy` (l.1520) | SGA 7 I, Exp. IX, Thm 3.6 and Prop. 3.5 (UNVERIFIED) | CONSEQUENCE | Lean: `∃` finite `K' ⊆ K̄` such that every inertia `σ` fixing `K'` has `(σ−1)² = 0` on `A(K̄)[ℓⁿ]` for all `ℓ` invertible in `O`, all `n`. 3.6: semistable reduction over a finite `K'` (one `K'` for all `ℓ`); 3.5 over `K'`, whose inertia at `w` is `I_w ∩ G_{K'}`; finite level from `T_ℓ` as in `r6`. | — |
| `t3` | `HDec.PkgI2.NeronMappingAbelianScheme` (l.1555) | Bosch–Lütkebohmert–Raynaud, *Néron models* (1990) §1.2, Def. 1, Prop. 8 (UNVERIFIED) | CONSEQUENCE | Lean: for abelian schemes `𝒜, ℬ` over the DVR `O`, restriction to the generic fibre is a bijection on morphisms of `O`-schemes `𝒜 → ℬ`. BLR Prop. 8: an abelian scheme over a DVR is the Néron model of its generic fibre; the Néron mapping property applied to the smooth `O`-scheme `𝒜` and target `ℬ`. | — |
| `t41` | `HDec.ZInQ.H5Neron.NeronModelExists` (l.30153; orig. `ZInQKernel/HDecomp/Faltings/H5Neron.lean`) | BLR §1.4, Thm 3 (UNVERIFIED) | PUBLISHED-FORM | Lean: for `A/K` and a number field `L ⊇ K`, `A_L` has a `GroupModel` over `𝓞_L` (smooth, separated, quasi-compact group scheme with generic fibre `≅ A_L` as groups) with the Néron mapping property for every smooth `𝓞_L`-scheme. BLR 1.4/3 over the Dedekind ring `𝓞_L`; a Néron model is a smooth separated finite-type group scheme. | — |
| `properSmoothGenConnected` | `HDec.FrobPiecesNeron.ProperSmoothGenConnected` (l.110289; orig. `scratch/frob-pieces/FrobPiecesFull.lean`) | EGA III₁ 4.3.1-4.3.4 (Zariski's connectedness theorem) (UNVERIFIED) | CONSEQUENCE | Lean: `R ≅ 𝓞_L[1/f]`, `X/R` smooth proper with geometrically connected generic fibre ⇒ `X → Spec R` geometrically connected (every fibre). `X_L` proper, geometrically connected and geometrically reduced ⇒ `H⁰(X_L,𝒪) = L`; `H⁰(X,𝒪)` is finite over `R`, torsion-free (flat), inside `L`, integral over the normal `R`, so `= R`; EGA III 4.3.4 then gives geometrically connected fibres; fibres are nonempty (`X ≠ ∅` since the generic fibre is connected, `X → Spec R` open and closed, `Spec R` connected). `f = 0` is vacuous (no map from the zero ring to `L`). | — |

### 2.3 Group D: Faltings 1983 and Faltings heights (8)

`stableFaltingsHeight A = ⨅_{L, g, M} M.hodge.modelHeight ∈ EReal` over number fields `L ⊇ K` and
metrized models `M` (a smooth separated quasi-compact group model `𝒢/𝓞_L` of `A_L`, the lattice
`⋀^g ω_𝒢`, and archimedean data from an analytic uniformization), with
`modelHeight = (log #(⋀^gω_𝒢 / 𝓞_L η) − Σ_σ log ‖η‖_σ)/[L:ℚ]`, `‖η‖²_σ = |c|²·covol(Λ_σ)`
(Faltings' `(i/2)^g` normalization). See §3.1.

| field | Lean name and file | cited source | verdict | reason | repaired text |
|---|---|---|---|---|---|
| `r9a` | `HDec.PkgI3.FaltingsSemisimple` (l.2847; orig. `HDecomp/Objects.lean`) | Faltings, Invent. Math. 73 (1983), Satz 3 (UNVERIFIED) | PUBLISHED-FORM | Lean: `V_ℓ(A)` is a semisimple `G_K`-representation (`ComplementedLattice` of subrepresentations, VERIFIED in Mathlib), `K` a number field, every prime `ℓ`. Faltings' theorem; invariant subspaces of a finite-dimensional space need no continuity condition. | — |
| `r9b` | `HDec.PkgI3.FaltingsTate` (l.2854; orig. `HDecomp/Objects.lean`) | Faltings 1983, Satz 4, Korollar 1 (UNVERIFIED) | PUBLISHED-FORM | Lean: `ℤ_ℓ ⊗ Hom_K(A,B) → Hom_{ℤ_ℓ}(T_ℓA, T_ℓB)` is injective with image the `G_K`-equivariant maps. This is the Tate conjecture `Hom_K(A,B) ⊗ ℤ_ℓ ≅ Hom_{G_K}(T_ℓA, T_ℓB)`. | — |
| `r18` | `HDec.ZInQ.LeafPush2.R18_Javanpeykar` (l.21001; orig. `ZInQKernel/HDecomp/LeafPush2/R18.lean`) | Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 (VERIFIED in locators.md, read by the audit: `h_Fal(X) ≤ 13·10⁶·g·deg_B(X)⁵`, genus `g ≥ 1`, stable Jacobian height) | CONSEQUENCE | Lean: curve `X/K` (smooth proper geometrically connected integral, `K`-point), Jacobian `J` (Albanese property), `g = dim J ≥ 1`, Belyi function `t` over `K`, `d = [K(X):K(t)]` ⇒ `h^st_F(J) ≤ 13·10⁶ g d⁵`. Base change to `ℚ̄`: `J_ℚ̄ = Jac(X_ℚ̄)`, `g` = genus; `t` is unramified over `ℙ¹ ∖ {0,1,∞}` at every place (the Lean predicate checks ramification index 1 over every monic irreducible `q ≠ X, X−1` over `K`; geometric in char 0), so `deg_B(X_ℚ̄) ≤ d`; the bound is monotone in `d`. In Deligne's normalization the bound would still imply this one (`h_D ≥ h_F`). Uses premise 1 of §1. | — |
| `r19` | `HDec.ZInQ.DefFaltings.R19_GaudronRemond` (l.19012; orig. `ZInQKernel/HDecomp/Faltings/Leaves.lean`) | Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014) Thm 1.4, p. 2060; `κ`, `α(g) = 1024g³` p. 2058 (VERIFIED in locators.md: "a K-isogeny in each direction, each degree bounded by κ(A) … stable original-Faltings normalization") | PUBLISHED-FORM | Lean: `A, B` isogenous over the number field `K`, `dim A = g`, `h^st_F(A) = x` ⇒ isogenies `A → B` and `B → A` of degree `≤ ((14g)^{64g²}[K:ℚ] max(x, log[K:ℚ], 1)²)^{1024g³}`. Degree = `#ker(K̄)` (= degree in char 0). The height enters as a real `x`, never `EReal.toReal`. Uses premise 1. | — |
| `r20` | `HDec.ZInQ.DefFaltings.R20_FaltingsLemma5` (l.19022; orig. `HDecomp/Faltings/Leaves.lean`) | Faltings 1983, Lemma 5; Raynaud, *Hauteurs et isogénies*, Astérisque 127 (1985), Cor. 2.1.3 (UNVERIFIED; locators.md: Lemma 5 unread) | CONSEQUENCE | Lean: for an isogeny `φ : A → B` over `K` with real stable heights `x, y`: `|x − y| ≤ ½ log deg φ`. Over `L` with semistable reduction, Raynaud's formula `h(B) − h(A) = ½ log deg φ − [L:ℚ]⁻¹ log #s*Ω¹_{𝒢/𝓞_L}` (`𝒢` the kernel of the Néron-model map) with `0 ≤ [L:ℚ]⁻¹ log # ≤ log deg φ` gives the two-sided bound; stable heights do not change under `K → L`. Equal-dimension normalization shifts cancel. Uses premise 1. | — |
| `r21` | `HDec.ZInQ.DefFaltings.R21_Bost` (l.19029; orig. `HDecomp/Faltings/Leaves.lean`) | Bost, Sém. Bourbaki 795 (1994/95), Astérisque 237; as printed by Gaudron–Rémond 2014 §9, proof of Lemma 9.1, p. 2098 (VERIFIED in locators.md for GR's use; Bost's display unread) | CONSEQUENCE | Lean: `h^st_F(A) ≥ −(3/2) dim A` (in `EReal`). Bost's bound `h_D ≥ −(g/2) log(2π)` (UNVERIFIED display) gives `h_F = h_D − (g/2) log π ≥ −(g/2) log(2π²) ≈ −1.4915 g ≥ −1.5 g`; if Bost's display is in Faltings' normalization the Lean bound is weaker still. So the Lean bound follows in either normalization (the computation in locators.md, note on Bost, agrees). `stableFaltingsHeight = ⊤` satisfies it trivially. Uses premise 1. | — |
| `r22` | `HDec.ZInQ.LeafPush2.R22_Pazuki` (l.21159; orig. `ZInQKernel/HDecomp/LeafPush2/R22.lean`) | Pazuki, *Theta height and Faltings height*, Bull. SMF 140 (2012) Cor. 1.3(2) (VERIFIED in locators.md: `g = r = 2`, Deligne metric, `X_D ≥ max(1, h_D)`) | CONSEQUENCE | Lean: abelian surface `A/K`, `h^st_F(A) = x`, `X ≥ max(1, x + log π)`; for every `σ`, uniformization `(Λ, Φ)`, Siegel period matrix `Ω` of `Λ` and algebraic representative `z` of `[θ_m(0,Ω)]_m`: `h(z) ≤ X/2 + C₂ log(X+2)`. `h_D = h_F + log π` for `g = 2`, so `X ≥ max(1, h_D)`; Pazuki's upper half `max(1,h_Θ) ≤ max(1,h_D)/2 + C₂ log(min(·,·)+2)`; the sup-norm height is `≤` the Euclidean one; a Siegel period matrix of `Λ` is a principal polarization with symplectic basis, algebraic over `ℚ̄`; the projective height of the theta-null point does not depend on the basis (theta transformation formula). Premises 1 and 3 of §1. | — |
| `h5fin` | `HDec.ZInQ.DefFaltings.StableHeightFinite` (l.18789; orig. `ZInQKernel/HDecomp/Faltings/Height.lean`) | Faltings 1983 §1-2 (definition, base change of `h`); BLR 1.4/3; SGA 7 IX 3.6, 3.3 (UNVERIFIED) | CONSEQUENCE | Lean: for `A` over a number field, `stableFaltingsHeight A ∉ {⊤, ⊥}`. `≠ ⊤`: a Néron model over `𝓞_K` (BLR) with analytic uniformizations (Mumford §1) and its Hodge lattice is a metrized model. `≠ ⊥`: over every `L` the Néron model has the least model height (proved: `NeronModelMinimal`, h5-glue), and the Néron-model height over `L` is `≥` the stable height (Faltings heights do not increase under base change and are constant once the reduction is semistable). A statement about the project's definition; its derivation from the published facts is the H5 argument (premise 1). | — |

### 2.4 Group E: p-adic Hodge theory (6)

Common objects (`HDec.PkgI4`, l.3996-4787, orig. `ZInQKernel/Contrib/G9/I4Layer.lean`):
`htMult w = dim_E (ℂ_p(−w) ⊗ V^∨)^{G_{ℚ_p}}`, computed as `dim_{ℚ_p} H_{−w} / [E:ℚ_p]` with
`H_i = {φ : V → ℂ_p ℚ_p-linear | φ(ρ(σ)v) = χ(σ)^i σ(φ v)}`; the cyclotomic character has weight
`−1` (checked by hand: `H_i(ℚ_p(1)) ≠ 0` iff `i = 1`, i.e. `w = −1`; `V_ℓ(E)` gets `{0, −1}`).
`H_i` is an `E`-subspace (`φ ↦ φ(e·)`), so the division is exact. `IsDeRham`: `dim_{ℚ_p} D_dR(V^∨)
= dim_{ℚ_p} V`, on Mathlib's `BDeRham 𝓞_{ℂ_p} p`.

| field | Lean name and file | cited source | verdict | reason | repaired text |
|---|---|---|---|---|---|
| `r10` | `HDec.PkgI4.DeRhamComparisonHT` (l.35385; orig. `ZInQKernel/Contrib/R10/Amend.lean`) | Faltings 1988 (Hodge–Tate decomposition), Faltings 1989 / Fontaine–Messing / Tsuji (de Rham comparison), Tate 1967 (`ℂ_p(j)^{G_F} = 0`, `j ≠ 0`), Milne 1986 Thm 15.1(a) (UNVERIFIED) | CONSEQUENCE | Lean: `A` over a finite `F/ℚ_p`, `dim A = g`: `V_p(A)` is de Rham as a `G_F`-representation, Hodge–Tate multiplicity `g` at `0` and at `−1`, `0` elsewhere. `V_p(A)^∨ = H¹_ét(A_F̄, ℚ_p)` with `ℂ_p ⊗ H¹ ≅ ℂ_p^g ⊕ ℂ_p(−1)^g`; so `(ℂ_p(−w) ⊗ V^∨)^{G_F}` has `F`-dimension `g` for `w ∈ {0, −1}` and `0` otherwise (Tate); de Rham by the comparison theorem (`V` de Rham ⟺ `V^∨` de Rham). The multiplicities are `F`-dimensions (`dim_{ℚ_p}/[F:ℚ_p]`), matching `ℂ_p^{G_F} = F`. `PkgI4.I3.AbVar` is `PkgI3.AbVar` verbatim (VERIFIED by diff). | — |
| `r11r12` | `HDec.PkgI4.PanBerger` (l.4680; orig. `Contrib/G9/I4Layer.lean`) | Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, JAMS 35 (2022), Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (VERIFIED in locators.md for v2; JAMS numbering UNVERIFIED); Berger, Invent. Math. 148 (2002) Thm 0.7 (VERIFIED in locators.md / rv-h-a011 for arXiv numbering) | CONSEQUENCE | Lean, `p ≥ 5`: `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous, irreducible (image spans `M₂`), finitely ramified, de Rham at `p`, odd, distinct HT weights ⇒ a normalized eigenform `g` (weight `k ≥ 1`, nebentypus), a continuous `ψ`, embeddings and finite `S` with `tr ρ(Frob_q^{arith}) = ψ(Frob_q) ι(a_q(g))` for `q ∉ S`. Berger: de Rham ⇒ pst; Pan (no `p = 3` exception needed at `p ≥ 5`): `ρ ≅ ρ_f ⊗ ψ'` (geometric normalization); with `tr(M⁻¹) = tr M / det M`, `ā_q = χ̄(q)a_q` and `ψ = ψ'ε^{1−k}` one gets the arithmetic trace form for the conjugate form. | — |
| `r13` | `HDec.PkgI4.EigenformHT` (l.4599; orig. `Contrib/G9/I4Layer.lean`) | Faltings, Math. Ann. 278 (1987); Saito, Invent. Math. 129 (1997); Kato, Astérisque 295 (2004) §§9.2-9.4 (Kato VERIFIED in locators.md; others UNVERIFIED); with Li 1975 / NewformOfEigenform, Brauer–Nesbitt, Chebotarev | CONSEQUENCE | Lean: `k ≥ 2`, any `N`, `ℓ`, `g` a normalized cuspidal eigenform, `ρ` semisimple with `tr ρ(Frob_p^{arith}) = a_p` (`p ∤ Nℓ`) ⇒ HT weights `{0, 1−k}` at `ℓ`. Semisimple + traces at a density-one set determine `ρ ≅ (ρ_f^{Del})^∨` for the newform `f` with the same eigenvalues; `ρ_f^{Del}` is de Rham at `ℓ` (every level) with `ℂ_ℓ ⊗ ρ_f^{Del} ≅ ℂ_ℓ ⊕ ℂ_ℓ(1−k)`; with `htMult w = dim(ℂ_ℓ(−w) ⊗ V^∨)^G` this is `{0, 1−k}` (equals `{0,−1}` at `k = 2`, as for `V_ℓ` of an elliptic curve). | — |
| `t23` | `HDec.PkgI4.T23_FontaineClosure` (l.4756; orig. `Contrib/G9/I4Layer.lean`) | Fontaine, Astérisque 223 (1994), Exp. III §1.5 and Thm 3.8 (`B_dR` regular); Brinon–Conrad, CMI notes, Thm 5.2.1, Prop. 6.3.3, 6.3.8 (UNVERIFIED) | CONSEQUENCE | Lean: for `ℚ_p`-representations of `G_{ℚ_p}` on `ℚ_pⁿ`, `IsDeRham` is (i) invariant under `ρ' = PρP⁻¹` (no continuity needed: `φ ↦ φ∘P⁻¹` identifies the two `D_dR`), (ii) stable under duals, (iii) passes to sub and quotient of a block upper triangular `ρ`, (iv) holds for block diagonal sums, (v) for Kronecker products; continuity is assumed where Fontaine's theory needs it. Each clause is the matrix form of the Tannakian property of `B_dR`-admissible representations; `D_dR` is computed on `V^∨`, equivalent by (ii). | — |
| `senTwist` | `HDec.G0Galois.SenTwist` (l.50919; orig. `scratch/g12-det/part_weight.lean`) | Sen, Invent. Math. 62 (1980) §2 Thm 4 and Cor.; Fontaine–Ouyang §2.4-2.5 (UNVERIFIED) | CONSEQUENCE | Lean: `ρ' = ψ ⊗ ρ` (`ρ'(σ) = ψ(σ)ρ(σ)`), both Hodge–Tate at `p` with full weight multisets `S`, `S'` (size `n`) ⇒ `S' = S + s`, `s ∈ ℤ`. Over a common finite `E` (the entries of `ρ, ρ'` generate one, and `ψ|_{G_{ℚ_p}}` takes values in it for `n ≥ 1`): Sen operators `Θ_{ρ'} = Θ_ρ + s_ψ`, both semisimple with integer eigenvalue multisets `S`, `S'` at the given embedding, so `s_ψ ∈ ℤ` and `S' = S + s_ψ`; `n = 0`: `s = 0`. Full size is assumed, as the docstring notes it must be. | — |
| `finiteImageHT` | `HDec.G0Galois.FiniteImageHT` (l.50932; orig. `scratch/g12-det/part_weight.lean`) | Tate 1967 §3 Thm 2; Ax–Sen–Tate; Hilbert 90; Fontaine–Ouyang Prop. 2.15 (UNVERIFIED) | CONSEQUENCE | Lean: `ρ : G_ℚ → GL_n(ℚ̄_p)` with finite image ⇒ HT at `p` with all weights `0`. The finitely many matrix entries generate a finite `E/ℚ_p`; `ρ|_{G_{ℚ_p}}` factors through `Gal(M/ℚ_p)`, `M` finite; `(ℂ_p ⊗ W)^{G} = (M ⊗ W)^{Gal(M/ℚ_p)}` has dimension `dim W` (Ax–Sen–Tate, Hilbert 90) and `(ℂ_p(i) ⊗ W)^G = 0` for `i ≠ 0` (Tate). So `htMult 0 = n`, others `0`. | — |

### 2.5 Group G: modular and algebraic curves (4)

| field | Lean name and file | cited source | verdict | reason | repaired text |
|---|---|---|---|---|---|
| `t33` | `HDec.LeafModCurves.JacobianExists ℚ` (l.16613; orig. `ZInQKernel/HDecomp/ModCurves/Defs.lean`) | Weil 1948; Milne, *Jacobian varieties* (Arithmetic Geometry 1986) Thm 1.1, Prop. 6.1 (UNVERIFIED) | PUBLISHED-FORM | Lean: a smooth proper geometrically connected curve `X/ℚ` with a point `P₀ ∈ X(ℚ)` has an abelian variety `J` with `aj : X → J`, `aj(P₀) = 0`, through which every pointed `ℚ`-morphism to an abelian variety factors uniquely by a homomorphism. Milne's Jacobian with its Albanese property (Prop. 6.1), at `K = ℚ`. Genus 0: `J = 0`. | — |
| `t34` | `HDec.LeafModCurves.DimJ1Genus` (l.16829; orig. `ZInQKernel/HDecomp/ModCurves/Leaves.lean`) | Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971) Prop. 1.40, Thm 6.6/§6.7; Milne 1986 Prop. 2.1 (UNVERIFIED) | CONSEQUENCE | Lean: `J` the Jacobian of a model of `X₁(N)` (function field `ℚ(j)(x(P))`, `P` of exact order `N` on `E_j`) ⇒ `dim J = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` over `SL₂(ℤ)/±Γ₁(N)`. The formula is Shimura 1.40 (`μ = [SL₂(ℤ):±Γ]`, `ν₂`, `ν₃` fixed points of `S`, `ST`, `ν∞` the `⟨T⟩`-orbits = cusps); `ℂ(j, x(P))` is the function field of `Γ₁(N)\ℍ*` (both `ℚ`-forms, `ℤ/N ↪ E` and `μ_N ↪ E`, are this curve over ℂ; genus is geometric); `dim Jac = genus`. | — |
| `t38` | `HDec.X1Belyi.CurveOfFunctionFieldQ` (l.31006; orig. `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean`) | Stacks Project, Algebraic Curves, "Curves and function fields"; Hartshorne I.6.7-6.12, II.6.7 (UNVERIFIED tags) | CONSEQUENCE | Lean: `F` finite over `ℚ(T)` with `ℚ` algebraically closed in `F` ⇒ a smooth proper geometrically connected integral curve `X/ℚ` with function field `≅ F` (a ring iso in char 0 is `ℚ`-linear), with a `ℚ`-point if `F` has a degree-1 place. The normal projective model of `F/ℚ`: smooth (normal, dim 1, `ℚ` perfect), `H⁰(𝒪) = ` algebraic closure of `ℚ` in `F` `= ℚ` ⇒ geometrically connected; nontrivial valuation rings of `F/ℚ` are the local rings of closed points with the same residue fields. | — |
| `t40` | `HDec.X1Belyi.X1RationalCusp` (l.31027; orig. `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean`) | Ogg, *Rational points on certain elliptic modular curves* (1973); Silverman, *Advanced topics* Thm V.3.1 (Tate curve); Igusa 1959 (UNVERIFIED) | CONSEQUENCE | Lean: for `P` of exact order `N` on `E_j`, `ℚ(j)(x(P))` has a place of degree 1 over `ℚ`. On the Tate curve over `ℚ((q))` (`j = 1/q + …`) the point `q^{1/N}` has exact order `N` with `x ∈ ℚ((q^{1/N}))`, residue field `ℚ`; all points of exact order `N` of `E_j` are conjugate over `ℚ(j)` up to sign (Igusa; a quadratic twist changes the Galois image only by `±1`, and `x` depends only on `±P`), so every `K_N` has this place. (In the kernel T40 is proved from `X0Transitive`, leaf-fold3 §1.1; not re-reviewed here.) | — |

## 3. Remarks

### 3.1 The Faltings-height definition (premise 1)

Read in `Leaves3.lean` l.17156-19058 (`HDec.ZInQ.DefFaltings`) and the copy l.19272-20900
(`HDec.ZInQ.LeafPush2`). The two copies are identical up to the namespace, two `_root_` lemmas not
re-declared, and the abelian-variety structure (DefFaltings has its own 5-field `AbVar`, LeafPush2
uses `PkgI3.AbVar`) (VERIFIED, `diff`). So R19-R21 and H5 are over `DefFaltings.AbVar`, R18 and
R22 over `PkgI3.AbVar`; `LeafAdopt.abVarEquiv` identifies them (leaf-fold3).

The construction is Faltings': Arakelov degree `log #(M/𝓞_L s) − Σ_σ log ‖s‖_σ` of the line
`⋀^g ω_𝒢` (`ω_𝒢 = ⋂_s` of the conormal stalks inside `𝔪_ξ/𝔪_ξ²`), metric
`‖η‖²_σ = (i/2)^g ∫ η∧η̄ = |c|² covol(Λ_σ)`, divided by `[L:ℚ]`, then the infimum over `L` and over
smooth group models. A larger model lattice has a larger degree and a map `𝒢 → 𝒩` to the Néron
model gives `ω_𝒩 ⊆ ω_𝒢`, so the infimum over models at fixed `L` is the Néron value (proved:
`NeronModelMinimal`); over `L` it is the semistable value. That the infimum is therefore the published
stable height is the H5 argument; I did not re-prove it. Any defect in the archimedean data
(`IsAnalyticUniformization`, `jacDet`) would affect h5fin's `≠ ⊤` first; I found none on reading
(SPECULATIVE: not a proof).

### 3.2 Normalizations (D, E)

- R21 holds in both normalizations. If Bost's bound is `h_D ≥ −(g/2) log 2π` (Deligne), then
  `h_F = h_D − (g/2) log π ≥ −(g/2) log(2π²) = −1.4915… g ≥ −(3/2) g` (log(2π²) = 2.983 < 3); if it is
  `h_F ≥ −(g/2) log 2π` (Faltings), R21 is weaker still. STANDARD arithmetic (locators.md reaches
  the same conditional conclusion).
- R18 and R22 are stated so that a Deligne-normalized source still implies them (`h_D ≥ h_F`; R22
  shifts by `log π`, `g = 2`).
- Hodge–Tate convention: cyclotomic weight `−1` throughout (`htMult`, `htMultOver`); r10, r13,
  senTwist and finiteImageHT were checked in this convention.

### 3.3 Points that are not statement errors

- `t7`, `t6`, `t5`, `t26` are stated over any field; the cited Mumford statements are over an
  algebraically closed field. The step is base change to `k̄` (named in each row); this is why they
  are CONSEQUENCE, not PUBLISHED-FORM.
- `t11b` assumes char 0 where the theorem needs only `k = k̄`: harmless (a weaker statement).
- `r6` assumes all of `Gal(K̄/K)` fixes `A[m]` where Raynaud needs only inertia: harmless.
- `t27` drops Yu's splitting clause: harmless (weaker), as its docstring says.
- `h5fin` is a statement about the project's definition, not a literal published statement; it is
  CONSEQUENCE through the H5 argument. A reader who wants every research leaf to be a literal
  citation could reclassify it as glue (its docstring already calls it "H5, finiteness"); no text
  change is needed for truth.
- `t10`'s Galois equivariance depends on the direction conventions of `galH` and `galT`; my hand
  check (row `t10`) agrees with the statement, but it is SPECULATIVE (not compiled).

## 4. What remains

Nothing in scope is left unreviewed: all 41 fields have a verdict. Not done (out of scope or
impossible offline): reading the primary texts (no network); a Lean proof that
`stableFaltingsHeight` equals the published height; a compiled check of `t10`'s action directions.

## 5. Checks

- `lake build ZInQKernel.Hypotheses.JHeight` (upstream `lean/` helpers, needed by the flat file):
  success (VERIFIED).
- `scratch/leaf-review-b/run_check.sh`: `Leaves3.lean` with `PrintFields.lean.tail` appended (a
  metaprogram `#lrb_fields S` printing each field of the bundle `S` with its type, full names, and the
  body of its head definition), one `lake env lean` process. **Outcome: exit 0, 0 errors**; the
  flat file's 283 `#print axioms` reports read `[propext, Classical.choice, Quot.sound]`; the 62
  printed fields resolve to the head definitions named in §2 (VERIFIED; list in the log).
