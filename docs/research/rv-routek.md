# Route K (modularity through GL₂-type varieties over ℚ): an adversarial review

Scope: route K as proposed in `docs/research/hdec-elementary.md` §2.2 (Lemma GL₂ = G14, G15,
Lemma Ind = G16, G17, leaves L6, L7) and as adopted in `docs/research/hdec-alt.md` §1.2 (leaves
L13 Ribet–Pyle, L14 Khare–Wintenberger, L15, and the twist lemma). Both replace h-trust steps C3-C5,
C7, C8 (Pan's theorem with p-adic Hodge theory). hdec-elementary also drops C9, C10 and replaces E1.
Checks and their outputs are in `scratch/rv-routek/` (`log.md`).

Marks: **VERIFIED** (checked here against the manuscript, the notes, or by an exact computation, or
checked as an argument step by step), **STANDARD** (a published textbook fact), **SPECULATIVE**.
Theorem numbers given from memory are **UNVERIFIED**: this host has no network, and no source of
Ribet 1992, Pyle 2004 or Khare–Wintenberger 2009 is on disk.

## Verdict

**SOUND AFTER REPAIRS**, for both variants. No step fails, and the constants of Theorem 4.1 are
unchanged: `[L':ℚ] ≤ QM`, `N ≤ QM²`, `g = dim J₁(N) ≤ N²`, `h_F(A) ≤ Q¹⁷M²⁴`. The dimension of
the GL₂-type variety enters no bound. No counterexample was found: two scripts, every check passes.

The two arguments that carry the route are VERIFIED as arguments, over STANDARD inputs:

- hdec-elementary's Lemma GL₂ (G14): the `ℚ`-simple factor `B` of `Res_{L'/ℚ} A` that carries
  `r_ℓ` is of GL₂-type, and `B_{L'} ∼ A^k`;
- hdec-alt's twist lemma.

Lemma Ind (G16) is also correct. It needs one fact that route P never used: the upper groups above
`U₀` lie in `G_{L'}`. That fact holds because N5 defines `L'` as the kernel field of `β|G_L`
(N5 L715, VERIFIED).

The burden of proof is not fully met in one respect. The published statements of the leaves are
recalled, not read (UNVERIFIED), and their trust bases are larger than the designs say. The repairs:

1. **L6's citation (hdec-elementary §3, R2).** Two corrections.
   - Cite Khare–Wintenberger (II) and Kisin 2009 as well as KW (I). The GL₂-type corollary needs
     Serre's conjecture at arbitrary level. The level of `r̄_λ` may be even here (`2 ∈ T`), and the
     even-level case of KW's proof rests on Kisin, *Modularity of 2-adic Barsotti–Tate
     representations*, Invent. Math. 178 (2009) 587-634. This is VERIFIED as restated by Gee
     (arXiv:1402.7197 §3) and Dieulefait (arXiv:0712.1317 §3), both read by ser-ell R5/F1.
   - hdec-elementary R2's sentence "Kisin's 2-adic result is not needed" is wrong as a statement
     about the trust base. It is right only in that Ribet's deduction applies Serre's conjecture at
     odd primes.
   - The locators "KW (I) Thm 1.2" and "Ribet 1992 Thm 4.4" stay UNVERIFIED. If KW print only the
     weak form, the level-and-weight optimization (Ribet, Edixhoven, Diamond, Buzzard) belongs to
     the citation, as ser-ell R5 says. hdec-alt's L14 already lists Kisin.
2. **L7 is a bundle, and its use at `p = 3` needs one more input (hdec-elementary).**
   - L7 is four results: Shimura's `A_f`; the newform decomposition of `J₁(N₀)` (Atkin–Lehner–Li);
     `A_f` is `ℚ`-simple; and Carayol's local–global compatibility. hdec-elementary §2.2 says route K
     "removes" Li, Shimura and Eichler–Shimura "as separate inputs". They are not removed, only
     moved inside L7, and the leaf count should say so.
   - G16 computes the conductor at `p = 3` with `ℓ = 2`. It has to, because its "Galois form" of
     good reduction needs `B ⊗ ℚ_ℓ` to be a division algebra, so `ℓ ∈ {2, 3}`. L7 then needs
     Carayol's Théorème (A) at `λ | 2`. That is UNVERIFIED; h-trust D5 only asks about `p | N`.
   - Repair: add Grothendieck's theorem that the conductor of an abelian variety does not depend on
     `ℓ ≠ p` (SGA 7 I, Exp. IX; STANDARD, locator UNVERIFIED), and apply Carayol with `λ | 5`.
     Alternatively, check that Carayol's Théorème (A) allows `ℓ = 2`.
3. **Write out G16's two load-bearing facts (hdec-elementary).**
   - (i) For `u > U₀`, `G_{ℚ_p}^u ⊂ G_{L'}`. N5 shows that these groups lie in `G_L` and that `β`
     is trivial on them, and `L'` is the kernel field of `β|G_L` (N5 L715). So the permutation
     part of `Ind_{G_{L'}}^{G_ℚ}` is killed too.
   - (ii) `G^u` is normal in `G_{ℚ_p}`, and `L'/ℚ` is Galois. Mackey's formula therefore reduces
     the action on `V_ℓ(W)` to the action on `V_ℓ(A)` at every place of `L'` above `p`. N5's local
     argument depends only on the local degree `≤ DG₀`, so it is uniform in the place.
   - Both are VERIFIED here as arguments, with a finite-group model and 28 discriminant checks.
   - The note's "no Raynaud" at `p = 3` is a misnomer. `A[4]` together with the torsion-freeness of
     `1 + 4M₄(ℤ₂)` is Grothendieck's form of the criterion with `n = 4`. This is harmless.
4. **hdec-alt step 3: "for an embedding τ" must read "for some τ".** Alternatively, L13 must include
   that `B₀` is `ℚ`-simple and `B₀ ⊗ ℚ̄` is isotypic (Ribet, UNVERIFIED locator). Choosing `τ` by
   Frobenius reciprocity on `G_K` works with L13 exactly as stated (§2.3).
5. **hdec-alt L13 (Ribet–Pyle) is not needed. Prefer hdec-elementary's G14.**
   - The converse direction (every building block is a `ℚ̄`-factor of a GL₂-type variety over `ℚ`)
     is the less certain locator. Ribet's own converse may cover only `ℚ`-curves, leaving Pyle as
     the source (SPECULATIVE recollection).
   - That direction also rests on Tate's theorem `H²(G_ℚ, ℚ̄*) = 0`.
   - G14 builds the GL₂-type variety from Glazer's own descent (B1-B3, which already uses `Br(ℚ)`)
     by Weil restriction, so neither Ribet's converse nor Pyle is needed.
   - Recommended combination: G14 + L6, with either hdec-elementary's G15-G17 + L7, or hdec-alt's
     twist lemma + C9/C10.
6. **hdec-alt §1.1(ii) must be retracted: "the dimension of `B₀` is not bounded in `M`".**
   - G14's `B` is a GL₂-type variety over `ℚ` with `B_ℚ̄ ∼ A^k` and
     `dim B ≤ dim Res_{L'/ℚ} A = 2[L':ℚ] ≤ 2QM` (VERIFIED as an argument).
   - The degree forced by odd nebentypus at the primes of `T₋` is at most `m ≤ 2R^R M`
     (`checks.py`).
   - hdec-alt's conclusion survives on its point (iii): an effective Shafarevich bound that is
     exponential in `g` gives `exp(O(QM log M))`, which is not polynomial in `M`. von Känel's
     bound is still unread (UNVERIFIED).

## 1. The published statements (task (a))

| Leaf | As stated in the designs | Published form (from memory; UNVERIFIED) | No stronger than published? |
| --- | --- | --- | --- |
| hdec-elementary L6 | `B/ℚ` is `ℚ`-simple and `End⁰_ℚ(B)` contains a number field of degree `dim B` ⇒ there is a surjection `J₁(N) → B` over `ℚ` | Ribet 1992 (reprinted Progr. Math. 224 (2004) 241-261) §4 (Thm 4.4?): Serre's conjecture ⇒ every abelian variety of GL₂-type over `ℚ` is modular, "modular" meaning a quotient of `J₁(N)` over `ℚ`. Serre's conjecture is KW (I), (II) with Kisin 2009. The corollary is commonly stated in KW and in surveys | **Yes.** The hypothesis is stronger than needed (`ℚ`-simple), and the conclusion is Ribet's definition of modular. The citation must add KW (II) and Kisin (repair 1) |
| hdec-elementary L7 | `B` a `ℚ`-simple quotient of `J₁(N₀)` ⇒ there is `M` with `M^{dim B} = cond(B)` and a surjection `J₁(M) → B` | Atkin–Lehner–Li decomposition, Shimura 1973 Thm 1, Ribet (`A_f` is `ℚ`-simple), Carayol 1986 Thm (A); `cond(A_f) = M^{dim A_f}` is a standard corollary (Carayol's introduction?) | **Yes, as a consequence of four results** (repair 2). The definition of `cond` with `ℓ = 2` at `p = 3` needs ℓ-independence or Carayol at `ℓ = 2` |
| hdec-alt L13 | every building block (`End⁰` central simple over a totally real `F`, Schur index `t ≤ 2`, `t[F:ℚ] = dim`, isogenous to its conjugates compatibly with `End⁰`) is a `ℚ̄`-factor of a GL₂-type variety over `ℚ` | Ribet 1992 §§5-6 (the forward direction: factors of GL₂-type varieties are building blocks; the converse for `ℚ`-curves), Pyle 2004 (Progr. Math. 224, 189-239; the general converse). Pyle's definition also requires the quaternion algebra to be totally indefinite when `t = 2` | **Probably** (UNVERIFIED). For our `A` the extra conditions hold: `B = (2,−3)/ℚ` is an indefinite division algebra, and the `μ_σ` are `B`-linear (B1). Not needed if G14 is used (repair 5) |
| hdec-alt L14 | every 2-dimensional constituent of `V_ℓ(B) ⊗ Ē_λ`, `B` GL₂-type, is the representation of a weight-2 newform | same sources as L6. The form through constituents is equivalent to L6 given Shimura and Eichler–Shimura | **Yes** (consequence). It lists Kisin |
| Faltings 1983 over `ℚ` (G14) | `End_{G_ℚ}(V_ℓ B) = End⁰_ℚ(B) ⊗ ℚ_ℓ`, semisimplicity | Satz 3, Satz 4 (ASTRA-READ per hdec-elementary L5) | Yes |
| Milne 1972 (G14, G16) | `V_ℓ(Res_{L'/ℚ} A) ≅ Ind V_ℓ(A)`, `(Res A)_{L'} ≅ ∏_σ σA` | Milne, Invent. Math. 17 (1972) §1 (UNVERIFIED) | Yes (STANDARD) |

Refereed status. Ribet 1992 and Pyle 2004 appeared in proceedings volumes (Ribet's KAIST
proceedings, then Progr. Math. 224, Birkhäuser), and whether either was refereed is UNVERIFIED. KW
(I), (II) and Kisin are Inventiones papers (refereed). Route K's deep core is 2009 work, against
Pan 2022 together with Scholze/Faltings–Tsuji, Berger, Fontaine, Saito/Kato and Deligne–Serre on
route P. That is a real gain in maturity. It is not a gain in depth: KW and Kisin use finite flat
and Barsotti–Tate deformation theory internally (ser-ell F7).

## 2. The glue lemmas, proof by proof (task (b))

### 2.1 hdec-elementary G14 (Lemma GL₂): VERIFIED as an argument

Set `W = Res_{L'/ℚ}(A_{L'})` and let `E` be a finite extension of `ℚ_ℓ` over which `r_ℓ` is defined.

1. `V_ℓ(W) ⊗ E ≅ Ind_{G_{L'}}^{G_ℚ}(V_ℓ(A) ⊗ E)` (Milne, STANDARD). For a subgroup of finite
   index, induction equals coinduction, so Frobenius reciprocity gives
   `Hom_{G_ℚ}(r_ℓ, V_ℓ(W) ⊗ E) = Hom_{G_{L'}}(r_ℓ|, V_ℓ(A) ⊗ E)`.
2. The right side is nonzero, because `V_ℓ(A) ⊗ E|G_{L'} = ρ_ℓ|G_{L'} ≅ (r_ℓ|)^{⊕2}` (N5 L725-729:
   "On `G_{L'}` it is the actual Tate action of `A`"; VERIFIED by reading).
3. Poincaré reducibility gives `W ∼ ∏ B_i^{n_i}`. Since `r_ℓ` is irreducible, it embeds in some
   `V_ℓ(B_i) ⊗ E`.
4. Let `D = End⁰_ℚ(B)`, with centre `F` and `[D:F] = s²`. `H₁(B(ℂ), ℚ)` is free over the field `F`,
   so `V_ℓ(B)` is free over `F ⊗ ℚ_ℓ`. Over `ℚ̄_ℓ` this gives `V_ℓ(B) ⊗ ℚ̄_ℓ = ⊕_τ V_τ`, with each
   `V_τ` of dimension `2 dim B/[F:ℚ]`.
5. Faltings over `ℚ` gives `V_τ` semisimple with `End_{G_ℚ}(V_τ) = D ⊗_{F,τ} ℚ̄_ℓ ≅ M_s(ℚ̄_ℓ)`. A
   semisimple module with that endomorphism ring is `W_τ^{⊕s}` with `W_τ` irreducible.
6. `r_ℓ ⊗ ℚ̄_ℓ` is irreducible, because its restriction to `G_{L'}` is absolutely irreducible (C2).
   So it equals some `W_τ`, hence `2s = 2 dim B/[F:ℚ]` and `dim B = s[F:ℚ]`. A central simple
   algebra of degree `s` over `F` contains a maximal subfield of degree `s` over `F`, so `D`
   contains a field of degree `dim B` over `ℚ`.
7. `W_{L'} ≅ ∏_σ σA`, and the `μ_σ` make every `σA` isogenous to `A` over `L ⊆ L'`. `A` is
   geometrically simple (`End⁰(A_ℚ̄) = B` is a division algebra), so `B_{L'} ∼ A^k` with `k ≥ 1`.

Every step holds. The inputs are STANDARD: Milne; Faltings over `ℚ`; freeness over the centre; the
structure of semisimple modules; maximal subfields of central simple algebras. This is the
Weil-restriction argument of Ribet's `ℚ`-curve paper, specialized to Glazer's descent. A
finite-group model of steps 1-3 (Frobenius reciprocity, `S₄` with `H = A₄, V₄`) is in `checks.py`.

### 2.2 hdec-elementary G16 (Lemma Ind) and G17: VERIFIED as an argument, with repairs 2-3

- **The case `p ≤ R`.** Let `N_u = G_{ℚ_p}^u` with `u > U₀`.
  - N5 L813-829 shows that `N_u ⊂ G_L`, that `β|N_u = 1`, and that `N_u` acts trivially on every
    `V_ℓ(A)` with `ℓ ≠ p` (the text says "each `V_ℓ(A)`"). This is at a place `v` of `L` over `p`,
    and the argument uses only `[L_v(A[n]) : ℚ_p] ≤ DG₀`, so it holds at every place.
  - `L'` is the kernel field of `β|G_L` (N5 L715). Hence `N_u ⊂ G_{L'}` for every embedding.
  - `N_u` is normal in `G_{ℚ_p}`. In Mackey's formula
    `Res_{G_{ℚ_p}} Ind_{G_{L'}}^{G_ℚ} V = ⊕_w Ind_{G_{L'_w}}^{G_{ℚ_p}} V_w`, a normal subgroup contained
    in every `G_{L'_w}` and trivial on every `V_w` acts trivially on the sum. So `N_u` acts
    trivially on `V_ℓ(W)`.
  - The exponent is `f_p(V) = codim V^{I} + ∫_0^{U₀} codim V^{G^u} du ≤ dim V·(1 + U₀)` (Serre,
    *Corps locaux* VI §2, STANDARD).
  - With `dim V_ℓ(B) = 2 dim B` this gives `f_p(B) ≤ dim B(2 + 8(DG₀)²) ≤ dim B·E₀`, because
    `E₀ = 10(DG₀)²` (N5 L716; `checks.py`).
- **The choice of `ℓ`.** hdec-elementary takes `ℓ = 2` and `A[4]` at `p = 3`. The degree stays
  below `DG₀`: `|GL₄(ℤ/4)| = 1321205760 ≤ G₀ = |GL₄(𝔽₅)| = 116064000000` (`checks.py`). Inertia
  is trivial on `T₂(A)` over `L_v(A[4])` for two reasons: `B ⊗ ℚ₂` is a division algebra, which
  forces monodromy 0, and `1 + 4M₄(ℤ₂)` is torsion-free. VERIFIED as an argument.
- **The case `R < p ∈ T`.** `L_v/ℚ_p` is tame (degree `≤ D < p`). Wild inertia `P` is killed by
  `β`, as in N5 L848-850, so `P ⊂ G_{L'}`. `P` acts trivially on `V_ℓ(σA)`, which has good
  reduction. `P` is normal, so it acts trivially on `V_ℓ(W)`, and `f_p(B) ≤ 2 dim B`.
- **Primes outside `T`.** `L'` is unramified there and `A` has good reduction. Mackey again gives
  `f_p(B) = 0`.
- **The conductor bound (G17).** L7 gives `v_p(M) = f_p(B)/dim B`. So `v_p(M) ≤ E₀` for `p ≤ R`,
  `≤ 2` for `R < p ∈ T`, and `0` outside `T`. Hence `M ≤ ∏_{p≤R} p^{E₀}·∏_{p | M_S} p² ≤ QM²`,
  with the same inequalities as N5 L852-857. `dim B` cancels.
- **The permutation part.** The induced representation also carries the ramification of `L'`
  itself. Its conductor is `v_p(disc L') ≤ [L':ℚ](1 + u_last)`. This was checked on 28
  (field, `p`) pairs with PARI's ramification groups (`ind_conductor.py`, ALL OK).
- **What G16 adds over route P.** Route P never needed `G^u ⊂ G_{L'}`: it acts on `r_ℓ` only, where
  `β = 1` and `σ ∈ G_L` suffice. That inclusion is the one point where route K could have broken,
  and it holds because of how N5 chose `L'`.

### 2.3 hdec-alt's twist lemma: VERIFIED as an argument, with repair 4

- **Setting.** Take `K ⊇ L'` Galois over `ℚ` with `B₀ ⊗ K ∼ A^n ⊗ K`. Enlarging `K` to its Galois
  closure is harmless.
- **Restriction to `G_K` (step 3).** `V_ℓ(B₀) ⊗ Ē|G_K ≅ (V_ℓ(A) ⊗ Ē)^n ≅ (r_ℓ|)^{2n}`. If `B₀ ⊗ K`
  has other isogeny factors, as L13 literally allows ("a `ℚ̄`-factor"), use Frobenius reciprocity
  instead.
  - `r_ℓ|G_K` maps nontrivially into `⊕_τ ρ_τ|G_K`, so into some `ρ_τ|G_K`.
  - Both are 2-dimensional and `r_ℓ|G_K` is irreducible, so `ρ_τ|G_K ≅ r_ℓ|G_K` for that `τ`.
- **The twist (step 4).** By Schur, `X = Hom_{G_K}(ρ_τ, r_ℓ)` is a line. `G_ℚ` acts on it by
  `g·φ = r_ℓ(g) φ ρ_τ(g)⁻¹` (well defined because `G_K` is normal), and `G_K` acts trivially. So
  `G_ℚ` acts through a character `ψ` of `Gal(K/ℚ)`. Any `φ ≠ 0` in `X` satisfies
  `r_ℓ(g) φ = ψ(g) φ ρ_τ(g)`, so `r_ℓ ≅ ρ_τ ⊗ ψ`, and `ψ` has finite order. Kronecker–Weber makes
  `ψ` Dirichlet.
- **Step 5 and after.** KW gives `ρ_τ ≅ ρ_{f₀,λ}`, and L15 makes `f₀ ⊗ ψ` a newform's
  representation. C9 and C10 are kept, and so is D1-D5 on Glazer's `r_ℓ`, so the constants are
  N5's.

## 3. Constants and the shape of the bound (task (c))

| Quantity | Route P (N5) | Route K (hdec-elementary) | Route K (hdec-alt) |
| --- | --- | --- | --- |
| field of the isogeny | `L'`, `[L':ℚ] ≤ QM` | same `L'` (G15: `J₁(N)_{L'} ∼ B_{L'} × Z' ∼ A × Z`) | same |
| conductor exponent at `p ≤ R` | `a_p(r_ℓ) ≤ 2 + 2U₀ ≤ E₀` | `f_p(B)/dim B ≤ 2 + 2U₀ ≤ E₀` | N5's |
| at `R < p ∈ T` / outside `T` | `≤ 2` / `0` | `≤ 2` / `0` | N5's |
| level | `N ≤ QM²` | `N ≤ QM²` (`N` = level of `f` with `B ∼ A_f`) | N5's |
| `G₀` | `|GL₄(𝔽₅)|` | `|GL₄(𝔽₅)|`, which bounds `|GL₄(𝔽₃)|` and `|GL₄(ℤ/4)|` | N5's |
| `g` in Javanpeykar / GR14 | `dim J₁(N) ≤ N²` | same | same |
| dimension of the GL₂-type variety | not used | `dim B ≤ 2[L':ℚ] ≤ 2QM`; enters no bound | `dim B₀`; enters no bound |

`ModularityOutput` in `scratch/hdec-elementary/Leaves.lean` (a field `K` with `[K:ℚ] ≤ Qc·M`, a
level `N ≤ Qc·M²`, an isogeny `J₁(N)_K ∼ Jac × Z`) is route-independent. Route K delivers it with
the same constants (VERIFIED by reading the definition, L478-485).

hdec-alt's concern about von Känel's bound. It does not touch route K, which never applies an
effective Shafarevich theorem to `B`. The concern's own premise (ii) is false (repair 6). Its
conclusion stands on (iii), if von Känel's constant is exponential in `g` (UNVERIFIED).

## 4. What route P had that route K drops (task (d))

- **C9 (newform `f`, `r₅ ⊂ V₅(A_f)`).** In N5 it feeds E1 (Faltings' Hom theorem gives
  `A × Z → J₁(N)`) and D5. On hdec-elementary's route, G15 gives E1's output directly from
  `J₁(N) → B` and `B_{L'} ∼ A^k`, and L7 replaces D5. Nothing else in N5 L796-964 uses `f`
  (VERIFIED: N5 L860-867 uses `f` only through "a common constituent" of `V_ℓ(A)` and `V_ℓ(J₁(N))` over `L'`, which G15 supplies, and `g ≥ 2` follows from the isogeny; a grep of L868-964 finds no newform, `A_f` or `r_ℓ`). On hdec-alt's
  route C9 is kept.
- **C10 (one compatible system at 3 and 5).** In N5 it serves only D5 at `p = 5` and `p = 3`,
  that is, a representation with `ℓ ≠ p`. On hdec-elementary's route the object is `B/ℚ`, and G16
  bounds `V_ℓ(W)` with `ℓ ≠ p` at each `p` directly. So C10 is unnecessary, provided the
  conductor is computed with the same `ℓ(p)` that Carayol is applied to, or the ℓ-independence of
  the conductor is added (repair 2). On hdec-alt's route C10 is kept.
- **D5 (Carayol).** It is kept on both routes (inside L7 on hdec-elementary's).
- **E1-E4.** E1 is replaced (G15). E2-E4 are unchanged.
- **C3's appendix lemma `lem:de-rham-descent` (N5 L10939).** Its only use is N5 L735 (VERIFIED by
  grep), so dropping it orphans nothing.
- **The Weil pairing and Kronecker–Weber of C8.** The Weil pairing is used only in C8 (h-trust,
  VERIFIED by grep). Kronecker–Weber stays on hdec-alt's route (twist lemma). It leaves
  hdec-elementary's route: B2's `χ` is built directly as a Dirichlet character.
- **Oddness (C5) and de Rham / pst (C3, C4).** Not used anywhere else in h-trust.

## 5. Unchecked

- Every theorem number of Ribet 1992, Pyle 2004, KW (I)/(II), Kisin 2009 and Carayol 1986: no
  source is on this host.
- Whether Ribet 1992 states the converse (building block ⇒ factor of a GL₂-type variety) beyond
  `ℚ`-curves.
- Whether Carayol's Théorème (A) allows `ℓ = 2`.
- von Känel's main bound (dependence on `g`).
- hdec-elementary's G5 (Lemma PR(ii), Galois form). It is used by G16, but it lies outside route K's
  substitution and was checked here only for the `p = 3`, `ℓ = 2` instance (§2.2).
