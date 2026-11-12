# bp-qmmoduli: formalization blueprint for the Shimura-curve objects of H (leaves R1-R3, R5)

Status: research note (task bp-qmmoduli, 2026-11-12), written for a crowdsourced Lean team.
Lean companion: `scratch/bp-qmmoduli/` (`QMOrder.lean`, `QMAbVar.lean`, `Units72.lean`;
results log `log.md`; scripts `order_table.py`, `conj_coords.py`). All three Lean files compile
with `lake env lean` (Lean 4.35.0, Mathlib v4.35.0). They contain no `sorry` and depend only on
the axioms `propext`, `Classical.choice`, `Quot.sound` (VERIFIED, `#print axioms` at the end of
each file). `QMAbVar.lean` imports the kernel module `ZInQKernel.HDecomp.A6.A6`; run
`lake build ZInQKernel.HDecomp.A6.A6` first (about one minute). No file under `ZInQKernel/`,
`blueprint/` or another task's directory was edited.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a
published result with its reference. **SPECULATIVE**: an assessment. There is no network on this
host, so theorem numbers recalled from memory are marked **UNVERIFIED**. The manuscript
`diophantine_zq.tex` is cited as N5 with line numbers. Steps A1-F4 are those of
`docs/research/h-trust.md`; leaves R1-R22 and T1-T32 are those of
`docs/research/h-decomposition.md` §2.

---

## 0. Verdict

**The argument never uses the moduli scheme `Y₃` over a general base.** It uses five things:
- the field-valued points of the moduli problem;
- the curve `Y₃/ℚ` through its function field and its morphism to `P¹_j`;
- the fibres over the three branch values and over the CM points;
- one statement at complex points, the complex uniformization, needed for F1;
- the abelian surface `A` itself, an object over a number field.

The literal leaf R1 (representability on all `ℚ`-schemes, PEL form) can therefore be replaced, for
formalization, by **field-point consequences**. Each is printed in the cited sources or follows
from them, and each can be stated over the kernel's abelian varieties
(`PkgI3.AbVar`, `ZInQKernel/HDecomp/Objects.lean`) after a few small or medium definitions.
§2.3 gives them: R1fp, R1hecke, R1rec, R2fp, R5fp. Only F1's link to the analytic leaves (R1an)
needs a very large object, the analytification of an abelian surface with its period lattice.
R22 (Pazuki's theta height) needs the same object, so it should be built once, for both.

Main findings:

1. **No representability, no abelian schemes over a base, no finite flat group schemes.**
   - Prop. TS (h-b1 §1.2, which replaced N5's integral model) uses only the Galois extension
     `M = ℚ(Y₃)` of `ℚ(j)` and the normalization of `P¹_R` in `M` (VERIFIED, read in h-b1 §1.2;
     h-b1's summary, item 2, says "No integral model of `Y₃` is used").
   - Everything else uses objects over fields (§1).
   - The leaf "`Y₃` represents the functor on `Sch/ℚ`" can be weakened to "`Y₃(K)` is in
     bijection with the set of objects over `K`, naturally in the field `K`", together with the
     Hecke action by automorphisms of `Y₃` and the map to `P¹_j`. This drops three nodes of
     very large size from the critical path.
2. **The polarization can be dropped from the moduli problem for this datum.**
   - Fix `(A, ι)` with `ι : 𝒪 ↪ End(A)` in characteristic 0. Then a principal polarization whose
     Rosati involution restricts to `x ↦ μ⁻¹x̄μ` on `𝒪` exists and is unique (§2.2).
   - So the field points of the PEL problem `(A, ι, λ, η)` and of the problem `(A, ι, η)`
     without `λ` coincide.
   - The lattice core of this argument is **proved in Lean** (`BPQM.eq_smul_E0`,
     `BPQM.eq_pm_E0_of_principal`): every alternating form on `B` for which `𝒪` acts with
     adjoint `†` is `r·E₀`, and a principal one is `±E₀`.
   - Buzzard, *Integral models of certain Shimura curves*, states the moduli problem of "false
     elliptic curves" `(A, ι)` with level structure *without* a polarization (recalled,
     UNVERIFIED). N5 cites it at L444 as "Theorem 2.1 and Corollary 2.3", in the author's
     corrected preprint (N5 L11031-11033). The refereed version is Duke Math. J. 87 (1997)
     (recalled, UNVERIFIED). If confirmed, the field-point leaf can be stated with no polarization
     at all.
   - The dual abelian variety (Picard scheme), which Mathlib lacks, therefore leaves the
     critical path of R1, R2, R5. It stays on the paths of R22 and T9.
3. **The analytic link is the expensive node.** QMHauptmodul (statable now) works on `ℍ` with
   pkg-I1's period matrix `Ω(τ)`. F1 needs: for the fibre surface `A/K` and every complex
   embedding `σ` of `K`, `A_σ(ℂ) ≅ ℂ²/ι(𝒪)(τ, 1)ᵀ` `𝒪`-equivariantly for some `τ ∈ ℍ^±`. This
   requires the complex-analytic space `A(ℂ)` and its period lattice. No Lean library has them;
   they are the analytification of an abelian variety, the same object as T11.
4. **The weak statement suggested in the task** reads: "for each QM surface over a number field,
   a point of the analytic quotient with the right Igusa invariants". It serves F1 only, and only
   if "Igusa invariants" is replaced by "period matrix" (or if Thomae's formula is added as a
   further theorem). It does not give:
   - the fibre field and its ramification (A5);
   - the conjugates (A7);
   - NoCM (A10).

   Those need R1fp, R2fp, R1rec and R5fp. Recommendation: state R1fp + R1hecke + R2fp + R1rec +
   R5fp first, at about medium total size (§4, Stage 1). Keep QMHauptmodul for F1, and attach
   R1an to the analytification work package shared with R22.
5. **Built in Lean (first concrete layer, §5):**
   - the order `𝒪` as a `Subring` of Mathlib's `QuaternionAlgebra ℚ 2 0 (−3)`;
   - the Rosati involution `x† = μ⁻¹x̄μ` (anti-involution, preserves `𝒪`, positive);
   - N5's Riemann form `E₀`, compatible with `†`, unimodular;
   - the uniqueness theorem above;
   - the Atkin–Lehner elements of reduced norms 2, 3, 6 and their relations;
   - `|(𝒪/3𝒪)^×| = 72` by kernel computation;
   - over the kernel's `PkgI3.AbVar`: QM structures (`QMStr`), their action on points,
     level-3 structures (`Level3`), the action of `Γ'` by `Aut(𝒪)` and `𝒪^×` with `A` fixed
     (units `≡ 1 mod 3𝒪` act trivially, proved), the objects `QML3 K`, their isomorphisms, and
     the set `M3 K` of isomorphism classes;
   - the setoid of isomorphisms (`Iso.symm`, `Iso.trans`, `isoSetoid`);
   - the centralizer of `ι(𝒪)` and the three CM predicates;
   - base change of QM structures along any field extension (`endBC`, `endBC_injective`,
     `QMStr.baseChange`), using Mathlib's faithfulness of `Over.pullback` along flat surjective
     quasi-compact morphisms;
   - fields of moduli of QM pairs over `ℚ̄` (`fieldOfModuli`), and **R5 stated as Lean
     `def … : Prop`s**: degree form (`R5fp`) and count form (`R5fpCount`);
   - the `Γ'` operations descend to isomorphism classes (`M3'.twist`, `M3'.rightMul`);
   - **step A6 instantiated on every object of the moduli problem** (`QML3.goodReduction`):
     good reduction at every DVR in which 3 is a unit, from the kernel's leaves
     `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`. h-decomposition §2 R1 and
     h-trust A6 record this instantiation as missing ("needs A4 and the moduli objects").
6. **What remains unproved or unstated.**
   - Base change of `QML3` along field extensions (N8, medium) is half done: base change of QM
     structures is proved (`QMStr.baseChange`). Two parts are missing:
     - base change of level structures, which needs `A(K̄)[3] → A_L(L̄)[3]` to be onto, a
       consequence of the kernel leaf `TorsionStructure`, not of the definitions;
     - `dim A_L = dim A` for the `surface` field.

     N8 is needed for naturality in R1fp, for Galois conjugates (A7) and for fields of moduli
     (R1rec, R5fp).
   - `P¹_ℚ` with `P¹(K) = K ∪ {∞}` (N11, small to medium) is needed for R2fp.
   - **R5 compiles** as two Lean `def … : Prop`s (`BPQM.AV.R5fp`, degree of the field of
     moduli; `BPQM.AV.R5fpCount`, number of CM points `2^b·#Pic R`), over `fieldOfModuli`,
     `QMPair` and `pairSetoid` built here. R1fp, R2fp and R1rec are written below in Lean syntax but **not
     compiled**: they depend on the missing half of N8 (level structures) and on N11 (`P¹`).
   - The analytification (N14) is very large.

---

## 1. What the proof takes from the Shimura curve

What I1 must deliver is pkg-I1's (I1-out) (VERIFIED, read in pkg-I1 §1). Let `u ∈ ℚ∖𝒞` and
`j₀ = J(u)`. Then there are:
- a number field `K`, Galois over `ℚ`, of degree dividing 144;
- an abelian surface `A/K` with `ι : 𝒪 ↪ End_K(A)`, with N5's principal polarization, and with
  an `𝒪`-linear `𝒪/3𝒪 ≅ A[3]` over `K`;

such that:
- (i) `K` is unramified outside `T`;
- (ii) every conjugate `σA` is isomorphic to `A` over `ℚ̄`;
- (iii) `End⁰(A_ℚ̄) = B`;
- (iv) the theta constants of a period matrix of `A_σ` satisfy F1.

Each use, with the smallest object that carries it:

| Step | Use | Object actually used | Needs the scheme over a base? | Field-point substitute (§2.3) |
| --- | --- | --- | --- | --- |
| A1 | `B`, `𝒪`, `μ`, Gram matrix | the algebra | no | **done in Lean** (`QMOrder.lean`) |
| A3 | `deg(Y₃ → P¹_j)` divides 144 | `Γ' = N/(𝔸_f^×K₃)` acting with quotient `P¹_j` | no | R1hecke + R2fp; `\|(𝒪/3𝒪)^×\| = 72` **done in Lean**; the local index 2 is T29 (stated in leaf-push) |
| A4 | an object `(A, ι, λ, η)` over the residue field of a point | field points of the moduli problem | no | **R1fp** |
| A5 (Prop. TS) | `M = ℚ(Y^{(1)})` Galois over `ℚ(j)`, branched over `{0, ∞, −16/27}`; the fibre field is the residue field of `M` at a place over `j₀` (h-b1 M2, M8) | the function field of `Y₃` and the morphism `π : Y₃ → P¹_j` | no (h-b1: no integral model) | R1fp (`Y` and its function field) + R1hecke + R2fp |
| A5 (Lemma NV) | fibres over the branch values are unramified at `p ≥ 5` | Shimura reciprocity at level 3 for the CM points of discriminants −4, −3, −24 | no | **R1rec** (unramified form) |
| A6 | good reduction away from 3 | the object `(A, ι, η)` over `K` | no | **done in Lean** (`QML3.goodReduction`) |
| A7 | conjugates geometrically isomorphic | the fibres of `π` are `Γ'`-orbits, and `Γ'` changes `(ι, η)` only | no | R2fp (fibre clause) + base change N8 |
| A10 (NoCM) | no CM point over a rational `j₀ ∉ 𝒞` | number of CM points and their fields of moduli on `X₆ = X₀(6,1)`; the `W`-action | no | **R5fp**, R1rec, R2fp |
| F1 | `j₀ = 3779136∏θ⁴/(Σθ⁸)⁵` at a period matrix of `A_σ` | complex uniformization of `A_σ` | no, but it needs analytification | **R1an** + `PkgI1.QMHauptmodul` + `PkgI1.ThetaModularity` |

---

## 2. The moduli scheme versus weaker statements

### 2.1 What the scheme `Y₃` contributes

Representability over arbitrary `ℚ`-schemes enters the paper only to produce the `ℚ`-structure
(the canonical model) and the universal family. Once h-b1 replaced N5's integral model by
Prop. TS, the proof touches `Y₃` only through four things:
- (a) its points over fields, with the objects they classify;
- (b) its function field and the morphism to `P¹_j`;
- (c) the Hecke action of `Γ'` by automorphisms over `ℚ`;
- (d) reciprocity at CM points.

(a) is a statement about the functor on fields. (b) and (c) need `Y₃` as a scheme over `ℚ`, but
not its universal property over non-reduced or higher-dimensional bases. (d) is a statement about
fields of moduli. So the leaf can be the **field-point form** R1fp of §2.3. It is a consequence of
the printed theorems (the field points of a representing scheme), never stronger. It avoids three
nodes of very large size:
- abelian schemes over a base with endomorphisms;
- finite flat group schemes `A[3]` over a base;
- representability of functors on `Sch/ℚ`.

**Caution (STANDARD, Shimura reciprocity for `π₀`; derived here, not read).** `Y₃` is irreducible
over `ℚ` but **not geometrically connected**. Its complex points have
`#π₀ = #(ℚ^×_{>0}∖𝔸_f^×/nrd(K₃)) = #(ℤ₃^×/(1+3ℤ₃)) = 2`, because:
- `nrd(𝒪_p^×) = ℤ_p^×` for `p ≠ 3`;
- `nrd(1+3𝒪₃) = 1+3ℤ₃`, the unramified norm being onto the principal units.

The two components are defined over `ℚ(√−3)`. N5 L436 says "with all its determinant
components", and h-b1 M2 works with a `ℚ`-irreducible component, so the proof is unaffected. A
Lean statement of R1fp must not require `GeometricallyConnected`. Consistency check: the Weil
pairing on `A[3] = η(𝒪/3𝒪)` takes a value in `μ₃∖{1}` fixed by Galois, so every field of
definition of a level-3 object contains `ℚ(√−3)`.

### 2.2 The polarization is determined by `(A, ι)`

Claim (argument assembled here from STANDARD inputs; SPECULATIVE until reviewed). Let `F` be a
field of characteristic 0, `A/F` an abelian surface and `ι : 𝒪 ↪ End_F(A)`. Then `A` has exactly
one principal polarization `λ` over `F` whose Rosati involution induces `a ↦ a† = μ⁻¹āμ` on
`ι(𝒪)`.

- *Uniqueness* (h-trust A4 item 2, VERIFIED there as an argument). If `λ' = λ∘a` has the same
  Rosati involution, then `a` commutes with `ι(B)`, so `a` lies in the centralizer: `ℚ`, or an
  imaginary quadratic `k` by the dichotomy A9. Also `a` is Rosati-symmetric and positive, so
  `a ∈ ℚ_{>0}`. Both polarizations are principal, so `a⁴ = 1`, hence `a = 1`.
- *Existence over `ℂ`.* `H₁(A, ℤ)` is a faithful `𝒪`-module of rank 4 over `ℤ`, hence locally
  free of rank 1. It is free, because an indefinite maximal order has class number 1 (Eichler;
  Vignéras LNM 800 Ch. III §5, UNVERIFIED locator). Write `H₁ = 𝒪·v`. Then:
  - the Riemann forms compatible with `ι` and `†` are the alternating forms `E` on `B` with
    `E(ax, y) = E(x, a†y)`;
  - **in Lean** (`BPQM.eq_smul_E0`) these are exactly the multiples `r·E₀`,
    `E₀(x, y) = trd(μ⁻¹xȳ)`;
  - a principal one has `r = ±1` (`BPQM.eq_pm_E0_of_principal`, from `det gram = 1`);
  - exactly one sign is positive for the complex structure. The complex structures commuting
    with `𝒪` form the two sheets of `{J ∈ B_ℝ : J² = −1}`, and `E₀(xJ, x)` is definite with
    opposite signs on the two sheets (STANDARD, Shimura's uniformization of QM surfaces).
- *Existence over `F`.* By uniqueness, the polarization over `F̄` is fixed by `Gal(F̄/F)`, so it
  descends.

Consequence: for every field `K ⊇ ℚ`, (A4's PEL objects `(A, ι, λ, η)` over `K`)/≅ =
(`QML3 K`)/≅ = `M3 K`. Here `QML3 K` (Lean, `QMAbVar.lean` §4) is the problem without `λ`.
Buzzard 1997 (Thm 2.1 and Cor. 2.3, as cited by N5 at L444; whether his Thm 2.1 covers full
level 3 directly or only through N5's detour via `V₁(5)` and the finite étale
`Isom_𝒪(𝒪/3𝒪, A[3])` of N5 L447-452 is UNVERIFIED) works with `(A, ι)` and level structure,
without a polarization. So R1fp can be supplied either way:
- *Buzzard route:* one paper, no polarization anywhere;
- *Shimura–Deligne route:* PEL moduli, plus the claim above as glue. That glue needs
  polarizations in Lean, so it comes later.

### 2.3 The field-point leaves (Lean shapes; R5fp compiled, the others need N8 and N11)

Notation (existing or built here):
- `PkgI3.AbVar K` and `End`, `Pt`, `galAct`, `baseChange` (kernel);
- `BPQM.O`, `BPQM.AV.QMStr`, `Level3`, `QML3`, `M3`, `QML3.twist`, `QML3.rightMul` (built here);
- `QML3.baseChange` (N8; `QMStr.baseChange` is built, the level part is not);
- `fieldOfModuli` (N9; built for QM pairs, needed for level-3 objects in R1rec);
- `com` (N10; built), written `com(P)` below;
- `P1` with `P1pt : (Spec K ⟶ P1) ≃ OnePoint K` (N11).

Statements:

```lean
-- R1fp (consequence of Buzzard 1997 Thm 2.1 on the generic fibre, or of Shimura 1967 /
-- Deligne 1971 Thm 4.21 + §2.2). Y₃ represents the problem on fields, naturally.
def R1fp : Prop :=
  ∃ (Y : Over (Spec (.of ℚ))) (_ : IsProper Y.hom) (_ : SmoothOfRelativeDimension 1 Y.hom)
    (Φ : ∀ (K : Type) [Field K] [Algebra ℚ K], (specOverℚ K ⟶ Y) ≃ M3 K),
    ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
      (y : specOverℚ K ⟶ Y), Φ L (specMap f ≫ y) = M3.baseChange f (Φ K y)

-- R1hecke (Deligne 1971 §§4.15-4.21 / 1979 §2.7, UNVERIFIED): the operations `twist α`
-- (α ∈ Aut 𝒪) and `rightMul u` (u ∈ 𝒪ˣ), which change only (ι, η), are induced by
-- automorphisms of Y over ℚ (part of the same ∃ as R1fp).
--   ∀ α, ∃ g : Y ≅ Y, ∀ K y, Φ K (y ≫ g.hom) = M3.twist α (Φ K y)      (and likewise rightMul)

-- R2fp (Baba–Granath 2008 Thm 2.1, Lemma 3.1; normalization by the three CM values).
--   ∃ π : Y ⟶ P1, for P Q : QML3 ℚ̄:
--     π(Φ⁻¹[P]) = π(Φ⁻¹[Q]) ↔ ∃ α u, Nonempty (((P.twist α).rightMul u).Iso Q)
--   and, writing com(P) for the centralizer of ι(𝒪) in End(P.A):
--     (∃ φ ∈ com P, φ * φ = -1) → π(Φ⁻¹[P]) = 0
--     (∃ φ ∈ com P, φ * φ - φ + 1 = 0) → π(Φ⁻¹[P]) = ∞
--     (∃ φ ∈ com P, φ * φ = -6) → π(Φ⁻¹[P]) = -16/27

-- R1rec (Shimura reciprocity at CM points, Shimura 1967 Main Thm II / Deligne 1971 §3,
-- UNVERIFIED; only the unramified consequence is used, by Lemma NV):
--   for P : QML3 ℚ̄ with com(P) ≅ ℤ[i], ℤ[ζ₃] or ℤ[√-6], fieldOfModuli P is unramified at
--   every prime p ≥ 5.

-- R5fp: COMPILED in QMAbVar.lean §7 as `BPQM.AV.R5fp` (degree clause) and
-- `BPQM.AV.R5fpCount` (count clause, b = #{p ∈ {2,3} : p𝒪_k prime}, as in h-cm's 2^b·h(𝔬)).
-- (González–Rotger 2006, Prop. 5.6, Thms 5.8, 5.12, read by the locator audit; on
-- X₆ = X₀(6,1), i.e. for (A, ι) without level structure; degree form):
--   for an order R of conductor f, (f,6) = 1, in an imaginary quadratic field and optimally
--   embeddable in 𝒪, and (A, q) over ℚ̄ with com(A, q) ≅ R:
--     finrank ℚ (fieldOfModuli (A, q)) ∈ {Nat.card (CommRing.Pic R), 2 * Nat.card (CommRing.Pic R)}
--   and #{(A, q) : com ≅ R}/≅ = 2 ^ #{p ∣ 6 : p inert in R} * Nat.card (CommRing.Pic R).
```

Faithfulness notes (each must be checked by whoever compiles them).

- **R2fp needs `π` to be a morphism of schemes.**
  - A function on points `M3 ℚ̄ → OnePoint ℚ̄` with the fibre and CM clauses does not determine
    `j`: points can be permuted freely.
  - A morphism `Y → P¹` that is invariant under `Γ'` and has degree 1 on `Y/Γ' ≅ X₆/W` is pinned
    down by its values at three points (`0, ∞, −16/27`). So the normalization is not an extra
    leaf (h-decomposition R2: "Thm 2.1 and Lemma 3.1 alone do not fix the numerical
    normalization of `j`"; with three prescribed CM values it is fixed).
  - The branch *indices* are not part of R2fp. The locator audit found that `4, 6, 2` are
    orbifold orders, not indices of `X₆ → X₆/W`. The use of indices in Lemma NV (h-b1 M4) is
    under separate review, and R2fp makes no claim about them.
- **The CM clauses of R2fp go through `com(P)`.** A point fixed by `ι(x)` with `x ∈ 𝒪`,
  `x² = −1` gives the endomorphism "multiplication by the eigenvalue" of `ℂ²` preserving
  `ι(𝒪)v_τ`, and conversely (STANDARD: CM points correspond to optimal embeddings). This matches
  `PkgI1.QMHauptmodul`'s value clauses.
- **R1fp uses the full functor on fields**, including transcendental `K` such as `ℚ(t)`, so that
  `Φ` sees the generic point. Then `ℚ(Y)` is the field of moduli of the generic object, and the
  Galois extension `M/ℚ(j)` of Prop. TS is `ℚ(Y^{(1)})/π^*ℚ(j)`.
- **R5fp lives on `X₆`, not `Y₃`** (locator audit). It is about `(A, ι)` without `η`, and its
  "field of moduli" is the residue field of the coarse moduli space `X₆`. Identifying the two
  needs `X₆` as a coarse moduli space, a consequence of R1 at level 1. Whether NoCM (h-cm) uses
  the count on the right curve is the separate review's question (h-trust A10 note). The degree
  form is weaker than Thms 5.8 and 5.12 (`ℚ(x) = H_R` or its specified index-2 subfield, with
  `[H_R:ℚ] = 2h(R)`). It avoids ring class fields, which need class field theory for orders.
  `h(R) = #Pic(R)` uses Mathlib's `CommRing.Pic` (VERIFIED, `RingTheory/PicardGroup.lean`).
- **R1an** (for F1; very large): for `K ⊆ ℂ` and `P : QML3 K` there are `τ ∈ ℍ^±` and an
  `𝒪`-equivariant isomorphism of complex Lie groups `P.A(ℂ) ≅ ℂ²/ι(𝒪)(τ, 1)ᵀ`, carrying the
  polarization of §2.2 to `±E₀`. With R2fp and `PkgI1.QMHauptmodul`, the glue gets
  `π(P) = j_θ(Ω(τ))`: two holomorphic Hauptmoduln of `Γ*∖ℍ` with the same values at three
  points coincide. This gives F1. Stating R1an needs N14.

### 2.4 The weak statement suggested in the task

"For each QM surface over a number field, a point of the analytic quotient with the right Igusa
invariants."
- **As a statement about Igusa invariants** it needs Jacobians of genus-2 curves (or Igusa
  invariants of a principally polarized surface), node N15, large. It feeds F1 only through
  Thomae's formula (theta constants from the roots of the sextic), a further theorem; combining
  it with Pazuki would merge publications (hdec-elementary's variant, not adopted).
- **As a statement about period matrices** ("a `τ` with `A_σ ≅ A_τ`") it is R1an. It carries F1
  completely, with QMHauptmodul and ThetaModularity.
- **Either way** it gives none of A5 (fibre field, ramification), A7 (conjugates) or A10 (NoCM).
  Those use the global structure over `ℚ`: the function field of `Y₃`, the action of `Γ'` and of
  Galois on fibres, and reciprocity. In field-point terms that is R1fp + R1hecke + R2fp + R1rec
  + R5fp.

So the weak statement is worth stating, as R1an, but only as the F1 part of the package.

---

## 3. Dependency graph

Tiers (SPECULATIVE estimates of Lean size): **S** under 500 lines, **M** 500-3 000, **L**
3 000-15 000, **VL** above 15 000 or research-level formalization.

```
Mathlib: QuaternionAlgebra, Subring, ZMod ─────────────► N1 𝒪 ─► N2 † ─► N3 E₀, uniqueness ─┐
                                                         │                                  │
                                                         └─► N4 normalizer, (𝒪/3𝒪)ˣ = 72    │
Kernel Objects.lean: AbVar, End, Pt, galAct, baseChange ─► N5 QMStr ─► N6 Level3, Γ'-action │
                                                                   │                       │
                                                                   ▼                       │
                                                             N7 QML3, Iso, M3 ◄────────────┘ (§2.2)
                                                                   │
              ┌──────────────────────┬─────────────────────────────┼───────────────┐
              ▼                      ▼                             ▼               ▼
        N8 base change ──► N9 field of moduli       N10 commutant, CM order   kernel A6 ─► A6 on QML3 (done)
              │                      │                             │
Mathlib: Over, Proper, SmoothOfRelDim, functionField, Proj ─► N11 P¹, curves over ℚ
              │                      │                             │
              ▼                      ▼                             ▼
        ┌─ R1fp ◄── N11      R1rec ◄── N9, N10        R5fp ◄── N9, N10, CommRing.Pic
        ├─ R1hecke ◄── N6, N8
        └─ R2fp ◄── N10, N11
                                  N12 polarizations (dual AV) ──► (only for: Shimura–Deligne
                                                                   route of R1fp, R22, T9)
                                  N13 abelian schemes / A[3] / representability ──► (literal R1 only)
                                  N14 analytification, period lattice ──► R1an ──► F1
                                     (shared with T11, R22)
                                  N15 genus-2 Jacobians, Igusa invariants ──► literal R3
                                  N16 ring class fields (CFT for orders) ──► literal R5 fields
```

| Node | Object | Depends on | Tier | Status | Needed by |
| --- | --- | --- | --- | --- | --- |
| N1 | maximal order `𝒪` of `B = (2,−3)` as a `Subring`, structure constants | Mathlib `QuaternionAlgebra` | S | **done** (`BPQM.O`, `ofInt_mul`) | all |
| N2 | Rosati involution `†`: anti-involution, preserves `𝒪`, positive | N1 | S | **done** (`dag_dag`, `dag_mul`, `dag_mem`, `trd_mul_dag_pos`) | N3, R1an |
| N3 | Riemann form `E₀`, `†`-compatibility, integrality, unimodularity; uniqueness of compatible forms | N2 | S | **done** (`E0_rosati`, `E0_gram`, `gram_det`, `eq_smul_E0`, `eq_pm_E0_of_principal`) | §2.2, R1an |
| N4 | normalizer elements `w₂, w₃, w₆`; relations of `W ≅ (ℤ/2)²` modulo `ℚ^×𝒪^×`; `\|(𝒪/3𝒪)^×\| = 72` | N1 | S | **done** (`w2_normalizes`, `w3_normalizes`, `mu_normalizes`, `atkinLehner_relations`, `card_units`); the full `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²` needs T29 + class number one: M, open | A3, R2fp |
| N5 | QM structure `ι : 𝒪 ↪ End_K(A)`, action on `A(L)` | N1, kernel `AbVar` | S | **done** (`QMStr`, `endPt`, `qmAct`, `qmModule`) | all |
| N6 | level-3 structure; `Γ'` acting by `twist`, `rightMul`; units `≡ 1 mod 3` act trivially | N5 | S | **done** (`Level3`, `Level3.twist`, `Level3.rightMul`, `rightMul_eq_self`) | R1fp, R1hecke, R2fp |
| N7 | objects `QML3 K`, isomorphisms, classes `M3 K` | N6 | S | **done** (`QML3`, `QML3.Iso`, `Iso.refl`, `Iso.symm`, `Iso.trans`, `isoSetoid`, `M3`, `M3'`) | R1fp |
| — | A6 on every object | N7 + kernel A6 | S | **done** (`QML3.goodReduction`) | A6 |
| N8 | base change of `QMStr`, `Level3`, `QML3`, `M3` along `K → L` (incl. `σ ∈ Aut(L)`) | N7, kernel `baseChange`, Mathlib `Functor.map.instIsMonHom`, `(Over.pullback f).Faithful`; leaf `TorsionStructure` for `Level3` | M | **half done**: `endBC` (ring hom `End_K A → End_L A_L`), `endBC_injective`, `QMStr.baseChange`. Open: `Level3.baseChange` (needs `A(K̄)[3] ↠ A_L(L̄)[3]`, from `TorsionStructure` and injectivity of points along the epimorphism `Spec L̄ → Spec K̄`), `dim A_L = dim A`, compatibility with composition | R1fp naturality, A7, N9 |
| N9 | field of moduli of an object over `K̄`: fixed field of `{σ : σP ≅ P}` | N8, Mathlib `IntermediateField.fixedField` | S | **done for QM pairs** (`QMIso`, `conjAV`, `conjQM`, `fieldOfModuli`); for level-3 objects it waits for `Level3.baseChange` | R1rec, R5fp |
| N10 | centralizer of `ι(𝒪)` in `End(A)`; "CM by the order `R`"; `h(R) = #CommRing.Pic R` | N5, Mathlib | S | **partly done** (`com`, `HasCM4`, `HasCM3`, `HasCM24`, `intCast_mem_com`); the conductor and discriminant of `com q` as an order: open | R2fp, R1rec, R5fp |
| N11 | `P¹_ℚ` as a scheme with `P¹(K) ≃ OnePoint K`; smooth proper curves over `ℚ` | Mathlib `Proj`/gluing, `SmoothOfRelativeDimension`, `IsProper` | S-M | open (Mathlib has `Proj` and `𝔸ⁿ`, no ready `P¹` point bijection) | R1fp, R2fp |
| N12 | dual abelian variety, polarizations, Rosati involution of a polarization | Picard scheme | L-VL | missing everywhere | the Shimura–Deligne route of R1fp (§2.2 glue), R22, T9 |
| N13 | abelian schemes over a base with `𝒪`-action, `A[3]` as a finite flat group scheme, representability | N12 | VL | missing | literal R1 only |
| N14 | analytification `A(ℂ)` as a complex Lie group, `H₁`, period matrix in `𝔥₂` | Mathlib manifolds; T11 | VL | missing | R1an (F1), R22, T11, T12 |
| N15 | Jacobians of genus-2 curves; Igusa invariants of a principally polarized surface | N12 or explicit models | L | missing (the invariants of sextics exist: `PkgI1.J2..J10`) | literal R3 (not on the critical path, §2.4) |
| N16 | ring class fields `H_R` | class field theory | VL | missing | literal R5 (the degree form avoids it) |

What exists to build on (VERIFIED by grep in `.lake/packages/mathlib` and the kernel):
- `QuaternionAlgebra`, `Subring`, `ZMod`, `Matrix.det_smul`;
- `Over`, `Grp`, `IsProper`, `Smooth`, `SmoothOfRelativeDimension` (`AffineSpace.lean`);
- `Scheme.functionField`, `Proj` (`ProjectiveSpectrum/`), `CommRing.Pic`,
  `IntermediateField.fixedField`, `Functor.map.instIsMonHom` (`Monoidal/Mon.lean:845`, needed
  for N8);
- kernel: `PkgI3.AbVar` with `End` ring, `Pt`, `galAct`, `baseChange`, the bridge `ObjBridge`,
  and A6.

Mathlib lacks:
- ample line bundles, the Picard scheme or dual abelian variety;
- quaternion orders;
- analytification;
- `P¹` with its point bijection.

Prereq-survey (row A4) lists an Anthropic FLT development, `CerednikDrinfeld.QM.FakeEllipticCurve`
with `FullLevel m`, `QMCanonicalPol`, `QMRigidification` (built for Čerednik–Drinfeld). Its
`QMCanonicalPol` appears to be the canonical-polarization statement of §2.2 (SPECULATIVE from
the name; not examined, the source is not on this host). A team should check whether it can
supply N12-N13 or a proof of §2.2 before building them.

---

## 4. The cheapest faithful route

**Stage 0 (done here):** N1-N7, half of N8, part of N10, and A6 on the objects; 3 files, about
950 lines.

**Stage 1 (statements; about M in total):**
1. N7: done (setoid). Remaining: transport of `twist`/`rightMul` to `M3'`. S.
2. N8 base change:
   - `QMStr.baseChange`: **done** (`endBC` by `(Over.pullback f).map`, a ring homomorphism by
     functoriality and `Functor.map_mul` of the monoidal pullback; injective by Mathlib's
     faithfulness of the pullback);
   - `Level3.baseChange`: choose an embedding `K̄ → L̄` over `K → L` and pull points back along
     `Spec L̄ → Spec K̄`. Injectivity on points holds because `Spec L̄ → Spec K̄` is an
     epimorphism (Mathlib `epi_of_flat_of_surjective`). Surjectivity onto `A_L(L̄)[3]` holds by
     counting with `TorsionStructure` on both sides; this needs `dim A_L = dim A`, not in
     Mathlib as far as checked. Galois invariance transfers through the restriction
     `Aut(L̄/L) → Aut(K̄/K)`.
   - M. This is the main new work of Stage 1. Note that it consumes a leaf (`TorsionStructure`),
     so the naturality clause of R1fp is stated over a definition whose well-definedness is glue
     depending on a leaf. The alternative is to define the level structure scheme-theoretically,
     as an isomorphism of group schemes `(𝒪/3𝒪)_K ≅ A[3]`; it base-changes trivially but needs
     the kernel `A[3]` as a group scheme (finite limits in `Over`, available in Mathlib).
3. N9, N10. S each.
4. N11: `P¹_ℚ` and `P¹(K) ≃ OnePoint K`. S-M.
5. State R1fp (+ R1hecke), R2fp, R1rec, R5fp as `def … : Prop` and replace the placeholders
   `HSyn.R01_ShimuraDeligne`, `R02_BabaGranath`, `R05_GonzalezRotger` of
   `scratch/h-decomposition/Leaves.lean` by them. R3 stays inside `QMHauptmodul` (composite,
   already statable).

**Stage 2 (glue from the Stage 1 leaves; about M):**
- A3's degree bound, from R1hecke + R2fp and N4.
- A4: the object over the residue field, from R1fp.
- A5's Galois extension `M/ℚ(j)` and the fibre field (h-b1 M2, M8), from R1fp, R1hecke, R2fp
  and Mathlib's function fields. Prop. TS itself is h-b1's glue with leaves T1-T2 (purity,
  Abhyankar).
- A7: conjugates lie in one `Γ'`-orbit, so they share `A` (`QML3.twist_A`, `rightMul_A` are
  `rfl` already).
- NoCM: the finiteness step from R5fp; the explicit exclusion is h-cm's arithmetic.

**Stage 3 (the analytic link; VL, shared):**
- N14, then R1an, then F1 from R1an + R2fp + `QMHauptmodul` + `ThetaModularity`
  (`thetaRatio_invariant` and `f1_algebra` are already proved).
- Share with WP10 (Faltings and theta heights, R22) and T11.
- Fallback if N14 is out of reach: keep F1's analytic interface as an explicit hypothesis of the
  final theorem, stated over `PkgI1.Omega`. Then only the identification of `A_σ` with some
  `A_τ` is assumed.

**Not on the route:**
- N13 (representability), N12 (polarizations) for R1/R2/R5, N15 (Jacobians), N16 (ring class
  fields).
- Each is needed only for a literal form of a leaf whose field-point consequence suffices.

---

## 5. The Lean layer built here (VERIFIED: compiles, no `sorry`, standard axioms only)

`scratch/bp-qmmoduli/QMOrder.lean` (Mathlib only, about 15 s):
- `BPQM.B := QuaternionAlgebra ℚ 2 0 (-3)`.
- `ofInt`, `ofInt_eq_sum` (agrees with pkg-I1's `oBasis`), `mulCoord`, `ofInt_mul`, and
  **`O : Subring B`**.
- `mu`, `muInv`, `trd`, `nrd`, `mul_star_eq_nrd`.
- **`dag`** (`x† = μ⁻¹x̄μ`) with `dag_eq'` (`= μx̄μ⁻¹`, because `μ² = −6` is central), `dag_dag`,
  `dag_mul`, `dag_add`, `dag_smul`, `dag_one`, `dag_ofInt`, `dag_mem`.
- **`trd_mul_dag_pos`**: `trd(x x†) = 2x₀² + 4x₁² + 18x₂² − 48x₂x₃ + 36x₃² > 0` for `x ≠ 0`.
- `E0`, `E0bil`, `E0_alt`, **`E0_rosati`** (`E₀(ax, y) = E₀(x, a†y)`), `E0_gram` (N5's Gram
  matrix), `gram_det = 1`, `E0_int`.
- **`eq_smul_E0`**: every alternating `ℚ`-bilinear form `E` on `B` with
  `E(ax, y) = E(x, a†y)` equals `r·E₀`.
  - Proof: `E(x, y) = f(x†y)` with `f = E(1, ·)`.
  - Alternation at `x = 1, 1+i, 1+j` gives `f(1) = f(i) = f(j) + f(k) = 0`.
- **`eq_pm_E0_of_principal`**: if moreover the Gram determinant on N5's basis is 1, then
  `E = ±E₀`.
- `NormalizesO`, `w2_normalizes`, `w3_normalizes`, `mu_normalizes`, `nrd_w2 = 2`, `nrd_w3 = 3`,
  `nrd_mu = 6`.
- **`atkinLehner_relations`**: `w₃² = −3`; `μ² = −6`; `w₂² = 2(i+j)` with `i+j ∈ 𝒪¹`;
  `w₂w₃ = uμ` with `u ∈ 𝒪`, `nrd u = 1`.

`scratch/bp-qmmoduli/Units72.lean` (about 18 s): `BPQM.Mod3.card_units`. The two-sided units of
`𝒪/3𝒪`, modelled on `Fin 4 → ZMod 3` with the reduced structure constants, number 72
(`decide +kernel`, no `native_decide`). This is the count of h-trust A3 and h-b1 M3.

`scratch/bp-qmmoduli/QMAbVar.lean` (imports `ZInQKernel.HDecomp.A6.A6` and Mathlib's
`Morphisms/FlatDescent`, about 30 s; §0 copies
the order from `QMOrder.lean`, because scratch files cannot import each other):
- `endPt`: the ring homomorphism `End_K(A) → End(A(L))`.
- **`QMStr A`**: an injective `𝒪 →+* End_K(A)`.
- `qmAct`, `qmModule`.
- **`not_qmStr_zero`** (sanity): the zero abelian variety has no QM structure.
- **`Level3 q`**: an additive map `η : 𝒪 → A(K̄)` that is `𝒪`-linear, has kernel exactly
  `3𝒪`, is onto `A(K̄)[3]` and is pointwise `Gal(K̄/K)`-fixed. In characteristic 0 (and in
  every characteristic `≠ 3`, where `A[3]` is étale) this is an `𝒪`-linear isomorphism of
  constant group schemes `𝒪/3𝒪 ≅ A[3]` over `K`, h-trust A4 item 3.
- `Level3.tors`, `Level3.eq_iff`.
- **`Level3.rightMul`** (the `𝒪^×` action) and **`rightMul_eq_self`** (units `≡ 1 mod 3𝒪` act
  trivially, so the action factors through `(𝒪/3𝒪)^×`).
- **`QMStr.twist`, `Level3.twist`**: the `Aut(𝒪)` action, `(ι, η) ↦ (ι∘α, η∘α)`.
- **`QML3 K`** (surface, QM, level 3), **`QML3.Iso`**, `Iso.refl`, **`M3 K`** (a `Quot`).
- `QML3.twist`, `QML3.rightMul` with `twist_A`, `rightMul_A` (`rfl`: `Γ'` does not change `A`).
- **`QML3.goodReduction`**: for `P : QML3 K` and a DVR `Ov ⊆ K` with `3 ∈ Ov^×`,
  `PkgI2.HasGoodReduction (ObjBridge.toGrp P.A) Ov`, from `NeronOggShafarevich`,
  `RaynaudCriterion`, `TorsionStructure` via `GlueA6Alg.goodReduction_of_QM_rational3'`.
  - The hypotheses are discharged with `I = ι(i)`, `J = ι(j)` and the products `i² = 2`,
    `j² = −3`, `ji + ij = 0` in `𝒪` (`oi_mul_oi`, `oj_mul_oj`, `oj_mul_oi_add`).
  - The rational 3-torsion comes from `Level3.onto` and `Level3.rational`.
- §7:
  - `QMIso` (with `symm`, `trans`, `refl`), `QMPair`, `pairSetoid`;
  - `conjAV`, `conjQM` (conjugation by `σ ∈ Aut(ℚ̄/ℚ)`), **`fieldOfModuli`**, `conductor`,
    `inertCount6`;
  - the leaf statements **`R5fp`** and **`R5fpCount`**. They are `def … : Prop`s, not proved and
    not used, and they need the faithfulness review of §6 item 6.
- `QML3.Iso.twist`, `QML3.Iso.rightMul`, `M3'.twist`, `M3'.rightMul`: the `Γ'` operations on
  isomorphism classes. Not done: that inner twists (`Ad(u)` with `u ∈ 𝒪^×`, combined with
  `rightMul u⁻¹`) are trivial on classes. The attempt timed out in elaboration (log).
- §6:
  - `QML3.Iso.symm`, `QML3.Iso.trans`, `isoSetoid`, `M3'` (the `Quotient`);
  - `com q` (centralizer of `ι(𝒪)` in `End_K A`), `HasCM4`, `HasCM3`, `HasCM24` (the hypotheses
    of R2fp's value clauses), `intCast_mem_com`;
  - **`endBC`** (`End_K(A) →+* End_L(A_L)`), `specMap_flat`, `specMap_surjective`,
    **`endBC_injective`**, **`QMStr.baseChange`**.

Caveats.
- **`QML3 K` is uninhabited in Lean today.** Mathlib cannot construct a nonzero abelian variety
  (kernel `AbVar.zero` docstring), so no object can be exhibited. The definitions are tested by
  the sanity theorem and by A6's use, not by an example.
- The polarization is omitted from `QML3` by design (§2.2). Deriving R1fp from Shimura–Deligne's
  PEL statement needs §2.2 as glue in Lean, hence N12. From Buzzard's statement it does not.
- `M3` is a `Quot` by the isomorphism relation; `M3'` is the same set as a `Quotient` by the
  proved setoid `isoSetoid`.
- The copy of the order in `QMAbVar.lean` §0 should become one shared module at integration
  (suggested: `ZInQKernel/HDecomp/QM/Order.lean` and `QM/Structures.lean`).
- Pitfalls met (log):
  - `ι` and `η` are tokens under the kernel's `open`s, so the fields are named `iota` and `eta`;
  - `mul_assoc` is ambiguous with `MonObj.mul_assoc`;
  - `ring` fails on the noncommutative `𝒪`; use `noncomm_ring`.

---

## 6. Risks and open checks

1. **§2.2 is argued here, not read.** It is SPECULATIVE until a review. Its lattice core is
   proved in Lean, and its uniqueness half is h-trust A4 item 2. The existence half uses class
   number one for `𝒪` and the sign argument.
2. **Buzzard's Thm 2.1 for full level 3.** UNVERIFIED (no network). N5 applies it to `V₁(5)`
   and adds the level-3 structure as a finite étale `Isom` sheaf. A team should check whether
   "false elliptic curve" in Buzzard includes a polarization; it is recalled here as not
   including one.
3. **R2's branch indices** (locator audit) are not resolved here. R2fp asserts only the fibre
   structure and the three CM values. h-b1's Lemma NV (M4) uses inertia orders `e_i` over the
   branch points of `Y₃ → P¹_j`. Those orders are stabilizer orders in `Γ'`, a consequence of
   R1hecke + R2fp + neatness, so they should be derived in glue rather than taken from
   Baba–Granath (SPECULATIVE; for the separate review).
4. **R5 lives on `X₆`.** Its use on `Y₃` and on `X₆/W` by NoCM is under separate review
   (h-trust A10 note). R5fp is stated on `X₆`, for `(A, ι)` without level.
5. **Geometric components.** `Y₃` has two geometric components defined over `ℚ(√−3)` (§2.1).
   Any statement requiring geometric connectedness of `Y₃` would be false.
6. **Uncompiled statements.** The statements of §2.3 other than R5fp are not compiled. Their
   final form depends on N8 and N11. Each, including R5fp, needs a faithfulness review like
   rv-leaves-a/b before it replaces a placeholder. Points to check in R5fp:
   - that "centralizer `≅ R`" matches González–Rotger's CM points by `R` (optimal embeddings);
   - that the degree disjunction is implied by Thms 5.8 and 5.12 in all the cases they cover
     (they print `ℚ(x) = H_R` or a specified index-2 subfield);
   - the coarse-moduli identification of `ℚ(x)` with `fieldOfModuli`.
