# rv-qm-polar: the polarization premise of the QM leaves

Status: review note (task rv-qm-polar, 2026-11-12). Lean companion `scratch/rv-qm-polar/QMPolar.lean`
(Mathlib only, compiles with `lake env lean`, no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound`); exact checks `scratch/rv-qm-polar/polar_checks.py`; results log
`scratch/rv-qm-polar/log.md`. No file under `ZInQKernel/`, `blueprint/` or another task's directory was
edited.

Marks. **VERIFIED**: read in a named source, computed, or compiled. **STANDARD**: published, with
its reference. **SPECULATIVE**: an assessment. There is no network on this host, so every theorem
number recalled from memory is **UNVERIFIED**. N5 = `diophantine_zq.tex`, cited by line.

---

## 0. Verdict: PREMISE HOLDS WITH CONDITIONS

The premise (bp-qmmoduli §2.2), restated so that it is true:

> **Lemma P.** Let `F` be a field of characteristic 0, `A/F` an abelian surface and
> `ι : 𝒪 ↪ End_F(A)` a unital ring embedding (`𝒪` the maximal order of N5, discriminant 6). Fix
> `μ ∈ 𝒪` with `μ² = −6` (N5: `μ = 2j + ij`). Then `A` has exactly one principal polarization
> `λ` over `F` whose Rosati involution restricts on `ι(𝒪)` to `ι(b) ↦ ι(μ⁻¹b̄μ)` (**type `μ`**).

Lemma P holds whether `End(A_F̄)` equals `𝒪` or is larger (the CM points). Its conditions:

- **C1 (the type is fixed).** This is the only condition with content.
  - Without the type, "the principal polarization of `(A, ι)`" is **not unique**. `(A, ι)` has one
    principal polarization of type `c` for each `c ∈ 𝒪` with `c² = −6`, taken up to sign. These
    are infinitely many distinct polarizations: the `𝒪¹`-orbit of `μ` is infinite, because its
    stabilizer is `ℤ[√−6]^× = ±1`.
  - Each of them is `λ_μ ∘ ι(v)` for a unique `†`-symmetric `v ∈ 𝒪` with `nrd v = 1`.
    **Compiled:** `type_eq_mu_mul`, and the explicit second type `ν = 2j − k` in
    `two_principal_types` and `Enu_not_rosati_mu`.
  - When `End(A) = 𝒪`, these are *all* the principal polarizations of `A`. This is Rotger's
    theorem; §1.3 explains why `A` can carry several non-isomorphic ones in general.
  - The PEL moduli problems of Shimura and Deligne fix the involution (§1.1), so they fix the
    type. Every leaf is therefore read with a fixed `μ`. The λ-free statements do not depend on
    which `μ` is fixed (§1.4).
- **C2 (characteristic 0).** The proof goes through `ℂ` (Lefschetz principle) and Galois descent.
  All leaves are over `ℚ`-algebras, so this is no restriction.
- **C3 (`𝒪` maximal).** The proof uses this twice:
  - `H₁(A, ℤ)` is free over `𝒪`, by class number one;
  - `E_c` is unimodular exactly when `c𝒪` is the different. For `c ∈ 𝒪` with `c² = −6` this
    always holds; it is compiled as part of `type_eq_mu_mul`.
- **C4 (isomorphisms and twists).**
  - Every `𝒪`-equivariant isomorphism `(A, ι) ≅ (A', ι')` carries `λ` to `λ'`, by uniqueness.
  - The `Aut(𝒪)`-twist `(A, ι) ↦ (A, ι∘α)` corresponds to `(A, ι, λ) ↦ (A, ι∘α, λ∘ι(εv_α))`. Here
    `v_α = μ⁻¹α(μ) ∈ 𝒪¹` is `†`-symmetric and `ε = sign trd v_α`. This is defined in families
    (`twist_type`, compiled).
  - For the Atkin–Lehner generators `χ₂ = i` and `χ₃ = j + k`, `v = −1` and `λ` is unchanged:
    `χ` anticommutes with `μ` (`dag_conj_chi2/3/mu`, compiled). These are Rotger's twisting
    involutions.

Consequences:
- **Leaves (§2).** Every QM leaf of `scratch/leaf-qm-fp/QMLeaves.lean` stated without `λ`
  (`R1fpProps`, `X6Props`, `R1heckeProps`, `R2X6Props`/`R2fpProps`, `CMExists`, `X6Surj`,
  `R1recProps`, `R1rec`, `R5ptProps`, `R5fp`, `R5fpCount`) is a consequence of its published
  PEL statement (involution of type `μ`) together with Lemma P. **No Lean statement needs
  correcting.**
  - The docstrings that call the premise SPECULATIVE need the repair of §4.
  - One caution remains. Lemma P is a second published input folded into each leaf, because
    polarizations cannot yet be stated in Lean.
- **Glue (§3).** A4, A7, Lemma NV step 2 and h-b1 M9 are unaffected. The polarized form of A7
  (N5 L532, "the same geometric polarized moduli point") also holds. It uses the D = 6 twisting
  fact (C4), which is compiled. rv-jac-ext N1 gets its principal polarization over `K` from Lemma
  P (existence, descent).

Status of Lemma P itself:
- *Argument:* VERIFIED as an argument here (§1.2).
  - Uniqueness is h-trust A4 item 2, re-checked.
  - The existence lattice core is compiled: bp-qmmoduli `eq_pm_E0_of_principal`, copied here,
    and `type_eq_mu_mul`.
  - The sign step is **compiled** (`riemann_sign`, `lemmaP_lattice`, §5): for every complex
    structure `j`, exactly one of `±E₀` is a principal Riemann form. So Lemma P holds on every
    QM torus `ℂ²/𝒪v`, with every step in Lean except class number one (`H₁` free) and the
    descent from `ℂ` to `F`.
- *Published:* see §1.2. The locators are UNVERIFIED (no network). N5's v14 text cites Buzzard
  1997, p. 592, for exactly this uniqueness (h-v14 rows L699-705 and L1014; UNCHECKED there).

---

## 1. What the literature proves

### 1.1 The PEL moduli problem fixes the involution (STANDARD)

- **Deligne, *Travaux de Shimura*** (Sém. Bourbaki 389, 1971, §4), Milne (*Introduction to Shimura
  varieties*, §8) and Kottwitz (JAMS 5, 1992, §5) state the PEL datum as `(B, *, V, ψ)`:
  - `*` is a **fixed** positive involution of `B`;
  - `ψ` is an alternating form with `ψ(bx, y) = ψ(x, b*y)`.
- The moduli problem classifies `(A, ι, λ, η)` with `λ ∘ ι(b*) = ι(b)^∨ ∘ λ`, i.e. the Rosati
  involution of `λ` induces `*` on `ι(𝒪)`.
- For an indefinite quaternion algebra over `ℚ`, every positive involution is `b ↦ μ⁻¹b̄μ` with
  `μ ∈ B`, `μ² < 0` (STANDARD: the centre `ℚ` has no automorphism, so every involution is of the
  first kind, and the positive ones on an indefinite quaternion algebra are `b ↦ μ⁻¹b̄μ` with
  `μ² < 0`; Albert's type II, Mumford, *Abelian varieties*, §21, UNVERIFIED locator).
- A principal `ψ` on `𝒪` forces `μ𝒪` to be the different, so `μ² = −D` up to `ℚ^{×2}`
  (`type_eq_mu_mul` direction: every `c ∈ 𝒪` with `c² = −6` gives a unimodular form).
- Shimura's 1967 construction (Ann. of Math. 85, §§2-3, UNVERIFIED locators) has the same shape:
  a polarization of fixed type with Rosati inducing a fixed involution `ρ`.
- N5 L410-421 fixes `μ = 2j + ij` and the form `trd(μ⁻¹xȳ)` (Gram determinant 1, VERIFIED
  `gram_det`). That is the datum of the type-`μ` problem.

So the published moduli theorems (R1: Shimura 1967, Deligne 1971 Thm 4.21; X₆ as a coarse space)
are statements about type-`μ` triples `(A, ι, λ)` (plus `η`), not about pairs `(A, ι)`.

### 1.2 Lemma P: existence and uniqueness of the type-`μ` principal polarization

*Published* (all locators UNVERIFIED):
- **Buzzard**, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §1, p. 592.
  N5 v14 cites it at the line where it asserts that "the principal polarization with a given
  positive Rosati involution is unique" (h-v14 rows L699-705 and L1014, status UNCHECKED). As
  recalled, Buzzard's moduli problem of false elliptic curves `(A, i)` carries no polarization
  for this reason. Checking whether p. 592 states uniqueness only, or also existence, is a
  one-page job.
- **Rotger**, *Quaternions, polarizations and class numbers*, J. reine angew. Math. 561 (2003),
  §§3-4. For `End(A) ≅ 𝒪` maximal in an indefinite `B` of discriminant `D`, principal
  polarizations of `A` correspond to `{μ ∈ 𝒪 : μ² + D = 0}` up to sign, and isomorphism classes
  to `𝒪^×`-conjugacy classes. Their number `π₀(A)` is expressed by class numbers of `ℚ(√−D)`
  orders (recalled, UNVERIFIED).
- **Rotger**, *Modular Shimura varieties and forgetful maps*, Trans. AMS 356 (2004), §§2-4.
  - For each `μ` there is a principal polarization `L_μ` of type `μ` on every `(A, ι)`. The
    forgetful map `X_D → 𝒜₂`, `(A, ι) ↦ (A, L_μ)`, depends on `μ`.
  - Its fibres are orbits of the subgroup `W₀ ⊆ W` of twisting involutions.
  - (Recalled, UNVERIFIED; the owner's "J. Algebra 2004" item was not identified here.)
- Boutot–Carayol, Astérisque 196-197 (1991), Ch. III, has the analogous lemma for false elliptic
  curves over a base (recalled, UNVERIFIED).

*Proof (VERIFIED as an argument; inputs STANDARD).*
- **Uniqueness.** Let `λ, λ'` both be of type `μ`, with `a = λ⁻¹λ' ∈ End(A)`.
  - The Rosati involution of `λ'` is `x ↦ a⁻¹x^†a`. Equality on `ι(𝒪)` makes `a` commute with
    `ι(𝒪)`.
  - `a` is `†`-symmetric and totally positive.
  - The centralizer of `ι(B)` in `End⁰(A_F̄)` is `ℚ` or an imaginary quadratic `k` (A9:
    `End⁰ = B` or `M₂(k)`). `†` restricts to a positive involution on it, i.e. complex conjugation
    on `k`, so its symmetric elements are `ℚ`.
  - Hence `a ∈ ℚ_{>0} ∩ End(A) = ℤ_{>0}`, and `deg λ' = a⁴` gives `a = 1`.
  - This covers CM points. It is h-trust A4 item 2, re-checked here.
- **Existence over `ℂ`.**
  - `Λ = H₁(A, ℤ)` is a torsion-free `𝒪`-module of `ℤ`-rank 4. `𝒪` is hereditary, so `Λ` is
    projective of rank 1. Class number one of indefinite maximal orders (Eichler; Vignéras LNM
    800, Ch. III §5, UNVERIFIED locator) makes it free: `Λ = 𝒪v`.
  - The complex structure commuting with `𝒪` is right multiplication by some `j ∈ B_ℝ` with
    `j² = −1`.
  - Alternating type-`μ` forms on `Λ` are `rE₀`, and principal ones are `±E₀` (bp-qmmoduli
    `eq_smul_E0`, `eq_pm_E0_of_principal`, compiled; copied here).
  - `E₀(xj, yj) = E₀(x, y)` since `nrd j = 1`.
  - `E₀(xj, x) = trd(μ⁻¹·xjx̄)` is definite. On pure quaternions `nrd` has signature `(1, 2)`
    over `ℝ`. Both `μ⁻¹` and `xjx̄` are timelike when `nrd x ≠ 0`, and `xjx̄` is null but nonzero
    when `x ≠ 0` has `nrd x = 0`. Reverse Cauchy–Schwarz makes their pairing nonzero, with a sign
    constant on each sheet of `{j² = −1}`.
  - So exactly one of `±E₀` is a Riemann form. **Compiled** in a different form from the
    Cauchy–Schwarz argument above. The Gram matrix of `x ↦ E₀(xj, x)` (`j = ai + bj + ck`,
    `q = 3b² − 2a² − 6c² = 1`) has leading minors `2(b−c)`, `4(b²−2c²)`, `8(b+c)q` and `16q²`.
    These are all positive when `b > 0` and alternate in sign when `b < 0` (`Qpoly_ldl`,
    `riemann_sign`, `lemmaP_lattice`). This agrees with rv-blueprints' numerical
    `sheet_check.py`.
- **Existence over `F`.**
  - `A, ι` are defined over a finitely generated subfield; embed it in `ℂ`. The polarization
    over `F̄` is unique, hence fixed by `Gal(F̄/F)` (which fixes `ι`), and it descends because
    `Hom_F = Hom_F̄^{Gal}`.
  - Uniqueness over an arbitrary algebraically closed `F̄ ⊇ ℚ` uses A9 over `F̄`, which follows
    by rigidity of `End` under extension of algebraically closed fields (STANDARD).

### 1.3 Non-uniqueness when the type is free (Rotger), made explicit for D = 6

- **Every type is a unit transport of `μ`** (`type_eq_mu_mul`, compiled). For `c ∈ 𝒪` with
  `c² = −6` there is `v ∈ 𝒪` with:
  - `c = μv`, `nrd v = 1` and `v^† = v`;
  - `E_c(x, y) = trd(c⁻¹xȳ) = E₀(x, vy)`.

  So the type-`c` polarization of `(A, ι)` is `λ_μ ∘ ι(εv)`. For every `(A, ι)` in characteristic
  0, the principal polarizations whose Rosati involution preserves `ι(𝒪)` are in bijection with
  `{c ∈ 𝒪 : c² = −6}/±1`. (Assembled here from Lemma P, `type_eq_mu_mul` and the classification
  of positive involutions; SPECULATIVE only in that no source was read.)
- **A concrete second type** (`two_principal_types`, `Enu_not_rosati_mu`, `dagNu_ne_dag`,
  `nu_conj`, compiled). Take `ν = 2j − k ∈ 𝒪`, `ν² = −6`.
  - `E_ν` is alternating, integral and unimodular on `𝒪`, and compatible with `x ↦ ν⁻¹x̄ν`.
  - `E_ν` is not a rational multiple of `E₀` and is not compatible with `†`.
  - `ν = −vμv⁻¹` with `v = −1 + i`, `nrd v = −1`.

  So on every `(A, ι)` the polarizations `λ_μ ≠ λ_ν` are distinct and isomorphic through the
  automorphism `ι(v)`.
- **Up to isomorphism, for `End(A) = 𝒪`.** Rotger's `π₀(A)` is the number of `𝒪^×`-classes of
  `{c : c² = −6}/±`.
  - Evidence that it is 1 for `D = 6`: all 12 solutions with coordinates in `[−6, 6]` are
    `𝒪^×`-conjugate to `±μ` (`polar_checks.py`, VERIFIED computation).
  - An Eichler count for `ℤ[√−6]`, where 2 and 3 ramify, gives `h = 2` normalized classes,
    merged by a unit of norm −1. (SPECULATIVE; Rotger's own table UNVERIFIED.)
  - Not needed by any leaf.
- When `End(A_ℚ̄) ⊋ 𝒪` (CM points), `A` may carry further principal polarizations that do not
  preserve `ι(𝒪)`. No leaf uses them.

### 1.4 Independence of the choice of `μ`; the forgetful map

- **Independence of `μ`.** For any two types `c, c'`, the type-`c` and type-`c'` PEL problems
  have the same underlying groupoid of pairs `(A, ι)`, by Lemma P for each. So every λ-free
  statement is the same whichever `μ` the source fixes. The leaves need no `μ` in their Lean
  form.
- **The twisting involutions** (VERIFIED: `chi2_sq`, `chi3_sq`, `chi2_mu`, `chi3_mu`,
  `chi2_chi3`, `chi2_normalizes`, `chi3_normalizes`, `dag_conj_chi2/3/mu`, `w_eq_chi_mul`).
  - `χ₂ = i` and `χ₃ = j + k` lie in `𝒪`, normalize it, square to 2 and 3, and anticommute with
    `μ`; also `χ₂χ₃ = μ`.
  - bp-qmmoduli's `w₂ = 1+i+j` and `w₃ = j` are `χ₂, χ₃` times units of norm −1.
  - So every class of `W ≅ (ℤ/2)²` contains a twisting element, i.e. `W₀ = W` in Rotger's
    notation. The forgetful map `X₆ → 𝒜₂` factors through `X₆/W`. This matches Baba–Granath Thm
    2.1 ("polarized moduli = `V/W`", read by the locator audit) and N5 L533-534 ("its two twisting
    involutions generate the whole Atkin–Lehner group").
  - For a discriminant with `W₀ ≠ W` this would fail, and the polarized form of A7 would need
    more.

---

## 2. Leaf by leaf (`scratch/leaf-qm-fp/QMLeaves.lean`)

General transport. Lemma P with C4 gives, for every field `K ⊇ ℚ`, a bijection
`{(A, ι, λ, η) of type μ}/≅ → {(A, ι, η)}/≅ = M3 K`. The bijection:
- commutes with base change: the base change of `λ` is of type `μ`, hence equals the unique one;
- commutes with Galois conjugation (`σλ` is of type `μ` for `σι`);
- commutes with the twists `rightMul u`, which do not touch `λ`;
- commutes with the twists `twist α`, through `λ ↦ λ∘ι(εv_α)` (`twist_type`).

Fields of moduli of `(A, ι, λ, η)` and `(A, ι, η)` coincide (same stabilizer in `Aut(ℚ̄/ℚ)`).
Likewise at level one for `QMPair`.

| Leaf | Published statement (with `λ`, type `μ`) | λ-free Lean form is | Correction |
| --- | --- | --- | --- |
| `R1fpProps` (in `R1fp`, `R1R2fp`) | `Y₃` fine moduli of `(A, ι, λ, η)` (Shimura 1967; Deligne 1971 Thm 4.21) | consequence: restrict to fields, transport by Lemma P; naturality by base change of `λ` | none (docstring repair §4) |
| `X6Props` | `X₆` coarse moduli of `(A, ι, λ)`; `W` acts over `ℚ` | consequence: `X₆(ℚ̄)` = classes of pairs; the `W` action through C4 (`λ` unchanged for `χ₂, χ₃`) | none |
| `R1heckeProps` | the normalizer of `K₃` acts on `Y₃` over `ℚ` | consequence: `twist α` is a functor automorphism of the type-`μ` problem in families (`twist_type`); `rightMul` does not touch `λ` | none |
| `R2X6Props` / `R2fpProps` | Baba–Granath Thm 2.1, Lemma 3.1, §3 table: `X₆/W ≅ P¹`, CM images rational | consequence: the fibre clause is the quotient by `W`, whose moduli action is `Aut(𝒪)`-twisting of pairs; no `λ` enters | none |
| `CMExists` | CM points of discriminants −4, −3, −24 exist on `X₆` | consequence (pairs = points) | none |
| `X6Surj` | `π₆` onto, `Y₃ → X₆` onto | no `λ` | none |
| `R1recProps`, `R1rec` | Shimura reciprocity on the canonical model | consequence: fields of moduli coincide | none |
| `R5ptProps`, `R5fp` | González–Rotger 2006 Thm 5.12 (with 5.8) on `X₀(6,1)` | consequence: points of `X₆` = classes of pairs, residue fields and fields of moduli unchanged | none |
| `R5fpCount` | González–Rotger Prop. 5.6: `#CM(R) = 2^{b}h(R)` points of `X₀(6,1)` | consequence: points = classes of pairs `(A, ι)` | none |

Verdict for step 2: **every λ-free statement is a consequence of the published statement for the
type-`μ` PEL problem together with Lemma P. None is stronger, so no corrected Lean statement is
required.** The scratch file therefore contains no restated leaves. Instead it compiles the
algebra behind conditions C1 and C4, which are the only places where a misreading could make a
leaf false:
- a leaf over pairs `(A, ι)` that asserted uniqueness of *the* principal polarization of `A`, or
  of `(A, ι)` with free type, would be false (§1.3);
- a PEL-form twist that kept `λ` for every `α ∈ Aut(𝒪)` would be ill-typed for inner `α` (it
  changes the type to `α(μ)`), but is correct for `W` (§1.4).

The one structural caveat:
- Lemma P is folded into the leaves, which are therefore "published moduli theorem + published
  Lemma P". This cannot be split into two Lean hypotheses until `PkgI3.AbVar` has dual abelian
  varieties and polarizations (WP4).
- If the human check of Buzzard p. 592 or Rotger 2003 finds only uniqueness printed, existence
  becomes glue. It is proved in §1.2, with its lattice core and sign step in Lean
  (`eq_smul_E0`, `lemmaP_lattice`).

---

## 3. The glue that uses these leaves

- **A4** (`exists_fibre_object`). No `λ` is used; unaffected. Downstream consumers that need `λ`
  get it from Lemma P:
  - rv-jac-ext N1 needs a principally polarized `(A, λ)` over `K` with `A_K̄` simple. Take
    `λ = λ_μ`, which exists over `K` by descent, since `ι` is defined over `K` at a `K`-point
    (R1fp gives the object over the residue field). Simplicity is from A10.
  - F1/R1an's "carrying the polarization of §2.2 to `±E₀`" is correct as stated for type `μ`
    (sign by positivity).
- **A7** (`conj_twist_of_rational`, `conj_iso_of_rational`, `fibre_conjugates_isomorphic`).
  - The compiled conclusion, `σA ≅ A` over `ℚ̄` as abelian surfaces through an `Aut(𝒪)`-twisted
    QM isomorphism, uses no `λ`; unaffected. h-trust A7 needs only this, or even an isogeny.
  - N5's polarized form (L532: "the same geometric polarized moduli point") also follows.
    Write `α = Ad(u)∘Ad(χ)` with `u ∈ 𝒪^×` and `χ` a product of `χ₂, χ₃`:
    - `Ad χ` keeps `λ` (`dag_conj_chi2/3/mu`);
    - `Ad u` is undone by the automorphism `ι(u)`, which carries `λ_μ` to `λ_μ` by uniqueness.

    Hence `(σA, σλ) ≅ (A, λ)` over `ℚ̄` (SPECULATIVE only in being written here, not compiled at
    the abelian-variety level).
- **Lemma NV step 2** (`unramified_over_branch`, `residue_unramified_over_branch`). Uses
  `R1recProps`/`R1rec` and `cm_of_val`; no `λ`. The λ-free field of moduli equals the PEL one.
  Unaffected.
- **h-b1 M9** (`cm_of_val`). Uses `R2X6Props` and `CMExists`; no `λ`. Unaffected.

---

## 4. Repairs (exact text)

1. **bp-qmmoduli §2.2.**
   - Replace "Claim (argument assembled here from STANDARD inputs; SPECULATIVE until reviewed)"
     by "Claim (Lemma P; VERIFIED as an argument by rv-qm-polar §1.2; published: Buzzard 1997
     p. 592 and Rotger 2003/2004, locators UNVERIFIED)".
   - After "exactly one principal polarization `λ` over `F` whose Rosati involution induces
     `a ↦ a† = μ⁻¹āμ` on `ι(𝒪)`", add: "The type `μ` must be fixed: `(A, ι)` has one principal
     polarization of each type `c ∈ 𝒪`, `c² = −6`, up to sign (infinitely many, all
     `λ_μ∘ι(v)`, `v ∈ 𝒪¹` symmetric; rv-qm-polar `type_eq_mu_mul`, `two_principal_types`)."
   - In §0 item 2, replace "a principal polarization whose Rosati involution restricts to
     `x ↦ μ⁻¹x̄μ` on `𝒪` exists and is unique (§2.2)" by "for a fixed `μ`, a principal
     polarization whose Rosati involution restricts to `x ↦ μ⁻¹x̄μ` on `𝒪` exists and is unique
     (§2.2; without fixing `μ` it is not unique)".
2. **leaf-qm-fp.md §0 ("Dependence on an unreviewed claim")**, **§5 item 1**, and the docstrings
   of `QML3`, `R1fp`, `R5fp`, `R5fpCount` and `QMLeaves`: replace "bp-qmmoduli §2.2 ...
   SPECULATIVE" by "Lemma P (rv-qm-polar §0): for a fixed `μ` (N5's `2j+ij`), the type-`μ`
   principal polarization of `(A, ι)` exists and is unique in characteristic 0, also at CM
   points; VERIFIED as an argument, lattice cores compiled (`eq_pm_E0_of_principal`,
   `type_eq_mu_mul`), published locators UNVERIFIED. The published moduli theorems are for the
   type-`μ` PEL problem; the λ-free leaves are their consequences via Lemma P and do not depend on
   the choice of `μ`."
3. **leaf-qm-fp.md §2.2 (`R1heckeProps`)**, the parenthesis "With `λ` in the functor ...":
   - Replace "`λ' = ±λ∘ι(μ⁻¹μ')`, `μ'` rescaled to norm 6" by "`λ' = λ∘ι(εv)`,
     `v = μ⁻¹α(μ) ∈ 𝒪¹` `†`-symmetric (`twist_type`), `ε = sign trd v`".
   - Add: "for the Atkin–Lehner generators `i`, `j + k`, `v = −1` and `λ' = λ`."
4. **h-trust A4 item 2.** Add after "Alternatively Rotger ...": "Existence: rv-qm-polar §1.2.
   Buzzard 1997 p. 592 is the locator N5 v14 gives."

---

## 5. Lean (`scratch/rv-qm-polar/QMPolar.lean`, compiled, Mathlib only)

`lake env lean scratch/rv-qm-polar/QMPolar.lean` takes about 1 minute: no errors, linter warnings
only. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `two_principal_types`,
`Enu_not_rosati_mu`, `type_eq_mu_mul`, `twist_type`, `dag_conj_chi3`, `chi3_normalizes`,
`w_eq_chi_mul`, `riemann_sign`, `E0R_mul_j` and `lemmaP_lattice` (VERIFIED). There is no `sorry`.
- §§1-4 are copied from bp-qmmoduli `QMOrder.lean`: `O`, `mu`, `dag`, `E0`, `gram_det`,
  `eq_smul_E0`, `eq_pm_E0_of_principal`.
- §5:
  - `nu`, `Enu`, `dagNu`;
  - `Enu_alt`, `Enu_rosati`, `Enu_int`, `gramNu_det`;
  - `dagNu_ne_dag`, `Enu_ne_smul_E0`, `Enu_not_rosati_mu`, `two_principal_types`;
  - `nu_conj`.
- §6: `Ec`, `Ec_mu`, **`type_eq_mu_mul`** and **`twist_type`**.
  - `type_eq_mu_mul` uses a mod-2 and mod-3 descent, decided over `ZMod 2` and `ZMod 3`.
  - `twist_type` holds for any `α : O ≃+* O`.
- §7:
  - `chi2`, `chi3`, `chi2_mem`, `chi3_mem`, `chi2_sq`, `chi3_sq`;
  - `chi2_mu`, `chi3_mu`, `chi2_chi3`;
  - `chi2_normalizes`, `chi3_normalizes`;
  - `dag_conj_chi2`, `dag_conj_chi3`, `dag_conj_mu`, `w_eq_chi_mul`.
- §8 (over `B_ℝ = QuaternionAlgebra ℝ 2 0 (−3)`):
  - `pure_of_sq`: `j² = −1` gives `j` pure with `nrd j = 1`;
  - `E0R_mul_j`: `E₀(xj, yj) = E₀(x, y)`;
  - `Qpoly_ldl` (explicit `LDLᵀ`), `Qpoly_pos`;
  - **`riemann_sign`**: `x ↦ E₀(xj, x)` is positive definite if `imJ(j) > 0` and negative
    definite if `imJ(j) < 0`;
  - **`lemmaP_lattice`**: exactly one `r ∈ ℚ` has `det(r·gram) = 1` and `r·E₀(xj, x) > 0` for all
    `x ≠ 0`.

Not in Lean:
- class number one of `𝒪` (`H₁(A, ℤ)` free over `𝒪`);
- Lemma P at the level of abelian varieties, which needs polarizations (WP4);
- `π₀(A) = 1` for `D = 6` (evidence only).

## 6. Open checks

1. Read Buzzard 1997 p. 592 and Rotger 2003 §§3-4 / 2004 §§2-4 for the printed statements of
   Lemma P and of the twisting criterion. All locators here are UNVERIFIED.
2. The audit's qualification on R1 (Deligne's PEL model specializes to this functor) is
   unchanged by this note. This note settles only the polarization part of it.
