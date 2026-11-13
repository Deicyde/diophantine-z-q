# leaf-push: more of H's leaves stated concretely

## Verdict

Five of the 19 placeholders of docs/research/h-decomposition.md (§2.3) now have concrete Lean
statements over genuine definitions: **R8, T9, T23, T29, T32**. All compile (VERIFIED,
Lean 4.35.0 / Mathlib v4.35.0). Each is either the published statement or a consequence of it,
never stronger. With them the count becomes **40 of 54 leaves** stated concretely (was 35; the
synthesis' count is taken as given, VERIFIED there). The other **14** (R1, R2, R3, R5, R16,
R17, R18-R22, T10, T11, T12) cannot be stated faithfully today. For each one, the table in §2
names the definition that is missing. None of the 14 has a consequence form that avoids its
missing object without assuming another leaf's content.

| Leaf | Lean name | file | E/C | new definitions used |
| --- | --- | --- | --- | --- |
| R8 Grothendieck semistable reduction | `LeafPush.R08_GrothendieckMonodromy` | `scratch/leaf-push/Push.lean` | C (monodromy form) | pkg-I2's (copied) |
| T9 Weil pairing | `LeafPush.T09_WeilPairing` | `Push.lean` | C (finite-level, polarization hidden) | pkg-I2's (copied) |
| T29 local normalizers | `LeafPush.T29a_DivisionNormalizer`, `LeafPush.T29b_SplitNormalizer` | `Push.lean` | E | `QIntegral`, `IsOUnit`, `IsIntMat` (one line each) |
| T32 tame inertia, quadratic ramification | `LeafPush.T32a_TameQuadratic`, `LeafPush.T32b_QuadraticRamification` | `Push.lean` | C | `IsAtPrime`, `inertiaQ` (one line each) |
| T23 Fontaine closure | `PkgI4.T23_FontaineClosure` | `scratch/leaf-push/PushDR.lean` | E (matrix form) | pkg-I4's `IsDeRham` (copied), `ContRep` |

Scratch files cannot import each other, so `Push.lean` §1 copies pkg-I2's abelian-variety
layer verbatim (I2.lean lines 69-140), and lines 1-1108 of `PushDR.lean` are pkg-I4's I4.lean
verbatim. When the files are integrated, the copies should be replaced by the originals.

## 1. The new statements

Theorem numbers are UNVERIFIED (no network, no library here), except where a repository note
VERIFIED them. Each docstring in the Lean files gives the published statement, the reference and
the reason the Lean form is that statement or a consequence of it. Summary:

**R8 (Grothendieck, SGA 7 I, Exp. IX, Thm 3.6, with the direction "semistable ⇒ `(σ−1)² = 0`
on `T_ℓ`" of Prop. 3.5).** Lean: for `K` with a DVR `O`, a valuation ring `w` of `K̄` over `O`
and an abelian variety `A/K`, there is a finite `K' ⊆ K̄` such that every inertia element of `w`
fixing `K'` satisfies `(σ−1)² = 0` on every `A(K̄)[ℓⁿ]`, `ℓ` invertible in `O`. This is pkg-I2's
`GrothendieckMonodromy` (pkg-I2 note §4), so the novelty is the classification: what pkg-I2
showed for Raynaud (R6) applies equally to R8. The synthesis listed R8 as "new defs (Néron
models)" and mentioned the consequence only in passing. The proof uses R8 only on h-b1's route
for A6, where the Galois form is the form used. Consequence.

**T9 (Mumford §20, §23; Milne 1986 §§13, 16).** Lean: for every abelian variety `A/K` there are
`d ≥ 1` and pairings `e n` on `A(K̄)` such that, for every `n ≥ 1` invertible in `K`, on `A[n]`
the pairing `e n` takes values in `μ_n`. It is bimultiplicative and alternating, and Galois
equivariant: `e(σx, σy) = σ(e(x, y))`. It satisfies `e_n(x^m, y^m) = e_{mn}(x, y)^m`, and its
left kernel is killed by `d`. Proof that this is a consequence: take `e n x y = e_n(x, λy)` for
a polarization `λ = φ_L` defined over `K`. Alternation is `e^L_n(x, x) = 1` (§23). For the left
kernel, there is `ψ` with `λψ = [d]`, so `d·Â[n] ⊆ λ(A[n])`, and `e_n` is perfect. The first
draft required `(n, d) = 1`. That version is too weak for C8 step 1 (h-trust), which needs
`ℓ = 5` even when 5 divides the polarization degree, so it was revised (log). In the limit over
`n = ℓᵏ` the pairing is perfect on `V_ℓ A`, so `G_K` acts through `GSp` with cyclotomic
multiplier. That limit step is glue. The polarization is existentially hidden, because
polarizations need the dual abelian variety, which is missing. This is why the Lean form is a
consequence (C), not the theorem itself.

**T29 (Vignéras, LNM 800, Ch. II §§1-2).** (a) For `(a, b)_{ℚ_p}` with anisotropic norm form
(a division algebra), the following holds. The integral elements (reduced trace and norm in
`ℤ_p`) are closed under `+` and `·`. Some integral `π` is not of the form `ℚ_p·𝒪^×`. Every
`x ≠ 0` lies in `ℚ_p^×𝒪^× ∪ ℚ_p^×π𝒪^×`. Together these say that the index is exactly 2.
(b) The normalizer of `M₂(ℤ_p)` in `GL₂(ℚ_p)` is `ℚ_p^×GL₂(ℤ_p)`. Both are written over
Mathlib's `QuaternionAlgebra`, `Padic`, `Matrix`. The local-to-global bookkeeping of A3
(`|N/𝔸_f^×K₀| ≤ 4`) remains glue. The synthesis rated T29 "cheap", and it was.

**T32 (Serre, *Local fields* IV §2; Neukirch I-III).** The definition the synthesis called
missing, "inertia subgroups of `G_ℚ`", is one line: `inertiaQ w` is Mathlib's
`ValuationSubring.inertiaSubgroup` for a valuation ring `w ⊆ ℚ̄` over `ℤ_(p)`, pushed into
`Aut(ℚ̄/ℚ)` with the Krull topology. Here `ℤ_(p)` is characterized as a valuation subring of `ℚ`
that is a DVR in which `p` is not a unit. (a) For `p` odd, exactly 2 continuous homomorphisms
`I_w → ℤˣ` exist. This is the "unique quadratic character of inertia" of glue-descent L-B3a.
(b) For `d ≡ 1 mod 4` squarefree and `s² = d`, some inertia element moves `s` iff `p | d`. This
is L-B3b for the character of `ℚ(√d)`. Both are consequences: (a) combines the structure of
tame and wild inertia with the identification `I_w ≅ I(ℚ̄_p/ℚ_p)`; (b) combines `disc ℚ(√d) = d`
with "ramified ⇔ inertia acts nontrivially".

**T23 (Fontaine, Astérisque 223, Exp. III §1.5 with Thm 3.8 / Exp. II §3; Brinon–Conrad 5.2.1,
6.3.3, 6.3.8).** These are continuous `ℚ_p`-representations of `G_{ℚ_p}`, given as matrix
homomorphisms, with pkg-I4's `IsDeRham` (`dim_{ℚ_p} D_dR = n`, built on Mathlib's `B_dR`). The
leaf states that de Rham representations are closed under five operations: basis change; dual
(`ρ⁻ᵀ`); subquotients (the diagonal blocks of a block upper-triangular `ρ`); direct sums (block
diagonal); tensor products (Kronecker, reindexed). Each clause is a special case of the
published statement. It is stated for `ℚ_p` coefficients, which is Fontaine's setting. For
`E`-coefficients, which N5 uses for `r₅ ⊂ V₅(A) ⊗ E`, the reduction from `E`-coefficients to
`ℚ_p`-coefficients is glue: restriction of scalars, and `D_dR` commutes with it.

## 2. Placeholders that cannot be stated now

| Leaf | Missing definition (the smallest one that blocks a faithful statement) |
| --- | --- |
| R1 Shimura–Deligne | The dual abelian scheme (Picard scheme), hence polarizations and Rosati involutions over a base. Also PEL moduli functors and their representability by a curve over `ℚ`. Complex uniformization needs analytification (as T11). Mathlib has abelian schemes as `Grp (Over S)`, so the `𝒪`-action and level structures are definable; polarizations are not. |
| R2 Baba–Granath | The canonical model `X₆/ℚ` (via R1) and its Atkin–Lehner quotient. The analytic part alone ("a Hauptmodul of `Γ*\ℍ` takes values `0, ∞, −16/27` at the elliptic points") is empty, since any three points can be moved there by a Möbius map. The content is the `ℚ`-structure. pkg-I1's `QMHauptmodul` is a statable consequence of R2 + R3 + R4 together, not of R2 alone. |
| R3 Lin–Yang | Jacobians of genus-2 curves (Picard scheme), to say "`End⁰(Jac C) ⊇ B`". The Igusa-invariant side is already in Lean. |
| R5 González–Rotger | As R2 (CM points of `X₆` and their fields of definition over `ℚ`), plus ring class fields `H_R` of imaginary quadratic orders (class field theory for orders). An analytic form, "`[ℚ(f(τ_R)):ℚ] ∈ {h(R), h(R)/2}` for pkg-I1's explicit Hauptmodul `f`", is statable, but it is a consequence of R2 + R3 + R4 + R5 together, not of R5 alone. |
| R16 Eichler–Shimura in `J₁(N)` | The modular curve `X₁(N)` over `ℚ` as a scheme and its Jacobian. |
| R17 Carayol | The Artin conductor of an ℓ-adic representation of `G_{ℚ_p}`, `a(ρ) = codim V^{I} + ∫₀^∞ codim V^{G^u} du`. This needs the absolute upper-numbering filtration `G^u` of `G_{ℚ_p}`. pkg-I6 defines `upperRam` for a finite extension of local rings, so what is missing is the passage to the absolute group: restriction to finite Galois `L/ℚ_p`, rings of integers as local rings, and compatibility (Herbrand, which pkg-I6 states). Medium; not done in this run. The proof's D5 uses the quantitative equality `v_p(N) = a(ρ)`, so the existing `PkgI4.CarayolUnramified` (exponent 0) does not suffice. |
| R18 Javanpeykar, R19 Gaudron–Rémond, R20 Faltings' lemma, R21 Bost | The Faltings height. It needs the semistable Néron model over `𝒪_K` (or the Arakelov degree of `ω_{A/𝒪_K}` with its `L²` metrics). R18 also needs Belyi maps and Jacobians. |
| R22 Pazuki | The Faltings height and the theta height `h_Θ` of a principally polarized surface. The latter needs level-2 theta structures, so it also needs polarizations. |
| T10 `V_ℓ ≅ H¹_et^∨` | ℓ-adic étale cohomology. |
| T11 Riemann/GAGA, T12 Artin comparison | The analytification of a `ℂ`-scheme (a complex manifold or analytic space), and `H₁(A(ℂ), ℚ)`. |

## 3. Counts after this task

- Stated concretely: research R4, R6, R7, R8, R9, R10, R13, R14, R15, plus R11 + R12 jointly
  (11 leaves); textbook T1-T9 and T13-T32 (29 leaves). Total **40 of 54**.
- Placeholders: **14**. Very large definitions: R1-R3, R5, R16, R18-R22. Large: T10, T11, T12.
  Medium: R17.
- New Props: 7 (R08, T09, T29a, T29b, T32a, T32b, T23).

## 4. Caveats

- All new statements are statements only. None is proved, and none is used by a Lean proof yet.
  The glue that consumes them (A3's index count from T29, the `GSp` limit from T9, the
  `E`-coefficient form of T23, the use of T32 in glue-descent) is not written.
- T32's definitions use a valuation ring `w` of `ℚ̄`. That `inertiaQ w` is the classical
  inertia group, closed and isomorphic to that of `ℚ̄_p/ℚ_p`, is part of the leaf's published
  content (Neukirch II §9; UNVERIFIED locator). It is not proved.
- T9 depends on pkg-I2's points `Spec K̄ ⟶ A` and its multiplicative group law. T23 depends on
  pkg-I4's `B_dR` with `G_{ℚ_p}`-action. Both inherit those packages' reviews and none beyond
  them.
- The copied blocks are verbatim (VERIFIED by construction with `sed`). No other task's file was
  edited.
