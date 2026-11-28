# `y3FullThreeRepZ30` from eight printed statements

`Y3Buzzard.y3FullThreeRepZ30_of_printed_min5`, in `../Y3FullThreeRepZ30.lean`, proves the formerly
open statement `Y3RouteA.Y3FullThreeRepZ30` from eight hypotheses. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`. Each hypothesis is a `def ... : Prop` that states a printed
theorem, or a short consequence of printed theorems, over the definitions in `BuzzardLeaves.lean`.
This note quotes the prints and writes out the steps they do not contain, for the statement check.
After the folds of `ZInQKernel/OneProof/H/TailZ109.lean` to `TailZ111.lean`, only `milneProp207At3`,
`milneProp207At5` and `milneZeroPreservingHomLN` are fields of the frozen theorem as listed here:
`GeomCard3` and `BuzzardFrameRepTorsor 5` are proved from Milne (`../BuzzardFrameRepTorsor5.lean`,
field `milneTorsionCount : MilneRem84`), and `docs/one-proof/OPEN.md` lists the leaves that replaced
the other three.

## The eight hypotheses

| Field | Lean | Kind | Print | Steps |
|---|---|---|---|---|
| `buzzardThm21Cor23V15` | `Y3Buzzard.BuzzardThm21Cor23V15'` | consequence | Buzzard 1997, Thm 2.1 and Cor. 2.3 at U = V₁(5) | B-1, B-5 |
| `buzzardFrameRepTorsor5` | `Y3Buzzard.BuzzardFrameRepTorsor 5` | consequence | Buzzard 1997, §1, the sentence after Def. 1.1 | B-4 |
| `milneProp207At3` | `Y3Buzzard.MilneProp207 3` | published | Milne 1986, Prop. 20.7 | none |
| `milneProp207At5` | `Y3Buzzard.MilneProp207 5` | published | Milne 1986, Prop. 20.7 | none |
| `milneTorsionCount3` | `Y3Buzzard.GeomCard3` | published | Milne 1986, Rem. 8.4 with §20 | none |
| `milneZeroPreservingHomLN` | `Y3Buzzard.ZeroPreservingIsHomLN` | published | Milne 1986, Cor. 20.2(a) | none |
| `serreRigidityLevel3` | `Y3Buzzard.SerreRigidityLevel3'` | consequence | Milne 1986, Cor. 2.2 and Prop. 17.5(b); Buzzard 1997, §1 | B-2, B-3 |
| `projectiveFalseEllipticCurve` | `Y3Buzzard.ProjectiveFEC` | consequence | Buzzard 1997, §1; Lan 2008; Stacks Project | B-6 |

## Copies read

- K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), read in the
  author's preprint, https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf.
  Page numbers are the preprint's, as recorded in this repository's locators (the moduli problem
  p. 2, the canonical principal polarization p. 3, Thm 2.1 p. 5, Lemma 2.2 p. 6, Cor. 2.3 p. 7).
  The text extraction used here has no page heads, so they were not re-checked. Journal pages
  are UNVERIFIED.
- J. S. Milne, *Abelian varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic
  Geometry*, Springer (1986), read in the author's retyped edition,
  https://www.jmilne.org/math/xnotes/AVs.pdf. Pages are that edition's, read from its running
  heads. Pages of the 1986 printing are UNVERIFIED.
- J. S. Milne, *Abelian varieties*, course notes v2.0 (2008),
  https://www.jmilne.org/math/CourseNotes/AV.pdf. These notes are unrefereed and are cited only
  beside the 1986 statements, or for one standard step in B-2.
- K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis (2008),
  http://www.kwlan.org/articles/cpt-PEL-type-thesis-single.pdf, and its 2021 revision,
  http://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf. Unrefereed; the 2013 book was
  not checked.
- J. Voight, *Quaternion algebras*, GTM 288, https://jvoight.github.io/quat-book.pdf,
  Thm 15.5.5 (p. 241 of that PDF), for the maximality of `O`.
- The Stacks Project, tags 01VT, 0C4K, 0B45, 02GW and 025G.

## How they were read

Every quotation below was located by exact text search in fresh text extractions of these copies,
made on 26 November 2026. The quotations in the Lean docstrings were compared with the source text
mechanically. The judgement that each print implies its Lean statement was made by AI readers: a
primary reading, three or more independent readers per source, and three independent referees of
steps B-1 to B-6, none of whom found a step wrong. No human has compared these statements with the
prints. Under this repository's rules the published rows therefore enter unread, and the
consequence rows enter pending review.

## Definitions (`BuzzardLeaves.lean`)

- `O` is the maximal order Z⟨1, i, (1 + j)/2, (i + k)/2⟩ of B = (2, -3)_Q, with i² = 2,
  j² = -3 and k = ij. Its reduced discriminant is 6, so it is maximal (Voight, Thm 15.5.5).
- `FEC S` is an abelian scheme A of relative dimension 2 over S (proper, smooth of relative
  dimension 2, a group object, with geometrically connected fibres) with a ring homomorphism
  ι : O → End_S(A). Buzzard also asks ι to be injective; over a nonempty base that is automatic
  (B-1).
- `IsGenAt M A s P`: at a geometric point s, a ↦ ι(a)P is a bijection from O/MO onto A_s[M].
  Clause 1 says ι(a)P = 0 exactly when a ∈ MO; clause 2 says every M-torsion point is some ι(a)P.
- `IsGen M A P`: P is M-torsion and `IsGenAt` holds at every geometric point.
- `e5` is 3 + 2k, with reduced trace 6 and reduced norm -15.
- `V15 A` is a section Q with 5Q = 0 and ι(e5)Q = 0 that is nonzero at every geometric point.
- `V15Fibre` asks for an O-compatible cartesian square that carries Q′ to Q.
- `Z30Base` is Spec Z[1/30], and `PN N` is P^N over Z[1/30].

## The prints

Subscripts and exponents are transcribed.

**Buzzard, §1 (p. 2).** "A false elliptic curve over S is a pair (A/S, i) where A/S is an
abelian surface (that is, A is an abelian scheme over S of relative dimension two), and
i : O_D ↪ End_S(A) is an injective ring homomorphism"

**Buzzard, §1 (p. 3).** "if (A/S, i) is a false elliptic curve, then there is a unique principal
polarisation on A such that if s is a geometric point of S, then the corresponding Rosati
involution on End(A_s) induces ∗ on O_D"

**Buzzard, §1, the paragraph after Def. 1.1**, for M prime to d = 6 and S a Z[1/Md]-scheme.
"Then F_{A/S,M} is represented by a closed subscheme of A[M], and this representing scheme is an
étale (O_D ⊗ Z/MZ)^×-torsor." The paper gives no proof of this sentence.

**Buzzard, Thm 2.1 (p. 5).** "X_D(U) is an algebraic stack over Z[1/M_U d]. Moreover, the
morphism X_D(U) → Spec(Z[1/M_U d]) is proper and smooth of relative dimension 1."

**Buzzard, Cor. 2.3 (p. 7).** "X_D(U) is the stack associated to a regular scheme, and the
morphism X_D(U) → Spec(Z[1/M_U d]) is projective."

**Milne 1986, Prop. 20.7 (p. 44).** "Let A be an abelian scheme of relative dimension g over S,
and let n_A be multiplication by n on A. Then n_A is flat, surjective, and finite, and its kernel
A_n is a finite flat group scheme over S of order n^{2g}. Moreover n_A (and therefore its kernel)
is étale if and only if n is not divisible by any of the characteristics of the residue fields of
S."

**Milne 1986, Cor. 20.2(a) (p. 43).** "Every morphism of abelian schemes carrying the zero
section into the zero section is a homomorphism." Its proof applies the rigidity lemma,
Prop. 20.1, which is stated for a connected base.

**Milne 1986, Rem. 8.4 (p. 14).** "If k is separably algebraically closed and n is not divisible
by its characteristic, then the theorem says that the kernel A_n(k) of n : A(k) → A(k) has n^{2g}
elements. As this is also true for all n′ dividing n, it follows that A_n(k) is a free
Z/nZ-module of rank 2g."

**Milne 1986, Cor. 2.2 (p. 3).** "Every morphism f : A → B of abelian varieties is the composite
of a homomorphism with a translation."

**Milne 1986, Prop. 17.5 (p. 37).** "Let λ be a polarization of the abelian variety A. (a) The
automorphism group of (A, λ) is finite. (b) For any integer n ≥ 3, an automorphism of (A, λ)
acting as the identity on A_n(k̄) is equal to the identity." The proof writes α - 1 = nβ using
(12.6), which needs n prime to the characteristic. It is applied here only at n = 3 over fields
of characteristic other than 3.

**Lan, Cor. 1.3.1.6** (text of the 2021 revision; the thesis omits "separated"). "Let A be an
abelian scheme, and let G be a separated group scheme of finite presentation over a base scheme
S. If h : A → G is a morphism over S taking the identity e_A of A to the identity e_G of G, then h
is a homomorphism."

**Lan, Prop. 1.3.2.15 and Def. 1.3.2.16 of the 2021 revision** (Prop. 1.3.2.18 and
Def. 1.3.2.20 of the thesis, which prints "relatively ample over A" in (3)). "Let λ be a
symmetric homomorphism from A to A^∨ over S. The following conditions are equivalent: 1. Over
each geometric point s̄ of S, λ_s̄ is of the form λ_L for some ample invertible sheaf L over A_s̄.
2. Locally for the étale topology, λ is of the form λ_L for some invertible sheaf L over A
relatively ample over S. 3. The invertible sheaf (Id_A, λ)^*P_A over A is relatively ample over
S." "A polarization λ of A is a symmetric homomorphism from A to A^∨ satisfying any of the
conditions in Proposition 1.3.2.15."

## Steps not in the prints

Notation: x ↦ x̄ is the canonical involution of B. Buzzard fixes t ∈ O with t² = -6 and sets
x^∗ = t^{-1} x̄ t. σ : (O/MO)^× → O is the fixed set-theoretic lift `Y3OrderMod.σ`.

### B-1. ι is injective over a nonempty base

Let I = ker ι, a two-sided ideal of O, and suppose x ∈ I is nonzero. Then x̄ = trd(x) - x lies
in O, so n := nrd(x) = x x̄ lies in I ∩ Z. Since B is a division algebra, n ≠ 0. Then
ι(|n|) = |n|_A = 0, but |n|_A is surjective (Milne 1986, Prop. 20.7) and A has relative dimension
2 over a nonempty S, a contradiction. So `FEC` agrees with Buzzard's definition over nonempty
bases; over the empty base every statement here is vacuous.

### B-2. O-linear automorphisms preserve Buzzard's polarization

Let k be algebraically closed of characteristic prime to 6, (A, ι) an FEC over k, and λ
Buzzard's principal polarization. Let θ be an automorphism of A with θ(0) = 0 that commutes with
ι(O). Then θ^∨ λ θ = λ.

- θ is a homomorphism (Milne 1986, Cor. 2.2), so θ^∨ is defined.
- λ′ := θ^∨ λ θ is a principal polarization: for ample L, θ^*L is ample and
  λ_{θ^*L} = θ^∨ λ_L θ (Milne 2008, §15); λ′ is an isomorphism because θ is.
- The Rosati involution of λ′ sends φ to λ′^{-1} φ^∨ λ′ = θ^{-1} Ros_λ(θ φ θ^{-1}) θ. For
  φ = ι(x), θ ι(x) θ^{-1} = ι(x), so Ros_{λ′}(ι(x)) = θ^{-1} ι(x^∗) θ = ι(x^∗).
- By Buzzard's uniqueness, λ′ = λ.

In characteristic p, Buzzard's uniqueness is printed with its proof sketched by reference to
[BC] III.1.5 and [B] §11 of his bibliography.

### B-3. Assembling `SerreRigidityLevel3'`

The hypotheses give an automorphism θ of A over S commuting with ι(O), a geometric point
s : Spec k → S with char k not 2 or 3, and P with `IsGenAt 3` at s and θ(P) = P.

- θ_s(0) = 0: ι(0) = 0 by additivity, and compatibility at a = 0 gives it.
- θ_s is a homomorphism (Milne 1986, Cor. 2.2) and an automorphism of (A_s, λ) (B-2).
- For a 3-torsion point x, clause 2 of `IsGenAt` gives x = ι(a)P, so θ(x) = ι(a)θ(P) = x. So
  θ_s is the identity on A_3(k).
- Milne 1986, Prop. 17.5(b), with n = 3 and char k ≠ 3, gives θ_s = id.

### B-4. Frames and generators, for `BuzzardFrameRepTorsor 5`

Buzzard defines a full level-M structure on A_T as an O-linear isomorphism of T-schemes
α : (O/MO)_T → A[M]_T, for M prime to 6 and invertible on T. The claim is that α ↦ α(1) is a
bijection onto the points P ∈ A[M](T) satisfying `IsGen M`.

- (O/MO)_T is a disjoint union of copies of T indexed by O/MO. An O-linear morphism satisfies
  α(x) = x·α(1) on each copy, so it is determined by α(1); conversely α_P(x) := x·P, defined copy
  by copy, is O-linear.
- A[M] is finite étale over T (Milne 1986, Prop. 20.7). If α_P is bijective on geometric fibres,
  it is a morphism between étale T-schemes, hence étale (Stacks 02GW), and it is universally
  injective, so it is an open immersion (Stacks 025G); being surjective, it is an isomorphism.
- On a geometric fibre both sides have M^4 elements (Milne 1986, Rem. 8.4, and O/MO ≅ (Z/M)^4),
  so bijective is equivalent to injective, which is clause 1 of `IsGenAt`; clause 2 then follows
  by counting.

The rest of Buzzard's sentence: A[M] is closed in A, being the base change of the zero section
along M_A, a closed immersion since A/S is separated; Z is closed in A[M], hence in A. "Étale
(O/MO)^×-torsor" is the statement that Z × G → Z ×_S Z, (z, g) ↦ (z, g·z), is an isomorphism (the
kernel-pair square), with Z → S finite étale and surjective. Precomposition α ↦ α ∘ r_δ, with
r_δ(x) = xδ, is a left action; on P = α(1) it is P ↦ α(δ) = δ·P = ι(σ(δ))P.

### B-5. The κ dictionary, for `BuzzardThm21Cor23V15'`

Buzzard fixes an isomorphism κ : O ⊗ R → M_2(R), R = ∏_{p∤6} Z_p, arbitrarily; V₁(5) is the
preimage of H = {(a b; 0 1)}, and a V₁(5)-structure is a section of the étale sheafification of
H\F_{A/S,5}.

Choice of κ: e5 has trd 6 and nrd -15, so e5² ≡ e5 mod 5 with trace ≡ 1; it is a rank-one
idempotent of O/5O ≅ M_2(F_5). Rank-one idempotents of M_2(F_5) are conjugate and GL_2(R) →
GL_2(Z/5) is surjective, so κ can be chosen with κ(e5) ≡ E₁₁ = diag(1, 0). Buzzard's results hold
for every κ.

Claim: V₁(5)-structures correspond to sections Q of the subscheme Y ⊆ A[5] cut out by e5·Q = 0
and Q ≠ 0 at every geometric point (open and closed in A[5], which is finite étale). This is
`V15`.

- The map: Q_α := α(E₂₂), E₂₂ = 1 - E₁₁. For δ ∈ H, E₂₂δ = E₂₂, so Q is constant on H-orbits;
  e5·Q = α(E₁₁E₂₂) = 0, 5Q = 0, and Q ≠ 0 at geometric points.
- Q determines the orbit: if α(E₂₂) = α′(E₂₂), then α^{-1}α′ is right multiplication by a
  locally constant unit δ with E₂₂δ = E₂₂, so δ has second row (0, 1), i.e. δ ∈ H locally.
- Surjectivity: α ↦ α(E₂₂) is a morphism of finite étale S-schemes Z → Y, surjective on
  geometric points. A[5](k) ≅ M_2(F_5) as a left module, being 4-dimensional (Milne 1986,
  Rem. 8.4) over a ring with a unique simple module, of dimension 2; Q corresponds to some
  y = (0 0; c d) with (c, d) ≠ 0, and x ↦ xg, for g with second row (c, d), sends E₂₂ to y. So
  every section of Y lifts to Z étale locally, and the sheafification is the functor of sections
  of Y.

Buzzard uses the same dictionary in his proof of Lemma 2.2, with Q = β((0 0; 0 1)).

### B-6. Buzzard's polarization in Lan's sense, for `ProjectiveFEC`

X has a closed immersion into P^N over Z[1/30], so X is noetherian and proper over Z[1/30], and
O_X(1) is ample (Stacks 01VT).

- Buzzard gives a principal polarization λ of A/X. He does not define a polarization over a
  base; it is read in Milne's sense (1986, §20, p. 46): at every geometric point λ_s̄ = φ_L with
  L ample. This is a convention, not a quoted statement. It is condition 1 of Lan's
  Prop. 1.3.2.15.
- Symmetry: λ - λ^∨ is a homomorphism of abelian schemes vanishing on every geometric fibre,
  since φ_L is symmetric (Lan, Lemma 1.3.2.16); A^∨ is an abelian scheme (Lan, Thm 1.3.2.6); by
  rigidity on the connected components of the noetherian X (Lan, Cor. 1.3.1.5, or Milne 1986,
  Prop. 20.1), λ - λ^∨ = 0.
- So λ is a polarization in Lan's sense, and condition 3 makes (Id, λ)^*P relatively ample over
  X.
- A → Spec Z[1/30] is proper. Stacks 0C4K makes L ⊗ f^*O_X(1)^{⊗a} ample relative to
  Spec Z[1/30] for a ≫ 0, and Stacks 0B45 ((6) ⇒ (2)), over the affine base, gives a closed
  immersion into some P^{N′} over Z[1/30].

## For the statement check

For each row: compare the Lean `def` with the quoted print at the page given, and for consequence
rows read the steps listed in the table.

1. `BuzzardThm21Cor23V15'`: Buzzard Thm 2.1 and Cor. 2.3 (pp. 5, 7) at V₁(5); B-1, B-5.
2. `BuzzardFrameRepTorsor 5`: Buzzard §1 after Def. 1.1; B-4.
3. `MilneProp207 3` and `MilneProp207 5`: Milne 1986, Prop. 20.7 (p. 44).
4. `GeomCard3`: Milne 1986, Rem. 8.4 (p. 14) and §20 (p. 42).
5. `ZeroPreservingIsHomLN`: Milne 1986, Cor. 20.2(a) (p. 43).
6. `SerreRigidityLevel3'`: Milne 1986, Cor. 2.2 (p. 3) and Prop. 17.5(b) (p. 37); Buzzard §1
   (p. 3); B-2, B-3.
7. `ProjectiveFEC`: Buzzard §1 (p. 3); Lan, as above; Stacks 01VT, 0C4K, 0B45; B-6.
