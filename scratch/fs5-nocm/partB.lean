namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin ZInQ ZInQ.JHeight PkgI3

/-! ## §B The statement -/

/-- **FS5 as stated by g0-fibresimple** (verbatim from `scratch/g0-fibresimple/FibreSimple.lean`,
`HSyn.G0Split.FibreComTrivial`, with the old `R1fpProps`; kept for reference: g0-fibresimple §2
shows that the old clause list does not pin `Φ`, so this form is not a consequence of the leaves).

**Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- **`R1fpProps` after qm-pin's full edit** (text of `scratch/qm-pin/QM-Leaves-full.patch`,
lines 63-70: the four old clauses, `R1famProps` and `R1univProps`). After the integration this is
`LeafQM.AV.R1fpProps`. -/
def R1fpPropsFull (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ ∧ R1univProps Y Φ

theorem r1fpPropsFull_iff (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    R1fpPropsFull Y Φ ↔ R1fpPropsU Y Φ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d, e⟩, f⟩, fun ⟨⟨a, b, c, d, e⟩, f⟩ => ⟨a, b, c, d, e, f⟩⟩

theorem R1fpPropsFull.old {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsFull Y Φ) : R1fpProps Y Φ := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **FS5 with the repaired QM clauses** (the statement this task proves): `FibreComTrivial`
verbatim, with `R1fpProps` read as after qm-pin's full edit (`R1fpPropsFull`). -/
def FibreComTrivialFull : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpPropsFull Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- The clause list of the leaf bundle `LeafQM.AV.R1R2fp` on one witness, with `R1fpProps` as
after qm-pin's full edit. -/
def R1R2fpFullProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left) : Prop :=
  R1fpPropsFull Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
    CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- **The leaf bundle `LeafQM.AV.R1R2fp` after qm-pin's full edit** (same text, `R1fpProps`
repaired). -/
def R1R2fpFull : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆

theorem R1R2fp_of_full (h : R1R2fpFull) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, h⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1.old, h⟩

/-- **FS5 for the leaf's own triple** (the restatement that qm-pin's `pointwise_of_witness_mor`
allows): for every witness `(Y, Φ, X, Ψ, fY, π₆)` of the repaired leaf bundle, the objects over
`J(u)`, `u ∉ 𝒞`, of the triple `(Y, Φ, π₆ ∘ fY)` have `End_𝒪 = ℤ`. Quantified over all witnesses
(not a `Classical.choice` of one), so it is a statement about the published data, not about a
choice. -/
def FibreComTrivialOwn : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (π₆.comp fY.left).val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)

/-! ## §C The named Props NoCM needs -/

/-- **NoCM input N1a (glue; G5-G6, rv-h-cm §7.2 "the CM order"): `End_𝒪(A)` is `ℤ` or an order in
an imaginary quadratic field.** For a QM pair `(A, ι)` over `ℚ̄`, either every element of the
centralizer `com ι = End_𝒪(A)` is an integer, or `com ι` is isomorphic to a subring `R` of the
ring of integers of an imaginary quadratic field `k`, of finite index (`conductor R ≠ 0`).
*Why true* (STANDARD): by Yu's dichotomy (leaf T27, `PkgI3.QMDichotomyYu`, in characteristic 0)
`End⁰(A) ≅ B` or `≅ M₂(k)` with `k` imaginary quadratic; the centralizer of `B` is `ℚ`, resp. the
centre `k` (FS4's argument, `centralizerOfMatrixEnd0_of_homFree`); `com ι = End(A) ∩ com⁰` is a
finitely generated (T6) subring of `ℚ`, resp. of `k`, of rank 1, resp. 2, and integral over `ℤ`,
hence `ℤ`, resp. an order of `k`. Glue from T27 and T6 (not compiled here). -/
def ComIntOrQuadOrder : Prop :=
  ∀ P : QMPair Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com P.q ≃+* R)

/-- **NoCM input N1b (leaf; "(Emb)" of rv-h-cm §7.2 and rv-nocm §1.2): the CM order has conductor
prime to 6.** If `End_𝒪(A) ≅ R` for an order `R` of an imaginary quadratic field `k`, then the
conductor of `R` is prime to `6 = disc B`.
*Published statement*: the CM points of `X₀(D, 1)` by `R` correspond to optimal embeddings
`R ↪ 𝒪` (Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5;
locators UNVERIFIED), and an order of conductor `f` embeds optimally in the maximal order of the
quaternion division algebra over `ℚ_p` only if `p ∤ f` and `p` does not split in `k` (Vignéras,
*Arithmétique des algèbres de quaternions*, LNM 800, Ch. II §3 / Ch. III §5, theorem numbers
UNVERIFIED; for `p ∤ f`: `k ∩ 𝒪_p = 𝒪_{k,p}` because `𝒪_p` is the set of integral elements).
A consequence of the published statements (only the conductor half is kept). -/
def CMConductorCoprime6 : Prop :=
  ∀ (P : QMPair Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      conductor R ≠ 0 → Nonempty (com P.q ≃+* R) → Nat.Coprime (conductor R) 6

/-- **NoCM input N2 (glue; the Kummer model of `X₆ → X₆/W ≅ P¹`, rv-h-cm §2.3-2.4,
`GlueRepo.PR.fibre_iff`).** On the leaf bundle's `X₆`, for a rational value `j₀ ∉ {0, −16/27}`
of `π₆` (so `t₀ = 1 + 27 j₀/16 ∉ {0, 1, ∞}`):
(i) every `ℚ̄`-point `x` over `j₀` has residue field `ℚ(x) = ℚ(a, b)` for any `a, b ∈ ℚ̄` with
`a² = −t₀`, `b² = 3(t₀ − 1)`;
(ii) the fibre over `j₀` has (at least) four distinct `ℚ̄`-points.
*Why true* (argued; Elkies, "Shimura curve computations", ANTS-III, LNCS 1423 (1998), the curve
`X*(6)` and its double covers (section number UNVERIFIED); the constants `c₀ = −1`, `c₁ = 3` are
derived in rv-h-cm §2.3 and checked against González–Rotger Thm 5.12 on all 24 rows of Elkies'
table, rv-nocm §1.3 Part B (VERIFIED there)): `ℚ(X₆) = ℚ(t)(y₁, y₂)`, `y₁² = −t`,
`y₂² = 3(t − 1)`, with `W ≅ (ℤ/2)²` acting by the sign changes; the affine model is smooth over
`t ∉ {0, 1, ∞}`, so the points over `t₀` are `(t₀, ±a, ±b)` (four, as `ab ≠ 0`) with residue field
generated by their coordinates. On an arbitrary witness of the bundle the statement is the same
statement, transported: with the repaired `R1fpProps` the witness `Y` maps to the genuine `Y₃`
with `Φ = Φ₃ ∘ g`, `π = π₃ ∘ g` (qm-pin `phi_part`, mobius-glue), `fY` is onto `X(ℚ̄)` (`X6Surj`),
`Ψ(fY y) = [forget (Φ y)]` (`X6Props`), and a residue field is the fixed field of the Galois
stabilizer of the point, which `Ψ` matches with the stabilizer of the pair (Galois-equivariance in
`X6Props`). Glue: geometry of an explicit curve plus the identification (not compiled). -/
def X6KummerFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)

