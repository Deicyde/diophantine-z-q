/-! ## g0-assemble2: fs5-nocm (scratch/fs5-nocm/partB, partD, partE, partG, partH, partI, verbatim except three
edits forced by pin-apply, which made Leaves.lean's `R1fpProps` the repaired six-clause list (=`R1fpPropsFull`,
same text): `R1fpPropsFull.old` is now `h` itself; in `fibreComTrivialFull_of_own` the conversions
`(r1fpPropsFull_iff _ _).1` to mobius-glue's `R1fpPropsU` are dropped, since Leaves.lean's
`pointwise_of_witness_mor` takes `R1fpProps`. The qm-pin copies of its FS5NoCM.lean are Leaves.lean's.) -/
noncomputable section

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin _root_.ZInQ ZInQ ZInQ.JHeight PkgI3

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
    (h : R1fpPropsFull Y Φ) : R1fpProps Y Φ := h

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
hence `ℤ`, resp. an order of `k`. Glue; **proved** from T27 and T6 in §G-§H
(`comIntOrQuadOrder_of_leaves`). -/
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
A consequence of the published statements (only the conductor half is kept). **Proved** in §I
from the leaf `CMOptimalEmbedding` (Shimura's description of CM points), `cmConductorCoprime6_of`. -/
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


/-! ## §D Arithmetic -/

/-- In a number field containing a square root `ι` of `−1`, the prime `2` is not inert:
`(1 + ι)² = 2ι ∈ (2)` but `(1 + ι)/2` is not integral (its fourth power is `−1/4`). -/
theorem two_not_prime_of_sqrt_neg_one {k : Type} [Field k] [NumberField k] (ι : k)
    (hι : ι ^ 2 = -1) : ¬ (Ideal.span {(2 : NumberField.RingOfIntegers k)}).IsPrime := by
  intro hP
  have hint : IsIntegral ℤ ι := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).add_of_left
        (by rw [Polynomial.degree_one, Polynomial.degree_X_pow]; norm_num)
    · simp [hι]
  let ιO : NumberField.RingOfIntegers k := ⟨ι, hint⟩
  have hsq : (1 + ιO) ^ 2 = 2 * ιO := by
    apply NumberField.RingOfIntegers.ext
    simp only [map_pow, map_add, map_one, map_mul, map_ofNat]
    change (1 + ι) ^ 2 = 2 * ι
    linear_combination hι
  have hmem : (1 + ιO) ^ 2 ∈ Ideal.span {(2 : NumberField.RingOfIntegers k)} := by
    rw [hsq]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hP.mem_of_pow_mem 2 hmem)
  have hck : (c : k) * 2 = 1 + ι := congrArg (fun z : NumberField.RingOfIntegers k => (z : k)) hc
  have h4 : (c : k) ^ 4 = algebraMap ℚ k (-1 / 4) := by
    have : (c : k) ^ 4 = -1 / 4 := by
      linear_combination (1 / 16 : k) * ((c * 2) ^ 3 + (c * 2) ^ 2 * (1 + ι) +
        (c * 2) * (1 + ι) ^ 2 + (1 + ι) ^ 3) * hck + (1 / 16 : k) * (ι ^ 2 + 4 * ι + 5) * hι
    rw [this]; simp
  have hI : IsIntegral ℤ (algebraMap ℚ k (-1 / 4)) := by
    rw [← h4]; exact (NumberField.RingOfIntegers.isIntegral_coe c).pow 4
  have hI' : IsIntegral ℤ (-1 / 4 : ℚ) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
      (algebraMap ℚ k).injective).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  have : (n : ℚ) * 4 = -1 := by
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]; norm_num
  have : n * 4 = -1 := by exact_mod_cast this
  omega

/-- `[ℚ(i) : ℚ] = 2` inside `ℚ̄`. -/
theorem finrank_adjoin_sqrt_neg_one (i : Qbar) (hi : i ^ 2 = -1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) = 2 := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])
  have hmp : minpoly ℚ i = Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ?_).symm
    · simp [hi]
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hint : IsIntegral ℚ i := Algebra.IsIntegral.isIntegral i
  rw [IntermediateField.adjoin.finrank hint, hmp, Polynomial.natDegree_X_pow_sub_C]

/-- `ℚ(i h₁, i h₂) = ℚ(i)` for rational `h₁ ≠ 0`, `h₂`. -/
theorem adjoin_pair_eq (i : Qbar) (h₁ h₂ : ℚ) (hh : h₁ ≠ 0) :
    IntermediateField.adjoin ℚ {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} =
      IntermediateField.adjoin ℚ {i} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl <;>
      exact mul_mem (IntermediateField.mem_adjoin_simple_self ℚ i)
        (IntermediateField.algebraMap_mem _ _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h0 : algebraMap ℚ Qbar h₁ ≠ 0 := by simpa using hh
    have hm : i * algebraMap ℚ Qbar h₁ ∈ IntermediateField.adjoin ℚ
        {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    have := mul_mem hm (IntermediateField.algebraMap_mem _ (h₁⁻¹))
    rwa [map_inv₀, mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

/-- The Elkies identities at `t(u)` (`GlueRepo.PR.t_eq`, `t_sub_one`), in `ℚ̄`: with `i² = −1`,
`(i H/G³)² = −t(u)` and `(i·540F/G³)² = 3(t(u) − 1)`, `t(u) = 1 + 27 J(u)/16`. -/
theorem elkies_sq (u : ℚ) (i : Qbar) (hi : i ^ 2 = -1) :
    (i * algebraMap ℚ Qbar (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        -algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) ∧
      (i * algebraMap ℚ Qbar (540 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        3 * (algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1) := by
  have ht : (1 + 27 * Jmap u / 16 : ℚ) = (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := by
    rw [div_pow, ← pow_mul]; exact GlueRepo.PR.t_eq u
  have ht1 : (1 + 27 * Jmap u / 16 : ℚ) - 1 =
      -3 * (180 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := GlueRepo.PR.t_sub_one u
  constructor
  · rw [ht, mul_pow, hi, map_pow]; ring
  · have e : algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1 =
        algebraMap ℚ Qbar ((1 + 27 * Jmap u / 16 : ℚ) - 1) := by rw [map_sub, map_one]
    rw [e, ht1, mul_pow, hi]
    simp only [map_mul, map_pow, map_neg, map_div₀, map_ofNat]
    ring


/-! ## §E NoCM on the leaf's own witness, and FS5 -/

/-- **NoCM on the leaf bundle's witness** (rv-h-cm §7.2 with the corrected count of rv-nocm §1.1).
Let `y` be a `ℚ̄`-point of the witness `Y` over `J(u)`, `u ∉ 𝒞`, with object `P`, and
`x = fY(y) ∈ X₆`. If `End_𝒪(P.A) ≅ R` were an order of an imaginary quadratic `k` (N1a), its
conductor is prime to 6 (N1b). The residue field of `x` is `ℚ(i)` (N2 (i) with the Elkies
identities), so R5 (`R5ptProps`) gives `2 = h(R)` if `b(k) = 0`, and `2 = 2h(R)` with
`k ↪ ℚ(i)` if `b(k) ≥ 1`; in the second case `k ≅ ℚ(i)`, where `2` ramifies, so `b(k) = 1`.
Either way `#CM(R) = 2^{b(k)} h(R) = 2` (R5fpCount). But the four points of the fibre over
`J(u)` (N2 (ii)) are pairwise distinct points of `X₆`, hence (`Ψ` bijective) four distinct
classes, and each is an `Aut(𝒪)`-twist of `P` (`R2X6Props`), hence CM by `R` (`com_twist`,
`comEquiv`): `#CM(R) ≥ 4`. Contradiction; so `End_𝒪(P.A) = ℤ`. -/
theorem nocm_on_witness (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hW : R1R2fpFullProps Y Φ X Ψ fY π₆)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar)
    (hP : Φ Qbar y = M3.mk P)
    (hv : (π₆.comp fY.left).val (K := Qbar) y.left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A) := by
  obtain ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ := hW
  have hx : Ψ (y ≫ fY) = Quotient.mk _ P.forget := hX.2.2.2.2.2 y P hP
  have hv' : π₆.val (K := Qbar) (y ≫ fY).left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u)) := by
    exact (ToP1.val_comp_right π₆ fY.left y.left).symm.trans hv
  rcases hA P.forget with hZ | ⟨k, _, _, _, hk2, R, hR, hc0, ⟨e⟩⟩
  · exact hZ
  exfalso
  have hcop : Nat.Coprime (conductor R) 6 := hB P.forget k hk2 R hR hc0 ⟨e⟩
  obtain ⟨hdeg, hemb⟩ := h5 k hk2 R hR hcop (y ≫ fY) P.forget hx ⟨e⟩
  -- the fibre over `J(u)` (N2) and its residue field `ℚ(i)`
  obtain ⟨hres, f, hf, hfv⟩ := hK Y Φ X Ψ fY π₆ ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ (Jmap u)
    (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos
  obtain ⟨ha, hb⟩ := elkies_sq u i hi
  have hresEq : residueImage (X := X.left) (y ≫ fY).left = IntermediateField.adjoin ℚ {i} := by
    rw [hres _ hv' _ _ ha hb]
    exact adjoin_pair_eq i _ _ (GlueRepo.PR.h₁_ne_zero u)
  have hfin : Module.finrank ℚ (residueImage (X := X.left) (y ≫ fY).left) = 2 := by
    rw [hresEq]; exact finrank_adjoin_sqrt_neg_one i hi
  rw [hfin] at hdeg
  -- four distinct classes with CM by `R`
  have hcount := hC k hk2 R hR hcop ⟨P.forget, ⟨e⟩⟩
  have hmemS : ∀ j : Fin 4, ∃ P' : QMPair Qbar, Quotient.mk _ P' = Ψ (f j) ∧
      Nonempty (com P'.q ≃+* R) := by
    intro j
    refine ⟨Quotient.out (Ψ (f j)), Quotient.out_eq _, ?_⟩
    have hQ : Ψ (f j) = Quotient.mk _ (Quotient.out (Ψ (f j))) := (Quotient.out_eq _).symm
    obtain ⟨α, ⟨g⟩⟩ := ((h2 (y ≫ fY) (f j) P.forget _ hx hQ).1).1 (hv'.trans (hfv j).symm)
    exact ⟨((comEquiv g).symm.trans (RingEquiv.subringCongr (com_twist P.forget.q α))).trans e⟩
  let F : Fin 4 → {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    fun j => ⟨Ψ (f j), hmemS j⟩
  have hFinj : Function.Injective F := fun a b hab =>
    hf (Ψ.injective (congrArg Subtype.val hab))
  -- `#CM(R) = 2`
  have hcard2 : Nat.card {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} = 2 := by
    rw [hcount]
    by_cases hb0 : inertCount6 k = 0
    · simp only [hb0, ↓reduceIte] at hdeg
      rw [hb0]; omega
    · simp only [hb0, ↓reduceIte] at hdeg
      have hh1 : Nat.card (CommRing.Pic R) = 1 := by omega
      obtain ⟨e'⟩ := hemb hb0
      have hik : i ∈ residueImage (X := X.left) (y ≫ fY).left := by
        rw [hresEq]; exact IntermediateField.mem_adjoin_simple_self ℚ i
      have : FiniteDimensional ℚ (residueImage (X := X.left) (y ≫ fY).left) :=
        Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
      have hsurj : Function.Surjective e'.toLinearMap := by
        rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hk2, hfin])]
        exact e'.toRingHom.injective
      obtain ⟨ι, hι⟩ := hsurj ⟨i, hik⟩
      have hι2 : ι ^ 2 = -1 := by
        apply e'.toRingHom.injective
        change e' (ι ^ 2) = e' (-1)
        rw [map_pow, map_neg, map_one]
        have : e' ι = ⟨i, hik⟩ := hι
        rw [this]
        apply Subtype.ext
        simp [hi]
      have h2n := two_not_prime_of_sqrt_neg_one ι hι2
      have hb1 : inertCount6 k = 1 := by
        have : inertCount6 k ≤ 1 := by
          unfold inertCount6
          simp only [h2n, ↓reduceIte]
          split_ifs <;> omega
        omega
      rw [hb1, hh1]; norm_num
  have hfinS : Finite {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; norm_num)
  have := Nat.card_le_card_of_injective F hFinj
  rw [hcard2, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **FS5 for the leaf's own triple, from NoCM's inputs.** -/
theorem fibreComTrivialOwn_of (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialOwn :=
  fun _ _ _ _ _ _ hW u hu y P hP hv => nocm_on_witness hA hB hK hC hW u hu y P hP hv

/-- **From the leaf's own triple to every triple** (qm-pin's `pointwise_of_witness_mor`, with
`MobiusGlue` and the CM objects of the bundle, `cm_objects_of_R1R2fp`). -/
theorem fibreComTrivialFull_of_own (hL : R1R2fpFull) (hM : MobiusGlue)
    (hO : FibreComTrivialOwn) : FibreComTrivialFull := by
  obtain ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩ := hL
  have hCM := cm_objects_of_R1R2fp (R1R2fp_of_full ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩)
  have h1 : R1fpProps Y₀ Φ₀ := hW.1
  have h2 : R2fpProps Y₀ Φ₀ (π₆.comp fY.left) := R2fpProps_of_X6 hW.2.2.1 hW.2.2.2.1
  have key := pointwise_of_witness_mor hM hCM h1 h2
    (fun t P => ∀ u : ℚ, u ∉ contactSet → t = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A))
    (fun t y P hP ht u hu htu => hO Y₀ Φ₀ X Ψ fY π₆ hW u hu y P hP (ht.trans htu))
  intro Y Φ π h1' h2' u hu y P hP hv
  exact key Y Φ π h1' h2' _ y P hP hv u hu rfl

/-- **FS5 with the repaired QM clauses, proved** from the leaf bundle (after qm-pin's full edit),
`MobiusGlue` (proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and T5), N1a, N1b, N2 and
the leaf R5fpCount. -/
theorem fibreComTrivialFull_of (hL : R1R2fpFull) (hM : MobiusGlue) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) :
    FibreComTrivialFull :=
  fibreComTrivialFull_of_own hL hM (fibreComTrivialOwn_of hA hB hK hC)

end FS5NoCM


/-! ## §G N1a split: the case `End⁰(A) ≅ B` proved from T6; the CM case named

The block from `B6_isUnit` to `qm_embeds_end0` is copied verbatim from
`scratch/g0-fibresimple/olean/Tail.lean` (lines 40-116, proved there). -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩

/-- The centre of `B = ℍ[ℚ, 2, -3]` is `ℚ`. -/
theorem B6_central_eq (z : ℍ[ℚ, 2, -3]) (hz : ∀ y : ℍ[ℚ, 2, -3], z * y = y * z) :
    z = algebraMap ℚ _ z.re := by
  have hi := hz ⟨0, 1, 0, 0⟩
  have hj := hz ⟨0, 0, 1, 0⟩
  have hi2 := congrArg QuaternionAlgebra.imJ hi
  have hi3 := congrArg QuaternionAlgebra.imK hi
  have hj1 := congrArg QuaternionAlgebra.imI hj
  have hj3 := congrArg QuaternionAlgebra.imK hj
  simp at hi2 hi3 hj1 hj3
  ext <;> simp <;> linarith

/-- `m ↦ 1 ⊗ m`, `End(A) → End⁰(A)`, is injective when `End(A)` is a free `ℤ`-module (T6). -/
theorem tmul_one_injective {k : Type} [Field k] {A : PkgI3.AbVar k}
    (hfree : Module.Free ℤ (PkgI3.AbVar.End A)) (m : PkgI3.AbVar.End A)
    (hm : (1 : ℚ) ⊗ₜ[ℤ] m = 0) : m = 0 := by
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
  rw [Submonoid.smul_def] at hs'
  exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')

/-- **N1a, case `End⁰(A) ≅ B` (proved from T6).** If `End⁰(A) ≅ ℍ[ℚ, 2, -3]` for an abelian
variety with a QM structure `q`, then every element of `com q = End_𝒪(A)` is an integer: `1 ⊗ φ`
commutes with the image of `B`, which is all of `End⁰(A)` (an injective map of 4-dimensional
`ℚ`-spaces), so it is a rational scalar `c` (`B6_central_eq`); `φ` is integral over `ℤ` (`End(A)`
is a finitely generated `ℤ`-module, T6), hence so is `c`, so `c ∈ ℤ`; and `m ↦ 1 ⊗ m` is
injective (T6). -/
theorem com_int_of_end0_quat (hHF : PkgI3.HomFreeFinite) {k : Type} [Field k]
    {A : PkgI3.AbVar k} (q : QMStr A) (e : PkgI3.AbVar.End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) :
    ∀ φ ∈ com q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End A) := by
  intro φ hφ
  obtain ⟨hfree, hfin, -, -⟩ := hHF k A A
  let L : ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A := (qmBasis q).liftHom
  have : Nontrivial (PkgI3.AbVar.End0 A) := e.toRingEquiv.nontrivial
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have := (B6_isUnit b hb0).map L
    rw [hb] at this
    exact not_isUnit_zero this
  have : FiniteDimensional ℚ (PkgI3.AbVar.End0 A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hLsurj : Function.Surjective L.toLinearMap := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, e.toLinearEquiv.finrank_eq,
        QuaternionAlgebra.finrank_eq_four])]
    exact hLinj
  set x : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] φ with hx
  have e1 : ∀ a b : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hcomm_g : ∀ a : LeafQM.O, Commute x ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hφ
    have h := hφ (q.iota a) ⟨a, rfl⟩
    show x * _ = _ * x
    rw [hx, ← e1, ← e1, h]
  have hcomm : ∀ y : PkgI3.AbVar.End0 A, x * y = y * x := by
    intro y
    obtain ⟨b, rfl⟩ := hLsurj y
    change Commute x ((qmBasis q).lift b)
    simp only [QuaternionAlgebra.Basis.lift]
    have h0 : Commute x (algebraMap ℚ (PkgI3.AbVar.End0 A) b.re) := (Algebra.commutes _ _).symm
    exact ((h0.add_right ((hcomm_g oi).smul_right _)).add_right
      ((hcomm_g oj).smul_right _)).add_right (((hcomm_g oi).mul_right (hcomm_g oj)).smul_right _)
  -- `x` is a rational scalar
  have hex : e x = algebraMap ℚ _ (e x).re := by
    apply B6_central_eq
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hcomm]
  set c : ℚ := (e x).re
  have hxc : x = algebraMap ℚ _ c := by
    apply e.injective; rw [hex, AlgEquiv.commutes]
  -- `c` is an integer
  have hint : IsIntegral ℤ φ := Algebra.IsIntegral.isIntegral φ
  obtain ⟨p, hpm, hp⟩ := hint
  have hpc : Polynomial.aeval c p = 0 := by
    have h1 : Polynomial.aeval x p = 0 := by
      have := Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A)
        φ p
      rw [← Polynomial.aeval_def] at hp
      rw [hp, map_zero] at this
      exact this
    rw [hxc, Polynomial.aeval_algebraMap_apply] at h1
    exact (algebraMap ℚ (PkgI3.AbVar.End0 A)).injective (h1.trans (map_zero _).symm)
  have hcint : IsIntegral ℤ c := ⟨p, hpm, by rw [← Polynomial.aeval_def]; exact hpc⟩
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
  refine ⟨n, sub_eq_zero.mp (tmul_one_injective hfree _ ?_)⟩
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] (n : PkgI3.AbVar.End A) = (n : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
  have h2 : algebraMap ℚ (PkgI3.AbVar.End0 A) c = (n : PkgI3.AbVar.End0 A) := by
    rw [← hn, show algebraMap ℤ ℚ n = (n : ℚ) from rfl, map_intCast]
  rw [TensorProduct.tmul_sub, ← hx, hxc, h1, h2, sub_self]


/-- **N1a-CM (glue; G6, the CM case of Yu's dichotomy): the CM order.** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for a QM abelian surface `(A, ι)` over `ℚ̄`, then
`com ι = End_𝒪(A)` is isomorphic to a subring of finite index of `𝒪_k`, `k` imaginary quadratic.
*Why true* (STANDARD linear algebra; Shimura): `B ⊗ ℚ(√d) ≅ M₂(ℚ(√d))` (`B ⊗ k` is central simple
of `k`-dimension 4 and maps to `M₂(k)`), so the centralizer of `B` in `End⁰(A)` is the centre
`k = ℚ(√d)`; `com ι = End(A) ∩ k` is a finitely generated `ℤ`-module (T6) of integral elements
(`End(A)` is finite over `ℤ`), containing `ℤ` and a non-integer `n√d` (FS4,
`centralizerOfMatrixEnd0_of_homFree`), hence a subring of finite index of `𝒪_k`. Glue;
**proved** from T6 in §H (`comOfMatrixEnd0_of_homFree`). -/
def ComOfMatrixEnd0 : Prop :=
  ∀ (A : AbVar Qbar) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com q ≃+* R)

/-- **N1a from T27 (Yu), T6 and N1a-CM.** -/
theorem comIntOrQuadOrder_of (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite)
    (hCM : ComOfMatrixEnd0) : ComIntOrQuadOrder := by
  intro P
  rcases PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q) with
    he | ⟨d, hd, hM⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (com_int_of_end0_quat t6 P.q e)
  · exact Or.inr (hCM P.A P.q d hd hM)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 (in `TextbookLeaves`), N1b, and the glue `MobiusGlue`, N1a-CM, N2. -/
theorem fibreComTrivialFull_of_leaves (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hCM : ComOfMatrixEnd0)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of t27 t6 hCM) hB hK hC

end FS5NoCM


/-! ## §H N1a-CM proved from T6 (`End_𝒪(A)` is an order of `ℚ(√d)` when `End⁰(A) ≅ M₂(ℚ(√d))`) -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

section LinAlg

variable {K : Type} [Field K]

local notation "M2" => Matrix (Fin 2) (Fin 2) K

theorem quat_comm_I (I J : M2) (hI : I * I = (2 : K) • 1) (hJI : J * I = -(I * J))
    (a b c d : K) :
    I * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * I =
      (2 * c) • (I * J) + (4 * d) • J := by
  have r1 : I * (I * J) = (2 : K) • J := by rw [← mul_assoc, hI, smul_mul_assoc, one_mul]
  have r2 : (I * J) * I = -((2 : K) • J) := by
    rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hI, smul_mul_assoc, one_mul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hI, r1, r2, hJI]
  module

theorem quat_comm_J (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (a b c d : K) :
    J * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * J =
      (-2 * b) • (I * J) + (6 * d) • I := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have r4 : J * (I * J) = (3 : K) • I := by
    rw [← mul_assoc, hJI, neg_mul, mul_assoc, hJ, mul_smul_comm, mul_one, neg_smul]; module
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJ, r3, r4, hJI]
  module

/-- **A matrix commuting with `I` and `J` is scalar**, if `I² = 2`, `J² = −3`, `JI = −IJ` in
`M₂(K)`, `2, 3 ≠ 0` in `K` (then `1, I, J, IJ` is a `K`-basis of `M₂(K)`). -/
theorem commute_quat_scalar (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (Y : M2) (hYI : I * Y = Y * I) (hYJ : J * Y = Y * J) : ∃ a : K, Y = a • (1 : M2) := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have hinj : Function.Injective (fun x : K => x • (1 : M2)) := smul_left_injective K one_ne_zero
  have hIns : ∀ s : K, I ≠ s • (1 : M2) := by
    intro s hs
    have hc : I * J = J * I := by rw [hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hJI] at hc
    have h0 : I * J = 0 := by
      have : (2 : K) • (I * J) = 0 := by
        rw [two_smul]; nth_rewrite 2 [hc]; exact add_neg_cancel _
      exact (smul_eq_zero.mp this).resolve_left h2
    have hI0 : I = 0 := by
      have := r3; rw [h0, zero_mul] at this
      exact (smul_eq_zero.mp this.symm).resolve_left (neg_ne_zero.mpr h3)
    apply h2; apply hinj; simp only; rw [← hI, hI0, mul_zero, zero_smul]
  -- `(2c)•IJ + (4d)•J = 0 → c = 0 ∧ d = 0`
  have kill : ∀ c d : K, (2 * c) • (I * J) + (4 * d) • J = 0 → c = 0 ∧ d = 0 := by
    intro c d h
    have h' := congrArg (· * J) h
    simp only [add_mul, smul_mul_assoc, r3, hJ, zero_mul] at h'
    have hc : c = 0 := by
      by_contra hc
      have h6 : (-6 * c : K) ≠ 0 := mul_ne_zero (by
        rw [show (-6 : K) = -(2 * 3) by norm_num]; exact neg_ne_zero.mpr (mul_ne_zero h2 h3)) hc
      apply hIns ((-6 * c)⁻¹ * (12 * d))
      have : (-6 * c) • I = (12 * d) • (1 : M2) := by
        have e : (-6 * c) • I - (12 * d) • (1 : M2) =
            (2 * c) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by module
        rw [h'] at e; exact sub_eq_zero.mp e
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ h6, one_smul]
    subst hc
    refine ⟨rfl, ?_⟩
    have : (-12 * d) • (1 : M2) = 0 := by
      have e : (-12 * d) • (1 : M2) = ((2 : K) * 0) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by
        module
      rw [e]; exact h'
    have h12 : (-12 * d : K) = 0 := hinj (by simpa using this)
    have : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
    have := mul_eq_zero.mp (show (-12 : K) * d = 0 from h12)
    rcases this with h | h
    · exact absurd (neg_eq_zero.mp h) ‹(12 : K) ≠ 0›
    · exact h
  let v : Fin 4 → M2 := ![1, I, J, I * J]
  have hsum : ∀ g : Fin 4 → K, ∑ i, g i • v i = g 0 • 1 + g 1 • I + g 2 • J + g 3 • (I * J) := by
    intro g; simp [Fin.sum_univ_four, v]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hsum] at hg
    have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
    rw [hg, mul_zero, zero_mul, sub_zero] at hI0
    obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
    rw [hg2, hg3, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hIns (-(g 1)⁻¹ * g 0)
      have hb : g 1 • I = -(g 0 • (1 : M2)) := eq_neg_of_add_eq_zero_right hg
      calc I = (g 1)⁻¹ • (g 1 • I) := by rw [smul_smul, inv_mul_cancel₀ hg1, one_smul]
        _ = (-(g 1)⁻¹ * g 0) • 1 := by rw [hb]; module
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := hinj (by simpa using hg)
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
  have hY : Y ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hY
  rw [hsum] at hg
  subst hg
  have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYI, sub_self] at hI0
  obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
  have hJ0 := quat_comm_J I J hI hJ hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYJ, sub_self, hg3, mul_zero, zero_smul, add_zero] at hJ0
  have hg1 : g 1 = 0 := by
    have h' := congrArg (· * J) hJ0
    simp only [smul_mul_assoc, r3, zero_mul, smul_smul] at h'
    by_contra hg1
    apply hIns 0
    have hne : (-2 * g 1 * -3 : K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hg1) (neg_ne_zero.mpr h3)
    rw [zero_smul]
    exact (smul_eq_zero.mp h'.symm).resolve_left hne
  refine ⟨g 0, ?_⟩
  rw [hg1, hg2, hg3]; simp

section AdjRoot

open Polynomial

variable (d : ℚ)

/-- `X² − d` is irreducible over `ℚ` for `d < 0`. -/
theorem irred_sq_sub (hd : d < 0) : Irreducible (X ^ 2 - C d : ℚ[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])

theorem monic_sq_sub : (X ^ 2 - C d : ℚ[X]).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem finrank_adjRoot : Module.finrank ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_sq_sub d)).finrank]
  exact natDegree_X_pow_sub_C

theorem finite_adjRoot : Module.Finite ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
  (AdjoinRoot.powerBasis' (monic_sq_sub d)).finite

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- For `d < 0`, `ℚ(√d)` (as `AdjoinRoot`, with its field structure) is a totally complex
quadratic number field. -/
theorem adjRoot_numberField (hd : d < 0) :
    letI : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
    NumberField (AdjoinRoot (X ^ 2 - C d : ℚ[X])) ∧
      NumberField.IsTotallyComplex (AdjoinRoot (X ^ 2 - C d : ℚ[X])) := by
  let : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
  have : CharZero (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))).injective
  have := finite_adjRoot d
  refine ⟨{}, ⟨fun v => ?_⟩⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  rintro ⟨φ, hφ, -⟩
  have h2 : (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := by
    have := congrArg hφ.embedding (root_sq d)
    rwa [map_pow, eq_ratCast (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))) d,
      map_ratCast] at this
  have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])))]

end AdjRoot


end LinAlg

local notation "Kd[" d "]" => AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)

/-- `root` is not rational: `x + y·√d = 0` with `x, y ∈ ℚ` forces `x = y = 0` (`d < 0`). -/
theorem root_lin_indep (d : ℚ) (hd : d < 0) (x y : ℚ)
    (h : algebraMap ℚ Kd[d] x + algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = 0) : x = 0 ∧ y = 0 := by
  have : Nontrivial Kd[d] := AdjoinRoot.nontrivial _ (by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  have hinj := (algebraMap ℚ Kd[d]).injective
  by_cases hy : y = 0
  · subst hy
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨hinj (h.trans (map_zero _).symm), rfl⟩
  · exfalso
    have h1 : algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = -algebraMap ℚ Kd[d] x := by
      linear_combination h
    have h2 : (algebraMap ℚ Kd[d] y * AdjoinRoot.root _) ^ 2 = (algebraMap ℚ Kd[d] x) ^ 2 := by
      rw [h1]; ring
    rw [mul_pow, root_sq, ← map_pow, ← map_mul, ← map_pow] at h2
    have h3 := hinj h2
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]

/-- The same with integer coefficients. -/
theorem root_lin_indep_int (d : ℚ) (hd : d < 0) (a c : ℤ)
    (h : a • (1 : Kd[d]) + c • AdjoinRoot.root _ = 0) : a = 0 ∧ c = 0 := by
  have := root_lin_indep d hd a c (by
    rw [map_intCast, map_intCast]; rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at h; exact h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- **N1a-CM proved from T6.** If `End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, then `End_𝒪(A)` is isomorphic
to a subring of finite index of `𝒪_k`, `k = ℚ(√d)`: `1 ⊗ φ` (`φ ∈ End_𝒪(A)`) commutes with the
images `I, J` of `i, j ∈ 𝒪` (`I² = 2`, `J² = −3`, `JI = −IJ`), hence is a scalar
(`commute_quat_scalar`); `φ ↦` that scalar is an injective ring map `ψ` (T6); its image `R`
consists of integral elements (T6: `End(A)` is finite over `ℤ`), and contains `1` and `s√d`,
`s ≠ 0` (FS4's localization step), so it has rank 2 in `𝒪_k` and finite index. -/
theorem comOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) : ComOfMatrixEnd0 := by
  intro A q d hd hM
  obtain ⟨e⟩ := hM
  letI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) :=
    ⟨irred_sq_sub d hd⟩
  obtain ⟨hNF, hTC⟩ := adjRoot_numberField d hd
  obtain ⟨hfree, hfin, -, -⟩ := hHF Qbar A A
  let g : LeafQM.O →+* AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] AbVar.End A).toRingHom.comp
      q.iota
  have e1 : ∀ a b : AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hI : e (g oi) * e (g oi) = (2 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oi_mul_oi, map_ofNat, map_ofNat, Algebra.smul_def, mul_one,
      map_ofNat]
  have hJ : e (g oj) * e (g oj) = (-3 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oj_mul_oj, map_neg, map_neg, map_ofNat, map_ofNat,
      Algebra.smul_def, mul_one, map_neg, map_ofNat]
  have hJI : e (g oj) * e (g oi) = -(e (g oi) * e (g oj)) := by
    rw [← map_mul, ← map_mul, oj_mul_oi, map_neg, map_neg, map_mul, map_mul]
  have hcommφ : ∀ φ ∈ com q, ∀ a : LeafQM.O,
      ((1 : ℚ) ⊗ₜ[ℤ] φ) * g a = g a * ((1 : ℚ) ⊗ₜ[ℤ] φ) := by
    intro φ hφ a
    rw [com, Subring.mem_centralizer_iff] at hφ
    show ((1 : ℚ) ⊗ₜ[ℤ] φ) * ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) = ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) * _
    rw [← e1, ← e1, hφ _ ⟨a, rfl⟩]
  have hsc : ∀ φ ∈ com q, e ((1 : ℚ) ⊗ₜ[ℤ] φ) =
      (e ((1 : ℚ) ⊗ₜ[ℤ] φ) 0 0) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    intro φ hφ
    obtain ⟨a, ha⟩ := commute_quat_scalar (e (g oi)) (e (g oj)) hI hJ hJI two_ne_zero
      three_ne_zero (e ((1 : ℚ) ⊗ₜ[ℤ] φ))
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oi])
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oj])
    rw [ha]; simp
  -- the scalar map `ψ : End_𝒪(A) → ℚ(√d)`
  let ψ : com q →+* Kd[d] :=
    { toFun := fun φ => e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) 0 0
      map_one' := by
        simp only [OneMemClass.coe_one]
        rw [← Algebra.TensorProduct.one_def, map_one, Matrix.one_apply_eq]
      map_mul' := fun φ φ' => by
        simp only [MulMemClass.coe_mul]
        rw [e1, map_mul, hsc φ φ.2, hsc φ' φ'.2, smul_mul_smul_comm, one_mul]
        simp
      map_zero' := by simp
      map_add' := fun φ φ' => by simp [TensorProduct.tmul_add] }
  have hψ : ∀ φ : com q, e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = ψ φ • 1 := fun φ => hsc φ φ.2
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ0
    have h0 : e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = 0 := by rw [hψ, hφ0, zero_smul]
    rw [← map_zero e] at h0
    exact Subtype.ext (tmul_one_injective hfree _ (e.injective h0))
  -- an element `s√d` in the image (FS4's localization step)
  set c' : AbVar.End0 A :=
    e.symm ((AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) •
      (1 : Matrix (Fin 2) (Fin 2) Kd[d])) with hc'
  have hcen : ∀ x : AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  let f := TensorProduct.mk ℤ ℚ (AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ₀, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ₀ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hφ₀ : φ₀ ∈ com q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ₀ - φ₀ * q.iota a) = 0 := by
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (tmul_one_injective hfree _ key)
  have hw : ψ ⟨φ₀, hφ₀⟩ = (s : ℤ) • AdjoinRoot.root _ := by
    change e ((1 : ℚ) ⊗ₜ[ℤ] φ₀) 0 0 = _
    rw [hs', map_zsmul, hc', e.apply_symm_apply]
    simp
  -- the order `R = ψ(End_𝒪(A))`
  have hRint : ψ.range ≤ (integralClosure ℤ Kd[d]).toSubring := by
    rintro _ ⟨φ, rfl⟩
    have h1 : IsIntegral ℤ (φ : AbVar.End A) := Algebra.IsIntegral.isIntegral _
    have h2 : IsIntegral ℤ φ :=
      (isIntegral_algHom_iff ((com q).subtype.toIntAlgHom) Subtype.val_injective).mp h1
    exact h2.map ψ.toIntAlgHom
  refine ⟨Kd[d], inferInstance, hNF, hTC, finrank_adjRoot d, ψ.range, hRint, ?_,
    ⟨RingEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b h => hψinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩⟩⟩
  -- finite index: `R ∩ 𝒪_k` has rank 2 (it contains `1` and `s√d`)
  let fO : NumberField.RingOfIntegers Kd[d] →+ Kd[d] :=
    (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d]).toAddMonoidHom
  have hrange : (integralClosure ℤ Kd[d]).toSubring.toAddSubgroup =
      (⊤ : AddSubgroup (NumberField.RingOfIntegers Kd[d])).map fO := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩; exact y.2
  unfold LeafQM.AV.conductor
  suffices hsuff : (ψ.range.toAddSubgroup.comap fO).index ≠ 0 by
    convert hsuff using 1
    rw [← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, ← hrange]
    rfl
  let N' : Submodule ℤ (NumberField.RingOfIntegers Kd[d]) :=
    (ψ.range.toAddSubgroup.comap fO).toIntSubmodule
  have hw' : IsIntegral ℤ ((s : ℤ) •
      AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) := by
    rw [← hw]; exact hRint ⟨_, rfl⟩
  let w' : NumberField.RingOfIntegers Kd[d] := ⟨_, hw'⟩
  have h1N : (1 : NumberField.RingOfIntegers Kd[d]) ∈ N' := by
    show fO 1 ∈ ψ.range
    rw [show fO 1 = 1 from map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])]
    exact ψ.range.one_mem
  have hwN : w' ∈ N' := ⟨⟨φ₀, hφ₀⟩, hw⟩
  have hv : LinearIndependent ℤ ![(⟨1, h1N⟩ : N'), ⟨w', hwN⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hK := congrArg (fun z : N' => fO (z : NumberField.RingOfIntegers Kd[d])) hab
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul, Submodule.coe_zero,
      map_zero] at hK
    have e1' : fO 1 = 1 := map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])
    have e2' : fO w' = (s : ℤ) •
        AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) := rfl
    rw [e1', e2', smul_smul] at hK
    obtain ⟨ha, hbs⟩ := root_lin_indep_int d hd _ _ hK
    exact ⟨ha, (mul_eq_zero.mp hbs).resolve_right hs0⟩
  have hfr : Module.finrank ℤ N' = Module.finrank ℤ (NumberField.RingOfIntegers Kd[d]) := by
    apply le_antisymm (Submodule.finrank_le N')
    rw [NumberField.RingOfIntegers.rank, finrank_adjRoot]
    simpa using hv.fintype_card_le_finrank
  have := Submodule.finiteQuotientOfFreeOfRankEq N' hfr
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

/-- **N1a proved from the leaves T27 (Yu) and T6.** -/
theorem comIntOrQuadOrder_of_leaves (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) :
    ComIntOrQuadOrder :=
  comIntOrQuadOrder_of t27 t6 (comOfMatrixEnd0_of_homFree t6)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 and N1b (leaves), and `MobiusGlue` and N2 (glue). -/
theorem fibreComTrivialFull_of_leaves' (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of_leaves t27 t6) hB hK hC

end FS5NoCM


/-! ## §I N1b reduced to Shimura's description of CM points (`CMOptimalEmbedding`)

`R = φ⁻¹(𝒪)` for an embedding `φ : k → B` forces `(f(R), 6) = 1`: N5's `𝒪` is the set of
integral elements of `B_p` for `p = 2, 3` (finite checks `check2`, `check3` modulo `p²`). -/

namespace FS5NoCM


set_option maxRecDepth 100000 in
theorem check3 : ∀ a b c d : ZMod 9,
    a ^ 2 + a * c + c ^ 2 + 7 * (b ^ 2 + b * d + d ^ 2) = 0 →
      3 ∣ a.val ∧ 3 ∣ b.val ∧ 3 ∣ c.val ∧ 3 ∣ d.val := by decide

set_option maxRecDepth 100000 in
theorem check2 : ∀ a b c d : ZMod 4,
    a ^ 2 + a * c + c ^ 2 + 2 * (b ^ 2 + b * d + d ^ 2) = 0 →
      2 ∣ a.val ∧ 2 ∣ b.val ∧ 2 ∣ c.val ∧ 2 ∣ d.val := by decide

open LeafQM

/-- The reduced norm of `ofInt n`, as an integer quadratic form. -/
def Qf (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

theorem nrd_ofInt (n : Fin 4 → ℤ) : ofInt n * star (ofInt n) = algebraMap ℚ B (Qf n : ℚ) := by
  ext <;> simp [ofInt, Qf, QuaternionAlgebra.algebraMap_eq] <;> ring

/-- `p² ∣ nrd(ofInt n)` forces `p ∣ n` for `p = 2, 3` (`𝒪_p` is the set of integral elements of
the ramified `B_p`; a finite check modulo `p²`). -/
theorem dvd_of_sq_dvd_Qf (p : ℕ) (hp : p = 2 ∨ p = 3) (n : Fin 4 → ℤ) (h : (p : ℤ) ^ 2 ∣ Qf n) :
    ∀ i, (p : ℤ) ∣ n i := by
  rcases hp with rfl | rfl
  · have h0 : ((Qf n : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 4) ^ 2 + (n 0 : ZMod 4) * (n 2 : ZMod 4) + (n 2 : ZMod 4) ^ 2 +
        2 * ((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) + (n 3 : ZMod 4) ^ 2) = 0 := by
      have h4 : (4 : ZMod 4) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) +
        (n 3 : ZMod 4) ^ 2)) * h4
    obtain ⟨a, b, c, d⟩ := check2 _ _ _ _ e
    have key : ∀ m : ℤ, 2 ∣ ((m : ZMod 4)).val → (2 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 4)).val : ℤ) = m % 4 := ZMod.val_intCast m
      have h2 : (2 : ℤ) ∣ m % 4 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d
  · have h0 : ((Qf n : ℤ) : ZMod 9) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 9) ^ 2 + (n 0 : ZMod 9) * (n 2 : ZMod 9) + (n 2 : ZMod 9) ^ 2 +
        7 * ((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) + (n 3 : ZMod 9) ^ 2) = 0 := by
      have h9 : (9 : ZMod 9) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) +
        (n 3 : ZMod 9) ^ 2)) * h9
    obtain ⟨a, b, c, d⟩ := check3 _ _ _ _ e
    have key : ∀ m : ℤ, 3 ∣ ((m : ZMod 9)).val → (3 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 9)).val : ℤ) = m % 9 := ZMod.val_intCast m
      have h2 : (3 : ℤ) ∣ m % 9 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d

theorem ofInt_nsmul (p : ℕ) (w : Fin 4 → ℤ) : ofInt (fun i => (p : ℤ) * w i) = (p : ℚ) • ofInt w := by
  ext <;> simp [ofInt] <;> ring

theorem mul_star_comm (x : B) : star x * x = x * star x := by
  ext <;> simp <;> ring

/-- **Optimal embeddings have conductor prime to 6** (the algebra behind N1b). If `R ⊆ 𝒪_k` is
the preimage `φ⁻¹(𝒪)` of N5's maximal order under an embedding `φ : k → B` and has finite index,
then `p ∤ [𝒪_k : R]` for `p = 2, 3`: otherwise some `y ∈ 𝒪_k ∖ R` has `p y ∈ R`, so
`φ(p y) = ofInt v ∈ 𝒪`; `nrd φ(y) ∈ ℤ` (its minimal polynomial is that of `y`, integral), so
`p² ∣ nrd(ofInt v)`, hence `p ∣ v` (`dvd_of_sq_dvd_Qf`) and `φ(y) ∈ 𝒪`, i.e. `y ∈ R`. -/
theorem not_dvd_conductor_of_optimal {k : Type} [Field k] [NumberField k]
    (φ : k →ₐ[ℚ] B) (R : Subring k) (hR : R = O.comap φ.toRingHom)
    (hc0 : AV.conductor R ≠ 0) (p : ℕ) (hp : p = 2 ∨ p = 3) : ¬ p ∣ AV.conductor R := by
  intro hdvd
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  set L := (integralClosure ℤ k).toSubring.toAddSubgroup with hL
  set H := R.toAddSubgroup.addSubgroupOf L with hH
  have hidx : H.index = AV.conductor R := rfl
  have hcard : Nat.card (↥L ⧸ H) = AV.conductor R := by rw [← AddSubgroup.index_eq_card, hidx]
  have hfin : Finite (↥L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hc0)
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥L ⧸ H) p (by rw [hcard]; exact hdvd)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hyR : (y : k) ∉ R := by
    intro hy
    have h0 : ((y : ↥L) : ↥L ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    rw [h0, addOrderOf_zero] at hg
    exact hpp.one_lt.ne hg
  have hpy : p • (y : k) ∈ R := by
    have h1 : p • ((y : ↥L) : ↥L ⧸ H) = 0 := by rw [← hg]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h1
    exact h1
  have hyint : IsIntegral ℤ (y : k) := y.2
  have hynq : (y : k) ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq⟩
    have hqi : IsIntegral ℤ q :=
      (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
        (algebraMap ℚ k).injective).mp (by rw [← hq] at hyint; exact hyint)
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
    apply hyR
    rw [← hq, ← hm]
    have : algebraMap ℚ k (algebraMap ℤ ℚ m) = (m : k) := by simp
    rw [this]; exact intCast_mem R m
  set x : B := φ (y : k) with hx
  have hxint : IsIntegral ℤ x := hyint.map (φ.restrictScalars ℤ)
  have hxnq : x ∉ Set.range (algebraMap ℚ B) := by
    rintro ⟨q, hq⟩
    apply hynq
    refine ⟨q, φ.injective ?_⟩
    change φ (algebraMap ℚ k q) = φ y
    rw [AlgHom.commutes]; exact hq
  -- the minimal polynomial of `x` is `X² − t X + n`, with integer coefficients
  set t : ℚ := 2 * x.re with ht
  set n : ℚ := (x * star x).re with hn
  have hxx : x * star x = algebraMap ℚ B n := by
    rw [hn, QuaternionAlgebra.mul_star_eq_coe]; rfl
  have hsum : x + star x = algebraMap ℚ B t := by
    rw [QuaternionAlgebra.self_add_star', ht]; simp
  have hP : Polynomial.aeval x (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n) = 0 := by
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      map_one, one_mul, map_neg]
    rw [← hsum, ← hxx, ← mul_star_comm]
    noncomm_ring
  have hPm : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_quadratic one_ne_zero]
  have hPd : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  have hxintQ : IsIntegral ℚ x := hxint.tower_top
  have hmin : minpoly ℚ x = Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxintQ) hPm
      (minpoly.dvd ℚ x hP) ?_).symm
    rw [hPd]
    exact (minpoly.two_le_natDegree_iff hxintQ).mpr hxnq
  have hmin' : minpoly ℚ x = (minpoly ℤ (y : k)).map (algebraMap ℤ ℚ) := by
    rw [hx, minpoly.algHom_eq φ φ.injective]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hyint
  obtain ⟨N, hN⟩ : ∃ N : ℤ, (N : ℚ) = n := by
    refine ⟨(minpoly ℤ (y : k)).coeff 0, ?_⟩
    have := congrArg (fun P : Polynomial ℚ => P.coeff 0) (hmin.symm.trans hmin')
    simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at this
    simpa using this.symm
  -- `φ(p y) = p x ∈ 𝒪`, so `p² ∣ nrd`, so `x ∈ 𝒪`
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hz : (p : ℚ) • x ∈ O := by
    have h1 : p • (y : k) ∈ O.comap φ.toRingHom := hR ▸ hpy
    have h2 : φ (p • (y : k)) ∈ O := h1
    rwa [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h2
  obtain ⟨v, hv⟩ := hz
  have hQ : (Qf v : ℚ) = (p : ℚ) ^ 2 * N := by
    have h1 := nrd_ofInt v
    rw [← hv, star_smul, smul_mul_smul_comm, hxx, Algebra.smul_def, ← map_mul] at h1
    rw [hN, ← (algebraMap ℚ B).injective h1, star_trivial]; ring
  have hQ' : (p : ℤ) ^ 2 ∣ Qf v := ⟨N, by exact_mod_cast hQ⟩
  choose w hw using dvd_of_sq_dvd_Qf p hp v hQ'
  have hvw : v = fun i => (p : ℤ) * w i := funext hw
  have hxw : x = ofInt w := by
    apply smul_right_injective B hp0
    simp only
    rw [hv, hvw, ofInt_nsmul]
  apply hyR
  rw [hR]
  exact ⟨w, hxw⟩

/-- **N1b′ (leaf; Shimura's description of CM points on `X₀(6,1)`).** If `End_𝒪(A) ≅ R` for an order
`R` of an imaginary quadratic `k`, then `R` is the preimage `φ⁻¹(𝒪)` of N5's maximal order under
some `ℚ`-embedding `φ : k → B`.
*Published statement*: for `(A, ι)` over `ℂ` with CM, `A = ℂ²/𝒪 v_τ` and `End_𝒪(A) ≅ φ_τ(k) ∩ 𝒪`,
where `φ_τ : k → B` is the embedding whose image fixes `τ ∈ ℍ` (Shimura, Ann. of Math. 85 (1967);
Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5; locators
UNVERIFIED); in characteristic 0 the same holds over `ℚ̄`. Transport to the given `k ⊇ R`: an
isomorphism `R ≅ φ_τ(k) ∩ 𝒪` extends to the fraction fields `k ≅ k_τ` (`R` has rank 2), and the
composite embedding pulls `𝒪` back to `R`. A consequence of the published statement (up to
replacing `B` by `B^op ≅ B`, which preserves `𝒪`). -/
def CMOptimalEmbedding : Prop :=
  ∀ (P : AV.QMPair AV.Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      AV.conductor R ≠ 0 → Nonempty (AV.com P.q ≃+* R) →
        ∃ φ : k →ₐ[ℚ] B, R = O.comap φ.toRingHom

theorem cmConductorCoprime6_of (h : CMOptimalEmbedding) : CMConductorCoprime6 := by
  intro P k _ _ _ hk2 R hR hc0 he
  obtain ⟨φ, hφ⟩ := h P k hk2 R hR hc0 he
  have h2 := not_dvd_conductor_of_optimal φ R hφ hc0 2 (Or.inl rfl)
  have h3 := not_dvd_conductor_of_optimal φ R hφ hc0 3 (Or.inr rfl)
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  exact ⟨(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)),
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))⟩


/-- **FS5 with the repaired clauses, from leaves and named glue**: the bundle, R5fpCount, T27, T6,
N1b′ `CMOptimalEmbedding` (leaves), and `MobiusGlue`, N2 (glue). -/
theorem fibreComTrivialFull_of_leaves'' (hL : R1R2fpFull) (hM : LeafQM.AV.Pin.MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : LeafQM.AV.R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves' hL hM t27 t6 (cmConductorCoprime6_of hE) hK hC

end FS5NoCM


end
