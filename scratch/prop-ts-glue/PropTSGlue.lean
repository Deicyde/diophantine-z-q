import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# prop-ts: Proposition TS (Beckmann's specialization inertia theorem) for the fibre cover

Task prop-ts (2026-11-13). `PropTS` and `PropTSAll` are copied verbatim from
`scratch/fibre-cover/FibreCover.lean` (namespace `G0ModField` kept, so the names agree).

The reduction:

* `BeckmannSIT` (**leaf**): Beckmann's specialization inertia theorem over `ℚ` for a finite
  Galois extension `E/ℚ(X)` with rational branch points, in its unramified consequence, stated
  over Mathlib's `RatFunc ℚ`, `integralClosure`, `Ideal.ramificationIdx`, `padicValRat` and the
  repository's `UnramifiedAt` (ring of integers of a subfield of `ℚ̄`).
* `FunctionFieldModel` (**glue**, curve theory): the `ℚ̄`-points of `Y` over a finite rational
  value `t` have the residue fields of the primes of the integral closure of `ℚ[X]` in `E` over
  `X − t`.
* `CoverBranchData` (**glue from leaves**: Baba–Granath's elliptic orders, h-b1 M3/M4): degree
  `≤ 324`, branch points in `{0, −16/27, ∞}`, indices dividing `4, 2, 6`.
* `NoVerticalRam` (**glue**, Lemma NV of h-b1 §3): no vertical ramification at `p > 324`.

`propTS_of_coverModel : BeckmannSIT → CoverModel Y π → PropTS Y π` is proved here.
-/

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV GlueDescent.B2Q

noncomputable section

namespace G0ModField

/-! ## The statements, copied verbatim from `scratch/fibre-cover/FibreCover.lean` -/

/-- **Glue from leaves: Prop. TS (specialization inertia) on one cover `π₀ : Y₀ → P¹`**
(N5 L484-525; Beckmann, *On extensions of number fields obtained by specializing branched
coverings*, J. reine angew. Math. 419 (1991), Prop. 4.2, UNVERIFIED number; or T1-T2 with the
integral model R1(d)). For a rational non-branch value `t` and a prime `p > 324` (so
`p ∤ |G|`, `p ∤ 30`: good reduction, and the branch points `0, ∞, −16/27` stay distinct mod `p`),
the residue field of a `ℚ̄`-point over `t` is unramified at `p` once the three Beckmann inertia
orders `e_b / gcd(e_b, m_b)` are `1`: `e = 4, 6, 2` at `0, ∞, −16/27` (the indices of
`Y₃ → P¹`, `RvNocm.ramification_eq_orbifold_order`), `m_b` the intersection multiplicities
`v_p(t)⁺`, `(−v_p(t))⁺`, `v_p(t + 16/27)⁺`. -/
def PropTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (t : ℚ) (y : fieldPt Qbar ⟶ Y₀), t ≠ 0 → t ≠ -16 / 27 →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar t) →
    ∀ p : Nat.Primes, 324 < (p : ℕ) →
      4 ∣ (padicValRat p t).toNat → 6 ∣ (-padicValRat p t).toNat →
      2 ∣ (padicValRat p (t + 16 / 27)).toNat →
      UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **Prop. TS for every admissible cover** (the pin-free alternative to `CurvePinned`): every
`(Y, π)` admitting a moduli bijection with R1fp and R2fp satisfies Prop. TS. SPECULATIVE truth
argument (fibre-cover §3.2): R2fp makes every rational fibre of `π` isomorphic, as a Galois set
with residue fields, to a fibre of the genuine `π₀`, a `G`-torsor; by Hilbert irreducibility the
arithmetic monodromy of `π` then acts regularly, so `π` is Galois of degree `|G|` with the same
branch values and indices `4, 6, 2`, and Beckmann's theorem applies with the same inertia orders. -/
def PropTSAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → PropTS Y π

end G0ModField

namespace PropTSRed

open Polynomial G0ModField

/-! ## Part 1: the function-field objects (genuine Mathlib definitions) -/

/-- The affine coordinate ring at `∞` of `P¹_ℚ`: a copy of `ℚ[s]`, mapped to `ℚ(X)` by
`s ↦ X⁻¹` (`Algebra InfCoord (RatFunc ℚ)` below). -/
def InfCoord : Type := Polynomial ℚ

noncomputable instance : CommRing InfCoord := inferInstanceAs (CommRing ℚ[X])

noncomputable instance : Algebra InfCoord (RatFunc ℚ) :=
  @RingHom.toAlgebra InfCoord (RatFunc ℚ) _ _
    (Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹) : ℚ[X] →+* RatFunc ℚ)

/-- The local coordinate `s = 1/X` at `∞`, as an element of `InfCoord`. -/
noncomputable def infUnif : InfCoord := (Polynomial.X : ℚ[X])

/-- `ℚ[s] → E` through `ℚ(X)` (`s ↦ X⁻¹`). -/
@[reducible] noncomputable def infAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E] : Algebra InfCoord E :=
  ((algebraMap (RatFunc ℚ) E).comp (algebraMap InfCoord (RatFunc ℚ))).toAlgebra

/-- `ℤ[X] → E` through `ℚ[X]` (coefficients `ℤ ⊆ ℚ`). -/
@[reducible] noncomputable def intPolyAlg (E : Type) [Field E] [Algebra ℚ[X] E] : Algebra ℤ[X] E :=
  ((algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))).toAlgebra

/-- The prime `p·ℤ[X]` of `ℤ[X]`: the generic point of the fibre of `P¹_ℤ` at `p`. -/
def vertPrime (p : ℕ) : Ideal ℤ[X] := Ideal.map (C : ℤ →+* ℤ[X]) (Ideal.span {(p : ℤ)})

/-- **Branch data of `E/ℚ(X)`** (finite branch points in `S`, with ramification indices dividing
`n b`, and index at `∞` dividing `nInf`), in terms of the integral closures of the two affine
coordinate rings `ℚ[X]` and `ℚ[1/X]` of `P¹_ℚ` in `E`. `Ideal.ramificationIdx` is Mathlib's
localized ramification index (length of `B_Q / 𝔭 B_Q`). -/
def BranchData (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) : Prop :=
  (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime →
      (∀ b ∈ S, Q.under ℚ[X] ≠ Ideal.span {X - C b}) → Q.ramificationIdx ℚ[X] = 1) ∧
  (∀ b ∈ S, ∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime →
      Q.under ℚ[X] = Ideal.span {X - C b} → Q.ramificationIdx ℚ[X] ∣ n b) ∧
  (letI := infAlg E
    ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime →
      Q.under InfCoord = Ideal.span {infUnif} → Q.ramificationIdx InfCoord ∣ nInf)

/-- **No vertical ramification at `p`** (Beckmann's hypothesis (d)): every prime of the integral
closure of `ℤ[X]` in `E` lying over `p·ℤ[X]` (the height-one primes of the fibre at `p`) has
ramification index `1`. Mathlib's `ramificationIdx` localizes at the prime, so this is the
ramification index of the discrete valuation ring at the generic point of a component of the
fibre at `p`. (With `[E : ℚ(X)] < p` the residue extensions are then separable: the inseparable
degree is a power of `p` dividing `f ≤ [E : ℚ(X)]`.) -/
def NoVerticalRam (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∀ Q : Ideal (integralClosure ℤ[X] E), Q.IsPrime → Q.under ℤ[X] = vertPrime p →
    Q.ramificationIdx ℤ[X] = 1

/-! ## Part 2: the leaf -/

/-- **Leaf: Beckmann's specialization inertia theorem over `ℚ`, unramified consequence.**
S. Beckmann, *On extensions of number fields obtained by specializing branched coverings*,
J. reine angew. Math. 419 (1991), Prop. 4.2 (number UNVERIFIED); restated as the
"Specialization Inertia Theorem" by Legrand (Israel J. Math. 2016, §2) and Dèbes–Legrand (Trans.
AMS 2013) (locators UNVERIFIED). h-b1 §1.2 proves the case from SGA 1 (purity + Abhyankar).

Let `E/ℚ(X)` be finite Galois (`X` need not be geometrically irreducible), with branch points in
`S ∪ {∞}` (`S ⊆ ℚ`) and ramification indices dividing `n b` (at `b ∈ S`) and `nInf` (at `∞`).
Let `p` be a prime with (a) `[E : ℚ(X)] < p` (a stronger hypothesis than `p ∤ |G|`, so the leaf
is weaker than the theorem), (b) the branch points pairwise distinct mod `p`
(every `b ∈ S` is `p`-integral, so it does not meet `∞`, and `v_p(b − b') = 0`), (c) automatic
(branch points rational), (d) no vertical ramification at `p`. Let `t ∈ ℚ ∖ S` (not a branch
point). Beckmann: the inertia group at `p` of the specialization `E_t` is conjugate to
`⟨g_b^{I_p(t, b)}⟩`, of order `e_b / gcd(e_b, I_p(t, b))`, where `I_p(t, b) = v_p(t − b)⁺` for
`b ∈ S` and `I_p(t, ∞) = (−v_p t)⁺`, and `E_t` is unramified at `p` if `t` meets no branch point
mod `p`. Hence (`e_b ∣ n b`): if `n b ∣ v_p(t − b)⁺` for all `b ∈ S` and `nInf ∣ (−v_p t)⁺`, then
the residue field `B/𝔓` of every prime `𝔓` of `B = ` (integral closure of `ℚ[X]` in `E`) over
`X − t`, embedded in `ℚ̄` in any way, is unramified at `p`.

Non-regular `E` (constant field `k' ⊋ ℚ`; needed since `Y₃` has two geometric components):
this case follows from the regular case over `k'` (the form of Legrand and Dèbes–Legrand). Apply
the theorem to `E/k'(X)`, whose group is a subgroup of `G`, with the same rational branch points.
`NoVerticalRam E p` forces `k'` unramified at `p` (multiplicativity of `e` in
`ℤ[X] ⊆ 𝒪_{k'}[X] ⊆ C`). `B/𝔓 ⊇ k'` is the specialization of `E/k'(X)` at `t`. Whether
Beckmann's Prop. 4.2 itself assumes regularity, and its exact form of (d), are UNVERIFIED. -/
def BeckmannSIT : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf →
    Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    NoVerticalRam E p →
    ∀ t : ℚ, t ∉ S →
      (∀ b ∈ S, n b ∣ (padicValRat p (t - b)).toNat) → nInf ∣ (-padicValRat p t).toNat →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C t} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p

/-! ## Part 3: the glue for the cover `(Y, π)` -/

/-- **Glue (curve theory): `E` is the function field of `Y` over `ℚ(X) = ℚ(P¹)` along `π`, on
the finite rational fibres.** For every `ℚ̄`-point `y` of `Y` with `π(y) = t ∈ ℚ`, the residue
field `ℚ(y) ⊆ ℚ̄` is the image of the residue field `B/𝔓` of a prime `𝔓` of the integral closure
`B` of `ℚ[X]` in `E` over `X − t`, under some embedding into `ℚ̄`. True when `Y` is a normal
proper curve, `π` finite (non-constant on each component) and `E = ℚ(Y^{(1)})` for a
`ℚ`-irreducible component `Y^{(1)}` whose translates under a group acting over `ℚ` and leaving
`π` invariant cover the fibre (then `π⁻¹(𝔸¹) ∩ Y^{(1)} = Spec B` and `κ(y) ≅ B/𝔓`; h-b1 M2, M8).
For `Y₃`: rightMul keeps the QM pair and twists are R2fp's fibre relation, so `π` is invariant. -/
def FunctionFieldModel (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) (E : Type)
    [Field E] [Algebra ℚ[X] E] : Prop :=
  ∀ (t : ℚ) (y : fieldPt Qbar ⟶ Y),
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar t) →
    ∃ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime ∧
      𝔓.under ℚ[X] = Ideal.span {X - C t} ∧
      ∃ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range φ)

/-- The indices `4` at `0` and `2` at `−16/27` (the finite branch points of `Y₃ → P¹_j`). -/
def nY3 (b : ℚ) : ℕ := if b = 0 then 4 else 2

/-- **Glue from leaves: the branch data of `Y₃ → P¹_j`** (h-b1 M3, M4: `[E : ℚ(j)]` divides
`|Γ'| = 144 ≤ 324`; branch points `0, ∞, −16/27` with indices `4, 6, 2`, the elliptic orders of
Baba–Granath §3.1, `RvNocm.ramification_eq_orbifold_order`). -/
def CoverBranchData (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [FiniteDimensional (RatFunc ℚ) E] : Prop :=
  Module.finrank (RatFunc ℚ) E ≤ 324 ∧ BranchData E {0, -16 / 27} nY3 6

/-- **The cover model of `(Y, π)`**: a finite Galois `E/ℚ(X)` with the three glue properties
(`FunctionFieldModel`, `CoverBranchData`, `NoVerticalRam` at every `p > 324`, Lemma NV). -/
def CoverModel (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
    (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E)
    (_ : IsGalois (RatFunc ℚ) E),
    FunctionFieldModel Y π E ∧ CoverBranchData E ∧
      ∀ p : ℕ, p.Prime → 324 < p → NoVerticalRam E p

/-! ## Part 4: the reduction -/

theorem padicValRat_16_27 (p : ℕ) [Fact p.Prime] (hp : 27 < p) :
    padicValRat p (16 / 27 : ℚ) = 0 := by
  have h16 : padicValRat p ((16 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have h27 : padicValRat p ((27 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have e : (16 / 27 : ℚ) = ((16 : ℕ) : ℚ) / ((27 : ℕ) : ℚ) := by norm_num
  rw [e, padicValRat.div (by norm_num) (by norm_num), h16, h27, sub_zero]

/-- **Prop. TS from Beckmann's theorem and the cover model** (the valuation bookkeeping:
`S = {0, −16/27}`, `n = 4, 2`, `nInf = 6`; `p > 324` gives (a) from `[E : ℚ(X)] ≤ 324` and (b)
from `v_p(16/27) = 0`). -/
theorem propTS_of_coverModel (hB : BeckmannSIT) (Y : Over (Spec (CommRingCat.of ℚ)))
    (π : ToP1 Y.left) (h : CoverModel Y π) : PropTS Y π := by
  obtain ⟨E, _, _, _, _, _, _, hM, ⟨hdeg, hBr⟩, hV⟩ := h
  intro t y ht0 htb hπ p hp h4 h6 h2
  obtain ⟨𝔓, hP, hU, φ, hres⟩ := hM t y hπ
  rw [hres]
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have h16 := padicValRat_16_27 p (by omega)
  have hne : (-16 / 27 : ℚ) ≠ 0 := by norm_num
  refine hB E {0, -16 / 27} nY3 6 p p.2 hBr ?_ ?_ ?_ (hV p p.2 hp) t ?_ ?_ h6 𝔓 hP hU φ
  · omega
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simp
    · rw [show (-16 / 27 : ℚ) = -(16 / 27) by ring, padicValRat.neg, h16]
  · intro b hb b' hb' hbb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hbb
    · rw [show (0 : ℚ) - -16 / 27 = 16 / 27 by ring, h16]
    · rw [show (-16 / 27 : ℚ) - 0 = -(16 / 27) by ring, padicValRat.neg, h16]
    · exact absurd rfl hbb
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ht0, htb⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simpa [nY3] using h4
    · rw [show t - -16 / 27 = t + 16 / 27 by ring]
      simpa [nY3, hne] using h2

/-- **`PropTSAll` from Beckmann's theorem and a cover model for every admissible `(Y, π)`.** -/
theorem propTSAll_of_coverModel (hB : BeckmannSIT)
    (h : ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → CoverModel Y π) : PropTSAll :=
  fun Y Φ π h1 h2 => propTS_of_coverModel hB Y π (h Y Φ π h1 h2)


/-! ## Part 5: only the leaf's own triple needs a cover model (via the kernel's `MobiusGlue`) -/

open LeafQM.AV.Pin

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree (copied from `scratch/fibre-cover/FibreCover.lean`). -/
theorem spec_to_specQ_eq {K : Type} [Field K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- A `ℚ̄`-point factors through every subfield `K ⊆ ℚ̄` containing its residue field (copied from
`scratch/fibre-cover/FibreCover.lean`). -/
theorem exists_factor_of_residueImage_le (Y : Over (Spec (CommRingCat.of ℚ)))
    (y : fieldPt Qbar ⟶ Y) (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ yK : fieldPt K ⟶ Y, fieldMap K.val ≫ yK = y := by
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  unfold residueImage at hK
  rw [hp] at hK
  have hmem : ∀ a, emb a ∈ K := fun a => hK (IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩)
  let emb' : Y.left.residueField x ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (emb.hom.codRestrict K hmem)
  have aux : Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
      (Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩ = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply, hp]
    rfl
  exact ⟨Over.homMk ((Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩)
    (spec_to_specQ_eq _ _), Over.OverMorphism.ext aux⟩

/-- The residue field of `z ∘ Spec(K ⊆ ℚ̄)` lies in `K` (copied from fibre-cover). -/
theorem residueImage_le_aux {X : Scheme.{0}} (K : IF) (z : Spec (CommRingCat.of K) ⟶ X) :
    residueImage (X := X)
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ z) ≤ K := by
  unfold residueImage
  rw [IntermediateField.adjoin_le_iff, specToEquivOfField_comp]
  rintro _ ⟨a, rfl⟩
  exact ((Scheme.SpecToEquivOfField K X z).2 a).2

/-- The residue field can only shrink along a morphism (copied from fibre-cover). -/
theorem residueImage_comp_le_self_aux {X X' : Scheme.{0}} (h : X ⟶ X')
    (z : Spec (CommRingCat.of Qbar) ⟶ X) :
    residueImage (X := X') (z ≫ h) ≤ residueImage (X := X) z := by
  unfold residueImage
  rw [specToEquivOfField_comp_right]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _ ⟨_, rfl⟩

/-- **Residue fields are preserved by a morphism compatible with the moduli bijections**: if
`Φ' = Φ ∘ g` on `K`-points for every field `K`, then `ℚ(g ∘ y') = ℚ(y')` (composition with `g`
is then a bijection on `K`-points, so `y'` factors through `ℚ(g ∘ y')`). -/
theorem residueImage_comp_eq_of_pt {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} (g : Y' ⟶ Y)
    (hΦ : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g))
    (y' : fieldPt Qbar ⟶ Y') :
    residueImage (X := Y.left) (y' ≫ g).left = residueImage (X := Y'.left) y'.left := by
  apply le_antisymm (residueImage_comp_le_self_aux g.left y'.left)
  let K : IF := residueImage (X := Y.left) (y' ≫ g).left
  obtain ⟨w, hw⟩ := exists_factor_of_residueImage_le Y (y' ≫ g) K le_rfl
  let z : fieldPt K ⟶ Y' := (Φ' K).symm (Φ K w)
  have hz : z ≫ g = w := (Φ K).injective (by rw [← hΦ]; exact Equiv.apply_symm_apply _ _)
  have hy : fieldMap K.val ≫ z = y' :=
    (Φ' Qbar).injective (by rw [hΦ, hΦ, Category.assoc, hz, hw])
  have key : residueImage (X := Y'.left) y'.left ≤ K := by
    rw [← hy]
    exact residueImage_le_aux K z.left
  exact key

/-- **Prop. TS transfers along the comparison of triples** (`SameTripleMor`, kernel
`ZInQKernel/HDecomp/QM/Pin.lean`). -/
theorem propTS_transfer {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : SameTripleMor Y Y' Φ Φ' π π') (h : PropTS Y π) : PropTS Y' π' := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  intro t y' ht0 htb hπ' p hp h4 h6 h2
  rw [← residueImage_comp_eq_of_pt g hΦ y']
  exact h t (y' ≫ g) ht0 htb ((hπ y').symm.trans hπ') p hp h4 h6 h2

/-- **`PropTSAll` from Prop. TS on one triple satisfying the repaired clauses**, given the
kernel's named curve glue `MobiusGlue` and the leaf bundle's `R1R2fp` (for the CM objects). -/
theorem propTSAll_of_witness (hM : MobiusGlue) (hR : R1R2fp)
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpProps Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀) (h : PropTS Y₀ π₀) : PropTSAll :=
  fun _ _ _ h1' h2' =>
    propTS_transfer (sameTripleMor_of_mobius hM (cm_objects_of_R1R2fp hR) h1 h2 h1' h2') h

/-- **Glue (from the leaf clauses on one triple): the cover model of `Y₃ → P¹_j`.** A triple with
R1fp, R1hecke (the group `Γ'` acts over `ℚ`, so the function field of a `ℚ`-component is Galois
over `ℚ(j)`, h-b1 M1-M2) and R2fp has a cover model: `FunctionFieldModel` (normalization; h-b1
M8), `CoverBranchData` (h-b1 M3-M4), and `NoVerticalRam` at `p > 324` (Lemma NV, h-b1 §3). -/
def CoverModelOfHecke : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → CoverModel Y π

/-- **The composite: `PropTSAll` from the leaf `BeckmannSIT`, the bundle leaf `R1R2fp`, the kernel
glue `MobiusGlue`, and the glue `CoverModelOfHecke`.** -/
theorem propTSAll_of_leaves (hB : BeckmannSIT) (hR : R1R2fp) (hM : MobiusGlue)
    (hC : CoverModelOfHecke) : PropTSAll := by
  obtain ⟨Y₀, Φ₀, π₀, h1, hh, h2⟩ := R1R2fp_Y hR
  exact propTSAll_of_witness hM hR h1 h2 (propTS_of_coverModel hB Y₀ π₀ (hC Y₀ Φ₀ π₀ h1 hh h2))

/-! ## Part 6: sanity checks on the statements -/

/-- The leaf's instance binders are satisfiable by the genuine objects: `ℚ(X)` itself. -/
example (h : BeckmannSIT) := h (RatFunc ℚ)

/-! ## Part 7: Beckmann's theorem as glue from purity (t-purity3, proved) and Abhyankar (T2)

h-b1 §1.2 proves the case of Beckmann's theorem we use from Zariski–Nagata purity and Abhyankar's
lemma. We split the unramified consequence into three Props:

* `SpecNonMeeting` (glue from purity): the case where the specialization point meets no branch
  point mod `p`. Proof (not compiled): at the closed point `m = (p, X − s₀)` of `ℤ_(p)[X]` the
  height-one primes are `(p)` (unramified: `NoVerticalRam` and `[E : ℚ(X)] < p`) and `(g)` with `g`
  primitive irreducible and `p ∣ g(s₀)`; a ramified `(g)` is excluded by `NonMeeting` (Gauss's
  lemma: `f ∈ gℚ[X]` `p`-integral gives `f = g h` in `ℤ_(p)[X]`, so `p ∣ f(s₀)`). So the integral
  closure of `ℤ_(p)[X]_m` in `E` (normal, finite, torsion-free) is étale over the 2-dimensional
  regular local ring (`TPurity3.purityGlobalDim2'`, proved in `scratch/t-purity3/PurityDim2.lean`);
  base change along `X ↦ s₀` gives an étale `ℤ_(p)`-algebra whose fraction fields are the
  residue fields `B/𝔓`, so these are unramified at `p`.
* `KummerStep` (glue from Abhyankar's lemma, the bundle's leaf T2 `PkgI2.AbhyankarDVR`): the
  meeting case reduces to the non-meeting case. If `t` meets `b ∈ S` with `m = v_p(t − b)`,
  `n_b ∣ m`, write `t − b = p^m u` and adjoin `s` with `s^{n_b} = c (X − b)`, `c = u^{n_b − 1}`;
  then `s₀ = p^{m/n_b} u ∈ ℚ` lies over `t`; by Abhyankar (DVR form at `X = b`) `E(s)/ℚ(s)` is
  unramified over `s = 0`, its other finite branch points `s^{n_b} = c (b' − b)` are units at
  `s₀`, and `ℚ(s)/ℚ(X)` is unramified at the Gauss valuation (`p ∤ n_b`), so `NoVerticalRam`
  persists. At `∞` (`v_p(t) < 0`) use `s^{nInf} = c / X`. If `t` meets nothing, `E' = E`,
  `s₀ = t`.
* `UnramifiedMono` (textbook): a subfield of a number field unramified at `p` is unramified at `p`
  (multiplicativity of ramification indices in towers). -/

/-- `s₀` meets no branch point of `E/ℚ(X)` mod `p`: every ramified prime `Q` of the integral
closure of `ℚ[X]` in `E` contains a `p`-integral polynomial `f` with `f(s₀)` a `p`-adic unit. -/
def NonMeeting (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) (s₀ : ℚ) : Prop :=
  ∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.ramificationIdx ℚ[X] ≠ 1 →
    ∃ f ∈ Q.under ℚ[X], (∀ i, 0 ≤ padicValRat p (f.coeff i)) ∧ f.eval s₀ ≠ 0 ∧
      padicValRat p (f.eval s₀) = 0

/-- **Glue from purity (T1, proved by t-purity3): specialization away from the branch locus.**
For `E/ℚ(X)` finite with `[E : ℚ(X)] < p`, no vertical ramification at `p`, and a `p`-integral
`s₀ ∈ ℚ` meeting no branch point mod `p`, every residue field of the integral closure of `ℚ[X]`
in `E` over `X − s₀`, embedded in `ℚ̄`, is a number field unramified at `p`. (Grothendieck's specialization of
étale covers; SGA 1 X; the proof via `purityGlobalDim2'` is sketched above.) -/
def SpecNonMeeting : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ), p.Prime →
    Module.finrank (RatFunc ℚ) E < p → NoVerticalRam E p →
    ∀ s₀ : ℚ, 0 ≤ padicValRat p s₀ → NonMeeting E p s₀ →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C s₀} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range φ)) ∧
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p

/-- **Glue from Abhyankar's lemma: the Kummer reduction of the meeting case** (h-b1 §1.2, proof of
Prop. TS, second case, rewritten with a rational Kummer coordinate; see the Part 7 header). For a
specialization `t` with `n_b ∣ v_p(t − b)⁺` and `nInf ∣ (−v_p t)⁺`, there is a finite `E'/ℚ(s)`
(a factor of `E ⊗ ℚ(s)`, `s` the Kummer coordinate) and a `p`-integral `s₀ ∈ ℚ` meeting no branch
point of `E'` mod `p`, with no vertical ramification at `p`, such that the given residue field of
`E` at `t` embeds in a residue field of `E'` at `s₀`. The case where `t` meets no branch point is
proved (`kummerStep_of_meet`); the glue is `KummerMeet`. -/
def KummerStep : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf →
    Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 < n b ∧ n b < p) → 0 < nInf → nInf < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    NoVerticalRam E p →
    ∀ t : ℚ, t ∉ S →
      (∀ b ∈ S, n b ∣ (padicValRat p (t - b)).toNat) → nInf ∣ (-padicValRat p t).toNat →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C t} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
          (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
          (s₀ : ℚ), Module.finrank (RatFunc ℚ) E' < p ∧ NoVerticalRam E' p ∧
          0 ≤ padicValRat p s₀ ∧ NonMeeting E' p s₀ ∧
          ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
            𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
            ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* Qbar,
              IntermediateField.adjoin ℚ (Set.range φ) ≤
                IntermediateField.adjoin ℚ (Set.range φ')

/-- `KummerStep` is glue whose proof uses the bundle's textbook leaf T2 (Abhyankar's lemma, DVR
form, `PkgI2.AbhyankarDVR`) at the branch point being met. -/
def KummerGlue : Prop := PkgI2.AbhyankarDVR.{0} → KummerStep

/-- **Glue from Abhyankar's lemma, the meeting case only**: `KummerStep` under the extra
hypothesis that `t` meets a branch point mod `p` (`v_p(t) < 0`, or `v_p(t − b) > 0` for some
`b ∈ S`). -/
def KummerMeet : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf →
    Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 < n b ∧ n b < p) → 0 < nInf → nInf < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    NoVerticalRam E p →
    ∀ t : ℚ, t ∉ S →
      (∀ b ∈ S, n b ∣ (padicValRat p (t - b)).toNat) → nInf ∣ (-padicValRat p t).toNat →
      (padicValRat p t < 0 ∨ ∃ b ∈ S, 0 < padicValRat p (t - b)) →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C t} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
          (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
          (s₀ : ℚ), Module.finrank (RatFunc ℚ) E' < p ∧ NoVerticalRam E' p ∧
          0 ≤ padicValRat p s₀ ∧ NonMeeting E' p s₀ ∧
          ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
            𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
            ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* Qbar,
              IntermediateField.adjoin ℚ (Set.range φ) ≤
                IntermediateField.adjoin ℚ (Set.range φ')

/-- `KummerMeet` is glue whose proof uses the bundle's leaf T2 (`PkgI2.AbhyankarDVR`). -/
def KummerMeetGlue : Prop := PkgI2.AbhyankarDVR.{0} → KummerMeet

theorem padicValRat_sub_nonneg (p : ℕ) [Fact p.Prime] {t b : ℚ} (ht : 0 ≤ padicValRat p t)
    (hb : 0 ≤ padicValRat p b) (htb : t ≠ b) : 0 ≤ padicValRat p (t - b) := by
  have h := padicValRat.min_le_padicValRat_add (p := p) (q := t) (r := -b)
    (by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr htb)
  rw [padicValRat.neg, ← sub_eq_add_neg] at h
  exact le_trans (le_min ht hb) h

/-- **The non-meeting case of `KummerStep` is proved** (`E' = E`, `s₀ = t`: the ramified primes
lie over `X − b`, `b ∈ S`, by `BranchData`, and `f = X − b` is `p`-integral with `f(t)` a unit). -/
theorem kummerStep_of_meet (h : KummerMeet) : KummerStep := by
  intro E _ _ _ _ _ _ S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf 𝔓 hP hU φ
  by_cases hm : padicValRat p t < 0 ∨ ∃ b ∈ S, 0 < padicValRat p (t - b)
  · exact h E S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf hm 𝔓 hP hU φ
  push Not at hm
  obtain ⟨ht0, hbt⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, t, hdeg,
    hV, ht0, ?_, 𝔓, hP, hU, φ, le_rfl⟩
  intro Q hQ he
  obtain ⟨b, hbS, hb⟩ : ∃ b ∈ S, Q.under ℚ[X] = Ideal.span {X - C b} := by
    by_contra hc
    push Not at hc
    exact he (hBr.1 Q hQ hc)
  have htb : t ≠ b := fun e => ht (e ▸ hbS)
  refine ⟨X - C b, ?_, ?_, ?_, ?_⟩
  · rw [hb]
    exact Ideal.mem_span_singleton_self _
  · intro i
    rw [coeff_sub, coeff_X, coeff_C]
    by_cases h1 : 1 = i
    · subst h1
      simp
    · by_cases h0 : i = 0
      · subst h0
        simp only [one_ne_zero, ↓reduceIte, zero_sub, padicValRat.neg]
        exact hint b hbS
      · simp [h1, h0]
  · simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr htb
  · simp only [eval_sub, eval_X, eval_C]
    exact le_antisymm (hbt b hbS) (padicValRat_sub_nonneg p ht0 (hint b hbS) htb)

/-- **Textbook: subfields inherit unramifiedness** (Neukirch, ANT I §8, multiplicativity of `e`
in towers; Mathlib `Ideal.ramificationIdx_below_dvd` for flat towers). -/
def UnramifiedMono : Prop :=
  ∀ L L' : IntermediateField ℚ Qbar, FiniteDimensional ℚ L' → L ≤ L' →
    ∀ p : ℕ, UnramifiedAt L' p → UnramifiedAt L p

/-- **Beckmann's theorem, tame form**: `BeckmannSIT` with the extra hypotheses `0 < n_b < p`,
`0 < nInf < p` (weaker than `BeckmannSIT`, `beckmannSITTame_of`). -/
def BeckmannSITTame : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf →
    Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 < n b ∧ n b < p) → 0 < nInf → nInf < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    NoVerticalRam E p →
    ∀ t : ℚ, t ∉ S →
      (∀ b ∈ S, n b ∣ (padicValRat p (t - b)).toNat) → nInf ∣ (-padicValRat p t).toNat →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C t} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p

theorem beckmannSITTame_of (h : BeckmannSIT) : BeckmannSITTame :=
  fun E _ _ _ _ _ _ S n nInf p hp hBr hdeg _ _ _ hint hdist hV t ht hn hinf 𝔓 hP hU φ =>
    h E S n nInf p hp hBr hdeg hint hdist hV t ht hn hinf 𝔓 hP hU φ

/-- **Beckmann's theorem (tame form) from the three glue pieces** (compiled). -/
theorem beckmannSITTame_of_glue (hK : KummerStep) (hN : SpecNonMeeting)
    (hMono : UnramifiedMono) : BeckmannSITTame := by
  intro E _ _ _ _ _ _ S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf 𝔓 hP hU φ
  obtain ⟨E', _, _, _, _, _, s₀, hdeg', hV', hs₀, hNM, 𝔓', hP', hU', φ', hle⟩ :=
    hK E S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf 𝔓 hP hU φ
  obtain ⟨hfin, hun⟩ := hN E' p hp hdeg' hV' s₀ hs₀ hNM 𝔓' hP' hU' φ'
  exact hMono _ _ hfin hle p hun

/-- **Prop. TS from the tame form of Beckmann's theorem and the cover model** (as
`propTS_of_coverModel`; the extra hypotheses hold as `4, 2, 6 < 324 < p`). -/
theorem propTS_of_coverModel_tame (hB : BeckmannSITTame) (Y : Over (Spec (CommRingCat.of ℚ)))
    (π : ToP1 Y.left) (h : CoverModel Y π) : PropTS Y π := by
  obtain ⟨E, _, _, _, _, _, _, hM, ⟨hdeg, hBr⟩, hV⟩ := h
  intro t y ht0 htb hπ p hp h4 h6 h2
  obtain ⟨𝔓, hP, hU, φ, hres⟩ := hM t y hπ
  rw [hres]
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have h16 := padicValRat_16_27 p (by omega)
  have hne : (-16 / 27 : ℚ) ≠ 0 := by norm_num
  refine hB E {0, -16 / 27} nY3 6 p p.2 hBr (by omega) ?_ (by norm_num) (by omega) ?_ ?_
    (hV p p.2 hp) t ?_ ?_ h6 𝔓 hP hU φ
  · intro b _
    unfold nY3
    split_ifs <;> omega
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simp
    · rw [show (-16 / 27 : ℚ) = -(16 / 27) by ring, padicValRat.neg, h16]
  · intro b hb b' hb' hbb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hbb
    · rw [show (0 : ℚ) - -16 / 27 = 16 / 27 by ring, h16]
    · rw [show (-16 / 27 : ℚ) - 0 = -(16 / 27) by ring, padicValRat.neg, h16]
    · exact absurd rfl hbb
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ht0, htb⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · simpa [nY3] using h4
    · rw [show t - -16 / 27 = t + 16 / 27 by ring]
      simpa [nY3, hne] using h2

/-- **The composite without a Beckmann leaf**: `PropTSAll` from the bundle leaves T2
(`PkgI2.AbhyankarDVR`) and `R1R2fp`, the glue `KummerGlue`, `SpecNonMeeting` (from purity),
`UnramifiedMono` (textbook), the kernel glue `MobiusGlue`, and `CoverModelOfHecke`. -/
theorem propTSAll_of_bundle (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hKG : KummerGlue)
    (hN : SpecNonMeeting) (hMono : UnramifiedMono) (hM : MobiusGlue)
    (hC : CoverModelOfHecke) : PropTSAll := by
  obtain ⟨Y₀, Φ₀, π₀, h1, hh, h2⟩ := R1R2fp_Y hR
  exact propTSAll_of_witness hM hR h1 h2
    (propTS_of_coverModel_tame (beckmannSITTame_of_glue (hKG t2) hN hMono) Y₀ π₀
      (hC Y₀ Φ₀ π₀ h1 hh h2))

/-- **`UnramifiedMono` is a theorem** (Mathlib: `Ideal.exists_ideal_over_prime_of_isIntegral`,
`Ideal.ramificationIdx_below_dvd` for the flat extension `𝓞 L → 𝓞 L'` of Dedekind domains). -/
theorem unramifiedMono : UnramifiedMono := by
  intro L L' _ hle p hU
  have : FiniteDimensional ℚ L := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have : NumberField L := ⟨⟩
  have : NumberField L' := ⟨⟩
  let : Algebra L L' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  intro P hP hpP
  have : Algebra.IsIntegral (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers L') :=
    inferInstance
  have : Module.Flat (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers L') :=
    inferInstance
  obtain ⟨r, -, hr, hrP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P
    (⊥ : Ideal (NumberField.RingOfIntegers L')) (by simp)
  have hpr : ((p : ℤ) : NumberField.RingOfIntegers L') ∈ r := by
    have h1 : ((p : ℤ) : NumberField.RingOfIntegers L) ∈ r.under (NumberField.RingOfIntegers L) :=
      hrP ▸ hpP
    simpa using h1
  have : r.LiesOver P := ⟨hrP.symm⟩
  have hd := Ideal.ramificationIdx_below_dvd (R := ℤ) P r
  rw [hU r hr hpr] at hd
  exact Nat.dvd_one.mp hd

/-- **The composite without a Beckmann leaf and without `UnramifiedMono`.** -/
theorem propTSAll_of_bundle' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hKG : KummerGlue)
    (hN : SpecNonMeeting) (hM : MobiusGlue) (hC : CoverModelOfHecke) : PropTSAll :=
  propTSAll_of_bundle t2 hR hKG hN unramifiedMono hM hC

/-- **The final composite**: `PropTSAll` from the bundle leaves T2 (`PkgI2.AbhyankarDVR`) and
`R1R2fp`, and the glue `KummerMeetGlue`, `SpecNonMeeting`, `MobiusGlue` (kernel),
`CoverModelOfHecke`. -/
theorem propTSAll_of_bundle_meet (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp)
    (hKG : KummerMeetGlue) (hN : SpecNonMeeting) (hM : MobiusGlue) (hC : CoverModelOfHecke) :
    PropTSAll :=
  propTSAll_of_bundle' t2 hR (fun t2' => kummerStep_of_meet (hKG t2')) hN hM hC

/-! ## Part 8: `FunctionFieldModel` from the normalization of `P¹` in `E` over `𝔸¹` -/

/-- Scheme form of fibre-cover's `exists_factor_of_residueImage_le`. -/
theorem exists_factor_scheme {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) (K : IF)
    (hK : residueImage (X := X) y ≤ K) :
    ∃ z : Spec (CommRingCat.of K) ⟶ X,
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ z = y := by
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar X y = q := ⟨_, rfl⟩
  unfold residueImage at hK
  rw [hp] at hK
  have hmem : ∀ a, emb a ∈ K := fun a => hK (IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩)
  let emb' : X.residueField x ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (emb.hom.codRestrict K hmem)
  refine ⟨(Scheme.SpecToEquivOfField K X).symm ⟨x, emb'⟩, ?_⟩
  apply (Scheme.SpecToEquivOfField Qbar X).injective
  rw [specToEquivOfField_comp, Equiv.apply_symm_apply, hp]
  rfl

/-- **The residue field of the `ℚ̄`-point `Spec ψ` of `Spec B` is the field generated by
`ψ(B)`.** -/
theorem residueImage_specMap (B : Type) [CommRing B] (ψ : B →+* Qbar) :
    residueImage (X := Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom ψ)) =
      IntermediateField.adjoin ℚ (Set.range ψ) := by
  apply le_antisymm
  · set K : IF := IntermediateField.adjoin ℚ (Set.range ψ)
    have hmem : ∀ b, ψ b ∈ K := fun b => IntermediateField.subset_adjoin ℚ _ ⟨b, rfl⟩
    let ψ' : B →+* K := ψ.codRestrict K.toSubfield hmem
    have e : Spec.map (CommRingCat.ofHom ψ) =
        Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
          Spec.map (CommRingCat.ofHom ψ') := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [e]
    exact residueImage_le_aux K _
  · set K : IF := residueImage (X := Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom ψ))
    obtain ⟨z, hz⟩ := exists_factor_scheme (Spec.map (CommRingCat.ofHom ψ)) K le_rfl
    rw [← Spec.map_preimage z, ← Spec.map_comp, Spec.map_inj] at hz
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, rfl⟩
    have := congrArg (fun f => f.hom b) hz
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    rw [← this]
    exact ((Spec.preimage z).hom b).2

/-- **Open immersions preserve residue fields of `ℚ̄`-points.** -/
theorem residueImage_comp_openImmersion {X X' : Scheme.{0}} (h : X ⟶ X') [IsOpenImmersion h]
    (y : Spec (CommRingCat.of Qbar) ⟶ X) :
    residueImage (X := X') (y ≫ h) = residueImage (X := X) y := by
  apply le_antisymm (residueImage_comp_le_self_aux h y)
  set K : IF := residueImage (X := X') (y ≫ h)
  obtain ⟨w, hw⟩ := exists_factor_scheme (y ≫ h) K le_rfl
  have hr : Set.range w ⊆ Set.range h := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, (Spec.map (CommRingCat.ofHom
        ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar))) b = a := ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    refine ⟨y b, ?_⟩
    rw [← hb, ← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]
  have hl := IsOpenImmersion.lift_fac h w hr
  have : Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
      IsOpenImmersion.lift h w hr = y := by
    rw [← cancel_mono h, Category.assoc, hl, hw]
  rw [← this]
  exact residueImage_le_aux K _

/-- **Glue (normalization of `P¹` in `E` over `𝔸¹`).** An open immersion
`h : Spec B → Y` (`B` the integral closure of `ℚ[X]` in `E`) whose image contains every
`ℚ̄`-point with finite `π`-value, and along which `π` is the coordinate `X`. True for a normal
proper `ℚ`-irreducible curve `Y` with function field `E` and `π` finite (`π⁻¹(𝔸¹) = Spec B`).
`Y₃` is `ℚ`-irreducible: its two geometric components (`π₀ = ℤ̂^×/nrd(K₃) ≅ (ℤ/3)^×`) are
conjugate over `ℚ(√−3)` by Shimura reciprocity on `π₀` (SPECULATIVE reading, h-b1 M10 style). -/
def NormalizationModel (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) (E : Type)
    [Field E] [Algebra ℚ[X] E] : Prop :=
  ∃ h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left, IsOpenImmersion h ∧
    (∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h) ∧
    ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X))

theorem functionFieldModel_of_normalization (Y : Over (Spec (CommRingCat.of ℚ)))
    (π : ToP1 Y.left) (E : Type) [Field E] [Algebra ℚ[X] E] (hN : NormalizationModel Y π E) :
    FunctionFieldModel Y π E := by
  obtain ⟨h, hO, himg, hval⟩ := hN
  intro t y hπ
  obtain ⟨y', hy'⟩ := himg y.left (by rw [hπ]; exact OnePoint.coe_ne_infty _)
  set ψ := (Spec.preimage y').hom with hψ
  have hy'' : y' = Spec.map (CommRingCat.ofHom ψ) := by
    rw [hψ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hX : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Qbar t := by
    have := hval ψ
    rw [← hy'', ← hy', hπ] at this
    exact (OnePoint.coe_injective this).symm
  have hC : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C t)) = algebraMap ℚ Qbar t := by
    have hsub : ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp C : ℚ →+* Qbar) =
        algebraMap ℚ Qbar := Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* Qbar => f t) hsub
  refine ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ, ?_, Ideal.Quotient.lift _ ψ (fun a ha => ha), ?_⟩
  · have hle : Ideal.span {X - C t} ≤ (RingHom.ker ψ).under ℚ[X] := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (X - C t)) = 0
      rw [map_sub, map_sub, hX, hC, sub_self]
    have hmax : (Ideal.span {X - C t} : Ideal ℚ[X]).IsMaximal := by
      rw [← Polynomial.ker_evalRingHom]
      exact RingHom.ker_isMaximal_of_surjective _ (fun x => ⟨C x, eval_C⟩)
    have hprime : ((RingHom.ker ψ).under ℚ[X]).IsPrime :=
      haveI := RingHom.ker_isPrime ψ; Ideal.IsPrime.comap _
    exact (hmax.eq_of_le hprime.ne_top hle).symm
  · rw [hy', residueImage_comp_openImmersion h y', hy'', residueImage_specMap]
    congr 1
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨Ideal.Quotient.mk _ b, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨b, rfl⟩


/-- **The cover model with the normalization statement** in place of `FunctionFieldModel`. -/
def CoverModelN (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
    (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E)
    (_ : IsGalois (RatFunc ℚ) E),
    NormalizationModel Y π E ∧ CoverBranchData E ∧
      ∀ p : ℕ, p.Prime → 324 < p → NoVerticalRam E p

theorem coverModel_of_N {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left}
    (h : CoverModelN Y π) : CoverModel Y π := by
  obtain ⟨E, i1, i2, i3, i4, i5, i6, hN, hB, hV⟩ := h
  exact ⟨E, i1, i2, i3, i4, i5, i6, functionFieldModel_of_normalization Y π E hN, hB, hV⟩

/-- **Glue (from the leaf clauses on one triple), normalization form.** -/
def CoverModelOfHeckeN : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → CoverModelN Y π

/-- **The final composite, normalization form**: `PropTSAll` from the bundle leaves T2 and
`R1R2fp`, and the glue `KummerMeetGlue`, `SpecNonMeeting`, `MobiusGlue` (kernel),
`CoverModelOfHeckeN`. -/
theorem propTSAll_of_bundle_N (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp)
    (hKG : KummerMeetGlue) (hN : SpecNonMeeting) (hM : MobiusGlue) (hC : CoverModelOfHeckeN) :
    PropTSAll :=
  propTSAll_of_bundle_meet t2 hR hKG hN hM
    (fun Y Φ π h1 hh h2 => coverModel_of_N (hC Y Φ π h1 hh h2))

/-! ## Part 9: `PropTS` is a property of the cover, not a tautology -/

/-- The constant map `Y → P¹`, value `1`. -/
def constOne (X : Scheme.{0}) : ToP1 X where
  U := ⊤
  V := ⊤
  cover := sup_idem _
  f := 1
  g := 1
  inv := by simp
  basicOpen_f := by rw [Scheme.basicOpen_one, inf_idem]
  basicOpen_g := by rw [Scheme.basicOpen_one, inf_idem]

theorem constOne_val (X : Scheme.{0}) {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ X) :
    (constOne X).val y = OnePoint.some 1 := by
  unfold ToP1.val
  split_ifs with h
  · congr 1
    show (Scheme.SpecToEquivOfField K X y).2 (X.evaluation ⊤ _ h 1) = 1
    rw [map_one, map_one]
  · exact absurd trivial h

theorem exists_primitive_331 : ∃ z : Qbar, IsPrimitiveRoot z 331 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic 331 Qbar)
    (degree_cyclotomic_pos 331 Qbar (by norm_num)).ne.symm
  exact ⟨z, (isRoot_cyclotomic_iff).mp hz⟩


theorem padicValRat_43_27 (p : ℕ) [Fact p.Prime] (hp : 43 < p) :
    padicValRat p (1 + 16 / 27 : ℚ) = 0 := by
  have h43 : padicValRat p ((43 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have h27 : padicValRat p ((27 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have e : (1 + 16 / 27 : ℚ) = ((43 : ℕ) : ℚ) / ((27 : ℕ) : ℚ) := by norm_num
  rw [e, padicValRat.div (by norm_num) (by norm_num), h43, h27, sub_zero]

/-- **`PropTS` fails for some `(Y₀, π₀)`** (so it is a genuine constraint on the cover, to be
proved for `Y₃ → P¹_j` only): `Y₀ = Spec ℚ(ζ₃₃₁)`, `π₀ ≡ 1`, `t = 1`, `p = 331`. Every hypothesis
holds (`v₃₃₁(1) = v₃₃₁(43/27) = 0`), but `331` is totally ramified in `ℚ(ζ₃₃₁)`
(Mathlib `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime`). -/
theorem not_propTS_cyclotomic :
    ∃ (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left), ¬ PropTS Y₀ π₀ := by
  obtain ⟨z, hz⟩ := exists_primitive_331
  have : Fact (Nat.Prime 331) := ⟨by norm_num⟩
  set K : IF := IntermediateField.adjoin ℚ {z}
  have : IsCyclotomicExtension {331} ℚ K := hz.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {331} ℚ K
  have : NumberField K := ⟨⟩
  refine ⟨fieldPt K, constOne _, fun h => ?_⟩
  have hval : (constOne (fieldPt K).left).val (K := Qbar) (fieldMap K.val).left =
      OnePoint.some (algebraMap ℚ Qbar 1) := by
    rw [map_one]
    exact constOne_val (fieldPt K).left (K := Qbar) (fieldMap K.val).left
  have hU := h 1 (fieldMap K.val) one_ne_zero (by norm_num) hval ⟨331, by norm_num⟩
    (by norm_num) (by simp) (by simp) (by rw [padicValRat_43_27 331 (by norm_num)]; simp)
  have hres : residueImage (X := (fieldPt K).left) (fieldMap K.val).left = K := by
    show residueImage (X := Spec (CommRingCat.of K))
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar))) = K
    rw [residueImage_specMap]
    have : Set.range ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) = (K : Set Qbar) := by
      ext x
      simp
    rw [this, IntermediateField.adjoin_self]
  rw [hres] at hU
  have : (Ideal.span {((331 : ℕ) : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr (Nat.prime_iff_prime_int.mp (by norm_num))
  obtain ⟨P, -, hP, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {((331 : ℕ) : ℤ)}) (⊥ : Ideal (NumberField.RingOfIntegers K)) (by simp)
  have : P.LiesOver (Ideal.span {((331 : ℕ) : ℤ)}) := ⟨hPu.symm⟩
  have he := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime 331 K P
  have hmem : (((331 : ℕ) : ℤ) : NumberField.RingOfIntegers K) ∈ P := by
    have : ((331 : ℕ) : ℤ) ∈ P.under ℤ := by
      rw [hPu]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  have h1 := hU P hP hmem
  omega

end PropTSRed

end

#print axioms PropTSRed.padicValRat_16_27
#print axioms PropTSRed.propTS_of_coverModel
#print axioms PropTSRed.propTSAll_of_coverModel
#print axioms PropTSRed.residueImage_comp_eq_of_pt
#print axioms PropTSRed.propTS_transfer
#print axioms PropTSRed.propTSAll_of_witness
#print axioms PropTSRed.propTSAll_of_leaves
#print axioms PropTSRed.beckmannSITTame_of
#print axioms PropTSRed.beckmannSITTame_of_glue
#print axioms PropTSRed.propTS_of_coverModel_tame
#print axioms PropTSRed.propTSAll_of_bundle
#print axioms PropTSRed.unramifiedMono
#print axioms PropTSRed.propTSAll_of_bundle'
#print axioms PropTSRed.padicValRat_sub_nonneg
#print axioms PropTSRed.kummerStep_of_meet
#print axioms PropTSRed.propTSAll_of_bundle_meet
#print axioms PropTSRed.exists_factor_scheme
#print axioms PropTSRed.residueImage_specMap
#print axioms PropTSRed.residueImage_comp_openImmersion
#print axioms PropTSRed.functionFieldModel_of_normalization
#print axioms PropTSRed.coverModel_of_N
#print axioms PropTSRed.propTSAll_of_bundle_N
#print axioms PropTSRed.constOne_val
#print axioms PropTSRed.not_propTS_cyclotomic

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# prop-ts-glue: the three glue Props under Proposition TS, reduced

Everything above this line is `scratch/prop-ts/PropTS.lean`, copied verbatim (checked by
`scratch/prop-ts-glue/check_identical.py`). The three Props of this task are
`PropTSRed.SpecNonMeeting`, `PropTSRed.KummerMeetGlue` and `PropTSRed.CoverModelOfHecke`; they are
used unchanged. Below, each is reduced to strictly smaller named Props.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace PropTSGlue

open Polynomial G0ModField PropTSRed

/-! ## Part A: `SpecNonMeeting` from purity (t-purity3) and three pieces of commutative algebra -/

universe u

/-- **Purity of the branch locus over a two-dimensional regular local base** (Zariski–Nagata;
SGA 1 X 3.1, UNVERIFIED number). Copied verbatim from `scratch/t-purity3/PurityDim2.lean`
(namespace `TPurity3`), where it is **proved** (`TPurity3.purityGlobalDim2`, standard axioms;
docs/research/t-purity3.md §1). It is a hypothesis here only because scratch files cannot import
each other. -/
def PurityGlobalDim2 : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsRegularLocalRing R],
    ringKrullDim R = 2 → ∀ [IsDomain S] [IsIntegrallyClosed S] [Module.Finite R S],
    Function.Injective (algebraMap R S) →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → Algebra.IsUnramifiedIn S P) →
    Algebra.Etale R S

/-- A maximal ideal of `ℤ[X]` over a nonzero prime of `ℤ` has height `2` (copied with its proof
from `scratch/prop-ts/ZXRegular.lean`). -/
theorem height_maximal_intPoly (m : Ideal ℤ[X]) [m.IsMaximal]
    (hne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥) : m.height = 2 := by
  have hc : (m.comap (C : ℤ →+* ℤ[X])).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap _) hne
  have : m.LiesOver (m.comap (C : ℤ →+* ℤ[X])) := ⟨rfl⟩
  rw [Polynomial.height_eq_height_add_one (m.comap (C : ℤ →+* ℤ[X])) m]
  have h1 : (m.comap (C : ℤ →+* ℤ[X])).height = 1 := by
    apply le_antisymm
    · have := Ideal.height_le_ringKrullDim_of_isPrime (I := m.comap (C : ℤ →+* ℤ[X]))
      rw [IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at this
      exact_mod_cast this
    · rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hne
  rw [h1]
  rfl

/-- `ℤ[X]_m` is regular local of dimension `2` (copied with its proof from
`scratch/prop-ts/ZXRegular.lean`). -/
theorem regular_dim2_intPoly (m : Ideal ℤ[X]) [m.IsMaximal]
    (hne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥) :
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = 2 := by
  refine ⟨inferInstance, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m, height_maximal_intPoly m hne]
  rfl

/-- `ℤ[X] → E` through `ℚ[X]` (the map of `intPolyAlg`). -/
abbrev zxMap (E : Type) [Field E] [Algebra ℚ[X] E] : ℤ[X] →+* E :=
  (algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem zxMap_injective (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] : Function.Injective (zxMap E) := by
  intro a b h
  simp only [zxMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E] at h
  have h1 := (algebraMap (RatFunc ℚ) E).injective h
  have h2 := (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) h1
  exact Polynomial.map_injective _ Int.cast_injective h2

/-- **The local base `ℤ[X]_m` mapped to `E`** (the localization of `zxMap E`; elements outside
`m` are nonzero, hence units in the field `E`). -/
@[reducible] noncomputable def locAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E]
    [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] (m : Ideal ℤ[X]) [m.IsPrime] :
    Algebra (Localization.AtPrime m) E :=
  (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) (g := zxMap E)
    (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      apply y.2
      rw [(zxMap_injective E) (h.trans (map_zero _).symm)]
      exact m.zero_mem)).toAlgebra

/-- **The normalization of the local base (PROVED below, `snLocalData`).** For `E/ℚ(X)`
finite and a maximal ideal `m` of `ℤ[X]`, the integral closure `S` of `R = ℤ[X]_m` in `E` is
integrally closed, module-finite over `R` (`R` is Noetherian and normal, `E/Frac R` finite
separable: Mathlib `IsIntegralClosure.finite`), and `R → S` is injective. (`S` is a domain as a
subring of a field.) -/
def SNLocalData : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (m : Ideal ℤ[X]) [m.IsMaximal],
    letI := locAlg E m
    IsIntegrallyClosed (integralClosure (Localization.AtPrime m) E) ∧
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) ∧
    Function.Injective
      (algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E))

/-- `ℚ(X)` is the fraction field of `ℤ[X]` (through `ℤ[X] → ℚ[X] → ℚ(X)`). -/
theorem isFractionRing_zx :
    letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
    IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := zxMap_injective (RatFunc ℚ)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero y (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨⟨P, Q⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors ℚ[X]) z
    obtain ⟨bP, hbPM, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
    obtain ⟨bQ, hbQM, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (Q : ℚ[X])
    set P' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
    set Q' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q : ℚ[X])
    have hbP0 : bP ≠ 0 := nonZeroDivisors.ne_zero hbPM
    have hbQ0 : bQ ≠ 0 := nonZeroDivisors.ne_zero hbQM
    have hQ0 : (Q : ℚ[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero Q
    have hmapQ : Q'.map (Int.castRingHom ℚ) = C (bQ : ℚ) * Q := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbQ
    have hmapP : P'.map (Int.castRingHom ℚ) = C (bP : ℚ) * P := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbP
    have hy : C bP * Q' ∈ nonZeroDivisors ℤ[X] := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      refine mul_ne_zero (by simpa using hbP0) ?_
      intro h0
      have := hmapQ
      rw [h0, Polynomial.map_zero] at this
      exact mul_ne_zero (by simpa using hbQ0) hQ0 this.symm
    refine ⟨⟨C bQ * P', ⟨_, hy⟩⟩, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_C, hmapP, hmapQ, map_mul, eq_intCast]
    rw [← hz]
    simp only [map_intCast, Int.cast_id, Polynomial.map_intCast]
    ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

/-- **`SNLocalData` holds** (the normalization of `ℤ[X]_m` in `E` is normal, finite, and
contains `ℤ[X]_m`). -/
theorem snLocalData_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (m : Ideal ℤ[X]) [m.IsMaximal] :
    letI := locAlg E m
    IsIntegrallyClosed (integralClosure (Localization.AtPrime m) E) ∧
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) ∧
    Function.Injective
      (algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)) := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  letI iK : Algebra (Localization.AtPrime m) (RatFunc ℚ) := locAlg (RatFunc ℚ) m
  letI iZ : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hZ : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  have hT1 : IsScalarTower ℤ[X] (Localization.AtPrime m) (RatFunc ℚ) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hfr : IsFractionRing (Localization.AtPrime m) (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl _ _
  have hT2 : IsScalarTower (Localization.AtPrime m) (RatFunc ℚ) E := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext m.primeCompl
    rw [RingHom.comp_assoc]
    change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime m)) =
      (algebraMap (RatFunc ℚ) E).comp
        ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime m)))
    rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
    simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have hic : IsIntegrallyClosed (Localization.AtPrime m) :=
    isIntegrallyClosed_of_isLocalization _ m.primeCompl m.primeCompl_le_nonZeroDivisors
  refine ⟨integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc ℚ),
    IsIntegralClosure.finite (Localization.AtPrime m) (RatFunc ℚ) E
      (integralClosure (Localization.AtPrime m) E), ?_⟩
  intro a b h
  have h1 := congrArg Subtype.val h
  simp only [IntermediateField.algebraMap_apply, Subalgebra.coe_algebraMap] at h1
  rw [IsScalarTower.algebraMap_apply (Localization.AtPrime m) (RatFunc ℚ) E,
    IsScalarTower.algebraMap_apply (Localization.AtPrime m) (RatFunc ℚ) E] at h1
  exact IsFractionRing.injective (Localization.AtPrime m) (RatFunc ℚ)
    ((algebraMap (RatFunc ℚ) E).injective h1)

/-- **`SNLocalData` is a theorem** (Mathlib: `IsIntegralClosure.finite`,
`integralClosure.isIntegrallyClosedOfFiniteExtension`, `isIntegrallyClosed_of_isLocalization`;
`ℚ(X)` is the fraction field of `ℤ[X]_m` via `isFractionRing_zx`). -/
theorem snLocalData : SNLocalData := fun E _ _ _ _ _ m _ => snLocalData_aux E m

/-- **Glue (prop-ts §4.1 step 1): unramified in codimension one at the section `X = s₀` over
`p`.** Let `E/ℚ(X)` be finite with `[E : ℚ(X)] < p`, no vertical ramification at `p`, and let
`s₀ = a/d` be `p`-integral and meet no branch point mod `p` (`NonMeeting`). Let `m ⊂ ℤ[X]` be the
maximal ideal containing `p` and `dX − a` (it is `(p, dX − a)`). Then every height-one prime `P`
of `R = ℤ[X]_m` is unramified in the integral closure of `R` in `E`. Proof: `P = (p)` is handled
by `NoVerticalRam` (`e = 1`) and `[E : ℚ(X)] < p` (separable residue extension: the inseparable
degree is a power of `p` dividing `f ≤ [E : ℚ(X)]`); `P = (g)`, `g` primitive irreducible with
`g ∈ m`: a ramified prime over `gℚ[X]` would give, by `NonMeeting`, a `p`-integral `f ∈ gℚ[X]`
with `f(s₀)` a unit, while Gauss's lemma gives `f = g h` with `h ∈ ℤ_(p)[X]`, so `p ∣ f(s₀)`;
residue fields of horizontal primes have characteristic 0. -/
def SNHeightOne : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ), p.Prime →
    Module.finrank (RatFunc ℚ) E < p → NoVerticalRam E p →
    ∀ s₀ : ℚ, 0 ≤ padicValRat p s₀ → NonMeeting E p s₀ →
    ∀ (m : Ideal ℤ[X]) [m.IsMaximal], C (p : ℤ) ∈ m → C (s₀.den : ℤ) * X - C s₀.num ∈ m →
      letI := locAlg E m
      ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 →
        Algebra.IsUnramifiedIn (integralClosure (Localization.AtPrime m) E) P

/-- **Glue (prop-ts §4.1 step 3): specializing an étale cover along the section `X = s₀`.** With
`m ∋ p, dX − a` as in `SNHeightOne`, if the integral closure `S` of `R = ℤ[X]_m` in `E` is étale
over `R`, then every residue field `B/𝔓` of the integral closure `B` of `ℚ[X]` in `E` over
`X − s₀`, embedded in `ℚ̄`, is a number field unramified at `p`. Proof: `S/(dX − a)S` is étale over
`R/(dX − a) = ℤ_(p)`, hence a finite product of finite étale `ℤ_(p)`-domains; the factor through
`𝔓` (every `𝔓` survives: going up from `ℤ[1/d]` to the closure of `𝔓`) has fraction field
`B/𝔓`, which is therefore unramified at `p` (Neukirch I.8; étale over a DVR = unramified with
separable residue fields). -/
def SNSpecialize : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ), p.Prime →
    ∀ s₀ : ℚ, 0 ≤ padicValRat p s₀ →
    ∀ (m : Ideal ℤ[X]) [m.IsMaximal], C (p : ℤ) ∈ m → C (s₀.den : ℤ) * X - C s₀.num ∈ m →
      letI := locAlg E m
      Algebra.Etale (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C s₀} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
          FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range φ)) ∧
          UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p

/-- A `p`-integral rational has denominator prime to `p`. -/
theorem not_dvd_den_of_nonneg (p : ℕ) [hp : Fact p.Prime] (s : ℚ) (hs : 0 ≤ padicValRat p s) :
    ¬ p ∣ s.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ s.num := by
    intro hn
    have h1 : p ∣ s.num.natAbs := Int.natCast_dvd.mp hn
    exact hp.out.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h1 s.reduced).eq_one_of_dvd hd)
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum] at hs
  have := one_le_padicValNat_of_dvd s.den_nz hd
  omega

/-- **The maximal ideal `(p, dX − a)` of `ℤ[X]` exists** for `p`-integral `s₀ = a/d`: the kernel
of `ℤ[X] → 𝔽_p`, `X ↦ a d⁻¹`. -/
theorem exists_secIdeal (p : ℕ) [hp : Fact p.Prime] (s₀ : ℚ) (hs : 0 ≤ padicValRat p s₀) :
    ∃ m : Ideal ℤ[X], m.IsMaximal ∧ C (p : ℤ) ∈ m ∧ C (s₀.den : ℤ) * X - C s₀.num ∈ m := by
  have hd : ((s₀.den : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact not_dvd_den_of_nonneg p s₀ hs
  let f : ℤ[X] →+* ZMod p := Polynomial.eval₂RingHom (Int.castRingHom (ZMod p))
    ((s₀.num : ZMod p) * ((s₀.den : ℤ) : ZMod p)⁻¹)
  refine ⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f ?_, ?_, ?_⟩
  · intro z
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨C n, by simp [f]⟩
  · rw [RingHom.mem_ker]
    simp [f]
  · rw [RingHom.mem_ker]
    simp only [f, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
    simp only [eq_intCast]
    rw [mul_left_comm, mul_inv_cancel₀ hd, mul_one, sub_self]

/-- **`SpecNonMeeting` from purity (proved by t-purity3) and the three commutative-algebra
pieces.** The base `ℤ[X]_m` is regular local of dimension 2 (`regular_dim2_intPoly`, proved). -/
theorem specNonMeeting_of_pieces (hPur : PurityGlobalDim2.{0}) (hL : SNLocalData)
    (hH : SNHeightOne) (hS : SNSpecialize) : SpecNonMeeting := by
  intro E _ _ _ _ _ p hp hdeg hV s₀ hs₀ hNM 𝔓 hP𝔓 hU φ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hmax, hpm, hsm⟩ := exists_secIdeal p s₀ hs₀
  letI := locAlg E m
  obtain ⟨hic, hfin, hinj⟩ := hL E m
  have hne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥ := by
    intro h0
    have : (p : ℤ) ∈ m.comap (C : ℤ →+* ℤ[X]) := hpm
    rw [h0, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  obtain ⟨hreg, hdim⟩ := regular_dim2_intPoly m hne
  have het := hPur (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) hdim hinj
    (hH E p hp hdeg hV s₀ hs₀ hNM m hpm hsm)
  exact hS E p hp s₀ hs₀ m hpm hsm het 𝔓 hP𝔓 hU φ

/-- **`SpecNonMeeting` from purity (proved by t-purity3) and the two remaining pieces**
(`SNLocalData` is proved: `snLocalData`). -/
theorem specNonMeeting_of_pieces' (hPur : PurityGlobalDim2.{0}) (hH : SNHeightOne)
    (hS : SNSpecialize) : SpecNonMeeting :=
  specNonMeeting_of_pieces hPur snLocalData hH hS

/-- **Clearing `p`-integral denominators**: a polynomial with `p`-integral coefficients times an
integer `N` prime to `p` has integer coefficients. -/
theorem exists_int_multiple (p : ℕ) [hp : Fact p.Prime] (f : ℚ[X])
    (hf : ∀ i, 0 ≤ padicValRat p (f.coeff i)) :
    ∃ N : ℤ, ¬ (p : ℤ) ∣ N ∧ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = C (N : ℚ) * f := by
  refine ⟨∏ i ∈ f.support, ((f.coeff i).den : ℤ), ?_, ?_⟩
  · intro hdvd
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hpr _).mp hdvd
    exact not_dvd_den_of_nonneg p _ (hf i) (Int.natCast_dvd_natCast.mp hi)
  · rw [← mem_lifts, lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    by_cases hn : n ∈ f.support
    · obtain ⟨M', hM'⟩ := Finset.dvd_prod_of_mem (fun i => ((f.coeff i).den : ℤ)) hn
      refine ⟨M' * (f.coeff n).num, ?_⟩
      simp only [eq_intCast, Int.cast_mul]
      rw [hM', Int.cast_mul, ← Rat.den_mul_eq_num]
      push_cast
      ring
    · rw [notMem_support_iff.mp hn, mul_zero]
      exact ⟨0, by simp⟩

/-- `C n ∉ m` when `C p ∈ m` and `p ∤ n` (`m` proper). -/
theorem C_notMem (p : ℕ) [hp : Fact p.Prime] (m : Ideal ℤ[X]) (hm : m ≠ ⊤)
    (hpm : C (p : ℤ) ∈ m) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : C n ∉ m := by
  intro hnm
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨α, β, h⟩ := (Prime.coprime_iff_not_dvd hpr).mpr hn
  apply hm
  rw [Ideal.eq_top_iff_one]
  have : C (α * p + β * n) ∈ m := by
    rw [map_add, map_mul, map_mul]
    exact m.add_mem (m.mul_mem_left _ hpm) (m.mul_mem_left _ hnm)
  rwa [h, map_one] at this

/-- **Reduction mod `(p, dX − a)`**: `d^k F ≡ Σ c_i a^i d^{k−i}` modulo any ideal containing
`dX − a` (`k = deg F`). -/
theorem homog_mem (m : Ideal ℤ[X]) (a d : ℤ) (hm : C d * X - C a ∈ m) (F : ℤ[X]) :
    C (d ^ F.natDegree) * F -
      C (∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * a ^ i * d ^ (F.natDegree - i)) ∈ m := by
  set k := F.natDegree
  have hF : F = ∑ i ∈ Finset.range (k + 1), C (F.coeff i) * X ^ i := as_sum_range_C_mul_X_pow F
  nth_rw 1 [hF]
  rw [Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e : C (d ^ k) * (C (F.coeff i) * X ^ i) - C (F.coeff i * a ^ i * d ^ (k - i)) =
      C (F.coeff i * d ^ (k - i)) * ((C d * X) ^ i - C a ^ i) := by
    rw [show d ^ k = d ^ (k - i) * d ^ i by rw [← pow_add, Nat.sub_add_cancel hik]]
    simp only [map_mul, map_pow]
    ring
  rw [e]
  apply m.mul_mem_left
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (C d * X) (C a) i
  rw [hq]
  exact m.mul_mem_right _ hm

/-- **A polynomial `F ∈ ℤ[X]` with `F(s₀)` a `p`-adic unit is not in `m`**, for any proper
ideal `m` containing `p` and `dX − a` (`s₀ = a/d`). -/
theorem notMem_of_val_zero (p : ℕ) [hp : Fact p.Prime] (s₀ : ℚ) (hs₀ : 0 ≤ padicValRat p s₀)
    (m : Ideal ℤ[X]) (hm : m ≠ ⊤) (hpm : C (p : ℤ) ∈ m)
    (hsm : C (s₀.den : ℤ) * X - C s₀.num ∈ m) (F : ℤ[X])
    (hne : (F.map (Int.castRingHom ℚ)).eval s₀ ≠ 0)
    (hval : padicValRat p ((F.map (Int.castRingHom ℚ)).eval s₀) = 0) : F ∉ m := by
  intro hF
  set k := F.natDegree
  set d : ℤ := (s₀.den : ℤ) with hd
  set n₀ : ℤ := ∑ i ∈ Finset.range (k + 1), F.coeff i * s₀.num ^ i * d ^ (k - i)
  have hd0 : (d : ℚ) ≠ 0 := by simp [d]
  have hrel : (n₀ : ℚ) = (d : ℚ) ^ k * (F.map (Int.castRingHom ℚ)).eval s₀ := by
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective (RingHom.injective_int _), Finset.mul_sum]
    simp only [n₀, Int.cast_sum, Int.cast_mul, Int.cast_pow, coeff_map, eq_intCast]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hs : (s₀.num : ℚ) = (d : ℚ) * s₀ := by simp [d]
    rw [hs, show (d : ℚ) ^ k = (d : ℚ) ^ (k - i) * (d : ℚ) ^ i by
      rw [← pow_add, Nat.sub_add_cancel hik]]
    ring
  have hn₀ : ¬ (p : ℤ) ∣ n₀ := by
    intro hdvd
    have hn0 : (n₀ : ℚ) ≠ 0 := by rw [hrel]; exact mul_ne_zero (pow_ne_zero _ hd0) hne
    have hdv : padicValRat p (d : ℚ) = 0 := by
      rw [show (d : ℚ) = ((s₀.den : ℕ) : ℚ) by simp [d], ← padicValRat_of_nat,
        padicValNat.eq_zero_of_not_dvd (not_dvd_den_of_nonneg p s₀ hs₀)]
      rfl
    have hv : padicValRat p (n₀ : ℚ) = 0 := by
      rw [hrel, padicValRat.mul (pow_ne_zero _ hd0) hne, padicValRat.pow, hdv, hval]
      simp
    rw [padicValRat.of_int] at hv
    have hn0' : n₀ ≠ 0 := by exact_mod_cast hn0
    have := padicValInt_dvd_iff (p := p) 1 n₀
    simp only [pow_one] at this
    have hv' : padicValInt p n₀ = 0 := by exact_mod_cast hv
    rw [hv'] at this
    have h2 := this.mp hdvd
    rcases h2 with h2 | h2
    · exact hn0' h2
    · omega
  apply C_notMem p m hm hpm n₀ hn₀
  have h1 : C (d ^ k) * F - C n₀ ∈ m := homog_mem m s₀.num d hsm F
  have h2 : C (d ^ k) * F ∈ m := m.mul_mem_left _ hF
  have := m.sub_mem h2 h1
  rwa [sub_sub_cancel] at this

/-- **Glue (prop-ts §4.1 step 1, the vertical prime `(p)`).** With the hypotheses of
`SNHeightOne`, a height-one prime `P` of `ℤ[X]_m` containing `p` (it is `pℤ[X]_m`) is unramified
in the integral closure of `ℤ[X]_m` in `E`: `NoVerticalRam` gives `e = 1` at the primes of the
integral closure of `ℤ[X]` over `pℤ[X]` (their local rings are those over `P`), and
`[E : ℚ(X)] < p` makes the residue extensions separable. -/
def SNVertical : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ), p.Prime →
    Module.finrank (RatFunc ℚ) E < p → NoVerticalRam E p →
    ∀ s₀ : ℚ, 0 ≤ padicValRat p s₀ →
    ∀ (m : Ideal ℤ[X]) [m.IsMaximal], C (p : ℤ) ∈ m → C (s₀.den : ℤ) * X - C s₀.num ∈ m →
      letI := locAlg E m
      ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 →
        algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∈ P →
        Algebra.IsUnramifiedIn (integralClosure (Localization.AtPrime m) E) P

/-- **Glue (localization of primes; char 0): a ramified horizontal height-one prime of `ℤ[X]_m`
comes from a ramified prime of `B`.** Let `P` be a height-one prime of `R = ℤ[X]_m` with
`p ∉ P` and `P` ramified in the integral closure `S` of `R` in `E`. Then some prime `Q` of the
integral closure `B` of `ℚ[X]` in `E` has `e(Q) ≠ 1`, and every `F ∈ ℤ[X]` lying in `Q` lies in
`P`. Proof: take `Q'` over `P` with `S_{Q'}` ramified over `R_P = ℚ[X]_{(g)}` (`P ∩ ℤ = 0` as
`p ∉ P`, so `ℚ ⊆ S_{Q'}` and `B ⊆ S_{Q'}`); `Q` = the maximal ideal of `S_{Q'}` intersected with
`B`; then `B_Q = S_{Q'}`, `e(Q)` is the length of `S_{Q'}/g S_{Q'}`, which is `≠ 1` by Mathlib's
`Ideal.ramificationIdx_eq_one_iff` (residue fields of characteristic 0); `F ∈ Q` gives
`F ∈ Q'S_{Q'} ∩ R = P`. -/
def SNHorizontalTransfer : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ), p.Prime →
    ∀ (m : Ideal ℤ[X]) [m.IsMaximal], C (p : ℤ) ∈ m →
      letI := locAlg E m
      ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 →
        algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∉ P →
        ¬ Algebra.IsUnramifiedIn (integralClosure (Localization.AtPrime m) E) P →
        ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧ Q.ramificationIdx ℚ[X] ≠ 1 ∧
          ∀ F : ℤ[X], F.map (Int.castRingHom ℚ) ∈ Q.under ℚ[X] →
            algebraMap ℤ[X] (Localization.AtPrime m) F ∈ P

/-- **`SNHeightOne` from the vertical piece and the horizontal transfer** (compiled). The
horizontal case is the Gauss-lemma argument of prop-ts §4.1, done here without Gauss's lemma:
`NonMeeting` gives `f ∈ Q ∩ ℚ[X]` with `p`-integral coefficients and `f(s₀)` a `p`-unit;
`N f = F ∈ ℤ[X]` with `p ∤ N` (`exists_int_multiple`); `F ∉ m` (`notMem_of_val_zero`), so `F` is
a unit of `ℤ[X]_m`, while the transfer puts it in the proper ideal `P`. -/
theorem snHeightOne_of_pieces (hV : SNVertical) (hT : SNHorizontalTransfer) : SNHeightOne := by
  intro E _ _ _ _ _ p hp hdeg hNV s₀ hs₀ hNM m _ hpm hsm P hP hP1
  by_cases hpP : algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∈ P
  · exact hV E p hp hdeg hNV s₀ hs₀ m hpm hsm P hP hP1 hpP
  · by_contra hnot
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨Q, hQ, he, hQP⟩ := hT E p hp m hpm P hP hP1 hpP hnot
    obtain ⟨f, hfQ, hcoef, hne, hval⟩ := hNM Q hQ he
    obtain ⟨N, hN, F, hF⟩ := exists_int_multiple p f hcoef
    have hFQ : F.map (Int.castRingHom ℚ) ∈ Q.under ℚ[X] := by
      rw [hF]
      exact Ideal.mul_mem_left _ _ hfQ
    have hFP := hQP F hFQ
    have hNq : (N : ℚ) ≠ 0 := by
      intro h
      apply hN
      rw [Int.cast_eq_zero.mp h]
      exact dvd_zero _
    have hevF : (F.map (Int.castRingHom ℚ)).eval s₀ = N * f.eval s₀ := by
      rw [hF, eval_mul, eval_C]
    have hNv : padicValRat p (N : ℚ) = 0 := by
      rw [padicValRat.of_int]
      exact_mod_cast padicValInt.eq_zero_of_not_dvd hN
    have hFm : F ∉ m := notMem_of_val_zero p s₀ hs₀ m (Ideal.IsMaximal.ne_top ‹_›) hpm hsm F
      (by rw [hevF]; exact mul_ne_zero hNq hne)
      (by rw [hevF, padicValRat.mul hNq hne, hNv, hval]; simp)
    have hu : IsUnit (algebraMap ℤ[X] (Localization.AtPrime m) F) :=
      IsLocalization.map_units (Localization.AtPrime m) (⟨F, hFm⟩ : m.primeCompl)
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hFP hu)

/-- **`SpecNonMeeting` from purity (proved by t-purity3), `SNVertical`, `SNHorizontalTransfer`
and `SNSpecialize`** (`SNLocalData` and the horizontal arithmetic are proved). -/
theorem specNonMeeting_of_pieces'' (hPur : PurityGlobalDim2.{0}) (hV : SNVertical)
    (hT : SNHorizontalTransfer) (hS : SNSpecialize) : SpecNonMeeting :=
  specNonMeeting_of_pieces' hPur (snHeightOne_of_pieces hV hT) hS

/-! ## Part B: `KummerMeetGlue` from the Kummer compositum, Abhyankar (T2) and two ramification
facts -/

/-- **`E'` is the compositum `E(s)` along `X ↦ r(s)`**: a field embedding `ι : E → E'` sending the
coordinate `X` of `ℚ(X) ⊆ E` to `r ∈ ℚ(s) ⊆ E'` (`s` the coordinate of the second `RatFunc ℚ`),
with `E'` generated as a field by `ι(E)` and `s`. -/
def KummerShape (E E' : Type) [Field E] [Field E'] [Algebra (RatFunc ℚ) E]
    [Algebra (RatFunc ℚ) E'] (ι : E →+* E') (r : RatFunc ℚ) : Prop :=
  ι (algebraMap (RatFunc ℚ) E RatFunc.X) = algebraMap (RatFunc ℚ) E' r ∧
    Subfield.closure (Set.range ι ∪ {algebraMap (RatFunc ℚ) E' RatFunc.X}) = ⊤

/-- The Kummer substitution at a finite branch point: `X = b + s^n / c`, i.e. `s^n = c (X − b)`. -/
def rFin (b c : ℚ) (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C (b * c) + X ^ n) / algebraMap ℚ[X] (RatFunc ℚ) (C c)

/-- The Kummer substitution at `∞`: `X = c / s^n`, i.e. `s^n = c / X`. -/
def rInf (c : ℚ) (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C c) / algebraMap ℚ[X] (RatFunc ℚ) (X ^ n)

/-- **Glue (algebra; STANDARD): the compositum exists, with a prime over a given prime.** Let
`E/ℚ(X)` be finite and `r = P/Q ∈ ℚ(s)` non-constant, regular at `s₀ ∈ ℚ` with `r(s₀) = t`. For
every prime `𝔓` of the integral closure `B` of `ℚ[X]` in `E` over `X − t` and every embedding
`φ : B/𝔓 → ℚ̄` there are a field `E'` finite over `ℚ(s)` which is a compositum `E(s)` along
`X ↦ r` (a factor of `E ⊗_{ℚ(X)} ℚ(s)`), so `[E' : ℚ(s)] ≤ [E : ℚ(X)]`, a prime `𝔓'` of the
integral closure of `ℚ[s]` in `E'` over `s − s₀`, and an embedding `φ'` of its residue field with
`ℚ(φ(B/𝔓)) ⊆ ℚ(φ'(B'/𝔓'))`. Proof: every valuation of `E` over `X = t` extends to some factor
of `E ⊗ ℚ(s)` above the valuation `s = s₀` of `ℚ(s)` (which restricts to `X = t` on `ℚ(X)`), and
`φ` extends to the finite extension of residue fields as `ℚ̄` is algebraically closed. -/
def KummerCompositum : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (P Q : ℚ[X]) (t s₀ : ℚ), Q.eval s₀ ≠ 0 → P.eval s₀ = t * Q.eval s₀ → (∀ a : ℚ, P ≠ C a * Q) →
    ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime → 𝔓.under ℚ[X] = Ideal.span {X - C t} →
    ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
    ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
      (ι : E →+* E'),
      KummerShape E E' ι (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) ∧
      Module.finrank (RatFunc ℚ) E' ≤ Module.finrank (RatFunc ℚ) E ∧
      ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
        𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
        ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* Qbar,
          IntermediateField.adjoin ℚ (Set.range φ) ≤ IntermediateField.adjoin ℚ (Set.range φ')

/-- **Glue from T2 (Abhyankar's lemma), finite branch point.** If `E' = E(s)` with
`s^n = c (X − b)` (`c ≠ 0`) and every prime of `B` over `X − b` has ramification index dividing
`n`, then `E'/ℚ(s)` is unramified over `s = 0`. Proof: T2 (`PkgI2.AbhyankarDVR`) for the DVR
`ℚ[X]_(X−b)` with uniformizer `c (X − b) = s^n` gives `e = n` over `X = b` for every prime of
`E'`; `ℚ(s)/ℚ(X)` is totally ramified of index `n` at `s = 0`, and `e` is multiplicative in
towers. -/
def KummerAbhyankarFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (b c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rFin b c n) →
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = Ideal.span {X - C b} →
      Q.ramificationIdx ℚ[X] ∣ n) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.under ℚ[X] = Ideal.span {X} →
      Q'.ramificationIdx ℚ[X] = 1

/-- `KummerAbhyankarFin` is glue whose proof uses the bundle leaf T2. -/
def KummerAbhyankarFinGlue : Prop := PkgI2.AbhyankarDVR.{0} → KummerAbhyankarFin

/-- **Glue (ramification in a compositum), finite branch point.** If `E' = E(s)` with
`s^n = c (X − b)`, `b ∈ S` and `E/ℚ(X)` is unramified over every finite prime other than the
`X − b'` (`b' ∈ S`), then a ramified prime of `E'/ℚ(s)` lies over `s = 0` or contains
`s^n − c (b' − b)` for some `b' ∈ S ∖ {b}`. Proof: over a prime `g` of `ℚ[s]` with
`g ∩ ℚ[X] = h`: if `h = (X − b)` then `g = (s)`; if `h = (X − b')` then `s^n − c(b' − b) ∈ g`;
otherwise `E` and `ℚ(s)` are both unramified over `h` (`ℚ(s)/ℚ(X)` ramifies only over `b` and
`∞`), hence so is the compositum. -/
def KummerOtherBranchFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (b c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rFin b c n) →
    ∀ S : Finset ℚ, b ∈ S →
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime →
      (∀ b' ∈ S, Q.under ℚ[X] ≠ Ideal.span {X - C b'}) → Q.ramificationIdx ℚ[X] = 1) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.ramificationIdx ℚ[X] ≠ 1 →
      Q'.under ℚ[X] = Ideal.span {X} ∨
        ∃ b' ∈ S, b' ≠ b ∧ X ^ n - C (c * (b' - b)) ∈ Q'.under ℚ[X]

/-- **Glue (Gauss valuation), finite branch point.** If `E' = E(s)` with `s^n = c (X − b)`,
`0 < n < p`, `c` a `p`-unit, `b` `p`-integral, `[E : ℚ(X)] < p`, and `E` has no vertical
ramification at `p`, then neither has `E'`. Proof: the Gauss valuation of `ℚ(s)` restricts to the
Gauss valuation of `ℚ(X)` (the substitution `X ↦ b + s^n/c` is injective mod `p`), with `e = 1`
and residue extension `𝔽_p(s)/𝔽_p(X̄)` separable of degree `n < p`; the vertical primes of `E` are
unramified with separable residue fields (`[E : ℚ(X)] < p`); a compositum of extensions unramified
at a valuation is unramified there. -/
def KummerVerticalFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (b c : ℚ) (n : ℕ) (p : ℕ), p.Prime → 0 < n → n < p →
    Module.finrank (RatFunc ℚ) E < p → c ≠ 0 → padicValRat p c = 0 → 0 ≤ padicValRat p b →
    KummerShape E E' ι (rFin b c n) → NoVerticalRam E p → NoVerticalRam E' p

/-- **`KummerMeet`, finite case**: `KummerMeet` when `t` meets a finite branch point `b ∈ S`. -/
def KummerMeetFin : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf →
    Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 < n b ∧ n b < p) → 0 < nInf → nInf < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    NoVerticalRam E p →
    ∀ t : ℚ, t ∉ S →
      (∀ b ∈ S, n b ∣ (padicValRat p (t - b)).toNat) → nInf ∣ (-padicValRat p t).toNat →
      (∃ b ∈ S, 0 < padicValRat p (t - b)) →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C t} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
          (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
          (s₀ : ℚ), Module.finrank (RatFunc ℚ) E' < p ∧ NoVerticalRam E' p ∧
          0 ≤ padicValRat p s₀ ∧ NonMeeting E' p s₀ ∧
          ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
            𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
            ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* Qbar,
              IntermediateField.adjoin ℚ (Set.range φ) ≤
                IntermediateField.adjoin ℚ (Set.range φ')

/-- **`KummerMeet`, case at `∞`**: `KummerMeet` when `v_p(t) < 0` (glue from T2 at the DVR of `∞`,
substitution `rInf`: `X = c/s^n`; prop-ts §4.2, second case). -/
def KummerMeetInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (S : Finset ℚ) (n : ℚ → ℕ) (nInf : ℕ) (p : ℕ), p.Prime →
    BranchData E S n nInf →
    Module.finrank (RatFunc ℚ) E < p →
    (∀ b ∈ S, 0 < n b ∧ n b < p) → 0 < nInf → nInf < p →
    (∀ b ∈ S, 0 ≤ padicValRat p b) →
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → padicValRat p (b - b') = 0) →
    NoVerticalRam E p →
    ∀ t : ℚ, t ∉ S →
      (∀ b ∈ S, n b ∣ (padicValRat p (t - b)).toNat) → nInf ∣ (-padicValRat p t).toNat →
      padicValRat p t < 0 →
      ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
        𝔓.under ℚ[X] = Ideal.span {X - C t} →
        ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar,
        ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
          (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
          (s₀ : ℚ), Module.finrank (RatFunc ℚ) E' < p ∧ NoVerticalRam E' p ∧
          0 ≤ padicValRat p s₀ ∧ NonMeeting E' p s₀ ∧
          ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
            𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
            ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* Qbar,
              IntermediateField.adjoin ℚ (Set.range φ) ≤
                IntermediateField.adjoin ℚ (Set.range φ')

/-- `KummerMeet` splits into its two cases (compiled). -/
theorem kummerMeet_of_cases (hF : KummerMeetFin) (hI : KummerMeetInf) : KummerMeet := by
  intro E _ _ _ _ _ _ S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf hm 𝔓 hP hU φ
  rcases hm with hm | hm
  · exact hI E S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf hm 𝔓 hP hU φ
  · exact hF E S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf hm 𝔓 hP hU φ

/-- `p`-adic valuation of `X^n − C a` coefficients: all `≥ 0` when `v_p(a) ≥ 0`. -/
theorem coeff_X_pow_sub_C_nonneg (p : ℕ) (n : ℕ) (hn : 0 < n) (a : ℚ)
    (ha : 0 ≤ padicValRat p a) (i : ℕ) : 0 ≤ padicValRat p ((X ^ n - C a : ℚ[X]).coeff i) := by
  rw [coeff_sub, coeff_X_pow, coeff_C]
  by_cases h1 : i = n
  · subst h1
    simp [hn.ne']
  · by_cases h0 : i = 0
    · subst h0
      simp only [if_neg h1, if_true, zero_sub, padicValRat.neg]
      exact ha
    · simp [h1, h0]

/-- **`KummerMeetFin` from the four pieces** (compiled; the `p`-adic bookkeeping of prop-ts §4.2:
`t − b = p^M u`, `c = u^{n−1}`, `s₀ = p^{M/n} u`, so `s₀^n = c (t − b)`). -/
theorem kummerMeetFin_of_pieces (hC : KummerCompositum) (hA : KummerAbhyankarFin)
    (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin) : KummerMeetFin := by
  intro E _ _ _ _ _ _ S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf hm 𝔓 hP hU φ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hbS, hpos⟩ := hm
  have htb : t - b ≠ 0 := sub_ne_zero.mpr (fun e => ht (e ▸ hbS))
  set M : ℕ := (padicValRat p (t - b)).toNat with hMdef
  have hM : padicValRat p (t - b) = (M : ℤ) := by rw [hMdef]; omega
  obtain ⟨hnb0, hnbp⟩ := hn0 b hbS
  set nb := n b with hnb
  obtain ⟨k, hk⟩ : nb ∣ M := hn b hbS
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := (t - b) / (p : ℚ) ^ M with hu
  have hu0 : u ≠ 0 := div_ne_zero htb (pow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.div htb (pow_ne_zero _ hp0), padicValRat.pow, padicValRat.self hp.one_lt,
      hM]
    ring
  set c : ℚ := u ^ (nb - 1) with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ hu0
  have hvc : padicValRat p c = 0 := by rw [hc, padicValRat.pow, hvu, mul_zero]
  set s₀ : ℚ := (p : ℚ) ^ k * u with hs₀
  have hs₀n : s₀ ^ nb = c * (t - b) := by
    have e1 : t - b = (p : ℚ) ^ M * u := by rw [hu]; field_simp
    rw [hs₀, hc, e1, hk, mul_pow, ← pow_mul, mul_comm k nb]
    obtain ⟨j, hj⟩ : ∃ j, nb = j + 1 := ⟨nb - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, pow_succ]
    ring
  have hvs₀ : 0 ≤ padicValRat p s₀ := by
    rw [hs₀, padicValRat.mul (pow_ne_zero _ hp0) hu0, padicValRat.pow, padicValRat.self hp.one_lt,
      hvu]
    simp
  -- the compositum
  have hQ : (C c : ℚ[X]).eval s₀ ≠ 0 := by simpa using hc0
  have hPQ : (C (b * c) + X ^ nb : ℚ[X]).eval s₀ = t * (C c : ℚ[X]).eval s₀ := by
    simp only [eval_add, eval_C, eval_pow, eval_X]
    rw [hs₀n]
    ring
  have hnc : ∀ a : ℚ, (C (b * c) + X ^ nb : ℚ[X]) ≠ C a * C c := by
    intro a h
    have := congrArg (fun f : ℚ[X] => f.coeff nb) h
    simp only [coeff_add, coeff_C, coeff_X_pow, if_true, ← C_mul] at this
    rw [if_neg (by omega), if_neg (by omega)] at this
    simp at this
  obtain ⟨E', i1, i2, i3, i4, i5, ι, hshape, hdeg', 𝔓', hP', hU', φ', hle⟩ :=
    hC E (C (b * c) + X ^ nb) (C c) t s₀ hQ hPQ hnc 𝔓 hP hU φ
  have hshape' : KummerShape E E' ι (rFin b c nb) := hshape
  refine ⟨E', i1, i2, i3, i4, i5, s₀, lt_of_le_of_lt hdeg' hdeg,
    hVF E E' ι b c nb p hp hnb0 hnbp hdeg hc0 hvc (hint b hbS) hshape' hV, hvs₀, ?_,
    𝔓', hP', hU', φ', hle⟩
  -- `NonMeeting E' p s₀`
  intro Q' hQ' he
  rcases hO E E' ι b c nb hnb0 hc0 hshape' S hbS hBr.1 Q' hQ' he with h0 | ⟨b', hb'S, hb'b, hmem⟩
  · exact absurd (hA E E' ι b c nb hnb0 hc0 hshape' (hBr.2.1 b hbS) Q' hQ' h0) he
  · have hbb' : b' - b ≠ 0 := sub_ne_zero.mpr hb'b
    have htb' : t - b' ≠ 0 := sub_ne_zero.mpr (fun e => ht (e ▸ hb'S))
    have hv1 : padicValRat p (b' - b) = 0 := hdist b' hb'S b hbS hb'b
    have hval : padicValRat p (t - b') = 0 := by
      have hbb'' : b - b' ≠ 0 := sub_ne_zero.mpr (Ne.symm hb'b)
      have e2 : t - b' = (b - b') + (t - b) := by ring
      have hv2 : padicValRat p (b - b') = 0 := hdist b hbS b' hb'S (Ne.symm hb'b)
      rw [e2, padicValRat.add_eq_of_lt (by rw [← e2]; exact htb') hbb'' htb (by rw [hv2]; omega),
        hv2]
    refine ⟨X ^ nb - C (c * (b' - b)), hmem, ?_, ?_, ?_⟩
    · apply coeff_X_pow_sub_C_nonneg p nb hnb0
      rw [padicValRat.mul hc0 hbb', hvc, hv1]
      simp
    · simp only [eval_sub, eval_pow, eval_X, eval_C]
      rw [hs₀n, show c * (t - b) - c * (b' - b) = c * (t - b') by ring]
      exact mul_ne_zero hc0 htb'
    · simp only [eval_sub, eval_pow, eval_X, eval_C]
      rw [hs₀n, show c * (t - b) - c * (b' - b) = c * (t - b') by ring,
        padicValRat.mul hc0 htb', hvc, hval]
      simp

/-- **`KummerMeetGlue` from the pieces**: T2 enters only through `KummerAbhyankarFinGlue` (and the
`∞` case `KummerMeetInf`, glue from T2 at the DVR of `∞`). -/
theorem kummerMeetGlue_of_pieces (hC : KummerCompositum) (hA : KummerAbhyankarFinGlue)
    (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hI : PkgI2.AbhyankarDVR.{0} → KummerMeetInf) : KummerMeetGlue :=
  fun t2 => kummerMeet_of_cases (kummerMeetFin_of_pieces hC (hA t2) hO hVF) (hI t2)


/-! ### The case at `∞` -/

/-- **Glue from T2 (Abhyankar's lemma), branch point `∞`.** If `E' = E(s)` with `s^n = c / X`
(`c ≠ 0`) and every prime of the integral closure of `ℚ[1/X]` in `E` over `1/X` has ramification
index dividing `n`, then `E'/ℚ(s)` is unramified over `s = 0`. Proof: T2 for the DVR
`ℚ[1/X]_(1/X)` with uniformizer `c · (1/X) = s^n`, and multiplicativity of `e`. -/
def KummerAbhyankarInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rInf c n) →
    (letI := infAlg E
      ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime →
        Q.under InfCoord = Ideal.span {infUnif} → Q.ramificationIdx InfCoord ∣ n) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.under ℚ[X] = Ideal.span {X} →
      Q'.ramificationIdx ℚ[X] = 1

/-- `KummerAbhyankarInf` is glue whose proof uses the bundle leaf T2. -/
def KummerAbhyankarInfGlue : Prop := PkgI2.AbhyankarDVR.{0} → KummerAbhyankarInf

/-- **Glue (ramification in a compositum), branch point `∞`.** If `E' = E(s)` with `s^n = c / X`
and `E/ℚ(X)` is unramified over every finite prime other than the `X − b'` (`b' ∈ S`), then a
ramified prime of `E'/ℚ(s)` lies over `s = 0` or contains `b' s^n − c` for some `b' ∈ S ∖ {0}`.
Proof: `ℚ(s)/ℚ(X)` ramifies only over `X = ∞` (`s = 0`) and `X = 0` (`s = ∞`, not a prime of
`ℚ[s]`); over `s = α ≠ 0` the point `X = c/α^n` is finite and nonzero, and the compositum is
ramified there only if `E` is, i.e. `c/α^n = b' ∈ S`. -/
def KummerOtherBranchInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (c : ℚ) (n : ℕ), 0 < n → c ≠ 0 → KummerShape E E' ι (rInf c n) →
    ∀ S : Finset ℚ,
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime →
      (∀ b' ∈ S, Q.under ℚ[X] ≠ Ideal.span {X - C b'}) → Q.ramificationIdx ℚ[X] = 1) →
    ∀ Q' : Ideal (integralClosure ℚ[X] E'), Q'.IsPrime → Q'.ramificationIdx ℚ[X] ≠ 1 →
      Q'.under ℚ[X] = Ideal.span {X} ∨
        ∃ b' ∈ S, b' ≠ 0 ∧ C b' * X ^ n - C c ∈ Q'.under ℚ[X]

/-- **Glue (Gauss valuation), branch point `∞`.** If `E' = E(s)` with `s^n = c / X`, `0 < n < p`,
`c` a `p`-unit, `[E : ℚ(X)] < p`, and `E` has no vertical ramification at `p`, then neither has
`E'`. Proof: for `f ∈ ℤ_(p)[X]` primitive of degree `d`, `s^{nd} f(c/s^n) ∈ ℤ_(p)[s]` is primitive
(the substitution is injective mod `p`), so the Gauss valuation of `ℚ(s)` restricts to that of
`ℚ(X)`, with `e = 1` and residue extension separable of degree `n < p`; then as in
`KummerVerticalFin`. -/
def KummerVerticalInf : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] [FiniteDimensional (RatFunc ℚ) E']
    (ι : E →+* E') (c : ℚ) (n : ℕ) (p : ℕ), p.Prime → 0 < n → n < p →
    Module.finrank (RatFunc ℚ) E < p → c ≠ 0 → padicValRat p c = 0 →
    KummerShape E E' ι (rInf c n) → NoVerticalRam E p → NoVerticalRam E' p

/-- **`KummerMeetInf` from the four pieces** (compiled; `t = p^{−M} u`, `c = u^{1−n}`,
`s₀ = p^{M/n} / u`, so `c / s₀^n = t`). -/
theorem kummerMeetInf_of_pieces (hC : KummerCompositum) (hA : KummerAbhyankarInf)
    (hO : KummerOtherBranchInf) (hVI : KummerVerticalInf) : KummerMeetInf := by
  intro E _ _ _ _ _ _ S n nInf p hp hBr hdeg hn0 hinf0 hinf1 hint hdist hV t ht hn hinf hm 𝔓 hP hU φ
  have : Fact p.Prime := ⟨hp⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hm
  set M : ℕ := (-padicValRat p t).toNat with hMdef
  have hM : padicValRat p t = -(M : ℤ) := by rw [hMdef]; omega
  obtain ⟨k, hk⟩ : nInf ∣ M := hinf
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := t * (p : ℚ) ^ M with hu
  have hu0 : u ≠ 0 := mul_ne_zero ht0 (pow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.mul ht0 (pow_ne_zero _ hp0), padicValRat.pow, padicValRat.self hp.one_lt,
      hM]
    ring
  set c : ℚ := (u ^ (nInf - 1))⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hu0)
  have hvc : padicValRat p c = 0 := by rw [hc, padicValRat.inv, padicValRat.pow, hvu]; simp
  set s₀ : ℚ := (p : ℚ) ^ k / u with hs₀
  have hs₀0 : s₀ ≠ 0 := div_ne_zero (pow_ne_zero _ hp0) hu0
  have hts : t * s₀ ^ nInf = c := by
    have e1 : t = u / (p : ℚ) ^ M := by rw [hu]; field_simp
    obtain ⟨j, hj⟩ : ∃ j, nInf = j + 1 := ⟨nInf - 1, by omega⟩
    rw [e1, hs₀, hc, hk, hj, Nat.add_sub_cancel, div_pow, ← pow_mul, mul_comm k (j + 1)]
    field_simp
    ring
  have hvs₀ : 0 ≤ padicValRat p s₀ := by
    rw [hs₀, padicValRat.div (pow_ne_zero _ hp0) hu0, padicValRat.pow, padicValRat.self hp.one_lt,
      hvu]
    simp
  have hQ : (X ^ nInf : ℚ[X]).eval s₀ ≠ 0 := by simpa using pow_ne_zero nInf hs₀0
  have hPQ : (C c : ℚ[X]).eval s₀ = t * (X ^ nInf : ℚ[X]).eval s₀ := by
    simp only [eval_C, eval_pow, eval_X]
    exact hts.symm
  have hnc : ∀ a : ℚ, (C c : ℚ[X]) ≠ C a * X ^ nInf := by
    intro a h
    have := congrArg (fun f : ℚ[X] => f.coeff 0) h
    simp only [coeff_C_zero, coeff_C_mul, coeff_X_pow] at this
    rw [if_neg (by omega), mul_zero] at this
    exact hc0 this
  obtain ⟨E', i1, i2, i3, i4, i5, ι, hshape, hdeg', 𝔓', hP', hU', φ', hle⟩ :=
    hC E (C c) (X ^ nInf) t s₀ hQ hPQ hnc 𝔓 hP hU φ
  have hshape' : KummerShape E E' ι (rInf c nInf) := hshape
  refine ⟨E', i1, i2, i3, i4, i5, s₀, lt_of_le_of_lt hdeg' hdeg,
    hVI E E' ι c nInf p hp hinf0 hinf1 hdeg hc0 hvc hshape' hV, hvs₀, ?_,
    𝔓', hP', hU', φ', hle⟩
  intro Q' hQ' he
  rcases hO E E' ι c nInf hinf0 hc0 hshape' S hBr.1 Q' hQ' he with h0 | ⟨b', hb'S, hb'0, hmem⟩
  · exact absurd (hA E E' ι c nInf hinf0 hc0 hshape' hBr.2.2 Q' hQ' h0) he
  · have hb't : b' - t ≠ 0 := sub_ne_zero.mpr (fun e => ht (e ▸ hb'S))
    have hval : padicValRat p (b' - t) = -(M : ℤ) := by
      have e2 : b' - t = -t + b' := by ring
      have hlt : padicValRat p (-t) < padicValRat p b' := by
        rw [padicValRat.neg, hM]
        have := hint b' hb'S
        have : (0 : ℤ) < M := by
          by_contra h0'
          have : M = 0 := by omega
          rw [this] at hM
          omega
        omega
      rw [e2, padicValRat.add_eq_of_lt (by rw [← e2]; exact hb't) (neg_ne_zero.mpr ht0) hb'0 hlt,
        padicValRat.neg, hM]
    have hev : (C b' * X ^ nInf - C c : ℚ[X]).eval s₀ = c * (b' - t) / t := by
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      rw [← hts]
      field_simp
    refine ⟨C b' * X ^ nInf - C c, hmem, ?_, ?_, ?_⟩
    · intro i
      rw [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C]
      by_cases h1 : i = nInf
      · subst h1
        rw [if_pos rfl, if_neg (by omega), mul_one, sub_zero]
        exact hint b' hb'S
      · rw [if_neg h1, mul_zero]
        by_cases h0 : i = 0
        · rw [if_pos h0, zero_sub, padicValRat.neg, hvc]
        · rw [if_neg h0, sub_zero, padicValRat.zero]
    · rw [hev]
      exact div_ne_zero (mul_ne_zero hc0 hb't) ht0
    · rw [hev, padicValRat.div (mul_ne_zero hc0 hb't) ht0, padicValRat.mul hc0 hb't, hvc, hval, hM]
      ring

/-- **`KummerMeetGlue` from the eight pieces**: T2 enters only through the two Abhyankar steps. -/
theorem kummerMeetGlue_of_pieces' (hC : KummerCompositum) (hAF : KummerAbhyankarFinGlue)
    (hOF : KummerOtherBranchFin) (hVF : KummerVerticalFin) (hAI : KummerAbhyankarInfGlue)
    (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf) : KummerMeetGlue :=
  kummerMeetGlue_of_pieces hC hAF hOF hVF (fun t2 => kummerMeetInf_of_pieces hC (hAI t2) hOI hVI)

/-! ## Part C: `CoverModelOfHecke` from three properties of the normalization chart -/

/-- **Glue (curve theory; h-b1 M1, M2, M8): the normalization chart of `Y₃ → P¹_j`.** A triple
with R1fp, R1hecke and R2fp has a finite Galois `E/ℚ(X)` such that `π⁻¹(𝔸¹) ≅ Spec B` (`B` the
integral closure of `ℚ[X]` in `E`) with `π = X` there (`NormalizationModel`). Proof sketch: `Y`
is a smooth proper curve, `ℚ`-irreducible (its two geometric components are conjugate over
`ℚ(√−3)`: `π₀ = ℤ̂^×/nrd(K₃) ≅ (ℤ/3)^×` with Galois acting through the cyclotomic character,
SPECULATIVE reading of Deligne's reciprocity on `π₀`); `π` is finite and invariant under the group
`Γ'` of R1hecke, whose orbits are the fibres (R2fp), so `ℚ(Y)/ℚ(j)` is Galois (Artin) and `Y`
is the normalization of `P¹` in `ℚ(Y)`. -/
def HeckeNormalization : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E)
      (_ : IsGalois (RatFunc ℚ) E), NormalizationModel Y π E

/-- **Glue from leaves (h-b1 M3): the degree.** For a triple as above and any `E` carrying the
normalization chart, `[E : ℚ(X)] ≤ 324` (it divides `|Γ'| = 144`). `NormalizationModel` pins `B`
(and so `E = Frac B`) up to isomorphism, so this is a property of the cover. -/
def HeckeDegree : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      Module.finrank (RatFunc ℚ) E ≤ 324

/-- **Glue from leaves (h-b1 M4; Baba–Granath §3.1 elliptic orders,
`RvNocm.ramification_eq_orbifold_order`): the branch data.** For a triple as above and any `E`
carrying the normalization chart, `E/ℚ(X)` is ramified at most over `0, −16/27, ∞` with indices
dividing `4, 2, 6`. -/
def HeckeBranch : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      BranchData E {0, -16 / 27} nY3 6

/-- **Glue (h-b1 §3, Lemma NV; uses R1rec through `residue_unramified_over_branch`, Abhyankar and
the `W`-quotient `X₆ → P¹_j`): no vertical ramification.** For a triple as above and any `E`
carrying the normalization chart, `E` has no vertical ramification at any prime `p > 324`. -/
def HeckeNoVertRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p → NoVerticalRam E p

/-- **`CoverModelOfHeckeN` from the four pieces** (compiled). -/
theorem coverModelOfHeckeN_of_pieces (hN : HeckeNormalization) (hD : HeckeDegree)
    (hB : HeckeBranch) (hV : HeckeNoVertRam) : CoverModelOfHeckeN := by
  intro Y Φ π h1 hh h2
  obtain ⟨E, i1, i2, i3, i4, i5, i6, hM⟩ := hN Y Φ π h1 hh h2
  exact ⟨E, i1, i2, i3, i4, i5, i6, hM, ⟨hD Y Φ π h1 hh h2 E hM, hB Y Φ π h1 hh h2 E hM⟩,
    hV Y Φ π h1 hh h2 E hM⟩

/-- **`CoverModelOfHecke` from the four pieces** (through prop-ts's
`functionFieldModel_of_normalization`, compiled). -/
theorem coverModelOfHecke_of_pieces (hN : HeckeNormalization) (hD : HeckeDegree)
    (hB : HeckeBranch) (hV : HeckeNoVertRam) : CoverModelOfHecke :=
  fun Y Φ π h1 hh h2 => coverModel_of_N (coverModelOfHeckeN_of_pieces hN hD hB hV Y Φ π h1 hh h2)

/-! ### Only one triple needs a cover model -/

/-- **`FunctionFieldModel` transfers along the comparison of triples** (`Pin.SameTripleMor`; the
argument of prop-ts's `propTS_transfer`). -/
theorem functionFieldModel_transfer {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : Pin.SameTripleMor Y Y' Φ Φ' π π') (E : Type) [Field E] [Algebra ℚ[X] E]
    (h : FunctionFieldModel Y π E) : FunctionFieldModel Y' π' E := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  intro t y' hπ'
  obtain ⟨𝔓, hP, hU, φ, hres⟩ := h t (y' ≫ g) ((hπ y').symm.trans hπ')
  exact ⟨𝔓, hP, hU, φ, (residueImage_comp_eq_of_pt g hΦ y').symm.trans hres⟩

/-- `CoverModel` transfers along the comparison of triples. -/
theorem coverModel_transfer {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : Pin.SameTripleMor Y Y' Φ Φ' π π') (h : CoverModel Y π) : CoverModel Y' π' := by
  obtain ⟨E, i1, i2, i3, i4, i5, i6, hM, hB, hV⟩ := h
  exact ⟨E, i1, i2, i3, i4, i5, i6, functionFieldModel_transfer hS E hM, hB, hV⟩

/-- **The witness form of `CoverModelOfHecke`** (glue): some triple satisfying the leaf clause
lists R1fp, R1hecke, R2fp has a cover model. (For the leaf's own triple from `R1R2fp_Y`.) -/
def CoverModelWitness : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π ∧ CoverModel Y π

/-- **`CoverModelOfHecke` from one witness** (compiled): with the kernel's `MobiusGlue` and the
bundle leaf `R1R2fp`, a cover model for one triple gives one for every triple. -/
theorem coverModelOfHecke_of_witness (hM : Pin.MobiusGlue) (hR : R1R2fp)
    (hW : CoverModelWitness) : CoverModelOfHecke := by
  obtain ⟨Y₀, Φ₀, π₀, h1, -, h2, hC⟩ := hW
  exact fun _ _ _ h1' _ h2' =>
    coverModel_transfer (Pin.sameTripleMor_of_mobius hM (Pin.cm_objects_of_R1R2fp hR) h1 h2 h1' h2')
      hC

/-! ### Sanity: the binders of the new Props are satisfiable by genuine objects -/

example (h : SNSpecialize) := h (RatFunc ℚ)
example (h : SNVertical) := h (RatFunc ℚ)
example (h : SNHorizontalTransfer) := h (RatFunc ℚ)
example (h : KummerCompositum) := h (RatFunc ℚ)
example (h : KummerAbhyankarFin) := h (RatFunc ℚ) (RatFunc ℚ) (RingHom.id _)
example (h : KummerOtherBranchFin) := h (RatFunc ℚ) (RatFunc ℚ) (RingHom.id _)
example (h : KummerVerticalFin) := h (RatFunc ℚ) (RatFunc ℚ) (RingHom.id _)

/-! ## Part D: the composite -/

/-- **`PropTSAll` from the bundle leaves T2 and `R1R2fp`, the kernel glue `MobiusGlue`, purity
(proved by t-purity3), and the smaller glue of Parts A-C.** -/
theorem propTSAll_of_pieces (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hPur : PurityGlobalDim2.{0}) (hVert : SNVertical) (hT : SNHorizontalTransfer)
    (hS : SNSpecialize) (hC : KummerCompositum) (hA : KummerAbhyankarFinGlue)
    (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin) (hAI : KummerAbhyankarInfGlue)
    (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf) (hN : HeckeNormalization)
    (hD : HeckeDegree) (hB : HeckeBranch) (hV : HeckeNoVertRam) :
    PropTSAll :=
  propTSAll_of_bundle_meet t2 hR (kummerMeetGlue_of_pieces' hC hA hO hVF hAI hOI hVI)
    (specNonMeeting_of_pieces'' hPur hVert hT hS) hM (coverModelOfHecke_of_pieces hN hD hB hV)

end PropTSGlue

end

#print axioms PropTSGlue.regular_dim2_intPoly
#print axioms PropTSGlue.zxMap_injective
#print axioms PropTSGlue.not_dvd_den_of_nonneg
#print axioms PropTSGlue.exists_secIdeal
#print axioms PropTSGlue.specNonMeeting_of_pieces
#print axioms PropTSGlue.isFractionRing_zx
#print axioms PropTSGlue.snLocalData
#print axioms PropTSGlue.specNonMeeting_of_pieces'
#print axioms PropTSGlue.exists_int_multiple
#print axioms PropTSGlue.notMem_of_val_zero
#print axioms PropTSGlue.snHeightOne_of_pieces
#print axioms PropTSGlue.specNonMeeting_of_pieces''
#print axioms PropTSGlue.kummerMeet_of_cases
#print axioms PropTSGlue.coeff_X_pow_sub_C_nonneg
#print axioms PropTSGlue.kummerMeetFin_of_pieces
#print axioms PropTSGlue.kummerMeetGlue_of_pieces
#print axioms PropTSGlue.kummerMeetInf_of_pieces
#print axioms PropTSGlue.kummerMeetGlue_of_pieces'
#print axioms PropTSGlue.coverModelOfHeckeN_of_pieces
#print axioms PropTSGlue.coverModelOfHecke_of_pieces
#print axioms PropTSGlue.propTSAll_of_pieces
#print axioms PropTSGlue.functionFieldModel_transfer
#print axioms PropTSGlue.coverModel_transfer
#print axioms PropTSGlue.coverModelOfHecke_of_witness
