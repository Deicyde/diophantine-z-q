import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Textbook.SkolemNoether

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
# The five Hecke Props, copied verbatim from `scratch/prop-ts-glue/PropTSGlue.lean`
(lines 3356-3442, Part C, with the two composition theorems; namespace `PropTSGlue` and its
`open` line kept)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace PropTSGlue

open Polynomial G0ModField PropTSRed
open scoped TensorProduct

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

/-- **Glue (SPECULATIVE input, h-b1 M10 style; split out on the reviewer's advice): `Y₃` is
`ℚ`-irreducible.** For a triple with R1fp, R1hecke and R2fp, the underlying space of `Y` is
irreducible. (`Y₃` has two geometric components, `π₀ = ℤ̂^×/nrd(K₃) ≅ (ℤ/3)^×`; they should be
conjugate over `ℚ(√−3)` by Deligne's reciprocity law on `π₀`. If this failed, `HeckeNormalization`
would be false, and `CoverModelWitness` with `FunctionFieldModel` would be the form to use.) -/
def HeckeIrreducible : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left

/-- **Glue (curve theory; h-b1 M1, M2, M8): the normalization chart of an irreducible `Y`.**
`HeckeNormalization` under the extra hypothesis that `Y` is irreducible. -/
def HeckeNormalizationIrr : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left →
    ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E)
      (_ : IsGalois (RatFunc ℚ) E), NormalizationModel Y π E

/-- `HeckeNormalization` from its two parts (compiled). -/
theorem heckeNormalization_of_irr (hI : HeckeIrreducible) (hN : HeckeNormalizationIrr) :
    HeckeNormalization :=
  fun Y Φ π h1 hh h2 => hN Y Φ π h1 hh h2 (hI Y Φ π h1 hh h2)

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

end PropTSGlue

end

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# Copy of `scratch/aut-o-finite/AutOFinite.lean` (lines 3-1037), verbatim except for the imports
and the trailing `#print axioms` lines; it proves `LeafQM.AV.Pin.Exact.autO_mod_inner_exact`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section AutOCopy

/-!
# aut-o-finite: `AutOInnerFinite` (from `scratch/mobius-glue/MobiusGlue.lean`, §4), proved

Task aut-o-finite (2026-11-13). See `docs/research/aut-o-finite.md`.

* §A the target `LeafQM.AV.Pin.AutOInnerFinite`, copied verbatim (docstring and body) from
  `scratch/mobius-glue/MobiusGlue.lean` lines 419-428. It depends only on the kernel's order
  `LeafQM.O ⊆ LeafQM.B = (2, -3)_ℚ` (`ZInQKernel/HDecomp/QM/Structures.lean`).
* §7 (copied from `MobiusGlue.lean` §7): extension of `α ∈ Aut 𝒪` to `α̃ ∈ Aut_ℚ B`,
  Skolem–Noether from the kernel (`TSkolemKW.leafSkolemNoether` via `GlueDescent.B6_inner`),
  `autOInnerFinite_of_normalizer`.
* §8 (copied from `MobiusGlue.lean` §8): `NormalizerFinite` (descent on the reduced norm,
  `N(𝒪) = ℚ^× 𝒪^× {1, i, j, ij}`), hence `autOInnerFinite`.
* §9 (new): the explicit computation: `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

/-! ## §A The target (verbatim) -/

/-- **Algebra fact (finiteness of `Aut(𝒪)` modulo inner automorphisms by units).** Every ring
automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many. (Every
automorphism of `𝒪` extends to `B = 𝒪 ⊗ ℚ`, hence is conjugation by some `x ∈ N(𝒪)`
(Skolem–Noether), and `N(𝒪)/ℚ^×𝒪^×` is finite: for the maximal order of the quaternion algebra
of discriminant 6 it is the Atkin–Lehner group `W ≅ (ℤ/2)²`. STANDARD (Vignéras, *Arithmétique
des algèbres de quaternions*; locator UNVERIFIED); not in Mathlib.) A statement about the concrete
order `O` of the kernel only. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

end Pin

end AV

end LeafQM

/-! ## §7 `AutOInnerFinite` from Skolem–Noether (proved in the kernel) and `NormalizerFinite`

(Outside the `open MonObj` scope of §0-§6.) -/

namespace LeafQM

namespace AV

namespace Pin

namespace AutOExt

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-! ### `AutOInnerFinite` from Skolem–Noether and the normalizer -/

/-- **Normalizer fact (N(𝒪)/ℚ^×𝒪^× finite).** Every `u ∈ B^×` normalizing `𝒪` is
`q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t` in a fixed finite set. -/
def NormalizerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ, (∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) →
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B)

/-- Skolem–Noether (proved in the kernel, `TSkolemKW.leafSkolemNoether`) applied to `α̃`. -/
theorem conj_of_skolem : ∃ u : Bˣ, ∀ b : B, extFun α b = u * b * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner TSkolemKW.leafSkolemNoether (extAlgEquiv α)
  exact ⟨u, fun b => hu b⟩

/-- Conjugation by a unit of `𝒪`, `a ↦ v⁻¹ a v`. -/
def conjUnit (v : Oˣ) : O ≃+* O where
  toFun a := ((v⁻¹ : Oˣ) : O) * a * v
  invFun a := (v : O) * a * ((v⁻¹ : Oˣ) : O)
  left_inv a := by
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  right_inv a := by
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  map_mul' a b := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' a b := by
    simp only [mul_add, add_mul]

theorem key_conj {R : Type*} [Ring R] (x y w w' c c' t : R) (hvv : w' * w = 1) (hcc : c' * c = 1)
    (hc : c * x = x * c) (h : x * (c * w * t) = c * w * t * y) : w' * x * w * t = t * y := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc w' * x * w * t = w' * (x * w * t) := by simp only [mul_assoc]
    _ = w' * (w * t * y) := by rw [h1]
    _ = t * y := by simp only [← mul_assoc]; rw [hvv, one_mul]

/-- **`AutOInnerFinite` from the normalizer fact** (with Skolem–Noether from the kernel). -/
theorem autOInnerFinite_of_normalizer (hN : NormalizerFinite) : AutOInnerFinite := by
  classical
  obtain ⟨T, hT, hTu⟩ := hN
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hT' : T'.Finite := by
    refine Set.Finite.of_finite_image (f := f) (hT.subset (t := f '' T') ?_) ?_
    · rintro _ ⟨β, hβ, rfl⟩; exact (hf β hβ).1
    · intro β₁ h₁ β₂ h₂ heq
      apply RingEquiv.ext; intro a
      apply Subtype.ext
      have e1 := (hf β₁ h₁).2 a
      have e2 := (hf β₂ h₂).2 a
      rw [heq] at e1
      exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  refine ⟨T', hT', fun α => ?_⟩
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := hTu u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end AutOExt

end Pin

end AV

end LeafQM

/-! ## §8 `NormalizerFinite`, proved: `N(𝒪)/ℚ^×𝒪^×` is represented by `{1, i, j, ij}`

Descent on `|nrd|`. A prime `p ∤ 6` dividing `nrd(u)` of a normalizing `u ∈ 𝒪` divides `u`: an
explicit identity `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`,
`scratch/mobius-glue/py/normalizer_identity.py`). If `2 | nrd(u)` then `u i⁻¹ ∈ 𝒪`, and if
`3 | nrd(u)` then `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by `decide`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace NormO

/-! ### Integer coordinates -/

/-- The reduced norm in the coordinates of `ofInt`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2

/-- The conjugate in the coordinates of `ofInt`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [mulCoord, nrdZ]; ring

theorem ofInt_scalar (z : ℤ) : ofInt ![z, 0, 0, 0] = algebraMap ℚ B (z : ℚ) := by
  ext <;> simp [ofInt]

theorem smul_ofInt (z : ℤ) (n : Fin 4 → ℤ) : (z : ℚ) • ofInt n = ofInt (fun l => z * n l) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O_iff (x : B) : x ∈ O ↔ ∃ n, x = ofInt n := Iff.rfl

/-- `(1/z) • ofInt m ∈ 𝒪` forces `z ∣ m`. -/
theorem dvd_of_smul_mem {z : ℤ} (hz : z ≠ 0) {m : Fin 4 → ℤ}
    (h : ((z : ℚ)⁻¹) • ofInt m ∈ O) : ∀ l, z ∣ m l := by
  obtain ⟨w, hw⟩ := h
  have : ofInt m = ofInt (fun l => z * w l) := by
    rw [← smul_ofInt, ← hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hz), one_smul]
  have e := AV.ofInt_injective this
  intro l
  exact ⟨w l, congrFun e l⟩

/-! ### The units `i`, `j` of `B` -/

def ei : Fin 4 → ℤ := ![0, 1, 0, 0]
def ej : Fin 4 → ℤ := ![-1, 0, 2, 0]

theorem nrdZ_ei : nrdZ ei = -2 := by simp [nrdZ, ei]
theorem nrdZ_ej : nrdZ ej = 3 := by simp [nrdZ, ej]

def ui : Bˣ where
  val := ofInt ei
  inv := ((2 : ℚ)⁻¹) • ofInt ei
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]

def uj : Bˣ where
  val := ofInt ej
  inv := ((-3 : ℚ)⁻¹) • ofInt ej
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]

/-- The representatives `{1, i, j, ij}` of `N(𝒪)/ℚ^×𝒪^×`. -/
def T : Set Bˣ := {1, ui, uj, ui * uj}

theorem T_finite : T.Finite := by
  simp only [T]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-! ### Normalizing units -/

/-- `u` normalizes `𝒪`. -/
def IsNorm (u : Bˣ) : Prop :=
  ∀ a ∈ O, (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O ∧ ((u⁻¹ : Bˣ) : B) * a * u ∈ O

theorem IsNorm.mul {u w : Bˣ} (hu : IsNorm u) (hw : IsNorm w) : IsNorm (u * w) := by
  intro a ha
  refine ⟨?_, ?_⟩
  · have := (hu _ (hw a ha).1).1
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this
  · have := (hw _ (hu a ha).2).2
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this

theorem IsNorm.inv {u : Bˣ} (hu : IsNorm u) : IsNorm u⁻¹ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hu a ha
  exact ⟨h2, by simpa using h1⟩

/-- The unit `c ∈ ℚ^×` of `B`. -/
def sc (c : ℚ) (hc : c ≠ 0) : Bˣ where
  val := algebraMap ℚ B c
  inv := algebraMap ℚ B c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem isNorm_sc (c : ℚ) (hc : c ≠ 0) : IsNorm (sc c hc) := by
  intro a ha
  have e1 : ((sc c hc : Bˣ) : B) * a * (((sc c hc)⁻¹ : Bˣ) : B) = a := by
    change algebraMap ℚ B c * a * algebraMap ℚ B c⁻¹ = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
  have e2 : (((sc c hc)⁻¹ : Bˣ) : B) * a * ((sc c hc : Bˣ) : B) = a := by
    change algebraMap ℚ B c⁻¹ * a * algebraMap ℚ B c = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  exact ⟨by rw [e1]; exact ha, by rw [e2]; exact ha⟩

theorem isNorm_ui : IsNorm ui := by
  rintro a ⟨n, rfl⟩
  have e : ((ui : Bˣ) : B) * ofInt n * ((ui⁻¹ : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change ofInt ei * ofInt n * (((2 : ℚ)⁻¹) • ofInt ei) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  have e' : ((ui⁻¹ : Bˣ) : B) * ofInt n * ((ui : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change (((2 : ℚ)⁻¹) • ofInt ei) * ofInt n * ofInt ei = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

theorem isNorm_uj : IsNorm uj := by
  rintro a ⟨n, rfl⟩
  have e : ((uj : Bˣ) : B) * ofInt n * ((uj⁻¹ : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change ofInt ej * ofInt n * (((-3 : ℚ)⁻¹) • ofInt ej) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  have e' : ((uj⁻¹ : Bˣ) : B) * ofInt n * ((uj : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change (((-3 : ℚ)⁻¹) • ofInt ej) * ofInt n * ofInt ej = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

/-! ### The norm of a unit in `𝒪` and its inverse -/

theorem nrdZ_ne_zero (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) : nrdZ n ≠ 0 := by
  intro h0
  have h1 : (u : B) * ofInt (conjC n) = 0 := by
    rw [hu, ofInt_mul, mulCoord_conjC, h0, ofInt_scalar]; simp
  have h2 : ofInt (conjC n) = 0 := by
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) * x) h1
    simpa [← mul_assoc] using this
  have h3 : conjC n = 0 := AV.ofInt_injective (h2.trans ofInt_zero.symm)
  have h4 : n = 0 := by
    funext l
    have e0 := congrFun h3 0; have e1 := congrFun h3 1
    have e2 := congrFun h3 2; have e3 := congrFun h3 3
    simp [conjC] at e0 e1 e2 e3
    fin_cases l <;> simp <;> omega
  have : (u : B) = 0 := by rw [hu, h4, ofInt_zero]
  exact u.ne_zero this

theorem inv_eq (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) :
    ((u⁻¹ : Bˣ) : B) = ((nrdZ n : ℚ)⁻¹) • ofInt (conjC n) := by
  have hN : (nrdZ n : ℚ) ≠ 0 := by exact_mod_cast nrdZ_ne_zero u n hu
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_smul_comm, hu, ofInt_mul, mulCoord_conjC, ofInt_scalar, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ hN, map_one]

def bas : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- For a normalizing `u = ofInt n`, `nrd(u)` divides every coordinate of `u e_k ū`. -/
theorem nrd_dvd_coords (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (k l : Fin 4) : nrdZ n ∣ mulCoord (mulCoord n (bas k)) (conjC n) l := by
  have h := (hN (ofInt (bas k)) ⟨_, rfl⟩).1
  rw [inv_eq u n hu, mul_smul_comm, hu, ofInt_mul, ofInt_mul] at h
  exact dvd_of_smul_mem (nrdZ_ne_zero u n hu) h l

/-- The identities `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`). -/
theorem six_sq_identities (n : Fin 4 → ℤ) :
    let F := fun k l => mulCoord (mulCoord n (bas k)) (conjC n) l
    6 * n 0 ^ 2 = 2 * F 0 0 + 2 * F 1 1 + 2 * F 1 3 + 2 * F 2 2 - 2 * F 3 1 ∧
    6 * n 1 ^ 2 = -F 1 1 - 2 * F 2 0 + F 3 1 + F 3 3 ∧
    6 * n 2 ^ 2 = 2 * F 0 0 - 2 * F 1 1 + 2 * F 2 2 - 2 * F 3 3 ∧
    6 * n 3 ^ 2 = F 1 1 + F 1 3 - 2 * F 2 0 - F 3 3 := by
  intro F
  simp only [F, mulCoord, bas, conjC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- A prime `p ≠ 2, 3` dividing `nrd(u)` of a normalizing `u = ofInt n` divides `n`. -/
theorem dvd_of_prime_dvd_nrd (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hpd : (p : ℤ) ∣ nrdZ n) :
    ∀ l, (p : ℤ) ∣ n l := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hF : ∀ k l, (p : ℤ) ∣ mulCoord (mulCoord n (bas k)) (conjC n) l :=
    fun k l => hpd.trans (nrd_dvd_coords u n hu hN k l)
  have h6 : ¬ (p : ℤ) ∣ 6 := by
    intro h
    have h' : p ∣ 6 := by exact_mod_cast h
    have : p ∣ 2 * 3 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  obtain ⟨i0, i1, i2, i3⟩ := six_sq_identities n
  have k0 : (p : ℤ) ∣ 6 * n 0 ^ 2 := by
    rw [i0]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 1 3) _))
      (dvd_mul_of_dvd_right (hF 2 2) _)) (dvd_mul_of_dvd_right (hF 3 1) _)
  have k1 : (p : ℤ) ∣ 6 * n 1 ^ 2 := by
    rw [i1]
    exact dvd_add (dvd_add (dvd_sub (dvd_neg.mpr (hF 1 1)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 1)) (hF 3 3)
  have k2 : (p : ℤ) ∣ 6 * n 2 ^ 2 := by
    rw [i2]
    exact dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 2 2) _))
      (dvd_mul_of_dvd_right (hF 3 3) _)
  have k3 : (p : ℤ) ∣ 6 * n 3 ^ 2 := by
    rw [i3]
    exact dvd_sub (dvd_sub (dvd_add (hF 1 1) (hF 1 3)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 3)
  have key : ∀ l, (p : ℤ) ∣ 6 * n l ^ 2 := by
    intro l; fin_cases l
    exacts [k0, k1, k2, k3]
  intro l
  rcases hpZ.dvd_or_dvd (key l) with h | h
  · exact absurd h h6
  · exact hpZ.dvd_of_dvd_pow h

/-! ### The primes 2 and 3 -/

theorem two_dvd_mulCoord_ei (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) :
    ∀ l, (2 : ℤ) ∣ mulCoord n ei l := by
  have hz : ((nrdZ n : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 2,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a = 0 ∧ c = 0 := by
    decide
  obtain ⟨h0, h2⟩ := key _ _ _ _ hz
  have d0 : (2 : ℤ) ∣ n 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
  have d2 : (2 : ℤ) ∣ n 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
  intro l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem three_dvd_mulCoord_ej (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) :
    ∀ l, (3 : ℤ) ∣ mulCoord n ej l := by
  have hz : ((nrdZ n : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 3,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a - c = 0 ∧ b - d = 0 := by
    decide
  obtain ⟨h0, h1⟩ := key _ _ _ _ hz
  have d0 : (3 : ℤ) ∣ n 0 - n 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h0)
  have d1 : (3 : ℤ) ∣ n 1 - n 3 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h1)
  intro l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

/-! ### Closure of `T` under right multiplication by `i` and `j` -/

theorem T_mem_iff (t : Bˣ) : t ∈ T ↔ t = 1 ∨ t = ui ∨ t = uj ∨ t = ui * uj := Iff.rfl

theorem T_mul_ui : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (ui : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, ui, by simp [T], by simp⟩
  · refine ⟨2, two_ne_zero, 1, by simp [T], ?_⟩
    change ofInt ei * ofInt ei = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ei, QuaternionAlgebra.algebraMap_eq]
  · refine ⟨-1, by norm_num, ui * uj, by simp [T], ?_⟩
    change ofInt ej * ofInt ei = _ * (ofInt ei * ofInt ej)
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-2, by norm_num, uj, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ei = _ * ofInt ej
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

theorem T_mul_uj : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (uj : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, uj, by simp [T], by simp⟩
  · exact ⟨1, one_ne_zero, ui * uj, by simp [T], by simp⟩
  · refine ⟨-3, by norm_num, 1, by simp [T], ?_⟩
    change ofInt ej * ofInt ej = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-3, by norm_num, ui, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ej = _ * ofInt ei
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

/-- Rearranging `q v t i = (q c) v t'` for central `c`. -/
theorem rearrange (q c : ℚ) (V Tt I T' : B) (h : Tt * I = algebraMap ℚ B c * T') :
    algebraMap ℚ B q * V * Tt * I = algebraMap ℚ B (q * c) * V * T' := by
  rw [mul_assoc (algebraMap ℚ B q * V), h, ← mul_assoc, mul_assoc (algebraMap ℚ B q),
    ← Algebra.commutes c V, ← mul_assoc, ← map_mul]

theorem mulCoord_smul_right (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord n (fun l => z * m l) = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem mulCoord_smul_left (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord (fun l => z * n l) m = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem nrdZ_smul (n : Fin 4 → ℤ) (z : ℤ) : nrdZ (fun l => z * n l) = z ^ 2 * nrdZ n := by
  simp [nrdZ]; ring

/-! ### The descent -/

theorem descent (m : ℕ) : ∀ (u : Bˣ) (n : Fin 4 → ℤ), (u : B) = ofInt n →
    (nrdZ n).natAbs = m → IsNorm u →
    ∃ q : ℚ, q ≠ 0 ∧ ∃ v : Oˣ, ∃ t ∈ T, (u : B) = algebraMap ℚ B q * ((v : O) : B) * t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u n hu hm hN
  have hN0 := nrdZ_ne_zero u n hu
  by_cases h1 : m = 1
  · have hsq : nrdZ n * nrdZ n = 1 := by
      have : (nrdZ n).natAbs = 1 := hm.trans h1
      rcases Int.natAbs_eq_iff.mp this with h | h <;> rw [h] <;> norm_num
    set w : Fin 4 → ℤ := fun l => nrdZ n * conjC n l with hw_def
    have hw1 : mulCoord n w = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_right, mulCoord_conjC]
      funext l; fin_cases l <;> simp [hsq]
    have hw2 : mulCoord w n = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_left, mulCoord_conjC']
      funext l; fin_cases l <;> simp [hsq]
    let v : Oˣ :=
      ⟨⟨ofInt n, n, rfl⟩, ⟨ofInt w, w, rfl⟩,
        Subtype.ext (by
          change ofInt n * ofInt w = 1
          rw [ofInt_mul, hw1, ofInt_one]),
        Subtype.ext (by
          change ofInt w * ofInt n = 1
          rw [ofInt_mul, hw2, ofInt_one])⟩
    refine ⟨1, one_ne_zero, v, 1, by simp [T], ?_⟩
    rw [map_one, one_mul, Units.val_one, mul_one]
    exact hu
  · have hm0 : m ≠ 0 := by
      rintro rfl; exact hN0 (Int.natAbs_eq_zero.mp hm)
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : (p : ℤ) ∣ nrdZ n := by
      rw [Int.natCast_dvd, hm]; exact Nat.minFac_dvd m
    have hp1 : 2 ≤ p := hp.two_le
    by_cases hp2 : p = 2
    · have h2 : (2 : ℤ) ∣ nrdZ n := by rw [hp2] at hpd; exact_mod_cast hpd
      have hc := two_dvd_mulCoord_ei n h2
      set n' : Fin 4 → ℤ := fun l => mulCoord n ei l / 2 with hn'_def
      have hn' : mulCoord n ei = fun l => 2 * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hc l)).symm
      have hu' : ((u * ui⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((2 : ℚ)⁻¹) • ofInt ei) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ei = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * ui⁻¹ : Bˣ) : B) * ((ui : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ei
        rw [hmul, nrdZ_ei] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h2' : (-2 : ℤ).natAbs = 2 := rfl
        rw [← hm, e, Int.natAbs_mul, h2']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * ui⁻¹) n' hu' rfl (hN.mul isNorm_ui.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_ui t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * ui⁻¹ : Bˣ) : B) * ui := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    by_cases hp3 : p = 3
    · have h3 : (3 : ℤ) ∣ nrdZ n := by rw [hp3] at hpd; exact_mod_cast hpd
      have hc := three_dvd_mulCoord_ej n h3
      set n' : Fin 4 → ℤ := fun l => -(mulCoord n ej l / 3) with hn'_def
      have hn' : mulCoord n ej = fun l => (-3) * n' l := by
        funext l
        simp only [hn'_def]
        rw [mul_neg, neg_mul, neg_neg, Int.mul_ediv_cancel' (hc l)]
      have hu' : ((u * uj⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((-3 : ℚ)⁻¹) • ofInt ej) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ej = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * uj⁻¹ : Bˣ) : B) * ((uj : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ej
        rw [hmul, nrdZ_ej] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [← hm, e, Int.natAbs_mul, h3']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * uj⁻¹) n' hu' rfl (hN.mul isNorm_uj.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_uj t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * uj⁻¹ : Bˣ) : B) * uj := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    · have hdiv := dvd_of_prime_dvd_nrd u n hu hN p hp hp2 hp3 hpd
      set n' : Fin 4 → ℤ := fun l => n l / p with hn'_def
      have hn' : n = fun l => (p : ℤ) * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hdiv l)).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpi : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero hp0
      have hu' : ((sc _ hpi * u : Bˣ) : B) = ofInt n' := by
        change algebraMap ℚ B ((p : ℚ)⁻¹) * u = _
        rw [← Algebra.smul_def, hu, hn', ← smul_ofInt, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hp0, one_smul]
      have hlt : (nrdZ n').natAbs < m := by
        have e : nrdZ n = (p : ℤ) ^ 2 * nrdZ n' := by rw [hn', nrdZ_smul]
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        rw [← hm, e, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have : 4 ≤ p ^ 2 := by nlinarith
        have : (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs := by
          have : 1 * (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa using this
        exact this
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (sc _ hpi * u) n' hu' rfl ((isNorm_sc _ hpi).mul hN)
      refine ⟨p * q, mul_ne_zero hp0 hq, v, t, ht, ?_⟩
      have : (u : B) = algebraMap ℚ B (p : ℚ) * ((sc _ hpi * u : Bˣ) : B) := by
        change _ = _ * (algebraMap ℚ B ((p : ℚ)⁻¹) * u)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
      rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

/-! ### `NormalizerFinite` -/

/-- **`N(𝒪)/ℚ^×𝒪^×` is finite** (represented by `{1, i, j, ij}`). -/
theorem normalizerFinite : AutOExt.NormalizerFinite := by
  refine ⟨T, T_finite, fun u hu => ?_⟩
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

end NormO

open CategoryTheory AlgebraicGeometry

/-- **`AutOInnerFinite`, proved** (Skolem–Noether from the kernel, the normalizer from §8). -/
theorem autOInnerFinite : AutOInnerFinite :=
  AutOExt.autOInnerFinite_of_normalizer NormO.normalizerFinite

end Pin

end AV

end LeafQM


/-! ## §9 The explicit computation: `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes

Representatives: conjugation by `1, i, j, ij` (`rep 0, …, rep 3`). Every ring automorphism of `𝒪`
is `v · rep k · v⁻¹` for some `k` and `v ∈ 𝒪^×` (`rep_cover`), and `rep k`, `rep l` are conjugate
by a unit of `𝒪` only if `k = l` (`rep_distinct`: a conjugating unit would give
`nrd(t_k) = ± r² nrd(t_l)` with `r ∈ ℚ`, impossible as `nrd(1, i, j, ij) = 1, -2, 3, -6`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace Exact

open NormO AutOExt

/-- The reduced norm of `B = (2, -3)_ℚ`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem nrd_algebraMap (q : ℚ) : nrd (algebraMap ℚ B q) = q ^ 2 := by
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

theorem nrd_ofInt (n : Fin 4 → ℤ) : nrd (ofInt n) =
    ((n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2 : ℤ) : ℚ) := by
  simp [nrd, ofInt]; ring

theorem not_sq (s : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : s ^ 2 = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨s, by rw [← h]; ring⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

/-- An element of `B` commuting with `i` and `j` is a scalar. -/
theorem comm_scalar (w : B) (hi : w * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * w)
    (hj : w * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * w) : w = algebraMap ℚ B w.re := by
  have h1 := congrArg QuaternionAlgebra.imJ hi
  have h2 := congrArg QuaternionAlgebra.imK hi
  have h3 := congrArg QuaternionAlgebra.imI hj
  have h4 := congrArg QuaternionAlgebra.imK hj
  simp at h1 h2 h3 h4
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> linarith

/-- The norm of a unit of `𝒪` is `±1`. -/
theorem nrd_unit (v : Oˣ) : nrd ((v : O) : B) = 1 ∨ nrd ((v : O) : B) = -1 := by
  obtain ⟨n, hn⟩ := (v : O).2
  obtain ⟨m, hm⟩ := ((v⁻¹ : Oˣ) : O).2
  have h1 : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h2 := congrArg nrd h1
  rw [nrd_mul, hn, hm, nrd_ofInt, nrd_ofInt] at h2
  have h3 : nrd 1 = 1 := by simp [nrd]
  rw [h3] at h2
  have h4 := Int.eq_one_or_neg_one_of_mul_eq_one (by exact_mod_cast h2)
  rw [hn, nrd_ofInt]
  rcases h4 with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem isNorm_one : IsNorm 1 := by
  intro a ha
  exact ⟨by simpa using ha, by simpa using ha⟩

/-- Conjugation `a ↦ u a u⁻¹` by a unit `u ∈ B^×` normalizing `𝒪`, as a ring automorphism. -/
def conjO (u : Bˣ) (hu : IsNorm u) : O ≃+* O where
  toFun a := ⟨(u : B) * a * ((u⁻¹ : Bˣ) : B), (hu a a.2).1⟩
  invFun a := ⟨((u⁻¹ : Bˣ) : B) * a * u, (hu a a.2).2⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]
  map_add' a b := by apply Subtype.ext; simp [mul_add, add_mul]

theorem conjO_apply (u : Bˣ) (hu : IsNorm u) (a : O) :
    ((conjO u hu a : O) : B) = (u : B) * a * ((u⁻¹ : Bˣ) : B) := rfl

/-- The representatives `1, i, j, ij` of `N(𝒪)/ℚ^×𝒪^×`. -/
def tt : Fin 4 → Bˣ := ![1, ui, uj, ui * uj]

theorem tt_isNorm (k : Fin 4) : IsNorm (tt k) := by
  fin_cases k
  exacts [isNorm_one, isNorm_ui, isNorm_uj, isNorm_ui.mul isNorm_uj]

/-- The four representatives of `Aut(𝒪)/Inn(𝒪^×)`: conjugation by `1, i, j, ij`. -/
def rep (k : Fin 4) : O ≃+* O := conjO (tt k) (tt_isNorm k)

/-- The reduced norms `1, -2, 3, -6` of `1, i, j, ij`. -/
def N : Fin 4 → ℤ := ![1, -2, 3, -6]

theorem nrd_tt (k : Fin 4) : nrd (tt k : B) = (N k : ℚ) := by
  fin_cases k
  · simp [tt, N, nrd]
  · change nrd (ofInt ei) = _
    simp [nrd_ofInt, ei, N]
  · change nrd (ofInt ej) = _
    simp [nrd_ofInt, ej, N]
  · change nrd (ofInt ei * ofInt ej) = _
    rw [nrd_mul]
    simp [nrd_ofInt, ei, ej, N]; norm_num

theorem tt_of_T (t : Bˣ) (ht : t ∈ T) : ∃ k, tt k = t := by
  rcases (T_mem_iff t).1 ht with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The concrete normalizer statement (the body of `NormO.normalizerFinite`, with `T` named). -/
theorem normalizer_rep (u : Bˣ) (hu : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) :
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B) := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem key2 {R : Type*} [Ring R] (x y w w' c c' t t' : R) (hww : w * w' = 1)
    (hcc : c' * c = 1) (htt : t * t' = 1) (hc : c * x = x * c)
    (h : x * (c * w * t) = c * w * t * y) : x = w * (t * y * t') * w' := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc x = x * (w * (t * t') * w') := by rw [htt, mul_one, hww, mul_one]
    _ = x * w * t * t' * w' := by simp only [mul_assoc]
    _ = w * t * y * t' * w' := by rw [h1]
    _ = w * (t * y * t') * w' := by simp only [mul_assoc]

/-- **Every automorphism of `𝒪` is `v · rep k · v⁻¹`** for some `k` and some `v ∈ 𝒪^×`. -/
theorem rep_cover (α : O ≃+* O) : ∃ k : Fin 4, ∃ v : Oˣ, ∀ a : O,
    α a = (v : O) * rep k a * ((v⁻¹ : Oˣ) : O) := by
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := normalizer_rep u hnorm
  obtain ⟨k, rfl⟩ := tt_of_T t ht
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  refine ⟨k, v, fun a => Subtype.ext ?_⟩
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  change _ = ((v : O) : B) * ((tt k : B) * a * (((tt k)⁻¹ : Bˣ) : B)) * (((v⁻¹ : Oˣ) : O) : B)
  have hvv : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have h := hrel a
  rw [huq] at h
  exact key2 _ _ _ _ _ _ _ _ hvv hcc (Units.mul_inv _) (Algebra.commutes q _) h

/-- **The four representatives are pairwise non-conjugate by units of `𝒪`.** -/
theorem rep_distinct (k l : Fin 4) (v : Oˣ)
    (h : ∀ a : O, rep k a = (v : O) * rep l a * ((v⁻¹ : Oˣ) : O)) : k = l := by
  set V : B := ((v : O) : B) with hVdef
  set V' : B := (((v⁻¹ : Oˣ) : O) : B) with hV'def
  have hVV' : V * V' = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hV'V : V' * V = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.inv_mul]; rfl
  have hV'Vx : ∀ X : B, V' * (V * X) = X := fun X => by rw [← mul_assoc, hV'V, one_mul]
  set P : B := (tt k : B) with hP
  set P' : B := (((tt k)⁻¹ : Bˣ) : B) with hP'
  set Q : B := (tt l : B) with hQ
  set Q' : B := (((tt l)⁻¹ : Bˣ) : B) with hQ'
  have hP'P : P' * P = 1 := Units.inv_mul _
  have hQ'Qx : ∀ X : B, Q' * (Q * X) = X := fun X => by
    rw [← mul_assoc, show Q' * Q = 1 from Units.inv_mul _, one_mul]
  have hQQ'x : ∀ X : B, Q * (Q' * X) = X := fun X => by
    rw [← mul_assoc, show Q * Q' = 1 from Units.mul_inv _, one_mul]
  have hVV'x : ∀ X : B, V * (V' * X) = X := fun X => by rw [← mul_assoc, hVV', one_mul]
  have hcomm : ∀ a ∈ O, (Q' * V' * P) * a = a * (Q' * V' * P) := by
    intro a ha
    have e : P * a * P' = V * (Q * a * Q') * V' := by
      have := congrArg Subtype.val (h ⟨a, ha⟩)
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul] at this
      exact this
    calc Q' * V' * P * a = Q' * V' * (P * a * P') * P := by
          simp only [mul_assoc, hP'P, mul_one]
      _ = Q' * V' * (V * (Q * a * Q') * V') * P := by rw [e]
      _ = a * (Q' * V' * P) := by simp only [mul_assoc, hV'Vx, hQ'Qx]
  set W := Q' * V' * P with hW
  have hWs : W = algebraMap ℚ B W.re :=
    comm_scalar W (hcomm _ (mem_O_of_int 0 1 0 0)) (hcomm _ (mem_O_of_int 0 0 1 0))
  have hPW : P = V * Q * W := by
    rw [hW]; simp only [mul_assoc, hQQ'x, hVV'x]
  have e1 : (N k : ℚ) = nrd V * N l * W.re ^ 2 := by
    rw [← nrd_tt, ← nrd_tt, ← nrd_algebraMap, ← hWs, ← nrd_mul, ← nrd_mul]
    exact congrArg nrd hPW
  have hmain : ∀ ε : ℤ, nrd V = ε → ε ^ 2 = 1 →
      (W.re * N l) ^ 2 = ((ε * N k * N l : ℤ) : ℚ) := by
    intro ε hε hε2
    have hε2' : (ε : ℚ) ^ 2 = 1 := by exact_mod_cast hε2
    push_cast
    rw [e1, hε]
    linear_combination (-(W.re ^ 2 * (N l : ℚ) ^ 2)) * hε2'
  rcases nrd_unit v with h1 | h1
  · have hm := hmain 1 (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim
  · have hm := hmain (-1) (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim

/-- **Explicit computation of `Aut(𝒪)/Inn(𝒪^×)`: exactly four classes**, represented by
conjugation by `1, i, j, ij`. -/
theorem autO_mod_inner_exact : ∃ t : Fin 4 → (O ≃+* O),
    (∀ α : O ≃+* O, ∃ k, ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t k a * ((v⁻¹ : Oˣ) : O)) ∧
    ∀ k l, (∃ v : Oˣ, ∀ a : O, t k a = (v : O) * t l a * ((v⁻¹ : Oˣ) : O)) → k = l :=
  ⟨rep, rep_cover, fun k l ⟨v, hv⟩ => rep_distinct k l v hv⟩

/-- `AutOInnerFinite` again, from the explicit computation. -/
theorem autOInnerFinite' : AutOInnerFinite := by
  refine ⟨Set.range rep, Set.finite_range rep, fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := rep_cover α
  exact ⟨rep k, ⟨k, rfl⟩, v, hv⟩

end Exact

end Pin

end AV

end LeafQM

end

end AutOCopy

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# Copy of `scratch/infra-smooth-dim/SmoothStalk.lean` (lines 3-388), verbatim except for the
import line; it proves `InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section SmoothStalkCopy
/-! # Local rings of smooth schemes over a field (§0-§3 = StdSmoothLocal.lean verbatim)

Task infra-smooth-dim. Mathlib-only. (Lemmas from `MaxHeight.lean` and `CotQuot.lean` are copied
verbatim in §0, since scratch files cannot import each other.)

**Main result.** If `S` is a standard smooth algebra of relative dimension `n` over a field `k` and
`𝔪` is a maximal ideal of `S`, then `S_𝔪` has Krull dimension `n` and its maximal ideal is spanned by
`n` elements (so `S_𝔪` is regular, and `dim_κ 𝔪/𝔪² = n`).

Proof: write `S = k[x_ι]/(f_σ)` with invertible Jacobian, `M` the preimage of `𝔪`. Krull's height
theorem and `ht M = |ι|` give `dim S_𝔪 ≥ |ι| - |σ|`; the derivatives `∂f_i/∂x_{map j}` show that
the `f_i` have linearly independent classes in `M A_M / M² A_M`, so killing them lowers the embedding
dimension `|ι|` of the regular local ring `k[x]_M` by `|σ|`; and `dim ≤ edim`. -/

open Ideal IsLocalRing

namespace InfraSmoothDim

/-! ## §0 Copied from `MaxHeight.lean` and `CotQuot.lean` -/

theorem height_isMaximal_mvPolynomial (k : Type*) [Field k] :
    ∀ (ι : Type) [Finite ι] (M : Ideal (MvPolynomial ι k)) [M.IsMaximal],
      M.height = Nat.card ι := by
  intro ι _
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    have e' := (MvPolynomial.renameEquiv k e).toRingEquiv
    have : (M.map e'.symm).IsMaximal := map_isMaximal_of_equiv e'.symm
    rw [← e'.symm.height_map M, H, Nat.card_congr e]
  | h_empty =>
    intro M _
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (I := M) IsPrime.ne_top'
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero, add_zero] at h1
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero]
    exact_mod_cast nonpos_iff_eq_zero.mp (by exact_mod_cast h1)
  | @h_option α _ IH =>
    intro M _
    let e := (MvPolynomial.optionEquivLeft k α).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := map_isMaximal_of_equiv e
    let p := P.comap (Polynomial.C : MvPolynomial α k →+* _)
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    rw [← e.height_map M, Polynomial.height_eq_height_add_one p P, IH p]
    simp [Nat.card_eq_fintype_card, Fintype.card_option]

theorem spanFinrank_add_card_le {B C : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing C] [IsLocalRing C] (ψ : B →+* C)
    (hmap : (maximalIdeal B).map ψ = maximalIdeal C)
    {σ : Type*} [Fintype σ] (f : σ → maximalIdeal B)
    (hf : LinearIndependent (ResidueField B) (fun i => (maximalIdeal B).toCotangent (f i)))
    (hker : ∀ i, ψ (f i) = 0) :
    (maximalIdeal C).spanFinrank + Fintype.card σ ≤ (maximalIdeal B).spanFinrank := by
  classical
  set κ := ResidueField B
  set V := CotangentSpace B
  let v : σ → V := fun i => (maximalIdeal B).toCotangent (f i)
  let W : Submodule κ V := Submodule.span κ (Set.range v)
  have hW : Module.finrank κ W = Fintype.card σ := finrank_span_eq_card hf
  have hVW := Submodule.finrank_quotient_add_finrank W
  set d := Module.finrank κ (V ⧸ W)
  let b := Module.finBasis κ (V ⧸ W)
  have hsurj : Function.Surjective
      (fun x : maximalIdeal B => W.mkQ ((maximalIdeal B).toCotangent x)) :=
    (Submodule.mkQ_surjective W).comp (Ideal.toCotangent_surjective _)
  choose g hg using fun j : Fin d => hsurj (b j)
  -- the classes of `f` and `g` span `V`
  let s : Set (maximalIdeal B) := Set.range f ∪ Set.range g
  have hspan : Submodule.span κ ((maximalIdeal B).toCotangent '' s) = ⊤ := by
    have h1 : W ≤ Submodule.span κ ((maximalIdeal B).toCotangent '' s) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨f i, Or.inl ⟨i, rfl⟩, rfl⟩
    have h2 : (Submodule.span κ ((maximalIdeal B).toCotangent '' s)).map W.mkQ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hg j]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩)
    have := Submodule.comap_map_mkQ W (Submodule.span κ ((maximalIdeal B).toCotangent '' s))
    rw [h2, Submodule.comap_top, sup_eq_right.mpr h1] at this
    exact this.symm
  have hspanB : Submodule.span B s = ⊤ := (CotangentSpace.span_image_eq_top_iff).mp hspan
  have hmB : maximalIdeal B = Ideal.span (((↑) : maximalIdeal B → B) '' s) := by
    have := congrArg (Submodule.map (maximalIdeal B).subtype) hspanB
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
    exact this.symm
  have hmC : maximalIdeal C = Ideal.span (Set.range fun j => ψ (g j)) := by
    rw [← hmap, congrArg (Ideal.map ψ) hmB, Ideal.map_span]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨_, ⟨x, hx | hx, rfl⟩, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        simp [hker i]
      · obtain ⟨j, rfl⟩ := hx
        exact Ideal.subset_span ⟨j, rfl⟩
    · rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨_, ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩, rfl⟩
  have hle : (maximalIdeal C).spanFinrank ≤ d := by
    rw [hmC]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := C)
      (Set.finite_range fun j => ψ (g j))
    refine this.trans ?_
    have h3 : (Set.range fun j => ψ (g j)).ncard ≤ Nat.card (Fin d) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
    rw [Nat.card_fin] at h3
    exact h3
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace B]
  change _ ≤ Module.finrank κ V
  omega

/-! ## §1 Derivatives vanish modulo `M` on `M²` -/

theorem derivation_mem_of_mem_sq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {M : Ideal A} {x : A} (hx : x ∈ M ^ 2) : D x ∈ M := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (M.mul_mem_right _ ha) (M.mul_mem_right _ hb)
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

/-! ## §2 The main theorem -/

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable {ι σ : Type} [Finite ι] [Finite σ]

/-- The class of a relation in the cotangent space of `k[x]_M`. -/
noncomputable def relCot (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) (i : σ) : maximalIdeal (Localization.AtPrime M) :=
  ⟨algebraMap P.Ring (Localization.AtPrime M) (P.relation i), by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hker (P.relation_mem_ker i))⟩

theorem exists_residue_algebraMap_eq {R : Type*} [CommRing R] (M : Ideal R) [M.IsMaximal]
    (x : ResidueField (Localization.AtPrime M)) :
    ∃ a : R, residue _ (algebraMap R (Localization.AtPrime M) a) = x := by
  obtain ⟨y, hy⟩ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal M (Localization.AtPrime M)).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] at hy
  exact ⟨a, hy⟩

omit [Finite ι] in
theorem jacobiMatrix_det_notMem [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) : P.jacobiMatrix.det ∉ M := by
  intro hdet
  have hu := P.jacobian_isUnit
  rw [P.jacobian_eq_jacobiMatrix_det] at hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨a', rfl⟩ := P.algebraMap_surjective u
  have h1 : P.jacobiMatrix.det * a' - 1 ∈ M := hker (by
    show _ ∈ RingHom.ker (algebraMap P.Ring S)
    rw [RingHom.mem_ker, map_sub, map_mul, hu, map_one, sub_self])
  have h2 : P.jacobiMatrix.det * a' ∈ M := M.mul_mem_right _ hdet
  have : (1 : P.Ring) ∈ M := by simpa using M.sub_mem h2 h1
  exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one M).mpr this)

omit [Finite ι] in
/-- If `∑ aᵢ fᵢ ∈ M²` then every `aᵢ ∈ M` (differentiate and invert the Jacobian mod `M`). -/
theorem coeffs_mem_of_sum_mem_sq [Fintype σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring) [M.IsMaximal]
    (hker : P.ker ≤ M) (a : σ → P.Ring) (hy2 : ∑ i, a i * P.relation i ∈ M ^ 2) :
    ∀ i, a i ∈ M := by
  have hrM : ∀ i, P.relation i ∈ M := fun i => hker (P.relation_mem_ker i)
  have hder : ∀ j : σ, ∑ i, a i * MvPolynomial.pderiv (P.map j) (P.relation i) ∈ M := by
    intro j
    have h1 := derivation_mem_of_mem_sq (MvPolynomial.pderiv (P.map j)) hy2
    have h2 : MvPolynomial.pderiv (P.map j) (∑ i, a i * P.relation i) =
        ∑ i, a i * MvPolynomial.pderiv (P.map j) (P.relation i)
        + ∑ i, P.relation i * MvPolynomial.pderiv (P.map j) (a i) := by
      simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    rw [h2] at h1
    have h3 : ∑ i, P.relation i * MvPolynomial.pderiv (P.map j) (a i) ∈ M :=
      Ideal.sum_mem _ fun i _ => M.mul_mem_right _ (hrM i)
    have := M.sub_mem h1 h3
    rwa [add_sub_cancel_right] at this
  let _ : Field (P.Ring ⧸ M) := Ideal.Quotient.field M
  let J := P.jacobiMatrix.map (Ideal.Quotient.mk M)
  have hJ : J.det ≠ 0 := by
    rw [show J.det = Ideal.Quotient.mk M P.jacobiMatrix.det from (RingHom.map_det _ _).symm,
      Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact jacobiMatrix_det_notMem P M hker
  have hv : Matrix.mulVec J (fun i => Ideal.Quotient.mk M (a i)) = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, J, Matrix.map_apply, Pi.zero_apply]
    rw [← Ideal.Quotient.eq_zero_iff_mem.mpr (hder j), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.jacobiMatrix_apply, map_mul, mul_comm]
  have := Matrix.eq_zero_of_mulVec_eq_zero hJ hv
  intro i
  have hi := congrFun this i
  rwa [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at hi

omit [Finite ι] in
/-- A relation among the cotangent classes, with coefficients lifted to `k[x]`, gives an element
`∑ aᵢ fᵢ` of `M²`. -/
theorem sum_mem_sq_of_cotangent [Fintype σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring) [M.IsMaximal]
    (hker : P.ker ≤ M) (a : σ → P.Ring)
    (hc : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a i) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i) = 0) :
    ∑ i, a i * P.relation i ∈ M ^ 2 := by
  rw [← IsLocalization.AtPrime.under_maximalIdeal_pow M (Localization.AtPrime M) 2,
    Ideal.mem_comap]
  simp_rw [← map_smul, ← map_sum, Ideal.toCotangent_eq_zero] at hc
  convert hc using 1
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, smul_eq_mul, map_mul]
  rfl

omit [Finite ι] in
/-- The relations of a submersive presentation have linearly independent classes in the cotangent
space of `k[x]_M`, for any maximal ideal `M ⊇ ker (k[x] → S)`. -/
theorem linearIndependent_relCot (P : Algebra.SubmersivePresentation k S ι σ) (M : Ideal P.Ring)
    [M.IsMaximal] (hker : P.ker ≤ M) :
    LinearIndependent (ResidueField (Localization.AtPrime M))
      (fun i => (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i)) := by
  classical
  have := Fintype.ofFinite σ
  rw [Fintype.linearIndependent_iff]
  intro c hc
  choose a ha using exists_residue_algebraMap_eq M
  have hc' : ∑ i, algebraMap P.Ring (Localization.AtPrime M) (a (c i)) •
      (maximalIdeal (Localization.AtPrime M)).toCotangent (relCot P M hker i) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul (ResidueField (Localization.AtPrime M)), ResidueField.algebraMap_eq,
      ha (c i)]
  have hmem := coeffs_mem_of_sum_mem_sq P M hker (fun i => a (c i))
    (sum_mem_sq_of_cotangent P M hker _ hc')
  intro i
  rw [← ha (c i), residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (hmem i)

/-! ## §3 Dimension and embedding dimension of `S_𝔪` -/

/-- **Main algebraic theorem.** For a submersive presentation `P` of `S` over a field `k` and a
maximal ideal `𝔪` of `S`: `dim S_𝔪 = P.dimension` and `𝔪 S_𝔪` is spanned by `P.dimension`
elements (and no fewer). -/
theorem ringKrullDim_and_spanFinrank_localization (P : Algebra.SubmersivePresentation k S ι σ)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = P.dimension ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = P.dimension := by
  classical
  have := Fintype.ofFinite σ
  have hφs : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hkerφ : ∀ x ∈ P.ker, algebraMap P.Ring S x = 0 := fun x hx => hx
  obtain ⟨M, hMdef⟩ : ∃ M, M = m.comap (algebraMap P.Ring S) := ⟨_, rfl⟩
  have : M.IsMaximal := hMdef ▸ Ideal.comap_isMaximal_of_surjective _ hφs
  have hker : P.ker ≤ M := fun x hx => by
    rw [hMdef, Ideal.mem_comap, hkerφ x hx]
    exact m.zero_mem
  have : IsNoetherianRing S := isNoetherianRing_of_surjective _ _ _ hφs
  -- lower bound (Krull's height theorem)
  have hM : M.height = Nat.card ι := height_isMaximal_mvPolynomial k ι M
  have hK := Ideal.height_le_height_add_spanFinrank_of_le hker
  have hspan : P.ker.spanFinrank ≤ Nat.card σ := by
    rw [← P.span_range_relation_eq_ker]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
  have hquot : (M.map (Ideal.Quotient.mk P.ker)).height = m.height := by
    let e : (P.Ring ⧸ P.ker) ≃+* S := RingHom.quotientKerEquivOfSurjective hφs
    refine (e.height_map _).symm.trans (congrArg Ideal.height ?_)
    change Ideal.map (e : P.Ring ⧸ P.ker →+* S) _ = m
    rw [Ideal.map_map]
    have : (e : P.Ring ⧸ P.ker →+* S).comp (Ideal.Quotient.mk P.ker) = algebraMap P.Ring S :=
      RingHom.ext fun x => RingHom.quotientKerEquivOfSurjective_apply_mk hφs x
    rw [this, hMdef, Ideal.map_comap_of_surjective _ hφs]
  rw [hquot, hM] at hK
  have hdimC : ringKrullDim (Localization.AtPrime m) = m.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
  -- upper bound (embedding dimension)
  let ψ := Localization.localRingHom M m (algebraMap P.Ring S) hMdef
  have hcomp : ψ.comp (algebraMap P.Ring (Localization.AtPrime M)) =
      (algebraMap S (Localization.AtPrime m)).comp (algebraMap P.Ring S) := by
    ext x
    · exact Localization.localRingHom_to_map M m _ hMdef _
    · exact Localization.localRingHom_to_map M m _ hMdef _
  have hmap : (maximalIdeal (Localization.AtPrime M)).map ψ =
      maximalIdeal (Localization.AtPrime m) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, hcomp, ← Ideal.map_map, hMdef, Ideal.map_comap_of_surjective _ hφs]
  have hkill : ∀ i, ψ (relCot P M hker i) = 0 := by
    intro i
    change ψ (algebraMap P.Ring (Localization.AtPrime M) (P.relation i)) = 0
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, hkerφ _ (P.relation_mem_ker i), map_zero]
  have hU := spanFinrank_add_card_le ψ hmap (relCot P M hker) (linearIndependent_relCot P M hker)
    hkill
  have hB : ((maximalIdeal (Localization.AtPrime M)).spanFinrank : WithBot ℕ∞) = Nat.card ι := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M), hM]
    rfl
  have hB' : (maximalIdeal (Localization.AtPrime M)).spanFinrank = Nat.card ι := by
    exact_mod_cast hB
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime m)
  rw [hdimC] at hle
  have hle' : m.height ≤ ((maximalIdeal (Localization.AtPrime m)).spanFinrank : ℕ∞) := by
    exact_mod_cast hle
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle')
  rw [← hh] at hle' hK
  rw [hB', Fintype.card_eq_nat_card] at hU
  rw [hdimC, ← hh]
  simp only [Algebra.Presentation.dimension]
  have hK' : Nat.card ι ≤ h + P.ker.spanFinrank := by exact_mod_cast hK
  have hle'' : h ≤ (maximalIdeal (Localization.AtPrime m)).spanFinrank := by exact_mod_cast hle'
  constructor
  · have : h = Nat.card ι - Nat.card σ := by omega
    rw [this]; rfl
  · omega

end InfraSmoothDim


/-! ## §4 Scheme stalks (task infra-smooth-dim) -/

namespace InfraSmoothDim

open CategoryTheory AlgebraicGeometry

/-- The algebraic theorem over a base ring that is a field (without a `Field` instance). -/
theorem ringKrullDim_and_spanFinrank_of_isField {R S : Type*} [CommRing R] [CommRing S]
    (hR : IsField R) (φ : R →+* S) (n : ℕ) (h : φ.IsStandardSmoothOfRelativeDimension n)
    (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = n ∧
      (maximalIdeal (Localization.AtPrime m)).spanFinrank = n := by
  let _ := hR.toField
  let _ := φ.toAlgebra
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (h : @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ φ.toAlgebra).out
  rw [← hP]
  exact ringKrullDim_and_spanFinrank_localization P m

/-- Sections of `Spec K` over a nonempty open form a field. -/
theorem isField_sections_spec (K : Type*) [Field K] (U : (Spec (CommRingCat.of K)).Opens)
    (hU : (U : Set (Spec (CommRingCat.of K))).Nonempty) :
    IsField Γ(Spec (CommRingCat.of K), U) := by
  have hUt : U = ⊤ := by
    obtain ⟨z, hz⟩ := hU
    refine eq_top_iff.mpr fun y _ => ?_
    have : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim y z]
  subst hUt
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

/-- **Local form.** If `f : X → Spec K` is standard smooth of relative dimension `n` on an affine
chart `V → U` containing a closed point `x`, then `dim 𝒪_{X,x} = n` and `𝔪_x` is spanned by `n`
elements (so `dim_{κ(x)} 𝔪_x/𝔪_x² = n`). -/
theorem stalk_dim_of_chart {K : Type*} [Field K] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of K))
    {U : (Spec (CommRingCat.of K)).Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (n : ℕ)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom)
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  have hR := isField_sections_spec K U ⟨f.base x, e hxV⟩
  have hmax := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  obtain ⟨h1, h2⟩ := ringKrullDim_and_spanFinrank_of_isField hR _ n h
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let eq : Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _).toRingEquiv
  constructor
  · rw [← ringKrullDim_eq_of_ringEquiv eq, h1]
  · rw [← map_ringEquiv_maximalIdeal eq, Ideal.spanFinrank_map_eq_of_ringEquiv, h2]

/-- **Smooth of relative dimension `n` over a field.** At every closed point, the local ring has
Krull dimension `n` and embedding dimension `n` (it is a regular local ring of dimension `n`). -/
theorem stalk_dim_of_smoothOfRelativeDimension {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = n ∧
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank = n := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact stalk_dim_of_chart f hU hV e n h x hxV hx
end InfraSmoothDim

end SmoothStalkCopy

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# Copy of `scratch/curve-glue/CIproof.lean.part` (all of it), with the statement
`ComponentIrreducible` copied verbatim from `scratch/curve-glue/CurveGlueAll.lean` (line 1251),
wrapped in namespace `CIcopy`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section CICopy

open CategoryTheory AlgebraicGeometry

namespace CIcopy

def ComponentIrreducible : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsIrreducible (connectedComponent x)

/-! ## (CI) proved: components of a proper smooth curve are irreducible (task curve-glue)

Uses task infra-smooth-dim's `InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension` (local rings
at closed points have Krull dimension 1 and principal maximal ideal). -/

namespace CurveGlueCI

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- **A Noetherian local ring of Krull dimension 1 with principal maximal ideal is a domain.**
(Krull intersection theorem: every nonzero element is `π^n · unit`; `π` is not nilpotent since the
dimension is positive.) -/
theorem isDomain_of_dim_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hspan : (maximalIdeal R).spanFinrank = 1) : IsDomain R := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  rw [hspan] at hs
  obtain ⟨π, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
  -- `π` is not nilpotent
  have hπ : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hsub : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
      intro p
      refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
      rw [← hspan', Ideal.span_le, Set.singleton_subset_iff]
      exact p.2.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
    have : Subsingleton (PrimeSpectrum R) :=
      ⟨fun p q => PrimeSpectrum.ext ((hsub p).trans (hsub q).symm)⟩
    have h0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
    rw [hdim] at h0
    norm_num at h0
  -- every nonzero element is `π ^ n * unit`
  have hdec : ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
    intro a ha
    have hex : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra! h
      apply ha
      have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
      rw [← Submodule.mem_bot R, ← this, Submodule.mem_iInf]
      exact h
    let k := Nat.find hex
    have hk : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      apply hk
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hmem : a ∈ maximalIdeal R ^ n := by
      have := Nat.find_min hex (show n < k by omega)
      push Not at this
      exact this
    rw [← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [← hspan', Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, ← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

/-- **Two irreducible components meeting at a point with a domain stalk coincide.** -/
theorem irreducibleComponent_eq_of_isDomain_stalk {X : Scheme} {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) {y : X}
    (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) (hdom : IsDomain (X.presheaf.stalk y)) : Z₁ = Z₂ := by
  let G : Set X := Set.range (X.fromSpecStalk y)
  have hG : IsIrreducible G := by
    have : IrreducibleSpace (Spec (X.presheaf.stalk y)) := PrimeSpectrum.irreducibleSpace
    show IsIrreducible (Set.range (X.fromSpecStalk y))
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (X.fromSpecStalk y).continuous.continuousOn
  have key : ∀ Z ∈ irreducibleComponents X, y ∈ Z → Z = closure G := by
    intro Z hZ hyZ
    have hcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgen := hZ.1.isGenericPoint_genericPoint hcl
    have hspec : hZ.1.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hgen.def]; exact hyZ
    have hmem : hZ.1.genericPoint ∈ G := by
      show _ ∈ Set.range (X.fromSpecStalk y)
      rw [Scheme.range_fromSpecStalk]; exact hspec
    have hsub : Z ⊆ closure G := by
      rw [← hgen.def]
      exact closure_mono (Set.singleton_subset_iff.2 hmem)
    exact (hZ.eq_of_subset hG.closure hsub)
  rw [key Z₁ h₁ hy₁, key Z₂ h₂ hy₂]

end CurveGlueCI

/-- **(CI), proved** (from infra-smooth-dim's stalk dimensions). -/
theorem componentIrreducible : ComponentIrreducible := by
  intro K _ X f hP hS x
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  have : SmoothOfRelativeDimension 1 f := hS
  -- stalks at closed points are domains
  have hdom : ∀ y : X, IsClosed ({y} : Set X) → IsDomain (X.presheaf.stalk y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 y hy
    exact CurveGlueCI.isDomain_of_dim_one (by exact_mod_cast h1) h2
  -- irreducible components are pairwise disjoint
  have hdisj : ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂ := by
    intro Z₁ h₁ Z₂ h₂ hne
    have hcl : IsClosed (Z₁ ∩ Z₂) :=
      (isClosed_of_mem_irreducibleComponents Z₁ h₁).inter (isClosed_of_mem_irreducibleComponents Z₂ h₂)
    obtain ⟨y, ⟨hy₁, hy₂⟩, hyc⟩ := nonempty_inter_closedPoints hne hcl.isLocallyClosed
    exact CurveGlueCI.irreducibleComponent_eq_of_isDomain_stalk h₁ h₂ hy₁ hy₂
      (hdom y (mem_closedPoints_iff.mp hyc))
  -- the irreducible component of `x` is clopen
  set Z := irreducibleComponent x with hZ
  have hZc : IsClosed Z := isClosed_irreducibleComponent
  have hZmem := irreducibleComponent_mem_irreducibleComponents x
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hcompl : Zᶜ = ⋃ Z' ∈ {Z' ∈ irreducibleComponents X | Z' ≠ Z}, Z' := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      intro h
      exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hzZ'⟩ hzZ
      exact hne (hdisj Z' hZ' Z hZmem ⟨z, hzZ', hzZ⟩)
  have hZo : IsOpen Z := by
    rw [← isClosed_compl_iff, hcompl]
    exact (hfin.subset fun Z' hZ' => hZ'.1).isClosed_biUnion fun Z' hZ' =>
      isClosed_of_mem_irreducibleComponents Z' hZ'.1
  have h1 : connectedComponent x ⊆ Z :=
    (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ mem_irreducibleComponent)
  have h2 : Z ⊆ connectedComponent x :=
    isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent


end CIcopy

end CICopy

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/ts-hecke/GenericFibre.lean` (task ts-hecke, Mathlib only), minus its import and
`#print` lines: `GFC.genericFibreCount`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section GFCopy

/-! # ts-hecke: `GenericFibreCount` (development file, Mathlib only)

A finite extension `E/ℚ(X)` with `B` the integral closure of `ℚ[X]` in `E`: some rational `t` has
at least `[E : ℚ(X)]` ring maps `B → Λ` (`Λ` algebraically closed of characteristic 0) sending `X`
to `t`. -/

open Polynomial

namespace GFC

/-- Ring maps to an algebraically closed field extend along integral algebras (lying over and
`IsAlgClosed.lift`). -/
theorem exists_extend {Λ : Type*} [Field Λ] [IsAlgClosed Λ] {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] (φ : R →+* Λ)
    (hker : RingHom.ker (algebraMap R S) ≤ RingHom.ker φ) :
    ∃ ψ : S →+* Λ, ψ.comp (algebraMap R S) = φ := by
  classical
  set p := RingHom.ker φ with hp
  haveI : p.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by
      intro a ha
      exact hker ((Ideal.mem_comap.1 ha : algebraMap R S a ∈ (⊥ : Ideal S)) |>
        fun h => by simpa [RingHom.mem_ker] using h))
  haveI := hQ
  haveI : Q.LiesOver p := ⟨hQp.symm⟩
  let φ' : R ⧸ p →+* Λ := Ideal.Quotient.lift p φ (fun a ha => ha)
  letI : Algebra (R ⧸ p) Λ := φ'.toAlgebra
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  haveI : IsDomain (S ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.IsTorsionFree (R ⧸ p) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ p) Λ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rintro ⟨a⟩ ⟨b⟩ hab
    apply Ideal.Quotient.eq.2
    change φ (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.2 hab
  haveI : Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let L : (S ⧸ Q) →ₐ[R ⧸ p] Λ := IsAlgClosed.lift
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h1 := L.commutes (Ideal.Quotient.mk p a)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h1
  exact h1

/-- **`GenericFibreCount`, general form** (target field `Λ`). -/
theorem genericFibreCount (Λ : Type) [Field Λ] [IsAlgClosed Λ] [CharZero Λ]
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] :
    ∃ t : ℚ, ∃ s : Finset (integralClosure ℚ[X] E →+* Λ),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Λ t := by
  classical
  -- a primitive element, made integral
  obtain ⟨z, hz⟩ := Field.exists_primitive_element (RatFunc ℚ) E
  have hzalg : IsAlgebraic ℚ[X] z :=
    (IsFractionRing.isAlgebraic_iff ℚ[X] (RatFunc ℚ) E).2
      (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy0, hyint⟩ := hzalg.exists_integral_multiple
  set θ : E := y • z with hθ
  have hyF : algebraMap ℚ[X] (RatFunc ℚ) y ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 hy0
  have hθF : IntermediateField.adjoin (RatFunc ℚ) {θ} = ⊤ := by
    rw [eq_top_iff, ← hz, IntermediateField.adjoin_simple_le_iff]
    have hθ' : θ = algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) y) * z := by
      rw [hθ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hz' : z = (algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) y))⁻¹ * θ := by
      rw [hθ', ← mul_assoc, inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hyF), one_mul]
    rw [hz']
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.mem_adjoin_simple_self _ _)
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b h
    have h' := congrArg Subtype.val h
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  haveI : Module.IsTorsionFree ℚ[X] (integralClosure ℚ[X] E) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinjB
  let θB : integralClosure ℚ[X] E := ⟨θ, hyint⟩
  have hθBint : IsIntegral ℚ[X] θB := integralClosure.isIntegral θB
  set f : ℚ[X][X] := minpoly ℚ[X] θB with hfdef
  have hfE : minpoly ℚ[X] θ = f := by
    rw [hfdef, ← minpoly.algebraMap_eq (Subtype.val_injective) θB]
    rfl
  have hfmonic : f.Monic := minpoly.monic hθBint
  have hfF : minpoly (RatFunc ℚ) θ = f.map (algebraMap ℚ[X] (RatFunc ℚ)) := by
    rw [← hfE]; exact minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc ℚ) hyint
  have hdeg : f.natDegree = Module.finrank (RatFunc ℚ) E := by
    have h1 := IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := RatFunc ℚ) θ)
    rw [hθF, IntermediateField.finrank_top', hfF, hfmonic.natDegree_map] at h1
    exact h1.symm
  -- separability, with denominators cleared
  have hsepF : (minpoly (RatFunc ℚ) θ).Separable := Algebra.IsSeparable.isSeparable (RatFunc ℚ) θ
  obtain ⟨a₀, b₀, hab₀⟩ := hsepF
  obtain ⟨c₁, hc₁, ha₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℚ[X]) a₀
  obtain ⟨c₂, hc₂, hb₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℚ[X]) b₀
  set a₁ := IsLocalization.integerNormalization (nonZeroDivisors ℚ[X]) a₀
  set b₁ := IsLocalization.integerNormalization (nonZeroDivisors ℚ[X]) b₀
  set D : ℚ[X] := c₁ * c₂ with hD
  have hD0 : D ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hc₁) (nonZeroDivisors.ne_zero hc₂)
  have hab : C c₂ * a₁ * f + C c₁ * b₁ * derivative f = C D := by
    apply Polynomial.map_injective _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
    rw [hfF, Polynomial.derivative_map] at hab₀
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ha₁, hb₁]
    rw [Algebra.smul_def, Algebra.smul_def, Polynomial.algebraMap_apply,
      Polynomial.algebraMap_apply, hD, map_mul, Polynomial.C_mul]
    linear_combination (C (algebraMap ℚ[X] (RatFunc ℚ) c₁) * C (algebraMap ℚ[X] (RatFunc ℚ) c₂)) * hab₀
  -- a good rational value
  obtain ⟨t, ht⟩ : ∃ t : ℚ, D.eval t ≠ 0 := by
    by_contra h
    push Not at h
    exact hD0 (Polynomial.funext fun r => by simpa using h r)
  set ev : ℚ[X] →+* Λ := (algebraMap ℚ Λ).comp (Polynomial.evalRingHom t) with hev
  set g : Λ[X] := f.map ev with hg
  have hevD : ev D ≠ 0 := by
    simp only [hev, RingHom.comp_apply, Polynomial.coe_evalRingHom]
    exact (map_ne_zero_iff _ (algebraMap ℚ Λ).injective).2 ht
  have hgsep : g.Separable := by
    refine ⟨C (ev D)⁻¹ * (C c₂ * a₁).map ev, C (ev D)⁻¹ * (C c₁ * b₁).map ev, ?_⟩
    have := congrArg (Polynomial.map ev) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.derivative_map] at this
    rw [hg, Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add]
    simp only [Polynomial.map_mul, Polynomial.map_C] at this ⊢
    rw [show (ev c₂ : Λ) = ev c₂ from rfl]
    calc C (ev D)⁻¹ * (C (ev c₂) * Polynomial.map ev a₁ * Polynomial.map ev f +
          C (ev c₁) * Polynomial.map ev b₁ * Polynomial.map ev (derivative f))
        = C (ev D)⁻¹ * C (ev D) := by rw [this]
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hevD, C_1]
  have hgdeg : g.natDegree = f.natDegree := hfmonic.natDegree_map ev
  have hroots : g.roots.toFinset.card = g.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hgsep),
      IsAlgClosed.card_roots_eq_natDegree]
  -- one ring map per root
  have hext : ∀ r ∈ g.roots, ∃ ψ : integralClosure ℚ[X] E →+* Λ,
      ψ θB = r ∧ ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Λ t := by
    intro r hr
    letI : Algebra ℚ[X][X] (integralClosure ℚ[X] E) := (Polynomial.aeval θB).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ[X] ℚ[X][X] (integralClosure ℚ[X] E) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        change _ = Polynomial.aeval θB (algebraMap ℚ[X] ℚ[X][X] x)
        rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
    haveI : Algebra.IsIntegral ℚ[X][X] (integralClosure ℚ[X] E) :=
      Algebra.IsIntegral.tower_top ℚ[X]
    let φ : ℚ[X][X] →+* Λ := Polynomial.eval₂RingHom ev r
    have hker : RingHom.ker (algebraMap ℚ[X][X] (integralClosure ℚ[X] E)) ≤ RingHom.ker φ := by
      intro q hq
      have hq' : Polynomial.aeval θB q = 0 := hq
      obtain ⟨u, rfl⟩ := minpoly.isIntegrallyClosed_dvd hθBint hq'
      rw [RingHom.mem_ker, map_mul]
      have : φ (minpoly ℚ[X] θB) = 0 := by
        change Polynomial.eval₂ ev r f = 0
        rw [← Polynomial.eval_map, ← hg]
        exact (Polynomial.mem_roots'.1 hr).2
      rw [this, zero_mul]
    obtain ⟨ψ, hψ⟩ := GFC.exists_extend φ hker
    refine ⟨ψ, ?_, ?_⟩
    · have h1 := congrArg (fun h : ℚ[X][X] →+* Λ => h X) hψ
      simp only [RingHom.comp_apply] at h1
      have h2 : algebraMap ℚ[X][X] (integralClosure ℚ[X] E) X = θB := Polynomial.aeval_X θB
      rw [h2] at h1
      rw [h1]
      simp [φ]
    · have h1 := congrArg (fun h : ℚ[X][X] →+* Λ => h (C X)) hψ
      simp only [RingHom.comp_apply] at h1
      have h2 : algebraMap ℚ[X][X] (integralClosure ℚ[X] E) (C X) =
          algebraMap ℚ[X] (integralClosure ℚ[X] E) X := Polynomial.aeval_C θB X
      rw [h2] at h1
      rw [h1]
      simp [φ, hev]
  rcases isEmpty_or_nonempty (integralClosure ℚ[X] E →+* Λ) with hE | hne
  · have h0 : g.roots = 0 := Multiset.eq_zero_of_forall_notMem fun r hr =>
      hE.false (hext r hr).choose
    refine ⟨t, ∅, ?_, by simp⟩
    rw [← hdeg, ← hgdeg, ← hroots, h0]
    simp
  choose! Ψ hΨ using hext
  refine ⟨t, g.roots.toFinset.image Ψ, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hroots, hgdeg, hdeg]
    intro r hr r' hr' h
    have h1 := (hΨ r (Multiset.mem_toFinset.1 hr)).1
    have h2 := (hΨ r' (Multiset.mem_toFinset.1 hr')).1
    rw [← h1, ← h2, h]
  · intro ψ hψ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hψ
    exact (hΨ r (Multiset.mem_toFinset.1 hr)).2

end GFC


end GFCopy

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/ts-hecke/RamCount.lean` (task ts-hecke, Mathlib only), minus its import and `#print`
lines: `RamCount.ramCount` (`e(Q) · #{ψ} = [E : F]` for Galois extensions).
════════════════════════════════════════════════════════════════════════════════════════════ -/

section RamCountCopy

/-! # ts-hecke: ramification index × geometric fibre = degree (development file, Mathlib only)

For a finite Galois extension `E/F`, `F = Frac A` with `A` a principal ideal domain, `B` the
integral closure of `A` in `E`, `φ : A → Ω` (`Ω` algebraically closed of characteristic 0) with
nonzero kernel `P`, and a prime `Q` of `B` over `P`:
`e(Q) · #{ψ : B → Ω | ψ ∘ (A → B) = φ} = [E : F]`. -/

open Polynomial

namespace RamCount

variable {A F E Ω : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [IsGalois F E] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- The fibre of `ψ ↦ ker ψ` over a prime `q` is the set of `A ⧸ P`-embeddings of `B ⧸ q`. -/
noncomputable def fiberEquiv {B : Type} [CommRing B] [Algebra A B] (φ : A →+* Ω)
    (q : (RingHom.ker φ).primesOver B) [q.1.IsMaximal]
    (f : {ψ : B →+* Ω // ψ.comp (algebraMap A B) = φ} → (RingHom.ker φ).primesOver B)
    (hf : ∀ ψ, (f ψ).1 = RingHom.ker ψ.1) :
    letI : Algebra (A ⧸ RingHom.ker φ) Ω :=
      (Ideal.Quotient.lift (RingHom.ker φ) φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
    {ψ // f ψ = q} ≃ (B ⧸ q.1 →ₐ[A ⧸ RingHom.ker φ] Ω) :=
  letI : Algebra (A ⧸ RingHom.ker φ) Ω :=
    (Ideal.Quotient.lift (RingHom.ker φ) φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
  letI : Field (B ⧸ q.1) := Ideal.Quotient.field q.1
  { toFun := fun ψ =>
      { toRingHom := Ideal.Quotient.lift q.1 ψ.1.1 (fun x hx => by
          have h : RingHom.ker ψ.1.1 = q.1 := (hf ψ.1).symm.trans (congrArg Subtype.val ψ.2)
          rw [← h] at hx; exact hx)
        commutes' := by
          intro r
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
          change ψ.1.1 (algebraMap A B a) = φ a
          exact congrArg (fun g : A →+* Ω => g a) ψ.1.2 }
    invFun := fun χ => ⟨⟨χ.toRingHom.comp (Ideal.Quotient.mk q.1), RingHom.ext fun a => by
        change χ (Ideal.Quotient.mk q.1 (algebraMap A B a)) = φ a
        exact χ.commutes (Ideal.Quotient.mk _ a)⟩, by
        apply Subtype.ext
        rw [hf]
        ext x
        simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
        rw [show (χ.toRingHom (Ideal.Quotient.mk q.1 x) = 0) ↔ Ideal.Quotient.mk q.1 x = 0 from
          map_eq_zero_iff χ.toRingHom χ.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]⟩
    left_inv := fun ψ => by
      apply Subtype.ext; apply Subtype.ext
      ext x
      rfl
    right_inv := fun χ => by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem ramCount (φ : A →+* Ω) (hφ : RingHom.ker φ ≠ ⊥)
    (Q : Ideal (integralClosure A E)) [hQ : Q.IsPrime] (hQP : Q.under A = RingHom.ker φ) :
    Q.ramificationIdx A *
      {ψ : integralClosure A E →+* Ω | ψ.comp (algebraMap A (integralClosure A E)) = φ}.ncard =
      Module.finrank F E := by
  classical
  set P := RingHom.ker φ with hPdef
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime φ
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hφ
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  have hinjAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  haveI : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAE
  haveI : Module.Finite A (integralClosure A E) := IsIntegralClosure.finite A F E _
  haveI : Module.Free A (integralClosure A E) := IsIntegralClosure.module_free A F E _
  haveI : IsFractionRing (integralClosure A E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F E _
  have hrank : Module.finrank A (integralClosure A E) = Module.finrank F E :=
    IsIntegralClosure.rank A F E _
  haveI : SMulCommClass Gal(E/F) A E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A F E, AlgEquiv.commutes]⟩
  haveI : IsGaloisGroup Gal(E/F) A (integralClosure A E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/F) A (integralClosure A E) F E
  haveI : Fintype (P.primesOver (integralClosure A E)) :=
    (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (integralClosure A E)
  have he : ∀ q : P.primesOver (integralClosure A E),
      q.1.ramificationIdx A = Q.ramificationIdx A :=
    fun q => Ideal.ramificationIdx_eq_of_isGaloisGroup P q.1 Q Gal(E/F)
  -- the count of embeddings
  letI : Algebra (A ⧸ P) Ω := (Ideal.Quotient.lift P φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : CharZero (A ⧸ P) := RingHom.charZero (algebraMap (A ⧸ P) Ω)
  let f : {ψ : integralClosure A E →+* Ω // ψ.comp (algebraMap A (integralClosure A E)) = φ} →
      P.primesOver (integralClosure A E) := fun ψ =>
    ⟨RingHom.ker ψ.1, RingHom.ker_isPrime _, ⟨by
      rw [Ideal.under, RingHom.comap_ker, ψ.2]⟩⟩
  have hcount : {ψ : integralClosure A E →+* Ω |
      ψ.comp (algebraMap A (integralClosure A E)) = φ}.ncard =
      ∑ q : P.primesOver (integralClosure A E), q.1.inertiaDeg A := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {ψ : integralClosure A E →+* Ω //
      ψ.comp (algebraMap A (integralClosure A E)) = φ} = _
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
    have hfib : ∀ q : P.primesOver (integralClosure A E),
        Nat.card {ψ // f ψ = q} = q.1.inertiaDeg A := by
      intro q
      haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
      letI : Field (integralClosure A E ⧸ q.1) := Ideal.Quotient.field q.1
      rw [Nat.card_congr (fiberEquiv φ q f (fun _ => rfl)),
        AlgHom.natCard_of_splits (A ⧸ P) (integralClosure A E ⧸ q.1) Ω
          (fun _ => IsAlgClosed.splits _),
        Ideal.inertiaDeg_eq_of_isMaximal P q.1]
    haveI : ∀ q : P.primesOver (integralClosure A E), Finite {ψ // f ψ = q} := by
      intro q
      haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
      letI : Field (integralClosure A E ⧸ q.1) := Ideal.Quotient.field q.1
      exact Finite.of_equiv _ (fiberEquiv φ q f (fun _ => rfl)).symm
    rw [Nat.card_sigma]
    exact Finset.sum_congr rfl fun q _ => hfib q
  rw [hcount, Finset.mul_sum, ← hrank, ← hsum]
  exact Finset.sum_congr rfl fun q _ => by rw [he q]

end RamCount


end RamCountCopy

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/ts-hecke/Units.lean` (task ts-hecke), minus its import and `#print` lines:
`TSHeckeUnits.exists_unit_congr` (`𝒪^× → (𝒪/3𝒪)^×` is onto).
════════════════════════════════════════════════════════════════════════════════════════════ -/

section UnitsCopy

/-! # ts-hecke: `𝒪^× → (𝒪/3𝒪)^×` is onto (development file)

Table of 72 explicit units (`units_table.py`), checked by `decide`. -/

noncomputable section

namespace TSHeckeUnits

open LeafQM LeafQM.AV

/-- The reduced norm in `ofInt` coordinates:
`nrd(n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2) = n₀² + n₀n₂ + n₂² − 2(n₁² + n₁n₃ + n₃²)`. -/
def nrdC (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

/-- The conjugate in `ofInt` coordinates. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem nrdC_mul (n m : Fin 4 → ℤ) : nrdC (mulCoord n m) = nrdC n * nrdC m := by
  simp only [nrdC, mulCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem mulCoord_smul_conjC (n : Fin 4 → ℤ) (ε : ℤ) :
    mulCoord n (fun i => ε * conjC n i) = ![ε * nrdC n, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mulCoord, conjC, nrdC] <;> ring

theorem mulCoord_smul_conjC' (n : Fin 4 → ℤ) (ε : ℤ) :
    mulCoord (fun i => ε * conjC n i) n = ![ε * nrdC n, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mulCoord, conjC, nrdC] <;> ring

/-- A unit of `𝒪` from coordinates of reduced norm `ε = ±1`. -/
def unitOf (n : Fin 4 → ℤ) (ε : ℤ) (hε : nrdC n = ε) (hε2 : ε * ε = 1) : Oˣ where
  val := ⟨ofInt n, n, rfl⟩
  inv := ⟨ofInt (fun i => ε * conjC n i), _, rfl⟩
  val_inv := by
    apply Subtype.ext
    change ofInt n * ofInt (fun i => ε * conjC n i) = 1
    rw [ofInt_mul, mulCoord_smul_conjC, hε, hε2, ofInt_one]
  inv_val := by
    apply Subtype.ext
    change ofInt (fun i => ε * conjC n i) * ofInt n = 1
    rw [ofInt_mul, mulCoord_smul_conjC', hε, hε2, ofInt_one]

def unitTbl : List (Fin 4 → ℤ) :=
  [![0, 0, 0, 0],
   ![1, 0, 0, 0],
   ![-1, 0, 0, 0],
   ![-3, -2, 0, 0],
   ![1, 1, 0, 0],
   ![-1, 1, 0, 0],
   ![-3, 2, 0, 0],
   ![1, -1, 0, 0],
   ![-1, -1, 0, 0],
   ![0, 0, 1, 0],
   ![0, 0, 0, 0],
   ![-1, 0, 1, 0],
   ![0, 1, 1, 0],
   ![1, 1, 1, 0],
   ![-1, 1, 1, 0],
   ![0, -1, 1, 0],
   ![1, -1, 1, 0],
   ![-1, -1, 1, 0],
   ![0, 0, -1, 0],
   ![1, 0, -1, 0],
   ![0, 0, 0, 0],
   ![0, 1, -1, 0],
   ![1, 1, -1, 0],
   ![-1, 1, -1, 0],
   ![0, -1, -1, 0],
   ![1, -1, -1, 0],
   ![-1, -1, -1, 0],
   ![-3, 0, 0, -2],
   ![1, 0, 0, 1],
   ![-1, 0, 0, 1],
   ![0, 0, 0, 0],
   ![1, 1, -3, 1],
   ![-1, 1, 3, 1],
   ![-3, 2, 0, -2],
   ![1, -1, 0, 1],
   ![-1, -1, 0, 1],
   ![0, 0, 1, 1],
   ![1, 0, 1, 1],
   ![-1, 0, 1, 1],
   ![-3, 1, 1, 1],
   ![0, 0, 0, 0],
   ![-1, 1, -2, 1],
   ![0, -1, 1, 1],
   ![1, -1, 1, 1],
   ![-1, -1, 1, 1],
   ![0, 0, -1, 1],
   ![1, 0, -1, 1],
   ![-1, 0, -1, 1],
   ![3, 1, -1, 1],
   ![-2, 1, -1, 1],
   ![0, 0, 0, 0],
   ![0, -1, -1, 1],
   ![1, -1, -1, 1],
   ![-1, -1, -1, 1],
   ![-3, 0, 0, 2],
   ![1, 0, 0, -1],
   ![-1, 0, 0, -1],
   ![-3, -2, 0, 2],
   ![1, 1, 0, -1],
   ![-1, 1, 0, -1],
   ![0, 0, 0, 0],
   ![1, -1, -3, -1],
   ![-1, -1, 3, -1],
   ![0, 0, 1, -1],
   ![1, 0, 1, -1],
   ![-1, 0, 1, -1],
   ![0, 1, 1, -1],
   ![1, 1, 1, -1],
   ![-1, 1, 1, -1],
   ![-3, -1, 1, -1],
   ![0, 0, 0, 0],
   ![-1, -1, -2, -1],
   ![0, 0, -1, -1],
   ![1, 0, -1, -1],
   ![-1, 0, -1, -1],
   ![0, 1, -1, -1],
   ![1, 1, -1, -1],
   ![-1, 1, -1, -1],
   ![3, -1, -1, -1],
   ![-2, -1, -1, -1],
   ![0, 0, 0, 0]]


/-- The table entry for a residue vector. -/
def tbl (c : Fin 4 → ZMod 3) : Fin 4 → ℤ :=
  unitTbl.getD ((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val) 0

/-- The reduced norm mod 3. -/
def nrd3 (c : Fin 4 → ZMod 3) : ZMod 3 :=
  c 0 ^ 2 + c 0 * c 2 + c 2 ^ 2 - 2 * (c 1 ^ 2 + c 1 * c 3 + c 3 ^ 2)

/-- **The table is correct** (checked by `decide`): for every residue of nonzero reduced norm,
the entry reduces to it and has reduced norm `±1`. -/
theorem tbl_spec : ∀ c : Fin 4 → ZMod 3, nrd3 c ≠ 0 →
    (∀ i, ((tbl c i : ℤ) : ZMod 3) = c i) ∧ (nrdC (tbl c) = 1 ∨ nrdC (tbl c) = -1) := by
  decide +kernel

theorem nrdC_cast (n : Fin 4 → ℤ) : ((nrdC n : ℤ) : ZMod 3) = nrd3 (fun i => (n i : ZMod 3)) := by
  simp [nrdC, nrd3]

/-- **`𝒪^× → (𝒪/3𝒪)^×` is onto** (compiled): an element `u₀` of `𝒪` invertible modulo `3𝒪` is
congruent mod `3𝒪` to a unit. -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ d : O, u₀ - (u : O) = 3 * d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have h1 : ((1 : O) : B) = ofInt ![1, 0, 0, 0] := by rw [ofInt_one]; rfl
  have hcoord : mulCoord nv nu - ![1, 0, 0, 0] = fun i => 3 * nc i := by
    apply ofInt_injective
    rw [← ofInt_sub, ← ofInt_mul, ← three_mul_ofInt, ← hnu, ← hnv, ← hnc, ← h1, ← h33]
    exact congrArg Subtype.val hc
  -- the reduced norm of `u₀` is nonzero mod 3
  have hn1 : ((nrdC (mulCoord nv nu) : ℤ) : ZMod 3) = 1 := by
    have : mulCoord nv nu = fun i => ![1, 0, 0, 0] i + 3 * nc i := by
      funext i
      have := congrFun hcoord i
      simp only [Pi.sub_apply] at this
      linarith
    rw [this, nrdC_cast]
    simp only [nrd3]
    simp [show (3 : ZMod 3) = 0 from rfl]
  have hnu3 : nrd3 (fun i => (nu i : ZMod 3)) ≠ 0 := by
    intro h0
    rw [nrdC_mul, Int.cast_mul, nrdC_cast nu, h0, mul_zero] at hn1
    exact zero_ne_one hn1
  obtain ⟨hred, hε⟩ := tbl_spec _ hnu3
  set n := tbl (fun i => (nu i : ZMod 3))
  have hdvd : ∀ i, (3 : ℤ) ∣ nu i - n i := by
    intro i
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (nu i - n i) 3).1
      (by rw [Int.cast_sub, hred i, sub_self])
    exact_mod_cast this
  let ε : ℤ := nrdC n
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [ε, h]
  refine ⟨unitOf n ε rfl hε2, ⟨ofInt (fun i => (nu i - n i) / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  change (u₀ : B) - ofInt n = ((3 : O) : B) * ofInt (fun i => (nu i - n i) / 3)
  rw [hnu, h33, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact (Int.mul_ediv_cancel' (hdvd i)).symm

end TSHeckeUnits

end


end UnitsCopy

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# ts-hecke: the five Hecke Props under `CoverModelOfHecke`, settled and reduced

Everything above this line is copied verbatim (see `assemble.py` and `check_identical.py`):
the prop-ts prefix, the five Hecke Props of prop-ts-glue, aut-o-finite's computation of
`Aut(𝒪)/Inn(𝒪^×)`, infra-smooth-dim's stalk dimensions and curve-glue's proof of
`ComponentIrreducible`. Below: the work of task ts-hecke. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace TSHecke

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue PkgI3
open MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## Part 1: `HeckeIrreducible` -/

/-- **Any two triples satisfying R1fp are related by a surjective morphism** (compiled). The
morphism is `phi_part`'s `g : Y' → Y` with `Φ' = Φ ∘ g`; it is onto because every point `x` of `Y`
is the image of its own `κ(x)`-point, and `Φ'` is onto `M3 κ(x)` while `Φ` is injective. -/
theorem exists_surjective_of_R1fp {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} (h : R1fpProps Y Φ) (h' : R1fpProps Y' Φ') :
    ∃ g : Y' ⟶ Y, Function.Surjective g.left := by
  obtain ⟨g, hg⟩ := phi_part (R1fpProps.univ h) h'
  refine ⟨g, fun x => ?_⟩
  let φ : CommRingCat.of ℚ ⟶ Y.left.residueField x :=
    Spec.preimage (Y.left.fromSpecResidueField x ≫ Y.hom)
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  let y : fieldPt (Y.left.residueField x) ⟶ Y :=
    Over.homMk (Y.left.fromSpecResidueField x) (by
      change _ = Spec.map φ
      exact (Spec.map_preimage _).symm)
  obtain ⟨y', hy'⟩ := (Φ' (Y.left.residueField x)).surjective (Φ _ y)
  have hyy : y' ≫ g = y := (Φ _).injective ((hg _ y').symm.trans hy')
  let s : (fieldPt (Y.left.residueField x)).left := IsLocalRing.closedPoint _
  refine ⟨y'.left s, ?_⟩
  have h1 : (y' ≫ g).left s = y.left s := by rw [hyy]
  rw [Over.comp_left, Scheme.Hom.comp_apply] at h1
  rw [h1]
  exact Y.left.fromSpecResidueField_apply x _

/-- **Leaf R1conn (the canonical model `Y₃ = Sh_{K₃}` is connected over `ℚ`), witness form.**
Some triple satisfying the clause list R1fp has a connected underlying space.

*Published statement* (Shimura; Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3,
and *Variétés de Shimura*, Proc. Symp. Pure Math. 33 (1979), §2.1 and Thm 2.6.3; Milne,
*Introduction to Shimura varieties* (2005), §5 and §13; all locators UNVERIFIED): for `G = B^×`
the set of geometric components of `Sh_K` is `ℚ_{>0}^× \ 𝔸_f^× / nrd(K)`, and `Gal(ℚ̄/ℚ)` acts on
it through the cyclotomic character (Artin reciprocity), i.e. through multiplication by `ℤ̂^×`.
*Consequence used*: for `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`, `nrd(K₃) = ∏_{ℓ≠3} ℤ_ℓ^× × (1 + 3ℤ_3)`, so the
set of components is `(ℤ/3)^×` (two points) and `ℤ̂^×` acts transitively on it: `Y₃` is
`ℚ`-connected (its two geometric components are swapped by `Gal(ℚ(√−3)/ℚ)`, in particular by
complex conjugation).
*Computation* (VERIFIED, `scratch/ts-hecke/pi0_check.py`): in Shimura's uniformization
`Y₃(ℂ) = 𝒪^× \ (ℍ^± × (𝒪/3𝒪)^×)` there are exactly two orbits, separated by `s · nrd(a) mod 3`,
and complex conjugation `(s, a) ↦ (−s, a)` swaps them. -/
def Y3Connected : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left

/-- Connectedness transfers to every triple satisfying R1fp (compiled). -/
theorem connectedSpace_of_R1fp (hC : Y3Connected) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1fpProps Y Φ) : ConnectedSpace Y.left := by
  obtain ⟨Y₀, Φ₀, h₀, hc⟩ := hC
  obtain ⟨g, hg⟩ := exists_surjective_of_R1fp h h₀
  exact hg.connectedSpace g.left.continuous

/-- Irreducibility transfers to every triple satisfying R1fp (compiled). -/
theorem irreducibleSpace_of_R1fp {Y₀ Y : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀}
    {Φ : PtEquiv Y} (h₀ : R1fpProps Y₀ Φ₀) (hI : IrreducibleSpace Y₀.left)
    (h : R1fpProps Y Φ) : IrreducibleSpace Y.left := by
  obtain ⟨g, hg⟩ := exists_surjective_of_R1fp h h₀
  exact hg.irreducibleSpace g.left.continuous

/-- **A connected proper smooth curve over a field is irreducible** (compiled, from curve-glue's
`componentIrreducible`, itself from infra-smooth-dim's stalk dimensions). -/
theorem irreducibleSpace_of_connected {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f) (hS : SmoothOfRelativeDimension 1 f)
    [ConnectedSpace X] : IrreducibleSpace X := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have h := CIcopy.componentIrreducible K X f hP hS x
  rw [PreconnectedSpace.connectedComponent_eq_univ] at h
  exact (irreducibleSpace_def X).2 h

/-- **`HeckeIrreducible` from the leaf R1conn** (compiled). -/
theorem heckeIrreducible_of_connected (hC : Y3Connected) : HeckeIrreducible := by
  intro Y Φ π h1 _ _
  have := connectedSpace_of_R1fp hC h1
  obtain ⟨hP, hS, -⟩ := h1
  exact irreducibleSpace_of_connected Y.hom hP hS

/-- `HeckeIrreducible` is equivalent to the leaf, given one triple (compiled): with the bundle
leaf `R1R2fp`, `HeckeIrreducible → Y3Connected`. So R1conn is exactly what is needed. -/
theorem connected_of_heckeIrreducible (hR : R1R2fp) (hI : HeckeIrreducible) : Y3Connected := by
  obtain ⟨Y, Φ, π, h1, hh, h2⟩ := R1R2fp_Y hR
  have := hI Y Φ π h1 hh h2
  exact ⟨Y, Φ, h1, inferInstance⟩

/-! ## Part 2: `HeckeDegree`

The bound `324 = 4 · 81` is a count of `ℚ̄`-points in one fibre of `π`: four classes of
`Aut(𝒪)` modulo inner automorphisms (aut-o-finite) times at most `81` level structures on a fixed
QM pair (the kernel's leaf `ObjBridge.TorsionStructure`, through `Level3.torsor`). The degree
`[E : ℚ(X)]` is at most the number of `ℚ̄`-points of `Spec B` over a generic rational value
(`GenericFibreCount`, algebra), and those points are distinct points of one `π`-fibre. -/

/-- The classes whose QM pair is an `Aut(𝒪)`-twist of the pair of `P` (the shape of a `π`-fibre
on `ℚ̄`-points, by R2fp). -/
def twistFibre (P : QML3 Qbar) : Set (M3 Qbar) :=
  {c | ∃ Q : QML3 Qbar, c = M3.mk Q ∧ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}

/-- **Glue (commutative algebra; generic étaleness of a finite separable extension).** For a
finite extension `E/ℚ(X)` (separable: characteristic 0) with `B` the integral closure of `ℚ[X]`
in `E`, some rational value `t` has at least `[E : ℚ(X)]` ring maps `B → ℚ̄` sending `X` to `t`.
*Proof sketch* (STANDARD; e.g. Neukirch, *Algebraic Number Theory*, I.8.3 with I.2.9, or Serre,
*Local Fields*, I §4, locators UNVERIFIED): take a primitive element `θ ∈ B` with monic minimal
polynomial `f ∈ ℚ[X][T]` (`ℚ[X]` is integrally closed); `f` is separable, so `a f + b f' = D(X)`
with `D ≠ 0`; for `t ∈ ℚ` with `D(t) ≠ 0`, `f(t, T)` has `n = [E : ℚ(X)]` distinct roots
`r_i ∈ ℚ̄`; each `ℚ[X][θ] → ℚ̄`, `X ↦ t`, `θ ↦ r_i`, extends to `B` (integral over `ℚ[X][θ]`;
lying over and `ℚ̄` algebraically closed); the extensions are distinct since their values at `θ`
are. Glue, not a leaf. -/
def GenericFibreCount : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
    ∃ t : ℚ, ∃ s : Finset (integralClosure ℚ[X] E →+* Qbar),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Qbar t

section Count

variable {K : Type} [Field K]

theorem end_mul_hom {A : AbVar K} (f g : AbVar.End A) : (f * g).hom = g.hom ≫ f.hom := rfl

theorem end_one_hom {A : AbVar K} : (1 : AbVar.End A).hom = 𝟙 _ := rfl

/-- **Transport of a level structure along a QM isomorphism** (pull back by `G.ψ`). -/
def pullLevel {A₁ A₂ : AbVar K} {q₁ : QMStr A₁} {q₂ : QMStr A₂} (G : QMIso q₁ q₂)
    (e : Level3 q₂) : Level3 q₁ where
  eta := (AbVar.ptMap (L := K) G.ψ).toAdditive.comp e.eta
  linear a b := by
    show Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ G.ψ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ G.ψ.hom) ≫ (q₁.iota a).hom)
    rw [e.linear a b]
    show Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q₂.iota a).hom) ≫ G.ψ.hom) = _
    rw [Category.assoc, Category.assoc]
    congr 2
    exact (G.symm).equivariant a
  ker a := by
    have hinj : Function.Injective (AbVar.ptMap (L := K) G.ψ).toAdditive := by
      intro x y hxy
      have h' : Additive.toMul x ≫ G.ψ.hom = Additive.toMul y ≫ G.ψ.hom := congrArg Additive.toMul hxy
      have h'' := congrArg (· ≫ G.φ.hom) h'
      simp only [Category.assoc, G.right, Category.comp_id] at h''
      exact Additive.toMul.injective h''
    rw [AddMonoidHom.comp_apply, map_eq_zero_iff _ hinj, e.ker]

/-- The isomorphism of objects underlying `pullLevel`. -/
def pullIso {A₁ A₂ : AbVar K} (s₁ : A₁.dim = 2) (s₂ : A₂.dim = 2) {q₁ : QMStr A₁}
    {q₂ : QMStr A₂} (G : QMIso q₁ q₂) (e : Level3 q₂) :
    QML3.Iso (⟨A₁, s₁, q₁, pullLevel G e⟩ : QML3 K) ⟨A₂, s₂, q₂, e⟩ where
  φ := G.φ
  ψ := G.ψ
  left := G.left
  right := G.right
  equivariant := G.equivariant
  level a := by
    show Additive.ofMul ((Additive.toMul (e.eta a) ≫ G.ψ.hom) ≫ G.φ.hom) = e.eta a
    rw [Category.assoc, G.right, Category.comp_id]
    rfl

/-- **Inner twists are isomorphic** (`ι(v⁻¹) : (A, ι ∘ α) ≅ (A, ι ∘ t)` when `α = Ad(v) ∘ t`). -/
def innerIso {A : AbVar K} (q : QMStr A) (t α : O ≃+* O) (v : Oˣ)
    (h : ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)) : QMIso (q.twist α) (q.twist t) where
  φ := q.iota ((v⁻¹ : Oˣ) : O)
  ψ := q.iota (v : O)
  left := by
    rw [← end_mul_hom, ← map_mul, Units.mul_inv, map_one, end_one_hom]
  right := by
    rw [← end_mul_hom, ← map_mul, Units.inv_mul, map_one, end_one_hom]
  equivariant a := by
    show (q.iota (α a)).hom ≫ (q.iota ((v⁻¹ : Oˣ) : O)).hom =
      (q.iota ((v⁻¹ : Oˣ) : O)).hom ≫ (q.iota (t a)).hom
    rw [← end_mul_hom, ← end_mul_hom, ← map_mul, ← map_mul, h a]
    congr 2
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

end Count

/-- `u ∈ 𝒪` and the lift of its coordinates mod 3 differ by an element of `3𝒪`. -/
theorem exists_sub_liftO (u : O) : ∃ c : Fin 4 → ZMod 3, ∃ d : O, u - liftO c = 3 * d := by
  obtain ⟨n, hn⟩ := u.2
  refine ⟨fun i => (n i : ZMod 3), ⟨ofInt (fun i => n i / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [liftO, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33]
  rw [hn, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast]
  have := Int.emod_def (n i) 3
  omega

/-- **The fibre count** (compiled, from the kernel's leaf `TorsionStructure` and aut-o-finite's
`autO_mod_inner_exact`): a twist fibre has at most `4 · 81 = 324` classes. -/
theorem twistFibre_count (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) :
    (twistFibre P).Finite ∧ (twistFibre P).ncard ≤ 324 := by
  classical
  obtain ⟨t, hcov, -⟩ := LeafQM.AV.Pin.Exact.autO_mod_inner_exact
  let F : Fin 4 × (Fin 4 → ZMod 3) → M3 Qbar := fun kc =>
    if h : ∃ e : Level3 (P.twist (t kc.1)).q,
        ∀ a, e.eta a = (P.twist (t kc.1)).e.eta (a * liftO kc.2) then
      M3.mk ⟨P.A, P.surface, (P.twist (t kc.1)).q, h.choose⟩
    else M3.mk P
  have hsub : twistFibre P ⊆ Set.range F := by
    rintro c ⟨Q, rfl, α, ⟨g⟩⟩
    obtain ⟨k, v, hv⟩ := hcov α
    let G : QMIso (P.twist (t k)).q Q.q := (innerIso P.q (t k) α v hv).symm.trans g
    let e₀ : Level3 (P.twist (t k)).q := pullLevel G Q.e
    obtain ⟨u₀, -, -, hu⟩ := Level3.torsor hT (P.twist (t k)) e₀
    obtain ⟨c, d, hd⟩ := exists_sub_liftO u₀
    have hc : ∀ a, (P.twist (t k)).e.eta (a * u₀) = (P.twist (t k)).e.eta (a * liftO c) := by
      intro a
      rw [(P.twist (t k)).e.eq_iff]
      refine ⟨a * d, ?_⟩
      rw [← _root_.mul_sub, hd]
      noncomm_ring
    have h : ∃ e : Level3 (P.twist (t k)).q,
        ∀ a, e.eta a = (P.twist (t k)).e.eta (a * liftO c) :=
      ⟨e₀, fun a => (hu a).trans (hc a)⟩
    refine ⟨(k, c), ?_⟩
    have he : h.choose = e₀ := Level3.ext' (AddMonoidHom.ext fun a =>
      (h.choose_spec a).trans ((hu a).trans (hc a)).symm)
    simp only [F, dif_pos h, he]
    exact Quotient.sound ⟨pullIso P.surface Q.surface G Q.e⟩
  have hfin : (Set.range F).Finite := Set.finite_range F
  refine ⟨hfin.subset hsub, ?_⟩
  calc (twistFibre P).ncard ≤ (Set.range F).ncard := Set.ncard_le_ncard hsub hfin
    _ = (F '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin 4 × (Fin 4 → ZMod 3))).ncard := Set.ncard_image_le
    _ = 324 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]; simp

/-- Any two morphisms `Spec ℚ̄ → Spec ℚ` agree. -/
theorem specQbar_to_specQ_eq (f g : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of ℚ)) :
    f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **`HeckeDegree` from `GenericFibreCount` and the kernel's leaf `TorsionStructure`**
(compiled; aut-o-finite's computation inlined). -/
theorem heckeDegree_of (hG : GenericFibreCount) (hT : ObjBridge.TorsionStructure) :
    HeckeDegree := by
  intro Y Φ π _ _ h2 E _ _ _ _ _ _ hM
  obtain ⟨h, hO, -, hval⟩ := hM
  obtain ⟨t, s, hs, hst⟩ := hG E
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  have hpt_inj : Function.Injective pt := by
    intro ψ ψ' hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    have h2' := (cancel_mono h).1 h1
    have h3 := Spec.map_injective h2'
    exact congrArg CommRingCat.Hom.hom h3
  have hpt_val : ∀ ψ ∈ s, π.val (K := Qbar) (pt ψ).left = OnePoint.some (algebraMap ℚ Qbar t) := by
    intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hst ψ hψ]
  rcases s.eq_empty_or_nonempty with hs0 | ⟨ψ₀, hψ₀⟩
  · rw [hs0, Finset.card_empty] at hs
    omega
  set P : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ₀)) with hPdef
  have hP : Φ Qbar (pt ψ₀) = M3.mk P := (Quotient.out_eq _).symm
  have hmem : ∀ ψ ∈ s, Φ Qbar (pt ψ) ∈ twistFibre P := by
    intro ψ hψ
    set Q : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ)) with hQdef
    have hQ : Φ Qbar (pt ψ) = M3.mk Q := (Quotient.out_eq _).symm
    refine ⟨Q, hQ, ((h2 (pt ψ₀) (pt ψ) P Q hP hQ).1).1 ?_⟩
    rw [hpt_val ψ₀ hψ₀, hpt_val ψ hψ]
  obtain ⟨hfin, hcard⟩ := twistFibre_count hT P
  have hinj : Set.InjOn (fun ψ => Φ Qbar (pt ψ)) (s : Set _) :=
    fun ψ _ ψ' _ hψ => hpt_inj ((Φ Qbar).injective hψ)
  have := Set.ncard_le_ncard_of_injOn (fun ψ => Φ Qbar (pt ψ)) hmem hinj hfin
  rw [Set.ncard_coe_finset] at this
  omega

/-- **`GenericFibreCount` is proved** (`GFC.genericFibreCount` at `Ω = ℚ̄`, Mathlib only). -/
theorem genericFibreCount : GenericFibreCount := fun E _ _ _ _ _ => GFC.genericFibreCount Qbar E

/-- **`HeckeDegree` from the kernel's textbook leaf `TorsionStructure` alone** (compiled). -/
theorem heckeDegree_of_torsion (hT : ObjBridge.TorsionStructure) : HeckeDegree :=
  heckeDegree_of genericFibreCount hT

/-! ## Part 3: `HeckeNormalizationIrr`

The moduli-theoretic input is **fibre transitivity**: two `ℚ̄`-points with the same `π`-value
differ by an automorphism of `Y` coming from R1hecke (`twist α`, then `rightMul u`), and these
automorphisms preserve `π`. It is proved here from R1hecke, R2fp, the kernel's leaf
`TorsionStructure` (level torsor) and the surjectivity of `𝒪^× → (𝒪/3𝒪)^×` (`Units.lean`). What
is left is one statement of curve theory with no moduli in it, `CurveGaloisChart`. -/

/-- **Fibre transitivity on classes** (compiled). -/
theorem fibre_transitive (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (y y' : fieldPt Qbar ⟶ Y)
    (hyy : π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left) :
    ∃ α : O ≃+* O, ∃ u : Oˣ, Φ Qbar y' = M3.rightMul u (M3.twist α (Φ Qbar y)) := by
  set P := Quotient.out (Φ Qbar y)
  set Q := Quotient.out (Φ Qbar y')
  have hP : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
  have hQ : Φ Qbar y' = M3.mk Q := (Quotient.out_eq _).symm
  obtain ⟨α, ⟨G⟩⟩ := ((h2 y y' P Q hP hQ).1).1 hyy
  let e₀ : Level3 (P.twist α).q := pullLevel G Q.e
  obtain ⟨u₀, v₀, hvu, hu⟩ := Level3.torsor hT (P.twist α) e₀
  obtain ⟨u, d, hd⟩ := TSHeckeUnits.exists_unit_congr u₀ v₀ hvu
  refine ⟨α, u, ?_⟩
  have he : (P.twist α).e.rightMul u = e₀ := Level3.ext' (AddMonoidHom.ext fun a => by
    rw [hu a]
    show (P.twist α).e.eta (a * u) = (P.twist α).e.eta (a * u₀)
    rw [(P.twist α).e.eq_iff]
    exact ⟨-(a * d), by rw [← _root_.mul_sub, ← neg_sub, hd]; noncomm_ring⟩)
  rw [hQ, hP]
  show M3.mk Q = M3.mk ((P.twist α).rightMul u)
  have hiso : QML3.Iso ((P.twist α).rightMul u) Q := by
    show QML3.Iso ⟨P.A, P.surface, (P.twist α).q, (P.twist α).e.rightMul u⟩ Q
    rw [he]
    exact pullIso P.surface Q.surface G Q.e
  symm
  exact Quotient.sound ⟨hiso⟩

/-- **Fibre transitivity by automorphisms of `Y`** (compiled): two `ℚ̄`-points with the same
`π`-value differ by the composite of two automorphisms supplied by R1hecke. -/
theorem fibre_transitive_aut (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) (y y' : fieldPt Qbar ⟶ Y)
    (hyy : π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left) :
    ∃ (α : O ≃+* O) (u : Oˣ) (g₁ g₂ : Y ≅ Y),
      (∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
        Φ K (z ≫ g₁.hom) = M3.twist α (Φ K z)) ∧
      (∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
        Φ K (z ≫ g₂.hom) = M3.rightMul u (Φ K z)) ∧
      y' = y ≫ g₁.hom ≫ g₂.hom := by
  obtain ⟨α, u, hαu⟩ := fibre_transitive hT h2 y y' hyy
  obtain ⟨g₁, hg₁⟩ := hh.1 α
  obtain ⟨g₂, hg₂⟩ := hh.2 u
  refine ⟨α, u, g₁, g₂, hg₁, hg₂, (Φ Qbar).injective ?_⟩
  rw [hαu, ← Category.assoc, hg₂, hg₁]

/-- **The automorphisms of R1hecke preserve `π` on `ℚ̄`-points** (compiled; R2fp's fibre clause).
Twist case. -/
theorem pi_invariant_twist {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (α : O ≃+* O) (g : Y ≅ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      Φ K (z ≫ g.hom) = M3.twist α (Φ K z)) (z : fieldPt Qbar ⟶ Y) :
    π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left := by
  set P := Quotient.out (Φ Qbar z)
  set Q := Quotient.out (Φ Qbar (z ≫ g.hom))
  have hP : Φ Qbar z = M3.mk P := (Quotient.out_eq _).symm
  have hQ : Φ Qbar (z ≫ g.hom) = M3.mk Q := (Quotient.out_eq _).symm
  have hQP : M3.mk (P.twist α) = M3.mk Q := by rw [← hQ, hg, hP]; rfl
  obtain ⟨f⟩ := Quotient.exact hQP
  have hf : QMIso (P.q.twist α) Q.q := ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩
  exact (((h2 z (z ≫ g.hom) P Q hP hQ).1).2 ⟨α, ⟨hf⟩⟩).symm

/-- `rightMul` case. -/
theorem pi_invariant_rightMul {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (u : Oˣ) (g : Y ≅ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      Φ K (z ≫ g.hom) = M3.rightMul u (Φ K z)) (z : fieldPt Qbar ⟶ Y) :
    π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left := by
  set P := Quotient.out (Φ Qbar z)
  set Q := Quotient.out (Φ Qbar (z ≫ g.hom))
  have hP : Φ Qbar z = M3.mk P := (Quotient.out_eq _).symm
  have hQ : Φ Qbar (z ≫ g.hom) = M3.mk Q := (Quotient.out_eq _).symm
  have hQP : M3.mk (P.rightMul u) = M3.mk Q := by rw [← hQ, hg, hP]; rfl
  obtain ⟨f⟩ := Quotient.exact hQP
  have hf : QMIso (P.q.twist (RingEquiv.refl O)) Q.q :=
    ⟨f.φ, f.ψ, f.left, f.right, fun a => f.equivariant a⟩
  exact (((h2 z (z ≫ g.hom) P Q hP hQ).1).2 ⟨RingEquiv.refl O, ⟨hf⟩⟩).symm

/-- **The `π`-fibres on `ℚ̄`-points are finite** (compiled; `twistFibre_count`). -/
theorem fibre_finite (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (t : OnePoint Qbar) :
    {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite := by
  rcases Set.eq_empty_or_nonempty {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t} with
    h | ⟨y₀, hy₀⟩
  · rw [h]; exact Set.finite_empty
  set P := Quotient.out (Φ Qbar y₀)
  have hP : Φ Qbar y₀ = M3.mk P := (Quotient.out_eq _).symm
  refine Set.Finite.of_finite_image ((twistFibre_count hT P).1.subset ?_)
    ((Φ Qbar).injective.injOn)
  rintro _ ⟨y, hy, rfl⟩
  set Q := Quotient.out (Φ Qbar y)
  have hQ : Φ Qbar y = M3.mk Q := (Quotient.out_eq _).symm
  exact ⟨Q, hQ, ((h2 y₀ y P Q hP hQ).1).1 (hy₀.trans hy.symm)⟩

/-- **Glue (curve theory; h-b1 M1, M2, M8), with no moduli in it.** Let `Y` be a proper smooth
irreducible curve over `ℚ` and `π : Y → P¹` a morphism with finite fibres on `ℚ̄`-points, such
that any two `ℚ̄`-points with the same `π`-value differ by an automorphism of `Y` preserving `π` on
`ℚ̄`-points. Then there is a finite Galois `E/ℚ(X)` with `NormalizationModel Y π E`.
*Proof* (STANDARD; Hartshorne II.6.7-6.8, II.5.20 and Ex. II.3.5; Artin's theorem): `π` is
quasi-finite and proper, hence finite (EGA III 4.4.2 / Stacks 02OG); `Y` is normal (smooth), so
`π⁻¹(𝔸¹) = Spec B` with `B` the integral closure of `ℚ[X]` in `E = ℚ(Y)`; the `π`-preserving
automorphisms act on `E` over `ℚ(X)`, faithfully (`Y` integral and separated), and transitively on
a generic geometric fibre, which has `[E : ℚ(X)]` points (generic étaleness in characteristic 0),
so the group `G` they generate has `|G| ≥ [E : ℚ(X)] ≥ [E : E^G] = |G|`; hence `E^G = ℚ(X)` and
`E/ℚ(X)` is Galois (Artin). Locators UNVERIFIED. Glue, not a leaf. -/
def CurveGaloisChart : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    (∀ y y' : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left →
      ∃ g : Y ≅ Y, y' = y ≫ g.hom ∧
        ∀ z : fieldPt Qbar ⟶ Y, π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left) →
    ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E)
      (_ : IsGalois (RatFunc ℚ) E), NormalizationModel Y π E

/-- **`HeckeNormalizationIrr` from `CurveGaloisChart` and the kernel's leaf `TorsionStructure`**
(compiled). -/
theorem heckeNormalizationIrr_of (hC : CurveGaloisChart) (hT : ObjBridge.TorsionStructure) :
    HeckeNormalizationIrr := by
  intro Y Φ π h1 hh h2 hI
  obtain ⟨hP, hS, -⟩ := h1
  refine hC Y π hP hS hI (fibre_finite hT h2) ?_
  intro y y' hyy
  obtain ⟨α, u, g₁, g₂, hg₁, hg₂, hy⟩ := fibre_transitive_aut hT hh h2 y y' hyy
  refine ⟨g₁ ≪≫ g₂, by rw [hy]; rfl, fun z => ?_⟩
  change π.val (K := Qbar) (z ≫ g₁.hom ≫ g₂.hom).left = _
  rw [← Category.assoc, pi_invariant_rightMul h2 u g₂ hg₂, pi_invariant_twist h2 α g₁ hg₁]

/-- **`HeckeNormalization` (both parts)** from the leaf R1conn, `CurveGaloisChart` and
`TorsionStructure` (compiled). -/
theorem heckeNormalization_of (hconn : Y3Connected) (hC : CurveGaloisChart)
    (hT : ObjBridge.TorsionStructure) : HeckeNormalization :=
  heckeNormalization_of_irr (heckeIrreducible_of_connected hconn) (heckeNormalizationIrr_of hC hT)

/-! ## Part 4: `HeckeBranch`

`e(Q) · #(geometric fibre) = [E : ℚ(X)]` for a Galois extension (`RamOfFibreCount`, algebra); the
geometric fibres of `Spec B → 𝔸¹` (and of the chart at `∞`) are the `π`-fibres of `Y`
(`chart_count`, compiled from `NormalizationModel`; `CurveChartInf`, curve theory, at `∞`); a
`π`-fibre is a twist fibre (`fibre_ncard`, compiled); and the twist fibres have the sizes of the
Baba–Granath elliptic table (`HeckeFibreSizes`, the moduli input). -/

/-- **Glue (commutative algebra; fundamental identity for a Galois extension).** Let `E/ℚ(X)` be
finite Galois and `B` the integral closure of `ℚ[X]` in `E`. (a) A prime over `0` has
ramification index `1` (it is `0`). (b) For `t ∈ ℚ̄` and a prime `Q` of `B` over the kernel of
`ℚ[X] → ℚ̄`, `X ↦ t`: `e(Q) · #{ψ : B → ℚ̄ | ψ(X) = t} = [E : ℚ(X)]`. (c) The same at `∞` for the
integral closure of `ℚ[s]` (`s = 1/X`) and `t = 0`. *Proof* (STANDARD: Serre, *Local Fields*,
I §7 Prop. 21 and I §4; Neukirch I.9.3; locators UNVERIFIED): `B` is a Dedekind domain; Galois
acts transitively on the primes over `P`, so all have the same `e` and `f`, and `e f g = n`; the
residue extensions are separable (characteristic 0), so a prime `Q'` over `P` contributes
`f` maps `B/Q' → ℚ̄` over a fixed `ℚ[X]/P → ℚ̄`; hence the number of `ψ` is `g f = n / e`. Mathlib
has the fundamental identity (`Ideal.sum_ramification_inertia`) and its Galois form. Glue. -/
def RamOfFibreCount : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E],
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = ⊥ →
      Q.ramificationIdx ℚ[X] = 1) ∧
    (∀ (t : Qbar) (Q : Ideal (integralClosure ℚ[X] E)), Q.IsPrime →
      Q.under ℚ[X] = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) →
      Q.ramificationIdx ℚ[X] *
        {ψ : integralClosure ℚ[X] E →+* Qbar |
          ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard =
        Module.finrank (RatFunc ℚ) E) ∧
    (letI := infAlg E
      ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime →
        Q.under InfCoord = Ideal.span {infUnif} →
        Q.ramificationIdx InfCoord *
          {ψ : integralClosure InfCoord E →+* Qbar |
            ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = 0}.ncard =
          Module.finrank (RatFunc ℚ) E)

/-- **The normalization chart at `∞`**: an open immersion `Spec B_∞ → Y` (`B_∞` the integral
closure of `ℚ[s]`, `s = 1/X`, in `E`) whose image contains every `ℚ̄`-point with `π ≠ 0`, along
which `π = ∞` exactly where `s = 0`. -/
def NormalizationModelInf (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) (E : Type)
    [Field E] [Algebra (RatFunc ℚ) E] : Prop :=
  letI := infAlg E
  ∃ h : Spec (CommRingCat.of (integralClosure InfCoord E)) ⟶ Y.left, IsOpenImmersion h ∧
    (∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.some 0 →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure InfCoord E)),
        y = y' ≫ h) ∧
    ∀ ψ : integralClosure InfCoord E →+* Qbar,
      (π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = OnePoint.infty ↔
        ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = 0)

/-- **Glue (curve theory): the chart at `∞`.** For a proper smooth curve `Y/ℚ` and `π : Y → P¹`
with finite `ℚ̄`-fibres, a field `E` carrying the chart over `𝔸¹` (`NormalizationModel`) also
carries the chart over `P¹ ∖ {0}`. *Proof* (STANDARD; Hartshorne II.6.7-6.8): finite fibres force
every component of `Y` to meet `π⁻¹(𝔸¹) ≅ Spec B`, so `Y` is irreducible with function field `E`;
`π` is finite and `Y` normal, so `π⁻¹(P¹ ∖ {0}) = Spec B_∞`, with `s = 1/π` there. Glue. -/
def CurveChartInf : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
      NormalizationModel Y π E → NormalizationModelInf Y π E

/-- **The moduli input: sizes of the twist fibres** (the shape of Baba–Granath's elliptic table).
There is `M` (it is `144 = |Γ'|`) such that every twist fibre has at most `M` classes, the fibre
of an object without CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` has exactly `M`, and at objects with CM by
`ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) `M` divides `4` (resp. `6`, `2`) times the fibre size (the
expected sizes are `36`, `24`, `72`). *Count*: a fixed pair `(A, ι)` over `ℚ̄` has
`72 = |(𝒪/3𝒪)^×|` level structures, permuted freely by `com(ι)^×/{±1}` (trivial unless CM by
`ℤ[i]` or `ℤ[ζ₃]`); `Aut(𝒪)/Inn(𝒪^×) = W` has order 4 and acts freely on the pairs except at CM by
`ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (stabilizers `⟨w₂⟩`, `⟨w₃⟩`, `⟨w₆⟩`); CM points of discriminants `−8`
and `−12` do not exist on `X₆` (`3` splits in `ℚ(√−2)`; `2` divides conductor and discriminant).
So the sizes are `4·36 = 144`, `2·18 = 36`, `2·12 = 24`, `2·36 = 72`. *Source*: the fibre of
`Y₃ → P¹` through a point `y` has
`|Γ'| / |Stab(y)|` points; `Stab(y)` is trivial off the elliptic points of `Γ*`, whose orders are
`4, 6, 2` at the CM points of discriminants `−4, −3, −24` (Baba–Granath, Canad. J. Math. 60
(2008), §3.1, the elliptic-order table, p. 740 per docs/research/locators.md; signature
`(0; 2, 4, 6)`); the complete list of elliptic elements of the normalizer (h-b1 M9, VERIFIED by
`scratch/rv-h-b1/rv_checks.py`) shows that every point with a nontrivial stabilizer has CM by one of
the three maximal orders; `Γ₃` is torsion-free (`−1 ∉ K₃`). Glue from leaves (Shimura's
uniformization and Baba–Granath). -/
def HeckeFibreSizes : Prop :=
  ∃ M : ℕ, (∀ P : QML3 Qbar, (twistFibre P).ncard ≤ M) ∧
    (∀ P : QML3 Qbar, ¬ HasCM4 P.q → ¬ HasCM3 P.q → ¬ HasCM24 P.q →
      (twistFibre P).ncard = M) ∧
    (∀ P : QML3 Qbar, HasCM4 P.q → M ∣ 4 * (twistFibre P).ncard) ∧
    (∀ P : QML3 Qbar, HasCM3 P.q → M ∣ 6 * (twistFibre P).ncard) ∧
    (∀ P : QML3 Qbar, HasCM24 P.q → M ∣ 2 * (twistFibre P).ncard)

/-- The `ℚ̄`-points of `Spec B` over `t` are the `π`-fibre over `t` (compiled). -/
theorem chart_count {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type} [Field E]
    [Algebra ℚ[X] E] (hM : NormalizationModel Y π E) (t : Qbar) :
    {ψ : integralClosure ℚ[X] E →+* Qbar |
        ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard =
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = OnePoint.some t}.ncard := by
  obtain ⟨h, hO, himg, hval⟩ := hM
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  refine Set.ncard_congr (fun ψ _ => pt ψ) ?_ ?_ ?_
  · intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hψ]
  · intro ψ ψ' _ _ hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  · intro y hy
    obtain ⟨y', hy'⟩ := himg y.left (by rw [hy]; exact OnePoint.coe_ne_infty _)
    refine ⟨(Spec.preimage y').hom, ?_, ?_⟩
    · have := hval (Spec.preimage y').hom
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy', hy] at this
      exact (OnePoint.coe_injective this).symm
    · apply Over.OverMorphism.ext
      show Spec.map (CommRingCat.ofHom (Spec.preimage y').hom) ≫ h = y.left
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy']

/-- The same at `∞` (compiled). -/
theorem chart_count_inf {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type}
    [Field E] [Algebra (RatFunc ℚ) E] (hM : NormalizationModelInf Y π E) :
    letI := infAlg E
    {ψ : integralClosure InfCoord E →+* Qbar |
        ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = 0}.ncard =
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = OnePoint.infty}.ncard := by
  letI := infAlg E
  obtain ⟨h, hO, himg, hval⟩ := hM
  let pt : (integralClosure InfCoord E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  refine Set.ncard_congr (fun ψ _ => pt ψ) ?_ ?_ ?_
  · intro ψ hψ
    exact (hval ψ).2 hψ
  · intro ψ ψ' _ _ hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  · intro y hy
    obtain ⟨y', hy'⟩ := himg y.left (by
      change π.val (K := Qbar) y.left = OnePoint.infty at hy
      rw [hy]; exact OnePoint.infty_ne_coe _)
    refine ⟨(Spec.preimage y').hom, ?_, ?_⟩
    · apply (hval (Spec.preimage y').hom).1
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy']
      exact hy
    · apply Over.OverMorphism.ext
      show Spec.map (CommRingCat.ofHom (Spec.preimage y').hom) ≫ h = y.left
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy']

/-- A `π`-fibre on `ℚ̄`-points is a twist fibre (compiled). -/
theorem fibre_ncard {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h2 : R2fpProps Y Φ π) (y₀ : fieldPt Qbar ⟶ Y) :
    {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = π.val (K := Qbar) y₀.left}.ncard =
      (twistFibre (Quotient.out (Φ Qbar y₀))).ncard := by
  set P := Quotient.out (Φ Qbar y₀)
  have hP : Φ Qbar y₀ = M3.mk P := (Quotient.out_eq _).symm
  rw [← Set.ncard_image_of_injective _ (Φ Qbar).injective]
  congr 1
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    set Q := Quotient.out (Φ Qbar y)
    have hQ : Φ Qbar y = M3.mk Q := (Quotient.out_eq _).symm
    exact ⟨Q, hQ, ((h2 y₀ y P Q hP hQ).1).1 hy.symm⟩
  · rintro ⟨Q, rfl, hα⟩
    refine ⟨(Φ Qbar).symm (M3.mk Q), ?_, Equiv.apply_symm_apply _ _⟩
    exact (((h2 y₀ _ P Q hP (Equiv.apply_symm_apply _ _)).1).2 hα).symm

/-- The kernel of evaluation at a rational point (compiled). -/
theorem ker_eval_rat (b : ℚ) :
    RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) (algebraMap ℚ Qbar b)) =
      Ideal.span {X - C b} := by
  rw [← Polynomial.ker_evalRingHom]
  ext p
  simp only [RingHom.mem_ker, Polynomial.coe_eval₂RingHom, Polynomial.coe_evalRingHom]
  rw [Polynomial.eval₂_at_apply, map_eq_zero_iff _ (algebraMap ℚ Qbar).injective]

/-- A nonzero prime of `ℚ[X]` is the kernel of evaluation at some `t ∈ ℚ̄` (compiled). -/
theorem exists_ker_eval (P : Ideal ℚ[X]) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ t : Qbar, P = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) := by
  have hmax : P.IsMaximal := hP.isMaximal h0
  obtain ⟨p, rfl⟩ := (Submodule.IsPrincipal.principal P)
  have hp0 : p ≠ 0 := by rintro rfl; exact h0 (by simp)
  have hdeg : (p.map (algebraMap ℚ Qbar)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro hd
    rw [Polynomial.eq_C_of_degree_eq_zero hd] at hmax
    apply hmax.ne_top
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    have : p.coeff 0 ≠ 0 := by
      intro hc; apply hp0; rw [Polynomial.eq_C_of_degree_eq_zero hd, hc, map_zero]
    exact Polynomial.isUnit_C.2 (Ne.isUnit this)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨t, hmax.eq_of_le (RingHom.ker_ne_top _) ?_⟩
  rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
  show Polynomial.eval₂ (algebraMap ℚ Qbar) t p = 0
  rw [← Polynomial.eval_map]
  exact ht

/-- `[E : ℚ(X)]` is at most the size of some twist fibre (compiled; the argument of
`heckeDegree_of`). -/
theorem finrank_le_twistFibre {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (hT : ObjBridge.TorsionStructure) (h2 : R2fpProps Y Φ π)
    (hne : Nonempty (fieldPt Qbar ⟶ Y)) (E : Type)
    [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    [FiniteDimensional (RatFunc ℚ) E] (hM : NormalizationModel Y π E) :
    ∃ P : QML3 Qbar, Module.finrank (RatFunc ℚ) E ≤ (twistFibre P).ncard := by
  obtain ⟨h, hO, -, hval⟩ := hM
  obtain ⟨t, s, hs, hst⟩ := genericFibreCount E
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  have hpt_inj : Function.Injective pt := by
    intro ψ ψ' hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  have hpt_val : ∀ ψ ∈ s, π.val (K := Qbar) (pt ψ).left =
      OnePoint.some (algebraMap ℚ Qbar t) := by
    intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hst ψ hψ]
  rcases s.eq_empty_or_nonempty with hs0 | ⟨ψ₀, hψ₀⟩
  · obtain ⟨y⟩ := hne
    refine ⟨Quotient.out (Φ Qbar y), ?_⟩
    rw [hs0, Finset.card_empty] at hs
    omega
  set P : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ₀))
  have hP : Φ Qbar (pt ψ₀) = M3.mk P := (Quotient.out_eq _).symm
  have hmem : ∀ ψ ∈ s, Φ Qbar (pt ψ) ∈ twistFibre P := by
    intro ψ hψ
    set Q : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ))
    have hQ : Φ Qbar (pt ψ) = M3.mk Q := (Quotient.out_eq _).symm
    refine ⟨Q, hQ, ((h2 (pt ψ₀) (pt ψ) P Q hP hQ).1).1 ?_⟩
    rw [hpt_val ψ₀ hψ₀, hpt_val ψ hψ]
  have hinj : Set.InjOn (fun ψ => Φ Qbar (pt ψ)) (s : Set _) :=
    fun ψ _ ψ' _ hψ => hpt_inj ((Φ Qbar).injective hψ)
  have := Set.ncard_le_ncard_of_injOn (fun ψ => Φ Qbar (pt ψ)) hmem hinj
    (twistFibre_count hT P).1
  rw [Set.ncard_coe_finset] at this
  exact ⟨P, hs.trans this⟩

/-- `HasCM4` and its kin pass along isomorphisms of objects. -/
def qmIso_of_iso {P Q : QML3 Qbar} (f : P.Iso Q) : QMIso P.q Q.q :=
  ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩

theorem algebraMap_m16_27 : algebraMap ℚ Qbar (-16 / 27) = -16 / 27 := by
  rw [map_div₀, map_neg, map_ofNat, map_ofNat]

/-- The CM point of a CM object (compiled): for an object `P₀`, the point `y₀ = Φ⁻¹[P₀]` and its
class representative `P = out(Φ y₀)`, with an isomorphism `P₀ ≅ P`. -/
theorem out_iso {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y) (P₀ : QML3 Qbar) :
    Nonempty (P₀.Iso (Quotient.out (Φ Qbar ((Φ Qbar).symm (M3.mk P₀))))) := by
  rw [Equiv.apply_symm_apply]
  exact Quotient.exact (Quotient.out_eq (M3.mk P₀)).symm

/-- **`HeckeBranch` from `RamOfFibreCount`, `CurveChartInf`, `HeckeFibreSizes`, the kernel's
leaf `TorsionStructure` and the existence of the three CM objects** (compiled; the CM objects
come from the bundle leaf `R1R2fp`, `Pin.cm_objects_of_R1R2fp`). -/
theorem heckeBranch_of (hR : RamOfFibreCount) (hCI : CurveChartInf) (hF : HeckeFibreSizes)
    (hT : ObjBridge.TorsionStructure)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) : HeckeBranch := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hM
  obtain ⟨M, hle, hgen, h4, h3, h24⟩ := hF
  obtain ⟨hR0, hRfin, hRinf⟩ := hR E
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂₄, c₂₄⟩⟩ := hCM
  have hfinite := fibre_finite hT h2
  have hMinf := hCI Y π h1.1 h1.2.1 hfinite E hM
  have hnpos : 0 < Module.finrank (RatFunc ℚ) E := Module.finrank_pos
  -- `n ≤ M`
  obtain ⟨P₀, hP₀⟩ := finrank_le_twistFibre hT h2 h1.2.2.1 E hM
  have hnM : Module.finrank (RatFunc ℚ) E ≤ M := hP₀.trans (hle P₀)
  -- the fibre count over a finite value `t`, through a point of the fibre
  have hfib : ∀ (t : Qbar) (y : fieldPt Qbar ⟶ Y), π.val (K := Qbar) y.left = OnePoint.some t →
      {ψ : integralClosure ℚ[X] E →+* Qbar |
        ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard =
        (twistFibre (Quotient.out (Φ Qbar y))).ncard := by
    intro t y hy
    rw [chart_count hM t, ← hy, fibre_ncard h2 y]
  -- a nonempty fibre from a positive count
  have hne : ∀ (t : Qbar) (Q : Ideal (integralClosure ℚ[X] E)), Q.IsPrime →
      Q.under ℚ[X] = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) →
      ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = OnePoint.some t := by
    intro t Q hQ hQt
    have h := hRfin t Q hQ hQt
    have hc : {ψ : integralClosure ℚ[X] E →+* Qbar |
        ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h; omega
    rw [chart_count hM t] at hc
    exact Set.nonempty_of_ncard_ne_zero hc
  -- a generic finite value has fibre size `M`
  have hgenfib : ∀ (t : Qbar) (y : fieldPt Qbar ⟶ Y), π.val (K := Qbar) y.left = OnePoint.some t →
      t ≠ 0 → t ≠ algebraMap ℚ Qbar (-16 / 27) →
      (twistFibre (Quotient.out (Φ Qbar y))).ncard = M := by
    intro t y hy ht0 ht1
    set P := Quotient.out (Φ Qbar y)
    have hP : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
    obtain ⟨-, hc4, hc3, hc24⟩ := h2 y y P P hP hP
    refine hgen P (fun h => ht0 ?_) (fun h => ?_) (fun h => ht1 ?_)
    · have := (hy.symm.trans (hc4 h)); exact OnePoint.coe_injective this
    · exact OnePoint.coe_ne_infty _ (hy.symm.trans (hc3 h))
    · have := OnePoint.coe_injective (hy.symm.trans (hc24 h))
      rw [this, algebraMap_m16_27]
  -- `n = M`, through the value `1`
  have hnM' : Module.finrank (RatFunc ℚ) E = M := by
    have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
      intro a b hab
      have h' := congrArg Subtype.val hab
      change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
      rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
        IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
      exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
    haveI : (RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 1)).IsPrime :=
      RingHom.ker_isPrime _
    obtain ⟨Q₁, -, hQ₁, hQ₁u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 1)) (⊥ : Ideal (integralClosure ℚ[X] E))
      (Ideal.comap_bot_le_of_injective _ hinjB)
    have h := hRfin 1 Q₁ hQ₁ hQ₁u
    obtain ⟨y₁, hy₁⟩ := hne 1 Q₁ hQ₁ hQ₁u
    rw [hfib 1 y₁ hy₁, hgenfib 1 y₁ hy₁ one_ne_zero (by
      rw [← map_one (algebraMap ℚ Qbar)]
      exact fun h => absurd ((algebraMap ℚ Qbar).injective h) (by norm_num))] at h
    have hM0 : 0 < M := lt_of_lt_of_le hnpos hnM
    have he : Q₁.ramificationIdx ℚ[X] ≤ 1 := by
      by_contra hc
      push Not at hc
      have : 2 * M ≤ Q₁.ramificationIdx ℚ[X] * M := Nat.mul_le_mul_right M hc
      omega
    interval_cases (Q₁.ramificationIdx ℚ[X]) <;> omega
  -- the three clauses
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ hS
    by_cases h0 : Q.under ℚ[X] = ⊥
    · exact hR0 Q hQ h0
    haveI : (Q.under ℚ[X]).IsPrime := Ideal.IsPrime.under ℚ[X] Q
    obtain ⟨t, ht⟩ := exists_ker_eval (Q.under ℚ[X]) h0
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hS 0 (by simp)
      rw [ht, ← map_zero (algebraMap ℚ Qbar), ker_eval_rat]
    have ht1 : t ≠ algebraMap ℚ Qbar (-16 / 27) := by
      rintro rfl
      apply hS (-16 / 27) (by simp)
      rw [ht, ker_eval_rat]
    obtain ⟨y, hy⟩ := hne t Q hQ ht
    have h := hRfin t Q hQ ht
    rw [hfib t y hy, hgenfib t y hy ht0 ht1, ← hnM'] at h
    have : Q.ramificationIdx ℚ[X] * Module.finrank (RatFunc ℚ) E =
        1 * Module.finrank (RatFunc ℚ) E := by rw [h, _root_.one_mul]
    exact Nat.eq_of_mul_eq_mul_right hnpos this
  · intro b hb Q hQ hQb
    have hQb' : Q.under ℚ[X] =
        RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) (algebraMap ℚ Qbar b)) := by
      rw [ker_eval_rat]; exact hQb
    have h := hRfin _ Q hQ hQb'
    -- the CM object over `b` and its fibre
    have key : ∀ (P₁ : QML3 Qbar) (k : ℕ),
        π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P₁)).left = OnePoint.some (algebraMap ℚ Qbar b) →
        M ∣ k * (twistFibre (Quotient.out (Φ Qbar ((Φ Qbar).symm (M3.mk P₁))))).ncard →
        Q.ramificationIdx ℚ[X] ∣ k := by
      intro P₁ k hπ hdvd
      rw [hfib _ _ hπ, hnM'] at h
      set F := (twistFibre (Quotient.out (Φ Qbar ((Φ Qbar).symm (M3.mk P₁))))).ncard
      have hF0 : 0 < F := by
        rcases Nat.eq_zero_or_pos F with hF | hF
        · rw [hF, mul_zero] at h; omega
        · exact hF
      rw [← h] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_right hF0 hdvd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · -- `b = 0`: CM by `ℤ[i]`, index `4`
      obtain ⟨f⟩ := out_iso Φ P₄
      have hπ : π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P₄)).left =
          OnePoint.some (algebraMap ℚ Qbar 0) := by
        rw [map_zero]
        exact ((h2 _ _ P₄ P₄ (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)).2.1) c₄
      have := key P₄ 4 hπ (h4 _ (HasCM4.of_iso (qmIso_of_iso f) c₄))
      simpa [nY3] using this
    · -- `b = −16/27`: CM by `ℤ[√−6]`, index `2`
      obtain ⟨f⟩ := out_iso Φ P₂₄
      have hπ : π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P₂₄)).left =
          OnePoint.some (algebraMap ℚ Qbar (-16 / 27)) := by
        rw [((h2 _ _ P₂₄ P₂₄ (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)).2.2.2) c₂₄,
          algebraMap_m16_27]
      have := key P₂₄ 2 hπ (h24 _ (HasCM24.of_iso (qmIso_of_iso f) c₂₄))
      simpa [nY3] using this
  · -- `∞`: CM by `ℤ[ζ₃]`, index `6`
    letI := infAlg E
    intro Q hQ hQs
    have h := hRinf Q hQ hQs
    obtain ⟨f⟩ := out_iso Φ P₃
    set y₃ := (Φ Qbar).symm (M3.mk P₃)
    have hπ : π.val (K := Qbar) y₃.left = OnePoint.infty :=
      ((h2 _ _ P₃ P₃ (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)).2.2.1) c₃
    rw [chart_count_inf hMinf, ← hπ, fibre_ncard h2 y₃, hnM'] at h
    have hdvd := h3 _ (HasCM3.of_iso (qmIso_of_iso f) c₃)
    set F := (twistFibre (Quotient.out (Φ Qbar y₃))).ncard
    have hF0 : 0 < F := by
      rcases Nat.eq_zero_or_pos F with hF | hF
      · rw [hF, mul_zero] at h; omega
      · exact hF
    rw [← h] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right hF0 hdvd

/-! ### `RamOfFibreCount` is proved (from `RamCount.ramCount`) -/

/-- `ℚ(X)` is the fraction field of `ℚ[s]` through `s ↦ X⁻¹` (compiled). -/
theorem isFractionRing_infCoord : IsFractionRing InfCoord (RatFunc ℚ) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  letI : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero hX
  have hev : Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X =
      algebraMap ℚ[X] (RatFunc ℚ) :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun (Subsingleton.elim
      ((Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X).comp Polynomial.C)
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp Polynomial.C)) a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RatFunc.algebraMap_X])
  have key : ∀ (N : ℕ) (f : ℚ[X]), f.natDegree ≤ N →
      algebraMap InfCoord (RatFunc ℚ) (Polynomial.reflect N f : ℚ[X]) * RatFunc.X ^ N =
        algebraMap ℚ[X] (RatFunc ℚ) f := by
    intro N f hf
    change Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹) (Polynomial.reflect N f) *
      RatFunc.X ^ N = _
    rw [show (RatFunc.X⁻¹ : RatFunc ℚ) = ⅟RatFunc.X from (invOf_eq_inv _).symm,
      Polynomial.eval₂_reflect_mul_pow _ _ N f hf, ← hev, Polynomial.coe_eval₂RingHom]
  have hinj : Function.Injective (algebraMap InfCoord (RatFunc ℚ)) := by
    rw [injective_iff_map_eq_zero]
    show ∀ p : ℚ[X], algebraMap InfCoord (RatFunc ℚ) p = 0 → p = 0
    intro p hp
    have h1 := Polynomial.eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X p.natDegree
      (Polynomial.reflect p.natDegree p) (Polynomial.natDegree_reflect_le.trans (by simp))
    rw [Polynomial.reflect_reflect] at h1
    have hp' : Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (⅟RatFunc.X) p = 0 := by
      rw [invOf_eq_inv]; exact hp
    rw [hp', zero_mul, ← Polynomial.coe_eval₂RingHom, hev] at h1
    have h2 := (map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).1 h1.symm
    rwa [Polynomial.reflect_eq_zero_iff] at h2
  haveI : FaithfulSMul InfCoord (RatFunc ℚ) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field InfCoord (RatFunc ℚ) fun z => ?_
  set N := max (RatFunc.num z).natDegree (RatFunc.denom z).natDegree
  refine ⟨(Polynomial.reflect N (RatFunc.num z) : ℚ[X]),
    (Polynomial.reflect N (RatFunc.denom z) : ℚ[X]), ?_⟩
  have h1 := key N (RatFunc.num z) (le_max_left _ _)
  have h2 := key N (RatFunc.denom z) (le_max_right _ _)
  have hXN : (RatFunc.X : RatFunc ℚ) ^ N ≠ 0 := pow_ne_zero _ hX
  calc z = algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num z) /
        algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom z) := (RatFunc.num_div_denom z).symm
    _ = _ := by rw [← h1, ← h2, mul_div_mul_right _ _ hXN]

/-- **`RamOfFibreCount` is proved** (compiled; `RamCount.ramCount` at `ℚ[X]` and at `ℚ[s]`). -/
theorem ramOfFibreCount : RamOfFibreCount := by
  intro E _ _ _ _ _ _
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ h0
    have : Q = ⊥ := Ideal.eq_bot_of_under_eq_bot (R := ℚ[X]) h0
    subst this
    exact Ideal.ramificationIdx_bot_eq_one (R := ℚ[X]) (S := integralClosure ℚ[X] E)
  · intro t Q hQ hQt
    have hφ : RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) ≠ ⊥ := by
      obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := Qbar) t
      intro hbot
      apply hp0
      have : p ∈ RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) := hp
      rw [hbot] at this
      exact this
    have h := RamCount.ramCount (F := RatFunc ℚ) (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t)
      hφ Q hQt
    convert h using 3
    ext ψ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hψ
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · exact RingHom.congr_fun (Subsingleton.elim
          ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp Polynomial.C)
          ((Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t).comp Polynomial.C)) a
      · simp [hψ]
    · intro hψ
      have := RingHom.congr_fun hψ X
      simpa using this
  · letI := infAlg E
    haveI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
    haveI : IsPrincipalIdealRing InfCoord := inferInstanceAs (IsPrincipalIdealRing ℚ[X])
    haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
    haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    intro Q hQ hQs
    let φ : InfCoord →+* Qbar := Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 0
    have hker : RingHom.ker φ = Ideal.span {infUnif} := by
      have := ker_eval_rat 0
      rw [map_zero, map_zero, sub_zero] at this
      exact this
    have hφ : RingHom.ker φ ≠ ⊥ := by
      rw [hker]
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact Polynomial.X_ne_zero h
    have h := RamCount.ramCount (F := RatFunc ℚ) φ hφ Q (hQs.trans hker.symm)
    convert h using 3
    ext ψ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hψ
      refine Polynomial.ringHom_ext (R := ℚ) (f := ψ.comp (algebraMap InfCoord _)) (g := φ)
        (fun a => ?_) ?_
      · exact RingHom.congr_fun (Subsingleton.elim
          ((ψ.comp (algebraMap InfCoord (integralClosure InfCoord E))).comp Polynomial.C)
          (φ.comp Polynomial.C)) a
      · change ψ (algebraMap InfCoord _ infUnif) = φ X
        rw [hψ]
        exact (Polynomial.eval₂_X (algebraMap ℚ Qbar) (0 : Qbar)).symm
    · intro hψ
      have := RingHom.congr_fun hψ (X : ℚ[X])
      change ψ (algebraMap InfCoord _ infUnif) = φ X at this
      rw [this]
      exact Polynomial.eval₂_X (algebraMap ℚ Qbar) (0 : Qbar)

/-- **`HeckeBranch` with the CM objects supplied by the bundle leaf `R1R2fp`** (compiled). -/
theorem heckeBranch_of_R1R2fp (hRR : R1R2fp) (hR : RamOfFibreCount) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hT : ObjBridge.TorsionStructure) : HeckeBranch :=
  heckeBranch_of hR hCI hF hT (cm_objects_of_R1R2fp hRR)

/-! ## Part 5: the composite -/

/-- **`HeckeBranch` from the curve glue `CurveChartInf`, the moduli input `HeckeFibreSizes` and
the leaves `TorsionStructure`, `R1R2fp`** (compiled; `RamOfFibreCount` is proved). -/
theorem heckeBranch_of' (hRR : R1R2fp) (hCI : CurveChartInf) (hF : HeckeFibreSizes)
    (hT : ObjBridge.TorsionStructure) : HeckeBranch :=
  heckeBranch_of_R1R2fp hRR ramOfFibreCount hCI hF hT

/-- **`CoverModelOfHecke` from ts-hecke's reductions** (compiled). Hypotheses:
* leaves: R1conn (`Y3Connected`, Shimura/Deligne `π₀` with reciprocity), the kernel's
  `ObjBridge.TorsionStructure` (Mumford §4) and the bundle leaf `R1R2fp`;
* glue: `CurveGaloisChart`, `CurveChartInf` (curve theory with no moduli), `HeckeFibreSizes`
  (the moduli count of Baba–Granath's elliptic table) and `HeckeNoVertRam` (Lemma NV, open). -/
theorem coverModelOfHecke_of_tsHecke (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hCG : CurveGaloisChart) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : CoverModelOfHecke :=
  coverModelOfHecke_of_pieces (heckeNormalization_of hconn hCG hT) (heckeDegree_of_torsion hT)
    (heckeBranch_of' hRR hCI hF hT) hV

end TSHecke

end

#print axioms TSHecke.exists_surjective_of_R1fp
#print axioms TSHecke.connectedSpace_of_R1fp
#print axioms TSHecke.irreducibleSpace_of_R1fp
#print axioms TSHecke.irreducibleSpace_of_connected
#print axioms TSHecke.heckeIrreducible_of_connected
#print axioms TSHecke.connected_of_heckeIrreducible
#print axioms TSHecke.pullLevel
#print axioms TSHecke.innerIso
#print axioms TSHecke.exists_sub_liftO
#print axioms TSHecke.twistFibre_count
#print axioms TSHecke.heckeDegree_of
#print axioms TSHecke.genericFibreCount
#print axioms TSHecke.heckeDegree_of_torsion
#print axioms TSHecke.fibre_transitive
#print axioms TSHecke.fibre_transitive_aut
#print axioms TSHecke.pi_invariant_twist
#print axioms TSHecke.pi_invariant_rightMul
#print axioms TSHecke.fibre_finite
#print axioms TSHecke.heckeNormalizationIrr_of
#print axioms TSHecke.heckeNormalization_of
#print axioms TSHecke.chart_count
#print axioms TSHecke.chart_count_inf
#print axioms TSHecke.fibre_ncard
#print axioms TSHecke.ker_eval_rat
#print axioms TSHecke.exists_ker_eval
#print axioms TSHecke.finrank_le_twistFibre
#print axioms TSHecke.heckeBranch_of
#print axioms TSHecke.heckeBranch_of_R1R2fp
#print axioms TSHecke.isFractionRing_infCoord
#print axioms TSHecke.ramOfFibreCount
#print axioms TSHecke.heckeBranch_of'
#print axioms TSHecke.coverModelOfHecke_of_tsHecke
