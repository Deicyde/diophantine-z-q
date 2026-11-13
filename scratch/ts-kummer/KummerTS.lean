import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.NumberTheory.RamificationInertia.Basic

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
# Copy of `scratch/t-purity3/PurityDim2.lean` (origin/wip/t-purity3, commit 7e4d4dd0), verbatim
except for the `import Mathlib` line and the trailing `#print axioms` lines, wrapped in a section
so that its `open`s stay local. It proves `TPurity3.purityGlobalDim2`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

section TPurity3Copy

/-!
# Zariski–Nagata purity over a two-dimensional regular local base (t-purity3)

Self-contained concatenation of `PurityFree.lean`, the `S₂` section of `FreeDim2.lean` and
`Regular2.lean`, plus the final assembly:

* `TPurity3.etale_of_free_of_isUnramifiedIn_height_one` — purity for finite free algebras over a
  Noetherian local domain;
* `TPurity3.uniqueFactorizationMonoid_of_dim2` — a 2-dimensional regular local domain is a UFD;
* `TPurity3.normalFreeDim2` — a normal domain, finite and torsion-free over a 2-dimensional regular
  local ring, is free;
* **`TPurity3.purityGlobalDim2`** — purity of the branch locus for such an algebra (global over a
  local base), with no hypotheses beyond the statement;
* `TPurity3.purityGlobalDim1` — the same over a 1-dimensional regular local base.
-/

open IsLocalRing Pointwise

/-!
# Purity of the branch locus for finite free algebras (t-purity3)

A finite free algebra `S` over a Noetherian local domain `R` (not a field) that is unramified at
every prime lying over a height-one prime of `R` is étale.  Proof: the discriminant `d` of a basis
is not in any height-one prime (fibre argument + trace form), hence a unit (Krull's principal
ideal theorem), hence the closed fibre is unramified and Nakayama kills `Ω[S⁄R]`.
-/

open Algebra TensorProduct

namespace TPurity3

section Pi

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (L : ι → Type*) [∀ i, CommRing (L i)] [∀ i, Algebra k (L i)] [∀ i, Module.Finite k (L i)]

theorem trace_pi_apply (x : ∀ i, L i) :
    Algebra.trace k (∀ i, L i) x = ∑ i, Algebra.trace k (L i) (x i) := by
  classical
  let b := fun i => Module.finBasis k (L i)
  let B := Pi.basis b
  rw [Algebra.trace_eq_matrix_trace B, Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [B, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]

end Pi

section Field

variable (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A] [Module.Finite k A]

theorem traceForm_nondegenerate_of_formallyUnramified [FormallyUnramified k A] :
    (traceForm k A).Nondegenerate := by
  classical
  have : FormallyEtale k A := FormallyEtale.of_formallyUnramified_of_field k A
  obtain ⟨I, hI, L, _, _, e, hsep⟩ := (FormallyEtale.iff_exists_algEquiv_prod k A).mp this
  have : Fintype I := Fintype.ofFinite I
  have hfin : ∀ i, Module.Finite k (L i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp e.toLinearMap)
      ((Function.surjective_eval i).comp e.surjective)
  have hsym : ∀ x y, traceForm k A x y = traceForm k A y x := by
    intro x y; simp [traceForm_apply, mul_comm]
  have hL : (traceForm k A).SeparatingLeft := by
    intro x hx
    apply e.injective
    rw [map_zero]
    funext i
    have key : ∀ z : L i, traceForm k (L i) (e x i) z = 0 := by
      intro z
      have h := hx (e.symm (Pi.single i z))
      rw [traceForm_apply, ← Algebra.trace_eq_of_algEquiv e, map_mul, AlgEquiv.apply_symm_apply,
        trace_pi_apply, Finset.sum_eq_single i] at h
      · simpa [traceForm_apply] using h
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    exact (traceForm_nondegenerate k (L i)).1 (e x i) key
  exact ⟨hL, fun y hy => hL y fun x => by rw [hsym]; exact hy x⟩

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
theorem formallyUnramified_of_traceForm_nondegenerate (h : (traceForm k A).Nondegenerate) :
    FormallyUnramified k A := by
  classical
  have hred : IsReduced A := by
    refine ⟨fun n hn => h.1 n fun y => ?_⟩
    rw [traceForm_apply, mul_comm]
    exact (Algebra.isNilpotent_trace_of_isNilpotent (R := k)
      (Commute.isNilpotent_mul_left (Commute.all _ _) hn)).eq_zero
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  let e := (IsArtinianRing.equivPi A).restrictScalars k
  have : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  rw [FormallyUnramified.iff_of_equiv e, FormallyUnramified.pi_iff]
  intro M
  have : FormallyUnramified k (A ⧸ M.asIdeal) := by
    have : Algebra.IsSeparable k (A ⧸ M.asIdeal) := by
      refine ((traceForm_nondegenerate_tfae k (A ⧸ M.asIdeal)).out 2 1).mp ?_
      intro htr
      have hy := h.1 (e.symm (Pi.single M 1)) fun z => by
        rw [traceForm_apply, ← Algebra.trace_eq_of_algEquiv e, map_mul,
          AlgEquiv.apply_symm_apply, trace_pi_apply, Finset.sum_eq_single M]
        · simp [htr]
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
      have : (Pi.single M 1 : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) = 0 := by
        simpa using congr(e $hy)
      simpa using congr_fun this M
    exact FormallyUnramified.of_isSeparable k _
  exact this

theorem formallyUnramified_iff_traceForm_nondegenerate :
    FormallyUnramified k A ↔ (traceForm k A).Nondegenerate :=
  ⟨fun _ => traceForm_nondegenerate_of_formallyUnramified k A,
    formallyUnramified_of_traceForm_nondegenerate k A⟩

theorem formallyUnramified_iff_discr_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k A) : FormallyUnramified k A ↔ discr k b ≠ 0 := by
  rw [formallyUnramified_iff_traceForm_nondegenerate, discr_def, traceMatrix_of_basis,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]

end Field


section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S] (A : Type*) [CommRing A] [Algebra R A]

theorem trace_baseChange_tmul (s : S) :
    Algebra.trace A (A ⊗[R] S) (1 ⊗ₜ s) = algebraMap R A (Algebra.trace R S s) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext t
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem discr_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) :
    discr A (Algebra.TensorProduct.basis A b) = algebraMap R A (discr R b) := by
  rw [discr_def, discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [traceMatrix_apply, traceForm_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, trace_baseChange_tmul]

end BaseChange

section Krull

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem exists_height_one_mem {x : R} (hx0 : x ≠ 0) (hx : ¬ IsUnit x) :
    ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P := by
  obtain ⟨P, hP⟩ := (Ideal.span {x}).nonempty_minimalPrimes (by simpa using hx)
  have hPp : P.IsPrime := hP.1.1
  have hxP : x ∈ P := hP.1.2 (Ideal.mem_span_singleton_self x)
  refine ⟨P, hPp, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP) ?_, hxP⟩
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  intro h0
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  exact hx0 (by simpa [h0] using hxP)

theorem isUnit_of_forall_height_one [IsLocalRing R] (hR : ¬ IsField R) {d : R}
    (hd : ∀ P : Ideal R, P.IsPrime → P.height = 1 → d ∉ P) : IsUnit d := by
  by_contra hdu
  by_cases hd0 : d = 0
  · have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      rwa [Ne, ← IsLocalRing.isField_iff_maximalIdeal_eq]
    obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    obtain ⟨P, hP, h1, -⟩ := exists_height_one_mem hx0 ((IsLocalRing.mem_maximalIdeal x).mp hxm)
    exact hd P hP h1 (hd0 ▸ P.zero_mem)
  · obtain ⟨P, hP, h1, hdP⟩ := exists_height_one_mem hd0 hdu
    exact hd P hP h1 hdP

end Krull

section Main

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The fibre of `R → S` at `P` is formally unramified if `P` is unramified in `S`. -/
theorem formallyUnramified_fiber (P : Ideal R) [P.IsPrime] (h : Algebra.IsUnramifiedIn S P) :
    FormallyUnramified P.ResidueField (P.Fiber S) := by
  rw [formallyUnramified_iff_forall]
  intro Q'
  let Q : Ideal S := Q'.asIdeal.comap
    (Algebra.TensorProduct.includeRight (R := R) (A := P.ResidueField) (B := S)).toRingHom
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q.LiesOver P := by
    constructor
    rw [Ideal.under, Ideal.comap_comap]
    have : (Algebra.TensorProduct.includeRight (R := R) (A := P.ResidueField)
        (B := S)).toRingHom.comp (algebraMap R S) = algebraMap R (P.Fiber S) :=
      (Algebra.TensorProduct.includeRight (R := R) (A := P.ResidueField) (B := S)).comp_algebraMap
    rw [this]
    exact Ideal.LiesOver.over
  have := h Q hQ hQP
  exact IsUnramifiedAt.residueField P Q Q'.asIdeal rfl

/-- **Purity of the branch locus for finite free algebras.** -/
theorem etale_of_free_of_isUnramifiedIn_height_one [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] (hR : ¬ IsField R) [Module.Free R S] [Module.Finite R S]
    (h : ∀ P : Ideal R, P.IsPrime → P.height = 1 → Algebra.IsUnramifiedIn S P) :
    Algebra.Etale R S := by
  classical
  let b := Module.Free.chooseBasis R S
  have hd : ∀ P : Ideal R, P.IsPrime → P.height = 1 → discr R b ∉ P := by
    intro P hP h1 hdP
    have hF := formallyUnramified_fiber P (h P hP h1)
    have := (formallyUnramified_iff_discr_ne_zero _ _
      (Algebra.TensorProduct.basis P.ResidueField b)).mp hF
    rw [discr_baseChange] at this
    exact this (Ideal.algebraMap_residueField_eq_zero.mpr hdP)
  have hu : IsUnit (discr R b) := isUnit_of_forall_height_one hR hd
  let k := IsLocalRing.ResidueField R
  have hk : FormallyUnramified k (k ⊗[R] S) := by
    rw [formallyUnramified_iff_discr_ne_zero _ _ (Algebra.TensorProduct.basis k b),
      discr_baseChange]
    exact (hu.map (algebraMap R k)).ne_zero
  have hU : FormallyUnramified R S := by
    rw [Algebra.formallyUnramified_iff] at hk ⊢
    letI : Algebra S (k ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    have e := KaehlerDifferential.tensorKaehlerEquivBase R k S (k ⊗[R] S)
    have h1 : Subsingleton (k ⊗[R] Ω[S⁄R]) := e.toEquiv.subsingleton
    have : Module.Finite R Ω[S⁄R] := Module.Finite.trans S _
    exact IsLocalRing.subsingleton_tensorProduct.mp h1
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Main

section Dim2

universe u

/-- Finite flat version: over a local ring, finite flat modules are free. -/
theorem etale_of_flat_of_isUnramifiedIn_height_one {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    [Module.Flat R S] [Module.Finite R S]
    (h : ∀ P : Ideal R, P.IsPrime → P.height = 1 → Algebra.IsUnramifiedIn S P) :
    Algebra.Etale R S :=
  have : Module.Free R S := Module.free_of_flat_of_isLocalRing
  etale_of_free_of_isUnramifiedIn_height_one hR h

/-- **Leaf candidate (A).** A normal domain that is a finite torsion-free algebra over a
two-dimensional regular local ring is a free module.  A consequence of Serre's normality
criterion (normal ⇒ `S₂`, so `S` is Cohen–Macaulay in dimension 2), going-down for a normal
base, and miracle flatness (Matsumura, *Commutative Ring Theory*, Thm 23.1), plus "finite flat
over local is free".  Equivalently (Auslander–Buchsbaum): finite reflexive modules over a
two-dimensional regular local ring are free. -/
def NormalFreeDim2 : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsRegularLocalRing R],
    ringKrullDim R = 2 → ∀ [IsDomain S] [IsIntegrallyClosed S] [Module.Finite R S],
    Function.Injective (algebraMap R S) → Module.Free R S

/-- **Purity in dimension 2, global form over a local base (the case Prop. TS uses)**, from
leaf (A). -/
theorem etale_of_normalFreeDim2 (hA : NormalFreeDim2.{u}) {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsRegularLocalRing R] (hdim : ringKrullDim R = 2)
    [IsDomain S] [IsIntegrallyClosed S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (h : ∀ P : Ideal R, P.IsPrime → P.height = 1 → Algebra.IsUnramifiedIn S P) :
    Algebra.Etale R S := by
  have : Module.Free R S := hA R S hdim hinj
  have : IsDomain R := hinj.isDomain _
  have hR : ¬ IsField R := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [hdim] at this
    exact absurd this (by decide)
  exact etale_of_free_of_isUnramifiedIn_height_one hR h

/-- The same purity statement, as a Prop (what the consumer needs). -/
def PurityGlobalDim2 : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsRegularLocalRing R],
    ringKrullDim R = 2 → ∀ [IsDomain S] [IsIntegrallyClosed S] [Module.Finite R S],
    Function.Injective (algebraMap R S) →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → Algebra.IsUnramifiedIn S P) →
    Algebra.Etale R S

theorem purityGlobalDim2_of_normalFreeDim2 (hA : NormalFreeDim2.{u}) : PurityGlobalDim2.{u} :=
  fun _ _ _ _ _ _ hdim _ _ _ hinj h => etale_of_normalFreeDim2 hA hdim hinj h

end Dim2

section S2

variable {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S]

/-- In a normal Noetherian domain, a prime of the form `(x : s)` with `s ∉ (x)` has height
`≤ 1`. -/
theorem height_le_one_of_colon {x s : S} (hx : x ≠ 0) (hs : s ∉ Ideal.span {x})
    {Q : Ideal S} [hQp : Q.IsPrime] (hQ : ∀ q, q ∈ Q ↔ q * s ∈ Ideal.span {x}) :
    Q.height ≤ 1 := by
  classical
  let K := FractionRing S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hx' : algebraMap S K x ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx
  let t : K := algebraMap S K s / algebraMap S K x
  have ht : ∀ q ∈ Q, ∃ a : S, t * algebraMap S K q = algebraMap S K a := by
    intro q hq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp ((hQ q).mp hq)
    refine ⟨a, ?_⟩
    simp only [t]
    rw [div_mul_eq_mul_div, div_eq_iff hx', ← map_mul, ← map_mul, ha, mul_comm q s]
  have hxQ : x ∈ Q := (hQ x).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x))
  by_cases hcase : ∀ q ∈ Q, ∃ q' ∈ Q, t * algebraMap S K q = algebraMap S K q'
  · exfalso
    let N : Submodule S K := Submodule.map (Algebra.linearMap S K) Q
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap S K x ∈ N := Submodule.mem_map_of_mem hxQ
      rw [h, Submodule.mem_bot] at this
      exact hx' this
    have hNfg : N.FG := (IsNoetherian.noetherian Q).map _
    have hint : IsIntegral S t := by
      refine isIntegral_of_smul_mem_submodule N hN hNfg t ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hn
      obtain ⟨q', hq', e⟩ := hcase q hq
      rw [smul_eq_mul, Algebra.linearMap_apply, e]
      exact Submodule.mem_map_of_mem hq'
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    apply hs
    rw [Ideal.mem_span_singleton']
    refine ⟨a, hinj ?_⟩
    rw [map_mul, ha]
    simp only [t]
    rw [div_mul_cancel₀ _ hx']
  · push Not at hcase
    obtain ⟨q₀, hq₀, hne⟩ := hcase
    obtain ⟨u, hu⟩ := ht q₀ hq₀
    have huQ : u ∉ Q := fun h => hne u h hu
    have hmin : Q ∈ (Ideal.span {q₀}).minimalPrimes := by
      refine ⟨⟨hQp, (Ideal.span_singleton_le_iff_mem _).mpr hq₀⟩, ?_⟩
      rintro P ⟨hP, hq₀P⟩ hPQ q hq
      obtain ⟨a, ha⟩ := ht q hq
      have : u * q = q₀ * a := by
        apply hinj
        rw [map_mul, map_mul, ← hu, ← ha]
        ring
      have hmem : u * q ∈ P := by
        rw [this]
        exact Ideal.mul_mem_right _ _ ((Ideal.span_singleton_le_iff_mem _).mp hq₀P)
      rcases hP.mem_or_mem hmem with h | h
      · exact absurd (hPQ h) huQ
      · exact h
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hmin

/-- **Serre's `S₂` for normal domains** (the form used): if `x ≠ 0` and every prime containing
`x` and `y` has height `≥ 2`, then `y` is a non-zero-divisor on `S ⧸ (x)`. -/
theorem mem_span_of_mul_mem {x y s : S} (hx : x ≠ 0)
    (hxy : ∀ Q : Ideal S, Q.IsPrime → x ∈ Q → y ∈ Q → 2 ≤ Q.height)
    (h : y * s ∈ Ideal.span {x}) : s ∈ Ideal.span {x} := by
  by_contra hs
  let m : S ⧸ Ideal.span {x} := Ideal.Quotient.mk _ s
  have hm : m ≠ 0 := by
    simpa [m, Ideal.Quotient.eq_zero_iff_mem] using hs
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S m hm
  obtain ⟨hPp, m', hm'⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective m'
  have hQ : ∀ q, q ∈ P ↔ q * s' ∈ Ideal.span {x} := by
    intro q
    rw [hm', Submodule.mem_colon_singleton, Submodule.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem,
      map_mul, Algebra.smul_def]
    rfl
  have hs' : s' ∉ Ideal.span {x} := by
    intro h'
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hQ, one_mul]
    exact h'
  have h1 := height_le_one_of_colon hx hs' hQ
  have hxP : x ∈ P := hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def]
    change Ideal.Quotient.mk _ x * Ideal.Quotient.mk _ s = 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x))
  have hyP : y ∈ P := hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def]
    change Ideal.Quotient.mk _ y * Ideal.Quotient.mk _ s = 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact h)
  have h2 := hxy P hPp hxP hyP
  have := h2.trans h1
  exact absurd this (by norm_num)

end S2

section Pair

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem height_maximalIdeal_le_one_of_eq_span_singleton {w : R}
    (h : maximalIdeal R = Ideal.span {w}) : (maximalIdeal R).height ≤ 1 := by
  have hw : w ∈ maximalIdeal R := h ▸ Ideal.mem_span_singleton_self w
  have := Ideal.height_span_singleton_le_one (R := R) (x := w) ((mem_maximalIdeal w).mp hw)
  rwa [← h] at this

theorem ne_zero_of_pair {z w : R} (hm : maximalIdeal R = Ideal.span {z, w})
    (hht : (maximalIdeal R).height = 2) : z ≠ 0 := by
  rintro rfl
  have h := height_maximalIdeal_le_one_of_eq_span_singleton (w := w) (by rw [hm]; simp)
  rw [hht] at h
  norm_num at h

theorem span_pair_comm (z w : R) : Ideal.span {z, w} = Ideal.span ({w, z} : Set R) := by
  rw [Set.pair_comm]

/-- In a 2-dimensional local ring with `𝔪 = (z, w)`, `w` is a non-zero-divisor mod `z`. -/
theorem mem_span_of_mul_mem_pair {z w r : R} (hm : maximalIdeal R = Ideal.span {z, w})
    (hht : (maximalIdeal R).height = 2) (h : w * r ∈ Ideal.span {z}) :
    r ∈ Ideal.span {z} := by
  classical
  by_contra hr
  let A := R ⧸ Ideal.span {z}
  let π : R →+* A := Ideal.Quotient.mk _
  have hzm : z ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have hwm : w ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr
    (Ideal.span_singleton_ne_top ((mem_maximalIdeal z).mp hzm))
  have : IsLocalRing A := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal R).map π = Ideal.span {π w} := by
    rw [hm, Ideal.map_span]
    simp [π, Set.image_insert_eq, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self z)]
    try rfl
  have hne : Ideal.span {π w} ≠ ⊤ := by
    rw [← hmap]
    intro htop
    have h1 : (1 : A) ∈ (maximalIdeal R).map π := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ maximalIdeal R, π a = 1 := by
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
      exact h1
    have : a - 1 ∈ Ideal.span {z} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [π, sub_eq_zero] using ha1
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem ha (Ideal.span_le.mpr (by simpa using hzm) this)
      simp at this
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
  have ha0 : π r ≠ 0 := fun h0 => hr (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hex : ∃ i, π r ∉ Ideal.span {π w} ^ i := by
    by_contra hall
    push Not at hall
    have : π r ∈ ⨅ i : ℕ, Ideal.span {π w} ^ i := Submodule.mem_iInf _ |>.mpr hall
    rw [hK] at this
    exact ha0 this
  let i := Nat.find hex
  have hi : π r ∉ Ideal.span {π w} ^ i := Nat.find_spec hex
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.one_eq_top] at hi
    exact hi Submodule.mem_top
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hmemj : π r ∈ Ideal.span {π w} ^ j := by
    have := Nat.find_min hex (show j < i by omega)
    push Not at this
    exact this
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmemj
  obtain ⟨c', hc'⟩ := hmemj
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  have hcm : c ∉ maximalIdeal R := by
    intro hc
    apply hi
    rw [hj, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    have : π c ∈ Ideal.span {π w} := hmap ▸ Ideal.mem_map_of_mem π hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨d, by rw [← hc', ← hd, pow_succ]; ring⟩
  have hcu : IsUnit c := by
    by_contra hcu; exact hcm ((mem_maximalIdeal c).mpr hcu)
  have hw0 : π w * π r = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact h
  rw [← hc'] at hw0
  have hwj : w ^ (j + 1) * c ∈ Ideal.span {z} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : π (w ^ (j + 1) * c) = π w * (Ideal.Quotient.mk _ c * π w ^ j) := by
      simp only [map_mul, map_pow, π]; ring
    exact this.trans hw0
  have hwj' : w ^ (j + 1) ∈ Ideal.span {z} := by
    obtain ⟨u, rfl⟩ := hcu
    have := Ideal.mul_mem_right (↑u⁻¹ : R) _ hwj
    simpa [mul_assoc] using this
  have hrad : maximalIdeal R ≤ (Ideal.span {z}).radical := by
    rw [hm, Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
    · exact ⟨j + 1, hwj'⟩
  have hmin : maximalIdeal R ∈ (Ideal.span {z}).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.span_le.mpr (by simpa using hzm)⟩, ?_⟩
    rintro P ⟨hP, hzP⟩ -
    exact hrad.trans ((Ideal.radical_mono hzP).trans hP.radical.le)
  have := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  rw [hht] at this
  norm_num at this

/-- A finite module of depth `2` over a local ring with `𝔪 = (z, w)` is free. -/
theorem free_of_regular_pair (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {z w : R} (hm : maximalIdeal R = Ideal.span {z, w}) (hz : IsSMulRegular M z)
    (hw : ∀ m : M, w • m ∈ z • (⊤ : Submodule R M) → m ∈ z • (⊤ : Submodule R M)) :
    Module.Free R M := by
  have hzm : z ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have hwm : w ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  let A := R ⧸ Ideal.span {z}
  let N := QuotSMulTop z M
  have hfinA : Module.Finite A N := Module.Finite.of_restrictScalars_finite R A N
  have hfpA : Module.FinitePresentation A N := Module.finitePresentation_of_finite A N
  let wA : A := Ideal.Quotient.mk _ w
  have hwjac : wA ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.mem_jacobson_bot]
    intro t
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    have : IsUnit (w * t + 1) := by
      by_contra hu
      have h1 : w * t + 1 ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hu
      have h2 : w * t ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hwm
      have h3 := (maximalIdeal R).sub_mem h1 h2
      simp only [add_sub_cancel_left] at h3
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    simpa [wA] using this.map (Ideal.Quotient.mk (Ideal.span {z}))
  have hwreg : IsSMulRegular N wA := by
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro m hm0
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hm1 : (Submodule.Quotient.mk (w • s) : N) = 0 := hm0
    rw [Submodule.Quotient.mk_eq_zero] at hm1
    rw [Submodule.Quotient.mk_eq_zero]
    exact hw s hm1
  have hmaxA : (Ideal.span {wA}).IsMaximal := by
    have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {z})) = Ideal.span {wA} := by
      rw [hm, Ideal.map_span]
      simp [wA, Set.image_insert_eq, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self z)]
      try rfl
    rw [← hmap]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker, Ideal.span_le]; simpa using hzm)
  let _ : Field (A ⧸ Ideal.span {wA}) := Ideal.Quotient.field _
  have hfree1 : Module.Free (A ⧸ Ideal.span {wA}) (QuotSMulTop wA N) :=
    Module.Free.of_divisionRing _ _
  have hfreeA : Module.Free A N := (Module.free_quotSMulTop_iff_free A N hwjac hwreg).mp hfree1
  have hfpR : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have hzjac : z ∈ (⊥ : Ideal R).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hzm
  exact (Module.free_quotSMulTop_iff_free R M hzjac hz).mp hfreeA

end Pair

section UFD

theorem exists_pair_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) : ∃ x y : R, maximalIdeal R = Ideal.span {x, y} := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have h2 : (maximalIdeal R).spanFinrank = 2 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at this
    exact_mod_cast this
  rw [h2] at hcard
  obtain ⟨x, y, -, rfl⟩ := Finset.card_eq_two.mp hcard
  exact ⟨x, y, by rw [← hs]; simp [Ideal.span]⟩

theorem height_maximalIdeal_of_dim2 {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 2) : (maximalIdeal R).height = 2 := by
  have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hdim] at this
  exact WithBot.coe_injective (this.trans rfl)

/-- A free ideal of a domain is principal. -/
theorem exists_eq_span_singleton_of_free {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R)
    [Module.Free R P] : ∃ b : R, P = Ideal.span {b} := by
  classical
  let bs := Module.Free.chooseBasis R P
  by_cases hι : IsEmpty (Module.Free.ChooseBasisIndex R P)
  · refine ⟨0, ?_⟩
    rw [Ideal.span_singleton_eq_bot.mpr rfl, eq_bot_iff]
    intro p hp
    have : (⟨p, hp⟩ : P) = 0 := by
      rw [← bs.repr.symm_apply_apply ⟨p, hp⟩, Subsingleton.elim (bs.repr ⟨p, hp⟩) 0, map_zero]
    simpa using congrArg Subtype.val this
  · obtain ⟨i⟩ := not_isEmpty_iff.mp hι
    have hall : ∀ j, j = i := by
      intro j
      by_contra hji
      have hinj : Function.Injective ![j, i] := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
      have hli : LinearIndependent R ![bs j, bs i] := by
        have := bs.linearIndependent.comp _ hinj
        convert this using 1
        ext k
        fin_cases k <;> rfl
      obtain ⟨h1, -⟩ := LinearIndependent.pair_iff.mp hli ((bs i : R)) (-(bs j : R))
        (by ext; simp [mul_comm])
      exact bs.ne_zero i (Subtype.ext (by simpa using h1))
    have hrange : Set.range bs = {bs i} := by
      ext p
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; rw [hall j]
      · rintro rfl; exact ⟨i, rfl⟩
    refine ⟨bs i, ?_⟩
    have := bs.span_eq
    rw [hrange] at this
    have h2 := congrArg (Submodule.map P.subtype) this
    rw [Submodule.map_span, Submodule.map_subtype_top, Set.image_singleton] at h2
    exact h2.symm

/-- **A two-dimensional regular local domain is a UFD.** -/
theorem uniqueFactorizationMonoid_of_dim2 {R : Type*} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (hdim : ringKrullDim R = 2) : UniqueFactorizationMonoid R := by
  obtain ⟨x, y, hm⟩ := exists_pair_span_eq_maximalIdeal hdim
  have hht := height_maximalIdeal_of_dim2 (R := R) hdim
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
  obtain ⟨q, hqI, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨P, hPmin, hPI⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr hqI)
  have hPp : P.IsPrime := hPmin.1.1
  have hqP : q ∈ P := hPmin.1.2 (Ideal.mem_span_singleton_self q)
  have hP1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hPmin
  have hnot : ¬ (x ∈ P ∧ y ∈ P) := by
    rintro ⟨hx, hy⟩
    have hle : maximalIdeal R ≤ P := by
      rw [hm, Ideal.span_le]
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> assumption
    have heq : P = maximalIdeal R := ((maximalIdeal.isMaximal R).eq_of_le hPp.ne_top hle).symm
    rw [heq, hht] at hP1
    norm_num at hP1
  obtain ⟨z, w, hmzw, hwP⟩ : ∃ z w : R, maximalIdeal R = Ideal.span {z, w} ∧ w ∉ P := by
    by_cases hy : y ∈ P
    · exact ⟨y, x, by rw [hm, span_pair_comm], fun hx => hnot ⟨hx, hy⟩⟩
    · exact ⟨x, y, hm, hy⟩
  have hz0 : z ≠ 0 := ne_zero_of_pair hmzw hht
  have hfree : Module.Free R P := by
    refine free_of_regular_pair P hmzw ?_ ?_
    · intro a b hab
      apply Subtype.ext
      have : z * (a : R) = z * b := by simpa using congrArg Subtype.val hab
      exact mul_left_cancel₀ hz0 this
    · intro m hm'
      rw [Submodule.mem_smul_pointwise_iff_exists] at hm' ⊢
      obtain ⟨p', -, hp'⟩ := hm'
      have hp'v : z * (p' : R) = w * (m : R) := by simpa using congrArg Subtype.val hp'
      have hmem : w * (m : R) ∈ Ideal.span {z} :=
        Ideal.mem_span_singleton'.mpr ⟨p', by rw [mul_comm]; exact hp'v⟩
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (mem_span_of_mul_mem_pair hmzw hht hmem)
      have h1 : z * (w * r) = z * p' := by
        rw [hp'v, ← hr]; ring
      have h2 : w * r = p' := mul_left_cancel₀ hz0 h1
      have hrP : r ∈ P := by
        have : w * r ∈ P := h2 ▸ p'.2
        rcases hPp.mem_or_mem this with h | h
        · exact absurd h hwP
        · exact h
      exact ⟨⟨r, hrP⟩, Submodule.mem_top, Subtype.ext (by simp [← hr, mul_comm])⟩
  obtain ⟨b, hb⟩ := exists_eq_span_singleton_of_free P
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hq0
    rw [hb, Ideal.span_singleton_eq_bot.mpr rfl] at hqP
    simpa using hqP
  refine ⟨b, hPI (hb ▸ Ideal.mem_span_singleton_self b), ?_⟩
  exact (Ideal.span_singleton_prime hb0).mp (hb ▸ hPp)

theorem isIntegrallyClosed_of_dim2 {R : Type*} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (hdim : ringKrullDim R = 2) : IsIntegrallyClosed R :=
  have := uniqueFactorizationMonoid_of_dim2 (R := R) hdim
  inferInstance

end UFD

section Final

universe v

theorem normalFreeDim2 : NormalFreeDim2.{v} := by
  intro R S _ _ _ _ hdim _ _ _ hinj
  have : IsDomain R := hinj.isDomain _
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_dim2 hdim
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Algebra.HasGoingDown R S := inferInstance
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  obtain ⟨x, y, hm⟩ := exists_pair_span_eq_maximalIdeal hdim
  have hht := height_maximalIdeal_of_dim2 (R := R) hdim
  have hx0 : x ≠ 0 := ne_zero_of_pair hm hht
  set x' := algebraMap R S x with hx'
  set y' := algebraMap R S y with hy'
  have hx'0 : x' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
  have hxy : ∀ Q : Ideal S, Q.IsPrime → x' ∈ Q → y' ∈ Q → 2 ≤ Q.height := by
    intro Q hQ hxQ hyQ
    have hle : maximalIdeal R ≤ Q.under R := by
      rw [hm, Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxQ
      · exact hyQ
    have heq : Q.under R = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
    have : Q.LiesOver (maximalIdeal R) := ⟨heq.symm⟩
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) Q, hht]
    exact le_self_add
  have hS2 : ∀ s : S, y' * s ∈ Ideal.span {x'} → s ∈ Ideal.span {x'} :=
    fun s hs => mem_span_of_mul_mem hx'0 hxy hs
  refine free_of_regular_pair S hm ?_ ?_
  · intro a b hab
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hx'0 hab
  · intro s hs
    rw [Submodule.mem_smul_pointwise_iff_exists] at hs ⊢
    obtain ⟨s', -, hs'⟩ := hs
    have hmem : y' * s ∈ Ideal.span {x'} := by
      refine Ideal.mem_span_singleton'.mpr ⟨s', ?_⟩
      simpa [Algebra.smul_def, mul_comm] using hs'
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hS2 s hmem)
    exact ⟨a, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]; exact ha⟩

/-- **Purity of the branch locus over a two-dimensional regular local ring** (global form over a
local base): proved. -/
theorem purityGlobalDim2 : PurityGlobalDim2.{v} :=
  purityGlobalDim2_of_normalFreeDim2 normalFreeDim2

/-- The same over a one-dimensional regular local ring (a DVR). -/
theorem purityGlobalDim1 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 1) [IsDomain S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (h : ∀ P : Ideal R, P.IsPrime → P.height = 1 → Algebra.IsUnramifiedIn S P) :
    Algebra.Etale R S := by
  classical
  have : IsDomain R := hinj.isDomain _
  have hR : ¬ IsField R := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [hdim] at this
    exact absurd this (by decide)
  have hprin : (maximalIdeal R).IsPrincipal := by
    have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
    obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
    have h1 : (maximalIdeal R).spanFinrank = 1 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [hdim] at this
      exact_mod_cast this
    rw [h1] at hcard
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ⟨a, by rw [← hs]; simp [Ideal.span]⟩
  have : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hR).out 5 1).mp hprin
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.Free R S := Module.free_of_finite_type_torsion_free'
  exact etale_of_free_of_isUnramifiedIn_height_one hR h

/-- Over an integral extension with going-down, a prime over a height-one prime has height one. -/
theorem height_eq_one_of_liesOver {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal R) [P.IsPrime] (hP : P.height = 1) (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] :
    Q.height = 1 := by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Q, hP]
  have hmin : Q ∈ (P.map (algebraMap R S)).minimalPrimes := by
    have := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) Q
    have hu : Q.under R = P := (Ideal.LiesOver.over).symm
    rwa [hu] at this
  rw [Ideal.minimalPrimes_eq_comap] at hmin
  obtain ⟨J, hJ, hJQ⟩ := hmin
  have hQJ : Q.map (Ideal.Quotient.mk _) = J := by
    rw [← hJQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [hQJ]
  have : J.IsPrime := hJ.1.1
  rw [Ideal.height_eq_zero_iff.mpr hJ, add_zero]

/-- `purityGlobalDim2` with the hypothesis on the height-one primes of `S` ("étale in
codimension one" upstairs, as in the kernel's `PkgI2.PurityBranchLocus`). -/
theorem purityGlobalDim2' {R S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) [IsDomain S] [IsIntegrallyClosed S]
    [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    (h : ∀ Q : Ideal S, [Q.IsPrime] → Q.height = 1 → Algebra.IsUnramifiedAt R Q) :
    Algebra.Etale R S := by
  have : IsDomain R := hinj.isDomain _
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_dim2 hdim
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : Module.Free R S := normalFreeDim2 R S hdim hinj
  refine etale_of_free_of_isUnramifiedIn_height_one ?_ ?_
  · intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [hdim] at this
    exact absurd this (by decide)
  · intro P hP h1 Q hQ hQP
    have := hQ
    exact h Q (height_eq_one_of_liesOver P h1 Q)

end Final

section RegularBase

universe w

theorem isDiscreteValuationRing_of_dim1 {R : Type*} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  classical
  have hR : ¬ IsField R := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [hdim] at this
    exact absurd this (by decide)
  have hprin : (maximalIdeal R).IsPrincipal := by
    have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
    obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
    have h1 : (maximalIdeal R).spanFinrank = 1 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [hdim] at this
      exact_mod_cast this
    rw [h1] at hcard
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ⟨a, by rw [← hs]; simp [Ideal.span]⟩
  exact ((IsDiscreteValuationRing.TFAE R hR).out 5 1).mp hprin

/-- `purityGlobalDim1` with the hypothesis on the height-one primes of `S`. -/
theorem purityGlobalDim1' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 1) [IsDomain S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (h : ∀ Q : Ideal S, [Q.IsPrime] → Q.height = 1 → Algebra.IsUnramifiedAt R Q) :
    Algebra.Etale R S := by
  have : IsDomain R := hinj.isDomain _
  have : IsDiscreteValuationRing R := isDiscreteValuationRing_of_dim1 hdim
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  refine purityGlobalDim1 hdim hinj ?_
  intro P hP h1 Q hQ hQP
  have := hQ
  exact h Q (height_eq_one_of_liesOver P h1 Q)

/-- `(S_p)_Q ≅ S_{Q ∩ S}` as `R`-algebras (copied from t-purity2's `T1Local.lean`). -/
noncomputable def locLocEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime]
    (Q : Ideal (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) [Q.IsPrime] :
    Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime
      (Q.comap (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)))) :=
  haveI : IsScalarTower R S (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (IsLocalization.algEquiv
    (Q.comap (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)))).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R

noncomputable def atPrimeEquivOfEq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} [I.IsPrime] [J.IsPrime] (h : I = J) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime J := by
  subst h; exact AlgEquiv.refl

/-- **Purity of the branch locus over a regular ring of dimension ≤ 2** (input (P) of h-b1 §1.2
in ring form): a normal domain, finite and torsion-free over a regular ring `B` of dimension
`≤ 2` (not a field), unramified at its height-one primes, is étale over `B`. -/
theorem purityRegularRing {B S : Type w} [CommRing B] [CommRing S] [Algebra B S]
    [IsRegularRing B] (hdim : ringKrullDim B ≤ 2) (hB : ¬ IsField B)
    [IsDomain S] [IsIntegrallyClosed S] [Module.Finite B S]
    (hinj : Function.Injective (algebraMap B S))
    (h : ∀ Q : Ideal S, [Q.IsPrime] → Q.height = 1 → Algebra.IsUnramifiedAt B Q) :
    Algebra.Etale B S := by
  have : IsDomain B := hinj.isDomain _
  have : Algebra.FinitePresentation B S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmax : ∀ q : Ideal S, [q.IsMaximal] → Algebra.IsEtaleAt B q := by
    intro q hq
    set p := q.comap (algebraMap B S) with hp
    have hpmax : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) q
    have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hpmax hB
    let Rp := Localization.AtPrime p
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    have : Module.Finite Rp Sp := Module.Finite.of_isLocalization B S p.primeCompl
    have hle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ nonZeroDivisors S := by
      rintro _ ⟨b, hb, rfl⟩
      refine mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr ?_)
      rintro rfl
      exact hb p.zero_mem
    have : IsDomain Sp := IsLocalization.isDomain_localization hle
    have : IsIntegrallyClosed Sp := isIntegrallyClosed_of_isLocalization Sp _ hle
    have hinjp : Function.Injective (algebraMap Rp Sp) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
      have h1 : algebraMap Rp Sp (algebraMap B Rp a) = 0 := by
        rw [← IsLocalization.mk'_spec Rp a s, map_mul, hx, zero_mul]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B S Sp] at h1
      have h2 : a = 0 := hinj (IsLocalization.injective Sp hle (by simpa using h1))
      simp [h2]
    have hdimp : ringKrullDim Rp = p.height := IsLocalization.AtPrime.ringKrullDim_eq_height p Rp
    have hp1 : p.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]; exact hp0
    have hp2 : p.height ≤ 2 := by
      have := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
      exact WithBot.coe_le_coe.mp (this.trans (hdim.trans (le_of_eq rfl)))
    have hdisj : Disjoint (Algebra.algebraMapSubmonoid S p.primeCompl : Set S) (q : Set S) := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hqs
      exact hs hqs
    let Q : Ideal Sp := q.map (algebraMap S Sp)
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Sp q inferInstance hdisj
    have hQc : Q.comap (algebraMap S Sp) = q :=
      IsLocalization.under_map_of_isPrime_disjoint _ Sp (I := q) inferInstance hdisj
    let E : Localization.AtPrime Q ≃ₐ[B] Localization.AtPrime q :=
      (locLocEquiv p Q).trans (atPrimeEquivOfEq hQc)
    have hyp : ∀ Q'' : Ideal Sp, [Q''.IsPrime] → Q''.height = 1 →
        Algebra.IsUnramifiedAt Rp Q'' := by
      intro Q'' _ hht
      have hht' : (Q''.comap (algebraMap S Sp)).height = 1 := by
        rw [← hht]
        exact IsLocalization.height_under (Algebra.algebraMapSubmonoid S p.primeCompl) Q''
      have hU := h _ hht'
      have : Algebra.FormallyUnramified B (Localization.AtPrime Q'') :=
        Algebra.FormallyUnramified.of_equiv (locLocEquiv p Q'').symm
      exact Algebra.FormallyUnramified.of_restrictScalars B Rp _
    have hEt : Algebra.Etale Rp Sp := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, p.height = n := ENat.ne_top_iff_exists.mp
        (ne_top_of_le_ne_top (by decide) hp2) |>.imp fun n h => h.symm
      rw [hn] at hp1 hp2 hdimp
      have hn2 : n ≤ 2 := by exact_mod_cast hp2
      have hn0 : n ≠ 0 := by exact_mod_cast hp1
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      interval_cases n
      · exact purityGlobalDim1' (by rw [hdimp]; norm_cast) hinjp hyp
      · exact purityGlobalDim2' (by rw [hdimp]; norm_cast) hinjp hyp
    have : Algebra.FormallyEtale Rp (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.comp Rp Sp _
    have : Algebra.FormallyEtale B (Localization.AtPrime Q) := Algebra.FormallyEtale.comp B Rp _
    exact Algebra.FormallyEtale.of_equiv E
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  ext ⟨P, hP⟩
  simp only [Set.mem_univ, iff_true]
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  have hMe : (⟨M, hM.isPrime⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus B S := by have := hM; exact hmax M
  exact (Algebra.isOpen_etaleLocus).stableUnderGeneralization
    ((PrimeSpectrum.le_iff_specializes _ _).mp hPM) hMe

end RegularBase

end TPurity3

end TPurity3Copy

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
open scoped TensorProduct

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

/-- A field is its own localization at any submonoid of nonzero elements. -/
theorem isLocalization_field_self {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (M : Submonoid A) (hM : ∀ x ∈ M, algebraMap A K x ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by simpa using hM x hx)
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

/-- `P ∩ ℤ = 0` for a prime `P` of `ℤ[X]_m` (`m ∋ p` maximal) not containing `p`. -/
theorem int_notMem (p : ℕ) [hp : Fact p.Prime] (m : Ideal ℤ[X]) [m.IsMaximal]
    (hpm : C (p : ℤ) ∈ m) (P : Ideal (Localization.AtPrime m)) [P.IsPrime]
    (hpP : algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∉ P) (n : ℤ) (hn : n ≠ 0) :
    algebraMap ℤ[X] (Localization.AtPrime m) (C n) ∉ P := by
  intro hnP
  set J : Ideal ℤ := (P.comap (algebraMap ℤ[X] (Localization.AtPrime m))).comap C
  have hJp : J.IsPrime := Ideal.IsPrime.comap _
  have hJ0 : J ≠ ⊥ := fun h => hn (by
    have : n ∈ J := hnP
    rwa [h, Ideal.mem_bot] at this)
  have hJmax : J.IsMaximal := hJp.isMaximal hJ0
  have hle : J ≤ m.comap C := by
    intro x hx
    have hx' : algebraMap ℤ[X] (Localization.AtPrime m) (C x) ∈ P := hx
    by_contra hxm
    have hu : IsUnit (algebraMap ℤ[X] (Localization.AtPrime m) (C x)) :=
      IsLocalization.map_units (Localization.AtPrime m) (⟨C x, hxm⟩ : m.primeCompl)
    exact (inferInstance : P.IsPrime).ne_top (P.eq_top_of_isUnit_mem hx' hu)
  have hne : m.comap C ≠ ⊤ := fun h => (Ideal.IsMaximal.ne_top ‹m.IsMaximal›)
    (Ideal.comap_eq_top_iff.mp h)
  have hEq : J = m.comap C := hJmax.eq_of_le hne hle
  have : (p : ℤ) ∈ J := hEq ▸ hpm
  exact hpP this

theorem atPrime_congr {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (h : p = q) [IsLocalization.AtPrime S p] :
    IsLocalization.AtPrime S q := by
  subst h
  assumption

attribute [local instance] Polynomial.algebra in
theorem snHorizontalTransfer_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m) :
    letI := locAlg E m
    ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 →
      algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∉ P →
      ¬ Algebra.IsUnramifiedIn (integralClosure (Localization.AtPrime m) E) P →
      ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧ Q.ramificationIdx ℚ[X] ≠ 1 ∧
        ∀ F : ℤ[X], F.map (Int.castRingHom ℚ) ∈ Q.under ℚ[X] →
          algebraMap ℤ[X] (Localization.AtPrime m) F ∈ P := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  intro P hP _ hpP hnot
  have : Fact p.Prime := ⟨hp⟩
  simp only [Algebra.IsUnramifiedIn, not_forall] at hnot
  obtain ⟨Q', hQ', hlies, hnu⟩ := hnot
  -- the rings
  letI iZ : Algebra ℤ[X] E := (zxMap E).toAlgebra
  have hTR : IsScalarTower ℤ[X] (Localization.AtPrime m) E := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hTQ : IsScalarTower ℤ[X] ℚ[X] E := IsScalarTower.of_algebraMap_eq' rfl
  -- `C → S`
  let ιS : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime m) E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime m) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCS := ιS.toAlgebra
  have hCSE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
      E := IsScalarTower.of_algebraMap_eq' rfl
  have hZCS : IsScalarTower ℤ[X] (integralClosure ℤ[X] E)
      (integralClosure (Localization.AtPrime m) E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E)]
    change algebraMap (Localization.AtPrime m) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
    exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
  have hlocE : IsLocalization (Algebra.algebraMapSubmonoid E m.primeCompl) E :=
    isLocalization_field_self _ (fun x hx h0 => hx (by
      rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact m.zero_mem))
  have hlocS : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E)
      m.primeCompl) (integralClosure (Localization.AtPrime m) E) :=
    IsLocalization.integralClosure m.primeCompl
  -- `C → B`
  let ιB : integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := ℚ[X]) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCB := ιB.toAlgebra
  have hCBE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hZCB : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] ℚ[X] (integralClosure ℚ[X] E)]
    rfl
  set M₀ : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map C with hM₀
  have hlocQ : IsLocalization M₀ ℚ[X] := Polynomial.isLocalization _ _
  have hlocE₀ : IsLocalization (Algebra.algebraMapSubmonoid E M₀) E :=
    isLocalization_field_self _ (by
      rintro _ ⟨n, hn, rfl⟩ h0
      have : C n = 0 := (zxMap_injective E) (h0.trans (map_zero _).symm)
      exact nonZeroDivisors.ne_zero hn (C_eq_zero.mp this))
  have hlocB : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀)
      (integralClosure ℚ[X] E) :=
    IsLocalization.integralClosure M₀
  -- the prime `𝔮` of `C` under `Q'`, and `Q = 𝔮 B`
  set 𝔮 : Ideal (integralClosure ℤ[X] E) :=
    Q'.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E))
    with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.comap _
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀ :
      Submonoid _) : Set (integralClosure ℤ[X] E)) ↑𝔮 := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩ hmem
    have hmem' : algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)
        (algebraMap ℤ[X] (Localization.AtPrime m) (C n)) ∈ Q' := by
      have : algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
          (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C n)) ∈ Q' := hmem
      rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X]
        (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)] at this
    have hP' : algebraMap ℤ[X] (Localization.AtPrime m) (C n) ∈ P := by
      rw [hlies.over]
      exact hmem'
    exact int_notMem p m hpm P hpP n (nonZeroDivisors.ne_zero hn) hP'
  set Q : Ideal (integralClosure ℚ[X] E) := 𝔮.map (algebraMap _ _) with hQdef
  have hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ 𝔮 h𝔮p hdisj
  have hQ𝔮 : Q.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ h𝔮p hdisj
  refine ⟨Q, hQp, ?_, ?_⟩
  swap
  · -- elements of `ℤ[X]` in `Q` lie in `P`
    intro F hF
    have h1 : algebraMap ℤ[X] (integralClosure ℤ[X] E) F ∈ 𝔮 := by
      rw [← hQ𝔮]
      change algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
        (algebraMap ℤ[X] (integralClosure ℤ[X] E) F) ∈ Q
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X] ℚ[X]
        (integralClosure ℚ[X] E)]
      exact hF
    have h2 : algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)
        (algebraMap ℤ[X] (Localization.AtPrime m) F) ∈ Q' := by
      have : algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
          (algebraMap ℤ[X] (integralClosure ℤ[X] E) F) ∈ Q' := h1
      rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X]
        (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)] at this
    rw [hlies.over]
    exact h2
  · intro he1
    apply hnu
    have hfinB : Module.Finite ℚ[X] (integralClosure ℚ[X] E) :=
      IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
    have : Algebra.EssFiniteType ℚ[X] (integralClosure ℚ[X] E) := inferInstance
    have : CharZero (Q.under ℚ[X]).ResidueField :=
      charZero_of_injective_ringHom
        ((algebraMap ℚ[X] (Q.under ℚ[X]).ResidueField).comp (C : ℚ →+* ℚ[X])).injective
    have : Algebra.HasSeparableResidueFieldsAt ℚ[X] (integralClosure ℚ[X] E) (Q.under ℚ[X]) :=
      inferInstance
    have hunQ : Algebra.IsUnramifiedAt ℚ[X] Q := (Ideal.ramificationIdx_eq_one_iff).mp he1
    have hZQ : Algebra.FormallyUnramified ℤ[X] ℚ[X] :=
      Algebra.FormallyUnramified.of_isLocalization M₀
    have hZB : Algebra.FormallyUnramified ℤ[X] (Localization.AtPrime Q) :=
      Algebra.FormallyUnramified.comp ℤ[X] ℚ[X] (Localization.AtPrime Q)
    -- both local rings are the localization of `C` at `𝔮`
    have hL1 : IsLocalization.AtPrime (Localization Q'.primeCompl) 𝔮 :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl)
        (Localization Q'.primeCompl) Q'
    have hL2' : IsLocalization.AtPrime (Localization.AtPrime Q)
        (Q.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀) (Localization.AtPrime Q) Q
    have hL2 : IsLocalization.AtPrime (Localization.AtPrime Q) 𝔮 := atPrime_congr hQ𝔮
    let e : Localization Q'.primeCompl ≃ₐ[integralClosure ℤ[X] E] Localization.AtPrime Q :=
      IsLocalization.algEquiv 𝔮.primeCompl _ _
    have t1 : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (Localization Q'.primeCompl) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      rw [IsScalarTower.algebraMap_apply (integralClosure ℤ[X] E)
        (integralClosure (Localization.AtPrime m) E) (Localization Q'.primeCompl),
        ← IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure (Localization.AtPrime m) E)]
      rfl
    have t2 : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (Localization.AtPrime Q) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      rw [IsScalarTower.algebraMap_apply (integralClosure ℤ[X] E)
        (integralClosure ℚ[X] E) (Localization.AtPrime Q),
        ← IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure ℚ[X] E)]
      rfl
    have hZS : Algebra.FormallyUnramified ℤ[X] (Localization Q'.primeCompl) :=
      Algebra.FormallyUnramified.of_equiv (A := Localization.AtPrime Q)
        (AlgEquiv.ofRingEquiv (f := (e.symm : Localization.AtPrime Q ≃+* Localization Q'.primeCompl))
          (fun x => by
            rw [IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
                (Localization.AtPrime Q),
              IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
                (Localization Q'.primeCompl)]
            exact e.symm.commutes _))
    have t3 : IsScalarTower ℤ[X] (Localization.AtPrime m) (Localization Q'.primeCompl) :=
      inferInstance
    exact Algebra.FormallyUnramified.of_restrictScalars ℤ[X] (Localization.AtPrime m)
      (Localization Q'.primeCompl)

/-- **`SNHorizontalTransfer` is a theorem** (compiled): both local rings `(ℤ[X]_m-closure)_{Q'}`
and `B_Q` are localizations of the integral closure `C` of `ℤ[X]` at `𝔮 = Q' ∩ C`
(`IsLocalization.integralClosure`, `isLocalization_isLocalization_atPrime_isLocalization`), so
they are isomorphic over `C`; `e(Q) = 1` gives `ℚ[X] → B_Q` formally unramified
(`Ideal.ramificationIdx_eq_one_iff`, residue fields of characteristic 0), hence `ℤ[X] → B_Q`
(`ℚ[X]` a localization of `ℤ[X]`), hence `ℤ[X] → S_{Q'}`, hence `ℤ[X]_m → S_{Q'}`
(`FormallyUnramified.of_restrictScalars`). -/
theorem snHorizontalTransfer : SNHorizontalTransfer :=
  fun E _ _ _ _ _ p hp m _ hpm => snHorizontalTransfer_aux E p hp m hpm

/-- **`SpecNonMeeting` from purity, `SNVertical` and `SNSpecialize`** (`SNLocalData`,
`SNHorizontalTransfer` and the horizontal arithmetic are proved). -/
theorem specNonMeeting_of_pieces''' (hPur : PurityGlobalDim2.{0}) (hV : SNVertical)
    (hS : SNSpecialize) : SpecNonMeeting :=
  specNonMeeting_of_pieces'' hPur hV snHorizontalTransfer hS

theorem vertPrime_isPrime (p : ℕ) (hp : p.Prime) : (vertPrime p).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).mpr
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp))

theorem sep_congr {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q) [Algebra.HasSeparableResidueFieldsAt A B p] :
    Algebra.HasSeparableResidueFieldsAt A B q := by
  subst h
  assumption

/-- **Glue (field theory): residue fields at the vertical primes are separable when
`[E : ℚ(X)] < p`** (the residue degree `f` of a prime of the integral closure of `ℤ[X]` over `pℤ[X]`
is at most `[E : ℚ(X)] < p`, and an extension of degree `< p` in characteristic `p` is
separable). -/
def VerticalResidueSeparable : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime),
    Module.finrank (RatFunc ℚ) E < p →
    letI := intPolyAlg E
    haveI := vertPrime_isPrime p hp
    Algebra.HasSeparableResidueFieldsAt ℤ[X] (integralClosure ℤ[X] E) (vertPrime p)

theorem snVertical_aux (hVS : VerticalResidueSeparable) (E : Type) [Field E]
    [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (hdeg : Module.finrank (RatFunc ℚ) E < p) (hNV : NoVerticalRam E p)
    (m : Ideal ℤ[X]) [m.IsMaximal] :
    letI := locAlg E m
    ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 →
      algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∈ P →
      Algebra.IsUnramifiedIn (integralClosure (Localization.AtPrime m) E) P := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  intro P hP hP1 hpP Q' hQ' hlies
  letI iZ : Algebra ℤ[X] E := (zxMap E).toAlgebra
  have hTR : IsScalarTower ℤ[X] (Localization.AtPrime m) E := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  let ιS : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime m) E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime m) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCS := ιS.toAlgebra
  have hCSE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
      E := IsScalarTower.of_algebraMap_eq' rfl
  have hZCS : IsScalarTower ℤ[X] (integralClosure ℤ[X] E)
      (integralClosure (Localization.AtPrime m) E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E)]
    change algebraMap (Localization.AtPrime m) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
    exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
  have hlocE : IsLocalization (Algebra.algebraMapSubmonoid E m.primeCompl) E :=
    isLocalization_field_self _ (fun x hx h0 => hx (by
      rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact m.zero_mem))
  have hlocS : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E)
      m.primeCompl) (integralClosure (Localization.AtPrime m) E) :=
    IsLocalization.integralClosure m.primeCompl
  set 𝔮 : Ideal (integralClosure ℤ[X] E) :=
    Q'.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E))
    with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.comap _
  -- `𝔮` lies over `pℤ[X]`
  have hPunder : P.under ℤ[X] = vertPrime p := by
    have hvp : (vertPrime p).IsPrime := vertPrime_isPrime p hp
    have hle : vertPrime p ≤ P.under ℤ[X] := by
      rw [vertPrime, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
      exact hpP
    have hPu : (P.under ℤ[X]).IsPrime := Ideal.IsPrime.under _ _
    have hht : (P.under ℤ[X]).height = 1 := by
      rw [IsLocalization.height_under m.primeCompl P, hP1]
    by_contra hne
    have hlt : vertPrime p < P.under ℤ[X] := lt_of_le_of_ne hle (Ne.symm hne)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hht] at h1
    have h0 : (vertPrime p).height = 0 := by
      by_contra hne0
      have h1' : 1 ≤ (vertPrime p).height := by
        rw [Order.one_le_iff_pos, pos_iff_ne_zero]
        exact hne0
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left h1' 1) h1
      have h3 : ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
        simpa [one_add_one_eq_two] using h2
      exact absurd (Nat.cast_le.mp h3) (by norm_num)
    rw [Ideal.height_eq_zero_iff_eq_bot] at h0
    have hCp : C (p : ℤ) ∈ vertPrime p := Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    rw [h0, Ideal.mem_bot, C_eq_zero] at hCp
    exact hp.ne_zero (by exact_mod_cast hCp)
  have h𝔮under : 𝔮.under ℤ[X] = vertPrime p := by
    rw [← hPunder, hlies.over]
    ext x
    simp only [Ideal.mem_comap, h𝔮]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X]
      (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)]
  have he1 : 𝔮.ramificationIdx ℤ[X] = 1 := hNV 𝔮 h𝔮p h𝔮under
  -- finiteness of `C` over `ℤ[X]`
  letI iZK : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hZK : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  have hZKE : IsScalarTower ℤ[X] (RatFunc ℚ) E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply]
    exact IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E _
  have hfinC : Module.Finite ℤ[X] (integralClosure ℤ[X] E) :=
    IsIntegralClosure.finite ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  have : Algebra.EssFiniteType ℤ[X] (integralClosure ℤ[X] E) := inferInstance
  have hsep0 := hVS E p hp hdeg
  have hvp : (vertPrime p).IsPrime := vertPrime_isPrime p hp
  have hsep : Algebra.HasSeparableResidueFieldsAt ℤ[X] (integralClosure ℤ[X] E) (𝔮.under ℤ[X]) :=
    sep_congr h𝔮under.symm
  have hun𝔮 : Algebra.IsUnramifiedAt ℤ[X] 𝔮 := (Ideal.ramificationIdx_eq_one_iff).mp he1
  have hL1 : IsLocalization.AtPrime (Localization Q'.primeCompl) 𝔮 :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl)
      (Localization Q'.primeCompl) Q'
  let e : Localization Q'.primeCompl ≃ₐ[integralClosure ℤ[X] E] Localization.AtPrime 𝔮 :=
    IsLocalization.algEquiv 𝔮.primeCompl _ _
  have t1 : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (Localization Q'.primeCompl) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply (integralClosure ℤ[X] E)
      (integralClosure (Localization.AtPrime m) E) (Localization Q'.primeCompl),
      ← IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
        (integralClosure (Localization.AtPrime m) E)]
    rfl
  have hZS : Algebra.FormallyUnramified ℤ[X] (Localization Q'.primeCompl) :=
    Algebra.FormallyUnramified.of_equiv (A := Localization.AtPrime 𝔮)
      (AlgEquiv.ofRingEquiv (f := (e.symm : Localization.AtPrime 𝔮 ≃+* Localization Q'.primeCompl))
        (fun x => by
          rw [IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
              (Localization.AtPrime 𝔮),
            IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
              (Localization Q'.primeCompl)]
          exact e.symm.commutes _))
  have t3 : IsScalarTower ℤ[X] (Localization.AtPrime m) (Localization Q'.primeCompl) :=
    inferInstance
  exact Algebra.FormallyUnramified.of_restrictScalars ℤ[X] (Localization.AtPrime m)
    (Localization Q'.primeCompl)

/-- **`SNVertical` from `VerticalResidueSeparable`** (compiled): the prime `P ∋ p` of height one
is `pℤ[X]_m` (heights, `IsLocalization.height_under`); the prime `𝔮 = Q' ∩ C` lies over
`pℤ[X]`, so `NoVerticalRam` gives `e(𝔮) = 1`; with separable residue fields,
`Ideal.ramificationIdx_eq_one_iff` makes `ℤ[X] → C_𝔮` formally unramified; `S_{Q'} ≅ C_𝔮`
over `C`, so `ℤ[X]_m → S_{Q'}` is formally unramified. -/
theorem snVertical_of_sep (hVS : VerticalResidueSeparable) : SNVertical :=
  fun E _ _ _ _ _ p hp hdeg hNV _ _ m _ _ _ => snVertical_aux hVS E p hp hdeg hNV m

/-- **`SpecNonMeeting` from purity, `VerticalResidueSeparable` and `SNSpecialize`** (compiled). -/
theorem specNonMeeting_of_pieces4 (hPur : PurityGlobalDim2.{0}) (hVS : VerticalResidueSeparable)
    (hS : SNSpecialize) : SpecNonMeeting :=
  specNonMeeting_of_pieces''' hPur (snVertical_of_sep hVS) hS

/-- **An extension of degree `< p` in characteristic `p` is separable.** -/
theorem isSeparable_of_finrank_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h : Module.finrank K L < p) : Algebra.IsSeparable K L := by
  refine ⟨fun x => ?_⟩
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  have hirr := minpoly.irreducible hint
  rcases separable_or p hirr with hs | ⟨-, g, hg, hgf⟩
  · exact hs
  · exfalso
    have hdeg := minpoly.natDegree_le (A := K) (B := L) x
    have h1 : (minpoly K x).natDegree = g.natDegree * p := by rw [← hgf, natDegree_expand]
    have hg1 : 1 ≤ g.natDegree := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have := natDegree_eq_zero.mp h0
      obtain ⟨c, rfl⟩ := this
      exact hg.not_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
        rintro rfl
        simp at hg)))
    have : p ≤ (minpoly K x).natDegree := by rw [h1]; nlinarith
    omega

/-- **Glue (STANDARD, `Σ e f = n`): the residue degree at a vertical prime is at most
`[E : ℚ(X)]`.** For every prime `q` of the integral closure `C` of `ℤ[X]` in `E` over `pℤ[X]`,
`κ(q)/κ(pℤ[X])` is finite of degree `≤ [E : ℚ(X)]` (localize at `pℤ[X]`: `ℤ[X]_{(p)}` is a DVR,
`C_{(p)}` is free of rank `[E : ℚ(X)]`, and `κ(q)` is a quotient of `C_{(p)}/p`). -/
def VerticalResidueDegree : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime),
    letI := intPolyAlg E
    haveI := vertPrime_isPrime p hp
    ∀ (q : Ideal (integralClosure ℤ[X] E)) [q.IsPrime] [q.LiesOver (vertPrime p)],
      letI := Localization.AtPrime.algebraOfLiesOver (vertPrime p) q
      FiniteDimensional (vertPrime p).ResidueField q.ResidueField ∧
        Module.finrank (vertPrime p).ResidueField q.ResidueField ≤
          Module.finrank (RatFunc ℚ) E

/-- **`VerticalResidueSeparable` from the residue degree bound** (compiled). -/
theorem verticalResidueSeparable_of_degree (hD : VerticalResidueDegree) :
    VerticalResidueSeparable := by
  intro E _ _ _ _ _ p hp hdeg
  letI := intPolyAlg E
  haveI := vertPrime_isPrime p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun q _ _ => ?_⟩
  letI := Localization.AtPrime.algebraOfLiesOver (vertPrime p) q
  obtain ⟨hfin, hle⟩ := hD E p hp q
  have hchar : CharP (vertPrime p).ResidueField p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have hmem : C (p : ℤ) ∈ vertPrime p :=
      Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    have := Ideal.algebraMap_residueField_eq_zero.mpr hmem
    simpa using this
  exact isSeparable_of_finrank_lt p (lt_of_le_of_lt hle hdeg)

theorem vrd_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime) :
    letI := intPolyAlg E
    haveI := vertPrime_isPrime p hp
    ∀ (q : Ideal (integralClosure ℤ[X] E)) [q.IsPrime] [q.LiesOver (vertPrime p)],
      letI := Localization.AtPrime.algebraOfLiesOver (vertPrime p) q
      FiniteDimensional (vertPrime p).ResidueField q.ResidueField ∧
        Module.finrank (vertPrime p).ResidueField q.ResidueField ≤
          Module.finrank (RatFunc ℚ) E := by
  letI := intPolyAlg E
  haveI := vertPrime_isPrime p hp
  intro q _ _
  letI := Localization.AtPrime.algebraOfLiesOver (vertPrime p) q
  letI iZK : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hZK : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  have hZKE : IsScalarTower ℤ[X] (RatFunc ℚ) E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply]
    exact IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E _
  have hfinC : Module.Finite ℤ[X] (integralClosure ℤ[X] E) :=
    IsIntegralClosure.finite ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  have hQF : Algebra.QuasiFinite ℤ[X] (integralClosure ℤ[X] E) := inferInstance
  letI : Fintype ((vertPrime p).primesOver (integralClosure ℤ[X] E)) :=
    (Algebra.QuasiFinite.finite_primesOver (vertPrime p)).fintype
  have hNoeth : IsNoetherianRing (integralClosure ℤ[X] E) :=
    IsIntegralClosure.isNoetherianRing ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  have hfd : FiniteDimensional (vertPrime p).ResidueField q.ResidueField := inferInstance
  refine ⟨hfd, ?_⟩
  -- `e(q) > 0`
  have hmin : q ∈ ((vertPrime p).map (algebraMap ℤ[X] (integralClosure ℤ[X] E))).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def q (vertPrime p)))⟩,
      fun q' hq' hle => ?_⟩
    obtain ⟨hq'p, hmap⟩ := hq'
    by_contra hnle
    have hlt : q' < q := lt_of_le_of_ne hle (fun h => hnle (h ▸ le_rfl))
    have h1 := Ideal.IsIntegral.under_lt_under (R := ℤ[X]) hlt
    have h2 : vertPrime p ≤ q'.under ℤ[X] := Ideal.map_le_iff_le_comap.mp hmap
    rw [← Ideal.over_def q (vertPrime p)] at h1
    exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
  have he : 0 < q.ramificationIdx ℤ[X] := Ideal.ramificationIdx_pos_of_mem_minimalPrimes _ _ hmin
  -- the sum formula
  have hsum := Ideal.sum_ramification_inertia_eq_finrank_fiber (vertPrime p) (integralClosure ℤ[X] E)
  have hqmem : q ∈ (vertPrime p).primesOver (integralClosure ℤ[X] E) := ⟨inferInstance, inferInstance⟩
  have hle := Finset.single_le_sum
    (f := fun x : (vertPrime p).primesOver (integralClosure ℤ[X] E) =>
      x.1.ramificationIdx ℤ[X] * x.1.inertiaDeg ℤ[X]) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨q, hqmem⟩)
  have hf : q.inertiaDeg ℤ[X] = Module.finrank (vertPrime p).ResidueField q.ResidueField :=
    Ideal.inertiaDeg_eq (vertPrime p) q
  have hfib : Module.finrank (vertPrime p).ResidueField
      ((vertPrime p).Fiber (integralClosure ℤ[X] E)) ≤ Module.finrank (RatFunc ℚ) E := by
    apply le_of_eq
    set 𝔭 := vertPrime p with h𝔭
    -- the local base `ℤ[X]_𝔭` and its maps to `ℚ(X)` and `E`
    letI iE : Algebra (Localization.AtPrime 𝔭) E := locAlg E 𝔭
    letI iK : Algebra (Localization.AtPrime 𝔭) (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
    have hT1 : IsScalarTower ℤ[X] (Localization.AtPrime 𝔭) (RatFunc ℚ) := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (IsLocalization.lift_comp _).symm
    have hfr : IsFractionRing (Localization.AtPrime 𝔭) (RatFunc ℚ) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ _
    have hT2 : IsScalarTower (Localization.AtPrime 𝔭) (RatFunc ℚ) E := by
      apply IsScalarTower.of_algebraMap_eq'
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      rw [RingHom.comp_assoc]
      change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)) =
        (algebraMap (RatFunc ℚ) E).comp
          ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)))
      rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
      simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    have hTR : IsScalarTower ℤ[X] (Localization.AtPrime 𝔭) E := by
      apply IsScalarTower.of_algebraMap_eq'
      exact (IsLocalization.lift_comp _).symm
    have hic : IsIntegrallyClosed (Localization.AtPrime 𝔭) :=
      isIntegrallyClosed_of_isLocalization _ 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
    -- `ℤ[X]_𝔭` is a DVR (principal maximal ideal)
    have hCp0 : algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ)) ≠ 0 := by
      intro h0
      have := IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
        (h0.trans (map_zero _).symm)
      rw [C_eq_zero] at this
      exact hp.ne_zero (by exact_mod_cast this)
    have h3 : 𝔭 = Ideal.span {C (p : ℤ)} := by
      rw [h𝔭, vertPrime, Ideal.map_span, Set.image_singleton]
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) =
        Ideal.span {algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ))} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      refine (congrArg (Ideal.map (algebraMap ℤ[X] (Localization.AtPrime 𝔭))) h3).trans ?_
      rw [Ideal.map_span, Set.image_singleton]
    have hnf : ¬ IsField (Localization.AtPrime 𝔭) := by
      intro hF
      have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
      rw [hmax, Ideal.span_singleton_eq_bot] at this
      exact hCp0 this
    have hprin : (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)).IsPrincipal := ⟨⟨_, hmax⟩⟩
    have hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
      ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔭) hnf).out 1 5).mpr hprin
    -- the integral closure `C₀` of `ℤ[X]_𝔭` in `E`
    have hinj : Function.Injective (algebraMap (Localization.AtPrime 𝔭) E) := by
      rw [IsScalarTower.algebraMap_eq (Localization.AtPrime 𝔭) (RatFunc ℚ) E]
      exact (algebraMap (RatFunc ℚ) E).injective.comp
        (IsFractionRing.injective (Localization.AtPrime 𝔭) (RatFunc ℚ))
    have hfs : FaithfulSMul (Localization.AtPrime 𝔭) E :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have hfree : Module.Free (Localization.AtPrime 𝔭) (integralClosure (Localization.AtPrime 𝔭) E) :=
      IsIntegralClosure.module_free (Localization.AtPrime 𝔭) (RatFunc ℚ) E
        (integralClosure (Localization.AtPrime 𝔭) E)
    have hfin0 : Module.Finite (Localization.AtPrime 𝔭) (integralClosure (Localization.AtPrime 𝔭) E) :=
      IsIntegralClosure.finite (Localization.AtPrime 𝔭) (RatFunc ℚ) E
        (integralClosure (Localization.AtPrime 𝔭) E)
    have hrank : Module.finrank (Localization.AtPrime 𝔭) (integralClosure (Localization.AtPrime 𝔭) E)
        = Module.finrank (RatFunc ℚ) E :=
      IsIntegralClosure.rank (Localization.AtPrime 𝔭) (RatFunc ℚ) E
        (integralClosure (Localization.AtPrime 𝔭) E)
    -- `C₀` is the localization of `C`
    let ιS : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime 𝔭) E :=
      { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime 𝔭) c.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    letI aCS := ιS.toAlgebra
    have hCSE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime 𝔭) E)
        E := IsScalarTower.of_algebraMap_eq' rfl
    have hZCS : IsScalarTower ℤ[X] (integralClosure ℤ[X] E)
        (integralClosure (Localization.AtPrime 𝔭) E) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      apply Subtype.ext
      rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime 𝔭)
        (integralClosure (Localization.AtPrime 𝔭) E)]
      change algebraMap (Localization.AtPrime 𝔭) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
      exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
    have hlocE : IsLocalization (Algebra.algebraMapSubmonoid E 𝔭.primeCompl) E :=
      isLocalization_field_self _ (fun x hx h0 => hx (by
        rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact 𝔭.zero_mem))
    have hlocS : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E)
        𝔭.primeCompl) (integralClosure (Localization.AtPrime 𝔭) E) :=
      IsLocalization.integralClosure 𝔭.primeCompl
    have hlm : IsLocalizedModule 𝔭.primeCompl
        (IsScalarTower.toAlgHom ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure (Localization.AtPrime 𝔭) E)).toLinearMap :=
      (isLocalizedModule_iff_isLocalization).mpr hlocS
    have hbc := IsLocalizedModule.isBaseChange 𝔭.primeCompl (Localization.AtPrime 𝔭)
      (IsScalarTower.toAlgHom ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure (Localization.AtPrime 𝔭) E)).toLinearMap
    -- the chain of dimensions
    rw [← hrank]
    change Module.finrank 𝔭.ResidueField (𝔭.ResidueField ⊗[ℤ[X]] integralClosure ℤ[X] E) = _
    rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ[X] (Localization.AtPrime 𝔭) 𝔭.ResidueField
      𝔭.ResidueField (integralClosure ℤ[X] E)).finrank_eq,
      (hbc.equiv.baseChange (Localization.AtPrime 𝔭) 𝔭.ResidueField _ _).finrank_eq,
      Module.finrank_baseChange]
  calc Module.finrank (vertPrime p).ResidueField q.ResidueField = q.inertiaDeg ℤ[X] := hf.symm
    _ ≤ q.ramificationIdx ℤ[X] * q.inertiaDeg ℤ[X] := Nat.le_mul_of_pos_left _ he
    _ ≤ _ := hle
    _ = _ := hsum
    _ ≤ _ := hfib

/-- **`VerticalResidueDegree` is a theorem** (compiled): Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank_fiber` for `ℤ[X] → C` at `pℤ[X]` (`C` quasi-finite;
`e(q) > 0` since `q` is minimal over `pC`, by incomparability), and the fibre has dimension
`[E : ℚ(X)]`: it is `κ ⊗_{ℤ[X]_{(p)}} C_{(p)}`, where `ℤ[X]_{(p)}` is a DVR (principal maximal
ideal, `IsDiscreteValuationRing.TFAE`) and `C_{(p)}` (the integral closure of `ℤ[X]_{(p)}` in `E`,
a localization of `C` by `IsLocalization.integralClosure`) is free of rank `[E : ℚ(X)]`
(`IsIntegralClosure.module_free`, `IsIntegralClosure.rank`). -/
theorem verticalResidueDegree : VerticalResidueDegree :=
  fun E _ _ _ _ _ p hp => vrd_aux E p hp

/-- **`SpecNonMeeting` from `SNSpecialize` alone** (compiled; purity, `SNLocalData`,
`SNHorizontalTransfer`, `SNVertical` with its residue separability, and the Gauss-lemma arithmetic
are all proved in this file). -/
theorem specNonMeeting_of_specialize (hS : SNSpecialize) : SpecNonMeeting :=
  specNonMeeting_of_pieces4 TPurity3.purityGlobalDim2
    (verticalResidueSeparable_of_degree verticalResidueDegree) hS

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

/-- **`PurityGlobalDim2` is a theorem** (t-purity3's `TPurity3.purityGlobalDim2`, whose proof is
copied into this file above; the two statements are character-identical). -/
theorem purityGlobalDim2 : PurityGlobalDim2.{0} := TPurity3.purityGlobalDim2

/-- **The composite without the purity hypothesis.** -/
theorem propTSAll_of_pieces' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hVS : VerticalResidueSeparable) (hS : SNSpecialize) (hC : KummerCompositum) (hA : KummerAbhyankarFinGlue)
    (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin) (hAI : KummerAbhyankarInfGlue)
    (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf) (hN : HeckeNormalization)
    (hD : HeckeDegree) (hB : HeckeBranch) (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_of_pieces t2 hR hM purityGlobalDim2 (snVertical_of_sep hVS) snHorizontalTransfer hS hC hA
    hO hVF hAI hOI hVI hN hD hB hV

/-- **The final composite**: `PropTSAll` from the bundle leaves T2 and `R1R2fp`, the kernel glue
`MobiusGlue`, and 14 open glue Props (purity, `SNLocalData`, `SNHorizontalTransfer` and the
reduction of `SNVertical` are proved in this file). -/
theorem propTSAll_of_pieces'' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hVS : VerticalResidueSeparable) (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch)
    (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_of_pieces' t2 hR hM hVS hS hC hA hO hVF hAI hOI hVI (heckeNormalization_of_irr hI hNI)
    hD hB hV

/-- **The final composite, with `VerticalResidueDegree`**: `PropTSAll` from the bundle leaves T2
and `R1R2fp`, the kernel glue `MobiusGlue`, and 14 open glue Props. -/
theorem propTSAll_of_pieces''' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hVD : VerticalResidueDegree) (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch)
    (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_of_pieces'' t2 hR hM (verticalResidueSeparable_of_degree hVD) hS hC hA hO hVF hAI hOI
    hVI hI hNI hD hB hV

/-- **The final composite**: `PropTSAll` from the bundle leaves T2 and `R1R2fp`, the kernel glue
`MobiusGlue`, and 13 open glue Props (`SNSpecialize`, seven Kummer pieces, five Hecke pieces). -/
theorem propTSAll_final (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch)
    (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_of_bundle_meet t2 hR (kummerMeetGlue_of_pieces' hC hA hO hVF hAI hOI hVI)
    (specNonMeeting_of_specialize hS) hM
    (coverModelOfHecke_of_pieces (heckeNormalization_of_irr hI hNI) hD hB hV)

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
#print axioms PropTSGlue.snHorizontalTransfer
#print axioms PropTSGlue.snVertical_of_sep
#print axioms PropTSGlue.specNonMeeting_of_pieces4
#print axioms PropTSGlue.specNonMeeting_of_pieces'''
#print axioms PropTSGlue.kummerMeet_of_cases
#print axioms PropTSGlue.coeff_X_pow_sub_C_nonneg
#print axioms PropTSGlue.kummerMeetFin_of_pieces
#print axioms PropTSGlue.kummerMeetGlue_of_pieces
#print axioms PropTSGlue.kummerMeetInf_of_pieces
#print axioms PropTSGlue.kummerMeetGlue_of_pieces'
#print axioms PropTSGlue.coverModelOfHeckeN_of_pieces
#print axioms PropTSGlue.coverModelOfHecke_of_pieces
#print axioms PropTSGlue.heckeNormalization_of_irr
#print axioms PropTSGlue.propTSAll_of_pieces
#print axioms PropTSGlue.purityGlobalDim2
#print axioms PropTSGlue.propTSAll_of_pieces'
#print axioms PropTSGlue.propTSAll_of_pieces''
#print axioms PropTSGlue.propTSAll_of_pieces'''
#print axioms PropTSGlue.verticalResidueDegree
#print axioms PropTSGlue.specNonMeeting_of_specialize
#print axioms PropTSGlue.propTSAll_final
#print axioms PropTSGlue.isSeparable_of_finrank_lt
#print axioms PropTSGlue.verticalResidueSeparable_of_degree
#print axioms PropTSGlue.functionFieldModel_transfer
#print axioms PropTSGlue.coverModel_transfer
#print axioms PropTSGlue.coverModelOfHecke_of_witness


/-! # ts-kummer appendix (namespace `TsKummer`) -/

/-! ts-kummer development file: the abstract Abhyankar transfer (`abhyankar_core`), from T2. -/

open Polynomial IsLocalRing
open scoped TensorProduct
open PropTSRed PropTSGlue

set_option linter.style.haveILetI false

noncomputable section

namespace TsKummer

/-- The ramification index is invariant under an `R`-algebra isomorphism. -/
theorem ramificationIdx_map_algEquiv {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S ≃ₐ[R] S') (q : Ideal S) [hq : q.IsPrime] :
    (q.map f).ramificationIdx R = q.ramificationIdx R := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hbij : Function.Bijective (algebraMap S S') := f.bijective
  let e : S' ≃ₗ[S] S :=
    { toFun := f.symm
      invFun := f
      map_add' := fun x y => map_add f.symm x y
      map_smul' := fun r x => by
        change f.symm (f r * x) = r * f.symm x
        simp
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  haveI : Module.Flat S S' := Module.Flat.of_linearEquiv e
  have hq' : (q.map f).IsPrime := Ideal.map_isPrime_of_equiv f
  have hunder : (q.map f).under S = q := by
    change Ideal.comap (algebraMap S S') (Ideal.map (algebraMap S S') q) = q
    exact Ideal.comap_map_of_bijective _ hbij
  haveI : (q.map f).LiesOver q := ⟨hunder.symm⟩
  rw [Ideal.ramificationIdx_tower q (q.map f)]
  suffices h : (q.map f).ramificationIdx S = 1 by rw [h, mul_one]
  let Sq := Localization.AtPrime (q.map f)
  rw [Ideal.ramificationIdx_def, hunder, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff, IsScalarTower.algebraMap_eq S S' Sq, ← Ideal.map_map]
  change Ideal.map (algebraMap S' Sq) (Ideal.map (algebraMap S S') q) = _
  exact Localization.AtPrime.map_eq_maximalIdeal

/-- The inclusion of integral closures `integralClosure R0 L → integralClosure Rp L`. -/
def intClIncl (R0 Rp L : Type) [CommRing R0] [CommRing Rp] [Field L] [Algebra R0 Rp]
    [Algebra R0 L] [Algebra Rp L] [IsScalarTower R0 Rp L] :
    integralClosure R0 L →+* integralClosure Rp L where
  toFun c := ⟨c.1, IsIntegral.tower_top (A := Rp) c.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A field is its own localization at any submonoid of nonzero elements. -/
theorem isLocalization_field_self' {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (M : Submonoid A) (hM : ∀ x ∈ M, algebraMap A K x ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by simpa using hM x hx)
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

theorem intCl_isLocalization (R0 Rp L : Type) [CommRing R0] [CommRing Rp] [Field L]
    [Algebra R0 Rp] [Algebra R0 L] [Algebra Rp L] [IsScalarTower R0 Rp L] (P : Submonoid R0)
    [IsLocalization P Rp] (hP : ∀ x ∈ P, algebraMap R0 L x ≠ 0) :
    letI := (intClIncl R0 Rp L).toAlgebra
    IsScalarTower (integralClosure R0 L) (integralClosure Rp L) L ∧
    IsScalarTower R0 (integralClosure R0 L) (integralClosure Rp L) ∧
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R0 L) P)
      (integralClosure Rp L) := by
  letI := (intClIncl R0 Rp L).toAlgebra
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid L P) L := isLocalization_field_self' _ hP
  have h1 : IsScalarTower (integralClosure R0 L) (integralClosure Rp L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h2 : IsScalarTower R0 (integralClosure R0 L) (integralClosure Rp L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  exact ⟨h1, h2, IsLocalization.integralClosure P⟩

/-- In residue characteristic `0`, residue field extensions over a `ℚ`-algebra are separable. -/
theorem isSeparable_residue_of_rat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R] (m : Ideal R) [m.IsMaximal] (Q : Ideal S) [Q.IsMaximal] [Q.LiesOver m]
    [Algebra.IsIntegral R S] :
    letI : Field (R ⧸ m) := Ideal.Quotient.field _
    letI : Field (S ⧸ Q) := Ideal.Quotient.field _
    Algebra.IsSeparable (R ⧸ m) (S ⧸ Q) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field _
  letI : Field (S ⧸ Q) := Ideal.Quotient.field _
  haveI : CharZero (R ⧸ m) := by
    have : Function.Injective ((Ideal.Quotient.mk m).comp (algebraMap ℚ R)) := RingHom.injective _
    exact charZero_of_injective_ringHom this
  haveI : Algebra.IsIntegral (R ⧸ m) (S ⧸ Q) := inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ m) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **Abstract Abhyankar transfer from T2.** `R0` a Dedekind `ℚ`-algebra with fraction field `K`,
`L/K` finite separable, `ι : L → M` a field embedding, `A` a Dedekind domain with `A → M`
injective, and `σ : R0 → A` integral with `A → M` compatible with `ι` on `R0`. If `π0` generates a
nonzero prime of `R0`, `σ π0 = s ^ n` with `(s)` prime, `M = L(s)`, and every prime of the integral
closure of `R0` in `L` over `(π0)` has ramification index dividing `n`, then every prime of the
integral closure of `A` in `M` over `(s)` is unramified over `A`. -/
theorem abhyankar_core (t2 : PkgI2.AbhyankarDVR.{0})
    (R0 K L M A : Type) [CommRing R0] [IsDomain R0] [IsDedekindDomain R0] [Algebra ℚ R0]
    [Field K] [Algebra R0 K] [IsFractionRing R0 K]
    [Field L] [Algebra K L] [Algebra R0 L] [IsScalarTower R0 K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Field M] [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A M]
    (ι : L →+* M) (σ : R0 →+* A) (hσ : ∀ x, algebraMap A M (σ x) = ι (algebraMap R0 L x))
    (hint : σ.IsIntegral) (hAM : Function.Injective (algebraMap A M))
    (π0 : R0) [hπp : (Ideal.span {π0}).IsPrime] (hπ0 : π0 ≠ 0)
    (s : A) [hsp : (Ideal.span {s}).IsPrime] (hs0 : s ≠ 0) (n : ℕ) (hn : 0 < n)
    (hsn : σ π0 = s ^ n)
    (hadj : letI := ι.toAlgebra; IntermediateField.adjoin L {algebraMap A M s} = ⊤)
    (hE : ∀ Q : Ideal (integralClosure R0 L), Q.IsPrime → Q.under R0 = Ideal.span {π0} →
      Q.ramificationIdx R0 ∣ n)
    (Q' : Ideal (integralClosure A M)) [hQ'p : Q'.IsPrime] (hQ' : Q'.under A = Ideal.span {s}) :
    Q'.ramificationIdx A = 1 := by
  classical
  set p : Ideal R0 := Ideal.span {π0} with hp_def
  letI : Algebra R0 A := σ.toAlgebra
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  letI : Algebra R0 M := ((algebraMap K M).comp (algebraMap R0 K)).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 K M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 A M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ι (algebraMap K L (algebraMap R0 K x)) = algebraMap A M (σ x)
    rw [hσ, IsScalarTower.algebraMap_apply R0 K L]
  haveI : Algebra.IsIntegral R0 A := ⟨hint⟩
  have hp0 : p ≠ ⊥ := by
    rw [hp_def, Ne, Ideal.span_singleton_eq_bot]; exact hπ0
  haveI hpmax : p.IsMaximal := Ideal.IsPrime.isMaximal hπp hp0
  -- the DVR `Rp`
  set Rp := Localization.AtPrime p
  haveI hDVR : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R0 hp0 Rp
  letI : Algebra Rp K := IsLocalization.localizationAlgebraOfSubmonoidLe Rp K p.primeCompl (nonZeroDivisors R0)
    p.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower R0 Rp K := IsLocalization.localization_isScalarTower_of_submonoid_le Rp K p.primeCompl
    (nonZeroDivisors R0) p.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rp K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rp K
  letI : Algebra Rp L := ((algebraMap K L).comp (algebraMap Rp K)).toAlgebra
  letI : Algebra Rp M := ((algebraMap K M).comp (algebraMap Rp K)).toAlgebra
  haveI : IsScalarTower Rp K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rp K M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 Rp L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R0 L x = algebraMap K L (algebraMap Rp K (algebraMap R0 Rp x))
    rw [← IsScalarTower.algebraMap_apply R0 Rp K, ← IsScalarTower.algebraMap_apply R0 K L]
  haveI : IsScalarTower R0 Rp M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap K M (algebraMap R0 K x) = algebraMap K M (algebraMap Rp K (algebraMap R0 Rp x))
    rw [← IsScalarTower.algebraMap_apply R0 Rp K]
  -- injectivity of `R0 → L`, `R0 → M`
  have hR0K : Function.Injective (algebraMap R0 K) := IsFractionRing.injective R0 K
  have hR0L : Function.Injective (algebraMap R0 L) := by
    rw [IsScalarTower.algebraMap_eq R0 K L]
    exact (algebraMap K L).injective.comp hR0K
  have hR0M : Function.Injective (algebraMap R0 M) := by
    rw [IsScalarTower.algebraMap_eq R0 K M]
    exact (algebraMap K M).injective.comp hR0K
  have hPL : ∀ x ∈ p.primeCompl, algebraMap R0 L x ≠ 0 := fun x hx h0 =>
    hx (by rw [hR0L (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  have hPM : ∀ x ∈ p.primeCompl, algebraMap R0 M x ≠ 0 := fun x hx h0 =>
    hx (by rw [hR0M (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  -- the uniformizer
  have hmax : maximalIdeal Rp = Ideal.span {algebraMap R0 Rp π0} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_span _ _).trans (by rw [Set.image_singleton])
  have hirr : Irreducible (algebraMap R0 Rp π0) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  -- units
  have hunit : ∀ k : ℕ, k ≠ 0 → IsUnit (k : Rp) := by
    intro k hk
    have h1 : IsUnit ((algebraMap R0 Rp).comp (algebraMap ℚ R0) (k : ℚ)) :=
      (Ne.isUnit (by exact_mod_cast hk : (k : ℚ) ≠ 0)).map _
    simpa using h1
  -- localizing the integral closure of `R0` in `L`
  obtain ⟨hL1, hL2, hL3⟩ := intCl_isLocalization R0 Rp L p.primeCompl hPL
  letI := (intClIncl R0 Rp L).toAlgebra
  -- T2's hypothesis
  have hyp : ∀ (Q : Ideal (integralClosure Rp L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)],
      IsUnit ((Q.ramificationIdx Rp : ℕ) : Rp) ∧ Q.ramificationIdx Rp ∣ n ∧
      Algebra.IsSeparable (Rp ⧸ maximalIdeal Rp) (integralClosure Rp L ⧸ Q) := by
    intro Q _ _
    set P0 := Q.comap (algebraMap (integralClosure R0 L) (integralClosure Rp L))
    haveI : P0.LiesOver p := IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rp Q
    haveI : P0.IsPrime := Ideal.IsPrime.comap _
    have hQ : Q = P0.map (algebraMap (integralClosure R0 L) (integralClosure Rp L)) :=
      (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R0 L) p.primeCompl)
        (integralClosure Rp L) Q).symm
    have he : Q.ramificationIdx Rp = P0.ramificationIdx R0 := by
      rw [hQ]
      exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rp
        (integralClosure Rp L) P0
    have hdvd : Q.ramificationIdx Rp ∣ n := by
      rw [he]; exact hE P0 inferInstance (Ideal.LiesOver.over (P := P0) (p := p)).symm
    refine ⟨hunit _ (fun h0 => by rw [h0, zero_dvd_iff] at hdvd; omega), hdvd, ?_⟩
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rp) Q
      (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rp)]; infer_instance)
    letI : Algebra ℚ Rp := ((algebraMap R0 Rp).comp (algebraMap ℚ R0)).toAlgebra
    exact isSeparable_residue_of_rat (maximalIdeal Rp) Q
  -- T2 applied to `M = L(s)`
  have ht : (algebraMap A M s) ^ n = algebraMap Rp M (algebraMap R0 Rp π0) := by
    rw [← IsScalarTower.algebraMap_apply R0 Rp M, IsScalarTower.algebraMap_apply R0 A M, ← map_pow]
    congr 1
    exact hsn.symm
  have key := t2 Rp K L M (algebraMap R0 Rp π0) hirr n hn (hunit n (by omega)) hyp
    (algebraMap A M s) ht hadj
  -- localizing the integral closure of `R0` in `M`
  obtain ⟨hM1, hM2, hM3⟩ := intCl_isLocalization R0 Rp M p.primeCompl hPM
  letI := (intClIncl R0 Rp M).toAlgebra
  -- `integralClosure A M = integralClosure R0 M`
  have hmem : ∀ x : M, IsIntegral A x ↔ IsIntegral R0 x := fun x =>
    ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩
  let f0 : integralClosure A M ≃+* integralClosure R0 M :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (hmem y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let f : integralClosure A M ≃ₐ[R0] integralClosure R0 M :=
    AlgEquiv.ofRingEquiv (f := f0) (fun r => rfl)
  -- `(s) ∩ R0 = p`
  have hsunder : (Ideal.span {s}).comap (algebraMap R0 A) = p := by
    have hle : p ≤ (Ideal.span {s}).comap (algebraMap R0 A) := by
      rw [hp_def, Ideal.span_le, Set.singleton_subset_iff]
      change σ π0 ∈ Ideal.span {s}
      rw [hsn]; exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self s) n hn
    exact (hpmax.eq_of_le (Ideal.IsPrime.comap _).ne_top hle).symm
  haveI : (Ideal.span {s}).LiesOver p := ⟨hsunder.symm⟩
  haveI : Q'.LiesOver (Ideal.span {s}) := ⟨hQ'.symm⟩
  haveI : Q'.LiesOver p := Ideal.LiesOver.trans Q' (Ideal.span {s}) p
  set P := Q'.map f with hP_def
  haveI : P.IsPrime := Ideal.map_isPrime_of_equiv f
  have hPunder : P.under R0 = p := by
    ext x
    rw [Ideal.under, Ideal.mem_comap, hP_def, ← f.commutes x, ← Ideal.mem_comap,
      Ideal.comap_map_of_bijective f f.bijective, ← Ideal.mem_comap]
    change x ∈ Q'.under R0 ↔ x ∈ p
    rw [← Ideal.LiesOver.over (P := Q') (p := p)]
  haveI : P.LiesOver p := ⟨hPunder.symm⟩
  haveI := IsLocalization.AtPrime.isPrime_map_of_liesOver (integralClosure R0 M) p
    (integralClosure Rp M) P
  haveI := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rp (integralClosure Rp M) P
  have h1 := (key (P.map (algebraMap (integralClosure R0 M) (integralClosure Rp M)))).1
  rw [IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rp (integralClosure Rp M) P,
    hP_def, ramificationIdx_map_algEquiv f Q'] at h1
  -- the tower `R0 → A → integralClosure A M`
  haveI : Module.IsTorsionFree A (integralClosure A M) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply hAM
    have := congrArg Subtype.val hxy
    simpa using this
  have htow := Ideal.ramificationIdx_tower (R := R0) (Ideal.span {s}) Q'
  have hsn' : (Ideal.span {s}).ramificationIdx R0 = n := by
    have hs_ne : Ideal.span {s} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hs0
    haveI : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {s})) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hs_ne _
    rw [Ideal.ramificationIdx_eq p (Ideal.span {s})]
    have hmapn : p.map (algebraMap R0 (Localization.AtPrime (Ideal.span {s}))) =
        maximalIdeal (Localization.AtPrime (Ideal.span {s})) ^ n := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, Ideal.span_singleton_pow,
        Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        IsScalarTower.algebraMap_apply R0 A (Localization.AtPrime (Ideal.span {s}))]
      rw [show algebraMap R0 A π0 = s ^ n from hsn]
    rw [hmapn, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  rw [h1, hsn'] at htow
  have : n * Q'.ramificationIdx A = n * 1 := by rw [← htow, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hn this

end TsKummer

namespace TsKummer

/-- `ℚ[X] → E'` through `ℚ(s)` is injective. -/
theorem polyMap_injective (E' : Type) [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] : Function.Injective (algebraMap ℚ[X] E') := by
  rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E']
  exact (algebraMap (RatFunc ℚ) E').injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))

/-- `KummerShape` gives `E' = E(s)` as an intermediate-field statement. -/
theorem adjoin_eq_top_of_shape {E E' : Type} [Field E] [Field E'] [Algebra (RatFunc ℚ) E]
    [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E'] [IsScalarTower ℚ[X] (RatFunc ℚ) E']
    (ι : E →+* E') (r : RatFunc ℚ) (h : KummerShape E E' ι r) :
    letI := ι.toAlgebra
    IntermediateField.adjoin E {algebraMap ℚ[X] E' X} = ⊤ := by
  letI := ι.toAlgebra
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield,
    IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E', RatFunc.algebraMap_X]
  exact h.2

/-- An integral element for `σ` makes the whole polynomial ring integral (if `σ` fixes constants). -/
theorem isIntegral_of_X (σ : ℚ[X] →+* ℚ[X]) (hC : ∀ a : ℚ, σ (C a) = C a)
    (hX : σ.IsIntegralElem X) : σ.IsIntegral := by
  intro f
  induction f using Polynomial.induction_on with
  | C a => rw [← hC a]; exact σ.isIntegralElem_map
  | add f g hf hg => exact RingHom.IsIntegralElem.add σ hf hg
  | monomial k a _ =>
    rw [pow_succ, ← mul_assoc]
    exact RingHom.IsIntegralElem.mul σ (by assumption) hX

/-- **`KummerAbhyankarFinGlue` is proved** (from T2, via `abhyankar_core`). -/
theorem kummerAbhyankarFinGlue : KummerAbhyankarFinGlue := by
  intro t2 E _ _ _ _ _ E' _ _ _ _ _ ι b c n hn hc hshape hE Q' hQ'p hQ'
  have hcu : IsUnit (C c : ℚ[X]) := Polynomial.isUnit_C.mpr (Ne.isUnit hc)
  let σ : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n)
  have hσC : ∀ a : ℚ, σ (C a) = C a := fun a => by simp [σ]
  have hσX : σ X = C b + C c⁻¹ * X ^ n := by simp [σ]
  have hsn : σ (C c * (X - C b)) = X ^ n := by
    rw [map_mul, map_sub, hσC, hσC, hσX, add_sub_cancel_left, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * (X - C b)), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hσ : ∀ x, algebraMap ℚ[X] E' (σ x) = ι (algebraMap ℚ[X] E x) := by
    have : (algebraMap ℚ[X] E').comp σ = ι.comp (algebraMap ℚ[X] E) := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat (((algebraMap ℚ[X] E').comp σ).comp C)
          ((ι.comp (algebraMap ℚ[X] E)).comp C)
        exact congrArg (fun g => g a) this
      · simp only [RingHom.comp_apply]
        rw [hσX, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
          IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E', RatFunc.algebraMap_X, hshape.1]
        congr 1
        rw [rFin, eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
          (C_ne_zero.mpr hc)), ← map_mul]
        congr 1
        have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
        rw [C_mul]
        linear_combination (X ^ n) * h1
    intro x
    exact congrArg (fun g => g x) this
  haveI : (Ideal.span {C c * (X - C b)} : Ideal ℚ[X]).IsPrime := by
    rw [Ideal.span_singleton_mul_left_unit hcu]
    exact (Ideal.span_singleton_prime (X_sub_C_ne_zero b)).mpr (prime_X_sub_C b)
  haveI : (Ideal.span {X} : Ideal ℚ[X]).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  refine abhyankar_core t2 ℚ[X] (RatFunc ℚ) E E' ℚ[X] ι σ hσ (isIntegral_of_X σ hσC hXint)
    (polyMap_injective E') (C c * (X - C b)) (mul_ne_zero (C_ne_zero.mpr hc) (X_sub_C_ne_zero b))
    X X_ne_zero n hn hsn (adjoin_eq_top_of_shape ι _ hshape) ?_ Q' hQ'
  intro Q hQ hQu
  rw [Ideal.span_singleton_mul_left_unit hcu] at hQu
  exact hE Q hQ hQu

theorem eval₂_X_eq (f : ℚ[X]) :
    eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X f = algebraMap ℚ[X] (RatFunc ℚ) f := by
  have := eval₂_algebraMap_X f (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ))
  simpa [RatFunc.algebraMap_X] using this

/-- `ℚ(X)` is the fraction field of `InfCoord = ℚ[1/X]`. -/
theorem isFractionRing_infCoord : IsFractionRing InfCoord (RatFunc ℚ) := by
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have key : ∀ (f : ℚ[X]) (N : ℕ), f.natDegree ≤ N →
      eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N f) * RatFunc.X ^ N =
        algebraMap ℚ[X] (RatFunc ℚ) f := by
    intro f N hf
    letI : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero hX
    have := eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X N f hf
    rw [invOf_eq_inv, eval₂_X_eq] at this
    exact this
  have hinj0 : ∀ f : ℚ[X], eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ f = 0 → f = 0 := by
    intro f hf
    letI : Invertible (RatFunc.X⁻¹ : RatFunc ℚ) := invertibleOfNonzero (inv_ne_zero hX)
    have h := eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (f : ℚ[X]).natDegree
      (f : ℚ[X]) le_rfl
    rw [hf, invOf_eq_inv, inv_inv, eval₂_X_eq] at h
    have h2 := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hX))
    rw [map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ)), reflect_eq_zero_iff] at h2
    exact h2
  have hinj : Function.Injective (algebraMap InfCoord (RatFunc ℚ)) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    exact hinj0 f hf
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hy))
  · intro z
    obtain ⟨P, Q, hQ, rfl⟩ : ∃ P Q : ℚ[X], Q ≠ 0 ∧
        z = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q :=
      ⟨z.num, z.denom, z.denom_ne_zero, (RatFunc.num_div_denom z).symm⟩
    set N := max P.natDegree Q.natDegree
    have hQN : (reflect N Q : InfCoord) ∈ nonZeroDivisors InfCoord :=
      mem_nonZeroDivisors_of_ne_zero (M₀ := InfCoord)
        (show (reflect N Q : InfCoord) ≠ 0 from fun h => hQ (reflect_eq_zero_iff.mp h))
    refine ⟨⟨reflect N P, ⟨reflect N Q, hQN⟩⟩, ?_⟩
    change algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q *
        eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N Q) =
      eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N P)
    have hP := key P N (le_max_left _ _)
    have hQ' := key Q N (le_max_right _ _)
    have hQ0 : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr hQ
    have hXN : (RatFunc.X : RatFunc ℚ) ^ N ≠ 0 := pow_ne_zero _ hX
    have hq : eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (reflect N Q) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hQ'; exact hQ0 hQ'.symm
    rw [← hP, ← hQ', mul_div_mul_right _ _ hXN, div_mul_cancel₀ _ hq]
  · intro x y h
    exact ⟨1, by simp [hinj h]⟩

/-- **`KummerAbhyankarInfGlue` is proved** (from T2, via `abhyankar_core` with `R0 = ℚ[1/X]`). -/
theorem kummerAbhyankarInfGlue : KummerAbhyankarInfGlue := by
  intro t2 E _ _ _ _ _ E' _ _ _ _ _ ι c n hn hc hshape hE Q' hQ'p hQ'
  letI := infAlg E
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  letI : IsDedekindDomain InfCoord := inferInstanceAs (IsDedekindDomain ℚ[X])
  letI : Algebra ℚ InfCoord := inferInstanceAs (Algebra ℚ ℚ[X])
  haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
  haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  have hcu : IsUnit (C c : ℚ[X]) := Polynomial.isUnit_C.mpr (Ne.isUnit hc)
  let σ0 : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n)
  let σ : InfCoord →+* ℚ[X] := σ0
  have hσC : ∀ a : ℚ, σ0 (C a) = C a := fun a => by simp [σ0]
  have hσX : σ0 X = C c⁻¹ * X ^ n := by simp [σ0]
  have hsn : σ0 (C c * X) = X ^ n := by
    rw [map_mul, hσC, hσX, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ0.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * X), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hσ : ∀ x : InfCoord, algebraMap ℚ[X] E' (σ x) = ι (algebraMap InfCoord E x) := by
    have : ((algebraMap ℚ[X] E').comp σ0 : ℚ[X] →+* E') =
        (ι.comp (algebraMap InfCoord E) : ℚ[X] →+* E') := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat (((algebraMap ℚ[X] E').comp σ0).comp C)
          (((ι.comp (algebraMap InfCoord E) : ℚ[X] →+* E')).comp C)
        exact congrArg (fun g => g a) this
      · simp only [RingHom.comp_apply]
        rw [hσX]
        change algebraMap ℚ[X] E' (C c⁻¹ * X ^ n) =
          ι (algebraMap (RatFunc ℚ) E (eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ X))
        rw [eval₂_X, map_inv₀ (algebraMap (RatFunc ℚ) E), map_inv₀ ι, hshape.1,
          ← map_inv₀ (algebraMap (RatFunc ℚ) E'),
          IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E']
        congr 1
        have hCc : algebraMap ℚ[X] (RatFunc ℚ) (C c) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (C_ne_zero.mpr hc)
        rw [rInf, inv_div, eq_div_iff hCc, ← map_mul]
        congr 1
        have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
        linear_combination (X ^ n) * h1
    intro x
    exact congrArg (fun g => g x) this
  let π0 : InfCoord := (C c * X : ℚ[X])
  haveI : (Ideal.span {π0}).IsPrime := by
    change (Ideal.span {(C c * X : ℚ[X])} : Ideal ℚ[X]).IsPrime
    rw [Ideal.span_singleton_mul_left_unit hcu]
    exact (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  haveI : (Ideal.span {X} : Ideal ℚ[X]).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  refine abhyankar_core t2 InfCoord (RatFunc ℚ) E E' ℚ[X] ι σ hσ
    (isIntegral_of_X σ0 hσC hXint) (polyMap_injective E') π0
    (show (C c * X : ℚ[X]) ≠ 0 from mul_ne_zero (C_ne_zero.mpr hc) X_ne_zero) X X_ne_zero n hn hsn
    (adjoin_eq_top_of_shape ι _ hshape) ?_ Q' hQ'
  intro Q hQ hQu
  have hspan : (Ideal.span {π0}) = Ideal.span {infUnif} := by
    change (Ideal.span {(C c * X : ℚ[X])} : Ideal ℚ[X]) = Ideal.span {X}
    rw [Ideal.span_singleton_mul_left_unit hcu]
  rw [hspan] at hQu
  exact hE Q hQ hQu

end TsKummer

namespace TsKummer

/-- **Glue (STANDARD): a compositum of unramified extensions is unramified (DVR form).**
`R` a discrete valuation ring with fraction field `K`; `L/K`, `L'/K` finite separable; `M` a field
containing `L` and `L'` over `K` and generated by them (`M = L·L'`). If every prime of the integral
closure of `R` in `L`, and in `L'`, over the maximal ideal of `R` has ramification index `1` and
separable residue field extension, then so does every such prime of the integral closure of `R`
in `M`. (Stated in the binder conventions of T2 `PkgI2.AbhyankarDVR`. Reference: base change and
composition of étale algebras, SGA 1 Exp. I, Prop. 4.6 and Cor. 4.8 (numbers UNVERIFIED); for
function fields Stichtenoth, *Algebraic function fields and codes*, Prop. 3.9.6 (UNVERIFIED).) -/
def UnramCompositum : Prop :=
  ∀ (R K L L' M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field L'] [Algebra K L'] [Algebra R L'] [IsScalarTower R K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L']
    [Field M] [Algebra L M] [Algebra L' M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower K L' M] [IsScalarTower R K M],
    IntermediateField.adjoin L (Set.range (algebraMap L' M)) = ⊤ →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q)) →
    (∀ (Q : Ideal (integralClosure R L')) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L' ⧸ Q)) →
    ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q)

/-- Localization transfer, downwards: a prime of the integral closure of `R0_p` in `F` over the
maximal ideal comes from a prime of the integral closure of `R0` over `p`, with the same `e`. -/
theorem locTransfer_down (R0 F : Type) [CommRing R0] [IsDomain R0] [Field F] [Algebra R0 F]
    (p : Ideal R0) [p.IsPrime] [Algebra (Localization.AtPrime p) F]
    [IsScalarTower R0 (Localization.AtPrime p) F] (hinj : Function.Injective (algebraMap R0 F))
    (Q : Ideal (integralClosure (Localization.AtPrime p) F)) [Q.IsPrime]
    [Q.LiesOver (maximalIdeal (Localization.AtPrime p))] :
    letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
    ∃ P0 : Ideal (integralClosure R0 F), P0.IsPrime ∧ P0.under R0 = p ∧
      Q.ramificationIdx (Localization.AtPrime p) = P0.ramificationIdx R0 := by
  have hP : ∀ x ∈ p.primeCompl, algebraMap R0 F x ≠ 0 := fun x hx h0 =>
    hx (by rw [hinj (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  obtain ⟨h1, h2, h3⟩ := intCl_isLocalization R0 (Localization.AtPrime p) F p.primeCompl hP
  letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
  set P0 := Q.comap (algebraMap (integralClosure R0 F) (integralClosure (Localization.AtPrime p) F))
  haveI : P0.LiesOver p := IsLocalization.AtPrime.liesOver_comap_of_liesOver p (Localization.AtPrime p) Q
  haveI : P0.IsPrime := Ideal.IsPrime.comap _
  have hQ : Q = P0.map (algebraMap (integralClosure R0 F) (integralClosure (Localization.AtPrime p) F)) :=
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R0 F) p.primeCompl)
      (integralClosure (Localization.AtPrime p) F) Q).symm
  refine ⟨P0, inferInstance, (Ideal.LiesOver.over (P := P0) (p := p)).symm, ?_⟩
  rw [hQ]
  exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p _ _ P0

/-- Localization transfer, upwards. -/
theorem locTransfer_up (R0 F : Type) [CommRing R0] [IsDomain R0] [Field F] [Algebra R0 F]
    (p : Ideal R0) [p.IsPrime] [Algebra (Localization.AtPrime p) F]
    [IsScalarTower R0 (Localization.AtPrime p) F] (hinj : Function.Injective (algebraMap R0 F))
    (P : Ideal (integralClosure R0 F)) [P.IsPrime] [P.LiesOver p] :
    letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
    ∃ Q : Ideal (integralClosure (Localization.AtPrime p) F), Q.IsPrime ∧
      Q.LiesOver (maximalIdeal (Localization.AtPrime p)) ∧
      Q.ramificationIdx (Localization.AtPrime p) = P.ramificationIdx R0 := by
  have hP : ∀ x ∈ p.primeCompl, algebraMap R0 F x ≠ 0 := fun x hx h0 =>
    hx (by rw [hinj (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  obtain ⟨h1, h2, h3⟩ := intCl_isLocalization R0 (Localization.AtPrime p) F p.primeCompl hP
  letI := (intClIncl R0 (Localization.AtPrime p) F).toAlgebra
  exact ⟨_, IsLocalization.AtPrime.isPrime_map_of_liesOver _ p _ P,
    IsLocalization.AtPrime.liesOver_map_of_liesOver p _ _ P,
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p _ _ P⟩


/-- **Abstract compositum transfer (residue characteristic 0).** As `abhyankar_core`, with the
Kummer step replaced by an extension `A/R0` (finite via `σ`) unramified over `p`: if every prime of
the integral closure of `R0` in `L` over `p`, and every prime of `A` over `p`, has ramification
index `1`, then every prime of the integral closure of `A` in `M = L·Frac(A)` over a prime of `A`
over `p` has ramification index `1` over `A`. -/
theorem compositum_core0 (hU : UnramCompositum)
    (R0 K L M A : Type) [CommRing R0] [IsDomain R0] [IsDedekindDomain R0] [Algebra ℚ R0]
    [Field K] [Algebra R0 K] [IsFractionRing R0 K]
    [Field L] [Algebra K L] [Algebra R0 L] [IsScalarTower R0 K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Field M] [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A M]
    (ι : L →+* M) (σ : R0 →+* A) (hσ : ∀ x, algebraMap A M (σ x) = ι (algebraMap R0 L x))
    (hfin : letI := σ.toAlgebra; Module.Finite R0 A) (hσinj : Function.Injective σ)
    (hAM : Function.Injective (algebraMap A M))
    (p : Ideal R0) [hpp : p.IsPrime] (hp0 : p ≠ ⊥)
    (hadj : letI := ι.toAlgebra; IntermediateField.adjoin L (Set.range (algebraMap A M)) = ⊤)
    (hE : ∀ Q : Ideal (integralClosure R0 L), Q.IsPrime → Q.under R0 = p →
      Q.ramificationIdx R0 = 1)
    (hA : ∀ g : Ideal A, g.IsPrime → g.comap σ = p → letI := σ.toAlgebra;
      g.ramificationIdx R0 = 1)
    (Q' : Ideal (integralClosure A M)) [hQ'p : Q'.IsPrime] (hQ' : (Q'.under A).comap σ = p) :
    Q'.ramificationIdx A = 1 := by
  classical
  letI : Algebra R0 A := σ.toAlgebra
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  letI : Algebra R0 M := ((algebraMap K M).comp (algebraMap R0 K)).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 K M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R0 A M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ι (algebraMap K L (algebraMap R0 K x)) = algebraMap A M (σ x)
    rw [hσ, IsScalarTower.algebraMap_apply R0 K L]
  haveI : Module.Finite R0 A := hfin
  haveI : Algebra.IsIntegral R0 A := inferInstance
  haveI hpmax : p.IsMaximal := Ideal.IsPrime.isMaximal hpp hp0
  have hR0K : Function.Injective (algebraMap R0 K) := IsFractionRing.injective R0 K
  haveI : CharZero K := charZero_of_injective_ringHom
    (show Function.Injective ((algebraMap R0 K).comp (algebraMap ℚ R0)) from RingHom.injective _)
  -- the fraction field `K'` of `A`
  set K' := FractionRing A
  have hR0K' : Function.Injective (algebraMap R0 K') := by
    rw [IsScalarTower.algebraMap_eq R0 A K']
    exact (IsFractionRing.injective A K').comp hσinj
  letI : Algebra K K' := (IsFractionRing.lift hR0K' : K →+* K').toAlgebra
  haveI : IsScalarTower R0 K K' := IsScalarTower.of_algebraMap_eq
    (fun x => (IsFractionRing.lift_algebraMap hR0K' x).symm)
  haveI : Module.IsTorsionFree R0 A := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hσinj
  haveI : FaithfulSMul R0 K' := (faithfulSMul_iff_algebraMap_injective R0 K').mpr hR0K'
  haveI : FiniteDimensional K K' := by
    letI := FractionRing.liftAlgebra R0 K'
    haveI : IsScalarTower R0 (FractionRing R0) K' := FractionRing.isScalarTower_liftAlgebra R0 K'
    haveI : FiniteDimensional (FractionRing R0) K' := by
      haveI : FiniteDimensional (FractionRing R0) (FractionRing A) := inferInstance
      exact this
    refine Module.Finite.of_equiv_equiv (FractionRing.algEquiv R0 K).toRingEquiv
      (RingEquiv.refl K') ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors R0)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply R0 K K', ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable K K' := inferInstance
  letI : Algebra K' M := (IsFractionRing.lift hAM : K' →+* M).toAlgebra
  haveI : IsScalarTower A K' M := IsScalarTower.of_algebraMap_eq
    (fun x => (IsFractionRing.lift_algebraMap hAM x).symm)
  haveI : IsScalarTower K K' M := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors R0)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R0 K M, ← IsScalarTower.algebraMap_apply R0 K K',
      IsScalarTower.algebraMap_apply R0 A K', ← IsScalarTower.algebraMap_apply A K' M,
      ← IsScalarTower.algebraMap_apply R0 A M]
  -- the DVR `Rp`
  set Rp := Localization.AtPrime p
  haveI hDVR : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R0 hp0 Rp
  letI : Algebra Rp K := IsLocalization.localizationAlgebraOfSubmonoidLe Rp K p.primeCompl
    (nonZeroDivisors R0) p.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower R0 Rp K := IsLocalization.localization_isScalarTower_of_submonoid_le Rp K
    p.primeCompl (nonZeroDivisors R0) p.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rp K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rp K
  letI : Algebra Rp L := ((algebraMap K L).comp (algebraMap Rp K)).toAlgebra
  letI : Algebra Rp K' := ((algebraMap K K').comp (algebraMap Rp K)).toAlgebra
  letI : Algebra Rp M := ((algebraMap K M).comp (algebraMap Rp K)).toAlgebra
  haveI : IsScalarTower Rp K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rp K K' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rp K M := IsScalarTower.of_algebraMap_eq' rfl
  have tow : ∀ (F : Type) [Field F] [Algebra K F] [Algebra R0 F] [IsScalarTower R0 K F],
      letI : Algebra Rp F := ((algebraMap K F).comp (algebraMap Rp K)).toAlgebra
      IsScalarTower R0 Rp F := by
    intro F _ _ _ _
    letI : Algebra Rp F := ((algebraMap K F).comp (algebraMap Rp K)).toAlgebra
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R0 F x = algebraMap K F (algebraMap Rp K (algebraMap R0 Rp x))
    rw [← IsScalarTower.algebraMap_apply R0 Rp K, ← IsScalarTower.algebraMap_apply R0 K F]
  haveI : IsScalarTower R0 Rp L := tow L
  haveI : IsScalarTower R0 Rp K' := tow K'
  haveI : IsScalarTower R0 Rp M := tow M
  have hR0L : Function.Injective (algebraMap R0 L) := by
    rw [IsScalarTower.algebraMap_eq R0 K L]; exact (algebraMap K L).injective.comp hR0K
  have hR0M : Function.Injective (algebraMap R0 M) := by
    rw [IsScalarTower.algebraMap_eq R0 K M]; exact (algebraMap K M).injective.comp hR0K
  -- hypotheses of `UnramCompositum`
  have hadj' : IntermediateField.adjoin L (Set.range (algebraMap K' M)) = ⊤ := by
    refine eq_top_iff.mpr (hadj.symm.le.trans (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap A K' a, (IsScalarTower.algebraMap_apply A K' M a).symm⟩
  have hypL : ∀ (Q : Ideal (integralClosure Rp L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)],
      Q.ramificationIdx Rp = 1 ∧
      Algebra.IsSeparable (Rp ⧸ maximalIdeal Rp) (integralClosure Rp L ⧸ Q) := by
    intro Q _ _
    obtain ⟨P0, hP0, hP0u, he⟩ := locTransfer_down R0 L p hR0L Q
    refine ⟨he.trans (hE P0 hP0 hP0u), ?_⟩
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rp) Q
      (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rp)]; infer_instance)
    letI : Algebra ℚ Rp := ((algebraMap R0 Rp).comp (algebraMap ℚ R0)).toAlgebra
    exact isSeparable_residue_of_rat (maximalIdeal Rp) Q
  have hypL' : ∀ (Q : Ideal (integralClosure Rp K')) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)],
      Q.ramificationIdx Rp = 1 ∧
      Algebra.IsSeparable (Rp ⧸ maximalIdeal Rp) (integralClosure Rp K' ⧸ Q) := by
    intro Q _ _
    obtain ⟨P0, hP0, hP0u, he⟩ := locTransfer_down R0 K' p hR0K' Q
    refine ⟨?_, ?_⟩
    · rw [he]
      let e : integralClosure R0 K' ≃ₐ[R0] A :=
        IsIntegralClosure.equiv R0 (integralClosure R0 K') K' A
      rw [← ramificationIdx_map_algEquiv e P0]
      apply hA _ (Ideal.map_isPrime_of_equiv e)
      change Ideal.comap (algebraMap R0 A) (P0.map e) = p
      rw [← hP0u, Ideal.under]
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap, ← e.commutes x, ← Ideal.mem_comap,
        Ideal.comap_map_of_bijective e e.bijective]
    · haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rp) Q
        (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rp)]; infer_instance)
      letI : Algebra ℚ Rp := ((algebraMap R0 Rp).comp (algebraMap ℚ R0)).toAlgebra
      exact isSeparable_residue_of_rat (maximalIdeal Rp) Q
  have key := hU Rp K L K' M hadj' hypL hypL'
  -- back to `integralClosure A M`
  have hmem : ∀ x : M, IsIntegral A x ↔ IsIntegral R0 x := fun x =>
    ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩
  let f0 : integralClosure A M ≃+* integralClosure R0 M :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (hmem y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let f : integralClosure A M ≃ₐ[R0] integralClosure R0 M :=
    AlgEquiv.ofRingEquiv (f := f0) (fun r => rfl)
  haveI : Q'.LiesOver p := ⟨by rw [← Ideal.under_under (B := A) Q']; exact hQ'.symm⟩
  set P := Q'.map f with hP_def
  haveI : P.IsPrime := Ideal.map_isPrime_of_equiv f
  have hPunder : P.under R0 = p := by
    ext x
    rw [Ideal.under, Ideal.mem_comap, hP_def, ← f.commutes x, ← Ideal.mem_comap,
      Ideal.comap_map_of_bijective f f.bijective, ← Ideal.mem_comap]
    change x ∈ Q'.under R0 ↔ x ∈ p
    rw [← Ideal.LiesOver.over (P := Q') (p := p)]
  haveI : P.LiesOver p := ⟨hPunder.symm⟩
  obtain ⟨Qp, hQp, hQpl, hQpe⟩ := locTransfer_up R0 M p hR0M P
  have h1 := (key Qp).1
  rw [hQpe, hP_def, ramificationIdx_map_algEquiv f Q'] at h1
  haveI : Module.IsTorsionFree A (integralClosure A M) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply hAM
    have := congrArg Subtype.val hxy
    simpa using this
  haveI : Q'.LiesOver (Q'.under A) := ⟨rfl⟩
  have htow := Ideal.ramificationIdx_tower (R := R0) (Q'.under A) Q'
  rw [h1] at htow
  exact Nat.eq_one_of_mul_eq_one_left htow.symm

/-- A copy of `ℚ[X]` used as the source of a substitution `X ↦ r` (so that its module structure
on the target `ℚ[X]` is the one induced by the substitution). -/
def SrcPoly : Type := Polynomial ℚ

instance : CommRing SrcPoly := inferInstanceAs (CommRing ℚ[X])
instance : IsDomain SrcPoly := inferInstanceAs (IsDomain ℚ[X])
instance : IsPrincipalIdealRing SrcPoly := inferInstanceAs (IsPrincipalIdealRing ℚ[X])
instance : IsDedekindDomain SrcPoly := inferInstanceAs (IsDedekindDomain ℚ[X])
instance : Algebra ℚ SrcPoly := inferInstanceAs (Algebra ℚ ℚ[X])

/-- The identity `SrcPoly → ℚ[X]`. -/
def SrcPoly.toPoly (f : SrcPoly) : ℚ[X] := f

/-- Substitution `X ↦ r` (`r` non-constant) is unramified at every nonzero prime `g` of the target
`ℚ[X]` not containing `r'`. -/
theorem polyUnram (r : ℚ[X]) (hr : 0 < r.natDegree)
    (hint : (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).IsIntegral)
    (g : Ideal ℚ[X]) [hg : g.IsPrime] (hg0 : g ≠ ⊥) (hder : derivative r ∉ g) :
    letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
    g.ramificationIdx SrcPoly = 1 := by
  letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
  have hσ : ∀ f : SrcPoly, algebraMap SrcPoly ℚ[X] f = f.toPoly.comp r := fun f => rfl
  have hinj : Function.Injective (algebraMap SrcPoly ℚ[X]) := by
    rw [injective_iff_map_eq_zero]; intro f hf
    change f.toPoly.comp r = 0 at hf
    rw [comp_eq_zero_iff] at hf
    rcases hf with hf | ⟨_, hr'⟩
    · exact hf
    · exfalso; rw [hr', natDegree_C] at hr; exact lt_irrefl 0 hr
  haveI : Module.IsTorsionFree SrcPoly ℚ[X] :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
  set h := g.under SrcPoly with hh_def
  have hh0 : h ≠ ⊥ := Ideal.IsIntegral.under_ne_bot SrcPoly hg0
  obtain ⟨q, rfl⟩ := Submodule.IsPrincipal.principal g
  obtain ⟨f, hf⟩ := Submodule.IsPrincipal.principal h
  have hq0 : q ≠ 0 := fun h0 => hg0 (by rw [h0]; exact Submodule.span_singleton_eq_bot.mpr rfl)
  have hqp : Prime q := (Ideal.span_singleton_prime hq0).mp hg
  have hf0 : f ≠ 0 := fun h0 => hh0 (by rw [hf, h0]; exact Submodule.span_singleton_eq_bot.mpr rfl)
  haveI hhp : h.IsPrime := Ideal.IsPrime.under _ _
  have hfp : Prime f := by
    have : (Ideal.span {f} : Ideal SrcPoly).IsPrime := by
      have e : (Ideal.span {f} : Ideal SrcPoly) = h := hf.symm
      rw [e]; exact hhp
    exact (Ideal.span_singleton_prime hf0).mp this
  have hfp' : Prime f.toPoly := hfp
  haveI : (Ideal.span {q}).LiesOver h := ⟨rfl⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx h (Ideal.span {q}) hh0]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]; exact Ideal.map_comap_le
  · have hfmem : f ∈ h := by rw [hf]; exact Submodule.mem_span_singleton_self f
    have hFq : q ∣ f.toPoly.comp r := by
      rw [← Ideal.mem_span_singleton, ← hσ]; exact hfmem
    have hmap : h.map (algebraMap SrcPoly ℚ[X]) = Ideal.span {f.toPoly.comp r} := by
      have e : h = Ideal.span {f} := hf
      rw [e, Ideal.map_span, Set.image_singleton, hσ]
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    intro hdvd
    have h2 : q ∣ derivative (f.toPoly.comp r) := by
      simpa using pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    rw [derivative_comp] at h2
    rcases hqp.dvd_or_dvd h2 with h3 | h3
    · exact hder (Ideal.mem_span_singleton.mpr h3)
    · obtain ⟨u, v, huv⟩ := (hfp'.irreducible.separable : f.toPoly.Separable)
      have := congrArg (fun t => t.comp r) huv
      simp only [add_comp, mul_comp, one_comp] at this
      have h4 : q ∣ 1 := by
        rw [← this]
        exact dvd_add (dvd_mul_of_dvd_right hFq _) (dvd_mul_of_dvd_right h3 _)
      exact hqp.not_unit (isUnit_of_dvd_one h4)

/-- An integral substitution `X ↦ r` makes `ℚ[X]` module-finite over the source. -/
theorem finite_of_isIntegral (r : ℚ[X])
    (hint : (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).IsIntegral) :
    letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
    Module.Finite SrcPoly ℚ[X] := by
  letI : Algebra SrcPoly ℚ[X] := (Polynomial.eval₂RingHom C r : SrcPoly →+* ℚ[X]).toAlgebra
  haveI : IsScalarTower ℚ SrcPoly ℚ[X] := IsScalarTower.of_algebraMap_eq (fun a => by
    change C a = (C a).comp r
    rw [C_comp])
  haveI : Algebra.FiniteType SrcPoly ℚ[X] :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := ℚ) (S := SrcPoly) (A := ℚ[X])
  haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
  exact Algebra.IsIntegral.finite

/-- Compatibility of the finite Kummer substitution with `ι` (from `KummerShape`). -/
theorem finSubst_compat {E E' : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] (ι : E →+* E') (b c : ℚ) (n : ℕ) (hc : c ≠ 0)
    (hshape : KummerShape E E' ι (rFin b c n)) (x : ℚ[X]) :
    algebraMap ℚ[X] E' (Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n) x) =
      ι (algebraMap ℚ[X] E x) := by
  have : (algebraMap ℚ[X] E').comp (Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n)) =
      ι.comp (algebraMap ℚ[X] E) := by
    apply Polynomial.ringHom_ext
    · intro a
      have := RingHom.ext_rat
        (((algebraMap ℚ[X] E').comp (Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n))).comp C)
        ((ι.comp (algebraMap ℚ[X] E)).comp C)
      exact congrArg (fun g => g a) this
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
        IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E', RatFunc.algebraMap_X, hshape.1]
      congr 1
      rw [rFin, eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (C_ne_zero.mpr hc)), ← map_mul]
      congr 1
      have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
      rw [C_mul]
      linear_combination (X ^ n) * h1
  exact congrArg (fun g => g x) this

/-- A prime of `ℚ[X]` containing an irreducible `f` is `(f)`. -/
theorem eq_span_of_irreducible_mem {f : ℚ[X]} (hf : Irreducible f) (g : Ideal ℚ[X])
    [hg : g.IsPrime] (hX : f ∈ g) : g = Ideal.span {f} := by
  have hmax : (Ideal.span {f} : Ideal ℚ[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hf
  exact (hmax.eq_of_le hg.ne_top (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))).symm

/-- `X` is the only prime of `ℚ[X]` containing `X`. -/
theorem eq_span_X_of_mem (g : Ideal ℚ[X]) [hg : g.IsPrime] (hX : X ∈ g) : g = Ideal.span {X} :=
  eq_span_of_irreducible_mem irreducible_X g hX

/-- `r' = C (c⁻¹ n) X^(n-1)` lies outside every prime not containing `X`. -/
theorem derivative_notMem (a c : ℚ) (n : ℕ) (hn : 0 < n) (hc : c ≠ 0) (g : Ideal ℚ[X])
    [hg : g.IsPrime] (hX : X ∉ g) : derivative (C a + C c⁻¹ * X ^ n) ∉ g := by
  rw [derivative_add, derivative_C, zero_add, derivative_C_mul_X_pow]
  intro hm
  rcases hg.mem_or_mem hm with h1 | h1
  · refine hg.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_C.mpr (Ne.isUnit ?_)))
    exact mul_ne_zero (inv_ne_zero hc) (by exact_mod_cast hn.ne')
  · exact hX (hg.mem_of_pow_mem _ h1)

/-- **`KummerOtherBranchFin` from `UnramCompositum`.** -/
theorem kummerOtherBranchFin_of_unram (hU : UnramCompositum) : KummerOtherBranchFin := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι b c n hn hc hshape S hbS hE Q' hQ'p hQ'e
  classical
  let σ : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C b + C c⁻¹ * X ^ n)
  have hσC : ∀ a : ℚ, σ (C a) = C a := fun a => by simp [σ]
  have hσX : σ X = C b + C c⁻¹ * X ^ n := by simp [σ]
  have hsn : σ (C c * (X - C b)) = X ^ n := by
    rw [map_mul, map_sub, hσC, hσC, hσX, add_sub_cancel_left, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * (X - C b)), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hint : σ.IsIntegral := isIntegral_of_X σ hσC hXint
  have hrdeg : 0 < (C b + C c⁻¹ * X ^ n : ℚ[X]).natDegree := by
    rw [natDegree_C_add, natDegree_C_mul_X_pow n _ (inv_ne_zero hc)]; exact hn
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]; intro f hf
    change f.comp (C b + C c⁻¹ * X ^ n) = 0 at hf
    rw [comp_eq_zero_iff] at hf
    rcases hf with hf | ⟨_, hr'⟩
    · exact hf
    · exfalso
      have := congrArg natDegree hr'
      rw [natDegree_C] at this; omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hS'⟩ := hcon
  apply hQ'e
  set g := Q'.under ℚ[X] with hg_def
  haveI hgp : g.IsPrime := Ideal.IsPrime.under _ _
  have hQ'0 : Q' ≠ ⊥ := by rintro rfl; exact hQ'e (Ideal.ramificationIdx_bot_eq_one _)
  have hg0 : g ≠ ⊥ := Ideal.IsIntegral.under_ne_bot ℚ[X] hQ'0
  have hXg : X ∉ g := fun hX => hne (eq_span_X_of_mem g hX)
  set h := g.comap σ with hh_def
  haveI hhp : h.IsPrime := Ideal.IsPrime.comap σ
  have hh0 : h ≠ ⊥ := by
    letI : Algebra SrcPoly ℚ[X] := (σ : SrcPoly →+* ℚ[X]).toAlgebra
    haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
    exact Ideal.IsIntegral.under_ne_bot SrcPoly hg0
  have hXb : ∀ g' : Ideal ℚ[X], g'.IsPrime → g'.comap σ = h → X ∉ g' → X - C b ∉ h := by
    intro g' hg'p hg' hXg' hm
    rw [← hg'] at hm
    have hm' : σ (X - C b) ∈ g' := hm
    rw [map_sub, hσX, hσC, add_sub_cancel_left] at hm'
    rcases hg'p.mem_or_mem hm' with h1 | h1
    · exact hg'p.ne_top (Ideal.eq_top_of_isUnit_mem _ h1
        (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hc))))
    · exact hXg' (hg'p.mem_of_pow_mem n h1)
  have hhS : ∀ b' ∈ S, h ≠ Ideal.span {X - C b'} := by
    intro b' hb' heq
    have hmem : X - C b' ∈ h := heq ▸ Ideal.mem_span_singleton_self _
    by_cases hbb : b' = b
    · subst hbb; exact hXb g hgp rfl hXg hmem
    · apply hS' b' hb' hbb
      have hm' : σ (X - C b') ∈ g := hmem
      have e : (X ^ n - C (c * (b' - b)) : ℚ[X]) = C c * σ (X - C b') := by
        rw [map_sub, hσX, hσC]
        have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
        rw [C_mul, C_sub]
        linear_combination (-(X ^ n)) * h1
      rw [e]; exact Ideal.mul_mem_left _ _ hm'
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap ℚ[X] E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨X, rfl⟩
  refine compositum_core0 hU ℚ[X] (RatFunc ℚ) E E' ℚ[X] ι σ
    (finSubst_compat ι b c n hc hshape) (finite_of_isIntegral _ hint) hσinj (polyMap_injective E')
    h hh0 hadj ?_ ?_ Q' rfl
  · intro Q hQ hQu
    exact hE Q hQ (fun b' hb' => by rw [hQu]; exact hhS b' hb')
  · intro g' hg'p hg'
    have hg'0 : g' ≠ ⊥ := by
      rintro rfl
      apply hh0
      rw [← hg', Ideal.comap_bot_of_injective σ hσinj]
    have hXg' : X ∉ g' := by
      intro hX
      apply hhS b hbS
      have hm : X - C b ∈ h := by
        rw [← hg']
        change σ (X - C b) ∈ g'
        rw [map_sub, hσX, hσC, add_sub_cancel_left]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hX n hn)
      exact eq_span_of_irreducible_mem (irreducible_X_sub_C b) h hm
    exact polyUnram _ hrdeg hint g' hg'0 (derivative_notMem b c n hn hc g' hXg')

theorem sepCongr {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q) [Algebra.HasSeparableResidueFieldsAt A B p] :
    Algebra.HasSeparableResidueFieldsAt A B q := by
  subst h
  assumption

/-- A finite separable extension, unramified at every prime over the maximal ideal of a DVR, has
formally unramified integral closure. -/
theorem fu_of_unram (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q)) :
    Algebra.FormallyUnramified R (integralClosure R L) := by
  classical
  set B := integralClosure R L
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI : Algebra.EssFiniteType R B := inferInstance
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  rw [Algebra.formallyUnramified_iff_forall]
  rintro ⟨q, hq⟩
  by_cases hq0 : q = ⊥
  · subst hq0
    change Algebra.FormallyUnramified R (Localization.AtPrime (⊥ : Ideal B))
    haveI : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
      simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
    let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] L :=
      IsLocalization.algEquiv (nonZeroDivisors B) _ L
    haveI : Algebra.FormallyUnramified R K := Algebra.FormallyUnramified.of_isLocalization
      (M := nonZeroDivisors R)
    haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
    haveI : Algebra.FormallyUnramified R L := Algebra.FormallyUnramified.comp R K L
    exact Algebra.FormallyUnramified.of_equiv (e.symm.restrictScalars R)
  · have hu0 : q.under R ≠ ⊥ := Ideal.IsIntegral.under_ne_bot R hq0
    haveI : (q.under R).IsPrime := Ideal.IsPrime.under R q
    have hu : q.under R = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hu0)
    haveI : q.LiesOver (maximalIdeal R) := ⟨hu.symm⟩
    have he := (h q).1
    haveI : Algebra.HasSeparableResidueFieldsAt R B (maximalIdeal R) := by
      constructor
      intro q' _ _
      letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) q'
      haveI : q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q'
        (by rw [← Ideal.LiesOver.over (P := q') (p := maximalIdeal R)]; infer_instance)
      haveI := (h q').2
      exact Algebra.isSeparable_residueField_iff.mpr inferInstance
    haveI : Algebra.HasSeparableResidueFieldsAt R B (q.under R) := sepCongr hu.symm
    exact (Ideal.ramificationIdx_eq_one_iff).mp he

/-- **`UnramCompositum` is proved.** Proof: the integral closures `B`, `B'` of `R` in `L`, `L'` are
formally unramified over `R` (`fu_of_unram`); the image `D` of `B ⊗_R B'` in `M` is finite and
formally unramified over `R`, so each localization of `D` at a maximal ideal has maximal ideal
generated by a uniformizer of `R`, hence is a DVR; so `D` is integrally closed, with fraction field
`M = L·L'`, hence `D` is the integral closure of `R` in `M`, which is therefore unramified. -/
theorem unramCompositum : UnramCompositum := by
  intro R K L L' M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hadj hL hL' Q _ _
  classical
  set B := integralClosure R L
  set B' := integralClosure R L'
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply K L M,
      ← IsScalarTower.algebraMap_apply R K L])
  haveI : IsScalarTower R L' M := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply K L' M,
      ← IsScalarTower.algebraMap_apply R K L'])
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI : Module.Finite R B' := IsIntegralClosure.finite R K L' B'
  haveI hfB : Algebra.FormallyUnramified R B := fu_of_unram R K L hL
  haveI hfB' : Algebra.FormallyUnramified R B' := fu_of_unram R K L' hL'
  let fB : B →ₐ[R] M := (IsScalarTower.toAlgHom R L M).comp (integralClosure R L).val
  let fB' : B' →ₐ[R] M := (IsScalarTower.toAlgHom R L' M).comp (integralClosure R L').val
  let φ : B ⊗[R] B' →ₐ[R] M :=
    Algebra.TensorProduct.lift fB fB' (fun _ _ => Commute.all _ _)
  set D : Subalgebra R M := φ.range
  haveI : Algebra.FormallyUnramified B (B ⊗[R] B') := inferInstance
  haveI : Algebra.FormallyUnramified R (B ⊗[R] B') := Algebra.FormallyUnramified.comp R B _
  haveI hfD : Algebra.FormallyUnramified R D :=
    Algebra.FormallyUnramified.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI hDfin : Module.Finite R D :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R K M]; exact (algebraMap K M).injective.comp hRK
  have hDinj : Function.Injective (algebraMap D M) := Subtype.val_injective
  have hRD : Function.Injective (algebraMap R D) := by
    intro x y hxy
    apply hRM
    have := congrArg Subtype.val hxy
    simpa using this
  have hfBD : ∀ b : B, fB b ∈ D := fun b => ⟨b ⊗ₜ 1, by simp [φ]⟩
  have hfB'D : ∀ b : B', fB' b ∈ D := fun b => ⟨1 ⊗ₜ b, by simp [φ]⟩
  -- the fraction field of `D` is `M`
  let F : Subfield M := (IsFractionRing.lift (K := FractionRing D) hDinj).fieldRange
  have hDF : ∀ d : D, (d : M) ∈ F := fun d =>
    ⟨algebraMap D (FractionRing D) d, IsFractionRing.lift_algebraMap _ _⟩
  have hF : ∀ (L₀ : Type) [Field L₀] [Algebra K L₀] [Algebra R L₀] [IsScalarTower R K L₀]
      [FiniteDimensional K L₀] [Algebra L₀ M] [IsScalarTower K L₀ M] (f₀ : integralClosure R L₀ →ₐ[R] M),
      (∀ b, f₀ b = algebraMap L₀ M b) → (∀ b, f₀ b ∈ D) → ∀ l : L₀, algebraMap L₀ M l ∈ F := by
    intro L₀ _ _ _ _ _ _ _ f₀ hf₀ hf₀D l
    have halg : IsAlgebraic R l :=
      (IsFractionRing.isAlgebraic_iff R K L₀).mpr (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
    let b : integralClosure R L₀ := ⟨y • l, hyint⟩
    have hy : algebraMap R M y ≠ 0 := (map_ne_zero_iff _ hRM).mpr hy0
    have e : algebraMap L₀ M l = f₀ b / algebraMap R M y := by
      rw [eq_div_iff hy, hf₀]
      change _ = algebraMap L₀ M (y • l)
      rw [Algebra.smul_def, map_mul, mul_comm, IsScalarTower.algebraMap_apply R K L₀,
        IsScalarTower.algebraMap_apply R K M, ← IsScalarTower.algebraMap_apply K L₀ M]
    rw [e]
    refine div_mem (hDF ⟨_, hf₀D b⟩) ?_
    exact hDF (algebraMap R D y)
  have hLF := hF L fB (fun _ => rfl) hfBD
  have hL'F := hF L' fB' (fun _ => rfl) hfB'D
  have hFtop : F = ⊤ := by
    letI := (algebraMap L M)
    have h1 := congrArg IntermediateField.toSubfield hadj
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h1
    rw [eq_top_iff, ← h1, Subfield.closure_le]
    rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
    · exact hLF l
    · exact hL'F l
  haveI hFrac : IsFractionRing D M := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro z
      have hz : z ∈ F := hFtop ▸ Subfield.mem_top z
      obtain ⟨w, rfl⟩ := hz
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := D) w
      refine ⟨⟨x, ⟨y, hy⟩⟩, ?_⟩
      simp only [map_div₀, IsFractionRing.lift_algebraMap]
      exact div_mul_cancel₀ _ ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro x y hxy
      exact ⟨1, by simp [hDinj hxy]⟩
  -- `D` is integrally closed
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing R D
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmaxR : maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI hDic : IsIntegrallyClosed D := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P hP0 hPmax
    have hPu : P.under R = maximalIdeal R := IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under R P)
    set Dp := Localization.AtPrime P
    haveI : IsLocalHom (algebraMap R Dp) := by
      constructor
      intro r hr
      by_contra hnu
      have hrm : r ∈ maximalIdeal R := hnu
      rw [← hPu] at hrm
      have : algebraMap D Dp (algebraMap R D r) ∈ maximalIdeal Dp := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hrm
      rw [← IsScalarTower.algebraMap_apply] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hr
    haveI : Algebra.FormallyUnramified D Dp :=
      Algebra.FormallyUnramified.of_isLocalization (M := P.primeCompl)
    haveI : Algebra.FormallyUnramified R Dp := Algebra.FormallyUnramified.comp R D Dp
    haveI : Algebra.EssFiniteType D Dp := Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType R Dp := Algebra.EssFiniteType.comp R D Dp
    have hmaxDp : maximalIdeal Dp = Ideal.span {algebraMap R Dp ϖ} := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := Dp), hmaxR, Ideal.map_span,
        Set.image_singleton]
    have hRDp : Function.Injective (algebraMap R Dp) := by
      rw [IsScalarTower.algebraMap_eq R D Dp]
      exact (IsLocalization.injective Dp P.primeCompl_le_nonZeroDivisors).comp hRD
    have hnf : ¬ IsField Dp := by
      intro hF
      have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
      rw [hmaxDp, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ hRDp] at this
      exact hϖ.ne_zero this
    have hprin : (maximalIdeal Dp).IsPrincipal := ⟨⟨_, hmaxDp⟩⟩
    haveI : IsDiscreteValuationRing Dp :=
      ((IsDiscreteValuationRing.TFAE Dp hnf).out 1 5).mpr hprin
    infer_instance
  -- `D` is the integral closure of `R` in `M`
  have hDC : D = integralClosure R M := by
    apply le_antisymm
    · intro x hx
      exact (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : D)).map (IsScalarTower.toAlgHom R D M)
    · intro x hx
      have hxD : IsIntegral D x := IsIntegral.tower_top hx
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := D) (K := M)).mp hxD
      exact y.2
  -- conclusion
  let eDC : D ≃ₐ[R] integralClosure R M := Subalgebra.equivOfEq D _ hDC
  haveI : Algebra.FormallyUnramified R (integralClosure R M) :=
    Algebra.FormallyUnramified.of_equiv eDC
  haveI : Module.Finite R (integralClosure R M) := Module.Finite.equiv eDC.toLinearEquiv
  haveI : Algebra.IsUnramifiedAt R Q :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance ⟨Q, inferInstance⟩
  refine ⟨Ideal.ramificationIdx_eq_one Q R, ?_⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q
    (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal R)]; infer_instance)
  letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) Q
  have hsep := ((Algebra.isUnramifiedAt_iff_map_eq R (maximalIdeal R) Q).mp inferInstance).1
  exact Algebra.isSeparable_residueField_iff.mp hsep

/-- `ℚ → ℚ[1/X]`, constants. -/
def Cinf : ℚ →+* InfCoord := (Polynomial.C : ℚ →+* ℚ[X])

/-- The identity `ℚ[X] → InfCoord` (as types). -/
def toInf (f : ℚ[X]) : InfCoord := f

/-- **Transfer between `ℚ[1/X]` and `ℚ[X]` away from `0` and `∞`.** A prime `Q` of the integral
closure of `ℚ[1/X]` in `E` over a prime `h` with `1/X ∉ h` has the ramification index of a prime
`QX` of the integral closure of `ℚ[X]` in `E`; if `QX` lies over `X − b'`, then `b' ≠ 0` and
`b'·(1/X) − 1 ∈ h`. -/
theorem infTransfer (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] (h : Ideal InfCoord) [hh : h.IsPrime]
    (hu : infUnif ∉ h) :
    letI := infAlg E
    ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime → Q.under InfCoord = h →
      ∃ QX : Ideal (integralClosure ℚ[X] E), QX.IsPrime ∧
        QX.ramificationIdx ℚ[X] = Q.ramificationIdx InfCoord ∧
        ∀ b' : ℚ, QX.under ℚ[X] = Ideal.span {X - C b'} →
          b' ≠ 0 ∧ toInf (C b' * X - 1) ∈ h := by
  letI := infAlg E
  intro Q hQp hQu
  classical
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
  haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  set Rp := Localization.AtPrime h
  letI : Algebra Rp (RatFunc ℚ) := IsLocalization.localizationAlgebraOfSubmonoidLe Rp (RatFunc ℚ)
    h.primeCompl (nonZeroDivisors InfCoord) h.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower InfCoord Rp (RatFunc ℚ) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Rp (RatFunc ℚ)
      h.primeCompl (nonZeroDivisors InfCoord) h.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Rp (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization h.primeCompl Rp (RatFunc ℚ)
  letI : Algebra Rp E := ((algebraMap (RatFunc ℚ) E).comp (algebraMap Rp (RatFunc ℚ))).toAlgebra
  haveI : IsScalarTower Rp (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower InfCoord Rp E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc ℚ) E (algebraMap InfCoord (RatFunc ℚ) x) =
      algebraMap (RatFunc ℚ) E (algebraMap Rp (RatFunc ℚ) (algebraMap InfCoord Rp x))
    rw [← IsScalarTower.algebraMap_apply InfCoord Rp (RatFunc ℚ)]
  have hRpK : Function.Injective (algebraMap Rp (RatFunc ℚ)) := IsFractionRing.injective Rp _
  -- the unit `μ` (image of `1/X`) and the map `τ : ℚ[X] → Rp`, `X ↦ μ⁻¹`
  have hμ : IsUnit (algebraMap InfCoord Rp infUnif) :=
    IsLocalization.map_units Rp (⟨infUnif, hu⟩ : h.primeCompl)
  set μ := hμ.unit with hμ_def
  let i0 : ℚ →+* Rp := (algebraMap InfCoord Rp).comp Cinf
  let τ : ℚ[X] →+* Rp := Polynomial.eval₂RingHom i0 (↑μ⁻¹ : Rp)
  have hevalμ : ∀ f : ℚ[X], eval₂ i0 (μ : Rp) f = algebraMap InfCoord Rp (toInf f) := by
    intro f
    have := Polynomial.hom_eval₂ f (Polynomial.C : ℚ →+* ℚ[X])
      (algebraMap InfCoord Rp : ℚ[X] →+* Rp) X
    rw [eval₂_C_X] at this
    rw [hμ_def, IsUnit.unit_spec]
    exact this.symm
  have hrefl : ∀ (f : ℚ[X]) (N : ℕ), f.natDegree ≤ N →
      τ (reflect N f) * (μ : Rp) ^ N = algebraMap InfCoord Rp (toInf f) := by
    intro f N hf
    letI : Invertible (μ : Rp) := μ.invertible
    have := eval₂_reflect_mul_pow i0 (μ : Rp) N f hf
    rw [hevalμ] at this
    rw [← this]
    rfl
  -- compatibility of `τ` with the maps to `ℚ(X)`
  have hτK : ∀ f : ℚ[X], algebraMap Rp (RatFunc ℚ) (τ f) = algebraMap ℚ[X] (RatFunc ℚ) f := by
    have : (algebraMap Rp (RatFunc ℚ)).comp τ = algebraMap ℚ[X] (RatFunc ℚ) := by
      apply Polynomial.ringHom_ext
      · intro a
        have := RingHom.ext_rat (((algebraMap Rp (RatFunc ℚ)).comp τ).comp C)
          ((algebraMap ℚ[X] (RatFunc ℚ)).comp C)
        exact congrArg (fun g => g a) this
      · simp only [RingHom.comp_apply]
        change algebraMap Rp (RatFunc ℚ) (eval₂ i0 (↑μ⁻¹ : Rp) X) = _
        rw [eval₂_X, RatFunc.algebraMap_X]
        have h1 : algebraMap Rp (RatFunc ℚ) (μ : Rp) = RatFunc.X⁻¹ := by
          rw [hμ_def, IsUnit.unit_spec, ← IsScalarTower.algebraMap_apply]
          change eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ (X : ℚ[X]) = _
          rw [eval₂_X]
        have h2 : algebraMap Rp (RatFunc ℚ) (↑μ⁻¹ : Rp) * algebraMap Rp (RatFunc ℚ) (μ : Rp) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [h1] at h2
        exact (mul_inv_eq_one₀ RatFunc.X_ne_zero).mp h2
    intro f
    exact congrArg (fun g => g f) this
  have hτinj : Function.Injective τ := by
    intro x y hxy
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    rw [← hτK, ← hτK, hxy]
  letI : Algebra ℚ[X] Rp := τ.toAlgebra
  haveI : IsScalarTower ℚ[X] Rp E := by
    apply IsScalarTower.of_algebraMap_eq
    intro f
    change algebraMap ℚ[X] E f = algebraMap (RatFunc ℚ) E (algebraMap Rp (RatFunc ℚ) (τ f))
    rw [hτK, ← IsScalarTower.algebraMap_apply]
  set hX : Ideal ℚ[X] := (maximalIdeal Rp).comap (algebraMap ℚ[X] Rp) with hX_def
  haveI : hX.IsPrime := Ideal.IsPrime.comap _
  -- `Rp` is the localization of `ℚ[X]` at `hX`
  haveI hlocX : IsLocalization.AtPrime Rp hX := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact (IsLocalRing.notMem_maximalIdeal).mp hy
    · intro z
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective h.primeCompl z
      set N := max (a : ℚ[X]).natDegree (s.1 : ℚ[X]).natDegree
      have ha := hrefl a N (le_max_left _ _)
      have hs := hrefl s.1 N (le_max_right _ _)
      have hsu : IsUnit (algebraMap InfCoord Rp s.1) := IsLocalization.map_units Rp s
      have hys : IsUnit (τ (reflect N (s.1 : ℚ[X]))) := by
        have : IsUnit (τ (reflect N (s.1 : ℚ[X])) * (μ : Rp) ^ N) := by rw [hs]; exact hsu
        exact isUnit_of_mul_isUnit_left this
      refine ⟨⟨reflect N (a : ℚ[X]), ⟨reflect N (s.1 : ℚ[X]), fun hm => ?_⟩⟩, ?_⟩
      · exact (IsLocalRing.notMem_maximalIdeal.mpr hys) hm
      · change IsLocalization.mk' Rp a s * τ (reflect N (s.1 : ℚ[X])) = τ (reflect N (a : ℚ[X]))
        have hμN : IsUnit ((μ : Rp) ^ N) := (Units.isUnit μ).pow N
        apply hμN.mul_right_cancel
        rw [mul_assoc, hs, ha]
        exact IsLocalization.mk'_spec Rp a s
    · intro x y hxy
      exact ⟨1, by simp [hτinj hxy]⟩
  -- integral closures
  have hP1 : ∀ x ∈ h.primeCompl, algebraMap InfCoord E x ≠ 0 := by
    intro x hx h0
    apply hx
    have hinj : Function.Injective (algebraMap InfCoord E) := by
      rw [IsScalarTower.algebraMap_eq InfCoord (RatFunc ℚ) E]
      exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective _ _)
    rw [hinj (h0.trans (map_zero _).symm)]; exact h.zero_mem
  have hP2 : ∀ x ∈ hX.primeCompl, algebraMap ℚ[X] E x ≠ 0 := by
    intro x hx h0
    apply hx
    have hinj : Function.Injective (algebraMap ℚ[X] E) := by
      rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
      exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective _ _)
    rw [hinj (h0.trans (map_zero _).symm)]; exact hX.zero_mem
  obtain ⟨h11, h12, h13⟩ := intCl_isLocalization InfCoord Rp E h.primeCompl hP1
  obtain ⟨h21, h22, h23⟩ := intCl_isLocalization ℚ[X] Rp E hX.primeCompl hP2
  letI := (intClIncl InfCoord Rp E).toAlgebra
  letI := (intClIncl ℚ[X] Rp E).toAlgebra
  haveI : Q.LiesOver h := ⟨hQu.symm⟩
  set Qp := Q.map (algebraMap (integralClosure InfCoord E) (integralClosure Rp E))
  haveI : Qp.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver _ h _ Q
  haveI : Qp.LiesOver (maximalIdeal Rp) := IsLocalization.AtPrime.liesOver_map_of_liesOver h Rp _ Q
  have he1 : Qp.ramificationIdx Rp = Q.ramificationIdx InfCoord :=
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx h Rp _ Q
  set QX := Qp.comap (algebraMap (integralClosure ℚ[X] E) (integralClosure Rp E))
  haveI : QX.LiesOver hX := IsLocalization.AtPrime.liesOver_comap_of_liesOver hX Rp Qp
  haveI : QX.IsPrime := Ideal.IsPrime.comap _
  have hQpX : Qp = QX.map (algebraMap (integralClosure ℚ[X] E) (integralClosure Rp E)) :=
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure ℚ[X] E)
      hX.primeCompl) (integralClosure Rp E) Qp).symm
  have he2 : Qp.ramificationIdx Rp = QX.ramificationIdx ℚ[X] := by
    rw [hQpX]
    exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx hX Rp _ QX
  refine ⟨QX, inferInstance, he2.symm.trans he1, ?_⟩
  intro b' hb'
  have hmem : X - C b' ∈ hX := by
    have e0 : hX = QX.under ℚ[X] := Ideal.LiesOver.over
    rw [e0, hb']
    exact Ideal.mem_span_singleton_self _
  have hm : τ (X - C b') ∈ maximalIdeal Rp := hmem
  rw [map_sub] at hm
  change eval₂ i0 (↑μ⁻¹ : Rp) X - eval₂ i0 (↑μ⁻¹ : Rp) (C b') ∈ maximalIdeal Rp at hm
  rw [eval₂_X, eval₂_C] at hm
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [map_zero, sub_zero] at hm
    exact (IsLocalRing.notMem_maximalIdeal.mpr (Units.isUnit μ⁻¹)) hm
  · have hm2 : (μ : Rp) * (↑μ⁻¹ - i0 b') ∈ maximalIdeal Rp := Ideal.mul_mem_left _ _ hm
    have e : (μ : Rp) * (↑μ⁻¹ - i0 b') = -algebraMap InfCoord Rp (toInf (C b' * X - 1)) := by
      rw [mul_sub, Units.mul_inv, ← hevalμ]
      simp only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_one]
      ring
    rw [e, neg_mem_iff] at hm2
    rw [← Localization.AtPrime.comap_maximalIdeal (I := h)]
    exact hm2

/-- Compatibility of the Kummer substitution at `∞` (`1/X ↦ s^n/c`) with `ι`. -/
theorem infSubst_compat {E E' : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [Field E'] [Algebra (RatFunc ℚ) E'] [Algebra ℚ[X] E']
    [IsScalarTower ℚ[X] (RatFunc ℚ) E'] (ι : E →+* E') (c : ℚ) (n : ℕ) (hc : c ≠ 0)
    (hshape : KummerShape E E' ι (rInf c n)) :
    letI := infAlg E
    ∀ x : InfCoord, algebraMap ℚ[X] E'
      ((Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n) : ℚ[X] →+* ℚ[X]) x) =
        ι (algebraMap InfCoord E x) := by
  letI := infAlg E
  let σ0 : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n)
  have hσX : σ0 X = C c⁻¹ * X ^ n := by simp [σ0]
  have : ((algebraMap ℚ[X] E').comp σ0 : ℚ[X] →+* E') =
      (ι.comp (algebraMap InfCoord E) : ℚ[X] →+* E') := by
    apply Polynomial.ringHom_ext
    · intro a
      have := RingHom.ext_rat (((algebraMap ℚ[X] E').comp σ0).comp C)
        (((ι.comp (algebraMap InfCoord E) : ℚ[X] →+* E')).comp C)
      exact congrArg (fun g => g a) this
    · simp only [RingHom.comp_apply]
      rw [hσX]
      change algebraMap ℚ[X] E' (C c⁻¹ * X ^ n) =
        ι (algebraMap (RatFunc ℚ) E (eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X⁻¹ X))
      rw [eval₂_X, map_inv₀ (algebraMap (RatFunc ℚ) E), map_inv₀ ι, hshape.1,
        ← map_inv₀ (algebraMap (RatFunc ℚ) E'),
        IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E']
      congr 1
      have hCc : algebraMap ℚ[X] (RatFunc ℚ) (C c) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (C_ne_zero.mpr hc)
      rw [rInf, inv_div, eq_div_iff hCc, ← map_mul]
      congr 1
      have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
      linear_combination (X ^ n) * h1
  intro x
  exact congrArg (fun g => g x) this

/-- **`KummerOtherBranchInf` from `UnramCompositum`.** -/
theorem kummerOtherBranchInf_of_unram (hU : UnramCompositum) : KummerOtherBranchInf := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι c n hn hc hshape S hE Q' hQ'p hQ'e
  classical
  letI := infAlg E
  letI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
  letI : IsDedekindDomain InfCoord := inferInstanceAs (IsDedekindDomain ℚ[X])
  letI : Algebra ℚ InfCoord := inferInstanceAs (Algebra ℚ ℚ[X])
  haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
  haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq' rfl
  let σ0 : ℚ[X] →+* ℚ[X] := Polynomial.eval₂RingHom C (C c⁻¹ * X ^ n)
  let σ : InfCoord →+* ℚ[X] := σ0
  have hσC : ∀ a : ℚ, σ0 (C a) = C a := fun a => by simp [σ0]
  have hσX : σ0 X = C c⁻¹ * X ^ n := by simp [σ0]
  have hsn : σ0 (C c * X) = X ^ n := by
    rw [map_mul, hσC, hσX, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have hXint : σ0.IsIntegralElem X := by
    refine ⟨X ^ n - C (C c * X), Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hsn, sub_self]
  have hint : σ0.IsIntegral := isIntegral_of_X σ0 hσC hXint
  have hrdeg : 0 < (C c⁻¹ * X ^ n : ℚ[X]).natDegree := by
    rw [natDegree_C_mul_X_pow n _ (inv_ne_zero hc)]; exact hn
  have hσinj : Function.Injective σ0 := by
    rw [injective_iff_map_eq_zero]; intro f hf
    change f.comp (C c⁻¹ * X ^ n) = 0 at hf
    rw [comp_eq_zero_iff] at hf
    rcases hf with hf | ⟨_, hr'⟩
    · exact hf
    · exfalso
      have := congrArg natDegree hr'
      rw [natDegree_C] at this; omega
  have hσu : ∀ g' : Ideal ℚ[X], g'.IsPrime → X ∉ g' → σ infUnif ∉ g' := by
    intro g' hg'p hXg' hm
    change σ0 X ∈ g' at hm
    rw [hσX] at hm
    rcases hg'p.mem_or_mem hm with h1 | h1
    · exact hg'p.ne_top (Ideal.eq_top_of_isUnit_mem _ h1
        (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hc))))
    · exact hXg' (hg'p.mem_of_pow_mem n h1)
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hS'⟩ := hcon
  apply hQ'e
  set g := Q'.under ℚ[X] with hg_def
  haveI hgp : g.IsPrime := Ideal.IsPrime.under _ _
  have hQ'0 : Q' ≠ ⊥ := by rintro rfl; exact hQ'e (Ideal.ramificationIdx_bot_eq_one _)
  have hg0 : g ≠ ⊥ := Ideal.IsIntegral.under_ne_bot ℚ[X] hQ'0
  have hXg : X ∉ g := fun hX => hne (eq_span_X_of_mem g hX)
  set h := g.comap σ with hh_def
  haveI hhp : h.IsPrime := Ideal.IsPrime.comap σ
  have hh0 : h ≠ ⊥ := by
    letI : Algebra SrcPoly ℚ[X] := (σ0 : SrcPoly →+* ℚ[X]).toAlgebra
    haveI : Algebra.IsIntegral SrcPoly ℚ[X] := ⟨hint⟩
    exact Ideal.IsIntegral.under_ne_bot SrcPoly hg0
  have hu : infUnif ∉ h := hσu g hgp hXg
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap ℚ[X] E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨X, rfl⟩
  refine compositum_core0 hU InfCoord (RatFunc ℚ) E E' ℚ[X] ι σ
    (infSubst_compat ι c n hc hshape) (finite_of_isIntegral _ hint) hσinj (polyMap_injective E')
    h hh0 hadj ?_ ?_ Q' rfl
  · intro Q hQ hQu
    obtain ⟨QX, hQXp, heq, hb⟩ := infTransfer E h hu Q hQ hQu
    rw [← heq]
    apply hE QX hQXp
    intro b' hb' hQXb
    obtain ⟨hb'0, hmem⟩ := hb b' hQXb
    apply hS' b' hb' hb'0
    have hm : σ (toInf (C b' * X - 1)) ∈ g := hmem
    have e : (C b' * X ^ n - C c : ℚ[X]) = C c * σ (toInf (C b' * X - 1)) := by
      change _ = C c * σ0 (C b' * X - 1)
      rw [map_sub, map_mul, hσC, hσX, map_one]
      have h1 : C c * C c⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
      linear_combination (-(C b' * X ^ n)) * h1
    rw [e]; exact Ideal.mul_mem_left _ _ hm
  · intro g' hg'p hg'
    have hg'0 : g' ≠ ⊥ := by
      rintro rfl
      apply hh0
      rw [← hg']
      exact Ideal.comap_bot_of_injective σ hσinj
    have hXg' : X ∉ g' := by
      intro hX
      apply hu
      rw [← hg']
      have : σ0 X ∈ g' := by
        rw [hσX]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hX n hn)
      exact this
    have hder := derivative_notMem 0 c n hn hc g' hXg'
    rw [C_0, zero_add] at hder
    exact polyUnram _ hrdeg hint g' hg'0 hder

/-- **Unramified base change (DVR form), proved.** `R`, `T` discrete valuation rings with fraction
fields `K`, `K'`; `σ : R → T` any ring map; `L/K` finite separable; `M` a field generated by `ι(L)`
and `K'`, compatibly with `σ` on `R`. If the integral closure of `R` in `L` is unramified over the
maximal ideal of `R` (with separable residue fields), then every prime of the integral closure of
`T` in `M` over the maximal ideal of `T` has ramification index `1`. (Same proof as
`unramCompositum`, with `T ⊗_R B` in place of `B ⊗_R B'`.) -/
theorem unramBaseChange (R K L M T K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K'] [Algebra T K'] [IsFractionRing T K'] [Algebra K' M] [Algebra T M]
    [IsScalarTower T K' M]
    (ι : L →+* M) (σ : R →+* T) (hσ : ∀ x, algebraMap T M (σ x) = ι (algebraMap R L x))
    (hadj : letI := ι.toAlgebra; IntermediateField.adjoin L (Set.range (algebraMap K' M)) = ⊤)
    (hL : ∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      Q.ramificationIdx R = 1 ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q))
    (Q : Ideal (integralClosure T M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal T)] :
    Q.ramificationIdx T = 1 ∧
      Algebra.IsSeparable (T ⧸ maximalIdeal T) (integralClosure T M ⧸ Q) := by
  classical
  letI : Algebra R T := σ.toAlgebra
  letI : Algebra L M := ι.toAlgebra
  letI : Algebra R M := ((algebraMap T M).comp σ).toAlgebra
  haveI : IsScalarTower R T M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq (fun x => hσ x)
  set B := integralClosure R L
  haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
  haveI hfB : Algebra.FormallyUnramified R B := fu_of_unram R K L hL
  let fB : B →ₐ[R] M := (IsScalarTower.toAlgHom R L M).comp (integralClosure R L).val
  let φ : T ⊗[R] B →ₐ[T] M :=
    Algebra.TensorProduct.lift (Algebra.ofId T M) fB (fun _ _ => Commute.all _ _)
  set D : Subalgebra T M := φ.range
  haveI : Algebra.FormallyUnramified T (T ⊗[R] B) := inferInstance
  haveI hfD : Algebra.FormallyUnramified T D :=
    Algebra.FormallyUnramified.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Module.Finite T (T ⊗[R] B) := inferInstance
  haveI hDfin : Module.Finite T D :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hTK : Function.Injective (algebraMap T K') := IsFractionRing.injective T K'
  have hTM : Function.Injective (algebraMap T M) := by
    rw [IsScalarTower.algebraMap_eq T K' M]; exact (algebraMap K' M).injective.comp hTK
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R L M, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap L M).injective.comp ((algebraMap K L).injective.comp hRK)
  have hDinj : Function.Injective (algebraMap D M) := Subtype.val_injective
  have hTD : Function.Injective (algebraMap T D) := by
    intro x y hxy
    apply hTM
    have := congrArg Subtype.val hxy
    simpa using this
  have hfBD : ∀ b : B, fB b ∈ D := fun b => ⟨1 ⊗ₜ b, by simp [φ]⟩
  have hRD : ∀ r : R, algebraMap R M r ∈ D := fun r => by
    rw [IsScalarTower.algebraMap_apply R T M]; exact D.algebraMap_mem _
  -- the fraction field of `D` is `M`
  let F : Subfield M := (IsFractionRing.lift (K := FractionRing D) hDinj).fieldRange
  have hDF : ∀ x ∈ D, x ∈ F := fun x hx =>
    ⟨algebraMap D (FractionRing D) ⟨x, hx⟩, IsFractionRing.lift_algebraMap _ _⟩
  have hLF : ∀ l : L, algebraMap L M l ∈ F := by
    intro l
    have halg : IsAlgebraic R l :=
      (IsFractionRing.isAlgebraic_iff R K L).mpr (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
    let b : B := ⟨y • l, hyint⟩
    have hy : algebraMap R M y ≠ 0 := (map_ne_zero_iff _ hRM).mpr hy0
    have e : algebraMap L M l = fB b / algebraMap R M y := by
      rw [eq_div_iff hy]
      change _ = algebraMap L M (y • l)
      rw [Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply R L M]
    rw [e]
    exact div_mem (hDF _ (hfBD b)) (hDF _ (hRD y))
  have hK'F : ∀ k : K', algebraMap K' M k ∈ F := by
    intro k
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := T) k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact div_mem (hDF _ (D.algebraMap_mem x)) (hDF _ (D.algebraMap_mem y))
  have hFtop : F = ⊤ := by
    have h1 := congrArg IntermediateField.toSubfield hadj
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h1
    rw [eq_top_iff, ← h1, Subfield.closure_le]
    rintro _ (⟨l, rfl⟩ | ⟨k, rfl⟩)
    · exact hLF l
    · exact hK'F k
  haveI hFrac : IsFractionRing D M := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro z
      have hz : z ∈ F := hFtop ▸ Subfield.mem_top z
      obtain ⟨w, rfl⟩ := hz
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := D) w
      refine ⟨⟨x, ⟨y, hy⟩⟩, ?_⟩
      simp only [map_div₀, IsFractionRing.lift_algebraMap]
      exact div_mul_cancel₀ _ ((map_ne_zero_iff _ hDinj).mpr (nonZeroDivisors.ne_zero hy))
    · intro x y hxy
      exact ⟨1, by simp [hDinj hxy]⟩
  -- `D` is integrally closed
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing T D
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmaxT : maximalIdeal T = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI hDic : IsIntegrallyClosed D := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P hP0 hPmax
    have hPu : P.under T = maximalIdeal T := IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under T P)
    set Dp := Localization.AtPrime P
    haveI : IsLocalHom (algebraMap T Dp) := by
      constructor
      intro r hr
      by_contra hnu
      have hrm : r ∈ maximalIdeal T := hnu
      rw [← hPu] at hrm
      have : algebraMap D Dp (algebraMap T D r) ∈ maximalIdeal Dp := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hrm
      rw [← IsScalarTower.algebraMap_apply] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hr
    haveI : Algebra.FormallyUnramified D Dp :=
      Algebra.FormallyUnramified.of_isLocalization (M := P.primeCompl)
    haveI : Algebra.FormallyUnramified T Dp := Algebra.FormallyUnramified.comp T D Dp
    haveI : Algebra.EssFiniteType D Dp := Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType T Dp := Algebra.EssFiniteType.comp T D Dp
    have hmaxDp : maximalIdeal Dp = Ideal.span {algebraMap T Dp ϖ} := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := T) (S := Dp), hmaxT, Ideal.map_span,
        Set.image_singleton]
    have hTDp : Function.Injective (algebraMap T Dp) := by
      rw [IsScalarTower.algebraMap_eq T D Dp]
      exact (IsLocalization.injective Dp P.primeCompl_le_nonZeroDivisors).comp hTD
    have hnf : ¬ IsField Dp := by
      intro hF
      have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
      rw [hmaxDp, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ hTDp] at this
      exact hϖ.ne_zero this
    have hprin : (maximalIdeal Dp).IsPrincipal := ⟨⟨_, hmaxDp⟩⟩
    haveI : IsDiscreteValuationRing Dp :=
      ((IsDiscreteValuationRing.TFAE Dp hnf).out 1 5).mpr hprin
    infer_instance
  -- `D` is the integral closure of `T` in `M`
  have hDC : D = integralClosure T M := by
    apply le_antisymm
    · intro x hx
      exact (Algebra.IsIntegral.isIntegral (R := T) (⟨x, hx⟩ : D)).map (IsScalarTower.toAlgHom T D M)
    · intro x hx
      have hxD : IsIntegral D x := IsIntegral.tower_top hx
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := D) (K := M)).mp hxD
      exact y.2
  let eDC : D ≃ₐ[T] integralClosure T M := Subalgebra.equivOfEq D _ hDC
  haveI : Algebra.FormallyUnramified T (integralClosure T M) :=
    Algebra.FormallyUnramified.of_equiv eDC
  haveI : Module.Finite T (integralClosure T M) := Module.Finite.equiv eDC.toLinearEquiv
  haveI : Algebra.IsUnramifiedAt T Q :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance ⟨Q, inferInstance⟩
  refine ⟨Ideal.ramificationIdx_eq_one Q T, ?_⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := T) Q
    (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal T)]; infer_instance)
  letI := Localization.AtPrime.algebraOfLiesOver (maximalIdeal T) Q
  have hsep := ((Algebra.isUnramifiedAt_iff_map_eq T (maximalIdeal T) Q).mp inferInstance).1
  exact Algebra.isSeparable_residueField_iff.mp hsep

theorem mem_vertPrime_iff (p : ℕ) (f : ℤ[X]) :
    f ∈ vertPrime p ↔ f.map (Int.castRingHom (ZMod p)) = 0 := by
  rw [vertPrime, Ideal.mem_map_C_iff]
  constructor
  · intro h
    ext k
    rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Ideal.mem_span_singleton.mp (h k)
  · intro h k
    have := congrArg (fun g => g.coeff k) h
    simp only [coeff_map, coeff_zero, eq_intCast] at this
    exact Ideal.mem_span_singleton.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this)

theorem C_mem_vertPrime (p : ℕ) (m : ℤ) : C m ∈ vertPrime p ↔ (p : ℤ) ∣ m := by
  rw [mem_vertPrime_iff, Polynomial.map_C, C_eq_zero, eq_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem not_dvd_num_of_val_zero (p : ℕ) [hp : Fact p.Prime] (c : ℚ) (hc : c ≠ 0)
    (h : padicValRat p c = 0) : ¬ (p : ℤ) ∣ c.num := by
  intro hd
  have h1 : padicValNat p c.den = 0 :=
    padicValNat.eq_zero_of_not_dvd (not_dvd_den_of_nonneg p c (by rw [h]))
  have h2 : 1 ≤ padicValInt p c.num := by
    rcases (padicValInt_dvd_iff 1 c.num).mp (by simpa using hd) with h0 | h0
    · exact absurd h0 (Rat.num_ne_zero.mpr hc)
    · exact h0
  rw [padicValRat_def, h1] at h
  omega

/-- `ℤ[X]_(p)` is a discrete valuation ring. -/
theorem zxLoc_dvr (p : ℕ) (hp : p.Prime) :
    haveI := vertPrime_isPrime p hp
    IsDiscreteValuationRing (Localization.AtPrime (vertPrime p)) := by
  haveI := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p with h𝔭
  have hCp0 : algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ)) ≠ 0 := by
    intro h0
    have := IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
      (h0.trans (map_zero _).symm)
    rw [C_eq_zero] at this
    exact hp.ne_zero (by exact_mod_cast this)
  have h3 : 𝔭 = Ideal.span {C (p : ℤ)} := by
    rw [h𝔭, vertPrime, Ideal.map_span, Set.image_singleton]
  have hmax : maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap ℤ[X] (Localization.AtPrime 𝔭) (C (p : ℤ))} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine (congrArg (Ideal.map (algebraMap ℤ[X] (Localization.AtPrime 𝔭))) h3).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime 𝔭) := by
    intro hF
    have := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    rw [hmax, Ideal.span_singleton_eq_bot] at this
    exact hCp0 this
  have hprin : (maximalIdeal (Localization.AtPrime 𝔭)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔭) hnf).out 1 5).mpr hprin

/-- A localization-compatible lift: `ℤ[X] → R` with every `f ∉ (p)` sent to a unit extends to
`ℤ[X]_(p)`; the image of a substitution is computed through `ℚ(X)`. Generic unit criterion:
if `g(β) · s^d = (image of F)` with `s` a unit and `F ∉ (p)`, then `g(β)` is a unit. -/
theorem unit_of_scaleRoots (p : ℕ) (hp : p.Prime) (N : ℤ[X]) (s : ℤ) (hs : ¬ (p : ℤ) ∣ s)
    (hN : 0 < (N.map (Int.castRingHom (ZMod p))).natDegree) :
    haveI := vertPrime_isPrime p hp
    ∀ (β : Localization.AtPrime (vertPrime p)),
      (s : Localization.AtPrime (vertPrime p)) * β =
        algebraMap ℤ[X] (Localization.AtPrime (vertPrime p)) N →
      ∀ f : ℤ[X], f ∉ vertPrime p →
        IsUnit (Polynomial.eval₂ (Int.castRingHom _) β f) := by
  haveI := vertPrime_isPrime p hp
  haveI : Fact p.Prime := ⟨hp⟩
  set 𝔭 := vertPrime p
  set Rz := Localization.AtPrime 𝔭
  intro β hβ f hf
  have hsu : IsUnit (s : Rz) := by
    have : IsUnit (algebraMap ℤ[X] Rz (C s)) :=
      IsLocalization.map_units Rz (⟨C s, (C_mem_vertPrime p s).not.mpr hs⟩ : 𝔭.primeCompl)
    simpa using this
  have key := Polynomial.scaleRoots_eval₂_mul (p := f) (Int.castRingHom Rz) β s
  rw [eq_intCast, hβ] at key
  have hcomp : eval₂ (Int.castRingHom Rz) (algebraMap ℤ[X] Rz N) (scaleRoots f s) =
      algebraMap ℤ[X] Rz ((scaleRoots f s).comp N) := by
    rw [Polynomial.comp, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  rw [hcomp] at key
  set F := (scaleRoots f s).comp N
  have hF : F ∉ 𝔭 := by
    rw [mem_vertPrime_iff, Polynomial.map_comp]
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · obtain ⟨k, hk⟩ : ∃ k, ¬ (p : ℤ) ∣ f.coeff k := by
        by_contra hcon
        push_neg at hcon
        exact hf ((mem_vertPrime_iff p f).mpr (by
          ext k; rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hcon k))
      have := congrArg (fun g => g.coeff k) h0
      simp only [coeff_map, coeff_scaleRoots, coeff_zero, map_mul, map_pow, eq_intCast] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1)
      · exact hs ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (pow_eq_zero_iff'.mp h1).1)
    · have := congrArg natDegree h0
      rw [natDegree_C] at this
      omega
  have hFu : IsUnit (algebraMap ℤ[X] Rz F) := IsLocalization.map_units Rz (⟨F, hF⟩ : 𝔭.primeCompl)
  rw [key] at hFu
  exact isUnit_of_mul_isUnit_right hFu

/-- Common setup of the vertical pieces: `Rz = ℤ[X]_(p)` and its maps. -/
theorem locAlg_tower (p : ℕ) (hp : p.Prime) (F : Type) [Field F] [Algebra (RatFunc ℚ) F]
    [Algebra ℚ[X] F] [IsScalarTower ℚ[X] (RatFunc ℚ) F] :
    haveI := vertPrime_isPrime p hp
    letI : Algebra (Localization.AtPrime (vertPrime p)) (RatFunc ℚ) :=
      locAlg (RatFunc ℚ) (vertPrime p)
    letI : Algebra (Localization.AtPrime (vertPrime p)) F := locAlg F (vertPrime p)
    IsScalarTower (Localization.AtPrime (vertPrime p)) (RatFunc ℚ) F := by
  haveI := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p
  letI : Algebra (Localization.AtPrime 𝔭) (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
  letI : Algebra (Localization.AtPrime 𝔭) F := locAlg F 𝔭
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext 𝔭.primeCompl
  rw [RingHom.comp_assoc]
  change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)) =
    (algebraMap (RatFunc ℚ) F).comp
      ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime 𝔭)))
  rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
  simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

/-- Localization transfer, downwards, for any localization `Rp` of `R0` at `p`. -/
theorem locTransfer_down' (R0 Rp F : Type) [CommRing R0] [IsDomain R0] [Field F] [Algebra R0 F]
    (p : Ideal R0) [p.IsPrime] [CommRing Rp] [Algebra R0 Rp] [IsLocalization.AtPrime Rp p]
    [IsLocalRing Rp] [Algebra Rp F] [IsScalarTower R0 Rp F]
    (hinj : Function.Injective (algebraMap R0 F))
    (Q : Ideal (integralClosure Rp F)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rp)] :
    letI := (intClIncl R0 Rp F).toAlgebra
    ∃ P0 : Ideal (integralClosure R0 F), P0.IsPrime ∧ P0.under R0 = p ∧
      Q.ramificationIdx Rp = P0.ramificationIdx R0 := by
  have hP : ∀ x ∈ p.primeCompl, algebraMap R0 F x ≠ 0 := fun x hx h0 =>
    hx (by rw [hinj (h0.trans (map_zero _).symm)]; exact p.zero_mem)
  obtain ⟨h1, h2, h3⟩ := intCl_isLocalization R0 Rp F p.primeCompl hP
  letI := (intClIncl R0 Rp F).toAlgebra
  set P0 := Q.comap (algebraMap (integralClosure R0 F) (integralClosure Rp F))
  haveI : P0.LiesOver p := IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rp Q
  haveI : P0.IsPrime := Ideal.IsPrime.comap _
  have hQ : Q = P0.map (algebraMap (integralClosure R0 F) (integralClosure Rp F)) :=
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure R0 F) p.primeCompl)
      (integralClosure Rp F) Q).symm
  refine ⟨P0, inferInstance, (Ideal.LiesOver.over (P := P0) (p := p)).symm, ?_⟩
  rw [hQ]
  exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rp _ P0

/-- `E` with `[E : ℚ(X)] < p` and no vertical ramification at `p` is unramified, with separable
residue fields, over (any copy `Rz` of) `ℤ[X]_(p)`. -/
theorem vertical_hL (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (hdeg : Module.finrank (RatFunc ℚ) E < p) (hV : NoVerticalRam E p)
    (Rz : Type) [CommRing Rz] [IsDomain Rz] [IsDiscreteValuationRing Rz] [Algebra ℤ[X] Rz]
    [hloc : @IsLocalization.AtPrime ℤ[X] _ Rz _ _ (vertPrime p) (vertPrime_isPrime p hp)]
    [Algebra Rz (RatFunc ℚ)] [IsFractionRing Rz (RatFunc ℚ)] [Algebra Rz E]
    [IsScalarTower Rz (RatFunc ℚ) E]
    (htow : ∀ f : ℤ[X], algebraMap Rz E (algebraMap ℤ[X] Rz f) = zxMap E f) :
    ∀ (Q : Ideal (integralClosure Rz E)) [Q.IsPrime] [Q.LiesOver (maximalIdeal Rz)],
      Q.ramificationIdx Rz = 1 ∧
      Algebra.IsSeparable (Rz ⧸ maximalIdeal Rz) (integralClosure Rz E ⧸ Q) := by
  intro Q hQp hQl
  haveI := vertPrime_isPrime p hp
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra ℤ[X] E := intPolyAlg E
  haveI : IsScalarTower ℤ[X] Rz E := IsScalarTower.of_algebraMap_eq (fun f => (htow f).symm)
  obtain ⟨P0, hP0, hP0u, he⟩ := locTransfer_down' ℤ[X] Rz E (vertPrime p) (zxMap_injective E) Q
  refine ⟨he.trans (hV P0 hP0 hP0u), ?_⟩
  haveI : IsFractionRing (integralClosure Rz E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc ℚ) E
  haveI : Module.Finite Rz (integralClosure Rz E) :=
    IsIntegralClosure.finite Rz (RatFunc ℚ) E (integralClosure Rz E)
  haveI hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Rz) Q
    (by rw [← Ideal.LiesOver.over (P := Q) (p := maximalIdeal Rz)]; infer_instance)
  have hmax0 : maximalIdeal Rz ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  haveI : Algebra.IsSeparable (RatFunc ℚ) E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsDedekindDomain (integralClosure Rz E) := integralClosure.isDedekindDomain Rz (RatFunc ℚ) E
  have hRzE : Function.Injective (algebraMap Rz (integralClosure Rz E)) := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    change algebraMap Rz E x = algebraMap Rz E y at h1
    rw [IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E] at h1
    exact IsFractionRing.injective Rz (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h1)
  haveI : NoZeroSMulDivisors Rz (integralClosure Rz E) := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl (hRzE (h1.trans (map_zero _).symm))
    · exact Or.inr h1⟩
  have hf := Ideal.inertiaDeg_le_finrank (integralClosure Rz E) (RatFunc ℚ) E Q hmax0
  rw [Ideal.inertiaDeg'_algebraMap] at hf
  letI : Field (Rz ⧸ maximalIdeal Rz) := Ideal.Quotient.field _
  letI : Field (integralClosure Rz E ⧸ Q) := Ideal.Quotient.field _
  haveI : CharP (Rz ⧸ maximalIdeal Rz) p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have hpm : algebraMap ℤ[X] Rz (C (p : ℤ)) ∈ maximalIdeal Rz := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (vertPrime p) Rz]
      exact Ideal.mem_map_of_mem _ ((C_mem_vertPrime p p).mpr dvd_rfl)
    have : ((p : ℕ) : Rz) = algebraMap ℤ[X] Rz (C (p : ℤ)) := by simp
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal Rz)), this, Ideal.Quotient.eq_zero_iff_mem]
    exact hpm
  exact isSeparable_of_finrank_lt p (lt_of_le_of_lt hf hdeg)

/-- **`KummerVerticalFin` is proved** (unramified base change along `ℤ[X]_(p) → ℤ[s]_(p)`,
`X ↦ b + s^n/c`). -/
theorem kummerVerticalFin_proof : KummerVerticalFin := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι b c n p hp hn hnp hdeg hc hcp hbp hshape hV
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI h𝔭p := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p with h𝔭
  set Rz := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing Rz := zxLoc_dvr p hp
  letI iK : Algebra Rz (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
  letI iE : Algebra Rz E := locAlg E 𝔭
  letI iE' : Algebra Rz E' := locAlg E' 𝔭
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  haveI : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  haveI : IsScalarTower ℤ[X] Rz (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  haveI : IsFractionRing Rz (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ _
  haveI : IsScalarTower Rz (RatFunc ℚ) E := locAlg_tower p hp E
  haveI : IsScalarTower Rz (RatFunc ℚ) E' := locAlg_tower p hp E'
  -- numerators and denominators of `b`, `c`
  have hbd : ¬ (p : ℤ) ∣ (b.den : ℤ) := by
    have := not_dvd_den_of_nonneg p b hbp
    exact_mod_cast this
  have hcd : ¬ (p : ℤ) ∣ (c.den : ℤ) := by
    have := not_dvd_den_of_nonneg p c (by rw [hcp])
    exact_mod_cast this
  have hcn : ¬ (p : ℤ) ∣ c.num := not_dvd_num_of_val_zero p c hc hcp
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨s, hs_def⟩ : ∃ s : ℤ, s = (b.den : ℤ) * c.num := ⟨_, rfl⟩
  have hs : ¬ (p : ℤ) ∣ s := fun h => (hpz.dvd_or_dvd (hs_def ▸ h)).elim hbd hcn
  obtain ⟨N, hN_def⟩ : ∃ N : ℤ[X], N = C (b.num * c.num) + C ((b.den : ℤ) * c.den) * X ^ n :=
    ⟨_, rfl⟩
  have hN : 0 < (N.map (Int.castRingHom (ZMod p))).natDegree := by
    have h1 : (Int.castRingHom (ZMod p)) ((b.den : ℤ) * c.den) ≠ 0 := by
      rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact fun h => (hpz.dvd_or_dvd h).elim hbd hcd
    rw [hN_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, natDegree_C_add, natDegree_C_mul_X_pow n _ h1]
    exact hn
  have hCs : C s ∉ 𝔭 := (C_mem_vertPrime p s).not.mpr hs
  set β : Rz := IsLocalization.mk' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl) with hβ_def
  have hβ : (s : Rz) * β = algebraMap ℤ[X] Rz N := by
    have := IsLocalization.mk'_spec' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl)
    rw [← this]
    congr 1
    change (s : Rz) = algebraMap ℤ[X] Rz (C s)
    have e : (C s : ℤ[X]) = (s : ℤ[X]) := by simp
    rw [e, map_intCast]
  let σ0 : ℤ[X] →+* Rz := Polynomial.eval₂RingHom (Int.castRingHom Rz) β
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (σ0 y) := fun y =>
    unit_of_scaleRoots p hp N s hs hN β hβ y.1 y.2
  let σ : Rz →+* Rz := IsLocalization.lift (M := 𝔭.primeCompl) (S := Rz) (g := σ0) hunit
  have hσ0 : ∀ f : ℤ[X], σ (algebraMap ℤ[X] Rz f) = σ0 f := fun f => IsLocalization.lift_eq hunit f
  -- the image of `β` in `ℚ(X)` is `rFin b c n`
  have hs0 : (s : ℚ) ≠ 0 := by
    intro h0
    exact hs (by rw [show s = 0 by exact_mod_cast h0]; exact dvd_zero _)
  have e1 : (s : ℚ) * (b * c) = c * (b.num * c.num) := by
    have hb := Rat.mul_den_eq_num b
    rw [hs_def]; push_cast
    rw [← hb]; ring
  have e2 : (s : ℚ) = c * (b.den * c.den) := by
    have hc' := Rat.mul_den_eq_num c
    rw [hs_def]; push_cast
    rw [← hc']; ring
  have hpoly : C (s : ℚ) * (C (b * c) + X ^ n) = C c * N.map (Int.castRingHom ℚ) := by
    have hNm : N.map (Int.castRingHom ℚ) = C ((b.num * c.num : ℤ) : ℚ) +
        C (((b.den : ℤ) * c.den : ℤ) : ℚ) * X ^ n := by
      rw [hN_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, eq_intCast, eq_intCast]
    have e1' : (s : ℚ) * b * c = c * ((b.num * c.num : ℤ) : ℚ) := by
      rw [mul_assoc]; push_cast; exact e1
    have e2' : (s : ℚ) = c * (((b.den : ℤ) * c.den : ℤ) : ℚ) := by push_cast; exact e2
    rw [hNm]
    simp only [mul_add, ← mul_assoc, ← C_mul]
    rw [e1', ← e2']
  have hβK : algebraMap Rz (RatFunc ℚ) β = rFin b c n := by
    have h1 := congrArg (algebraMap Rz (RatFunc ℚ)) hβ
    rw [map_mul, map_intCast, ← IsScalarTower.algebraMap_apply] at h1
    have h2 := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hpoly
    simp only [map_mul] at h2
    have hsK : algebraMap ℚ[X] (RatFunc ℚ) (C (s : ℚ)) = (s : RatFunc ℚ) := by
      rw [RatFunc.algebraMap_C, map_intCast]
    have hCc : algebraMap ℚ[X] (RatFunc ℚ) (C c) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (C_ne_zero.mpr hc)
    have hsK0 : (s : RatFunc ℚ) ≠ 0 := by
      rw [← hsK]
      exact (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (C_ne_zero.mpr hs0)
    have h3 : algebraMap ℤ[X] (RatFunc ℚ) N = algebraMap ℚ[X] (RatFunc ℚ)
        (N.map (Int.castRingHom ℚ)) := rfl
    apply mul_left_cancel₀ hsK0
    rw [h1, h3, rFin, ← mul_div_assoc, eq_div_iff hCc, mul_comm _ (algebraMap ℚ[X] _ (C c)),
      ← h2, hsK, ← C_mul, add_comm]
  -- compatibility with `ι`
  have hσ : ∀ x, algebraMap Rz E' (σ x) = ι (algebraMap Rz E x) := by
    have : (algebraMap Rz E').comp σ = ι.comp (algebraMap Rz E) := by
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_int
          ((((algebraMap Rz E').comp σ).comp (algebraMap ℤ[X] Rz)).comp C)
          (((ι.comp (algebraMap Rz E)).comp (algebraMap ℤ[X] Rz)).comp C)) a
      · simp only [RingHom.comp_apply]
        rw [hσ0]
        change algebraMap Rz E' (eval₂ (Int.castRingHom Rz) β X) =
          ι (IsLocalization.lift _ (algebraMap ℤ[X] Rz X))
        rw [eval₂_X, IsLocalization.lift_eq, IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E', hβK]
        change _ = ι (algebraMap ℚ[X] E (X.map (Int.castRingHom ℚ)))
        rw [Polynomial.map_X, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
          RatFunc.algebraMap_X, hshape.1]
    intro x
    exact RingHom.congr_fun this x
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap (RatFunc ℚ) E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨algebraMap ℚ[X] (RatFunc ℚ) X, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
  -- conclusion
  letI : Algebra ℤ[X] E' := intPolyAlg E'
  haveI : IsScalarTower ℤ[X] Rz E' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  intro Q' hQ'p hQ'u
  haveI : Q'.LiesOver 𝔭 := ⟨hQ'u.symm⟩
  obtain ⟨Qp, hQp, hQpl, hQpe⟩ := locTransfer_up ℤ[X] E' 𝔭 (zxMap_injective E') Q'
  rw [← hQpe]
  exact (unramBaseChange Rz (RatFunc ℚ) E E' Rz (RatFunc ℚ) ι σ hσ hadj
    (vertical_hL E p hp hdeg hV Rz (fun f => IsLocalization.lift_eq _ f)) Qp).1
/-- **`KummerVerticalInf` is proved** (unramified base change along `ℤ[X]_(p) → ℤ[s]_(p)`,
`X ↦ c/s^n`). -/
theorem kummerVerticalInf_proof : KummerVerticalInf := by
  intro E _ _ _ _ _ E' _ _ _ _ _ ι c n p hp hn hnp hdeg hc hcp hshape hV
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI h𝔭p := vertPrime_isPrime p hp
  set 𝔭 := vertPrime p with h𝔭
  set Rz := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing Rz := zxLoc_dvr p hp
  letI iK : Algebra Rz (RatFunc ℚ) := locAlg (RatFunc ℚ) 𝔭
  letI iE : Algebra Rz E := locAlg E 𝔭
  letI iE' : Algebra Rz E' := locAlg E' 𝔭
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  haveI : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  haveI : IsScalarTower ℤ[X] Rz (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  haveI : IsFractionRing Rz (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl _ _
  haveI : IsScalarTower Rz (RatFunc ℚ) E := locAlg_tower p hp E
  haveI : IsScalarTower Rz (RatFunc ℚ) E' := locAlg_tower p hp E'
  -- numerator and denominator of `c`
  have hcd : ¬ (p : ℤ) ∣ (c.den : ℤ) := by
    have := not_dvd_den_of_nonneg p c (by rw [hcp])
    exact_mod_cast this
  have hcn : ¬ (p : ℤ) ∣ c.num := not_dvd_num_of_val_zero p c hc hcp
  obtain ⟨s, hs_def⟩ : ∃ s : ℤ, s = c.num := ⟨_, rfl⟩
  have hs : ¬ (p : ℤ) ∣ s := hs_def ▸ hcn
  obtain ⟨N, hN_def⟩ : ∃ N : ℤ[X], N = C (c.den : ℤ) * X ^ n := ⟨_, rfl⟩
  have h1 : (Int.castRingHom (ZMod p)) (c.den : ℤ) ≠ 0 := by
    rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcd
  have hNmap : N.map (Int.castRingHom (ZMod p)) =
      C ((Int.castRingHom (ZMod p)) (c.den : ℤ)) * X ^ n := by
    rw [hN_def, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  have hN : 0 < (N.map (Int.castRingHom (ZMod p))).natDegree := by
    rw [hNmap, natDegree_C_mul_X_pow n _ h1]
    exact hn
  have hN𝔭 : N ∉ 𝔭 := by
    rw [mem_vertPrime_iff, hNmap]
    exact mul_ne_zero (C_ne_zero.mpr h1) (pow_ne_zero _ X_ne_zero)
  have hCs : C s ∉ 𝔭 := (C_mem_vertPrime p s).not.mpr hs
  -- `β' = s^n/c` and `β = c/s^n`
  set β' : Rz := IsLocalization.mk' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl) with hβ'_def
  have hβ' : (s : Rz) * β' = algebraMap ℤ[X] Rz N := by
    have := IsLocalization.mk'_spec' Rz N (⟨C s, hCs⟩ : 𝔭.primeCompl)
    rw [← this]
    congr 1
    change (s : Rz) = algebraMap ℤ[X] Rz (C s)
    have e : (C s : ℤ[X]) = (s : ℤ[X]) := by simp
    rw [e, map_intCast]
  set β : Rz := IsLocalization.mk' Rz (C s) (⟨N, hN𝔭⟩ : 𝔭.primeCompl) with hβ_def
  have hββ' : β * β' = 1 :=
    IsLocalization.mk'_mul_mk'_eq_one (⟨C s, hCs⟩ : 𝔭.primeCompl) (⟨N, hN𝔭⟩ : 𝔭.primeCompl)
  letI : Invertible β := ⟨β', by rw [mul_comm]; exact hββ', hββ'⟩
  have hβu : IsUnit β := isUnit_of_invertible β
  let σ0 : ℤ[X] →+* Rz := Polynomial.eval₂RingHom (Int.castRingHom Rz) β
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (σ0 y) := by
    intro y
    set f := (y : ℤ[X])
    have hf : f ∉ 𝔭 := y.2
    set d := f.natDegree
    have hrefl : reflect d f ∉ 𝔭 := by
      intro hm
      apply hf
      change reflect d f ∈ Ideal.map C (Ideal.span {(p : ℤ)}) at hm
      change f ∈ Ideal.map C (Ideal.span {(p : ℤ)})
      rw [Ideal.mem_map_C_iff] at hm ⊢
      intro k
      by_cases hk : k ≤ d
      · have := hm (revAt d k)
        rwa [coeff_reflect, revAt_invol] at this
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        exact Ideal.zero_mem _
    have h1 := unit_of_scaleRoots p hp N s hs hN β' hβ' (reflect d f) hrefl
    have h2 := eval₂_reflect_mul_pow (Int.castRingHom Rz) β d f le_rfl
    change IsUnit (eval₂ (Int.castRingHom Rz) β f)
    rw [← h2]
    refine IsUnit.mul ?_ (hβu.pow d)
    convert h1
  let σ : Rz →+* Rz := IsLocalization.lift (M := 𝔭.primeCompl) (S := Rz) (g := σ0) hunit
  have hσ0 : ∀ f : ℤ[X], σ (algebraMap ℤ[X] Rz f) = σ0 f := fun f => IsLocalization.lift_eq hunit f
  -- the image of `β` in `ℚ(X)` is `rInf c n`
  have hβK : algebraMap Rz (RatFunc ℚ) β = rInf c n := by
    have hspec := IsLocalization.mk'_spec' Rz (C s) (⟨N, hN𝔭⟩ : 𝔭.primeCompl)
    have h1 := congrArg (algebraMap Rz (RatFunc ℚ)) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
    change algebraMap ℤ[X] (RatFunc ℚ) N * algebraMap Rz (RatFunc ℚ) β =
      algebraMap ℤ[X] (RatFunc ℚ) (C s) at h1
    have hNK : algebraMap ℤ[X] (RatFunc ℚ) N = algebraMap ℚ[X] (RatFunc ℚ) (C (c.den : ℚ) * X ^ n) := by
      change algebraMap ℚ[X] (RatFunc ℚ) (N.map (Int.castRingHom ℚ)) = _
      rw [hN_def, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        eq_intCast, Int.cast_natCast]
    have hsK : algebraMap ℤ[X] (RatFunc ℚ) (C s) = algebraMap ℚ[X] (RatFunc ℚ) (C (c.num : ℚ)) := by
      change algebraMap ℚ[X] (RatFunc ℚ) ((C s).map (Int.castRingHom ℚ)) = _
      rw [Polynomial.map_C, eq_intCast, hs_def]
    have hN0 : algebraMap ℚ[X] (RatFunc ℚ) (C (c.den : ℚ) * X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
        (mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast c.den_nz)) (pow_ne_zero _ X_ne_zero))
    have hXn : algebraMap ℚ[X] (RatFunc ℚ) (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr (pow_ne_zero _ X_ne_zero)
    rw [hNK, hsK] at h1
    apply mul_left_cancel₀ hN0
    rw [h1, rInf, map_mul, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hXn, ← map_mul,
      ← C_mul, mul_comm ((c.den : ℚ)) c, Rat.mul_den_eq_num]
  -- compatibility with `ι`
  have hσ : ∀ x, algebraMap Rz E' (σ x) = ι (algebraMap Rz E x) := by
    have : (algebraMap Rz E').comp σ = ι.comp (algebraMap Rz E) := by
      apply IsLocalization.ringHom_ext 𝔭.primeCompl
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_int
          ((((algebraMap Rz E').comp σ).comp (algebraMap ℤ[X] Rz)).comp C)
          (((ι.comp (algebraMap Rz E)).comp (algebraMap ℤ[X] Rz)).comp C)) a
      · simp only [RingHom.comp_apply]
        rw [hσ0]
        change algebraMap Rz E' (eval₂ (Int.castRingHom Rz) β X) =
          ι (IsLocalization.lift _ (algebraMap ℤ[X] Rz X))
        rw [eval₂_X, IsLocalization.lift_eq, IsScalarTower.algebraMap_apply Rz (RatFunc ℚ) E', hβK]
        change _ = ι (algebraMap ℚ[X] E (X.map (Int.castRingHom ℚ)))
        rw [Polynomial.map_X, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
          RatFunc.algebraMap_X, hshape.1]
    intro x
    exact RingHom.congr_fun this x
  have hadj : letI := ι.toAlgebra
      IntermediateField.adjoin E (Set.range (algebraMap (RatFunc ℚ) E')) = ⊤ := by
    letI := ι.toAlgebra
    refine eq_top_iff.mpr ((adjoin_eq_top_of_shape ι _ hshape).symm.le.trans
      (IntermediateField.adjoin.mono _ _ _ ?_))
    rintro _ rfl
    exact ⟨algebraMap ℚ[X] (RatFunc ℚ) X, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
  -- conclusion
  letI : Algebra ℤ[X] E' := intPolyAlg E'
  haveI : IsScalarTower ℤ[X] Rz E' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  intro Q' hQ'p hQ'u
  haveI : Q'.LiesOver 𝔭 := ⟨hQ'u.symm⟩
  obtain ⟨Qp, hQp, hQpl, hQpe⟩ := locTransfer_up ℤ[X] E' 𝔭 (zxMap_injective E') Q'
  rw [← hQpe]
  exact (unramBaseChange Rz (RatFunc ℚ) E E' Rz (RatFunc ℚ) ι σ hσ hadj
    (vertical_hL E p hp hdeg hV Rz (fun f => IsLocalization.lift_eq _ f)) Qp).1
/-- Every element of `ℚ(X)` lies in the subfield generated by `X`. -/
theorem ratFunc_mem_closure (z : RatFunc ℚ) : z ∈ Subfield.closure {(RatFunc.X : RatFunc ℚ)} := by
  have hpoly : ∀ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f ∈
      Subfield.closure {(RatFunc.X : RatFunc ℚ)} := by
    intro f
    induction f using Polynomial.induction_on with
    | C a =>
      rw [RatFunc.algebraMap_C, eq_ratCast]
      exact SubfieldClass.ratCast_mem _ a
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial k a _ =>
      rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]
      exact mul_mem (by assumption) (Subfield.subset_closure rfl)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℚ[X]) z
  exact div_mem (hpoly a) (hpoly b)

/-- A non-constant rational function `P/Q` is transcendental over `ℚ`. -/
theorem ratFunc_transc (P Q : ℚ[X]) (hQ : Q ≠ 0) (hnc : ∀ a : ℚ, P ≠ C a * Q) (f : ℚ[X])
    (hf : aeval (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) f = 0) :
    f = 0 := by
  by_contra hf0
  set x := algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q
  have hxQ : IsIntegral ℚ x := (isAlgebraic_iff_isIntegral).mp ⟨f, hf0, hf⟩
  have hxP : IsIntegral ℚ[X] x := hxQ.tower_top
  obtain ⟨g, hg⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℚ[X]) (K := RatFunc ℚ)).mp hxP
  have h1 : aeval (algebraMap ℚ[X] (RatFunc ℚ) g) f = algebraMap ℚ[X] (RatFunc ℚ) (f.comp g) := by
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) g f
    rw [Polynomial.comp_eq_aeval]
    exact this
  rw [← hg, h1, map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ)), comp_eq_zero_iff] at hf
  rcases hf with hf | ⟨_, hgc⟩
  · exact hf0 hf
  · apply hnc (g.coeff 0)
    have hQK : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr hQ
    have h2 : x = algebraMap ℚ[X] (RatFunc ℚ) (C (g.coeff 0)) := by rw [← hg, ← hgc]
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    rw [map_mul, ← h2, div_mul_cancel₀ _ hQK]

/-- A copy of `FractionRing D` carrying no instances inherited from the algebra structures of
`D`. -/
def KSyn (D : Type) [CommRing D] [IsDomain D] : Type := FractionRing D

instance (D : Type) [CommRing D] [IsDomain D] : Field (KSyn D) :=
  inferInstanceAs (Field (FractionRing D))
instance (D : Type) [CommRing D] [IsDomain D] : Algebra D (KSyn D) :=
  inferInstanceAs (Algebra D (FractionRing D))
instance (D : Type) [CommRing D] [IsDomain D] : IsFractionRing D (KSyn D) :=
  inferInstanceAs (IsFractionRing D (FractionRing D))

/-- The identity `ℚ[X] → SrcPoly`. -/
def toSrc (f : ℚ[X]) : SrcPoly := f

/-- The construction behind `KummerCompositum`, from an abstract ring `D` (in the application
`D = (O ⊗_{ℚ[X]} B)/𝔫` for a minimal prime `𝔫`). -/
theorem kc_core (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (P Q : ℚ[X]) (s₀ : ℚ)
    (𝔓 : Ideal (integralClosure ℚ[X] E)) [h𝔓m : 𝔓.IsMaximal]
    (φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* AlgebraicClosure ℚ)
    (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra SrcPoly O]
    [hp0 : (Ideal.span {toSrc (X - C s₀)}).IsPrime]
    [IsLocalization.AtPrime O (Ideal.span {toSrc (X - C s₀)})]
    (ρ : ℚ[X] →+* O) (hρ : Function.Injective ρ)
    (oK : O →+* RatFunc ℚ)
    (hoK : ∀ a : SrcPoly, oK (algebraMap SrcPoly O a) = algebraMap ℚ[X] (RatFunc ℚ) a.toPoly)
    (hoKρX : oK (ρ X) = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q)
    (evO : O →+* ℚ) (hevO : ∀ o, evO o = 0 ↔ o ∈ maximalIdeal O)
    (hevS : ∀ a : SrcPoly, evO (algebraMap SrcPoly O a) = a.toPoly.eval s₀)
    (D : Type) [CommRing D] [IsDomain D] (iO : O →+* D) (hiO : Function.Injective iO)
    (iB : integralClosure ℚ[X] E →+* D)
    (hiB : ∀ c : ℚ[X], iB (algebraMap ℚ[X] (integralClosure ℚ[X] E) c) = iO (ρ c))
    (hgen : ∀ d : D, d ∈ Subring.closure (Set.range iO ∪ Set.range iB))
    (hint : iO.IsIntegral)
    (N' : Ideal D) [hN' : N'.IsPrime] (hN'O : N'.comap iO = maximalIdeal O)
    (hN'B : 𝔓 ≤ N'.comap iB) :
    ∃ (E' : Type) (_ : Field E') (_ : Algebra (RatFunc ℚ) E') (_ : Algebra ℚ[X] E')
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E') (_ : FiniteDimensional (RatFunc ℚ) E')
      (ι : E →+* E'),
      KummerShape E E' ι (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) ∧
      Module.finrank (RatFunc ℚ) E' ≤ Module.finrank (RatFunc ℚ) E ∧
      ∃ 𝔓' : Ideal (integralClosure ℚ[X] E'), 𝔓'.IsPrime ∧
        𝔓'.under ℚ[X] = Ideal.span {X - C s₀} ∧
        ∃ φ' : integralClosure ℚ[X] E' ⧸ 𝔓' →+* AlgebraicClosure ℚ,
          IntermediateField.adjoin ℚ (Set.range φ) ≤ IntermediateField.adjoin ℚ (Set.range φ') := by
  classical
  set p0 : Ideal SrcPoly := Ideal.span {toSrc (X - C s₀)} with hp0_def
  -- the maps into `E' = Frac D`
  let gO : O →+* KSyn D := (algebraMap D (KSyn D)).comp iO
  have hgO : Function.Injective gO := (IsFractionRing.injective D (KSyn D)).comp hiO
  let gS : ℚ[X] →+* KSyn D := gO.comp (algebraMap SrcPoly O)
  have hSO : Function.Injective (algebraMap SrcPoly O) :=
    IsLocalization.injective O p0.primeCompl_le_nonZeroDivisors
  have hgS : Function.Injective gS := fun a b h => hSO (hgO h)
  letI iK' : Algebra (RatFunc ℚ) (KSyn D) :=
    (IsFractionRing.lift (A := ℚ[X]) (K := RatFunc ℚ) hgS).toAlgebra
  letI iP : Algebra ℚ[X] (KSyn D) :=
    ((algebraMap (RatFunc ℚ) (KSyn D)).comp (algebraMap ℚ[X] (RatFunc ℚ))).toAlgebra
  haveI iT : IsScalarTower ℚ[X] (RatFunc ℚ) (KSyn D) := IsScalarTower.of_algebraMap_eq' rfl
  have hPS : ∀ a : ℚ[X], algebraMap ℚ[X] (KSyn D) a = gS a := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) (KSyn D)]
    exact IsFractionRing.lift_algebraMap hgS a
  have hKO : ∀ o, algebraMap (RatFunc ℚ) (KSyn D) (oK o) = gO o := by
    have : (algebraMap (RatFunc ℚ) (KSyn D)).comp oK = gO := by
      apply IsLocalization.ringHom_ext p0.primeCompl
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply]
      rw [hoK]
      exact IsFractionRing.lift_algebraMap hgS a
    intro o
    exact RingHom.congr_fun this o
  -- `ι : E → E'`
  let ιB : integralClosure ℚ[X] E →+* KSyn D := (algebraMap D (KSyn D)).comp iB
  have hιB : Function.Injective ιB := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have hne := Ideal.under_ne_bot_of_integral_mem (R := ℚ[X]) hb0
      (Ideal.mem_span_singleton_self b) (Algebra.IsIntegral.isIntegral b)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp hc
    have h1 : ιB (algebraMap ℚ[X] _ c) = 0 := by rw [← hb', map_mul, hb, mul_zero]
    change algebraMap D (KSyn D) (iB _) = 0 at h1
    rw [hiB] at h1
    exact hc0 (hρ (hgO (h1.trans (map_zero gO).symm) |>.trans (map_zero ρ).symm))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc ℚ) E
  let ι : E →+* KSyn D := IsFractionRing.lift hιB
  have hι : ∀ b, ι (algebraMap (integralClosure ℚ[X] E) E b) = ιB b :=
    fun b => IsFractionRing.lift_algebraMap hιB b
  have hιX : ι (algebraMap ℚ[X] E X) = gO (ρ X) := by
    rw [IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E, hι]
    change algebraMap D (KSyn D) (iB _) = _
    rw [hiB]
    rfl
  have hshape1 : ι (algebraMap (RatFunc ℚ) E RatFunc.X) = algebraMap (RatFunc ℚ) (KSyn D)
      (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) := by
    rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, hιX,
      ← hoKρX, hKO]
  -- the subfield generated by `ι(E)` and `s` is everything
  set F := Subfield.closure (Set.range ι ∪ {algebraMap (RatFunc ℚ) (KSyn D) RatFunc.X}) with hF
  have hK'F : ∀ z : RatFunc ℚ, algebraMap (RatFunc ℚ) (KSyn D) z ∈ F := by
    intro z
    have h1 : Subfield.closure {(RatFunc.X : RatFunc ℚ)} ≤ F.comap (algebraMap (RatFunc ℚ) (KSyn D)) := by
      rw [Subfield.closure_le]
      rintro _ rfl
      exact Subfield.subset_closure (Or.inr rfl)
    exact h1 (ratFunc_mem_closure z)
  have hDF : ∀ d : D, algebraMap D (KSyn D) d ∈ F := by
    intro d
    induction hgen d using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨o, rfl⟩ | ⟨b, rfl⟩
      · change gO o ∈ F
        rw [← hKO]; exact hK'F _
      · change ιB b ∈ F
        rw [← hι]; exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact one_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hFtop : F = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := D) z
    exact div_mem (hDF a) (hDF b)
  -- `κ : ℚ(X) → ℚ(s)`, `X ↦ P/Q`, compatible with `ι`
  have hκg : Function.Injective (oK.comp ρ) := by
    intro a b h
    apply hρ
    apply hgO
    rw [← hKO, ← hKO]
    exact congrArg (algebraMap (RatFunc ℚ) (KSyn D)) h
  let κ : RatFunc ℚ →+* RatFunc ℚ := IsFractionRing.lift (A := ℚ[X]) (K := RatFunc ℚ) hκg
  have hκ : ∀ k, algebraMap (RatFunc ℚ) (KSyn D) (κ k) = ι (algebraMap (RatFunc ℚ) E k) := by
    have : (algebraMap (RatFunc ℚ) (KSyn D)).comp κ = ι.comp (algebraMap (RatFunc ℚ) E) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
      apply RingHom.ext
      intro f
      simp only [RingHom.comp_apply]
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply, hKO,
        ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
        IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E, hι]
      change gO (ρ f) = algebraMap D (KSyn D) (iB _)
      rw [hiB]
      rfl
    intro k
    exact RingHom.congr_fun this k
  -- a primitive element
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (RatFunc ℚ) E
  have hθint : IsIntegral (RatFunc ℚ) θ := .of_finite _ _
  set m := minpoly (RatFunc ℚ) θ
  have hroot : aeval (ι θ) (m.map κ) = 0 := by
    rw [aeval_def, eval₂_map]
    have : (algebraMap (RatFunc ℚ) (KSyn D)).comp κ = ι.comp (algebraMap (RatFunc ℚ) E) :=
      RingHom.ext hκ
    rw [this, ← Polynomial.hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hmon : (m.map κ).Monic := (minpoly.monic hθint).map κ
  have hιθint : IsIntegral (RatFunc ℚ) (ι θ) := ⟨_, hmon, hroot⟩
  -- `E' = ℚ(s)(ι θ)`
  have hadjtop : IntermediateField.adjoin (RatFunc ℚ) {ι θ} = ⊤ := by
    set L' := IntermediateField.adjoin (RatFunc ℚ) {ι θ}
    have hrange : ∀ e : E, ι e ∈ L' := by
      intro e
      have hle : (IntermediateField.adjoin (RatFunc ℚ) {θ}).toSubfield ≤
          L'.toSubfield.comap ι := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro _ (⟨k, rfl⟩ | h)
        · change ι (algebraMap (RatFunc ℚ) E k) ∈ L'
          rw [← hκ]; exact L'.algebraMap_mem _
        · rw [Set.mem_singleton_iff] at h
          subst h
          exact IntermediateField.mem_adjoin_simple_self _ _
      have he : e ∈ (IntermediateField.adjoin (RatFunc ℚ) {θ}).toSubfield := by
        rw [hθ]; trivial
      exact hle he
    have hFle : F ≤ L'.toSubfield := by
      rw [hF, Subfield.closure_le]
      rintro _ (⟨e, rfl⟩ | h)
      · exact hrange e
      · rw [Set.mem_singleton_iff] at h
        rw [h]; exact L'.algebraMap_mem _
    rw [eq_top_iff]
    intro z _
    exact hFle (hFtop ▸ Subfield.mem_top z)
  haveI hfd : FiniteDimensional (RatFunc ℚ) (KSyn D) := by
    have h1 := IntermediateField.adjoin.finiteDimensional hιθint
    rw [hadjtop] at h1
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  have hfin : Module.finrank (RatFunc ℚ) (KSyn D) ≤ Module.finrank (RatFunc ℚ) E := by
    rw [← IntermediateField.finrank_top', ← hadjtop, IntermediateField.adjoin.finrank hιθint,
      ← IntermediateField.finrank_top' (F := RatFunc ℚ) (E := E), ← hθ,
      IntermediateField.adjoin.finrank hθint]
    calc (minpoly (RatFunc ℚ) (ι θ)).natDegree ≤ (m.map κ).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hmon.ne_zero
      _ = m.natDegree := natDegree_map κ
  -- the integral closure `C` of `O` in `E'` and a prime `𝔐` of `C` over `N'`
  letI iOE : Algebra O (KSyn D) := gO.toAlgebra
  letI iOD : Algebra O D := iO.toAlgebra
  haveI : IsScalarTower O D (KSyn D) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral O D := ⟨hint⟩
  let jD : D →ₐ[O] integralClosure O (KSyn D) :=
    (IsScalarTower.toAlgHom O D (KSyn D)).codRestrict (integralClosure O (KSyn D))
      (fun d => (Algebra.IsIntegral.isIntegral (R := O) d).map (IsScalarTower.toAlgHom O D (KSyn D)))
  have hjD : Function.Injective jD := by
    intro x y h
    exact IsFractionRing.injective D (KSyn D) (congrArg Subtype.val h)
  letI iDC : Algebra D (integralClosure O (KSyn D)) := jD.toRingHom.toAlgebra
  haveI : IsScalarTower O D (integralClosure O (KSyn D)) :=
    IsScalarTower.of_algebraMap_eq (fun o => (jD.commutes o).symm)
  haveI : Algebra.IsIntegral D (integralClosure O (KSyn D)) :=
    Algebra.IsIntegral.tower_top O
  have hkerD : (⊥ : Ideal (integralClosure O (KSyn D))).under D ≤ N' := by
    intro x hx
    have : jD x = 0 := hx
    rw [hjD (this.trans (map_zero jD).symm)]
    exact N'.zero_mem
  obtain ⟨𝔐, -, h𝔐p, h𝔐⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure O (KSyn D)) N' ⊥ hkerD
  have hmem𝔐 : ∀ d : D, jD d ∈ 𝔐 ↔ d ∈ N' := by
    intro d
    rw [← h𝔐]
    rfl
  -- `B' ⊆ C`
  let sO : ℚ[X] →+* O := algebraMap SrcPoly O
  have hintB' : ∀ x : KSyn D, IsIntegral ℚ[X] x → IsIntegral O x := by
    intro x ⟨p, hp, hpx⟩
    refine ⟨p.map sO, hp.map _, ?_⟩
    rw [eval₂_map]
    have : (algebraMap O (KSyn D)).comp sO = algebraMap ℚ[X] (KSyn D) :=
      RingHom.ext fun a => (hPS a).symm
    rw [this]; exact hpx
  let jB : integralClosure ℚ[X] (KSyn D) →+* integralClosure O (KSyn D) :=
    { toFun := fun x => ⟨x.1, hintB' x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hjBalg : ∀ a : ℚ[X], jB (algebraMap ℚ[X] _ a) =
      jD (iO (algebraMap SrcPoly O a)) := by
    intro a
    apply Subtype.ext
    change algebraMap ℚ[X] (KSyn D) a = gO (algebraMap SrcPoly O a)
    exact hPS a
  set 𝔓' := 𝔐.comap jB with h𝔓'_def
  haveI : 𝔓'.IsPrime := Ideal.IsPrime.comap jB
  have hunder : 𝔓'.under ℚ[X] = Ideal.span {X - C s₀} := by
    ext a
    change jB (algebraMap ℚ[X] _ a) ∈ 𝔐 ↔ _
    rw [hjBalg, hmem𝔐, ← Ideal.mem_comap, hN'O]
    change algebraMap SrcPoly O (toSrc a) ∈ maximalIdeal O ↔ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O p0]
    rfl
  -- residue fields and the extension `φ'`
  haveI hN'm : N'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) N'
    (by change (N'.comap iO).IsMaximal; rw [hN'O]; infer_instance)
  haveI h𝔐m : 𝔐.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := D) 𝔐
    (by rw [h𝔐]; exact hN'm)
  have h𝔐O : 𝔐.under O = maximalIdeal O := by
    ext o
    change jD (iO o) ∈ 𝔐 ↔ _
    rw [hmem𝔐, ← Ideal.mem_comap, hN'O]
  haveI : 𝔐.LiesOver (maximalIdeal O) := ⟨h𝔐O.symm⟩
  letI : Field (integralClosure ℚ[X] E ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  letI : Field (integralClosure O (KSyn D) ⧸ 𝔐) := Ideal.Quotient.field 𝔐
  let ψ1 : (integralClosure ℚ[X] E ⧸ 𝔓) →+* (integralClosure O (KSyn D) ⧸ 𝔐) :=
    Ideal.Quotient.lift 𝔓 ((Ideal.Quotient.mk 𝔐).comp (jD.toRingHom.comp iB)) (fun b hb => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact (hmem𝔐 _).mpr (hN'B hb))
  letI aψ : Algebra (integralClosure ℚ[X] E ⧸ 𝔓) (integralClosure O (KSyn D) ⧸ 𝔐) :=
    ψ1.toAlgebra
  letI aφ : Algebra (integralClosure ℚ[X] E ⧸ 𝔓) (AlgebraicClosure ℚ) := φ.toAlgebra
  haveI : Module.IsTorsionFree (integralClosure ℚ[X] E ⧸ 𝔓)
      (integralClosure O (KSyn D) ⧸ 𝔐) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr ψ1.injective
  haveI : Module.IsTorsionFree (integralClosure ℚ[X] E ⧸ 𝔓) (AlgebraicClosure ℚ) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ.injective
  -- `C/𝔐` is algebraic over `B/𝔓` (both are algebraic over `ℚ ≅ O/max O`)
  have hsurj : Function.Surjective evO := by
    intro q
    refine ⟨algebraMap SrcPoly O (toSrc (C q)), ?_⟩
    rw [hevS]
    exact eval_C
  have hker : maximalIdeal O = RingHom.ker evO := by
    ext o; rw [RingHom.mem_ker, hevO]
  let e : (O ⧸ maximalIdeal O) ≃+* ℚ :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  let ratB : ℚ →+* (integralClosure ℚ[X] E ⧸ 𝔓) :=
    (algebraMap ℚ[X] (integralClosure ℚ[X] E ⧸ 𝔓)).comp C
  let κ0 : (O ⧸ maximalIdeal O) →+* (integralClosure ℚ[X] E ⧸ 𝔓) := ratB.comp e.toRingHom
  have hκ0 : ψ1.comp κ0 = algebraMap (O ⧸ maximalIdeal O) (integralClosure O (KSyn D) ⧸ 𝔐) := by
    apply RingHom.ext
    intro z
    obtain ⟨q, rfl⟩ := e.symm.surjective z
    have := RingHom.ext_rat ((ψ1.comp κ0).comp e.symm.toRingHom)
      ((algebraMap (O ⧸ maximalIdeal O) (integralClosure O (KSyn D) ⧸ 𝔐)).comp e.symm.toRingHom)
    exact RingHom.congr_fun this q
  haveI : Algebra.IsAlgebraic (integralClosure ℚ[X] E ⧸ 𝔓) (integralClosure O (KSyn D) ⧸ 𝔐) := by
    constructor
    intro y
    obtain ⟨p, hp, hpy⟩ := Algebra.IsIntegral.isIntegral (R := O ⧸ maximalIdeal O) y
    refine ⟨p.map κ0, (hp.map κ0).ne_zero, ?_⟩
    rw [aeval_def, eval₂_map]
    change eval₂ (ψ1.comp κ0) y p = 0
    rw [hκ0]
    exact hpy
  let φ'' : (integralClosure O (KSyn D) ⧸ 𝔐) →ₐ[integralClosure ℚ[X] E ⧸ 𝔓]
      AlgebraicClosure ℚ := IsAlgClosed.lift
  have hφ'' : ∀ x, φ'' (ψ1 x) = φ x := fun x => φ''.commutes x
  let φ' : (integralClosure ℚ[X] (KSyn D) ⧸ 𝔓') →+* AlgebraicClosure ℚ :=
    φ''.toRingHom.comp (Ideal.quotientMap 𝔐 jB le_rfl)
  refine ⟨KSyn D, inferInstance, iK', iP, iT, hfd, ι, ⟨hshape1, ?_⟩, hfin, 𝔓', inferInstance,
    hunder, φ', ?_⟩
  · -- `E'` is generated by `ι(E)` and `s`
    exact hFtop
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    set w := jD (iB b)
    letI iSE : Algebra SrcPoly (KSyn D) := (gO.comp (algebraMap SrcPoly O)).toAlgebra
    haveI : IsScalarTower SrcPoly O (KSyn D) := IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := SrcPoly) (Rₘ := O) p0.primeCompl w.1 w.2
    have hmQ : IsIntegral ℚ[X] (m • w.1) := by
      obtain ⟨p, hp, hpx⟩ := hm
      refine ⟨p, hp, ?_⟩
      have : algebraMap ℚ[X] (KSyn D) = algebraMap SrcPoly (KSyn D) :=
        RingHom.ext fun a => hPS a
      rw [this]
      exact hpx
    let y : integralClosure ℚ[X] (KSyn D) := ⟨m • w.1, hmQ⟩
    let u : integralClosure ℚ[X] (KSyn D) := algebraMap ℚ[X] _ (m : SrcPoly).toPoly
    have hyu : jB y = jB u * w := by
      apply Subtype.ext
      change (m • w.1 : KSyn D) = algebraMap ℚ[X] (KSyn D) (m : SrcPoly).toPoly * w.1
      rw [Submonoid.smul_def, Algebra.smul_def, hPS]
      rfl
    have hu0 : Ideal.Quotient.mk 𝔐 (jB u) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      change jB (algebraMap ℚ[X] _ (m : SrcPoly).toPoly) ∈ 𝔐 → False
      rw [hjBalg, hmem𝔐, ← Ideal.mem_comap, hN'O]
      intro hmm
      exact m.2 ((IsLocalization.AtPrime.to_map_mem_maximal_iff O p0 _).mp hmm)
    have hw : Ideal.Quotient.mk 𝔐 w =
        Ideal.Quotient.mk 𝔐 (jB y) / Ideal.Quotient.mk 𝔐 (jB u) := by
      rw [eq_div_iff hu0, hyu, map_mul, mul_comm]
    have hφx : φ (Ideal.Quotient.mk 𝔓 b) = φ' (Ideal.Quotient.mk 𝔓' y) /
        φ' (Ideal.Quotient.mk 𝔓' u) := by
      rw [← hφ'']
      change φ'' (Ideal.Quotient.mk 𝔐 w) = _
      rw [hw, map_div₀]
      rfl
    rw [hφx]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩)


theorem kummerCompositum_proof : KummerCompositum := by
  intro E _ _ _ _ _ P Q t s₀ hQ hPQ hnc 𝔓 h𝔓 h𝔓u φ
  classical
  -- the `s`-coordinate local ring `O = ℚ[s]_(s - s₀)` (as a localization of `SrcPoly`)
  set p0 : Ideal SrcPoly := Ideal.span {toSrc (X - C s₀)} with hp0_def
  haveI hp0 : p0.IsPrime := by
    change (Ideal.span {(X - C s₀ : ℚ[X])}).IsPrime
    exact (Ideal.span_singleton_prime (X_sub_C_ne_zero s₀)).mpr (prime_X_sub_C s₀)
  have hmem0 : ∀ f : SrcPoly, f ∈ p0 ↔ f.toPoly.eval s₀ = 0 := by
    intro f
    change (f.toPoly ∈ Ideal.span {(X - C s₀ : ℚ[X])}) ↔ _
    rw [Ideal.mem_span_singleton, dvd_iff_isRoot]
    rfl
  set O := Localization.AtPrime p0
  let ev0 : SrcPoly →+* ℚ := (Polynomial.evalRingHom s₀ : ℚ[X] →+* ℚ)
  have hev0 : ∀ f : SrcPoly, ev0 f = f.toPoly.eval s₀ := fun f => rfl
  have hunit0 : ∀ y : p0.primeCompl, IsUnit (ev0 y) := fun y =>
    Ne.isUnit (by rw [hev0]; exact fun h => y.2 ((hmem0 _).mpr h))
  let evO : O →+* ℚ := IsLocalization.lift (M := p0.primeCompl) (S := O) (g := ev0) hunit0
  have hevO : ∀ f : SrcPoly, evO (algebraMap SrcPoly O f) = f.toPoly.eval s₀ :=
    fun f => IsLocalization.lift_eq hunit0 f
  have hQ0 : toSrc Q ∉ p0 := fun h => hQ ((hmem0 _).mp h)
  set r : O := IsLocalization.mk' O (toSrc P) (⟨toSrc Q, hQ0⟩ : p0.primeCompl) with hr_def
  have hrspec : r * algebraMap SrcPoly O (toSrc Q) = algebraMap SrcPoly O (toSrc P) :=
    IsLocalization.mk'_spec O _ _
  have hevr : evO r = t := by
    have h1 := congrArg evO hrspec
    rw [map_mul, hevO, hevO] at h1
    change evO r * Q.eval s₀ = P.eval s₀ at h1
    rw [hPQ] at h1
    exact mul_right_cancel₀ hQ h1
  let Csrc : ℚ →+* SrcPoly := (Polynomial.C : ℚ →+* ℚ[X])
  let ρ : ℚ[X] →+* O := Polynomial.eval₂RingHom ((algebraMap SrcPoly O).comp Csrc) r
  have hevρ : ∀ f : ℚ[X], evO (ρ f) = f.eval t := by
    have : evO.comp ρ = Polynomial.evalRingHom t := by
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_rat ((evO.comp ρ).comp C)
          ((Polynomial.evalRingHom t).comp C)) a
      · simp only [RingHom.comp_apply, coe_evalRingHom, eval_X]
        change evO (eval₂ _ r X) = t
        rw [eval₂_X, hevr]
    intro f
    exact RingHom.congr_fun this f
  letI : Algebra ℚ[X] O := ρ.toAlgebra
  -- `(integralClosure ℚ[X] E)` and the residue field at `𝔓`
  haveI := h𝔓
  let χ0 : O →+* (integralClosure ℚ[X] E) ⧸ 𝔓 := ((algebraMap ℚ[X] ((integralClosure ℚ[X] E) ⧸ 𝔓)).comp C).comp evO
  have hχ0 : ∀ f : ℚ[X], χ0 (ρ f) = algebraMap ℚ[X] ((integralClosure ℚ[X] E) ⧸ 𝔓) f := by
    intro f
    change algebraMap ℚ[X] ((integralClosure ℚ[X] E) ⧸ 𝔓) (C (evO (ρ f))) = _
    rw [hevρ, ← sub_eq_zero, ← map_sub,
      IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) ((integralClosure ℚ[X] E) ⧸ 𝔓), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]
    change _ ∈ 𝔓.under ℚ[X]
    rw [h𝔓u, Ideal.mem_span_singleton, ← dvd_neg, neg_sub]
    exact X_sub_C_dvd_sub_C_eval
  let χ : O →ₐ[ℚ[X]] (integralClosure ℚ[X] E) ⧸ 𝔓 := { χ0 with commutes' := hχ0 }
  -- the tensor product `T = O ⊗_{ℚ[X]} (integralClosure ℚ[X] E)` and the prime `N` over `𝔓` and `max O`
  let ψ0 : O ⊗[ℚ[X]] (integralClosure ℚ[X] E) →ₐ[ℚ[X]] (integralClosure ℚ[X] E) ⧸ 𝔓 :=
    Algebra.TensorProduct.lift χ (Ideal.Quotient.mkₐ ℚ[X] 𝔓) (fun x y => Commute.all (χ x) (Ideal.Quotient.mkₐ ℚ[X] 𝔓 y))
  set N := RingHom.ker ψ0.toRingHom
  haveI : N.IsPrime := RingHom.ker_isPrime _
  obtain ⟨𝔫, h𝔫min, h𝔫N⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (O ⊗[ℚ[X]] (integralClosure ℚ[X] E))))
    (J := N) bot_le
  haveI h𝔫p : 𝔫.IsPrime := h𝔫min.1.1
  -- `T` is free over `O`
  have hinjE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : Module.IsTorsionFree ℚ[X] E := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjE
  haveI : Algebra.IsSeparable (RatFunc ℚ) E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Free ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.module_free ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Finite ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Free O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := inferInstance
  haveI : Module.IsTorsionFree O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := inferInstance
  have hdisj : ∀ o : O, o ≠ 0 → algebraMap O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) o ∉ 𝔫 := by
    intro o ho hm
    have hnzd : algebraMap O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) o ∈ nonZeroDivisors (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro x hx
      rw [mul_comm, ← Algebra.smul_def] at hx
      exact (smul_eq_zero_iff_right ho).mp hx
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔫min) hm hnzd
  -- the map `O → ℚ(s)` and injectivity of `ρ`
  let sK : SrcPoly →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)
  have hS_K : ∀ y : p0.primeCompl, IsUnit (sK y) := by
    intro y
    refine Ne.isUnit fun h0 => y.2 ?_
    have : (y : SrcPoly) = 0 := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
      (h0.trans (map_zero sK).symm)
    rw [this]; exact p0.zero_mem
  let oK : O →+* RatFunc ℚ := IsLocalization.lift (M := p0.primeCompl) (S := O) (g := sK) hS_K
  have hoK : ∀ a : SrcPoly, oK (algebraMap SrcPoly O a) = algebraMap ℚ[X] (RatFunc ℚ) a.toPoly :=
    fun a => IsLocalization.lift_eq hS_K a
  have hQK : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
      (fun h0 => hQ (by rw [h0, eval_zero]))
  have hoKr : oK r = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q := by
    have h1 := congrArg oK hrspec
    rw [map_mul, hoK, hoK] at h1
    rw [eq_div_iff hQK]; exact h1
  have hoKρ : ∀ f : ℚ[X], oK (ρ f) =
      aeval (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) f := by
    have : oK.comp ρ = (aeval (algebraMap ℚ[X] (RatFunc ℚ) P /
        algebraMap ℚ[X] (RatFunc ℚ) Q) : ℚ[X] →ₐ[ℚ] RatFunc ℚ).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_rat ((oK.comp ρ).comp C)
          (((aeval (algebraMap ℚ[X] (RatFunc ℚ) P /
            algebraMap ℚ[X] (RatFunc ℚ) Q) : ℚ[X] →ₐ[ℚ] RatFunc ℚ).toRingHom).comp C)) a
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        change oK (eval₂ _ r X) = _
        rw [eval₂_X, hoKr]
    intro f
    exact RingHom.congr_fun this f
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have := hoKρ f
    rw [hf, map_zero] at this
    exact ratFunc_transc P Q (fun h0 => hQ (by rw [h0, eval_zero])) hnc f this.symm
  -- the injection `ρ` and the map `O → ℚ(s)`
  let sK : SrcPoly →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)
  have hS_K : ∀ y : p0.primeCompl, IsUnit (sK y) := by
    intro y
    refine Ne.isUnit fun h0 => y.2 ?_
    have : (y : SrcPoly) = 0 := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
      (h0.trans (map_zero sK).symm)
    rw [this]; exact p0.zero_mem
  let oK : O →+* RatFunc ℚ := IsLocalization.lift (M := p0.primeCompl) (S := O) (g := sK) hS_K
  have hoK : ∀ a : SrcPoly, oK (algebraMap SrcPoly O a) = algebraMap ℚ[X] (RatFunc ℚ) a.toPoly :=
    fun a => IsLocalization.lift_eq hS_K a
  have hQK : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
      (fun h0 => hQ (by rw [h0, eval_zero]))
  have hoKr : oK r = algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q := by
    have h1 := congrArg oK hrspec
    rw [map_mul, hoK, hoK] at h1
    rw [eq_div_iff hQK]; exact h1
  have hρX : ρ X = r := by simp [ρ]
  have hoKρ : ∀ f : ℚ[X], oK (ρ f) =
      aeval (algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q) f := by
    have : oK.comp ρ = (aeval (algebraMap ℚ[X] (RatFunc ℚ) P /
        algebraMap ℚ[X] (RatFunc ℚ) Q) : ℚ[X] →ₐ[ℚ] RatFunc ℚ).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        exact RingHom.congr_fun (RingHom.ext_rat ((oK.comp ρ).comp C)
          (((aeval (algebraMap ℚ[X] (RatFunc ℚ) P /
            algebraMap ℚ[X] (RatFunc ℚ) Q) : ℚ[X] →ₐ[ℚ] RatFunc ℚ).toRingHom).comp C)) a
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rw [hρX, hoKr]
    intro f
    exact RingHom.congr_fun this f
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have := hoKρ f
    rw [hf, map_zero] at this
    exact ratFunc_transc P Q (fun h0 => hQ (by rw [h0, eval_zero])) hnc f this.symm
  -- the kernel of `evO` is the maximal ideal
  have hevOmax : ∀ o, evO o = 0 ↔ o ∈ maximalIdeal O := by
    intro o
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p0.primeCompl o
    have hs : evO (algebraMap SrcPoly O s) ≠ 0 := by
      rw [hevO]; exact fun h => s.2 ((hmem0 _).mpr h)
    have hspec := IsLocalization.mk'_spec O a s
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O p0, hmem0, ← hevO]
    constructor
    · intro h0
      rw [← hspec, map_mul, h0, zero_mul]
    · intro h0
      rw [← hspec, map_mul] at h0
      exact (mul_eq_zero.mp h0).resolve_right hs
  -- `D = T/𝔫` and the data of `kc_core`
  haveI : IsDomain ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫) := Ideal.Quotient.isDomain 𝔫
  haveI h𝔓m : 𝔓.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℚ[X]) 𝔓
    (by rw [h𝔓u]; exact PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C t))
  have hiO : ∀ o : O, algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫) o =
      Ideal.Quotient.mk 𝔫 (o ⊗ₜ 1) := fun o => rfl
  have hiOinj : Function.Injective
      (algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫)) := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    by_contra hne
    apply hdisj o hne
    rw [hiO, Ideal.Quotient.eq_zero_iff_mem] at ho
    exact ho
  let iB : integralClosure ℚ[X] E →+* (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫 :=
    (Ideal.Quotient.mk 𝔫).comp (Algebra.TensorProduct.includeRight.toRingHom)
  have hiB : ∀ c : ℚ[X], iB (algebraMap ℚ[X] (integralClosure ℚ[X] E) c) =
      algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫) (ρ c) := by
    intro c
    rw [hiO]
    change Ideal.Quotient.mk 𝔫 (1 ⊗ₜ algebraMap ℚ[X] _ c) = _
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hgen : ∀ d : (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫,
      d ∈ Subring.closure (Set.range (algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫)) ∪
        Set.range iB) := by
    intro d
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective d
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul o b =>
      have : Ideal.Quotient.mk 𝔫 (o ⊗ₜ[ℚ[X]] b) =
          algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫) o * iB b := by
        rw [hiO]
        change _ = Ideal.Quotient.mk 𝔫 (o ⊗ₜ 1) * Ideal.Quotient.mk 𝔫 (1 ⊗ₜ b)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨o, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  haveI : Module.Finite O (O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) := inferInstance
  haveI : Algebra.IsIntegral O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫) := inferInstance
  have hint : (algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫)).IsIntegral :=
    fun d => Algebra.IsIntegral.isIntegral d
  set N' := N.map (Ideal.Quotient.mk 𝔫) with hN'_def
  haveI : N'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact h𝔫N)
  have hNcomap : N'.comap (Ideal.Quotient.mk 𝔫) = N := by
    rw [hN'_def, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr h𝔫N]
  have hratB : Function.Injective ((algebraMap ℚ[X] (integralClosure ℚ[X] E ⧸ 𝔓)).comp C) :=
    RingHom.injective _
  have hN'O : N'.comap (algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫)) =
      maximalIdeal O := by
    ext o
    rw [Ideal.mem_comap, hiO, ← Ideal.mem_comap, hNcomap, ← hevOmax]
    change ψ0 (o ⊗ₜ 1) = 0 ↔ _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    change ((algebraMap ℚ[X] (integralClosure ℚ[X] E ⧸ 𝔓)).comp C) (evO o) = 0 ↔ _
    rw [← map_zero ((algebraMap ℚ[X] (integralClosure ℚ[X] E ⧸ 𝔓)).comp C)]
    exact hratB.eq_iff
  have hN'B : 𝔓 ≤ N'.comap iB := by
    intro b hb
    rw [Ideal.mem_comap]
    change Ideal.Quotient.mk 𝔫 (1 ⊗ₜ b) ∈ N'
    rw [← Ideal.mem_comap, hNcomap]
    change ψ0 (1 ⊗ₜ b) = 0
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  refine kc_core E P Q s₀ 𝔓 φ O ρ hρinj oK ?_ ?_ evO ?_ ?_
    ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫)
    (algebraMap O ((O ⊗[ℚ[X]] (integralClosure ℚ[X] E)) ⧸ 𝔫)) ?_ iB ?_ ?_ ?_ N' ?_ ?_
  · exact hoK
  · rw [hρX, hoKr]
  · exact hevOmax
  · exact hevO
  · exact hiOinj
  · exact hiB
  · exact hgen
  · exact hint
  · exact hN'O
  · exact hN'B

end TsKummer
#print axioms TsKummer.kummerAbhyankarFinGlue
#print axioms TsKummer.kummerAbhyankarInfGlue
#print axioms TsKummer.compositum_core0
#print axioms TsKummer.kummerOtherBranchFin_of_unram
#print axioms TsKummer.unramCompositum
#print axioms TsKummer.kummerOtherBranchInf_of_unram
#print axioms TsKummer.unramBaseChange
#print axioms TsKummer.kummerVerticalFin_proof
#print axioms TsKummer.kummerVerticalInf_proof
#print axioms TsKummer.kummerCompositum_proof

/-! ## ts-kummer: the Kummer pieces of `PropTSGlue`, final statements -/

namespace TsKummer

open Polynomial G0ModField PropTSRed PropTSGlue

/-- **`KummerOtherBranchFin` is proved** (from `UnramCompositum`, which is proved). -/
theorem kummerOtherBranchFin : KummerOtherBranchFin :=
  kummerOtherBranchFin_of_unram unramCompositum

/-- **`KummerOtherBranchInf` is proved** (from `UnramCompositum`, which is proved). -/
theorem kummerOtherBranchInf : KummerOtherBranchInf :=
  kummerOtherBranchInf_of_unram unramCompositum

/-- **`KummerVerticalFin` is proved.** -/
theorem kummerVerticalFin : KummerVerticalFin := kummerVerticalFin_proof

/-- **`KummerVerticalInf` is proved.** -/
theorem kummerVerticalInf : KummerVerticalInf := kummerVerticalInf_proof

/-- **`KummerCompositum` is proved.** -/
theorem kummerCompositum : KummerCompositum := kummerCompositum_proof

/-- **`KummerMeetGlue` is proved** (all seven Kummer pieces are proved; the two Abhyankar pieces
use T2, which is `KummerMeetGlue`'s own hypothesis). -/
theorem kummerMeetGlue : KummerMeetGlue := kummerMeetGlue_of_compositum kummerCompositum

/-- `KummerMeetGlue` from `KummerCompositum` alone (the other six Kummer pieces are proved;
the two Abhyankar pieces use T2 inside `KummerMeetGlue`'s own hypothesis). -/
theorem kummerMeetGlue_of_compositum (hC : KummerCompositum) : KummerMeetGlue :=
  kummerMeetGlue_of_pieces' hC kummerAbhyankarFinGlue kummerOtherBranchFin kummerVerticalFin
    kummerAbhyankarInfGlue kummerOtherBranchInf kummerVerticalInf

/-- `PropTSAll` (prop-ts-glue's `propTSAll_final`) with the six proved Kummer pieces removed
(superseded by `propTSAll_ts'`). -/
theorem propTSAll_ts (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize) (hC : KummerCompositum)
    (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch)
    (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_final t2 hR hM hS hC kummerAbhyankarFinGlue kummerOtherBranchFin kummerVerticalFin
    kummerAbhyankarInfGlue kummerOtherBranchInf kummerVerticalInf hI hNI hD hB hV

/-- **`PropTSAll` with all seven Kummer pieces removed**: from T2, `R1R2fp`, `MobiusGlue`,
`SNSpecialize` and the five Hecke Props. -/
theorem propTSAll_ts' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize)
    (hI : HeckeIrreducible) (hNI : HeckeNormalizationIrr) (hD : HeckeDegree) (hB : HeckeBranch)
    (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_ts t2 hR hM hS kummerCompositum hI hNI hD hB hV

end TsKummer

#print axioms TsKummer.kummerCompositum
#print axioms TsKummer.kummerMeetGlue
#print axioms TsKummer.propTSAll_ts'
#print axioms TsKummer.kummerOtherBranchFin
#print axioms TsKummer.kummerOtherBranchInf
#print axioms TsKummer.kummerVerticalFin
#print axioms TsKummer.kummerVerticalInf
#print axioms TsKummer.kummerMeetGlue_of_compositum
#print axioms TsKummer.propTSAll_ts
