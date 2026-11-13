import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Textbook.SkolemNoether

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# `scratch/prop-ts-glue/PropTSGlue.lean`, lines 3-3553 (everything but the imports and the trailing
`#print axioms` lines), verbatim. Its first 906 lines are `scratch/prop-ts/PropTS.lean`; its Part C
holds the five Hecke Props of this task.
════════════════════════════════════════════════════════════════════════════════════════════ -/

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
# `scratch/ts-hecke/GaloisPart.lean.part` (task ts-hecke; compiled on its own as `GaloisDev.lean`)
════════════════════════════════════════════════════════════════════════════════════════════ -/

/-! ## Part 3b: the Galois property in `CurveGaloisChart` (dev section) -/

noncomputable section

namespace TSHeckeGal

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed

/-- Any two morphisms `Spec ℚ̄ → Spec ℚ` agree. -/
theorem specQbar_to_specQ_eq' (f g : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of ℚ)) :
    f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **A closed point of a scheme locally of finite type over `ℚ` has a `ℚ̄`-point** (compiled). -/
theorem exists_qbar_point {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (z : X) (hz : IsClosed ({z} : Set X)) :
    ∃ y : Spec (CommRingCat.of Qbar) ⟶ X, ∀ s, y s = z := by
  have : IsClosedImmersion (X.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have : IsFinite (X.fromSpecResidueField z ≫ f) :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
      (f := X.fromSpecResidueField z ≫ f)).mpr inferInstance
  let φ := Spec.preimage (X.fromSpecResidueField z ≫ f)
  letI : Algebra ℚ (X.residueField z) := φ.hom.toAlgebra
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  haveI : Algebra.IsIntegral ℚ (X.residueField z) := ⟨fun x => hφ x⟩
  haveI : Algebra.IsAlgebraic ℚ (X.residueField z) := Algebra.IsIntegral.isAlgebraic
  let L : X.residueField z →ₐ[ℚ] Qbar := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom L.toRingHom) ≫ X.fromSpecResidueField z, fun s => ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

variable {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type} [Field E]
  [Algebra ℚ[X] E]

/-- **A `π`-preserving endomorphism maps the chart into itself** (compiled; Jacobson). -/
theorem range_comp_subset [LocallyOfFiniteType Y.hom]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left) [IsOpenImmersion h]
    (himg : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)))
    (g : Y.left ⟶ Y.left)
    (hg : ∀ z : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) (z ≫ g) = π.val (K := Qbar) z) :
    Set.range (h ≫ g) ⊆ Set.range h := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  by_contra hcon
  rw [Set.not_subset] at hcon
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hcon
  set W : Set Y.left := Set.range h ∩ g ⁻¹' (Set.range h)ᶜ
  have hWne : W.Nonempty := ⟨h x, ⟨x, rfl⟩, by simpa using hx⟩
  have hWlc : IsLocallyClosed W :=
    (h.isOpenEmbedding.isOpen_range).isLocallyClosed.inter
      ((h.isOpenEmbedding.isOpen_range).isClosed_compl.preimage g.continuous).isLocallyClosed
  obtain ⟨z, ⟨hzh, hzg⟩, hzc⟩ := nonempty_inter_closedPoints hWne hWlc
  obtain ⟨y, hy⟩ := exists_qbar_point Y.hom z (mem_closedPoints_iff.mp hzc)
  have hyr : Set.range y ⊆ Set.range h := by
    rintro _ ⟨s, rfl⟩; rw [hy s]; exact hzh
  set y'' := IsOpenImmersion.lift h y hyr
  have hy'' : y'' ≫ h = y := IsOpenImmersion.lift_fac h y hyr
  have hfin : π.val (K := Qbar) y ≠ OnePoint.infty := by
    rw [← hy'', ← Spec.map_preimage y'', ← CommRingCat.ofHom_hom (Spec.preimage y''), hval]
    exact OnePoint.coe_ne_infty _
  obtain ⟨y', hy'⟩ := himg (y ≫ g) (by rw [hg]; exact hfin)
  apply hzg
  obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of Qbar)) := inferInstance
  refine ⟨y' s, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hy', Scheme.Hom.comp_apply, hy s]

/-- A nonzero prime of `ℚ[X]` is the kernel of evaluation at some `t ∈ ℚ̄` (compiled). -/
theorem exists_ker_eval' (P : Ideal ℚ[X]) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
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

/-- **Separation by `ℚ̄`-points** (compiled): in a domain `B` finite over `ℚ[X]`, two elements with
the same value under every ring map `B → ℚ̄` are equal (`B` is Jacobson; every maximal ideal is
the kernel of such a map). -/
theorem eq_of_forall_qbar {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ[X] B]
    [Algebra.IsIntegral ℚ[X] B] (hinj : Function.Injective (algebraMap ℚ[X] B)) (a b : B)
    (h : ∀ ψ : B →+* Qbar, ψ a = ψ b) : a = b := by
  haveI : IsJacobsonRing B := isJacobsonRing_of_isIntegral (R := ℚ[X])
  rw [← sub_eq_zero]
  have hjac := IsJacobsonRing.out (R := B) inferInstance
    (Ideal.isRadical_bot_of_noZeroDivisors (R := B))
  rw [← Ideal.mem_bot, ← hjac, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  haveI := hm
  set P := m.under ℚ[X]
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℚ[X]) m
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0] at hPmax
    exact Polynomial.not_isField ℚ (Ring.isField_iff_maximal_bot.2 hPmax)
  obtain ⟨t, ht⟩ := exists_ker_eval' P hP0
  let φ : ℚ[X] →+* Qbar := Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t
  haveI : m.LiesOver P := ⟨rfl⟩
  letI : Algebra (ℚ[X] ⧸ P) Qbar :=
    (Ideal.Quotient.lift P φ (fun x hx => by rw [ht] at hx; exact RingHom.mem_ker.1 hx)).toAlgebra
  letI : Field (ℚ[X] ⧸ P) := Ideal.Quotient.field P
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Module.IsTorsionFree (ℚ[X] ⧸ P) (B ⧸ m) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (ℚ[X] ⧸ P) Qbar := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (ℚ[X] ⧸ P) Qbar).injective
  haveI : Algebra.IsAlgebraic (ℚ[X] ⧸ P) (B ⧸ m) := Algebra.IsIntegral.isAlgebraic
  let L : (B ⧸ m) →ₐ[ℚ[X] ⧸ P] Qbar := IsAlgClosed.lift
  have h1 := h (L.toRingHom.comp (Ideal.Quotient.mk m))
  simp only [RingHom.coe_comp, Function.comp_apply] at h1
  have h2 := L.toRingHom.injective h1
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact h2

/-- **The ring map induced by a `π`-preserving endomorphism** (compiled). -/
theorem exists_sigma [LocallyOfFiniteType Y.hom] [Algebra (RatFunc ℚ) E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left) [IsOpenImmersion h]
    (himg : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)))
    (g : Y.left ⟶ Y.left)
    (hg : ∀ z : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) (z ≫ g) = π.val (K := Qbar) z) :
    ∃ σ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E,
      Spec.map (CommRingCat.ofHom σ) ≫ h = h ≫ g ∧
      σ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ[X] (integralClosure ℚ[X] E) X := by
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  have hr := range_comp_subset h himg hval g hg
  set k := IsOpenImmersion.lift h (h ≫ g) hr
  have hk : k ≫ h = h ≫ g := IsOpenImmersion.lift_fac h (h ≫ g) hr
  refine ⟨(Spec.preimage k).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage, hk]
  · apply eq_of_forall_qbar hinjB
    intro ψ
    have e1 := hval (ψ.comp (Spec.preimage k).hom)
    have e2 : Spec.map (CommRingCat.ofHom (ψ.comp (Spec.preimage k).hom)) ≫ h =
        (Spec.map (CommRingCat.ofHom ψ) ≫ h) ≫ g := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage,
        Category.assoc, hk, Category.assoc]
    rw [e2, hg, hval ψ] at e1
    exact (OnePoint.coe_injective e1).symm

/-- **The field automorphism induced by a `π`-preserving endomorphism** (compiled): the ring map
`σ` of `exists_sigma` fixes `ℚ[X]`, so it extends to an automorphism `τ` of `E` over `ℚ(X)`. -/
theorem exists_tau [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    [FiniteDimensional (RatFunc ℚ) E]
    (σ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E)
    (hσ : σ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ[X] (integralClosure ℚ[X] E) X) :
    ∃ τ : E ≃ₐ[RatFunc ℚ] E, ∀ b : integralClosure ℚ[X] E,
      τ (algebraMap (integralClosure ℚ[X] E) E b) = algebraMap (integralClosure ℚ[X] E) E (σ b) := by
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  haveI : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  -- `σ` fixes `ℚ[X]`
  have hfix : σ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E)) =
      algebraMap ℚ[X] (integralClosure ℚ[X] E) :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun (RingHom.ext_rat
      ((σ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp Polynomial.C)
      ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp Polynomial.C)) a) (by simpa using hσ)
  -- `σ` is injective
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hker : (RingHom.ker σ).under ℚ[X] = ⊥ := by
      ext a
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro ha
        rw [← RingHom.comp_apply, hfix] at ha
        exact hinjB (by rw [ha, map_zero])
      · rintro rfl; simp
    have := Ideal.eq_bot_of_under_eq_bot (R := ℚ[X]) hker
    have hb' : b ∈ RingHom.ker σ := hb
    rw [this] at hb'
    exact hb'
  have hg : Function.Injective ((algebraMap (integralClosure ℚ[X] E) E).comp σ) :=
    (IsFractionRing.injective (integralClosure ℚ[X] E) E).comp hσinj
  let τ₀ : E →+* E := IsFractionRing.lift hg
  have hτ₀ : ∀ b, τ₀ (algebraMap (integralClosure ℚ[X] E) E b) =
      algebraMap (integralClosure ℚ[X] E) E (σ b) := fun b => IsFractionRing.lift_algebraMap hg b
  have hcomm : τ₀.comp (algebraMap (RatFunc ℚ) E) = algebraMap (RatFunc ℚ) E := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
    refine RingHom.ext fun a => ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℚ[X]
      (integralClosure ℚ[X] E) E, hτ₀, ← RingHom.comp_apply σ, hfix,
      ← IsScalarTower.algebraMap_apply]
  let τ₁ : E →ₐ[RatFunc ℚ] E := { τ₀ with commutes' := fun r => RingHom.congr_fun hcomm r }
  exact ⟨AlgEquiv.ofBijective τ₁ (AlgHom.bijective τ₁), fun b => hτ₀ b⟩

/-- **Galois from fibre transitivity** (compiled). If `E` carries the normalization chart of
`(Y, π)`, some rational fibre has at least `[E : ℚ(X)]` points of `Spec B` (generic étaleness),
and any two `ℚ̄`-points with the same `π`-value differ by a `π`-preserving automorphism of `Y`,
then `E/ℚ(X)` is Galois. -/
theorem isGalois_of_transitive [LocallyOfFiniteType Y.hom] [Algebra (RatFunc ℚ) E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (hM : NormalizationModel Y π E)
    (hG : ∃ t : ℚ, ∃ s : Finset (integralClosure ℚ[X] E →+* Qbar),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Qbar t)
    (htrans : ∀ y y' : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left →
      ∃ g : Y ≅ Y, y' = y ≫ g.hom ∧
        ∀ z : fieldPt Qbar ⟶ Y, π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left) :
    IsGalois (RatFunc ℚ) E := by
  classical
  haveI : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  obtain ⟨h, hO, himg, hval⟩ := hM
  obtain ⟨t, s, hs, hst⟩ := hG
  let ptO : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq' _ _)
  have hnpos : 0 < Module.finrank (RatFunc ℚ) E := Module.finrank_pos
  obtain ⟨ψ₀, hψ₀⟩ : s.Nonempty := by
    rw [← Finset.card_pos]; omega
  -- for each `ψ ∈ s`, an automorphism `τ` and a ring map `σ` with `ψ = ψ₀ ∘ σ`
  have key : ∀ ψ ∈ s, ∃ τ : E ≃ₐ[RatFunc ℚ] E, ∃ σ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E,
      (∀ b, τ (algebraMap (integralClosure ℚ[X] E) E b) = algebraMap (integralClosure ℚ[X] E) E (σ b)) ∧
      ψ = ψ₀.comp σ := by
    intro ψ hψ
    have hπ : π.val (K := Qbar) (ptO ψ₀).left = π.val (K := Qbar) (ptO ψ).left := by
      show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ₀) ≫ h) =
        π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h)
      rw [hval, hval, hst ψ₀ hψ₀, hst ψ hψ]
    obtain ⟨g, hgy, hgπ⟩ := htrans (ptO ψ₀) (ptO ψ) hπ
    have hg' : ∀ z : Spec (CommRingCat.of Qbar) ⟶ Y.left,
        π.val (K := Qbar) (z ≫ g.hom.left) = π.val (K := Qbar) z := fun z =>
      hgπ (Over.homMk z (specQbar_to_specQ_eq' _ _))
    obtain ⟨σ, hσh, hσX⟩ := exists_sigma h himg hval g.hom.left hg'
    obtain ⟨τ, hτ⟩ := exists_tau σ hσX
    refine ⟨τ, σ, hτ, ?_⟩
    have e1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom (ψ₀.comp σ)) ≫ h := by
      have := congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hgy
      change Spec.map (CommRingCat.ofHom ψ) ≫ h =
        (Spec.map (CommRingCat.ofHom ψ₀) ≫ h) ≫ g.hom.left at this
      rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, hσh]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 e1))
  choose T σT hT hψT using key
  have hTinj : Function.Injective (fun ψ : s => T ψ.1 ψ.2) := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ heq
    simp only at heq
    apply Subtype.ext
    simp only
    rw [hψT ψ hψ, hψT ψ' hψ']
    congr 1
    ext1 b
    apply IsFractionRing.injective (integralClosure ℚ[X] E) E
    rw [← hT ψ hψ b, ← hT ψ' hψ' b, heq]
  have hcard : s.card ≤ Fintype.card (E ≃ₐ[RatFunc ℚ] E) := by
    rw [← Fintype.card_coe s]
    exact Fintype.card_le_of_injective _ hTinj
  have hle := AlgEquiv.card_le (F := RatFunc ℚ) (K := E)
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  omega

end TSHeckeGal

end

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

/-- **Glue (curve theory; h-b1 M1, M8): the normalization chart, without the Galois property.**
For a proper smooth irreducible curve `Y/ℚ` and `π : Y → P¹` with finite `ℚ̄`-fibres there is a
finite `E/ℚ(X)` with `NormalizationModel Y π E`. *Proof* (STANDARD; Hartshorne II.6.7-6.8,
Stacks 02OG; locators UNVERIFIED): `π` is quasi-finite and proper, hence finite; `Y` is normal, so
`π⁻¹(𝔸¹) = Spec B` with `B` the integral closure of `ℚ[X]` in `E = ℚ(Y)`. Glue, not a leaf. -/
def CurveNormChart : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E),
      NormalizationModel Y π E

/-- **`CurveGaloisChart` from `CurveNormChart`** (compiled): the Galois property follows from
fibre transitivity (`TSHeckeGal.isGalois_of_transitive`: the `π`-preserving automorphisms map the
chart into itself (Jacobson), induce automorphisms of `B` fixing `ℚ[X]` (separation by
`ℚ̄`-points) and of `E` over `ℚ(X)`, and act transitively on the `[E : ℚ(X)]` points of a generic
fibre, so `|Aut(E/ℚ(X))| = [E : ℚ(X)]`). -/
theorem curveGaloisChart_of (hN : CurveNormChart) : CurveGaloisChart := by
  intro Y π hP hS hI hfin htrans
  obtain ⟨E, i1, i2, i3, i4, i5, hM⟩ := hN Y π hP hS hI hfin
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  exact ⟨E, i1, i2, i3, i4, i5,
    TSHeckeGal.isGalois_of_transitive hM (genericFibreCount E) htrans, hM⟩

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

/-- **`PropTSAll` with ts-hecke's reductions in place of the five Hecke Props** (compiled; through
prop-ts-glue's `propTSAll_final`). Hypotheses: the bundle leaves T2 and `R1R2fp`, the kernel glue
`MobiusGlue`, prop-ts-glue's open glue (`SNSpecialize`, seven Kummer pieces), and ts-hecke's
inputs (leaves `Y3Connected`, `TorsionStructure`; glue `CurveGaloisChart`, `CurveChartInf`,
`HeckeFibreSizes`, `HeckeNoVertRam`). -/
theorem propTSAll_of_tsHecke (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure) (hCG : CurveGaloisChart)
    (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_final t2 hR hM hS hC hA hO hVF hAI hOI hVI (heckeIrreducible_of_connected hconn)
    (heckeNormalizationIrr_of hCG hT) (heckeDegree_of_torsion hT) (heckeBranch_of' hR hCI hF hT) hV

/-- **`CoverModelOfHecke` with `CurveNormChart` in place of `CurveGaloisChart`** (compiled). -/
theorem coverModelOfHecke_of_tsHecke' (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hCN : CurveNormChart) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : CoverModelOfHecke :=
  coverModelOfHecke_of_tsHecke hconn hRR hT (curveGaloisChart_of hCN) hCI hF hV

/-- **`PropTSAll` with ts-hecke's reductions, `CurveNormChart` form** (compiled). -/
theorem propTSAll_of_tsHecke' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure) (hCN : CurveNormChart)
    (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_of_tsHecke t2 hR hM hS hC hA hO hVF hAI hOI hVI hconn hT (curveGaloisChart_of hCN)
    hCI hF hV

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
#print axioms TSHecke.propTSAll_of_tsHecke
#print axioms TSHeckeGal.exists_qbar_point
#print axioms TSHeckeGal.range_comp_subset
#print axioms TSHeckeGal.eq_of_forall_qbar
#print axioms TSHeckeGal.exists_sigma
#print axioms TSHeckeGal.exists_tau
#print axioms TSHeckeGal.isGalois_of_transitive
#print axioms TSHecke.curveGaloisChart_of
#print axioms TSHecke.coverModelOfHecke_of_tsHecke'
#print axioms TSHecke.propTSAll_of_tsHecke'


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: the integrated file (assembled by `scratch/hecke-rest/assemble.py`)

Above: `scratch/ts-hecke/TSHecke.lean`, all 7109 lines, verbatim. Below: the value calculus of
`scratch/image-plane/AlgDepProof.lean` (lines 15-171, 277-322, verbatim) and the new parts of
`FibreSizes.lean`, `NoVert.lean`, `CurveChart.lean` (their `*Main.lean.part` files, verbatim),
then the composite theorems. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
open PkgI3

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1


/-! ## §1 Values of sections at `K`-points -/

section Ev

variable {K : Type} [Field K] {X : Scheme.{0}}

/-- Restriction of sections along `O' ≤ O`, as a ring hom. -/
abbrev res {O O' : X.Opens} (h : O' ≤ O) : Γ(X, O) →+* Γ(X, O') :=
  (X.presheaf.map (homOfLE h).op).hom

theorem res_res {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (s : Γ(X, O)) :
    res h' (res h s) = res (h'.trans h) s := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The value `s(p) ∈ K` of a section `s ∈ Γ(X, O)` at a field point `p` whose point lies in `O`
(the image of `s(x) ∈ κ(x)` under the embedding `κ(x) → K` of `p`; this is how `ToP1.val`
evaluates). -/
def ev (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O) : Γ(X, O) →+* K :=
  (X.evaluation O (ptOf p) hx ≫ (Scheme.SpecToEquivOfField K X p).2).hom

theorem ev_res (p : Spec (CommRingCat.of K) ⟶ X) {O O' : X.Opens} (h : O' ≤ O)
    (hx : ptOf p ∈ O') (s : Γ(X, O)) : ev p hx (res h s) = ev p (h hx) s := by
  simp only [ev, res, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  congr 1
  simp only [Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply (X.presheaf.map _), TopCat.Presheaf.germ_res]

theorem ev_eq_zero_iff (p : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf p ∈ O)
    (s : Γ(X, O)) : ev p hx s = 0 ↔ ptOf p ∉ X.basicOpen s := by
  rw [← X.evaluation_eq_zero_iff_notMem_basicOpen (ptOf p) hx s]
  simp only [ev, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact map_eq_zero_iff _ (Scheme.SpecToEquivOfField K X p).2.hom.injective

theorem ev_top (p : Spec (CommRingCat.of K) ⟶ X) (s : Γ(X, ⊤)) :
    ev p (show ptOf p ∈ (⊤ : X.Opens) from trivial) s =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (p.appTop s) := by
  have e := Scheme.germ_stalkClosedPointTo p ⊤ trivial
  have e' := congrArg (fun φ => φ.hom s) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e'
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo p)).hom
    ((X.presheaf.germ ⊤ _ trivial).hom s) = _
  rw [Scheme.residue_descResidueField, e']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op, eqToHom_map,
    Scheme.Hom.appTop]
  rfl

/-- The constant section `a ∈ K` on `O`, through the structure morphism `f : X → Spec K`. -/
def cst (f : X ⟶ Spec (CommRingCat.of K)) (O : X.Opens) (a : K) : Γ(X, O) :=
  res le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

theorem ev_cst (f : X ⟶ Spec (CommRingCat.of K)) (p : Spec (CommRingCat.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) {O : X.Opens} (hx : ptOf p ∈ O) (a : K) : ev p hx (cst f O a) = a := by
  rw [cst, ev_res, ev_top]
  have h1 : p.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv a := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]; rfl
  rw [h1]; simp

end Ev

/-! ## §2 Closed points are `K`-points; units by values -/

section Units

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [JacobsonSpace X]

theorem exists_point_of_isLocallyClosed {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧ ptOf p ∈ Z := by
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed ({y} : Set X) := mem_closedPoints_iff.mp hyc
  refine ⟨pointOfClosedPoint f y hy, pointOfClosedPoint_comp f y hy, ?_⟩
  have e : ptOf (pointOfClosedPoint f y hy) = y := pointOfClosedPoint_apply f y hy _
  rw [e]; exact hyZ

/-- A section whose value at every `K`-point of its domain is nonzero is a unit (Jacobson). -/
theorem isUnit_of_ev_ne_zero {O : X.Opens} (s : Γ(X, O))
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → ∀ hx : ptOf p ∈ O, ev p hx s ≠ 0) :
    IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ O s fun x hx => ?_
  rw [← X.mem_basicOpen s x hx]
  by_contra hb
  obtain ⟨p, hp, hpO, hpb⟩ := exists_point_of_isLocallyClosed f
    (Z := (O : Set X) ∩ (X.basicOpen s : Set X)ᶜ)
    (O.isOpen.isLocallyClosed.inter (X.basicOpen s).isOpen.isClosed_compl.isLocallyClosed)
    ⟨x, hx, hb⟩
  exact h p hp hpO ((ev_eq_zero_iff p hpO s).2 hpb)

end Units

section Main

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem ev_eq_of_nilpotent (f : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {s : Γ(X, W)} {c : K}
    (hN : IsNilpotent (s - cst f W c)) (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hx : ptOf p ∈ W) : ev p hx s = c := by
  have h0 := (hN.map (ev p hx)).eq_zero
  rw [map_sub, ev_cst f p hp] at h0
  exact sub_eq_zero.mp h0

theorem res_cst (f : X ⟶ Spec (CommRingCat.of K)) {O O' : X.Opens} (h : O' ≤ O) (a : K) :
    res h (cst f O a) = cst f O' a := by
  rw [cst, cst, res_res]

theorem val_of_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∈ σ.U) :
    σ.val p = OnePoint.some (ev p h σ.f) := by
  unfold ToP1.val
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem val_of_not_mem (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (h : ptOf p ∉ σ.U) :
    σ.val p = OnePoint.infty := by
  unfold ToP1.val
  split_ifs with h'
  · exact absurd h' h
  · rfl

theorem ev_f_mul_g (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hU : ptOf p ∈ σ.U)
    (hV : ptOf p ∈ σ.V) : ev p hU σ.f * ev p hV σ.g = 1 := by
  have e := congrArg (ev p (show ptOf p ∈ σ.U ⊓ σ.V from ⟨hU, hV⟩)) σ.inv
  rw [map_mul, map_one] at e
  rw [← ev_res p (inf_le_left : σ.U ⊓ σ.V ≤ σ.U) ⟨hU, hV⟩,
    ← ev_res p (inf_le_right : σ.U ⊓ σ.V ≤ σ.V) ⟨hU, hV⟩]
  exact e

theorem ev_g_eq_zero (σ : ToP1 X) (p : Spec (CommRingCat.of K) ⟶ X) (hV : ptOf p ∈ σ.V)
    (hU : ptOf p ∉ σ.U) : ev p hV σ.g = 0 := by
  rw [ev_eq_zero_iff, σ.basicOpen_g]
  exact fun h => hU h.1

theorem mem_V_of_not_mem_U (σ : ToP1 X) {x : X} (hU : x ∉ σ.U) : x ∈ σ.V := by
  have hx : x ∈ (σ.U ⊔ σ.V : X.Opens) := by rw [σ.cover]; trivial
  rcases hx with h | h
  · exact absurd h hU
  · exact h

end Main

namespace ImagePlane

open Polynomial

section Gen

variable {K : Type} [Field K]

theorem ptOf_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of K) ⟶ Y) (h : Y ⟶ X) :
    ptOf (q ≫ h) = h.base (ptOf q) := rfl

/-- Values commute with pullback of sections. -/
theorem ev_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of K) ⟶ Y) (h : Y ⟶ X) {O : X.Opens}
    (hx : ptOf (q ≫ h) ∈ O) (s : Γ(X, O)) :
    ev (q ≫ h) hx s = ev q (show ptOf q ∈ h ⁻¹ᵁ O from hx) (h.app O s) := by
  simp only [ev, Scheme.evaluation, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (X.residue _ ≫ X.descResidueField (Scheme.stalkClosedPointTo (q ≫ h))).hom
      ((X.presheaf.germ O _ hx).hom s) =
    (Y.residue _ ≫ Y.descResidueField (Scheme.stalkClosedPointTo q)).hom
      ((Y.presheaf.germ (h ⁻¹ᵁ O) _ hx).hom (h.app O s))
  rw [Scheme.residue_descResidueField, Scheme.residue_descResidueField,
    Scheme.stalkClosedPointTo_comp]
  have key : ∀ (y : Y) (hy : h.base y ∈ O) (φ : Y.presheaf.stalk y ⟶ CommRingCat.of K),
      (h.stalkMap y ≫ φ).hom (X.presheaf.germ O (h.base y) hy s) =
        φ.hom (Y.presheaf.germ (h ⁻¹ᵁ O) y hy (h.app O s)) := by
    intro y hy φ
    rw [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  exact key (ptOf q) hx _

/-- The value of a global function on an affine scheme at `Spec.map φ`. -/
theorem ev_spec_top {R : Type} [CommRing R] (φ : CommRingCat.of R ⟶ CommRingCat.of K) (Q : R) :
    ev (Spec.map φ) (show ptOf (Spec.map φ) ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv Q) = φ Q := by
  rw [ev_top, ← ConcreteCategory.comp_apply, Scheme.ΓSpecIso_naturality]
  simp

/-- The point of `Spec.map φ` is the kernel of `φ`. -/
theorem ptOf_spec_asIdeal {R : Type} [CommRing R] (φ : CommRingCat.of R ⟶ CommRingCat.of K) :
    (ptOf (Spec.map φ)).asIdeal = RingHom.ker φ.hom := by
  change (PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint K)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal]
  show Ideal.comap φ.hom (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

end Gen

end ImagePlane

end Pin

end AV

end LeafQM

end

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 1: `HeckeFibreSizes` from three leaves on QM pairs and `TorsionStructure`

The count (computed in `fibre_sizes.py`): a twist fibre is the set of classes of
`(A, ι ∘ t_k, η)`, `k ∈ Fin 4`, `η` one of the `72` level structures on `(A, ι ∘ t_k)`.
`(A, ι ∘ t_k, η) ≅ (A, ι ∘ t_l, η')` iff some `φ : (A, ι ∘ t_k) ≅ (A, ι ∘ t_l)` carries `η` to
`η'`; distinct `φ` give distinct `η'` (Serre's lemma). So each class has `s · a` members, where
`a = |Aut(A, ι)|` and `s = #{m | (A, ι ∘ t_m) ≅ (A, ι)}`, and `n · s · a = 4 · 72 = 288`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRest

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.Exact LeafQM.AV.Pin.NormO PkgI3 TSHecke
open TSHeckeUnits
open scoped MonObj
open Classical

/-! ## The three leaves -/

/-- **Leaf (Shimura's classification of the centralizer of `ι(𝒪)`; units of imaginary quadratic
orders).** For an abelian surface `A` over `ℚ̄` with QM `ι : 𝒪 ↪ End(A)` by the maximal order of
the indefinite quaternion algebra `B = (2, −3)` of discriminant `6`, the centralizer
`End_𝒪(A) = com(ι)` is `ℤ` or an order in one imaginary quadratic field (Shimura, *On analytic
families of polarized abelian varieties and automorphic functions*, Ann. of Math. 78 (1963), and
the standard classification of `End⁰(A) ⊇ B`: `End⁰(A) = B` or `M₂(K)` with `K` imaginary
quadratic splitting `B`; e.g. Rotger, *Quaternions, polarizations and class numbers*, J. reine
angew. Math. 561 (2003), §2; locators UNVERIFIED). Consequences stated here: the automorphism
group of the pair, `com(ι)^×`, has `4` elements under CM by `ℤ[i]` (a maximal order, so
`com = ℤ[i]`), `6` under CM by `ℤ[ζ₃]`, and `2` (`±1`) otherwise; and no two of the three CM
types occur together (the three fields `ℚ(i)`, `ℚ(√−3)`, `ℚ(√−6)` are distinct). -/
def QMAutCard : Prop :=
  ∀ (A : AbVar Qbar), A.dim = 2 → ∀ q : QMStr A,
    Nat.card (QMIso q q) = (if HasCM4 q then 4 else if HasCM3 q then 6 else 2) ∧
    ¬ (HasCM4 q ∧ HasCM3 q) ∧ ¬ (HasCM4 q ∧ HasCM24 q) ∧ ¬ (HasCM3 q ∧ HasCM24 q)

/-- **Leaf (Serre's lemma, level 3).** An endomorphism of finite order of an abelian variety
over `ℚ̄` that fixes every `3`-torsion point is the identity (Serre's lemma in its finite-order
form: J.-P. Serre, *Rigidité du foncteur de Jacobi d'échelon n ≥ 3*, appendix to Sém. H. Cartan
13 (1960/61), exp. 17; Silverberg–Zarhin, J. Pure Appl. Algebra 111 (1996); Mumford,
*Abelian varieties*, §21, Theorem 5 is the polarized form; locators UNVERIFIED. Proof: `φ − 1`
kills `A[3]`, so `φ = 1 + 3β` with `β ∈ End(A)`; an eigenvalue `ζ ≠ 1` of the semisimple `φ`
would make `(ζ − 1)/3` integral). Stated over the kernel's genuine abelian varieties
`PkgI3.AbVar` and their `ℚ̄`-points. -/
def SerreRigidity3 : Prop :=
  ∀ (A : AbVar Qbar) (φ : AbVar.End A), (∃ m : ℕ, 0 < m ∧ φ ^ m = 1) →
    (∀ x : A.Pt Qbar, x ^ 3 = 1 → x ≫ φ.hom = x) → φ = 1

/-- **Leaf (fixed points of the Atkin–Lehner involutions on `X₆ = X₀^6(1)`).** The twists
`rep 1, rep 2, rep 3` (conjugation by `i, j, ij`, of reduced norms `−2, 3, −6`) represent
`w₂, w₃, w₆` (Rotger, *Modular Shimura varieties and forgetful maps*, Trans. AMS 356 (2004),
§§2-4; Ogg, *Real points on Shimura curves* (1983), fixed points of `w_m`; locators UNVERIFIED).
A pair isomorphic to its `w_m`-twist is a fixed point of `w_m`, hence a CM point by an order
containing `ℤ[μ]` for an elliptic `μ ∈ 𝒪` of norm `m`; by the embedding check of
`fibre_sizes.py` §5 (`ℚ(√−2)`, `ℚ(√−7)`, `ℚ(√−11)`, `ℚ(√−5)`, `ℚ(√−15)`, `ℚ(√−23)` do not
embed in `B`; for `m = 3` the field is `ℚ(√−3)` and `𝒪 ⊗ ℤ₂` is the maximal order of the
division algebra, so the CM order contains `ℤ[ζ₃]`) the CM is by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`. -/
def ALFixedPoints : Prop :=
  ∀ (A : AbVar Qbar), A.dim = 2 → ∀ q : QMStr A,
    (Nonempty (QMIso (q.twist (rep 1)) q) → HasCM4 q) ∧
    (Nonempty (QMIso (q.twist (rep 2)) q) → HasCM3 q) ∧
    (Nonempty (QMIso (q.twist (rep 3)) q) → HasCM24 q)

/-! ## Generalities on QM isomorphisms -/

section General

variable {K : Type} [Field K]

theorem qmIso_ext {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} {G G' : QMIso q q'}
    (h : G.φ.hom = G'.φ.hom) : G = G' := by
  have hφ : G.φ = G'.φ := AbVar.Hom.ext' h
  have hψ : G.ψ = G'.ψ := by
    apply AbVar.Hom.ext'
    calc G.ψ.hom = G.ψ.hom ≫ G'.φ.hom ≫ G'.ψ.hom := by rw [G'.left, Category.comp_id]
      _ = G.ψ.hom ≫ G.φ.hom ≫ G'.ψ.hom := by rw [h]
      _ = G'.ψ.hom := by rw [← Category.assoc, G.right, Category.id_comp]
  cases G; cases G'; cases hφ; cases hψ; rfl

/-- Re-index a QM isomorphism along `g0 : 𝒪 → 𝒪` (same underlying maps). -/
def qmCongr {A A' : AbVar K} {q₁ q₁' : QMStr A} {q₂ q₂' : QMStr A'} (G : QMIso q₁ q₂)
    (g0 : O → O) (h₁ : ∀ a, q₁'.iota a = q₁.iota (g0 a)) (h₂ : ∀ a, q₂'.iota a = q₂.iota (g0 a)) :
    QMIso q₁' q₂' where
  φ := G.φ
  ψ := G.ψ
  left := G.left
  right := G.right
  equivariant a := by rw [h₁, h₂]; exact G.equivariant (g0 a)

/-- `Aut(A, ι ∘ α) = Aut(A, ι)`. -/
def autTwistEquiv {A : AbVar K} (q : QMStr A) (α : O ≃+* O) :
    QMIso (q.twist α) (q.twist α) ≃ QMIso q q where
  toFun G := qmCongr G α.symm
    (fun a => by
      show q.iota a = q.iota (α (α.symm a))
      rw [RingEquiv.apply_symm_apply])
    (fun a => by
      show q.iota a = q.iota (α (α.symm a))
      rw [RingEquiv.apply_symm_apply])
  invFun G := qmCongr G α (fun _ => rfl) (fun _ => rfl)
  left_inv G := qmIso_ext rfl
  right_inv G := qmIso_ext rfl

/-- `Iso(q, q') ≃ Aut(q)` once one isomorphism is fixed. -/
def isoEquivAut {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (G₀ : QMIso q q') :
    QMIso q q ≃ QMIso q q' where
  toFun G := G.trans G₀
  invFun G := G.trans G₀.symm
  left_inv G := qmIso_ext (by
    show (G.φ.hom ≫ G₀.φ.hom) ≫ G₀.ψ.hom = G.φ.hom
    rw [Category.assoc, G₀.left, Category.comp_id])
  right_inv G := qmIso_ext (by
    show (G.φ.hom ≫ G₀.ψ.hom) ≫ G₀.φ.hom = G.φ.hom
    rw [Category.assoc, G₀.right, Category.comp_id])

/-- An automorphism of a pair with finitely many automorphisms has finite order in `End(A)`. -/
theorem exists_pow_eq_one {A : AbVar K} {q : QMStr A} [Finite (QMIso q q)] (θ : QMIso q q) :
    ∃ m : ℕ, 0 < m ∧ θ.φ ^ m = 1 := by
  let pw : ℕ → QMIso q q := fun n => Nat.rec (QMIso.refl q) (fun _ G => G.trans θ) n
  have hpw : ∀ n, (pw n).φ = θ.φ ^ n := by
    intro n
    induction n with
    | zero => exact AbVar.Hom.ext' rfl
    | succ n ih =>
      apply AbVar.Hom.ext'
      show (pw n).φ.hom ≫ θ.φ.hom = (θ.φ ^ (n + 1)).hom
      rw [pow_succ', end_mul_hom, ih]
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite pw
  have hu : IsUnit θ.φ := by
    refine ⟨⟨θ.φ, θ.ψ, AbVar.Hom.ext' ?_, AbVar.Hom.ext' ?_⟩, rfl⟩
    · show θ.ψ.hom ≫ θ.φ.hom = 𝟙 _
      exact θ.right
    · show θ.φ.hom ≫ θ.ψ.hom = 𝟙 _
      exact θ.left
  have hij' : θ.φ ^ i = θ.φ ^ j := by rw [← hpw, ← hpw, h]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have : θ.φ ^ i * θ.φ ^ (j - i) = θ.φ ^ i * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, hij']
    exact (hu.pow i).mul_left_cancel this
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have : θ.φ ^ j * θ.φ ^ (i - j) = θ.φ ^ j * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, hij']
    exact (hu.pow j).mul_left_cancel this

end General

/-! ## Level structures on a fixed pair: exactly `72`, indexed by `(𝒪/3𝒪)^×` -/

/-- Residues of nonzero reduced norm mod 3, i.e. `(𝒪/3𝒪)^×` in coordinates. -/
abbrev Good : Type := {c : Fin 4 → ZMod 3 // nrd3 c ≠ 0}

theorem card_good : Fintype.card Good = 72 := by decide +kernel

theorem tbl_unit (c : Good) : nrdC (tbl c.1) * nrdC (tbl c.1) = 1 := by
  rcases (tbl_spec c.1 c.2).2 with h | h <;> rw [h] <;> norm_num

/-- The table unit of `𝒪` reducing to `c`. -/
def uc (c : Good) : Oˣ := unitOf (tbl c.1) (nrdC (tbl c.1)) rfl (tbl_unit c)

theorem uc_congr (c : Good) : ∃ d : O, ((uc c : Oˣ) : O) - liftO c.1 = 3 * d := by
  obtain ⟨hred, -⟩ := tbl_spec c.1 c.2
  have hdvd : ∀ i, (3 : ℤ) ∣ tbl c.1 i - ((c.1 i).val : ℤ) := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
    rw [Int.cast_sub, hred i]
    simp
  refine ⟨⟨ofInt (fun i => (tbl c.1 i - ((c.1 i).val : ℤ)) / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  change ofInt (tbl c.1) - ofInt (fun i => ((c.1 i).val : ℤ)) = ((3 : O) : B) * ofInt _
  rw [h33, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact (Int.mul_ediv_cancel' (hdvd i)).symm

theorem liftO_inj3 {c c' : Fin 4 → ZMod 3} (h : ∃ d : O, liftO c - liftO c' = 3 * d) :
    c = c' := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨k, hk⟩ := d.2
  have h3 : ofInt (fun i => ((c i).val : ℤ)) - ofInt (fun i => ((c' i).val : ℤ)) =
      3 * ofInt k := by
    have := congrArg Subtype.val hd
    have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
    simp only [liftO, hk, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33] at this
    exact this
  rw [ofInt_sub, three_mul_ofInt] at h3
  have h4 := ofInt_injective h3
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.sub_apply] at h5
  have h6 : (((c i).val : ℤ) : ZMod 3) - (((c' i).val : ℤ) : ZMod 3) = 0 := by
    rw [← Int.cast_sub, h5]; push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  simpa [sub_eq_zero] using h6

theorem sub_liftO_coord (n : Fin 4 → ℤ) (u : O) (hu : (u : B) = ofInt n) :
    ∃ d : O, u - liftO (fun i => (n i : ZMod 3)) = 3 * d := by
  refine ⟨⟨ofInt (fun i => n i / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [liftO, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33]
  rw [hu, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast]
  have := Int.emod_def (n i) 3
  omega

/-- An element of `𝒪` invertible mod `3𝒪` has reduced norm `≢ 0 mod 3` (the argument of
`TSHeckeUnits.exists_unit_congr`). -/
theorem nrd3_ne_zero_of_inv (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) (nu : Fin 4 → ℤ)
    (hnu : (u₀ : B) = ofInt nu) : nrd3 (fun i => (nu i : ZMod 3)) ≠ 0 := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have h1 : ((1 : O) : B) = ofInt ![1, 0, 0, 0] := by rw [ofInt_one]; rfl
  have hcoord : mulCoord nv nu - ![1, 0, 0, 0] = fun i => 3 * nc i := by
    apply ofInt_injective
    rw [← ofInt_sub, ← ofInt_mul, ← three_mul_ofInt, ← hnu, ← hnv, ← hnc, ← h1, ← h33]
    exact congrArg Subtype.val hc
  have hn1 : ((nrdC (mulCoord nv nu) : ℤ) : ZMod 3) = 1 := by
    have : mulCoord nv nu = fun i => ![1, 0, 0, 0] i + 3 * nc i := by
      funext i
      have := congrFun hcoord i
      simp only [Pi.sub_apply] at this
      linarith
    rw [this, nrdC_cast]
    simp only [nrd3]
    simp [show (3 : ZMod 3) = 0 from rfl]
  intro h0
  rw [nrdC_mul, Int.cast_mul, nrdC_cast nu, h0, mul_zero] at hn1
  exact zero_ne_one hn1

/-- The level structure `η ∘ (· u_c)` on the pair of `P`. -/
def lv (P : QML3 Qbar) (c : Good) : Level3 P.q := P.e.rightMul (uc c)

theorem lv_eta (P : QML3 Qbar) (c : Good) (a : O) :
    (lv P c).eta a = P.e.eta (a * ((uc c : Oˣ) : O)) := rfl

theorem lv_injective (P : QML3 Qbar) : Function.Injective (lv P) := by
  intro c c' h
  have h1 : P.e.eta (1 * ((uc c : Oˣ) : O)) = P.e.eta (1 * ((uc c' : Oˣ) : O)) := by
    rw [← lv_eta, ← lv_eta, h]
  rw [_root_.one_mul, _root_.one_mul, P.e.eq_iff] at h1
  obtain ⟨d, hd⟩ := h1
  obtain ⟨d1, h1'⟩ := uc_congr c
  obtain ⟨d2, h2'⟩ := uc_congr c'
  apply Subtype.ext
  apply liftO_inj3
  refine ⟨d - d1 + d2, ?_⟩
  rw [mul_add, mul_sub, ← hd, ← h1', ← h2']
  abel

theorem lv_surjective (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) :
    Function.Surjective (lv P) := by
  intro et
  obtain ⟨u₀, v₀, hinv, hu⟩ := Level3.torsor hT P et
  obtain ⟨nu, hnu⟩ := u₀.2
  have hgood := nrd3_ne_zero_of_inv u₀ v₀ hinv nu hnu
  obtain ⟨d, hd⟩ := sub_liftO_coord nu u₀ hnu
  refine ⟨⟨_, hgood⟩, Level3.ext' (AddMonoidHom.ext fun a => ?_)⟩
  rw [lv_eta, hu a, P.e.eq_iff]
  obtain ⟨d1, h1⟩ := uc_congr ⟨_, hgood⟩
  refine ⟨a * d1 - a * d, ?_⟩
  calc a * ((uc ⟨_, hgood⟩ : Oˣ) : O) - a * u₀
      = a * (((uc ⟨_, hgood⟩ : Oˣ) : O) - liftO (fun i => (nu i : ZMod 3))) -
        a * (u₀ - liftO (fun i => (nu i : ZMod 3))) := by noncomm_ring
    _ = a * (3 * d1) - a * (3 * d) := by rw [h1, hd]
    _ = 3 * (a * d1 - a * d) := by noncomm_ring

/-- **The level structures on a fixed pair over `ℚ̄`: `72` of them** (given `TorsionStructure`). -/
def lvEquiv (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) : Good ≃ Level3 P.q :=
  Equiv.ofBijective (lv P) ⟨lv_injective P, lv_surjective hT P⟩

/-! ## The twisted pairs `ι ∘ t_k` and their composition law -/

/-- `t_k ∘ t_l = t_{k ⊕ l}` (the group `W = (ℤ/2)²`). -/
def xr (k l : Fin 4) : Fin 4 := ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] k l

theorem xr_xr_left (k l : Fin 4) : xr k (xr k l) = l := by revert k l; decide
theorem xr_xr_right (k l : Fin 4) : xr (xr k l) l = k := by revert k l; decide
theorem xr_self (l : Fin 4) : xr l l = 0 := by revert l; decide

/-- The values `1, i, j, k` of the representatives `tt`. -/
def ttv : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem tt_val (k : Fin 4) : ((tt k : Bˣ) : B) = ttv k := by
  fin_cases k
  · ext <;> simp [tt, ttv]
  · change ofInt ei = _
    ext <;> simp [ofInt, ei, ttv]
  · change ofInt ej = _
    ext <;> simp [ofInt, ej, ttv]
  · change ofInt ei * ofInt ej = _
    ext <;> simp [ofInt, ei, ej, ttv]

theorem ttv_mul : ∀ k l : Fin 4, ∃ c : ℚ, c ≠ 0 ∧ ttv k * ttv l = algebraMap ℚ B c * ttv (xr k l)
  | 0, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 0, 1 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 0, 2 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 0, 3 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 1 => ⟨2, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 2 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 3 => ⟨2, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 1 => ⟨-1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 2 => ⟨-3, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 3 => ⟨3, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 1 => ⟨-2, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 2 => ⟨-3, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 3 => ⟨6, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩

theorem tt_mul (k l : Fin 4) : ∃ c : ℚ, c ≠ 0 ∧
    ((tt k : Bˣ) : B) * ((tt l : Bˣ) : B) = algebraMap ℚ B c * ((tt (xr k l) : Bˣ) : B) := by
  rw [tt_val, tt_val, tt_val]
  exact ttv_mul k l

theorem conj_conj (u v w : Bˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (u : B) * (v : B) = algebraMap ℚ B c * (w : B)) (a : B) :
    (u : B) * ((v : B) * a * ((v⁻¹ : Bˣ) : B)) * ((u⁻¹ : Bˣ) : B) =
      (w : B) * a * ((w⁻¹ : Bˣ) : B) := by
  have hC'C : algebraMap ℚ B c⁻¹ * algebraMap ℚ B c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  set x := (u : B) * ((v : B) * a * ((v⁻¹ : Bˣ) : B)) * ((u⁻¹ : Bˣ) : B) with hx
  have h1 : x * ((u : B) * (v : B)) = ((u : B) * (v : B)) * a := by
    simp only [hx, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  rw [h] at h1
  have h2 : algebraMap ℚ B c * (x * w) = algebraMap ℚ B c * ((w : B) * a) := by
    rw [← mul_assoc, Algebra.commutes, mul_assoc, h1, mul_assoc]
  have h3 : x * w = (w : B) * a := by
    have := congrArg (fun y => algebraMap ℚ B c⁻¹ * y) h2
    simp only [← mul_assoc, hC'C, one_mul] at this
    exact this
  calc x = x * (w : B) * ((w⁻¹ : Bˣ) : B) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (w : B) * a * ((w⁻¹ : Bˣ) : B) := by rw [h3]

theorem rep_rep (k l : Fin 4) (a : O) : rep k (rep l a) = rep (xr k l) a := by
  obtain ⟨c, hc, h⟩ := tt_mul k l
  apply Subtype.ext
  simp only [rep, conjO_apply]
  exact conj_conj _ _ _ c hc h a

theorem rep_zero (a : O) : rep 0 a = a := by
  apply Subtype.ext
  simp only [rep, conjO_apply]
  simp [tt]

/-! ## The count -/

section Count

variable (P : QML3 Qbar)

/-- The object `(A, ι ∘ t_k, η ∘ t_k)`. -/
abbrev Pk (k : Fin 4) : QML3 Qbar := P.twist (rep k)

/-- `(k, c) ↦` the class of `(A, ι ∘ t_k, et_k ∘ (· u_c))`. -/
def Ψ (x : Fin 4 × Good) : M3 Qbar :=
  M3.mk ⟨P.A, P.surface, (Pk P x.1).q, lv (Pk P x.1) x.2⟩

/-- `Rk k l`: the pairs `ι ∘ t_k` and `ι ∘ t_l` are isomorphic. -/
def Rk (k l : Fin 4) : Prop := Nonempty (QMIso (Pk P k).q (Pk P l).q)

/-- `a = |Aut(A, ι)|`. -/
def aP : ℕ := Nat.card (QMIso P.q P.q)

/-- `s = #{m | (A, ι ∘ t_m) ≅ (A, ι)}`. -/
def sP : ℕ := (Finset.univ.filter fun m : Fin 4 => Nonempty (QMIso (P.q.twist (rep m)) P.q)).card

theorem range_Ψ (hT : ObjBridge.TorsionStructure) : Set.range (Ψ P) = twistFibre P := by
  ext c
  constructor
  · rintro ⟨⟨k, d⟩, rfl⟩
    exact ⟨⟨P.A, P.surface, (Pk P k).q, lv (Pk P k) d⟩, rfl, rep k, ⟨QMIso.refl _⟩⟩
  · rintro ⟨Q, rfl, α, ⟨g⟩⟩
    obtain ⟨k, v, hv⟩ := rep_cover α
    let G : QMIso (Pk P k).q Q.q := (innerIso P.q (rep k) α v hv).symm.trans g
    obtain ⟨d, hd⟩ := lv_surjective hT (Pk P k) (pullLevel G Q.e)
    refine ⟨(k, d), ?_⟩
    exact (congrArg (fun e : Level3 (Pk P k).q =>
      M3.mk (⟨P.A, P.surface, (Pk P k).q, e⟩ : QML3 Qbar)) hd).trans
      (Quotient.sound ⟨pullIso P.surface Q.surface G Q.e⟩)

theorem rk_iff (k l : Fin 4) :
    Rk P k l ↔ Nonempty (QMIso (P.q.twist (rep (xr k l))) P.q) := by
  constructor
  · rintro ⟨G⟩
    refine ⟨qmCongr G (rep l) (fun a => ?_) (fun a => ?_)⟩
    · show P.q.iota (rep (xr k l) a) = P.q.iota (rep k (rep l a))
      rw [rep_rep]
    · show P.q.iota a = P.q.iota (rep l (rep l a))
      rw [rep_rep, xr_self, rep_zero]
  · rintro ⟨G⟩
    refine ⟨qmCongr G (rep l) (fun a => ?_) (fun _ => rfl)⟩
    show P.q.iota (rep k a) = P.q.iota (rep (xr k l) (rep l a))
    rw [rep_rep, xr_xr_right]

theorem card_rk (k : Fin 4) : (Finset.univ.filter (Rk P k)).card = sP P := by
  apply Finset.card_nbij' (xr k) (xr k)
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl ⊢
    exact (rk_iff P k l).1 hl
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢
    rw [rk_iff, xr_xr_left]
    exact hm
  · intro l _
    exact xr_xr_left k l
  · intro m _
    exact xr_xr_left k m

theorem finite_aut_k (hfin : Finite (QMIso P.q P.q)) (k : Fin 4) :
    Finite (QMIso (Pk P k).q (Pk P k).q) :=
  Finite.of_equiv _ (autTwistEquiv P.q (rep k)).symm

theorem card_iso (k l : Fin 4) :
    Nat.card (QMIso (Pk P k).q (Pk P l).q) = if Rk P k l then aP P else 0 := by
  split_ifs with h
  · obtain ⟨G₀⟩ := h
    exact (Nat.card_congr (isoEquivAut G₀)).symm.trans (Nat.card_congr (autTwistEquiv P.q (rep k)))
  · haveI : IsEmpty (QMIso (Pk P k).q (Pk P l).q) := ⟨fun G => h ⟨G⟩⟩
    exact Nat.card_of_isEmpty

theorem finite_iso (hfin : Finite (QMIso P.q P.q)) (k l : Fin 4) :
    Finite (QMIso (Pk P k).q (Pk P l).q) := by
  by_cases h : Rk P k l
  · obtain ⟨G₀⟩ := h
    haveI := finite_aut_k P hfin k
    exact Finite.of_equiv _ (isoEquivAut G₀)
  · haveI : IsEmpty (QMIso (Pk P k).q (Pk P l).q) := ⟨fun G => h ⟨G⟩⟩
    infer_instance

/-- Push a level structure forward along a QM isomorphism. -/
def push {A : AbVar Qbar} {q₁ q₂ : QMStr A} (φ : QMIso q₁ q₂) (et : Level3 q₁) : Level3 q₂ :=
  pullLevel φ.symm et

theorem push_eta {A : AbVar Qbar} {q₁ q₂ : QMStr A} (φ : QMIso q₁ q₂) (et : Level3 q₁) (a : O) :
    (push φ et).eta a = Additive.ofMul (Additive.toMul (et.eta a) ≫ φ.φ.hom) := rfl

/-- **Freeness (Serre's lemma)**: distinct isomorphisms push a level structure to distinct
level structures. -/
theorem push_injective (hT : ObjBridge.TorsionStructure) (hS : SerreRigidity3) (X : QML3 Qbar)
    [Finite (QMIso X.q X.q)] {q₂ : QMStr X.A} (φ φ' : QMIso X.q q₂)
    (h : push φ X.e = push φ' X.e) : φ = φ' := by
  let θ : QMIso X.q X.q := φ.trans φ'.symm
  have hθ : θ.φ.hom = φ.φ.hom ≫ φ'.ψ.hom := rfl
  have hfix : ∀ a, Additive.toMul (X.e.eta a) ≫ θ.φ.hom = Additive.toMul (X.e.eta a) := by
    intro a
    have h1 : Additive.toMul (X.e.eta a) ≫ φ.φ.hom = Additive.toMul (X.e.eta a) ≫ φ'.φ.hom := by
      have := congrArg (fun e : Level3 q₂ => Additive.toMul (e.eta a)) h
      exact this
    rw [hθ, ← Category.assoc, h1, Category.assoc, φ'.left, Category.comp_id]
  have htors : ∀ x : X.A.Pt Qbar, x ^ 3 = 1 → x ≫ θ.φ.hom = x := by
    intro x hx
    have hx' : bcPt X.A x ^ 3 = 1 := by
      rw [bcPt, ← MonObj.comp_pow, hx]
      exact MonObj.comp_one _
    obtain ⟨a, ha⟩ := Level3.onto hT X (bcPt X.A x) hx'
    have := bcPt_injective X.A ha
    rw [← this]
    exact hfix a
  have h1 : θ.φ = 1 := hS X.A θ.φ (exists_pow_eq_one θ) htors
  have h2 : φ.φ.hom ≫ φ'.ψ.hom = 𝟙 _ := by
    rw [← hθ, h1]; rfl
  apply qmIso_ext
  calc φ.φ.hom = φ.φ.hom ≫ φ'.ψ.hom ≫ φ'.φ.hom := by rw [φ'.right, Category.comp_id]
    _ = φ'.φ.hom := by rw [← Category.assoc, h2, Category.id_comp]

/-- **The fibre of `Ψ` through `(k, c)` has `s · a` elements.** -/
theorem fibre_card (hT : ObjBridge.TorsionStructure) (hS : SerreRigidity3)
    (hfin : Finite (QMIso P.q P.q)) (x : Fin 4 × Good) :
    Nat.card {y : Fin 4 × Good // Ψ P y = Ψ P x} = sP P * aP P := by
  obtain ⟨k, c⟩ := x
  let et : Level3 (Pk P k).q := lv (Pk P k) c
  let X : QML3 Qbar := ⟨P.A, P.surface, (Pk P k).q, et⟩
  haveI : Finite (QMIso X.q X.q) := finite_aut_k P hfin k
  haveI : ∀ l, Finite (QMIso (Pk P k).q (Pk P l).q) := finite_iso P hfin k
  let f : (Σ l : Fin 4, QMIso (Pk P k).q (Pk P l).q) → {y : Fin 4 × Good // Ψ P y = Ψ P (k, c)} :=
    fun z => ⟨(z.1, (lvEquiv hT (Pk P z.1)).symm (push z.2 et)), by
      have : lv (Pk P z.1) ((lvEquiv hT (Pk P z.1)).symm (push z.2 et)) = push z.2 et :=
        (lvEquiv hT (Pk P z.1)).apply_symm_apply _
      exact (congrArg (fun e : Level3 (Pk P z.1).q =>
        M3.mk (⟨P.A, P.surface, (Pk P z.1).q, e⟩ : QML3 Qbar)) this).trans
        (Quotient.sound ⟨pullIso P.surface P.surface z.2.symm et⟩)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨l, φ⟩ ⟨l', φ'⟩ hz
      have h1 := congrArg (fun y => y.1.1) hz
      simp only [f] at h1
      subst h1
      have h2 := congrArg (fun y => y.1.2) hz
      simp only [f] at h2
      have h3 : push φ et = push φ' et := (lvEquiv hT (Pk P l)).symm.injective h2
      have := push_injective hT hS X φ φ' h3
      subst this
      rfl
    · rintro ⟨⟨l, d⟩, hy⟩
      have hy' : Quotient.mk (isoSetoid Qbar)
          (⟨P.A, P.surface, (Pk P l).q, lv (Pk P l) d⟩ : QML3 Qbar) =
          Quotient.mk (isoSetoid Qbar) X := hy
      have hI : Nonempty (QML3.Iso (⟨P.A, P.surface, (Pk P l).q, lv (Pk P l) d⟩ : QML3 Qbar) X) :=
        Quotient.exact hy'
      obtain ⟨I⟩ := hI
      let J := I.symm
      let φ : QMIso (Pk P k).q (Pk P l).q := ⟨J.φ, J.ψ, J.left, J.right, J.equivariant⟩
      refine ⟨⟨l, φ⟩, Subtype.ext ?_⟩
      show (l, (lvEquiv hT (Pk P l)).symm (push φ et)) = (l, d)
      congr 1
      rw [Equiv.symm_apply_eq]
      apply Level3.ext'
      apply AddMonoidHom.ext
      intro a
      exact J.level a
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_sigma]
  simp only [card_iso]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, card_rk]

/-- **The count**: `#(twist fibre) · s · a = 4 · 72 = 288`. -/
theorem ncard_mul (hT : ObjBridge.TorsionStructure) (hS : SerreRigidity3)
    (hfin : Finite (QMIso P.q P.q)) :
    (twistFibre P).ncard * (sP P * aP P) = 288 := by
  have hcard : (Finset.univ : Finset (Fin 4 × Good)).card = 288 := by
    rw [Finset.card_univ, Fintype.card_prod, card_good, Fintype.card_fin]
  have hsum := Finset.card_eq_sum_card_image (Ψ P) (Finset.univ : Finset (Fin 4 × Good))
  have hterm : ∀ y ∈ (Finset.univ : Finset (Fin 4 × Good)).image (Ψ P),
      (Finset.univ.filter (fun z => Ψ P z = y)).card = sP P * aP P := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← fibre_card P hT hS hfin x, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hcard] at hsum
  have himg : twistFibre P = ↑((Finset.univ : Finset (Fin 4 × Good)).image (Ψ P)) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, range_Ψ P hT]
  rw [himg, Set.ncard_coe_finset]
  exact hsum.symm

end Count

/-! ## `HeckeFibreSizes` -/

theorem sP_pos (P : QML3 Qbar) : 1 ≤ sP P := by
  apply Finset.card_pos.2
  refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨qmCongr (QMIso.refl P.q) id
    (fun a => ?_) (fun _ => rfl)⟩⟩⟩
  show P.q.iota (rep 0 a) = P.q.iota a
  rw [rep_zero]

theorem sP_le (P : QML3 Qbar) (m₀ : Fin 4)
    (h : ∀ m : Fin 4, m ≠ 0 → m ≠ m₀ → Nonempty (QMIso (P.q.twist (rep m)) P.q) → False) :
    sP P ≤ 2 := by
  calc sP P ≤ ({0, m₀} : Finset (Fin 4)).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter] at hm
        by_cases h0 : m = 0
        · simp [h0]
        by_cases h1 : m = m₀
        · simp [h1]
        exact (h m h0 h1 hm.2).elim
    _ ≤ 2 := Finset.card_le_two

theorem sP_eq_one (P : QML3 Qbar)
    (h : ∀ m : Fin 4, m ≠ 0 → Nonempty (QMIso (P.q.twist (rep m)) P.q) → False) :
    sP P = 1 := by
  apply le_antisymm _ (sP_pos P)
  calc sP P ≤ ({0} : Finset (Fin 4)).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter] at hm
        by_cases h0 : m = 0
        · simp [h0]
        exact (h m h0 hm.2).elim
    _ = 1 := Finset.card_singleton _

/-- **`HeckeFibreSizes` from the leaves** `QMAutCard`, `SerreRigidity3`, `ALFixedPoints` and the
kernel's `TorsionStructure` (with `M = 144`). -/
theorem heckeFibreSizes_of (hT : ObjBridge.TorsionStructure) (hA : QMAutCard)
    (hS : SerreRigidity3) (hW : ALFixedPoints) : HeckeFibreSizes := by
  have key : ∀ P : QML3 Qbar, (twistFibre P).ncard * (sP P * aP P) = 288 ∧
      aP P = (if HasCM4 P.q then 4 else if HasCM3 P.q then 6 else 2) ∧
      ¬ (HasCM4 P.q ∧ HasCM3 P.q) ∧ ¬ (HasCM4 P.q ∧ HasCM24 P.q) ∧
      ¬ (HasCM3 P.q ∧ HasCM24 P.q) := by
    intro P
    obtain ⟨ha, hx⟩ := hA P.A P.surface P.q
    have hpos : 0 < Nat.card (QMIso P.q P.q) := by
      rw [ha]; split_ifs <;> norm_num
    haveI : Finite (QMIso P.q P.q) := (Nat.card_pos_iff.1 hpos).2
    exact ⟨ncard_mul P hT hS inferInstance, ha, hx⟩
  have hAL := fun P : QML3 Qbar => hW P.A P.surface P.q
  refine ⟨144, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨h, ha, -⟩ := key P
    have hs := sP_pos P
    have ha2 : 2 ≤ aP P := by rw [ha]; split_ifs <;> norm_num
    have : 2 ≤ sP P * aP P := le_trans ha2 (Nat.le_mul_of_pos_left _ hs)
    nlinarith
  · intro P h4 h3 h24
    obtain ⟨h, ha, -⟩ := key P
    rw [if_neg h4, if_neg h3] at ha
    have hs : sP P = 1 := sP_eq_one P (fun m hm hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact h4 (w1 hI)
      · exact h3 (w2 hI)
      · exact h24 (w3 hI))
    rw [hs, ha] at h
    omega
  · intro P h4
    obtain ⟨h, ha, -, x2, -⟩ := key P
    rw [if_pos h4] at ha
    have hs := sP_pos P
    have hs2 : sP P ≤ 2 := sP_le P 1 (fun m hm hm1 hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact hm1 rfl
      · exact (key P).2.2.1 ⟨h4, w2 hI⟩
      · exact x2 ⟨h4, w3 hI⟩)
    rw [ha] at h
    interval_cases (sP P) <;> omega
  · intro P h3
    obtain ⟨h, ha, x1, -, x3⟩ := key P
    rw [if_neg (fun h4 => x1 ⟨h4, h3⟩), if_pos h3] at ha
    have hs := sP_pos P
    have hs2 : sP P ≤ 2 := sP_le P 2 (fun m hm hm2 hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact x1 ⟨w1 hI, h3⟩
      · exact hm2 rfl
      · exact x3 ⟨h3, w3 hI⟩)
    rw [ha] at h
    interval_cases (sP P) <;> omega
  · intro P h24
    obtain ⟨h, ha, -, x2, x3⟩ := key P
    rw [if_neg (fun h4 => x2 ⟨h4, h24⟩), if_neg (fun h3 => x3 ⟨h3, h24⟩)] at ha
    have hs := sP_pos P
    have hs2 : sP P ≤ 2 := sP_le P 3 (fun m hm hm3 hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact x2 ⟨w1 hI, h24⟩
      · exact x3 ⟨w2 hI, h24⟩
      · exact hm3 rfl)
    rw [ha] at h
    interval_cases (sP P) <;> omega

end HeckeRest

end

#print axioms HeckeRest.heckeFibreSizes_of
#print axioms HeckeRest.ncard_mul

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 2: `HeckeNoVertRam` reduced to one unramified vertical prime

`NoVerticalRam E p` asks every prime of `B = ` (integral closure of `ℤ[X]` in `E`) over `p ℤ[X]`
to have ramification index `1`. For `E/ℚ(X)` Galois, `Gal(E/ℚ(X))` acts on `B` and permutes the
primes over `p ℤ[X]` transitively, preserving ramification indices; so one such prime with
`e = 1` suffices (`noVerticalRam_of_witness`, compiled). What is left (`HeckeVertWitness`) is the
existence, for the Hecke cover and `p > 324`, of one vertical prime with `e = 1`: the valuation
of `E` at the generic point of a component of the special fibre of a smooth model of `Y₃` over
`ℤ_(p)` (good reduction, Morita; see docs/research/hecke-rest.md §3).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestNV

open Polynomial G0ModField PropTSRed PropTSGlue
open CategoryTheory AlgebraicGeometry Limits LeafQM.AV

/-! ## Galois transitivity on the primes of an integral closure -/

section Generic

variable {A F E : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [IsGalois F E]

include F in
/-- **Primes of the integral closure over the same prime have the same ramification index**
(Galois case; `A` an integrally closed domain, not necessarily Dedekind). -/
theorem ramIdx_eq_of_under_eq (Q₀ Q : Ideal (integralClosure A E)) [Q₀.IsPrime] [Q.IsPrime]
    (h : Q₀.under A = Q.under A) : Q.ramificationIdx A = Q₀.ramificationIdx A := by
  have hinjAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  haveI : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAE
  haveI : IsFractionRing (integralClosure A E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F E _
  haveI : SMulCommClass Gal(E/F) A E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A F E, AlgEquiv.commutes]⟩
  haveI : IsGaloisGroup Gal(E/F) A (integralClosure A E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/F) A (integralClosure A E) F E
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq A (integralClosure A E) Gal(E/F) Q₀ Q h
  rw [hg, Ideal.ramificationIdx_smul]

end Generic

/-! ## `ℚ(X)` is the fraction field of `ℤ[X]` -/

/-- `ℤ[X] → ℚ(X)` through `ℚ[X]`. -/
@[reducible] def intRatAlg : Algebra ℤ[X] (RatFunc ℚ) :=
  ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))).toAlgebra

theorem isFractionRing_int : letI := intRatAlg; IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI := intRatAlg
  have e : ∀ g : ℤ[X], algebraMap ℤ[X] (RatFunc ℚ) g =
      algebraMap ℚ[X] (RatFunc ℚ) (g.map (Int.castRingHom ℚ)) := fun g => rfl
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := by
    intro a b hab
    rw [e, e] at hab
    exact Polynomial.map_injective _ Int.cast_injective (IsFractionRing.injective ℚ[X] _ hab)
  haveI : FaithfulSMul ℤ[X] (RatFunc ℚ) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field ℤ[X] (RatFunc ℚ) fun z => ?_
  obtain ⟨bN, hbNm, hN⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (RatFunc.num z)
  obtain ⟨bD, hbDm, hD⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (RatFunc.denom z)
  set gN := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (RatFunc.num z)
  set gD := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (RatFunc.denom z)
  have hbN : (bN : ℚ) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hbNm)
  have hbD : (bD : ℚ) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hbDm)
  have hmapN : gN.map (Int.castRingHom ℚ) = C (bN : ℚ) * RatFunc.num z := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hN, zsmul_eq_mul]
    simp
  have hmapD : gD.map (Int.castRingHom ℚ) = C (bD : ℚ) * RatFunc.denom z := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hD, zsmul_eq_mul]
    simp
  refine ⟨C bD * gN, C bN * gD, ?_⟩
  rw [e, e, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hmapN,
    hmapD]
  set c : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) (C (bD : ℚ) * C (bN : ℚ))
  have hc : c ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] _), ← C_mul, C_eq_zero]
    exact mul_ne_zero hbD hbN
  have h1 : algebraMap ℚ[X] (RatFunc ℚ)
      (C ((Int.castRingHom ℚ) bD) * (C (bN : ℚ) * RatFunc.num z)) =
      c * algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num z) := by
    rw [← map_mul]; congr 1; simp only [eq_intCast]; ring
  have h2 : algebraMap ℚ[X] (RatFunc ℚ)
      (C ((Int.castRingHom ℚ) bN) * (C (bD : ℚ) * RatFunc.denom z)) =
      c * algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom z) := by
    rw [← map_mul]; congr 1; simp only [eq_intCast]; ring
  rw [h1, h2, mul_div_mul_left _ _ hc, RatFunc.num_div_denom]

/-! ## The reduction -/

/-- **Glue (arithmetic input of Lemma NV / good reduction): one unramified vertical prime.**
Some prime of the integral closure of `ℤ[X]` in `E` over `p ℤ[X]` has ramification index `1`. -/
def VertUnramWitness (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∃ Q : Ideal (integralClosure ℤ[X] E), Q.IsPrime ∧ Q.under ℤ[X] = vertPrime p ∧
    Q.ramificationIdx ℤ[X] = 1

/-- **One unramified vertical prime gives no vertical ramification** (Galois case; compiled). -/
theorem noVerticalRam_of_witness (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (p : ℕ) (h : VertUnramWitness E p) : NoVerticalRam E p := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  obtain ⟨Q₀, hQ₀, hu₀, he₀⟩ := h
  intro Q hQ hu
  rw [ramIdx_eq_of_under_eq (F := RatFunc ℚ) Q₀ Q (hu₀.trans hu.symm), he₀]

/-- **Glue (h-b1 §3 Lemma NV, or good reduction of `Y₃` at `p ∤ 6`): one unramified vertical
prime for the Hecke cover.** For a triple with R1fp, R1hecke, R2fp and any `E` carrying the
normalization chart, for every prime `p > 324` some prime of the integral closure of `ℤ[X]` in
`E` over `p ℤ[X]` is unramified. *Route GR* (STANDARD inputs, locators UNVERIFIED): `Y₃` has a
smooth proper model `𝒴` over `ℤ_(p)` (Morita 1981; Carayol 1986); `π` is regular at the generic
point `ξ` of a component of the special fibre with nonconstant reduction (the tame quotient of
`𝒴` by `Γ'` is `P¹_{ℤ_(p)}` in the coordinate `j`); the local ring `𝒪_{𝒴,ξ}` is a DVR of
`E = ℚ(Y₃)` with uniformizer `p` (reduced special fibre) containing `ℤ[X]`, so its centre on the
integral closure is a vertical prime with `e = 1`. *Route NV*: h-b1 §3 (tameness, unramified
branch fibres, Abhyankar at `(p, X − b)`, the `W`-quotient). Glue, not a leaf. -/
def HeckeVertWitness : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p → VertUnramWitness E p

/-- **`HeckeNoVertRam` from one unramified vertical prime** (compiled). -/
theorem heckeNoVertRam_of_witness (h : HeckeVertWitness) : HeckeNoVertRam := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324
  exact noVerticalRam_of_witness E p (h Y Φ π h1 hh h2 E hN p hp hp324)

end HeckeRestNV

end

#print axioms HeckeRestNV.ramIdx_eq_of_under_eq
#print axioms HeckeRestNV.isFractionRing_int
#print axioms HeckeRestNV.heckeNoVertRam_of_witness

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3: `CurveNormChart` from `ChartFinite` and `ChartNormal`

`CurveNormChart` asks for a finite `E/ℚ(X)` with an open immersion `Spec B → Y`
(`B = ` integral closure of `ℚ[X]` in `E`) through which every `ℚ̄`-point with `π ≠ ∞` factors and
along which `π` is the coordinate `X`. Given that `U = π⁻¹(𝔸¹)` is affine with `Γ(Y, U)` a finite
`ℚ[X]`-algebra via `X ↦ π.f` (`ChartFinite`) and a normal domain (`ChartNormal`), the field
`E = Frac Γ(Y, U)` does it: `Γ(Y, U)` is the integral closure of `ℚ[X]` in `E`, and the chart is
`Spec B ≅ Spec Γ(Y, U) ≅ U ⊆ Y` (compiled below).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- `ℚ → Γ(Y, U)` through the structure morphism `Y → Spec ℚ`. -/
def cQ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens) : ℚ →+* Γ(Y.left, U) :=
  (res (le_top : U ≤ ⊤)).comp
    ((Y.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom)

/-- `ℚ[X] → Γ(Y, π⁻¹(𝔸¹))`, `X ↦ π.f` (the chart of `π` over `𝔸¹` on rings). -/
def chartHom (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : ℚ[X] →+* Γ(Y.left, π.U) :=
  Polynomial.eval₂RingHom (cQ Y π.U) π.f

/-- **Glue (curve theory: `π` is finite over `𝔸¹`).** For a proper smooth irreducible curve `Y/ℚ`
and `π : Y → P¹` with finite `ℚ̄`-fibres, `U = π⁻¹(𝔸¹)` is a nonempty affine open and `Γ(Y, U)` is
a finite `ℚ[X]`-algebra via `X ↦ π.f`, with `ℚ[X] → Γ(Y, U)` injective. *Proof* (STANDARD;
Hartshorne II.6.8 and Ex. II.3.5, Stacks 02OG (= Mathlib's
`IsFinite.of_isProper_of_locallyQuasiFinite`), 01WN; locators UNVERIFIED): `U → 𝔸¹` is proper
(valuative criterion: a valuation-ring point of `Y` over `𝔸¹` cannot meet `π = ∞`, since `f g = 1`
on `U ∩ V`) and quasi-finite (closed fibres: finite `ℚ̄`-fibres; generic fibre: the generic point
of `Y`), hence finite (Zariski's main theorem), hence affine; it is surjective onto `𝔸¹` (finite and
dominant), so `ℚ[X] → Γ(Y, U)` is injective. Glue, not a leaf. -/
def ChartFinite : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    IsAffineOpen π.U ∧ (π.U : Set Y.left).Nonempty ∧ Function.Injective (chartHom Y π) ∧
      @Module.Finite ℚ[X] Γ(Y.left, π.U) _ _ (chartHom Y π).toAlgebra.toModule

/-- **Glue (smooth curves are normal).** On a smooth irreducible curve `Y/ℚ`, the sections over a
nonempty affine open form an integrally closed domain. *Proof* (STANDARD; Hartshorne I.6,
II.6.2A, Stacks 033B/0567; locators UNVERIFIED): `Y` is reduced and irreducible, hence integral;
its local rings at closed points are regular of dimension 1 (curve-glue, infra-smooth-dim:
`isDomain_of_dim_one`, stalk dimensions), hence DVRs; a domain whose localizations at all maximal
ideals are integrally closed is integrally closed. Glue; **proved below** (`chartNormal`). -/
def ChartNormal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens),
    SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left → IsAffineOpen U →
    (U : Set Y.left).Nonempty → IsDomain Γ(Y.left, U) ∧ IsIntegrallyClosed Γ(Y.left, U)

/-- The value at `Spec χ → Spec Γ(X, U) → X` of a section over the affine open `U` is `χ s`. -/
theorem ev_fromSpec {K : Type} [Field K] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (χ : Γ(X, U) ⟶ CommRingCat.of K) (hx : ptOf (Spec.map χ ≫ hU.fromSpec) ∈ U) (s : Γ(X, U)) :
    ev (Spec.map χ ≫ hU.fromSpec) hx s = χ s := by
  rw [ev_comp, hU.fromSpec_app_self_apply]
  change ev (Spec.map χ) _ (res (le_top : hU.fromSpec ⁻¹ᵁ U ≤ ⊤)
    ((Scheme.ΓSpecIso Γ(X, U)).inv s)) = _
  rw [ev_res]
  exact ev_spec_top (R := Γ(X, U)) χ s

/-- **`CurveNormChart` from `ChartFinite` and `ChartNormal`** (compiled). -/
theorem curveNormChart_of (hF : ChartFinite) (hN : ChartNormal) : CurveNormChart := by
  intro Y π hP hS hI hfin
  obtain ⟨hU, hne, hinj, hfinM⟩ := hF Y π hP hS hI hfin
  obtain ⟨hdom, hic⟩ := hN Y π.U hS hI hU hne
  letI : Algebra ℚ[X] Γ(Y.left, π.U) := (chartHom Y π).toAlgebra
  haveI : Module.Finite ℚ[X] Γ(Y.left, π.U) := hfinM
  haveI := hdom
  haveI := hic
  let E := FractionRing Γ(Y.left, π.U)
  have hinjE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] Γ(Y.left, π.U) E]
    exact (IsFractionRing.injective Γ(Y.left, π.U) E).comp hinj
  letI : Algebra (RatFunc ℚ) E := (IsFractionRing.lift (K := RatFunc ℚ) hinjE).toAlgebra
  haveI : IsScalarTower ℚ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq
    (fun a => (IsFractionRing.lift_algebraMap (K := RatFunc ℚ) hinjE a).symm)
  haveI : IsIntegralClosure Γ(Y.left, π.U) ℚ[X] E :=
    IsIntegralClosure.of_isIntegrallyClosed Γ(Y.left, π.U) ℚ[X] E
  haveI : Algebra.IsAlgebraic (RatFunc ℚ) E :=
    isAlgebraic_of_isFractionRing ℚ[X] Γ(Y.left, π.U) (RatFunc ℚ) E
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y.left, π.U) (nonZeroDivisors ℚ[X])) E :=
    IsIntegralClosure.isLocalization ℚ[X] (RatFunc ℚ) E Γ(Y.left, π.U)
  haveI : Module.Finite (RatFunc ℚ) E :=
    Module.Finite.of_isLocalization ℚ[X] Γ(Y.left, π.U) (nonZeroDivisors ℚ[X])
  let e : Γ(Y.left, π.U) ≃ₐ[ℚ[X]] integralClosure ℚ[X] E :=
    IsIntegralClosure.equiv ℚ[X] Γ(Y.left, π.U) E (integralClosure ℚ[X] E)
  let eH : Γ(Y.left, π.U) ⟶ CommRingCat.of (integralClosure ℚ[X] E) :=
    CommRingCat.ofHom (e : Γ(Y.left, π.U) →+* integralClosure ℚ[X] E)
  let eH' : CommRingCat.of (integralClosure ℚ[X] E) ⟶ Γ(Y.left, π.U) :=
    CommRingCat.ofHom (e.symm : integralClosure ℚ[X] E →+* Γ(Y.left, π.U))
  have heH : eH ≫ eH' = 𝟙 _ := by
    ext x
    exact e.symm_apply_apply x
  haveI : IsIso eH := ⟨⟨eH', heH, by ext x; exact congrArg Subtype.val (e.apply_symm_apply x)⟩⟩
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map eH ≫ hU.fromSpec, inferInstance, ?_, ?_⟩
  · intro y hy
    have hmem : ptOf y ∈ π.U := by
      by_contra h
      exact hy (val_of_not_mem π y h)
    have hr : Set.range y.base ⊆ Set.range hU.fromSpec.base := by
      rintro _ ⟨z, rfl⟩
      rw [hU.range_fromSpec]
      have hz : z = IsLocalRing.closedPoint Qbar := Subsingleton.elim _ _
      rw [hz]
      exact hmem
    refine ⟨IsOpenImmersion.lift hU.fromSpec y hr ≫ Spec.map eH', ?_⟩
    rw [Category.assoc, ← Category.assoc (Spec.map eH'), ← Spec.map_comp, heH, Spec.map_id,
      Category.id_comp, IsOpenImmersion.lift_fac]
  · intro ψ
    let χ : Γ(Y.left, π.U) ⟶ CommRingCat.of Qbar := eH ≫ CommRingCat.ofHom ψ
    have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map eH ≫ hU.fromSpec =
        Spec.map χ ≫ hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]
    have hmem : ptOf (Spec.map χ ≫ hU.fromSpec) ∈ π.U := by
      have h0 : ptOf (Spec.map χ ≫ hU.fromSpec) ∈ Set.range hU.fromSpec.base := by
        rw [ptOf_comp]; exact ⟨_, rfl⟩
      rw [hU.range_fromSpec] at h0
      exact h0
    rw [hpt, val_of_mem π _ hmem, ev_fromSpec hU χ hmem π.f]
    congr 1
    have hf : π.f = algebraMap ℚ[X] Γ(Y.left, π.U) X := by
      show π.f = Polynomial.eval₂ (cQ Y π.U) π.f X
      rw [Polynomial.eval₂_X]
    rw [hf]
    show ψ (e (algebraMap ℚ[X] Γ(Y.left, π.U) X)) = _
    rw [AlgEquiv.commutes]

/-! ## `CurveChartInf` from `ChartFiniteInf`, `ChartNormalD` and `InfFnField`

The same construction over `P¹ ∖ {0}`: `V = π⁻¹(P¹ ∖ {0})`, `ℚ[s] → Γ(Y, V)`, `s ↦ π.g`. The given
`E` enters through `InfFnField`: `E` is the fraction field of `Γ(Y, V)` with `π.g ↦ 1/X`. -/

/-- `ℚ[s] → Γ(Y, π⁻¹(P¹ ∖ {0}))`, `s ↦ π.g`. -/
def chartHomInf (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) :
    InfCoord →+* Γ(Y.left, π.V) :=
  (Polynomial.eval₂RingHom (cQ Y π.V) π.g : ℚ[X] →+* Γ(Y.left, π.V))

/-- **Glue (curve theory: `π` is finite over `P¹ ∖ {0}`).** As `ChartFinite`, for
`V = π⁻¹(P¹ ∖ {0})` and the coordinate `s = 1/X` (`π.g`). Same proof (Hartshorne II.6.8,
Stacks 02OG; locators UNVERIFIED); irreducibility is not needed, nonemptiness is (for `Y = ∅`,
`Γ(Y, V) = 0` and injectivity fails). Glue, not a leaf. -/
def ChartFiniteInf : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → Nonempty Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    IsAffineOpen π.V ∧ Function.Injective (chartHomInf Y π) ∧
      @Module.Finite InfCoord Γ(Y.left, π.V) _ _ (chartHomInf Y π).toAlgebra.toModule

/-- **Glue (smooth curves are normal), domain form.** On a smooth curve `Y/ℚ`, if the sections over
an affine open form a domain, the domain is integrally closed (local rings at closed points are
DVRs; Hartshorne I.6, Stacks 033B; locators UNVERIFIED). Glue; **proved below** (`chartNormalD`). -/
def ChartNormalD : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens),
    SmoothOfRelativeDimension 1 Y.hom → IsAffineOpen U → IsDomain Γ(Y.left, U) →
    IsIntegrallyClosed Γ(Y.left, U)

/-- **Glue (curve theory: the function field seen from `∞`).** If `E` carries the chart of `π` over
`𝔸¹`, then `E` is the fraction field of `Γ(Y, π⁻¹(P¹ ∖ {0}))` through a ring map sending `π.g` to
`1/X`. *Proof* (STANDARD; Hartshorne I.6, II.6.7): finite fibres force every component of `Y` to
meet `π⁻¹(𝔸¹)`, whose image under the chart is `Spec B` with `B` a domain; so `Y` is integral with
function field `Frac B = E`; restriction `Γ(Y, V) → Γ(Y, U ∩ V) → E` is injective, and `π.g = 1/π.f`
on `U ∩ V` with `π.f ↦ X`; `E` is finite over `ℚ(X)` and `Γ(Y, V)` contains `ℚ[1/X]`, so `E` is its
fraction field. Glue, not a leaf. -/
def InfFnField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
      NormalizationModel Y π E →
      ∃ φ : Γ(Y.left, π.V) →+* E, φ π.g = algebraMap (RatFunc ℚ) E (RatFunc.X : RatFunc ℚ)⁻¹ ∧
        @IsFractionRing Γ(Y.left, π.V) _ E _ φ.toAlgebra

/-- **`CurveChartInf` from `ChartFiniteInf`, `ChartNormalD` and `InfFnField`** (compiled). -/
theorem curveChartInf_of (hF : ChartFiniteInf) (hND : ChartNormalD) (hFF : InfFnField) :
    CurveChartInf := by
  intro Y π hP hS hfin E _ _ _ _ _ hN
  have hne : Nonempty Y.left := by
    obtain ⟨h, -, -⟩ := hN
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (integralClosure ℚ[X] E))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (integralClosure ℚ[X] E)))
    exact ⟨h.base z⟩
  obtain ⟨hV, hinj, hfinM⟩ := hF Y π hP hS hne hfin
  obtain ⟨φ, hφg, hfrac⟩ := hFF Y π hP hS hfin E hN
  letI : Algebra InfCoord Γ(Y.left, π.V) := (chartHomInf Y π).toAlgebra
  haveI : Module.Finite InfCoord Γ(Y.left, π.V) := hfinM
  letI : Algebra Γ(Y.left, π.V) E := φ.toAlgebra
  haveI : IsFractionRing Γ(Y.left, π.V) E := hfrac
  haveI : IsDomain Γ(Y.left, π.V) :=
    (IsFractionRing.injective Γ(Y.left, π.V) E).isDomain _
  haveI : IsIntegrallyClosed Γ(Y.left, π.V) := hND Y π.V hS hV inferInstance
  letI := infAlg E
  have hcomp : (φ.comp (chartHomInf Y π) : ℚ[X] →+* E) = (algebraMap InfCoord E : ℚ[X] →+* E) := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (Subsingleton.elim
        (((φ.comp (chartHomInf Y π) : ℚ[X] →+* E)).comp Polynomial.C)
        (((algebraMap InfCoord E : ℚ[X] →+* E)).comp Polynomial.C)) a
    · show φ (Polynomial.eval₂ (cQ Y π.V) π.g Polynomial.X) =
        algebraMap (RatFunc ℚ) E (Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹)
          Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, hφg]
  haveI : IsScalarTower InfCoord Γ(Y.left, π.V) E := IsScalarTower.of_algebraMap_eq
    (fun a => (RingHom.congr_fun hcomp a).symm)
  haveI : IsIntegralClosure Γ(Y.left, π.V) InfCoord E :=
    IsIntegralClosure.of_isIntegrallyClosed Γ(Y.left, π.V) InfCoord E
  let e : Γ(Y.left, π.V) ≃ₐ[InfCoord] integralClosure InfCoord E :=
    IsIntegralClosure.equiv InfCoord Γ(Y.left, π.V) E (integralClosure InfCoord E)
  let eH : Γ(Y.left, π.V) ⟶ CommRingCat.of (integralClosure InfCoord E) :=
    CommRingCat.ofHom (e : Γ(Y.left, π.V) →+* integralClosure InfCoord E)
  let eH' : CommRingCat.of (integralClosure InfCoord E) ⟶ Γ(Y.left, π.V) :=
    CommRingCat.ofHom (e.symm : integralClosure InfCoord E →+* Γ(Y.left, π.V))
  have heH : eH ≫ eH' = 𝟙 _ := by
    ext x
    exact e.symm_apply_apply x
  haveI : IsIso eH :=
    ⟨⟨eH', heH, by ext x; exact congrArg Subtype.val (e.apply_symm_apply x)⟩⟩
  refine ⟨Spec.map eH ≫ hV.fromSpec, inferInstance, ?_, ?_⟩
  · intro y hy
    have hmem : ptOf y ∈ π.V := by
      by_contra hv
      have hu : ptOf y ∈ π.U := by
        have : ptOf y ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases this with h | h
        · exact h
        · exact absurd h hv
      apply hy
      rw [val_of_mem π y hu]
      congr 1
      rw [ev_eq_zero_iff, π.basicOpen_f]
      exact fun h => hv h.2
    have hr : Set.range y.base ⊆ Set.range hV.fromSpec.base := by
      rintro _ ⟨z, rfl⟩
      rw [hV.range_fromSpec]
      have hz : z = IsLocalRing.closedPoint Qbar := Subsingleton.elim _ _
      rw [hz]
      exact hmem
    refine ⟨IsOpenImmersion.lift hV.fromSpec y hr ≫ Spec.map eH', ?_⟩
    rw [Category.assoc, ← Category.assoc (Spec.map eH'), ← Spec.map_comp, heH, Spec.map_id,
      Category.id_comp, IsOpenImmersion.lift_fac]
  · intro ψ
    let χ : Γ(Y.left, π.V) ⟶ CommRingCat.of Qbar := eH ≫ CommRingCat.ofHom ψ
    have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map eH ≫ hV.fromSpec =
        Spec.map χ ≫ hV.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]
    have hmem : ptOf (Spec.map χ ≫ hV.fromSpec) ∈ π.V := by
      have h0 : ptOf (Spec.map χ ≫ hV.fromSpec) ∈ Set.range hV.fromSpec.base := by
        rw [ptOf_comp]; exact ⟨_, rfl⟩
      rw [hV.range_fromSpec] at h0
      exact h0
    have hg : π.g = algebraMap InfCoord Γ(Y.left, π.V) infUnif := by
      show π.g = Polynomial.eval₂ (cQ Y π.V) π.g Polynomial.X
      rw [Polynomial.eval₂_X]
    have hval : ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = χ π.g := by
      rw [hg]
      show _ = ψ (e (algebraMap InfCoord Γ(Y.left, π.V) infUnif))
      rw [AlgEquiv.commutes]
    rw [hpt, hval, ← ev_fromSpec hV χ hmem π.g, ev_eq_zero_iff, π.basicOpen_g]
    constructor
    · intro h hUV
      rw [val_of_mem π _ hUV.1] at h
      exact OnePoint.coe_ne_infty _ h
    · intro h
      apply val_of_not_mem
      exact fun hU => h ⟨hU, hmem⟩

/-! ## `ChartNormalD` proved; `ChartNormal` reduced to its domain part -/

/-- **The localizations of `Γ(Y, U)` at maximal ideals are discrete valuation rings** (as domains
that are integrally closed): they are the local rings of `Y` at closed points, regular of
dimension 1 (infra-smooth-dim's `stalk_dim_of_smoothOfRelativeDimension`, curve-glue's
`isDomain_of_dim_one`, Mathlib's DVR TFAE). -/
theorem loc_max_dvr (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens)
    (hS : SmoothOfRelativeDimension 1 Y.hom) (hU : IsAffineOpen U) (p : Ideal Γ(Y.left, U))
    (hpm : p.IsMaximal) :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let q : PrimeSpectrum Γ(Y.left, U) := ⟨p, hpm.isPrime⟩
  let x : Y.left := hU.fromSpec q
  have hxU : x ∈ U := by
    have : x ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hxc : IsClosed ({x} : Set Y.left) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    have hq : IsClosed ({q} : Set ↥(Spec Γ(Y.left, U))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).2 hpm
    have h2 := hq.isLocallyClosed.image hU.fromSpec.isOpenEmbedding.isInducing
      hU.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
    have e2 : (hU.fromSpec.base '' {q} : Set Y.left) = {x} := Set.image_singleton
    rw [e2] at h2
    exact h2
  obtain ⟨hdim, hspan⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension Y.hom 1 x hxc
  have hdim' : ringKrullDim (Y.left.presheaf.stalk x) = 1 := by rw [hdim]; rfl
  have hspan' : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).spanFinrank = 1 := hspan
  haveI : IsDomain (Y.left.presheaf.stalk x) := CIcopy.CurveGlueCI.isDomain_of_dim_one hdim' hspan'
  have hnf : ¬ IsField (Y.left.presheaf.stalk x) := fun h => by
    have h0 := ringKrullDim_eq_zero_of_isField h
    rw [hdim'] at h0
    exact one_ne_zero h0
  have hprin : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).IsPrincipal := by
    have hfg : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).FG := IsNoetherian.noetherian _
    obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
    rw [hspan'] at hs
    obtain ⟨t, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
    exact ⟨⟨t, hsp.symm⟩⟩
  have key : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).IsPrincipal ↔
      (IsIntegrallyClosed (Y.left.presheaf.stalk x) ∧
        ∃! P : Ideal (Y.left.presheaf.stalk x), P ≠ ⊥ ∧ P.IsPrime) :=
    (IsDiscreteValuationRing.TFAE _ hnf).out 5 4
  haveI : IsIntegrallyClosed (Y.left.presheaf.stalk x) := (key.mp hprin).1
  letI : Algebra Γ(Y.left, U) (Y.left.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.left.presheaf ⟨x, hxU⟩
  haveI : IsLocalization.AtPrime (Y.left.presheaf.stalk x) p := hU.isLocalization_stalk' q hxU
  let eq := (IsLocalization.algEquiv p.primeCompl (Y.left.presheaf.stalk x)
      (Localization.AtPrime p)).toRingEquiv
  exact ⟨eq.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv eq⟩

/-- **`ChartNormalD` holds** (compiled). -/
theorem chartNormalD : ChartNormalD := by
  intro Y U hS hU hdom
  exact IsIntegrallyClosed.of_localization_maximal fun p _ hpm => (loc_max_dvr Y U hS hU p hpm).2

/-- **Glue (smooth irreducible curves are integral).** The sections of a smooth irreducible curve
over a nonempty affine open form a domain. -/
def CurveSectionsDomain : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens),
    SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left → IsAffineOpen U →
    (U : Set Y.left).Nonempty → IsDomain Γ(Y.left, U)

/-- **`CurveSectionsDomain` holds** (compiled): `Γ(Y, U)` is reduced (its localizations at maximal
ideals are domains) and `Spec Γ(Y, U) ≅ U` is irreducible, so `Spec Γ(Y, U)` is integral. -/
theorem curveSectionsDomain : CurveSectionsDomain := by
  intro Y U hS hI hU hne
  haveI : IsReduced Γ(Y.left, U) := isReduced_ofLocalizationMaximal _ fun J hJ => by
    haveI := (loc_max_dvr Y U hS hU J hJ).1
    infer_instance
  have hUirr : IsIrreducible (U : Set Y.left) :=
    ⟨hne, (IrreducibleSpace.isIrreducible_univ Y.left).2.open_subset U.isOpen
      (Set.subset_univ _)⟩
  haveI : IrreducibleSpace (Spec Γ(Y.left, U)) :=
    @Function.Surjective.irreducibleSpace _ _ _ _ hU.isoSpec.hom.base
      hU.isoSpec.hom.base.hom.continuous hU.isoSpec.hom.surjective
      (Subtype.irreducibleSpace hUirr)
  exact (affine_isIntegral_iff _).1 (isIntegral_of_irreducibleSpace_of_isReduced _)

/-- **`ChartNormal` holds** (compiled), from `curveSectionsDomain` and `chartNormalD`. -/
theorem chartNormal : ChartNormal := by
  intro Y U hS hI hU hne
  haveI := curveSectionsDomain Y U hS hI hU hne
  exact ⟨inferInstance, chartNormalD Y U hS hU inferInstance⟩

/-- **`CurveNormChart` from `ChartFinite` alone** (compiled). -/
theorem curveNormChart_of' (hF : ChartFinite) : CurveNormChart :=
  curveNormChart_of hF chartNormal

/-- **`CurveChartInf` from `ChartFiniteInf` and `InfFnField`** (compiled). -/
theorem curveChartInf_of' (hF : ChartFiniteInf) (hFF : InfFnField) : CurveChartInf :=
  curveChartInf_of hF chartNormalD hFF

/-! ## `ChartFinite`, `ChartFiniteInf` from properness, quasi-finiteness and dominance

Mathlib's Zariski main theorem corollary `IsFinite.of_isProper_of_locallyQuasiFinite` (Stacks 02OG)
turns a proper, locally quasi-finite chart into a finite one; a finite morphism to an affine scheme
has affine source; and `IsFinite (Spec.map φ) ↔ φ` finite (compiled). -/

/-- `ℚ[X] → Γ(Y, W)`, `X ↦ s`. -/
def secHom (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens) (s : Γ(Y.left, W)) :
    ℚ[X] →+* Γ(Y.left, W) :=
  Polynomial.eval₂RingHom (cQ Y W) s

/-- The morphism `W → 𝔸¹ = Spec ℚ[X]` given by `s ∈ Γ(Y, W)`. -/
def secMor (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens) (s : Γ(Y.left, W)) :
    W.toScheme ⟶ Spec (CommRingCat.of ℚ[X]) :=
  W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (secHom Y W s))

/-- **A proper, locally quasi-finite `W → 𝔸¹` has affine source and finite ring map** (compiled). -/
theorem finite_of_proper_qf (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens)
    (s : Γ(Y.left, W)) [IsProper (secMor Y W s)] [LocallyQuasiFinite (secMor Y W s)] :
    IsAffineOpen W ∧ @Module.Finite ℚ[X] Γ(Y.left, W) _ _ (secHom Y W s).toAlgebra.toModule := by
  haveI : IsFinite (secMor Y W s) := IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : IsAffine W.toScheme := isAffine_of_isAffineHom (secMor Y W s)
  have hW : IsAffineOpen W := inferInstanceAs (IsAffine W.toScheme)
  refine ⟨hW, ?_⟩
  have h5 : IsFinite (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (secHom Y W s))) := by
    rw [hW.isoSpec_hom]
    exact (inferInstance : IsFinite (secMor Y W s))
  haveI := h5
  have h6 : IsFinite (Spec.map (CommRingCat.ofHom (secHom Y W s))) := by
    have e : Spec.map (CommRingCat.ofHom (secHom Y W s)) =
        hW.isoSpec.inv ≫ (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (secHom Y W s))) := by
      rw [Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  rw [IsFinite.SpecMap_iff] at h6
  exact h6

/-- **Glue (curve theory: the two charts of `π` are proper).** For a proper smooth curve `Y/ℚ` and
`π : Y → P¹` with finite `ℚ̄`-fibres, `π⁻¹(𝔸¹) → 𝔸¹` (by `π.f`) and `π⁻¹(P¹ ∖ {0}) → 𝔸¹` (by
`π.g = 1/π.f`) are proper. *Proof* (STANDARD; valuative criterion, Hartshorne II.4.7 and
II.4.8(f); locators UNVERIFIED): separated and of finite type by cancellation from `Y → Spec ℚ`;
universally closed since a valuation-ring point of `Y` (which exists by properness of `Y`) whose
generic point lies in `U` and whose `π.f`-value is integral cannot meet `π = ∞`, because
`π.f · π.g = 1` on `U ∩ V`. Glue, not a leaf. -/
def ChartProper : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    IsProper (secMor Y π.U π.f) ∧ IsProper (secMor Y π.V π.g)

/-- **Glue (curve theory: the two charts of `π` are quasi-finite).** Under the same hypotheses
both charts are locally quasi-finite. *Proof* (STANDARD; Stacks 01TD/02NH; locators UNVERIFIED):
the points over a closed point of `𝔸¹` are closed points of `Y`, each with a `ℚ̄`-point in the
corresponding finite `π`-fibre; over the generic point of `𝔸¹` lie only generic points of
components of `Y` (finitely many). Glue, not a leaf. -/
def ChartQuasiFinite : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    LocallyQuasiFinite (secMor Y π.U π.f) ∧ LocallyQuasiFinite (secMor Y π.V π.g)

/-- **Glue (curve theory: the two charts are dominant).** Under the same hypotheses `π⁻¹(𝔸¹)` is
nonempty and `ℚ[X] → Γ(Y, π⁻¹(𝔸¹))`, `ℚ[s] → Γ(Y, π⁻¹(P¹ ∖ {0}))` are injective (a polynomial
relation for `π.f` on a component would make a `π`-fibre infinite: `π` would take finitely many
values on the infinitely many `ℚ̄`-points of that component; `Y ≠ ∅` is needed, since for `Y = ∅`
both clauses fail). Glue, not a leaf. -/
def ChartDominant : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → Nonempty Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    (π.U : Set Y.left).Nonempty ∧ Function.Injective (secHom Y π.U π.f) ∧
      Function.Injective (secHom Y π.V π.g)

/-- **`ChartFinite` from `ChartProper`, `ChartQuasiFinite`, `ChartDominant`** (compiled). -/
theorem chartFinite_of (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant) :
    ChartFinite := by
  intro Y π h1 h2 h3 h4
  haveI := (hP Y π h1 h2 h4).1
  haveI := (hQ Y π h1 h2 h4).1
  obtain ⟨hU, hfin⟩ := finite_of_proper_qf Y π.U π.f
  obtain ⟨hne, hinj, -⟩ := hD Y π h1 h2 inferInstance h4
  exact ⟨hU, hne, hinj, hfin⟩

/-- **`ChartFiniteInf` from `ChartProper`, `ChartQuasiFinite`, `ChartDominant`** (compiled). -/
theorem chartFiniteInf_of (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant) :
    ChartFiniteInf := by
  intro Y π h1 h2 h3 h4
  haveI := (hP Y π h1 h2 h4).2
  haveI := (hQ Y π h1 h2 h4).2
  obtain ⟨hV, hfin⟩ := finite_of_proper_qf Y π.V π.g
  obtain ⟨-, -, hinj⟩ := hD Y π h1 h2 h3 h4
  exact ⟨hV, hinj, hfin⟩

/-- **`CurveNormChart` from the three chart Props** (compiled). -/
theorem curveNormChart_of_charts (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant) :
    CurveNormChart :=
  curveNormChart_of' (chartFinite_of hP hQ hD)

/-- **`CurveChartInf` from the three chart Props and `InfFnField`** (compiled). -/
theorem curveChartInf_of_charts (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant)
    (hFF : InfFnField) : CurveChartInf :=
  curveChartInf_of' (chartFiniteInf_of hP hQ hD) hFF

end HeckeRestCurve

end

#print axioms HeckeRestCurve.curveNormChart_of
#print axioms HeckeRestCurve.curveChartInf_of
#print axioms HeckeRestCurve.chartNormalD
#print axioms HeckeRestCurve.curveNormChart_of'
#print axioms HeckeRestCurve.curveChartInf_of'
#print axioms HeckeRestCurve.curveNormChart_of_charts
#print axioms HeckeRestCurve.curveChartInf_of_charts

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3b: `InfFnField` from `ChartFiniteInf` and `ChartIrreducible`

Given the chart `h : Spec B → Y` over `𝔸¹` (`NormalizationModel`): its range is `U = π⁻¹(𝔸¹)`
(Jacobson); `h^*π.f = X` (separation by `ℚ̄`-points); `h⁻¹(V) = D(X) ⊆ Spec B`; and
`Γ(Y, V) → Γ(Spec B, D(X)) = B[1/X] ⊆ E` is the required map (`π.g ↦ 1/X`), injective because
`Γ(Y, V)` is a domain integral over `ℚ[s]` (incomparability), with fraction field `E` because
`Γ(Spec B, D(X)) ≅ Γ(Y, U ∩ V) = Γ(Y, V)[1/π.g]`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- **Glue (curve theory: the curve is irreducible).** A proper smooth curve `Y/ℚ` with
`π : Y → P¹` of finite `ℚ̄`-fibres and a normalization chart over `𝔸¹` is irreducible. *Proof*
(STANDARD; Hartshorne II.6.7; locators UNVERIFIED): the chart's image `U = π⁻¹(𝔸¹)` is irreducible
(the image of `Spec B`, `B` a domain); its complement is the fibre over `∞`; a nonempty open set
outside `closure U` would have infinitely many closed points (no point of a smooth curve is open:
local rings have dimension 1), all in the finite fibre over `∞`. Glue, not a leaf. -/
def ChartIrreducible : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
      NormalizationModel Y π E → IrreducibleSpace Y.left

section Chart

variable {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type} [Field E]
  [Algebra ℚ[X] E]

/-- **The chart's range is `π⁻¹(𝔸¹)`** (compiled; Jacobson, as in ts-hecke's `range_comp_subset`). -/
theorem range_chart_eq [LocallyOfFiniteType Y.hom]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left) [IsOpenImmersion h]
    (himg : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X))) :
    Set.range h = (π.U : Set Y.left) := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  apply Set.Subset.antisymm
  · by_contra hcon
    rw [Set.not_subset] at hcon
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hcon
    set W : Set Y.left := Set.range h ∩ (π.U : Set Y.left)ᶜ
    have hWne : W.Nonempty := ⟨h x, ⟨x, rfl⟩, hx⟩
    have hWlc : IsLocallyClosed W :=
      (h.isOpenEmbedding.isOpen_range).isLocallyClosed.inter
        π.U.isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨z, ⟨hzh, hzU⟩, hzc⟩ := nonempty_inter_closedPoints hWne hWlc
    obtain ⟨y, hy⟩ := TSHeckeGal.exists_qbar_point Y.hom z (mem_closedPoints_iff.mp hzc)
    have hyr : Set.range y ⊆ Set.range h := by
      rintro _ ⟨s, rfl⟩; rw [hy s]; exact hzh
    set y'' := IsOpenImmersion.lift h y hyr
    have hy'' : y'' ≫ h = y := IsOpenImmersion.lift_fac h y hyr
    have hfin : π.val (K := Qbar) y ≠ OnePoint.infty := by
      rw [← hy'', ← Spec.map_preimage y'', ← CommRingCat.ofHom_hom (Spec.preimage y''), hval]
      exact OnePoint.coe_ne_infty _
    have hmem : ptOf y ∈ π.U := by
      by_contra hn
      exact hfin (val_of_not_mem π y hn)
    have hpt : ptOf y = z := hy _
    exact hzU (hpt ▸ hmem)
  · intro z hzU
    by_contra hz
    set W : Set Y.left := (π.U : Set Y.left) ∩ (Set.range h)ᶜ
    have hWne : W.Nonempty := ⟨z, hzU, hz⟩
    have hWlc : IsLocallyClosed W :=
      π.U.isOpen.isLocallyClosed.inter
        (h.isOpenEmbedding.isOpen_range).isClosed_compl.isLocallyClosed
    obtain ⟨z', ⟨hz'U, hz'h⟩, hz'c⟩ := nonempty_inter_closedPoints hWne hWlc
    obtain ⟨y, hy⟩ := TSHeckeGal.exists_qbar_point Y.hom z' (mem_closedPoints_iff.mp hz'c)
    have hpt : ptOf y = z' := hy _
    have hmem : ptOf y ∈ π.U := hpt ▸ hz'U
    have hfin : π.val (K := Qbar) y ≠ OnePoint.infty := by
      rw [val_of_mem π y hmem]
      exact OnePoint.coe_ne_infty _
    obtain ⟨y', hy'⟩ := himg y hfin
    apply hz'h
    obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of Qbar)) := inferInstance
    refine ⟨y' s, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hy', hy s]

/-- **`h^* π.f = X`** (compiled; separation by `ℚ̄`-points in the Jacobson domain `B`). -/
theorem app_f_eq [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)))
    (htop : h ⁻¹ᵁ π.U = ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom
        (res htop.ge (h.app π.U π.f)) = algebraMap ℚ[X] (integralClosure ℚ[X] E) X := by
  have hinjQE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    apply hinjQE
    have := congrArg (fun x : integralClosure ℚ[X] E => (x : E)) hab
    simpa using this
  apply TSHeckeGal.eq_of_forall_qbar hinjB
  intro ψ
  have hx : ptOf (Spec.map (CommRingCat.ofHom ψ) ≫ h) ∈ π.U := by
    show h.base (ptOf (Spec.map (CommRingCat.ofHom ψ))) ∈ π.U
    have : ptOf (Spec.map (CommRingCat.ofHom ψ)) ∈ h ⁻¹ᵁ π.U := by rw [htop]; trivial
    exact this
  have h1 := hval ψ
  rw [val_of_mem π _ hx] at h1
  have h2 : ev (Spec.map (CommRingCat.ofHom ψ) ≫ h) hx π.f =
      ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) := OnePoint.coe_injective h1
  rw [← h2, ev_comp, ← ev_res _ htop.ge (show ptOf (Spec.map (CommRingCat.ofHom ψ)) ∈
    (⊤ : (Spec (CommRingCat.of (integralClosure ℚ[X] E))).Opens) from trivial)]
  set w := res htop.ge (h.app π.U π.f)
  have hw : w = (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom w) :=
    (Iso.hom_inv_id_apply _ _).symm
  conv_rhs => rw [hw]
  rw [ev_spec_top]
  rfl

/-- `ℚ[s] → ℚ(X)`, `s ↦ 1/X`, is injective (ts-hecke's argument in `isFractionRing_infCoord`). -/
theorem infCoord_injective : Function.Injective (algebraMap InfCoord (RatFunc ℚ)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  letI : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero hX
  have hev : Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X =
      algebraMap ℚ[X] (RatFunc ℚ) :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun (Subsingleton.elim
      ((Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X).comp Polynomial.C)
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp Polynomial.C)) a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RatFunc.algebraMap_X])
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

/-- Restriction after `appLE`. -/
theorem res_appLE {X Y' : Scheme.{0}} (h : X ⟶ Y') {U : Y'.Opens} {D D' : X.Opens}
    (e : D ≤ h ⁻¹ᵁ U) (hDD : D' ≤ D) (s : Γ(Y', U)) :
    res hDD (h.appLE U D e s) = h.appLE U D' (hDD.trans e) s := by
  rw [res, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- `appLE` after restriction. -/
theorem appLE_res {X Y' : Scheme.{0}} (h : X ⟶ Y') {U U' : Y'.Opens} {D : X.Opens}
    (hUU : U' ≤ U) (e : D ≤ h ⁻¹ᵁ U') (s : Γ(Y', U)) :
    h.appLE U' D e (res hUU s) = h.appLE U D (e.trans (h.preimage_mono hUU)) s := by
  rw [res, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

/-- Sections over `W = D(g)` are fractions `a / g^n` (helper, by `subst`). -/
theorem loc_helper {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V))
    (W : X.Opens) (hW : W = X.basicOpen g) (hWV : W ≤ V) (w : Γ(X, W)) :
    ∃ (a : Γ(X, V)) (n : ℕ), w * res hWV (g ^ n) = res hWV a := by
  subst hW
  haveI := hV.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hw⟩ := IsLocalization.surj (Submonoid.powers g) w
  exact ⟨a, n, hw⟩

end Chart

/-- **`InfFnField` from `ChartFiniteInf` and `ChartIrreducible`** (compiled). -/
theorem infFnField_of (hFI : ChartFiniteInf) (hIrr : ChartIrreducible) : InfFnField := by
  intro Y π hP hS hfin E _ _ _ _ _ hN
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI hirr : IrreducibleSpace Y.left := hIrr Y π hP hS hfin E hN
  obtain ⟨h, hO, himg, hval⟩ := hN
  haveI := hO
  -- the ring `B` and its fraction field `E`
  have hinjQE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    apply hinjQE
    have := congrArg (fun x : integralClosure ℚ[X] E => (x : E)) hab
    simpa using this
  haveI : Module.IsTorsionFree ℚ[X] E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjQE
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  set XB : integralClosure ℚ[X] E := algebraMap ℚ[X] (integralClosure ℚ[X] E) X with hXBdef
  have hXB0 : XB ≠ 0 := by
    rw [hXBdef, ne_eq, map_eq_zero_iff _ hinjB]; exact Polynomial.X_ne_zero
  have hXBE : algebraMap (integralClosure ℚ[X] E) E XB = algebraMap ℚ[X] E X := rfl
  -- the chart's range is `U`; `h^* f = X`
  have hrange := range_chart_eq h himg hval
  have htop : h ⁻¹ᵁ π.U = ⊤ := by
    apply top_unique
    intro x _
    show h x ∈ π.U
    have : h x ∈ Set.range h := ⟨x, rfl⟩
    rw [hrange] at this
    exact this
  set rB : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv XB with hrBdef
  have hres : res htop.ge (h.app π.U π.f) = rB := by
    have hX := app_f_eq h hval htop
    rw [← hXBdef] at hX
    rw [hrBdef, ← hX, Iso.hom_inv_id_apply]
  set D := (Spec (CommRingCat.of (integralClosure ℚ[X] E))).basicOpen rB with hDdef
  have hD : h ⁻¹ᵁ π.V = D := by
    have e1 : h ⁻¹ᵁ π.V = h ⁻¹ᵁ (Y.left.basicOpen π.f) := by
      rw [π.basicOpen_f, Scheme.Hom.preimage_inf, htop, top_inf_eq]
    rw [e1, Scheme.preimage_basicOpen, hDdef, ← hres, res, Scheme.basicOpen_res, top_inf_eq]
  have eV : D ≤ h ⁻¹ᵁ π.V := hD.ge
  have eU : D ≤ h ⁻¹ᵁ π.U := by rw [htop]; exact le_top
  have eUV : D ≤ h ⁻¹ᵁ (π.U ⊓ π.V) := le_inf eU eV
  -- `V` nonempty, `Γ(Y, V)` a domain
  have hVne : (π.V : Set Y.left).Nonempty := by
    let x₀ : PrimeSpectrum (integralClosure ℚ[X] E) := ⟨⊥, inferInstance⟩
    have hx₀ : x₀ ∈ D := by
      have : x₀ ∈ PrimeSpectrum.basicOpen XB := by
        rw [PrimeSpectrum.mem_basicOpen]; exact hXB0
      rw [hDdef, hrBdef, basicOpen_eq_of_affine]
      exact this
    exact ⟨h x₀, eV hx₀⟩
  have hneY : Nonempty Y.left := ⟨h (Nonempty.some inferInstance)⟩
  obtain ⟨hV, hinjV, hfinV⟩ := hFI Y π hP hS hneY hfin
  haveI : IsDomain Γ(Y.left, π.V) := curveSectionsDomain Y π.V hS hirr hV hVne
  -- the map `φ`
  haveI : IsLocalization.Away rB Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), D) :=
    isLocalization_away_of_isAffine rB
  let gB : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) →+* E :=
    (algebraMap (integralClosure ℚ[X] E) E).comp
      (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom.hom
  have hgB : gB rB = algebraMap ℚ[X] E X := by
    show algebraMap _ E ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv XB)) = _
    rw [Iso.inv_hom_id_apply]
    exact hXBE
  have hunit : IsUnit (gB rB) := by
    rw [hgB]; exact (map_ne_zero_iff _ hinjQE).2 Polynomial.X_ne_zero |>.isUnit
  let lam : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), D) →+* E :=
    IsLocalization.Away.lift rB hunit
  have hlam : ∀ x, lam (algebraMap _ _ x) = gB x := fun x => IsLocalization.lift_eq _ _
  let φ : Γ(Y.left, π.V) →+* E := lam.comp (h.appLE π.V D eV).hom
  -- `φ(g) = 1/X`
  have hfD : h.appLE π.U D eU π.f =
      algebraMap Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) _ rB := by
    show _ = res (Scheme.basicOpen_le _ rB) rB
    calc h.appLE π.U D eU π.f = res ((Scheme.basicOpen_le _ rB).trans htop.ge) (h.app π.U π.f) :=
          rfl
      _ = res (Scheme.basicOpen_le _ rB) (res htop.ge (h.app π.U π.f)) := (res_res _ _ _).symm
      _ = res (Scheme.basicOpen_le _ rB) rB := by rw [hres]
  have hgf : h.appLE π.V D eV π.g * h.appLE π.U D eU π.f = 1 := by
    have hinv := congrArg (h.appLE (π.U ⊓ π.V) D eUV) π.inv
    rw [map_mul, map_one] at hinv
    have e1 := appLE_res h (inf_le_left : π.U ⊓ π.V ≤ π.U) eUV π.f
    have e2 := appLE_res h (inf_le_right : π.U ⊓ π.V ≤ π.V) eUV π.g
    simp only [e1, e2] at hinv
    rw [mul_comm]
    exact hinv
  have hφg : φ π.g = algebraMap (RatFunc ℚ) E (RatFunc.X : RatFunc ℚ)⁻¹ := by
    have h1 : φ π.g * algebraMap ℚ[X] E X = 1 := by
      rw [← hgB, ← hlam, ← hfD]
      show lam (h.appLE π.V D eV π.g) * lam (h.appLE π.U D eU π.f) = 1
      rw [← map_mul, hgf, map_one]
    rw [map_inv₀, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨φ, hφg, ?_⟩
  -- injectivity: `ker φ` lies over `0` in `ℚ[s]`
  letI : Algebra InfCoord Γ(Y.left, π.V) := (chartHomInf Y π).toAlgebra
  haveI : Module.Finite InfCoord Γ(Y.left, π.V) := hfinV
  letI := infAlg E
  have hcomp : (φ.comp (chartHomInf Y π) : ℚ[X] →+* E) =
      (algebraMap InfCoord E : ℚ[X] →+* E) := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (Subsingleton.elim
        (((φ.comp (chartHomInf Y π) : ℚ[X] →+* E)).comp Polynomial.C)
        (((algebraMap InfCoord E : ℚ[X] →+* E)).comp Polynomial.C)) a
    · show φ (Polynomial.eval₂ (cQ Y π.V) π.g Polynomial.X) =
        algebraMap (RatFunc ℚ) E (Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹)
          Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, hφg]
  have hinjI : Function.Injective (algebraMap InfCoord E) := by
    show Function.Injective ((algebraMap (RatFunc ℚ) E).comp (algebraMap InfCoord (RatFunc ℚ)))
    exact (algebraMap (RatFunc ℚ) E).injective.comp infCoord_injective
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hker : (RingHom.ker φ).under InfCoord = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Ideal.mem_bot]
      have hc' : φ (chartHomInf Y π c) = 0 := hc
      have : (algebraMap InfCoord E) c = 0 := (RingHom.congr_fun hcomp c).symm.trans hc'
      exact (map_eq_zero_iff _ hinjI).1 this
    haveI : Nontrivial InfCoord := inferInstanceAs (Nontrivial ℚ[X])
    have := Ideal.eq_bot_of_under_eq_bot hker
    have ha' : a ∈ RingHom.ker φ := ha
    rw [this] at ha'
    exact ha'
  letI : Algebra Γ(Y.left, π.V) E := φ.toAlgebra
  haveI : FaithfulSMul Γ(Y.left, π.V) E := (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
  -- fractions
  have hW : h ''ᵁ D = Y.left.basicOpen π.g := by
    rw [← hD, Scheme.Hom.image_preimage_eq_opensRange_inf, π.basicOpen_g]
    have hor : h.opensRange = π.U := by
      ext1; exact hrange
    rw [hor]
  have hWV : h ''ᵁ D ≤ π.V := by rw [hW]; exact Y.left.basicOpen_le π.g
  have heD : D ≤ h ⁻¹ᵁ (h ''ᵁ D) := (Scheme.Hom.preimage_image_eq h D).ge
  have hθsurj : Function.Surjective (h.appLE (h ''ᵁ D) D heD) := by
    rw [← Scheme.Hom.appIso_hom']
    exact (h.appIso D).commRingCatIsoToRingEquiv.surjective
  have hfrac : ∀ b : integralClosure ℚ[X] E, ∃ (a : Γ(Y.left, π.V)) (n : ℕ),
      algebraMap _ E b * φ π.g ^ n = φ a := by
    intro b
    obtain ⟨w', hw'⟩ := hθsurj (algebraMap Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤)
      Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), D)
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv b))
    obtain ⟨a, n, han⟩ := loc_helper hV π.g (h ''ᵁ D) hW hWV w'
    refine ⟨a, n, ?_⟩
    have := congrArg (h.appLE (h ''ᵁ D) D heD) han
    rw [map_mul, hw', appLE_res, appLE_res, map_pow] at this
    have h2 := congrArg lam this
    rw [map_mul, map_pow, hlam] at h2
    convert h2 using 2
    show algebraMap _ E b = algebraMap _ E
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv b))
    rw [Iso.inv_hom_id_apply]
  have hφg0 : φ π.g ≠ 0 := by
    rw [hφg]; exact (map_ne_zero_iff _ (algebraMap (RatFunc ℚ) E).injective).2
      (inv_ne_zero RatFunc.X_ne_zero)
  refine IsFractionRing.of_field Γ(Y.left, π.V) E fun z => ?_
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure ℚ[X] E) z
  obtain ⟨a₁, n₁, h₁⟩ := hfrac b₁
  obtain ⟨a₂, n₂, h₂⟩ := hfrac b₂
  refine ⟨a₁ * π.g ^ n₂, a₂ * π.g ^ n₁, ?_⟩
  show _ = φ (a₁ * π.g ^ n₂) / φ (a₂ * π.g ^ n₁)
  have hb₂' : algebraMap (integralClosure ℚ[X] E) E b₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ E)).2 (nonZeroDivisors.ne_zero hb₂)
  rw [map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
  field_simp

/-- **`CurveChartInf` from the three chart Props and `ChartIrreducible`** (compiled). -/
theorem curveChartInf_of_charts' (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant)
    (hIrr : ChartIrreducible) : CurveChartInf :=
  curveChartInf_of_charts hP hQ hD (infFnField_of (chartFiniteInf_of hP hQ hD) hIrr)

end HeckeRestCurve

end

#print axioms HeckeRestCurve.infFnField_of
#print axioms HeckeRestCurve.curveChartInf_of_charts'

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3c: `ChartIrreducible` and `ChartDominant` proved

No closed point of a smooth curve is open (its local ring has dimension 1, while an open point has
no proper generization); so a nonempty open subset has infinitely many closed points (Jacobson),
hence infinitely many `ℚ̄`-points. A `π`-fibre is finite, so `π` cannot be `∞` on a nonempty open
set (`ChartIrreducible`: the chart's image is dense; `ChartDominant`: `π⁻¹(𝔸¹) ≠ ∅`), nor take
finitely many values on one (`ChartDominant`: no polynomial relation for `π.f` or `π.g`).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- **No closed point of a smooth curve is open** (compiled). -/
theorem not_isOpen_closed_point {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] (x : X)
    (hx : IsClosed ({x} : Set X)) : ¬ IsOpen ({x} : Set X) := by
  intro ho
  obtain ⟨hdim, -⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 x hx
  haveI hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) := by
    constructor
    intro p q
    apply (X.fromSpecStalk x).isEmbedding.injective
    have hmem : ∀ r : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x r = x := by
      intro r
      have hr : X.fromSpecStalk x r ∈ Set.range (X.fromSpecStalk x) := ⟨r, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hr
      exact (hr.mem_open ho rfl : X.fromSpecStalk x r ∈ ({x} : Set X))
    rw [hmem p, hmem q]
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  rw [hdim] at hle
  exact absurd hle (by decide)

/-- **A nonempty open subset of a smooth curve over `ℚ` has infinitely many closed points**
(compiled; Jacobson). -/
theorem infinite_closedPoints_of_isOpen {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [SmoothOfRelativeDimension 1 f] {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    (W ∩ closedPoints X).Infinite := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro hfin
  have hclosed : ∀ S ⊆ W ∩ closedPoints X, IsClosed S := by
    intro S hS
    have hSfin : S.Finite := hfin.subset hS
    rw [← Set.biUnion_of_singleton S]
    exact hSfin.isClosed_biUnion fun y hy => (hS hy).2
  have hWF : W ⊆ W ∩ closedPoints X := by
    calc W ⊆ closure W := subset_closure
      _ = closure (W ∩ closedPoints X) :=
          (JacobsonSpace.closure_inter_closedPoints_eq_closure hW.isLocallyClosed).symm
      _ = W ∩ closedPoints X := (hclosed _ le_rfl).closure_eq
  obtain ⟨x, hxW⟩ := hne
  have hxF := hWF hxW
  have hopen : IsOpen ({x} : Set X) := by
    have e : ({x} : Set X) = W ∩ ((W ∩ closedPoints X) \ {x})ᶜ := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff,
        not_and, not_not]
      constructor
      · rintro rfl; exact ⟨hxW, fun _ => rfl⟩
      · rintro ⟨hyW, hy⟩; exact hy (hWF hyW)
    rw [e]
    exact hW.inter (hclosed _ Set.diff_subset).isOpen_compl
  exact not_isOpen_closed_point f x hxF.2 hopen

/-- **A nonempty open subset of a smooth curve over `ℚ` has infinitely many `ℚ̄`-points**
(compiled). -/
theorem infinite_qbar_points {Y : Over (Spec (CommRingCat.of ℚ))}
    (hS : SmoothOfRelativeDimension 1 Y.hom) {W : Set Y.left} (hW : IsOpen W) (hne : W.Nonempty) :
    {y : fieldPt Qbar ⟶ Y | ptOf y.left ∈ W}.Infinite := by
  have hinf := infinite_closedPoints_of_isOpen Y.hom hW hne
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : Infinite ↥(W ∩ closedPoints Y.left) := hinf.to_subtype
  have hch : ∀ z : ↥(W ∩ closedPoints Y.left),
      ∃ y : fieldPt Qbar ⟶ Y, ptOf y.left = z := by
    intro z
    obtain ⟨y, hy⟩ := TSHeckeGal.exists_qbar_point Y.hom z (mem_closedPoints_iff.mp z.2.2)
    exact ⟨Over.homMk y (TSHeckeGal.specQbar_to_specQ_eq' _ _), hy _⟩
  choose F hF using hch
  refine Set.infinite_of_injective_forall_mem (f := F) ?_ ?_
  · intro z₁ z₂ h12
    apply Subtype.ext
    rw [← hF z₁, ← hF z₂, h12]
  · intro z
    show ptOf (F z).left ∈ W
    rw [hF z]
    exact z.2.1

/-- **`ChartIrreducible` holds** (compiled). -/
theorem chartIrreducible : ChartIrreducible := by
  intro Y π hP hS hfin E _ _ _ _ _ hN
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  obtain ⟨h, hO, himg, hval⟩ := hN
  haveI := hO
  have hrange := range_chart_eq h himg hval
  haveI : IrreducibleSpace (Spec (CommRingCat.of (integralClosure ℚ[X] E))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (integralClosure ℚ[X] E)))
  have hUirr : IsIrreducible (π.U : Set Y.left) := by
    rw [← hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ h.continuous.continuousOn
  have hdense : closure (π.U : Set Y.left) = Set.univ := by
    by_contra hne
    have hWo : IsOpen (closure (π.U : Set Y.left))ᶜ := isClosed_closure.isOpen_compl
    have hWne : ((closure (π.U : Set Y.left))ᶜ).Nonempty := Set.nonempty_compl.2 hne
    apply infinite_qbar_points hS hWo hWne
    apply (hfin OnePoint.infty).subset
    intro y hy
    show π.val (K := Qbar) y.left = OnePoint.infty
    apply val_of_not_mem
    intro hU
    exact hy (subset_closure hU)
  have := hUirr.closure
  rw [hdense] at this
  exact (irreducibleSpace_def _).2 this

/-- The value of `p(s)` at a `ℚ̄`-point is `p` at the value of `s`. -/
theorem ev_secHom {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens} (s : Γ(Y.left, W))
    (y : Spec (CommRingCat.of Qbar) ⟶ Y.left) (hx : ptOf y ∈ W) (p : ℚ[X]) :
    ev y hx (secHom Y W s p) = Polynomial.eval₂ (algebraMap ℚ Qbar) (ev y hx s) p := by
  rw [secHom, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

/-- A value that is a root of a nonzero `p` lies in the finite root set of `p`. -/
theorem mem_roots_of_eval₂ {p : ℚ[X]} (hp : p ≠ 0) {t : Qbar}
    (ht : Polynomial.eval₂ (algebraMap ℚ Qbar) t p = 0) :
    t ∈ (p.map (algebraMap ℚ Qbar)).roots := by
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp), Polynomial.IsRoot,
    Polynomial.eval_map]
  exact ht

/-- **`ChartDominant` holds** (compiled). -/
theorem chartDominant : ChartDominant := by
  classical
  intro Y π hP hS hne hfin
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  -- `π` takes the value `∞` on the complement of `U`
  have hUne : (π.U : Set Y.left).Nonempty := by
    by_contra hU
    rw [Set.not_nonempty_iff_eq_empty] at hU
    apply infinite_qbar_points hS isOpen_univ Set.univ_nonempty
    apply (hfin OnePoint.infty).subset
    intro y _
    show π.val (K := Qbar) y.left = OnePoint.infty
    apply val_of_not_mem
    intro hm
    have : ptOf y.left ∈ (π.U : Set Y.left) := hm
    rw [hU] at this
    exact this
  refine ⟨hUne, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    apply infinite_qbar_points hS π.U.isOpen hUne
    apply (Set.Finite.biUnion (Multiset.finite_toSet (p.map (algebraMap ℚ Qbar)).roots)
      (fun t _ => hfin (OnePoint.some t))).subset
    intro y hy
    let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
    have hy' : ptOf y₀ ∈ π.U := hy
    have h0 := congrArg (ev y₀ hy') hp
    rw [map_zero, ev_secHom] at h0
    refine Set.mem_biUnion (show _ ∈ {t | t ∈ (p.map (algebraMap ℚ Qbar)).roots} from mem_roots_of_eval₂ hp0 h0) ?_
    show π.val (K := Qbar) y₀ = OnePoint.some (ev y₀ hy' π.f)
    exact val_of_mem π y₀ hy'
  · -- `V` is nonempty
    have hVne : (π.V : Set Y.left).Nonempty := by
      by_contra hV
      rw [Set.not_nonempty_iff_eq_empty] at hV
      apply infinite_qbar_points hS isOpen_univ Set.univ_nonempty
      apply (hfin (OnePoint.some 0)).subset
      intro y _
      let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
      have hyU : ptOf y₀ ∈ π.U := by
        have : ptOf y₀ ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases this with h | h
        · exact h
        · have : ptOf y₀ ∈ (π.V : Set Y.left) := h
          rw [hV] at this; exact this.elim
      show π.val (K := Qbar) y₀ = OnePoint.some 0
      rw [val_of_mem π y₀ hyU]
      congr 1
      rw [ev_eq_zero_iff, π.basicOpen_f]
      intro h
      have : ptOf y₀ ∈ (π.V : Set Y.left) := h.2
      rw [hV] at this; exact this
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    apply infinite_qbar_points hS π.V.isOpen hVne
    apply ((hfin OnePoint.infty).union (Set.Finite.biUnion
      (Multiset.finite_toSet (p.map (algebraMap ℚ Qbar)).roots)
      (fun t _ => hfin (OnePoint.some t⁻¹)))).subset
    intro y hy
    let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
    have hy' : ptOf y₀ ∈ π.V := hy
    have h0 := congrArg (ev y₀ hy') hp
    rw [map_zero, ev_secHom] at h0
    by_cases hU : ptOf y₀ ∈ π.U
    · right
      refine Set.mem_biUnion (show _ ∈ {t | t ∈ (p.map (algebraMap ℚ Qbar)).roots} from mem_roots_of_eval₂ hp0 h0) ?_
      show π.val (K := Qbar) y₀ = OnePoint.some (ev y₀ hy' π.g)⁻¹
      rw [val_of_mem π y₀ hU]
      congr 1
      exact eq_inv_of_mul_eq_one_left (ev_f_mul_g π y₀ hU hy')
    · left
      exact val_of_not_mem π y₀ hU

/-! ## `ChartQuasiFinite` from `ChartProper`

Given properness, Mathlib's Stacks 02UP (`exists_isFinite_morphismRestrict_of_finite_preimage_singleton`)
makes a chart finite over a neighbourhood of each closed point of `𝔸¹` with finite fibre; these
neighbourhoods cover `𝔸¹` (Jacobson). A closed fibre is finite: its closed points carry `ℚ̄`-points
with `s`-values among the roots of a generator, finitely many by the finite `π`-fibres, and a
locally closed set whose closed points are finitely many consists of closed points (Jacobson). -/

/-- **The point `secMor w` of `𝔸¹`**: `q` vanishes there iff `q(s)` vanishes at `w` (compiled). -/
theorem mem_secMor_iff {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens} (s : Γ(Y.left, W))
    (w : W.toScheme) (q : ℚ[X]) :
    q ∈ (secMor Y W s w).asIdeal ↔ W.ι w ∉ Y.left.basicOpen (secHom Y W s q) := by
  have key := congrArg (fun O : W.toScheme.Opens => w ∈ O)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen W (secHom Y W s q))
  simp only [eq_iff_iff] at key
  change secHom Y W s q ∈ (W.toSpecΓ w).asIdeal ↔ _
  rw [← not_iff_not, not_not]
  exact key

/-- A `ℚ̄`-point at a point of `W` over a point of `𝔸¹` containing `q`: `q(s(point)) = 0`. -/
theorem eval_eq_zero_of_mem {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens}
    (s : Γ(Y.left, W)) (w : W.toScheme) (q : ℚ[X]) (hq : q ∈ (secMor Y W s w).asIdeal)
    (p : Spec (CommRingCat.of Qbar) ⟶ Y.left) (hp : ptOf p = W.ι w) (hx : ptOf p ∈ W) :
    Polynomial.eval₂ (algebraMap ℚ Qbar) (ev p hx s) q = 0 := by
  rw [← ev_secHom, ev_eq_zero_iff, hp]
  exact (mem_secMor_iff s w q).1 hq

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness is local on the target (instance search needs the transparency option, as in
Mathlib's own uses). -/
theorem isFinite_of_iSup {X Y' : Scheme.{0}} (f : X ⟶ Y') {ι : Type} (U : ι → Y'.Opens)
    (hU : iSup U = ⊤) (H : ∀ i, IsFinite (f ∣_ U i)) : IsFinite f :=
  IsZariskiLocalAtTarget.of_iSup_eq_top U hU H

/-- **A proper chart with finite `ℚ̄`-fibres of `s` is locally quasi-finite** (compiled). -/
theorem lqf_of_proper (Y : Over (Spec (CommRingCat.of ℚ))) (hS : SmoothOfRelativeDimension 1 Y.hom)
    (W : Y.left.Opens) (s : Γ(Y.left, W)) [IsProper (secMor Y W s)]
    (hfinS : ∀ t : Qbar,
      {y : fieldPt Qbar ⟶ Y | ∃ hy : ptOf y.left ∈ W, ev y.left hy s = t}.Finite) :
    LocallyQuasiFinite (secMor Y W s) := by
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hclosedfib : ∀ y : Spec (CommRingCat.of ℚ[X]), IsClosed ({y} : Set _) →
      (secMor Y W s ⁻¹' {y}).Finite := by
    intro y hy
    have hmax : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 hy
    have hne : y.asIdeal ≠ ⊥ := by
      intro h0
      have := hmax
      rw [h0] at this
      exact Polynomial.not_isField ℚ (Ring.isField_iff_maximal_bot.2 this)
    obtain ⟨q₀, hq₀, hq₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set C : Set Y.left := W.ι '' (secMor Y W s ⁻¹' {y}) with hCdef
    have hC : ∀ z : ↥(C ∩ closedPoints Y.left), ∃ yQ : fieldPt Qbar ⟶ Y, ptOf yQ.left = z ∧
        ∃ hy : ptOf yQ.left ∈ W, ev yQ.left hy s ∈ {t | t ∈ (q₀.map (algebraMap ℚ Qbar)).roots} := by
      intro z
      obtain ⟨⟨w, hw, hwz⟩, hzc⟩ := z.2
      obtain ⟨p, hp⟩ := TSHeckeGal.exists_qbar_point Y.hom z (mem_closedPoints_iff.mp hzc)
      have hpz : ptOf p = z := hp _
      have hx : ptOf p ∈ W := by
        rw [hpz, ← hwz]
        have : W.ι w ∈ Set.range W.ι := ⟨w, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      refine ⟨Over.homMk p (TSHeckeGal.specQbar_to_specQ_eq' _ _), hpz, hx, ?_⟩
      have hmem : q₀ ∈ (secMor Y W s w).asIdeal := by
        have hw' : secMor Y W s w = y := hw
        rw [hw']; exact hq₀
      exact mem_roots_of_eval₂ hq₀ne
        (eval_eq_zero_of_mem s w q₀ hmem p (hpz.trans hwz.symm) hx)
    choose F hF using hC
    have hCfin : (C ∩ closedPoints Y.left).Finite := by
      by_contra hinf
      haveI : Infinite ↥(C ∩ closedPoints Y.left) := Set.infinite_coe_iff.2 hinf
      apply Set.infinite_of_injective_forall_mem (f := F)
        (s := ⋃ t ∈ {t | t ∈ (q₀.map (algebraMap ℚ Qbar)).roots},
          {y : fieldPt Qbar ⟶ Y | ∃ hy : ptOf y.left ∈ W, ev y.left hy s = t})
      · intro z₁ z₂ h12
        apply Subtype.ext
        rw [← (hF z₁).1, ← (hF z₂).1, h12]
      · intro z
        obtain ⟨-, hx, hroot⟩ := hF z
        exact Set.mem_biUnion hroot ⟨hx, rfl⟩
      · exact (Multiset.finite_toSet _).biUnion fun t _ => hfinS t
    have hClc : IsLocallyClosed C :=
      (hy.preimage (secMor Y W s).continuous).isLocallyClosed.image
        W.ι.isOpenEmbedding.isInducing W.ι.isOpenEmbedding.isOpen_range.isLocallyClosed
    have hCF : C ⊆ C ∩ closedPoints Y.left := by
      have hcl : IsClosed (C ∩ closedPoints Y.left) := by
        rw [← Set.biUnion_of_singleton (C ∩ closedPoints Y.left)]
        exact hCfin.isClosed_biUnion fun z hz => hz.2
      calc C ⊆ closure C := subset_closure
        _ = closure (C ∩ closedPoints Y.left) :=
            (JacobsonSpace.closure_inter_closedPoints_eq_closure hClc).symm
        _ = C ∩ closedPoints Y.left := hcl.closure_eq
    exact Set.Finite.of_finite_image (hCfin.subset hCF) W.ι.isOpenEmbedding.injective.injOn
  haveI : JacobsonSpace (Spec (CommRingCat.of ℚ[X])) :=
    inferInstanceAs (JacobsonSpace (PrimeSpectrum ℚ[X]))
  choose Vy hyV hVfin using fun (y : {y : Spec (CommRingCat.of ℚ[X]) // IsClosed ({y} : Set _)}) =>
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton (secMor Y W s) y.1
      (hclosedfib y.1 y.2)
  have hsup : iSup Vy = ⊤ := by
    by_contra hne
    have hSne : (SetLike.coe (iSup Vy))ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      apply hne
      apply SetLike.coe_injective
      rw [h, TopologicalSpace.Opens.coe_top]
    obtain ⟨y₀, hy₀, hy₀c⟩ := nonempty_inter_closedPoints hSne
      (iSup Vy).isOpen.isClosed_compl.isLocallyClosed
    apply hy₀
    exact (le_iSup Vy ⟨y₀, mem_closedPoints_iff.mp hy₀c⟩) (hyV ⟨y₀, mem_closedPoints_iff.mp hy₀c⟩)
  haveI : IsFinite (secMor Y W s) := isFinite_of_iSup (secMor Y W s) Vy hsup hVfin
  infer_instance

/-- **`ChartQuasiFinite` from `ChartProper`** (compiled). -/
theorem chartQuasiFinite_of_proper (hP : ChartProper) : ChartQuasiFinite := by
  intro Y π h1 h2 h4
  obtain ⟨hPU, hPV⟩ := hP Y π h1 h2 h4
  constructor
  · refine lqf_of_proper Y h2 π.U π.f fun t => (h4 (OnePoint.some t)).subset ?_
    rintro y ⟨hy, hyt⟩
    show π.val (K := Qbar) y.left = OnePoint.some t
    rw [val_of_mem π y.left hy, hyt]
  · refine lqf_of_proper Y h2 π.V π.g fun t =>
      ((h4 OnePoint.infty).union (h4 (OnePoint.some t⁻¹))).subset ?_
    rintro y ⟨hy, hyt⟩
    let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
    by_cases hU : ptOf y₀ ∈ π.U
    · right
      show π.val (K := Qbar) y₀ = OnePoint.some t⁻¹
      rw [val_of_mem π y₀ hU]
      congr 1
      have hfg := ev_f_mul_g π y₀ hU hy
      have hyt' : ev y₀ hy π.g = t := hyt
      rw [hyt'] at hfg
      exact eq_inv_of_mul_eq_one_left hfg
    · left
      exact val_of_not_mem π y₀ hU

/-- **`CurveNormChart` from `ChartProper` alone** (compiled). -/
theorem curveNormChart_of_proper (hP : ChartProper) : CurveNormChart :=
  curveNormChart_of_charts hP (chartQuasiFinite_of_proper hP) chartDominant

/-- **`CurveChartInf` from `ChartProper` alone** (compiled). -/
theorem curveChartInf_of_proper (hP : ChartProper) : CurveChartInf :=
  curveChartInf_of_charts' hP (chartQuasiFinite_of_proper hP) chartDominant chartIrreducible

/-- **`CurveNormChart` from `ChartProper` and `ChartQuasiFinite`** (compiled). -/
theorem curveNormChart_of_pq (hP : ChartProper) (hQ : ChartQuasiFinite) : CurveNormChart :=
  curveNormChart_of_charts hP hQ chartDominant

/-- **`CurveChartInf` from `ChartProper` and `ChartQuasiFinite`** (compiled). -/
theorem curveChartInf_of_pq (hP : ChartProper) (hQ : ChartQuasiFinite) : CurveChartInf :=
  curveChartInf_of_charts' hP hQ chartDominant chartIrreducible

end HeckeRestCurve

end

#print axioms HeckeRestCurve.chartIrreducible
#print axioms HeckeRestCurve.chartDominant
#print axioms HeckeRestCurve.curveNormChart_of_pq
#print axioms HeckeRestCurve.curveChartInf_of_pq
#print axioms HeckeRestCurve.curveNormChart_of_proper
#print axioms HeckeRestCurve.curveChartInf_of_proper

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: the composite

ts-hecke's `CoverModelOfHecke` and `PropTSAll` composites with hecke-rest's reductions of its four
glue inputs: `CurveNormChart` (hence `CurveGaloisChart`) and `CurveChartInf` from the chart Props,
`HeckeFibreSizes` from three leaves on QM pairs, `HeckeNoVertRam` from `HeckeVertWitness`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestAll

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue PkgI3 TSHecke

/-- **`CoverModelOfHecke` from hecke-rest's inputs** (compiled). Leaves: `Y3Connected`,
`R1R2fp`, `TorsionStructure` (as in ts-hecke), `QMAutCard`, `SerreRigidity3`, `ALFixedPoints`
(new). Glue: `ChartProper` (curve theory, no moduli) and `HeckeVertWitness` (one unramified vertical prime: Lemma NV / good reduction). -/
theorem coverModelOfHecke_of_heckeRest (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hP : HeckeRestCurve.ChartProper)
    (hV : HeckeRestNV.HeckeVertWitness) : CoverModelOfHecke :=
  coverModelOfHecke_of_tsHecke' hconn hRR hT (HeckeRestCurve.curveNormChart_of_proper hP)
    (HeckeRestCurve.curveChartInf_of_proper hP) (HeckeRest.heckeFibreSizes_of hT hA hS hW)
    (HeckeRestNV.heckeNoVertRam_of_witness hV)

/-- **`PropTSAll` from hecke-rest's inputs** (compiled; through ts-hecke's `propTSAll_of_tsHecke'`
and prop-ts-glue's `propTSAll_final`). -/
theorem propTSAll_of_heckeRest (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hSN : SNSpecialize) (hC : KummerCompositum)
    (hKA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hP : HeckeRestCurve.ChartProper)
    (hV : HeckeRestNV.HeckeVertWitness) : PropTSAll :=
  propTSAll_of_tsHecke' t2 hR hM hSN hC hKA hO hVF hAI hOI hVI hconn hT
    (HeckeRestCurve.curveNormChart_of_proper hP)
    (HeckeRestCurve.curveChartInf_of_proper hP)
    (HeckeRest.heckeFibreSizes_of hT hA hS hW) (HeckeRestNV.heckeNoVertRam_of_witness hV)

end HeckeRestAll

end

#print axioms HeckeRestAll.coverModelOfHecke_of_heckeRest
#print axioms HeckeRestAll.propTSAll_of_heckeRest
