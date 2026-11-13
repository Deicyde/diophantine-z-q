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
#print axioms PropTSGlue.isSeparable_of_finrank_lt
#print axioms PropTSGlue.verticalResidueSeparable_of_degree
#print axioms PropTSGlue.functionFieldModel_transfer
#print axioms PropTSGlue.coverModel_transfer
#print axioms PropTSGlue.coverModelOfHecke_of_witness
