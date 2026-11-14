import ZInQKernel.Contrib.Mobius.Main
import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: `HeckeNoVertRam` (assembled by `scratch/hecke-rest/assemble.py`)

Verbatim copies from `scratch/ts-hecke/TSHecke.lean`: lines 6-889 (the prop-ts prefix:
`NoVerticalRam`, `intPolyAlg`, `vertPrime`, `NormalizationModel`, ...) and, inside
`namespace PropTSGlue`, lines 3427-3437 (`HeckeNoVertRam`, the target). New work below the
second banner. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

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

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV GlueDescent.B2Q

noncomputable section

namespace PropTSGlue

open Polynomial G0ModField PropTSRed

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


end PropTSGlue

end

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

/-! ## A local-ring witness suffices (commutative algebra, compiled)

If a ring map `ψ : B → R` to a local ring has `ψ⁻¹(𝔪_R) = Q` over `p ℤ[X]` and `ψ(p) ∉ 𝔪_R²`, then
`e(Q) = 1`. Here `B = ` the integral closure of `ℤ[X]` in `E`, which is Noetherian and normal, so
`B_Q` is a DVR (`Q` has height one over the height-one `p ℤ[X]`), and `p` is a uniformizer of `B_Q`
since its image avoids `𝔪_R²`. This is the shape of the good-reduction input: `R` is the local ring
of a smooth model at the generic point of a component of the special fibre. -/

/-- A nonzero prime of `ℤ[X]` inside `p ℤ[X]` is `p ℤ[X]` (`ℤ[X]` is a UFD, `p` is prime). -/
theorem eq_vertPrime {p : ℕ} (hp : p.Prime) (I : Ideal ℤ[X]) [hI : I.IsPrime] (h0 : I ≠ ⊥)
    (hle : I ≤ vertPrime p) : I = vertPrime p := by
  have hv : vertPrime p = Ideal.span {C (p : ℤ)} := by
    rw [vertPrime, Ideal.map_span, Set.image_singleton]
  have hCp : Prime (C (p : ℤ)) := Polynomial.prime_C_iff.2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨r, hrI, hr⟩ := hI.exists_mem_prime_of_ne_bot h0
  have hdvd : C (p : ℤ) ∣ r := by
    rw [hv] at hle
    exact Ideal.mem_span_singleton.1 (hle hrI)
  obtain ⟨u, hu⟩ := hdvd
  have hunit : IsUnit u := by
    rcases hr.irreducible.isUnit_or_isUnit hu with h | h
    · exact absurd h hCp.not_unit
    · exact h
  apply le_antisymm hle
  rw [hv, Ideal.span_le, Set.singleton_subset_iff]
  have : C (p : ℤ) = r * ↑hunit.unit⁻¹ := by
    rw [hu, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [SetLike.mem_coe, this]
  exact I.mul_mem_right _ hrI

/-- **Glue (good-reduction input, local form): a local-ring witness.** A prime `Q` of the integral
closure of `ℤ[X]` in `E` over `p ℤ[X]`, cut out by a ring map `ψ` to a local ring `R` with
`ψ(p) ∉ 𝔪_R²` (e.g. `R` the local ring at the generic point of a component of the special fibre of a
smooth model, `p` a uniformizer there). Glue, not a leaf. -/
def VertLocalWitness (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∃ (Q : Ideal (integralClosure ℤ[X] E)) (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
    (ψ : integralClosure ℤ[X] E →+* R),
    Q = (IsLocalRing.maximalIdeal R).comap ψ ∧ Q.under ℤ[X] = vertPrime p ∧
    ψ (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))) ∉ (IsLocalRing.maximalIdeal R) ^ 2

/-- **A local-ring witness gives an unramified vertical prime** (compiled). -/
theorem vertUnramWitness_of_local (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (h : VertLocalWitness E p) : VertUnramWitness E p := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  obtain ⟨Q, R, _, _, ψ, hQ, hQu, hψ⟩ := h
  haveI hQp : Q.IsPrime := by rw [hQ]; exact Ideal.comap_isPrime _ _
  refine ⟨Q, hQp, hQu, ?_⟩
  -- `B` is Noetherian and normal; `B_Q` is a Noetherian normal local domain
  haveI : IsNoetherianRing (integralClosure ℤ[X] E) :=
    IsIntegralClosure.isNoetherianRing ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  haveI : IsIntegrallyClosed (integralClosure ℤ[X] E) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc ℚ)
  set BQ := Localization.AtPrime Q
  haveI : IsNoetherianRing BQ := IsLocalization.isNoetherianRing Q.primeCompl BQ inferInstance
  haveI : IsIntegrallyClosed BQ :=
    isIntegrallyClosed_of_isLocalization BQ Q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors Q)
  -- `p ∈ Q`, and `p ≠ 0` in `B`
  set pB : integralClosure ℤ[X] E := algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))
    with hpBdef
  have hpQ : pB ∈ Q := by
    have : C (p : ℤ) ∈ Q.under ℤ[X] := by
      rw [hQu, vertPrime]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    exact this
  -- the local hom `B_Q → R`
  have hmemQ : ∀ b, b ∈ Q ↔ ψ b ∈ IsLocalRing.maximalIdeal R := fun b => by rw [hQ]; rfl
  have hunitψ : ∀ y : Q.primeCompl, IsUnit (ψ y) := by
    intro y
    have hy : (y : integralClosure ℤ[X] E) ∉ Q := y.2
    by_contra hn
    exact hy ((hmemQ _).2 ((IsLocalRing.mem_maximalIdeal _).2 hn))
  let φ : BQ →+* R := IsLocalization.lift hunitψ
  have hφ : ∀ b, φ (algebraMap _ BQ b) = ψ b := fun b => IsLocalization.lift_eq hunitψ b
  have hmap : (IsLocalRing.maximalIdeal BQ).map φ ≤ IsLocalRing.maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.comp_apply, hφ]
    exact (hmemQ b).1 hb
  set x := algebraMap (integralClosure ℤ[X] E) BQ pB with hxdef
  have hxm : x ∈ IsLocalRing.maximalIdeal BQ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hpQ
  have hxm2 : x ∉ (IsLocalRing.maximalIdeal BQ) ^ 2 := by
    intro hx
    apply hψ
    have h1 : φ x ∈ ((IsLocalRing.maximalIdeal BQ).map φ) ^ 2 := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx
    have h2 : ((IsLocalRing.maximalIdeal BQ).map φ) ^ 2 ≤ (IsLocalRing.maximalIdeal R) ^ 2 := by
      rw [sq, sq]; exact Ideal.mul_mono hmap hmap
    have h3 := h2 h1
    rwa [hxdef, hφ] at h3
  have hx0 : x ≠ 0 := fun h => hxm2 (by rw [h]; exact zero_mem _)
  haveI : IsDomain BQ := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors Q)
  -- the unique nonzero prime of `B_Q`
  have huniq : ∃! P : Ideal BQ, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal BQ, ⟨?_, inferInstance⟩, ?_⟩
    · intro h
      rw [h] at hxm
      exact hx0 (Ideal.mem_bot.1 hxm)
    · rintro P' ⟨hne, hprime⟩
      set Q' := P'.comap (algebraMap (integralClosure ℤ[X] E) BQ) with hQ'def
      haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
      have hQ'le : Q' ≤ Q := by
        intro b hb
        by_contra hbQ
        have hu : IsUnit (algebraMap (integralClosure ℤ[X] E) BQ b) :=
          IsLocalization.map_units BQ (⟨b, hbQ⟩ : Q.primeCompl)
        exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hb hu)
      have hmc : Q'.map (algebraMap (integralClosure ℤ[X] E) BQ) = P' :=
        IsLocalization.map_comap Q.primeCompl BQ P'
      have hQ'ne : Q' ≠ ⊥ := by
        intro h0
        apply hne
        rw [← hmc, h0, Ideal.map_bot]
      have hQ'eq : Q' = Q := by
        by_contra hneq
        have hlt : Q' < Q := lt_of_le_of_ne hQ'le hneq
        have h1 := Ideal.IsIntegral.under_lt_under (R := ℤ[X]) hlt
        have h2 : Q'.under ℤ[X] ≠ ⊥ := fun h => hQ'ne (Ideal.eq_bot_of_under_eq_bot h)
        have h3 := eq_vertPrime hp (Q'.under ℤ[X]) h2 (by rw [← hQu]; exact h1.le)
        rw [h3, hQu] at h1
        exact lt_irrefl _ h1
      rw [← hmc, hQ'eq]
      exact Localization.AtPrime.map_eq_maximalIdeal
  have hnf : ¬ IsField BQ := by
    intro hf
    have hm0 := (IsLocalRing.isField_iff_maximalIdeal_eq.1 hf)
    rw [hm0] at hxm
    exact hx0 (Ideal.mem_bot.1 hxm)
  have key : (IsIntegrallyClosed BQ ∧ ∃! P : Ideal BQ, P ≠ ⊥ ∧ P.IsPrime) ↔
      IsDiscreteValuationRing BQ := (IsDiscreteValuationRing.TFAE BQ hnf).out 4 1
  haveI : IsDiscreteValuationRing BQ := key.mp ⟨inferInstance, huniq⟩
  -- `x` is a uniformizer
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible BQ
  obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal BQ := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at hxu
      exact (IsLocalRing.mem_maximalIdeal _).1 hxm (hxu ▸ u.isUnit)
    · rfl
    · exfalso
      apply hxm2
      have e : (u : BQ) * ϖ ^ (n + 1 + 1) = ((u : BQ) * ϖ ^ n * ϖ) * ϖ := by ring
      rw [hxu, e, sq]
      exact Ideal.mul_mem_mul ((IsLocalRing.maximalIdeal BQ).mul_mem_left _ hϖm) hϖm
  rw [hn1, pow_one] at hxu
  have hPm : (Q.under ℤ[X]).map (algebraMap ℤ[X] BQ) = IsLocalRing.maximalIdeal BQ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E) BQ,
        ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ ha
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_le,
        Set.singleton_subset_iff]
      have hϖx : ϖ = ↑u⁻¹ * x := by rw [hxu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [SetLike.mem_coe, hϖx]
      apply Ideal.mul_mem_left
      rw [hxdef, hpBdef, ← IsScalarTower.algebraMap_apply]
      apply Ideal.mem_map_of_mem
      rw [hQu, vertPrime]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]
  exact hPm

/-- **Glue (good-reduction input, local form) for the Hecke cover.** For a triple with R1fp,
R1hecke, R2fp and any `E` carrying the chart, every prime `p > 324` has a local-ring witness
(`VertLocalWitness`): the local ring of a smooth model of `Y₃` over `ℤ_(p)` at the generic point of
a component of the special fibre, with `p` a uniformizer and `X` of transcendental reduction (route
GR, §3 of docs/research/hecke-rest.md). Glue, not a leaf. -/
def HeckeVertLocal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p → VertLocalWitness E p

/-- **`HeckeNoVertRam` from local-ring witnesses** (compiled). -/
theorem heckeNoVertRam_of_local (h : HeckeVertLocal) : HeckeNoVertRam :=
  heckeNoVertRam_of_witness fun Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324 =>
    vertUnramWitness_of_local E p hp (h Y Φ π h1 hh h2 E hN p hp hp324)

end HeckeRestNV

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# vert-witness: `HeckeVertWitness` from good reduction of `Y₃` (route GR)

Everything above this banner is `scratch/hecke-rest/NoVert.lean` verbatim (lines 1-1261, i.e.
without its trailing `#print axioms` lines). New work:

* `VertGaussWitness E p` (glue target, valuation form): a valuation subring of `E` whose
  valuation restricts on `ℤ[X]` to the Gauss valuation at `p` and in which `p` generates the
  maximal ideal. `vertLocalWitness_of_gauss` (compiled): it gives hecke-rest's
  `VertLocalWitness`, hence `VertUnramWitness`.
* `ShimuraGoodReduction` (**leaf**, Morita 1981 / Carayol 1986 / Kottwitz 1992, locators
  UNVERIFIED): for `p > 324`, a smooth proper model `𝒴` of `Y₃` over `ℤ_(p)` with its universal
  family, the moduli bijection on `ℚ̄`-points and the Hecke automorphisms over `ℤ_(p)`.
* `ModelGaussGlue` (**glue**, not proved): the model gives a `VertGaussWitness` for every `E`
  carrying the normalization chart (comparison of generic fibres, the local ring at the generic
  point of a component of the special fibre, nonconstant reduction of the coordinate via the
  tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`; docs/research/vert-witness.md §3).
* `heckeVertWitness_of_goodReduction : ShimuraGoodReduction → ModelGaussGlue →
  HeckeVertWitness` (compiled).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace VertWitness

open Polynomial G0ModField PropTSRed PropTSGlue HeckeRestNV
open CategoryTheory AlgebraicGeometry Limits LeafQM.AV

/-! ## Part 1: the Gauss-valuation witness and its commutative algebra -/

/-- **Glue target (valuation form of the good-reduction output).** A valuation subring `A` of `E`
such that, on `ℤ[X]` (mapped to `E` through `ℚ[X]`), `v_A ≤ 1` everywhere and `v_A(f) < 1` exactly
on `p ℤ[X]` (so `v_A` restricts to the Gauss valuation: `X` has transcendental reduction), and
`p` generates the maximal ideal of `A` (`v_A(x) < 1 → v_A(x) ≤ v_A(p)`: ramification index 1).
For `Y₃`: `A` is the local ring of the smooth model `𝒴/ℤ_(p)` at the generic point of a component
of the special fibre (docs/research/vert-witness.md §3). -/
def VertGaussWitness (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∃ A : ValuationSubring E,
    (∀ f : ℤ[X], A.valuation (algebraMap ℤ[X] E f) ≤ 1) ∧
    (∀ f : ℤ[X], A.valuation (algebraMap ℤ[X] E f) < 1 ↔ f ∈ vertPrime p) ∧
    (∀ x : E, A.valuation x < 1 → A.valuation x ≤ A.valuation (algebraMap ℤ[X] E (C (p : ℤ))))

/-- `p` maps to `(p : E)`, which is nonzero (`ℚ → E` is injective). -/
theorem intPolyAlg_C_ne_zero (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) (hp : p ≠ 0) :
    letI := intPolyAlg E
    algebraMap ℤ[X] E (C (p : ℤ)) ≠ 0 := by
  letI := intPolyAlg E
  have e : algebraMap ℤ[X] E (C (p : ℤ)) = algebraMap ℚ[X] E (C (p : ℚ)) := by
    show algebraMap ℚ[X] E ((C (p : ℤ)).map (Int.castRingHom ℚ)) = _
    rw [Polynomial.map_C]; simp
  rw [e]
  show ((algebraMap ℚ[X] E).comp C) (p : ℚ) ≠ 0
  exact (map_ne_zero_iff _ ((algebraMap ℚ[X] E).comp C).injective).2 (by exact_mod_cast hp)

/-- **A Gauss-valuation witness gives a local-ring witness** (compiled). -/
theorem vertLocalWitness_of_gauss (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) (hp : p.Prime)
    (h : VertGaussWitness E p) : VertLocalWitness E p := by
  letI := intPolyAlg E
  obtain ⟨A, h1, h2, h3⟩ := h
  set v := A.valuation
  -- `ℤ[X] → A`
  let φ : ℤ[X] →+* A :=
    (algebraMap ℤ[X] E).codRestrict A.toSubring (fun f => (A.valuation_le_one_iff _).1 (h1 f))
  letI : Algebra ℤ[X] A := φ.toAlgebra
  haveI : IsScalarTower ℤ[X] A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the integral closure lies in `A`
  have hmem : ∀ b : integralClosure ℤ[X] E, (b : E) ∈ A := by
    intro b
    have hb : IsIntegral A (b : E) := IsIntegral.tower_top (R := ℤ[X]) b.2
    have hint : Valuation.Integers v A :=
      { hom_inj := Subtype.val_injective
        map_le_one := fun r => A.valuation_le_one r
        exists_of_le_one := fun x hx => ⟨⟨x, (A.valuation_le_one_iff x).1 hx⟩, rfl⟩ }
    exact (A.valuation_le_one_iff _).1 (hint.isIntegral_iff_v_le_one.1 hb)
  let ψ : integralClosure ℤ[X] E →+* A :=
    ((integralClosure ℤ[X] E).val.toRingHom).codRestrict A.toSubring hmem
  have hψ : ∀ b, ((ψ b : A) : E) = (b : E) := fun _ => rfl
  have hψalg : ∀ f : ℤ[X], ((ψ (algebraMap ℤ[X] (integralClosure ℤ[X] E) f) : A) : E) =
      algebraMap ℤ[X] E f := fun _ => rfl
  refine ⟨(IsLocalRing.maximalIdeal A).comap ψ, A, inferInstance, inferInstance, ψ, rfl, ?_, ?_⟩
  · ext f
    rw [Ideal.under, Ideal.mem_comap, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff,
      ← h2 f]
    rfl
  · set a : A := ψ (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))) with ha
    have hav : v (a : E) = v (algebraMap ℤ[X] E (C (p : ℤ))) := rfl
    have ha0 : v (a : E) ≠ 0 := by
      rw [hav, Ne, Valuation.zero_iff]
      exact intPolyAlg_C_ne_zero E p hp.ne_zero
    have ha1 : v (a : E) < 1 := by
      rw [hav, h2]
      rw [vertPrime]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    intro hsq
    have key : ∀ y ∈ (IsLocalRing.maximalIdeal A) ^ 2, v (y : E) ≤ v (a : E) * v (a : E) := by
      intro y hy
      rw [sq] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro x hx z hz
        have hx' : v (x : E) ≤ v (a : E) :=
          hav ▸ h3 _ ((ValuationSubring.valuation_lt_one_iff A x).1 hx)
        have hz' : v (z : E) ≤ v (a : E) :=
          hav ▸ h3 _ ((ValuationSubring.valuation_lt_one_iff A z).1 hz)
        rw [Subring.coe_mul, Valuation.map_mul]
        exact mul_le_mul' hx' hz'
      · intro x z hx hz
        rw [Subring.coe_add]
        exact le_trans (Valuation.map_add v _ _) (max_le hx hz)
    have hle := key a hsq
    have hlt : v (a : E) * v (a : E) < v (a : E) :=
      mul_lt_of_lt_one_right (zero_lt_iff.2 ha0) ha1
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

/-- **A Gauss-valuation witness gives an unramified vertical prime** (compiled). -/
theorem vertUnramWitness_of_gauss (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (h : VertGaussWitness E p) : VertUnramWitness E p :=
  vertUnramWitness_of_local E p hp (vertLocalWitness_of_gauss E p hp h)

/-- **Glue (valuation form): a Gauss-valuation witness for the Hecke cover.** -/
def HeckeVertGauss : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p → VertGaussWitness E p

/-- **`HeckeVertWitness` from Gauss-valuation witnesses** (compiled). -/
theorem heckeVertWitness_of_gauss (h : HeckeVertGauss) : HeckeVertWitness :=
  fun Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324 =>
    vertUnramWitness_of_gauss E p hp (h Y Φ π h1 hh h2 E hN p hp hp324)

/-! ## Part 2: the leaf (good reduction of `Y₃` at `p > 324`) -/

/-- The prime ideal `(p)` of `ℤ`. -/
abbrev pIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

instance pIdeal_isPrime (p : ℕ) [hp : Fact p.Prime] : (pIdeal p).IsPrime :=
  (Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.1 hp.out)

/-- `ℤ_(p)`, the localization of `ℤ` at `(p)`. -/
abbrev Zloc (p : ℕ) [Fact p.Prime] : Type := Localization.AtPrime (pIdeal p)

/-- **The smooth model of `Y₃` over `ℤ_(p)` (the data asserted by the leaf).** A scheme `𝒴`
over `ℤ_(p)`, proper and smooth of relative dimension 1, with a family `𝒜 → 𝒴` of level-3 QM
abelian surfaces (`QMFamily`: proper smooth of relative dimension 2, `ι(a)` and level sections
`η(a)`), such that

* (fibres) for every field `K ⊇ ℚ`, the fibre of `𝒜` at every `K`-point of `𝒴` is an object
  `(A, ι, η)` over `K` (`IsFibreOf`; a `K`-point of `𝒴` is automatically over `ℤ_(p)`, as
  `Hom(ℤ_(p), K)` is a singleton in characteristic 0);
* (moduli on `ℚ̄`-points) two `ℚ̄`-points with isomorphic fibres are equal, and every object over
  `ℚ̄` is a fibre;
* (Hecke) each twist `α ∈ Aut 𝒪` and each `u ∈ 𝒪^×` is induced on `ℚ̄`-points by an automorphism of
  `𝒴` over `ℤ_(p)`;
* (guard, as in R1fp) `𝒴` has a `ℚ̄`-point (without it `𝒴 = ∅` would satisfy every clause if
  `QML3 ℚ̄` were mis-encoded as empty). -/
def IsShimuraModel (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : Prop :=
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : Spec (CommRingCat.of K) ⟶ 𝒴.left),
      ∃ P : QML3 K, IsFibreOf 𝒜 y P) ∧
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → M3.mk P = M3.mk P' → y = y') ∧
    (∀ P : QML3 Qbar, ∃ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, IsFibreOf 𝒜 y P) ∧
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g : 𝒴 ≅ 𝒴, ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.hom.left) P' → M3.mk P' = M3.rightMul u (M3.mk P)) ∧
    Nonempty (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left)

/-- The leaf's assertion at `p`: some `(𝒴, 𝒜)` is a smooth model as in `IsShimuraModel`. -/
def ShimuraSmoothModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜

/-- **Leaf: good reduction of `Y₃` at the primes `p > 324`** (in the field-point form of the
representability of the integral moduli problem).

*Published statement* (locators UNVERIFIED; no network): for an indefinite quaternion algebra `B`
over `ℚ` of discriminant `D`, a maximal order `𝒪`, and a neat open compact `K = ∏ K_ℓ ⊂ 𝒪̂^×`
with `K_p = 𝒪_p^× ≅ GL₂(ℤ_p)` for a prime `p ∤ D`, the moduli problem of abelian surfaces with
`𝒪`-action (and, in the PEL form, a principal polarization of the fixed Rosati type) and
`K`-level structure, on `ℤ_(p)`-schemes, is representable by a smooth proper curve over `ℤ_(p)`
whose generic fibre is the Shimura curve `Sh_K` over `ℚ`.
- R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5 (1992), 373-444,
  §5 (bibliographic identity established in docs/research/locators.md row R1; §5 itself unread,
  UNVERIFIED): PEL moduli with neat `K^p` and hyperspecial `K_p` are smooth over `𝒪_{E,(p)}`;
  proper when `B` is a division algebra. This covers the level `K₃` at `3 ∣ D` (`3 ≠ p`).
- K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), §1-§4
  (UNVERIFIED): the polarization-free moduli of `(A, ι)` with level structure over `ℤ[1/DN]`.
- Y. Morita, *Reduction modulo 𝔓 of Shimura curves*, Hokkaido Math. J. 10 (1981), 209-238
  (main theorem; number UNVERIFIED): good reduction of `Sh_K` at `p ∤ D·level`.
- H. Carayol, *Sur la mauvaise réduction des courbes de Shimura*, Compositio Math. 59 (1986),
  151-230 (UNVERIFIED; its main construction is for totally real `F ≠ ℚ`, so cite Kottwitz or
  Buzzard first). Whether Morita and Carayol allow level at a prime dividing `D` is UNVERIFIED.

Here `B = (2, −3)`, `D = 6`, `K = K₃` (full level 3, neat), and `p > 324` (so `p ∤ 6`).

*Why this Lean form is a consequence, never stronger*: restrict the representing isomorphism to
`Spec K` for fields `K` of characteristic 0 (fibre clause: the object at `y` is `y*` of the
universal object; this is the shape of `IsFibreOf`, as in R1fp's `R1famProps`), and to
`K = ℚ̄` for the bijection (as in R1fp, the polarization is dropped by Lemma P in characteristic 0);
`twist α` and `rightMul u` are automorphisms of the moduli functor over `ℤ_(p)` (defined on
families over any base), hence by Yoneda automorphisms of `𝒴` over `ℤ_(p)`, which act on
`ℚ̄`-points as stated. Only `p > 324` is asserted (the published range is `p ∤ 6`). The leaf
says nothing about a coordinate on `𝒴/Γ'`; that is glue (`ModelGaussGlue`). -/
def ShimuraGoodReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraSmoothModel p

/-- **CM objects exist over `ℚ̄`** (an input of the coordinate glue: it pins the normalization of
the coordinate by the three CM orbits): level-3 QM surfaces over `ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]`
and `ℤ[√−6]`. Derived from the bundle leaf `R1R2fp` (`cmObjectsExist_of_R1R2fp`). -/
def CMObjectsExist : Prop :=
  (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧ (∃ P : QML3 Qbar, HasCM24 P.q)

/-- **`CMObjectsExist` from the bundle leaf `R1R2fp`** (compiled: `CMExists` on `X₆`, a level
structure from `X6Surj`, and invariance of the CM predicates under isomorphism). -/
theorem cmObjectsExist_of_R1R2fp (hRR : R1R2fp) : CMObjectsExist := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, hX, -, hE, -, hsurj, -⟩ := hRR
  obtain ⟨-, -, -, -, -, hf⟩ := hX
  have lift : ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
      ∃ P' : QML3 Qbar, Nonempty (QMIso P.q P'.q) := by
    intro x P hP
    obtain ⟨y, hy⟩ := hsurj.2 x
    obtain ⟨P', hP'⟩ := Quotient.exists_rep (s := isoSetoid Qbar) (Φ Qbar y)
    have h1 := hf y P' hP'.symm
    rw [hy, hP] at h1
    exact ⟨P', Quotient.exact h1⟩
  obtain ⟨⟨x₄, P₄, h₄, c₄⟩, ⟨x₃, P₃, h₃, c₃⟩, ⟨x₂, P₂, h₂, c₂⟩⟩ := hE
  obtain ⟨Q₄, ⟨g₄⟩⟩ := lift x₄ P₄ h₄
  obtain ⟨Q₃, ⟨g₃⟩⟩ := lift x₃ P₃ h₃
  obtain ⟨Q₂, ⟨g₂⟩⟩ := lift x₂ P₂ h₂
  exact ⟨⟨Q₄, HasCM4.of_iso g₄ c₄⟩, ⟨Q₃, HasCM3.of_iso g₃ c₃⟩, ⟨Q₂, HasCM24.of_iso g₂ c₂⟩⟩

/-! ## Part 3: the glue and the composite -/

/-- **Glue (route GR, not proved): the smooth model gives a Gauss-valuation witness.** For a
prime `p > 324` with a smooth model as in `ShimuraSmoothModel`, a triple with R1fp, R1hecke, R2fp,
and any finite Galois `E/ℚ(X)` carrying the normalization chart, `E` has a valuation subring
restricting to the Gauss valuation of `ℚ(X)` at `p` in which `p` is a uniformizer. Proof outline
(docs/research/vert-witness.md §3):
(b) R1univProps classifies the generic fibre `𝒴_ℚ` with the pulled-back family by `g : 𝒴_ℚ → Y`;
    `g` is bijective on `ℚ̄`-points (the moduli clauses of both), hence an isomorphism of smooth
    proper curves (char 0, Zariski's main theorem); so `E = ℚ(Y) = ℚ(𝒴)` with `X = π`;
(c) smoothness over `ℤ_(p)`: the special fibre is smooth, hence reduced, and nonempty (proper +
    flat + nonempty generic fibre); at the generic point `ξ` of a component, `𝒪_{𝒴,ξ}` is a DVR
    with uniformizer `p` and fraction field `E`;
(d) the Hecke automorphisms generate a group `G'` of order `≤ 324 < p` acting on `𝒴` over
    `ℤ_(p)`; the tame quotient `𝒵 = 𝒴/G'` commutes with base change, is smooth proper of genus 0
    with geometrically connected fibres, and its generic fibre is `P¹_ℚ` in the coordinate `π`
    (R2fp's fibre clause, with `𝒪^× ↠ (𝒪/3𝒪)^×` by strong approximation); `𝒵` has smooth fibres
    (normal quotients of smooth curves); the three CM sections `0, ∞, −16/27` have distinct
    reductions (the fixed scheme of each `g ≠ 1` is finite étale over `ℤ_(p)`, stabilizers of
    special points are cyclic, and the generic stabilizer orders `4, 6, 2` differ), so the
    coordinate `π` is an isomorphism
    `𝒵 ≅ P¹_{ℤ_(p)}` (`PGL₂(ℤ_(p))` acts simply transitively on triples of pairwise disjoint
    sections); hence `π` is regular at `ξ` with transcendental reduction, which is the first two
    clauses of `VertGaussWitness`. -/
def ModelGaussGlue : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraSmoothModel p → CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
      ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
        [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
        [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E → VertGaussWitness E p

/-- **`HeckeVertGauss` from the leaf and the glue** (compiled). -/
theorem heckeVertGauss_of_goodReduction (hL : ShimuraGoodReduction) (hCM : CMObjectsExist)
    (hG : ModelGaussGlue) : HeckeVertGauss := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324
  haveI : Fact p.Prime := ⟨hp⟩
  exact hG p hp324 (hL p hp324) hCM Y Φ π h1 hh h2 E hN

/-- **`HeckeVertWitness` from good reduction of `Y₃` and the GR glue** (compiled). -/
theorem heckeVertWitness_of_goodReduction (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hG : ModelGaussGlue) : HeckeVertWitness :=
  heckeVertWitness_of_gauss (heckeVertGauss_of_goodReduction hL (cmObjectsExist_of_R1R2fp hRR) hG)

/-- **`HeckeNoVertRam` from good reduction of `Y₃` and the GR glue** (compiled). -/
theorem heckeNoVertRam_of_goodReduction (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hG : ModelGaussGlue) : HeckeNoVertRam :=
  heckeNoVertRam_of_witness (heckeVertWitness_of_goodReduction hL hRR hG)

/-! ## Part 4: splitting `ModelGaussGlue` into a scheme-local piece and the coordinate piece -/

/-- `p ∈ ℤ[X]` maps to `(p : E)`. -/
theorem intPolyAlg_C_natCast (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) :
    letI := intPolyAlg E
    algebraMap ℤ[X] E (C (p : ℤ)) = (p : E) := by
  letI := intPolyAlg E
  show algebraMap ℚ[X] E ((C (p : ℤ)).map (Int.castRingHom ℚ)) = _
  rw [Polynomial.map_C]
  show ((algebraMap ℚ[X] E).comp C) ((Int.castRingHom ℚ) (p : ℤ)) = _
  simp

/-- **Glue target (DVR form).** A discrete valuation ring `R` embedded in `E` with fraction field
`E`, maximal ideal `(p)`, containing the image of `ℤ[X]`, whose maximal ideal meets `ℤ[X]` in
`p ℤ[X]`. (For `Y₃`: `R = 𝒪_{𝒴,ξ}`, `ξ` the generic point of a component of the special fibre of
the smooth model.) -/
def VertDVRWitness (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (ι : R →+* E),
    Function.Injective ι ∧ (∀ x : E, ∃ a b : R, b ≠ 0 ∧ x * ι b = ι a) ∧
    IsLocalRing.maximalIdeal R = Ideal.span {(p : R)} ∧
    ∀ f : ℤ[X], ∃ s : R, ι s = algebraMap ℤ[X] E f ∧
      (s ∈ IsLocalRing.maximalIdeal R ↔ f ∈ vertPrime p)

/-- **A DVR witness gives a Gauss-valuation witness** (compiled). -/
theorem vertGaussWitness_of_DVR (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ)
    (h : VertDVRWitness E p) : VertGaussWitness E p := by
  letI := intPolyAlg E
  obtain ⟨R, _, _, _, ι, hinj, hfrac, hmax, hcoord⟩ := h
  have hval : ∀ x : E, x ∈ ι.range ∨ x⁻¹ ∈ ι.range := by
    intro x
    obtain ⟨a, b, hb, hx⟩ := hfrac x
    have hb' : ι b ≠ 0 := (map_ne_zero_iff ι hinj).2 hb
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · -- `b = a c`
      by_cases hx0 : x = 0
      · right; rw [hx0, inv_zero]; exact zero_mem _
      · right
        refine ⟨c, ?_⟩
        have ha : ι a ≠ 0 := by
          intro h0; rw [h0] at hx; exact mul_ne_zero hx0 hb' hx
        have hx' : x * (ι a * ι c) = ι a := by rw [← map_mul, hc]; exact hx
        have : x * ι c = 1 := by
          apply mul_left_cancel₀ ha
          calc ι a * (x * ι c) = x * (ι a * ι c) := by ring
            _ = ι a := hx'
            _ = ι a * 1 := (mul_one _).symm
        exact (eq_inv_of_mul_eq_one_right this).symm ▸ rfl
    · -- `a = b c`
      left
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hb'
      rw [← map_mul, hc, ← hx, mul_comm]
  let A : ValuationSubring E := { ι.range with mem_or_inv_mem' := hval }
  have hA : ∀ y : E, y ∈ A ↔ y ∈ ι.range := fun _ => Iff.rfl
  set v := A.valuation
  have hunit : ∀ s : R, v (ι s) < 1 ↔ s ∈ IsLocalRing.maximalIdeal R := by
    intro s
    rw [← ValuationSubring.valuation_lt_one_iff A ⟨ι s, ⟨s, rfl⟩⟩, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨t, ht⟩ := (u⁻¹ : Aˣ).1.2
      have hu' : (u : A).1 = ι s := by rw [hu]
      have hst : s * t = 1 := hinj (by
        rw [map_mul, ht, map_one, ← hu']
        exact congrArg Subtype.val (Units.mul_inv u))
      exact ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, rfl⟩
    · intro hs
      exact hs.map (ι.codRestrict A.toSubring (fun r => ⟨r, rfl⟩))
  refine ⟨A, fun f => ?_, fun f => ?_, fun x hx => ?_⟩
  · obtain ⟨s, hs, -⟩ := hcoord f
    rw [← hs]
    exact (A.valuation_le_one_iff _).2 ⟨s, rfl⟩
  · obtain ⟨s, hs, hiff⟩ := hcoord f
    rw [← hs, hunit, hiff]
  · obtain ⟨s, rfl⟩ := (A.valuation_le_one_iff x).1 hx.le
    have hs : s ∈ IsLocalRing.maximalIdeal R := (hunit s).1 hx
    rw [hmax, Ideal.mem_span_singleton] at hs
    obtain ⟨t, rfl⟩ := hs
    rw [intPolyAlg_C_natCast, map_mul, Valuation.map_mul, map_natCast]
    have ht : v (ι t) ≤ 1 := (A.valuation_le_one_iff _).2 ⟨t, rfl⟩
    calc v (p : E) * v (ι t) ≤ v (p : E) * 1 := mul_le_mul' le_rfl ht
      _ = v (p : E) := mul_one _

/-- **Glue (STANDARD scheme theory, not proved): the local ring at the generic point of a
component of the special fibre.** For `𝒴` proper and smooth of relative dimension 1 over
`ℤ_(p)` and nonempty, some point `ξ` has a stalk that is a discrete valuation ring with maximal
ideal `(p)`. (Proof: `𝒴 → Spec ℤ_(p)` is flat and proper, so its image is open, closed and
nonempty, hence everything; let `ξ` be a generic point of a component of the special fibre
`𝒴_p`, which is smooth over `𝔽_p`, hence reduced; `𝒪_{𝒴,ξ}/p = 𝒪_{𝒴_p,ξ}` is a reduced local
ring of dimension 0, i.e. a field; `p` is a nonzerodivisor (flatness) in the Noetherian local
ring `𝒪_{𝒴,ξ}`, whose maximal ideal is therefore principal generated by a nonzerodivisor: a DVR.
Stacks 00PD for the last step; EGA IV 6.8 / 17.5.1 for smooth ⇒ flat with smooth fibres;
locators UNVERIFIED.) -/
def SpecialFibreDVR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom → Nonempty 𝒴.left →
    ∃ ξ : 𝒴.left, ∃ _ : IsDomain (𝒴.left.presheaf.stalk ξ),
      IsDiscreteValuationRing (𝒴.left.presheaf.stalk ξ) ∧
      IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
        Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)}

/-- **A Noetherian local ring whose maximal ideal is generated by a nonzerodivisor is a DVR**
(compiled; Stacks 00PD, UNVERIFIED tag). Krull's intersection theorem writes every nonzero `a` as
`t^n · unit`; products of such are nonzero since `t` is a nonzerodivisor. -/
theorem dvr_of_maximalIdeal_eq_span {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : t ∈ nonZeroDivisors R) (hm : IsLocalRing.maximalIdeal R = Ideal.span {t}) :
    ∃ _ : IsDomain R, IsDiscreteValuationRing R := by
  set m := IsLocalRing.maximalIdeal R with hmdef
  have hpow : ∀ n : ℕ, m ^ n = Ideal.span {t ^ n} := by
    intro n; rw [hm, Ideal.span_singleton_pow]
  have hfac : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ a = t ^ n * u := by
    intro a ha
    have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing m (Ideal.IsPrime.ne_top')
    have hex : ∃ n : ℕ, a ∉ m ^ n := by
      by_contra h
      push Not at h
      apply ha
      have : a ∈ ⨅ n : ℕ, m ^ n := Submodule.mem_iInf _ |>.2 h
      rw [hK] at this
      exact this
    classical
    have hN : a ∉ m ^ Nat.find hex := Nat.find_spec hex
    have hN0 : Nat.find hex ≠ 0 := by
      intro h
      apply hN
      rw [h, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
    have han : a ∈ m ^ n := by
      have := Nat.find_min hex (show n < Nat.find hex by omega)
      push Not at this
      exact this
    rw [hpow, Ideal.mem_span_singleton] at han
    obtain ⟨u, hu⟩ := han
    refine ⟨n, u, ?_, hu⟩
    by_contra hu'
    apply hN
    have hum : u ∈ m := (IsLocalRing.mem_maximalIdeal u).2 hu'
    rw [hm, Ideal.mem_span_singleton] at hum
    obtain ⟨w, hw⟩ := hum
    rw [hn, hpow, Ideal.mem_span_singleton, hu, hw]
    exact ⟨w, by rw [Nat.succ_eq_add_one]; ring⟩
  have htn : ∀ n : ℕ, t ^ n ∈ nonZeroDivisors R := fun n => pow_mem ht n
  haveI : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hfac a hne.1
    obtain ⟨k, w, hw, rfl⟩ := hfac b hne.2
    have h0 : t ^ (n + k) * (u * w) = 0 := by rw [← hab]; ring
    have := (mem_nonZeroDivisors_iff.1 (htn (n + k))).1 _ h0
    exact (hu.mul hw).ne_zero this
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  refine ⟨inferInstance, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨t, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t ht0 hm, fun {x} hx => ?_⟩⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, rfl⟩

/-- **Glue (STANDARD scheme theory, not proved), uniformizer form of `SpecialFibreDVR`**: some
point `ξ` of a nonempty proper smooth relative curve over `ℤ_(p)` has `𝔪_ξ = (p)` with `p` a
nonzerodivisor in `𝒪_{𝒴,ξ}`. (The generic point of a component of the special fibre: `𝒪_ξ/p` is a
local ring of the reduced special fibre at a generic point, hence a field; `p` is regular by
flatness. What Mathlib 4.35 lacks: "smooth over a field ⇒ reduced", generic points of fibres,
stalks of fibres as quotients.) -/
def SpecialFibreUniformizer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom → Nonempty 𝒴.left →
    ∃ ξ : 𝒴.left,
      IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
        Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)} ∧
      (p : 𝒴.left.presheaf.stalk ξ) ∈ nonZeroDivisors (𝒴.left.presheaf.stalk ξ)

/-- `p ≠ 0` in every stalk of `Spec ℤ_(p)`. -/
theorem natCast_ne_zero_stalk_Spec (p : ℕ) [hp : Fact p.Prime]
    (s : Spec (CommRingCat.of (Zloc p))) :
    (p : (Spec (CommRingCat.of (Zloc p))).presheaf.stalk s) ≠ 0 := by
  have hinj := germ_injective_of_isIntegral (Spec (CommRingCat.of (Zloc p))) (U := ⊤) s trivial
  have h1 : ((p : Γ(Spec (CommRingCat.of (Zloc p)), ⊤))) ≠ 0 := by
    intro h0
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).hom.hom h0
    rw [map_natCast, map_zero] at h2
    have h3 : algebraMap ℤ (Zloc p) (p : ℤ) = 0 := by simpa using h2
    have hinjZ : Function.Injective (algebraMap ℤ (Zloc p)) :=
      IsLocalization.injective (Zloc p) (Ideal.primeCompl_le_nonZeroDivisors (pIdeal p))
    have : (p : ℤ) = 0 := hinjZ (by rw [map_zero]; exact h3)
    exact hp.out.ne_zero (by exact_mod_cast this)
  intro h0
  apply h1
  apply hinj
  rw [map_natCast, map_zero]
  exact h0

/-- **`p` is a nonzerodivisor in every stalk of a flat `ℤ_(p)`-scheme** (compiled: flatness of the
stalk maps, `Module.Flat.isSMulRegular_of_nonZeroDivisors`). -/
theorem natCast_mem_nonZeroDivisors_stalk (p : ℕ) [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) [Flat 𝒴.hom] (ξ : 𝒴.left) :
    (p : 𝒴.left.presheaf.stalk ξ) ∈ nonZeroDivisors (𝒴.left.presheaf.stalk ξ) := by
  have hflat := Flat.stalkMap 𝒴.hom ξ
  set φ := (𝒴.hom.stalkMap ξ).hom
  letI : Algebra _ _ := φ.toAlgebra
  haveI : Module.Flat _ (𝒴.left.presheaf.stalk ξ) := hflat
  have hp : (p : (Spec (CommRingCat.of (Zloc p))).presheaf.stalk (𝒴.hom.base ξ)) ∈
      nonZeroDivisors _ :=
    mem_nonZeroDivisors_of_ne_zero (natCast_ne_zero_stalk_Spec p _)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := 𝒴.left.presheaf.stalk ξ) hp
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · apply hreg
    show (p : (Spec (CommRingCat.of (Zloc p))).presheaf.stalk (𝒴.hom.base ξ)) • x =
      (p : (Spec (CommRingCat.of (Zloc p))).presheaf.stalk (𝒴.hom.base ξ)) • (0 : 𝒴.left.presheaf.stalk ξ)
    rw [smul_zero, Algebra.smul_def, map_natCast]
    exact hx
  · apply hreg
    show (p : (Spec (CommRingCat.of (Zloc p))).presheaf.stalk (𝒴.hom.base ξ)) • x =
      (p : (Spec (CommRingCat.of (Zloc p))).presheaf.stalk (𝒴.hom.base ξ)) • (0 : 𝒴.left.presheaf.stalk ξ)
    rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm]
    exact hx

/-- **Glue (STANDARD scheme theory, not proved), maximal-ideal form**: some point `ξ` of a nonempty
proper smooth relative curve over `ℤ_(p)` has `𝔪_ξ = (p)` (a generic point of a component of the
special fibre, which is reduced since it is smooth over `𝔽_p`; Mathlib 4.35 lacks "smooth over a
field ⇒ reduced"). -/
def SpecialFibreMaxIdeal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom → Nonempty 𝒴.left →
    ∃ ξ : 𝒴.left, IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
      Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)}

/-- **At a minimal prime `𝔮` of a radical ideal `I`, the maximal ideal of `A_𝔮` is `I A_𝔮`**
(compiled, Mathlib only). -/
theorem maximalIdeal_eq_map_of_mem_minimalPrimes {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] [IsLocalRing S] (I 𝔮 : Ideal A) [𝔮.IsPrime] [IsLocalization.AtPrime S 𝔮]
    (hI : I.IsRadical)
    (hq : 𝔮 ∈ I.minimalPrimes) :
    IsLocalRing.maximalIdeal S = I.map (algebraMap A S) := by
  have hIq : I ≤ 𝔮 := hq.1.2
  apply le_antisymm
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 S, Ideal.map_le_iff_le_comap]
    intro x hx
    -- `algebraMap x` lies in the radical of `I S`
    have hrad : algebraMap A S x ∈ (I.map (algebraMap A S)).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hIP, hP⟩
      have hPc : (Ideal.comap (algebraMap A S) P).IsPrime := Ideal.comap_isPrime _ _
      have hle : Ideal.comap (algebraMap A S) P ≤ 𝔮 := by
        rw [← IsLocalization.AtPrime.comap_maximalIdeal S 𝔮]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP.ne_top)
      have hge : 𝔮 ≤ Ideal.comap (algebraMap A S) P :=
        hq.2 ⟨hPc, Ideal.map_le_iff_le_comap.1 hIP⟩ hle
      exact hge hx
    obtain ⟨n, hn⟩ := hrad
    rw [← map_pow] at hn
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔮.primeCompl S).1 hn
    simp only at hs
    have h' : algebraMap A S (x ^ n * s) = algebraMap A S a := by rw [map_mul]; exact hs
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := 𝔮.primeCompl) (S := S) h'
    -- `c * (x^n * s) = c * a ∈ I`
    have hmem : (c * s : A) * x ^ n ∈ I := by
      have : (c : A) * (x ^ n * s) = c * a := hc
      rw [show ((c : A) * s) * x ^ n = (c : A) * (x ^ n * s) by ring, this]
      exact I.mul_mem_left _ a.2
    have hmem' : ((c * s : A) * x) ^ (n + 1) ∈ I := by
      rw [show ((c * s : A) * x) ^ (n + 1) = (c * s : A) ^ n * ((c * s : A) * x ^ n) * x by ring]
      exact I.mul_mem_right _ (I.mul_mem_left _ hmem)
    have hu : (c * s : A) * x ∈ I := hI ⟨n + 1, hmem'⟩
    have hcs : (c * s : A) ∈ 𝔮.primeCompl := 𝔮.primeCompl.mul_mem c.2 s.2
    have hunit : IsUnit (algebraMap A S (c * s)) := IsLocalization.map_units S ⟨_, hcs⟩
    rw [Ideal.mem_comap]
    obtain ⟨v, hv⟩ := hunit.exists_left_inv
    have : algebraMap A S x = v * algebraMap A S ((c * s : A) * x) := by
      rw [map_mul, ← mul_assoc, hv, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hu)
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 S]
    exact Ideal.map_mono hIq

/-- **Textbook (commutative algebra; not proved here): the fibres of a smooth ring map over closed
points are reduced.** For a smooth ring map `φ : R → A` (Mathlib's `RingHom.Smooth`: formally
smooth and of finite presentation) and a maximal ideal `m ⊂ R`, the ideal `m A` is radical, i.e.
`A/mA` is reduced. (`A/mA = A ⊗_R R/m` is smooth over the field `R/m`, hence regular, hence
reduced: Stacks, *Smooth ring maps* (base change) and *smooth over a field ⇒ regular*;
Matsumura, *Commutative Ring Theory*, Thm 28.7 (UNVERIFIED numbers). Mathlib 4.35 has neither
"smooth over a field ⇒ reduced" nor "⇒ regular".) -/
def SmoothFibreReduced : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A), φ.Smooth →
    ∀ m : Ideal R, m.IsMaximal → (m.map φ).IsRadical

/-- The maximal ideal of `ℤ_(p)` is `(p)`. -/
theorem maximalIdeal_Zloc (p : ℕ) [Fact p.Prime] :
    IsLocalRing.maximalIdeal (Zloc p) = Ideal.span {(p : Zloc p)} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pIdeal p) (Zloc p), Ideal.map_span,
    Set.image_singleton, map_natCast]

/-- **`SpecialFibreMaxIdeal` from `SmoothFibreReduced`** (compiled). A point `x` over the closed point
(properness: the image is closed; every point of `Spec ℤ_(p)` specializes to the closed point), an
affine open `V = Spec A ∋ x` with `ℤ_(p) → A` smooth, a minimal prime `𝔮` of `pA` inside `𝔭_x`,
and `ξ` its point: `𝒪_{𝒴,ξ} = A_𝔮` has maximal ideal `pA_𝔮` since `pA` is radical. -/
theorem specialFibreMaxIdeal_of (h : SmoothFibreReduced) : SpecialFibreMaxIdeal := by
  intro p _ 𝒴 hP hS hne
  haveI := hP
  haveI := hS
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  set R := Zloc p
  let s : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  -- a point over the closed point
  obtain ⟨y₀⟩ := hne
  have hcl : IsClosed (Set.range 𝒴.hom.base) := 𝒴.hom.isClosedMap.isClosed_range
  obtain ⟨x, hx⟩ : s ∈ Set.range 𝒴.hom.base :=
    (IsLocalRing.specializes_closedPoint (R := R) (𝒴.hom.base y₀)).mem_closed hcl ⟨y₀, rfl⟩
  -- an affine open around it
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    𝒴.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hT : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
  have e : V ≤ 𝒴.hom ⁻¹ᵁ ⊤ := fun _ _ => trivial
  set φ := (𝒴.hom.appLE ⊤ V e).hom
  have hsm : φ.Smooth := HasRingHomProperty.appLE (P := @Smooth) 𝒴.hom ‹_› ⟨⊤, hT⟩ ⟨V, hV⟩ e
  -- the maximal ideal of `Γ(Spec ℤ_(p), ⊤)`
  set Ms := hT.primeIdealOf ⟨s, trivial⟩
  have hMs : Ms.asIdeal.IsMaximal :=
    hT.primeIdealOf_isMaximal_of_isClosed _ (IsLocalRing.isClosed_singleton_closedPoint R)
  set I := Ms.asIdeal.map φ
  have hIrad : I.IsRadical := h _ _ φ hsm Ms.asIdeal hMs
  set Px := hV.primeIdealOf ⟨x, hxV⟩
  have hcomap : Px.comap φ = hT.primeIdealOf ⟨𝒴.hom.base x, e hxV⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE ⊤ hT V hV e hxV
  have hIP : I ≤ Px.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have : (Px.comap φ).asIdeal = Ms.asIdeal := by
      rw [hcomap]
      congr 2
      exact Subtype.ext hx
    rw [← this]
    rfl
  obtain ⟨𝔮, h𝔮min, -⟩ := Ideal.exists_minimalPrimes_le hIP
  haveI : 𝔮.IsPrime := h𝔮min.1.1
  set ξ := hV.fromSpec ⟨𝔮, inferInstance⟩
  have hξV : ξ ∈ V := by
    have h1 : ξ ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
    rw [hV.range_fromSpec] at h1
    exact h1
  have hloc := hV.isLocalization_stalk' ⟨𝔮, inferInstance⟩ hξV
  letI : Algebra Γ(𝒴.left, V) (𝒴.left.presheaf.stalk ξ) :=
    TopCat.Presheaf.algebra_section_stalk 𝒴.left.presheaf ⟨ξ, hξV⟩
  haveI hloc' : IsLocalization.AtPrime (𝒴.left.presheaf.stalk ξ) 𝔮 := hloc
  refine ⟨ξ, ?_⟩
  rw [maximalIdeal_eq_map_of_mem_minimalPrimes (S := 𝒴.left.presheaf.stalk ξ) I 𝔮 hIrad h𝔮min]
  have hMsK : Ms.asIdeal = Ideal.span {(p : Γ(Spec (CommRingCat.of R), ⊤))} := by
    set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    have hK : ((IsLocalRing.maximalIdeal R).comap e).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (f := e) e.surjective
    have hle : Ms.asIdeal ≤ (IsLocalRing.maximalIdeal R).comap e := by
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hMs.ne_top
      have hua : IsUnit a := by
        have h2 := hu.map e.symm
        rwa [RingEquiv.symm_apply_apply] at h2
      exact Ideal.eq_top_of_isUnit_mem _ ha hua
    rw [hMs.eq_of_le hK.ne_top hle, maximalIdeal_Zloc, ← Ideal.map_symm, Ideal.map_span,
      Set.image_singleton, map_natCast]
  have hI : I = Ideal.span {(p : Γ(𝒴.left, V))} := by
    rw [show I = Ms.asIdeal.map φ from rfl, hMsK, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI, Ideal.map_span, Set.image_singleton, map_natCast]

/-- **`SpecialFibreUniformizer` from the maximal-ideal form** (compiled: `p` is regular in every
stalk by flatness). -/
theorem specialFibreUniformizer_of_maxIdeal (h : SpecialFibreMaxIdeal) :
    SpecialFibreUniformizer := by
  intro p _ 𝒴 hP hS hne
  obtain ⟨ξ, hm⟩ := h p 𝒴 hP hS hne
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hS
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  exact ⟨ξ, hm, natCast_mem_nonZeroDivisors_stalk p 𝒴 ξ⟩

/-- **`SpecialFibreDVR` from its uniformizer form** (compiled): stalks of `𝒴` are Noetherian
(`𝒴` is locally of finite type over the Noetherian `ℤ_(p)`), then `dvr_of_maximalIdeal_eq_span`. -/
theorem specialFibreDVR_of_uniformizer (h : SpecialFibreUniformizer) : SpecialFibreDVR := by
  intro p _ 𝒴 hP hS hne
  obtain ⟨ξ, hm, hreg⟩ := h p 𝒴 hP hS hne
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hS
  haveI : IsLocallyNoetherian 𝒴.left := LocallyOfFiniteType.isLocallyNoetherian 𝒴.hom
  obtain ⟨hdom, hdvr⟩ := dvr_of_maximalIdeal_eq_span _ hreg hm
  exact ⟨ξ, hdom, hdvr, hm⟩

/-- **Glue (route GR, not proved): comparison of generic fibres and the coordinate.** Given the
smooth model `(𝒴, 𝒜)` at `p > 324` and a point `ξ` whose stalk is a DVR with maximal ideal `(p)`
(a generic point of a component of the special fibre), a triple with R1fp, R1hecke, R2fp, and any
finite Galois `E/ℚ(X)` with the normalization chart: the stalk embeds in `E` with fraction field
`E`, and the image of `ℤ[X]` lies in it with `𝔪_ξ ∩ ℤ[X] = p ℤ[X]` (`X` has transcendental
reduction). Proof outline (docs/research/vert-witness.md §3): (b) `R1univProps` of `Y` classifies
`𝒴_ℚ` with the pulled-back family by `g : 𝒴_ℚ → Y`, bijective on `ℚ̄`-points by the moduli clauses,
hence an isomorphism of smooth proper curves; `Y` is irreducible (the chart's image is dense), so
`𝒴` is integral with function field `ℚ(Y) = Frac B = E` and `𝒪_{𝒴,ξ} ↪ E`; (d) the Hecke
automorphisms generate a finite group `G'` of order prime to `p` acting on `𝒴` over `ℤ_(p)`;
the quotient `𝒵 = 𝒴/G'` commutes with base change (tame), is smooth proper over `ℤ_(p)` with
generic fibre `P¹_ℚ` in the coordinate `π` (R2fp), and the three CM sections `0, ∞, −16/27` stay
disjoint mod `p`; so `π : 𝒵 ≅ P¹_{ℤ_(p)}`, finite and surjective on special fibres, and `π` is
regular at `ξ` with transcendental reduction. -/
def ModelCoordinateGlue : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (ξ : 𝒴.left) (_ : IsDomain (𝒴.left.presheaf.stalk ξ)),
      IsDiscreteValuationRing (𝒴.left.presheaf.stalk ξ) →
      IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
        Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)} →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
      ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
        [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
        [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      letI := intPolyAlg E
      ∃ ι : 𝒴.left.presheaf.stalk ξ →+* E, Function.Injective ι ∧
        (∀ x : E, ∃ a b : 𝒴.left.presheaf.stalk ξ, b ≠ 0 ∧ x * ι b = ι a) ∧
        ∀ f : ℤ[X], ∃ s : 𝒴.left.presheaf.stalk ξ, ι s = algebraMap ℤ[X] E f ∧
          (s ∈ IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) ↔ f ∈ vertPrime p)

/-- **`ModelGaussGlue` from the two pieces** (compiled). The model is nonempty: `Y` has a
`ℚ̄`-point (R1fp), whose object is a fibre of `𝒜` (the leaf's surjectivity clause). -/
theorem modelGaussGlue_of (hC : SpecialFibreDVR) (hBD : ModelCoordinateGlue) :
    ModelGaussGlue := by
  intro p _ hp324 hmod hCM Y Φ π h1 hh h2 E _ _ _ _ _ _ hN
  obtain ⟨𝒴, 𝒜, hM⟩ := hmod
  have hne : Nonempty 𝒴.left := by
    obtain ⟨y⟩ := h1.2.2.1
    obtain ⟨P, -⟩ := Quotient.exists_rep (s := isoSetoid Qbar) (Φ Qbar y)
    obtain ⟨y', -⟩ := hM.2.2.2.2.1 P
    exact ⟨y'.base (IsLocalRing.closedPoint Qbar)⟩
  obtain ⟨ξ, hdom, hdvr, hmax⟩ := hC p 𝒴 hM.1 hM.2.1 hne
  obtain ⟨ι, hinj, hfrac, hcoord⟩ := hBD p hp324 𝒴 𝒜 hM hCM ξ hdom hdvr hmax Y Φ π h1 hh h2 E hN
  exact vertGaussWitness_of_DVR E p ⟨_, _, hdom, hdvr, ι, hinj, hfrac, hmax, hcoord⟩

/-- **`HeckeVertWitness` from the leaf and the two glue pieces** (compiled). -/
theorem heckeVertWitness_of_goodReduction' (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hC : SpecialFibreDVR) (hBD : ModelCoordinateGlue) : HeckeVertWitness :=
  heckeVertWitness_of_goodReduction hL hRR (modelGaussGlue_of hC hBD)

/-- **`HeckeVertWitness` from the leaf, the uniformizer form of the scheme glue, and the coordinate
glue** (compiled). -/
theorem heckeVertWitness_of_goodReduction'' (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hU : SpecialFibreUniformizer) (hBD : ModelCoordinateGlue) : HeckeVertWitness :=
  heckeVertWitness_of_goodReduction' hL hRR (specialFibreDVR_of_uniformizer hU) hBD

/-! ### Splitting `ModelCoordinateGlue`: the coordinate on the model, and the comparison -/

/-- **R2-type clauses for a map `ρ : 𝒴 → P¹` on the `ℚ̄`-points of the model** (the shape of
`R2fpProps`, with `IsFibreOf 𝒜` in place of `Φ`): two `ℚ̄`-points have the same `ρ`-value iff their
QM pairs are `Aut(𝒪)`-twists of each other, and the CM points of discriminants `−4, −3, −24` go to
`0, ∞, −16/27`. -/
def CoordFibres {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) (ρ : ToP1 𝒴.left) : Prop :=
  ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P Q : QML3 Qbar),
    IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' Q →
      (ρ.val y = ρ.val y' ↔ ∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q → ρ.val y = OnePoint.some 0) ∧
      (HasCM3 P.q → ρ.val y = OnePoint.infty) ∧
      (HasCM24 P.q → ρ.val y = OnePoint.some (-16 / 27))

/-- **Glue (d), the coordinate on the model (route GR, not proved).** Given the smooth model at
`p > 324` and a triple with R1fp, R1hecke, R2fp, there is a morphism `ρ : 𝒴 → P¹` over `ℤ_(p)`
with the R2-type clauses on `ℚ̄`-points, regular at every point `ξ` whose stalk is a DVR with
maximal ideal `(p)` (the generic points of the components of the special fibre), with
transcendental reduction there: `f(ρ) ∈ 𝔪_ξ ⟺ f ∈ p ℤ[X]` for `f ∈ ℤ[X]`. The qualifying `ξ` are
exactly the generic points of the components of the special fibre. (Proof outline: `ρ` is the
coordinate of the tame quotient `𝒵 = 𝒴/G' ≅ P¹_{ℤ_(p)}` (the image of `G'` has order `2^a 3^b`, so
tameness holds for every `p ≥ 5`) normalized by the three CM sections, which are pairwise disjoint
mod `p` (finite étale fixed loci, cyclic stabilizers; this uses that the CM orbits have the
nontrivial stabilizers of orders `4, 6, 2`, the indices of `RvNocm.ramification_eq_orbifold_order`);
see docs/research/vert-witness.md §4.3 (d).) -/
def ModelCoordinate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∃ ρ : ToP1 𝒴.left, CoordFibres 𝒴 𝒜 ρ ∧
      ∀ (ξ : 𝒴.left) (_ : IsDomain (𝒴.left.presheaf.stalk ξ)),
        IsDiscreteValuationRing (𝒴.left.presheaf.stalk ξ) →
        IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
          Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)} →
        ∃ hξ : ξ ∈ ρ.U, ∀ f : ℤ[X],
          (f.eval₂ (Int.castRingHom _) (𝒴.left.presheaf.germ ρ.U ξ hξ ρ.f) ∈
              IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) ↔ f ∈ vertPrime p)

/-- **Glue (b), comparison of function fields (route GR, not proved).** Given the smooth model at
`p > 324`, a triple with R1fp, R1hecke, R2fp, a morphism `ρ : 𝒴 → P¹` with the R2-type clauses,
a point `ξ ∈ ρ.U`, and any finite Galois `E/ℚ(X)` with the normalization chart, the stalk at `ξ`
embeds in `E` with fraction field `E`, sending the germ of `ρ` to `X`. (Proof outline:
`R1univProps` classifies `𝒴_ℚ` by `g : 𝒴_ℚ → Y`, bijective on `ℚ̄`-points, hence an isomorphism of
smooth proper curves; `Y` is irreducible, so `𝒴` is integral with function field
`ℚ(Y) = Frac B = E`; `ρ' = ρ ∘ g⁻¹` and `π` have the same fibres on `ℚ̄`-points (`CoordFibres`,
R2fp), so `ρ' = m ∘ π` for a rational map `m` injective on `P¹(ℚ̄)`, i.e. a Möbius map (char 0);
the three CM points exist on `𝒴` (`CMObjectsExist` and the leaf's surjectivity clause), so `m`
fixes `0, ∞, −16/27` and `m = id`; Mathlib's `IsFractionRing (X.presheaf.stalk x) X.functionField`
for integral `X`.) -/
def ModelComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ ρ : ToP1 𝒴.left, CoordFibres 𝒴 𝒜 ρ →
    ∀ (ξ : 𝒴.left) (hξ : ξ ∈ ρ.U),
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∃ ι : 𝒴.left.presheaf.stalk ξ →+* E, Function.Injective ι ∧
        (∀ x : E, ∃ a b : 𝒴.left.presheaf.stalk ξ, b ≠ 0 ∧ x * ι b = ι a) ∧
        ι (𝒴.left.presheaf.germ ρ.U ξ hξ ρ.f) = algebraMap ℚ[X] E X

/-- `ℤ[X] → E` (through `ℚ[X]`) is evaluation at `X`. -/
theorem intPolyAlg_eq_eval₂ (E : Type) [Field E] [Algebra ℚ[X] E] (f : ℤ[X]) :
    letI := intPolyAlg E
    algebraMap ℤ[X] E f = f.eval₂ (Int.castRingHom E) (algebraMap ℚ[X] E X) := by
  letI := intPolyAlg E
  have key : ((algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) =
      Polynomial.eval₂RingHom (Int.castRingHom E) (algebraMap ℚ[X] E X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun φ : ℤ[X] →+* E => φ f) key

/-- **`ModelCoordinateGlue` from the coordinate (d) and the comparison (b)** (compiled). -/
theorem modelCoordinateGlue_of (hD : ModelCoordinate) (hB : ModelComparison) :
    ModelCoordinateGlue := by
  intro p _ hp324 𝒴 𝒜 hM hCM ξ hdom hdvr hmax Y Φ π h1 hh h2 E _ _ _ _ _ _ hN
  letI := intPolyAlg E
  obtain ⟨ρ, hρ, hreg⟩ := hD p hp324 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨hξ, htr⟩ := hreg ξ hdom hdvr hmax
  obtain ⟨ι, hinj, hfrac, hX⟩ := hB p hp324 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 ρ hρ ξ hξ E hN
  refine ⟨ι, hinj, hfrac, fun f => ⟨f.eval₂ (Int.castRingHom _)
    (𝒴.left.presheaf.germ ρ.U ξ hξ ρ.f), ?_, htr f⟩⟩
  rw [Polynomial.hom_eval₂, hX, intPolyAlg_eq_eval₂]
  congr 1
  exact RingHom.ext_int _ _

/-- **`HeckeVertWitness` from the leaf and three glue Props** (compiled):
`SpecialFibreUniformizer` (scheme theory), `ModelCoordinate` (the coordinate on the model, tame
quotient) and `ModelComparison` (function fields). -/
theorem heckeVertWitness_of_goodReduction₃ (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hU : SpecialFibreUniformizer) (hD : ModelCoordinate) (hB : ModelComparison) :
    HeckeVertWitness :=
  heckeVertWitness_of_goodReduction' hL hRR (specialFibreDVR_of_uniformizer hU)
    (modelCoordinateGlue_of hD hB)

/-- **`HeckeVertWitness` from the leaves, `SpecialFibreMaxIdeal`, (d) and (b)** (compiled). -/
theorem heckeVertWitness_of_maxIdeal (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hMI : SpecialFibreMaxIdeal) (hD : ModelCoordinate) (hB : ModelComparison) :
    HeckeVertWitness :=
  heckeVertWitness_of_goodReduction₃ hL hRR (specialFibreUniformizer_of_maxIdeal hMI) hD hB

/-- **`HeckeVertWitness`, finest form** (compiled): from the leaf `ShimuraGoodReduction`, the bundle
leaf `R1R2fp`, the textbook statement `SmoothFibreReduced` (commutative algebra), and the two GR
glue Props `ModelCoordinate` (d) and `ModelComparison` (b). -/
theorem heckeVertWitness_of_leaves (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hSR : SmoothFibreReduced) (hD : ModelCoordinate) (hB : ModelComparison) :
    HeckeVertWitness :=
  heckeVertWitness_of_maxIdeal hL hRR (specialFibreMaxIdeal_of hSR) hD hB

end VertWitness

end

#print axioms HeckeRestNV.heckeNoVertRam_of_local
#print axioms VertWitness.vertLocalWitness_of_gauss
#print axioms VertWitness.cmObjectsExist_of_R1R2fp
#print axioms VertWitness.vertUnramWitness_of_gauss
#print axioms VertWitness.heckeVertWitness_of_gauss
#print axioms VertWitness.heckeVertWitness_of_goodReduction
#print axioms VertWitness.heckeNoVertRam_of_goodReduction
#print axioms VertWitness.vertGaussWitness_of_DVR
#print axioms VertWitness.dvr_of_maximalIdeal_eq_span
#print axioms VertWitness.specialFibreDVR_of_uniformizer
#print axioms VertWitness.modelGaussGlue_of
#print axioms VertWitness.heckeVertWitness_of_goodReduction'
#print axioms VertWitness.heckeVertWitness_of_goodReduction''
#print axioms VertWitness.intPolyAlg_eq_eval₂
#print axioms VertWitness.modelCoordinateGlue_of
#print axioms VertWitness.heckeVertWitness_of_goodReduction₃
#print axioms VertWitness.natCast_mem_nonZeroDivisors_stalk
#print axioms VertWitness.specialFibreUniformizer_of_maxIdeal
#print axioms VertWitness.maximalIdeal_eq_map_of_mem_minimalPrimes
#print axioms VertWitness.specialFibreMaxIdeal_of
#print axioms VertWitness.heckeVertWitness_of_maxIdeal
#print axioms VertWitness.heckeVertWitness_of_leaves

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# model-glue: reductions of `ModelCoordinate` and `ModelComparison`

Everything above this banner is `scratch/vert-witness/VertWitness.lean` verbatim (whole file).
`VertWitness.ModelCoordinate` and `VertWitness.ModelComparison` are used by name from that
prefix, so the theorems below have exactly those types.

* `ModelGlue.mem_maximalIdeal_iff_of_transcendental` (commutative algebra, compiled): in a local
  ring with `p ∈ 𝔪`, if the residue of `r` is transcendental over the prime field of the residue
  field, then `f(r) ∈ 𝔪 ⟺ f ∈ p ℤ[X]` for `f ∈ ℤ[X]` (the Gauss criterion).
* `ModelGlue.ModelCoordinateResidue` (glue, smaller): the coordinate exists, is regular at every
  qualifying `ξ`, and its reduction at `ξ` is transcendental (non-constant reduction).
  `modelCoordinate_of_residue : ModelCoordinateResidue → ModelCoordinate` (compiled).
* `ModelGlue.ModelIntegral` and `ModelGlue.ModelFunctionField` (glue, smaller): the model is
  integral, and at its generic point the germ of every coordinate with `CoordFibres` goes to `X`
  under a surjection `ℚ(𝒴) → E`.
  `modelComparison_of : ModelIntegral → ModelFunctionField → ModelComparison` (compiled).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace ModelGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue

/-! ## Part 1: transcendental reduction gives the Gauss criterion -/

/-- In a local ring with `p ∈ 𝔪`, an integer lies in `𝔪` iff `p` divides it. -/
theorem intCast_mem_maximalIdeal_iff {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ}
    (hp : p.Prime) (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R) (c : ℤ) :
    (c : R) ∈ IsLocalRing.maximalIdeal R ↔ (p : ℤ) ∣ c := by
  constructor
  · intro hc
    by_contra hnd
    obtain ⟨a, b, hab⟩ : IsCoprime c (p : ℤ) :=
      ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hnd).symm
    have hmem : ((a * c + b * p : ℤ) : R) ∈ IsLocalRing.maximalIdeal R := by
      push_cast
      exact add_mem (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_left _ _ hpm)
    rw [hab, Int.cast_one] at hmem
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  · rintro ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpm

/-- **Gauss criterion from transcendental reduction** (commutative algebra, compiled). In a local
ring `R` with `p ∈ 𝔪_R`, if the residue `r̄` of `r` is transcendental over the prime field of the
residue field, then for `f ∈ ℤ[X]`: `f(r) ∈ 𝔪_R ⟺ f ∈ p ℤ[X]`. -/
theorem mem_maximalIdeal_iff_of_transcendental {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ}
    (hp : p.Prime) (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R) (r : R)
    (ht : Transcendental (⊥ : Subfield (IsLocalRing.ResidueField R)) (IsLocalRing.residue R r))
    (f : ℤ[X]) :
    f.eval₂ (Int.castRingHom R) r ∈ IsLocalRing.maximalIdeal R ↔ f ∈ vertPrime p := by
  set k : Subfield (IsLocalRing.ResidueField R) := ⊥
  have hcoe : ∀ c : ℤ, ((c : k) = 0 ↔ (c : R) ∈ IsLocalRing.maximalIdeal R) := by
    intro c
    rw [← IsLocalRing.residue_eq_zero_iff, map_intCast, ← Subtype.coe_inj]
    simp
  have key : IsLocalRing.residue R (f.eval₂ (Int.castRingHom R) r) =
      aeval (IsLocalRing.residue R r) (f.map (Int.castRingHom k)) := by
    rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
    congr 1
  have hmap : f.map (Int.castRingHom k) = 0 ↔ f ∈ vertPrime p := by
    rw [vertPrime, Ideal.mem_map_C_iff, Polynomial.ext_iff]
    refine forall_congr' fun n => ?_
    rw [coeff_map, coeff_zero, Ideal.mem_span_singleton, eq_intCast, hcoe,
      intCast_mem_maximalIdeal_iff hp hpm]
  rw [← IsLocalRing.residue_eq_zero_iff, key, ← hmap]
  constructor
  · intro h0
    by_contra hne
    exact ht ⟨_, hne, h0⟩
  · intro h0
    rw [h0, map_zero]

/-! ## Part 2: the coordinate (d) -/

/-- **Glue (d'), the coordinate on the model with non-constant reduction** (route GR; not proved;
strictly smaller than `ModelCoordinate`: the membership criterion is replaced by its source, the
transcendence of the reduction). Given the smooth model at `p > 324` and a triple with R1fp,
R1hecke, R2fp, there is `ρ : 𝒴 → P¹` over `ℤ_(p)` with `CoordFibres`, regular at every `ξ` whose
stalk is a DVR with maximal ideal `(p)`, whose reduction `ρ̄(ξ) ∈ κ(ξ)` is transcendental over
`𝔽_p` (the prime field of `κ(ξ)`). Proof outline (docs/research/vert-witness.md §4.3 (d)): `ρ` is
the coordinate of the tame quotient `𝒵 = 𝒴/G' ≅ P¹_{ℤ_(p)}` (SGA 1 Exp. V for the quotient and
its base change, `p ∤ |G'|`; three pairwise disjoint CM sections, Edixhoven, Compositio 97 (1995),
fixed loci; locators UNVERIFIED); `q : 𝒴 → 𝒵` is finite surjective, so the generic point `ξ` of a
special-fibre component maps to the generic point of `P¹_{𝔽_p}`, and `ρ̄(ξ)` is the coordinate
`t ∈ 𝔽_p(t) ⊆ κ(ξ)`, transcendental. -/
def ModelCoordinateResidue : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∃ ρ : ToP1 𝒴.left, CoordFibres 𝒴 𝒜 ρ ∧
      ∀ (ξ : 𝒴.left) (_ : IsDomain (𝒴.left.presheaf.stalk ξ)),
        IsDiscreteValuationRing (𝒴.left.presheaf.stalk ξ) →
        IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
          Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)} →
        ∃ hξ : ξ ∈ ρ.U,
          Transcendental (⊥ : Subfield (IsLocalRing.ResidueField (𝒴.left.presheaf.stalk ξ)))
            (IsLocalRing.residue _ (𝒴.left.presheaf.germ ρ.U ξ hξ ρ.f))

/-- **`ModelCoordinate` from `ModelCoordinateResidue`** (compiled; the Gauss criterion). -/
theorem modelCoordinate_of_residue (h : ModelCoordinateResidue) : ModelCoordinate := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨ρ, hρ, hreg⟩ := h p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  refine ⟨ρ, hρ, fun ξ hdom hdvr hmax => ?_⟩
  obtain ⟨hξ, ht⟩ := hreg ξ hdom hdvr hmax
  refine ⟨hξ, mem_maximalIdeal_iff_of_transcendental (Fact.out : p.Prime) ?_ _ ht⟩
  rw [hmax]
  exact Ideal.subset_span rfl

/-! ## Part 3: the comparison (b) -/

/-- **Glue (b1), the model is integral** (route GR; not proved). Given the smooth model at
`p > 324`, a triple with R1fp, R1hecke, R2fp, and a finite Galois `E/ℚ(X)` with the
normalization chart, `𝒴` is an integral scheme. Proof outline (docs/research/vert-witness.md
§4.3 (b)): `R1univProps` gives `g : 𝒴_ℚ → Y`, bijective on `ℚ̄`-points, hence an isomorphism of
smooth proper curves over `ℚ` (finite, degree 1, normal target); `Y` is irreducible (the chart
`Spec B`, `B` a domain since `E` is a field, meets every component: a component with `π ≡ ∞`
would carry infinitely many twist-inequivalent `ℚ̄`-points in one `π`-fibre, against R2fp) and
reduced (smooth); `𝒴` is flat over `ℤ_(p)` (smooth), so its generic fibre is dense and `𝒴` is
reduced (smooth over a regular base), hence integral. -/
def ModelIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      IsIntegral 𝒴.left

/-- **Glue (b2), comparison of function fields at the generic point** (route GR; not proved).
Given the smooth model at `p > 324` (integral), CM objects, a triple with R1fp, R1hecke, R2fp, a
coordinate `ρ : 𝒴 → P¹` with `CoordFibres` (defined at the generic point `η` of `𝒴`), and a
finite Galois `E/ℚ(X)` with the normalization chart, there is a surjection `κ : ℚ(𝒴) → E` with
`κ(ρ) = X`. Proof outline (docs/research/vert-witness.md §4.3 (b)): `ℚ(𝒴) = ℚ(𝒴_ℚ) ≅ ℚ(Y)` via
the isomorphism `g` of (b1), and `ℚ(Y) = Frac B = E` via the chart; `ρ ∘ g⁻¹` and `π` have the same
`ℚ̄`-fibres (`CoordFibres`, R2fp), so `ρ ∘ g⁻¹ = m ∘ π` with `m` injective on `P¹(ℚ̄)`, a Möbius
map (char 0; cf. `Pin.MobiusGlue` and `Contrib/Mobius/`), which fixes `0, ∞, −16/27` (the CM points
exist on `𝒴` by `CMObjectsExist` and the leaf's surjectivity), so `m = id` and `κ(ρ) = π = X`. -/
def ModelFunctionField : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (_ : IsIntegral 𝒴.left),
    ∀ ρ : ToP1 𝒴.left, CoordFibres 𝒴 𝒜 ρ →
    ∀ (hη : genericPoint 𝒴.left ∈ ρ.U),
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∃ κ : 𝒴.left.functionField →+* E, Function.Surjective κ ∧
        κ (𝒴.left.presheaf.germ ρ.U (genericPoint 𝒴.left) hη ρ.f) = algebraMap ℚ[X] E X

/-- **From the generic point to every stalk** (compiled): for an integral scheme `X`, a point
`ξ ∈ U`, and a surjection `κ : ℚ(X) → E` onto a field, `κ ∘ (𝒪_{X,ξ} → ℚ(X))` is injective, `E` is
its fraction field, and it sends the germ of `s ∈ Γ(U)` at `ξ` to `κ` of its germ at `η`. -/
theorem stalk_embedding_of_functionField {X : Scheme.{0}} [IsIntegral X] {E : Type} [Field E]
    (κ : X.functionField →+* E) (hκ : Function.Surjective κ) {U : X.Opens} {ξ : X} (hξ : ξ ∈ U)
    (hη : genericPoint X ∈ U) (s : Γ(X, U)) :
    ∃ ι : X.presheaf.stalk ξ →+* E, Function.Injective ι ∧
      (∀ x : E, ∃ a b : X.presheaf.stalk ξ, b ≠ 0 ∧ x * ι b = ι a) ∧
      ι (X.presheaf.germ U ξ hξ s) = κ (X.presheaf.germ U (genericPoint X) hη s) := by
  haveI : Nonempty U := ⟨⟨ξ, hξ⟩⟩
  refine ⟨κ.comp (algebraMap (X.presheaf.stalk ξ) X.functionField), ?_, ?_, ?_⟩
  · exact κ.injective.comp (IsFractionRing.injective _ _)
  · intro x
    obtain ⟨y, rfl⟩ := hκ x
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk ξ)) y
    refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
    simp only [RingHom.comp_apply]
    rw [← map_mul, ← hab]
  · simp only [RingHom.comp_apply]
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]

/-- **`ModelComparison` from (b1) and (b2)** (compiled). -/
theorem modelComparison_of (hI : ModelIntegral) (hF : ModelFunctionField) : ModelComparison := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 ρ hρ ξ hξ E _ _ _ _ _ _ hN
  haveI := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 E hN
  have hη : genericPoint 𝒴.left ∈ ρ.U :=
    ((genericPoint_spec 𝒴.left).mem_open_set_iff ρ.U.isOpen).mpr ⟨ξ, trivial, hξ⟩
  obtain ⟨κ, hκs, hκX⟩ := hF p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 inferInstance ρ hρ hη E hN
  obtain ⟨ι, hinj, hfrac, hX⟩ := stalk_embedding_of_functionField κ hκs hξ hη ρ.f
  exact ⟨ι, hinj, hfrac, hX.trans hκX⟩

/-! ## Part 4: the composite -/

/-- **`ModelCoordinateGlue` from the three smaller glue Props** (compiled). -/
theorem modelCoordinateGlue_of_parts (hD : ModelCoordinateResidue) (hI : ModelIntegral)
    (hF : ModelFunctionField) : ModelCoordinateGlue :=
  modelCoordinateGlue_of (modelCoordinate_of_residue hD) (modelComparison_of hI hF)

/-- **`HeckeVertWitness` from the leaves and the finer glue** (compiled). -/
theorem heckeVertWitness_of_parts (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hSR : SmoothFibreReduced) (hD : ModelCoordinateResidue) (hI : ModelIntegral)
    (hF : ModelFunctionField) : HeckeVertWitness :=
  heckeVertWitness_of_leaves hL hRR hSR (modelCoordinate_of_residue hD)
    (modelComparison_of hI hF)

end ModelGlue

end

#print axioms ModelGlue.intCast_mem_maximalIdeal_iff
#print axioms ModelGlue.mem_maximalIdeal_iff_of_transcendental
#print axioms ModelGlue.modelCoordinate_of_residue
#print axioms ModelGlue.stalk_embedding_of_functionField
#print axioms ModelGlue.modelComparison_of
#print axioms ModelGlue.modelCoordinateGlue_of_parts
#print axioms ModelGlue.heckeVertWitness_of_parts

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# model-glue, step 2: Möbius rigidity for `CoordFibres` (needs `ZInQKernel.Contrib.Mobius.Main`)

`ModelGlue2.lean` = `import ZInQKernel.Contrib.Mobius.Main` + `VertWitness.lean` (verbatim) +
`ModelGlue.lean.part` + this part. `ModelFunctionField` is reduced to
`ModelFunctionFieldExists` (one coordinate with the function-field property), the textbook glue
`ModelGenericFibre` (base change to `ℚ`) and `GermOfQbarValues` (Jacobson density), using the
proved curve facts `LeafQM.AV.Pin.curveFacts` and `TwistClassFinite` (from the leaf T5).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace ModelGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue

/-- **Textbook glue: the generic fibre** (base change; STANDARD: properness and smoothness of
relative dimension `1` are stable under base change, and `ℚ̄`-points of `𝒴 ×_{ℤ_(p)} ℚ` are the
`ℚ̄`-points of `𝒴`, since `Hom(ℤ_(p), ℚ̄)` is a singleton; EGA II 5.4.2, EGA IV 17.3.3, locators
UNVERIFIED; not proved here). For a proper smooth curve `𝒴` over `ℤ_(p)` there is a proper smooth
curve `S` over `ℚ` with `j : S → 𝒴` inducing a bijection on `ℚ̄`-points. -/
def ModelGenericFibre : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∃ (S : Over (Spec (CommRingCat.of ℚ))) (j : S.left ⟶ 𝒴.left),
      IsProper S.hom ∧ SmoothOfRelativeDimension 1 S.hom ∧
      (∀ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, ∃ s : fieldPt Qbar ⟶ S, s.left ≫ j = y) ∧
      ∀ s s' : fieldPt Qbar ⟶ S, s.left ≫ j = s'.left ≫ j → s = s'

/-- **Möbius rigidity of `CoordFibres` on `ℚ̄`-points** (compiled, from the proved curve facts
`curveFacts`, `TwistClassFinite`, `ModelGenericFibre` and the leaf's clauses): two maps
`ρ, ρ' : 𝒴 → P¹` with `CoordFibres` take the same value at every `ℚ̄`-point. (The argument of
`Pin.mobiusGlue_of_curveFacts`, on the generic fibre: `ρ' = R ∘ ρ` with `R` injective on `ℚ̄`,
so Möbius, fixing `0, ∞, −16/27`.) -/
theorem coordFibres_val_eq (hT : TwistClassFinite) (hG : ModelGenericFibre) {p : ℕ}
    [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left}
    (hM : IsShimuraModel p 𝒴 𝒜) (hCM : CMObjectsExist) {ρ ρ' : ToP1 𝒴.left}
    (hρ : CoordFibres 𝒴 𝒜 ρ) (hρ' : CoordFibres 𝒴 𝒜 ρ')
    (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) : ρ.val y = ρ'.val y := by
  obtain ⟨S, j, hprop, hsm, hpts, hinjpt⟩ := hG p 𝒴 hM.1 hM.2.1
  obtain ⟨-, -, hfib, hinjM, hsurjM, -, -, -⟩ := hM
  set σ : ToP1 S.left := ρ.comp j
  set σ' : ToP1 S.left := ρ'.comp j
  have hσ : ∀ s : fieldPt Qbar ⟶ S, σ.val (K := Qbar) s.left = ρ.val (s.left ≫ j) :=
    fun s => ToP1.val_comp_right ρ j s.left
  have hσ' : ∀ s : fieldPt Qbar ⟶ S, σ'.val (K := Qbar) s.left = ρ'.val (s.left ≫ j) :=
    fun s => ToP1.val_comp_right ρ' j s.left
  have hP : ∀ s : fieldPt Qbar ⟶ S, ∃ P : QML3 Qbar, IsFibreOf 𝒜 (s.left ≫ j) P :=
    fun s => hfib Qbar (s.left ≫ j)
  choose Pof hPof using hP
  -- the two maps have the same fibres
  have hrel : ∀ s₁ s₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) s₁.left = σ.val (K := Qbar) s₂.left
      ↔ σ'.val (K := Qbar) s₁.left = σ'.val (K := Qbar) s₂.left := by
    intro s₁ s₂
    rw [hσ, hσ, hσ', hσ', (hρ _ _ _ _ (hPof s₁) (hPof s₂)).1, (hρ' _ _ _ _ (hPof s₁) (hPof s₂)).1]
  -- CM points on `S`
  have hcm : ∀ P : QML3 Qbar, ∃ s : fieldPt Qbar ⟶ S, IsFibreOf 𝒜 (s.left ≫ j) P := by
    intro P
    obtain ⟨y, hy⟩ := hsurjM P
    obtain ⟨s, hs⟩ := hpts y
    exact ⟨s, hs ▸ hy⟩
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  obtain ⟨y₄, f₄⟩ := hcm P₄
  obtain ⟨y₃, f₃⟩ := hcm P₃
  obtain ⟨y₂, f₂⟩ := hcm P₂
  have σ₄ : σ.val (K := Qbar) y₄.left = OnePoint.some 0 := by
    rw [hσ]; exact (hρ _ _ _ _ f₄ f₄).2.1 c₄
  have π₄ : σ'.val (K := Qbar) y₄.left = OnePoint.some 0 := by
    rw [hσ']; exact (hρ' _ _ _ _ f₄ f₄).2.1 c₄
  have σ₃ : σ.val (K := Qbar) y₃.left = OnePoint.infty := by
    rw [hσ]; exact (hρ _ _ _ _ f₃ f₃).2.2.1 c₃
  have π₃ : σ'.val (K := Qbar) y₃.left = OnePoint.infty := by
    rw [hσ']; exact (hρ' _ _ _ _ f₃ f₃).2.2.1 c₃
  have σ₂ : σ.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) := by
    rw [hσ]; exact (hρ _ _ _ _ f₂ f₂).2.2.2 c₂
  have π₂ : σ'.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) := by
    rw [hσ']; exact (hρ' _ _ _ _ f₂ f₂).2.2.2 c₂
  -- finite fibres
  have hmkinj : Function.Injective (fun s : fieldPt Qbar ⟶ S => M3.mk (Pof s)) := by
    intro s s' h
    exact hinjpt s s' (hinjM _ _ _ _ (hPof s) (hPof s') h)
  have hfin : ∀ s : fieldPt Qbar ⟶ S, {s' : fieldPt Qbar ⟶ S |
      σ.val (K := Qbar) s'.left = σ.val (K := Qbar) s.left}.Finite := by
    intro s
    refine ((hT (Pof s)).preimage (Set.injOn_of_injective hmkinj)).subset ?_
    intro s' hs'
    have e : σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left := hs'.symm
    rw [hσ, hσ] at e
    exact ⟨Pof s', rfl, ((hρ _ _ _ _ (hPof s) (hPof s')).1).1 e⟩
  obtain ⟨y₀, -⟩ := hcm P₄
  have hsurj := curveFacts.2 S hprop hsm ⟨y₀⟩ σ hfin
  obtain ⟨F, G, hcop, hFG⟩ := curveFacts.1 S hprop hsm σ σ' (fun s₁ s₂ h => (hrel s₁ s₂).1 h)
  have hinj : ∀ s t : Qbar, Mob.ratEval F G s = Mob.ratEval F G t → s = t := by
    intro s t hst
    obtain ⟨ys, hys⟩ := hsurj (OnePoint.some s)
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : σ'.val (K := Qbar) ys.left = σ'.val (K := Qbar) yt.left := by
      rw [hFG ys s hys, hFG yt t hyt, hst]
    have := (hrel ys yt).2 e
    rw [hys, hyt] at this
    exact OnePoint.coe_injective this
  have hdeg := Mob.natDegree_le_one_of_injective hcop hinj
  have hpole : ∀ t, Mob.ratEval F G t ≠ OnePoint.infty := by
    intro t ht
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : σ'.val (K := Qbar) yt.left = σ'.val (K := Qbar) y₃.left := by
      rw [hFG yt t hyt, ht, π₃]
    have := (hrel yt y₃).2 e
    rw [hyt, σ₃] at this
    exact OnePoint.coe_ne_infty t this
  have h0 : Mob.ratEval F G 0 = OnePoint.some 0 := by rw [← hFG y₄ 0 σ₄, π₄]
  have hc : Mob.ratEval F G (-16 / 27) = OnePoint.some (-16 / 27) := by
    rw [← hFG y₂ _ σ₂, π₂]
  have hid := Mob.ratEval_eq_self hdeg.1 hpole h0 (by norm_num) hc
  -- conclusion on `S`, then on `𝒴`
  have hS : ∀ s : fieldPt Qbar ⟶ S, σ'.val (K := Qbar) s.left = σ.val (K := Qbar) s.left := by
    intro s
    by_cases hinf : σ.val (K := Qbar) s.left = OnePoint.infty
    · rw [hinf, ← π₃]
      exact (hrel s y₃).1 (by rw [hinf, σ₃])
    · obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hinf
      rw [← ht, hFG s t ht.symm, hid t]
  obtain ⟨s, rfl⟩ := hpts y
  have e := hS s
  rw [hσ, hσ'] at e
  exact e.symm

/-- **Glue (Jacobson density on the model; not proved).** On an integral proper smooth curve `𝒴`
over `ℤ_(p)`, two maps to `P¹` with the same value at every `ℚ̄`-point have the same germ at the
generic point. (The generic fibre `𝒴_ℚ = 𝒴[1/p]` is a nonempty open of finite type over `ℚ`,
hence Jacobson, so the closed points (all `ℚ̄`-points up to `Gal(ℚ̄/ℚ)`) are dense in
`ρ.U ∩ ρ'.U ∩ 𝒴_ℚ`; there `ρ.f − ρ'.f` vanishes at every closed point, so it is zero on the
reduced scheme `𝒴`; Stacks 01P4, 00GA, locators UNVERIFIED.) -/
def GermOfQbarValues : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom → ∀ (_ : IsIntegral 𝒴.left)
    (ρ ρ' : ToP1 𝒴.left), (∀ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, ρ.val y = ρ'.val y) →
    ∀ (hη : genericPoint 𝒴.left ∈ ρ.U) (hη' : genericPoint 𝒴.left ∈ ρ'.U),
      𝒴.left.presheaf.germ ρ.U (genericPoint 𝒴.left) hη ρ.f =
        𝒴.left.presheaf.germ ρ'.U (genericPoint 𝒴.left) hη' ρ'.f

/-- **Glue (b2'), one coordinate with the function-field property** (route GR; not proved;
strictly weaker than `ModelFunctionField`: one `ρ₀` instead of every `ρ`). Given the smooth model
(integral), CM objects, a triple with R1fp, R1hecke, R2fp and `E` with the chart, some `ρ₀` with
`CoordFibres`, defined at `η`, has `κ(ρ₀) = X` for a surjection `κ : ℚ(𝒴) → E`. (`ρ₀` is the
coordinate of `ModelCoordinateResidue`; `κ` is `ℚ(𝒴) = ℚ(𝒴_ℚ) ≅ ℚ(Y) = Frac B = E` through the
isomorphism `𝒴_ℚ ≅ Y` given by `R1univProps`, and `κ(ρ₀) = π ∘ g` is `X` by the rigidity above
applied on `Y`; docs/research/vert-witness.md §4.3 (b).) -/
def ModelFunctionFieldExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (_ : IsIntegral 𝒴.left),
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∃ ρ₀ : ToP1 𝒴.left, CoordFibres 𝒴 𝒜 ρ₀ ∧ ∃ hη : genericPoint 𝒴.left ∈ ρ₀.U,
        ∃ κ : 𝒴.left.functionField →+* E, Function.Surjective κ ∧
          κ (𝒴.left.presheaf.germ ρ₀.U (genericPoint 𝒴.left) hη ρ₀.f) = algebraMap ℚ[X] E X

/-- **`ModelFunctionField` from the finer glue** (compiled; Möbius rigidity `coordFibres_val_eq`). -/
theorem modelFunctionField_of (hT : TwistClassFinite) (hG : ModelGenericFibre)
    (hJ : GermOfQbarValues) (hE : ModelFunctionFieldExists) : ModelFunctionField := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 hI ρ hρ hη E _ _ _ _ _ _ hN
  obtain ⟨ρ₀, hρ₀, hη₀, κ, hκs, hκX⟩ := hE p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 hI E hN
  refine ⟨κ, hκs, ?_⟩
  rw [hJ p 𝒴 hM.1 hM.2.1 hI ρ ρ₀ (coordFibres_val_eq hT hG hM hCM hρ hρ₀) hη hη₀]
  exact hκX

/-- **`ModelComparison` from the finer glue and the leaf T5** (compiled). -/
theorem modelComparison_of_parts (hT : ObjBridge.TorsionStructure) (hI : ModelIntegral)
    (hG : ModelGenericFibre) (hJ : GermOfQbarValues) (hE : ModelFunctionFieldExists) :
    ModelComparison :=
  modelComparison_of hI (modelFunctionField_of (twistClassFinite hT) hG hJ hE)

/-- **`HeckeVertWitness` from the leaves and the finest glue** (compiled). -/
theorem heckeVertWitness_of_parts₂ (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hSR : SmoothFibreReduced) (hT : ObjBridge.TorsionStructure) (hD : ModelCoordinateResidue)
    (hI : ModelIntegral) (hG : ModelGenericFibre) (hJ : GermOfQbarValues)
    (hE : ModelFunctionFieldExists) : HeckeVertWitness :=
  heckeVertWitness_of_parts hL hRR hSR hD hI (modelFunctionField_of (twistClassFinite hT) hG hJ hE)

end ModelGlue

end

#print axioms ModelGlue.coordFibres_val_eq
#print axioms ModelGlue.modelFunctionField_of
#print axioms ModelGlue.modelComparison_of_parts
#print axioms ModelGlue.heckeVertWitness_of_parts₂

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# model-glue, step 3: the generic fibre and Jacobson density (proved)

`ModelGlue3.lean` = `ModelGlue2.lean` + this part.
* `ModelGlue.modelGenericFibre : ModelGenericFibre` (base change `𝒴 ×_{ℤ_(p)} Spec ℚ`).
* `ModelGlue.germOfQbarValues : GermOfQbarValues` (Jacobson density on the generic fibre).
The lemmas `exists_qbarPt`, `eval_res` and the forward half of `val_eq_iff_agree` are copied
from task period-glue (`scratch/period-glue/PiTwist.lean`, branch wip/period-glue).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace ModelGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue

/-! ## Part 6: `ℤ_(p)` and its generic point -/

/-- Ring maps out of `ℤ_(p)` are unique. -/
theorem zloc_ringHom_ext {p : ℕ} [Fact p.Prime] {T : Type*} [CommRing T]
    (f g : Zloc p →+* T) : f = g :=
  IsLocalization.ringHom_ext (pIdeal p).primeCompl (RingHom.ext_int _ _)

/-- The inclusion `ℤ_(p) → ℚ`. -/
def zlocToRat (p : ℕ) [Fact p.Prime] : Zloc p →+* ℚ :=
  IsLocalization.lift (M := (pIdeal p).primeCompl) (S := Zloc p) (g := Int.castRingHom ℚ)
    (by
      rintro ⟨s, hs⟩
      refine isUnit_iff_ne_zero.2 ?_
      simp only [eq_intCast, ne_eq, Int.cast_eq_zero]
      rintro rfl
      exact hs (Ideal.zero_mem _))

/-- `Spec ℚ → Spec ℤ_(p)`. -/
abbrev specRatToZloc (p : ℕ) [Fact p.Prime] :
    Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (Zloc p)) :=
  Spec.map (CommRingCat.ofHom (zlocToRat p))

/-- Morphisms `Spec T → Spec ℤ_(p)` are unique. -/
theorem spec_to_zloc_eq {p : ℕ} [Fact p.Prime] {T : CommRingCat.{0}}
    (a b : Spec T ⟶ Spec (CommRingCat.of (Zloc p))) : a = b := by
  apply Spec.homEquiv.injective
  ext1
  exact zloc_ringHom_ext _ _

/-- A prime of `ℤ_(p)` not containing `p` is `0` (`ℤ_(p)` is a DVR with uniformizer `p`). -/
theorem zloc_prime_eq_bot {p : ℕ} [Fact p.Prime] (q : Ideal (Zloc p)) [hq : q.IsPrime]
    (hpq : (p : Zloc p) ∉ q) : q = ⊥ := by
  haveI : IsDiscreteValuationRing (Zloc p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
      (by
        show Ideal.span {((p : ℕ) : ℤ)} ≠ ⊥
        rw [ne_eq, Ideal.span_singleton_eq_bot]
        exact_mod_cast (Fact.out : p.Prime).ne_zero) _
  have hp0 : (p : Zloc p) ≠ 0 := by
    intro h
    apply hpq
    rw [h]
    exact q.zero_mem
  have hirr := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hp0
    (maximalIdeal_Zloc p)
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  by_contra hx0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
  have hpn : (p : Zloc p) ^ n ∈ q := by
    have := q.mul_mem_left (↑u⁻¹ : Zloc p) hx
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  cases n with
  | zero => exact hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hpn))
  | succ n => exact hpq (hq.mem_of_pow_mem _ hpn)

/-! ## Part 7: the generic fibre (`ModelGenericFibre`, proved) -/

/-- The generic fibre `𝒴 ×_{ℤ_(p)} Spec ℚ` as a `ℚ`-scheme. -/
def genFib {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) :
    Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (pullback.snd 𝒴.hom (specRatToZloc p))

/-- Every `ℚ̄`-point of `𝒴` lifts to the generic fibre. -/
theorem genFib_pt {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) :
    ∃ s : fieldPt Qbar ⟶ genFib 𝒴, s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) = y :=
  ⟨Over.homMk (pullback.lift y (fieldPt Qbar).hom (spec_to_zloc_eq _ _))
      (pullback.lift_snd _ _ _),
    pullback.lift_fst _ _ _⟩

/-- `ℚ̄`-points of the generic fibre are determined by their image in `𝒴`. -/
theorem genFib_pt_inj {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (s s' : fieldPt Qbar ⟶ genFib 𝒴)
    (h : s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
      s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) : s = s' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w s).trans (Over.w s').symm

/-- **`ModelGenericFibre` (proved).** -/
theorem modelGenericFibre : ModelGenericFibre := by
  intro p _ 𝒴 hP hS
  haveI := hP
  haveI := hS
  refine ⟨genFib 𝒴, pullback.fst _ _, ?_, ?_, genFib_pt 𝒴, genFib_pt_inj 𝒴⟩
  · show IsProper (pullback.snd 𝒴.hom (specRatToZloc p))
    infer_instance
  · show SmoothOfRelativeDimension 1 (pullback.snd 𝒴.hom (specRatToZloc p))
    infer_instance

/-! ## Part 8: Jacobson density (`GermOfQbarValues`, proved) -/

/-- A closed point of a `ℚ`-scheme locally of finite type is the point of a `ℚ̄`-point
(copied from period-glue). -/
theorem exists_qbarPt (Y : Over (Spec (CommRingCat.of ℚ))) [LocallyOfFiniteType Y.hom]
    (x : Y.left) (hx : IsClosed ({x} : Set Y.left)) :
    ∃ emb : Y.left.residueField x ⟶ CommRingCat.of Qbar, ∃ y0 : fieldPt Qbar ⟶ Y,
      y0.left = (Scheme.SpecToEquivOfField Qbar Y.left).symm ⟨x, emb⟩ := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  haveI : LocallyOfFiniteType (Y.left.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (Y.left.fromSpecResidueField x ≫ Y.hom)
  have hφ' : Spec.map φ = Y.left.fromSpecResidueField x ≫ Y.hom := hφ
  have hft : RingHom.FiniteType φ.hom := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ']; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℚ (Y.left.residueField x) := hft
  haveI : Module.Finite ℚ (Y.left.residueField x) := finite_of_finite_type_of_isJacobsonRing ℚ _
  haveI : Algebra.IsAlgebraic ℚ (Y.left.residueField x) := Algebra.IsAlgebraic.of_finite ℚ _
  let emb : Y.left.residueField x →ₐ[ℚ] Qbar := IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom emb.toRingHom,
    Over.homMk ((Scheme.SpecToEquivOfField Qbar Y.left).symm
      ⟨x, CommRingCat.ofHom emb.toRingHom⟩) ?_, rfl⟩
  show _ ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
  apply Spec.homEquiv.injective
  ext1
  exact Subsingleton.elim _ _

/-- Evaluation commutes with restriction (copied from period-glue). -/
theorem eval_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (f : Γ(X, U)) :
    X.evaluation V x hx (X.presheaf.map (homOfLE h).op f) = X.evaluation U x (h hx) f := by
  rw [← Scheme.germ_residue, ← Scheme.germ_residue, CommRingCat.comp_apply,
    CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- Equal values at a field point: same chart, same evaluation (forward half of period-glue's
`val_eq_iff_agree`). -/
theorem agree_of_val_eq {X : Scheme.{0}} (σ ρ : ToP1 X) {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ X) (h : σ.val a = ρ.val a)
    (h1 : (Scheme.SpecToEquivOfField K X a).1 ∈ σ.U)
    (h2 : (Scheme.SpecToEquivOfField K X a).1 ∈ ρ.U) :
    X.evaluation σ.U _ h1 σ.f = X.evaluation ρ.U _ h2 ρ.f := by
  unfold ToP1.val at h
  rw [dif_pos h1, dif_pos h2] at h
  exact (Scheme.SpecToEquivOfField K X a).2.hom.injective (OnePoint.coe_injective h)

/-- On an integral flat `ℤ_(p)`-scheme, the generic point lies over the generic point of
`Spec ℤ_(p)`, hence in the image of the generic fibre. -/
theorem genericPoint_mem_range {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    [Flat 𝒴.hom] [IsIntegral 𝒴.left] :
    genericPoint 𝒴.left ∈ Set.range (pullback.fst 𝒴.hom (specRatToZloc p)) := by
  rw [Scheme.Pullback.range_fst]
  have hpη : (p : 𝒴.left.presheaf.stalk (genericPoint 𝒴.left)) ≠ 0 := by
    intro h
    have := natCast_mem_nonZeroDivisors_stalk p 𝒴 (genericPoint 𝒴.left)
    rw [h] at this
    exact zero_notMem_nonZeroDivisors this
  have hηB : genericPoint 𝒴.left ∈ 𝒴.left.basicOpen (p : Γ(𝒴.left, ⊤)) := by
    rw [Scheme.mem_basicOpen_top, map_natCast]
    exact isUnit_iff_ne_zero.2 hpη
  have hpre : 𝒴.left.basicOpen (p : Γ(𝒴.left, ⊤)) =
      𝒴.hom ⁻¹ᵁ (Spec (CommRingCat.of (Zloc p))).basicOpen
        (p : Γ(Spec (CommRingCat.of (Zloc p)), ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, map_natCast]
  rw [hpre] at hηB
  have hηB' : 𝒴.hom (genericPoint 𝒴.left) ∈
      PrimeSpectrum.basicOpen (p : Zloc p) := by
    have := hηB
    rw [Scheme.Hom.mem_preimage, basicOpen_eq_of_affine', map_natCast] at this
    exact this
  set q : PrimeSpectrum (Zloc p) := 𝒴.hom (genericPoint 𝒴.left) with hqdef
  have hq := zloc_prime_eq_bot q.asIdeal (PrimeSpectrum.mem_basicOpen _ _ |>.1 hηB')
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [hq]
  show Ideal.comap (zlocToRat p) ⊥ = ⊥
  apply zloc_prime_eq_bot
  rw [Ideal.mem_comap, map_natCast, Ideal.mem_bot]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- **`GermOfQbarValues` (proved).** If the germs at `η` differed, their difference would be
nonzero on a nonempty open of the generic fibre `S`, which is Jacobson (locally of finite type
over `ℚ`); a closed point there is the point of a `ℚ̄`-point, where the values agree. -/
theorem germOfQbarValues : GermOfQbarValues := by
  intro p _ 𝒴 hP hS hI ρ ρ' hQ hη hη'
  haveI := hP
  haveI := hS
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : LocallyOfFiniteType (genFib 𝒴).hom := by
    show LocallyOfFiniteType (pullback.snd 𝒴.hom (specRatToZloc p))
    infer_instance
  haveI : JacobsonSpace (genFib 𝒴).left := LocallyOfFiniteType.jacobsonSpace (genFib 𝒴).hom
  set j : (genFib 𝒴).left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  set W := ρ.U ⊓ ρ'.U with hW
  have hηW : genericPoint 𝒴.left ∈ W := ⟨hη, hη'⟩
  let d : Γ(𝒴.left, W) := 𝒴.left.presheaf.map (homOfLE inf_le_left).op ρ.f -
    𝒴.left.presheaf.map (homOfLE inf_le_right).op ρ'.f
  have key : 𝒴.left.presheaf.germ W (genericPoint 𝒴.left) hηW d = 0 := by
    by_contra hne
    have hB : genericPoint 𝒴.left ∈ 𝒴.left.basicOpen d :=
      (Scheme.mem_basicOpen _ _ _ hηW).2 (isUnit_iff_ne_zero.2 hne)
    obtain ⟨s, hs⟩ : ∃ s : (genFib 𝒴).left, j s = genericPoint 𝒴.left :=
      genericPoint_mem_range 𝒴
    have hne' : ((j ⁻¹ᵁ 𝒴.left.basicOpen d : (genFib 𝒴).left.Opens) :
        Set (genFib 𝒴).left).Nonempty := ⟨s, by
      show j s ∈ 𝒴.left.basicOpen d
      rw [hs]
      exact hB⟩
    obtain ⟨x, hxB, hxc⟩ := nonempty_inter_closedPoints hne'
      (j ⁻¹ᵁ 𝒴.left.basicOpen d).isOpen.isLocallyClosed
    obtain ⟨emb, y0, hy0⟩ := exists_qbarPt (genFib 𝒴) x hxc
    let z : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒴).left := y0.left
    have hz : z = (Scheme.SpecToEquivOfField Qbar (genFib 𝒴).left).symm ⟨x, emb⟩ := hy0
    have hpt : (Scheme.SpecToEquivOfField Qbar 𝒴.left (z ≫ j)).1 = j x := by
      rw [specToEquivOfField_comp_right, hz, Equiv.apply_symm_apply]
    have hxB' : j x ∈ 𝒴.left.basicOpen d := hxB
    have hxW : j x ∈ W := 𝒴.left.basicOpen_le d hxB'
    have h1 : (Scheme.SpecToEquivOfField Qbar 𝒴.left (z ≫ j)).1 ∈ ρ.U := hpt ▸ hxW.1
    have h2 : (Scheme.SpecToEquivOfField Qbar 𝒴.left (z ≫ j)).1 ∈ ρ'.U := hpt ▸ hxW.2
    have e := agree_of_val_eq ρ ρ' (z ≫ j) (hQ (z ≫ j)) h1 h2
    have h0 := (𝒴.left.evaluation_ne_zero_iff_mem_basicOpen _ hxW d).mpr hxB'
    apply h0
    simp only [d, map_sub, eval_res]
    revert h1 h2 e
    rw [hpt]
    intro h1 h2 e
    rw [e, sub_self]
  simp only [d, map_sub, TopCat.Presheaf.germ_res_apply, sub_eq_zero] at key
  exact key

/-! ## Part 9: composites -/

/-- **`ModelComparison` from `ModelIntegral`, `ModelFunctionFieldExists` and the leaf T5**
(compiled; the generic fibre and Jacobson density are proved above). -/
theorem modelComparison_of_parts₃ (hT : ObjBridge.TorsionStructure) (hI : ModelIntegral)
    (hE : ModelFunctionFieldExists) : ModelComparison :=
  modelComparison_of_parts hT hI modelGenericFibre germOfQbarValues hE

/-- **`HeckeVertWitness` from the leaves and the remaining glue** (compiled). -/
theorem heckeVertWitness_of_parts₃ (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hSR : SmoothFibreReduced) (hT : ObjBridge.TorsionStructure) (hD : ModelCoordinateResidue)
    (hI : ModelIntegral) (hE : ModelFunctionFieldExists) : HeckeVertWitness :=
  heckeVertWitness_of_parts₂ hL hRR hSR hT hD hI modelGenericFibre germOfQbarValues hE

end ModelGlue

end

#print axioms ModelGlue.zloc_prime_eq_bot
#print axioms ModelGlue.modelGenericFibre
#print axioms ModelGlue.exists_qbarPt
#print axioms ModelGlue.genericPoint_mem_range
#print axioms ModelGlue.germOfQbarValues
#print axioms ModelGlue.modelComparison_of_parts₃
#print axioms ModelGlue.heckeVertWitness_of_parts₃

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# model-glue, step 4: the comparison morphism `𝒴_ℚ → Y` and `ModelIntegral`

`ModelGlue4.lean` = `ModelGlue3.lean` + this part.
* `famBC`, `isFibreOf_baseChange`: pulling a QM family back along `T → S`.
* `exists_genFib_to_Y` (proved, from `R1univProps`): a morphism `g : 𝒴_ℚ → Y` over `ℚ`,
  compatible with the moduli maps and bijective on `ℚ̄`-points.
* `CurveBijIso` (textbook leaf, not proved): a morphism of proper smooth curves over `ℚ` that is
  bijective on `ℚ̄`-points is an isomorphism.
* `irreducible_of_chart` (proved, from T5 via `TwistClassFinite` and the proved
  `smoothStalkDimOne`): `Y` is irreducible.
* `isReduced_of_smooth_zloc` (proved): a smooth `ℤ_(p)`-scheme is reduced.
* `irreducibleSpace_of_genFib` (proved): `𝒴` is irreducible if its generic fibre is.
* `modelIntegral_of (hT : TwistClassFinite) (hC : CurveBijIso) : ModelIntegral` (proved).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace ModelGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue

/-! ## Part 10: base change of a QM family and the comparison morphism -/

/-- The pullback of a QM family along `j : T → S`. -/
def famBC {S T : Scheme.{0}} (𝒜 : QMFamily S) (j : T ⟶ S) : QMFamily T where
  F := Over.mk (pullback.snd 𝒜.F.hom j)
  proper := by
    have := 𝒜.proper
    show IsProper (pullback.snd 𝒜.F.hom j)
    infer_instance
  smooth := by
    have := 𝒜.smooth
    show SmoothOfRelativeDimension 2 (pullback.snd 𝒜.F.hom j)
    infer_instance
  iota a := pullback.lift (pullback.fst _ _ ≫ 𝒜.iota a) (pullback.snd _ _)
    (by rw [Category.assoc, 𝒜.iota_over, pullback.condition])
  iota_over a := pullback.lift_snd _ _ _
  eta a := pullback.lift (j ≫ 𝒜.eta a) (𝟙 T)
    (by rw [Category.assoc, 𝒜.eta_sec, Category.comp_id, Category.id_comp])
  eta_sec a := pullback.lift_snd _ _ _

/-- The fibre of `𝒜` at `y ≫ j` is a fibre of the pulled-back family at `y`. -/
theorem isFibreOf_baseChange {S T : Scheme.{0}} (𝒜 : QMFamily S) (j : T ⟶ S) {K : Type}
    [Field K] (y : Spec (CommRingCat.of K) ⟶ T) (P : QML3 K) (h : IsFibreOf 𝒜 (y ≫ j) P) :
    IsFibreOf (famBC 𝒜 j) y P := by
  obtain ⟨g₀, hpb, hι, hη⟩ := h
  have w : g₀ ≫ 𝒜.F.hom = (P.A.X.hom ≫ y) ≫ j := by rw [hpb.w, Category.assoc]
  refine ⟨pullback.lift g₀ (P.A.X.hom ≫ y) w, ?_, ?_, ?_⟩
  · have hR : IsPullback (pullback.fst 𝒜.F.hom j) (pullback.snd 𝒜.F.hom j) 𝒜.F.hom j :=
      IsPullback.of_hasPullback _ _
    have hs : IsPullback (pullback.lift g₀ (P.A.X.hom ≫ y) w ≫ pullback.fst 𝒜.F.hom j)
        P.A.X.hom 𝒜.F.hom (y ≫ j) := by
      rw [pullback.lift_fst]
      exact hpb
    exact IsPullback.of_right hs (pullback.lift_snd _ _ _) hR
  · intro a
    apply pullback.hom_ext
    · simp only [famBC, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hι a
    · simp only [famBC, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, Over.w]
  · intro a
    apply pullback.hom_ext
    · dsimp only [famBC, PkgI3.AbVar.ptObj, Over.mk_left, Over.mk_hom]
      rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (hη a).trans (Category.assoc _ _ _)
    · dsimp only [famBC, PkgI3.AbVar.ptObj, Over.mk_left, Over.mk_hom]
      rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id,
        ← Category.assoc]
      have hw := Over.w (Additive.toMul (P.e.eta a))
      have hid : ∀ f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K),
          f = Spec.map (CommRingCat.ofHom (algebraMap K K)) → f ≫ y = y := by
        rintro f rfl
        rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      exact hid _ hw

theorem genFib_isProper {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (h : IsProper 𝒴.hom) : IsProper (genFib 𝒴).hom := by
  show IsProper (pullback.snd 𝒴.hom (specRatToZloc p))
  infer_instance

theorem genFib_smooth {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (h : SmoothOfRelativeDimension 1 𝒴.hom) : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := by
  show SmoothOfRelativeDimension 1 (pullback.snd 𝒴.hom (specRatToZloc p))
  infer_instance

/-- **The comparison morphism (proved, from `R1univProps`).** -/
theorem exists_genFib_to_Y {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ) :
    ∃ g : genFib 𝒴 ⟶ Y,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ genFib 𝒴) (P : QML3 K),
        IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P →
          Φ K (s ≫ g) = M3.mk P) ∧
      Function.Bijective (fun s : fieldPt Qbar ⟶ genFib 𝒴 => s ≫ g) := by
  obtain ⟨hP, hS, hfib, hinj, hsurj, -, -, -⟩ := hM
  set j := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ genFib 𝒴),
      ∃ P : QML3 K, IsFibreOf (famBC 𝒜 j) s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := hfib K (s.left ≫ j)
    exact ⟨P, isFibreOf_baseChange 𝒜 j s.left P hP⟩
  obtain ⟨g, hg⟩ := R1fpProps.univ h1 (genFib 𝒴) (genFib_isProper 𝒴 hP) (genFib_smooth 𝒴 hS)
    (famBC 𝒜 j) hall
  have hg' : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ genFib 𝒴) (P : QML3 K),
      IsFibreOf 𝒜 (s.left ≫ j) P → Φ K (s ≫ g) = M3.mk P :=
    fun K _ _ s P hP => hg K s P (isFibreOf_baseChange 𝒜 j s.left P hP)
  refine ⟨g, hg', ?_, ?_⟩
  · intro s s' hss
    obtain ⟨P, hPs⟩ := hfib Qbar (s.left ≫ j)
    obtain ⟨P', hPs'⟩ := hfib Qbar (s'.left ≫ j)
    have e : M3.mk P = M3.mk P' := by
      rw [← hg' _ s P hPs, ← hg' _ s' P' hPs']
      exact congrArg (Φ Qbar) hss
    exact genFib_pt_inj 𝒴 s s' (hinj _ _ P P' hPs hPs' e)
  · intro y
    set P := Quotient.out (Φ Qbar y)
    have hPy : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
    obtain ⟨y𝒴, hy⟩ := hsurj P
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y𝒴
    refine ⟨s, (Φ Qbar).injective ?_⟩
    rw [hPy]
    exact hg' Qbar s P (hs ▸ hy)

/-- **Textbook leaf: a bijection on `ℚ̄`-points between proper smooth curves over `ℚ` is an
isomorphism** (not proved here). A morphism `g : S → Y` over `ℚ` of proper smooth curves (smooth
of relative dimension 1) that induces a bijection `S(ℚ̄) → Y(ℚ̄)` is an isomorphism.
STANDARD (locators UNVERIFIED): `g` is quasi-finite (injective on `ℚ̄`-points; a positive-
dimensional fibre has infinitely many) and proper, hence finite (EGA III 4.4.2 / Hartshorne
III Ex. 11.2); in characteristic 0 it is generically étale, so the number of `ℚ̄`-points of a
general fibre over a component of `Y_ℚ̄` is the degree there (Hartshorne II.6.9, III.10.7), so
each degree is 1 and `g` is finite birational onto the normal `Y`, hence an isomorphism
(Hartshorne I.6.12 / II.6.7). -/
def CurveBijIso : Prop :=
  ∀ (S Y : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ g : S ⟶ Y,
    Function.Bijective (fun s : fieldPt Qbar ⟶ S => s ≫ g) → IsIso g

/-! ## Part 11: `Y` is irreducible (chart + finite twist classes) -/

/-- A `ℚ̄`-point factoring through `h` sits in the range of `h`. -/
theorem ptOf_comp_mem_range {X X' : Scheme.{0}} (h : X ⟶ X')
    (y' : Spec (CommRingCat.of Qbar) ⟶ X) :
    (Scheme.SpecToEquivOfField Qbar X' (y' ≫ h)).1 ∈ Set.range h := by
  rw [specToEquivOfField_comp_right]
  exact ⟨_, rfl⟩

/-- **`Y` is irreducible (proved).** The closure `T` of the chart `Spec B` (irreducible, `B` a
domain) is all of `Y`: otherwise the open `Tᶜ` has infinitely many closed points (Jacobson, and no
isolated points by the proved `smoothStalkDimOne`), each the point of a `ℚ̄`-point with `π = ∞`,
while `π⁻¹(∞)` is one twist class, finite by `TwistClassFinite`. -/
theorem irreducible_of_chart (hT : TwistClassFinite) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (E : Type)
    [Field E] [Algebra ℚ[X] E] (hN : NormalizationModel Y π E) : IrreducibleSpace Y.left := by
  obtain ⟨hP, hS, -, -, -, -⟩ := h1
  haveI := hP
  haveI := hS
  obtain ⟨h, hO, himg, -⟩ := hN
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  set T : Set Y.left := closure (Set.range h) with hTdef
  have hrange : IsIrreducible (Set.range h) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ h.continuous.continuousOn
  -- `π = ∞` at every `ℚ̄`-point outside `T`
  have hinf : ∀ y : fieldPt Qbar ⟶ Y, (Scheme.SpecToEquivOfField Qbar Y.left y.left).1 ∉ T →
      π.val (K := Qbar) y.left = OnePoint.infty := by
    intro y hy
    by_contra hne
    obtain ⟨y', hy'⟩ := himg y.left hne
    apply hy
    have := ptOf_comp_mem_range h y'
    rw [← hy'] at this
    exact subset_closure this
  -- the set of `ℚ̄`-points with `π = ∞` is finite
  have hZ : {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = OnePoint.infty}.Finite := by
    by_cases hne : ∃ y₁ : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y₁.left = OnePoint.infty
    · obtain ⟨y₁, hy₁⟩ := hne
      set P₁ := Quotient.out (Φ Qbar y₁)
      refine ((hT P₁).preimage ((Φ Qbar).injective.injOn)).subset ?_
      intro y hy
      set P := Quotient.out (Φ Qbar y)
      have := (h2 y₁ y P₁ P (Quotient.out_eq _).symm (Quotient.out_eq _).symm).1
      have e : π.val (K := Qbar) y₁.left = π.val (K := Qbar) y.left := by
        rw [hy₁]
        exact hy.symm
      exact ⟨P, (Quotient.out_eq _).symm, this.1 e⟩
    · push_neg at hne
      convert Set.finite_empty
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hne y
  rw [irreducibleSpace_def]
  show IsIrreducible (Set.univ : Set Y.left)
  by_contra hTne
  have hTu : T ≠ Set.univ := by
    intro hu
    apply hTne
    rw [← hu]
    exact hrange.closure
  have hU : (Tᶜ : Set Y.left).Nonempty := by
    rw [Set.nonempty_compl]
    exact hTu
  have hUo : IsOpen (Tᶜ : Set Y.left) := isClosed_closure.isOpen_compl
  set C : Set Y.left := Tᶜ ∩ closedPoints Y.left with hC
  -- `C` is infinite
  have hCinf : C.Infinite := by
    intro hCf
    have hCcl : IsClosed C := by
      rw [← Set.biUnion_of_singleton C]
      exact hCf.isClosed_biUnion fun x hx => hx.2
    -- every point of `Tᶜ` is in `C`
    have hsub : (Tᶜ : Set Y.left) ⊆ C := by
      intro x hx
      by_contra hxC
      obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := nonempty_inter_closedPoints (Z := Tᶜ \ C) ⟨x, hx, hxC⟩
        (hUo.sdiff hCcl).isLocallyClosed
      exact hz2 ⟨hz1, hz3⟩
    obtain ⟨x, hx⟩ := hU
    have hopen : IsOpen ({x} : Set Y.left) := by
      have hfin : (C \ {x}).Finite := hCf.sdiff
      have hcl : IsClosed (C \ {x}) := by
        rw [← Set.biUnion_of_singleton (C \ {x})]
        exact hfin.isClosed_biUnion fun z hz => hz.1.2
      have : ({x} : Set Y.left) = Tᶜ \ (C \ {x}) := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_sdiff]
        constructor
        · rintro rfl
          exact ⟨hx, fun h => h.2 rfl⟩
        · rintro ⟨hz, hz'⟩
          by_contra hzx
          exact hz' ⟨hsub hz, hzx⟩
      rw [this]
      exact hUo.sdiff hcl
    exact smoothCurveNoIsolatedPoint_of smoothStalkDimOne ℚ Y.left Y.hom hS x hopen
  -- each point of `C` gives a `ℚ̄`-point with `π = ∞`, injectively
  have hpt : ∀ x : C, ∃ y0 : fieldPt Qbar ⟶ Y,
      (Scheme.SpecToEquivOfField Qbar Y.left y0.left).1 = x := by
    intro x
    obtain ⟨emb, y0, hy0⟩ := exists_qbarPt Y x.1 x.2.2
    refine ⟨y0, ?_⟩
    rw [hy0, Equiv.apply_symm_apply]
  choose f hf using hpt
  haveI : Infinite C := hCinf.to_subtype
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rw [← hf a, ← hf b, hab]
  apply Set.infinite_of_injective_forall_mem hfinj (fun x => ?_) hZ
  show π.val (K := Qbar) (f x).left = OnePoint.infty
  apply hinf
  rw [hf x]
  exact x.2.1

/-! ## Part 12: `𝒴` is reduced and irreducible -/

/-- An étale algebra over a domain is reduced (copied verbatim from task smooth-fibre,
`ZInQKernel/Contrib/SmoothFibre/Basic.lean`, `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain`). -/
theorem isReduced_of_etale_of_isDomain' (P S : Type*) [CommRing P] [IsDomain P] [CommRing S]
    [Algebra P S] [Algebra.Etale P S] : IsReduced S := by
  let K := FractionRing P
  let f := Algebra.TensorProduct.includeRight (R := P) (A := K) (B := S)
  have hinj : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor S (Algebra.ofId P K).toLinearMap).comp
        (Algebra.TensorProduct.lid P S).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective P K)).comp (Algebra.TensorProduct.lid P S).symm.injective
  have : IsReduced (TensorProduct P K S) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (f : S →+* TensorProduct P K S) hinj

/-- A smooth algebra over a domain is reduced (the proof of smooth-fibre's
`isReduced_of_smooth_of_field`, with a domain in place of a field). -/
theorem isReduced_of_smooth_of_isDomain (k A : Type*) [CommRing k] [IsDomain k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  by_contra hne
  let I : Ideal A := (Ideal.span {x} : Submodule A A).annihilator
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hne h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  have := hm.isPrime
  have : Algebra.IsSmoothAt k m := inferInstance
  obtain ⟨f, hf, n, inst, -, hst⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := m)
  have : IsReduced (Localization.Away f) :=
    isReduced_of_etale_of_isDomain' (MvPolynomial (Fin n) k) _
  have h0 : algebraMap A (Localization.Away f) x = 0 := (hx.map _).eq_zero
  obtain ⟨⟨_, k', rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) x).1 h0
  apply hf
  apply hm.isPrime.mem_of_pow_mem k'
  apply hle
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  exact hk

/-- **A smooth `ℤ_(p)`-scheme is reduced (proved).** -/
theorem isReduced_of_smooth_zloc {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    [Smooth 𝒴.hom] : IsReduced 𝒴.left := by
  refine @IsReduced.of_openCover 𝒴.left 𝒴.left.affineCover (fun i => ?_)
  have hsm : Smooth (𝒴.left.affineCover.f i ≫ 𝒴.hom) := inferInstance
  have hring := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp hsm
  letI := ((𝒴.left.affineCover.f i ≫ 𝒴.hom).appTop).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Spec (CommRingCat.of (Zloc p)), ⊤) Γ(𝒴.left.affineCover.X i, ⊤) :=
    RingHom.smooth_algebraMap.1 hring
  haveI : _root_.IsReduced Γ(𝒴.left.affineCover.X i, ⊤) :=
    isReduced_of_smooth_of_isDomain Γ(Spec (CommRingCat.of (Zloc p)), ⊤) _
  exact isReduced_of_isAffine_isReduced _

/-- Points of `𝒴` in `D(p)` lie in the image of the generic fibre. -/
theorem mem_range_of_mem_basicOpen {p : ℕ} [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (x : 𝒴.left)
    (hx : x ∈ 𝒴.left.basicOpen (p : Γ(𝒴.left, ⊤))) :
    x ∈ Set.range (pullback.fst 𝒴.hom (specRatToZloc p)) := by
  rw [Scheme.Pullback.range_fst]
  have hpre : 𝒴.left.basicOpen (p : Γ(𝒴.left, ⊤)) =
      𝒴.hom ⁻¹ᵁ (Spec (CommRingCat.of (Zloc p))).basicOpen
        (p : Γ(Spec (CommRingCat.of (Zloc p)), ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, map_natCast]
  rw [hpre] at hx
  have hx' : 𝒴.hom x ∈ PrimeSpectrum.basicOpen (p : Zloc p) := by
    have := hx
    rw [Scheme.Hom.mem_preimage, basicOpen_eq_of_affine', map_natCast] at this
    exact this
  set q : PrimeSpectrum (Zloc p) := 𝒴.hom x with hqdef
  have hq := zloc_prime_eq_bot q.asIdeal (PrimeSpectrum.mem_basicOpen _ _ |>.1 hx')
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [hq]
  show Ideal.comap (zlocToRat p) ⊥ = ⊥
  apply zloc_prime_eq_bot
  rw [Ideal.mem_comap, map_natCast, Ideal.mem_bot]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- **`𝒴` is irreducible if its generic fibre is (proved).** The image of the generic fibre is
irreducible and contains `D(p)`, which is dense: on an open `U` missing `D(p)`, `p` vanishes
(`𝒴` reduced), against `p` being a non-zero-divisor in the stalks (flatness). -/
theorem irreducibleSpace_of_genFib {p : ℕ} [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) [Flat 𝒴.hom] [IsReduced 𝒴.left]
    [IrreducibleSpace (genFib 𝒴).left] : IrreducibleSpace 𝒴.left := by
  set j : (genFib 𝒴).left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  have hirr : IsIrreducible (Set.range j) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ j.continuous.continuousOn
  have hdense : Dense (Set.range j) := by
    rw [dense_iff_inter_open]
    intro U hU hUne
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    obtain ⟨x, hx⟩ := hUne
    let U' : 𝒴.left.Opens := ⟨U, hU⟩
    let r : Γ(𝒴.left, U') := 𝒴.left.presheaf.map (homOfLE le_top).op (p : Γ(𝒴.left, ⊤))
    have hr : 𝒴.left.basicOpen r = ⊥ := by
      rw [Scheme.basicOpen_res]
      ext z
      simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
        TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
      intro hzU hzB
      have : z ∈ U ∩ Set.range j := ⟨hzU, mem_range_of_mem_basicOpen 𝒴 z hzB⟩
      rw [hempty] at this
      exact this
    rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hr
    have hg : 𝒴.left.presheaf.germ U' x hx r = 0 := by rw [hr, map_zero]
    rw [TopCat.Presheaf.germ_res_apply, map_natCast] at hg
    have := natCast_mem_nonZeroDivisors_stalk p 𝒴 x
    rw [hg] at this
    exact zero_notMem_nonZeroDivisors this
  rw [irreducibleSpace_def]
  show IsIrreducible (Set.univ : Set 𝒴.left)
  rw [← hdense.closure_eq]
  exact hirr.closure

/-! ## Part 13: `ModelIntegral` -/

/-- **`ModelIntegral` from `CurveBijIso` and `TwistClassFinite` (proved).** -/
theorem modelIntegral_of (hT : TwistClassFinite) (hC : CurveBijIso) : ModelIntegral := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 E _ _ _ _ _ _ hN
  obtain ⟨g, -, hbij⟩ := exists_genFib_to_Y hM h1
  haveI : IsIso g := hC (genFib 𝒴) Y (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1)
    h1.1 h1.2.1 g hbij
  haveI : IsIso g.left := (Over.forget _).map_isIso g
  haveI : IrreducibleSpace Y.left := irreducible_of_chart hT h1 h2 E hN
  haveI : IrreducibleSpace (genFib 𝒴).left := by
    rw [irreducibleSpace_def]
    show IsIrreducible (Set.univ : Set (genFib 𝒴).left)
    have hsurj : Function.Surjective (inv g.left) := fun s =>
      ⟨g.left s, by rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl⟩
    rw [← Set.range_eq_univ.2 hsurj, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (inv g.left).continuous.continuousOn
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hM.2.1
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : IsReduced 𝒴.left := isReduced_of_smooth_zloc 𝒴
  haveI : IrreducibleSpace 𝒴.left := irreducibleSpace_of_genFib 𝒴
  exact isIntegral_of_irreducibleSpace_of_isReduced 𝒴.left

end ModelGlue

end

#print axioms ModelGlue.isFibreOf_baseChange
#print axioms ModelGlue.exists_genFib_to_Y
#print axioms ModelGlue.irreducible_of_chart
#print axioms ModelGlue.isReduced_of_smooth_zloc
#print axioms ModelGlue.irreducibleSpace_of_genFib
#print axioms ModelGlue.modelIntegral_of

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# model-glue, step 5: `ModelFunctionField` from `CurveBijIso`

`ModelGlue5.lean` = `ModelGlue4.lean` + this part.
* `isOpenImmersion_specRatToZloc`: `ℚ = ℤ_(p)[1/p]`, so `𝒴_ℚ → 𝒴` is an open immersion.
* `germ_eq_of_closedPoints`, `germ_eq_of_val_eq`, `germ_chart_eq`: Jacobson density for germs at
  the generic point.
* `val_eq_of_same_fibres`: Möbius rigidity on a proper smooth `ℚ`-curve (the argument of
  `Pin.mobiusGlue_of_curveFacts`, from the proved `curveFacts`).
* `ffMap`: the map of function fields along a morphism preserving generic points.
* `modelFunctionField_of_curveBijIso (hT : TwistClassFinite) (hC : CurveBijIso) :
  ModelFunctionField` (proved).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace ModelGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue

/-! ## Part 14: `ℚ = ℤ_(p)[1/p]` -/

theorem zlocToRat_natCast (p : ℕ) [Fact p.Prime] (n : ℕ) : zlocToRat p (n : Zloc p) = n :=
  map_natCast _ n

theorem zlocToRat_injective (p : ℕ) [Fact p.Prime] : Function.Injective (zlocToRat p) := by
  unfold zlocToRat
  rw [IsLocalization.lift_injective_iff]
  intro x y
  have hinj : Function.Injective (algebraMap ℤ (Zloc p)) :=
    IsLocalization.injective (Zloc p) (M := (pIdeal p).primeCompl)
      (le_nonZeroDivisors_of_noZeroDivisors (S := (pIdeal p).primeCompl)
        (fun h0 => h0 (Ideal.zero_mem _)))
  constructor
  · intro h
    rw [hinj h]
  · intro h
    have : x = y := Int.cast_injective h
    rw [this]

/-- `ℚ` is the localization of `ℤ_(p)` away from `p`. -/
theorem zloc_away (p : ℕ) [Fact p.Prime] :
    letI := (zlocToRat p).toAlgebra
    IsLocalization.Away (p : Zloc p) ℚ := by
  letI := (zlocToRat p).toAlgebra
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine isUnit_iff_ne_zero.2 ?_
    show zlocToRat p ((p : Zloc p) ^ n) ≠ 0
    rw [map_pow, zlocToRat_natCast]
    exact pow_ne_zero _ hp
  · intro z
    obtain ⟨e, m, hm, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd z.den_nz p
      (Fact.out : p.Prime).one_lt.ne'
    have hmem : ((m : ℤ)) ∈ (pIdeal p).primeCompl := by
      show (m : ℤ) ∉ Ideal.span {(p : ℤ)}
      rw [Ideal.mem_span_singleton]
      exact_mod_cast hm
    have hm0 : (m : ℚ) ≠ 0 := by
      rintro h0
      apply hm
      rw [Nat.cast_eq_zero.1 h0]
      exact dvd_zero p
    refine ⟨⟨IsLocalization.mk' (Zloc p) z.num ⟨(m : ℤ), hmem⟩, ⟨(p : Zloc p) ^ e, e, rfl⟩⟩, ?_⟩
    show z * zlocToRat p ((p : Zloc p) ^ e) =
      zlocToRat p (IsLocalization.mk' (Zloc p) z.num ⟨(m : ℤ), hmem⟩)
    have hval : zlocToRat p (IsLocalization.mk' (Zloc p) z.num ⟨(m : ℤ), hmem⟩) =
        (z.num : ℚ) / m := by
      unfold zlocToRat
      rw [IsLocalization.lift_mk'_spec]
      simp only [eq_intCast, Int.cast_natCast]
      field_simp
    rw [hval, map_pow, zlocToRat_natCast]
    have hz : (z.den : ℚ) = (p : ℚ) ^ e * m := by exact_mod_cast hden
    conv_lhs => rw [← Rat.num_div_den z]
    rw [hz]
    field_simp
  · intro x y h
    exact ⟨1, by rw [zlocToRat_injective p h]⟩

/-- **`Spec ℚ → Spec ℤ_(p)` is an open immersion.** -/
theorem isOpenImmersion_specRatToZloc (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specRatToZloc p) := by
  letI := (zlocToRat p).toAlgebra
  haveI := zloc_away p
  exact IsOpenImmersion.of_isLocalization (p : Zloc p)

/-! ## Part 15: reducedness over a domain, Jacobson density for germs -/

/-- A smooth scheme over a domain is reduced. -/
theorem isReduced_of_smooth_domain {R : CommRingCat.{0}} [IsDomain R] {X : Scheme.{0}}
    (f : X ⟶ Spec R) [Smooth f] : IsReduced X := by
  refine @IsReduced.of_openCover X X.affineCover (fun i => ?_)
  have hsm : Smooth (X.affineCover.f i ≫ f) := inferInstance
  have hring := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp hsm
  letI := ((X.affineCover.f i ≫ f).appTop).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Spec R, ⊤) Γ(X.affineCover.X i, ⊤) :=
    RingHom.smooth_algebraMap.1 hring
  haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    isReduced_of_smooth_of_isDomain Γ(Spec R, ⊤) _
  exact isReduced_of_isAffine_isReduced _

/-- **Jacobson density for germs at the generic point.** On an integral Jacobson scheme, two
sections defined at the generic point with the same values at all closed points have the same
germ there. -/
theorem germ_eq_of_closedPoints {X : Scheme.{0}} [IsIntegral X] [JacobsonSpace X]
    {U₁ U₂ : X.Opens} (f₁ : Γ(X, U₁)) (f₂ : Γ(X, U₂)) (h₁ : genericPoint X ∈ U₁)
    (h₂ : genericPoint X ∈ U₂)
    (H : ∀ (x : X) (hx1 : x ∈ U₁) (hx2 : x ∈ U₂), IsClosed ({x} : Set X) →
      X.evaluation U₁ x hx1 f₁ = X.evaluation U₂ x hx2 f₂) :
    X.presheaf.germ U₁ (genericPoint X) h₁ f₁ = X.presheaf.germ U₂ (genericPoint X) h₂ f₂ := by
  set W := U₁ ⊓ U₂ with hW
  let d : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op f₁ -
    X.presheaf.map (homOfLE inf_le_right).op f₂
  have hd : X.basicOpen d = ⊥ := by
    by_contra hne
    have hne' : ((X.basicOpen d : X.Opens) : Set X).Nonempty := by
      by_contra h0
      apply hne
      ext1
      simpa [Set.not_nonempty_iff_eq_empty] using h0
    obtain ⟨x, hxb, hxc⟩ := nonempty_inter_closedPoints hne'
      (X.basicOpen d).isOpen.isLocallyClosed
    have hxW : x ∈ W := X.basicOpen_le d hxb
    have h0 := (X.evaluation_ne_zero_iff_mem_basicOpen x hxW d).mpr hxb
    apply h0
    simp only [d, map_sub, eval_res]
    rw [H x hxW.1 hxW.2 hxc, sub_self]
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hd
  have key : X.presheaf.germ W (genericPoint X) ⟨h₁, h₂⟩ d = 0 := by rw [hd, map_zero]
  simp only [d, map_sub, sub_eq_zero] at key
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at key
  exact key

/-- **Two maps to `P¹` with the same `ℚ̄`-values have the same germ at the generic point** (on an
integral `ℚ`-scheme locally of finite type). -/
theorem germ_eq_of_val_eq (Y : Over (Spec (CommRingCat.of ℚ))) [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (σ τ : ToP1 Y.left)
    (hval : ∀ y : fieldPt Qbar ⟶ Y, σ.val (K := Qbar) y.left = τ.val (K := Qbar) y.left)
    (hσ : genericPoint Y.left ∈ σ.U) :
    ∃ hτ : genericPoint Y.left ∈ τ.U,
      Y.left.presheaf.germ σ.U _ hσ σ.f = Y.left.presheaf.germ τ.U _ hτ τ.f := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hcl : ∀ x : Y.left, IsClosed ({x} : Set Y.left) → (x ∈ σ.U → x ∈ τ.U) ∧
      ∀ (h1 : x ∈ σ.U) (h2 : x ∈ τ.U),
        Y.left.evaluation σ.U x h1 σ.f = Y.left.evaluation τ.U x h2 τ.f := by
    intro x hx
    obtain ⟨emb, y0, hy0⟩ := exists_qbarPt Y x hx
    have e := hval y0
    unfold ToP1.val at e
    rw [hy0, Equiv.apply_symm_apply] at e
    refine ⟨fun h1 => ?_, fun h1 h2 => ?_⟩
    · by_contra h2
      rw [dif_pos h1, dif_neg h2] at e
      exact OnePoint.coe_ne_infty _ e
    · rw [dif_pos h1, dif_pos h2] at e
      exact emb.hom.injective (OnePoint.coe_injective e)
  have hτ : genericPoint Y.left ∈ τ.U := by
    obtain ⟨x, hxσ, hxc⟩ := nonempty_inter_closedPoints (Z := (σ.U : Set Y.left))
      ⟨_, hσ⟩ σ.U.isOpen.isLocallyClosed
    exact ((genericPoint_spec Y.left).mem_open_set_iff τ.U.isOpen).mpr
      ⟨x, trivial, (hcl x hxc).1 hxσ⟩
  exact ⟨hτ, germ_eq_of_closedPoints σ.f τ.f hσ hτ fun x h1 h2 hx => (hcl x hx).2 h1 h2⟩

/-- **On the chart `Spec B`, the germ of `π ∘ h` at the generic point is `b`** when `π` takes the
value `ψ(b)` at every `ℚ̄`-point `ψ : B → ℚ̄` of the chart. -/
theorem germ_chart_eq {B : Type} [CommRing B] [IsDomain B] {Y : Over (Spec (CommRingCat.of ℚ))}
    [LocallyOfFiniteType Y.hom] (h : Spec (CommRingCat.of B) ⟶ Y.left) [IsOpenImmersion h]
    (π : ToP1 Y.left) (b : B)
    (hval : ∀ ψ : B →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = OnePoint.some (ψ b))
    (hη : genericPoint (Spec (CommRingCat.of B)) ∈ (π.comp h).U) :
    (Spec (CommRingCat.of B)).presheaf.germ (π.comp h).U _ hη (π.comp h).f =
      (Spec (CommRingCat.of B)).presheaf.germ ⊤ _ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
  let Z : Over (Spec (CommRingCat.of ℚ)) := Over.mk (h ≫ Y.hom)
  haveI : LocallyOfFiniteType Z.hom := by
    show LocallyOfFiniteType (h ≫ Y.hom)
    infer_instance
  haveI : JacobsonSpace (Spec (CommRingCat.of B)) := LocallyOfFiniteType.jacobsonSpace Z.hom
  refine germ_eq_of_closedPoints (U₂ := ⊤) _ _ hη trivial fun x hx1 hx2 hxc => ?_
  obtain ⟨emb, y0, hy0⟩ := exists_qbarPt Z x hxc
  have hpt : ptOf (y0.left : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of B)) = x := by
    show (Scheme.SpecToEquivOfField Qbar _ y0.left).1 = x
    rw [hy0, Equiv.apply_symm_apply]
  generalize (y0.left : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of B)) = z at hpt
  subst hpt
  obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = z := ⟨Spec.preimage z, Spec.map_preimage z⟩
  apply (Scheme.SpecToEquivOfField Qbar _ (Spec.map ψ)).2.hom.injective
  change ev (Spec.map ψ) hx1 (π.comp h).f = ev (Spec.map ψ) hx2 _
  rw [ImagePlane.ev_spec_top]
  have e := hval ψ.hom
  rw [CommRingCat.ofHom_hom, ← ToP1.val_comp_right] at e
  unfold ToP1.val at e
  rw [dif_pos (show (Scheme.SpecToEquivOfField Qbar _ (Spec.map ψ)).1 ∈ (π.comp h).U from hx1)]
    at e
  exact OnePoint.coe_injective e

/-! ## Part 16: Möbius rigidity on a proper smooth `ℚ`-curve -/

/-- **Möbius rigidity (the argument of `Pin.mobiusGlue_of_curveFacts`, compiled).** Two maps to
`P¹` on a proper smooth `ℚ`-curve with the same fibre relation on `ℚ̄`-points, finite fibres, and
the values `0, ∞, −16/27` at three common points take the same values. -/
theorem val_eq_of_same_fibres {S : Over (Spec (CommRingCat.of ℚ))} (hprop : IsProper S.hom)
    (hsm : SmoothOfRelativeDimension 1 S.hom) (σ σ' : ToP1 S.left)
    (hrel : ∀ s₁ s₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) s₁.left = σ.val (K := Qbar) s₂.left
      ↔ σ'.val (K := Qbar) s₁.left = σ'.val (K := Qbar) s₂.left)
    (y₄ y₃ y₂ : fieldPt Qbar ⟶ S)
    (σ₄ : σ.val (K := Qbar) y₄.left = OnePoint.some 0)
    (π₄ : σ'.val (K := Qbar) y₄.left = OnePoint.some 0)
    (σ₃ : σ.val (K := Qbar) y₃.left = OnePoint.infty)
    (π₃ : σ'.val (K := Qbar) y₃.left = OnePoint.infty)
    (σ₂ : σ.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27))
    (π₂ : σ'.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27))
    (hfin : ∀ s : fieldPt Qbar ⟶ S, {s' : fieldPt Qbar ⟶ S |
      σ.val (K := Qbar) s'.left = σ.val (K := Qbar) s.left}.Finite) :
    ∀ s : fieldPt Qbar ⟶ S, σ'.val (K := Qbar) s.left = σ.val (K := Qbar) s.left := by
  have hsurj := curveFacts.2 S hprop hsm ⟨y₄⟩ σ hfin
  obtain ⟨F, G, hcop, hFG⟩ := curveFacts.1 S hprop hsm σ σ' (fun s₁ s₂ h => (hrel s₁ s₂).1 h)
  have hinj : ∀ s t : Qbar, Mob.ratEval F G s = Mob.ratEval F G t → s = t := by
    intro s t hst
    obtain ⟨ys, hys⟩ := hsurj (OnePoint.some s)
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : σ'.val (K := Qbar) ys.left = σ'.val (K := Qbar) yt.left := by
      rw [hFG ys s hys, hFG yt t hyt, hst]
    have := (hrel ys yt).2 e
    rw [hys, hyt] at this
    exact OnePoint.coe_injective this
  have hdeg := Mob.natDegree_le_one_of_injective hcop hinj
  have hpole : ∀ t, Mob.ratEval F G t ≠ OnePoint.infty := by
    intro t ht
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : σ'.val (K := Qbar) yt.left = σ'.val (K := Qbar) y₃.left := by
      rw [hFG yt t hyt, ht, π₃]
    have := (hrel yt y₃).2 e
    rw [hyt, σ₃] at this
    exact OnePoint.coe_ne_infty t this
  have h0 : Mob.ratEval F G 0 = OnePoint.some 0 := by rw [← hFG y₄ 0 σ₄, π₄]
  have hc : Mob.ratEval F G (-16 / 27) = OnePoint.some (-16 / 27) := by
    rw [← hFG y₂ _ σ₂, π₂]
  have hid := Mob.ratEval_eq_self hdeg.1 hpole h0 (by norm_num) hc
  intro s
  by_cases hinf : σ.val (K := Qbar) s.left = OnePoint.infty
  · rw [hinf, ← π₃]
    exact (hrel s y₃).1 (by rw [hinf, σ₃])
  · obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← ht, hFG s t ht.symm, hid t]

/-! ## Part 17: maps of function fields -/

variable {X Z : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Z]

theorem isIso_stalkSpecializes_of_eq {W : Scheme.{0}} {x y : W} (h : x ⤳ y) (e : x = y) :
    IsIso (W.presheaf.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

/-- The map of function fields along `f : X → Z` with `f(η_X) = η_Z`. -/
def ffMap (f : X ⟶ Z) (e : f (genericPoint X) = genericPoint Z) :
    Z.functionField ⟶ X.functionField :=
  Z.presheaf.stalkSpecializes (show f (genericPoint X) ⤳ genericPoint Z by rw [e]) ≫
    f.stalkMap (genericPoint X)

theorem ffMap_germ (f : X ⟶ Z) (e : f (genericPoint X) = genericPoint Z)
    (U : Z.Opens) (hU : genericPoint Z ∈ U) (s : Γ(Z, U)) (hU' : genericPoint X ∈ f ⁻¹ᵁ U) :
    ffMap f e (Z.presheaf.germ U _ hU s) = X.presheaf.germ (f ⁻¹ᵁ U) _ hU' (f.app U s) := by
  rw [ffMap, CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

theorem ffMap_bijective (f : X ⟶ Z) [IsOpenImmersion f]
    (e : f (genericPoint X) = genericPoint Z) : Function.Bijective (ffMap f e) := by
  haveI := isIso_stalkSpecializes_of_eq (W := Z)
    (show f (genericPoint X) ⤳ genericPoint Z by rw [e]) e
  haveI : IsIso (ffMap f e) := by unfold ffMap; infer_instance
  exact ConcreteCategory.bijective_of_isIso (ffMap f e)

/-! ## Part 18: `ModelFunctionField` -/

/-- **`ModelFunctionField` from `CurveBijIso` and `TwistClassFinite` (proved).** `R1univProps`
gives `g : 𝒴_ℚ → Y`, bijective on `ℚ̄`-points, an isomorphism by `CurveBijIso`; `𝒴_ℚ → 𝒴` is an
open immersion (`ℚ = ℤ_(p)[1/p]`), so `ℚ(𝒴) ≅ ℚ(𝒴_ℚ) ≅ ℚ(Y) ≅ ℚ(Spec B) ≅ E`; under these, the
germ of `ρ` goes to the germ of `ρ ∘ j`, equal (Möbius rigidity on `𝒴_ℚ` + Jacobson) to that of
`π ∘ g`, i.e. to the germ of `π`, whose image on the chart is `X` (Jacobson on `Spec B`). -/
theorem modelFunctionField_of_curveBijIso (hT : TwistClassFinite) (hC : CurveBijIso) :
    ModelFunctionField := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 hI ρ hρ hη E _ _ _ _ _ _ hN
  obtain ⟨g, hgΦ, hbij⟩ := exists_genFib_to_Y hM h1
  have hSp := genFib_isProper 𝒴 hM.1
  have hSs := genFib_smooth 𝒴 hM.2.1
  haveI : IsIso g := hC (genFib 𝒴) Y hSp hSs h1.1 h1.2.1 g hbij
  haveI : IsIso g.left := (Over.forget _).map_isIso g
  haveI : SmoothOfRelativeDimension 1 Y.hom := h1.2.1
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := hSs
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 (genFib 𝒴).hom
  haveI : IrreducibleSpace Y.left := irreducible_of_chart hT h1 h2 E hN
  haveI : IsReduced Y.left := isReduced_of_smooth_domain Y.hom
  haveI : IsIntegral Y.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsIntegral (genFib 𝒴).left := IsIntegral.of_isIso (inv g.left)
  haveI : LocallyOfFiniteType (genFib 𝒴).hom := inferInstance
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : IsOpenImmersion (specRatToZloc p) := isOpenImmersion_specRatToZloc p
  set j : (genFib 𝒴).left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  haveI : IsOpenImmersion j :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)
  have ej : j (genericPoint (genFib 𝒴).left) = genericPoint 𝒴.left :=
    genericPoint_eq_of_isOpenImmersion j
  have eg : g.left (genericPoint (genFib 𝒴).left) = genericPoint Y.left :=
    genericPoint_eq_of_isOpenImmersion g.left
  obtain ⟨h, hO, -, hval⟩ := hN
  haveI := hO
  have eh : h (genericPoint (Spec (CommRingCat.of (integralClosure ℚ[X] E)))) = genericPoint Y.left :=
    genericPoint_eq_of_isOpenImmersion h
  set σ : ToP1 (genFib 𝒴).left := ρ.comp j with hσ
  set τ : ToP1 (genFib 𝒴).left := π.comp g.left with hτ
  have hση : genericPoint (genFib 𝒴).left ∈ σ.U := by
    show j (genericPoint _) ∈ ρ.U
    rw [ej]
    exact hη
  -- the values of `σ = ρ ∘ j` and `τ = π ∘ g` agree (Möbius rigidity)
  have hvalS : ∀ s : fieldPt Qbar ⟶ genFib 𝒴,
      τ.val (K := Qbar) s.left = σ.val (K := Qbar) s.left := by
    have hσs : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, σ.val (K := Qbar) s.left = ρ.val (s.left ≫ j) :=
      fun s => ToP1.val_comp_right ρ j s.left
    have hτs : ∀ s : fieldPt Qbar ⟶ genFib 𝒴,
        τ.val (K := Qbar) s.left = π.val (K := Qbar) (s ≫ g).left :=
      fun s => ToP1.val_comp_right π g.left s.left
    obtain ⟨-, -, hfib, hinjM, hsurjM, -, -, -⟩ := hM
    have hP : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, ∃ P : QML3 Qbar, IsFibreOf 𝒜 (s.left ≫ j) P :=
      fun s => hfib Qbar (s.left ≫ j)
    choose Pof hPof using hP
    have hΦ' : ∀ (s : fieldPt Qbar ⟶ genFib 𝒴) (P : QML3 Qbar), IsFibreOf 𝒜 (s.left ≫ j) P →
        Φ Qbar (s ≫ g) = M3.mk P := fun s P hP => hgΦ Qbar s P hP
    have hrel : ∀ s₁ s₂ : fieldPt Qbar ⟶ genFib 𝒴,
        σ.val (K := Qbar) s₁.left = σ.val (K := Qbar) s₂.left ↔
          τ.val (K := Qbar) s₁.left = τ.val (K := Qbar) s₂.left := by
      intro s₁ s₂
      rw [hσs, hσs, hτs, hτs, (hρ _ _ _ _ (hPof s₁) (hPof s₂)).1,
        (h2 _ _ _ _ (hΦ' s₁ _ (hPof s₁)) (hΦ' s₂ _ (hPof s₂))).1]
    have hcm : ∀ P : QML3 Qbar, ∃ s : fieldPt Qbar ⟶ genFib 𝒴, IsFibreOf 𝒜 (s.left ≫ j) P := by
      intro P
      obtain ⟨y, hy⟩ := hsurjM P
      obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
      exact ⟨s, hs ▸ hy⟩
    obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
    obtain ⟨y₄, f₄⟩ := hcm P₄
    obtain ⟨y₃, f₃⟩ := hcm P₃
    obtain ⟨y₂, f₂⟩ := hcm P₂
    have hfin : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, {s' : fieldPt Qbar ⟶ genFib 𝒴 |
        σ.val (K := Qbar) s'.left = σ.val (K := Qbar) s.left}.Finite := by
      intro s
      have hmkinj : Function.Injective (fun s : fieldPt Qbar ⟶ genFib 𝒴 => M3.mk (Pof s)) := by
        intro s s' hss
        exact genFib_pt_inj 𝒴 s s' (hinjM _ _ _ _ (hPof s) (hPof s') hss)
      refine ((hT (Pof s)).preimage (Set.injOn_of_injective hmkinj)).subset ?_
      intro s' hs'
      have e : σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left := hs'.symm
      rw [hσs, hσs] at e
      exact ⟨Pof s', rfl, ((hρ _ _ _ _ (hPof s) (hPof s')).1).1 e⟩
    refine val_eq_of_same_fibres hSp hSs σ τ hrel y₄ y₃ y₂ ?_ ?_ ?_ ?_ ?_ ?_ hfin
    · rw [hσs]; exact (hρ _ _ _ _ f₄ f₄).2.1 c₄
    · rw [hτs]; exact (h2 _ _ _ _ (hΦ' y₄ P₄ f₄) (hΦ' y₄ P₄ f₄)).2.1 c₄
    · rw [hσs]; exact (hρ _ _ _ _ f₃ f₃).2.2.1 c₃
    · rw [hτs]; exact (h2 _ _ _ _ (hΦ' y₃ P₃ f₃) (hΦ' y₃ P₃ f₃)).2.2.1 c₃
    · rw [hσs]; exact (hρ _ _ _ _ f₂ f₂).2.2.2 c₂
    · rw [hτs]; exact (h2 _ _ _ _ (hΦ' y₂ P₂ f₂) (hΦ' y₂ P₂ f₂)).2.2.2 c₂
  obtain ⟨hτη, hgerm⟩ := germ_eq_of_val_eq (genFib 𝒴) σ τ (fun s => (hvalS s).symm) hση
  have hπη : genericPoint Y.left ∈ π.U := by
    have : g.left (genericPoint _) ∈ π.U := hτη
    rwa [eg] at this
  have hBη : genericPoint (Spec (CommRingCat.of (integralClosure ℚ[X] E))) ∈ (π.comp h).U := by
    show h _ ∈ π.U
    rw [eh]
    exact hπη
  -- the maps of function fields
  have hφb := ffMap_bijective j ej
  have hψb := ffMap_bijective g.left eg
  have hθb := ffMap_bijective h eh
  haveI : IsFractionRing (integralClosure ℚ[X] E) E := integralClosure.isFractionRing_of_finite_extension (RatFunc ℚ) E
  letI algB : Algebra (CommRingCat.of (integralClosure ℚ[X] E))
      (Spec (CommRingCat.of (integralClosure ℚ[X] E))).functionField :=
    @instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (integralClosure ℚ[X] E)) _
  haveI : IsFractionRing (CommRingCat.of (integralClosure ℚ[X] E))
      (Spec (CommRingCat.of (integralClosure ℚ[X] E))).functionField :=
    functionField_isFractionRing_of_affine _
  let hBe : (CommRingCat.of (integralClosure ℚ[X] E)) ≃+* (integralClosure ℚ[X] E) :=
    RingEquiv.refl _
  let eB : (Spec (CommRingCat.of (integralClosure ℚ[X] E))).functionField ≃+* E :=
    IsFractionRing.ringEquivOfRingEquiv hBe
  let ψe := RingEquiv.ofBijective (ffMap g.left eg).hom hψb
  refine ⟨eB.toRingHom.comp
    ((ffMap h eh).hom.comp (ψe.symm.toRingHom.comp (ffMap j ej).hom)), ?_, ?_⟩
  · exact eB.surjective.comp (hθb.2.comp (ψe.symm.surjective.comp hφb.2))
  · have k1 : (ffMap j ej) (𝒴.left.presheaf.germ ρ.U _ hη ρ.f) =
        (genFib 𝒴).left.presheaf.germ σ.U _ hση σ.f := ffMap_germ j ej ρ.U hη ρ.f hση
    have k2 : (ffMap g.left eg) (Y.left.presheaf.germ π.U _ hπη π.f) =
        (genFib 𝒴).left.presheaf.germ τ.U _ hτη τ.f := ffMap_germ g.left eg π.U hπη π.f hτη
    have k3 : ψe.symm ((genFib 𝒴).left.presheaf.germ σ.U _ hση σ.f) =
        Y.left.presheaf.germ π.U _ hπη π.f := by
      rw [hgerm, ← k2]
      exact ψe.symm_apply_apply _
    have k4 : (ffMap h eh) (Y.left.presheaf.germ π.U _ hπη π.f) =
        (Spec (CommRingCat.of (integralClosure ℚ[X] E))).presheaf.germ (π.comp h).U _ hBη (π.comp h).f :=
      ffMap_germ h eh π.U hπη π.f hBη
    have k5 := germ_chart_eq h π (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) hval hBη
    have k6 : (Spec (CommRingCat.of (integralClosure ℚ[X] E))).presheaf.germ ⊤ _ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)) =
          algebraMap (CommRingCat.of (integralClosure ℚ[X] E))
            (Spec (CommRingCat.of (integralClosure ℚ[X] E))).functionField
            (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) := rfl
    simp only [RingHom.comp_apply]
    rw [k1]
    erw [k3]
    rw [k4, k5, k6]
    show eB (algebraMap (CommRingCat.of (integralClosure ℚ[X] E)) _
      (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)) = _
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact (IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E X).symm

/-- **`ModelComparison` from `CurveBijIso` and the leaf T5 (proved).** -/
theorem modelComparison_of_curveBijIso (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso) :
    ModelComparison :=
  modelComparison_of (modelIntegral_of (twistClassFinite hT) hC)
    (modelFunctionField_of_curveBijIso (twistClassFinite hT) hC)

end ModelGlue

end

#print axioms ModelGlue.isOpenImmersion_specRatToZloc
#print axioms ModelGlue.germ_eq_of_val_eq
#print axioms ModelGlue.germ_chart_eq
#print axioms ModelGlue.val_eq_of_same_fibres
#print axioms ModelGlue.ffMap_bijective
#print axioms ModelGlue.modelFunctionField_of_curveBijIso
#print axioms ModelGlue.modelComparison_of_curveBijIso

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# model-glue, step 6: composites

`ModelGlue6.lean` = `ModelGlue5.lean` + this part.
* `smoothFibreReduced' : SmoothFibreReduced` — the proof of task smooth-fibre
  (`ZInQKernel/Contrib/SmoothFibre/Basic.lean`, branch wip/smooth-fibre, `ZInQ.SmoothFibre.
  smoothFibreReduced`, whose statement is verbatim the same), with its field lemma replaced by
  `isReduced_of_smooth_of_isDomain` above.
* `modelCoordinate_of_residue` (step 1) and `modelComparison_of_curveBijIso` (step 5) give both
  targets; `heckeVertWitness_of_curveBijIso` is the resulting composite.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace ModelGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue TensorProduct

/-- **`SmoothFibreReduced`, proved** (task smooth-fibre's proof). -/
theorem smoothFibreReduced' : SmoothFibreReduced := by
  intro R A _ _ φ hφ m hm
  let := φ.toAlgebra
  have : Algebra.Smooth R A := RingHom.smooth_algebraMap.1 hφ
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have h1 : IsReduced ((R ⧸ m) ⊗[R] A) := isReduced_of_smooth_of_isDomain (R ⧸ m) _
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m
  let e' := e.toRingEquiv.trans (Algebra.TensorProduct.comm R A (R ⧸ m)).toRingEquiv
  have h2 : IsReduced (A ⧸ m.map (algebraMap R A)) :=
    isReduced_of_injective (e' : A ⧸ m.map (algebraMap R A) →+* (R ⧸ m) ⊗[R] A) e'.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).2 h2

/-- **The two targets from the remaining inputs** (compiled). -/
theorem modelCoordinate_and_modelComparison (hT : ObjBridge.TorsionStructure)
    (hD : ModelCoordinateResidue) (hC : CurveBijIso) : ModelCoordinate ∧ ModelComparison :=
  ⟨modelCoordinate_of_residue hD, modelComparison_of_curveBijIso hT hC⟩

/-- **`HeckeVertWitness` from the leaves, T5, `ModelCoordinateResidue` and `CurveBijIso`**
(compiled; `SmoothFibreReduced` is proved above). -/
theorem heckeVertWitness_of_curveBijIso (hL : ShimuraGoodReduction) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hD : ModelCoordinateResidue) (hC : CurveBijIso) :
    HeckeVertWitness :=
  heckeVertWitness_of_leaves hL hRR smoothFibreReduced' (modelCoordinate_of_residue hD)
    (modelComparison_of_curveBijIso hT hC)

end ModelGlue

end

#print axioms ModelGlue.smoothFibreReduced'
#print axioms ModelGlue.modelCoordinate_and_modelComparison
#print axioms ModelGlue.heckeVertWitness_of_curveBijIso

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue: a reduction of `ModelGlue.ModelCoordinateResidue`

Everything above this banner is `scratch/model-glue/ModelGlue6.lean` verbatim (whole file).
`ModelGlue.ModelCoordinateResidue` is used by name from that prefix, so the theorem below has
exactly that type.

* Part 1 (commutative algebra / scheme theory, compiled): a polynomial-chart map `ρ' : Z → P¹`
  pulled back along an integral `q : X → Z` has transcendental residue at every point `ξ` of `X`
  whose residue field is not algebraic over its prime field (`transcendental_of_polyCharts`).
* Part 2: two smaller named Props and the reduction
  `modelCoordinateResidue_of_quotient : QuotientP1Coordinate → SpecialFibreTranscendence →
  ModelCoordinateResidue` (compiled).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-! ## Part 1: transcendence of a pulled-back polynomial coordinate -/

/-- Every element of `κ(x)` is a quotient of evaluations of sections over an affine open
neighbourhood; so if those evaluations are algebraic over the prime field, so is `κ(x)`. -/
theorem residueField_isAlgebraic_of_affine {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    (x : X) (hx : x ∈ W)
    (h : ∀ a : Γ(X, W), IsAlgebraic (⊥ : Subfield (X.residueField x)) (X.evaluation W x hx a)) :
    Algebra.IsAlgebraic (⊥ : Subfield (X.residueField x)) (X.residueField x) := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hW.isLocalization_stalk ⟨x, hx⟩
  refine ⟨fun y => ?_⟩
  obtain ⟨s, rfl⟩ := X.residue_surjective x y
  obtain ⟨⟨a, b⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  have hb : IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk x) b) := IsLocalization.map_units _ b
  have hev : ∀ c : Γ(X, W), X.residue x (algebraMap Γ(X, W) (X.presheaf.stalk x) c) =
      X.evaluation W x hx c := fun c => rfl
  have key : X.residue x (IsLocalization.mk' (X.presheaf.stalk x) a b) *
      X.evaluation W x hx b = X.evaluation W x hx a := by
    rw [← hev, ← hev, ← map_mul, IsLocalization.mk'_spec]
  have hb0 : X.evaluation W x hx (b : Γ(X, W)) ≠ 0 := by
    rw [← hev]; exact (hb.map (X.residue x).hom).ne_zero
  have hy : X.residue x (IsLocalization.mk' (X.presheaf.stalk x) a b) =
      X.evaluation W x hx a * (X.evaluation W x hx b)⁻¹ := by
    rw [← key, mul_inv_cancel_right₀ hb0]
  rw [hy, ← mem_algebraicClosure_iff]
  exact mul_mem (mem_algebraicClosure_iff.2 (h a)) (inv_mem (mem_algebraicClosure_iff.2 (h b)))

/-- A ring homomorphism from a localization of `ℤ` to a field lands in the prime field. -/
theorem mem_bot_of_localization {R : Type*} [CommRing R] [Algebra ℤ R] (M : Submonoid ℤ)
    [IsLocalization M R]
    {K : Type*} [Field K] (ψ : R →+* K) (z : R) : ψ z ∈ (⊥ : Subfield K) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have hb : IsUnit (ψ (algebraMap ℤ R b)) := (IsLocalization.map_units R b).map ψ
  have key : ψ (IsLocalization.mk' R a b) * ψ (algebraMap ℤ R b) = ψ (algebraMap ℤ R a) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  have hy : ψ (IsLocalization.mk' R a b) = ψ (algebraMap ℤ R a) * (ψ (algebraMap ℤ R b))⁻¹ := by
    rw [← key, mul_inv_cancel_right₀ hb.ne_zero]
  rw [hy]
  simp only [eq_intCast, map_intCast]
  exact mul_mem (intCast_mem _ _) (inv_mem (intCast_mem _ _))

/-- **A chart with a polynomial coordinate ring**: if `Γ(Z, W)` is generated by `h` over a
localization `R` of `ℤ` and the evaluation of `q^* h` at `ξ` is algebraic over the prime field,
then every section over `W` evaluates at `ξ` (through `q`) to an algebraic element. -/
theorem eval_mem_algebraicClosure {X Z : Scheme.{0}} (q : X ⟶ Z) {W : Z.Opens} {R : Type}
    [CommRing R] [Algebra ℤ R] (M : Submonoid ℤ) [IsLocalization M R] (c : R →+* Γ(Z, W)) (h : Γ(Z, W))
    (hs : Function.Surjective (eval₂RingHom c h)) (ξ : X) (hξ : ξ ∈ q ⁻¹ᵁ W)
    (halg : IsAlgebraic (⊥ : Subfield (X.residueField ξ))
      (X.evaluation (q ⁻¹ᵁ W) ξ hξ (q.app W h))) (s : Γ(Z, W)) :
    X.evaluation (q ⁻¹ᵁ W) ξ hξ (q.app W s) ∈
      algebraicClosure (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ) := by
  obtain ⟨H, rfl⟩ := hs s
  set ν : Γ(Z, W) →+* X.residueField ξ := (q.app W ≫ X.evaluation (q ⁻¹ᵁ W) ξ hξ).hom
  have hν : ∀ t, X.evaluation (q ⁻¹ᵁ W) ξ hξ (q.app W t) = ν t := fun t => rfl
  rw [hν, coe_eval₂RingHom, Polynomial.hom_eval₂]
  have hx : ν h ∈ algebraicClosure (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ) :=
    mem_algebraicClosure_iff.2 halg
  have hc : ∀ r : R, (ν.comp c) r ∈
      algebraicClosure (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ) := by
    intro r
    have := mem_bot_of_localization M (ν.comp c) r
    rw [mem_algebraicClosure_iff]
    exact isAlgebraic_algebraMap (⟨_, this⟩ : (⊥ : Subfield (X.residueField ξ)))
  induction H using Polynomial.induction_on with
  | C a => simpa using hc a
  | add f g hf hg => rw [eval₂_add]; exact add_mem hf hg
  | monomial n a _ =>
    rw [eval₂_mul, eval₂_C, eval₂_X_pow]
    exact mul_mem (hc a) (pow_mem hx _)

/-- **Through an integral morphism**: if every section over an affine `W ⊆ Z` evaluates at `ξ`
(through `q`) to an algebraic element, then `κ(ξ)` is algebraic over the prime field. -/
theorem residueField_isAlgebraic_of_integral {X Z : Scheme.{0}} (q : X ⟶ Z) [IsIntegralHom q]
    {W : Z.Opens} (hW : IsAffineOpen W) (ξ : X) (hξ : ξ ∈ q ⁻¹ᵁ W)
    (hC : ∀ s : Γ(Z, W), X.evaluation (q ⁻¹ᵁ W) ξ hξ (q.app W s) ∈
      algebraicClosure (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ)) :
    Algebra.IsAlgebraic (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ) := by
  have hW' : IsAffineOpen (q ⁻¹ᵁ W) := hW.preimage q
  have hint := q.isIntegral_app W hW
  set C := algebraicClosure (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ)
  set ν : Γ(Z, W) →+* X.residueField ξ := (q.app W ≫ X.evaluation (q ⁻¹ᵁ W) ξ hξ).hom
  let ν' : Γ(Z, W) →+* C := ν.codRestrict C hC
  refine residueField_isAlgebraic_of_affine hW' ξ hξ fun a => ?_
  obtain ⟨P, hPm, hP⟩ := hint a
  have hI : IsIntegral C (X.evaluation (q ⁻¹ᵁ W) ξ hξ a) := by
    refine ⟨P.map ν', hPm.map _, ?_⟩
    rw [eval₂_map]
    have : (algebraMap C (X.residueField ξ)).comp ν' =
        (X.evaluation (q ⁻¹ᵁ W) ξ hξ).hom.comp (q.app W).hom := by
      ext t; rfl
    rw [this, ← Polynomial.hom_eval₂, hP, map_zero]
  exact (isIntegral_trans _ hI).isAlgebraic

/-- **The pulled-back coordinate of a polynomial-chart `ToP1` has transcendental residue.** Let
`q : X → Z` be integral and `ρ' : Z → P¹` a map whose charts `U = ρ'⁻¹(𝔸¹)`, `V = ρ'⁻¹(P¹ ∖ 0)` are
affine with coordinate rings generated by `f`, resp. `g`, over a localization `R` of `ℤ` (e.g.
`ρ'` an isomorphism onto `P¹_R`). If `κ(ξ)` is not algebraic over its prime field, then `q(ξ) ∈ U`
and the residue of `q^* f` at `ξ` is transcendental over the prime field. -/
theorem transcendental_of_polyCharts {X Z : Scheme.{0}} (q : X ⟶ Z) [IsIntegralHom q]
    (ρ' : ToP1 Z) {R : Type} [CommRing R] [Algebra ℤ R] (M : Submonoid ℤ) [IsLocalization M R]
    (cU : R →+* Γ(Z, ρ'.U)) (cV : R →+* Γ(Z, ρ'.V)) (hU : IsAffineOpen ρ'.U)
    (hV : IsAffineOpen ρ'.V) (hsU : Function.Surjective (eval₂RingHom cU ρ'.f))
    (hsV : Function.Surjective (eval₂RingHom cV ρ'.g)) (ξ : X)
    (hna : ¬ Algebra.IsAlgebraic (⊥ : Subfield (X.residueField ξ)) (X.residueField ξ)) :
    ∃ hξ : ξ ∈ q ⁻¹ᵁ ρ'.U, Transcendental (⊥ : Subfield (X.residueField ξ))
      (X.evaluation (q ⁻¹ᵁ ρ'.U) ξ hξ (q.app ρ'.U ρ'.f)) := by
  by_cases hξ : ξ ∈ q ⁻¹ᵁ ρ'.U
  · refine ⟨hξ, fun halg => hna ?_⟩
    exact residueField_isAlgebraic_of_integral q hU ξ hξ
      (eval_mem_algebraicClosure q M cU ρ'.f hsU ξ hξ halg)
  · exfalso
    have hcov : q ξ ∈ ρ'.U ⊔ ρ'.V := by rw [ρ'.cover]; trivial
    have hξV : ξ ∈ q ⁻¹ᵁ ρ'.V := (TopologicalSpace.Opens.mem_sup.1 hcov).resolve_left hξ
    have h0 : X.evaluation (q ⁻¹ᵁ ρ'.V) ξ hξV (q.app ρ'.V ρ'.g) = 0 := by
      rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, ← Scheme.preimage_basicOpen,
        ρ'.basicOpen_g]
      exact fun h => hξ h.1
    apply hna
    refine residueField_isAlgebraic_of_integral q hV ξ hξV
      (eval_mem_algebraicClosure q M cV ρ'.g hsV ξ hξV ?_)
    rw [h0]; exact isAlgebraic_zero


/-! ## Part 2: the reduction -/

/-- The structure map `ℤ_(p) → Γ(𝒵, W)` of a scheme `𝒵` over `ℤ_(p)`. -/
def baseToSections {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    (W : 𝒵.left.Opens) : Zloc p →+* Γ(𝒵.left, W) :=
  (𝒵.left.presheaf.map (homOfLE le_top).op).hom.comp
    ((𝒵.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (Zloc p))).inv.hom)

/-- **`ρ' : 𝒵 → P¹_{ℤ_(p)}` is an isomorphism** (by charts; a genuine definition). `P¹_{ℤ_(p)}` is
covered by `𝔸¹ = Spec ℤ_(p)[t]` and `Spec ℤ_(p)[1/t]`, whose preimages under `ρ'` are `ρ'.U` and
`ρ'.V` (`ToP1`); so `ρ'` is an isomorphism iff both preimages are affine and
`ℤ_(p)[X] → Γ(𝒵, ρ'.U)`, `X ↦ f`, and `ℤ_(p)[X] → Γ(𝒵, ρ'.V)`, `X ↦ g`, are bijective (STANDARD:
a morphism is an isomorphism iff it is so over each member of an open cover of the target, and a
morphism to an affine scheme from an affine scheme is the `Spec` of its map on global sections). -/
def IsP1Coordinate {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    (ρ' : ToP1 𝒵.left) : Prop :=
  IsAffineOpen ρ'.U ∧ IsAffineOpen ρ'.V ∧
    Function.Bijective (eval₂RingHom (baseToSections 𝒵 ρ'.U) ρ'.f) ∧
    Function.Bijective (eval₂RingHom (baseToSections 𝒵 ρ'.V) ρ'.g)

/-- **Glue (d1), the coordinate factors through a finite map to `P¹_{ℤ_(p)}`** (route GR; not
proved here; strictly smaller than `ModelCoordinateResidue`: no residue clause). Given the smooth
model at `p > 324` and a triple with R1fp, R1hecke, R2fp, there are a scheme `𝒵` over `ℤ_(p)`, a
finite morphism `q : 𝒴 → 𝒵` over `ℤ_(p)` and an isomorphism `ρ' : 𝒵 ≅ P¹_{ℤ_(p)}` (by charts,
`IsP1Coordinate`) such that `ρ = ρ' ∘ q` has the R2-type clauses `CoordFibres` on `ℚ̄`-points.
Proof outline (docs/research/mcr-glue.md §3): `𝒵 = 𝒴/G'` for the group `G'` generated by the Hecke
automorphisms of `IsShimuraModel` (order prime to `p`); the quotient exists and is finite over
`𝒴` (SGA 1 Exp. V, 1.1 and 1.8; `𝒴` projective), is smooth over `ℤ_(p)` (tame: formation commutes
with base change, normal curves over perfect fields are smooth), its generic fibre is `P¹_ℚ` in
the coordinate `π` (R2fp), and the three CM sections over `0, ∞, −16/27` are pairwise disjoint
mod `p` (fixed loci of tame automorphisms are finite étale, Edixhoven 1995); a smooth proper
`ℤ_(p)`-curve with generic fibre `P¹_ℚ` and three pairwise disjoint sections is `P¹_{ℤ_(p)}` in the
coordinate taking the values `0, ∞, −16/27` on them. The leaves are listed in
docs/research/mcr-glue.md §3 (locators UNVERIFIED). -/
def QuotientP1Coordinate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∃ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵) (ρ' : ToP1 𝒵.left),
      IsFinite q.left ∧ IsP1Coordinate 𝒵 ρ' ∧ CoordFibres 𝒴 𝒜 (ρ'.comp q.left)

/-- **Glue (d2), residue fields at the generic points of the special fibre** (scheme theory;
STANDARD; not proved here). For `𝒴` smooth of relative dimension 1 over `ℤ_(p)` and a point `ξ`
whose stalk is a DVR with maximal ideal `(p)`, the residue field `κ(ξ)` is not algebraic over its
prime field `𝔽_p`. (Proof: `𝒪_ξ / p = κ(ξ)`, so `ξ` is a generic point of the special fibre
`𝒴_p`, which is smooth of relative dimension 1 over `𝔽_p`; if `κ(ξ)` were algebraic over `𝔽_p`, `ξ`
would be a closed point of the finite-type `𝔽_p`-scheme `𝒴_p` (a domain integral over a field is a
field), hence an isolated point of `𝒴_p`, which a smooth curve over a field does not have.) -/
def SpecialFibreTranscendence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ (ξ : 𝒴.left) (_ : IsDomain (𝒴.left.presheaf.stalk ξ)),
      IsDiscreteValuationRing (𝒴.left.presheaf.stalk ξ) →
      IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
        Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)} →
      ¬ Algebra.IsAlgebraic (⊥ : Subfield (IsLocalRing.ResidueField (𝒴.left.presheaf.stalk ξ)))
        (IsLocalRing.ResidueField (𝒴.left.presheaf.stalk ξ))

/-- **`ModelCoordinateResidue` from `QuotientP1Coordinate` and `SpecialFibreTranscendence`**
(compiled). `ρ = ρ' ∘ q`; at `ξ`, `κ(ξ)` is not algebraic over `𝔽_p`, so by
`transcendental_of_polyCharts` the point `q(ξ)` lies in the affine chart and the residue of `ρ` at
`ξ` is transcendental. -/
theorem modelCoordinateResidue_of_quotient (hQ : QuotientP1Coordinate)
    (hS : SpecialFibreTranscendence) : ModelCoordinateResidue := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨𝒵, q, ρ', hfin, ⟨hU, hV, hbU, hbV⟩, hCF⟩ := hQ p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  refine ⟨ρ'.comp q.left, hCF, fun ξ hdom hdvr hmax => ?_⟩
  have hna := hS p 𝒴 hM.2.1 ξ hdom hdvr hmax
  have := hfin
  exact transcendental_of_polyCharts q.left ρ' (pIdeal p).primeCompl _ _ hU hV hbU.2 hbV.2 ξ hna

end MCRGlue

#print axioms MCRGlue.residueField_isAlgebraic_of_affine
#print axioms MCRGlue.mem_bot_of_localization
#print axioms MCRGlue.eval_mem_algebraicClosure
#print axioms MCRGlue.residueField_isAlgebraic_of_integral
#print axioms MCRGlue.transcendental_of_polyCharts
#print axioms MCRGlue.modelCoordinateResidue_of_quotient

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue, part 3: `QuotientP1Coordinate` from leaves and three glue Props

The leaves are stated over genuine definitions: schemes over `ℤ_(p)`, automorphisms
(`CategoryTheory.Aut`), the SGA 1 notion of a quotient by a finite group (`IsGQuotient`),
isomorphisms onto `P¹` by charts (`IsP1Coordinate`, `IsP1CoordinateQ`), closures of points.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-! ## Definitions -/

/-- If `g ≫ q = q` then `q⁻¹ W ⊆ g⁻¹ (q⁻¹ W)`. -/
theorem preimage_le_of_comp_eq {X Z : Scheme.{0}} {g : X ⟶ X} {q : X ⟶ Z} (h : g ≫ q = q)
    (W : Z.Opens) : q ⁻¹ᵁ W ≤ g ⁻¹ᵁ (q ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, h]

/-- **Quotient of a scheme by a finite group of automorphisms** (SGA 1 Exp. V §1; a genuine
definition). `q : X → Z` is `G`-invariant and affine, and for every affine open `W ⊆ Z` the map
`Γ(Z, W) → Γ(X, q⁻¹W)` is injective with image the `G`-invariant sections; i.e. `q` is affine
and `𝒪_Z = (q_* 𝒪_X)^G`, which characterizes `X/G` up to unique isomorphism. -/
def IsGQuotient {X Z : Scheme.{0}} (G : Subgroup (Aut X)) (q : X ⟶ Z) : Prop :=
  ∃ hinv : ∀ g ∈ G, g.asIso.hom ≫ q = q,
    IsAffineHom q ∧
    ∀ W : Z.Opens, IsAffineOpen W →
      Function.Injective (q.app W) ∧
      Set.range (q.app W) = {s | ∀ (g : Aut X) (hg : g ∈ G),
        g.asIso.hom.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq (hinv g hg) W) s = s}

/-- The structure map `R → Γ(𝒵, W)` of a scheme `𝒵` over `Spec R`. -/
def baseToSectionsOver (R : CommRingCat.{0}) (𝒵 : Over (Spec R)) (W : 𝒵.left.Opens) :
    R →+* Γ(𝒵.left, W) :=
  (𝒵.left.presheaf.map (homOfLE le_top).op).hom.comp
    ((𝒵.hom.appTop).hom.comp (Scheme.ΓSpecIso R).inv.hom)

/-- **`σ : 𝒵 → P¹_ℚ` is an isomorphism** (by charts, as `IsP1Coordinate`, over `ℚ`). -/
def IsP1CoordinateQ (𝒵 : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 𝒵.left) : Prop :=
  IsAffineOpen σ.U ∧ IsAffineOpen σ.V ∧
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 σ.U) σ.f) ∧
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 σ.V) σ.g)

/-- The point of `X` underlying a `ℚ̄`-point. -/
def qbarPoint {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField Qbar X y).1

/-- **The fibre-preserving automorphisms of the model** (generators): automorphisms of `𝒴` over
`ℤ_(p)` that move every `ℚ̄`-point to a point whose QM pair is an `Aut(𝒪)`-twist of the original
(the automorphisms preserving the twist classes, i.e. the fibres of `CoordFibres`). The Hecke
automorphisms of `IsShimuraModel` (clauses 6-7) are among them. -/
def FibreAutSet {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : Set (Aut 𝒴.left) :=
  {g | g.asIso.hom ≫ 𝒴.hom = 𝒴.hom ∧
    ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.asIso.hom) P' →
        ∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (P.q.twist α) P'.q)}

/-- The group generated by the fibre-preserving automorphisms (`Gal(E/ℚ(X))` on the model). -/
def fibreAut {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : Subgroup (Aut 𝒴.left) :=
  Subgroup.closure (FibreAutSet 𝒴 𝒜)

/-- Every element of `fibreAut` is an automorphism over `ℤ_(p)`. -/
theorem fibreAut_over {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p))))
    (𝒜 : QMFamily 𝒴.left) : ∀ g ∈ fibreAut 𝒴 𝒜, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => exact Category.id_comp _
  | mul x y _ _ hx hy =>
    change (y.asIso.hom ≫ x.asIso.hom) ≫ 𝒴.hom = 𝒴.hom
    rw [Category.assoc, hx, hy]
  | inv x _ hx =>
    change x.asIso.inv ≫ 𝒴.hom = 𝒴.hom
    rw [← hx, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, hx]

/-! ## The leaves (published; locators UNVERIFIED: no network) -/

/-- **Leaf (L1): finite sets of points of a proper smooth curve over `ℤ_(p)` lie in an affine
open.** Each connected component of `𝒴` is integral and dominates `Spec ℤ_(p)` (flatness), and
there are finitely many (properness). A proper flat regular (here smooth) curve over a DVR is
projective (S. Lichtenbaum,
*Curves over discrete valuation rings*, Amer. J. Math. 90 (1968), Thm. 2.8; Q. Liu, *Algebraic
Geometry and Arithmetic Curves*, Thm. 8.3.16), and in a scheme projective over an affine scheme
every finite set of points lies in an affine open (EGA II 4.5.4; Liu Prop. 3.3.36). Locators
UNVERIFIED. -/
def ProperCurveAF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ s : Finset 𝒴.left, ∃ W : 𝒴.left.Opens, IsAffineOpen W ∧ ∀ x ∈ s, x ∈ W

/-- **Leaf (L2): quotients by finite groups exist** (SGA 1 Exp. V, Prop. 1.8 with Prop. 1.1 and
Cor. 1.5; locators UNVERIFIED). Let `X` be proper over `S = Spec ℤ_(p)` and `G` a finite group of
`S`-automorphisms of `X` such that every finite set of points (in particular every orbit) lies in
an affine open. Then the quotient `q : X → X/G` exists over `S` (`IsGQuotient`), and `q` is
integral (SGA 1 V 1.1); over affines `B` is of finite type over the Noetherian `ℤ_(p)` and
integral over `B^G`, so `B^G` is of finite type (Artin–Tate) and `B` is finite over `B^G`: `q`
is finite. The leaf only asserts the case of a
proper `X` over `ℤ_(p)`. -/
def FiniteQuotientExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))), IsProper 𝒴.hom →
    (∀ s : Finset 𝒴.left, ∃ W : 𝒴.left.Opens, IsAffineOpen W ∧ ∀ x ∈ s, x ∈ W) →
    ∀ G : Subgroup (Aut 𝒴.left), Finite G → (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) →
    ∃ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient G q.left ∧ IsFinite q.left

/-- **Leaf (L3): tame quotients of smooth proper curves over `ℤ_(p)` are smooth and proper.** If
`p ∤ |G|`, the formation of `X/G` commutes with every base change `S' → S` (the Reynolds operator
`|G|⁻¹ Σ g` splits `𝒪_X → (𝒪_X)^G`; SGA 1 Exp. V, Prop. 1.9; D. Mumford, *Abelian Varieties*,
§7, Thm. 3; locators UNVERIFIED), so the fibres of `X/G` are `X_s/G`, normal curves over the
perfect fields `𝔽_p` and `ℚ`, hence smooth; `X/G` is flat over `ℤ_(p)` (torsion-free), so smooth
over `ℤ_(p)` (EGA IV 17.5.1), and proper (the image of a proper scheme under the surjective `q`; separated because
`X ×_S X → Z ×_S Z` is integral and surjective and the preimage of `Δ_Z` is the union of the
graphs of the `g ∈ G`; of finite type by Artin–Tate). -/
def TameQuotientSmooth : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ G : Subgroup (Aut 𝒴.left), Finite G → ¬ p ∣ Nat.card G →
    (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) → IsGQuotient G q.left → IsFinite q.left →
    IsProper 𝒵.hom ∧ SmoothOfRelativeDimension 1 𝒵.hom

/-- **Leaf (L4): a smooth proper model of `P¹_ℚ` over `ℤ_(p)` is `P¹_{ℤ_(p)}`.** If `𝒵` is proper
and smooth of relative dimension 1 over `ℤ_(p)` with generic fibre isomorphic to `P¹_ℚ`, then
`𝒵 ≅ P¹_{ℤ_(p)}` (in some coordinate). (The special fibre is a smooth proper geometrically
connected curve of genus 0 (Zariski connectedness, constancy of the Euler characteristic in flat
proper families) with an `𝔽_p`-point (a `ℚ`-point extends to a section by properness), hence
`P¹_{𝔽_p}`; the degree-1 line bundle of the section and `H¹ = 0` give the isomorphism. Liu,
*Algebraic Geometry and Arithmetic Curves*, §8.3 and §10.1; locators UNVERIFIED; STANDARD.) -/
def SmoothModelOfP1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒵.hom → SmoothOfRelativeDimension 1 𝒵.hom →
    ∀ σ₀ : ToP1 (genFib 𝒵).left, IsP1CoordinateQ (genFib 𝒵) σ₀ →
    ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ'

/-- **Leaf (L5): fixed points of a tame automorphism have distinct reductions.** For `𝒴` proper
and smooth of relative dimension 1 over `ℤ_(p)` and an automorphism `σ` over `ℤ_(p)` of finite
order `n` with `p ∤ n`, the fixed scheme `𝒴^σ` is smooth over `ℤ_(p)` (B. Edixhoven, *Néron
models and tame ramification*, Compositio Math. 81 (1992), Prop. 3.4; locator UNVERIFIED). If `σ`
fixes only finitely many `ℚ̄`-points, `𝒴^σ` has no component of relative dimension 1, so it is
étale and proper, hence finite étale over `ℤ_(p)`, a disjoint union of spectra of semilocal
Dedekind rings each with a one-point generic fibre: two `σ`-fixed `ℚ̄`-points with distinct
underlying points have disjoint closures in `𝒴`. -/
def TameFixedPointsDisjoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ (σ : Aut 𝒴.left) (n : ℕ), σ.asIso.hom ≫ 𝒴.hom = 𝒴.hom → 0 < n → ¬ p ∣ n → σ ^ n = 1 →
    {y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | y ≫ σ.asIso.hom = y}.Finite →
    ∀ y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, y ≫ σ.asIso.hom = y → y' ≫ σ.asIso.hom = y' →
      qbarPoint y ≠ qbarPoint y' →
      Disjoint (closure ({qbarPoint y} : Set 𝒴.left)) (closure {qbarPoint y'})

/-- **Leaf (L6): tame inertia groups are cyclic.** For `𝒴` proper and smooth of relative
dimension 1 over `ℤ_(p)`, a finite group `H` of automorphisms over `ℤ_(p)` with `p ∤ |H|` whose
nontrivial elements fix only finitely many `ℚ̄`-points, and a point `w` fixed by every element of
`H` with trivial action on `κ(w)`, `H` is cyclic. (Faithfulness: an element trivial near `w` is trivial on the connected component
through `w`, which has infinitely many `ℚ̄`-points. At a closed point `w` of the special fibre,
`p ∈ 𝔪 ∖ 𝔪²` (smoothness); by Maschke `𝔪/𝔪² = ⟨p̄⟩ ⊕ T` with `T` a line on which `H` acts by a
character `χ : H → κ(w)^×`; `ker χ` acts unipotently on `gr 𝒪_w`, hence trivially (order prime to
`p`), hence is trivial; so `H ↪ κ(w)^×` is cyclic. This is the argument of J.-P. Serre, *Local
Fields*, Ch. IV §2, Cor. 1 of Prop. 7 (locator UNVERIFIED). At generic points `H` is trivial; at
closed points of the generic fibre the same argument works in characteristic 0.) -/
def TameInertiaCyclic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ H : Subgroup (Aut 𝒴.left), Finite H → ¬ p ∣ Nat.card H →
    (∀ g ∈ H, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) →
    (∀ g ∈ H, g ≠ 1 →
      {y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | y ≫ g.asIso.hom = y}.Finite) →
    ∀ w : 𝒴.left, (∀ g ∈ H, ∃ e : g.asIso.hom w = w,
      (𝒴.left.residueFieldCongr e).inv ≫ g.asIso.hom.residueFieldMap w = 𝟙 _) →
    IsCyclic H

/-! ## The glue (route GR; not proved) -/

/-- **Glue (A): the fibre-preserving group is finite of order prime to `p`.** For the smooth
model at `p > 324` and a triple with R1fp, R1hecke, R2fp. (Outline: `𝒴` is integral with function
field `E` (model-glue: `ModelIntegral`, `ModelFunctionField` from T5 and `CurveBijIso`); an
automorphism over `ℤ_(p)` is determined by its action on `E` (`𝒴` reduced, separated); a
fibre-preserving one fixes the germ `X` of the coordinate (`CoordFibres`, Möbius rigidity as in
`val_eq_of_same_fibres`), so `fibreAut ↪ Gal(E/ℚ(X))`, whose order `[E : ℚ(X)]` divides
`|Γ'| = 144 = 2⁴3²` (h-b1 M3; `CoverBranchData`), so is prime to every `p > 324`.) -/
def FibreAutTame : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    Finite (fibreAut 𝒴 𝒜) ∧ ¬ p ∣ Nat.card (fibreAut 𝒴 𝒜)

/-- **Glue (B): the generic fibre of the quotient is `P¹_ℚ`.** (Outline: the quotient commutes
with the flat base change `ℤ_(p) → ℚ` (localization commutes with invariants), so
`(𝒴/G)_ℚ = 𝒴_ℚ/G ≅ Y/G` (model-glue's comparison `g : 𝒴_ℚ ≅ Y`); `π` is `G`-invariant, so it
descends to `Y/G → P¹_ℚ`, which is bijective on `ℚ̄`-points (R2fp: the `π`-fibres are the
`G`-orbits, the transitivity coming from the Hecke clauses of R1hecke and `𝒪^× ↠ (𝒪/3𝒪)^×`), hence
an isomorphism of smooth proper curves (`CurveBijIso`).) -/
def GenericQuotientP1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
    ∃ σ₀ : ToP1 (genFib 𝒵).left, IsP1CoordinateQ (genFib 𝒵) σ₀

/-- **Glue (C), from Leaves L5 and L6: normalizing the coordinate by the CM sections.** Given the
quotient `q : 𝒴 → 𝒵` by `fibreAut`, with `𝒵` proper smooth and an isomorphism
`ρ'₀ : 𝒵 ≅ P¹_{ℤ_(p)}`, there is an isomorphism `ρ' : 𝒵 ≅ P¹_{ℤ_(p)}` such that `ρ' ∘ q` has the
R2-type clauses `CoordFibres`. (Outline: on the generic fibre `ρ'₀ = m ∘ π̄` for a Möbius `m`
(Glue B, both are isomorphisms `𝒵_ℚ ≅ P¹_ℚ`); the CM points `y_0, y_∞, y_c` of `𝒴` (from
`CMObjectsExist` and the leaf's surjectivity clause) have stabilizers in `fibreAut` of even orders
`4, 6, 2` (the orbifold indices); if the closures of two of their images in `𝒵` met, some point
`w` of `𝒴` would lie in the closures of `y_b` and `g y_{b'}`, its inertia group would contain both
stabilizers (they act trivially on the closures), be cyclic (L6), and its unique involution would
fix `y_b` and `g y_{b'}`, against L5. So the three sections `0, ∞, −16/27` of `P¹_ℚ` (in `π̄`)
extend to pairwise disjoint sections of `𝒵 ≅ P¹_{ℤ_(p)}`, i.e. `m ∈ PGL₂(ℤ_(p))` (`v_p(16/27) = 0`
for `p > 3`), and `ρ' := m⁻¹ ∘ ρ'₀` is again an isomorphism, equal to `π̄` on the generic fibre;
`CoordFibres` then follows from R2fp through the comparison `𝒴_ℚ ≅ Y`.) -/
def CoordinateNormalization : Prop :=
  TameFixedPointsDisjoint → TameInertiaCyclic →
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
      IsProper 𝒵.hom → SmoothOfRelativeDimension 1 𝒵.hom →
    ∀ ρ'₀ : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ'₀ →
    ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ' ∧ CoordFibres 𝒴 𝒜 (ρ'.comp q.left)

/-! ## The reduction (compiled) -/

/-- **`QuotientP1Coordinate` from the leaves L1-L6 and the glue A, B, C** (compiled plumbing:
L1 + L2 give the quotient by `fibreAut` (finite by A), L3 makes it smooth and proper, B and L4
make it `P¹_{ℤ_(p)}`, C normalizes the coordinate). -/
theorem quotientP1Coordinate_of_leaves (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (gA : FibreAutTame) (gB : GenericQuotientP1)
    (gC : CoordinateNormalization) : QuotientP1Coordinate := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨hfin, hnd⟩ := gA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hover := fibreAut_over 𝒴 𝒜
  obtain ⟨𝒵, q, hq, hqf⟩ :=
    hQE p 𝒴 hM.1 (hAF p 𝒴 hM.1 hM.2.1) (fibreAut 𝒴 𝒜) hfin hover
  obtain ⟨hZp, hZs⟩ := hTS p 𝒴 𝒵 q hM.1 hM.2.1 _ hfin hnd hover hq hqf
  obtain ⟨σ₀, hσ₀⟩ := gB p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf
  obtain ⟨ρ'₀, hρ'₀⟩ := hP1 p 𝒵 hZp hZs σ₀ hσ₀
  obtain ⟨ρ', hρ', hCF⟩ :=
    gC hFix hCyc p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf hZp hZs ρ'₀ hρ'₀
  exact ⟨𝒵, q, ρ', hqf, hρ', hCF⟩

/-- **`ModelCoordinateResidue` from the leaves L1-L6 and the glue A, B, C,
`SpecialFibreTranscendence`.** -/
theorem modelCoordinateResidue_of_leaves (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (gA : FibreAutTame) (gB : GenericQuotientP1)
    (gC : CoordinateNormalization) (hS : SpecialFibreTranscendence) : ModelCoordinateResidue :=
  modelCoordinateResidue_of_quotient
    (quotientP1Coordinate_of_leaves hAF hQE hTS hP1 hFix hCyc gA gB gC) hS

end MCRGlue

#print axioms MCRGlue.preimage_le_of_comp_eq
#print axioms MCRGlue.fibreAut_over
#print axioms MCRGlue.quotientP1Coordinate_of_leaves
#print axioms MCRGlue.modelCoordinateResidue_of_leaves

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue, part 4: `SpecialFibreTranscendence` is proved
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-- In characteristic `p`, if `K` is algebraic over its prime field, the image of any ring in `K`
is a field, so every kernel of a map to `K` is maximal. -/
theorem ker_isMaximal_of_isAlgebraic {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : Algebra.IsAlgebraic (⊥ : Subfield K) K) {A : Type*} [CommRing A] (ψ : A →+* K) :
    (RingHom.ker ψ).IsMaximal := by
  let S : Subalgebra (⊥ : Subfield K) K :=
    { ψ.range with
      algebraMap_mem' := fun c => by
        obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p K).1 c.2
        exact ⟨n, by rw [map_intCast]; exact hn⟩ }
  have hS : IsField S := Subalgebra.isField_of_algebraic S
  let _ := hS.toField
  let ψ' : A →+* S := ψ.codRestrict S (fun a => ⟨a, rfl⟩)
  have hsurj : Function.Surjective ψ' := by
    rintro ⟨s, a, rfl⟩
    exact ⟨a, rfl⟩
  have hk : RingHom.ker ψ' = RingHom.ker ψ := by
    ext a
    simp only [RingHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [← hk]
  exact RingHom.ker_isMaximal_of_surjective ψ' hsurj

/-- **Residue fields at points of a smooth curve over a local ring whose maximal ideal is `(p)`.**
If `R` is local with `𝔪_R = (p)`, `𝒴 → Spec R` is smooth of relative dimension 1 and `ξ ∈ 𝒴` has
`𝔪_ξ = (p)`, then `κ(ξ)` is not algebraic over `𝔽_p`. Otherwise `ξ` would be a closed point of an
affine chart (`ker_isMaximal_of_isAlgebraic`), so its point `ξ'` on the special fibre
`𝒴 ×_R κ_R` (smooth of relative dimension 1 over a field, Jacobson) would be closed, with stalk
`𝒪_ξ / p = κ(ξ)` (closed immersion: surjective on stalks), of dimension 0, against
`smoothStalkDimOne` (kernel: closed points of smooth curves over a field have 1-dimensional
stalks). -/
theorem not_isAlgebraic_residueField_of_smooth {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ}
    [hp : Fact p.Prime] (hR : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)})
    (𝒴 : Over (Spec (CommRingCat.of R))) (hsm : SmoothOfRelativeDimension 1 𝒴.hom)
    (ξ : 𝒴.left)
    (hmax : IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
      Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)}) :
    ¬ Algebra.IsAlgebraic (⊥ : Subfield (𝒴.left.residueField ξ)) (𝒴.left.residueField ξ) := by
  intro halg
  have hpξ : (p : 𝒴.left.presheaf.stalk ξ) ∈ IsLocalRing.maximalIdeal _ := by rw [hmax]; exact Ideal.subset_span rfl
  have hpκ : (p : 𝒴.left.residueField ξ) = 0 := by
    have : IsLocalRing.residue (𝒴.left.presheaf.stalk ξ) (p : 𝒴.left.presheaf.stalk ξ) =
        (p : 𝒴.left.residueField ξ) := map_natCast _ _
    rw [← this]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hpξ
  have hcharξ : CharP (𝒴.left.residueField ξ) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpκ
  -- an affine chart
  obtain ⟨_, ⟨V, hV, rfl⟩, hξV, -⟩ :=
    𝒴.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ξ) isOpen_univ
  have hV' : IsAffineOpen V := hV
  set ev := 𝒴.left.evaluation V ξ hξV
  have hmaxker : (RingHom.ker ev.hom).IsMaximal := ker_isMaximal_of_isAlgebraic p halg ev.hom
  set 𝔮 := hV'.primeIdealOf ⟨ξ, hξV⟩
  have hfs : hV'.fromSpec 𝔮 = ξ := hV'.fromSpec_primeIdealOf ⟨ξ, hξV⟩
  have hker : 𝔮.asIdeal = RingHom.ker ev.hom := by
    ext a
    rw [RingHom.mem_ker]
    have h1 : 𝔮 ∈ PrimeSpectrum.basicOpen a ↔ ξ ∈ 𝒴.left.basicOpen a := by
      have : 𝔮 ∈ hV'.fromSpec ⁻¹ᵁ 𝒴.left.basicOpen a ↔ ξ ∈ 𝒴.left.basicOpen a := by
        rw [← hfs]; rfl
      rwa [hV'.fromSpec_preimage_basicOpen] at this
    have h2 : ev.hom a = 0 ↔ ξ ∉ 𝒴.left.basicOpen a :=
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen 𝒴.left ξ hξV a
    rw [h2, ← h1, PrimeSpectrum.mem_basicOpen, not_not]
  -- `{ξ}` is locally closed in `X`
  have hlc : IsLocallyClosed ({ξ} : Set 𝒴.left) := by
    have hcl : IsClosed ({𝔮} : Set (Spec Γ(𝒴.left, V))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal 𝔮).2 (hker ▸ hmaxker)
    have := hcl.isLocallyClosed.image hV'.fromSpec.isOpenEmbedding.isInducing
      (by rw [hV'.range_fromSpec]; exact V.isOpen.isLocallyClosed)
    convert this using 1
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro rfl; exact ⟨𝔮, rfl, hfs⟩
    · rintro ⟨a, rfl, rfl⟩; exact hfs
  -- the special fibre
  set K := IsLocalRing.ResidueField R
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hι : ∀ s, ι s = IsLocalRing.closedPoint R := fun s =>
    IsLocalRing.PrimeSpectrum.comap_residue _ s
  have hfξ : 𝒴.hom ξ = IsLocalRing.closedPoint R := by
    have hnot : ξ ∉ 𝒴.left.basicOpen (𝒴.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (p : R))) := by
      rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen 𝒴.left (U := ⊤) ξ trivial]
      simp only [map_natCast]
      exact hpκ
    have hmem : (p : R) ∈ (𝒴.hom ξ).asIdeal := by
      rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hnot
      by_contra h
      exact hnot h
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal (𝒴.hom ξ).isPrime.ne_top) ?_
    show IsLocalRing.maximalIdeal R ≤ _
    rw [hR, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  obtain ⟨ξ', hξ'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒴.hom) (g := ι) ξ
    (IsLocalRing.closedPoint K) (by rw [hfξ, hι (IsLocalRing.closedPoint K)])
  have : IsClosedImmersion ι := IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hsm' : SmoothOfRelativeDimension 1 𝒴.hom := hsm
  have hsmp : SmoothOfRelativeDimension 1 (pullback.snd 𝒴.hom ι) := inferInstance
  have : Smooth (pullback.snd 𝒴.hom ι) := SmoothOfRelativeDimension.smooth 1 _
  have hJ : JacobsonSpace (pullback (C := Scheme) 𝒴.hom ι) := LocallyOfFiniteType.jacobsonSpace (pullback.snd 𝒴.hom ι)
  have hinj : Function.Injective (pullback.fst 𝒴.hom ι) :=
    (pullback.fst 𝒴.hom ι).isClosedEmbedding.injective
  have hpre : (pullback.fst 𝒴.hom ι) ⁻¹' {ξ} = {ξ'} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact hinj (h.trans hξ'1.symm)
    · rintro rfl; exact hξ'1
  have hcl' : IsClosed ({ξ'} : Set (pullback (C := Scheme) 𝒴.hom ι)) := by
    have := hlc.preimage (pullback.fst 𝒴.hom ι).continuous
    rw [hpre] at this
    exact isClosed_singleton_of_isLocallyClosed_singleton this
  have hd1 := LeafQM.AV.Pin.smoothStalkDimOne K (pullback (C := Scheme) 𝒴.hom ι) (pullback.snd 𝒴.hom ι) hsmp ξ' hcl'
  subst hξ'1
  have hsurj := (pullback.fst 𝒴.hom ι).stalkMap_surjective ξ'
  have hpK : (p : K) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff, hR]
    exact Ideal.subset_span rfl
  have hp0 : (p : (pullback (C := Scheme) 𝒴.hom ι).presheaf.stalk ξ') = 0 := by
    have h := map_natCast ((pullback (C := Scheme) 𝒴.hom ι).presheaf.germ ⊤ ξ' trivial).hom p
    have h2 := map_natCast ((pullback.snd 𝒴.hom ι).appTop).hom p
    have h3 := map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom p
    rw [← h, ← h2, ← h3, hpK]
    simp
  have hfield : IsField ((pullback (C := Scheme) 𝒴.hom ι).presheaf.stalk ξ') := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {s} hs => ?_⟩
    obtain ⟨t, rfl⟩ := hsurj s
    by_cases ht : t ∈ IsLocalRing.maximalIdeal _
    · rw [hmax, Ideal.mem_span_singleton'] at ht
      obtain ⟨u, rfl⟩ := ht
      exact absurd (by rw [map_mul, map_natCast, hp0, mul_zero]) hs
    · have hu : IsUnit t := by
        by_contra h
        exact ht ((IsLocalRing.mem_maximalIdeal _).2 h)
      exact (hu.map ((pullback.fst 𝒴.hom ι).stalkMap ξ').hom).exists_right_inv
  rw [ringKrullDim_eq_zero_of_isField hfield] at hd1
  exact absurd hd1 (by decide)


/-- **`SpecialFibreTranscendence` holds** (compiled; the DVR hypothesis is not needed). -/
theorem specialFibreTranscendence : SpecialFibreTranscendence := by
  intro p _ 𝒴 hsm ξ _ _ hmax
  exact not_isAlgebraic_residueField_of_smooth (maximalIdeal_Zloc p) 𝒴 hsm ξ hmax

/-- **`ModelCoordinateResidue` from `QuotientP1Coordinate` alone** (compiled). -/
theorem modelCoordinateResidue_of_quotient' (hQ : QuotientP1Coordinate) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_of_quotient hQ specialFibreTranscendence

/-- **`ModelCoordinateResidue` from the leaves L1-L6 and the glue A, B, C** (compiled). -/
theorem modelCoordinateResidue_of_leaves' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (gA : FibreAutTame) (gB : GenericQuotientP1)
    (gC : CoordinateNormalization) : ModelCoordinateResidue :=
  modelCoordinateResidue_of_leaves hAF hQE hTS hP1 hFix hCyc gA gB gC specialFibreTranscendence

end MCRGlue

#print axioms MCRGlue.ker_isMaximal_of_isAlgebraic
#print axioms MCRGlue.not_isAlgebraic_residueField_of_smooth
#print axioms MCRGlue.specialFibreTranscendence
#print axioms MCRGlue.modelCoordinateResidue_of_quotient'
#print axioms MCRGlue.modelCoordinateResidue_of_leaves'

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue, part 5: a sanity check of `IsGQuotient`, and a split of glue C
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-- **Sanity check: `IsGQuotient` is satisfiable** — the identity is the quotient by the trivial
group (so the definition used by Leaves L2, L3 is not vacuous or contradictory in this case). -/
theorem isGQuotient_bot_id (X : Scheme.{0}) : IsGQuotient (⊥ : Subgroup (Aut X)) (𝟙 X) := by
  have hinv : ∀ g ∈ (⊥ : Subgroup (Aut X)), g.asIso.hom ≫ 𝟙 X = 𝟙 X := by
    intro g hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    rfl
  refine ⟨hinv, inferInstance, fun W _ => ⟨fun a b h => h, ?_⟩⟩
  ext s
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, rfl⟩ g hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    show (X.presheaf.map (𝟙 (Opposite.op W))) t = t
    rw [CategoryTheory.Functor.map_id]
    rfl
  · intro _
    exact ⟨s, rfl⟩

/-- **Glue (C1), from Leaves L5 and L6: the CM sections of the quotient are disjoint.** For the
quotient `q : 𝒴 → 𝒵` by `fibreAut` and two `ℚ̄`-points of `𝒴` with CM by two different ones of
`ℤ[i], ℤ[ζ₃], ℤ[√−6]`, the closures in `𝒵` of their images are disjoint. (Outline in
`CoordinateNormalization`: a common point of the closures lifts to a point `w` of `𝒴` in the
closures of `y` and `g y'`; the inertia group at `w` contains the stabilizers of `y` and `g y'`
(even orders 4, 6, 2) and is cyclic (L6), so its involution fixes `y` and `g y'`, whose closures
are then disjoint by L5.) -/
def CMSectionsDisjoint : Prop :=
  TameFixedPointsDisjoint → TameInertiaCyclic →
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
    ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM3 P'.q) ∨ (HasCM4 P.q ∧ HasCM24 P'.q) ∨ (HasCM3 P.q ∧ HasCM24 P'.q)) →
      Disjoint (closure ({q.left (qbarPoint y)} : Set 𝒵.left)) (closure {q.left (qbarPoint y')})

/-- **Glue (C2): the coordinate from three disjoint sections** (geometry of `P¹_{ℤ_(p)}` and the
generic-fibre comparison; no new literature). Given the quotient `q : 𝒴 → 𝒵` by `fibreAut`, with
`𝒵` proper smooth, an isomorphism `ρ'₀ : 𝒵 ≅ P¹_{ℤ_(p)}`, and the CM sections pairwise disjoint (the
conclusion of C1), there is an isomorphism `ρ' : 𝒵 ≅ P¹_{ℤ_(p)}` with `CoordFibres` for `ρ' ∘ q`.
(Outline: `ρ'₀ = m ∘ π̄` on the generic fibre for a Möbius `m` (Glue B: both are isomorphisms
`𝒵_ℚ ≅ P¹_ℚ`); `m(0), m(∞), m(−16/27)` have pairwise distinct reductions, so `m ∈ PGL₂(ℤ_(p))`;
`ρ' := m⁻¹ ∘ ρ'₀`; `CoordFibres` from R2fp through `𝒴_ℚ ≅ Y`.) -/
def CoordinateFromSections : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
      IsProper 𝒵.hom → SmoothOfRelativeDimension 1 𝒵.hom →
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM3 P'.q) ∨ (HasCM4 P.q ∧ HasCM24 P'.q) ∨ (HasCM3 P.q ∧ HasCM24 P'.q)) →
      Disjoint (closure ({q.left (qbarPoint y)} : Set 𝒵.left)) (closure {q.left (qbarPoint y')})) →
    ∀ ρ'₀ : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ'₀ →
    ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ' ∧ CoordFibres 𝒴 𝒜 (ρ'.comp q.left)

/-- **`CoordinateNormalization` from C1 and C2** (compiled plumbing). -/
theorem coordinateNormalization_of (h1 : CMSectionsDisjoint) (h2 : CoordinateFromSections) :
    CoordinateNormalization := by
  intro hFix hCyc p _ hp 𝒴 𝒜 hM hCM Y Φ π h1' hh h2' 𝒵 q hq hqf hZp hZs ρ'₀ hρ'₀
  exact h2 p hp 𝒴 𝒜 hM hCM Y Φ π h1' hh h2' 𝒵 q hq hqf hZp hZs
    (h1 hFix hCyc p hp 𝒴 𝒜 hM hCM Y Φ π h1' hh h2' 𝒵 q hq hqf) ρ'₀ hρ'₀

/-- **`ModelCoordinateResidue` from the leaves L1-L6 and the glue A, B, C1, C2** (compiled). -/
theorem modelCoordinateResidue_of_leaves'' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (gA : FibreAutTame) (gB : GenericQuotientP1)
    (gC1 : CMSectionsDisjoint) (gC2 : CoordinateFromSections) : ModelCoordinateResidue :=
  modelCoordinateResidue_of_leaves' hAF hQE hTS hP1 hFix hCyc gA gB
    (coordinateNormalization_of gC1 gC2)

end MCRGlue

#print axioms MCRGlue.isGQuotient_bot_id
#print axioms MCRGlue.coordinateNormalization_of
#print axioms MCRGlue.modelCoordinateResidue_of_leaves''

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-glue, part 6: sanity check — `fibreAut` contains the Hecke automorphisms
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue

/-- An isomorphism of level-3 objects is an isomorphism of their QM pairs. -/
def qmIsoOfIso {K : Type} [Field K] {P Q : QML3 K} (f : P.Iso Q) : QMIso P.q Q.q where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant

/-- The automorphism of `𝒴.left` underlying an automorphism of `𝒴` over `ℤ_(p)`. -/
def autOfOverIso {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    (g : 𝒴 ≅ 𝒴) : Aut 𝒴.left :=
  Aut.of ((Over.forget _).mapIso g)

/-- **Sanity check: `fibreAut` contains automorphisms inducing every Hecke operation** (`twist α`
and `rightMul u`, clauses 6-7 of `IsShimuraModel`), so the quotient by `fibreAut` is at least as
coarse as the quotient by `Γ'`. -/
theorem hecke_mem_fibreAut {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜) :
    (∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g ∈ fibreAut 𝒴 𝒜,
      ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.asIso.hom) P' →
          M3.mk P' = M3.twist α (M3.mk P)) ∧
    (∀ u : (LeafQM.O)ˣ, ∃ g ∈ fibreAut 𝒴 𝒜,
      ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
        IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ g.asIso.hom) P' →
          M3.mk P' = M3.rightMul u (M3.mk P)) := by
  obtain ⟨-, -, -, -, -, htw, hru, -⟩ := hM
  constructor
  · intro α
    obtain ⟨g, hg⟩ := htw α
    refine ⟨autOfOverIso g, Subgroup.subset_closure ⟨Over.w g.hom, fun y P P' h1 h2 => ?_⟩, hg⟩
    have h : M3.mk P' = M3.mk (P.twist α) := by rw [← M3.twist_mk]; exact hg y P P' h1 h2
    obtain ⟨f⟩ := Quotient.exact (s := isoSetoid Qbar) h
    exact ⟨α, ⟨(qmIsoOfIso f).symm⟩⟩
  · intro u
    obtain ⟨g, hg⟩ := hru u
    refine ⟨autOfOverIso g, Subgroup.subset_closure ⟨Over.w g.hom, fun y P P' h1 h2 => ?_⟩, hg⟩
    have h : M3.mk P' = M3.mk (P.rightMul u) := hg y P P' h1 h2
    obtain ⟨f⟩ := Quotient.exact (s := isoSetoid Qbar) h
    let e : QMIso P.q P'.q := (qmIsoOfIso f).symm
    let e' : QMIso (P.q.twist (RingEquiv.refl LeafQM.O)) P'.q :=
      { φ := e.φ
        ψ := e.ψ
        left := e.left
        right := e.right
        equivariant := e.equivariant }
    exact ⟨RingEquiv.refl _, ⟨e'⟩⟩

end MCRGlue

#print axioms MCRGlue.hecke_mem_fibreAut

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 1: `𝒪^× ↠ (𝒪/3𝒪)^×` and the transitivity of the Hecke automorphisms on twist
classes
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue

/-! ## Units of `𝒪` modulo 3 (a finite computation) -/

/-- The reduced norm of `ofInt n` (an integer form). -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, mulCoord]
  ring

/-- **The unit table** (computed by `py/units.py`): every class of `(ℤ/3)⁴` of nonzero norm mod 3
contains a unit `ofInt n` of `𝒪` (inverse `ofInt m`). -/
theorem unit_table : ∀ a b c d : ZMod 3,
    a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    ∃ n m : Fin 4 → ℤ, mulCoord n m = ![1, 0, 0, 0] ∧ mulCoord m n = ![1, 0, 0, 0] ∧
      ((n 0 : ℤ) : ZMod 3) = a ∧ ((n 1 : ℤ) : ZMod 3) = b ∧ ((n 2 : ℤ) : ZMod 3) = c ∧
      ((n 3 : ℤ) : ZMod 3) = d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, 0, 0, -2], ![-3, 0, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 0, 0, 2], ![-3, 0, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 0], ![1, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 1], ![-1, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, -1], ![-1, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 0], ![-1, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 1], ![1, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, -1], ![1, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -2, 0, 0], ![-3, 2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, -2, 0, 2], ![-3, 2, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, 0], ![-1, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 1, 1, 1], ![-2, -1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, -1], ![-1, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, 0], ![1, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, 1, -1, 1], ![2, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, -1], ![1, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, 0], ![-3, -2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, -2], ![-3, -2, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![0, -1, 1, 0], ![-1, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, 1, 1], ![-1, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -1, 1, -1], ![-2, 1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 0], ![1, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 1], ![1, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, -1, -1, -1], ![2, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 0], ![1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 1], ![-1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, -1], ![-1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 0, 1, 1], ![2, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 1, -1], ![2, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 0], ![0, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 1], ![0, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, -1], ![0, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, 0], ![-1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -3, 1], ![-2, -1, 3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, -1], ![-1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 1, 0], ![2, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 1, 1, -1], ![2, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, 0], ![0, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, 1, -1, 1], ![-3, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, -1], ![0, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 0], ![-1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 1], ![-1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -3, -1], ![-2, 1, 3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 0], ![2, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 1], ![2, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, -1, -1, 0], ![0, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -1, 1], ![0, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, -1, -1, -1], ![-3, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 0], ![-1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 1], ![1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, -1], ![1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 0], ![0, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 1], ![0, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, -1], ![0, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 0, -1, 1], ![-2, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, -1, -1], ![-2, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, 0], ![1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 3, 1], ![2, -1, -3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, -1], ![1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, 0], ![0, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -2, 1], ![-3, -1, 2, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, -1], ![0, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -1, 0], ![-2, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 1, -1, -1], ![-2, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 0], ![1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 1], ![1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 3, -1], ![2, 1, -3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 0], ![0, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 1], ![0, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -2, -1], ![-3, 1, 2, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 0], ![-2, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 1], ![-2, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim

theorem nrdZ_mod3 (nc : Fin 4 → ℤ) :
    ((nrdZ (fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i) : ℤ) : ZMod 3) = 1 := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  simp [nrdZ, h3]

/-- **`𝒪^× ↠ (𝒪/3𝒪)^×`**: an element of `𝒪` invertible modulo `3𝒪` is congruent modulo `3𝒪` to a
unit of `𝒪` (the unit table). -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ c : O, (u : O) - u₀ = 3 * c := by
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨c, hc⟩ := h
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have hcB : (v₀ : B) * u₀ - 1 = 3 * c := by
    have := congrArg Subtype.val hc
    simpa [h33] using this
  have key : mulCoord nv nu = fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i := by
    have e : ofInt (mulCoord nv nu) - ofInt ![1, 0, 0, 0] = ofInt (fun i => 3 * nc i) := by
      rw [← ofInt_mul, ofInt_one, ← AV.three_mul_ofInt, ← hnu, ← hnv, ← hnc, hcB]
    rw [AV.ofInt_sub] at e
    have e2 := AV.ofInt_injective e
    funext i
    have := congrFun e2 i
    simp only [Pi.sub_apply] at this
    omega
  have hN : ((nrdZ nu : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    have e := nrdZ_mul nv nu
    rw [key] at e
    have e3 := congrArg (fun z : ℤ => (z : ZMod 3)) e
    simp only [nrdZ_mod3, Int.cast_mul, h0, mul_zero] at e3
    exact one_ne_zero e3
  have hN' : ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 ≠ 0 := by
    have : ((nrdZ nu : ℤ) : ZMod 3) = ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 := by simp [nrdZ]
    rwa [← this]
  obtain ⟨n, m, hnm, hmn, h0, h1, h2, h3⟩ := unit_table _ _ _ _ hN'
  have hdiv : ∀ i, (3 : ℤ) ∣ n i - nu i := by
    intro i
    have hi : ((nu i : ℤ) : ZMod 3) = ((n i : ℤ) : ZMod 3) := by
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).1 hi
  choose k hk using hdiv
  let u : Oˣ :=
    { val := ⟨ofInt n, ⟨n, rfl⟩⟩
      inv := ⟨ofInt m, ⟨m, rfl⟩⟩
      val_inv := by
        apply Subtype.ext
        change ofInt n * ofInt m = 1
        rw [ofInt_mul, hnm, ofInt_one]
      inv_val := by
        apply Subtype.ext
        change ofInt m * ofInt n = 1
        rw [ofInt_mul, hmn, ofInt_one] }
  refine ⟨u, ⟨ofInt k, ⟨k, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ofInt n - (u₀ : B) = ((3 : O) : B) * ofInt k
  rw [hnu, h33, AV.ofInt_sub, AV.three_mul_ofInt]
  congr 1
  funext i
  simp [hk i]

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 2: twist classes are the `fibreAut`-orbits on `ℚ̄`-points
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

variable {K : Type} [Field K]

/-- Twist-equivalence of level-3 objects: their QM pairs are `Aut(𝒪)`-twists of each other (the
relation of `CoordFibres`). -/
def TwistEq (P P' : QML3 K) : Prop := ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) P'.q)

/-- A QM isomorphism `ι ∘ γ ≅ ι` when `γ` is the identity pointwise. -/
def twistIdIso {A : AbVar K} (q : QMStr A) (γ : O ≃+* O) (hγ : ∀ a, γ a = a) :
    QMIso (q.twist γ) q where
  φ := 1
  ψ := 1
  left := (QMIso.refl q).left
  right := (QMIso.refl q).right
  equivariant a := by
    change (q.iota (γ a)).hom ≫ _ = _ ≫ (q.iota a).hom
    rw [hγ a]
    exact (QMIso.refl q).equivariant a

/-- Twisting a QM isomorphism. -/
def twistIso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') (β : O ≃+* O) :
    QMIso (q.twist β) (q'.twist β) where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant a := f.equivariant (β a)

/-- `(ι ∘ α) ∘ β = ι ∘ (α ∘ β)`. -/
def twistTwistIso {A : AbVar K} (q : QMStr A) (α β : O ≃+* O) :
    QMIso (q.twist (β.trans α)) ((q.twist α).twist β) where
  φ := 1
  ψ := 1
  left := (QMIso.refl q).left
  right := (QMIso.refl q).right
  equivariant a := (QMIso.refl ((q.twist α).twist β)).equivariant a

theorem twistEq_of_qmIso {P P' : QML3 K} (f : QMIso P.q P'.q) : TwistEq P P' :=
  ⟨RingEquiv.refl O, ⟨(twistIdIso P.q _ fun _ => rfl).trans f⟩⟩

theorem twistEq_of_iso {P P' : QML3 K} (f : P.Iso P') : TwistEq P P' :=
  twistEq_of_qmIso (qmIsoOfIso f)

theorem TwistEq.trans' {P R S : QML3 K} (h1 : TwistEq P R) (h2 : TwistEq R S) : TwistEq P S := by
  obtain ⟨α, ⟨f⟩⟩ := h1
  obtain ⟨β, ⟨g⟩⟩ := h2
  exact ⟨β.trans α, ⟨((twistTwistIso P.q α β).trans (twistIso f β)).trans g⟩⟩

theorem TwistEq.symm' {P R : QML3 K} (h : TwistEq P R) : TwistEq R P := by
  obtain ⟨α, ⟨f⟩⟩ := h
  refine ⟨α.symm, ⟨(twistIso f.symm α.symm).trans ?_⟩⟩
  exact ((twistTwistIso P.q α α.symm).symm).trans
    (twistIdIso P.q _ fun a => RingEquiv.apply_symm_apply α a)

/-- **Orbits lie in twist classes**: if fibres at a `ℚ̄`-point are unique up to isomorphism, every
element of `fibreAut` moves a point within its twist class. -/
theorem twistEq_of_mem_fibreAut {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜)
    (huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P')
    {h : Aut 𝒴.left} (hh : h ∈ fibreAut 𝒴 𝒜) :
    ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 (y ≫ h.asIso.hom) P' → TwistEq P P' := by
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one =>
    intro y P P' hP hP'
    have hP'' : IsFibreOf 𝒜 y P' := by simpa using hP'
    obtain ⟨f⟩ := Quotient.exact (s := isoSetoid Qbar) (huniq y P P' hP hP'')
    exact twistEq_of_iso f
  | mul x z _ _ hx hz =>
    intro y P P' hP hP'
    obtain ⟨R, hR⟩ := hM.2.2.1 Qbar (y ≫ z.asIso.hom)
    have hP2 : IsFibreOf 𝒜 ((y ≫ z.asIso.hom) ≫ x.asIso.hom) P' := by
      simpa [Category.assoc] using hP'
    exact (hz y P R hP hR).trans' (hx _ R P' hR hP2)
  | inv x _ hx =>
    intro y P P' hP hP'
    have hP2 : IsFibreOf 𝒜 ((y ≫ x⁻¹.asIso.hom) ≫ x.asIso.hom) P := by
      simpa [Category.assoc] using hP
    exact (hx _ P' P hP' hP2).symm'

/-- **Twist classes lie in orbits** (from the Hecke clauses of `IsShimuraModel`, the level torsor
`Level3.torsor` (needs the kernel's textbook leaf `TorsionStructure`, T5) and
`𝒪^× ↠ (𝒪/3𝒪)^×` (`exists_unit_congr`, proved)). -/
theorem mem_orbit_of_twistEq (hT : ObjBridge.TorsionStructure) {p : ℕ} [Fact p.Prime]
    {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜)
    (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar)
    (hP : IsFibreOf 𝒜 y P) (hP' : IsFibreOf 𝒜 y' P') (hTE : TwistEq P P') :
    ∃ h ∈ fibreAut 𝒴 𝒜, y' = y ≫ h.asIso.hom := by
  obtain ⟨α, ⟨f⟩⟩ := hTE
  obtain ⟨htw, hru⟩ := hecke_mem_fibreAut hM
  obtain ⟨g1, hg1G, hg1⟩ := htw α
  obtain ⟨P1, hP1⟩ := hM.2.2.1 Qbar (y ≫ g1.asIso.hom)
  have e1 : M3.mk P1 = M3.mk (P.twist α) := by rw [← M3.twist_mk]; exact hg1 y P P1 hP hP1
  obtain ⟨i1⟩ := Quotient.exact (s := isoSetoid Qbar) e1
  let f1 : QMIso P1.q P'.q := (qmIsoOfIso i1).trans f
  let e' : Level3 P1.q := transportLevel f1.symm P'.e
  have hiso : P'.Iso ⟨P1.A, P1.surface, P1.q, e'⟩ := QML3.isoTransport P' P1.surface f1.symm
  obtain ⟨u₀, v₀, hvu, hlin⟩ := Level3.torsor hT P1 e'
  obtain ⟨u, c, hc⟩ := exists_unit_congr u₀ v₀ hvu
  have heq : P1.rightMul u = ⟨P1.A, P1.surface, P1.q, e'⟩ := by
    simp only [QML3.rightMul, QML3.mk.injEq, heq_eq_eq, true_and]
    apply Level3.ext'
    refine DFunLike.ext _ _ fun a => ?_
    change P1.e.eta (a * u) = e'.eta a
    rw [hlin a, P1.e.eq_iff]
    refine ⟨a * c, ?_⟩
    calc a * (u : O) - a * u₀ = a * ((u : O) - u₀) := by noncomm_ring
      _ = a * (3 * c) := by rw [hc]
      _ = 3 * (a * c) := by noncomm_ring
  obtain ⟨g2, hg2G, hg2⟩ := hru u
  obtain ⟨P2, hP2⟩ := hM.2.2.1 Qbar ((y ≫ g1.asIso.hom) ≫ g2.asIso.hom)
  have e2 : M3.mk P2 = M3.mk P' := by
    rw [hg2 _ P1 P2 hP1 hP2]
    change M3.mk (P1.rightMul u) = M3.mk P'
    rw [heq]
    exact Quotient.sound ⟨hiso.symm⟩
  have hy := hM.2.2.2.1 _ y' P2 P' hP2 hP' e2
  refine ⟨g2 * g1, Subgroup.mul_mem _ hg2G hg1G, ?_⟩
  rw [← hy]
  simp [Category.assoc]

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 3: `ℚ̄`-points of a quotient by a finite group are the orbits

Commutative algebra (`exists_comp_smul_eq`: two ring maps `B → K` to a field that agree on
`A = B^G` differ by an element of `G`; from Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`
and `Ideal.Quotient.stabilizerHom_surjective`), then the scheme version for the SGA 1 quotient
`IsGQuotient`: the action of `G` on the sections over `q⁻¹ W`, `W ⊆ Z` affine, is a
`MulSemiringAction` with invariants `Γ(Z, W)`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits MCRGlue

/-- Values of two ring maps agreeing on invariants differ by an element of the group. -/
theorem exists_root_smul {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] (χ χ' : B →+* K)
    (hχ : χ.comp (algebraMap A B) = χ'.comp (algebraMap A B)) (b : B) :
    ∃ k : G, χ' b = χ (k • b) := by
  obtain ⟨P, hP0⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
  have hP : P.map (algebraMap A B) = MulSemiringAction.charpoly G b := hP0
  have h1 : P.eval₂ (χ'.comp (algebraMap A B)) (χ' b) = 0 := by
    rw [← Polynomial.hom_eval₂, ← Polynomial.eval_map, hP, MulSemiringAction.eval_charpoly,
      map_zero]
  rw [← hχ, ← Polynomial.eval_map, ← Polynomial.map_map, hP, MulSemiringAction.charpoly_eq,
    Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
  obtain ⟨k, -, hk⟩ := h1
  refine ⟨k, ?_⟩
  simpa [sub_eq_zero] using hk

theorem exists_comp_smul_eq {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] (φ φ' : B →+* K)
    (h : φ.comp (algebraMap A B) = φ'.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, φ' b = φ (g • b) := by
  classical
  cases nonempty_fintype G
  set Q := RingHom.ker φ with hQdef
  set Q' := RingHom.ker φ' with hQ'def
  have : Q.IsPrime := RingHom.ker_isPrime φ
  have : Q'.IsPrime := RingHom.ker_isPrime φ'
  have hunder : Q.under A = Q'.under A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, Q, Q', RingHom.mem_ker]
    rw [← RingHom.comp_apply, h, RingHom.comp_apply]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q Q' hunder
  let ψ : B →+* K := φ'.comp (MulSemiringAction.toRingHom G B g)
  have hψ : ∀ b, ψ b = φ' (g • b) := fun _ => rfl
  have hkerψ : ∀ b, ψ b = 0 ↔ φ b = 0 := by
    intro b
    rw [hψ]
    change g • b ∈ Q' ↔ b ∈ Q
    rw [hg, Ideal.smul_mem_pointwise_smul_iff]
  have hψA : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B) := by
    ext a
    change φ' (g • algebraMap A B a) = φ (algebraMap A B a)
    rw [smul_algebraMap]
    exact (congrArg (fun f : A →+* K => f a) h).symm
  set P := Q.under A
  have : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* K := Ideal.Quotient.lift Q φ (fun b hb => hb)
  let ψb : B ⧸ Q →+* K := Ideal.Quotient.lift Q ψ (fun b hb => (hkerψ b).2 hb)
  have hφb : Function.Injective φb :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun b hb => hb)
  have hψb : Function.Injective ψb :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun b hb => (hkerψ b).1 hb)
  have hrange1 : ∀ x : B ⧸ Q, ∃ y : B ⧸ Q, ψb x = φb y := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨k, hk⟩ := exists_root_smul G φ ψ hψA.symm b
    exact ⟨Ideal.Quotient.mk Q (k • b), hk⟩
  have hrange2 : ∀ y : B ⧸ Q, ∃ x : B ⧸ Q, φb y = ψb x := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨k, hk⟩ := exists_root_smul G ψ φ hψA b
    exact ⟨Ideal.Quotient.mk Q (k • b), hk⟩
  choose τf hτf using hrange1
  choose τi hτi using hrange2
  have hτ1 : ∀ x, τi (τf x) = x := fun x => hψb (by rw [← hτi, ← hτf])
  have hτ2 : ∀ y, τf (τi y) = y := fun y => hφb (by rw [← hτf, ← hτi])
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) :=
    { toFun := τf
      invFun := τi
      left_inv := hτ1
      right_inv := hτ2
      map_mul' := fun x y => hφb (by rw [map_mul, ← hτf, ← hτf, ← hτf, map_mul])
      map_add' := fun x y => hφb (by rw [map_add, ← hτf, ← hτf, ← hτf, map_add])
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        apply hφb
        rw [← hτf]
        change ψ (algebraMap A B a) = φ (algebraMap A B a)
        exact congrArg (fun f : A →+* K => f a) hψA }
  obtain ⟨s, hs⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  have key : ∀ b, φ' (g • b) = φ ((s : G) • b) := by
    intro b
    have e1 : τ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q ((s : G) • b) := by
      rw [← hs]
      rfl
    have e2 := hτf (Ideal.Quotient.mk Q b)
    change ψ b = φb (τ (Ideal.Quotient.mk Q b)) at e2
    rw [e1] at e2
    exact e2
  refine ⟨(s : G) * g⁻¹, fun b => ?_⟩
  have := key (g⁻¹ • b)
  rwa [smul_inv_smul, ← mul_smul] at this

section GQuot

variable {X Z : Scheme.{0}} {q : X ⟶ Z}

/-- The ring map on sections over `q⁻¹ W` induced by `f : X → X` with `f ≫ q = q`. -/
def secMap (f : X ⟶ X) (hf : f ≫ q = q) (W : Z.Opens) : Γ(X, q ⁻¹ᵁ W) →+* Γ(X, q ⁻¹ᵁ W) :=
  (f.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq hf W)).hom

theorem appLE_congr' {X' Y' : Scheme.{0}} {f f' : X' ⟶ Y'} (h : f = f') (U : Y'.Opens)
    (V : X'.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h; rfl

theorem secMap_congr {f f' : X ⟶ X} (h : f = f') (hf : f ≫ q = q) (hf' : f' ≫ q = q)
    (W : Z.Opens) : secMap f hf W = secMap f' hf' W := by
  subst h; rfl

theorem secMap_id (h : 𝟙 X ≫ q = q) (W : Z.Opens) : secMap (𝟙 X) h W = RingHom.id _ := by
  ext b
  simp only [secMap, Scheme.Hom.appLE, Scheme.Hom.id_app]
  show (CommRingCat.Hom.hom (𝟙 _ ≫ X.presheaf.map (𝟙 (Opposite.op (q ⁻¹ᵁ W))))) b = b
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem secMap_comp (f f' : X ⟶ X) (hf : f ≫ q = q) (hf' : f' ≫ q = q) (h : (f ≫ f') ≫ q = q)
    (W : Z.Opens) : secMap (f ≫ f') h W = (secMap f hf W).comp (secMap f' hf' W) := by
  unfold secMap
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

/-- `f^*` fixes the pulled-back sections of `Z` when `f ≫ q = q`. -/
theorem secMap_app (f : X ⟶ X) (hf : f ≫ q = q) (W : Z.Opens) (a : Γ(Z, W)) :
    secMap f hf W (q.app W a) = q.app W a := by
  have key : q.app W ≫ f.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq hf W) = q.app W := by
    conv_lhs => rw [Scheme.Hom.app_eq_appLE]
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr' hf W (q ⁻¹ᵁ W) _ le_rfl,
      ← Scheme.Hom.app_eq_appLE]
  exact congrArg (fun φ => φ.hom a) key

theorem inv_comp_eq {g : Aut X} (hg : g.asIso.hom ≫ q = q) : g.asIso.inv ≫ q = q := by
  conv_lhs => rw [← hg]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {G : Subgroup (Aut X)}

/-- The action of `G` on `Γ(X, q⁻¹ W)`: `g • s = (g⁻¹)^* s`. -/
def secAction (hinv : ∀ g ∈ G, g.asIso.hom ≫ q = q) (W : Z.Opens) :
    MulSemiringAction G Γ(X, q ⁻¹ᵁ W) where
  smul g b := secMap (g : Aut X).asIso.inv (inv_comp_eq (hinv g g.2)) W b
  one_smul b := by
    change secMap _ _ W b = b
    rw [secMap_congr (f' := 𝟙 X) (by simp) _ (Category.id_comp q), secMap_id]
    rfl
  mul_smul x y b := by
    change secMap _ _ W b = secMap _ _ W (secMap _ _ W b)
    rw [secMap_congr (f' := (x : Aut X).asIso.inv ≫ (y : Aut X).asIso.inv) (by simp) _
      (by rw [Category.assoc, inv_comp_eq (hinv y y.2), inv_comp_eq (hinv x x.2)]),
      secMap_comp _ _ (inv_comp_eq (hinv x x.2)) (inv_comp_eq (hinv y y.2))]
    rfl
  smul_zero g := map_zero _
  smul_add g a b := map_add _ a b
  smul_one g := map_one _
  smul_mul g a b := map_mul _ a b

/-- A `K`-point is determined by its map on the sections of an affine open containing it. -/
theorem eq_of_appLE_eq {K : Type} [Field K] (y y' : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (e : ⊤ ≤ y ⁻¹ᵁ U) (e' : ⊤ ≤ y' ⁻¹ᵁ U)
    (h : y.appLE U ⊤ e = y'.appLE U ⊤ e') : y = y' := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hU (isAffineOpen_top _) e
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec y' hU (isAffineOpen_top _) e'
  rw [h, h2, IsAffineOpen.fromSpec_top] at h1
  exact ((cancel_epi _).1 h1).symm

/-- **The `K`-points of an SGA 1 quotient by a finite group are the orbits.** If `q : X → Z` is the
quotient by a finite group `G` (`IsGQuotient`) and two `K`-points of `X` have the same image in
`Z`, they differ by an element of `G`. -/
theorem exists_eq_comp_of_isGQuotient [Finite G] (hq : IsGQuotient G q) {K : Type} [Field K]
    (y y' : Spec (CommRingCat.of K) ⟶ X) (h : y ≫ q = y' ≫ q) :
    ∃ g ∈ G, y' = y ≫ g.asIso.hom := by
  obtain ⟨hinv, haff, hsec⟩ := hq
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hxW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q (y default))) isOpen_univ
  set U := q ⁻¹ᵁ W with hUdef
  have hU : IsAffineOpen U := hW.preimage q
  have ey : ⊤ ≤ y ⁻¹ᵁ U := by
    intro a _
    rw [Subsingleton.elim a default]
    exact hxW
  have ey' : ⊤ ≤ y' ⁻¹ᵁ U := by
    intro a _
    rw [Subsingleton.elim a default]
    change q (y' default) ∈ W
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact hxW
  letI : MulSemiringAction G Γ(X, U) := secAction hinv W
  letI : Algebra Γ(Z, W) Γ(X, U) := (q.app W).hom.toAlgebra
  haveI : SMulCommClass G Γ(Z, W) Γ(X, U) := by
    constructor
    intro g a b
    change secMap _ _ W (q.app W a * b) = q.app W a * secMap _ _ W b
    rw [map_mul, secMap_app]
  haveI : Algebra.IsInvariant Γ(Z, W) Γ(X, U) G := by
    constructor
    intro b hb
    have hmem : b ∈ Set.range (q.app W) := by
      rw [(hsec W hW).2]
      intro g hg
      have := hb ⟨g⁻¹, G.inv_mem hg⟩
      change secMap _ _ W b = b at this
      rw [secMap_congr (f' := g.asIso.hom) (by simp) _ (hinv g hg)] at this
      exact this
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  let φ : Γ(X, U) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (y.appLE U ⊤ ey).hom
  let φ' : Γ(X, U) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (y'.appLE U ⊤ ey').hom
  have hagree : φ.comp (algebraMap Γ(Z, W) Γ(X, U)) = φ'.comp (algebraMap Γ(Z, W) Γ(X, U)) := by
    ext a
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom (y.appLE U ⊤ ey (q.app W a)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (y'.appLE U ⊤ ey' (q.app W a))
    have k1 : q.app W ≫ y.appLE U ⊤ ey = (y ≫ q).appLE W ⊤ (ey.trans le_rfl) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have k2 : q.app W ≫ y'.appLE U ⊤ ey' = (y' ≫ q).appLE W ⊤ (ey'.trans le_rfl) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have k3 : q.app W ≫ y.appLE U ⊤ ey = q.app W ≫ y'.appLE U ⊤ ey' := by
      rw [k1, k2]; exact appLE_congr' h _ _ _ _
    exact congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom (φ.hom a)) k3
  obtain ⟨g, hg⟩ := exists_comp_smul_eq G φ φ' hagree
  refine ⟨(g : Aut X)⁻¹, G.inv_mem g.2, ?_⟩
  have key := Scheme.Hom.appLE_comp_appLE y (g : Aut X).asIso.inv U U ⊤
    (preimage_le_of_comp_eq (inv_comp_eq (hinv g g.2)) W) ey
  have hy' : y' = y ≫ (g : Aut X).asIso.inv := by
    refine eq_of_appLE_eq y' (y ≫ (g : Aut X).asIso.inv) hU ey' ?_ ?_
    · intro a _
      change q ((g : Aut X).asIso.inv (y a)) ∈ W
      rw [← Scheme.Hom.comp_apply, inv_comp_eq (hinv g g.2)]
      exact ey (show a ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
    rw [← key]
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    ext b
    exact hg b
  rw [hy']
  simp

end GQuot

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 4: glue C2 `CoordinateFromSections` from T5, glue A and the P¹ glue
`P1ThreePoints`
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-! ## Values at field points through charts -/

section Charts

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem top_le_preimage_of_ptOf_mem (y : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens}
    (hx : ptOf y ∈ O) : ⊤ ≤ y ⁻¹ᵁ O := by
  intro a _
  rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
  exact hx

/-- The value of a section at a field point, through `appLE`. -/
theorem ev_eq_appLE (y : Spec (CommRingCat.of K) ⟶ X) {O : X.Opens} (hx : ptOf y ∈ O)
    (s : Γ(X, O)) :
    ev y hx s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (y.appLE O ⊤ (top_le_preimage_of_ptOf_mem y hx) s) := by
  have e1 := ImagePlane.ev_comp (𝟙 _) y (O := O) hx s
  have e2 := ev_res (𝟙 (Spec (CommRingCat.of K)))
    (top_le_preimage_of_ptOf_mem y hx) (show ptOf (𝟙 (Spec (CommRingCat.of K))) ∈ ⊤ from trivial)
    (y.app O s)
  have e3 := ev_top (𝟙 (Spec (CommRingCat.of K)))
    (res (top_le_preimage_of_ptOf_mem y hx) (y.app O s))
  simp only [Category.id_comp] at e1
  rw [e1, ← e2, e3]
  rfl

/-- **Chart injectivity**: on an affine open `W` whose sections are generated by `h` over
`ℤ_(p)`, a field point in `W` is determined by the value of `h`. -/
theorem eq_of_ev_eq_chart {p : ℕ} [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    {W : 𝒵.left.Opens} (hW : IsAffineOpen W) (h : Γ(𝒵.left, W))
    (hs : Function.Surjective (eval₂RingHom (baseToSections 𝒵 W) h))
    (z z' : Spec (CommRingCat.of K) ⟶ 𝒵.left) (hz : ptOf z ∈ W) (hz' : ptOf z' ∈ W)
    (he : ev z hz h = ev z' hz' h) : z = z' := by
  have hring : ev z hz = ev z' hz' := by
    ext s
    obtain ⟨P, rfl⟩ := hs s
    simp only [coe_eval₂RingHom]
    rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, he,
      zloc_ringHom_ext ((ev z hz).comp (baseToSections 𝒵 W))
        ((ev z' hz').comp (baseToSections 𝒵 W))]
  refine eq_of_appLE_eq z z' hW (top_le_preimage_of_ptOf_mem z hz)
    (top_le_preimage_of_ptOf_mem z' hz') ?_
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  ext s
  have := congrArg (fun φ : Γ(𝒵.left, W) →+* K => φ s) hring
  simp only [ev_eq_appLE] at this
  exact this

/-- **An isomorphism onto `P¹` is injective on field points.** -/
theorem val_injective_of_isP1Coordinate {p : ℕ} [Fact p.Prime]
    {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left} (hρ : IsP1Coordinate 𝒵 ρ)
    (z z' : Spec (CommRingCat.of K) ⟶ 𝒵.left) (h : ρ.val z = ρ.val z') : z = z' := by
  obtain ⟨hU, hV, hbU, hbV⟩ := hρ
  by_cases hz : ptOf z ∈ ρ.U <;> by_cases hz' : ptOf z' ∈ ρ.U
  · rw [val_of_mem ρ z hz, val_of_mem ρ z' hz'] at h
    exact eq_of_ev_eq_chart 𝒵 hU ρ.f hbU.2 z z' hz hz' (OnePoint.coe_injective h)
  · rw [val_of_mem ρ z hz, val_of_not_mem ρ z' hz'] at h
    exact (OnePoint.coe_ne_infty _ h).elim
  · rw [val_of_not_mem ρ z hz, val_of_mem ρ z' hz'] at h
    exact (OnePoint.coe_ne_infty _ h.symm).elim
  · have hv := mem_V_of_not_mem_U ρ hz
    have hv' := mem_V_of_not_mem_U ρ hz'
    refine eq_of_ev_eq_chart 𝒵 hV ρ.g hbV.2 z z' hv hv' ?_
    rw [ev_g_eq_zero ρ z hv hz, ev_g_eq_zero ρ z' hv' hz']

end Charts

/-- A point of `P¹(ℚ̄)` fixed by `Gal(ℚ̄/ℚ)` is rational. -/
theorem exists_rat_of_fixed (v : OnePoint Qbar)
    (hv : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, v.map σ = v) :
    ∃ r : OnePoint ℚ, v = r.map (algebraMap ℚ Qbar) := by
  induction v using OnePoint.rec with
  | infty => exact ⟨OnePoint.infty, rfl⟩
  | coe x =>
    have hx : x ∈ Set.range (algebraMap ℚ Qbar) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro σ
      exact OnePoint.coe_injective (hv σ)
    obtain ⟨r, rfl⟩ := hx
    exact ⟨OnePoint.some r, rfl⟩

/-! ## The P¹ glue -/

/-- **Glue (C2-P¹): normalizing a coordinate of `P¹_{ℤ_(p)}` by three disjoint rational
sections** (geometry of `P¹` over the DVR `ℤ_(p)`; no literature). Let `ρ₀ : 𝒵 ≅ P¹_{ℤ_(p)}` (by
charts, `IsP1Coordinate`) and let `z₀, zi, z₁` be `ℚ̄`-points of `𝒵` whose `ρ₀`-values are rational,
`a, b, c ∈ P¹(ℚ)`, and whose underlying points have pairwise disjoint closures. Then some
`ρ : 𝒵 ≅ P¹_{ℤ_(p)}` takes the values `0, ∞, −16/27` at them. (Proof outline: the closure of the
point `t = a` of the generic fibre is the section `t = a`, which meets the special fibre in
`a mod p ∈ P¹(𝔽_p)`; so `a, b, c` have pairwise distinct reductions, and so do `0, ∞, −16/27`
(`p > 3`). Hence the Möbius map `m` with `m(a) = 0`, `m(b) = ∞`, `m(c) = −16/27` lies in
`PGL₂(ℤ_(p))` (`PGL₂(ℤ_(p)) → PGL₂(𝔽_p)` is onto and `PGL₂` is sharply 3-transitive), and
`ρ = m ∘ ρ₀` is again an isomorphism onto `P¹_{ℤ_(p)}`: it is a composite of translations
`t ↦ t + e` (`e ∈ ℤ_(p)`), scalings `t ↦ u t` (`u ∈ ℤ_(p)^×`) and the inversion `t ↦ 1/t`.) -/
def P1ThreePoints : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p))))
    (ρ₀ : ToP1 𝒵.left), IsP1Coordinate 𝒵 ρ₀ →
    ∀ (z₀ zi z₁ : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (a b c : OnePoint ℚ),
      ρ₀.val z₀ = a.map (algebraMap ℚ Qbar) → ρ₀.val zi = b.map (algebraMap ℚ Qbar) →
      ρ₀.val z₁ = c.map (algebraMap ℚ Qbar) →
      Disjoint (closure ({qbarPoint z₀} : Set 𝒵.left)) (closure {qbarPoint zi}) →
      Disjoint (closure ({qbarPoint z₀} : Set 𝒵.left)) (closure {qbarPoint z₁}) →
      Disjoint (closure ({qbarPoint zi} : Set 𝒵.left)) (closure {qbarPoint z₁}) →
      ∃ ρ : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ ∧ ρ.val z₀ = OnePoint.some 0 ∧
        ρ.val zi = OnePoint.infty ∧ ρ.val z₁ = OnePoint.some (-16 / 27)

/-! ## The reduction of C2 -/

theorem map_neg_16_27 (σ : Qbar ≃ₐ[ℚ] Qbar) : σ (-16 / 27 : Qbar) = -16 / 27 := by
  rw [map_div₀, map_neg, map_ofNat, map_ofNat]

/-- **Glue C2 `CoordinateFromSections` from the textbook leaf `TorsionStructure` (T5), glue A
`FibreAutTame` (used only for the finiteness of `fibreAut`) and the P¹ glue `P1ThreePoints`.**
The `ρ₀ ∘ q`-fibres on `ℚ̄`-points are the `q`-fibres (`val_injective_of_isP1Coordinate`), which are
the `fibreAut`-orbits (`exists_eq_comp_of_isGQuotient`), which are the twist classes
(`twistEq_of_mem_fibreAut`, `mem_orbit_of_twistEq`). The CM points have Galois-fixed, hence
rational, `ρ₀ ∘ q`-values (their `π`-values `0, ∞, −16/27` are rational, R2fp, through the
comparison `exists_genFib_to_Y`), and the disjointness hypothesis lets `P1ThreePoints` move them to
`0, ∞, −16/27`. -/
theorem coordinateFromSections_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hN : P1ThreePoints) : CoordinateFromSections := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf hZp hZs hdisj ρ₀ hρ₀
  obtain ⟨hfin, -⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hinvq := hq.1
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  have horb : ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → (y ≫ q.left = y' ≫ q.left ↔ TwistEq P P') := by
    intro y y' P P' hP hP'
    constructor
    · intro e
      obtain ⟨h, hhG, rfl⟩ := exists_eq_comp_of_isGQuotient hq y y' e
      exact twistEq_of_mem_fibreAut hM huniq hhG y P P' hP hP'
    · intro hte
      obtain ⟨h, hhG, rfl⟩ := mem_orbit_of_twistEq hT hM y y' P P' hP hP' hte
      rw [Category.assoc, hinvq h hhG]
  have hR2 : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P → IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' →
      (π.val (K := Qbar) (s ≫ g).left = π.val (K := Qbar) (s' ≫ g).left ↔ TwistEq P P') ∧
      (HasCM4 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.some 0) ∧
      (HasCM3 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.some (-16 / 27)) :=
    fun s s' P P' hP hP' => h2 (s ≫ g) (s' ≫ g) P P' (hg Qbar s P hP) (hg Qbar s' P' hP')
  -- two points of the same CM type have the same image in `𝒵`
  have hsameCM : ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM4 P'.q) ∨ (HasCM3 P.q ∧ HasCM3 P'.q) ∨
        (HasCM24 P.q ∧ HasCM24 P'.q)) → y ≫ q.left = y' ≫ q.left := by
    intro y y' P P' hP hP' hcm
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    obtain ⟨s', hs'⟩ := genFib_pt 𝒴 y'
    have hP2 : IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P :=
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    have hP2' : IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' := 
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs').mpr hP'
    obtain ⟨hrel, c4, c3, c2⟩ := hR2 s s' P P' hP2 hP2'
    obtain ⟨-, c4', c3', c2'⟩ := hR2 s' s P' P hP2' hP2
    refine (horb y y' P P' hP hP').2 (hrel.1 ?_)
    rcases hcm with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · rw [c4 a, c4' b]
    · rw [c3 a, c3' b]
    · rw [c2 a, c2' b]
  -- Galois-fixed values at CM points
  have hfix : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P : QML3 Qbar), IsFibreOf 𝒜 y P →
      (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (ρ₀.val (y ≫ q.left)).map σ = ρ₀.val (y ≫ q.left) := by
    intro y P hP hcm σ
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    have hP2 : IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P :=
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    set s' : fieldPt Qbar ⟶ genFib 𝒴 := fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ s with hs'def
    have hs'l : s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
        Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y := by
      rw [← hs]
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ _ = _
      exact Category.assoc _ _ _
    obtain ⟨P', hP'⟩ := hM.2.2.1 Qbar (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y)
    have hP2' : IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' := 
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs'l).mpr hP'
    obtain ⟨hrel, c4, c3, c2⟩ := hR2 s s' P P' hP2 hP2'
    have hl : (s' ≫ g).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ (s ≫ g).left := by
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ g.left = _
      exact Category.assoc _ _ _
    have hπ : π.val (K := Qbar) (s' ≫ g).left =
        (π.val (K := Qbar) (s ≫ g).left).map (σ : Qbar →+* Qbar) :=
      (congrArg (fun t => π.val (K := Qbar) t) hl).trans (ToP1.val_comp π _ _)
    have hval : π.val (K := Qbar) (s ≫ g).left = π.val (K := Qbar) (s' ≫ g).left := by
      rw [hπ]
      rcases hcm with a | a | a
      · rw [c4 a]; simp
      · rw [c3 a]; rfl
      · rw [c2 a]
        show OnePoint.some (-16 / 27 : Qbar) = OnePoint.some (σ (-16 / 27 : Qbar))
        rw [map_neg_16_27]
    have hq' := (horb y _ P P' hP hP').2 (hrel.1 hval)
    have e := ToP1.val_comp ρ₀ (σ : Qbar →+* Qbar) (y ≫ q.left)
    rw [← Category.assoc, ← hq'] at e
    exact e.symm
  -- the three CM points
  obtain ⟨⟨P4, c4⟩, ⟨P3, c3⟩, ⟨P2, c2⟩⟩ := hCM
  obtain ⟨y4, hy4⟩ := hM.2.2.2.2.1 P4
  obtain ⟨y3, hy3⟩ := hM.2.2.2.2.1 P3
  obtain ⟨y2, hy2⟩ := hM.2.2.2.2.1 P2
  obtain ⟨a, ha⟩ := exists_rat_of_fixed _ (hfix y4 P4 hy4 (Or.inl c4))
  obtain ⟨b, hb⟩ := exists_rat_of_fixed _ (hfix y3 P3 hy3 (Or.inr (Or.inl c3)))
  obtain ⟨c, hc⟩ := exists_rat_of_fixed _ (hfix y2 P2 hy2 (Or.inr (Or.inr c2)))
  have d43 := hdisj y4 y3 P4 P3 hy4 hy3 (Or.inl ⟨c4, c3⟩)
  have d42 := hdisj y4 y2 P4 P2 hy4 hy2 (Or.inr (Or.inl ⟨c4, c2⟩))
  have d32 := hdisj y3 y2 P3 P2 hy3 hy2 (Or.inr (Or.inr ⟨c3, c2⟩))
  obtain ⟨ρ, hρ, v4, v3, v2⟩ := hN p (by omega) 𝒵 ρ₀ hρ₀ (y4 ≫ q.left) (y3 ≫ q.left)
    (y2 ≫ q.left) a b c ha hb hc d43 d42 d32
  refine ⟨ρ, hρ, ?_⟩
  intro y y' P Q hP hQ
  rw [ToP1.val_comp_right, ToP1.val_comp_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Iff.trans ?_ (horb y y' P Q hP hQ)
    exact ⟨fun e => val_injective_of_isP1Coordinate hρ _ _ e, fun e => by rw [e]⟩
  · intro h4
    rw [hsameCM y y4 P P4 hP hy4 (Or.inl ⟨h4, c4⟩), v4]
  · intro h3
    rw [hsameCM y y3 P P3 hP hy3 (Or.inr (Or.inl ⟨h3, c3⟩)), v3]
  · intro h24
    rw [hsameCM y y2 P P2 hP hy2 (Or.inr (Or.inr ⟨h24, c2⟩)), v2]

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 5: glue A `FibreAutTame` from T5, a fixed-point glue and a twist-class count
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **Glue (A-fix): nontrivial elements of `fibreAut` fix only finitely many `ℚ̄`-points**
(scheme theory of curves; no literature). For the smooth model `𝒴` at `p > 324` and a triple with
R1fp, R1hecke, R2fp, every `h ≠ 1` in `fibreAut 𝒴 𝒜` fixes only finitely many `ℚ̄`-points.
(Outline: `𝒴` is integral (model-glue's `ModelIntegral`: `𝒴_ℚ ≅ Y` by `CurveBijIso`, `Y`
irreducible, `𝒴` reduced and flat); the fixed locus of `h` is the closed equalizer of `h` and
`id` (`𝒴` separated); infinitely many fixed `ℚ̄`-points lie over infinitely many closed points of
the irreducible curve `𝒴_ℚ`, so the equalizer contains the generic point, hence is all of the
integral `𝒴`, and `h = id`.) -/
def FibreAutFixFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ h ∈ fibreAut 𝒴 𝒜, h ≠ 1 →
      {y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | y ≫ h.asIso.hom = y}.Finite

/-- **Glue (A-count): a twist class has at most `324 = 4 · 81` isomorphism classes** (algebra of
`𝒪` and level structures; no new literature beyond T5). (Outline: by Skolem–Noether every
`α ∈ Aut 𝒪` is, up to conjugation by `𝒪^×` (which does not change the pair's class,
`conjUnitIso`), one of the at most four automorphisms induced by `1, i, j, ij` (`NormO.T`, the
Atkin–Lehner group), so a twist class contains at most 4 pair classes; on one pair the level
structures are `η₀(· u₀)` with `u₀` determined mod `3𝒪` (`Level3.torsor`, given T5), at most
`#(𝒪/3𝒪) = 81` of them (in fact 72). Proved below: `twistClassCard`.) -/
def TwistClassCard : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq P Q}.Finite ∧
    {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq P Q}.ncard ≤ 324

/-- The smooth model has infinitely many `ℚ̄`-points (`CurveSurj` for `π ∘ g` on `𝒴_ℚ`). -/
theorem infinite_qbarPoints {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
    {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) :
    (Set.univ : Set (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left)).Infinite := by
  intro hfin
  obtain ⟨g, -, -⟩ := exists_genFib_to_Y hM h1
  have hfin' : (Set.univ : Set (fieldPt Qbar ⟶ genFib 𝒴)).Finite := by
    refine Set.Finite.of_finite_image (f := fun s => s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p))
      (hfin.subset (Set.subset_univ _)) ?_
    intro s _ s' _ h
    exact genFib_pt_inj 𝒴 s s' h
  obtain ⟨y0⟩ := hM.2.2.2.2.2.2.2
  obtain ⟨s0, -⟩ := genFib_pt 𝒴 y0
  have hsurj := curveFacts.2 (genFib 𝒴) (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1) ⟨s0⟩
    (π.comp g.left) (fun _ => hfin'.subset (Set.subset_univ _))
  have : (Set.univ : Set (OnePoint Qbar)).Finite := by
    refine (hfin'.image (fun s => (π.comp g.left).val (K := Qbar) s.left)).subset ?_
    intro t _
    obtain ⟨s, hs⟩ := hsurj t
    exact ⟨s, trivial, hs⟩
  have hinf : (Set.univ : Set (OnePoint Qbar)).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => OnePoint.some (n : Qbar)) ?_
      (fun _ => trivial)
    intro m n h
    exact_mod_cast OnePoint.coe_injective h
  exact hinf this

/-- **Glue A `FibreAutTame` from T5, (A-fix) and (A-count).** A finite subset `S` of `fibreAut`
injects into the twist class of a `ℚ̄`-point `y` avoiding the (finitely many) fixed points of the
`s⁻¹ t` (`s ≠ t ∈ S`), so `|S| ≤ 324`; hence `fibreAut` is finite of order `≤ 324 < p`. -/
theorem fibreAutTame_of (hT : ObjBridge.TorsionStructure) (hfix : FibreAutFixFinite)
    (hcnt : TwistClassCard) : FibreAutTame := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  choose fib hfib using fun y => hM.2.2.1 Qbar y
  have hbound : ∀ S : Finset (Aut 𝒴.left), (↑S : Set (Aut 𝒴.left)) ⊆ fibreAut 𝒴 𝒜 →
      S.card ≤ 324 := by
    intro S hS
    classical
    let F : Set (Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) :=
      ⋃ s ∈ S, ⋃ t ∈ S, {y | s ≠ t ∧ y ≫ (s⁻¹ * t).asIso.hom = y}
    have hF : F.Finite := by
      refine Set.Finite.biUnion S.finite_toSet fun s hs => Set.Finite.biUnion S.finite_toSet
        fun t ht => ?_
      by_cases hst : s = t
      · simp [hst]
      · have hmem : s⁻¹ * t ∈ fibreAut 𝒴 𝒜 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS hs)) (hS ht)
        have hne : s⁻¹ * t ≠ 1 := fun h => hst (inv_mul_eq_one.mp h)
        refine (hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 _ hmem hne).subset ?_
        intro y hy
        exact hy.2
    obtain ⟨y, -, hyF⟩ := ((infinite_qbarPoints (π := π) hM h1).diff hF).nonempty
    have hcl := hcnt (fib y)
    have hmaps : ∀ s ∈ S, M3.mk (fib (y ≫ s.asIso.hom)) ∈
        {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq (fib y) Q} :=
      fun s hs => ⟨_, rfl, twistEq_of_mem_fibreAut hM huniq (hS hs) y _ _ (hfib y) (hfib _)⟩
    have hinj : Set.InjOn (fun s : Aut 𝒴.left => M3.mk (fib (y ≫ s.asIso.hom))) ↑S := by
      intro s hs t ht hst
      have e : y ≫ s.asIso.hom = y ≫ t.asIso.hom :=
        hM.2.2.2.1 _ _ _ _ (hfib _) (hfib _) hst
      by_contra hne
      apply hyF
      simp only [F, Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨s, hs, t, ht, hne, ?_⟩
      simp only [Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom]
      rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    calc S.card = (↑S : Set (Aut 𝒴.left)).ncard := (Set.ncard_coe_finset S).symm
      _ ≤ _ := Set.ncard_le_ncard_of_injOn _ hmaps hinj hcl.1
      _ ≤ 324 := hcl.2
  have hfinG : (fibreAut 𝒴 𝒜 : Set (Aut 𝒴.left)).Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf 325
    have := hbound S hS
    omega
  haveI : Finite (fibreAut 𝒴 𝒜) := hfinG.to_subtype
  refine ⟨this, fun hdvd => ?_⟩
  have hpos : 0 < Nat.card (fibreAut 𝒴 𝒜) := Nat.card_pos
  have hle : Nat.card (fibreAut 𝒴 𝒜) ≤ 324 := by
    have e : Nat.card (fibreAut 𝒴 𝒜) = (fibreAut 𝒴 𝒜 : Set (Aut 𝒴.left)).ncard :=
      Nat.card_coe_set_eq _
    rw [e, Set.ncard_eq_toFinset_card _ hfinG]
    exact hbound _ (by simp)
  have := Nat.le_of_dvd hpos hdvd
  omega

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 6: glue C1 `CMSectionsDisjoint` from L5, L6, A and four smaller glue Props
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-! ## Automorphisms fixing every field point over a set -/

section FixOn

variable {X : Scheme.{0}}

/-- `h` fixes every field point of `X` whose point lies in `Z` (for `Z = {w}`: `h` fixes `w` and
acts trivially on `κ(w)`). -/
def FixesFieldPointsOn (h : Aut X) (Z : Set X) : Prop :=
  ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ X), ptOf t ∈ Z → t ≫ h.asIso.hom = t

/-- The automorphisms fixing every field point over `Z` form a subgroup. -/
def fixOn (Z : Set X) : Subgroup (Aut X) where
  carrier := {h | FixesFieldPointsOn h Z}
  one_mem' := fun K _ t _ => by simp
  mul_mem' := by
    intro a b ha hb K _ t ht
    simp only [Aut.mul_asIso, Iso.trans_hom]
    rw [← Category.assoc, hb K t ht, ha K t ht]
  inv_mem' := by
    intro a ha K _ t ht
    simp only [Aut.inv_asIso, Iso.symm_hom]
    conv_lhs => rw [← ha K t ht]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem FixesFieldPointsOn.mono {h : Aut X} {Z Z' : Set X} (hh : FixesFieldPointsOn h Z)
    (hZ : Z' ⊆ Z) : FixesFieldPointsOn h Z' := fun K _ t ht => hh K t (hZ ht)

/-- Fixing the field points at `w` gives the hypothesis of Leaf L6 at `w`. -/
theorem residue_trivial_of_fixesOn {h : Aut X} {w : X} (hh : FixesFieldPointsOn h {w}) :
    ∃ e : h.asIso.hom w = w,
      (X.residueFieldCongr e).inv ≫ h.asIso.hom.residueFieldMap w = 𝟙 _ := by
  let K : Type := X.residueField w
  let t : Spec (CommRingCat.of K) ⟶ X :=
    (Scheme.SpecToEquivOfField K X).symm ⟨w, CommRingCat.ofHom (RingHom.id K)⟩
  have ht : ptOf t = w := by
    simp only [ptOf, t, Equiv.apply_symm_apply]
  have hfix := hh K t (by rw [ht]; rfl)
  have key : ∀ a : (Σ x : X, X.residueField x ⟶ CommRingCat.of K),
      a = ⟨w, CommRingCat.ofHom (RingHom.id K)⟩ →
      (⟨h.asIso.hom a.1, h.asIso.hom.residueFieldMap a.1 ≫ a.2⟩ :
        Σ x : X, X.residueField x ⟶ CommRingCat.of K) = a →
      ∃ e : h.asIso.hom w = w,
        (X.residueFieldCongr e).inv ≫ h.asIso.hom.residueFieldMap w = 𝟙 _ := by
    rintro _ rfl e
    rw [Scheme.SpecToEquivOfField_eq_iff] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨e1, ?_⟩
    have e3 : h.asIso.hom.residueFieldMap w = (X.residueFieldCongr e1).hom := by
      have := e2
      dsimp only at this
      ext x
      exact congrArg (fun φ => φ.hom x) this
    rw [e3, Iso.inv_hom_id]
  have e := congrArg (Scheme.SpecToEquivOfField K X) hfix
  rw [specToEquivOfField_comp_right] at e
  exact key _ (Equiv.apply_symm_apply _ _) e

end FixOn

/-! ## The smaller glue Props -/

/-- **Glue (C1a): the points of `X` over a point of an SGA 1 quotient form one orbit**
(commutative algebra; SGA 1 Exp. V, Prop. 1.1 (ii) (locator UNVERIFIED); over an affine `W ⊆ Z`
it is the transitivity of `G` on the primes of `Γ(q⁻¹W)` over a prime of `Γ(q⁻¹W)^G`, Mathlib's
`Algebra.IsInvariant.exists_smul_of_under_eq`). -/
def GQuotientPointOrbits : Prop :=
  ∀ (X Z : Scheme.{0}) (G : Subgroup (Aut X)) (q : X ⟶ Z), Finite G → IsGQuotient G q →
    ∀ x x' : X, q x = q x' → ∃ g ∈ G, g.asIso.hom x' = x

/-- **Glue (C1b): the stabilizer of a CM point contains an involution** (algebra of QM surfaces
with CM; no new literature). For the smooth model and a `ℚ̄`-point `y` whose object has CM by
`ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`, some `ι ≠ 1` in `fibreAut` with `ι² = 1` fixes `y`. (Outline: the CM
endomorphism `φ` (`φ² = −1`, resp. of order 6, resp. `φ² = −6` composed with the Atkin–Lehner
twist) is an isomorphism `(A, ι, η) ≅ (A, ι ∘ α, η ∘ (· u))` for a twist `α` and a unit `u`
(`Level3.torsor`, `exists_unit_congr`), so the Hecke automorphism of `(α, u)` (or a power of it)
fixes `y`; the stabilizers have the orbifold orders `4, 6, 2` modulo `±1`
(`RvNocm.ramification_eq_orbifold_order`), all even.) -/
def CMStabInvolution : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P : QML3 Qbar), IsFibreOf 𝒜 y P →
      (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
      ∃ ι ∈ fibreAut 𝒴 𝒜, ι ≠ 1 ∧ ι * ι = 1 ∧ y ≫ ι.asIso.hom = y

/-- **Glue (C1c): an automorphism fixing a `ℚ̄`-point fixes its closure pointwise, with trivial
residue action** (scheme theory; no literature). For `𝒴` proper and smooth over `ℤ_(p)` and an
automorphism `h` over `ℤ_(p)` with `y ≫ h = y`, `h` fixes every field point of `𝒴` lying in the
closure `Z` of the point of `y`. (Outline: `h` fixes `x` and acts trivially on `κ(x)` (it
commutes with the embedding `κ(x) → ℚ̄`); `Z` with its reduced structure is integral with
function field `κ(x)`, and `h|_Z, id_Z : Z → 𝒴` agree at the generic point, hence on a dense
open (`𝒴` locally of finite presentation over `ℤ_(p)`: EGA IV 8.13.1), hence everywhere (`Z`
reduced, `𝒴` separated); a field point over `Z` factors through `Z`.) -/
def StabFixesClosure : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    ∀ (h : Aut 𝒴.left), h.asIso.hom ≫ 𝒴.hom = 𝒴.hom →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, y ≫ h.asIso.hom = y →
      FixesFieldPointsOn h (closure {qbarPoint y})

/-- **Glue (C1d): two `ℚ̄`-points with the same underlying point are Galois conjugate**
(field theory; no literature): the two embeddings `κ(x) → ℚ̄` differ by an automorphism of `ℚ̄`
(extend one to `ℚ̄`, `IsAlgClosed.lift`; `ℚ̄` is algebraic over the image). -/
def QbarPointsConjugate : Prop :=
  ∀ (X : Scheme.{0}) (y y' : Spec (CommRingCat.of Qbar) ⟶ X), qbarPoint y = qbarPoint y' →
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, y' = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ y

/-! ## The reduction of C1 -/

/-- In a finite cyclic group there is at most one involution. -/
theorem eq_of_involutions_cyclic {H : Type*} [Group H] [Finite H] [IsCyclic H] {a b : H}
    (ha : a ≠ 1) (ha2 : a * a = 1) (hb : b ≠ 1) (hb2 : b * b = 1) : a = b := by
  classical
  cases nonempty_fintype H
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  by_contra hab
  have hsub : ({1, a, b} : Finset H) ⊆ Finset.univ.filter (fun x : H => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two, ha2]
    · rw [pow_two, hb2]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
    Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton] at hcard
  have : (Finset.univ.filter (fun x : H => x ^ 2 = 1)).card ≤ 2 := hle
  omega

theorem qbarPoint_comp {X X' : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) (h : X ⟶ X') :
    qbarPoint (y ≫ h) = h (qbarPoint y) := rfl

/-- **Glue C1 `CMSectionsDisjoint` from glue A, (A-fix), (C1a)-(C1d)** (L5 and L6 are the
hypotheses of the Prop). A common point `z` of the closures of `q(x)` and `q(x')` lifts to
`w ∈ closure{x}` and, after moving by some `h ∈ fibreAut` (C1a), to `w ∈ closure{h x'}`; the
inertia group `H` of `w` in `fibreAut` contains an involution fixing `y` and one fixing `y' ≫ h`
(C1b, C1c), is cyclic (L6), so the two involutions agree, and L5 makes the closures of `x` and
`h x'` disjoint (the two points differ: Galois conjugate points (C1d) have equal `π`-values, and
CM points of different types do not), a contradiction. -/
theorem cMSectionsDisjoint_of (hA : FibreAutTame) (hfix : FibreAutFixFinite)
    (hO : GQuotientPointOrbits) (hI : CMStabInvolution) (hS : StabFixesClosure)
    (hC : QbarPointsConjugate) : CMSectionsDisjoint := by
  intro hL5 hL6 p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf y y' P P' hP hP' htype
  obtain ⟨hfin, htame⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  rw [Set.disjoint_left]
  intro z hz hz'
  have hcl : ∀ u : 𝒴.left, closure {q.left u} ⊆ q.left '' closure {u} := by
    intro u
    refine closure_minimal ?_ (q.left.isClosedMap _ isClosed_closure)
    rintro _ rfl
    exact ⟨u, subset_closure rfl, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hcl _ hz
  obtain ⟨w', hw', hww'⟩ := hcl _ hz'
  obtain ⟨h, hhG, hhw⟩ := hO _ _ _ _ hfin hq w w' hww'.symm
  set y'' := y' ≫ h.asIso.hom with hy''
  have hw'' : w ∈ closure {qbarPoint y''} := by
    rw [hy'', qbarPoint_comp, ← hhw, ← Set.image_singleton]
    exact image_closure_subset_closure_image h.asIso.hom.continuous ⟨w', hw', rfl⟩
  obtain ⟨P'', hP''⟩ := hM.2.2.1 Qbar y''
  have hover := fibreAut_over 𝒴 𝒜
  -- the two involutions
  have htype1 : HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q := by
    rcases htype with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩
    · exact Or.inl a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
  have htype2 : HasCM4 P'.q ∨ HasCM3 P'.q ∨ HasCM24 P'.q := by
    rcases htype with ⟨-, a⟩ | ⟨-, a⟩ | ⟨-, a⟩
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr a)
    · exact Or.inr (Or.inr a)
  obtain ⟨ι, hιG, hι1, hι2, hιy⟩ := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP htype1
  obtain ⟨ι', hι'G, hι'1, hι'2, hι'y⟩ := hI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y' P' hP' htype2
  set ι'' := h * ι' * h⁻¹ with hι''
  have hι''G : ι'' ∈ fibreAut 𝒴 𝒜 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhG hι'G) (Subgroup.inv_mem _ hhG)
  have hι''1 : ι'' ≠ 1 := by
    intro e
    apply hι'1
    have : ι' = h⁻¹ * ι'' * h := by rw [hι'']; group
    rw [this, e]; group
  have hι''2 : ι'' * ι'' = 1 := by
    have : ι'' * ι'' = h * (ι' * ι') * h⁻¹ := by rw [hι'']; group
    rw [this, hι'2]; group
  have hι''y : y'' ≫ ι''.asIso.hom = y'' := by
    simp only [hy'', hι'', Aut.mul_asIso, Aut.inv_asIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hι'y]
  -- the inertia group at `w`
  let H : Subgroup (Aut 𝒴.left) := fibreAut 𝒴 𝒜 ⊓ fixOn {w}
  have hιH : ι ∈ H := ⟨hιG, (hS p 𝒴 hM.1 hM.2.1 ι (hover ι hιG) y hιy).mono
    (Set.singleton_subset_iff.mpr hw)⟩
  have hι''H : ι'' ∈ H := ⟨hι''G, (hS p 𝒴 hM.1 hM.2.1 ι'' (hover ι'' hι''G) y'' hι''y).mono
    (Set.singleton_subset_iff.mpr hw'')⟩
  have hHle : H ≤ fibreAut 𝒴 𝒜 := inf_le_left
  haveI : Finite H := Finite.of_injective (fun x : H => (⟨x.1, hHle x.2⟩ : fibreAut 𝒴 𝒜))
    (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
  have hcyc : IsCyclic H := by
    refine hL6 p 𝒴 hM.1 hM.2.1 H inferInstance ?_ (fun x hx => hover x (hHle hx))
      (fun x hx hx1 => hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 x (hHle hx) hx1) w
      (fun x hx => residue_trivial_of_fixesOn hx.2)
    intro hdvd
    exact htame (hdvd.trans (Subgroup.card_dvd_of_le hHle))
  have hιι : ι = ι'' := by
    have := eq_of_involutions_cyclic (H := H) (a := ⟨ι, hιH⟩) (b := ⟨ι'', hι''H⟩)
      (fun e => hι1 (congrArg Subtype.val e)) (Subtype.ext hι2)
      (fun e => hι''1 (congrArg Subtype.val e)) (Subtype.ext hι''2)
    exact congrArg Subtype.val this
  -- the two points differ
  have hne : qbarPoint y ≠ qbarPoint y'' := by
    intro e
    obtain ⟨σ, hσ⟩ := hC _ y y'' e
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    obtain ⟨s', hs'⟩ := genFib_pt 𝒴 y'
    obtain ⟨s'', hs''⟩ := genFib_pt 𝒴 y''
    have hP2 := (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    have hP2' := (congrArg (fun t => IsFibreOf 𝒜 t _) hs').mpr hP'
    have hP2'' := (congrArg (fun t => IsFibreOf 𝒜 t _) hs'').mpr hP''
    -- the conjugate lift
    set sσ : fieldPt Qbar ⟶ genFib 𝒴 := fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ s with hsσ
    have hsσl : sσ.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) = y'' := by
      rw [hσ, ← hs]
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ _ = _
      exact Category.assoc _ _ _
    have hsσ'' : sσ = s'' := genFib_pt_inj 𝒴 _ _ (hsσl.trans hs''.symm)
    have hl : (sσ ≫ g).left = Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ (s ≫ g).left := by
      show ((fieldMap (σ : Qbar →ₐ[ℚ] Qbar)).left ≫ s.left) ≫ g.left = _
      exact Category.assoc _ _ _
    have hπσ : π.val (K := Qbar) (s'' ≫ g).left =
        (π.val (K := Qbar) (s ≫ g).left).map (σ : Qbar →+* Qbar) := by
      rw [← hsσ'']
      exact (congrArg (fun t => π.val (K := Qbar) t) hl).trans (ToP1.val_comp π _ _)
    -- `y''` is in the orbit of `y'`, so it has the same `π`-value as `y'`
    have hte : TwistEq P' P'' := twistEq_of_mem_fibreAut hM huniq hhG y' P' P'' hP' hP''
    have hR' := h2 (s' ≫ g) (s'' ≫ g) P' P'' (hg Qbar s' P' hP2') (hg Qbar s'' P'' hP2'')
    have hR := h2 (s ≫ g) (s ≫ g) P P (hg Qbar s P hP2) (hg Qbar s P hP2)
    have hv : π.val (K := Qbar) (s' ≫ g).left = π.val (K := Qbar) (s'' ≫ g).left :=
      hR'.1.2 hte
    rw [hπσ] at hv
    have h16 : (0 : Qbar) ≠ -16 / 27 := by norm_num
    rcases htype with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · rw [hR.2.1 a, hR'.2.2.1 b] at hv
      norm_num at hv
    · rw [hR.2.1 a, hR'.2.2.2 b] at hv
      norm_num at hv
    · rw [hR.2.2.1 a, hR'.2.2.2 b] at hv
      norm_num at hv
  -- Leaf L5 for the involution `ι`
  have hfinι : {t : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | t ≫ ι.asIso.hom = t}.Finite :=
    hfix p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 ι hιG hι1
  have hdisj := hL5 p 𝒴 hM.1 hM.2.1 ι 2 (hover ι hιG) (by norm_num)
    (fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
    (by rw [pow_two, hι2]) hfinι y y'' hιy (by rw [hιι]; exact hι''y) hne
  exact Set.disjoint_left.mp hdisj hw hw''

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 6b: glue B `GenericQuotientP1` from T5, a descent glue and a curve glue
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- The induced map of generic fibres `𝒴_ℚ → 𝒵_ℚ`. -/
def genFibMap {p : ℕ} [Fact p.Prime] {𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} (q : 𝒴 ⟶ 𝒵) :
    genFib 𝒴 ⟶ genFib 𝒵 :=
  Over.homMk (pullback.lift (pullback.fst 𝒴.hom (specRatToZloc p) ≫ q.left)
      (pullback.snd 𝒴.hom (specRatToZloc p))
      ((Category.assoc _ _ _).trans (by rw [Over.w q]; exact pullback.condition)))
    (pullback.lift_snd _ _ _)

theorem genFibMap_fst {p : ℕ} [Fact p.Prime] {𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))}
    (q : 𝒴 ⟶ 𝒵) : (genFibMap q).left ≫ pullback.fst 𝒵.hom (specRatToZloc p) =
      pullback.fst 𝒴.hom (specRatToZloc p) ≫ q.left :=
  pullback.lift_fst _ _ _

/-- **Glue (B-desc): an orbit-invariant coordinate on `𝒴_ℚ` descends to the quotient**
(scheme theory of quotients; SGA 1 Exp. V §1 (locators UNVERIFIED), no new literature). For the
SGA 1 quotient `q : 𝒴 → 𝒵` over `ℤ_(p)` of a proper smooth relative curve `𝒴` by a finite group
`G` of `ℤ_(p)`-automorphisms with `q` finite, a map `σ : 𝒴_ℚ → P¹` whose values on `ℚ̄`-points are constant on `G`-orbits factors
through `𝒵_ℚ`, and every `ℚ̄`-point of `𝒵_ℚ` comes from `𝒴_ℚ`. (Outline: `𝒵_ℚ = 𝒴_ℚ/G`, since
the formation of invariants commutes with the localization `ℤ_(p) → ℚ`; `σ` is `G`-invariant as a
morphism, its values on the dense set of `ℚ̄`-points of the reduced `𝒴_ℚ` being invariant; so the
opens `σ⁻¹(t ≠ ∞)`, `σ⁻¹(t ≠ 0)` are `G`-stable and saturated, their images in `𝒵_ℚ` are open
(`q` is closed and surjective), and `f, g` are invariant sections, i.e. sections on `𝒵_ℚ`;
`q` is integral and surjective, so `ℚ̄`-points lift.) -/
def QuotientDescendsQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵)
    (G : Subgroup (Aut 𝒴.left)), IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    Finite G → (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) →
    IsGQuotient G q.left → IsFinite q.left →
    ∀ σ : ToP1 (genFib 𝒴).left,
      (∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
        s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
          s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
        σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left) →
    ∃ σ' : ToP1 (genFib 𝒵).left,
      (∀ s : fieldPt Qbar ⟶ genFib 𝒴,
        σ'.val (K := Qbar) (s ≫ genFibMap q).left = σ.val (K := Qbar) s.left) ∧
      ∀ t : fieldPt Qbar ⟶ genFib 𝒵, ∃ s : fieldPt Qbar ⟶ genFib 𝒴, s ≫ genFibMap q = t

/-- **Glue (B-iso): a map to `P¹` of a proper smooth `ℚ`-curve that is bijective on `ℚ̄`-points is
an isomorphism onto `P¹_ℚ`** (curve theory; the `P¹` case of model-glue's `CurveBijIso`: finite
(quasi-finite and proper), generically étale in characteristic 0 of degree 1, onto the normal
`P¹`, hence an isomorphism (Hartshorne II.6.7, I.6.12; locators UNVERIFIED); the charts are then
the preimages of `𝔸¹` and `P¹ ∖ {0}`). -/
def ToP1BijIsCoordinateQ : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of ℚ))), IsProper Z.hom → SmoothOfRelativeDimension 1 Z.hom →
    ∀ σ : ToP1 Z.left, Function.Bijective (fun t : fieldPt Qbar ⟶ Z => σ.val (K := Qbar) t.left) →
      IsP1CoordinateQ Z σ

/-- **Glue B `GenericQuotientP1` from T5, glue A, Leaf L3 (`𝒵` proper smooth), (B-desc) and
(B-iso).** The map
`π ∘ g : 𝒴_ℚ → P¹` is constant on `fibreAut`-orbits (orbits lie in twist classes, R2fp), so it
descends to `σ̄ : 𝒵_ℚ → P¹` (B-desc); `σ̄` is injective on `ℚ̄`-points (equal values give
twist-equivalent fibres, hence one orbit (T5), hence one point of `𝒵`) and onto (`CurveSurj` for
`π ∘ g`, whose fibres are finite twist classes), so it is an isomorphism onto `P¹_ℚ` (B-iso). -/
theorem genericQuotientP1_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hTS : TameQuotientSmooth) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ) :
    GenericQuotientP1 := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf
  obtain ⟨hfin, htame⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  obtain ⟨hZp, hZs⟩ := hTS p 𝒴 𝒵 q hM.1 hM.2.1 _ hfin htame (fibreAut_over 𝒴 𝒜) hq hqf
  have hinvq := hq.1
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  choose fib hfib using fun y => hM.2.2.1 Qbar y
  set j := pullback.fst 𝒴.hom (specRatToZloc p)
  let σ : ToP1 (genFib 𝒴).left := π.comp g.left
  have hσ : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, σ.val (K := Qbar) s.left = π.val (K := Qbar) (s ≫ g).left :=
    fun s => ToP1.val_comp_right π g.left s.left
  -- `σ`-values and twist classes
  have hrel : ∀ s s' : fieldPt Qbar ⟶ genFib 𝒴,
      (σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left ↔
        TwistEq (fib (s.left ≫ j)) (fib (s'.left ≫ j))) := by
    intro s s'
    rw [hσ, hσ]
    exact (h2 (s ≫ g) (s' ≫ g) _ _ (hg Qbar s _ (hfib _)) (hg Qbar s' _ (hfib _))).1
  have hinvσ : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (h : Aut 𝒴.left), h ∈ fibreAut 𝒴 𝒜 →
      s'.left ≫ j = s.left ≫ j ≫ h.asIso.hom →
      σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left := by
    intro s s' h hh e
    refine (hrel s s').2 (twistEq_of_mem_fibreAut hM huniq hh (s.left ≫ j) _ _ (hfib _) ?_)
    exact (congrArg (fun t => IsFibreOf 𝒜 t (fib (s'.left ≫ j)))
      (e.trans (Category.assoc _ _ _).symm)).mp (hfib _)
  obtain ⟨σ', hσ', hlift⟩ := hD p 𝒴 𝒵 q (fibreAut 𝒴 𝒜) hM.1 hM.2.1 hfin (fibreAut_over 𝒴 𝒜) hq hqf σ hinvσ
  refine ⟨σ', hB (genFib 𝒵) (genFib_isProper 𝒵 hZp) (genFib_smooth 𝒵 hZs) σ' ⟨?_, ?_⟩⟩
  · intro t t' htt
    obtain ⟨s, rfl⟩ := hlift t
    obtain ⟨s', rfl⟩ := hlift t'
    simp only [hσ'] at htt
    obtain ⟨h, hhG, hh⟩ := mem_orbit_of_twistEq hT hM (s.left ≫ j) (s'.left ≫ j) _ _ (hfib _)
      (hfib _) ((hrel s s').1 htt)
    have k : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, (s ≫ genFibMap q).left ≫
        pullback.fst 𝒵.hom (specRatToZloc p) = (s.left ≫ j) ≫ q.left := fun s =>
      (Category.assoc _ _ _).trans ((congrArg (s.left ≫ ·) (genFibMap_fst q)).trans
        (Category.assoc _ _ _).symm)
    apply genFib_pt_inj 𝒵
    refine (k s).trans ((k s').trans ?_).symm
    exact (congrArg (· ≫ q.left) hh).trans ((Category.assoc _ _ _).trans
      (congrArg ((s.left ≫ j) ≫ ·) (hinvq h hhG)))
  · intro v
    obtain ⟨y0⟩ := hM.2.2.2.2.2.2.2
    obtain ⟨s0, -⟩ := genFib_pt 𝒴 y0
    have hfin' : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, {s' : fieldPt Qbar ⟶ genFib 𝒴 |
        σ.val (K := Qbar) s'.left = σ.val (K := Qbar) s.left}.Finite := by
      intro s
      have hT' := twistClassFinite hT (fib (s.left ≫ j))
      refine Set.Finite.of_finite_image (f := fun s' => M3.mk (fib (s'.left ≫ j)))
        (hT'.subset ?_) ?_
      · rintro _ ⟨s', hs', rfl⟩
        exact ⟨_, rfl, (hrel s s').1 hs'.symm⟩
      · intro a _ b _ hab
        exact genFib_pt_inj 𝒴 a b (hM.2.2.2.1 _ _ _ _ (hfib _) (hfib _) hab)
    obtain ⟨s, hs⟩ := curveFacts.2 (genFib 𝒴) (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1)
      ⟨s0⟩ σ hfin' v
    exact ⟨s ≫ genFibMap q, (hσ' s).trans hs⟩

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 7: the composite
════════════════════════════════════════════════════════════════════════════════════════════ -/

namespace MCRQuot

open MCRGlue ModelGlue

/-- **`ModelCoordinateResidue` from the leaves L1-L6, the textbook leaf `TorsionStructure` (T5),
glue B, and the smaller glue of this task**: (A-fix) `FibreAutFixFinite`, (A-count)
`TwistClassCard`, (C1a) `GQuotientPointOrbits`, (C1b) `CMStabInvolution`, (C1c)
`StabFixesClosure`, (C1d) `QbarPointsConjugate`, (C2-P¹) `P1ThreePoints`. Glue A, C1 and C2 of
mcr-glue are no longer hypotheses. -/
theorem modelCoordinateResidue_of_mcrQuot (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (gB : GenericQuotientP1)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hO : GQuotientPointOrbits)
    (hI : CMStabInvolution) (hS : StabFixesClosure) (hC : QbarPointsConjugate)
    (hN : P1ThreePoints) : ModelCoordinateResidue :=
  have gA : FibreAutTame := fibreAutTame_of hT hfix hcnt
  modelCoordinateResidue_of_leaves'' hAF hQE hTS hP1 hFix hCyc gA gB
    (cMSectionsDisjoint_of gA hfix hO hI hS hC) (coordinateFromSections_of gA hT hN)

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 8: `P1ThreePoints` from the translation glue `P1Translate`

`PGL₂(ℤ_(p))` acting on isomorphisms `𝒵 ≅ P¹_{ℤ_(p)}` by charts: the inversion `t ↦ 1/t`
(`ImagePlane.inv`, charts swapped) and the scalings `t ↦ u t` (`u ∈ ℤ_(p)^×`, same charts) are
constructed here; the translations `t ↦ t + e` are the glue `P1Translate`. Disjoint closures of
rational sections force distinct reductions (`isUnit_sub_of_disjoint`), and a normalization
argument moves three such sections to `0, ∞, −16/27`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_(p) → ℚ̄`. -/
def iq (p : ℕ) [Fact p.Prime] : Zloc p →+* Qbar := (algebraMap ℚ Qbar).comp (zlocToRat p)

theorem iq_injective : Function.Injective (iq p) :=
  (algebraMap ℚ Qbar).injective.comp (zlocToRat_injective p)

theorem ev_baseToSections (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) {W : 𝒵.left.Opens}
    (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hz : ptOf z ∈ W) (a : Zloc p) :
    ev z hz (baseToSections 𝒵 W a) = iq p a :=
  congrArg (fun φ : Zloc p →+* Qbar => φ a) (zloc_ringHom_ext ((ev z hz).comp _) (iq p))

theorem res_baseToSections (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) {W W' : 𝒵.left.Opens}
    (h : W' ≤ W) (a : Zloc p) : res h (baseToSections 𝒵 W a) = baseToSections 𝒵 W' a := by
  simp only [res, baseToSections, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-! ## Inversion -/

theorem val_inv {K : Type} [Field K] {X : Scheme.{0}} (ρ : ToP1 X)
    (z : Spec (CommRingCat.of K) ⟶ X) : (ImagePlane.inv ρ).val z = ImagePlane.recip (ρ.val z) :=
  ImagePlane.val_eq_recip (ImagePlane.inv ρ) z

theorem isP1Coordinate_inv {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (h : IsP1Coordinate 𝒵 ρ) : IsP1Coordinate 𝒵 (ImagePlane.inv ρ) :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-! ## Scaling by a unit -/

/-- The scaled coordinate `u · ρ`. -/
def scale (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left) (u : (Zloc p)ˣ) :
    ToP1 𝒵.left where
  U := ρ.U
  V := ρ.V
  cover := ρ.cover
  f := baseToSections 𝒵 ρ.U (u : Zloc p) * ρ.f
  g := baseToSections 𝒵 ρ.V ((u⁻¹ : (Zloc p)ˣ) : Zloc p) * ρ.g
  inv := by
    change res _ (_ * ρ.f) * res _ (_ * ρ.g) = 1
    rw [map_mul, map_mul, res_baseToSections, res_baseToSections]
    have e : res (inf_le_left : ρ.U ⊓ ρ.V ≤ ρ.U) ρ.f * res (inf_le_right : ρ.U ⊓ ρ.V ≤ ρ.V) ρ.g
      = 1 := ρ.inv
    calc baseToSections 𝒵 (ρ.U ⊓ ρ.V) ↑u * res _ ρ.f *
          (baseToSections 𝒵 (ρ.U ⊓ ρ.V) ↑u⁻¹ * res _ ρ.g)
        = baseToSections 𝒵 (ρ.U ⊓ ρ.V) (↑u * ↑u⁻¹) *
            (res (inf_le_left : ρ.U ⊓ ρ.V ≤ ρ.U) ρ.f * res (inf_le_right : ρ.U ⊓ ρ.V ≤ ρ.V) ρ.g) := by
          rw [map_mul]; ring
      _ = 1 := by rw [e, Units.mul_inv, map_one, mul_one]
  basicOpen_f := by
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((u.isUnit).map _),
      inf_eq_right.mpr (Scheme.basicOpen_le _ _), ρ.basicOpen_f]
  basicOpen_g := by
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((u⁻¹.isUnit).map _),
      inf_eq_right.mpr (Scheme.basicOpen_le _ _), ρ.basicOpen_g]

theorem val_scale (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left) (u : (Zloc p)ˣ)
    (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) :
    (scale 𝒵 ρ u).val z = (ρ.val z).map (fun t => iq p u * t) := by
  by_cases hz : ptOf z ∈ ρ.U
  · rw [val_of_mem (scale 𝒵 ρ u) z hz, val_of_mem ρ z hz]
    change OnePoint.some (ev z hz (baseToSections 𝒵 ρ.U ↑u * ρ.f)) = _
    rw [map_mul, ev_baseToSections]
    rfl
  · rw [val_of_not_mem (scale 𝒵 ρ u) z hz, val_of_not_mem ρ z hz]
    rfl

/-- Bijectivity of `X ↦ c · h` when `X ↦ h` is bijective and `c` is a unit. -/
theorem bijective_eval₂_mul {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (h : S)
    (u : Rˣ) (hb : Function.Bijective (eval₂RingHom φ h)) :
    Function.Bijective (eval₂RingHom φ (φ u * h)) := by
  let m : R[X] →+* R[X] := eval₂RingHom C (C (u : R) * X)
  let m' : R[X] →+* R[X] := eval₂RingHom C (C ((u⁻¹ : Rˣ) : R) * X)
  have hcomp : eval₂RingHom φ (φ u * h) = (eval₂RingHom φ h).comp m := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m]
    · simp [m]
  have hmm' : m.comp m' = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp only [m, m', RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_mul,
        eval₂_C, eval₂_X, RingHom.id_apply]
      rw [← mul_assoc, ← C_mul, Units.inv_mul, C_1, one_mul]
  have hm'm : m'.comp m = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp only [m, m', RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_mul,
        eval₂_C, eval₂_X, RingHom.id_apply]
      rw [← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
  have hmb : Function.Bijective m :=
    ⟨Function.LeftInverse.injective (g := m') (fun x => congrArg (fun f => f x) hm'm),
      Function.RightInverse.surjective (g := m') (fun x => congrArg (fun f => f x) hmm')⟩
  rw [hcomp, RingHom.coe_comp]
  exact hb.comp hmb

theorem isP1Coordinate_scale {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (h : IsP1Coordinate 𝒵 ρ) (u : (Zloc p)ˣ) : IsP1Coordinate 𝒵 (scale 𝒵 ρ u) :=
  ⟨h.1, h.2.1, bijective_eval₂_mul _ _ u h.2.2.1, bijective_eval₂_mul _ _ u⁻¹ h.2.2.2⟩

/-! ## Translation (the glue) -/

/-- **Glue (C2-T): translations of `P¹_{ℤ_(p)}`** (chart algebra of `P¹` over `ℤ_(p)`; no
literature). For `ρ : 𝒵 ≅ P¹_{ℤ_(p)}` and `e ∈ ℤ_(p)`, the coordinate `ρ + e` is again an
isomorphism onto `P¹_{ℤ_(p)}`. (Outline: `U' = U`, `f' = f + e`;
`V' = D_V(1 + e g) ∪ D_U(f + e)`, `g'` glued from `g/(1 + e g)` and `1/(f + e)`; `V'` is covered by
the basic opens `D(g') = D_U(f + e)` and `D(1 − e g') = D_V(1 + e g)`, which are affine and generate
the unit ideal, so `V'` is affine; `ℤ_(p)[g'] = Γ(V')` because
`ℤ_(p)[Y, 1/Y] ∩ ℤ_(p)[Y, 1/(1 − eY)] = ℤ_(p)[Y]` (`Y` and `1 − eY` are coprime).) -/
def P1Translate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left),
    IsP1Coordinate 𝒵 ρ → ∀ e : Zloc p, ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ' ∧
      ∀ z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left, ρ'.val z = (ρ.val z).map (fun t => t + iq p e)

/-! ## Disjoint closures force distinct reductions -/

/-- The point of an affine open `W` with prime `ker ψ` lies in the closure of the point of a
`ℚ̄`-point `z` of `W` whose evaluation kernel is contained in `ker ψ`. -/
theorem fromSpec_ker_mem_closure {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    {F : Type} [Field F] (ψ : Γ(X, W) →+* F) (z : Spec (CommRingCat.of Qbar) ⟶ X)
    (hz : ptOf z ∈ W) (hker : ∀ s, ev z hz s = 0 → ψ s = 0) :
    hW.fromSpec ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ ∈ closure {ptOf z} := by
  set w := hW.fromSpec ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ with hwdef
  have hwW : w ∈ W := by
    change w ∈ (W : Set X)
    rw [← hW.range_fromSpec]; exact ⟨_, rfl⟩
  rw [mem_closure_iff]
  intro o ho hwo
  obtain ⟨s, hsle, hws⟩ := hW.exists_basicOpen_le (V := ⟨o, ho⟩) ⟨w, hwo⟩ hwW
  have hs : ψ s ≠ 0 := by
    have h1 : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum Γ(X, W)) ∈
        hW.fromSpec ⁻¹ᵁ X.basicOpen s := hws
    rw [hW.fromSpec_preimage_basicOpen] at h1
    exact fun h0 => h1 (RingHom.mem_ker.mpr h0)
  have hzs : ptOf z ∈ X.basicOpen s := by
    by_contra hn
    exact hs (hker s ((ev_eq_zero_iff z hz s).2 hn))
  exact ⟨ptOf z, hsle hzs, rfl⟩

/-- **Disjoint closures force distinct reductions** (in a polynomial chart `W` of `𝒵`, values
`a, a' ∈ ℤ_(p)`): `a − a'` is a unit. Otherwise the point of `W` over `(p, h − a)` lies in both
closures. -/
theorem isUnit_sub_of_disjoint (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) {W : 𝒵.left.Opens}
    (hW : IsAffineOpen W) (h : Γ(𝒵.left, W))
    (hb : Function.Bijective (eval₂RingHom (baseToSections 𝒵 W) h))
    (z z' : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hz : ptOf z ∈ W) (hz' : ptOf z' ∈ W)
    (a a' : Zloc p) (ha : ev z hz h = iq p a) (ha' : ev z' hz' h = iq p a')
    (hd : Disjoint (closure ({ptOf z} : Set 𝒵.left)) (closure {ptOf z'})) : IsUnit (a - a') := by
  by_contra hnu
  let e : (Zloc p)[X] ≃+* Γ(𝒵.left, W) := RingEquiv.ofBijective _ hb
  let ψ : Zloc p → (Γ(𝒵.left, W) →+* IsLocalRing.ResidueField (Zloc p)) := fun b =>
    (IsLocalRing.residue (Zloc p)).comp ((Polynomial.evalRingHom b).comp e.symm.toRingHom)
  have hres : IsLocalRing.residue (Zloc p) a = IsLocalRing.residue (Zloc p) a' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hnu
  have hψ : ψ a = ψ a' := by
    ext s
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, coe_evalRingHom]
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, hres]
  have hev : ∀ (b : Zloc p) (zz : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hzz : ptOf zz ∈ W),
      ev zz hzz h = iq p b → ∀ P : (Zloc p)[X], ev zz hzz (e P) = iq p (P.eval b) := by
    intro b zz hzz hbz P
    change ev zz hzz (eval₂RingHom (baseToSections 𝒵 W) h P) = _
    rw [coe_eval₂RingHom, Polynomial.hom_eval₂, hbz,
      zloc_ringHom_ext ((ev zz hzz).comp (baseToSections 𝒵 W)) ((iq p).comp (RingHom.id _)),
      ← Polynomial.hom_eval₂]
    rfl
  have hker : ∀ (b : Zloc p) (zz : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (hzz : ptOf zz ∈ W),
      ev zz hzz h = iq p b → ∀ s, ev zz hzz s = 0 → ψ b s = 0 := by
    intro b zz hzz hbz s hs
    obtain ⟨P, rfl⟩ := e.surjective s
    rw [hev b zz hzz hbz P, ← map_zero (iq p)] at hs
    have h0 : P.eval b = 0 := iq_injective hs
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, coe_evalRingHom, h0, map_zero]
  have h1 := fromSpec_ker_mem_closure hW (ψ a) z hz (hker a z hz ha)
  have h2 := fromSpec_ker_mem_closure hW (ψ a') z' hz' (hker a' z' hz' ha')
  have hpt : (⟨RingHom.ker (ψ a'), RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(𝒵.left, W)) =
      ⟨RingHom.ker (ψ a), RingHom.ker_isPrime _⟩ := PrimeSpectrum.ext (by rw [hψ])
  rw [hpt] at h2
  exact Set.disjoint_left.mp hd h1 h2

/-! ## Rational values and the normalization -/

theorem zlocToRat_algebraMap (n : ℤ) : zlocToRat p (algebraMap ℤ (Zloc p) n) = n := by
  unfold zlocToRat
  rw [IsLocalization.lift_eq]
  rfl

/-- A rational number or its inverse lies in `ℤ_(p)`; in the second case the inverse is a
non-unit. -/
theorem zloc_or_inv (r : ℚ) : (∃ e : Zloc p, zlocToRat p e = r) ∨
    (r ≠ 0 ∧ ∃ e : Zloc p, zlocToRat p e = r⁻¹ ∧ ¬ IsUnit e) := by
  have hp : (p : ℕ).Prime := Fact.out
  by_cases hd : (r.den : ℤ) ∈ (pIdeal p).primeCompl
  · left
    let u := (IsLocalization.map_units (Zloc p) (⟨r.den, hd⟩ : (pIdeal p).primeCompl)).unit
    refine ⟨algebraMap ℤ (Zloc p) r.num * ↑u⁻¹, ?_⟩
    rw [map_mul, zlocToRat_algebraMap, map_units_inv]
    change (r.num : ℚ) * (zlocToRat p (algebraMap ℤ (Zloc p) r.den))⁻¹ = r
    rw [zlocToRat_algebraMap, Int.cast_natCast, ← div_eq_mul_inv, Rat.num_div_den]
  · right
    have hd' : (p : ℤ) ∣ r.den := by
      have : (r.den : ℤ) ∈ pIdeal p := by
        simpa [Ideal.primeCompl] using hd
      exact Ideal.mem_span_singleton.mp this
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [Rat.den_zero, Nat.cast_one] at hd'
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd')
    have hnum : r.num ∈ (pIdeal p).primeCompl := by
      intro hmem
      have h1 : (p : ℤ) ∣ r.num := Ideal.mem_span_singleton.mp hmem
      have hcop := r.reduced
      have h2 : p ∣ r.num.natAbs := by
        exact Int.ofNat_dvd_left.mp h1
      have h3 : p ∣ r.den := by exact_mod_cast hd'
      have h4 : p ∣ 1 := by
        have := Nat.dvd_gcd h2 h3
        rwa [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
    refine ⟨hr0, ?_⟩
    let u := (IsLocalization.map_units (Zloc p) (⟨r.num, hnum⟩ : (pIdeal p).primeCompl)).unit
    refine ⟨algebraMap ℤ (Zloc p) r.den * ↑u⁻¹, ?_, ?_⟩
    · rw [map_mul, zlocToRat_algebraMap, map_units_inv]
      change ((r.den : ℤ) : ℚ) * (zlocToRat p (algebraMap ℤ (Zloc p) r.num))⁻¹ = r⁻¹
      rw [zlocToRat_algebraMap, Int.cast_natCast, ← div_eq_mul_inv]
      conv_rhs => rw [← Rat.num_div_den r]
      rw [inv_div]
    · intro hu
      have : IsUnit (algebraMap ℤ (Zloc p) r.den) := by
        have := hu.mul u.isUnit
        rwa [mul_assoc, Units.inv_mul, mul_one] at this
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Zloc p) (pIdeal p)] at this
      exact hd this

theorem iq_apply (e : Zloc p) : iq p e = algebraMap ℚ Qbar (zlocToRat p e) := rfl

theorem rat_shift (r : OnePoint ℚ) (e : Zloc p) :
    (r.map (algebraMap ℚ Qbar)).map (fun t => t + iq p e) =
      (r.map (fun s => s + zlocToRat p e)).map (algebraMap ℚ Qbar) := by
  induction r using OnePoint.rec with
  | infty => rfl
  | coe s => simp [iq_apply]

theorem recip_map_alg (r : OnePoint ℚ) :
    ImagePlane.recip (r.map (algebraMap ℚ Qbar)) = (ImagePlane.recip r).map (algebraMap ℚ Qbar) := by
  induction r using OnePoint.rec with
  | infty => simp [ImagePlane.recip_infty]
  | coe s =>
    rw [OnePoint.map_some, ImagePlane.recip_coe, ImagePlane.recip_coe]
    by_cases hs : s = 0
    · simp [hs]
    · simp [hs]

theorem chart_of_val {K : Type} [Field K] {X : Scheme.{0}} (ρ : ToP1 X)
    (z : Spec (CommRingCat.of K) ⟶ X) (t : K) (h : ρ.val z = OnePoint.some t) :
    ∃ hz : ptOf z ∈ ρ.U, ev z hz ρ.f = t := by
  by_cases hz : ptOf z ∈ ρ.U
  · rw [val_of_mem ρ z hz] at h
    exact ⟨hz, OnePoint.coe_injective h⟩
  · rw [val_of_not_mem ρ z hz] at h
    exact (OnePoint.infty_ne_coe t h).elim

theorem isUnit_of_vals {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (hρ : IsP1Coordinate 𝒵 ρ) (z z' : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (a a' : Zloc p)
    (h : ρ.val z = OnePoint.some (iq p a)) (h' : ρ.val z' = OnePoint.some (iq p a'))
    (hd : Disjoint (closure ({ptOf z} : Set 𝒵.left)) (closure {ptOf z'})) : IsUnit (a - a') := by
  obtain ⟨hz, hza⟩ := chart_of_val ρ z _ h
  obtain ⟨hz', hza'⟩ := chart_of_val ρ z' _ h'
  exact isUnit_sub_of_disjoint 𝒵 hρ.1 ρ.f hρ.2.2.1 z z' hz hz' a a' hza hza' hd

theorem ne_of_disjoint {X : Scheme.{0}} {z z' : Spec (CommRingCat.of Qbar) ⟶ X}
    (hd : Disjoint (closure ({ptOf z} : Set X)) (closure {ptOf z'})) : z ≠ z' := by
  rintro rfl
  exact Set.disjoint_left.mp hd (subset_closure rfl) (subset_closure rfl)

/-- A rational value whose section is disjoint from the section at `∞` is in `ℤ_(p)`. -/
theorem integral_of_disjoint_infty {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))} {ρ : ToP1 𝒵.left}
    (hρ : IsP1Coordinate 𝒵 ρ) (z zi : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left)
    (hi : ρ.val zi = OnePoint.infty) (r : OnePoint ℚ) (hr : ρ.val z = r.map (algebraMap ℚ Qbar))
    (hd : Disjoint (closure ({ptOf z} : Set 𝒵.left)) (closure {ptOf zi})) :
    ∃ α : Zloc p, ρ.val z = OnePoint.some (iq p α) := by
  induction r using OnePoint.rec with
  | infty =>
    exact (ne_of_disjoint hd (val_injective_of_isP1Coordinate hρ z zi (hr.trans hi.symm))).elim
  | coe s =>
    rcases zloc_or_inv (p := p) s with ⟨e, he⟩ | ⟨hs0, e, he, hnu⟩
    · exact ⟨e, by rw [hr, OnePoint.map_some, iq_apply, he]⟩
    · exfalso
      apply hnu
      have h1 : (ImagePlane.inv ρ).val z = OnePoint.some (iq p e) := by
        rw [val_inv, hr, OnePoint.map_some, ImagePlane.recip_coe, if_neg (by simpa using hs0),
          iq_apply, he, map_inv₀]
      have h2 : (ImagePlane.inv ρ).val zi = OnePoint.some (iq p 0) := by
        rw [val_inv, hi, ImagePlane.recip_infty, map_zero]
      simpa using isUnit_of_vals (isP1Coordinate_inv hρ) z zi e 0 h1 h2 hd

/-- Step 1 of the normalization: move a rational section to `∞`, keeping rational values
rational. -/
theorem exists_infty (hTr : P1Translate) {𝒵 : Over (Spec (CommRingCat.of (Zloc p)))}
    {ρ : ToP1 𝒵.left} (hρ : IsP1Coordinate 𝒵 ρ) (zi : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left)
    (b : OnePoint ℚ) (hb : ρ.val zi = b.map (algebraMap ℚ Qbar)) :
    ∃ ρ1 : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ1 ∧ ρ1.val zi = OnePoint.infty ∧
      ∀ (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) (r : OnePoint ℚ),
        ρ.val z = r.map (algebraMap ℚ Qbar) → ∃ r' : OnePoint ℚ,
          ρ1.val z = r'.map (algebraMap ℚ Qbar) := by
  induction b using OnePoint.rec with
  | infty => exact ⟨ρ, hρ, hb, fun z r h => ⟨r, h⟩⟩
  | coe s =>
    rcases zloc_or_inv (p := p) s with ⟨e, he⟩ | ⟨hs0, e, he, -⟩
    · obtain ⟨ρt, hρt, hvt⟩ := hTr p 𝒵 ρ hρ (-e)
      refine ⟨ImagePlane.inv ρt, isP1Coordinate_inv hρt, ?_, ?_⟩
      · rw [val_inv, hvt, hb, OnePoint.map_some, OnePoint.map_some, map_neg, iq_apply, he,
          add_neg_cancel, ImagePlane.recip_coe, if_pos rfl]
      · intro z r h
        exact ⟨_, by rw [val_inv, hvt, h, rat_shift, recip_map_alg]⟩
    · obtain ⟨ρt, hρt, hvt⟩ := hTr p 𝒵 (ImagePlane.inv ρ) (isP1Coordinate_inv hρ) (-e)
      refine ⟨ImagePlane.inv ρt, isP1Coordinate_inv hρt, ?_, ?_⟩
      · rw [val_inv, hvt, val_inv, hb, OnePoint.map_some, ImagePlane.recip_coe,
          if_neg (by simpa using hs0), OnePoint.map_some, map_neg, iq_apply, he, map_inv₀,
          add_neg_cancel, ImagePlane.recip_coe, if_pos rfl]
      · intro z r h
        exact ⟨_, by rw [val_inv, hvt, val_inv, h, recip_map_alg, rat_shift, recip_map_alg]⟩

/-- `−16/27` as a unit of `ℤ_(p)` (`p > 3`). -/
theorem exists_unit_neg_16_27 (hp3 : 3 < p) : ∃ μ : (Zloc p)ˣ, iq p μ = -16 / 27 := by
  have hp : (p : ℕ).Prime := Fact.out
  have h16 : (16 : ℤ) ∈ (pIdeal p).primeCompl := by
    intro hm
    have h1 : (p : ℤ) ∣ 16 := Ideal.mem_span_singleton.mp hm
    have h2 : p ∣ 2 ^ 4 := by exact_mod_cast h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    omega
  have h27 : (27 : ℤ) ∈ (pIdeal p).primeCompl := by
    intro hm
    have h1 : (p : ℤ) ∣ 27 := Ideal.mem_span_singleton.mp hm
    have h2 : p ∣ 3 ^ 3 := by exact_mod_cast h1
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h2)
    omega
  let u16 := (IsLocalization.map_units (Zloc p) (⟨16, h16⟩ : (pIdeal p).primeCompl)).unit
  let u27 := (IsLocalization.map_units (Zloc p) (⟨27, h27⟩ : (pIdeal p).primeCompl)).unit
  refine ⟨-(u16 * u27⁻¹), ?_⟩
  rw [Units.val_neg, map_neg, Units.val_mul, map_mul, map_units_inv, neg_div]
  congr 1
  change iq p (algebraMap ℤ (Zloc p) 16) * (iq p (algebraMap ℤ (Zloc p) 27))⁻¹ = 16 / 27
  rw [iq_apply, iq_apply, zlocToRat_algebraMap, zlocToRat_algebraMap, div_eq_mul_inv]
  norm_num

/-- **`P1ThreePoints` from the translation glue `P1Translate`.** Move the section `z∞` to `∞`
(`exists_infty`); then `z₀` has a value in `ℤ_(p)` (its section is disjoint from `∞`), translate
it to `0`; then `z₁` has a unit value `γ` (disjoint from `0` and `∞`); scale by `(−16/27)/γ`. -/
theorem p1ThreePoints_of (hTr : P1Translate) : P1ThreePoints := by
  intro p _ hp3 𝒵 ρ₀ hρ₀ z₀ zi z₁ a b c ha hb hc d0i d01 di1
  obtain ⟨ρ1, hρ1, hi1, hrat1⟩ := exists_infty hTr hρ₀ zi b hb
  obtain ⟨a1, ha1⟩ := hrat1 z₀ a ha
  obtain ⟨c1, hc1⟩ := hrat1 z₁ c hc
  obtain ⟨α, hα⟩ := integral_of_disjoint_infty hρ1 z₀ zi hi1 a1 ha1 d0i
  obtain ⟨ρ2, hρ2, hv2⟩ := hTr p 𝒵 ρ1 hρ1 (-α)
  have h20 : ρ2.val z₀ = OnePoint.some (iq p 0) := by
    rw [hv2, hα, OnePoint.map_some, map_neg, add_neg_cancel, map_zero]
  have h2i : ρ2.val zi = OnePoint.infty := by rw [hv2, hi1]; rfl
  have h21 : ρ2.val z₁ = (c1.map (fun s => s + zlocToRat p (-α))).map (algebraMap ℚ Qbar) := by
    rw [hv2, hc1, rat_shift]
  obtain ⟨γ, hγ⟩ := integral_of_disjoint_infty hρ2 z₁ zi h2i _ h21 di1.symm
  have hγu : IsUnit γ := by
    simpa using isUnit_of_vals hρ2 z₁ z₀ γ 0 hγ h20 d01.symm
  obtain ⟨μ, hμ⟩ := exists_unit_neg_16_27 hp3
  let u : (Zloc p)ˣ := μ * hγu.unit⁻¹
  refine ⟨scale 𝒵 ρ2 u, isP1Coordinate_scale hρ2 u, ?_, ?_, ?_⟩
  · rw [val_scale, h20, OnePoint.map_some, map_zero, mul_zero]
  · rw [val_scale, h2i]; rfl
  · rw [val_scale, hγ, OnePoint.map_some, ← map_mul]
    congr 1
    rw [← hμ]
    congr 1
    show (↑(μ * hγu.unit⁻¹) : Zloc p) * γ = ↑μ
    rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

end MCRQuot

namespace MCRQuot

open MCRGlue ModelGlue

/-- **`ModelCoordinateResidue` with `P1ThreePoints` replaced by the translation glue
`P1Translate`** (the composite of `modelCoordinateResidue_of_mcrQuot` and `p1ThreePoints_of`). -/
theorem modelCoordinateResidue_of_mcrQuot' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (gB : GenericQuotientP1)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hO : GQuotientPointOrbits)
    (hI : CMStabInvolution) (hS : StabFixesClosure) (hC : QbarPointsConjugate)
    (hTr : P1Translate) : ModelCoordinateResidue :=
  modelCoordinateResidue_of_mcrQuot hAF hQE hTS hP1 hFix hCyc hT gB hfix hcnt hO hI hS hC
    (p1ThreePoints_of hTr)

/-- **Glue C2 from T5, glue A and the translation glue.** -/
theorem coordinateFromSections_of' (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hTr : P1Translate) : CoordinateFromSections :=
  coordinateFromSections_of hA hT (p1ThreePoints_of hTr)

/-- **Main composite: `ModelCoordinateResidue` with none of mcr-glue's glue Props A, B, C1, C2**:
from the leaves L1-L6 of mcr-glue, the kernel's textbook leaf `TorsionStructure` (T5), and the
smaller glue of this task: (A-fix) `FibreAutFixFinite`, (A-count) `TwistClassCard`,
(B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1a) `GQuotientPointOrbits`,
(C1b) `CMStabInvolution`, (C1c) `StabFixesClosure`, (C1d) `QbarPointsConjugate`,
(C2-T) `P1Translate`. -/
theorem modelCoordinateResidue_of_mcrQuot'' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hD : QuotientDescendsQ)
    (hB : ToP1BijIsCoordinateQ) (hO : GQuotientPointOrbits) (hI : CMStabInvolution)
    (hS : StabFixesClosure) (hC : QbarPointsConjugate) (hTr : P1Translate) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_of_mcrQuot' hAF hQE hTS hP1 hFix hCyc hT
    (genericQuotientP1_of (fibreAutTame_of hT hfix hcnt) hT hTS hD hB) hfix hcnt hO hI hS hC hTr

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 10: proofs of some of the new glue Props
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open scoped Pointwise

/-! ## (C1a) `GQuotientPointOrbits`, proved -/

/-- **(C1a) proved: the points over a point of an SGA 1 quotient form one orbit.** On an affine
`W ⊆ Z` with `U = q⁻¹W`, the primes of `x, x'` lie over the same prime of `Γ(Z, W) = Γ(X, U)^G`
(`comap_primeIdealOf_appLE`), so they differ by `g ∈ G` (`exists_smul_of_under_eq`), and the
prime of `g x` is the `g`-translate of the prime of `x`. -/
theorem gQuotientPointOrbits : GQuotientPointOrbits := by
  intro X Z G q hfin hq x x' hxx
  have hq' := hq
  obtain ⟨hinv, haff, hsec⟩ := hq
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hxW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
  set U := q ⁻¹ᵁ W with hUdef
  have hU : IsAffineOpen U := hW.preimage q
  have hx : x ∈ U := hxW
  have hx' : x' ∈ U := by
    change q x' ∈ W
    rw [← hxx]; exact hxW
  letI : MulSemiringAction G Γ(X, U) := secAction hinv W
  letI : Algebra Γ(Z, W) Γ(X, U) := (q.app W).hom.toAlgebra
  haveI : SMulCommClass G Γ(Z, W) Γ(X, U) := by
    constructor
    intro g a b
    change secMap _ _ W (q.app W a * b) = q.app W a * secMap _ _ W b
    rw [map_mul, secMap_app]
  haveI : Algebra.IsInvariant Γ(Z, W) Γ(X, U) G := by
    constructor
    intro b hb
    have hmem : b ∈ Set.range (q.app W) := by
      rw [(hsec W hW).2]
      intro g hg
      have := hb ⟨g⁻¹, G.inv_mem hg⟩
      change secMap _ _ W b = b at this
      rw [secMap_congr (f' := g.asIso.hom) (by simp) _ (hinv g hg)] at this
      exact this
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  have hcomap : ∀ (u : X) (hu : u ∈ U),
      (hU.primeIdealOf ⟨u, hu⟩).asIdeal.under Γ(Z, W) = (hW.primeIdealOf ⟨q u, hu⟩).asIdeal := by
    intro u hu
    have e := IsAffineOpen.comap_primeIdealOf_appLE (f := q) W hW U hU le_rfl hu
    rw [← e]
    change Ideal.comap (q.app W).hom _ = Ideal.comap (q.appLE W U le_rfl).hom _
    rw [Scheme.Hom.app_eq_appLE]
  have hunder : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.under Γ(Z, W) =
      (hU.primeIdealOf ⟨x', hx'⟩).asIdeal.under Γ(Z, W) := by
    rw [hcomap, hcomap]
    congr 3
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq Γ(Z, W) Γ(X, U) G _ _ hunder
  have hgx : (g : Aut X).asIso.hom x ∈ U := by
    change q ((g : Aut X).asIso.hom x) ∈ W
    rw [← Scheme.Hom.comp_apply, hinv g g.2]; exact hxW
  have e3 := IsAffineOpen.comap_primeIdealOf_appLE (f := (g : Aut X).asIso.hom) U hU U hU
    (preimage_le_of_comp_eq (hinv g g.2) W) hx
  have hpr : hU.primeIdealOf ⟨x', hx'⟩ = hU.primeIdealOf ⟨(g : Aut X).asIso.hom x, hgx⟩ := by
    apply PrimeSpectrum.ext
    rw [hg, ← e3]
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    change secMap _ _ W b ∈ _ ↔ _
    rw [secMap_congr (f' := (g : Aut X).asIso.hom) (by simp) _ (hinv g g.2)]
    rfl
  have e4 := congrArg hU.fromSpec hpr
  rw [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at e4
  have e5 : x' = (g : Aut X).asIso.hom x := e4
  refine ⟨(g : Aut X)⁻¹, G.inv_mem g.2, ?_⟩
  simp only [Aut.inv_asIso, Iso.symm_hom]
  rw [e5, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-! ## (C1d) `QbarPointsConjugate`, proved -/

/-- Two embeddings of a field into `ℚ̄` differ by an automorphism of `ℚ̄` (`AlgHom.liftNormal`). -/
theorem exists_algEquiv_comp_eq {K : Type} [Field K] (f1 f2 : K →+* Qbar) :
    ∃ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ k, f2 k = σ (f1 k) := by
  have : CharZero K := f1.charZero
  let _ : Algebra ℚ K := DivisionRing.toRatAlgebra
  let f1' : K →ₐ[ℚ] Qbar := f1.toRatAlgHom
  let f2' : K →ₐ[ℚ] Qbar := f2.toRatAlgHom
  let e1 := AlgEquiv.ofInjectiveField f1'
  let e2 := AlgEquiv.ofInjectiveField f2'
  let χ : f1'.fieldRange →ₐ[ℚ] f2'.fieldRange := e2.toAlgHom.comp e1.symm.toAlgHom
  refine ⟨AlgEquiv.ofBijective (χ.liftNormal Qbar)
    (Algebra.IsAlgebraic.algHom_bijective _), fun k => ?_⟩
  have h := AlgHom.liftNormal_commutes χ Qbar (e1 k)
  have h1 : algebraMap f1'.fieldRange Qbar (e1 k) = f1 k := rfl
  have h2 : χ (e1 k) = e2 k := by
    show e2 (e1.symm (e1 k)) = e2 k
    rw [AlgEquiv.symm_apply_apply]
  rw [h1, h2] at h
  exact h.symm

/-- **(C1d) proved: two `ℚ̄`-points with the same underlying point are Galois conjugate.** -/
theorem qbarPointsConjugate : QbarPointsConjugate := by
  intro X y y' h
  set S := Scheme.SpecToEquivOfField Qbar X with hS
  have e : (S y').1 = (S y).1 := h.symm
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_eq
    ((X.residueFieldCongr e).hom ≫ (S y).2).hom (S y').2.hom
  refine ⟨σ, S.injective ?_⟩
  rw [specToEquivOfField_comp, Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨e, ?_⟩
  ext k
  exact hσ k

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 11: (A-count) `TwistClassCard`, proved from T5
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- The normalizer fact of the kernel (`NormO.normalizerFinite`) with its explicit set
`NormO.T = {1, i, j, ij}` (the same proof). -/
theorem normalizer_T (u : Bˣ) (hu : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) :
    ∃ t ∈ NormO.T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B) := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((NormO.sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : NormO.IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ :=
    NormO.descent _ (NormO.sc _ hm0 * u) n hu0 rfl ((NormO.isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((NormO.sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem ncard_T_le : (NormO.T : Set Bˣ).ncard ≤ 4 := by
  simp only [NormO.T]
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
  refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
  simp

/-- **`AutOInnerFinite` with a cardinality bound** (the kernel's
`AutOExt.autOInnerFinite_of_normalizer`, same proof, for `NormO.T`): every automorphism of `𝒪` is,
up to conjugation by a unit, one of at most 4. -/
theorem autOInnerCard : ∃ T' : Set (O ≃+* O), T'.Finite ∧ T'.ncard ≤ 4 ∧
    ∀ α : O ≃+* O, ∃ t ∈ T', ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O) := by
  classical
  let T := (NormO.T : Set Bˣ)
  have hT : T.Finite := NormO.T_finite
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hinj : Set.InjOn f T' := by
    intro β₁ h₁ β₂ h₂ heq
    apply RingEquiv.ext; intro a
    apply Subtype.ext
    have e1 := (hf β₁ h₁).2 a
    have e2 := (hf β₂ h₂).2 a
    rw [heq] at e1
    exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  have hmaps : Set.MapsTo f T' T := fun β hβ => (hf β hβ).1
  have hT' : T'.Finite := Set.Finite.of_finite_image (hT.subset (hmaps.image_subset)) hinj
  refine ⟨T', hT', (Set.ncard_le_ncard_of_injOn f hmaps hinj hT).trans ncard_T_le, fun α => ?_⟩
  obtain ⟨u, hu⟩ := AutOExt.conj_of_skolem α
  have hback : ∀ b : B, AutOExt.extFun α.symm (AutOExt.extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (AutOExt.extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, AutOExt.extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show AutOExt.extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, AutOExt.extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := normalizer_T u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← AutOExt.extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (AutOExt.conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact AutOExt.key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

/-- **(A-count) proved from T5: a twist class has at most `4 · 81 = 324` isomorphism classes.** -/
theorem twistClassCard (hT : ObjBridge.TorsionStructure) : TwistClassCard := by
  classical
  intro P
  obtain ⟨T', hT'fin, hT'card, hT'⟩ := autOInnerCard
  haveI : Fintype T' := hT'fin.fintype
  set S := {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧ TwistEq P Q} with hSdef
  let S' : T' → (Fin 4 → ZMod 3) → Set (M3 Qbar) := fun t c =>
    {m | ∃ e : Level3 (P.q.twist (t : O ≃+* O)),
      (∀ a, e.eta a = (P.e.twist (t : O ≃+* O)).eta (a * liftO c)) ∧
      m = M3.mk ⟨P.A, P.surface, P.q.twist (t : O ≃+* O), e⟩}
  have hsub : ∀ t c, (S' t c).Subsingleton := by
    rintro t c _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have : e = e' := Level3.ext' (DFunLike.ext _ _ fun a => (he a).trans (he' a).symm)
    rw [this]
  let F : T' × (Fin 4 → ZMod 3) → M3 Qbar := fun tc =>
    if h : (S' tc.1 tc.2).Nonempty then h.some else M3.mk P
  have hcover : S ⊆ Set.range F := by
    rintro m ⟨Q, rfl, α, ⟨f⟩⟩
    obtain ⟨t, ht, v, hv⟩ := hT' α
    let f' : QMIso (P.q.twist t) Q.q := (conjUnitIso P.q t α v hv).trans f
    let e' : Level3 (P.q.twist t) := transportLevel f'.symm Q.e
    have hiso : Q.Iso ⟨P.A, P.surface, P.q.twist t, e'⟩ := QML3.isoTransport Q P.surface f'.symm
    obtain ⟨u₀, v₀, -, hlin⟩ := Level3.torsor hT (P.twist t) e'
    obtain ⟨c, k, hk⟩ := exists_liftO_congr u₀
    have hmem : M3.mk Q ∈ S' ⟨t, ht⟩ c := by
      refine ⟨e', fun a => (hlin a).trans ?_, Quotient.sound ⟨hiso⟩⟩
      change (P.e.twist t).eta (a * u₀) = (P.e.twist t).eta (a * liftO c)
      rw [(P.e.twist t).eq_iff]
      refine ⟨a * k, ?_⟩
      calc a * u₀ - a * liftO c = a * (u₀ - liftO c) := by noncomm_ring
        _ = a * (3 * k) := by rw [hk]
        _ = 3 * (a * k) := by noncomm_ring
    refine ⟨(⟨t, ht⟩, c), ?_⟩
    have hne : (S' ⟨t, ht⟩ c).Nonempty := ⟨_, hmem⟩
    simp only [F, hne, dite_true]
    exact hsub ⟨t, ht⟩ c hne.some_mem hmem
  have hfinR : (Set.range F).Finite := Set.finite_range F
  refine ⟨hfinR.subset hcover, ?_⟩
  calc S.ncard ≤ (Set.range F).ncard := Set.ncard_le_ncard hcover hfinR
    _ ≤ Nat.card (T' × (Fin 4 → ZMod 3)) := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le Set.finite_univ
    _ = T'.ncard * 81 := by
      rw [Nat.card_prod, Nat.card_coe_set_eq]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    _ ≤ 4 * 81 := Nat.mul_le_mul_right _ hT'card
    _ = 324 := by norm_num

/-- **Glue A from T5 and (A-fix) alone.** -/
theorem fibreAutTame_of' (hT : ObjBridge.TorsionStructure) (hfix : FibreAutFixFinite) :
    FibreAutTame :=
  fibreAutTame_of hT hfix (twistClassCard hT)

/-- **Glue C1 from glue A, (A-fix), (C1b), (C1c)** ((C1a), (C1d) proved). -/
theorem cMSectionsDisjoint_of' (hA : FibreAutTame) (hfix : FibreAutFixFinite)
    (hI : CMStabInvolution) (hS : StabFixesClosure) : CMSectionsDisjoint :=
  cMSectionsDisjoint_of hA hfix gQuotientPointOrbits hI hS qbarPointsConjugate

/-- **Main composite (final form): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaf T5 and six glue Props of this task**: (A-fix) `FibreAutFixFinite`, (B-desc)
`QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b) `CMStabInvolution`, (C1c)
`StabFixesClosure`, (C2-T) `P1Translate`. (A-count), (C1a), (C1d) are proved. -/
theorem modelCoordinateResidue_final (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) (hS : StabFixesClosure) (hTr : P1Translate) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_of_mcrQuot'' hAF hQE hTS hP1 hFix hCyc hT hfix (twistClassCard hT) hD hB
    gQuotientPointOrbits hI hS qbarPointsConjugate hTr

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 12: translations of a coordinate (towards `P1Translate`)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV MCRGlue LeafQM.AV.Pin
open TopologicalSpace Opposite

section Translate

variable {X : Scheme.{0}}

theorem res_inv_mul {O O' : X.Opens} (h : O' ≤ O) (u : (Γ(X, O))ˣ) :
    res h (↑u⁻¹ : Γ(X, O)) * res h (u : Γ(X, O)) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem res_res' {O O' O'' : X.Opens} (h : O' ≤ O) (h' : O'' ≤ O') (h'' : O'' ≤ O)
    (s : Γ(X, O)) : res h' (res h s) = res h'' s := res_res h h' s

theorem eq_of_mul_eq_one {R : Type*} [CommRing R] {a b c : R} (ha : a * c = 1) (hb : b * c = 1) :
    a = b := by
  calc a = a * (c * b) := by rw [mul_comm c b, hb, mul_one]
    _ = (a * c) * b := by ring
    _ = b := by rw [ha, one_mul]

/-- Outside the basic open of `s`, `1 + a s` is a unit. -/
theorem mem_basicOpen_one_add {O : X.Opens} (a s : Γ(X, O)) {x : X} (hx : x ∈ O)
    (hs : x ∉ X.basicOpen s) : x ∈ X.basicOpen (1 + a * s) := by
  rw [Scheme.mem_basicOpen _ _ x hx] at hs ⊢
  rw [map_add, map_one, map_mul]
  apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
  rw [show (1 : X.presheaf.stalk x) - (1 + _ * _) = -(X.presheaf.germ O x hx a *
    X.presheaf.germ O x hx s) by ring, ← IsLocalRing.mem_maximalIdeal]
  refine neg_mem (Ideal.mul_mem_left _ _ ?_)
  rw [IsLocalRing.mem_maximalIdeal]
  exact hs

variable (ρ : ToP1 X) (E : Γ(X, ⊤))

/-- `f + E` on `U`. -/
def tF : Γ(X, ρ.U) := ρ.f + res le_top E
/-- `1 + E g` on `V`. -/
def tG : Γ(X, ρ.V) := 1 + res le_top E * ρ.g
/-- `D_U(f + E)`. -/
def tDU : X.Opens := X.basicOpen (tF ρ E)
/-- `D_V(1 + E g)`. -/
def tDV : X.Opens := X.basicOpen (tG ρ E)

theorem tDU_le : tDU ρ E ≤ ρ.U := Scheme.basicOpen_le _ _
theorem tDV_le : tDV ρ E ≤ ρ.V := Scheme.basicOpen_le _ _

/-- The unit `f + E` on `D_U(f + E)`. -/
def uF : (Γ(X, tDU ρ E))ˣ := (X.toRingedSpace.isUnit_res_basicOpen (tF ρ E)).unit
/-- The unit `1 + E g` on `D_V(1 + E g)`. -/
def uG : (Γ(X, tDV ρ E))ˣ := (X.toRingedSpace.isUnit_res_basicOpen (tG ρ E)).unit

theorem uF_val : (uF ρ E : Γ(X, tDU ρ E)) = res (tDU_le ρ E) (tF ρ E) := rfl
theorem uG_val : (uG ρ E : Γ(X, tDV ρ E)) = res (tDV_le ρ E) (tG ρ E) := rfl

/-- `g / (1 + E g)` on `D_V(1 + E g)`. -/
def tS1 : Γ(X, tDV ρ E) := res (tDV_le ρ E) ρ.g * ↑(uG ρ E)⁻¹
/-- `1 / (f + E)` on `D_U(f + E)`. -/
def tS2 : Γ(X, tDU ρ E) := ↑(uF ρ E)⁻¹

/-- On `U ⊓ V`, `g · (f + E) = 1 + E g`. -/
theorem g_mul_tF {W : X.Opens} (hW : W ≤ ρ.U ⊓ ρ.V) :
    res (hW.trans inf_le_right) ρ.g * res (hW.trans inf_le_left) (tF ρ E) =
      res (hW.trans inf_le_right) (tG ρ E) := by
  have hinv := congrArg (res (hW : W ≤ ρ.U ⊓ ρ.V)) ρ.inv
  rw [map_mul, map_one, res_res, res_res] at hinv
  simp only [tF, tG, map_add, map_mul, map_one, res_res]
  rw [mul_add, mul_comm (res _ ρ.g) (res _ ρ.f), hinv, mul_comm]

theorem tS_compat :
    res (inf_le_left : tDV ρ E ⊓ tDU ρ E ≤ tDV ρ E) (tS1 ρ E) =
      res (inf_le_right : tDV ρ E ⊓ tDU ρ E ≤ tDU ρ E) (tS2 ρ E) := by
  have hW : tDV ρ E ⊓ tDU ρ E ≤ ρ.U ⊓ ρ.V :=
    le_inf (inf_le_right.trans (tDU_le ρ E)) (inf_le_left.trans (tDV_le ρ E))
  let c := res (hW.trans inf_le_left) (tF ρ E)
  refine eq_of_mul_eq_one (c := c) ?_ ?_
  · have h1 := g_mul_tF ρ E hW
    simp only [tS1, map_mul, c, res_res]
    rw [mul_assoc, mul_comm (res _ (↑(uG ρ E)⁻¹ : Γ(X, tDV ρ E))), ← mul_assoc, h1]
    have := res_inv_mul (inf_le_left : tDV ρ E ⊓ tDU ρ E ≤ tDV ρ E) (uG ρ E)
    rw [uG_val, res_res] at this
    rw [mul_comm]; exact this
  · have := res_inv_mul (inf_le_right : tDV ρ E ⊓ tDU ρ E ≤ tDU ρ E) (uF ρ E)
    rw [uF_val, res_res] at this
    exact this

/-- `g' = 1/(t + E)` on `V' = D_V(1 + E g) ∪ D_U(f + E)`, glued. -/
def tg : Γ(X, tDV ρ E ⊔ tDU ρ E) :=
  (X.sheaf.objSupIsoProdEqLocus (tDV ρ E) (tDU ρ E)).inv ⟨(tS1 ρ E, tS2 ρ E), tS_compat ρ E⟩

theorem tg_res_DV : res (le_sup_left : tDV ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E) = tS1 ρ E :=
  TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf _ _ _

theorem tg_res_DU : res (le_sup_right : tDU ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E) = tS2 ρ E :=
  TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf _ _ _

omit ρ E in
theorem basicOpen_res_of_le {O O' : X.Opens} (h : O' ≤ O) (s : Γ(X, O)) :
    X.basicOpen (res h s) = O' ⊓ X.basicOpen s := Scheme.basicOpen_res X s (homOfLE h).op

theorem U_inf_tDV_le : ρ.U ⊓ tDV ρ E ≤ tDU ρ E := by
  intro x hx
  have hW : ρ.U ⊓ tDV ρ E ≤ ρ.U ⊓ ρ.V := inf_le_inf_left _ (tDV_le ρ E)
  have h1 := g_mul_tF ρ E hW
  have h2 : x ∈ X.basicOpen (res (hW.trans inf_le_right) (tG ρ E)) := by
    rw [basicOpen_res_of_le]; exact ⟨hx, hx.2⟩
  rw [← h1, Scheme.basicOpen_mul] at h2
  have h3 := h2.2
  rw [basicOpen_res_of_le] at h3
  exact h3.2

theorem tF_basicOpen : X.basicOpen (tF ρ E) = ρ.U ⊓ (tDV ρ E ⊔ tDU ρ E) := by
  apply le_antisymm
  · exact le_inf (tDU_le ρ E) le_sup_right
  · rintro x ⟨hU, hx⟩
    rcases hx with h | h
    · exact U_inf_tDV_le ρ E ⟨hU, h⟩
    · exact h

/-- **The translated coordinate `ρ + E`.** -/
def translate : ToP1 X where
  U := ρ.U
  V := tDV ρ E ⊔ tDU ρ E
  cover := by
    apply eq_top_iff.mpr
    intro x _
    by_cases hU : x ∈ ρ.U
    · exact Or.inl hU
    · have hV : x ∈ ρ.V := mem_V_of_not_mem_U ρ hU
      have hg : x ∉ X.basicOpen ρ.g := by rw [ρ.basicOpen_g]; exact fun h => hU h.1
      exact Or.inr (Or.inl (mem_basicOpen_one_add (res le_top E) ρ.g hV hg))
  f := tF ρ E
  g := tg ρ E
  inv := by
    refine X.sheaf.eq_of_locally_eq₂ (homOfLE (le_inf inf_le_left (inf_le_right.trans le_sup_left) :
        ρ.U ⊓ tDV ρ E ≤ ρ.U ⊓ (tDV ρ E ⊔ tDU ρ E)))
      (homOfLE (le_inf (tDU_le ρ E) le_sup_right : tDU ρ E ≤ ρ.U ⊓ (tDV ρ E ⊔ tDU ρ E)))
      ?_ _ _ ?_ ?_
    · rintro x ⟨hU, hx⟩
      rcases hx with h | h
      · exact Or.inl ⟨hU, h⟩
      · exact Or.inr h
    · change res _ (res _ (tF ρ E) * res _ (tg ρ E)) = res _ 1
      rw [map_mul, map_one, res_res, res_res]
      rw [show res (_ : ρ.U ⊓ tDV ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E) =
          res (inf_le_right : ρ.U ⊓ tDV ρ E ≤ tDV ρ E) (res le_sup_left (tg ρ E)) from
          (res_res _ _ _).symm, tg_res_DV]
      simp only [tS1, map_mul, res_res]
      have h1 := g_mul_tF ρ E (W := ρ.U ⊓ tDV ρ E) (inf_le_inf_left _ (tDV_le ρ E))
      rw [← mul_assoc, mul_comm (res _ (tF ρ E)), h1]
      have := res_inv_mul (inf_le_right : ρ.U ⊓ tDV ρ E ≤ tDV ρ E) (uG ρ E)
      rw [uG_val, res_res] at this
      rw [mul_comm]; exact this
    · change res _ (res _ (tF ρ E) * res _ (tg ρ E)) = res _ 1
      rw [map_mul, map_one, res_res, res_res, tg_res_DU, tS2,
        show res (_ : tDU ρ E ≤ ρ.U) (tF ρ E) = (uF ρ E : Γ(X, tDU ρ E)) from rfl,
        Units.mul_inv]
  basicOpen_f := tF_basicOpen ρ E
  basicOpen_g := by
    rw [← tF_basicOpen]
    apply le_antisymm
    · intro x hx
      have hxV : x ∈ tDV ρ E ⊔ tDU ρ E := Scheme.basicOpen_le _ _ hx
      rcases hxV with h | h
      · have h2 : x ∈ X.basicOpen (res (le_sup_left : tDV ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E)) := by
          rw [basicOpen_res_of_le]; exact ⟨h, hx⟩
        rw [tg_res_DV, tS1, Scheme.basicOpen_mul, basicOpen_res_of_le] at h2
        have h3 : x ∈ X.basicOpen ρ.g := h2.1.2
        rw [ρ.basicOpen_g] at h3
        exact U_inf_tDV_le ρ E ⟨h3.1, h⟩
      · exact h
    · intro x hx
      have h2 : X.basicOpen (res (le_sup_right : tDU ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E)) =
          tDU ρ E := by
        rw [tg_res_DU, tS2]; exact Scheme.basicOpen_of_isUnit _ (Units.isUnit _)
      have h3 : x ∈ X.basicOpen (res (le_sup_right : tDU ρ E ≤ tDV ρ E ⊔ tDU ρ E) (tg ρ E)) := by
        rw [h2]; exact hx
      rw [basicOpen_res_of_le] at h3
      exact h3.2

end Translate

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 13: (C1c) `StabFixesClosure` proved (the fixed locus as a closed subscheme)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- The residue field map of a closed immersion is an isomorphism (the stalk map is surjective). -/
theorem isIso_residueFieldMap_of_closedImm {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  have hs : Function.Surjective (f.residueFieldMap x) := by
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    refine ⟨Y.residue (f x) c, ?_⟩
    rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  have hb : Function.Bijective (f.residueFieldMap x) := ⟨(f.residueFieldMap x).hom.injective, hs⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

/-- A field point whose point lies in the range of a closed immersion factors through it. -/
theorem exists_factor_of_mem_range_closedImm {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Y) (ht : ptOf t ∈ Set.range f) :
    ∃ t' : Spec (CommRingCat.of K) ⟶ X, t' ≫ f = t := by
  obtain ⟨e, he⟩ := ht
  have := isIso_residueFieldMap_of_closedImm f e
  set xf := Scheme.SpecToEquivOfField K Y t with hxf
  have ht' : t = Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1 :=
    ((Scheme.SpecToEquivOfField K Y).symm_apply_apply t).symm
  have h1 : Y.fromSpecResidueField (f e) =
      Spec.map (inv (f.residueFieldMap e)) ≫ X.fromSpecResidueField e ≫ f := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  refine ⟨Spec.map xf.2 ≫ Spec.map (Y.residueFieldCongr he).hom ≫
    Spec.map (inv (f.residueFieldMap e)) ≫ X.fromSpecResidueField e, ?_⟩
  refine Eq.trans ?_ ht'.symm
  simp only [Category.assoc]
  rw [← h1, Scheme.residueFieldCongr_fromSpecResidueField]

/-- **The fixed locus is closed and contains the closure of a fixed point.** For an automorphism
`h` over `S` of a separated `S`-scheme `X` and a field point `y` with `y ≫ h = y`, every field point
whose point lies in the closure of the point of `y` is fixed by `h`. Proof: the equalizer of `h`
and `id` in `Over S` is a closed subscheme (`isClosedImmersion_equalizer_ι_left`, Stacks 01KM);
`y` factors through it, so its closed range contains the closure; a field point with point in the
range of a closed immersion factors through it (residue fields agree). -/
theorem fixes_closure_of_separated {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom]
    (h : X.left ≅ X.left) (hh : h.hom ≫ X.hom = X.hom) {K₀ : Type} [Field K₀]
    (y : Spec (CommRingCat.of K₀) ⟶ X.left) (hy : y ≫ h.hom = y) {K : Type} [Field K]
    (t : Spec (CommRingCat.of K) ⟶ X.left) (ht : ptOf t ∈ closure {ptOf y}) : t ≫ h.hom = t := by
  let f : X ⟶ X := Over.homMk h.hom hh
  let g : X ⟶ X := 𝟙 X
  let ι := (equalizer.ι f g).left
  have hι : ι ≫ h.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f g)
    simpa [f, g, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hyr : ptOf y ∈ Set.range ι := by
    let y' : Over.mk (y ≫ X.hom) ⟶ X := Over.homMk y rfl
    have hc : y' ≫ f = y' ≫ g := by
      ext1; simpa [f, g, y'] using hy
    refine ⟨(equalizer.lift y' hc).left (IsLocalRing.closedPoint K₀), ?_⟩
    show ((equalizer.lift y' hc).left ≫ (equalizer.ι f g).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have htr : ptOf t ∈ Set.range ι :=
    (closure_minimal (Set.singleton_subset_iff.2 hyr) hcl) ht
  obtain ⟨t', rfl⟩ := exists_factor_of_mem_range_closedImm ι t htr
  rw [Category.assoc, hι]

/-- **(C1c) `StabFixesClosure` proved.** Only the separatedness of `𝒴 → Spec ℤ_(p)` (from
properness) is used; smoothness is not needed, and the fixed field points over the closure need no
spreading out (EGA IV 8.13.1 is not used). -/
theorem stabFixesClosure : StabFixesClosure := by
  intro p _ 𝒴 hP _ h hh y hy K _ t ht
  exact fixes_closure_of_separated 𝒴 h.asIso hh y hy t ht

/-- **Glue C1 from glue A, (A-fix), (C1b)** ((C1a), (C1c), (C1d) proved). -/
theorem cMSectionsDisjoint_of'' (hA : FibreAutTame) (hfix : FibreAutFixFinite)
    (hI : CMStabInvolution) : CMSectionsDisjoint :=
  cMSectionsDisjoint_of' hA hfix hI stabFixesClosure

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 14: (C2-T) `P1Translate` proved (translations of `P¹_{ℤ_(p)}` by charts)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

variable {p : ℕ} [Fact p.Prime]

/-- Bijectivity of `X ↦ h + c` when `X ↦ h` is bijective. -/
theorem bijective_eval₂_add {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (h : S)
    (c : R) (hb : Function.Bijective (eval₂RingHom φ h)) :
    Function.Bijective (eval₂RingHom φ (h + φ c)) := by
  let m : R[X] →+* R[X] := eval₂RingHom C (X + C c)
  let m' : R[X] →+* R[X] := eval₂RingHom C (X - C c)
  have hcomp : eval₂RingHom φ (h + φ c) = (eval₂RingHom φ h).comp m := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m]
    · simp [m]
  have hmm' : m.comp m' = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp [m, m']
  have hm'm : m'.comp m = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [m, m']
    · simp [m, m']
  have hmb : Function.Bijective m :=
    ⟨Function.LeftInverse.injective (g := m') (fun x => congrArg (fun f => f x) hm'm),
      Function.RightInverse.surjective (g := m') (fun x => congrArg (fun f => f x) hmm')⟩
  rw [hcomp, RingHom.coe_comp]
  exact hb.comp hmb

section P1T

variable (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (ρ : ToP1 𝒵.left) (e : Zloc p)

/-- The constant `e` as a global section. -/
abbrev cE : Γ(𝒵.left, ⊤) := baseToSections 𝒵 ⊤ e

theorem res_cE {W : 𝒵.left.Opens} (h : W ≤ ⊤) : res h (cE 𝒵 e) = baseToSections 𝒵 W e :=
  res_baseToSections 𝒵 h e

theorem tF_eq : tF ρ (cE 𝒵 e) = ρ.f + baseToSections 𝒵 ρ.U e := by
  rw [tF, res_cE]

/-- The section `h' = 1 − e g'` on `V'`. -/
def tH : Γ(𝒵.left, tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)) :=
  1 - baseToSections 𝒵 _ e * tg ρ (cE 𝒵 e)

theorem basicOpen_tg : 𝒵.left.basicOpen (tg ρ (cE 𝒵 e)) = tDU ρ (cE 𝒵 e) :=
  (translate ρ (cE 𝒵 e)).basicOpen_g.trans (tF_basicOpen ρ (cE 𝒵 e)).symm

theorem res_tH_DV : res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) * (uG ρ (cE 𝒵 e) : _) = 1 := by
  have hu := Units.inv_mul (uG ρ (cE 𝒵 e))
  have huval : (uG ρ (cE 𝒵 e) : Γ(𝒵.left, tDV ρ (cE 𝒵 e))) =
      1 + baseToSections 𝒵 _ e * res (tDV_le ρ (cE 𝒵 e)) ρ.g := by
    rw [uG_val, tG, map_add, map_one, map_mul, res_res, res_cE]
  rw [tH, map_sub, map_one, map_mul, res_baseToSections, tg_res_DV, tS1]
  linear_combination huval - baseToSections 𝒵 (tDV ρ (cE 𝒵 e)) e *
    res (tDV_le ρ (cE 𝒵 e)) ρ.g * hu

theorem res_tH_DU : res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) =
    res (tDU_le ρ (cE 𝒵 e)) ρ.f * (tS2 ρ (cE 𝒵 e)) := by
  have hu := Units.mul_inv (uF ρ (cE 𝒵 e))
  have huval : (uF ρ (cE 𝒵 e) : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) =
      res (tDU_le ρ (cE 𝒵 e)) ρ.f + baseToSections 𝒵 _ e := by
    rw [uF_val, tF_eq, map_add, res_baseToSections]
  rw [tH, map_sub, map_one, map_mul, res_baseToSections, tg_res_DU, tS2]
  linear_combination (-1 : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) * hu +
    (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) * huval

theorem basicOpen_tH : 𝒵.left.basicOpen (tH 𝒵 ρ e) = tDV ρ (cE 𝒵 e) := by
  apply le_antisymm
  · intro x hx
    have hxV : x ∈ tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e) := Scheme.basicOpen_le _ _ hx
    rcases hxV with h | h
    · exact h
    · have h2 : x ∈ 𝒵.left.basicOpen (res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) := by
        rw [basicOpen_res_of_le]; exact ⟨h, hx⟩
      rw [res_tH_DU, Scheme.basicOpen_mul, basicOpen_res_of_le, ρ.basicOpen_f] at h2
      have hUV : x ∈ ρ.U ⊓ ρ.V := h2.1.2
      have h1 := g_mul_tF ρ (cE 𝒵 e) (W := ρ.U ⊓ ρ.V) le_rfl
      have h3 : x ∈ 𝒵.left.basicOpen (res (le_rfl.trans inf_le_right : ρ.U ⊓ ρ.V ≤ ρ.V) ρ.g *
          res (le_rfl.trans inf_le_left : ρ.U ⊓ ρ.V ≤ ρ.U) (tF ρ (cE 𝒵 e))) := by
        rw [Scheme.basicOpen_mul, basicOpen_res_of_le, basicOpen_res_of_le, ρ.basicOpen_g]
        exact ⟨⟨hUV, hUV⟩, ⟨hUV, h⟩⟩
      rw [h1, basicOpen_res_of_le] at h3
      exact h3.2
  · intro x hx
    have h2 : 𝒵.left.basicOpen (res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) =
        tDV ρ (cE 𝒵 e) :=
      Scheme.basicOpen_of_isUnit _ (isUnit_iff_exists_inv.mpr ⟨_, res_tH_DV 𝒵 ρ e⟩)
    have h3 : x ∈ 𝒵.left.basicOpen (res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) := by
      rw [h2]; exact hx
    rw [basicOpen_res_of_le] at h3
    exact h3.2

theorem isAffineOpen_V' (hρ : IsP1Coordinate 𝒵 ρ) :
    IsAffineOpen (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)) := by
  refine isAffineOpen_of_isAffineOpen_basicOpen _ {tg ρ (cE 𝒵 e), tH 𝒵 ρ e} ?_ ?_
  · rw [Ideal.eq_top_iff_one]
    have : (1 : Γ(𝒵.left, tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e))) =
        baseToSections 𝒵 _ e * tg ρ (cE 𝒵 e) + tH 𝒵 ρ e := by rw [tH]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.subset_span (by simp))
  · rintro i (rfl | rfl)
    · rw [basicOpen_tg]; exact hρ.1.basicOpen _
    · rw [basicOpen_tH]; exact hρ.2.1.basicOpen _

/-- `res` of `ψ(P) = P(g')` to `D_U(f + e)` is `P(1/(f + e))`. -/
theorem res_eval_DU (P : (Zloc p)[X]) :
    res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (eval₂ (baseToSections 𝒵 _) (tg ρ (cE 𝒵 e)) P) =
      eval₂ (baseToSections 𝒵 _) (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) P := by
  rw [hom_eval₂, tg_res_DU, tS2,
    show (res _).comp (baseToSections 𝒵 _) = baseToSections 𝒵 (tDU ρ (cE 𝒵 e)) from
      RingHom.ext (res_baseToSections 𝒵 _)]

/-- `res` of `ψ(P) = P(g')` to `D_V(1 + e g)` is `P(g/(1 + e g))`. -/
theorem res_eval_DV (P : (Zloc p)[X]) :
    res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (eval₂ (baseToSections 𝒵 _) (tg ρ (cE 𝒵 e)) P) =
      eval₂ (baseToSections 𝒵 _) (tS1 ρ (cE 𝒵 e)) P := by
  rw [hom_eval₂, tg_res_DV,
    show (res _).comp (baseToSections 𝒵 _) = baseToSections 𝒵 (tDV ρ (cE 𝒵 e)) from
      RingHom.ext (res_baseToSections 𝒵 _)]

/-- Sections on `D_U(f + e)` are polynomials in `1/(f + e)` up to a power of `1/(f + e)`. -/
theorem exists_poly_DU (hρ : IsP1Coordinate 𝒵 ρ) (z : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) :
    ∃ (N : ℕ) (P : (Zloc p)[X]),
      z * (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) ^ N =
        eval₂ (baseToSections 𝒵 _) (↑(uF ρ (cE 𝒵 e))⁻¹ : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) P := by
  letI : Algebra Γ(𝒵.left, ρ.U) Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := (res (tDU_le ρ (cE 𝒵 e))).toAlgebra
  haveI := hρ.1.isLocalization_of_eq_basicOpen (tF ρ (cE 𝒵 e)) (homOfLE (tDU_le ρ (cE 𝒵 e))) rfl
  obtain ⟨⟨a0, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (tF ρ (cE 𝒵 e))) z
  obtain ⟨Q, rfl⟩ := hρ.2.2.1.2 a0
  change z * res (tDU_le ρ (cE 𝒵 e)) (tF ρ (cE 𝒵 e) ^ n) =
    res (tDU_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.U) ρ.f Q) at hz
  set x : Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := ↑(uF ρ (cE 𝒵 e)) with hxdef
  set xi : Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := ↑(uF ρ (cE 𝒵 e))⁻¹ with hxidef
  have hx : x * xi = 1 := Units.mul_inv _
  letI : Invertible x := Units.invertible _
  have hfx : res (tDU_le ρ (cE 𝒵 e)) ρ.f = x - baseToSections 𝒵 _ e := by
    rw [hxdef, uF_val, tF_eq, map_add, res_baseToSections]; ring
  have hQ : res (tDU_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.U) ρ.f Q) =
      eval₂ (baseToSections 𝒵 _) x (Q.comp (X - C e)) := by
    rw [hom_eval₂, show (res _).comp (baseToSections 𝒵 ρ.U) = baseToSections 𝒵 (tDU ρ (cE 𝒵 e))
      from RingHom.ext (res_baseToSections 𝒵 _), hfx, eval₂_comp]
    simp
  set Q' := Q.comp (X - C e)
  set N := Q'.natDegree
  have hR := eval₂_reflect_mul_pow (baseToSections 𝒵 (tDU ρ (cE 𝒵 e))) x N Q' le_rfl
  have hinv : (⅟x : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) = xi := rfl
  rw [hinv] at hR
  have hxn : res (tDU_le ρ (cE 𝒵 e)) (tF ρ (cE 𝒵 e) ^ n) = x ^ n := by
    rw [map_pow, hxdef, uF_val]
  rw [hxn, hQ, ← hR] at hz
  refine ⟨N, reflect N Q' * X ^ n, ?_⟩
  rw [eval₂_mul, eval₂_X_pow]
  set R := eval₂ (baseToSections 𝒵 (tDU ρ (cE 𝒵 e))) xi (reflect N Q')
  calc z * xi ^ N = z * xi ^ N * (x * xi) ^ n := by rw [hx, one_pow, mul_one]
    _ = (z * x ^ n) * xi ^ N * xi ^ n := by ring
    _ = R * x ^ N * xi ^ N * xi ^ n := by rw [hz]
    _ = R * xi ^ n * (x * xi) ^ N := by ring
    _ = R * xi ^ n := by rw [hx, one_pow, mul_one]

/-- Sections on `D_V(1 + e g)` are polynomials in `g' = g/(1 + e g)` up to a power of
`h' = 1/(1 + e g)`. -/
theorem exists_poly_DV (hρ : IsP1Coordinate 𝒵 ρ) (z : Γ(𝒵.left, tDV ρ (cE 𝒵 e))) :
    ∃ (N : ℕ) (P : (Zloc p)[X]),
      z * res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) ^ N =
        eval₂ (baseToSections 𝒵 _) (tS1 ρ (cE 𝒵 e)) P := by
  letI : Algebra Γ(𝒵.left, ρ.V) Γ(𝒵.left, tDV ρ (cE 𝒵 e)) := (res (tDV_le ρ (cE 𝒵 e))).toAlgebra
  haveI := hρ.2.1.isLocalization_of_eq_basicOpen (tG ρ (cE 𝒵 e)) (homOfLE (tDV_le ρ (cE 𝒵 e))) rfl
  obtain ⟨⟨b0, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (tG ρ (cE 𝒵 e))) z
  obtain ⟨Q, rfl⟩ := hρ.2.2.2.2 b0
  change z * res (tDV_le ρ (cE 𝒵 e)) (tG ρ (cE 𝒵 e) ^ n) =
    res (tDV_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.V) ρ.g Q) at hz
  set φ := baseToSections 𝒵 (tDV ρ (cE 𝒵 e))
  set y : Γ(𝒵.left, tDV ρ (cE 𝒵 e)) := ↑(uG ρ (cE 𝒵 e)) with hydef
  set v := res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e) with hvdef
  set w := tS1 ρ (cE 𝒵 e) with hwdef
  set a := res (tDV_le ρ (cE 𝒵 e)) ρ.g with hadef
  have hvy : v * y = 1 := res_tH_DV 𝒵 ρ e
  have hv : v = 1 - φ e * w := by
    rw [hvdef, tH, map_sub, map_one, map_mul, res_baseToSections, tg_res_DV]
  have haw : a = w * y := by
    rw [hwdef, tS1, mul_assoc, Units.inv_mul, mul_one]
  have hyn : res (tDV_le ρ (cE 𝒵 e)) (tG ρ (cE 𝒵 e) ^ n) = y ^ n := by
    rw [map_pow, hydef, uG_val]
  have hQ : res (tDV_le ρ (cE 𝒵 e)) (eval₂ (baseToSections 𝒵 ρ.V) ρ.g Q) = eval₂ φ a Q := by
    rw [hom_eval₂, show (res _).comp (baseToSections 𝒵 ρ.V) = φ
      from RingHom.ext (res_baseToSections 𝒵 _)]
  rw [hyn, hQ] at hz
  set D := Q.natDegree + 1
  have hsum : eval₂ φ a Q = ∑ i ∈ Finset.range D, φ (Q.coeff i) * a ^ i :=
    eval₂_eq_sum_range' φ (Nat.lt_succ_self _) a
  refine ⟨D, ∑ i ∈ Finset.range D, C (Q.coeff i) * X ^ i * (1 - C e * X) ^ (n + D - i), ?_⟩
  rw [eval₂_finsetSum]
  have hterm : ∀ i ∈ Finset.range D,
      eval₂ φ w (C (Q.coeff i) * X ^ i * (1 - C e * X) ^ (n + D - i)) =
        φ (Q.coeff i) * a ^ i * v ^ (n + D) := by
    intro i hi
    have hiD : i ≤ n + D := (Finset.mem_range.1 hi).le.trans (Nat.le_add_left _ _)
    rw [eval₂_mul, eval₂_mul, eval₂_C, eval₂_X_pow, eval₂_pow, eval₂_sub, eval₂_one, eval₂_mul,
      eval₂_C, eval₂_X, ← hv, haw]
    conv_rhs => rw [← Nat.sub_add_cancel hiD, pow_add]
    calc φ (Q.coeff i) * w ^ i * v ^ (n + D - i)
        = φ (Q.coeff i) * w ^ i * v ^ (n + D - i) * (v * y) ^ i := by rw [hvy, one_pow, mul_one]
      _ = φ (Q.coeff i) * (w * y) ^ i * (v ^ (n + D - i) * v ^ i) := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hsum, ← hz]
  calc z * v ^ D = z * v ^ D * (v * y) ^ n := by rw [hvy, one_pow, mul_one]
    _ = z * y ^ n * v ^ (n + D) := by ring

/-- Clearing a power of `s` after restriction to `D(s)` (`O` affine). -/
theorem exists_pow_mul_eq_of_res {X : Scheme.{0}} {O W : X.Opens} (hO : IsAffineOpen O)
    (hWO : W ≤ O) (s : Γ(X, O)) (hW : X.basicOpen s = W) (c d : Γ(X, O)) (N : ℕ)
    (h : res hWO c * (res hWO s) ^ N = res hWO d) : ∃ m : ℕ, s ^ m * (c * s ^ N) = s ^ m * d := by
  letI : Algebra Γ(X, O) Γ(X, W) := (res hWO).toAlgebra
  haveI := hO.isLocalization_of_eq_basicOpen s (homOfLE hWO) hW.symm
  have h0 : algebraMap Γ(X, O) Γ(X, W) (c * s ^ N - d) = 0 := by
    change res hWO (c * s ^ N - d) = 0
    rw [map_sub, map_mul, map_pow, h, sub_self]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) Γ(X, W) _).1 h0
  refine ⟨m, ?_⟩
  rw [← sub_eq_zero, ← mul_sub]
  exact hm

theorem surjective_g' (hρ : IsP1Coordinate 𝒵 ρ) :
    Function.Surjective (eval₂RingHom (baseToSections 𝒵 (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)))
      (tg ρ (cE 𝒵 e))) := by
  intro c
  set ψ := eval₂RingHom (baseToSections 𝒵 (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e))) (tg ρ (cE 𝒵 e))
  have hV' := isAffineOpen_V' 𝒵 ρ e hρ
  have hψX : ψ X = tg ρ (cE 𝒵 e) := by simp [ψ]
  have hψH : ψ (1 - C e * X) = tH 𝒵 ρ e := by simp [ψ, tH]
  obtain ⟨N1, P1, h1⟩ := exists_poly_DU 𝒵 ρ e hρ (res le_sup_right c)
  have h1' : res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) c *
      (res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (tg ρ (cE 𝒵 e))) ^ N1 =
      res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _) (ψ P1) := by
    rw [tg_res_DU, tS2, h1]
    exact (res_eval_DU 𝒵 ρ e P1).symm
  obtain ⟨m1, hm1⟩ := exists_pow_mul_eq_of_res hV' le_sup_right (tg ρ (cE 𝒵 e))
    (basicOpen_tg 𝒵 ρ e) c (ψ P1) N1 h1'
  obtain ⟨N2, P2, h2⟩ := exists_poly_DV 𝒵 ρ e hρ (res le_sup_left c)
  have h2' : res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) c *
      (res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (tH 𝒵 ρ e)) ^ N2 =
      res (le_sup_left : tDV ρ (cE 𝒵 e) ≤ _) (ψ P2) := by
    rw [h2]
    exact (res_eval_DV 𝒵 ρ e P2).symm
  obtain ⟨m2, hm2⟩ := exists_pow_mul_eq_of_res hV' le_sup_left (tH 𝒵 ρ e)
    (basicOpen_tH 𝒵 ρ e) c (ψ P2) N2 h2'
  have hcop : IsCoprime ((X : (Zloc p)[X]) ^ (m1 + N1)) ((1 - C e * X) ^ (m2 + N2)) :=
    (show IsCoprime (X : (Zloc p)[X]) (1 - C e * X) from ⟨C e, 1, by ring⟩).pow
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u * (X ^ m1 * P1) + v * ((1 - C e * X) ^ m2 * P2), ?_⟩
  have e1 : ψ (X ^ m1 * P1) = c * tg ρ (cE 𝒵 e) ^ (m1 + N1) := by
    rw [map_mul, map_pow, hψX, ← hm1]; ring
  have e2 : ψ ((1 - C e * X) ^ m2 * P2) = c * tH 𝒵 ρ e ^ (m2 + N2) := by
    rw [map_mul, map_pow, hψH, ← hm2]; ring
  have e3 := congrArg ψ huv
  rw [map_add, map_mul, map_mul, map_pow, map_pow, hψX, hψH, map_one] at e3
  rw [map_add, map_mul ψ u, map_mul ψ v, e1, e2]
  linear_combination c * e3

theorem injective_g' (hρ : IsP1Coordinate 𝒵 ρ) :
    Function.Injective (eval₂RingHom (baseToSections 𝒵 (tDV ρ (cE 𝒵 e) ⊔ tDU ρ (cE 𝒵 e)))
      (tg ρ (cE 𝒵 e))) := by
  have hbU := hρ.2.2.1
  let eU := RingEquiv.ofBijective _ hbU
  haveI : IsDomain Γ(𝒵.left, ρ.U) :=
    Function.Injective.isDomain eU.symm.toRingHom eU.symm.injective
  letI : Algebra Γ(𝒵.left, ρ.U) Γ(𝒵.left, tDU ρ (cE 𝒵 e)) := (res (tDU_le ρ (cE 𝒵 e))).toAlgebra
  haveI := hρ.1.isLocalization_of_eq_basicOpen (tF ρ (cE 𝒵 e)) (homOfLE (tDU_le ρ (cE 𝒵 e))) rfl
  have htF0 : tF ρ (cE 𝒵 e) ≠ 0 := by
    intro h0
    have : eval₂RingHom (baseToSections 𝒵 ρ.U) ρ.f (X + C e) = 0 := by
      rw [← h0, tF_eq]; simp
    exact X_add_C_ne_zero e (hbU.1 (this.trans (map_zero _).symm))
  have hresinj : Function.Injective (res (tDU_le ρ (cE 𝒵 e))) :=
    IsLocalization.injective (M := Submonoid.powers (tF ρ (cE 𝒵 e))) Γ(𝒵.left, tDU ρ (cE 𝒵 e))
      (powers_le_nonZeroDivisors_of_noZeroDivisors htF0)
  rw [injective_iff_map_eq_zero]
  intro P hP
  have h1 := congrArg (res (le_sup_right : tDU ρ (cE 𝒵 e) ≤ _)) hP
  rw [map_zero, coe_eval₂RingHom, res_eval_DU] at h1
  letI : Invertible (uF ρ (cE 𝒵 e) : Γ(𝒵.left, tDU ρ (cE 𝒵 e))) := Units.invertible _
  set N := P.natDegree
  have h2 : eval₂ (baseToSections 𝒵 (tDU ρ (cE 𝒵 e)))
      (⅟(uF ρ (cE 𝒵 e) : Γ(𝒵.left, tDU ρ (cE 𝒵 e)))) (reflect N (reflect N P)) = 0 := by
    rw [reflect_reflect]; exact h1
  rw [eval₂_reflect_eq_zero_iff _ _ N _ (natDegree_reflect_le.trans (max_self _).le), uF_val]
    at h2
  have h3 : res (tDU_le ρ (cE 𝒵 e))
      (eval₂ (baseToSections 𝒵 ρ.U) (tF ρ (cE 𝒵 e)) (reflect N P)) = 0 := by
    rw [hom_eval₂, show (res _).comp (baseToSections 𝒵 ρ.U) = baseToSections 𝒵 _ from
      RingHom.ext (res_baseToSections 𝒵 _)]
    exact h2
  have h4 := hresinj (h3.trans (map_zero _).symm)
  rw [tF_eq] at h4
  have h5 := (bijective_eval₂_add _ _ e hbU).1
    ((show eval₂RingHom (baseToSections 𝒵 ρ.U) (ρ.f + baseToSections 𝒵 ρ.U e) (reflect N P) = 0
      from h4).trans (map_zero _).symm)
  exact reflect_eq_zero_iff.mp h5

/-- **The translated coordinate is again an isomorphism onto `P¹_{ℤ_(p)}` by charts.** -/
theorem isP1Coordinate_translate (hρ : IsP1Coordinate 𝒵 ρ) :
    IsP1Coordinate 𝒵 (translate ρ (cE 𝒵 e)) := by
  refine ⟨hρ.1, isAffineOpen_V' 𝒵 ρ e hρ, ?_, injective_g' 𝒵 ρ e hρ, surjective_g' 𝒵 ρ e hρ⟩
  show Function.Bijective (eval₂RingHom (baseToSections 𝒵 ρ.U) (tF ρ (cE 𝒵 e)))
  rw [tF_eq]
  exact bijective_eval₂_add _ _ e hρ.2.2.1

theorem val_translate (z : Spec (CommRingCat.of Qbar) ⟶ 𝒵.left) :
    (translate ρ (cE 𝒵 e)).val z = (ρ.val z).map (fun t => t + iq p e) := by
  by_cases hz : ptOf z ∈ ρ.U
  · rw [val_of_mem (translate ρ (cE 𝒵 e)) z hz, val_of_mem ρ z hz]
    change OnePoint.some (ev z hz (tF ρ (cE 𝒵 e))) = _
    rw [tF_eq, map_add, ev_baseToSections]
    rfl
  · rw [val_of_not_mem (translate ρ (cE 𝒵 e)) z hz, val_of_not_mem ρ z hz]
    rfl

end P1T

/-- **(C2-T) `P1Translate` proved**: translations `t ↦ t + e` (`e ∈ ℤ_(p)`) of `P¹_{ℤ_(p)}` act
on isomorphisms by charts. -/
theorem p1Translate : P1Translate := by
  intro p _ 𝒵 ρ hρ e
  exact ⟨translate ρ (cE 𝒵 e), isP1Coordinate_translate 𝒵 ρ e hρ, val_translate 𝒵 ρ e⟩

/-- **Glue C2 from glue A (finiteness of `fibreAut`) and T5 alone.** -/
theorem coordinateFromSections_of'' (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure) :
    CoordinateFromSections :=
  coordinateFromSections_of' hA hT p1Translate

/-- **Main composite (final form, after (C1c) and (C2-T)): `ModelCoordinateResidue` from the
leaves L1-L6, the textbook leaf T5 and four glue Props of this task**: (A-fix)
`FibreAutFixFinite`, (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b)
`CMStabInvolution`. -/
theorem modelCoordinateResidue_final2 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final hAF hQE hTS hP1 hFix hCyc hT hfix hD hB hI stabFixesClosure
    p1Translate

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 15: (A-fix) `FibreAutFixFinite` reduced (the fixed locus of `h` is closed)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **Input (A-fix-irr): the moduli curve `Y` is irreducible over `ℚ`.** For a triple with R1fp,
R1hecke, R2fp, the scheme `Y` is irreducible. True for `Y₃`: its two geometric components
(`π₀ = ℤ̂^×/nrd(K₃) ≅ (ℤ/3)^×`) are conjugate over `ℚ(√−3)` (Shimura reciprocity on `π₀`;
locator UNVERIFIED, SPECULATIVE reading as in `NormalizationModel`'s docstring). In this
development it also follows from a normalization chart: `ModelGlue.irreducible_of_chart` proves
`IrreducibleSpace Y.left` from T5 (`TwistClassFinite`) and any `E` with `NormalizationModel Y π E`.
The targets A and C1 have no such `E` among their hypotheses, so the irreducibility enters here as
a separate input (it is not implied by R1fp, R1hecke, R2fp as clause lists without arithmetic). -/
def ModelYIrreducible : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left

/-- **Glue (A-fix-dim): a closed subset of an integral relative curve over `ℤ_(p)` that misses the
generic point carries only finitely many `ℚ̄`-points** (dimension theory of curves; no
literature). For `𝒴` integral, proper and smooth of relative dimension 1 over `ℤ_(p)` and `Z ⊆ 𝒴` closed
with `η ∉ Z`, only finitely many `ℚ̄`-points of `𝒴` have their point in `Z`. (Outline: `ℚ̄`-points
lie on the generic fibre `𝒴_ℚ`, an integral curve over `ℚ`; by `smoothStalkDimOne` every point of
`Z ∩ 𝒴_ℚ` is closed (a non-closed point `x ≠ η` would give a chain `η ⤳ x ⤳ z` of length 2 below a
closed point `z`), so the closed set `Z ∩ 𝒴_ℚ` of the Noetherian space `𝒴_ℚ` is finite; each closed
point has a residue field finite over `ℚ` (Zariski's lemma), hence finitely many embeddings into
`ℚ̄`.) Properness (only quasi-compactness is used) cannot be dropped: the affine line with
infinitely many doubled points is integral and smooth, and its doubled points form an infinite
closed set missing the generic point. -/
def CurveClosedQbarFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))),
    IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom → ∀ (_ : IsIntegral 𝒴.left) (Z : Set 𝒴.left),
    IsClosed Z → genericPoint 𝒴.left ∉ Z →
    {y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left | qbarPoint y ∈ Z}.Finite

/-- **The model is integral, from `CurveBijIso` and the irreducibility of `Y`** (the argument of
`ModelGlue.modelIntegral_of`, with `ModelYIrreducible` in place of the chart). -/
theorem isIntegral_model (hC : CurveBijIso) (hYI : ModelYIrreducible) {p : ℕ} [Fact p.Prime]
    {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left} (hM : IsShimuraModel p 𝒴 𝒜)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) : IsIntegral 𝒴.left := by
  obtain ⟨g, -, hbij⟩ := exists_genFib_to_Y hM h1
  haveI : IsIso g := hC (genFib 𝒴) Y (genFib_isProper 𝒴 hM.1) (genFib_smooth 𝒴 hM.2.1)
    h1.1 h1.2.1 g hbij
  haveI : IsIso g.left := (Over.forget _).map_isIso g
  haveI : IrreducibleSpace Y.left := hYI Y Φ π h1 hh h2
  haveI : IrreducibleSpace (genFib 𝒴).left := by
    rw [irreducibleSpace_def]
    show IsIrreducible (Set.univ : Set (genFib 𝒴).left)
    have hsurj : Function.Surjective (inv g.left) := fun s =>
      ⟨g.left s, by rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl⟩
    rw [← Set.range_eq_univ.2 hsurj, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (inv g.left).continuous.continuousOn
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hM.2.1
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : IsReduced 𝒴.left := isReduced_of_smooth_zloc 𝒴
  haveI : IrreducibleSpace 𝒴.left := irreducibleSpace_of_genFib 𝒴
  exact isIntegral_of_irreducibleSpace_of_isReduced 𝒴.left

/-- **An automorphism over `S` of an integral separated `S`-scheme whose fixed locus contains the
generic point is the identity** (the fixed locus is a closed subscheme; a surjective closed
immersion into a reduced scheme is an isomorphism). -/
theorem eq_one_of_genericPoint_fixed {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom]
    [IsIntegral X.left] (h : Aut X.left) (hh : h.asIso.hom ≫ X.hom = X.hom)
    (hη : genericPoint X.left ∈ Set.range (equalizer.ι (Over.homMk h.asIso.hom hh : X ⟶ X)
      (𝟙 X)).left) : h = 1 := by
  let f : X ⟶ X := Over.homMk h.asIso.hom hh
  let ι := (equalizer.ι f (𝟙 X)).left
  have hι : ι ≫ h.asIso.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f (𝟙 X))
    simpa [f, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hsurj : Function.Surjective ι := by
    intro x
    have hcl' : closure ({genericPoint X.left} : Set X.left) = Set.univ := (genericPoint_spec _).def
    have hx : x ∈ closure ({genericPoint X.left} : Set X.left) := by rw [hcl']; trivial
    exact closure_minimal (Set.singleton_subset_iff.2 hη) hcl hx
  haveI : Surjective ι := ⟨hsurj⟩
  haveI := isIso_of_isClosedImmersion_of_surjective ι
  have h1 : h.asIso.hom = 𝟙 _ := by rw [← cancel_epi ι, hι, Category.comp_id]
  exact Aut.ext (Iso.ext h1)

/-- **(A-fix) reduced: `FibreAutFixFinite` from `CurveBijIso` (model-glue's textbook leaf),
`ModelYIrreducible` and `CurveClosedQbarFinite`.** If `h ≠ 1` fixed infinitely many `ℚ̄`-points,
the closed fixed locus of `h` would contain the generic point of the integral `𝒴`
(`CurveClosedQbarFinite`), so `h = 1` (`eq_one_of_genericPoint_fixed`). -/
theorem fibreAutFixFinite_of (hC : CurveBijIso) (hYI : ModelYIrreducible)
    (hF : CurveClosedQbarFinite) : FibreAutFixFinite := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 h hmem hne
  haveI : IsIntegral 𝒴.left := isIntegral_model hC hYI hM h1 hh h2
  haveI := hM.1
  have hh' := fibreAut_over 𝒴 𝒜 h hmem
  by_contra hinf
  apply hne
  refine eq_one_of_genericPoint_fixed 𝒴 h hh' ?_
  let f : 𝒴 ⟶ 𝒴 := Over.homMk h.asIso.hom hh'
  let ι := (equalizer.ι f (𝟙 𝒴)).left
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hfix : ∀ y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, y ≫ h.asIso.hom = y →
      qbarPoint y ∈ Set.range ι := by
    intro y hy
    let y' : Over.mk (y ≫ 𝒴.hom) ⟶ 𝒴 := Over.homMk y rfl
    have hc : y' ≫ f = y' ≫ 𝟙 𝒴 := by
      ext1; simpa [f, y'] using hy
    refine ⟨(equalizer.lift y' hc).left (IsLocalRing.closedPoint Qbar), ?_⟩
    show ((equalizer.lift y' hc).left ≫ (equalizer.ι f (𝟙 𝒴)).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  by_contra hη
  exact hinf ((hF p 𝒴 hM.1 hM.2.1 inferInstance _ hcl hη).subset (fun y hy => hfix y hy))

/-- **Glue A from T5, `CurveBijIso`, `ModelYIrreducible`, `CurveClosedQbarFinite`.** -/
theorem fibreAutTame_of'' (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hF : CurveClosedQbarFinite) : FibreAutTame :=
  fibreAutTame_of' hT (fibreAutFixFinite_of hC hYI hF)

/-- **Main composite (after part 15): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the input `ModelYIrreducible`, and the glue (A-fix-dim)
`CurveClosedQbarFinite`, (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b)
`CMStabInvolution`.** -/
theorem modelCoordinateResidue_final3 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hF : CurveClosedQbarFinite) (hD : QuotientDescendsQ)
    (hB : ToP1BijIsCoordinateQ) (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final2 hAF hQE hTS hP1 hFix hCyc hT (fibreAutFixFinite_of hC hYI hF) hD hB
    hI

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 16: (A-fix-dim) `CurveClosedQbarFinite` proved (dimension theory of curves)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **A closed point of a `ℚ`-scheme locally of finite type has a residue field finite over `ℚ`**
(Zariski's lemma, Mathlib's `finite_of_finite_type_of_isJacobsonRing`, through the closed immersion
`Spec κ(x) → X`). The `ℚ`-algebra structure is the one from the structure map. -/
theorem finite_residueField_of_isClosed (X : Over (Spec (CommRingCat.of ℚ)))
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    ∃ ψ : ℚ →+* X.left.residueField x,
      @Module.Finite ℚ (X.left.residueField x) _ _ ψ.toAlgebra.toModule := by
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hft : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  set ψ := Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) with hψ
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom), ← hψ,
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  letI : Algebra ℚ (X.left.residueField x) := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType ℚ (X.left.residueField x) := hft
  exact ⟨ψ.hom, finite_of_finite_type_of_isJacobsonRing ℚ (X.left.residueField x)⟩

/-- **Finitely many `ℚ̄`-points over a closed point** of a `ℚ`-scheme locally of finite type. -/
theorem finite_qbarPts_over_closed (X : Over (Spec (CommRingCat.of ℚ)))
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    {y : Spec (CommRingCat.of Qbar) ⟶ X.left | ptOf y = x}.Finite := by
  obtain ⟨ψ, hfin⟩ := finite_residueField_of_isClosed X x hx
  letI : Algebra ℚ (X.left.residueField x) := ψ.toAlgebra
  haveI : Module.Finite ℚ (X.left.residueField x) := hfin
  haveI : Finite (X.left.residueField x →ₐ[ℚ] Qbar) := inferInstance
  haveI : Finite (X.left.residueField x →+* Qbar) :=
    Finite.of_equiv _ (RingHom.equivRatAlgHom (R := X.left.residueField x) (S := Qbar)).symm
  haveI : Finite (X.left.residueField x ⟶ CommRingCat.of Qbar) :=
    Finite.of_injective (fun φ : X.left.residueField x ⟶ CommRingCat.of Qbar => φ.hom)
      (fun _ _ h => CommRingCat.hom_ext h)
  refine (Set.finite_range (fun φ : X.left.residueField x ⟶ CommRingCat.of Qbar =>
    (Scheme.SpecToEquivOfField Qbar X.left).symm ⟨x, φ⟩)).subset ?_
  intro y hy
  obtain ⟨⟨x', φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField Qbar X.left).symm.surjective y
  have hx' : x' = x := by
    have := hy
    simp only [Set.mem_setOf_eq, ptOf, Equiv.apply_symm_apply] at this
    exact this
  subst hx'
  exact ⟨φ, rfl⟩

/-- In a quasi-sober Noetherian space, a closed set all of whose points are closed is finite. -/
theorem finite_of_isClosed_of_closedPoints {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] [QuasiSober α] {s : Set α} (hs : IsClosed s)
    (hpts : ∀ x ∈ s, IsClosed ({x} : Set α)) : s.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine Set.Finite.sUnion hSf (fun t ht => ?_)
  have hg := (hSirr t ht).isGenericPoint_genericPoint_closure
  rw [(hScl t ht).closure_eq] at hg
  have hcl := hpts _ (Set.mem_sUnion.2 ⟨t, ht, hg.mem⟩)
  refine (Set.finite_singleton (hSirr t ht).genericPoint).subset ?_
  intro x hxt
  rw [← hcl.closure_eq, hg.def]
  exact hxt

/-- **(A-fix-dim) `CurveClosedQbarFinite` proved.** Every point of `Z` over the generic fibre is
closed there (`smoothStalkDimOne`: a non-closed point would give a chain of length 2 below a
closed point), so `Z ∩ 𝒴_ℚ` is finite (Noetherian, quasi-sober), and each closed point carries
finitely many `ℚ̄`-points (`finite_qbarPts_over_closed`). -/
theorem curveClosedQbarFinite : CurveClosedQbarFinite := by
  intro p _ 𝒴 hP hS hI Z hZ hη
  haveI := hP
  haveI := hS
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI := isOpenImmersion_specRatToZloc p
  set G := genFib 𝒴 with hG
  set j : G.left ⟶ 𝒴.left := pullback.fst 𝒴.hom (specRatToZloc p) with hj
  haveI : IsOpenImmersion j :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)
  haveI : IsProper G.hom := genFib_isProper 𝒴 hP
  haveI hGs : SmoothOfRelativeDimension 1 G.hom := genFib_smooth 𝒴 hS
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth 1 G.hom
  haveI : LocallyOfFiniteType G.hom := inferInstance
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  set Z' : Set G.left := j ⁻¹' Z with hZ'
  have hZ'cl : IsClosed Z' := hZ.preimage j.continuous
  obtain ⟨w, hw⟩ : ∃ w : G.left, j w = genericPoint 𝒴.left := genericPoint_mem_range 𝒴
  -- every point of `Z'` is closed in `G`
  have hpts : ∀ x ∈ Z', IsClosed ({x} : Set G.left) := by
    intro x hx
    obtain ⟨z, hzc, hzc'⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x |>.mono
      subset_closure) isClosed_closure.isLocallyClosed
    have hz1 : IsClosed ({z} : Set G.left) := mem_closedPoints_iff.mp hzc'
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hzc
    have hwx : w ⤳ x := by
      rw [← j.isOpenEmbedding.isInducing.specializes_iff, hw]
      exact (genericPoint_spec 𝒴.left).specializes trivial
    have hwx' : w ≠ x := by
      intro h
      apply hη
      rw [← hw, h]
      exact hx
    by_contra hxc
    have hzx : z ≠ x := by
      intro h; subst h; exact hxc hz1
    have hd := smoothStalkDimOne ℚ G.left G.hom hGs z hz1
    rw [ringKrullDim_stalk_eq_coheight] at hd
    have h1 : z < x := lt_of_le_not_ge hxz (fun h => hzx (Specializes.antisymm h hxz).eq)
    have h2 : x < w := lt_of_le_not_ge hwx (fun h => hwx' (Specializes.antisymm h hwx).eq.symm)
    have c1 := Order.coheight_add_one_le h1
    have c2 := Order.coheight_add_one_le h2
    have hd' : Order.coheight z = 1 := by exact_mod_cast hd
    have : (2 : ℕ∞) ≤ Order.coheight z := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.coheight w + 1 + 1 := add_le_add (add_le_add zero_le le_rfl) le_rfl
        _ ≤ Order.coheight x + 1 := add_le_add c2 le_rfl
        _ ≤ Order.coheight z := c1
    rw [hd'] at this
    exact absurd this (by decide)
  have hfin : Z'.Finite := finite_of_isClosed_of_closedPoints hZ'cl hpts
  have hfin2 : {y' : Spec (CommRingCat.of Qbar) ⟶ G.left | ptOf y' ∈ Z'}.Finite := by
    refine (hfin.biUnion (fun x hx => finite_qbarPts_over_closed G x (hpts x hx))).subset ?_
    intro y' hy'
    exact Set.mem_biUnion hy' rfl
  refine (hfin2.image (fun y' => y' ≫ j)).subset ?_
  intro y hy
  obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
  let s' : Spec (CommRingCat.of Qbar) ⟶ G.left := s.left
  have hs' : s' ≫ j = y := hs
  refine ⟨s', ?_, hs'⟩
  show j (ptOf s') ∈ Z
  have hpt : qbarPoint (s' ≫ j) = j (ptOf s') := by
    unfold qbarPoint
    rw [specToEquivOfField_comp_right]
  rw [← hpt, hs']
  exact hy

/-- **(A-fix) from `CurveBijIso` and `ModelYIrreducible` alone.** -/
theorem fibreAutFixFinite_of' (hC : CurveBijIso) (hYI : ModelYIrreducible) : FibreAutFixFinite :=
  fibreAutFixFinite_of hC hYI curveClosedQbarFinite

/-- **Main composite (after part 16): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the input `ModelYIrreducible`, and the glue (B-desc)
`QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b) `CMStabInvolution`.** -/
theorem modelCoordinateResidue_final4 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final3 hAF hQE hTS hP1 hFix hCyc hT hC hYI curveClosedQbarFinite hD hB hI

/-- **`ModelYIrreducible` from the decomposition's glue `CoverModelOfHeckeN` and T5** (the
normalization chart of `CoverModelN` and model-glue's `irreducible_of_chart`). -/
theorem modelYIrreducible_of_coverModelN (hT : ObjBridge.TorsionStructure)
    (hCov : CoverModelOfHeckeN) : ModelYIrreducible := by
  intro Y Φ π h1 hh h2
  obtain ⟨E, i1, i2, i3, i4, i5, i6, hN, -, -⟩ := hCov Y Φ π h1 hh h2
  exact irreducible_of_chart (twistClassFinite hT) h1 h2 E hN

/-- **Main composite (after part 16, chart form): `ModelCoordinateResidue` from the leaves L1-L6,
the textbook leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the
glue (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b) `CMStabInvolution`.** -/
theorem modelCoordinateResidue_final5 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hI : CMStabInvolution) : ModelCoordinateResidue :=
  modelCoordinateResidue_final4 hAF hQE hTS hP1 hFix hCyc hT hC
    (modelYIrreducible_of_coverModelN hT hCov) hD hB hI

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 17: (C1b) `CMStabInvolution` reduced to a statement on QM objects over `ℚ̄`
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **Glue (C1b-obj): a CM object is fixed by a Hecke operation of order exactly 2 on classes**
(QM with CM; the elliptic points of `Y₃ → P¹` have stabilizers of even order `4, 6, 2` in the
group of Hecke operations on classes, `CoverBranchData`/`nY3`, Baba–Granath §3.1 (locator
UNVERIFIED)). For a level-3 object `P` over `ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`, some
operation `T = twist α ∘ rightMul u` on `M3 ℚ̄` fixes the class of `P`, is an involution, and is not
the identity. (Outline: for `ℤ[i]` take `α = id` and `u ≡ φ` on `A[3]` (`Level3.torsor`,
`exists_unit_congr`); then `u² ≡ −1`, and `−1` acts trivially on classes. For `ℤ[ζ₃]` and
`ℤ[√−6]` the involution is an Atkin–Lehner-type twist induced by an element of the normalizer of
`ι(𝒪)` in `End A` (for `ℤ[√−6]`: `ι(ij)⁻¹ φ`), which needs the structure of `End A` at CM points.) -/
def CMStabObj : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    ∃ (α : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ),
      M3.twist α (M3.rightMul u (M3.mk P)) = M3.mk P ∧
      (∀ m : M3 Qbar, M3.twist α (M3.rightMul u (M3.twist α (M3.rightMul u m))) = m) ∧
      ∃ m : M3 Qbar, M3.twist α (M3.rightMul u m) ≠ m

/-- **An automorphism over `ℤ_(p)` of the smooth model fixing every `ℚ̄`-point is the identity**
(given `CurveBijIso` and `ModelYIrreducible`; through `FibreAutFixFinite` and the infinitely many
`ℚ̄`-points). -/
theorem eq_one_of_fixes_all (hC : CurveBijIso) (hYI : ModelYIrreducible) {p : ℕ} [Fact p.Prime]
    (hp : 324 < p) {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))} {𝒜 : QMFamily 𝒴.left}
    (hM : IsShimuraModel p 𝒴 𝒜) {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π)
    (g : Aut 𝒴.left) (hg : g ∈ fibreAut 𝒴 𝒜)
    (hfix : ∀ z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, z ≫ g.asIso.hom = z) : g = 1 := by
  by_contra hne
  have hfin := fibreAutFixFinite_of' hC hYI p hp 𝒴 𝒜 hM Y Φ π h1 hh h2 g hg hne
  apply infinite_qbarPoints (π := π) hM h1
  refine hfin.subset ?_
  intro z _
  exact hfix z

/-- **(C1b) reduced: `CMStabInvolution` from `CurveBijIso`, `ModelYIrreducible` and the
object-level glue `CMStabObj`.** The Hecke automorphisms `g_α`, `g_u` of `IsShimuraModel` lie in
`fibreAut` (`hecke_mem_fibreAut`); `ι = g_α ∘ g_u` acts on classes as `T`. It fixes `y` (moduli
injectivity), `ι²` fixes every `ℚ̄`-point (`T² = id`), hence `ι² = 1` (`eq_one_of_fixes_all`), and
`ι ≠ 1` because `T` moves the class of some object, which is the fibre at some `ℚ̄`-point. -/
theorem cMStabInvolution_of (hC : CurveBijIso) (hYI : ModelYIrreducible) (hO : CMStabObj) :
    CMStabInvolution := by
  intro p _ hp 𝒴 𝒜 hM Y Φ π h1 hh h2 y P hP hCM
  obtain ⟨α, u, hfixP, hinv, m0, hm0⟩ := hO P hCM
  obtain ⟨htw, hru⟩ := hecke_mem_fibreAut hM
  obtain ⟨ga, hgaG, hga⟩ := htw α
  obtain ⟨gu, hguG, hgu⟩ := hru u
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  set ι : Aut 𝒴.left := ga * gu with hιdef
  have hιG : ι ∈ fibreAut 𝒴 𝒜 := Subgroup.mul_mem _ hgaG hguG
  have hιhom : ι.asIso.hom = gu.asIso.hom ≫ ga.asIso.hom := rfl
  have hact : ∀ (z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (Q Q' : QML3 Qbar), IsFibreOf 𝒜 z Q →
      IsFibreOf 𝒜 (z ≫ ι.asIso.hom) Q' →
        M3.mk Q' = M3.twist α (M3.rightMul u (M3.mk Q)) := by
    intro z Q Q' hQ hQ'
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ gu.asIso.hom)
    have e1 := hgu z Q Q1 hQ hQ1
    rw [hιhom, ← Category.assoc] at hQ'
    have e2 := hga _ Q1 Q' hQ1 hQ'
    rw [e2, e1]
  have hfix2 : ∀ z : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, z ≫ (ι * ι).asIso.hom = z := by
    intro z
    obtain ⟨Q, hQ⟩ := hM.2.2.1 Qbar z
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ ι.asIso.hom)
    obtain ⟨Q2, hQ2⟩ := hM.2.2.1 Qbar ((z ≫ ι.asIso.hom) ≫ ι.asIso.hom)
    have e1 := hact z Q Q1 hQ hQ1
    have e2 := hact _ Q1 Q2 hQ1 hQ2
    have e3 : M3.mk Q2 = M3.mk Q := by rw [e2, e1, hinv]
    have := hM.2.2.2.1 _ z Q2 Q hQ2 hQ e3
    show z ≫ (ι.asIso.hom ≫ ι.asIso.hom) = z
    rw [← Category.assoc]
    exact this
  refine ⟨ι, hιG, ?_, ?_, ?_⟩
  · intro hι1
    obtain ⟨Q, rfl⟩ : ∃ Q : QML3 Qbar, M3.mk Q = m0 := Quotient.exists_rep m0
    obtain ⟨z, hz⟩ := hM.2.2.2.2.1 Q
    obtain ⟨Q1, hQ1⟩ := hM.2.2.1 Qbar (z ≫ ι.asIso.hom)
    have e1 := hact z Q Q1 hz hQ1
    have hz1 : z ≫ ι.asIso.hom = z := by rw [hι1]; simp
    rw [hz1] at hQ1
    apply hm0
    have e2 := huniq z Q1 Q hQ1 hz
    rw [← e1]
    exact e2
  · exact eq_one_of_fixes_all hC hYI hp hM h1 hh h2 _ (Subgroup.mul_mem _ hιG hιG) hfix2
  · obtain ⟨P1, hP1⟩ := hM.2.2.1 Qbar (y ≫ ι.asIso.hom)
    have e := hact y P P1 hP hP1
    rw [hfixP] at e
    exact hM.2.2.2.1 _ y P1 P hP1 hP e

/-- **Main composite (after part 17): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the glue (B-desc)
`QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b-obj) `CMStabObj`.** -/
theorem modelCoordinateResidue_final6 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ)
    (hO : CMStabObj) : ModelCoordinateResidue :=
  modelCoordinateResidue_final5 hAF hQE hTS hP1 hFix hCyc hT hC hCov hD hB
    (cMStabInvolution_of hC (modelYIrreducible_of_coverModelN hT hCov) hO)

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 18: (B-desc) split; the lifting of `ℚ̄`-points through the quotient, proved
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **An SGA 1 quotient by a finite group is surjective** (lying over for the integral extension
`Γ(W) = Γ(q⁻¹W)^G ⊆ Γ(q⁻¹W)`: Mathlib's `Algebra.IsInvariant.isIntegral` and
`Ideal.exists_ideal_over_prime_of_isIntegral`). -/
theorem isGQuotient_surjective {X Z : Scheme.{0}} (G : Subgroup (Aut X)) (q : X ⟶ Z)
    (hfin : Finite G) (hq : IsGQuotient G q) : Function.Surjective q := by
  intro z
  obtain ⟨hinv, haff, hsec⟩ := hq
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hzW, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  set U := q ⁻¹ᵁ W with hUdef
  have hU : IsAffineOpen U := hW.preimage q
  letI : MulSemiringAction G Γ(X, U) := secAction hinv W
  letI : Algebra Γ(Z, W) Γ(X, U) := (q.app W).hom.toAlgebra
  haveI : SMulCommClass G Γ(Z, W) Γ(X, U) := by
    constructor
    intro g a b
    change secMap _ _ W (q.app W a * b) = q.app W a * secMap _ _ W b
    rw [map_mul, secMap_app]
  haveI : Algebra.IsInvariant Γ(Z, W) Γ(X, U) G := by
    constructor
    intro b hb
    have hmem : b ∈ Set.range (q.app W) := by
      rw [(hsec W hW).2]
      intro g hg
      have := hb ⟨g⁻¹, G.inv_mem hg⟩
      change secMap _ _ W b = b at this
      rw [secMap_congr (f' := g.asIso.hom) (by simp) _ (hinv g hg)] at this
      exact this
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩
  haveI : Algebra.IsIntegral Γ(Z, W) Γ(X, U) := Algebra.IsInvariant.isIntegral Γ(Z, W) Γ(X, U) G
  set P := (hW.primeIdealOf ⟨z, hzW⟩).asIdeal with hPdef
  haveI : P.IsPrime := (hW.primeIdealOf ⟨z, hzW⟩).isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal Γ(X, U))
    (by
      intro a ha
      have h0 : q.app W a = 0 := Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)
      rw [(hsec W hW).1 (h0.trans (map_zero _).symm)]
      exact P.zero_mem)
  obtain ⟨y, hy⟩ : ∃ y : Spec Γ(X, U), y.asIdeal = Q := ⟨⟨Q, hQ⟩, rfl⟩
  refine ⟨hU.fromSpec y, ?_⟩
  have h1 : Spec.map (q.appLE W U le_rfl) y = hW.primeIdealOf ⟨z, hzW⟩ := by
    apply PrimeSpectrum.ext
    change Ideal.comap (q.appLE W U le_rfl).hom y.asIdeal = P
    rw [← Scheme.Hom.app_eq_appLE, hy]
    exact hQP
  rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec q hW hU le_rfl,
    Scheme.Hom.comp_apply, h1, IsAffineOpen.fromSpec_primeIdealOf]

/-- **`ℚ̄`-points lift through a finite SGA 1 quotient by a finite group**: the fibre
`X ×_Z Spec ℚ̄` is finite over `Spec ℚ̄` and nonempty (surjectivity), so it has a closed point,
which is a `ℚ̄`-point (Mathlib's `pointOfClosedPoint`). -/
theorem exists_lift_qbar {X Z : Scheme.{0}} (G : Subgroup (Aut X)) (q : X ⟶ Z) (hfin : Finite G)
    (hq : IsGQuotient G q) [IsFinite q] (t₀ : Spec (CommRingCat.of Qbar) ⟶ Z) :
    ∃ y₀ : Spec (CommRingCat.of Qbar) ⟶ X, y₀ ≫ q = t₀ := by
  have hsurj := isGQuotient_surjective G q hfin hq
  let f : pullback q t₀ ⟶ Spec (CommRingCat.of Qbar) := pullback.snd q t₀
  haveI : IsFinite f := inferInstance
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace (pullback q t₀ : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx⟩ := hsurj (t₀ (IsLocalRing.closedPoint Qbar))
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t₀) x
    (IsLocalRing.closedPoint Qbar) hx
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (⟨w, Set.mem_univ _⟩ :
    (Set.univ : Set (pullback q t₀ : Scheme.{0})).Nonempty) isOpen_univ.isLocallyClosed
  have hcl : IsClosed ({c} : Set (pullback q t₀ : Scheme.{0})) := mem_closedPoints_iff.mp hc
  refine ⟨pointOfClosedPoint f c hcl ≫ pullback.fst q t₀, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (pointOfClosedPoint f c hcl ≫ f) ≫ t₀ = t₀
  rw [pointOfClosedPoint_comp, Category.id_comp]

/-- **Glue (B-desc-map): an orbit-invariant coordinate on `𝒴_ℚ` descends to the quotient** (the
descent half of `QuotientDescendsQ`; SGA 1 Exp. V §1, locators UNVERIFIED). Same hypotheses as
`QuotientDescendsQ`; conclusion: some `σ' : 𝒵_ℚ → P¹` with `σ' ∘ q = σ` on `ℚ̄`-points. (Outline:
`𝒵_ℚ = 𝒴_ℚ/G` since invariants commute with the localization `ℤ_(p) → ℚ`; `σ` is `G`-invariant as
a morphism, its values on the dense set of `ℚ̄`-points of the reduced `𝒴_ℚ` being invariant; the
`G`-stable saturated opens `σ⁻¹(t ≠ ∞)`, `σ⁻¹(t ≠ 0)` have open images (`q` closed and surjective),
and `f, g` are invariant sections, i.e. sections on `𝒵_ℚ`.) -/
def QuotientDescendsMapQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (𝒴 𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵)
    (G : Subgroup (Aut 𝒴.left)), IsProper 𝒴.hom → SmoothOfRelativeDimension 1 𝒴.hom →
    Finite G → (∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) →
    IsGQuotient G q.left → IsFinite q.left →
    ∀ σ : ToP1 (genFib 𝒴).left,
      (∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
        s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
          s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
        σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left) →
    ∃ σ' : ToP1 (genFib 𝒵).left,
      ∀ s : fieldPt Qbar ⟶ genFib 𝒴,
        σ'.val (K := Qbar) (s ≫ genFibMap q).left = σ.val (K := Qbar) s.left

/-- **(B-desc) from its descent half**: the lifting half is proved (`exists_lift_qbar`). -/
theorem quotientDescendsQ_of (hDm : QuotientDescendsMapQ) : QuotientDescendsQ := by
  intro p _ 𝒴 𝒵 q G hP hS hfin hover hq hqf σ hσ
  obtain ⟨σ', hσ'⟩ := hDm p 𝒴 𝒵 q G hP hS hfin hover hq hqf σ hσ
  refine ⟨σ', hσ', fun t => ?_⟩
  haveI := hqf
  obtain ⟨y₀, hy₀⟩ := exists_lift_qbar G q.left hfin hq
    (t.left ≫ pullback.fst 𝒵.hom (specRatToZloc p))
  obtain ⟨s, hs⟩ := genFib_pt 𝒴 y₀
  refine ⟨s, genFib_pt_inj 𝒵 _ _ ?_⟩
  refine ((Category.assoc _ _ _).trans ((congrArg (s.left ≫ ·) (genFibMap_fst q)).trans
    (Category.assoc _ _ _).symm)).trans ?_
  rw [hs]
  exact hy₀

/-- **Main composite (after part 18): `ModelCoordinateResidue` from the leaves L1-L6, the textbook
leaves T5 and `CurveBijIso`, the decomposition's glue `CoverModelOfHeckeN`, and the glue
(B-desc-map) `QuotientDescendsMapQ`, (B-iso) `ToP1BijIsCoordinateQ`, (C1b-obj) `CMStabObj`.** -/
theorem modelCoordinateResidue_final7 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hCov : CoverModelOfHeckeN) (hDm : QuotientDescendsMapQ) (hB : ToP1BijIsCoordinateQ)
    (hO : CMStabObj) : ModelCoordinateResidue :=
  modelCoordinateResidue_final6 hAF hQE hTS hP1 hFix hCyc hT hC hCov (quotientDescendsQ_of hDm) hB
    hO

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 19: descent of invariant sections through an SGA 1 quotient (any open)
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

section Descent

variable {X Z : Scheme.{0}} {G : Subgroup (Aut X)} {q : X ⟶ Z}

/-- Restriction commutes with pulling back sections along `q`. -/
theorem app_map_eq {W W' : Z.Opens} (h : W ≤ W') (t : Γ(Z, W')) :
    q.app W (Z.presheaf.map (homOfLE h).op t) =
      X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W' from fun _ hx => h hx)).op (q.app W' t) := by
  have n := ConcreteCategory.congr_hom (q.naturality (homOfLE h).op) t
  simp only [ConcreteCategory.comp_apply] at n
  exact n

/-- `secMap` commutes with restriction. -/
theorem secMap_map (f : X ⟶ X) (hf : f ≫ q = q) {W W' : Z.Opens} (h : W ≤ W')
    (s : Γ(X, q ⁻¹ᵁ W')) :
    secMap f hf W (X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W' from fun _ hx => h hx)).op s) =
      X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W' from fun _ hx => h hx)).op (secMap f hf W' s) := by
  simp only [secMap]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- **Pulling back sections along an SGA 1 quotient is injective over every open.** -/
theorem app_injective_of_isGQuotient (hq : IsGQuotient G q) (W' : Z.Opens) :
    Function.Injective (q.app W') := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  apply TopCat.Presheaf.section_ext Z.sheaf W'
  intro z hz
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWW'⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hz W'.isOpen
  have hle : W ≤ W' := hWW'
  have n := app_map_eq (q := q) hle t
  rw [ht, map_zero] at n
  have h0 : Z.presheaf.map (homOfLE hle).op t = 0 :=
    (hq.2.2 W hW).1 (n.trans (map_zero _).symm)
  have e := Z.presheaf.germ_res_apply (homOfLE hle) z hzW t
  rw [h0, map_zero] at e
  change Z.presheaf.germ W' z hz t = Z.presheaf.germ W' z hz 0
  rw [← e, map_zero]

/-- **Invariant sections over any open descend through an SGA 1 quotient** (glue over an affine
cover from the affine case, which is the definition of `IsGQuotient`). -/
theorem exists_descend_section (hq : IsGQuotient G q) (W' : Z.Opens) (s : Γ(X, q ⁻¹ᵁ W'))
    (hs : ∀ (g : Aut X) (hg : g ∈ G), secMap g.asIso.hom (hq.1 g hg) W' s = s) :
    ∃ t : Γ(Z, W'), q.app W' t = s := by
  have key : ∀ z : W', ∃ W : Z.Opens, IsAffineOpen W ∧ z.1 ∈ W ∧ W ≤ W' := by
    intro z
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWW'⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open z.2 W'.isOpen
    exact ⟨W, hW, hzW, hWW'⟩
  choose Wf hWf hzWf hWfle using key
  have hloc : ∀ z : W', ∃ tz : Γ(Z, Wf z), q.app (Wf z) tz =
      X.presheaf.map (homOfLE (show q ⁻¹ᵁ Wf z ≤ q ⁻¹ᵁ W' from fun _ hx => hWfle z hx)).op s := by
    intro z
    have hr := (hq.2.2 (Wf z) (hWf z)).2
    have hmem : X.presheaf.map (homOfLE (show q ⁻¹ᵁ Wf z ≤ q ⁻¹ᵁ W' from
        fun _ hx => hWfle z hx)).op s ∈ Set.range (q.app (Wf z)) := by
      rw [hr]
      intro g hg
      have := secMap_map (q := q) g.asIso.hom (hq.1 g hg) (hWfle z) s
      change secMap g.asIso.hom (hq.1 g hg) (Wf z) _ = _
      rw [secMap_congr rfl _ (hq.1 g hg), this, hs g hg]
    obtain ⟨tz, htz⟩ := hmem
    exact ⟨tz, htz⟩
  choose tz htz using hloc
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 Wf tz := by
    intro i j
    apply app_injective_of_isGQuotient hq (Wf i ⊓ Wf j)
    change q.app _ (Z.presheaf.map (homOfLE inf_le_left).op (tz i)) =
      q.app _ (Z.presheaf.map (homOfLE inf_le_right).op (tz j))
    rw [app_map_eq, app_map_eq, htz i, htz j, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨t0, ht, -⟩ := Z.sheaf.existsUnique_gluing' Wf W' (fun i => homOfLE (hWfle i))
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzWf ⟨z, hz⟩⟩) tz hcompat
  let t : Γ(Z, W') := t0
  have ht' : ∀ z : W', Z.presheaf.map (homOfLE (hWfle z)).op t = tz z := ht
  refine ⟨t, ?_⟩
  apply TopCat.Presheaf.section_ext X.sheaf (q ⁻¹ᵁ W')
  intro x hx
  let z : W' := ⟨q x, hx⟩
  have hxz : x ∈ q ⁻¹ᵁ Wf z := hzWf z
  have hle' : q ⁻¹ᵁ Wf z ≤ q ⁻¹ᵁ W' := fun _ hy => hWfle z hy
  change X.presheaf.germ _ x hx (q.app W' t) = X.presheaf.germ _ x hx s
  rw [← X.presheaf.germ_res_apply (homOfLE hle') x hxz (q.app W' t),
    ← X.presheaf.germ_res_apply (homOfLE hle') x hxz s]
  have e1 : X.presheaf.map (homOfLE hle').op (q.app W' t) =
      q.app (Wf z) (Z.presheaf.map (homOfLE (hWfle z)).op t) := (app_map_eq (hWfle z) t).symm
  rw [e1, ht' z, htz z]

end Descent

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 20: descent of a `G`-invariant map to `P¹` (on an open) through an SGA 1 quotient
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

/-- A map to `P¹` by charts defined on the open `O` (the charts `U, V` cover `O`). -/
structure ToP1In (X : Scheme.{0}) (O : X.Opens) where
  U : X.Opens
  V : X.Opens
  cover : U ⊔ V = O
  f : Γ(X, U)
  g : Γ(X, V)
  inv : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op f *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g = 1
  basicOpen_f : X.basicOpen f = U ⊓ V
  basicOpen_g : X.basicOpen g = U ⊓ V

section DescentP1

variable {X Z : Scheme.{0}} {G : Subgroup (Aut X)} {q : X ⟶ Z}

/-- The image of a `G`-stable open under a closed quotient map, as an open. -/
def imgOpen (q : X ⟶ Z) [UniversallyClosed q] (U : X.Opens) : Z.Opens :=
  ⟨(q '' (U : Set X)ᶜ)ᶜ, (q.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

theorem preimage_imgOpen [UniversallyClosed q] (hq : IsGQuotient G q) (hfin : Finite G)
    (U : X.Opens) (hU : ∀ g ∈ G, ∀ x, g.asIso.hom x ∈ U ↔ x ∈ U) : q ⁻¹ᵁ imgOpen q U = U := by
  ext x
  change q x ∈ (q '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
  constructor
  · intro h
    by_contra hx
    exact h ⟨x, hx, rfl⟩
  · rintro hx ⟨x', hx', hqx⟩
    obtain ⟨g, hg, hgx⟩ := gQuotientPointOrbits X Z G q hfin hq x' x hqx
    apply hx'
    rw [← hgx]
    exact (hU g hg x).2 hx

theorem eq_of_preimage_eq (hs : Function.Surjective q) {A B : Z.Opens}
    (h : q ⁻¹ᵁ A = q ⁻¹ᵁ B) : A = B := by
  ext z
  obtain ⟨x, rfl⟩ := hs z
  change x ∈ q ⁻¹ᵁ A ↔ x ∈ q ⁻¹ᵁ B
  rw [h]

/-- Invariance of a pulled-back section, transported along an equality of opens. -/
theorem secMap_eqToHom (hq : IsGQuotient G q) {g : Aut X} (hg : g ∈ G) {W : Z.Opens}
    {U : X.Opens} (e : q ⁻¹ᵁ W = U) (hU : U ≤ g.asIso.hom ⁻¹ᵁ U) (s : Γ(X, U))
    (hs : g.asIso.hom.appLE U U hU s = s) :
    secMap g.asIso.hom (hq.1 g hg) W (X.presheaf.map (eqToHom e).op s) =
      X.presheaf.map (eqToHom e).op s := by
  simp only [secMap]
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  conv_rhs => rw [← hs]
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- **Descent of a `G`-invariant map to `P¹` through an SGA 1 quotient** (on the preimage of an
open `O`). The charts are the images of the `G`-stable charts (open, `q` closed and surjective);
the functions are the invariant sections, which descend (`exists_descend_section`); the identities
descend by injectivity of `q.app` (`app_injective_of_isGQuotient`). -/
theorem exists_descend_toP1In [IsFinite q] (hq : IsGQuotient G q) (hfin : Finite G) (O : Z.Opens)
    (σ : ToP1In X (q ⁻¹ᵁ O))
    (hU : ∀ g ∈ G, ∀ x, g.asIso.hom x ∈ σ.U ↔ x ∈ σ.U)
    (hV : ∀ g ∈ G, ∀ x, g.asIso.hom x ∈ σ.V ↔ x ∈ σ.V)
    (hf : ∀ (g : Aut X) (hg : g ∈ G),
      g.asIso.hom.appLE σ.U σ.U (fun x hx => (hU g hg x).2 hx) σ.f = σ.f)
    (hg' : ∀ (g : Aut X) (hg : g ∈ G),
      g.asIso.hom.appLE σ.V σ.V (fun x hx => (hV g hg x).2 hx) σ.g = σ.g) :
    ∃ σ' : ToP1In Z O, ∃ eU : q ⁻¹ᵁ σ'.U = σ.U,
      q.app σ'.U σ'.f = X.presheaf.map (eqToHom eU).op σ.f := by
  have hsurj := isGQuotient_surjective G q hfin hq
  set U' := imgOpen q σ.U with hU'
  set V' := imgOpen q σ.V with hV'
  have eU : q ⁻¹ᵁ U' = σ.U := preimage_imgOpen hq hfin σ.U hU
  have eV : q ⁻¹ᵁ V' = σ.V := preimage_imgOpen hq hfin σ.V hV
  obtain ⟨f', hf'⟩ := exists_descend_section hq U' (X.presheaf.map (eqToHom eU).op σ.f)
    (fun g hg => secMap_eqToHom hq hg eU _ σ.f (hf g hg))
  obtain ⟨g', hg''⟩ := exists_descend_section hq V' (X.presheaf.map (eqToHom eV).op σ.g)
    (fun g hg => secMap_eqToHom hq hg eV _ σ.g (hg' g hg))
  have eUV : q ⁻¹ᵁ (U' ⊓ V') = σ.U ⊓ σ.V := by
    rw [Scheme.Hom.preimage_inf, eU, eV]
  -- pulling back restrictions
  have hresf : q.app (U' ⊓ V') (Z.presheaf.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op f') =
      X.presheaf.map (eqToHom eUV).op
        (X.presheaf.map (homOfLE (inf_le_left : σ.U ⊓ σ.V ≤ σ.U)).op σ.f) := by
    rw [app_map_eq, hf', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hresg : q.app (U' ⊓ V') (Z.presheaf.map (homOfLE (inf_le_right : U' ⊓ V' ≤ V')).op g') =
      X.presheaf.map (eqToHom eUV).op
        (X.presheaf.map (homOfLE (inf_le_right : σ.U ⊓ σ.V ≤ σ.V)).op σ.g) := by
    rw [app_map_eq, hg'', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hbf : Z.basicOpen f' = U' ⊓ V' := by
    apply eq_of_preimage_eq hsurj
    rw [Scheme.preimage_basicOpen, hf', Scheme.basicOpen_res, σ.basicOpen_f, eUV]
    exact inf_eq_right.mpr (by rw [eU]; exact inf_le_left)
  have hbg : Z.basicOpen g' = U' ⊓ V' := by
    apply eq_of_preimage_eq hsurj
    rw [Scheme.preimage_basicOpen, hg'', Scheme.basicOpen_res, σ.basicOpen_g, eUV]
    exact inf_eq_right.mpr (by rw [eV]; exact inf_le_right)
  refine ⟨⟨U', V', ?_, f', g', ?_, hbf, hbg⟩, eU, hf'⟩
  · apply eq_of_preimage_eq hsurj
    rw [Scheme.Hom.preimage_sup, eU, eV, σ.cover]
  · apply app_injective_of_isGQuotient hq (U' ⊓ V')
    rw [map_mul, map_one, hresf, hresg, ← map_mul, σ.inv, map_one]

end DescentP1

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 21: transport of maps to `P¹` along open immersions
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

section Transport

variable {X Y : Scheme.{0}}

/-- Sections over an open inside the range of an open immersion are detected after pulling back. -/
theorem app_injective_of_le_range (j : Y ⟶ X) [IsOpenImmersion j] (A : X.Opens)
    (hA : A ≤ j.opensRange) : Function.Injective (j.app A) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf A
  intro x hx
  obtain ⟨y, rfl⟩ := hA hx
  have e := j.germ_stalkMap_apply A y hx s
  rw [hs, map_zero] at e
  have hinj : Function.Injective (j.stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap y)).1
  change X.presheaf.germ A (j y) hx s = X.presheaf.germ A (j y) hx 0
  rw [map_zero]
  exact hinj (e.trans (map_zero _).symm)

theorem eq_of_preimage_eq_of_le_range (j : Y ⟶ X) [IsOpenImmersion j] {A B : X.Opens} (hA : A ≤ j.opensRange)
    (hB : B ≤ j.opensRange) (h : j ⁻¹ᵁ A = j ⁻¹ᵁ B) : A = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := hA hx
    have : y ∈ j ⁻¹ᵁ B := h ▸ hx
    exact this
  · intro hx
    obtain ⟨y, rfl⟩ := hB hx
    have : y ∈ j ⁻¹ᵁ A := h.symm ▸ hx
    exact this

/-- The section `(j.appIso U).inv s` pulls back to `s`. -/
theorem app_appIso_inv_apply (j : Y ⟶ X) [IsOpenImmersion j] (U : Y.Opens) (s : Γ(Y, U)) :
    j.app (j ''ᵁ U) ((j.appIso U).inv s) =
      Y.presheaf.map (eqToHom (j.preimage_image_eq U)).op s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_app]

/-- **Pushing a map to `P¹` forward along an open immersion**, as a map on its range. -/
def pushToP1In (j : Y ⟶ X) [IsOpenImmersion j] (σ : ToP1 Y) : ToP1In X j.opensRange where
  U := j ''ᵁ σ.U
  V := j ''ᵁ σ.V
  cover := by
    rw [← j.image_top_eq_opensRange, ← σ.cover]
    ext x
    simp only [Opens.coe_sup, Set.mem_union, Scheme.Hom.coe_image, SetLike.mem_coe, Set.image_union]
  f := (j.appIso σ.U).inv σ.f
  g := (j.appIso σ.V).inv σ.g
  inv := by
    have hle : j ''ᵁ σ.U ⊓ j ''ᵁ σ.V ≤ j.opensRange :=
      inf_le_left.trans (j.image_le_opensRange _)
    apply app_injective_of_le_range j _ hle
    have hpre : j ⁻¹ᵁ (j ''ᵁ σ.U ⊓ j ''ᵁ σ.V) = σ.U ⊓ σ.V := by
      rw [Scheme.Hom.preimage_inf, j.preimage_image_eq, j.preimage_image_eq]
    rw [map_mul, map_one, app_map_eq, app_map_eq, app_appIso_inv_apply, app_appIso_inv_apply,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    have := congrArg (Y.presheaf.map (eqToHom hpre).op) σ.inv
    rw [map_mul, map_one, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp] at this
    exact this
  basicOpen_f := by
    rw [← Scheme.image_basicOpen, σ.basicOpen_f]
    ext x
    simp only [Opens.coe_inf, Scheme.Hom.coe_image, Set.mem_inter_iff, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
    · rintro ⟨⟨y, h1, rfl⟩, ⟨y', h2, hy⟩⟩
      obtain rfl := j.isOpenEmbedding.injective hy
      exact ⟨y', ⟨h1, h2⟩, rfl⟩
  basicOpen_g := by
    rw [← Scheme.image_basicOpen, σ.basicOpen_g]
    ext x
    simp only [Opens.coe_inf, Scheme.Hom.coe_image, Set.mem_inter_iff, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
    · rintro ⟨⟨y, h1, rfl⟩, ⟨y', h2, hy⟩⟩
      obtain rfl := j.isOpenEmbedding.injective hy
      exact ⟨y', ⟨h1, h2⟩, rfl⟩

/-- Values of the pushed-forward function. -/
theorem ev_pushToP1In (j : Y ⟶ X) [IsOpenImmersion j] (σ : ToP1 Y) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Y) (hy : ptOf y ∈ σ.U)
    (hy' : ptOf (y ≫ j) ∈ (pushToP1In j σ).U) :
    ev (y ≫ j) hy' (pushToP1In j σ).f = ev y hy σ.f := by
  rw [ImagePlane.ev_comp]
  change ev y _ (j.app (j ''ᵁ σ.U) ((j.appIso σ.U).inv σ.f)) = _
  rw [app_appIso_inv_apply]
  have e : Y.presheaf.map (eqToHom (j.preimage_image_eq σ.U)).op =
      Y.presheaf.map (homOfLE (j.preimage_image_eq σ.U).le).op :=
    congrArg (fun i : (j ⁻¹ᵁ j ''ᵁ σ.U) ⟶ σ.U => Y.presheaf.map i.op) (Subsingleton.elim _ _)
  rw [e]
  exact ev_res y _ _ σ.f

/-- **Pulling a map to `P¹` on `O` back along `h` with `h⁻¹O = ⊤`.** -/
def pullToP1 {O : X.Opens} (σ : ToP1In X O) (h : Y ⟶ X) (hO : h ⁻¹ᵁ O = ⊤) : ToP1 Y where
  U := h ⁻¹ᵁ σ.U
  V := h ⁻¹ᵁ σ.V
  cover := by rw [← Scheme.Hom.preimage_sup, σ.cover, hO]
  f := h.app σ.U σ.f
  g := h.app σ.V σ.g
  inv := by
    have n1 := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_left : σ.U ⊓ σ.V ≤ σ.U)).op) σ.f
    have n2 := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_right : σ.U ⊓ σ.V ≤ σ.V)).op) σ.g
    simp only [ConcreteCategory.comp_apply] at n1 n2
    have e := congrArg (h.app (σ.U ⊓ σ.V)) σ.inv
    rw [map_mul, map_one, n1, n2] at e
    exact e
  basicOpen_f := by rw [← Scheme.preimage_basicOpen, σ.basicOpen_f]; rfl
  basicOpen_g := by rw [← Scheme.preimage_basicOpen, σ.basicOpen_g]; rfl

theorem val_pullToP1_of_mem {O : X.Opens} (σ : ToP1In X O) (h : Y ⟶ X) (hO : h ⁻¹ᵁ O = ⊤)
    {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ Y) (hy : ptOf (y ≫ h) ∈ σ.U) :
    (pullToP1 σ h hO).val y = OnePoint.some (ev (y ≫ h) hy σ.f) := by
  rw [val_of_mem (pullToP1 σ h hO) y hy]
  rw [ImagePlane.ev_comp]
  rfl

theorem val_pullToP1_of_not_mem {O : X.Opens} (σ : ToP1In X O) (h : Y ⟶ X) (hO : h ⁻¹ᵁ O = ⊤)
    {K : Type} [Field K] (y : Spec (CommRingCat.of K) ⟶ Y) (hy : ptOf (y ≫ h) ∉ σ.U) :
    (pullToP1 σ h hO).val y = OnePoint.infty :=
  val_of_not_mem (pullToP1 σ h hO) y hy

end Transport

end MCRQuot

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# mcr-quot, part 22: (B-desc-map) `QuotientDescendsMapQ` proved
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3
open TopologicalSpace Opposite

/-- The inclusion of the generic fibre `𝒴_ℚ → 𝒴`. -/
abbrev genJ {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) :
    (genFib 𝒴).left ⟶ 𝒴.left :=
  pullback.fst 𝒴.hom (specRatToZloc p)

instance isOpenImmersion_genJ {p : ℕ} [Fact p.Prime] (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) :
    IsOpenImmersion (genJ 𝒴) :=
  MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_specRatToZloc p)

theorem ev_congr {K : Type} [Field K] {X : Scheme.{0}} {y y' : Spec (CommRingCat.of K) ⟶ X}
    (h : y = y') {O : X.Opens} (hx : ptOf y ∈ O) (hx' : ptOf y' ∈ O) (s : Γ(X, O)) :
    ev y hx s = ev y' hx' s := by
  subst h; rfl

theorem ev_appLE {K : Type} [Field K] {X Y : Scheme.{0}} (h : Y ⟶ X)
    (y : Spec (CommRingCat.of K) ⟶ Y) {O : X.Opens} {O' : Y.Opens} (e : O' ≤ h ⁻¹ᵁ O)
    (hy : ptOf y ∈ O') (hy' : ptOf (y ≫ h) ∈ O) (s : Γ(X, O)) :
    ev y hy (h.appLE O O' e s) = ev (y ≫ h) hy' s := by
  rw [ImagePlane.ev_comp y h hy' s]
  change ev y hy (Y.presheaf.map (homOfLE e).op (h.app O s)) = _
  exact ev_res y e hy (h.app O s)

section Invariance

variable {p : ℕ} [Fact p.Prime] {𝒴 : Over (Spec (CommRingCat.of (Zloc p)))}
  (hS : SmoothOfRelativeDimension 1 𝒴.hom) {G : Subgroup (Aut 𝒴.left)}
  (hover : ∀ g ∈ G, g.asIso.hom ≫ 𝒴.hom = 𝒴.hom) (σ : ToP1 (genFib 𝒴).left)
  (hσ : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (g : Aut 𝒴.left), g ∈ G →
    s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) =
      s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p) ≫ g.asIso.hom →
    σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left)

include hS in
/-- Closed points of the generic fibre give `ℚ̄`-points; the generic fibre is Jacobson. -/
theorem genFib_jacobson : JacobsonSpace (genFib 𝒴).left := by
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := genFib_smooth 𝒴 hS
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.jacobsonSpace (genFib 𝒴).hom

include hS hσ in
/-- **The pushed-forward chart `U` is `G`-stable** (closed points carry `ℚ̄`-points). -/
theorem pushU_stable (g : Aut 𝒴.left) (hg : g ∈ G) (x : 𝒴.left)
    (hx : x ∈ (pushToP1In (genJ 𝒴) σ).U) : g.asIso.hom x ∈ (pushToP1In (genJ 𝒴) σ).U := by
  haveI := genFib_jacobson hS
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := genFib_smooth 𝒴 hS
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 _
  by_contra hgx
  set j := genJ 𝒴 with hj
  set σX := pushToP1In j σ with hσX
  let S : Set (genFib 𝒴).left :=
    j ⁻¹' (σX.U : Set 𝒴.left) ∩ (j ≫ g.asIso.hom) ⁻¹' (σX.U : Set 𝒴.left)ᶜ
  have hSlc : IsLocallyClosed S :=
    ((σX.U.isOpen.preimage j.continuous).isLocallyClosed).inter
      ((σX.U.isOpen.isClosed_compl.preimage (j ≫ g.asIso.hom).continuous).isLocallyClosed)
  obtain ⟨y, hy⟩ : x ∈ Set.range j := j.image_le_opensRange _ hx
  have hne : S.Nonempty := ⟨y, by rw [← hy] at hx hgx; exact ⟨hx, hgx⟩⟩
  obtain ⟨c, hcS, hcc⟩ := nonempty_inter_closedPoints hne hSlc
  obtain ⟨emb, s, hs⟩ := exists_qbarPt (genFib 𝒴) c (mem_closedPoints_iff.mp hcc)
  have hpts : ptOf s.left = c := by
    change (Scheme.SpecToEquivOfField Qbar _ s.left).1 = c
    rw [hs, Equiv.apply_symm_apply]
  obtain ⟨s', hs'⟩ := genFib_pt 𝒴 (s.left ≫ j ≫ g.asIso.hom)
  have hv := hσ s s' g hg hs'
  have hcU : c ∈ σ.U := by
    have h1 := hcS.1
    change j c ∈ j ''ᵁ σ.U at h1
    obtain ⟨c', hc', he⟩ := h1
    rwa [← j.isOpenEmbedding.injective he]
  have hs'U : ptOf s'.left ∉ σ.U := by
    intro h
    apply hcS.2
    have e1 : j (ptOf s'.left) = (j ≫ g.asIso.hom) c := by
      rw [← hpts]
      change qbarPoint (s'.left ≫ j) = qbarPoint ((s.left ≫ j) ≫ g.asIso.hom)
      exact congrArg _ (hs'.trans (Category.assoc _ _ _).symm)
    change (j ≫ g.asIso.hom) c ∈ (j ''ᵁ σ.U : Set 𝒴.left)
    rw [← e1]
    exact ⟨_, h, rfl⟩
  rw [val_of_mem σ s.left (hpts ▸ hcU), val_of_not_mem σ s'.left hs'U] at hv
  exact OnePoint.coe_ne_infty _ hv

include hS hover hσ in
theorem pushU_stable_iff (g : Aut 𝒴.left) (hg : g ∈ G) (x : 𝒴.left) :
    g.asIso.hom x ∈ (pushToP1In (genJ 𝒴) σ).U ↔ x ∈ (pushToP1In (genJ 𝒴) σ).U := by
  constructor
  · intro h
    have := pushU_stable hS σ hσ g⁻¹ (G.inv_mem hg) _ h
    have e : (g⁻¹).asIso.hom (g.asIso.hom x) = x := by
      simp only [Aut.inv_asIso, Iso.symm_hom]
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rwa [e] at this
  · exact pushU_stable hS σ hσ g hg x

include hS hover hσ in
/-- **The pushed-forward function `f` is `G`-invariant** (`𝒴` reduced; a nonzero difference
would be nonzero at a closed point of the generic fibre, i.e. at a `ℚ̄`-point). -/
theorem pushF_invariant (g : Aut 𝒴.left) (hg : g ∈ G) :
    g.asIso.hom.appLE (pushToP1In (genJ 𝒴) σ).U (pushToP1In (genJ 𝒴) σ).U
      (fun x hx => (pushU_stable_iff hS hover σ hσ g hg x).2 hx) (pushToP1In (genJ 𝒴) σ).f =
      (pushToP1In (genJ 𝒴) σ).f := by
  haveI := genFib_jacobson hS
  haveI : SmoothOfRelativeDimension 1 (genFib 𝒴).hom := genFib_smooth 𝒴 hS
  haveI : Smooth (genFib 𝒴).hom := SmoothOfRelativeDimension.smooth 1 _
  haveI : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 𝒴.hom
  haveI : IsReduced 𝒴.left := isReduced_of_smooth_zloc 𝒴
  set j := genJ 𝒴 with hj
  set σX := pushToP1In j σ with hσX
  set d := g.asIso.hom.appLE σX.U σX.U
      (fun x hx => (pushU_stable_iff hS hover σ hσ g hg x).2 hx) σX.f - σX.f with hd
  rw [← sub_eq_zero, ← hd, ← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hx⟩ : ((𝒴.left.basicOpen d : 𝒴.left.Opens) : Set 𝒴.left).Nonempty := by
    by_contra h0
    apply hne
    ext1
    simpa [Set.not_nonempty_iff_eq_empty] using h0
  have hxU : x ∈ σX.U := 𝒴.left.basicOpen_le d hx
  obtain ⟨y, hy⟩ : x ∈ Set.range j := j.image_le_opensRange _ hxU
  let B : Set (genFib 𝒴).left := j ⁻¹' (𝒴.left.basicOpen d : Set 𝒴.left)
  have hBo : IsOpen B := (𝒴.left.basicOpen d).isOpen.preimage j.continuous
  have hyB : y ∈ B := by
    change j y ∈ (𝒴.left.basicOpen d : Set 𝒴.left)
    rw [hy]; exact hx
  obtain ⟨c, hcB, hcc⟩ := nonempty_inter_closedPoints ⟨y, hyB⟩ hBo.isLocallyClosed
  obtain ⟨emb, s, hs⟩ := exists_qbarPt (genFib 𝒴) c (mem_closedPoints_iff.mp hcc)
  let t : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒴).left := s.left
  have hpts : ptOf t = c := by
    change (Scheme.SpecToEquivOfField Qbar _ s.left).1 = c
    rw [hs, Equiv.apply_symm_apply]
  have hcX : j c ∈ σX.U := 𝒴.left.basicOpen_le d hcB
  have hcU : c ∈ σ.U := by
    obtain ⟨c', hc', he⟩ := hcX
    rwa [← j.isOpenEmbedding.injective he]
  obtain ⟨s', hs'⟩ := genFib_pt 𝒴 (t ≫ j ≫ g.asIso.hom)
  let t' : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒴).left := s'.left
  have hs't : t' ≫ j = t ≫ j ≫ g.asIso.hom := hs'
  have hv : σ.val t = σ.val t' := hσ s s' g hg hs'
  have hgc : g.asIso.hom (j c) ∈ σX.U := (pushU_stable_iff hS hover σ hσ g hg _).2 hcX
  have hs'X : ptOf (t' ≫ j) ∈ σX.U := by
    have e2 : qbarPoint (t' ≫ j) = g.asIso.hom (j (ptOf t)) := congrArg qbarPoint hs't
    change qbarPoint (t' ≫ j) ∈ _
    rw [e2, hpts]; exact hgc
  have hs'U : ptOf t' ∈ σ.U := by
    obtain ⟨c', hc', he⟩ := hs'X
    have : c' = ptOf t' := j.isOpenEmbedding.injective (he.trans rfl)
    rwa [← this]
  have hsX : ptOf (t ≫ j) ∈ σX.U := by
    change j (ptOf t) ∈ _; rw [hpts]; exact hcX
  rw [val_of_mem σ t (hpts ▸ hcU), val_of_mem σ t' hs'U] at hv
  have hv' := OnePoint.coe_injective hv
  have hdx : ptOf (t ≫ j) ∈ 𝒴.left.basicOpen d := by
    change j (ptOf t) ∈ _; rw [hpts]; exact hcB
  apply (ev_eq_zero_iff (t ≫ j) hsX d).1 _ hdx
  rw [hd, map_sub, sub_eq_zero]
  have hgX : ptOf ((t ≫ j) ≫ g.asIso.hom) ∈ σX.U := by
    rw [Category.assoc, ← hs't]; exact hs'X
  rw [ev_appLE (O := σX.U) (O' := σX.U) g.asIso.hom (t ≫ j)
    (fun x hx => (pushU_stable_iff hS hover σ hσ g hg x).2 hx) hsX hgX]
  rw [ev_congr (show (t ≫ j) ≫ g.asIso.hom = t' ≫ j by rw [Category.assoc, hs't]) hgX hs'X]
  rw [ev_pushToP1In j σ t' hs'U hs'X, ev_pushToP1In j σ t (hpts ▸ hcU) hsX]
  exact hv'.symm

end Invariance

end MCRQuot

#print axioms MCRQuot.exists_unit_congr
#print axioms MCRQuot.mem_orbit_of_twistEq
#print axioms MCRQuot.twistEq_of_mem_fibreAut
#print axioms MCRQuot.exists_comp_smul_eq
#print axioms MCRQuot.exists_eq_comp_of_isGQuotient
#print axioms MCRQuot.val_injective_of_isP1Coordinate
#print axioms MCRQuot.coordinateFromSections_of
#print axioms MCRQuot.infinite_qbarPoints
#print axioms MCRQuot.fibreAutTame_of
#print axioms MCRQuot.residue_trivial_of_fixesOn
#print axioms MCRQuot.cMSectionsDisjoint_of
#print axioms MCRQuot.modelCoordinateResidue_of_mcrQuot
#print axioms MCRQuot.isUnit_sub_of_disjoint
#print axioms MCRQuot.p1ThreePoints_of
#print axioms MCRQuot.coordinateFromSections_of'
#print axioms MCRQuot.modelCoordinateResidue_of_mcrQuot'
#print axioms MCRQuot.genericQuotientP1_of
#print axioms MCRQuot.modelCoordinateResidue_of_mcrQuot''
#print axioms MCRQuot.gQuotientPointOrbits
#print axioms MCRQuot.qbarPointsConjugate
#print axioms MCRQuot.autOInnerCard
#print axioms MCRQuot.twistClassCard
#print axioms MCRQuot.fibreAutTame_of'
#print axioms MCRQuot.cMSectionsDisjoint_of'
#print axioms MCRQuot.modelCoordinateResidue_final
#print axioms MCRQuot.translate
#print axioms MCRQuot.stabFixesClosure
#print axioms MCRQuot.cMSectionsDisjoint_of''
#print axioms MCRQuot.p1Translate
#print axioms MCRQuot.coordinateFromSections_of''
#print axioms MCRQuot.modelCoordinateResidue_final2
#print axioms MCRQuot.fibreAutFixFinite_of
#print axioms MCRQuot.fibreAutTame_of''
#print axioms MCRQuot.modelCoordinateResidue_final3
#print axioms MCRQuot.curveClosedQbarFinite
#print axioms MCRQuot.fibreAutFixFinite_of'
#print axioms MCRQuot.modelCoordinateResidue_final4
#print axioms MCRQuot.modelYIrreducible_of_coverModelN
#print axioms MCRQuot.modelCoordinateResidue_final5
#print axioms MCRQuot.eq_one_of_fixes_all
#print axioms MCRQuot.cMStabInvolution_of
#print axioms MCRQuot.modelCoordinateResidue_final6
#print axioms MCRQuot.isGQuotient_surjective
#print axioms MCRQuot.exists_lift_qbar
#print axioms MCRQuot.quotientDescendsQ_of
#print axioms MCRQuot.modelCoordinateResidue_final7
#print axioms MCRQuot.app_injective_of_isGQuotient
#print axioms MCRQuot.exists_descend_section
#print axioms MCRQuot.preimage_imgOpen
#print axioms MCRQuot.exists_descend_toP1In
