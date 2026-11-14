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
