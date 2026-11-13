import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: `CurveNormChart` (hence `CurveGaloisChart`) reduced to two statements of curve
theory (assembled by `scratch/hecke-rest/assemble.py`)

Verbatim copies: `scratch/ts-hecke/TSHecke.lean` lines 6-889 (prop-ts prefix, with
`NormalizationModel`) and 6444-6455 (`CurveNormChart`, the target, inside `namespace TSHecke`);
`scratch/image-plane/AlgDepProof.lean` lines 15-171 and 277-322 (the value calculus `ptOf`, `ev`,
`ev_res`, `ev_comp`, `ev_spec_top`, `val_of_mem`, ...). New work below the last banner.
No `sorry`, no `axiom`.
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


noncomputable section

namespace TSHecke

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PkgI3

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

end TSHecke

end

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
ideals are integrally closed is integrally closed. Glue, not a leaf. -/
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

end HeckeRestCurve

end

#print axioms HeckeRestCurve.curveNormChart_of
