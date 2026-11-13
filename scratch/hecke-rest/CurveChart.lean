import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: `CurveNormChart` (hence `CurveGaloisChart`) reduced to two statements of curve
theory (assembled by `scratch/hecke-rest/assemble.py`)

Verbatim copies: `scratch/ts-hecke/TSHecke.lean` lines 6-889 (prop-ts prefix, with
`NormalizationModel`) 6444-6455 (`CurveNormChart`) and 6526-6551 (`NormalizationModelInf`, `CurveChartInf`), the
targets, inside `namespace TSHecke`;
`scratch/ts-hecke/TSHecke.lean` lines 4613-5002 and 5010-5173 (infra-smooth-dim's stalk dimensions,
curve-glue's `isDomain_of_dim_one`), 5725-5858 (ts-hecke's `exists_qbar_point`,
`eq_of_forall_qbar`); `scratch/image-plane/AlgDepProof.lean` lines 15-171 and 277-322 (the value calculus `ptOf`, `ev`,
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


end TSHeckeGal

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
# hecke-rest, Part 3d: `ChartProper` proved (valuative criterion)

`secMor Y W s : W → 𝔸¹` is locally of finite type, separated and quasi-compact by cancellation
from `W → Y → Spec ℚ` (all morphisms to `Spec ℚ` agree). For the existence part of the valuative
criterion (Mathlib's `IsProper.of_valuativeCriterion`, Stacks 0BX5): a valuation-ring point of
`𝔸¹` with a `Frac`-point of `W` lifts to `Y` (properness of `Y`); if its closed point left `W`, the
whole point would lie in `W'` (the other chart), and the pull-back `G` of `s'` would be a non-unit
of the valuation ring, while `s · s' = 1` at the generic point with `s` integral there.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- **Any two morphisms to `Spec ℚ` agree** (compiled). -/
theorem toSpecQ_eq {X : Scheme.{0}} (a b : X ⟶ Spec (CommRingCat.of ℚ)) : a = b := by
  have key : ∀ c : X ⟶ Spec (CommRingCat.of ℚ),
      c = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ c.appTop) := by
    intro c
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key a, key b]
  congr 2
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- `W → 𝔸¹ → Spec ℚ` is `W → Y → Spec ℚ`. -/
theorem secMor_comp (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens) (s : Γ(Y.left, W)) :
    secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])) = W.ι ≫ Y.hom :=
  toSpecQ_eq _ _

/-- **The value of `s` at a field point of `W` over `Spec ρ`** is `ρ X` (compiled). -/
theorem ev_secMor {K : Type} [Field K] {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens}
    (s : Γ(Y.left, W)) (q : Spec (CommRingCat.of K) ⟶ W.toScheme)
    (ρ : CommRingCat.of ℚ[X] ⟶ CommRingCat.of K) (h : q ≫ secMor Y W s = Spec.map ρ)
    (hx : ptOf (q ≫ W.ι) ∈ W) : ev (q ≫ W.ι) hx s = ρ X := by
  have e1 := ev_spec_top ρ X
  rw [← h, ev_comp] at e1
  have e2 : (secMor Y W s).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv X) =
      W.topIso.inv s := by
    change (secMor Y W s).appTop _ = _
    rw [secMor, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have e : (Spec.map (CommRingCat.ofHom (secHom Y W s))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv X) =
        (Scheme.ΓSpecIso Γ(Y.left, W)).inv (secHom Y W s X) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    rw [e, Scheme.Opens.toSpecΓ_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    show W.topIso.inv (Polynomial.eval₂ (cQ Y W) s X) = _
    rw [Polynomial.eval₂_X]
  rw [e2] at e1
  rw [ev_comp, ← e1]
  have e3 : W.ι.app W s = W.toScheme.presheaf.map (homOfLE (le_top : W.ι ⁻¹ᵁ W ≤ ⊤)).op
      (W.topIso.inv s) := by
    have hmor : ∀ {U₁ U₂ U₃ : (Y.left.Opens)ᵒᵖ} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₃),
        Y.left.presheaf.map a ≫ Y.left.presheaf.map b = Y.left.presheaf.map c := by
      intro U₁ U₂ U₃ a b c
      rw [← Functor.map_comp]
      exact congrArg _ (Subsingleton.elim _ _)
    change Y.left.presheaf.map _ s = Y.left.presheaf.map _ (Y.left.presheaf.map _ s)
    first
    | (erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl)
    | (simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl)
    | (erw [← ConcreteCategory.comp_apply, hmor])
  rw [e3]
  exact ev_res _ _ _ _

/-- **The existence part of the valuative criterion for a chart** (compiled). -/
theorem secMor_existence (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    (W W' : Y.left.Opens) (s : Γ(Y.left, W)) (s' : Γ(Y.left, W')) (hcov : W ⊔ W' = ⊤)
    (hinv : ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y.left) (hW : ptOf p ∈ W)
      (hW' : ptOf p ∈ W'), ev p hW s * ev p hW' s' = 1)
    (hbo : Y.left.basicOpen s' = W ⊓ W') :
    ValuativeCriterion.Existence (secMor Y W s) := by
  intro S
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of ℚ[X] ⟶ CommRingCat.of S.R, S.i₂ = Spec.map ρ :=
    ⟨Spec.preimage S.i₂, (Spec.map_preimage _).symm⟩
  let alg : CommRingCat.of S.R ⟶ CommRingCat.of S.K := CommRingCat.ofHom (algebraMap S.R S.K)
  have halg : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  let S' : ValuativeCommSq Y.hom :=
    { R := S.R, K := S.K, i₁ := S.i₁ ≫ W.ι,
      i₂ := S.i₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])),
      commSq := ⟨toSpecQ_eq _ _⟩ }
  have hYv : ValuativeCriterion Y.hom := by
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType)
        Y.hom := by
      rw [← IsProper.eq_valuativeCriterion]; infer_instance
    exact h.1.1.1
  obtain ⟨⟨l', hl1, hl2⟩⟩ := (hYv.existence S').exists_lift
  have hl1' : Spec.map alg ≫ l' = S.i₁ ≫ W.ι := hl1
  -- the value of `s` at the generic point
  have hxW : ptOf (S.i₁ ≫ W.ι) ∈ W := by
    rw [ptOf_comp]
    have : W.ι (ptOf S.i₁) ∈ Set.range W.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have hsq : S.i₁ ≫ secMor Y W s = Spec.map (ρ ≫ alg) := by
    rw [Spec.map_comp, ← hρ]; exact S.commSq.w
  have hsval : ev (S.i₁ ≫ W.ι) hxW s = algebraMap S.R S.K (ρ X) :=
    ev_secMor s S.i₁ (ρ ≫ alg) hsq hxW
  -- the closed point stays in `W`
  have hc : l' (IsLocalRing.closedPoint S.R) ∈ W := by
    by_contra hcW
    have hcW' : l' (IsLocalRing.closedPoint S.R) ∈ W' := by
      have : l' (IsLocalRing.closedPoint S.R) ∈ W ⊔ W' := by rw [hcov]; trivial
      rcases this with h | h
      · exact absurd h hcW
      · exact h
    have hall : ∀ x, l' x ∈ W' := fun x =>
      ((IsLocalRing.specializes_closedPoint x).map l'.continuous).mem_open W'.isOpen hcW'
    have pre : l' ⁻¹ᵁ W' = ⊤ := top_unique fun x _ => hall x
    set G : S.R := (Scheme.ΓSpecIso (CommRingCat.of S.R)).hom (res pre.ge (l'.app W' s')) with hGdef
    have hGinv : (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv G = res pre.ge (l'.app W' s') := by
      rw [hGdef, Iso.hom_inv_id_apply]
    have hG : G ∈ IsLocalRing.maximalIdeal S.R := by
      have h1 : l' (IsLocalRing.closedPoint S.R) ∉ Y.left.basicOpen s' := by
        rw [hbo]; exact fun h => hcW h.1
      have h2 : IsLocalRing.closedPoint S.R ∉ (Spec (CommRingCat.of S.R)).basicOpen
          (l'.app W' s') := by
        rw [← Scheme.preimage_basicOpen]; exact h1
      have h3 : IsLocalRing.closedPoint S.R ∉ (Spec (CommRingCat.of S.R)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of S.R)).inv G) := by
        rw [hGinv, res, Scheme.basicOpen_res, top_inf_eq]; exact h2
      rw [basicOpen_eq_of_affine] at h3
      by_contra hn
      exact h3 ((PrimeSpectrum.mem_basicOpen _ _).2 hn)
    -- the value of `s'` at the generic point
    have hxW' : ptOf (S.i₁ ≫ W.ι) ∈ W' := by
      rw [← hl1', ptOf_comp]; exact hall _
    have hs'val : ev (S.i₁ ≫ W.ι) hxW' s' = algebraMap S.R S.K G := by
      have hx2 : ptOf (Spec.map alg ≫ l') ∈ W' := by rw [ptOf_comp]; exact hall _
      have e : ev (Spec.map alg ≫ l') hx2 s' = algebraMap S.R S.K G := by
        rw [ev_comp, ← ev_res _ pre.ge (show ptOf (Spec.map alg) ∈
          (⊤ : (Spec (CommRingCat.of S.R)).Opens) from trivial), ← hGinv, ev_spec_top]
        rfl
      have hgen : ∀ (p : Spec (CommRingCat.of S.K) ⟶ Y.left) (hp : p = S.i₁ ≫ W.ι)
          (h1 : ptOf p ∈ W') (h2 : ptOf (S.i₁ ≫ W.ι) ∈ W'), ev p h1 s' = ev (S.i₁ ≫ W.ι) h2 s' := by
        rintro _ rfl _ _; rfl
      rw [← hgen _ hl1' hx2 hxW', e]
    have hprod := hinv S.K (S.i₁ ≫ W.ι) hxW hxW'
    rw [hsval, hs'val, ← map_mul, ← map_one (algebraMap S.R S.K)] at hprod
    have h1 : ρ X * G = 1 := halg hprod
    have hunit : IsUnit G := ⟨⟨G, ρ X, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 hG hunit
  have hrange : Set.range l' ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map l'.continuous).mem_open W.isOpen hc
  let l := IsOpenImmersion.lift W.ι l' hrange
  have hfl : Spec.map alg ≫ l = S.i₁ := by
    rw [← cancel_mono W.ι, Category.assoc, IsOpenImmersion.lift_fac]
    exact hl1'
  have hfr : l ≫ secMor Y W s = S.i₂ := by
    have h1 : Spec.map alg ≫ (l ≫ secMor Y W s) = Spec.map alg ≫ S.i₂ := by
      rw [← Category.assoc, hfl]; exact S.commSq.w
    rw [hρ] at h1 ⊢
    rw [← Spec.map_preimage (l ≫ secMor Y W s)] at h1 ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    have h2 := Spec.map_injective h1
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    apply halg
    exact congrArg (fun φ : CommRingCat.of ℚ[X] ⟶ CommRingCat.of S.K => φ.hom a) h2
  exact ⟨⟨⟨l, hfl, hfr⟩⟩⟩

/-- **A chart is proper** (compiled). -/
theorem secMor_isProper (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    (W W' : Y.left.Opens) (s : Γ(Y.left, W)) (s' : Γ(Y.left, W')) (hcov : W ⊔ W' = ⊤)
    (hinv : ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y.left) (hW : ptOf p ∈ W)
      (hW' : ptOf p ∈ W'), ev p hW s * ev p hW' s' = 1)
    (hbo : Y.left.basicOpen s' = W ⊓ W') : IsProper (secMor Y W s) := by
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have e := secMor_comp Y W s
  haveI : LocallyOfFiniteType
      (secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))) := by
    rw [e]; infer_instance
  haveI : IsSeparated (secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))) := by
    rw [e]; infer_instance
  haveI : QuasiCompact (secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))) := by
    rw [e]; infer_instance
  haveI : LocallyOfFiniteType (secMor Y W s) :=
    locallyOfFiniteType_of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])))
  haveI : IsSeparated (secMor Y W s) :=
    IsSeparated.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])))
  haveI : QuasiCompact (secMor Y W s) :=
    QuasiCompact.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])))
  exact IsProper.of_valuativeCriterion _
    (ValuativeCriterion.iff.2 ⟨secMor_existence Y W W' s s' hcov hinv hbo,
      IsSeparated.valuativeCriterion _⟩)

/-- **`ChartProper` holds** (compiled). -/
theorem chartProper : ChartProper := by
  intro Y π hP hS hfin
  haveI := hP
  refine ⟨secMor_isProper Y π.U π.V π.f π.g π.cover ?_ π.basicOpen_g,
    secMor_isProper Y π.V π.U π.g π.f (by rw [sup_comm]; exact π.cover) ?_
      (by rw [π.basicOpen_f, inf_comm])⟩
  · intro K _ p hU hV
    exact ev_f_mul_g π p hU hV
  · intro K _ p hV hU
    rw [mul_comm]
    exact ev_f_mul_g π p hU hV

/-- **`CurveNormChart` is a theorem** (compiled; with ts-hecke's `curveGaloisChart_of`,
`CurveGaloisChart` follows). -/
theorem curveNormChart : CurveNormChart := curveNormChart_of_proper chartProper

/-- **`CurveChartInf` is a theorem** (compiled). -/
theorem curveChartInf : CurveChartInf := curveChartInf_of_proper chartProper

end HeckeRestCurve

end

#print axioms HeckeRestCurve.chartProper
#print axioms HeckeRestCurve.curveNormChart
#print axioms HeckeRestCurve.curveChartInf
