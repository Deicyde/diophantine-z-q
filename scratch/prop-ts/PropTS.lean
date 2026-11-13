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
fibre at `p`. (With `p ∤ [E : ℚ(X)]` the residue extensions are then separable.) -/
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
Let `p` be a prime with (a) `[E : ℚ(X)] < p` (so `p ∤ |G|`; stated in this weaker form so
that the leaf is implied by every version of the theorem), (b) the branch points pairwise distinct mod `p`
(every `b ∈ S` is `p`-integral, so it does not meet `∞`, and `v_p(b − b') = 0`), (c) automatic
(branch points rational), (d) no vertical ramification at `p`. Let `t ∈ ℚ ∖ S` (not a branch
point). Beckmann: the inertia group at `p` of the specialization `E_t` is conjugate to
`⟨g_b^{I_p(t, b)}⟩`, of order `e_b / gcd(e_b, I_p(t, b))`, where `I_p(t, b) = v_p(t − b)⁺` for
`b ∈ S` and `I_p(t, ∞) = (−v_p t)⁺`, and `E_t` is unramified at `p` if `t` meets no branch point
mod `p`. Hence (`e_b ∣ n b`): if `n b ∣ v_p(t − b)⁺` for all `b ∈ S` and `nInf ∣ (−v_p t)⁺`, then
the residue field `B/𝔓` of every prime `𝔓` of `B = ` (integral closure of `ℚ[X]` in `E`) over
`X − t`, embedded in `ℚ̄` in any way, is unramified at `p`. -/
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
proper curve, `π` finite and `E = ℚ(Y^{(1)})` for a `ℚ`-irreducible component `Y^{(1)}` whose
translates under a group acting over `ℚ` cover the fibre (then `π⁻¹(𝔸¹) ⊇ Spec B` and
`κ(y) ≅ B/𝔓`; h-b1 M2, M8). -/
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
