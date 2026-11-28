import ZInQKernel.Contrib.OneProof.RC.ModelGeneric7.FormulaTransport
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.ReductionInjective

/-! **The odd Vélu point map commutes with reduction on prime-to-residue torsion**
(rc-model-generic7, item 3, R1′).

Setting: `A` a valuation subring of an algebraically closed field `L`, `W` a Weierstrass curve over
`A` with good reduction (`(W.map (residue A)).Δ ≠ 0`), `reduceHom` the vendored reduction of points.

* `Red A a ra`: `a ∈ A` and its residue is `ra`; closed under the ring operations and under division
  by elements with nonzero residue.
* `coordsOrZero_reduceHom`: on torsion prime to the residue characteristic, reduction acts on
  coordinates by the residue map.
* `veluX_red`, `veluY_red`: the vendored odd Vélu formulas at the summing set of `Q₀` reduce to
  the formulas at the summing set of the reduced point, at every point `(x, y)` of torsion prime to
  the residue characteristic outside `⟨Q₀⟩`.
* `oddVelu_reduceHom` (R1′): for the odd Vélu point maps `φ` over `L` (at `Q₀`) and `φ̃` over the
  residue field (at the reduction of `Q₀`), both given by their formula (`OddStepFormula`) and
  kernel, and a model `V` over `A` of their targets, `reduceHom (φ P) = φ̃ (reduceHom P)` for every
  `P` with `m • P = 0`, `m` invertible in the residue field. The formula argument works term by
  term: such `P` off `⟨Q₀⟩` has integral coordinates and reduces off `⟨Q̃₀⟩`, so every denominator
  `x - x₀` is a unit (reduction is injective on prime-to-residue torsion, `reduceHom_injOn_torsion`).

Provenance: on the spot (c); background Silverman, AEC VII.3.1 (UNVERIFIED). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open ZInQ.Contrib.CloudB3RC53.ModularWeil (reduceHom_injOn_torsion eq_zero_of_reduceHom_eq_zero)

variable {L : Type} [Field L] [DecidableEq L] (A : ValuationSubring L)

/-- `a ∈ A` with residue `ra`. -/
def Red (a : L) (ra : ResidueField A) : Prop :=
  ∃ h : a ∈ A, residue A ⟨a, h⟩ = ra

namespace Red

variable {A}

theorem coe (a : A) : Red A (a : L) (residue A a) := ⟨a.2, rfl⟩

theorem add {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A (a + b) (ra + rb) := by
  obtain ⟨ha, rfl⟩ := ha
  obtain ⟨hb, rfl⟩ := hb
  exact ⟨add_mem ha hb, (map_add (residue A) ⟨a, ha⟩ ⟨b, hb⟩)⟩

theorem mul {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A (a * b) (ra * rb) := by
  obtain ⟨ha, rfl⟩ := ha
  obtain ⟨hb, rfl⟩ := hb
  exact ⟨mul_mem ha hb, (map_mul (residue A) ⟨a, ha⟩ ⟨b, hb⟩)⟩

theorem neg {a : L} {ra : ResidueField A} (ha : Red A a ra) : Red A (-a) (-ra) := by
  obtain ⟨ha, rfl⟩ := ha
  exact ⟨neg_mem ha, (map_neg (residue A) ⟨a, ha⟩)⟩

theorem sub {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A (a - b) (ra - rb) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

theorem one : Red A (1 : L) 1 := ⟨one_mem _, map_one (residue A)⟩

theorem zero : Red A (0 : L) 0 := ⟨zero_mem _, map_zero (residue A)⟩

theorem pow {a : L} {ra : ResidueField A} (ha : Red A a ra) (n : ℕ) : Red A (a ^ n) (ra ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one
  | succ n ih => rw [pow_succ, pow_succ]; exact Red.mul ih ha

theorem natCast (n : ℕ) : Red A (n : L) (n : ResidueField A) := by
  induction n with
  | zero => rw [Nat.cast_zero, Nat.cast_zero]; exact zero
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ]; exact Red.add ih one

theorem ofNat (n : ℕ) [n.AtLeastTwo] : Red A (OfNat.ofNat n : L) (OfNat.ofNat n) := by
  have := natCast (A := A) (OfNat.ofNat n)
  simpa only [Nat.cast_ofNat] using this

theorem inv {b : L} {rb : ResidueField A} (hb : Red A b rb) (hb0 : rb ≠ 0) : Red A b⁻¹ rb⁻¹ := by
  obtain ⟨hb, rfl⟩ := hb
  obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit _).mp hb0
  have hinv : ((u⁻¹ : Aˣ) : A).1 = b⁻¹ := by
    have h1 : ((u : A) : L) * ((u⁻¹ : Aˣ) : A) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  refine ⟨hinv ▸ ((u⁻¹ : Aˣ) : A).2, ?_⟩
  have : (⟨b⁻¹, hinv ▸ ((u⁻¹ : Aˣ) : A).2⟩ : A) = ((u⁻¹ : Aˣ) : A) := Subtype.ext hinv.symm
  rw [this, ← hu]
  exact (map_units_inv (residue A) u)

theorem div {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) (hb0 : rb ≠ 0) :
    Red A (a / b) (ra / rb) := by
  simpa [div_eq_mul_inv] using ha.mul (hb.inv hb0)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → L} {rf : ι → ResidueField A}
    (h : ∀ i ∈ s, Red A (f i) (rf i)) : Red A (∑ i ∈ s, f i) (∑ i ∈ s, rf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem unique {a : L} {ra ra₂ : ResidueField A} (h : Red A a ra) (h' : Red A a ra₂) : ra = ra₂ := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

end Red

variable {A}

open Classical in
/-- The residue of an element of `A` (zero off `A`). -/
def resL (a : L) : ResidueField A := if h : a ∈ A then residue A ⟨a, h⟩ else 0

theorem resL_of_mem {a : L} (h : a ∈ A) : resL (A := A) a = residue A ⟨a, h⟩ := by
  classical
  unfold resL
  rw [dif_pos h]

theorem Red.resL {a : L} {ra : ResidueField A} (h : Red A a ra) : resL (A := A) a = ra := by
  obtain ⟨h, rfl⟩ := h
  exact resL_of_mem h

theorem red_resL {a : L} (h : a ∈ A) : Red A a (resL (A := A) a) :=
  ⟨h, (resL_of_mem h).symm⟩

variable [DecidableEq (ResidueField A)] (W : WeierstrassCurve A)

theorem red_a₁ : Red A (W.map A.subtype).a₁ (W.map (residue A)).a₁ := Red.coe W.a₁
theorem red_a₂ : Red A (W.map A.subtype).a₂ (W.map (residue A)).a₂ := Red.coe W.a₂
theorem red_a₃ : Red A (W.map A.subtype).a₃ (W.map (residue A)).a₃ := Red.coe W.a₃
theorem red_a₄ : Red A (W.map A.subtype).a₄ (W.map (residue A)).a₄ := Red.coe W.a₄

theorem red_veluGx {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A ((W.map A.subtype).veluGx a b) ((W.map (residue A)).veluGx ra rb) := by
  simp only [veluGx]
  exact ((((Red.ofNat 3).mul (ha.pow 2)).add (((Red.ofNat 2).mul (red_a₂ W)).mul ha)).add
    (red_a₄ W)).sub ((red_a₁ W).mul hb)

theorem red_veluGy {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A ((W.map A.subtype).veluGy a b) ((W.map (residue A)).veluGy ra rb) := by
  simp only [veluGy]
  exact ((((Red.ofNat 2).mul hb).add ((red_a₁ W).mul ha)).add (red_a₃ W)).neg

theorem red_veluT {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A ((W.map A.subtype).veluT a b) ((W.map (residue A)).veluT ra rb) := by
  simp only [veluT]
  exact ((Red.ofNat 2).mul (red_veluGx W ha hb)).sub ((red_a₁ W).mul (red_veluGy W ha hb))

theorem red_veluU {a b : L} {ra rb : ResidueField A} (ha : Red A a ra) (hb : Red A b rb) :
    Red A ((W.map A.subtype).veluU a b) ((W.map (residue A)).veluU ra rb) := by
  simp only [veluU]
  exact (red_veluGy W ha hb).pow 2

/-- The vendored odd `x`-formula reduces, for an integral summing set whose residues are distinct
from the residue of `x`. -/
theorem veluX_red (S : Finset (L × L)) (hS : ∀ q ∈ S, q.1 ∈ A ∧ q.2 ∈ A)
    (hinj : Set.InjOn (Prod.map (resL (A := A)) (resL (A := A))) S)
    {x : L} {rx : ResidueField A} (hx : Red A x rx) (hsep : ∀ q ∈ S, rx ≠ resL (A := A) q.1) :
    Red A ((W.map A.subtype).veluX S x)
      ((W.map (residue A)).veluX (S.image (Prod.map (resL (A := A)) (resL (A := A)))) rx) := by
  simp only [veluX]
  rw [Finset.sum_image hinj]
  refine hx.add (Red.sum _ fun q hq => ?_)
  have h1 := red_resL (A := A) (hS q hq).1
  have h2 := red_resL (A := A) (hS q hq).2
  have hd : rx - resL (A := A) q.1 ≠ 0 := sub_ne_zero.mpr (hsep q hq)
  exact ((red_veluT W h1 h2).div (hx.sub h1) hd).add
    ((red_veluU W h1 h2).div ((hx.sub h1).pow 2) (pow_ne_zero 2 hd))

/-- The vendored odd `y`-formula reduces, under the same hypotheses. -/
theorem veluY_red (S : Finset (L × L)) (hS : ∀ q ∈ S, q.1 ∈ A ∧ q.2 ∈ A)
    (hinj : Set.InjOn (Prod.map (resL (A := A)) (resL (A := A))) S)
    {x y : L} {rx ry : ResidueField A} (hx : Red A x rx) (hy : Red A y ry)
    (hsep : ∀ q ∈ S, rx ≠ resL (A := A) q.1) :
    Red A ((W.map A.subtype).veluY S x y)
      ((W.map (residue A)).veluY (S.image (Prod.map (resL (A := A)) (resL (A := A)))) rx ry) := by
  simp only [veluY]
  rw [Finset.sum_image hinj]
  refine hy.sub (Red.sum _ fun q hq => ?_)
  have h1 := red_resL (A := A) (hS q hq).1
  have h2 := red_resL (A := A) (hS q hq).2
  have hd : rx - resL (A := A) q.1 ≠ 0 := sub_ne_zero.mpr (hsep q hq)
  have hdx := hx.sub h1
  exact ((((red_veluU W h1 h2).mul ((((Red.ofNat 2).mul hy).add ((red_a₁ W).mul hx)).add
      (red_a₃ W))).div (hdx.pow 3) (pow_ne_zero 3 hd)).add
    (((red_veluT W h1 h2).mul ((((red_a₁ W).mul hdx).add hy).sub h2)).div (hdx.pow 2)
      (pow_ne_zero 2 hd))).add
    ((((red_a₁ W).mul (red_veluU W h1 h2)).sub ((red_veluGx W h1 h2).mul (red_veluGy W h1 h2))).div
      (hdx.pow 2) (pow_ne_zero 2 hd))

variable {W}

/-- Nonzero torsion prime to the residue characteristic has integral coordinates. -/
theorem mem_of_torsion (hΔ : (W.map (residue A)).Δ ≠ 0) {m : ℕ} (hm : (m : ResidueField A) ≠ 0)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hP : m • (Point.some x y h : (W.map A.subtype).toAffine.Point) = 0) : x ∈ A ∧ y ∈ A := by
  by_cases hx : x ∈ A
  · exact ⟨hx, Affine.Y_mem_of_X_mem W h.1 hx⟩
  · exfalso
    have h0 : reduceHom hΔ (Point.some x y h) = 0 := reducePoint_some_of_notMem hΔ h hx
    exact Point.some_ne_zero h (eq_zero_of_reduceHom_eq_zero hΔ hm hP h0)

/-- On torsion prime to the residue characteristic, reduction acts on coordinates by the residue
map. -/
theorem coordsOrZero_reduceHom (hΔ : (W.map (residue A)).Δ ≠ 0) {m : ℕ}
    (hm : (m : ResidueField A) ≠ 0) (P : (W.map A.subtype).toAffine.Point) (hP : m • P = 0) :
    (reduceHom hΔ P).coordsOrZero = Prod.map (resL (A := A)) (resL (A := A)) P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · change ((0, 0) : ResidueField A × ResidueField A) = (resL (A := A) 0, resL (A := A) 0)
    rw [resL_of_mem (zero_mem A)]
    exact Prod.ext (map_zero _).symm (map_zero _).symm
  · obtain ⟨hx, hy⟩ := mem_of_torsion hΔ hm h hP
    change (reducePoint hΔ (Point.some x y h)).coordsOrZero = _
    rw [reducePoint_some_of_mem hΔ h hx]
    simp [Point.coordsOrZero, resL_of_mem hx, resL_of_mem hy]

/-- Reduction of nonzero prime-to-residue torsion is nonzero. -/
theorem reduceHom_ne_zero (hΔ : (W.map (residue A)).Δ ≠ 0) {m : ℕ}
    (hm : (m : ResidueField A) ≠ 0) {P : (W.map A.subtype).toAffine.Point} (hP : m • P = 0)
    (hP0 : P ≠ 0) : reduceHom hΔ P ≠ 0 :=
  fun h => hP0 (eq_zero_of_reduceHom_eq_zero hΔ hm hP h)

/-- The summing set of the reduced point is the residue image of the summing set. -/
theorem oddOrderSummingSet_reduceHom (hΔ : (W.map (residue A)).Δ ≠ 0) {p : ℕ}
    (hpk : (p : ResidueField A) ≠ 0) (Q₀ : (W.map A.subtype).toAffine.Point)
    (hQ₀ : p • Q₀ = 0) (n : ℕ) :
    (W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q₀) n =
      ((W.map A.subtype).oddOrderSummingSet Q₀ n).image
        (Prod.map (resL (A := A)) (resL (A := A))) := by
  rw [oddOrderSummingSet, oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  change (k • reduceHom hΔ Q₀).coordsOrZero = Prod.map resL resL (k • Q₀).coordsOrZero
  rw [← map_nsmul, coordsOrZero_reduceHom hΔ hpk]
  rw [smul_comm, hQ₀, smul_zero]

/-- **R1′: the odd Vélu point map commutes with reduction on prime-to-residue torsion.** -/
theorem oddVelu_reduceHom [IsAlgClosed L] [IsAlgClosed (ResidueField A)]
    (hΔ : (W.map (residue A)).Δ ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpk : (p : ResidueField A) ≠ 0) (Q₀ : (W.map A.subtype).toAffine.Point)
    (hQ₀ : addOrderOf Q₀ = p) {V₁ : WeierstrassCurve L} {V₂ : WeierstrassCurve (ResidueField A)}
    (φ : (W.map A.subtype).toAffine.Point →+ V₁.toAffine.Point)
    (φ' : (W.map (residue A)).toAffine.Point →+ V₂.toAffine.Point)
    (hφ : φ.ker = AddSubgroup.zmultiples Q₀) (hφf : OddStepFormula (W.map A.subtype) Q₀ p φ)
    (hφ' : φ'.ker = AddSubgroup.zmultiples (reduceHom hΔ Q₀))
    (hφf' : OddStepFormula (W.map (residue A)) (reduceHom hΔ Q₀) p φ')
    (V : WeierstrassCurve A) (hΔV : (V.map (residue A)).Δ ≠ 0) (hV₁ : V.map A.subtype = V₁)
    (hV₂ : V.map (residue A) = V₂) {m : ℕ} (hm : (m : ResidueField A) ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) (hP : m • P = 0) :
    reduceHom hΔV (pointCast hV₁.symm (φ P)) = pointCast hV₂.symm (φ' (reduceHom hΔ P)) := by
  have hpQ : p • Q₀ = 0 := hQ₀ ▸ addOrderOf_nsmul_eq_zero Q₀
  have hmp : ((m * p : ℕ) : ResidueField A) ≠ 0 := by push_cast; exact mul_ne_zero hm hpk
  have hmpQ : (m * p) • Q₀ = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (hQ₀ ▸ dvd_mul_left p m)
  have htors : ∀ k : ℤ, (m * p) • (k • Q₀) = 0 := fun k => by
    rw [smul_comm, hmpQ, smul_zero]
  have hPt : (m * p) • P = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp ((addOrderOf_dvd_of_nsmul_eq_zero hP).trans
      (dvd_mul_right m p))
  by_cases hPin : P ∈ AddSubgroup.zmultiples Q₀
  · have h0 : φ P = 0 := by rw [← AddMonoidHom.mem_ker, hφ]; exact hPin
    have h0' : φ' (reduceHom hΔ P) = 0 := by
      rw [← AddMonoidHom.mem_ker, hφ', ← AddMonoidHom.map_zmultiples]
      exact AddSubgroup.mem_map_of_mem _ hPin
    rw [h0, h0', map_zero, map_zero, map_zero]
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (AddSubgroup.zero_mem _) hPin
  obtain ⟨hxA, hyA⟩ := mem_of_torsion hΔ hm h hP
  -- the reduced point and its position
  have hns : (W.map (residue A)).toAffine.Nonsingular (resL (A := A) x) (resL (A := A) y) := by
    rw [resL_of_mem hxA, resL_of_mem hyA]
    exact Affine.nonsingular_residue W hΔ (x := ⟨x, hxA⟩) (y := ⟨y, hyA⟩) h.1
  have hred : reduceHom hΔ (Point.some x y h) =
      Point.some (resL (A := A) x) (resL (A := A) y) hns := by
    exact (reducePoint_some_of_mem hΔ h hxA).trans (by congr 1 <;> rw [resL_of_mem])
  have hPin' : reduceHom hΔ (Point.some x y h) ∉ AddSubgroup.zmultiples (reduceHom hΔ Q₀) := by
    rintro hk
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hk
    rw [← map_zsmul] at hk
    exact hPin (AddSubgroup.mem_zmultiples_iff.mpr
      ⟨k, reduceHom_injOn_torsion hΔ hmp (htors k) hPt hk⟩)
  -- the summing set
  set S := (W.map A.subtype).oddOrderSummingSet Q₀ (p / 2) with hSdef
  have hp2 : p / 2 < p := Nat.div_lt_self hp.pos (by norm_num)
  have hS : ∀ q ∈ S, ∃ k : ℕ, 1 ≤ k ∧ k ≤ p / 2 ∧ (k • Q₀).coordsOrZero = q := fun q hq =>
    (mem_oddOrderSummingSet _).mp hq
  have hkQ0 : ∀ k : ℕ, 1 ≤ k → k ≤ p / 2 → k • Q₀ ≠ 0 := by
    intro k hk1 hk2 h0
    have := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hQ₀] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hkt : ∀ k : ℕ, (m * p) • (k • Q₀) = 0 := fun k => by
    have := htors k; rwa [natCast_zsmul] at this
  have hSA : ∀ q ∈ S, q.1 ∈ A ∧ q.2 ∈ A := by
    intro q hq
    obtain ⟨k, hk1, hk2, rfl⟩ := hS q hq
    rcases hkp : k • Q₀ with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hkp (hkQ0 k hk1 hk2)
    · exact mem_of_torsion hΔ hmp h₀ (hkp ▸ hkt k)
  have hcoords : ∀ k : ℕ, (reduceHom hΔ (k • Q₀)).coordsOrZero =
      Prod.map (resL (A := A)) (resL (A := A)) (k • Q₀).coordsOrZero :=
    fun k => coordsOrZero_reduceHom hΔ hmp _ (hkt k)
  have hpt_eq : ∀ {V : WeierstrassCurve (ResidueField A)} {R R' : V.toAffine.Point}, R ≠ 0 →
      R' ≠ 0 → R.coordsOrZero = R'.coordsOrZero → R = R' := by
    intro V R R' hR hR' hc
    exact PtRel.eq ⟨⟨fun e => absurd e hR, fun e => absurd e hR'⟩, hc⟩
  have hinj : Set.InjOn (Prod.map (resL (A := A)) (resL (A := A))) S := by
    intro q hq q' hq' hqq
    obtain ⟨k, hk1, hk2, rfl⟩ := hS q hq
    obtain ⟨k', hk1', hk2', rfl⟩ := hS q' hq'
    have hr : reduceHom hΔ (k • Q₀) = reduceHom hΔ (k' • Q₀) :=
      hpt_eq (reduceHom_ne_zero hΔ hmp (hkt k) (hkQ0 k hk1 hk2))
        (reduceHom_ne_zero hΔ hmp (hkt k') (hkQ0 k' hk1' hk2'))
        (by rw [hcoords, hcoords, hqq])
    rw [reduceHom_injOn_torsion hΔ hmp (hkt k) (hkt k') hr]
  have hsep : ∀ q ∈ S, resL (A := A) x ≠ resL (A := A) q.1 := by
    intro q hq hxq
    obtain ⟨k, hk1, hk2, rfl⟩ := hS q hq
    rcases hkp : k • Q₀ with _ | ⟨x₀, y₀, h₀⟩
    · exact hkQ0 k hk1 hk2 hkp
    have hc := hcoords k
    rw [hkp] at hc hxq
    have hne := reduceHom_ne_zero hΔ hmp (hkp ▸ hkt k) (Point.some_ne_zero h₀)
    rcases hR : reduceHom hΔ (Point.some x₀ y₀ h₀) with _ | ⟨x₁, y₁, h₁⟩
    · exact hne hR
    rw [hR] at hc
    simp only [Point.coordsOrZero, Prod.map, Prod.mk.injEq] at hc hxq
    have hxx : resL (A := A) x = x₁ := hxq.trans hc.1.symm
    -- same x-coordinate: the reduced point is ± the reduction of `k • Q₀`
    have hR' : reduceHom hΔ (Point.some x y h) = reduceHom hΔ (k • Q₀) ∨
        reduceHom hΔ (Point.some x y h) = -reduceHom hΔ (k • Q₀) := by
      rw [hred, hkp, hR]
      rcases Y_eq_of_X_eq hns.1 h₁.1 hxx with hy | hy
      · left; simp only [Point.some.injEq]; exact ⟨hxx, hy⟩
      · right; rw [Point.neg_some]; simp only [Point.some.injEq]; exact ⟨hxx, hy⟩
    apply hPin'
    rcases hR' with hR' | hR'
    · rw [hR', map_nsmul]; exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _
    · rw [hR', map_nsmul]
      exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _)
  -- the two formulas
  obtain ⟨hne, hco⟩ := hφf x y h hPin
  rw [hred] at hPin' ⊢
  obtain ⟨hne', hco'⟩ := hφf' _ _ _ hPin'
  rw [oddOrderSummingSet_reduceHom hΔ hpk Q₀ hpQ] at hco'
  have hX := veluX_red W S hSA hinj (red_resL (A := A) hxA) hsep
  have hY := veluY_red W S hSA hinj (red_resL (A := A) hxA) (red_resL (A := A) hyA) hsep
  -- compare
  rcases hR : pointCast hV₁.symm (φ (Point.some x y h)) with _ | ⟨X, Y, hXY⟩
  · exact absurd ((pointCast_injective hV₁.symm) (hR.trans (map_zero _).symm)) hne
  have hcR : (X, Y) = ((W.map A.subtype).veluX S x, (W.map A.subtype).veluY S x y) := by
    rw [← hco, ← (ptRel_pointCast hV₁.symm _).2, hR]; rfl
  simp only [Prod.mk.injEq] at hcR
  obtain ⟨rfl, rfl⟩ := hcR
  obtain ⟨hXA, hXr⟩ := hX
  obtain ⟨hYA, hYr⟩ := hY
  have hl : reduceHom hΔV (Point.some _ _ hXY) = Point.some _ _
      (Affine.nonsingular_residue V hΔV (x := ⟨_, hXA⟩) (y := ⟨_, hYA⟩) hXY.1) := by
    exact reducePoint_some_of_mem hΔV hXY hXA
  rw [hl]
  apply hpt_eq (Point.some_ne_zero _)
  · intro h0
    exact hne' ((pointCast_injective hV₂.symm) (h0.trans (map_zero _).symm))
  · rw [(ptRel_pointCast hV₂.symm _).2, hco']
    simp only [Point.coordsOrZero]
    rw [hXr, hYr]

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluX_red
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluY_red
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.coordsOrZero_reduceHom
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.oddOrderSummingSet_reduceHom
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.oddVelu_reduceHom
