import ZInQKernel.OneProof.H.TailO

/-! # st-qbar: `STQM` (QM abelian surfaces over `ℂ` with CM are defined over `ℚ̄`), proved

Task st-qbar (docs/research/st-qbar.md). Removes the leaf `shimuraTaniyamaQbar`: the only use of
`ShimuraTaniyamaQbar` is `stQM := stQM_lf7 l.shimuraTaniyamaQbar` (TailX), and `STQM` is proved here from fields
already in the bundles (R1R2fpRep, Y3Connected, T5, T35, HomLatticeCorr) and the chain's `ALFixedPoints`.

Method (fixed points of Atkin–Lehner twists): for CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` with `φ ∈ End_𝒪(A)`,
`ψ = ι(w)c/n` with `(w, c, n) = (i, 1+φ, 2), (j, 2φ−1, 3), (ij, φ, 6)` is an automorphism of `A` with
`ψ ι(a) ψ⁻¹ = ι(w a w⁻¹)` (integrality: `ι(w)c` kills `A[n]`, by `A[p] ≅ 𝒪/p𝒪` and a finite check mod `p`;
then the uniformization and `HomLatticeCorr` divide by `n`). So the `ℂ`-point `y` of `Y₃` is fixed by the
automorphism `g_α ≫ g_u` of `Y₃` (R1hecke), which moves a non-CM `ℚ̄`-point (`ALFixedPoints`). `Y₃` is an
irreducible proper smooth curve over `ℚ`: at its generic point `g_α ≫ g_u` would be the identity
(`ext_of_isDominant`), so the point of `y` is closed, with residue field finite over `ℚ`, and `y` comes from
`Y₃(ℚ̄)`; R1fp naturality then gives the model over `ℚ̄`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace GapST
open _root_.LeafQM _root_.LeafQM.AV

/-! ## Part A: `𝒪` modulo `p` (finite checks) -/

/-- Multiplication of coordinate vectors modulo `p` (the formula of `mulCoord`). -/
def mulZ {p : ℕ} (n m : Fin 4 → ZMod p) : Fin 4 → ZMod p :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

/-- Reduction of integer coordinates modulo `p`. -/
def red (p : ℕ) (n : Fin 4 → ℤ) : Fin 4 → ZMod p := fun i => (n i : ZMod p)

theorem red_mul (p : ℕ) (n m : Fin 4 → ℤ) : red p (mulCoord n m) = mulZ (red p n) (red p m) := by
  funext i; fin_cases i <;> simp [red, mulZ, mulCoord]

/-- Coordinates of an element of `𝒪`. -/
noncomputable def crd (a : O) : Fin 4 → ℤ := a.2.choose

theorem crd_spec (a : O) : (a : B) = ofInt (crd a) := a.2.choose_spec

theorem crd_eq {a : O} {n : Fin 4 → ℤ} (h : (a : B) = ofInt n) : crd a = n :=
  ofInt_injective ((crd_spec a).symm.trans h)

theorem crd_mul (a b : O) : crd (a * b) = mulCoord (crd a) (crd b) := by
  apply crd_eq
  rw [MulMemClass.coe_mul, crd_spec a, crd_spec b, ofInt_mul]

theorem crd_sub (a b : O) : crd (a - b) = crd a - crd b := by
  apply crd_eq
  rw [AddSubgroupClass.coe_sub, crd_spec a, crd_spec b, ofInt_sub]

theorem crd_one : crd 1 = ![1, 0, 0, 0] := by
  apply crd_eq
  rw [OneMemClass.coe_one, ofInt_one]

theorem natCast_mul_ofInt (p : ℕ) (k : Fin 4 → ℤ) :
    (p : B) * ofInt k = ofInt (fun i => (p : ℤ) * k i) := by
  ext <;> simp [ofInt] <;> ring

/-- `a ∈ p𝒪` iff its coordinates vanish modulo `p`. -/
theorem mem_iff (p : ℕ) (a : O) : (∃ c : O, a = (p : O) * c) ↔ red p (crd a) = 0 := by
  have hp : ((p : O) : B) = (p : B) := map_natCast O.subtype p
  constructor
  · rintro ⟨c, rfl⟩
    have : crd ((p : O) * c) = fun i => (p : ℤ) * crd c i := by
      apply crd_eq
      rw [MulMemClass.coe_mul, hp, crd_spec c, natCast_mul_ofInt]
    funext i
    simp [red, this]
  · intro h
    have hd : ∀ i, (p : ℤ) ∣ crd a i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h i)
    choose k hk using hd
    refine ⟨⟨ofInt k, ⟨k, rfl⟩⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul, hp, crd_spec a, natCast_mul_ofInt]
    congr 1; funext i; exact hk i

/-- The lift of a vector mod `p` with coordinates in `[0, p)`. -/
def liftP {p : ℕ} (c : Fin 4 → ZMod p) : O := ⟨ofInt (fun i => ((c i).val : ℤ)), ⟨_, rfl⟩⟩

theorem red_liftP {p : ℕ} [NeZero p] (c : Fin 4 → ZMod p) : red p (crd (liftP c)) = c := by
  rw [crd_eq (n := fun i => ((c i).val : ℤ)) rfl]
  funext i; simp [red]

theorem vec_eta {p : ℕ} (x : Fin 4 → ZMod p) : x = ![x 0, x 1, x 2, x 3] := by
  funext i; fin_cases i <;> rfl

/-! ### The finite checks -/

set_option maxRecDepth 100000 in
theorem d2_2i : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 2,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![0, 1, 0, 0] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d2_3j : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 3,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![2, 0, 2, 0] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d2_3ij : ∀ x0 x1 x2 x3 a0 a1 a2 a3 : ZMod 3,
    mulZ ![x0, x1, x2, x3] ![x0, x1, x2, x3] = 0 →
    mulZ (mulZ ![0, 2, 0, 2] ![a0, a1, a2, a3]) ![x0, x1, x2, x3] = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d1_2i : ∀ x0 x1 x2 x3 : ZMod 2, ![x0, x1, x2, x3] ≠ 0 →
    ∃ b0 b1 b2 b3 : ZMod 2, mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![1, 0, 0, 0] ∨
      mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![0, 1, 0, 0] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d1_3j : ∀ x0 x1 x2 x3 : ZMod 3, ![x0, x1, x2, x3] ≠ 0 →
    ∃ b0 b1 b2 b3 : ZMod 3, mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![1, 0, 0, 0] ∨
      mulZ ![b0, b1, b2, b3] ![x0, x1, x2, x3] = ![2, 0, 2, 0] := by
  decide +kernel

/-! ### Consequences in `𝒪` -/

/-- `i·j ∈ 𝒪`. -/
theorem crd_oi : crd oi = ![0, 1, 0, 0] := crd_eq rfl
theorem crd_oj : crd oj = ![-1, 0, 2, 0] := crd_eq rfl
theorem crd_oij : crd (oi * oj) = ![0, -1, 0, 2] := by
  rw [crd_mul, crd_oi, crd_oj]; funext i; fin_cases i <;> simp [mulCoord]

/-- **D2** in `𝒪`: if `x² ∈ p𝒪` then `w a x ∈ p𝒪` for all `a` (for the listed `(p, w)`). -/
theorem d2_of {p : ℕ} (w : O)
    (hc : ∀ x a : Fin 4 → ZMod p, mulZ x x = 0 → mulZ (mulZ (red p (crd w)) a) x = 0)
    (x : O) (hx : ∃ c : O, x * x = (p : O) * c) (a : O) : ∃ c : O, w * a * x = (p : O) * c := by
  rw [mem_iff] at hx ⊢
  rw [crd_mul, red_mul, crd_mul, red_mul]
  rw [crd_mul, red_mul] at hx
  exact hc _ _ hx

theorem hc2i : ∀ x a : Fin 4 → ZMod 2, mulZ x x = 0 → mulZ (mulZ (red 2 (crd oi)) a) x = 0 := by
  intro x a h
  rw [vec_eta x] at h ⊢; rw [vec_eta a]
  have : red 2 (crd oi) = ![0, 1, 0, 0] := by rw [crd_oi]; funext i; fin_cases i <;> rfl
  rw [this]; exact d2_2i _ _ _ _ _ _ _ _ h



theorem red_sub (p : ℕ) (n m : Fin 4 → ℤ) : red p (n - m) = red p n - red p m := by
  funext i; simp [red]

/-- **D1** in `𝒪`: an element not in `p𝒪` has a left multiple `≡ 1` or `≡ w₀` mod `p`. -/
theorem d1_of {p : ℕ} [NeZero p] (w₀ : O)
    (hc : ∀ x : Fin 4 → ZMod p, x ≠ 0 →
      ∃ y : Fin 4 → ZMod p, mulZ y x = red p (crd 1) ∨ mulZ y x = red p (crd w₀))
    (a : O) (ha : ¬ ∃ c : O, a = (p : O) * c) :
    ∃ b : O, (∃ c : O, b * a - 1 = (p : O) * c) ∨ (∃ c : O, b * a - w₀ = (p : O) * c) := by
  rw [mem_iff] at ha
  obtain ⟨y, hy⟩ := hc _ ha
  refine ⟨liftP y, ?_⟩
  simp only [mem_iff, crd_sub, crd_mul, red_sub, red_mul, red_liftP]
  rcases hy with hy | hy
  · left; rw [hy, sub_self]
  · right; rw [hy, sub_self]

theorem hd1_2 : ∀ x : Fin 4 → ZMod 2, x ≠ 0 →
    ∃ y : Fin 4 → ZMod 2, mulZ y x = red 2 (crd 1) ∨ mulZ y x = red 2 (crd oi) := by
  intro x hx
  rw [vec_eta x] at hx
  obtain ⟨b0, b1, b2, b3, h⟩ := d1_2i _ _ _ _ hx
  refine ⟨![b0, b1, b2, b3], ?_⟩
  rw [crd_one, crd_oi, vec_eta x]
  have e1 : red 2 ![1, 0, 0, 0] = ![1, 0, 0, 0] := by funext i; fin_cases i <;> rfl
  have e2 : red 2 ![0, 1, 0, 0] = ![0, 1, 0, 0] := by funext i; fin_cases i <;> rfl
  rw [e1, e2]; exact h

theorem hd1_3 : ∀ x : Fin 4 → ZMod 3, x ≠ 0 →
    ∃ y : Fin 4 → ZMod 3, mulZ y x = red 3 (crd 1) ∨ mulZ y x = red 3 (crd oj) := by
  intro x hx
  rw [vec_eta x] at hx
  obtain ⟨b0, b1, b2, b3, h⟩ := d1_3j _ _ _ _ hx
  refine ⟨![b0, b1, b2, b3], ?_⟩
  rw [crd_one, crd_oj, vec_eta x]
  have e1 : red 3 ![1, 0, 0, 0] = ![1, 0, 0, 0] := by funext i; fin_cases i <;> rfl
  have e2 : red 3 ![-1, 0, 2, 0] = ![2, 0, 2, 0] := by funext i; fin_cases i <;> rfl
  rw [e1, e2]; exact h

theorem hc3j : ∀ x a : Fin 4 → ZMod 3, mulZ x x = 0 → mulZ (mulZ (red 3 (crd oj)) a) x = 0 := by
  intro x a h
  rw [vec_eta x] at h ⊢; rw [vec_eta a]
  have : red 3 (crd oj) = ![2, 0, 2, 0] := by rw [crd_oj]; funext i; fin_cases i <;> rfl
  rw [this]; exact d2_3j _ _ _ _ _ _ _ _ h

theorem hc3ij : ∀ x a : Fin 4 → ZMod 3, mulZ x x = 0 →
    mulZ (mulZ (red 3 (crd (oi * oj))) a) x = 0 := by
  intro x a h
  rw [vec_eta x] at h ⊢; rw [vec_eta a]
  have : red 3 (crd (oi * oj)) = ![0, 2, 0, 2] := by rw [crd_oij]; funext i; fin_cases i <;> rfl
  rw [this]; exact d2_3ij _ _ _ _ _ _ _ _ h

theorem hc2ij : ∀ x a : Fin 4 → ZMod 2, mulZ x x = 0 →
    mulZ (mulZ (red 2 (crd (oi * oj))) a) x = 0 := by
  intro x a h
  rw [vec_eta x] at h ⊢; rw [vec_eta a]
  have : red 2 (crd (oi * oj)) = ![0, 1, 0, 0] := by rw [crd_oij]; funext i; fin_cases i <;> rfl
  rw [this]; exact d2_2i _ _ _ _ _ _ _ _ h

/-! ## Part B: `A[p]` for a QM surface over `ℂ` -/

section Points

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {A : PkgI3.AbVar ℂ}

/-- An endomorphism acting on `ℂ`-points. -/
abbrev act (f : PkgI3.AbVar.End A) (x : A.Pt ℂ) : A.Pt ℂ := x ≫ f.hom

theorem act_mul (f g : PkgI3.AbVar.End A) (x : A.Pt ℂ) : act (f * g) x = act f (act g x) := by
  change x ≫ (g.hom ≫ f.hom) = (x ≫ g.hom) ≫ f.hom
  rw [Category.assoc]

theorem act_one (x : A.Pt ℂ) : act 1 x = x := Category.comp_id x

theorem act_add (f g : PkgI3.AbVar.End A) (x : A.Pt ℂ) : act (f + g) x = act f x * act g x := by
  change x ≫ (f.hom * g.hom) = _
  exact MonObj.comp_mul _ _ _

theorem act_zero (x : A.Pt ℂ) : act 0 x = 1 := by
  change x ≫ (1 : A.X ⟶ A.X) = 1
  exact MonObj.comp_one _

theorem act_pt_mul (f : PkgI3.AbVar.End A) (x y : A.Pt ℂ) : act f (x * y) = act f x * act f y :=
  MonObj.mul_comp _ _ _

theorem act_pt_one (f : PkgI3.AbVar.End A) : act f (1 : A.Pt ℂ) = 1 := MonObj.one_comp _

theorem act_pow (f : PkgI3.AbVar.End A) (x : A.Pt ℂ) (n : ℕ) : act f (x ^ n) = (act f x) ^ n :=
  MonObj.pow_comp _ _ _

theorem act_neg (f : PkgI3.AbVar.End A) (x : A.Pt ℂ) : act (-f) x = (act f x)⁻¹ := by
  have h := act_add (-f) f x
  rw [neg_add_cancel, act_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem act_sub (f g : PkgI3.AbVar.End A) (x : A.Pt ℂ) : act (f - g) x = act f x * (act g x)⁻¹ := by
  rw [sub_eq_add_neg, act_add, act_neg]

theorem act_natCast (n : ℕ) (x : A.Pt ℂ) : act (n : PkgI3.AbVar.End A) x = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, act_add, ih, act_one, pow_succ]

theorem act_neg_one (x : A.Pt ℂ) : act (-1 : PkgI3.AbVar.End A) x = x⁻¹ := by
  rw [act_neg, act_one]

theorem card_tors (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2) (n : ℕ) (hn : 0 < n) :
    Nat.card {x : A.Pt ℂ // x ^ n = 1} = n ^ 4 := by
  have := HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.card_torsion_algClosed hT A 2
    (by rw [hA]; rfl) n hn
  rwa [show 2 * 2 = 4 from rfl] at this

/-- **No `w₀` with `ι(w₀)² = p·ε` kills `A[p]`** (else `A[p²] ⊆ A[p]`, against the count `p⁸ > p⁴`). -/
theorem exists_not_killed (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2) (q : QMStr A)
    (p : ℕ) (hp : 1 < p) (w₀ : O) (ε : PkgI3.AbVar.End A)
    (hw : q.iota w₀ * q.iota w₀ = (p : PkgI3.AbVar.End A) * ε)
    (hε : ∀ y : A.Pt ℂ, act ε y = 1 → y = 1) :
    ∃ v : A.Pt ℂ, v ^ p = 1 ∧ act (q.iota w₀) v ≠ 1 := by
  by_contra H
  push Not at H
  have hp0 : 0 < p := by omega
  have key : ∀ x : A.Pt ℂ, x ^ (p * p) = 1 → x ^ p = 1 := by
    intro x hx
    have h1 : act (q.iota w₀) (x ^ p) = 1 := H _ (by rw [← pow_mul]; exact hx)
    have h2 : act (q.iota w₀) (act (q.iota w₀) x) = 1 := H _ (by rw [← act_pow]; exact h1)
    rw [← act_mul, hw, act_mul, act_natCast, ← act_pow] at h2
    exact hε _ h2
  let F : {x : A.Pt ℂ // x ^ (p * p) = 1} → {x : A.Pt ℂ // x ^ p = 1} := fun x => ⟨x.1, key _ x.2⟩
  have hF : Function.Injective F := fun x y h => Subtype.ext (by have := congrArg Subtype.val h; exact this)
  have c1 := card_tors hT hA (p * p) (Nat.mul_pos hp0 hp0)
  have c2 := card_tors hT hA p hp0
  haveI : Finite {x : A.Pt ℂ // x ^ p = 1} := Nat.finite_of_card_ne_zero (by rw [c2]; positivity)
  have := Nat.card_le_card_of_injective F hF
  rw [c1, c2] at this
  have h4 : p ^ 4 < (p * p) ^ 4 := Nat.pow_lt_pow_left (by nlinarith) (by norm_num)
  omega

/-- **The annihilator of `v` is `p𝒪`** (given `D1` for `(p, w₀)`). -/
theorem ann_iff (q : QMStr A) (p : ℕ) (w₀ : O) (v : A.Pt ℂ) (hv : v ^ p = 1)
    (hw : act (q.iota w₀) v ≠ 1)
    (hD1 : ∀ a : O, (¬ ∃ c : O, a = (p : O) * c) →
      ∃ b : O, (∃ c : O, b * a - 1 = (p : O) * c) ∨ (∃ c : O, b * a - w₀ = (p : O) * c))
    (a : O) : act (q.iota a) v = 1 ↔ ∃ c : O, a = (p : O) * c := by
  have hpc : ∀ c : O, act (q.iota ((p : O) * c)) v = 1 := by
    intro c
    rw [map_mul, map_natCast, act_mul, act_natCast, ← act_pow, hv, act_pt_one]
  constructor
  · intro ha
    by_contra hne
    obtain ⟨b, hb⟩ := hD1 a hne
    have hba : act (q.iota (b * a)) v = 1 := by rw [map_mul, act_mul, ha, act_pt_one]
    rcases hb with ⟨c, hc⟩ | ⟨c, hc⟩
    · have e : (1 : O) = b * a - (p : O) * c := by rw [← hc]; abel
      apply hw
      have : v = 1 := by
        have h1 := act_one (A := A) v
        rw [← map_one q.iota, e, map_sub, act_sub, hba, hpc, inv_one, _root_.mul_one] at h1
        exact h1.symm
      rw [this, act_pt_one]
    · have e : w₀ = b * a - (p : O) * c := by rw [← hc]; abel
      apply hw
      rw [e, map_sub, act_sub, hba, hpc, inv_one, _root_.mul_one]
  · rintro ⟨c, rfl⟩; exact hpc c

/-- **`a ↦ ι(a)v` is onto `A[p]`** (injective on `𝒪/p𝒪`, and `#A[p] = p⁴ = #(𝒪/p𝒪)`). -/
theorem surj_of_ann (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2) (q : QMStr A) (p : ℕ)
    [NeZero p] (v : A.Pt ℂ) (hv : v ^ p = 1)
    (hann : ∀ a : O, act (q.iota a) v = 1 ↔ ∃ c : O, a = (p : O) * c) :
    ∀ x : A.Pt ℂ, x ^ p = 1 → ∃ a : O, act (q.iota a) v = x := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  let F : (Fin 4 → ZMod p) → {x : A.Pt ℂ // x ^ p = 1} := fun c =>
    ⟨act (q.iota (liftP c)) v, by rw [← act_pow, hv, act_pt_one]⟩
  have hF : Function.Injective F := by
    intro c c' h
    have h1 : act (q.iota (liftP c)) v = act (q.iota (liftP c')) v := congrArg Subtype.val h
    have h2 : act (q.iota (liftP c - liftP c')) v = 1 := by
      rw [map_sub, act_sub, h1, mul_inv_cancel]
    rw [hann, mem_iff, crd_sub, red_sub, red_liftP, red_liftP, sub_eq_zero] at h2
    exact h2
  have c2 := card_tors hT hA p hp0
  haveI : Finite {x : A.Pt ℂ // x ^ p = 1} := Nat.finite_of_card_ne_zero (by rw [c2]; positivity)
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (by
    rw [c2, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin])
  intro x hx
  obtain ⟨c, hc⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨liftP c, congrArg Subtype.val hc⟩

/-- **`ι(w)c` kills `A[p]`** when `c ∈ End_𝒪(A)`, `c² ∈ p·End(A)` and `D2` holds for `(p, w)`. -/
theorem kills_of (q : QMStr A) (p : ℕ) (v : A.Pt ℂ) (hv : v ^ p = 1)
    (hann : ∀ a : O, act (q.iota a) v = 1 ↔ ∃ c : O, a = (p : O) * c)
    (hsurj : ∀ x : A.Pt ℂ, x ^ p = 1 → ∃ a : O, act (q.iota a) v = x)
    (w : O) (hD2 : ∀ x : O, (∃ c : O, x * x = (p : O) * c) → ∀ a : O, ∃ c : O, w * a * x = (p : O) * c)
    (c : PkgI3.AbVar.End A) (hc : c ∈ com q) (d : PkgI3.AbVar.End A)
    (hcd : c * c = (p : PkgI3.AbVar.End A) * d) :
    ∀ x : A.Pt ℂ, x ^ p = 1 → act (q.iota w * c) x = 1 := by
  have hcomm : ∀ a : O, c * q.iota a = q.iota a * c := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hc
    exact (hc _ ⟨a, rfl⟩).symm
  obtain ⟨u, hu⟩ := hsurj (act c v) (by rw [← act_pow, hv, act_pt_one])
  have hca : ∀ a : O, act c (act (q.iota a) v) = act (q.iota (a * u)) v := by
    intro a
    rw [← act_mul, hcomm, act_mul, ← hu, map_mul, act_mul]
  have huu : ∃ e : O, u * u = (p : O) * e := by
    rw [← hann, ← hca, hu, ← act_mul, hcd, act_mul, act_natCast, ← act_pow, hv, act_pt_one]
  intro x hx
  obtain ⟨a, rfl⟩ := hsurj x hx
  rw [act_mul, hca, ← act_mul, ← map_mul, hann, ← _root_.mul_assoc]
  exact hD2 u huu a

end Points


/-! ## Part C: division by `n` in `End(A)` (uniformization and `HomLatticeCorr`) -/

section Div

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {A : PkgI3.AbVar ℂ}

theorem unif_pow {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → ZInQ.LeafPush2.CPts A (RingHom.id ℂ)}
    (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ) (n : ℕ)
    (z : Fin g → ℂ) : Φ ((n : ℂ) • z) = Φ z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact (hker 0).2 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]

/-- **An endomorphism killing `A[n]` is `n` times an endomorphism.** -/
theorem dvd_of_kills (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HDec.HomUnify.HomLatticeCorr)
    (n : ℕ) (hn : 0 < n) (f : PkgI3.AbVar.End A) (hf : ∀ x : A.Pt ℂ, x ^ n = 1 → act f x = 1) :
    ∃ g : PkgI3.AbVar.End A, (n : PkgI3.AbVar.End A) * g = f := by
  obtain ⟨d, hd⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hdisc, hΛ, hΦ⟩ := hU ℂ A (RingHom.id ℂ) d hd
  obtain ⟨M, hM⟩ := hC.1 ℂ A A (RingHom.id ℂ) d d Λ Λ Φ Φ hd hd hΦ hΦ f
  have hΦ' := hΦ
  obtain ⟨hadd, hker, hsurj, -, -⟩ := hΦ'
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hM' : ∀ z ∈ Λ, ((n : ℂ)⁻¹ • M) z ∈ Λ := by
    intro z hz
    rw [LinearMap.smul_apply, ← map_smul, ← hker, hM]
    apply hf
    change Φ _ ^ n = 1
    rw [← unif_pow hadd hker, smul_smul, mul_inv_cancel₀ hn', one_smul]
    exact (hker z).2 hz
  obtain ⟨g, hg, -⟩ := hC.2 A A d d Λ Λ Φ Φ hd hd hΦ hΦ _ hM'
  refine ⟨g, PkgI3.AbVar.Hom.ext' (HDec.AVB2.hom_ext_of_pts _ _ fun x => ?_)⟩
  obtain ⟨z, hz⟩ := hsurj x
  change act ((n : PkgI3.AbVar.End A) * g) x = act f x
  rw [act_mul, act_natCast, ← hz]
  change (Φ z ≫ g.hom) ^ n = Φ z ≫ f.hom
  rw [← hg z, ← hM z, ← unif_pow hadd hker, LinearMap.smul_apply, smul_smul,
    mul_inv_cancel₀ hn', one_smul]

/-- **`End(A)` is torsion-free.** -/
theorem eq_zero_of_natCast_mul (hU : ZInQ.LeafPush2.UniformizationExists) (n : ℕ) (hn : 0 < n)
    (g : PkgI3.AbVar.End A) (h : (n : PkgI3.AbVar.End A) * g = 0) : g = 0 := by
  obtain ⟨d, hd⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hdisc, hΛ, hadd, hker, hsurj, -, -⟩ := hU ℂ A (RingHom.id ℂ) d hd
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  refine PkgI3.AbVar.Hom.ext' (HDec.AVB2.hom_ext_of_pts _ _ fun x => ?_)
  obtain ⟨z, hz⟩ := hsurj x
  change act g x = act 0 x
  obtain ⟨w, hw⟩ : ∃ w : A.Pt ℂ, w = Φ ((n : ℂ)⁻¹ • z) := ⟨_, rfl⟩
  have e : x = w ^ n := by
    have := unif_pow hadd hker n ((n : ℂ)⁻¹ • z)
    rw [smul_smul, mul_inv_cancel₀ hn', one_smul, hz] at this
    rw [hw]; exact this
  rw [act_zero, e, act_pow, ← act_natCast, ← act_mul, h, act_zero]

theorem cancel_natCast (hU : ZInQ.LeafPush2.UniformizationExists) (n : ℕ) (hn : 0 < n)
    {g g' : PkgI3.AbVar.End A} (h : (n : PkgI3.AbVar.End A) * g = (n : PkgI3.AbVar.End A) * g') :
    g = g' :=
  sub_eq_zero.1 (eq_zero_of_natCast_mul hU n hn _ (by rw [mul_sub, h, sub_self]))

end Div


/-! ## Part D: the normalizing automorphism and the fixed class -/

section Twist

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {A : PkgI3.AbVar ℂ}

/-- `w a = α(a) w` for `α = rep k` (conjugation by `w = tt k`). -/
theorem w_mul_eq (k : Fin 4) (w : O) (hw : (w : B) = (HDec.LeafQM.AV.Pin.Exact.tt k : B)) (a : O) :
    w * a = HDec.LeafQM.AV.Pin.Exact.rep k a * w := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  change (w : B) * a = ((HDec.LeafQM.AV.Pin.Exact.conjO _ _ a : O) : B) * w
  rw [HDec.LeafQM.AV.Pin.Exact.conjO_apply, hw, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

/-- **The Atkin–Lehner-type automorphism.** If `f = ι(w)c` (`c ∈ End_𝒪(A)`, `w = tt k`) kills `A[n]` and
`f² = n²r` with `r` a unit, then `ψ = f/n` is an automorphism of `A` with `ψ ι(a) = ι(α a) ψ`, i.e. a QM
isomorphism `(A, ι) ≅ (A, ι ∘ α)`, `α = rep k`. -/
theorem qmIso_twist (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HDec.HomUnify.HomLatticeCorr)
    (q : QMStr A) (k : Fin 4) (w : O) (hw : (w : B) = (HDec.LeafQM.AV.Pin.Exact.tt k : B))
    (n : ℕ) (hn : 0 < n) (c : PkgI3.AbVar.End A) (hc : c ∈ com q)
    (hkill : ∀ x : A.Pt ℂ, x ^ n = 1 → act (q.iota w * c) x = 1)
    (r r' : PkgI3.AbVar.End A) (hrr : r * r' = 1) (hr'r : r' * r = 1)
    (hf2 : (q.iota w * c) * (q.iota w * c) = ((n * n : ℕ) : PkgI3.AbVar.End A) * r) :
    Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep k))) := by
  obtain ⟨ψ, hψ⟩ := dvd_of_kills hU hC n hn _ hkill
  have hcomm : ∀ a : O, c * q.iota a = q.iota a * c := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hc
    exact (hc _ ⟨a, rfl⟩).symm
  have hψ2 : ψ * ψ = r := by
    apply cancel_natCast hU (n * n) (Nat.mul_pos hn hn)
    rw [← hf2, ← hψ, Nat.cast_mul]
    have hc' : (n : PkgI3.AbVar.End A) * ψ = ψ * n := (Nat.cast_commute n ψ).eq
    calc ((n : PkgI3.AbVar.End A) * n) * (ψ * ψ) = (n : PkgI3.AbVar.End A) * ((n * ψ) * ψ) := by
          simp only [_root_.mul_assoc]
      _ = (n : PkgI3.AbVar.End A) * ((ψ * n) * ψ) := by rw [hc']
      _ = ((n : PkgI3.AbVar.End A) * ψ) * ((n : PkgI3.AbVar.End A) * ψ) := by
          simp only [_root_.mul_assoc]
  have hinvR : ψ * (ψ * r') = 1 := by rw [← _root_.mul_assoc, hψ2, hrr]
  have hinvL : (r' * ψ) * ψ = 1 := by rw [_root_.mul_assoc, hψ2, hr'r]
  have heq : r' * ψ = ψ * r' := left_inv_eq_right_inv hinvL hinvR
  have heqv : ∀ a : O, ψ * q.iota a = q.iota (HDec.LeafQM.AV.Pin.Exact.rep k a) * ψ := by
    intro a
    apply cancel_natCast hU n hn
    have e1 : (n : PkgI3.AbVar.End A) * (q.iota (HDec.LeafQM.AV.Pin.Exact.rep k a) * ψ) =
        q.iota (HDec.LeafQM.AV.Pin.Exact.rep k a) * ((n : PkgI3.AbVar.End A) * ψ) := by
      rw [← _root_.mul_assoc, (Nat.cast_commute n _).eq, _root_.mul_assoc]
    rw [e1, hψ, ← _root_.mul_assoc, hψ, _root_.mul_assoc, hcomm, ← _root_.mul_assoc, ← map_mul,
      w_mul_eq k w hw a, map_mul, _root_.mul_assoc]
  exact ⟨{ φ := ψ
           ψ := ψ * r'
           left := by
             change ((ψ * r') * ψ).hom = (1 : PkgI3.AbVar.End A).hom
             rw [← heq, hinvL]
           right := by
             change (ψ * (ψ * r')).hom = (1 : PkgI3.AbVar.End A).hom
             rw [hinvR]
           equivariant := fun a => by
             change (ψ * q.iota a).hom = (q.iota (HDec.LeafQM.AV.Pin.Exact.rep k a) * ψ).hom
             rw [heqv a] }⟩

/-- **The fixed class.** A QM isomorphism `(A, ι) ≅ (A, ι ∘ α)` makes the class of `Q` a fixed point of
`rightMul u ∘ twist α` for some `u ∈ 𝒪^×` (the level structures differ by a unit mod 3: `Level3.torsor`,
and `𝒪^× → (𝒪/3𝒪)^×` is onto). -/
theorem fixed_class (hT : ObjBridge.TorsionStructure) (Q : QML3 ℂ) (α : O ≃+* O)
    (θ : QMIso Q.q (Q.q.twist α)) :
    ∃ u : Oˣ, M3.mk Q = M3.rightMul u (M3.twist α (M3.mk Q)) := by
  let e' := HDec.G0ModField.transportLevel θ Q.e
  obtain ⟨u₀, v₀, hv, hu⟩ := Level3.torsor (K := ℂ) hT (Q.twist α) e'
  obtain ⟨u, d, hd⟩ := HDec.TSHeckeUnits.exists_unit_congr u₀ v₀ hv
  refine ⟨u, ?_⟩
  have he : e' = (Q.e.twist α).rightMul u := by
    apply Level3.ext'
    refine AddMonoidHom.ext fun a => ?_
    refine (hu a).trans ?_
    change (Q.twist α).e.eta (a * u₀) = (Q.twist α).e.eta (a * u)
    rw [Level3.eq_iff]
    exact ⟨a * d, by rw [← mul_sub, hd]; noncomm_ring⟩
  have hiso := HDec.G0ModField.transportIso Q Q.surface θ
  rw [M3.twist_mk]
  change M3.mk Q = M3.mk ((Q.twist α).rightMul u)
  apply Quotient.sound
  have : ((Q.twist α).rightMul u) = ⟨Q.A, Q.surface, Q.q.twist α, e'⟩ := by rw [he]; rfl
  rw [this]
  exact ⟨hiso⟩

end Twist


/-! ## Part F: the three CM types -/

section CM

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {A : PkgI3.AbVar ℂ}

theorem oij_sq : (oi * oj) * (oi * oj) = 6 := by
  calc (oi * oj) * (oi * oj) = oi * (oj * oi) * oj := by noncomm_ring
    _ = oi * (-(oi * oj)) * oj := by rw [eq_neg_of_add_eq_zero_left oj_mul_oi_add]
    _ = -((oi * oi) * (oj * oj)) := by noncomm_ring
    _ = 6 := by rw [oi_mul_oi, oj_mul_oj]; norm_num

theorem act_inv_eq (y : A.Pt ℂ) : act (-1 : PkgI3.AbVar.End A) y = 1 → y = 1 := by
  rw [act_neg_one]; exact inv_eq_one.mp

/-- A generator of `A[2]` as an `𝒪`-module. -/
theorem gen2 (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2) (q : QMStr A) :
    ∃ v : A.Pt ℂ, v ^ 2 = 1 ∧ (∀ a : O, act (q.iota a) v = 1 ↔ ∃ c : O, a = ((2 : ℕ) : O) * c) ∧
      (∀ x : A.Pt ℂ, x ^ 2 = 1 → ∃ a : O, act (q.iota a) v = x) := by
  obtain ⟨v, hv, hw⟩ := exists_not_killed hT hA q 2 (by norm_num) oi 1
    (by rw [← map_mul, oi_mul_oi, _root_.mul_one, map_ofNat, Nat.cast_ofNat])
    (fun y hy => by rwa [act_one] at hy)
  have hann := ann_iff q 2 oi v hv hw (d1_of oi hd1_2)
  exact ⟨v, hv, hann, surj_of_ann hT hA q 2 v hv hann⟩

/-- A generator of `A[3]` as an `𝒪`-module. -/
theorem gen3 (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2) (q : QMStr A) :
    ∃ v : A.Pt ℂ, v ^ 3 = 1 ∧ (∀ a : O, act (q.iota a) v = 1 ↔ ∃ c : O, a = ((3 : ℕ) : O) * c) ∧
      (∀ x : A.Pt ℂ, x ^ 3 = 1 → ∃ a : O, act (q.iota a) v = x) := by
  obtain ⟨v, hv, hw⟩ := exists_not_killed hT hA q 3 (by norm_num) oj (-1)
    (by rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Nat.cast_ofNat, mul_neg, _root_.mul_one])
    act_inv_eq
  have hann := ann_iff q 3 oj v hv hw (d1_of oj hd1_3)
  exact ⟨v, hv, hann, surj_of_ann hT hA q 3 v hv hann⟩

theorem mem_com_iff (q : QMStr A) (c : PkgI3.AbVar.End A) :
    c ∈ com q ↔ ∀ a : O, c * q.iota a = q.iota a * c := by
  rw [com, Subring.mem_centralizer_iff]
  constructor
  · intro h a; exact (h _ ⟨a, rfl⟩).symm
  · rintro h _ ⟨a, rfl⟩; exact (h a).symm

theorem kills6 (f : PkgI3.AbVar.End A) (h2 : ∀ x : A.Pt ℂ, x ^ 2 = 1 → act f x = 1)
    (h3 : ∀ x : A.Pt ℂ, x ^ 3 = 1 → act f x = 1) : ∀ x : A.Pt ℂ, x ^ 6 = 1 → act f x = 1 := by
  intro x hx
  have e2 : act f (x ^ 3) = 1 := h2 _ (by rw [← pow_mul]; exact hx)
  have e3 : act f (x ^ 2) = 1 := h3 _ (by rw [← pow_mul]; exact hx)
  rw [pow_succ, act_pt_mul, e3, _root_.one_mul] at e2
  exact e2

/-- **The QM isomorphism `(A, ι) ≅ (A, ι ∘ rep k)` of a CM point**, with `k = 1, 2, 3` for CM by `ℤ[i]`,
`ℤ[ζ₃]`, `ℤ[√−6]`. -/
theorem twist_of_cm (hT : PkgI2.TorsionStructure.{0}) (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HDec.HomUnify.HomLatticeCorr) (hA : A.dim = 2) (q : QMStr A)
    (hcm : HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) :
    (HasCM4 q ∧ Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep 1)))) ∨
    (HasCM3 q ∧ Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep 2)))) ∨
    (HasCM24 q ∧ Nonempty (QMIso q (q.twist (HDec.LeafQM.AV.Pin.Exact.rep 3)))) := by
  obtain ⟨v2, hv2, hann2, hsurj2⟩ := gen2 hT hA q
  obtain ⟨v3, hv3, hann3, hsurj3⟩ := gen3 hT hA q
  rcases hcm with h4 | h3 | h24
  · left
    refine ⟨h4, ?_⟩
    obtain ⟨φ, hφ, hφ2⟩ := h4
    have hc : (1 + φ) ∈ com q := Subring.add_mem _ (Subring.one_mem _) hφ
    have hcc : (1 + φ) * (1 + φ) = ((2 : ℕ) : PkgI3.AbVar.End A) * φ := by
      have e : (1 + φ) * (1 + φ) = 1 + 2 * φ + φ * φ := by noncomm_ring
      rw [e, hφ2, Nat.cast_ofNat]; noncomm_ring
    have hkill := kills_of q 2 v2 hv2 hann2 hsurj2 oi (d2_of oi hc2i) _ hc φ hcc
    refine qmIso_twist hU hC q 1 oi rfl 2 (by norm_num) _ hc hkill φ (-φ)
      (by rw [mul_neg, hφ2, neg_neg]) (by rw [neg_mul, hφ2, neg_neg]) ?_
    rw [mem_com_iff] at hc
    calc (q.iota oi * (1 + φ)) * (q.iota oi * (1 + φ))
        = q.iota oi * ((1 + φ) * q.iota oi) * (1 + φ) := by noncomm_ring
      _ = (q.iota oi * q.iota oi) * ((1 + φ) * (1 + φ)) := by rw [hc]; noncomm_ring
      _ = ((2 * 2 : ℕ) : PkgI3.AbVar.End A) * φ := by
          rw [hcc, ← map_mul, oi_mul_oi, map_ofNat, Nat.cast_mul, Nat.cast_ofNat]; noncomm_ring
  · right; left
    refine ⟨h3, ?_⟩
    obtain ⟨φ, hφ, hφ2⟩ := h3
    have hφ2' : φ * φ = φ - 1 := by
      rw [← sub_eq_zero, ← hφ2]; abel
    have hc : (φ + φ - 1) ∈ com q :=
      Subring.sub_mem _ (Subring.add_mem _ hφ hφ) (Subring.one_mem _)
    have h3 : ((3 : ℕ) : PkgI3.AbVar.End A) = 1 + 1 + 1 := by norm_num
    have hcc : (φ + φ - 1) * (φ + φ - 1) = ((3 : ℕ) : PkgI3.AbVar.End A) * (-1) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, _root_.one_mul, _root_.mul_one, hφ2', h3,
        mul_neg]
      abel
    have hkill := kills_of q 3 v3 hv3 hann3 hsurj3 oj (d2_of oj hc3j) _ hc (-1) hcc
    refine qmIso_twist hU hC q 2 oj rfl 3 (by norm_num) _ hc hkill 1 1 (_root_.mul_one _)
      (_root_.mul_one _) ?_
    rw [mem_com_iff] at hc
    calc (q.iota oj * (φ + φ - 1)) * (q.iota oj * (φ + φ - 1))
        = q.iota oj * ((φ + φ - 1) * q.iota oj) * (φ + φ - 1) := by noncomm_ring
      _ = (q.iota oj * q.iota oj) * ((φ + φ - 1) * (φ + φ - 1)) := by rw [hc]; noncomm_ring
      _ = ((3 * 3 : ℕ) : PkgI3.AbVar.End A) * 1 := by
          rw [hcc, ← map_mul, oj_mul_oj, map_neg, map_ofNat, Nat.cast_mul, Nat.cast_ofNat]
          simp only [mul_neg, neg_mul, neg_neg, _root_.mul_one]
  · right; right
    refine ⟨h24, ?_⟩
    obtain ⟨φ, hφ, hφ2⟩ := h24
    have hcc2 : φ * φ = ((2 : ℕ) : PkgI3.AbVar.End A) * (-3) := by
      rw [hφ2, Nat.cast_ofNat]; norm_num
    have hcc3 : φ * φ = ((3 : ℕ) : PkgI3.AbVar.End A) * (-2) := by
      rw [hφ2, Nat.cast_ofNat]; norm_num
    have hk2 := kills_of q 2 v2 hv2 hann2 hsurj2 (oi * oj) (d2_of _ hc2ij) _ hφ _ hcc2
    have hk3 := kills_of q 3 v3 hv3 hann3 hsurj3 (oi * oj) (d2_of _ hc3ij) _ hφ _ hcc3
    refine qmIso_twist hU hC q 3 (oi * oj) rfl 6 (by norm_num) _ hφ (kills6 _ hk2 hk3) (-1) (-1)
      (by noncomm_ring) (by noncomm_ring) ?_
    have hc := (mem_com_iff q φ).1 hφ
    calc (q.iota (oi * oj) * φ) * (q.iota (oi * oj) * φ)
        = q.iota (oi * oj) * (φ * q.iota (oi * oj)) * φ := by noncomm_ring
      _ = (q.iota (oi * oj) * q.iota (oi * oj)) * (φ * φ) := by rw [hc]; noncomm_ring
      _ = ((6 * 6 : ℕ) : PkgI3.AbVar.End A) * (-1) := by
          rw [hφ2, ← map_mul, oij_sq, map_ofNat, Nat.cast_mul, Nat.cast_ofNat]; norm_num

end CM


/-- A non-closed point of an irreducible proper smooth curve over a field is dense. -/
theorem closure_eq_univ_of_not_closed {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [IrreducibleSpace X] (p : X) (hp : ¬ IsClosed ({p} : Set X)) :
    closure ({p} : Set X) = Set.univ := by
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨z, hzZ, hzc⟩ := nonempty_inter_closedPoints (Z := closure {p})
    ⟨p, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hz : IsClosed ({z} : Set X) := mem_closedPoints_iff.mp hzc
  have hpz : p ⤳ z := specializes_iff_mem_closure.mpr hzZ
  obtain ⟨h1, h2⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 z hz
  haveI : IsDomain (X.presheaf.stalk z) :=
    HDec.CIcopy.CurveGlueCI.isDomain_of_dim_one (by exact_mod_cast h1) h2
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := by
    rw [Ring.krullDimLE_iff]; exact h1.le
  obtain ⟨P, hP⟩ : p ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hpz
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := P.2.isMaximal_of_ne_bot hne
    have : P = IsLocalRing.closedPoint _ :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    apply hp
    rw [← hP, this, Scheme.fromSpecStalk_closedPoint]; exact hz
  have hηz : genericPoint X ⤳ z := (genericPoint_spec X).specializes (Set.mem_univ z)
  obtain ⟨Q, hQ⟩ : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hηz
  have hPQ : P ⤳ Q := (PrimeSpectrum.le_iff_specializes P Q).mp
    (by change P.asIdeal ≤ Q.asIdeal; rw [hPbot]; exact bot_le)
  have hpη : p ⤳ genericPoint X := by
    rw [← hP, ← hQ]; exact hPQ.map (X.fromSpecStalk z).continuous
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (genericPoint_spec X).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hpη))
    isClosed_closure

/-- **A fixed `ℂ`-point of a nontrivial endomorphism of an irreducible proper smooth curve over `ℚ`
comes from a `ℚ̄`-point.** -/
theorem exists_qbar_factor (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    [SmoothOfRelativeDimension 1 Y.hom] [IrreducibleSpace Y.left]
    (y : fieldPt ℂ ⟶ Y) (h : Y ⟶ Y) (hy : y ≫ h = y) (s : fieldPt Qbar ⟶ Y) (hs : s ≫ h ≠ s) :
    ∃ (ιe : Qbar →+* ℂ) (y₀ : fieldPt Qbar ⟶ Y), fieldMap ιe.toRatAlgHom ≫ y₀ = y := by
  obtain ⟨⟨p, e⟩, hpe⟩ : ∃ q, Scheme.SpecToEquivOfField ℂ Y.left y.left = q := ⟨_, rfl⟩
  have hyl : y.left = Spec.map e ≫ Y.left.fromSpecResidueField p := by
    rw [← (Scheme.SpecToEquivOfField ℂ Y.left).symm_apply_apply y.left, hpe]; rfl
  by_cases hc : IsClosed ({p} : Set Y.left)
  · have : IsClosedImmersion (Y.left.fromSpecResidueField p) :=
      isClosed_singleton_iff_isClosedImmersion.mp hc
    haveI : LocallyOfFiniteType Y.hom := inferInstance
    have : IsFinite (Y.left.fromSpecResidueField p ≫ Y.hom) :=
      (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
        (f := Y.left.fromSpecResidueField p ≫ Y.hom)).mpr inferInstance
    let φ := Spec.preimage (Y.left.fromSpecResidueField p ≫ Y.hom)
    letI : Algebra ℚ (Y.left.residueField p) := φ.hom.toAlgebra
    have hφ : φ.hom.IsIntegral := by
      rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
      infer_instance
    haveI : Algebra.IsIntegral ℚ (Y.left.residueField p) := ⟨fun x => hφ x⟩
    haveI : Algebra.IsAlgebraic ℚ (Y.left.residueField p) := Algebra.IsIntegral.isAlgebraic
    let j : Y.left.residueField p →ₐ[ℚ] Qbar := IsAlgClosed.lift
    letI : Algebra (Y.left.residueField p) Qbar := j.toRingHom.toAlgebra
    letI : Algebra (Y.left.residueField p) ℂ := e.hom.toAlgebra
    haveI : IsScalarTower ℚ (Y.left.residueField p) Qbar :=
      IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
    haveI : Algebra.IsAlgebraic (Y.left.residueField p) Qbar :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) _
    let ι : Qbar →ₐ[Y.left.residueField p] ℂ := IsAlgClosed.lift
    have hιj : ∀ x, ι (j x) = e.hom x := fun x => ι.commutes x
    let y₀ : fieldPt Qbar ⟶ Y :=
      Over.homMk (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ Y.left.fromSpecResidueField p)
        (HDec.TSHeckeGal.specQbar_to_specQ_eq' _ _)
    refine ⟨ι.toRingHom, y₀, ?_⟩
    apply Over.OverMorphism.ext
    rw [hyl]
    change Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      Y.left.fromSpecResidueField p = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact hιj x
  · exfalso
    apply hs
    have hcl := closure_eq_univ_of_not_closed Y.hom p hc
    haveI : IsReduced Y.left := by
      haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
      exact HDec.ModelGlue.isReduced_of_smooth_domain Y.hom
    haveI : IsDominant y.left := by
      constructor
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← hcl]
      apply closure_mono
      rw [Set.singleton_subset_iff]
      refine ⟨IsLocalRing.closedPoint ℂ, ?_⟩
      rw [hyl]; exact Y.left.fromSpecResidueField_apply p _
    have hl : h.left = 𝟙 Y.left :=
      ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w h, Category.id_comp]) y.left
        (by rw [Category.comp_id, ← Over.comp_left, hy])
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hl, Category.comp_id]


/-! ## Part G: assembly -/

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

/-- **A CM point of `Y₃(ℂ)` comes from `Y₃(ℚ̄)`**: a level-3 QM surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]`
or `ℤ[√−6]` is isomorphic to the base change of a level-3 QM surface over `ℚ̄`. -/
theorem cm_point (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : PkgI2.TorsionStructure.{0})
    (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HDec.HomUnify.HomLatticeCorr)
    (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (Q.Iso Q') := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := hRep
  haveI : IsProper Y.hom := h1.1
  haveI : SmoothOfRelativeDimension 1 Y.hom := h1.2.1
  haveI : ConnectedSpace Y.left := HDec.TSHecke.connectedSpace_of_R1fp hconn h1
  haveI : IrreducibleSpace Y.left := HDec.TSHecke.irreducibleSpace_of_connected Y.hom h1.1 h1.2.1
  -- a `ℚ̄`-point without CM
  obtain ⟨x, hx⟩ := hs.1 (OnePoint.some 1)
  obtain ⟨y₁, hy₁⟩ := hs.2 x
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : QML3 Qbar, Φ Qbar y₁ = M3.mk P₀ :=
    ⟨(Φ Qbar y₁).out, (Quotient.out_eq _).symm⟩
  have hΨ : Ψ x = Quotient.mk _ P₀.forget := by rw [← hy₁]; exact h6.2.2.2.2.2 y₁ P₀ hP₀
  obtain ⟨-, h4, h3, h24⟩ := h2 x x P₀.forget P₀.forget hΨ hΨ
  have n4 : ¬ HasCM4 P₀.q := fun h => by
    have := h4.1 h; rw [hx] at this; exact one_ne_zero (OnePoint.coe_injective this)
  have n3 : ¬ HasCM3 P₀.q := fun h => by
    have := h3.1 h; rw [hx] at this; exact OnePoint.coe_ne_infty _ this
  have n24 : ¬ HasCM24 P₀.q := fun h => by
    have := h24.1 h; rw [hx] at this
    have h' := OnePoint.coe_injective this
    norm_num at h'
  -- the automorphism fixing the point of `Q`
  have key : ∃ k : Fin 4, Nonempty (QMIso Q.q (Q.q.twist (HDec.LeafQM.AV.Pin.Exact.rep k))) ∧
      ¬ Nonempty (QMIso (P₀.q.twist (HDec.LeafQM.AV.Pin.Exact.rep k)) P₀.q) := by
    rcases twist_of_cm hT hU hC Q.surface Q.q hcm with ⟨-, hθ⟩ | ⟨-, hθ⟩ | ⟨-, hθ⟩
    · exact ⟨1, hθ, fun h => n4 ((hAL P₀.A P₀.surface P₀.q).1 h)⟩
    · exact ⟨2, hθ, fun h => n3 ((hAL P₀.A P₀.surface P₀.q).2.1 h)⟩
    · exact ⟨3, hθ, fun h => n24 ((hAL P₀.A P₀.surface P₀.q).2.2 h)⟩
  obtain ⟨k, ⟨θ⟩, hk⟩ := key
  obtain ⟨u, hu⟩ := fixed_class hT Q _ θ
  obtain ⟨gα, hgα⟩ := hh.1 (HDec.LeafQM.AV.Pin.Exact.rep k)
  obtain ⟨gu, hgu⟩ := hh.2 u
  set y := (Φ ℂ).symm (M3.mk Q) with hy
  have hyQ : Φ ℂ y = M3.mk Q := Equiv.apply_symm_apply _ _
  have hfix : y ≫ (gα.hom ≫ gu.hom) = y := by
    apply (Φ ℂ).injective
    rw [← Category.assoc, hgu, hgα, hyQ, ← hu]
  set s₀ := (Φ Qbar).symm (M3.mk P₀) with hs₀
  have hmove : s₀ ≫ (gα.hom ≫ gu.hom) ≠ s₀ := by
    intro heq
    have h' := congrArg (Φ Qbar) heq
    rw [← Category.assoc, hgu, hgα, hs₀, Equiv.apply_symm_apply, M3.twist_mk] at h'
    change M3.mk ((P₀.twist _).rightMul u) = M3.mk P₀ at h'
    obtain ⟨i⟩ := Quotient.exact h'
    exact hk ⟨⟨i.φ, i.ψ, i.left, i.right, i.equivariant⟩⟩
  obtain ⟨ιe, y₀, hy₀⟩ := exists_qbar_factor Y y _ hfix s₀ hmove
  obtain ⟨P, hP⟩ : ∃ P : QML3 Qbar, Φ Qbar y₀ = M3.mk P :=
    ⟨(Φ Qbar y₀).out, (Quotient.out_eq _).symm⟩
  obtain ⟨Q', hQ', hBC⟩ := h1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom y₀ P hP
  rw [hy₀, hyQ] at hQ'
  exact ⟨ιe, P, Q', hBC, Quotient.exact hQ'⟩

end Main


section Final

open MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

/-- `Q'.A ≅ P.A ×_{ℚ̄,ιe} ℂ` from `IsBaseChangeOf ιe P Q'` (the comparison of `descend_main`, TailO). -/
theorem bc_iso (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ) (hBC : IsBaseChangeOf ιe P Q') :
    ∃ (θ : PkgI3.AbVar.Hom Q'.A (bcC ιe P.A)) (θ' : PkgI3.AbVar.Hom (bcC ιe P.A) Q'.A),
      θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ := by
  obtain ⟨g', hg', hι', hl'⟩ := hBC
  let θ : Q'.A.X ⟶ (bcC ιe P.A).X :=
    Over.homMk ((bc_isPullback ιe P.A).lift g' Q'.A.X.hom hg'.w)
      ((bc_isPullback ιe P.A).lift_snd _ _ _)
  let θ' : (bcC ιe P.A).X ⟶ Q'.A.X :=
    Over.homMk (hg'.lift (fstC ιe P.A) (bcC ιe P.A).X.hom (bc_isPullback ιe P.A).w)
      (hg'.lift_snd _ _ _)
  have hθ : θ.left ≫ fstC ιe P.A = g' := (bc_isPullback ιe P.A).lift_fst _ _ _
  have hθ' : θ'.left ≫ g' = fstC ιe P.A := hg'.lift_fst _ _ _
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    ext1
    exact hg'.hom_ext (by rw [Over.comp_left, Category.assoc, hθ', hθ]; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ', Over.w θ]; simp)
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    ext1
    exact (bc_isPullback ιe P.A).hom_ext (by rw [Over.comp_left, Category.assoc, hθ, hθ']; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ, Over.w θ']; simp)
  have hη : η[Q'.A.X] ≫ θ = η[(bcC ιe P.A).X] := by
    ext1
    refine (bc_isPullback ιe P.A).hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, hθ, HDec.HSyn.G0Split.FibreQM.PeriodGlue.eta_comp hl',
        eta_bc_fst]
    · rw [Over.comp_left, Category.assoc, Over.w θ, Over.w η[Q'.A.X], Over.w η[(bcC ιe P.A).X]]
  have hη' : η[(bcC ιe P.A).X] ≫ θ' = η[Q'.A.X] := by
    rw [← hη, Category.assoc, hθθ', Category.comp_id]
  haveI : IsMonHom θ :=
    HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q'.A.X (bcC ιe P.A).X θ hη
  haveI : IsMonHom θ' :=
    HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral (bcC ιe P.A).X Q'.A.X θ' hη'
  exact ⟨PkgI3.AbVar.Hom.mk' θ, PkgI3.AbVar.Hom.mk' θ', hθθ', hθ'θ⟩

/-- **Every QM abelian surface over `ℂ` has a level-3 structure** (a generator of `A[3]` as an
`𝒪`-module: `gen3`). -/
theorem exists_level3 {A : PkgI3.AbVar ℂ} (hT : PkgI2.TorsionStructure.{0}) (hA : A.dim = 2)
    (q : QMStr A) : Nonempty (Level3 q) := by
  obtain ⟨v, hv, hann, -⟩ := gen3 hT hA q
  refine ⟨{ eta := { toFun := fun a => Additive.ofMul (act (q.iota a) v)
                     map_zero' := by
                       change Additive.ofMul (act (q.iota 0) v) = Additive.ofMul 1
                       rw [map_zero, act_zero]
                     map_add' := fun a b => by
                       change Additive.ofMul (act (q.iota (a + b)) v) =
                         Additive.ofMul (act (q.iota a) v * act (q.iota b) v)
                       rw [map_add, act_add] }
            linear := fun a b => by
              change Additive.ofMul (act (q.iota (a * b)) v) =
                Additive.ofMul (act (q.iota b) v ≫ (q.iota a).hom)
              rw [map_mul, act_mul]
            ker := fun a => by
              change Additive.ofMul (act (q.iota a) v) = Additive.ofMul 1 ↔ _
              rw [Additive.ofMul.injective.eq_iff, hann, Nat.cast_ofNat] }⟩

/-- **`STQM`, proved** (task st-qbar). A QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` is isomorphic to `A₀ ×_{ℚ̄,ιe} ℂ` for an abelian variety `A₀/ℚ̄`.

Hypotheses, all already in the bundles or proved on the base:
* `hRep` — research field `r1r2` (`LeafAdopt.R1R2fpRep`);
* `hconn` — added field `y3Connected` (`TSHecke.Y3Connected`);
* `hAL` — `HeckeRest.ALFixedPoints`, proved in the chain as `(qmRows_of7 t l).2.1` (TailX);
* `hT` — `PkgI2.TorsionStructure` (T5; textbook `t5`, from `mumfordTorsionAlgClosed`);
* `hU` — `ZInQ.LeafPush2.UniformizationExists` (T35; textbook `t35`, from `uniformizationLeafAll`);
* `hC` — `ZInQ.HomUnify.HomLatticeCorr` (textbook `homLatticeCorr`, from `uniformizationLeafAll`,
  `gagaMorphism`). -/
theorem stQM_of (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : _root_.PkgI2.TorsionStructure.{0})
    (hU : _root_.ZInQ.LeafPush2.UniformizationExists) (hC : _root_.ZInQ.HomUnify.HomLatticeCorr) :
    HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM := by
  intro A q hA hcm
  obtain ⟨e⟩ := exists_level3 hT hA q
  obtain ⟨ιe, P, Q', hBC, ⟨i⟩⟩ :=
    cm_point hRep hconn hAL hT hU (HDec.HSyn.homLatticeCorr_ofK5 hC) ⟨A, hA, q, e⟩ hcm
  obtain ⟨θ, θ', h1, h2⟩ := bc_iso ιe P Q' hBC
  refine ⟨ιe, P.A, PkgI3.AbVar.Hom.mk' (θ'.hom ≫ i.ψ.hom), PkgI3.AbVar.Hom.mk' (i.φ.hom ≫ θ.hom),
    ?_, ?_⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% i.right, h2]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h1, i.left]

/-- **`CMDescends` without `ShimuraTaniyamaQbar`** (the chain's `LeafQCheck.cmDescends_of` with `stQM_of`; T11(b) is
`t11b_of_exists5 t.t11bExists`, `TorsionDescends` is `torsionDescends_of_t5`). -/
theorem cmDescends_of (hRep : HDec.LeafAdopt.R1R2fpRep) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : _root_.PkgI2.TorsionStructure.{0})
    (hU : _root_.ZInQ.LeafPush2.UniformizationExists) (hC : _root_.ZInQ.HomUnify.HomLatticeCorr)
    (hR : ZInQ.LeafPush2.T11b_Rigidity) : HDec.HSyn.G0Split.FibreQM.PeriodMapH.CMDescends :=
  HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of (stQM_of hRep hconn hAL hT hU hC) hR
    (HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 hT) hRep

end Final


end GapST

