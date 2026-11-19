import ZInQKernel.Contrib.OneProof.ShimuraOrbitsNormal

/-! The triangular sums and diamonds descend to Γ₁(N)-orbits. -/

noncomputable section

namespace ShimuraSteps.Orbits

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

abbrev Orb (N : ℕ) := MulAction.orbitRel.Quotient (Gamma1 N) ℍ
abbrev Divisors (N : ℕ) := Orb N →₀ ℤ

def orb (N : ℕ) (τ : ℍ) : Orb N := Quotient.mk'' τ

def point {N : ℕ} (q : Orb N) : Divisors N := Finsupp.single q 1

theorem orb_smul {N : ℕ} {g : SL(2, ℤ)} (hg : g ∈ Gamma1 N) (τ : ℍ) :
    orb N (g • τ) = orb N τ := by
  apply Quotient.sound
  exact ⟨⟨g, hg⟩, rfl⟩

theorem orb_eq_of_residue {N : ℕ} (g h : Gamma0 N) (he : Gamma0Map N g = Gamma0Map N h)
    (τ : ℍ) : orb N ((g : SL(2, ℤ)) • τ) = orb N ((h : SL(2, ℤ)) • τ) := by
  have e := orb_smul (mul_inv_mem_Gamma1_of_Gamma0Map_eq g h he) ((h : SL(2, ℤ)) • τ)
  simpa only [← mul_smul, inv_mul_cancel_right] using e

/-- A Γ₀(N) matrix acts on Γ₁(N)-orbits by normality. -/
def diamondOrb {N : ℕ} (g : Gamma0 N) : Orb N → Orb N :=
  Quotient.lift (fun τ => orb N ((g : SL(2, ℤ)) • τ)) (by
    intro τ τ' he
    obtain ⟨s, rfl⟩ : ∃ s : Gamma1 N, s • τ' = τ := he
    simpa only [Subgroup.smul_def, ← mul_smul, inv_mul_cancel_right] using
      (orb_smul (Gamma0_normalizes_Gamma1 g s s.property) ((g : SL(2, ℤ)) • τ')))

def diamond {N : ℕ} (g : Gamma0 N) : Module.End ℤ (Divisors N) :=
  Finsupp.linearCombination ℤ (point ∘ diamondOrb g)

@[simp] theorem diamond_point {N : ℕ} (g : Gamma0 N) (τ : ℍ) :
    diamond g (point (orb N τ)) = point (orb N ((g : SL(2, ℤ)) • τ)) := by
  simp only [diamond, point, Finsupp.linearCombination_single, one_smul]
  rfl

theorem diamond_independent {N : ℕ} (g h : Gamma0 N) (he : Gamma0Map N g = Gamma0Map N h) :
    diamond g = diamond h := by
  unfold diamond
  apply congrArg (Finsupp.linearCombination ℤ)
  funext q
  induction q using Quotient.inductionOn
  exact congrArg point (orb_eq_of_residue g h he _)

def lift (N a : ℕ) (ha : a.Coprime N) : Gamma0 N :=
  ⟨gamma0Twist N a ha, gamma0Twist_mem_Gamma0 ha⟩

@[simp] theorem lift_residue (N a : ℕ) (ha : a.Coprime N) :
    Gamma0Map N (lift N a ha) = (a : ZMod N) := by
  simp [lift, Gamma0Map_apply]

def triAct (a b d : ℕ) (τ : ℍ) : ℍ :=
  if h : 0 < (tri a b d).det then matGL (tri a b d) h • τ else τ

theorem triAct_eq_smul (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    triAct a b d τ = matGL (tri a b d) (by rw [det_tri]; positivity) • τ :=
  dite_eq_left _

theorem coe_triAct (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    (triAct a b d τ : ℂ) = ((a : ℂ) * (τ : ℂ) + b) / d := by
  rw [triAct_eq_smul a b d ha hd]
  have hg : 0 < (matGL (tri a b d) (by rw [det_tri]; positivity)).det.val := by
    change 0 < ((Int.castRingHom ℝ).mapMatrix (tri a b d)).det
    rw [← RingHom.map_det, det_tri]
    change (0 : ℝ) < (((a : ℤ) * (d : ℤ) : ℤ) : ℝ)
    exact_mod_cast (mul_pos (show (0 : ℤ) < a by exact_mod_cast ha)
      (show (0 : ℤ) < d by exact_mod_cast hd))
  rw [coe_smul_of_det_pos hg]
  simp [num, denom, matGL, tri]

theorem triAct_comp {a c d f : ℕ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (hf : 0 < f)
    (b e : ℕ) (τ : ℍ) :
    triAct a b d (triAct c e f τ) = triAct (a * c) (a * e + b * f) (d * f) τ := by
  apply UpperHalfPlane.ext
  simp only [coe_triAct _ _ _ ha hd, coe_triAct _ _ _ hc hf,
    coe_triAct _ _ _ (Nat.mul_pos ha hc) (Nat.mul_pos hd hf), Nat.cast_add, Nat.cast_mul]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hf' : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  field_simp
  ring

theorem triAct_scale {a d p : ℕ} (ha : 0 < a) (hd : 0 < d) (hp : 0 < p)
    (b : ℕ) (τ : ℍ) :
    triAct (p * a) (p * b) (p * d) τ = triAct a b d τ := by
  apply UpperHalfPlane.ext
  simp only [coe_triAct _ _ _ ha hd,
    coe_triAct _ _ _ (Nat.mul_pos hp ha) (Nat.mul_pos hp hd), Nat.cast_mul]
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [mul_assoc, ← mul_add, mul_div_mul_left _ _ hp']

theorem gammaOne_translation (N : ℕ) (z : ℤ) :
    ModularGroup.T ^ z ∈ Gamma1 N := T_zpow_mem_Gamma1 N z

theorem orb_triAct_mod {N a d : ℕ} (ha : 0 < a) (hd : 0 < d) (g : Gamma0 N)
    (b : ℕ) (τ : ℍ) :
    orb N ((g : SL(2, ℤ)) • triAct a b d τ) =
      orb N ((g : SL(2, ℤ)) • triAct a (b % d) d τ) := by
  let T : SL(2, ℤ) := ModularGroup.T ^ ((b / d : ℕ) : ℤ)
  have h : triAct a b d τ = T • triAct a (b % d) d τ := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply]
    rw [show (↑T : Mat) = !![1, ((b / d : ℕ) : ℤ); 0, 1] from ModularGroup.coe_T_zpow _]
    simp [coe_triAct _ _ _ ha hd, -Int.natCast_ediv]
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have e : (b : ℂ) = d * (b / d : ℕ) + (b % d : ℕ) := by
      exact_mod_cast (Nat.mod_add_div b d).symm.trans (Nat.add_comm _ _)
    field_simp
    linear_combination e
  rw [h]
  have he := orb_smul (Gamma0_normalizes_Gamma1 g T (gammaOne_translation N _))
    ((g : SL(2, ℤ)) • triAct a (b % d) d τ)
  simpa only [← mul_smul, inv_mul_cancel_right] using he

/-- Reducing the right translate of a triangular matrix permutes the triangular
indices. The left multiplier remembers the change in the first diagonal entry. -/
private theorem exists_reduce_right {N n : ℕ} (hn : 0 < n) (g : Gamma0 N) (i : Rep N n) :
    ∃ (l : Gamma0 N) (j : Rep N n),
      repMat i * (↑(g : SL(2, ℤ)) : Mat) = (↑(l : SL(2, ℤ)) : Mat) * repMat j ∧
      (i.1.val : ZMod N) * Gamma0Map N l = Gamma0Map N g * (j.1.val : ZMod N) := by
  have hg₀ := Gamma0_mem.mp g.property
  have hdet : (repMat i * (↑(g : SL(2, ℤ)) : Mat)).det = (n : ℤ) := by
    rw [Matrix.det_mul, det_repMat, (g : SL(2, ℤ)).2, mul_one]
  have hc : (((repMat i * (↑(g : SL(2, ℤ)) : Mat)) 1 0 : ℤ) : ZMod N) = 0 := by
    simp [repMat, tri, Matrix.mul_apply, Fin.sum_univ_two, hg₀]
  have h₀ : (((repMat i * (↑(g : SL(2, ℤ)) : Mat)) 0 0 : ℤ) : ZMod N) =
      (i.1.val : ZMod N) * (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) := by
    simp [repMat, tri, Matrix.mul_apply, Fin.sum_univ_two, hg₀]
  have hu := ((ZMod.isUnit_iff_coprime _ _).2 (div_spec i.1).2.2.2).mul
    (isUnit_intCast_apply_zero_zero_of_mem_Gamma0 g.property)
  obtain ⟨l, j, h⟩ := exists_reduce hn hdet hc (h₀ ▸ hu : IsUnit _)
  refine ⟨l, j, h, ?_⟩
  rw [h] at h₀
  simp only [repMat, tri, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, Int.cast_mul, Int.cast_natCast] at h₀
  have hL := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 l.property
  have hG := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 g.property
  change _ * (((l : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) =
    (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) * _
  linear_combination
    -((((l : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)) * h₀ +
    -((i.1.val : ZMod N) * (((l : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)) * hG +
    ((j.1.val : ZMod N) * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)) * hL

private theorem reduce_right_injective {N n : ℕ} (g : Gamma0 N)
    (j : Rep N n → Rep N n) (l : Rep N n → Gamma0 N)
    (h : ∀ i, repMat i * (↑(g : SL(2, ℤ)) : Mat) =
      (↑(l i : SL(2, ℤ)) : Mat) * repMat (j i)) : Function.Injective j := by
  intro i i' e
  apply reduce_unique ((l i' : SL(2, ℤ)) * (l i : SL(2, ℤ))⁻¹)
  let G : SL(2, ℤ) := g
  let L : Rep N n → SL(2, ℤ) := fun i => l i
  have h' (a : Rep N n) : repMat a =
      (↑(L a) : Mat) * repMat (j a) * (↑G⁻¹ : Mat) := by
    rw [← h a, mul_assoc]
    change repMat a = repMat a * ((↑G : Mat) * (↑G⁻¹ : Mat))
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  change (↑(L i' * (L i)⁻¹) : Mat) * repMat i = repMat i'
  rw [h' i, e, h' i', ← mul_assoc, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

private theorem triAct_reduce {N n : ℕ} (hn : 0 < n) (g l : Gamma0 N) (i j : Rep N n)
    (h : repMat i * (↑(g : SL(2, ℤ)) : Mat) = (↑(l : SL(2, ℤ)) : Mat) * repMat j)
    (τ : ℍ) :
    triAct i.1.val i.2.val (n / i.1.val) ((g : SL(2, ℤ)) • τ) =
      (l : SL(2, ℤ)) • triAct j.1.val j.2.val (n / j.1.val) τ := by
  have hh (k : Rep N n) : 0 < (repMat k).det := by rw [det_repMat]; exact_mod_cast hn
  have he (k : Rep N n) (w : ℍ) :
      matGL (repMat k) (hh k) • w = triAct k.1.val k.2.val (n / k.1.val) w :=
    (triAct_eq_smul _ _ _ (div_spec k.1).1 (div_spec k.1).2.1 w).symm
  have hg : 0 < ((g : SL(2, ℤ)) : Mat).det := by rw [(g : SL(2, ℤ)).2]; decide
  have hl : 0 < ((l : SL(2, ℤ)) : Mat).det := by rw [(l : SL(2, ℤ)).2]; decide
  have e : matGL (repMat i) (hh i) * mapGL ℝ (g : SL(2, ℤ)) =
      mapGL ℝ (l : SL(2, ℤ)) * matGL (repMat j) (hh j) := by
    rw [← matGL_sl (g : SL(2, ℤ)), ← matGL_sl (l : SL(2, ℤ)),
      ← matGL_mul _ _ (hh i) hg, ← matGL_mul _ _ hl (hh j)]
    exact Units.ext (congrArg (fun A : Mat => A.map (Int.cast : ℤ → ℝ)) h)
  change triAct i.1.val i.2.val (n / i.1.val) ((mapGL ℝ (g : SL(2, ℤ))) • τ) =
    (mapGL ℝ (l : SL(2, ℤ))) • triAct j.1.val j.2.val (n / j.1.val) τ
  simpa only [mul_smul, he] using congrArg (fun A : GL (Fin 2) ℝ => A • τ) e

def term {N : ℕ} (g : Gamma0 N) (a b d : ℕ) (τ : ℍ) : Divisors N :=
  point (orb N ((g : SL(2, ℤ)) • triAct a b d τ))

theorem term_residue {N : ℕ} {g h : Gamma0 N} (he : Gamma0Map N g = Gamma0Map N h)
    (a b d : ℕ) (τ : ℍ) : term g a b d τ = term h a b d τ :=
  congrArg point (orb_eq_of_residue g h he _)

def repLift {N n : ℕ} (a : Div N n) : Gamma0 N := lift N a.val (div_spec a).2.2.2

def sumAt (N n : ℕ) (τ : ℍ) : Divisors N :=
  ∑ i : Rep N n, term (repLift i.1) i.1.val i.2.val (n / i.1.val) τ

theorem sumAt_covariant {N n : ℕ} (g : Gamma0 N) (τ : ℍ) :
    sumAt N n ((g : SL(2, ℤ)) • τ) = diamond g (sumAt N n τ) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsEmpty (Rep N 0) := ⟨fun i => (Nat.mem_divisors.mp
      (Finset.mem_filter.mp i.1.property).1).2 rfl⟩
    simp [sumAt]
  choose l j h hj using exists_reduce_right hn g
  let e := Equiv.ofBijective j (Finite.injective_iff_bijective.mp (reduce_right_injective g j l h))
  rw [sumAt, sumAt, map_sum]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  change _ = diamond g (term (repLift (j i).1) (j i).1.val (j i).2.val (n / (j i).1.val) τ)
  simp only [term, triAct_reduce hn g (l i) i (j i) (h i), diamond_point, ← mul_smul]
  apply congrArg point
  apply orb_eq_of_residue (repLift i.1 * l i) (g * repLift (j i).1)
  simpa [repLift] using hj i

/-- The sum is independent of the representative of the Γ₁(N)-orbit. -/
theorem sumAt_invariant {N n : ℕ} {g : SL(2, ℤ)} (hg : g ∈ Gamma1 N) (τ : ℍ) :
    sumAt N n (g • τ) = sumAt N n τ := by
  let g₀ : Gamma0 N := ⟨g, (mem_Gamma1_iff.mp hg).1⟩
  have he : Gamma0Map N g₀ = Gamma0Map N 1 := by
    rw [map_one]
    exact (mem_Gamma1_iff.mp hg).2
  change sumAt N n ((g₀ : SL(2, ℤ)) • τ) = _
  rw [sumAt_covariant, diamond_independent g₀ 1 he]
  simp [sumAt, term, map_sum]

/-- The operator R_n on the free abelian group on Γ₁(N)-orbits. -/
def R (N n : ℕ) : Module.End ℤ (Divisors N) :=
  Finsupp.linearCombination ℤ (Quotient.lift (sumAt N n) (by
    intro τ τ' he
    obtain ⟨g, rfl⟩ : ∃ g : Gamma1 N, g • τ' = τ := he
    exact sumAt_invariant g.property _))

@[simp] theorem R_point (N n : ℕ) (τ : ℍ) : R N n (point (orb N τ)) = sumAt N n τ := by
  simp [R, point, orb]

theorem sumAt_lifts {N n : ℕ} (g : Div N n → Gamma0 N)
    (hg : ∀ a, Gamma0Map N (g a) = (a.val : ZMod N)) (τ : ℍ) :
    sumAt N n τ = ∑ a : Div N n, ∑ b : Fin (n / a.val),
      term (g a) a.val b.val (n / a.val) τ := by
  rw [sumAt, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    term_residue (by simpa [repLift] using (hg a).symm) _ _ _ _

#print axioms orb_smul
#print axioms orb_eq_of_residue
#print axioms diamond_point
#print axioms diamond_independent
#print axioms lift_residue
#print axioms triAct_eq_smul
#print axioms coe_triAct
#print axioms triAct_comp
#print axioms triAct_scale
#print axioms gammaOne_translation
#print axioms orb_triAct_mod
#print axioms exists_reduce_right
#print axioms reduce_right_injective
#print axioms triAct_reduce
#print axioms term_residue
#print axioms sumAt_covariant
#print axioms sumAt_invariant
#print axioms R_point
#print axioms sumAt_lifts

end ShimuraSteps.Orbits
