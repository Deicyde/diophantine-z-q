import ZInQKernel.Contrib.OneProof.RC.ModelLevels.Reduction
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq

/-! # The Atkin–Lehner image subgroup is cyclic of order `N`

Let `A` be an abelian group whose `d`-torsion has `d²` elements for every `d ∣ Q`, where
`Q = q^e` is a prime power, `N = Q * M` with `Q` and `M` coprime, and `C ≤ A` is cyclic of order
`N`. Put `C_Q = M • C` (the subgroup of order `Q`) and `D = A[Q] ⊔ C`. For every group
homomorphism `g` out of `A` with kernel `C_Q`, the image `g(D)` is cyclic of order `N`
(`isAddCyclic_map_atkinSum`). This is finite group theory; the torsion counts come from the
vendored `card_torsionBy_eq_sq_of_isAlgClosed` and
`AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`.

For an elliptic curve over an algebraically closed field in which `N` and `2` are nonzero
(`atkinImage`), the image is an element of `CyclicSubgroups _ N`. This holds in characteristic
0 and in every characteristic `ℓ ≥ 5` prime to `N`. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric6

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels

section Group

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The subgroup `m • C`: the image of `C` under multiplication by `m`. -/
def smulSubgroup (m : ℕ) (C : AddSubgroup A) : AddSubgroup A :=
  C.map (DistribSMul.toAddMonoidHom A m)

/-- The Atkin–Lehner sum `A[Q] ⊔ C`, with `A[Q]` the actual `Q`-torsion subgroup. -/
def atkinSum (Q : ℕ) (C : AddSubgroup A) : AddSubgroup A :=
  (Submodule.torsionBy ℤ A (Q : ℤ)).toAddSubgroup ⊔ C

theorem mem_torsionBy_iff (Q : ℕ) (y : A) :
    y ∈ (Submodule.torsionBy ℤ A (Q : ℤ)).toAddSubgroup ↔ Q • y = 0 := by
  change y ∈ Submodule.torsionBy ℤ A (Q : ℤ) ↔ _
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

/-- In `ZMod (q^e)`, a non-unit is killed by `q^(e-1)`. -/
private theorem pow_pred_mul_eq_zero {q e : ℕ} (hq : q.Prime) (he : 0 < e) (x : ZMod (q ^ e))
    (hx : ¬ IsUnit x) : ((q ^ (e - 1) : ℕ) : ZMod (q ^ e)) * x = 0 := by
  haveI : NeZero (q ^ e) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hxv : (x.val : ZMod (q ^ e)) = x := ZMod.natCast_zmod_val x
  rw [← hxv] at hx ⊢
  rw [ZMod.isUnit_iff_coprime] at hx
  have hdvd : q ∣ x.val := by
    by_contra hnd
    exact hx (Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((hq.coprime_iff_not_dvd).2 hnd)))
  obtain ⟨t, ht⟩ := hdvd
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ht]
  refine ⟨t, ?_⟩
  have : q ^ e = q ^ (e - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel he]
  rw [this]; ring

/-- A complement datum for an element of order `Q = q^e` in `(ZMod Q)²`. -/
private theorem exists_complement {q e : ℕ} (hq : q.Prime) (he : 0 < e)
    (v : ZMod (q ^ e) × ZMod (q ^ e)) (hv : addOrderOf v = q ^ e) :
    ∃ w : ZMod (q ^ e) × ZMod (q ^ e),
      (∀ y : ZMod (q ^ e) × ZMod (q ^ e), ∃ a b : ℤ, y = a • v + b • w) ∧
      (∀ n m : ℤ, n • w = m • v → n • w = 0) ∧ addOrderOf w = q ^ e := by
  haveI : NeZero (q ^ e) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hunit : IsUnit v.1 ∨ IsUnit v.2 := by
    by_contra h
    push_neg at h
    have h0 : (q ^ (e - 1)) • v = 0 := by
      ext
      · rw [Prod.smul_fst, nsmul_eq_mul]; exact pow_pred_mul_eq_zero hq he _ h.1
      · rw [Prod.smul_snd, nsmul_eq_mul]; exact pow_pred_mul_eq_zero hq he _ h.2
    have hd := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hv] at hd
    have := Nat.le_of_dvd (pow_pos hq.pos _) hd
    have hlt : q ^ (e - 1) < q ^ e := Nat.pow_lt_pow_right hq.one_lt (by omega)
    omega
  -- The cast of an integer and the integer cast of `ZMod` elements.
  have hcast : ∀ z : ZMod (q ^ e), ((z.val : ℤ) : ZMod (q ^ e)) = z := fun z => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hzsmul : ∀ (n : ℤ) (z : ZMod (q ^ e)), n • z = (n : ZMod (q ^ e)) * z := fun n z => by
    rw [zsmul_eq_mul]
  have horder : addOrderOf ((0 : ZMod (q ^ e)), (1 : ZMod (q ^ e))) = q ^ e := by
    rw [Prod.addOrderOf, addOrderOf_zero, ZMod.addOrderOf_one, Nat.lcm_one_left]
  have horder' : addOrderOf ((1 : ZMod (q ^ e)), (0 : ZMod (q ^ e))) = q ^ e := by
    rw [Prod.addOrderOf, addOrderOf_zero, ZMod.addOrderOf_one, Nat.lcm_one_right]
  rcases hunit with hu | hu
  · obtain ⟨u, hu⟩ := hu
    refine ⟨(0, 1), fun y => ?_, fun n m h => ?_, horder⟩
    · let a : ZMod (q ^ e) := y.1 * (u⁻¹ : (ZMod (q ^ e))ˣ)
      refine ⟨(a.val : ℤ), ((y.2 - a * v.2).val : ℤ), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.smul_mk, hzsmul, hcast, mul_zero, add_zero]
        rw [← hu]; simp [a, mul_assoc]
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.smul_mk, hzsmul, hcast, mul_one]
        ring
    · have h1 := congrArg Prod.fst h
      simp only [Prod.smul_fst, Prod.smul_mk, hzsmul, mul_zero] at h1
      rw [← hu] at h1
      have hm : (m : ZMod (q ^ e)) = 0 := by
        have := congrArg (· * ((u⁻¹ : (ZMod (q ^ e))ˣ) : ZMod (q ^ e))) h1
        simpa [mul_assoc] using this.symm
      rw [h]
      ext <;> simp [hzsmul, hm]
  · obtain ⟨u, hu⟩ := hu
    refine ⟨(1, 0), fun y => ?_, fun n m h => ?_, horder'⟩
    · let a : ZMod (q ^ e) := y.2 * (u⁻¹ : (ZMod (q ^ e))ˣ)
      refine ⟨(a.val : ℤ), ((y.1 - a * v.1).val : ℤ), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.smul_mk, hzsmul, hcast, mul_one]
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.smul_mk, hzsmul, hcast, mul_zero, add_zero]
        rw [← hu]; simp [a, mul_assoc]
    · have h1 := congrArg Prod.snd h
      simp only [Prod.smul_snd, Prod.smul_mk, hzsmul, mul_zero] at h1
      rw [← hu] at h1
      have hm : (m : ZMod (q ^ e)) = 0 := by
        have := congrArg (· * ((u⁻¹ : (ZMod (q ^ e))ˣ) : ZMod (q ^ e))) h1
        simpa [mul_assoc] using this.symm
      rw [h]
      ext <;> simp [hzsmul, hm]

/-- **Cyclicity of the Atkin–Lehner image (finite group theory).** Let `Q = q^e` with `q`
prime and `e > 0`, `N = Q * M` with `Q`, `M` coprime, `C ≤ A` cyclic of order `N`, and suppose
`#A[d] = d²` for every `d ∣ Q`. For every homomorphism `g` with kernel `M • C`, the image of
`A[Q] ⊔ C` is cyclic of order `N`. -/
theorem isAddCyclic_map_atkinSum {q e Q M N : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e)
    (hN : N = Q * M) (hN0 : N ≠ 0) (hcop : Q.Coprime M)
    (hcard : ∀ d : ℕ, d ∣ Q → Nat.card (Submodule.torsionBy ℤ A (d : ℤ)) = d ^ 2)
    (C : AddSubgroup A) (hC : IsAddCyclic C ∧ Nat.card C = N)
    (g : A →+ B) (hg : g.ker = smulSubgroup M C) :
    IsAddCyclic ((atkinSum Q C).map g) ∧ Nat.card ((atkinSum Q C).map g) = N := by
  subst hQe
  have hQ0 : q ^ e ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hN
    exact hN0 hN
  -- A generator of `C`.
  haveI := hC.1
  obtain ⟨⟨c, hcC⟩, hc⟩ := IsAddCyclic.exists_generator (α := C)
  have hCc : C = AddSubgroup.zmultiples c := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hc ⟨y, hy⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, congrArg Subtype.val hn⟩
    · intro hy
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      exact C.zsmul_mem hcC n
  have hoc : addOrderOf c = N := by
    rw [← hC.2, hCc, Nat.card_zmultiples]
  -- `v = M • c` of order `Q` and `cM = Q • c` of order `M`.
  set v := M • c with hvdef
  set cM := (q ^ e) • c with hcMdef
  have hov : addOrderOf v = q ^ e := by
    rw [hvdef, addOrderOf_nsmul' (x := c) hM0, hoc, hN,
      Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM0)]
  have hocM : addOrderOf cM = M := by
    rw [hcMdef, addOrderOf_nsmul' (x := c) hQ0, hoc, hN,
      Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hQ0)]
  have hker : ∀ y, g y = 0 ↔ ∃ m : ℤ, m • v = y := by
    intro y
    rw [← AddMonoidHom.mem_ker, hg, smulSubgroup, hCc, AddMonoidHom.map_zmultiples]
    exact AddSubgroup.mem_zmultiples_iff
  -- Coordinates on the `Q`-torsion.
  obtain ⟨φ⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    hQ0 hcard
  have hvT : v ∈ Submodule.torsionBy ℤ A ((q ^ e : ℕ) : ℤ) := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← hov]; exact addOrderOf_nsmul_eq_zero v
  let v' := φ.symm ⟨v, hvT⟩
  have hsub : ∀ y : Submodule.torsionBy ℤ A ((q ^ e : ℕ) : ℤ), addOrderOf (y : A) = addOrderOf y :=
    fun y => addOrderOf_injective (Submodule.torsionBy ℤ A ((q ^ e : ℕ) : ℤ)).subtype.toAddMonoidHom
      Subtype.val_injective y
  have hov' : addOrderOf v' = q ^ e :=
    (AddEquiv.addOrderOf_eq φ.symm _).trans ((hsub ⟨v, hvT⟩).symm.trans hov)
  obtain ⟨w', hspan, hint, how'⟩ := exists_complement hq he v' hov'
  let w : A := (φ w' : A)
  have how : addOrderOf w = q ^ e :=
    (hsub (φ w')).trans ((AddEquiv.addOrderOf_eq φ w').trans how')
  have hφv : (φ v' : A) = v := by simp [v']
  have hφz : ∀ (n : ℤ) (y : ZMod (q ^ e) × ZMod (q ^ e)), (φ (n • y) : A) = n • (φ y : A) := by
    intro n y; rw [map_zsmul]; rfl
  -- The candidate generator.
  let x := w + cM
  have hcop' : Int.gcd (q ^ e : ℕ) M = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℤ, α * (q ^ e : ℕ) + β * M = 1 := by
    refine ⟨Int.gcdA (q ^ e : ℕ) M, Int.gcdB (q ^ e : ℕ) M, ?_⟩
    have := Int.gcd_eq_gcd_ab (q ^ e : ℕ) M
    rw [hcop'] at this
    linear_combination -this
  have hQw : ((q ^ e : ℕ) : ℤ) • w = 0 := by
    rw [natCast_zsmul, ← how]; exact addOrderOf_nsmul_eq_zero w
  have hMcM : (M : ℤ) • cM = 0 := by
    rw [natCast_zsmul, ← hocM]; exact addOrderOf_nsmul_eq_zero cM
  have hQv : ((q ^ e : ℕ) : ℤ) • v = 0 := by
    rw [natCast_zsmul, ← hov]; exact addOrderOf_nsmul_eq_zero v
  -- The order of `g x` is `N`.
  have hgx : ∀ n : ℤ, n • g x = 0 ↔ (N : ℤ) ∣ n := by
    intro n
    rw [← map_zsmul, hker]
    constructor
    · rintro ⟨m, hm⟩
      -- Multiply by `Q`: `M ∣ Q n`, so `M ∣ n`.
      have h1 : (n * (q ^ e : ℕ)) • cM = 0 := by
        have := congrArg (((q ^ e : ℕ) : ℤ) • ·) hm
        simp only [smul_add, smul_comm ((q ^ e : ℕ) : ℤ) _ v, hQv, smul_zero,
          smul_comm ((q ^ e : ℕ) : ℤ) n w, hQw, zero_add, x] at this
        rw [mul_comm, mul_zsmul]; exact this.symm
      have hMn : (M : ℤ) ∣ n := by
        have := (addOrderOf_dvd_iff_zsmul_eq_zero).2 h1
        rw [hocM] at this
        exact (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact hcop')).dvd_of_dvd_mul_right this
      -- Multiply by `M`: `(M n) • w = (M m) • v`, so `Q ∣ M n`.
      have h2 : (M * n) • w = (M * m) • v := by
        have := congrArg ((M : ℤ) • ·) hm
        simp only [smul_add, x, smul_comm (M : ℤ) n cM, hMcM, smul_zero, add_zero] at this
        rw [mul_zsmul, mul_zsmul]; exact this.symm
      have h2' : (M * n) • w' = (M * m) • v' := by
        apply φ.injective
        apply Subtype.ext
        rw [hφz, hφz, hφv]; exact h2
      have h3 := hint _ _ h2'
      have hQn : ((q ^ e : ℕ) : ℤ) ∣ M * n := by
        rw [← how']; exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 h3
      have hQn' : ((q ^ e : ℕ) : ℤ) ∣ n :=
        (Int.isCoprime_iff_gcd_eq_one.mpr hcop').dvd_of_dvd_mul_left hQn
      rw [hN, Nat.cast_mul]
      exact (Int.isCoprime_iff_gcd_eq_one.mpr hcop').mul_dvd hQn' hMn
    · rintro ⟨t, rfl⟩
      refine ⟨0, ?_⟩
      have h1 : ((N : ℤ) * t) • w = 0 := by
        rw [show (N : ℤ) * t = (t * M) * ((q ^ e : ℕ) : ℤ) by rw [hN]; push_cast; ring,
          ← smul_smul, hQw, smul_zero]
      have h2 : ((N : ℤ) * t) • cM = 0 := by
        rw [show (N : ℤ) * t = (t * ((q ^ e : ℕ) : ℤ)) * M by rw [hN]; push_cast; ring,
          ← smul_smul, hMcM, smul_zero]
      rw [zero_smul]
      change 0 = ((N : ℤ) * t) • (w + cM)
      rw [smul_add, h1, h2, add_zero]
  have hogx : addOrderOf (g x) = N := by
    apply Nat.dvd_antisymm
    · apply addOrderOf_dvd_of_nsmul_eq_zero
      rw [← natCast_zsmul]; exact (hgx N).2 dvd_rfl
    · have := (hgx (addOrderOf (g x))).1 (by rw [natCast_zsmul]; exact addOrderOf_nsmul_eq_zero _)
      exact_mod_cast this
  -- The image is generated by `g x`.
  have hxD : x ∈ atkinSum (q ^ e) C := by
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left ?_) (AddSubgroup.mem_sup_right ?_)
    · exact (φ w').property
    · rw [hCc]; exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples c) _
  have hmap : (atkinSum (q ^ e) C).map g = AddSubgroup.zmultiples (g x) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hy
      obtain ⟨a, b, hab⟩ := hspan (φ.symm ⟨t, ht⟩)
      have ht' : t = a • v + b • w := by
        have h1 := congrArg (fun y => (φ y : A)) hab
        have h2 : (φ (a • v' + b • w') : A) = a • v + b • w := by
          rw [map_add, Submodule.coe_add, hφz, hφz, hφv]
        simp only [AddEquiv.apply_symm_apply] at h1
        exact h1.trans h2
      rw [hCc] at hz
      obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
      -- `c = α • cM + β • v`.
      have hc' : c = α • cM + β • v := by
        rw [hcMdef, hvdef, ← natCast_zsmul, ← natCast_zsmul, ← mul_zsmul, ← mul_zsmul,
          ← add_zsmul, hαβ, one_zsmul]
      have hgv : g v = 0 := (hker v).2 ⟨1, one_zsmul v⟩
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨b * β * M + j * α * α * (q ^ e : ℕ), ?_⟩
      rw [ht', hc']
      simp only [map_add, map_zsmul, hgv, smul_zero, add_zero, zero_add, x]
      have hgQw : ((q ^ e : ℕ) : ℤ) • g w = 0 := by rw [← map_zsmul, hQw, map_zero]
      have hgMcM : (M : ℤ) • g cM = 0 := by rw [← map_zsmul, hMcM, map_zero]
      have hmod : ∀ (y : B) (K n s : ℤ), K • y = 0 → (n + s * K) • y = n • y := by
        intro y K n s hy
        rw [add_zsmul, ← smul_smul, hy, smul_zero, add_zero]
      have e1 : (b * β * M + j * α * α * (q ^ e : ℕ)) • g w = b • g w := by
        have : b * β * M + j * α * α * (q ^ e : ℕ) =
            b + (j * α * α - b * α) * (q ^ e : ℕ) := by linear_combination b * hαβ
        rw [this, hmod _ _ _ _ hgQw]
      have e2 : (b * β * M + j * α * α * (q ^ e : ℕ)) • g cM = (j * α) • g cM := by
        have : b * β * M + j * α * α * (q ^ e : ℕ) =
            j * α + (b * β - j * α * β) * M := by linear_combination j * α * hαβ
        rw [this, hmod _ _ _ _ hgMcM]
      rw [smul_add, e1, e2, smul_smul]
    · rw [AddSubgroup.zmultiples_le]
      exact ⟨x, hxD, rfl⟩
  rw [hmap, Nat.card_zmultiples, hogx]
  exact ⟨inferInstance, rfl⟩

end Group

section Curve

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k]

/-- **The Atkin–Lehner image subgroup on an elliptic curve.** Over an algebraically closed
field in which `N` and `2` are nonzero, let `Q = q^e` (`q` prime, `e > 0`) exactly divide
`N = Q * M`, and let `C` be a cyclic subgroup of order `N` of `E(k)`. For every group
homomorphism `g` out of `E(k)` with kernel `M • C`, the image `g(E[Q] ⊔ C)` is cyclic of order
`N`. The torsion counts are the vendored `card_torsionBy_eq_sq_of_isAlgClosed`. -/
theorem isAddCyclic_map_atkinSum_curve (E : WeierstrassCurve k) [E.IsElliptic]
    {q e Q M N : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e)
    (hN : N = Q * M) (hcop : Q.Coprime M) (hNk : (N : k) ≠ 0) (h2 : (2 : k) ≠ 0)
    (C : AddSubgroup E.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = N)
    {B : Type*} [AddCommGroup B] (g : E.toAffine.Point →+ B) (hg : g.ker = smulSubgroup M C) :
    IsAddCyclic ((atkinSum Q C).map g) ∧ Nat.card ((atkinSum Q C).map g) = N := by
  refine isAddCyclic_map_atkinSum hq he hQe hN (fun h => hNk (by rw [h, Nat.cast_zero])) hcop
    (fun d hd => ?_) C hC g hg
  apply E.card_torsionBy_eq_sq_of_isAlgClosed _ h2
  obtain ⟨t, rfl⟩ := hd.trans (Dvd.intro M hN.symm)
  intro h; apply hNk; push_cast; rw [h, zero_mul]

/-- The Atkin–Lehner image as an element of `CyclicSubgroups _ N`. -/
def atkinImage (E : WeierstrassCurve k) [E.IsElliptic]
    {q e Q M N : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e)
    (hN : N = Q * M) (hcop : Q.Coprime M) (hNk : (N : k) ≠ 0) (h2 : (2 : k) ≠ 0)
    (C : CyclicSubgroups E.toAffine.Point N)
    {B : Type*} [AddCommGroup B] (g : E.toAffine.Point →+ B)
    (hg : g.ker = smulSubgroup M C.1) : CyclicSubgroups B N :=
  ⟨(atkinSum Q C.1).map g,
    isAddCyclic_map_atkinSum_curve E hq he hQe hN hcop hNk h2 C.1 C.2 g hg⟩

end Curve

#print axioms isAddCyclic_map_atkinSum
#print axioms isAddCyclic_map_atkinSum_curve
#print axioms atkinImage

end ZInQ.Manuscript.RC.ModelGeneric6
