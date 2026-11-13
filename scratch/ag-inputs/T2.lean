import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Descent.B1Quat

noncomputable section

namespace AGInO

open LeafQM

theorem int_coord (r : ℚ) (k : ℕ) (h : r.den ∣ k) : ∃ z : ℤ, (k : ℚ) * r = z := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t * r.num, ?_⟩
  push_cast
  rw [mul_comm (r.den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem exists_nat_smul_mem (b : B) : ∃ n : ℕ, 0 < n ∧ ((n : ℚ) • b) ∈ O := by
  refine ⟨b.re.den * b.imI.den * b.imJ.den * b.imK.den, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := int_coord b.re (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.imI.den * b.imJ.den * b.imK.den, by ring⟩
  obtain ⟨z1, h1⟩ := int_coord b.imI (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.re.den * b.imJ.den * b.imK.den, by ring⟩
  obtain ⟨z2, h2⟩ := int_coord b.imJ (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.re.den * b.imI.den * b.imK.den, by ring⟩
  obtain ⟨z3, h3⟩ := int_coord b.imK (b.re.den * b.imI.den * b.imJ.den * b.imK.den)
    ⟨b.re.den * b.imI.den * b.imJ.den, by ring⟩
  have : ((b.re.den * b.imI.den * b.imJ.den * b.imK.den : ℕ) : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  rw [this]
  exact mem_O_of_int z0 z1 z2 z3

/-- A denominator for `b`. -/
def nOf (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem nOf_pos (b : B) : 0 < nOf b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem nOf_mem (b : B) : ((nOf b : ℚ) • b) ∈ O := (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- The `ℚ`-linear extension of `α ∈ Aut(𝒪)` to `B`, as a function. -/
def extFun (α : O ≃+* O) (b : B) : B := ((nOf b : ℚ)⁻¹) • (α ⟨(nOf b : ℚ) • b, nOf_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (y : B) : (n : B) * y = (n : ℚ) • y := by
  rw [Algebra.smul_def, map_natCast]

theorem coe_alpha_natCast_mul (α : O ≃+* O) (n : ℕ) (x : O) :
    (α ((n : O) * x) : B) = (n : ℚ) • (α x : B) := by
  rw [map_mul, map_natCast, Subring.coe_mul, Subring.coe_natCast, natCast_mul_eq_smul]

/-- Independence of the denominator. -/
theorem extFun_eq (α : O ≃+* O) (b : B) (n : ℕ) (hn : 0 < n) (x : O)
    (hx : (x : B) = (n : ℚ) • b) : extFun α b = ((n : ℚ)⁻¹) • (α x : B) := by
  set m := nOf b
  have hm : (0 : ℚ) < m := by exact_mod_cast nOf_pos b
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  set y : O := ⟨(m : ℚ) • b, nOf_mem b⟩
  have hxy : (n : O) * y = (m : O) * x := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, Subring.coe_natCast, hx,
      natCast_mul_eq_smul, natCast_mul_eq_smul]
    change (n : ℚ) • ((m : ℚ) • b) = (m : ℚ) • ((n : ℚ) • b)
    rw [smul_smul, smul_smul, mul_comm]
  have key : (n : ℚ) • (α y : B) = (m : ℚ) • (α x : B) := by
    rw [← coe_alpha_natCast_mul, ← coe_alpha_natCast_mul, hxy]
  unfold extFun
  change ((m : ℚ)⁻¹) • (α y : B) = _
  have := congrArg (fun z : B => ((n : ℚ)⁻¹ * (m : ℚ)⁻¹) • z) key
  simp only [smul_smul] at this
  rw [show (n : ℚ)⁻¹ * (m : ℚ)⁻¹ * n = (m : ℚ)⁻¹ by field_simp,
    show (n : ℚ)⁻¹ * (m : ℚ)⁻¹ * m = (n : ℚ)⁻¹ by field_simp] at this
  exact this

theorem extFun_coe (α : O ≃+* O) (a : O) : extFun α a = α a := by
  rw [extFun_eq α a 1 one_pos a (by simp)]
  simp

/-- The extension as a `ℚ`-algebra map. -/
def extHom (α : O ≃+* O) : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by
    have := extFun_coe α 1
    simpa using this
  map_zero' := by
    have := extFun_coe α 0
    simpa using this
  map_mul' b c := by
    set nb := nOf b
    set nc := nOf c
    have hb : (0 : ℚ) < nb := by exact_mod_cast nOf_pos b
    have hc : (0 : ℚ) < nc := by exact_mod_cast nOf_pos c
    set xb : O := ⟨(nb : ℚ) • b, nOf_mem b⟩
    set xc : O := ⟨(nc : ℚ) • c, nOf_mem c⟩
    rw [extFun_eq α (b * c) (nb * nc) (Nat.mul_pos (nOf_pos b) (nOf_pos c)) (xb * xc) (by
      rw [Subring.coe_mul]
      change ((nb : ℚ) • b) * ((nc : ℚ) • c) = _
      rw [smul_mul_smul_comm]; push_cast; rfl)]
    change _ = ((nb : ℚ)⁻¹ • (α xb : B)) * ((nc : ℚ)⁻¹ • (α xc : B))
    rw [smul_mul_smul_comm, map_mul, Subring.coe_mul]
    push_cast
    rw [mul_inv]
  map_add' b c := by
    set nb := nOf b
    set nc := nOf c
    have hb : (0 : ℚ) < nb := by exact_mod_cast nOf_pos b
    have hc : (0 : ℚ) < nc := by exact_mod_cast nOf_pos c
    set xb : O := ⟨(nb : ℚ) • b, nOf_mem b⟩
    set xc : O := ⟨(nc : ℚ) • c, nOf_mem c⟩
    rw [extFun_eq α (b + c) (nb * nc) (Nat.mul_pos (nOf_pos b) (nOf_pos c))
      ((nc : O) * xb + (nb : O) * xc) (by
        rw [Subring.coe_add, Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast,
          Subring.coe_natCast, natCast_mul_eq_smul, natCast_mul_eq_smul]
        change (nc : ℚ) • ((nb : ℚ) • b) + (nb : ℚ) • ((nc : ℚ) • c) = _
        rw [smul_smul, smul_smul, smul_add]; push_cast; ring_nf)]
    change _ = ((nb : ℚ)⁻¹ • (α xb : B)) + ((nc : ℚ)⁻¹ • (α xc : B))
    rw [map_add, Subring.coe_add, coe_alpha_natCast_mul, coe_alpha_natCast_mul, smul_add,
      smul_smul, smul_smul]
    congr 1
    · congr 1; push_cast; field_simp
    · congr 1; push_cast; field_simp
  commutes' q := by
    change extFun α (algebraMap ℚ B q) = algebraMap ℚ B q
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    rw [extFun_eq α _ q.den q.den_pos ((q.num : ℤ) : O) (by
      rw [Subring.coe_intCast, Algebra.smul_def, ← map_mul, mul_comm, Rat.mul_den_eq_num,
        map_intCast])]
    rw [map_intCast, Subring.coe_intCast, ← map_intCast (algebraMap ℚ B), Algebra.smul_def,
      ← map_mul]
    congr 1
    rw [← Rat.mul_den_eq_num]; field_simp

theorem extHom_coe (α : O ≃+* O) (a : O) : extHom α a = α a := extFun_coe α a

theorem extHom_symm_comp (α : O ≃+* O) (b : B) : extHom α (extHom α.symm b) = b := by
  set n := nOf b
  have hn : (0 : ℚ) < n := by exact_mod_cast nOf_pos b
  set x : O := ⟨(n : ℚ) • b, nOf_mem b⟩
  change extFun α (extFun α.symm b) = b
  have h1 : extFun α.symm b = (n : ℚ)⁻¹ • (α.symm x : B) := rfl
  rw [extFun_eq α _ (nOf b) (nOf_pos b) (α.symm x) (by rw [h1, smul_smul, mul_inv_cancel₀ hn.ne', one_smul])]
  rw [RingEquiv.apply_symm_apply]
  change (n : ℚ)⁻¹ • ((n : ℚ) • b) = b
  rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]

/-- **The `ℚ`-algebra automorphism of `B` extending `α ∈ Aut(𝒪)`.** -/
def extAut (α : O ≃+* O) : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extHom α) (extHom α.symm)
    (AlgHom.ext fun b => extHom_symm_comp α b)
    (AlgHom.ext fun b => by simpa using extHom_symm_comp α.symm b)

theorem extAut_coe (α : O ≃+* O) (a : O) : extAut α a = α a := extFun_coe α a


/-! ### `AutModInnFinite` from Skolem–Noether and the Atkin–Lehner finiteness -/

/-- Same statement as `AGIn.AutModInnFinite` (leaf AutO of `AGInputs.lean`). -/
def AutModInnFinite : Prop :=
  ∃ S : Set (O ≃+* O), S.Finite ∧
    ∀ α : O ≃+* O, ∃ s ∈ S, ∃ u : Oˣ, ∀ a, α a = s (u * a * ↑u⁻¹)

/-- **Leaf AL (STANDARD): the Atkin–Lehner group of `𝒪` is finite.** There is a finite set `T`
of units of `B` such that every `b ∈ B^×` normalizing `𝒪` (`b𝒪b⁻¹ = 𝒪`) is `r·t·u` with
`r ∈ ℚ`, `t ∈ T`, `u ∈ 𝒪^×`; i.e. `N_{B^×}(𝒪)/ℚ^×𝒪^×` is finite.
*Published*: for a maximal order in a quaternion algebra over `ℚ` of discriminant `D`,
`N(𝒪)/ℚ^×𝒪^×` is an elementary abelian 2-group of rank at most `#{p ∣ D}`, generated by elements
of reduced norm dividing `D` (Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800
(1980), Ch. II–III; Voight, *Quaternion Algebras*, GTM 288 (2021), Ch. 18 and §28.9; all
UNVERIFIED locators). Finiteness is a consequence. -/
def AtkinLehnerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ b : Bˣ,
    (∀ a : B, a ∈ O ↔ (b : B) * a * ((b⁻¹ : Bˣ) : B) ∈ O) →
      ∃ t ∈ T, ∃ (r : ℚ) (u : Oˣ), (b : B) = r • ((t : B) * ((u : O) : B))

/-- Conjugation by a unit normalizing `𝒪`, as an automorphism of `𝒪`. -/
def conjAut (t : Bˣ) (ht : ∀ a : B, a ∈ O ↔ (t : B) * a * ((t⁻¹ : Bˣ) : B) ∈ O) : O ≃+* O where
  toFun a := ⟨(t : B) * a * ((t⁻¹ : Bˣ) : B), (ht a).1 a.2⟩
  invFun a := ⟨((t⁻¹ : Bˣ) : B) * a * (t : B), (ht _).2 (by
    have : (t : B) * (((t⁻¹ : Bˣ) : B) * (a : B) * (t : B)) * ((t⁻¹ : Bˣ) : B) = a := by
      simp [mul_assoc]
    rw [this]; exact a.2)⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a c := by
    apply Subtype.ext
    simp only [Subring.coe_mul]
    calc (t : B) * (↑a * ↑c) * ((t⁻¹ : Bˣ) : B)
        = (t : B) * ↑a * (((t⁻¹ : Bˣ) : B) * (t : B)) * ↑c * ((t⁻¹ : Bˣ) : B) := by
          simp [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_add' a c := by
    apply Subtype.ext
    simp only [Subring.coe_add]
    noncomm_ring

open Classical in
/-- The finite set of automorphisms: conjugations by the normalizing elements of `T`. -/
def autSet (T : Set Bˣ) : Set (O ≃+* O) :=
  (fun t : Bˣ => if h : ∀ a : B, a ∈ O ↔ (t : B) * a * ((t⁻¹ : Bˣ) : B) ∈ O then conjAut t h
    else RingEquiv.refl O) '' T

/-- **Leaf AutO is glue** from Skolem–Noether (`GlueDescent.LeafSkolemNoether`, **proved** by
t-skolem-kw as `TSkolemKW.leafSkolemNoether`, same statement) and leaf AL. -/
theorem autModInnFinite_of (hSN : GlueDescent.LeafSkolemNoether) (hAL : AtkinLehnerFinite) :
    AutModInnFinite := by
  obtain ⟨T, hT, hAL⟩ := hAL
  refine ⟨autSet T, hT.image _, fun α => ?_⟩
  obtain ⟨b, hb⟩ := GlueDescent.B6_inner hSN (extAut α)
  have hnorm : ∀ a : B, a ∈ O ↔ (b : B) * a * ((b⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    constructor
    · intro ha
      rw [← hb a, show a = ((⟨a, ha⟩ : O) : B) from rfl, extAut_coe]
      exact (α ⟨a, ha⟩).2
    · intro hc
      have h1 : extAut α ((α.symm ⟨_, hc⟩ : O) : B) = extAut α a := by
        rw [extAut_coe, RingEquiv.apply_symm_apply, hb a]
      rw [← (extAut α).injective h1]
      exact (α.symm ⟨_, hc⟩).2
  obtain ⟨t, htT, r, u, hbr⟩ := hAL b hnorm
  have hr : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hbr
    exact b.ne_zero hbr
  have huu : ((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have huu' : (((u⁻¹ : Oˣ) : O) : B) * ((u : O) : B) = 1 := by
    rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
  have hbinv : ((b⁻¹ : Bˣ) : B) = r⁻¹ • ((((u⁻¹ : Oˣ) : O) : B) * ((t⁻¹ : Bˣ) : B)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hbr, smul_mul_smul_comm, mul_inv_cancel₀ hr, one_smul]
    calc (t : B) * ((u : O) : B) * ((((u⁻¹ : Oˣ) : O) : B) * ((t⁻¹ : Bˣ) : B))
        = (t : B) * (((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B)) * ((t⁻¹ : Bˣ) : B) := by
          simp only [mul_assoc]
      _ = 1 := by rw [huu, mul_one, Units.mul_inv]
  have hformula : ∀ a : B, (b : B) * a * ((b⁻¹ : Bˣ) : B) =
      (t : B) * (((u : O) : B) * a * (((u⁻¹ : Oˣ) : O) : B)) * ((t⁻¹ : Bˣ) : B) := by
    intro a
    rw [hbr, hbinv, smul_mul_assoc, smul_mul_smul_comm, mul_inv_cancel₀ hr, one_smul]
    simp only [mul_assoc]
  have ht : ∀ a : B, a ∈ O ↔ (t : B) * a * ((t⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    have e : (t : B) * a * ((t⁻¹ : Bˣ) : B) =
        (b : B) * ((((u⁻¹ : Oˣ) : O) : B) * a * ((u : O) : B)) * ((b⁻¹ : Bˣ) : B) := by
      rw [hformula]
      congr 2
      calc a = (((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B)) * a *
            ((((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B))) := by rw [huu, one_mul, mul_one]
        _ = _ := by simp only [mul_assoc]
    rw [e, ← hnorm]
    constructor
    · intro ha
      exact O.mul_mem (O.mul_mem ((u⁻¹ : Oˣ) : O).2 ha) (u : O).2
    · intro h
      have : a = ((u : O) : B) * ((((u⁻¹ : Oˣ) : O) : B) * a * ((u : O) : B)) *
          (((u⁻¹ : Oˣ) : O) : B) := by
        calc a = (((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B)) * a *
              ((((u : O) : B) * (((u⁻¹ : Oˣ) : O) : B))) := by rw [huu, one_mul, mul_one]
          _ = _ := by simp only [mul_assoc]
      rw [this]
      exact O.mul_mem (O.mul_mem (u : O).2 h) ((u⁻¹ : Oˣ) : O).2
  refine ⟨conjAut t ht, ⟨t, htT, dite_eq_left ht⟩, u, fun a => ?_⟩
  apply Subtype.ext
  rw [← extAut_coe, hb, hformula]
  rfl

end AGInO

#print axioms AGInO.extAut
#print axioms AGInO.autModInnFinite_of
