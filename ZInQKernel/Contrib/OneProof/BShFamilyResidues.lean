import ZInQKernel.Contrib.OneProof.BShFamilyTorsion

/-! ON THE SPOT (provenance (c)): changing the generator of an analytic
prime kernel permutes its nonzero residues. -/

noncomputable section

namespace BShFamily

open UpperHalfPlane PeriodPair T5Glue

/-- The residue one in the finite type of nonzero multiples. -/
def oneMultiple {p : ℕ} (hp : p.Prime) : Multiple p :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  ⟨⟨1, hp.one_lt⟩, Nat.one_ne_zero⟩

theorem oneMultiple_val {p : ℕ} (hp : p.Prime) : (oneMultiple hp).val.val = 1 := rfl

/-- The nonzero residue represented by the index, as a unit modulo the prime. -/
def multipleUnit {p : ℕ} (hp : p.Prime) (k : Multiple p) : (ZMod p)ˣ :=
  letI : Fact p.Prime := ⟨hp⟩
  Units.mk0 (k.val.val : ZMod p) (fun h => k.property (by
    rw [← ZMod.val_natCast_of_lt k.val.isLt, h, ZMod.val_zero]))

@[simp] theorem multipleUnit_coe {p : ℕ} (hp : p.Prime) (k : Multiple p) :
    (multipleUnit hp k : ZMod p) = k.val.val := rfl

/-- Identify the distinct nonzero representatives modulo the prime with its
units. This does not identify two opposite residues. -/
def multiplesEquivUnits {p : ℕ} (hp : p.Prime) : Multiple p ≃ (ZMod p)ˣ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine Equiv.ofBijective (multipleUnit hp) ⟨?_, ?_⟩
  · intro k l he
    apply Subtype.ext
    apply Fin.ext
    have hh := congrArg (fun a : (ZMod p)ˣ => (a : ZMod p).val) he
    simpa only [multipleUnit_coe, ZMod.val_natCast_of_lt k.val.isLt,
      ZMod.val_natCast_of_lt l.val.isLt] using hh
  · intro u
    let k : Fin p := ⟨(u : ZMod p).val, ZMod.val_lt _⟩
    have hk : k.val ≠ 0 := by
      intro h
      apply Units.ne_zero u
      rw [← ZMod.natCast_zmod_val (u : ZMod p), show (u : ZMod p).val = 0 from h, Nat.cast_zero]
    refine ⟨⟨k,hk⟩, Units.ext ?_⟩
    exact ZMod.natCast_zmod_val _

/-- Multiplying by a fixed nonzero residue permutes the nonzero residues. -/
def multiplePerm {p : ℕ} (hp : p.Prime) (k : Multiple p) : Equiv.Perm (Multiple p) :=
  let E := multiplesEquivUnits hp
  (E.trans (Equiv.mulLeft (E k))).trans E.symm

theorem multiplePerm_cast {p : ℕ} (hp : p.Prime) (k l : Multiple p) :
    ((multiplePerm hp k l).val.val : ZMod p) = (k.val.val : ZMod p) * (l.val.val : ZMod p) := by
  let E := multiplesEquivUnits hp
  have he : E (multiplePerm hp k l) = E k * E l := E.apply_symm_apply _
  exact congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) he

/-- The product of two nonzero residue representatives differs from the
permuted representative by a multiple of the original period. -/
theorem multiply_period {p : ℕ} (hp : p.Prime) (k l : Multiple p) (i : Line p) (τ : ℍ) :
    (l.val.val : ℂ) * ((k.val.val : ℂ) * generator p i τ) -
      ((multiplePerm hp k l).val.val : ℂ) * generator p i τ ∈ (pp τ).lattice := by
  have h : (((k.val.val : ℤ) * (l.val.val : ℤ) - (multiplePerm hp k l).val.val : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [multiplePerm_cast hp, sub_self]
  obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hn' : (k.val.val : ℂ) * (l.val.val : ℂ) - (multiplePerm hp k l).val.val =
      (p : ℂ) * (n : ℂ) := by exact_mod_cast hn
  have hg : (p : ℂ) * generator p i τ ∈ (pp τ).lattice := by
    simpa only [oneMultiple_val, Nat.cast_one, one_mul] using
      multiple_killed hp.pos i τ (oneMultiple hp).val
  convert (pp τ).lattice.smul_mem n hg using 1
  rw [zsmul_eq_mul, show (n : ℂ) * ((p : ℂ) * generator p i τ) =
    ((p : ℂ) * (n : ℂ)) * generator p i τ by ring, ← hn']
  ring

open WeierstrassCurve X1Igusa.Weber in
/-- Multiplication at a prime torsion section agrees with the section of the
permuted nonzero residue, expressed by the division ratios. -/
theorem mulX_of_multiple {p : ℕ} (hp : p.Prime) (i : Line p) (k l : Multiple p) (τ : ℍ)
    (h₂ : (pp τ).g₂ ≠ 0) (h₃ : (pp τ).g₃ ≠ 0) :
    mulX (curveG ((pp τ).g₂ ^ 3 / (pp τ).g₃ ^ 2)) l.val.val
      (normX τ ((k.val.val : ℂ) * generator p i τ)) =
      normX τ (((multiplePerm hp k l).val.val : ℂ) * generator p i τ) := by
  let a := (k.val.val : ℂ) * generator p i τ
  let b := ((multiplePerm hp k l).val.val : ℂ) * generator p i τ
  have hp' : (l.val.val : ℂ) * a - b ∈ (pp τ).lattice := multiply_period hp k l i τ
  have hh : (l.val.val : ℂ) * a ∉ (pp τ).lattice := by
    intro e
    apply multiple_notMem hp.pos i τ (multiplePerm hp k l)
    change b ∈ (pp τ).lattice
    simpa only [sub_sub_cancel] using (pp τ).lattice.sub_mem e hp'
  have he := (mulX_pointwise τ h₂ h₃ (l.val.val : ℤ)
    (multiple_notMem hp.pos i τ k) (by simpa only [Int.cast_natCast] using hh)).2
  rw [he, Int.cast_natCast]
  have he' := normX_period τ b ⟨_, hp'⟩
  change normX τ (b + ((l.val.val : ℂ) * a - b)) = normX τ b at he'
  rwa [add_sub_cancel] at he'

#print axioms oneMultiple_val
#print axioms multipleUnit_coe
#print axioms multiplePerm_cast
#print axioms multiply_period
#print axioms mulX_of_multiple

end BShFamily
