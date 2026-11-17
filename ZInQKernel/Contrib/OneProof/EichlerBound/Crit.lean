import ZInQKernel.Contrib.OneProof.EichlerBound.Unit

/-! eichler-bound, part B3: the unit criterion `J𝒪 = 𝒪` from the absence of bad primes (class number one of
`𝒪`), and the injectivity step. No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

/-- **`J𝒪 = 𝒪`**, in the form used: an element `u` with `u J ⊆ 𝒪` lies in `𝒪`. -/
def UnitCrit (Ψ Φ : OptEmb k R) : Prop := ∀ u : B, (∀ c ∈ Jo Ψ Φ, u * c ∈ LeafQM.O) → u ∈ LeafQM.O

include Bs in
/-- **The unit criterion from the absence of bad primes.** The left ideal `𝒪 J̄` is principal, `𝒪 α`
(class number one); a prime dividing `nrd α` would be bad, so `α` is a unit. -/
theorem unitCrit_of (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R)
    (h : ∀ p : ℕ, p.Prime → ¬ Bad Ψ Φ p) : UnitCrit Ψ Φ := by
  let S : Set B := {z | ∃ o ∈ LeafQM.O, ∃ c ∈ Jo Ψ Φ, z = o * star c}
  let I := AddSubgroup.closure S
  have hIO : ∀ z ∈ I, z ∈ LeafQM.O := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨o, ho, c, hc, rfl⟩ := hx
      exact LeafQM.O.mul_mem ho (star_mem hc.1)
    | zero => exact LeafQM.O.zero_mem
    | add x y _ _ hx hy => exact LeafQM.O.add_mem hx hy
    | neg x _ hx => exact LeafQM.O.neg_mem hx
  have hIl : ∀ q ∈ LeafQM.O, ∀ x ∈ I, q * x ∈ I := by
    intro q hq x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨o, ho, c, hc, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨q * o, LeafQM.O.mul_mem hq ho, c, hc, by rw [mul_assoc]⟩
    | zero => rw [mul_zero]; exact I.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact I.add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact I.neg_mem hx
  obtain ⟨α, hαI, hαgen⟩ := principal_of_lattice I hIl 1 one_pos (by
    intro x hx; rw [Nat.cast_one, one_smul]; exact hIO x hx)
  have hgen : ∀ c ∈ Jo Ψ Φ, star c ∈ I := fun c hc =>
    AddSubgroup.subset_closure ⟨1, LeafQM.O.one_mem, c, hc, (one_mul _).symm⟩
  obtain ⟨c0, hc0, hne⟩ := exists_Jo Bs hk Ψ Φ
  have hα0 : α ≠ 0 := by
    intro h0
    obtain ⟨q, -, hq⟩ := hαgen _ (hgen c0 hc0)
    rw [h0, mul_zero, star_eq_zero] at hq
    exact hne hq
  obtain ⟨z, hz⟩ := nrd_int (hIO α hαI)
  have hz1 : z.natAbs = 1 := by
    by_contra hz1
    have hp : (z.natAbs.minFac).Prime := Nat.minFac_prime hz1
    have hpd : z.natAbs.minFac ∣ z.natAbs := Nat.minFac_dvd _
    generalize z.natAbs.minFac = p at hp hpd
    apply h _ hp
    intro c hc d hd
    obtain ⟨q, hq, hcq⟩ := hαgen _ (hgen c hc)
    obtain ⟨q', hq', hdq⟩ := hαgen _ (hgen d hd)
    have hd' : d = star α * star q' := by rw [← star_star d, hdq, star_mul]
    rw [hcq, hd']
    have e : q * α * (star α * star q') = q * (α * star α) * star q' := by simp only [mul_assoc]
    rw [e, mul_star_self', hz]
    obtain ⟨w, hw⟩ : ((p : ℕ) : ℤ) ∣ z := Int.natCast_dvd.mpr hpd
    have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [LO_iff_smul _ hp0]
    refine ⟨(w : ℚ) • (q * star q'), smul_mem_O (LeafQM.O.mul_mem hq (star_mem hq')) w, ?_⟩
    rw [← coe_comm, mul_assoc, coe_mul_eq_smul, smul_smul, hw]
    congr 1; push_cast; ring
  intro u hu
  have hstar : ∀ y ∈ I, u * star y ∈ LeafQM.O := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨o, ho, c, hc, rfl⟩ := hx
      rw [star_mul, star_star, ← mul_assoc]
      exact LeafQM.O.mul_mem (hu c hc) (star_mem ho)
    | zero => rw [star_zero, mul_zero]; exact LeafQM.O.zero_mem
    | add x y _ _ hx hy => rw [star_add, mul_add]; exact LeafQM.O.add_mem hx hy
    | neg x _ hx => rw [star_neg, mul_neg]; exact LeafQM.O.neg_mem hx
  have h1 := LeafQM.O.mul_mem (hstar α hαI) (hIO α hαI)
  have hzz : (z : ℚ) * z = 1 := by
    rcases Int.natAbs_eq z with h | h <;> rw [h, hz1] <;> norm_num
  have e : u = (z : ℚ) • (u * star α * α) := by
    rw [mul_assoc, star_mul_self', hz, mul_coe_eq_smul, smul_smul, hzz, one_smul]
  rw [e]
  exact smul_mem_O h1 z

include Bs in
theorem jo_star (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ Jo Ψ Φ) :
    star c ∈ Jo Φ Ψ :=
  ⟨star_mem hc.1, J_star Bs hk hc.2⟩

include Bs in
/-- Swapping the two embeddings exchanges the two sides. -/
theorem bad'_of_bad_swap (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {ℓ : ℤ}
    (h : Bad Φ Ψ ℓ) : Bad' Ψ Φ ℓ := by
  intro c hc d hd
  have := h _ (jo_star Bs hk hc) _ (jo_star Bs hk hd)
  rwa [star_star] at this

include Bs in
theorem bad_of_bad'_swap (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {ℓ : ℤ}
    (h : Bad' Φ Ψ ℓ) : Bad Ψ Φ ℓ := by
  intro c hc d hd
  have := h _ (jo_star Bs hk hc) _ (jo_star Bs hk hd)
  rwa [star_star] at this

include Bs in
/-- **The other side, `𝒪J = 𝒪`**: an element `u` with `J u ⊆ 𝒪` lies in `𝒪`. -/
theorem unitCrit'_of (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R)
    (h : ∀ p : ℕ, p.Prime → ¬ Bad Ψ Φ p) (u : B) (hu : ∀ c ∈ Jo Ψ Φ, c * u ∈ LeafQM.O) :
    u ∈ LeafQM.O := by
  have h' : ∀ p : ℕ, p.Prime → ¬ Bad Φ Ψ p := fun p hp hb =>
    h p hp (bad_of_bad'_swap Bs hk (bad'_of_bad Bs hk (by exact_mod_cast hp.ne_zero) hb))
  have hU := unitCrit_of Bs hk Φ Ψ h'
  have : star u ∈ LeafQM.O := hU _ (fun c' hc' => by
    have := hu _ (jo_star Bs hk hc')
    have := star_mem this
    rwa [star_mul, star_star] at this)
  rw [← star_star u]; exact star_mem this

end Emb

end EichlerBound
