import ZInQKernel.Contrib.OneProof.EichlerBound.Inv

/-! eichler-bound, part B7: invertibility of the lattice of an intertwiner, the injectivity step, and the
comparison with `Pic R` through Mathlib's `Submodule.unitsToPic`. No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

theorem latB_of_latA {Ψ : OptEmb k R} {c : B} (hne : c ≠ 0) {a : k} (ha : a ∈ latA Ψ c) :
    ((nrd c : ℚ) : k) * sk Ψ a ∈ latB Ψ c := by
  have hn0 : nrd c ≠ 0 := nrd_ne_zero hne
  rw [mem_latB, map_mul, emb_ratCast, emb_sk, mul_assoc,
    show star (Ψ.1 a) * qinv c = (nrd c)⁻¹ • star (c * Ψ.1 a) by
      rw [star_mul, qinv, mul_smul_comm]]
  rw [coe_mul_eq_smul, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  exact star_mem ha

include Bs in
/-- **The lattice of an intertwiner is invertible** when no prime is bad. -/
theorem latA_isUnit (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ Jo Ψ Φ)
    (hne : c ≠ 0) (hNB : ∀ p : ℕ, p.Prime → ¬ Bad Ψ Φ p) : IsUnit (latA Ψ c) := by
  have hle := latA_mul_latB_le (Ψ := Ψ) hne
  have hU := unitCrit_of Bs hk Ψ Φ hNB
  have hU' := unitCrit'_of Bs hk Ψ Φ hNB
  have C1 : ∀ u : B, (∀ n ∈ latA Ψ c * latB Ψ c, Ψ.1 n * u ∈ LeafQM.O) → u ∈ LeafQM.O := by
    intro u hu
    apply hU' u
    intro d hd
    obtain ⟨a, rfl⟩ := J_param Bs hc.2 hne hd.2
    have ha : a ∈ latA Ψ c := hd.1
    have hw : star (c * Ψ.1 a * u) ∈ LeafQM.O := hU _ (fun d' hd' => by
      obtain ⟨a', rfl⟩ := J_param Bs hc.2 hne hd'.2
      have ha' : a' ∈ latA Ψ c := hd'.1
      rw [show star (c * Ψ.1 a * u) * (c * Ψ.1 a') = star (star (c * Ψ.1 a') * (c * Ψ.1 a * u)) by
        rw [star_mul (star _), star_star]]
      apply star_mem
      rw [← mul_assoc, star_J_mul]
      have hn := Submodule.mul_mem_mul ha (latB_of_latA hne ha')
      have := hu _ hn
      have e : Ψ.1 (a * (((nrd c : ℚ) : k) * sk Ψ a')) = nrd c • Ψ.1 (sk Ψ a' * a) := by
        rw [mul_comm a, mul_assoc, map_mul, emb_ratCast, coe_mul_eq_smul]
      rw [e] at this; exact this)
    have := star_mem hw; rwa [star_star] at this
  have h1 : (1 : k) ∈ latA Ψ c * latB Ψ c := by
    by_contra h1
    obtain ⟨ℓ, hℓ, hprod⟩ := lemmaD Bs Ψ _ hle (fun x hx => sk_mem_latAB hne hx) h1
    have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hall : ∀ n0 ∈ latA Ψ c * latB Ψ c, ((ℓ : ℚ)⁻¹ • Ψ.1 n0) ∈ LeafQM.O := by
      intro n0 hn0
      apply C1
      intro n hn
      obtain ⟨r, hr, e⟩ := hprod n hn n0 hn0
      rw [mul_smul_comm, ← map_mul, e, map_mul, show ((ℓ : ℕ) : k) = (((ℓ : ℕ) : ℚ) : k) by push_cast; rfl,
        emb_ratCast, coe_mul_eq_smul, smul_smul, inv_mul_cancel₀ hℓq, one_smul]
      exact (optEmb_mem Ψ r).2 hr
    have hq := C1 (((ℓ : ℚ)⁻¹ : ℚ) : B) (fun n hn => by rw [mul_coe_eq_smul]; exact hall n hn)
    obtain ⟨z, hz⟩ := rat_mem_O hq
    have : (ℓ : ℚ) * z = 1 := by rw [← hz, mul_inv_cancel₀ hℓq]
    have : (ℓ : ℤ) * z = 1 := by exact_mod_cast this
    have := Int.eq_one_of_mul_eq_one_right (by positivity) this
    exact hℓ.one_lt.ne' (by exact_mod_cast this)
  exact isUnit_iff_exists_inv.mpr ⟨_, le_antisymm hle (Submodule.one_le.mpr h1)⟩

include Bs in
/-- **Injectivity**: intertwiners with proportional lattices give `𝒪^×`-conjugate embeddings. -/
theorem conj_of_lat (hk : Module.finrank ℚ k = 2) {Ψ Φ Φ' : OptEmb k R} {c c' : B}
    (hc : c ∈ Jo Ψ Φ) (hne : c ≠ 0) (hc' : c' ∈ Jo Ψ Φ') (hne' : c' ≠ 0)
    (hU : UnitCrit Ψ Φ) (hU' : UnitCrit Ψ Φ') (x : k) (hx : x ≠ 0)
    (hlat : ∀ a : k, c' * Ψ.1 (x * a) ∈ LeafQM.O ↔ c * Ψ.1 a ∈ LeafQM.O) : ConjRel R Φ Φ' := by
  set u := c' * Ψ.1 x * qinv c
  set v := c * Ψ.1 x⁻¹ * qinv c'
  have hΨx : Ψ.1 x * Ψ.1 x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  have hΨx' : Ψ.1 x⁻¹ * Ψ.1 x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  have huv : u * v = 1 := by
    simp only [u, v, mul_assoc, qinv_mul_cancel_left hne]
    rw [← mul_assoc (Ψ.1 x), hΨx, one_mul, mul_qinv hne']
  have hvu : v * u = 1 := by
    simp only [u, v, mul_assoc, qinv_mul_cancel_left hne']
    rw [← mul_assoc (Ψ.1 x⁻¹), hΨx', one_mul, mul_qinv hne]
  have hu : u ∈ LeafQM.O := hU u (fun d hd => by
    obtain ⟨a, rfl⟩ := J_param Bs hc.2 hne hd.2
    simp only [u, mul_assoc, qinv_mul_cancel_left hne]
    rw [← map_mul]; exact (hlat a).2 hd.1)
  have hv : v ∈ LeafQM.O := hU' v (fun d hd => by
    obtain ⟨a, rfl⟩ := J_param Bs hc'.2 hne' hd.2
    simp only [v, mul_assoc, qinv_mul_cancel_left hne']
    rw [← map_mul]
    apply (hlat (x⁻¹ * a)).1
    rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]; exact hd.1)
  let w : (↥LeafQM.O)ˣ := ⟨⟨u, hu⟩, ⟨v, hv⟩, Subtype.ext huv, Subtype.ext hvu⟩
  refine ⟨w, fun a => ?_⟩
  show Φ'.1 a = u * Φ.1 a * v
  rw [J_conj hc'.2 hne' a, J_conj hc.2 hne a]
  simp only [u, v, mul_assoc, qinv_mul_cancel_left hne]
  rw [← mul_assoc (Ψ.1 a), ← map_mul, ← mul_assoc (Ψ.1 x), ← map_mul, mul_comm a x⁻¹,
    show x * (x⁻¹ * a) = a by rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]]

instance faithful_subring (R : Subring k) : FaithfulSMul R k :=
  ⟨fun h => Subtype.ext (by simpa using h 1)⟩

/-- Equal classes in `Pic R` of two invertible submodules: `J = x I`. -/
theorem eq_smul_of_pic {I J : (Submodule R k)ˣ} (h : Submodule.unitsToPic R k I = Submodule.unitsToPic R k J) :
    ∃ x : kˣ, ∀ a : k, a ∈ (J : Submodule R k) ↔ ∃ b ∈ (I : Submodule R k), (x : k) * b = a := by
  have h1 : J * I⁻¹ ∈ (Submodule.unitsToPic R k).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h, mul_inv_cancel]
  rw [Submodule.ker_unitsToPic] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, fun a => ?_⟩
  have e : (J : Submodule R k) = Submodule.span R {(x : k)} * (I : Submodule R k) := by
    have h2 : ((Units.map (Submodule.spanSingleton R).toMonoidHom x : (Submodule R k)ˣ) : Submodule R k) =
        Submodule.span R {(x : k)} := rfl
    rw [← h2, hx, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [e, Submodule.mem_span_singleton_mul]

end Emb

end EichlerBound
