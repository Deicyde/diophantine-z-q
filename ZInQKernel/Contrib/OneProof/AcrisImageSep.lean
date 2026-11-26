import ZInQKernel.Contrib.OneProof.AcrisImageBasic

/-! # `W(R)[w^n/n!]` is `p`-adically separated modulo `(ker θ)^m`

For a generator `w` of `ker θ`: if `y ∈ D = W(R)[w^n/n!]` lies in `p^k D + (ker θ)^m` for every
`k`, then `y ∈ (ker θ)^m` (`mem_ith_pow_of_forall`). Multiplying by `m!` moves `D` into `W(R)`
modulo `(ker θ)^m`, where
this is `⋂_k (p^k W(R) + w^m W(R)) = w^m W(R)`. This is the separatedness behind the
well-definedness of the map `A_cris → B_dR^+` (Fontaine, Astérisque 223 (1994), Exposé II,
§§4.1.1–4.1.2, p. 83).
-/

noncomputable section

namespace HDec.PkgI4.AcrisImage

open BergerBst FontaineSt BmaxOne PowerSeries Ideal
open PanBergerSplit (Ainf AinfP theta)
open FontaineComparison (finiteDividedPowers)

variable {p : ℕ} [Fact p.Prime] {w : Ainf p}

/-- `m! γ_n = (m!/n!) w^n` for `n ≤ m`. -/
theorem factorial_mul_gam_of_le (w : Ainf p) {m n : ℕ} (h : n ≤ m) :
    ((m.factorial : ℕ) : AinfP p) * gam w n =
      algebraMap (Ainf p) (AinfP p) (((m.factorial / n.factorial : ℕ) : Ainf p) * w ^ n) := by
  have hd : m.factorial / n.factorial * n.factorial = m.factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial h)
  rw [map_mul, map_pow, map_natCast, ← factorial_mul_gam w n, ← mul_assoc, ← Nat.cast_mul, hd]

/-- Modulo `(ker θ)^m`, `m!` times an element of `D` comes from `W(R)`. -/
theorem exists_factorial_mul_sub_mem (hw : theta p w = 0) {y : AinfP p}
    (hy : y ∈ finiteDividedPowers p w) (m : ℕ) :
    ∃ a : Ainf p, ((m.factorial : ℕ) : AinfP p) * y - algebraMap (Ainf p) (AinfP p) a ∈
      Ith p ^ m := by
  obtain ⟨f, N, hf, rfl⟩ := exists_psum w hy
  have htail : psum w f N - psum w f m ∈ Ith p ^ m := by
    rcases le_total m N with h | h
    · exact psum_sub_psum_mem w hw f h
    · rw [psum_eq_of_le w h hf, sub_self]
      exact Ideal.zero_mem _
  refine ⟨∑ n ∈ Finset.range m, PowerSeries.coeff n f * (((m.factorial / n.factorial : ℕ) : Ainf p) * w ^ n),
    ?_⟩
  have hsum : ((m.factorial : ℕ) : AinfP p) * psum w f m =
      algebraMap (Ainf p) (AinfP p)
        (∑ n ∈ Finset.range m, PowerSeries.coeff n f * (((m.factorial / n.factorial : ℕ) : Ainf p) * w ^ n)) := by
    rw [psum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [map_mul, ← factorial_mul_gam_of_le w (Finset.mem_range.mp hn).le]
    ring
  have h1 : ((m.factorial : ℕ) : AinfP p) * psum w f N -
      algebraMap (Ainf p) (AinfP p)
        (∑ n ∈ Finset.range m, PowerSeries.coeff n f * (((m.factorial / n.factorial : ℕ) : Ainf p) * w ^ n)) =
      ((m.factorial : ℕ) : AinfP p) * (psum w f N - psum w f m) := by
    rw [← hsum]
    ring
  rw [h1]
  exact Ideal.mul_mem_left _ _ htail

/-- **`D` is `p`-adically separated modulo `(ker θ)^m`.** -/
theorem mem_ith_pow_of_forall
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {y : AinfP p}
    (hy : y ∈ finiteDividedPowers p w) (m : ℕ)
    (h : ∀ k, ∃ e ∈ finiteDividedPowers p w, y - (p : AinfP p) ^ k * e ∈ Ith p ^ m) :
    y ∈ Ith p ^ m := by
  have hw : theta p w = 0 := by
    change w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
    rw [hgen]
    exact mem_span_singleton_self w
  obtain ⟨a, ha⟩ := exists_factorial_mul_sub_mem hw hy m
  have hmem : a ∈ span {w ^ m} := by
    refine mem_span_pow_of_forall hgen m fun k => ?_
    obtain ⟨e, he, hek⟩ := h k
    obtain ⟨b, hb⟩ := exists_factorial_mul_sub_mem hw he m
    have h2 : algebraMap (Ainf p) (AinfP p) (a - (p : Ainf p) ^ k * b) ∈ Ith p ^ m := by
      have h3 : algebraMap (Ainf p) (AinfP p) (a - (p : Ainf p) ^ k * b) =
          -(((m.factorial : ℕ) : AinfP p) * y - algebraMap (Ainf p) (AinfP p) a) +
            ((m.factorial : ℕ) : AinfP p) * (y - (p : AinfP p) ^ k * e) +
            (p : AinfP p) ^ k *
              (((m.factorial : ℕ) : AinfP p) * e - algebraMap (Ainf p) (AinfP p) b) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [h3]
      exact Ideal.add_mem _ (Ideal.add_mem _ (neg_mem ha)
        (Ideal.mul_mem_left _ _ hek)) (Ideal.mul_mem_left _ _ hb)
    obtain ⟨c, hc⟩ := mem_span_singleton'.mp (mem_span_pow_of_algebraMap hgen m h2)
    exact ⟨b, c, by linear_combination -hc⟩
  have hia : algebraMap (Ainf p) (AinfP p) a ∈ Ith p ^ m := by
    obtain ⟨c, rfl⟩ := mem_span_singleton'.mp hmem
    rw [ith_pow_eq hgen, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (mem_span_singleton_self _)
  have hmy : ((m.factorial : ℕ) : AinfP p) * y ∈ Ith p ^ m := by
    have := Ideal.add_mem _ ha hia
    rwa [sub_add_cancel] at this
  obtain ⟨u, hu⟩ := isUnit_natCast_factorial (p := p) m
  have hyu : y = ↑u⁻¹ * (((m.factorial : ℕ) : AinfP p) * y) := by
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hyu]
  exact Ideal.mul_mem_left _ _ hmy

end HDec.PkgI4.AcrisImage
