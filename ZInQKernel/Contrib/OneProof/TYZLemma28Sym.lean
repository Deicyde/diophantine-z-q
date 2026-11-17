import ZInQKernel.Contrib.OneProof.TYZLemma29Genus
import ZInQKernel.Contrib.OneProof.TYZGenusFold.Class

/-!
# TYZ Lemma 2.8 proved; `hL29` from TYZ Theorem 2.1 alone (task tyz-genus)

Report `docs/research/tyz-genus.md`, log `scratch/tyz-genus/log.md`.

Tian–Yuan–Zhang (TYZ), *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1, Asian J. Math.
21 (2017). The source was not on the host for this task; line numbers are quoted from the project notes.

* `tyzLemma28Sym : H29Genus.TYZLemma28Sym` — TYZ Lemma 2.8 (L1009–1057), the symmetry `P(d₁, d₂) = P(d₂, d₁)` of the
  quadratic periods for squarefree `1 < n ≡ 1 (mod 8)`, `d₂ ≡ 1 (mod 8)`, as stated by h29-proof, with **no
  hypothesis**. For `n ≡ 1 (mod 8)` the test vector `f_n` vanishes on every class `t` with
  `Π_{q ∣ n} χ_q(t) = −1` (`TYZGenusFold.tv_zero_of_gchar`): on such a class `τ̂(t)` lies in a double coset of
  `B^× \ B̂^× / ℚ̂^× U_n` with `χ₀(nrd) = −1` (reduced norms of an explicit idele `aK` in the class, and
  `Π_q χ_q([I]) = χ₄(N I)` by Jacobi reciprocity), where hfx-proof's generator `F` is `0` (`TYZGenusFold.F_zero`).
  Since `χ_{T^c} = χ_T · Π_q χ_q`, the two quadratic periods agree term by term.
* `tyzLemma29PrintedNe3_of_thm21Pairs : TYZThm21Pairs → TYZLemma29PrintedNe3` — with h29-proof's
  `tyzLemma29PrintedNe3_of_genus`, the top hypothesis `hL29` (TYZ Lemma 2.9 as printed, `n ≠ 3`) follows from TYZ
  Theorem 2.1 for every pair (`H29Genus.TYZThm21Pairs`) alone.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet divSet_div)

/-- **TYZ Lemma 2.8** (`TYZLemma28Sym`), proved: `P(d₁, d₂) = P(d₂, d₁)` for `n ≡ 1 (mod 8)`. -/
theorem tyzLemma28Sym : TYZLemma28Sym := by
  intro n _ hsq _ h8 τ hτ f hf d₁ d₂ hd _
  have hd2 : d₂ ∣ n := ⟨d₁, by rw [← hd, mul_comm]⟩
  have hd2pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hd2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hd1 : d₁ = n / d₂ := by rw [← hd, Nat.mul_div_cancel _ hd2pos]
  unfold quadPeriod
  rw [hd1, divSet_div hsq hd2]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hprod : gchar n Finset.univ t = gchar n (divSet n d₂) t * gchar n (divSet n d₂)ᶜ t := by
    unfold gchar; rw [Finset.prod_mul_prod_compl]
  rcases gchar_eq_one_or Finset.univ t with hu | hu
  · congr 1
    rcases gchar_eq_one_or (divSet n d₂) t with h | h <;> rw [h] at hprod ⊢ <;> linarith
  · rw [tv_zero_of_gchar hsq h8 hτ hf t hu, mul_zero, mul_zero]

/-- **`hL29` from TYZ Theorem 2.1 alone.** -/
theorem tyzLemma29PrintedNe3_of_thm21Pairs (h21 : TYZThm21Pairs) : TYZLemma29PrintedNe3 :=
  tyzLemma29PrintedNe3_of_genus h21 tyzLemma28Sym

end ZInQ.Contrib.TYZGenusFold
