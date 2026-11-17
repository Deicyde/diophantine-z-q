import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.HP23Proof.Case1
import ZInQKernel.Contrib.OneProof.HP23Proof.Case3

/-!
# `TYZProp23Printed` proved

Task hp23-proof (report `docs/research/hp23-proof.md`, log `scratch/hp23-proof/log.md`). The top hypothesis
`hP23 : H29Split.TYZProp23Printed` of `ZInQ.OneProof.frozenTarget` (Tian–Yuan–Zhang, arXiv:1411.4728v1,
Proposition 2.3, L580–586, first assertion: `f_n((B̂^×)²) ⊂ 1 + 2ℤ` for squarefree `1 < n ≡ 1, 3 (mod 8)`,
every admissible `τ` and every test vector `f_n`) is a theorem, with no new hypothesis:

* every test vector is `±F` on TYZ's 8 double cosets `B^× twoRep(t) ⟨U_n, ℚ̂^×⟩`, where `F` is hfx-proof's
  explicit generator (`HP23Proof.tv_eq_sign`, from the partition data of `HfxProof.testVector_of_partition`);
* `n ≡ 3 (mod 8)`: `F ∈ {−3, 1}` is odd (`HP23Proof.partition_three`);
* `n ≡ 1 (mod 8)`: `F ∈ {1, −1}` on the classes with `t.2.2 = 0` (`χ₀ = 1`) and `F = 0` on the others
  (`HP23Proof.partition_one8`); a square `h²` lies in a class with `t.2.2 = 0` (`HP23Proof.sq_class`):
  the reduced norm, read at the odd places (even valuations of `nrd γ`) and at `2` (the subgroup
  `2^ℤ(1 + 4ℤ₂)` of `ℚ₂^×`, which contains `nrd(H)` and the squares but no integer `≡ 3 (mod 4)`).
-/

namespace ZInQ.Contrib.HP23Proof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.HfxProof

/-- **TYZ Proposition 2.3, first assertion** (`hP23`): `f_n(h²)` is odd. -/
theorem tyzProp23Printed : ZInQ.Contrib.TYZDecomp.H29Split.TYZProp23Printed := by
  intro n _ hsq _ hcl τ hτ f hf h
  rcases hcl with h1 | h3
  · obtain ⟨v, hv, F, hP, hodd, C, hH, hC⟩ := partition_one8 hsq h1 hτ
    obtain ⟨s, hs, hfs⟩ := tv_eq_sign hv hP hf
    obtain ⟨t, ht⟩ := hP.1 (h * h)
    rw [hfs _ t ht]
    have hF := hodd t (sq_class hv C hH hC h ht)
    rcases hs with rfl | rfl
    · rwa [one_mul]
    · rw [neg_one_mul]; exact hF.neg
  · obtain ⟨v, hv, F, hP, hodd⟩ := partition_three hsq h3 hτ
    obtain ⟨s, hs, hfs⟩ := tv_eq_sign hv hP hf
    obtain ⟨t, ht⟩ := hP.1 (h * h)
    rw [hfs _ t ht]
    rcases hs with rfl | rfl
    · rw [one_mul]; exact hodd t
    · rw [neg_one_mul]; exact (hodd t).neg

end ZInQ.Contrib.HP23Proof
