import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.HfxProof.Case1

/-!
# `TYZTestVectorExists` proved

Task hfx-proof (report `docs/research/hfx-proof.md`, log `scratch/hfx-proof/log.md`). The top hypothesis
`hfx : H29Split.TYZTestVectorExists` of `ZInQ.OneProof.frozenTarget` (Tian–Yuan–Zhang, arXiv:1411.4728v1,
L542–550: `π_ℤ^{U_n}` has a generator `f_n`, and `f_n ≠ 0`, for squarefree `1 < n ≡ 1, 3 (mod 8)` and every
admissible embedding `τ`) is a theorem, with no new hypothesis:

* every unit of `B̂ = ℍ[𝔸ᶠ_ℚ]` lies in one of TYZ's 8 double cosets `B^× twoRep(t) ⟨U_n, ℚ̂^×⟩`
  (`HfxProof.exists_twoRep`: `B̂^× = B^× Ô_B^×` from the Euclidean property of the Hurwitz order, and
  TYZ Lemma 2.5's representatives, checked mod 4 by `decide`);
* the right action of `K_{n,2}^×` merges the 8 classes into two orbits (sizes 2, 6) for `n ≡ 3 (mod 8)` and
  three (sizes 2, 2, 4) for `n ≡ 1 (mod 8)`: explicit elements of `K^×` give the merges, a 2-adic
  obstruction (through the global step `γ = q·n`, `nrd n = 2^k`) separates the orbits; both are finite checks
  over the residues of `τ(√−n)` (`decide`, tables `tab3`, `tab1`);
* the function `F t` on the double coset of `twoRep t` (`−3, 1` resp. `1, −1, 0`) lies in `π_ℤ^{U_n}` and
  spans it (`HfxProof.testVector_of_partition`).
-/

namespace ZInQ.Contrib.HfxProof

/-- **TYZ's test vector exists and is nonzero** (`hfx`). -/
theorem tyzTestVectorExists : ZInQ.Contrib.TYZDecomp.H29Split.TYZTestVectorExists := by
  intro n _ hsq _ hcl τ hτ
  rcases hcl with h | h
  · exact testVector_one8 hsq h hτ
  · exact testVector_three hsq h hτ

end ZInQ.Contrib.HfxProof
