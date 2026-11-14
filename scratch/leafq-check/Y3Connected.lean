import TailK

/-!
# leafq-check: `Y3Connected` (LEAF?) — verbatim copy over leaf-fold4's chain

The Prop `HDec.TSHecke.Y3Connected` is copied verbatim (docstring and body) from `scratch/leaf-fold4/Leaves4.lean`
(def at line 97479), inside the sub-namespace `HDec.TSHecke.LeafQCheckCopy` with the `open`s in force at its
location; what it depends on is imported from leaf-fold4's olean chain (`import TailK`, the same
constants as the flat file). `copy_iff` checks that the copy is the chain's Prop. Verdict, published
statement and decomposition: docs/research/leafq-check.md §2.7. Check: `scratch/leafq-check/chk.sh scratch/leafq-check/Y3Connected.lean`.
-/

namespace HDec.TSHecke

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue PkgI3
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace LeafQCheckCopy

/-- **Leaf R1conn (the canonical model `Y₃ = Sh_{K₃}` is connected over `ℚ`), witness form.**
Some triple satisfying the clause list R1fp has a connected underlying space.

*Published statement* (Shimura; Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3,
and *Variétés de Shimura*, Proc. Symp. Pure Math. 33 (1979), §2.1 and Thm 2.6.3; Milne,
*Introduction to Shimura varieties* (2005), §5 and §13; all locators UNVERIFIED): for `G = B^×`
the set of geometric components of `Sh_K` is `ℚ_{>0}^× \ 𝔸_f^× / nrd(K)`, and `Gal(ℚ̄/ℚ)` acts on
it through the cyclotomic character (Artin reciprocity), i.e. through multiplication by `ℤ̂^×`.
*Consequence used*: for `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`, `nrd(K₃) = ∏_{ℓ≠3} ℤ_ℓ^× × (1 + 3ℤ_3)`, so the
set of components is `(ℤ/3)^×` (two points) and `ℤ̂^×` acts transitively on it: `Y₃` is
`ℚ`-connected (its two geometric components are swapped by `Gal(ℚ(√−3)/ℚ)`, in particular by
complex conjugation).
*Computation* (VERIFIED, `scratch/ts-hecke/pi0_check.py`): in Shimura's uniformization
`Y₃(ℂ) = 𝒪^× \ (ℍ^± × (𝒪/3𝒪)^×)` there are exactly two orbits, separated by `s · nrd(a) mod 3`,
and complex conjugation `(s, a) ↦ (−s, a)` swaps them. -/
def Y3Connected : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left

end LeafQCheckCopy

theorem LeafQCheckCopy.copy_iff : LeafQCheckCopy.Y3Connected ↔ Y3Connected := Iff.rfl

end HDec.TSHecke
