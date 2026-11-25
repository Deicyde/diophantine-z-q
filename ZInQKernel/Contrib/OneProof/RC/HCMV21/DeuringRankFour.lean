import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder

/-! The printed form of Deuring's endomorphism theorem (Voight, *Quaternion
Algebras*, GTM 288, Springer numbering, Theorem 42.1.9, p. 784), the
torsion-to-rank bridge, and the derivation of the older torsion-form
candidate `DeuringSupersingularEndOrder` from the two. Tex 8462–8468. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler PkgI3.AbVar
open scoped CategoryTheory.MonObj

/-- **Printed candidate, UNVERIFIED until the reading desk's two-lens pass.**
Voight, *Quaternion Algebras*, GTM 288 (Springer numbering), Theorem 42.1.9,
p. 784: "Let E be an elliptic curve over F and suppose that rk_Z End(E) = 4.
Then B = End(E)_Q is a quaternion algebra over Q ramified at p = char F and ∞,
and End(E) is a maximal order in B." Here `F` is any field (§42.1).

Representation. The field `F` is `k : Type` with `[Field k]` and
`[CharP k q]` for a prime `q` (the rank hypothesis forces positive
characteristic, so `q` is the printed `p`). The elliptic curve is a
one-dimensional `A : PkgI3.AbVar k`. The rank hypothesis is stated as printed,
`Module.finrank ℤ A.End = 4`. No algebraic closedness is assumed.

Conclusion shape. As in `DeuringSupersingularEndOrder`: a rational presentation
`(a, b)_ℚ` ramified exactly at `q` and `∞` (`AppF.RamifiedExactlyAtEll0Infty`),
an order `R` with `A.End ≃+* R.ring`, and maximality of `R`. "Ramified at
p = char F and ∞" is read as `Ram(B) = {p, ∞}`: the proof on p. 785 obtains
`Ram(B) = {p, ∞}` from Main Theorem 14.1.3, and Voight cites the theorem
in this form in §42.2, p. 787 ("By Theorem 42.1.9, we have Ram(B) = {p, ∞}").

The printed proof does not use the inseparable sentence of 42.2.4. At `p` it
uses an uncited Frobenius factorization (Silverman II.2.12) and that `[p]` is
purely inseparable (Silverman V.3.1). It remains a permitted leaf. -/
def VoightThm4219 : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (A : PkgI3.AbVar k), A.dim = 1 → Module.finrank ℤ A.End = 4 →
    ∃ a b : ℚ, AppF.RamifiedExactlyAtEll0Infty q a b ∧
      ∃ R : Eichler.Order a b, Nonempty (A.End ≃+* R.ring) ∧
        ∀ S : Eichler.Order a b, R.ring ≤ S.ring → S.ring ≤ R.ring

/-- **GLUE.** Over an algebraically closed field of characteristic `q`, a
one-dimensional abelian variety with no nonidentity geometric `q`-torsion
has endomorphism ring of `ℤ`-rank four. Voight, Prop. 42.1.7, lists
`E[p](F^al) = {0}` (item (ii)) among equivalent conditions for supersingularity
and proves the equivalences only by citing Silverman V.3.1. This bridge
is not part of any print, and it is not proved in the tree. -/
def SupersingularTorsionRankFour : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
    (A : PkgI3.AbVar k), A.dim = 1 → (∀ P : A.Pt k, P ^ q = 1 → P = 1) →
    Module.finrank ℤ A.End = 4

/-- The printed Theorem 42.1.9 candidate together with the torsion-to-rank
bridge gives the older torsion-form candidate. Every existing hypothesis
of type `DeuringSupersingularEndOrder` is reached from these two. -/
theorem deuringSupersingularEndOrder_of_rankFour (hT : VoightThm4219)
    (hB : SupersingularTorsionRankFour) : DeuringSupersingularEndOrder := by
  intro q _ k _ _ _ A hdim hss
  exact hT q k A hdim (hB q k A hdim hss)

variable {a b : ℚ} {k : Type} [Field k] {A : PkgI3.AbVar k}

/-- The rank-four variant of `exists_referenceEndOrder`. The printed
Theorem 42.1.9 candidate and the uniqueness of the algebra put the
endomorphism ring of a rank-four curve as a maximal order in any fixed
presentation ramified exactly at `q` and `∞`. No algebraic closedness and
no torsion bridge is used. -/
theorem exists_referenceEndOrder_of_rankFour
    (hT : VoightThm4219) (hV : QuaternionRamificationUniqueness)
    (q : ℕ) [Fact q.Prime] [CharP k q]
    (hram : AppF.RamifiedExactlyAtEll0Infty q a b)
    (hdim : A.dim = 1) (hrk : Module.finrank ℤ A.End = 4) :
    ∃ S : Order a b, Nonempty (A.End ≃+* S.ring) ∧
      ∀ T : Order a b, S.ring ≤ T.ring → T.ring ≤ S.ring := by
  obtain ⟨c, d, hcd, U, ⟨j⟩, hmax⟩ := hT q k A hdim hrk
  obtain ⟨e⟩ := hV q c d a b hcd hram
  let S := transportOrder U e
  let i : U.ring ≃+* S.ring := e.toRingEquiv.subringMap (s := U.ring)
  refine ⟨S, ⟨j.trans i⟩, ?_⟩
  intro T hST x hx
  let V := transportOrder T e.symm
  have hUV : U.ring ≤ V.ring := fun y hy =>
    ⟨e y, hST ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  have hh : e.symm x ∈ U.ring := hmax V hUV ⟨x, hx, rfl⟩
  exact ⟨e.symm x, hh, e.apply_symm_apply x⟩

end ZInQ.Manuscript.RC.HCMV21
