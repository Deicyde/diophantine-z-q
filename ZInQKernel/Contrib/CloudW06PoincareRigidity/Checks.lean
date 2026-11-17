import ZInQKernel.Contrib.CloudW06PoincareRigidity.T11bRigidity

/-!
Reproducible checks of the owner's expressly permitted verbatim statement copy.
The copy uses the canonical kernel PkgI3. This is not a definitional-equality claim
between the nominally distinct scratch HDec.PkgI3.AbVar and kernel PkgI3.AbVar.
The original scratch file and all kernel definitions remain untouched.
-/

open CategoryTheory AlgebraicGeometry MonObj

namespace ZInQ.Contrib.CloudW06PoincareRigidity

example : T11bExists =
    (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L]
      (A B : _root_.PkgI3.AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X), IsMonHom ψ →
      ∃ φ : A.X ⟶ B.X, IsMonHom φ ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ) := rfl

example : T11bExists := T11bExists_proof
example : ZInQ.LeafPush2.T11b_Rigidity := T11b_Rigidity_proof

#print axioms T11bExists_proof
#print axioms T11bRigidity_unique
#print axioms T11b_Rigidity_proof

end ZInQ.Contrib.CloudW06PoincareRigidity
