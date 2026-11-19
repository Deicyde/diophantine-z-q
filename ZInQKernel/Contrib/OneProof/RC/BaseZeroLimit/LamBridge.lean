import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Assembly
import ZInQKernel.Contrib.CloudB3RC53.BaseZeroLam.Lam

/-!
# Lane RC30 (base zero), optional part 6: the inner limit and the central comparison in the RC53
group's base-zero constructors

The RC53 group's file `CloudB3RC53/BaseZeroLam/Lam.lean` builds lane RC25's `BaseZeroCore` from a
closed paired functional (`BaseZeroCore.ofClosed`) or from the paired functional `PD(·, ψ(c z))`
itself (`BaseZeroCore.ofPaired`), with `hu` derived from one coordinate statement (Proposition
`ex:arith-paired-functional`, tex 3704–3880, and Definition `ex:arith-coordinate`, tex 3877–3892).
Those constructors still take `hcentral` (tex 4350–4352) and `boundary` ((4.5) at the base,
tex 3912–3921, 3952–3968) as arguments. This file feeds them lane RC30's two bridges:

* `hcentral := hcentral_of_selmer hSel C` (from `SelmerCorankOneOverK ℓ D.kfin` and the central
  comparison `CentralSelmerComparison`, file `Central.lean`);
* `boundary := B.toBoundary45Base` (from the retained inner-limit data `InnerLimit45Base`, file
  `Boundary.lean`).

Every declaration is `PROVED` (a composition). This file needs the RC53 group's
`BaseZeroLam/Lam.lean`, which is present at the integration head that contains it, but not at the
lane's base revision.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
  ZInQ.Manuscript.RC.BaseZeroAssembly
open CategoryTheory Matrix

/-- **The base-zero core from a closed functional, with lane RC30's inputs** (tex 3877–3892,
4330–4376): the RC53 group's `BaseZeroCore.ofClosed` with `hcentral` from `hcentral_of_selmer` and
`boundary` from `InnerLimit45Base.toBoundary45Base`. PROVED. -/
def coreOfClosed {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G] (P : G) (m : ℕ)
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT) (hSel : SelmerCorankOneOverK ℓ D.kfin)
    (Ccmp : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ D.kfin)) Dm)
    (z : Fin (m + 1) → Rings.LambdaT) (hz : Dm *ᵥ z = 0)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y) (lam : CU.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT)
    (hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0) (uprim : FractionRing Uniform.Lambda)
    (hu : Central.IsClassFunctionalCoord
      (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (z i))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (BaseZeroLam.rowOf lam e2 i))
      uprim)
    (B : InnerLimit45Base P (m + 1) (fun i => Rings.rhoT (z i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) : BaseZeroCore D Fam P :=
  BaseZeroLam.BaseZeroCore.ofClosed D Fam P m Dm (hcentral_of_selmer hSel Ccmp) z hz CU e1 e2 hd
    lam hlam uprim hu B.toBoundary45Base hprimId

/-- **The base-zero core with `lam := PD(·, ψ(c z))`, with lane RC30's inputs** (tex 3742–3749,
3845–3849, 3860–3863, 4330–4376): the RC53 group's `BaseZeroCore.ofPaired` with the two bridges.
PROVED. -/
def coreOfPaired {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G] (P : G) (m : ℕ)
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT) (hSel : SelmerCorankOneOverK ℓ D.kfin)
    (Ccmp : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ D.kfin)) Dm)
    (zm : Fin (m + 1) → Rings.LambdaT) (hzm : Dm *ᵥ zm = 0)
    (CU C' C : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (pd1 : CU.X 1 →ₗ[Rings.LambdaT] C'.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT)
    (pd2 : CU.X 2 →ₗ[Rings.LambdaT] C'.X 1 →ₗ[Rings.LambdaT] Rings.LambdaT) (ε : Rings.LambdaT)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (ψ : C ⟶ C') (cz : C.X 1) (hcz : (C.d 1 2).hom cz = 0) (uprim : FractionRing Uniform.Lambda)
    (hu : Central.IsClassFunctionalCoord
      (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (zm i))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)
        (BaseZeroLam.rowOf (BaseZeroLam.baseLam pd2 ψ cz) e2 i)) uprim)
    (B : InnerLimit45Base P (m + 1) (fun i => Rings.rhoT (zm i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) : BaseZeroCore D Fam P :=
  BaseZeroLam.BaseZeroCore.ofPaired D Fam P m Dm (hcentral_of_selmer hSel Ccmp) zm hzm CU C' C
    e1 e2 hd pd1 pd2 ε hL1 ψ cz hcz uprim hu B.toBoundary45Base hprimId

/-- The core of `coreOfPaired` has the paired functional as its field `lam` and keeps the model's
central cycle. PROVED. -/
theorem coreOfPaired_lam {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) {G : Type} [AddCommGroup G]
    (P : G) (m : ℕ) (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (hSel : SelmerCorankOneOverK ℓ D.kfin)
    (Ccmp : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ D.kfin)) Dm)
    (zm : Fin (m + 1) → Rings.LambdaT) (hzm : Dm *ᵥ zm = 0)
    (CU C' C : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y)
    (pd1 : CU.X 1 →ₗ[Rings.LambdaT] C'.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT)
    (pd2 : CU.X 2 →ₗ[Rings.LambdaT] C'.X 1 →ₗ[Rings.LambdaT] Rings.LambdaT) (ε : Rings.LambdaT)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (ψ : C ⟶ C') (cz : C.X 1) (hcz : (C.d 1 2).hom cz = 0) (uprim : FractionRing Uniform.Lambda)
    (hu : Central.IsClassFunctionalCoord
      (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (zm i))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)
        (BaseZeroLam.rowOf (BaseZeroLam.baseLam pd2 ψ cz) e2 i)) uprim)
    (B : InnerLimit45Base P (m + 1) (fun i => Rings.rhoT (zm i)))
    (hprimId : Wiring.IsTExpansion uprim (D.uPrim Fam 0)) :
    (coreOfPaired D Fam P m Dm hSel Ccmp zm hzm CU C' C e1 e2 hd pd1 pd2 ε hL1 ψ cz hcz uprim hu
      B hprimId).lam = BaseZeroLam.baseLam pd2 ψ cz ∧
    (coreOfPaired D Fam P m Dm hSel Ccmp zm hzm CU C' C e1 e2 hd pd1 pd2 ε hL1 ψ cz hcz uprim hu
      B hprimId).z = zm :=
  ⟨rfl, rfl⟩

end ZInQ.Manuscript.RC.BaseZeroLimit
