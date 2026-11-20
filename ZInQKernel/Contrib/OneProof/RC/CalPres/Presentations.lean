import ZInQKernel.Contrib.OneProof.RC.CalPres.SplitModel
import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.LocalOrders

/-! The presentation fields for the central local quotient, conditional on the finite full
local comparison and its degree-one Kummer compatibility. -/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open CategoryTheory NumberField IsDedekindDomain Matrix
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}

/-- The actual finite full local complex for the central character. -/
abbrev centralLocalComplex (W : WeierstrassCurve K) (i : ℕ) (v : Places K S)
    (s : KS K S) (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) : GCx (Acoef i) :=
  locAt K S (Acoef i) (Mcoef K S W i (centralChar i s hs hs0)) v

/-- The actual Kummer submodule of the degree-one cohomology of the central complex. -/
abbrev centralKummerImage (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (v : Places K S)
    (s : KS K S) (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (hFull : FullTorsion K S W (2 ^ i)) :=
  kummerImageH1 W i (centralChar i s hs hs0) v s hs hs0 hFull
    (isLocallyQuadAt_centralChar i s hs hs0 v.1)

/-- The linear map induced by an integral matrix at precision `i`. -/
abbrev reduceLocalBlock (i : ℕ) (B : Matrix (Fin 2) (Fin 2) ℤ_[2]) :=
  (B.map (constRed i)).mulVecLin

/-- Given a comparison on the full complex, this map reads its first degree-one coordinate
on the actual Kummer submodule. -/
def kummerFirstCoordinate {W : WeierstrassCurve K} [W.IsElliptic] {i : ℕ} {v : Places K S}
    (hFull : FullTorsion K S W (2 ^ i))
    {F D : (Fin 2 → Acoef i) →ₗ[Acoef i] (Fin 2 → Acoef i)}
    (c : (centralLocalComplex W i v s hs hs0).toCC ⟶ (splitLocalModel F D).toCC) :
    centralKummerImage W i v s hs hs0 hFull →ₗ[Acoef i]
      ((Fin 2 → Acoef i) ⧸ LinearMap.range F) :=
  ((LinearMap.fst _ _ _).comp (splitLocalH1 F D).toLinearMap).comp
    ((HomologicalComplex.homologyMap c 1).hom.comp
      (centralKummerImage W i v s hs hs0 hFull).subtype)

/-- A full comparison in degrees one and two yields the presentation if its first
coordinate identifies the Kummer subgroup with the ordinary coordinate. -/
def presentationOfSplit {W : WeierstrassCurve K} [W.IsElliptic] {i : ℕ} {v : Places K S}
    (hFull : FullTorsion K S W (2 ^ i))
    (F : (Fin 2 → Acoef i) →ₗ[Acoef i] (Fin 2 → Acoef i))
    (B : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (c : (centralLocalComplex W i v s hs hs0).toCC ⟶ (splitLocalModel F (reduceLocalBlock i B)).toCC)
    (hc1 : QuasiIsoAt c 1) (hc2 : QuasiIsoAt c 2)
    (hk : Function.Bijective (kummerFirstCoordinate hFull c)) :
    PresentsLocalQuotient W i (centralChar i s hs hs0) v s hs hs0 hFull
      (isLocallyQuadAt_centralChar i s hs hs0 v.1) B := by
  letI : QuasiIsoAt c 1 := hc1
  letI : QuasiIsoAt c 2 := hc2
  let P := centralKummerImage W i v s hs hs0 hFull
  let D := reduceLocalBlock i B
  let e := (asIso (HomologicalComplex.homologyMap c 1)).toLinearEquiv.trans (splitLocalH1 F D)
  let Q := P.map e.toLinearMap
  have hproj : Function.Bijective ((LinearMap.fst (Acoef i) _ _).comp Q.subtype) := by
    let he := e.submoduleMap P
    have heq : kummerFirstCoordinate hFull c =
        ((LinearMap.fst (Acoef i) _ _).comp Q.subtype).comp he.toLinearMap := by
      ext x
      change ((splitLocalH1 F D) ((HomologicalComplex.homologyMap c 1).hom x.val)).1 =
        ((e.submoduleMap P x).val).1
      rw [LinearEquiv.submoduleMap_apply]
      rfl
    rw [heq] at hk
    exact (he.toEquiv.bijective_comp _).1 hk
  let eq := Submodule.Quotient.equiv P Q e rfl
  exact ⟨(eq.trans (quotientOfFirstCoordinate Q hproj)).symm,
    (splitLocalH2 F D).symm.trans (asIso (HomologicalComplex.homologyMap c 2)).toLinearEquiv.symm⟩

/-- At a moving place the singular differential is the signed Tate Frobenius minus
the residue norm. The same definition applies to the other split place. -/
def movingBlock {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ) :
    Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  (χ : ℤ_[2]) • localTateMatrix E v H.frob - (r : ℤ_[2]) • 1

/-- The ordinary differential at a moving place is signed Tate Frobenius minus one. -/
def movingOrdinary {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ) :
    Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  (χ : ℤ_[2]) • localTateMatrix E v H.frob - 1

/-- The active integral differential in each of the two disks is twice the identity. -/
def activeBlock : Matrix (Fin 2) (Fin 2) ℤ_[2] := (2 : ℤ_[2]) • 1

/-- The specialization of the split comparison to either moving presentation field. -/
def movingPresentation {E : WeierstrassCurve ℚ} [E.IsElliptic] {v : Places K S}
    {r : ℕ} {a χ : ℤ} (H : MovingLocalAction E s hs hs0 v r a χ)
    (i : ℕ) (hFull : FullTorsion K S (E.baseChange K) (2 ^ i))
    (c : (centralLocalComplex (E.baseChange K) i v s hs hs0).toCC ⟶
      (splitLocalModel (reduceLocalBlock i (movingOrdinary H)) (reduceLocalBlock i (movingBlock H))).toCC)
    (hc1 : QuasiIsoAt c 1) (hc2 : QuasiIsoAt c 2)
    (hk : Function.Bijective (kummerFirstCoordinate hFull c)) :
    PresentsLocalQuotient (E.baseChange K) i (centralChar i s hs hs0) v s hs hs0 hFull
      (isLocallyQuadAt_centralChar i s hs hs0 v.1) (movingBlock H) :=
  presentationOfSplit hFull _ _ c hc1 hc2 hk

/-- The specialization of the split comparison to the active presentation field. -/
def activePresentation {W : WeierstrassCurve K} [W.IsElliptic] {v : Places K S}
    (i : ℕ) (hFull : FullTorsion K S W (2 ^ i))
    (c : (centralLocalComplex W i v s hs hs0).toCC ⟶
      (splitLocalModel (reduceLocalBlock i activeBlock) (reduceLocalBlock i activeBlock)).toCC)
    (hc1 : QuasiIsoAt c 1) (hc2 : QuasiIsoAt c 2)
    (hk : Function.Bijective (kummerFirstCoordinate hFull c)) :
    PresentsLocalQuotient W i (centralChar i s hs hs0) v s hs hs0 hFull
      (isLocallyQuadAt_centralChar i s hs hs0 v.1) activeBlock :=
  presentationOfSplit hFull _ _ c hc1 hc2 hk

/-- Precision zero has the zero coefficient ring, so every integral block presents the two
zero quotient groups at that precision. -/
def presentationAtZero {W : WeierstrassCurve K} [W.IsElliptic] (v : Places K S)
    (hFull : FullTorsion K S W (2 ^ 0)) (B : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    PresentsLocalQuotient W 0 (centralChar 0 s hs hs0) v s hs hs0 hFull
      (isLocallyQuadAt_centralChar 0 s hs hs0 v.1) B := by
  haveI : Subsingleton (Acoef 0) := (subsingleton_iff_zero_eq_one).1 (by
    simpa using (acoef_two_pow_eq_zero 0).symm)
  have trivialEquiv (X Y : Type) [AddCommMonoid X] [AddCommMonoid Y]
      [Module (Acoef 0) X] [Module (Acoef 0) Y] : X ≃ₗ[Acoef 0] Y := by
    haveI := Module.subsingleton (Acoef 0) X
    haveI := Module.subsingleton (Acoef 0) Y
    exact LinearEquiv.ofBijective 0 ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  exact ⟨trivialEquiv _ _, trivialEquiv _ _⟩


end ZInQ.Contrib.RC53Assist.Calibration
