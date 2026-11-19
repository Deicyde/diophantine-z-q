import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG

/-!
# Retention on the actual continuous-cochain Selmer complexes

The class-functional coordinate uses the actual class and the same paired
functional in a retained determinant basis.  The places are indexed by the
disjoint union of the old and the selected places.  At selected places the
primitive condition maps to the full continuous-cochain condition and the
paired strict condition is zero.  Every old condition and isotropy homotopy
is unchanged.  The retained-homotopy equality is a consequence of these maps,
not an independent assumption.

The locators are Definition ex:arith-coordinate, TeX 3877–3892, and the proof
of ex:arith-common-coordinate, TeX 4159–4177, citing Nekovář, Sections
6.4.1–6.4.3.  No termwise identification with a tame model and no additional
printed proposition is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom ghomComp restrictData changeMap)
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (RetainedPairing pairedFun)

universe u

section Conditions

variable {R : Type u} [CommRing R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Vo Vn : Type u} {Gv : Vo ⊕ Vn → Type u}
  [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* G}
  {A : Type u} [AddCommGroup A] [Module R A]
  [DistribMulAction G A] [SMulCommClass G R A]
  [TopologicalSpace A] [ContinuousAdd A]
  [ContinuousConstSMul R A] [ContinuousSMul G A]

/-- Retain old conditions and use the actual full local cochains at selected places. -/
def fullAt (Δ : LocalConditions R G Gv loc A) : LocalConditions R G Gv loc A where
  U
    | .inl v => Δ.U (.inl v)
    | .inr q => localCx R G Gv loc A (.inr q)
  i
    | .inl v => Δ.i (.inl v)
    | .inr _ => idGHom _

/-- Retain old paired conditions and use zero at selected places. -/
def zeroAt (Δ : LocalConditions R G Gv loc A) : LocalConditions R G Gv loc A where
  U
    | .inl v => Δ.U (.inl v)
    | .inr _ => ZInQ.Manuscript.RC.SelmerComplex.zeroCx R
  i
    | .inl v => Δ.i (.inl v)
    | .inr _ => ZInQ.Contrib.CloudB3RC53.SelmerDuality.zeroGHom _ _

/-- The primitive-to-full condition map is the identity at every old place. -/
def toFullAt (Δ : LocalConditions R G Gv loc A) :
    ∀ v, GHom (Δ.U v) ((fullAt Δ).U v)
  | .inl _ => idGHom _
  | .inr q => Δ.i (.inr q)

/-- The paired strict-to-primitive map is zero at every selected place. -/
def fromZeroAt (Δ : LocalConditions R G Gv loc A) :
    ∀ v, GHom ((zeroAt Δ).U v) (Δ.U v)
  | .inl _ => idGHom _
  | .inr _ => ZInQ.Contrib.CloudB3RC53.SelmerDuality.zeroGHom _ _

omit [IsTopologicalGroup G] in
/-- The primitive-to-full map commutes with the actual local inclusions. -/
theorem toFullAt_compat (Δ : LocalConditions R G Gv loc A)
    (v : Vo ⊕ Vn) (n : ℤ) (a : (Δ.U v).X n) :
    ((fullAt Δ).i v).f n n rfl ((toFullAt Δ v).f n n rfl a) = (Δ.i v).f n n rfl a := by
  cases v <;> rfl

omit [IsTopologicalGroup G] in
/-- The paired strict-to-primitive map commutes with the actual local inclusions. -/
theorem fromZeroAt_compat (Δ : LocalConditions R G Gv loc A)
    (v : Vo ⊕ Vn) (n : ℤ) (a : ((zeroAt Δ).U v).X n) :
    (Δ.i v).f n n rfl ((fromZeroAt Δ v).f n n rfl a) = ((zeroAt Δ).i v).f n n rfl a := by
  cases v with
  | inl v => rfl
  | inr q => exact map_zero _

/-- The primitive-to-relaxed map on the actual Selmer cones. -/
def primitiveToRelaxed (Δ : LocalConditions R G Gv loc A) :
    GHom (selCx (selData R G Gv loc A Δ)) (selCx (selData R G Gv loc A (fullAt Δ))) :=
  condMap Δ (fullAt Δ) (toFullAt Δ) (toFullAt_compat Δ)

/-- The paired strict-to-primitive map on the actual Selmer cones. -/
def strictToPrimitive (Δ : LocalConditions R G Gv loc A) :
    GHom (selCx (selData R G Gv loc A (zeroAt Δ))) (selCx (selData R G Gv loc A Δ)) :=
  condMap (zeroAt Δ) Δ (fromZeroAt Δ) (fromZeroAt_compat Δ)

end Conditions

section Retention

variable {R : Type u} [CommRing R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Vo Vn : Type u} {Gv : Vo ⊕ Vn → Type u}
  [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* G}
  {A B T : Type u}
  [AddCommGroup A] [Module R A] [DistribMulAction G A] [SMulCommClass G R A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul R A] [ContinuousSMul G A]
  [AddCommGroup B] [Module R B] [DistribMulAction G B] [SMulCommClass G R B]
  [TopologicalSpace B] [ContinuousAdd B] [ContinuousConstSMul R B] [ContinuousSMul G B]
  [AddCommGroup T] [Module R T] [DistribMulAction G T] [SMulCommClass G R T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul R T] [ContinuousSMul G T]
  (β : A →ₗ[R] B →ₗ[R] T)
  (hβ : ∀ (g : G) (a : A) (b : B), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : A × B => β x.1 x.2)
  (ΔPp : LocalConditions R G Gv loc A) (ΔP : LocalConditions R G Gv loc B)

/-- The relaxed isotropy homotopy is the old primitive homotopy, with zero
at the selected places against the zero condition. -/
def relaxedIsotropy (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP) :
    IsotropyData R G Gv loc β hβ hβc (zeroAt ΔPp) (fullAt ΔP) where
  h
    | .inl v => I.h (.inl v)
    | .inr _ => fun _ _ _ _ => 0
  isotropy := by
    intro v i i₁ j j₁ l l₁ h hi hj hl a b
    cases v with
    | inl v => exact I.isotropy (.inl v) i i₁ j j₁ l l₁ h hi hj hl a b
    | inr q =>
      change (localCx R G Gv loc T (.inr q)).d l l₁ hl
          ((0 : _ →ₗ[R] _ →ₗ[R] _) a b) + (0 : _ →ₗ[R] _ →ₗ[R] _) _ b +
        sgn i • (0 : _ →ₗ[R] _ →ₗ[R] _) a _ =
        (localPair R G Gv loc β hβ hβc (.inr q)).P i j l₁ _ 0 _
      simp

omit [IsTopologicalGroup G] in
/-- Placewise retention is derived, not imposed as an independent equality. -/
theorem relaxedIsotropy_retained (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP)
    (v : Vo ⊕ Vn) (i j l : ℤ) (h : i + j = l + 1)
    (a : ((zeroAt ΔPp).U v).X i) (b : (ΔP.U v).X j) :
    (relaxedIsotropy β hβ hβc ΔPp ΔP I).h v i j l h a ((toFullAt ΔP v).f j j rfl b) =
      I.h v i j l h ((fromZeroAt ΔPp v).f i i rfl a) b := by
  cases v with
  | inl v => rfl
  | inr q =>
    change (0 : _ →ₗ[R] _ →ₗ[R] _) a _ = I.h (.inr q) i j l h 0 b
    simp

/-- Retained pairing on the actual global and local continuous cochains.
No degreewise identification with a finite tame model is required. -/
def actualRetainedPairing (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP) :
    RetainedPairing (selData R G Gv loc B (fullAt ΔP)) (selData R G Gv loc A ΔPp)
      (piMap (toFullAt ΔP)) (piMap (fromZeroAt ΔPp)) := by
  let IR := relaxedIsotropy β hβ hβc ΔPp ΔP I
  let PR := genuinePairData R G Gv loc β hβ hβc (zeroAt ΔPp) (fullAt ΔP) IR
  let PP := genuinePairData R G Gv loc β hβ hβc ΔPp ΔP I
  refine
    { E := globalCx R G T
      EL := localSumCx R G Gv loc T
      resE := resS R G Gv loc T
      cupG := globalPair R G β hβ hβc
      cupL := localSumPair R G Gv loc β hβ hβc
      compat := PP.compat
      hR := PR.hU
      isoR := ?_
      hP := PP.hU
      isoP := ?_
      retained := ?_ }
  · intro i i₁ j j₁ l l₁ h hi hj hl a b
    have he := PR.isotropy i i₁ j j₁ l l₁ h hi hj hl a b
    have hc : (ghomComp (piMap (fromZeroAt ΔPp)) (piMap ΔPp.i)).f i i rfl a =
        (piMap (zeroAt ΔPp).i).f i i rfl a :=
      funext fun v => fromZeroAt_compat ΔPp v i (a v)
    exact he.trans (congrArg
      (fun c => (localSumPair R G Gv loc β hβ hβc).P i j l₁ (by omega) c
        ((piMap (fullAt ΔP).i).f j j rfl b)) hc.symm)
  · intro i i₁ j j₁ l l₁ h hi hj hl a b
    have he := PP.isotropy i i₁ j j₁ l l₁ h hi hj hl a b
    have hc : (ghomComp (piMap (toFullAt ΔP)) (piMap (fullAt ΔP).i)).f j j rfl b =
        (piMap ΔP.i).f j j rfl b :=
      funext fun v => toFullAt_compat ΔP v j (b v)
    exact he.trans (congrArg
      (fun c => (localSumPair R G Gv loc β hβ hβc).P i j l₁ (by omega)
        ((piMap ΔPp.i).f i i rfl a) c) hc.symm)
  · intro i j l h a b
    funext v
    exact relaxedIsotropy_retained β hβ hβc ΔPp ΔP I v i j l h (a v) (b v)

/-- The actual relaxed pairing with unchanged old isotropy homotopies. -/
abbrev actualRelaxedPairData (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP) :
    SelPairData (selData R G Gv loc A (zeroAt ΔPp)) (selData R G Gv loc B (fullAt ΔP)) :=
  genuinePairData R G Gv loc β hβ hβc (zeroAt ΔPp) (fullAt ΔP)
    (relaxedIsotropy β hβ hβc ΔPp ΔP I)

/-- The actual primitive pairing uses the given primitive isotropy homotopies. -/
abbrev actualPrimitivePairData (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP) :
    SelPairData (selData R G Gv loc A ΔPp) (selData R G Gv loc B ΔP) :=
  genuinePairData R G Gv loc β hβ hβc ΔPp ΔP I

/-- Naturality on the actual Selmer cones, with the actual condition maps. -/
theorem actual_cup_naturality (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP)
    (i j n : ℤ) (h : i + j = n)
    (s : (selCx (selData R G Gv loc A (zeroAt ΔPp))).X i)
    (p : (selCx (selData R G Gv loc B ΔP)).X j) :
    selCup (actualRelaxedPairData β hβ hβc ΔPp ΔP I) i j n h s
      ((primitiveToRelaxed ΔP).f j j rfl p) =
    selCup (actualPrimitivePairData β hβ hβc ΔPp ΔP I) i j n h
      ((strictToPrimitive ΔPp).f i i rfl s) p := by
  obtain ⟨a, u, x⟩ := s
  obtain ⟨b, v, y⟩ := p
  let PR := actualRelaxedPairData β hβ hβc ΔPp ΔP I
  let PP := actualPrimitivePairData β hβ hβc ΔPp ΔP I
  have hinc : (piMap (fullAt ΔP).i).f j j rfl ((piMap (toFullAt ΔP)).f j j rfl v) =
      (piMap ΔP.i).f j j rfl v := funext fun w => toFullAt_compat ΔP w j (v w)
  have hret : PR.hU i j (n - 1) (by omega) u ((piMap (toFullAt ΔP)).f j j rfl v) =
      PP.hU i j (n - 1) (by omega) ((piMap (fromZeroAt ΔPp)).f i i rfl u) v :=
    funext fun w => relaxedIsotropy_retained β hβ hβc ΔPp ΔP I w i j (n - 1) (by omega) (u w) (v w)
  change selCupFun PR i j n h (a, u, x) (b, (piMap (toFullAt ΔP)).f j j rfl v, y) =
    selCupFun PP i j n h (a, (piMap (fromZeroAt ΔPp)).f i i rfl u, x) (b, v, y)
  apply Prod.ext
  · rfl
  · change
      (localSumPair R G Gv loc β hβ hβc).P (i - 1) j (n - 1) (by omega) x
          ((piMap (fullAt ΔP).i).f j j rfl ((piMap (toFullAt ΔP)).f j j rfl v)) +
        sgn i • (localSumPair R G Gv loc β hβ hβc).P i (j - 1) (n - 1) (by omega)
          ((resS R G Gv loc A).f i i rfl a) y +
          (show (localSumCx R G Gv loc T).X (n - 1) from
            PR.hU i j (n - 1) (by omega) u ((piMap (toFullAt ΔP)).f j j rfl v)) =
      (localSumPair R G Gv loc β hβ hβc).P (i - 1) j (n - 1) (by omega) x
          ((piMap ΔP.i).f j j rfl v) +
        sgn i • (localSumPair R G Gv loc β hβ hβc).P i (j - 1) (n - 1) (by omega)
          ((resS R G Gv loc A).f i i rfl a) y +
          (show (localSumCx R G Gv loc T).X (n - 1) from
            PP.hU i j (n - 1) (by omega) ((piMap (fromZeroAt ΔPp)).f i i rfl u) v)
    erw [hinc, hret]

/-- The second norm factor is the value of the same actual paired functional.
The retained boundary of the strict lift disappears only on cocycles. -/
theorem actual_pairedFunctional_natural (I : IsotropyData R G Gv loc β hβ hβc ΔPp ΔP)
    (tr : (coneCx (actualPrimitivePairData β hβ hβc ΔPp ΔP I).resE).X 3 →ₗ[R] R)
    (htr : ∀ c, tr ((coneCx (actualPrimitivePairData β hβ hβc ΔPp ΔP I).resE).d 2 3 rfl c) = 0)
    (zS : (selCx (selData R G Gv loc A (zeroAt ΔPp))).X 1)
    (zPp : (selCx (selData R G Gv loc A ΔPp)).X 1) (e : R)
    (b : (selCx (selData R G Gv loc A ΔPp)).X 0)
    (hlift : (strictToPrimitive ΔPp).f 1 1 rfl zS =
      e • zPp + (selCx (selData R G Gv loc A ΔPp)).d 0 1 rfl b)
    (w : (selCx (selData R G Gv loc B ΔP)).X 2)
    (hw : (selCx (selData R G Gv loc B ΔP)).d 2 3 rfl w = 0) :
    pairedFun (actualRelaxedPairData β hβ hβc ΔPp ΔP I) tr zS
        ((primitiveToRelaxed ΔP).f 2 2 rfl w) =
      e * pairedFun (actualPrimitivePairData β hβ hβc ΔPp ΔP I) tr zPp w := by
  let PP := actualPrimitivePairData β hβ hβc ΔPp ΔP I
  change tr (selCup (actualRelaxedPairData β hβ hβc ΔPp ΔP I) 1 2 3 rfl zS
      ((primitiveToRelaxed ΔP).f 2 2 rfl w)) = e * tr (selCup PP 1 2 3 rfl zPp w)
  rw [actual_cup_naturality β hβ hβc ΔPp ΔP I, hlift]
  erw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [smul_eq_mul]
  have hl := selmerCupLeibniz_proof R (selData R G Gv loc A ΔPp) (selData R G Gv loc B ΔP)
    PP 0 1 2 3 2 3 rfl rfl rfl rfl b w
  rw [hw] at hl
  erw [map_zero, smul_zero, add_zero] at hl
  have h0 := htr (selCup PP 0 2 2 rfl b w)
  rw [hl] at h0
  rw [h0, add_zero]

end Retention

end ZInQ.Contrib.RC53Assist.CoordProvenance
