import ZInQKernel.Contrib.RC53Assist.Boundary45.LocalFacts
import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.Boundary

/-! # Wiring the base-zero local facts into the retained stages

The consumed form of the base-zero local facts is the pair of fields `honto` and `hinj` of
`RetainedStage45`, which feeds `InnerLimit45Base.ofStages`. `retainedStageOfLocalFacts` builds a
retained stage from local-condition data satisfying `LocalFacts`, filling those two fields verbatim
and keeping every other field as an input; `mixedRetainedStage` does so for the mixed stage pattern.
Matching the actual finite stages with `mixedStageSelData` remains open; note that `RetainedStage45`
works in the fibre `t = 0` over `ℤ/2^i`, while `mixedStageSelData` is over `(ℤ/2ⁿ)[t]/tⁿ`.
These declarations were written in an independent review of the local-facts contribution and are
recorded here unchanged in substance.
-/

namespace ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local

open ZInQ.Manuscript.RC.BaseZeroAssembly
open ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
open NumberField IsDedekindDomain Matrix

universe w

/-- **The consumed route.** `RetainedStage45` (used by `InnerLimit45Base.ofStages`) has
`honto`/`hinj` fields of the same shape; `LocalFacts` fills them verbatim when the stage's cochain
groups are those of a `SelData`. All other fields stay inputs. -/
def retainedStageOfLocalFacts {G : Type} [AddCommGroup G] {P : G} {L : ℤ} {i N M0 : ℕ}
    {k : Type} [CommRing k] (D : SelData k) (hD : LocalFacts D.ι)
    (S : SplitNormStage P) (H1 : Type) [AddCommGroup H1] (cls : D.G.X 1 →+ H1)
    (hexact : ∀ c : D.G.X 1, D.G.d 1 2 rfl c = 0 → cls c = 0 →
      ∃ g : D.G.X 0, D.G.d 0 1 rfl g = c)
    (δ : G →+ H1) (zG jG : D.G.X 1) (zU jU : D.U.X 1) (zL jL : D.L.X 0)
    (hzG : D.G.d 1 2 rfl zG = 0) (hjG : D.G.d 1 2 rfl jG = 0)
    (hzU : D.U.d 1 2 rfl zU = 0) (hjU : D.U.d 1 2 rfl jU = 0)
    (hz : D.res.f 1 1 rfl zG - D.ι.f 1 1 rfl zU = D.L.d 0 1 rfl zL)
    (hj : D.res.f 1 1 rfl jG - D.ι.f 1 1 rfl jU = D.L.d 0 1 rfl jL)
    (hzcls : cls zG = δ (L • S.W)) (hjcls : cls jG = δ P)
    (p1 : D.G.X 1 × D.U.X 1 × D.L.X 0 →+ (Fin N → ℤ_[2] ⧸ twoAdicStage i))
    (p0 : D.G.X 0 × D.U.X 0 →+ (Fin M0 → ℤ_[2] ⧸ twoAdicStage i))
    (dC : Matrix (Fin N) (Fin M0) ℤ_[2])
    (hdC : ∀ (v : D.G.X 0) (w : D.U.X 0), p1 (D.G.d 0 1 rfl v, D.U.d 0 1 rfl w,
      D.res.f 0 0 rfl v - D.ι.f 0 0 rfl w) = dC.map (Ideal.Quotient.mk (twoAdicStage i)) *ᵥ p0 (v, w))
    (zeta jay : Fin N → ℤ_[2])
    (hzeta : p1 (zG, zU, zL) = fun a => Ideal.Quotient.mk (twoAdicStage i) (zeta a))
    (hjay : p1 (jG, jU, jL) = fun a => Ideal.Quotient.mk (twoAdicStage i) (jay a)) :
    RetainedStage45 P L i N M0 :=
  { S := S, G0 := D.G.X 0, G1 := D.G.X 1, G2 := D.G.X 2, U0 := D.U.X 0, U1 := D.U.X 1,
    U2 := D.U.X 2, L0 := D.L.X 0, L1 := D.L.X 1, H1 := H1,
    dG0 := (D.G.d 0 1 rfl).toAddMonoidHom, dG1 := (D.G.d 1 2 rfl).toAddMonoidHom,
    dU0 := (D.U.d 0 1 rfl).toAddMonoidHom, dU1 := (D.U.d 1 2 rfl).toAddMonoidHom,
    dL0 := (D.L.d 0 1 rfl).toAddMonoidHom,
    loc0 := (D.res.f 0 0 rfl).toAddMonoidHom, loc1 := (D.res.f 1 1 rfl).toAddMonoidHom,
    ι0 := (D.ι.f 0 0 rfl).toAddMonoidHom, ι1 := (D.ι.f 1 1 rfl).toAddMonoidHom,
    hloc := D.res.comm 0 1 0 1 rfl rfl rfl rfl, hι := D.ι.comm 0 1 0 1 rfl rfl rfl rfl,
    honto := hD.1, hinj := hD.2, cls := cls, hexact := hexact, δ := δ,
    zG := zG, jG := jG, zU := zU, jU := jU, zL := zL, jL := jL,
    hzG := hzG, hjG := hjG, hzU := hzU, hjU := hjU, hz := hz, hj := hj,
    hzcls := hzcls, hjcls := hjcls, p1 := p1, p0 := p0, dC := dC, hdC := hdC,
    zeta := zeta, jay := jay, hzeta := hzeta, hjay := hjay }

/-- The mixed finite-stage pattern feeds that consumed structure directly. -/
noncomputable def mixedRetainedStage {G : Type} [AddCommGroup G] {P : G} {L : ℤ} {i N M0 : ℕ}
    {K : Type} [Field K] [NumberField K]
    {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S)
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
    (a : GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef n)ˣ) [IsOpenKer a]
    (F : Set (Places K S))
    (Z : ∀ v : Places K S, Submodule (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef n)
      (contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef n) (Gloc K v.1)
        (ResMod (locMap K S v.1) (MinS hS W n a)) 1))
    (hZ : ∀ v z, z ∈ Z v →
      contD (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef n) (Gloc K v.1)
        (ResMod (locMap K S v.1) (MinS hS W n a)) 1 z = 0) :=
  retainedStageOfLocalFacts (G := G) (P := P) (L := L) (i := i) (N := N) (M0 := M0)
    (mixedStageSelData hS W n a F Z hZ) (mixedStage_localFacts hS W n a F Z hZ)

/-- **Non-vacuity of the predicate**: the zero local condition into a complex with a nonzero
degree-zero cocycle fails `LocalFacts` (so the proved instances are not trivial by definition). -/
def constCx : GCx ℤ where
  X _ := ModuleCat.of ℤ ℤ
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

theorem not_localFacts_zero_into_const : ¬ LocalFacts (zeroGHom (ZInQ.Manuscript.RC.SelmerComplex.zeroCx ℤ) constCx) := by
  intro h
  obtain ⟨w, -, hw⟩ := h.1 (show constCx.X 0 from (1 : ℤ)) rfl
  exact one_ne_zero (show (1 : ℤ) = 0 from hw.symm)

end ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local
