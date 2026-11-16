import ZInQKernel.Contrib.OneProof.SGA1Printed
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

/-!
# gaga-serre: `gagaMorphism` from Serre's GAGA, as printed for projective varieties

sga1-fix's `SGA1Printed.SGA1_XII_4_4` (GAGA for morphisms of abelian varieties, over `IsAnMorphism` and
`AnFunAt`) was rated GLUE by the 11-16 review: SGA 1's `𝒪_{X^an}` may be nonreduced, so identifying it
with `AnFunAt` is a second theorem. Serre's `X^h` (GAGA, 1956) is reduced by construction: its
underlying space is `X(ℂ)` with the topology glued from affine pieces `U ↪ ℂ^k`, and its structure
sheaf is the sheaf of functions that are locally restrictions of holomorphic functions of the
coordinates; a holomorphic map is a continuous map pulling back germs of holomorphic functions. This
file restates the leaf as Serre's theorem on holomorphic maps of projective varieties and proves,
in Lean, that its objects are the repository's:

* `anFunAt_iff_serreHolAt`: `AnFunAt` is Serre's sheaf (`SerreHolAt`, over unif-topology's
  `AffineChart`s, the charts from which `analyticTopology` is glued);
* `anFunAt_iff_forall_chart`, `serreHolAt_iff_forall_chart`: chart independence (holomorphic in some
  affine chart iff in every affine chart at the point), so any affine cover gives the same sheaf;
* `isAnMorphism_iff_germ`, `isAnMorphism_iff_isSerreHolMap`: `IsAnMorphism` is Serre's holomorphic
  map `IsSerreHolMap` (continuous, pulls back germs of holomorphic functions at every point);
* `isProjVar`: an abelian variety is a projective variety in Serre's sense (reduced, closed in some
  `ℙ^N_ℂ`), from the vendored `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`
  and properness;
* `sga1_XII_4_4_of_serre : SerreGAGAMorphism → SGA1Printed.SGA1_XII_4_4` and the main theorem
  `gagaMorphism_of_serre`.

Report: `docs/research/gaga-serre.md`.
-/

open scoped Topology
open Filter Set CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

noncomputable section

namespace SerreGAGA

open UnifPrinted UnifTopology SGA1Printed SGA1Etale
open PkgI3 (AbVar)

/-! ## 1. Serre's objects -/

/-- **Projective variety over `ℂ`** in Serre's sense (FAC §51, GAGA; UNVERIFIED numbering): a reduced
closed subscheme of a projective space `ℙ^N_ℂ` (`N` finite; `ℙ` is the vendored Jacobian-Challenge
`ProjectiveSpace`, the base change of `Proj ℤ[x_i]`), as a `ℂ`-scheme. -/
def IsProjVar (X : Over (Spec (CommRingCat.of ℂ))) : Prop :=
  IsReduced X.left ∧
    ∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of ℂ))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ) = X.hom

/-- **Serre's sheaf of holomorphic functions on `X^h`** (GAGA §2; UNVERIFIED numbering): near `P`, `F`
is the restriction of a function `H` holomorphic near `(fᵢ(P))` in `ℂ^k`, for an affine piece
`U ↪ 𝔸^k_ℂ` (`AffineChart`: an affine open with `ℂ`-algebra generators `f₁, …, f_k`) containing `P`.
-/
def SerreHolAt (X : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → ℂ) (P : CPt X) : Prop :=
  ∃ c : AffineChart X, XPtIn X P c.U ∧ ∃ H : (Fin c.k → ℂ) → ℂ,
    AnalyticAt ℂ H (fun i => XevalAt X c.U (c.f i) P) ∧
    ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X c.U (c.f i) Q)

/-- **Serre's holomorphic maps `X^h → Y^h`** (GAGA §1–§2; UNVERIFIED numbering): continuous for the
analytic topologies (`analyticTopology`, glued from the affine pieces `U(ℂ) ⊂ ℂ^k`), and pulling back
every germ of holomorphic function at `F(P)` to a germ of holomorphic function at `P`. -/
def IsSerreHolMap (X Y : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → CPt Y) : Prop :=
  @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
    ∀ (P : CPt X) (s : CPt Y → ℂ), SerreHolAt Y s (F P) → SerreHolAt X (s ∘ F) P

/-! ## 2. The leaf -/

/-- **LEAF (printed form): Serre's GAGA for holomorphic maps of projective varieties.** J.-P. Serre,
*Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), 1–42, §4, the
proposition on holomorphic maps (every holomorphic map `X^h → Y^h` of projective varieties is
regular), proved there from Chow's theorem (§4, Prop. 13) through the graph. Section, number and
wording UNVERIFIED (not read for this task). All objects are Serre's: projective varieties are
`IsProjVar` (reduced closed subschemes of `ℙ^N_ℂ`); `X^h` is `X(ℂ)` with `analyticTopology` and the
sheaf `SerreHolAt`; holomorphic maps are `IsSerreHolMap`; "`F` is regular" is `∃ f : X ⟶ Y` (a
morphism of `ℂ`-schemes) with `F P = P ≫ f` on `ℂ`-points. -/
def SerreGAGAMorphism : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of ℂ))), IsProjVar X → IsProjVar Y →
    ∀ F : CPt X → CPt Y, IsSerreHolMap X Y F → ∃ f : X ⟶ Y, ∀ P, F P = P ≫ f

/-! ## 3. Glue: Serre's objects are the repository's -/

variable {X Y : Over (Spec (CommRingCat.of ℂ))}

/-- Being holomorphic at a point is an open condition. -/
theorem anFunAt_eventually [LocallyOfFiniteType X.hom] {F : CPt X → ℂ} {P : CPt X}
    (h : AnFunAt X F P) : ∀ᶠ Q in @nhds _ (analyticTopology X) P, AnFunAt X F Q := by
  letI := analyticTopology X
  obtain ⟨U, k, g, H, hPU, hH, hev⟩ := h
  have hcont : ContinuousAt (fun Q i => XevalAt X U (g i) Q) P :=
    continuousAt_pi.mpr fun i => continuousAt_xevalAt_an U (g i) hPU
  have hH' := hcont.eventually hH.eventually_analyticAt
  filter_upwards [(isOpen_ptIn_an U).mem_nhds hPU, hH', hev.eventually_nhds] with Q hQU hQH hQe
  exact ⟨U, k, g, H, hQU, hQH, hQe⟩

/-- `IsAnMorphism` (stated with opens) is the pointwise germ condition. -/
theorem isAnMorphism_iff_germ [LocallyOfFiniteType Y.hom] (F : CPt X → CPt Y) :
    IsAnMorphism X Y F ↔ @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
      ∀ (P : CPt X) (s : CPt Y → ℂ), AnFunAt Y s (F P) → AnFunAt X (s ∘ F) P := by
  letI := analyticTopology X
  letI := analyticTopology Y
  constructor
  · rintro ⟨hc, hF⟩
    refine ⟨hc, fun P s hs => ?_⟩
    have hmem : F P ∈ interior {Q | AnFunAt Y s Q} :=
      mem_interior_iff_mem_nhds.mpr (anFunAt_eventually hs)
    exact hF _ s isOpen_interior
      (fun Q hQ => (interior_subset (s := {Q | AnFunAt Y s Q}) hQ : AnFunAt Y s Q)) P hmem
  · rintro ⟨hc, hF⟩
    exact ⟨hc, fun W s _ hs P hP => hF P s (hs _ hP)⟩


/-- Every open `U ∋ P` contains an affine chart at `P` (`X` locally of finite type over `ℂ`). -/
theorem exists_affineChart_le [LocallyOfFiniteType X.hom] {P : CPt X} {U : X.left.Opens}
    (hPU : XPtIn X P U) : ∃ c : AffineChart X, XPtIn X P c.U ∧ c.U ≤ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    ((xPtIn_iff _ _).mp hPU) U.2
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType X.hom (inferInstance)
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by rw [Scheme.Hom.preimage_top]; exact le_top)
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have hft' : (algC X V).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ hsurj)
  letI := (algC X V).toAlgebra
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  refine ⟨⟨V, hV, n, fun i => φ (MvPolynomial.X i), fun y => ?_⟩, (xPtIn_iff _ _).mpr hxV,
    fun x hx => hVU hx⟩
  obtain ⟨p, hp⟩ := hφ y
  refine ⟨p, ?_⟩
  rw [← hp]
  conv_rhs => rw [MvPolynomial.aeval_unique φ]
  rfl

/-- **`AnFunAt` is Serre's sheaf of holomorphic functions.** -/
theorem anFunAt_iff_serreHolAt [LocallyOfFiniteType X.hom] (F : CPt X → ℂ) (P : CPt X) :
    AnFunAt X F P ↔ SerreHolAt X F P := by
  letI := analyticTopology X
  constructor
  · rintro ⟨U, k, g, H, hPU, hH, hev⟩
    obtain ⟨c, hPc, hcU⟩ := exists_affineChart_le hPU
    choose p hp using fun j => c.generates (res hcU (g j))
    have hval : ∀ Q, XPtIn X Q c.U → (fun j => XevalAt X U (g j) Q) =
        fun j => MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) (p j) := by
      intro Q hQ; funext j
      rw [← xevalAt_res hcU (g j) hQ, ← hp j, xevalAt_eq_evP hQ, MvPolynomial.coe_eval₂Hom,
        evP_eval₂]
      simp only [xevalAt_eq_evP hQ]
    refine ⟨c, hPc, fun v => H (fun j => MvPolynomial.eval v (p j)), ?_, ?_⟩
    · refine AnalyticAt.comp (g := H) (f := fun v j => MvPolynomial.eval v (p j)) ?_
        (AnalyticAt.pi fun j => ?_)
      · rw [← hval P hPc]; exact hH
      · have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ)
          (f := fun v : Fin c.k → ℂ => v) (z := fun i => XevalAt X c.U (c.f i) P)
          (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.k => ℂ) i).analyticAt _)
          (p j)
        simpa [MvPolynomial.coe_aeval_eq_eval] using h
    · filter_upwards [hev, (isOpen_ptIn_an c.U).mem_nhds hPc] with Q hQ hQc
      rw [hQ, hval Q hQc]
  · rintro ⟨c, hPc, H, hH, hev⟩
    exact ⟨c.U, c.k, c.f, H, hPc, hH, hev⟩

/-- Evaluation commutes with restriction to a basic open. -/
theorem xevalAt_algebraMap_basicOpen {U : X.left.Opens} (s : Γ(X.left, U)) (a : Γ(X.left, U))
    {Q : CPt X} (hQ : XPtIn X Q (X.left.basicOpen s)) :
    XevalAt X (X.left.basicOpen s) (algebraMap Γ(X.left, U) Γ(X.left, X.left.basicOpen s) a) Q =
      XevalAt X U a Q :=
  xevalAt_res (X.left.basicOpen_le s) a hQ

/-- Evaluation of a polynomial in regular functions. -/
theorem xevalAt_eval₂ {U : X.left.Opens} {k : ℕ} (f : Fin k → Γ(X.left, U))
    (p : MvPolynomial (Fin k) ℂ) {Q : CPt X} (hQ : XPtIn X Q U) :
    XevalAt X U (MvPolynomial.eval₂Hom (algC X U) f p) Q =
      MvPolynomial.eval (fun i => XevalAt X U (f i) Q) p := by
  rw [xevalAt_eq_evP hQ, MvPolynomial.coe_eval₂Hom, evP_eval₂]
  simp only [xevalAt_eq_evP hQ]

/-- Polynomials are analytic. -/
theorem analyticAt_mvEval {k : ℕ} (p : MvPolynomial (Fin k) ℂ) (z : Fin k → ℂ) :
    AnalyticAt ℂ (fun v => MvPolynomial.eval v p) z := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ)
    (f := fun v : Fin k → ℂ => v) (z := z)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).analyticAt _) p
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

/-- **Chart independence** (the well-definedness of Serre's sheaf, GAGA §2): a function holomorphic at
`P` is holomorphic in the coordinates of *every* affine chart at `P`. So `SerreHolAt` (some chart)
agrees with the sheaf glued from any affine cover (every chart of the cover). Proof: a basic open
`D(s) ∋ P` of the chart lies in `U`, `Γ(D(s)) = Γ(c.U)[1/s]` (`isLocalization_basicOpen`), so each
`gⱼ = pⱼ(f)/q(f)^m` on `D(s)` with `q(f)(P) = s(P) ≠ 0`. -/
theorem anFunAt_iff_forall_chart [LocallyOfFiniteType X.hom] (F : CPt X → ℂ) (P : CPt X) :
    AnFunAt X F P ↔ ∀ c : AffineChart X, XPtIn X P c.U → ∃ H : (Fin c.k → ℂ) → ℂ,
      AnalyticAt ℂ H (fun i => XevalAt X c.U (c.f i) P) ∧
      ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X c.U (c.f i) Q) := by
  letI := analyticTopology X
  constructor
  · rintro ⟨U, k, g, H, hPU, hH, hev⟩ c hPc
    obtain ⟨s, hsle, hPs⟩ := c.isAffine.exists_basicOpen_le (V := U)
      ⟨P.left.base default, (xPtIn_iff _ _).mp hPU⟩ ((xPtIn_iff _ _).mp hPc)
    set D := X.left.basicOpen s with hD
    have hPD : XPtIn X P D := (xPtIn_iff _ _).mpr hPs
    haveI := c.isAffine.isLocalization_basicOpen s
    have hloc : ∀ j, ∃ (a : Γ(X.left, c.U)) (m : ℕ),
        res hsle (g j) * algebraMap Γ(X.left, c.U) Γ(X.left, D) (s ^ m) =
          algebraMap Γ(X.left, c.U) Γ(X.left, D) a := by
      intro j
      obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) (res hsle (g j))
      exact ⟨a, m, ha⟩
    choose a m ha using hloc
    choose p hp using fun j => c.generates (a j)
    obtain ⟨q, hq⟩ := c.generates s
    have hDc : ∀ Q, XPtIn X Q D → XPtIn X Q c.U := fun Q hQ => xPtIn_mono (X.left.basicOpen_le s) hQ
    have hsQ : ∀ Q (hQ : XPtIn X Q D),
        MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) q ≠ 0 := by
      intro Q hQ
      rw [← xevalAt_eval₂ c.f q (hDc Q hQ), hq, xevalAt_eq_evP (hDc Q hQ)]
      exact (xPtIn_basicOpen_iff Q (hDc Q hQ) s).mp hQ
    have hval : ∀ Q, XPtIn X Q D → (fun j => XevalAt X U (g j) Q) =
        fun j => MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) (p j) /
          MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) q ^ m j := by
      intro Q hQ; funext j
      rw [eq_div_iff (pow_ne_zero _ (hsQ Q hQ))]
      have h1 := congrArg (fun x => XevalAt X D x Q) (ha j)
      rw [xevalAt_eq_evP hQ, map_mul, ← xevalAt_eq_evP hQ, ← xevalAt_eq_evP hQ,
        xevalAt_res hsle (g j) hQ, xevalAt_algebraMap_basicOpen s _ hQ,
        xevalAt_algebraMap_basicOpen s _ hQ, xevalAt_eq_evP (hDc Q hQ), map_pow,
        ← xevalAt_eq_evP (hDc Q hQ)] at h1
      rw [← xevalAt_eval₂ c.f q (hDc Q hQ), hq, ← xevalAt_eval₂ c.f (p j) (hDc Q hQ), hp j]
      exact h1
    refine ⟨fun v => H (fun j => MvPolynomial.eval v (p j) / MvPolynomial.eval v q ^ m j), ?_, ?_⟩
    · refine AnalyticAt.comp (g := H)
        (f := fun v j => MvPolynomial.eval v (p j) / MvPolynomial.eval v q ^ m j) ?_
        (AnalyticAt.pi fun j => ?_)
      · rw [← hval P hPD]; exact hH
      · exact (analyticAt_mvEval (p j) _).div ((analyticAt_mvEval q _).pow _)
          (pow_ne_zero _ (hsQ P hPD))
    · filter_upwards [hev, (isOpen_ptIn_an D).mem_nhds hPD] with Q hQ hQD
      rw [hQ, hval Q hQD]
  · intro h
    obtain ⟨c, hPc⟩ := exists_affineChart P
    obtain ⟨H, hH, hev⟩ := h c hPc
    exact ⟨c.U, c.k, c.f, H, hPc, hH, hev⟩

/-- Serre's sheaf, "every chart" form. -/
theorem serreHolAt_iff_forall_chart [LocallyOfFiniteType X.hom] (F : CPt X → ℂ) (P : CPt X) :
    SerreHolAt X F P ↔ ∀ c : AffineChart X, XPtIn X P c.U → ∃ H : (Fin c.k → ℂ) → ℂ,
      AnalyticAt ℂ H (fun i => XevalAt X c.U (c.f i) P) ∧
      ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X c.U (c.f i) Q) := by
  rw [← anFunAt_iff_serreHolAt, anFunAt_iff_forall_chart]

/-- **`IsAnMorphism` is Serre's holomorphic map** (`X`, `Y` locally of finite type over `ℂ`). -/
theorem isAnMorphism_iff_isSerreHolMap [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (F : CPt X → CPt Y) : IsAnMorphism X Y F ↔ IsSerreHolMap X Y F := by
  rw [isAnMorphism_iff_germ, IsSerreHolMap]
  simp only [← anFunAt_iff_serreHolAt]

/-- A projective variety is of finite type over `ℂ`. -/
theorem locallyOfFiniteType_of_isProjVar (h : IsProjVar X) : LocallyOfFiniteType X.hom := by
  obtain ⟨-, N, hN, i, hi, hover⟩ := h
  rw [← hover]
  infer_instance

/-- **Abelian varieties are projective varieties** (Serre's sense): `A` is integral (geometrically
integral over `ℂ`), and the vendored projective immersion `A → ℙ^N_ℂ` is proper (`A` proper,
`ℙ^N_ℂ` separated), so a closed immersion. -/
theorem isProjVar (A : AbVar ℂ) : IsProjVar A.X := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  refine ⟨inferInstance, ?_⟩
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  have : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ)) := by
    rw [hover]; infer_instance
  have : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ))
  exact ⟨N, hN, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, hover⟩

/-- sga1-fix's GAGA leaf for abelian varieties follows from Serre's printed theorem. -/
theorem sga1_XII_4_4_of_serre (h : SerreGAGAMorphism) : SGA1_XII_4_4 := by
  intro A B F hF
  have := locallyOfFiniteType_of_isProjVar (isProjVar A)
  have := locallyOfFiniteType_of_isProjVar (isProjVar B)
  exact h A.X B.X (isProjVar A) (isProjVar B) F ((isAnMorphism_iff_isSerreHolMap F).mp hF)

/-- **Main theorem: `GAGAMorphism` from printed leaves**: sga1-fix's leaves for `uniformizationLeafAll`
(Mumford §1, SGA 1 XII 3.3(a), SGA 1 XII 3.2, SGA 1 XII 2.4) and Serre's GAGA for holomorphic maps
of projective varieties. -/
theorem gagaMorphism_of_serre (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) (hS : SerreGAGAMorphism) :
    ZInQ.HomLattice.GAGAMorphism :=
  gagaMorphism_of_printed hM hL hPC hC (sga1_XII_4_4_of_serre hS)

end SerreGAGA
