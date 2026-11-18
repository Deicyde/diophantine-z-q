import ZInQKernel.Contrib.OneProof.RC.Uniform.UniformLowerBound
import ZInQKernel.Contrib.OneProof.RC.Central.Coordinate

/-!
# RC53 UniformSwitch: the height-one switching process from two-term models and switch data

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex L4976–5200. RC16 formalizes the descent as the structure
`ZInQ.Manuscript.RC.Uniform.RegularitySwitchProcess` (`RC/Uniform/HeightOneRegularity.lean`), whose
fields are Elliot's steps taken as inputs, and proves the algebra of each step in `Switch.lean`
(the determinant-preserving switch), `QuadraticCase.lean` (sign planes and the (5.5a)
bookkeeping) and `Determinant.lean`. This file builds an instance of that structure from genuine
data:

* each configuration carries its **two-term model** `[R^{n+1} --D--> R^{n+1}]` over the local ring
  `R` (in the text `R = Λ_𝔭`), an integral cycle `z`, an integral closed functional `w` (integral by
  the paired-functional proposition) and the generic class-functional coordinate `u`
  (`IsClassFunctionalCoord`, the central lane's form) — `TwoTermStage`;
* `fiberDim` is **computed**: `s = dim_k ker(D ⊗ k) = dim_k H¹(C ⊗ k)` for a residue map `ρ : R → k`;
* `coord` is the stage's coordinate `u`.

Fields of `RegularitySwitchProcess` (tex lines as in RC16):
* `pos` — **PROVED** from a primitive integral cycle (`∃ i, ρ (z i) ≠ 0`; tex 4986–4992,
  5154–5157: "has a primitive integral vector, so its fiber dimension is at least one").
* `terminal` — **PROVED**: at `s = 1` some maximal minor of `D ⊗ k` is nonzero
  (`exists_minor_ne_zero_of_finrank_ker_eq_one`), so `adj(D ⊗ k) ≠ 0`, and the integral base change
  of the coordinate (`coord_specializes`) puts `u` in `R` (tex 5157–5193).
* `switch_mixed`, `switch_single` — **PROVED from GLUE inputs** whose types carry the hypotheses of
  RC16's cores, not the fields themselves:
  - the coordinate relation `u = w · u'` with `w` integral comes from `switch_coord_relation` applied
    to the switch-plane data (`SwitchCoordData`) whose finite and singular coordinates are the two
    stage coordinates, with unit volume normalizations `μ_F, μ_S ∈ R^×` (tex 4900–4906, 5137–5153);
  - the dimension drop comes from `bookkeeping_mixed` / `bookkeeping_single_sign`
    (`QuadMixedDims`, `QuadSingleDims`: self-annihilating sign-plane images, detection, and the
    (5.5a) dimension equations; tex 5116–5136), or, at a nonquadratic prime, from the relaxed image
    being the finite plane with (5.5a) (`NonquadDims`; tex 4997–5003).

The GLUE content (labelled in each structure) is the identification of the cohomological objects
(sign decomposition of `H¹(C ⊗ k)`, the local images as self-annihilating planes, the (5.5a)
dimension equations, the stage coordinates as the switch-sequence coordinates) — exactly what RC16
lists as needing Selmer complexes over `Λ` and `𝒪`. The stages are not yet tied to the genuine
fibre models (see the caveat on `HeightOneSwitchData`).

The consumer: `regular_of_switchData` (every stage coordinate is in `R`) and, over the genuine
`Λ_𝔭 = Localization.AtPrime 𝔭` inside `Frac Λ`, `regularAtPrime_of_switchData`, which is the input
shape of RC16's `mem_lambdaHalf_of_regularity`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.UniformSwitch

open Matrix Module ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Manuscript.RC.Central

/-! ### Two-term stages -/

section Stage

variable {A F k : Type*} [CommRing A] [Field F] [Field k]

/-- A configuration's two-term model over `R = A` with its integral cycle, integral closed
functional and generic class-functional coordinate (tex 4976–4992, 3882–3892). -/
structure TwoTermStage (ι : A →+* F) where
  n : ℕ
  D : Matrix (Fin (n + 1)) (Fin (n + 1)) A
  z : Fin (n + 1) → A
  w : Fin (n + 1) → A
  u : F
  hz : D *ᵥ z = 0
  hw : w ᵥ* D = 0
  hu : IsClassFunctionalCoord (D.map ι) (fun i => ι (z i)) (fun i => ι (w i)) u

/-- The fiber dimension `s = dim_k ker(D ⊗_ρ k) = dim_k H¹(C ⊗ k)` (tex 4976–4996). -/
def TwoTermStage.fiberDim {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι) : ℕ :=
  finrank k (LinearMap.ker (S.D.map ρ).mulVecLin)

/-- **`pos`**: a primitive integral cycle gives fiber dimension at least one (tex 4986–4992,
5154–5157). PROVED. -/
theorem TwoTermStage.one_le_fiberDim {ι : A →+* F} (ρ : A →+* k) (S : TwoTermStage ι)
    (hprim : ∃ i, ρ (S.z i) ≠ 0) : 1 ≤ S.fiberDim ρ := by
  obtain ⟨i, hi⟩ := hprim
  have hmem : (fun j => ρ (S.z j)) ∈ LinearMap.ker (S.D.map ρ).mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    ext j
    have := congrFun S.hz j
    simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at this ⊢
    rw [← map_zero ρ, ← this, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_mul]
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hbot := Submodule.finrank_eq_zero.mp h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hi (congrFun hmem i)

/-- **`terminal`**: at fiber dimension one the coordinate is integral (tex 5157–5193). Some maximal
minor of `D ⊗ k` is nonzero, so `adj(D ⊗ k) ≠ 0`, and `coord_specializes` gives `u = ι u₀`.
PROVED. -/
theorem TwoTermStage.coord_integral_of_fiberDim_one [IsLocalRing A] {ι : A →+* F}
    (hι : Function.Injective ι) (ρ : A →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (S : TwoTermStage ι) (h1 : S.fiberDim ρ = 1) : ∃ u₀ : A, ι u₀ = S.u := by
  obtain ⟨k0, j0, hk⟩ := exists_minor_ne_zero_of_finrank_ker_eq_one (S.D.map ρ) h1
  have hres : (S.D.map ρ).adjugate ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 j0) k0
    rw [adjugate_fin_succ_eq_det_submatrix, Matrix.zero_apply] at this
    exact hk ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  obtain ⟨u₀, hu₀, -⟩ := coord_specializes ι hι ρ hρ S.D S.z S.w S.u S.hu hres
  exact ⟨u₀, hu₀⟩

end Stage

/-! ### The switch coordinate relation -/

section Coord

variable {K : Type*} [Field K]

/-- The switch-plane data of RC16's `switch_coord_relation` on the plane `R = K²` with its standard
basis `A = e₀`, `B = e₁` (tex 4888–4906): the local pairing data `(ε, σ, J)`, the localizations
`f, s` with `f A = v`, `s A = 0`, `f B = 0`, `s B = J v` ((4.2)), the strict volume form `ω`, the volume
normalizations `μ_F, μ_S`, and admissible complements `(x, w)`, `(y, w')`. -/
structure SwitchCoordData (K : Type*) [Field K] where
  ε : K
  σ : K
  J : Matrix (Fin 2) (Fin 2) K
  f : (Fin 2 → K) →ₗ[K] (Fin 2 → K)
  s : (Fin 2 → K) →ₗ[K] (Fin 2 → K)
  v : Fin 2 → K
  ω : LinearMap.BilinForm K (Module.Dual K (Fin 2 → K))
  μF : K
  μS : K
  x : Fin 2 → K
  y : Fin 2 → K
  w : Module.Dual K (Fin 2 → K)
  w' : Module.Dual K (Fin 2 → K)
  hσ : σ * σ = 1
  hJ2 : J * J = 1
  hJdet : J.det = -1
  hfA : f (Pi.basisFun K (Fin 2) 0) = v
  hsA : s (Pi.basisFun K (Fin 2) 0) = 0
  hfB : f (Pi.basisFun K (Fin 2) 1) = 0
  hsB : s (Pi.basisFun K (Fin 2) 1) = J *ᵥ v
  hω : LinearMap.IsAlt ω
  hxw : ω (bdryF ε σ J f s x) w ≠ 0
  hyw : ω (bdryS ε σ J f s y) w' ≠ 0

/-- The finite (old) coordinate `u_F` of the switch data. -/
def SwitchCoordData.uF (X : SwitchCoordData K) : K :=
  coordF X.ε X.σ X.J X.f X.s X.ω X.μF (Pi.basisFun K (Fin 2) 0) X.x X.w

/-- The singular (new) coordinate `u_S` of the switch data. -/
def SwitchCoordData.uS (X : SwitchCoordData K) : K :=
  coordS X.ε X.σ X.J X.f X.s X.ω X.μS (Pi.basisFun K (Fin 2) 1) X.y X.w'

/-- `u_F = (−σ μ_F/μ_S) u_S` (from `switch_coord_relation`, tex 4903–4905). PROVED. -/
theorem SwitchCoordData.uF_eq (X : SwitchCoordData K) (hμF : X.μF ≠ 0) (hμS : X.μS ≠ 0) :
    X.uF = (-X.σ * (X.μF / X.μS)) * X.uS := by
  have h := switch_coord_relation (Pi.basisFun K (Fin 2)) X.hσ X.hJ2 X.hJdet X.hfA X.hsA X.hfB
    X.hsB X.hω (μS := X.μS) hμF X.hxw X.hyw
  rw [SwitchCoordData.uS, h, SwitchCoordData.uF]
  field_simp
  linear_combination (-(coordF X.ε X.σ X.J X.f X.s X.ω X.μF (Pi.basisFun K (Fin 2) 0) X.x X.w))
    * X.hσ

end Coord

/-! ### Dimension data of one switch (GLUE identifications, RC16 cores) -/

section Dims

variable {k : Type*} [Field k]

/-- **Mixed signs at a quadratic prime** (tex 4997–5003, 5116–5122; core `bookkeeping_mixed`). GLUE
identification: the local images `U_±` of the actual classes are self-annihilating in the sign
planes `H_± ⊆ F ⊕ S` (the duality of the derivative local conditions), detection puts a nonzero
vector in each finite axis (rank-two detection), and the old and new sign dimensions satisfy (5.5a)
with a common `K_0^±` of dimensions `kp, km`. -/
structure QuadMixedDims (sp sm sp' sm' : ℕ) where
  h2 : (2 : k) ≠ 0
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  Up : Submodule k ((Fin 2 → k) × (Fin 2 → k))
  Um : Submodule k ((Fin 2 → k) × (Fin 2 → k))
  hUp : IsSelfAnnihilatingIn ε J (signPlane ep em) Up
  hUm : IsSelfAnnihilatingIn ε J (signPlane em ep) Um
  hdetp : ∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0
  hdetm : ∃ x ∈ Um, x ∈ finAxis em ∧ x ≠ 0
  kp : ℕ
  km : ℕ
  hVp : sp = kp + finrank k ↥(Up ⊓ finAxis ep)
  hVm : sm = km + finrank k ↥(Um ⊓ finAxis em)
  hVp' : sp' = kp + finrank k ↥(Up ⊓ singAxis em)
  hVm' : sm' = km + finrank k ↥(Um ⊓ singAxis ep)

theorem QuadMixedDims.drop {sp sm sp' sm' : ℕ} (X : QuadMixedDims (k := k) sp sm sp' sm') :
    sp' + sm' + 2 = sp + sm := by
  have h := bookkeeping_mixed X.h2 X.ε X.hε X.J X.ep X.em X.hp X.hm X.he X.Up X.Um X.hUp X.hUm
    X.hdetp X.hdetm (K0p := Fin X.kp → k) (K0m := Fin X.km → k) (Vp := Fin sp → k)
    (Vm := Fin sm → k) (Vp' := Fin sp' → k) (Vm' := Fin sm' → k)
    (by simpa using X.hVp) (by simpa using X.hVm) (by simpa using X.hVp') (by simpa using X.hVm')
  simpa using h.2.2.2.2.1

/-- **One sign only at a quadratic prime** (tex 5123–5136; core `bookkeeping_single_sign`). GLUE
identification as in `QuadMixedDims`, for an old configuration of fiber dimension `s` all in the
`+` sign (the orientation of `J` is part of the data) and new sign dimensions `(a, b)`. -/
structure QuadSingleDims (s a b : ℕ) where
  h2 : (2 : k) ≠ 0
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  Up : Submodule k ((Fin 2 → k) × (Fin 2 → k))
  Um : Submodule k ((Fin 2 → k) × (Fin 2 → k))
  hUp : IsSelfAnnihilatingIn ε J (signPlane ep em) Up
  hUm : IsSelfAnnihilatingIn ε J (signPlane em ep) Um
  hdetp : ∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0
  kp : ℕ
  km : ℕ
  hs : 1 < s
  hVp : s = kp + finrank k ↥(Up ⊓ finAxis ep)
  hVm : 0 = km + finrank k ↥(Um ⊓ finAxis em)
  hVp' : a = kp + finrank k ↥(Up ⊓ singAxis em)
  hVm' : b = km + finrank k ↥(Um ⊓ singAxis ep)

theorem QuadSingleDims.result {s a b : ℕ} (X : QuadSingleDims (k := k) s a b) :
    a + b = s ∧ 0 < a ∧ 0 < b := by
  have h := bookkeeping_single_sign X.h2 X.ε X.hε X.J X.ep X.em X.hp X.hm X.he X.Up X.Um X.hUp
    X.hUm X.hdetp (K0p := Fin X.kp → k) (K0m := Fin X.km → k) (Vp := Fin s → k)
    (Vm := Fin 0 → k) (Vp' := Fin a → k) (Vm' := Fin b → k) s X.hs (by simp) (by simp)
    (by simpa using X.hVp) (by simpa using X.hVm) (by simpa using X.hVp') (by simpa using X.hVm')
  simp only [finrank_fin_fun] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- **A nonquadratic prime** (tex 4997–5003; core `relaxed_image_eq_span`): GLUE identification:
detection makes the relaxed localization image `U` the finite plane, and (5.5a) relates the old and
new fiber dimensions with a common `K_0` of dimension `k0`. -/
structure NonquadDims (s s' : ℕ) where
  U : Submodule k ((Fin 2 → k) × (Fin 2 → k))
  hU : U = finPlane k (Fin 2 → k) (Fin 2 → k)
  k0 : ℕ
  hs : s = k0 + finrank k ↥(U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k))
  hs' : s' = k0 + finrank k ↥(U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k))

theorem finrank_finPlane_two : finrank k (finPlane k (Fin 2 → k) (Fin 2 → k)) = 2 := by
  have : finPlane k (Fin 2 → k) (Fin 2 → k) =
      LinearMap.range (LinearMap.inl k (Fin 2 → k) (Fin 2 → k)) := by
    ext z; simp [mem_finPlane, LinearMap.mem_range]
    constructor
    · intro h; exact ⟨z.1, by ext <;> simp [h]⟩
    · rintro ⟨y, rfl⟩; rfl
  rw [this, LinearMap.finrank_range_of_inj LinearMap.inl_injective]; simp

theorem finPlane_inf_singPlane :
    finPlane k (Fin 2 → k) (Fin 2 → k) ⊓ singPlane k (Fin 2 → k) (Fin 2 → k) = ⊥ := by
  ext z; simp [mem_finPlane, mem_singPlane, Prod.ext_iff, and_comm]

theorem NonquadDims.drop {s s' : ℕ} (X : NonquadDims (k := k) s s') : s' + 2 = s := by
  have h1 := X.hs
  have h2 := X.hs'
  rw [X.hU, inf_idem, finrank_finPlane_two] at h1
  rw [X.hU, finPlane_inf_singPlane, finrank_bot] at h2
  omega

end Dims

/-! ### The switching data and the process -/

section Process

variable {A F k : Type*} [CommRing A] [Field F] [Field k]

/-- **One switch's coordinate data** (GLUE identification, tex 5137–5153): the old stage coordinate is
the finite coordinate and the new one the singular coordinate of a switch plane, with unit volume
normalizations in `R` and the sign `σ` coming from `R`. -/
structure CoordStep (ι : A →+* F) (u u' : F) where
  X : SwitchCoordData F
  mF : A
  mS : A
  σ₀ : A
  hmF : IsUnit mF
  hmS : IsUnit mS
  hμF : X.μF = ι mF
  hμS : X.μS = ι mS
  hσ₀ : X.σ = ι σ₀
  hu : u = X.uF
  hu' : u' = X.uS

/-- From the coordinate data, `u = w · u'` with `w = ι(−σ₀ m_F m_S⁻¹)` integral. PROVED. -/
theorem CoordStep.relation {ι : A →+* F} {u u' : F}
    (C : CoordStep ι u u') : ∃ c : A, u = ι c * u' := by
  obtain ⟨X, mF, mS, σ₀, hmF, hmS, hμF', hμS', hσ₀, hu, hu'⟩ := C
  subst hu hu'
  obtain ⟨mS', hmS'⟩ := hmS
  have hne : ∀ a : A, IsUnit a → ι a ≠ 0 := fun a ha h0 => by
    obtain ⟨b, rfl⟩ := ha
    have : ι (b * ↑b⁻¹) = 0 := by rw [map_mul, h0, zero_mul]
    rw [Units.mul_inv, map_one] at this
    exact one_ne_zero this
  have hμF : X.μF ≠ 0 := by rw [hμF']; exact hne _ hmF
  have hμS : X.μS ≠ 0 := by rw [hμS']; exact hne _ ⟨mS', hmS'⟩
  refine ⟨-σ₀ * mF * ↑mS'⁻¹, ?_⟩
  rw [X.uF_eq hμF hμS, hσ₀, hμF', hμS']
  congr 1
  have hinv : ι ↑mS'⁻¹ * ι mS = 1 := by rw [← hmS', ← map_mul, Units.inv_mul, map_one]
  have hmS0 : ι mS ≠ 0 := by rw [← hμS']; exact hμS
  rw [map_mul, map_mul, map_neg]
  field_simp
  linear_combination (ι σ₀ * ι mF) * hinv

/-- **The height-one switching data** at one height-one prime (tex 4976–5193), over the local ring
`A` (`= Λ_𝔭`) with fraction field embedding `ι` and residue map `ρ`. The stages carry genuine
two-term models; `sp, sm` are the sign dimensions of `H¹(C ⊗ k)` at a quadratic prime. The switch
fields are GLUE inputs whose types carry the hypotheses of RC16's cores (`CoordStep`,
`QuadMixedDims`, `QuadSingleDims`, `NonquadDims`).

Caveat: the stages are not tied to the genuine fibre models; a one-stage datum of fibre dimension 1
(no switch demanded) satisfies the structure (`exampleSwitchData`), so as a hypothesis it is
equivalent to its conclusion (compare RC's `regularityInputsS_iff`). Linking the stages to the
genuine fibre models is pending. -/
structure HeightOneSwitchData (ι : A →+* F) (ρ : A →+* k) where
  Stage : Type
  stage : Stage → TwoTermStage ι
  /-- Whether the specialization is quadratic (`𝔭 = (t)` or `(t+2)`). -/
  quadratic : Prop
  sp : Stage → ℕ
  sm : Stage → ℕ
  /-- GLUE (tex 5035–5054): the sign decomposition `H¹(C ⊗ k) = V₊ ⊕ V₋` at a quadratic prime. -/
  sign_sum : quadratic → ∀ S, sp S + sm S = (stage S).fiberDim ρ
  /-- tex 4986–4992, 5154–5157: a primitive integral cycle. -/
  primitive : ∀ S, ∃ i, ρ ((stage S).z i) ≠ 0
  /-- GLUE inputs for a switch when both signs occur (or nonquadratic), tex 4997–5003, 5116–5122,
  5137–5153. -/
  switch_mixed : ∀ S, (¬ quadratic ∨ (0 < sp S ∧ 0 < sm S)) → 1 < (stage S).fiberDim ρ →
    ∃ S', Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      (quadratic → Nonempty (QuadMixedDims (k := k) (sp S) (sm S) (sp S') (sm S'))) ∧
      (¬ quadratic →
        Nonempty (NonquadDims (k := k) ((stage S).fiberDim ρ) ((stage S').fiberDim ρ)))
  /-- GLUE inputs for a switch when one sign only occurs, tex 5123–5136, 5137–5153. -/
  switch_single : ∀ S, quadratic → ¬ (0 < sp S ∧ 0 < sm S) → 1 < (stage S).fiberDim ρ →
    ∃ S' a b, Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      Nonempty (QuadSingleDims (k := k) ((stage S).fiberDim ρ) a b) ∧
      ((sp S' = a ∧ sm S' = b) ∨ (sp S' = b ∧ sm S' = a))

/-- **The instance of RC16's `RegularitySwitchProcess`** built from the switching data, with
`Reg` any predicate containing `ι(A)` (tex 4976–5193). `pos` and `terminal` are proved from the
two-term models; the switch fields from the GLUE inputs through RC16's cores. PROVED. -/
def HeightOneSwitchData.toProcess [IsLocalRing A] {ι : A →+* F} (hι : Function.Injective ι)
    {ρ : A →+* k} (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (Reg : F → Prop)
    (hReg : ∀ a : A, Reg (ι a)) (P : HeightOneSwitchData ι ρ) : RegularitySwitchProcess Reg where
  Stage := P.Stage
  fiberDim S := (P.stage S).fiberDim ρ
  mixed S := ¬ P.quadratic ∨ (0 < P.sp S ∧ 0 < P.sm S)
  coord S := (P.stage S).u
  pos S := (P.stage S).one_le_fiberDim ρ (P.primitive S)
  switch_mixed S hmix hs := by
    obtain ⟨S', ⟨hC⟩, hQ, hN⟩ := P.switch_mixed S hmix hs
    obtain ⟨c, hc⟩ := hC.relation
    refine ⟨S', ?_, ι c, hReg c, hc⟩
    by_cases hq : P.quadratic
    · obtain ⟨Q⟩ := hQ hq
      have h := Q.drop
      rw [P.sign_sum hq S, P.sign_sum hq S'] at h
      exact h
    · obtain ⟨N⟩ := hN hq
      exact N.drop
  switch_single S hmix hs := by
    have hq : P.quadratic := by
      by_contra hq; exact hmix (Or.inl hq)
    have hns : ¬ (0 < P.sp S ∧ 0 < P.sm S) := fun h => hmix (Or.inr h)
    obtain ⟨S', a, b, ⟨hC⟩, ⟨hQ⟩, hab⟩ := P.switch_single S hq hns hs
    obtain ⟨c, hc⟩ := hC.relation
    obtain ⟨hsum, ha, hb⟩ := hQ.result
    refine ⟨S', ?_, Or.inr ?_, ι c, hReg c, hc⟩
    · rw [← P.sign_sum hq S']
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  terminal S h1 := by
    obtain ⟨u₀, hu₀⟩ := (P.stage S).coord_integral_of_fiberDim_one hι ρ hρ h1
    rw [← hu₀]; exact hReg u₀

/-- **Regularity of every stage coordinate** (tex 5154–5193), from RC16's
`regular_of_switchProcess` applied to the instance. PROVED. -/
theorem regular_of_switchData [IsLocalRing A] {ι : A →+* F} (hι : Function.Injective ι)
    {ρ : A →+* k} (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (P : HeightOneSwitchData ι ρ) (S : P.Stage) : ∃ a : A, ι a = (P.stage S).u := by
  have := regular_of_switchProcess (Reg := fun x : F => ∃ a : A, ι a = x)
    (fun x y ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
    (P.toProcess hι hρ (fun x => ∃ a : A, ι a = x) (fun a => ⟨a, rfl⟩)) S
  exact this

end Process

/-! ### The genuine `Λ_𝔭` inside `Frac Λ` -/

section Genuine

variable (P : Ideal Lambda) [P.IsPrime]

/-- The embedding `Λ_𝔭 → Frac Λ` (the map of RC16's `RegularAtPrime`). -/
abbrev toFracAt : Localization.AtPrime P →+* FractionRing Lambda :=
  (Localization.mapToFractionRing (FractionRing Lambda) P.primeCompl
    (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)).toRingHom

theorem toFracAt_injective : Function.Injective (toFracAt P) := by
  intro a b h
  simp only [toFracAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Localization.mapToFractionRing_apply] at h
  exact (IsLocalization.lift_injective_iff _).2 (fun x y =>
    ⟨fun hxy => congr_arg _ (IsLocalization.injective (Localization.AtPrime P)
      (Ideal.primeCompl_le_nonZeroDivisors P) hxy),
     fun hxy => congr_arg _ (IsFractionRing.injective Lambda (FractionRing Lambda) hxy)⟩) h

/-- **The height-one switching process over the genuine `Λ_𝔭`**, as an instance of RC16's
`RegularitySwitchProcess (RegularAtPrime 𝔭)`, from switching data over `Λ_𝔭` with residue map the
residue of the local ring `Λ_𝔭`. PROVED (from the GLUE inputs of `HeightOneSwitchData`). -/
def processAtPrime (D : HeightOneSwitchData (toFracAt P)
    (IsLocalRing.residue (Localization.AtPrime P))) : RegularitySwitchProcess (RegularAtPrime P) :=
  D.toProcess (toFracAt_injective P) (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx)
    (RegularAtPrime P) (fun a => ⟨a, rfl⟩)

/-- **The input shape of RC16's `mem_lambdaHalf_of_regularity`**: switching data over `Λ_𝔭` whose
starting stage has coordinate `u` give a switching process starting at `u`. PROVED. -/
theorem exists_process_of_switchData (u : FractionRing Lambda)
    (D : HeightOneSwitchData (toFracAt P) (IsLocalRing.residue (Localization.AtPrime P)))
    (S₀ : D.Stage) (hS₀ : (D.stage S₀).u = u) :
    ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = u :=
  ⟨processAtPrime P D, S₀, hS₀⟩

end Genuine

/-! ### Non-vacuity -/

section Example

/-- The one-stage two-term model `[ℚ --0--> ℚ]` with cycle `1`, functional `1` and coordinate `1`
(`ι = ρ = id` on the field `ℚ`, a local ring). -/
def exampleStage : TwoTermStage (RingHom.id ℚ) where
  n := 0
  D := 0
  z := fun _ => 1
  w := fun _ => 1
  u := 1
  hz := by simp
  hw := by simp
  hu := by
    unfold IsClassFunctionalCoord
    rw [adjugate_fin_one]
    ext i j; fin_cases i; fin_cases j; simp [vecMulVec]

theorem exampleStage_fiberDim : exampleStage.fiberDim (RingHom.id ℚ) = 1 := by
  have h0 : (exampleStage.D.map (RingHom.id ℚ)).mulVecLin = 0 := by
    apply LinearMap.ext; intro v; ext i
    simp [exampleStage]; rfl
  rw [TwoTermStage.fiberDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

/-- **Non-vacuity of `HeightOneSwitchData`**: a single stage of fiber dimension one (no switch
needed), nonquadratic. PROVED. -/
def exampleSwitchData : HeightOneSwitchData (RingHom.id ℚ) (RingHom.id ℚ) where
  Stage := Unit
  stage _ := exampleStage
  quadratic := False
  sp _ := 0
  sm _ := 0
  sign_sum h := h.elim
  primitive _ := ⟨0, by simp [exampleStage]⟩
  switch_mixed _ _ hs := by rw [exampleStage_fiberDim] at hs; omega
  switch_single _ h := h.elim

/-- The process built from the example data has its terminal coordinate `1` regular. PROVED. -/
theorem exampleSwitchData_regular :
    ∃ a : ℚ, RingHom.id ℚ a = (exampleSwitchData.stage ()).u :=
  regular_of_switchData (fun _ _ h => h) (fun x hx => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hx
    simp [hx]) exampleSwitchData ()

end Example

end ZInQ.Contrib.CloudB3RC53.UniformSwitch
