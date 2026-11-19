import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.QuadWiring
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Lambda

/-!
# RC53 SwitchInputs: the Galois switching data, non-vacuity analysis and the quadratic steps

Height-one regularity by switches, Proposition `ex:limits-uniform-lower-bound`, tex L4976–5195.

**Part A (non-vacuity for `GaloisNonquadInputs`, `GaloisWiring.lean`).** The genuine Galois family
of `GaloisWiring.lean` has coefficients `𝔽₂` (`ZMod 2`). Two facts limit it:

* `isEmpty_ringHom_zmod_two_of_isUnit`, `isEmpty_ringHom_zmod_two_heightOne` (PROVED): if `2` is a
  unit of `A` there is no ring map `A → 𝔽₂`; at every height-one prime `𝔭 ≠ (2)` of `Λ = ℤ₂[[t]]`,
  `2` is a unit of `Λ_𝔭`. So `GaloisNonquadInputs` (whose residue map is `ρ : A →+* ZMod 2`) can
  never be applied with `A = Λ_𝔭`, `𝔭 ≠ (2)`, the primes at which Elliot's switching argument runs
  (tex L4976: `R = Λ_𝔭`, `k = Frac(Λ/𝔭)` of characteristic zero). **Finding (modelling, not a
  manuscript error):** the genuine wiring must be redone over a residue field of characteristic
  `≠ 2` (coefficient modules over `k(𝔭)`, tame coordinates over `k(𝔭)`); the `𝔽₂` wiring is only the
  residual level.
* `GaloisSwitchData.not_quadratic_of_two_eq_zero`, `isEmpty_quasiMixedStep_of_two_eq_zero`,
  `isEmpty_quasiSingleStep_of_two_eq_zero` (PROVED): over a field with `2 = 0` no switching data is
  quadratic and no quadratic step exists, so the quadratic steps cannot be wired over `𝔽₂` at all.
* `GaloisSwitchData.one_le_h1` (PROVED): every Galois switching datum, hence (through
  `GaloisNonquadInputs.toGaloisSwitchData`) every instance of `GaloisNonquadInputs`, forces `dim H¹`
  of the genuine actual fibre to be at least one (primitivity plus the stage model). So an instance
  needs an explicit computation of the continuous Galois cohomology of the genuine fibre, which the
  library does not provide (the zero-coefficient family has no data at all:
  `GaloisFamily.no_genuineSwitchData_of_zAct_zero`).

**Part B (the quadratic steps, over any field `k`).** `MixedCandidates` / `SingleCandidates`: at a
configuration `c`, candidate quadratic switch data at every prime `p` (sides equal to the fibres of
`c` and `next c p`, duality from Selmer duality with `σ = 1`, equivariant fibre isomorphisms,
nonzero sign classes, the other team's detecting-prime existence, a `CoordStep` for every
candidate). `GaloisQuadInputs Φ ι ρ u` is `GaloisSwitchData` with the quadratic steps given by
candidates; `GaloisQuadInputs.toGaloisSwitchData` (PROVED) chooses the prime by
`exists_detectingPrime` / `exists_detectingPrimePlus`, and `regular_of_galoisQuadInputs` gives
regularity. Non-vacuity: `GaloisQuadInputs.ofNonquadratic` and the instance `exGaloisQuadInputs`
(nonquadratic family); a quadratic instance needs candidates with `DualityFromSelmer` at every
prime, not built here.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.Uniform.QuadraticCase ZInQ.Manuscript.RC.SelmerComplex NumberField
  IsDedekindDomain

/-! ### Part A: characteristic two -/

/-- **No residue map to `𝔽₂` when `2` is a unit.** PROVED. -/
theorem isEmpty_ringHom_zmod_two_of_isUnit {A : Type*} [CommRing A] (h : IsUnit (2 : A)) :
    IsEmpty (A →+* ZMod 2) :=
  ⟨fun f => by
    have h' := h.map f
    rw [map_ofNat] at h'
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20] at h'
    exact not_isUnit_zero h'⟩

/-- **At a height-one prime `𝔭 ≠ (2)` of `Λ` there is no residue map `Λ_𝔭 → 𝔽₂`** (tex L4976: the
switching runs at such primes, with residue field of characteristic zero). PROVED. -/
theorem isEmpty_ringHom_zmod_two_heightOne (p : Ideal Lam) [p.IsPrime] (hp : p.height = 1)
    (hne : p ≠ Ideal.span {(2 : Lam)}) : IsEmpty (Localization.AtPrime p →+* ZMod 2) := by
  apply isEmpty_ringHom_zmod_two_of_isUnit
  have h := (activeInertiaUnit_proof p hp hne).2.1
  rwa [map_ofNat] at h

section CharTwo

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]
  {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **Over a field with `2 = 0` no Galois switching data is quadratic.** PROVED. -/
theorem GaloisSwitchData.not_quadratic_of_two_eq_zero (G : GaloisSwitchData Φ ι ρ u)
    (h : (2 : k) = 0) : ¬ Φ.quadratic ρ :=
  fun hq => G.h2 hq h

/-- **Over a field with `2 = 0` there is no mixed quadratic step.** PROVED. -/
theorem isEmpty_quasiMixedStep_of_two_eq_zero (h : (2 : k) = 0) {S S' : TwoTermStage ι}
    (σS : fiberH1 ρ S →ₗ[k] fiberH1 ρ S) (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S') :
    IsEmpty (QuasiMixedStep ρ S S' σS σS') :=
  ⟨fun M => M.h2 h⟩

/-- **Over a field with `2 = 0` there is no single-sign quadratic step.** PROVED. -/
theorem isEmpty_quasiSingleStep_of_two_eq_zero (h : (2 : k) = 0) {S S' : TwoTermStage ι}
    (σS' : fiberH1 ρ S' →ₗ[k] fiberH1 ρ S') : IsEmpty (QuasiSingleStep ρ S S' σS') :=
  ⟨fun M => M.h2 h⟩

end CharTwo

/-! ### Part A: Galois switching data force genuine cohomology -/

section Forces

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]
  {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **Galois switching data force nonzero genuine `H¹`** (non-vacuity analysis): the actual fibre's
Selmer complex has `dim H¹ ≥ 1`, equal to the actual stage's fibre dimension. Applied to
`GaloisNonquadInputs.toGaloisSwitchData` (`GaloisWiring.lean`) over the genuine family `galΦ`, an
instance of `GaloisNonquadInputs` requires an explicit computation of continuous Galois cohomology
of the genuine fibre. PROVED. -/
theorem GaloisSwitchData.one_le_h1 (G : GaloisSwitchData Φ ι ρ u) :
    1 ≤ finrank k ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) := by
  rw [← G.fiberDim_eq Φ.actual]
  exact TwoTermStage.one_le_fiberDim ρ _ (G.primitive Φ.actual Reach.start)

end Forces

/-! ### Part B: the quadratic steps over any field -/

section Quad

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **Candidate mixed quadratic switch data at a configuration `c`** (tex L5003–5122): at every
prime `p`, a quasi quadratic switch whose sides are the fibres of `c` and `next c p`, with the
duality from Selmer duality (`σ = 1`), equivariant fibre isomorphisms, nonzero sign classes of the
old fibre, the detecting-prime existence (GLUE, the other team's `DetectingPrimeExists`) and a
`CoordStep` for every candidate. -/
structure MixedCandidates (Φ : SwitchFamily k A) {ι : A →+* F} (ρ : A →+* k)
    (stage : Φ.Config → TwoTermStage ι)
    (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)) (c : Φ.Config) where
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  hJ2 : J ∘ₗ J = LinearMap.id
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  X : Φ.Prime → QuasiQuadSwitch k J
  hF : ∀ p, (X p).SF.Dside = Φ.fibre c
  hS : ∀ p, (X p).SS.Dside = Φ.fibre (Φ.next c p)
  D : ∀ p, DualityFromSelmer (X p).R
  hDε : ∀ p, (D p).ε = ε
  hDσ : ∀ p, (D p).σ = 1
  hDJ : ∀ p, Matrix.toLin' (D p).J = J
  φ : ∀ p, (selCx (X p).SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (stage c)
  hφ : ∀ p, (φ p).toLinearMap ∘ₗ (X p).σV = σ c ∘ₗ (φ p).toLinearMap
  φ' : ∀ p, (selCx (X p).SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (stage (Φ.next c p))
  hφ' : ∀ p, (φ' p).toLinearMap ∘ₗ (X p).σV' = σ (Φ.next c p) ∘ₗ (φ' p).toLinearMap
  cp : fiberH1 ρ (stage c)
  cm : fiberH1 ρ (stage c)
  hp0 : cp ≠ 0
  hm0 : cm ≠ 0
  hcp : σ c cp = cp
  hcm : σ c cm = -cm
  hex : DetectingPrimeExists (σ c) (fun p => (X p).R.lamQ ∘ₗ H1 (changeMap (X p).R.D (X p).SF.f₁) ∘ₗ
    (φ p).symm.toLinearMap) cp cm
  coord : ∀ p, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u)

/-- **Candidate single-sign quadratic switch data at a configuration `c`** (tex L5123–5136). -/
structure SingleCandidates (Φ : SwitchFamily k A) {ι : A →+* F} (ρ : A →+* k)
    (stage : Φ.Config → TwoTermStage ι)
    (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)) (c : Φ.Config) where
  ε : k
  hε : ε ≠ 0
  J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)
  hJ2 : J ∘ₗ J = LinearMap.id
  ep : Fin 2 → k
  em : Fin 2 → k
  hp : J ep = ep
  hm : J em = -em
  he : e₂ ep em ≠ 0
  X : Φ.Prime → QuasiQuadSwitch k J
  hF : ∀ p, (X p).SF.Dside = Φ.fibre c
  hS : ∀ p, (X p).SS.Dside = Φ.fibre (Φ.next c p)
  D : ∀ p, DualityFromSelmer (X p).R
  hDε : ∀ p, (D p).ε = ε
  hDσ : ∀ p, (D p).σ = 1
  hDJ : ∀ p, Matrix.toLin' (D p).J = J
  φ : ∀ p, (selCx (X p).SF.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (stage c)
  hφ : ∀ p, (φ p).toLinearMap ∘ₗ (X p).σV = σ c ∘ₗ (φ p).toLinearMap
  φ' : ∀ p, (selCx (X p).SS.Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (stage (Φ.next c p))
  hφ' : ∀ p, (φ' p).toLinearMap ∘ₗ (X p).σV' = σ (Φ.next c p) ∘ₗ (φ' p).toLinearMap ∨
    (φ' p).toLinearMap ∘ₗ (X p).σV' = (-σ (Φ.next c p)) ∘ₗ (φ' p).toLinearMap
  hs1 : ∀ p, 1 < finrank k ↥(signPart (X p).σV (1 : k))
  hs0 : ∀ p, 0 = finrank k ↥(signPart (X p).σV (-1 : k))
  cp : fiberH1 ρ (stage c)
  hp0 : cp ≠ 0
  hcp : σ c cp = cp
  hex : DetectingPrimePlusExists (σ c) (fun p => (X p).R.lamQ ∘ₗ
    H1 (changeMap (X p).R.D (X p).SF.f₁) ∘ₗ (φ p).symm.toLinearMap) cp
  coord : ∀ p, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u)

/-- **Galois switching inputs with quadratic steps from candidates** (tex L4976–5195): as
`GaloisSwitchData`, but each quadratic switch is given by candidate data at all primes, the prime
being chosen by the detecting-prime existence. -/
structure GaloisQuadInputs (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) where
  stage : Φ.Config → TwoTermStage ι
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i)
  hw0 : ∀ y, Φ.lamAct y =
    (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ (((model Φ.actual).hom.f 2).hom y : Fin _ → k)
  hu0 : (stage Φ.actual).u = u
  σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)
  h2 : Φ.quadratic ρ → (2 : k) ≠ 0
  hσ : Φ.quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id
  primitive : ∀ c, Reach Φ.next Φ.actual c → ∃ i, ρ ((stage c).z i) ≠ 0
  nonquad : ∀ c, Reach Φ.next Φ.actual c → ¬ Φ.quadratic ρ → 1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ N : QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)),
        N.SF.Dside = Φ.fibre c ∧ N.SS.Dside = Φ.fibre (Φ.next c p)
  mixed : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
    (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ → MixedCandidates Φ ρ stage σ c
  single : ∀ c, Reach Φ.next Φ.actual c → Φ.quadratic ρ →
    ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ → SingleCandidates Φ ρ stage σ c

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **The mixed step at the detected prime.** PROVED. -/
theorem MixedCandidates.exists_step {stage : Φ.Config → TwoTermStage ι}
    {σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)} {c : Φ.Config}
    (C : MixedCandidates Φ ρ stage σ c) (h2 : (2 : k) ≠ 0) :
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ M : QuasiMixedStep ρ (stage c) (stage (Φ.next c p)) (σ c) (σ (Φ.next c p)),
        M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p) := by
  obtain ⟨q, hq⟩ := exists_detectingPrime C.hex C.hp0 C.hm0 C.hcp C.hcm
  have hsym : ∀ x, (C.X q).σV ((C.φ q).symm x) = (C.φ q).symm (σ c x) := by
    intro x
    apply (C.φ q).injective
    have := LinearMap.congr_fun (C.hφ q) ((C.φ q).symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [LinearEquiv.apply_symm_apply, this]
  have hcp' : (C.X q).σV ((C.φ q).symm C.cp) = (C.φ q).symm C.cp := by rw [hsym, C.hcp]
  have hcm' : (C.X q).σV ((C.φ q).symm C.cm) = -(C.φ q).symm C.cm := by
    rw [hsym, C.hcm, map_neg]
  have hU : ∀ u, u ∈ (C.X q).R.U ↔ ∀ w ∈ (C.X q).R.U, localPair C.ε C.J u w = 0 := by
    have h := hU_of_dualityFromSelmer (C.D q) (C.hDσ q)
    rw [C.hDε q, C.hDJ q] at h
    exact h
  exact ⟨q, C.coord q, ⟨h2, C.ε, C.hε, C.J, C.hJ2, C.ep, C.em, C.hp, C.hm, C.he, C.X q, hU,
    (C.φ q).symm C.cp, (C.φ q).symm C.cm, hcp', hcm', fun _ _ => hq C.hcp C.hcm, C.φ q, C.hφ q,
    C.φ' q, C.hφ' q⟩, C.hF q, C.hS q⟩

/-- **The single-sign step at the detected prime.** PROVED. -/
theorem SingleCandidates.exists_step {stage : Φ.Config → TwoTermStage ι}
    {σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)} {c : Φ.Config}
    (C : SingleCandidates Φ ρ stage σ c) (h2 : (2 : k) ≠ 0) :
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ M : QuasiSingleStep ρ (stage c) (stage (Φ.next c p)) (σ (Φ.next c p)),
        M.X.SF.Dside = Φ.fibre c ∧ M.X.SS.Dside = Φ.fibre (Φ.next c p) := by
  obtain ⟨q, hq⟩ := exists_detectingPrimePlus C.hex C.hp0 C.hcp
  have hcp' : (C.X q).σV ((C.φ q).symm C.cp) = (C.φ q).symm C.cp := by
    apply (C.φ q).injective
    have := LinearMap.congr_fun (C.hφ q) ((C.φ q).symm C.cp)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    rw [LinearEquiv.apply_symm_apply, this, C.hcp]
  have hU : ∀ u, u ∈ (C.X q).R.U ↔ ∀ w ∈ (C.X q).R.U, localPair C.ε C.J u w = 0 := by
    have h := hU_of_dualityFromSelmer (C.D q) (C.hDσ q)
    rw [C.hDε q, C.hDJ q] at h
    exact h
  exact ⟨q, C.coord q, ⟨h2, C.ε, C.hε, C.J, C.hJ2, C.ep, C.em, C.hp, C.hm, C.he, C.X q, hU,
    (C.φ q).symm C.cp, hcp', fun _ => hq C.hcp, C.hs1 q, C.hs0 q, C.φ q, C.φ' q, C.hφ' q⟩,
    C.hF q, C.hS q⟩

/-- **Galois switching data from the quadratic inputs** (tex L4976–5195): the nonquadratic steps are
taken as given; each quadratic step is the step at the prime chosen by the detecting-prime
existence among the candidates. PROVED. -/
noncomputable def GaloisQuadInputs.toGaloisSwitchData (X : GaloisQuadInputs Φ ι ρ u) :
    GaloisSwitchData Φ ι ρ u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  σ := X.σ
  h2 := X.h2
  hσ := X.hσ
  primitive := X.primitive
  switch_mixed c hc hor h1 := by
    by_cases hq : Φ.quadratic ρ
    · have hboth := hor.resolve_left (not_not.mpr hq)
      obtain ⟨p, hcs, M, hF, hS⟩ := (X.mixed c hc hq hboth h1).exists_step (X.h2 hq)
      exact ⟨p, hcs, fun _ => ⟨M, hF, hS⟩, fun hnq => absurd hq hnq⟩
    · obtain ⟨p, hcs, N, hF, hS⟩ := X.nonquad c hc hq h1
      exact ⟨p, hcs, fun h => absurd h hq, fun _ => ⟨N, hF, hS⟩⟩
  switch_single c hc hq hnb h1 := (X.single c hc hq hnb h1).exists_step (X.h2 hq)

/-- **Regularity from the quadratic Galois switching inputs** (tex L4976–5195). PROVED (from the
inputs). -/
theorem regular_of_galoisQuadInputs [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (X : GaloisQuadInputs Φ ι ρ u) :
    ∃ a : A, ι a = u :=
  regular_of_galoisSwitchData' hι hρ X.toGaloisSwitchData

/-- **Nonquadratic Galois switching data are quadratic inputs** (the quadratic fields are vacuous).
PROVED. -/
noncomputable def GaloisQuadInputs.ofNonquadratic (G : GaloisSwitchData Φ ι ρ u)
    (hnq : ¬ Φ.quadratic ρ) : GaloisQuadInputs Φ ι ρ u where
  stage := G.stage
  model := G.model
  hz0 := G.hz0
  hw0 := G.hw0
  hu0 := G.hu0
  σ := G.σ
  h2 := G.h2
  hσ := G.hσ
  primitive := G.primitive
  nonquad c hc hq h1 := by
    obtain ⟨p, hcs, -, hN⟩ := G.switch_mixed c hc (Or.inl hq) h1
    exact ⟨p, hcs, hN hq⟩
  mixed _ _ hq := absurd hq hnq
  single _ _ hq := absurd hq hnq

end Quad

/-! ### Non-vacuity -/

/-- The example family of `GenuineSwitch.lean` is nonquadratic. PROVED. -/
theorem exGenuineFamily_not_quadratic : ¬ exGenuineFamily.quadratic (RingHom.id ℚ) := by
  simp only [SwitchFamily.quadratic, exGenuineFamily, RingHom.id_apply]
  norm_num

/-- **Non-vacuity of `GaloisQuadInputs`**: the example Galois switching data as quadratic inputs.
PROVED. -/
noncomputable def exGaloisQuadInputs :
    GaloisQuadInputs exGenuineFamily (RingHom.id ℚ) (RingHom.id ℚ) 1 :=
  GaloisQuadInputs.ofNonquadratic exGaloisSwitchData exGenuineFamily_not_quadratic

theorem exGaloisQuad_regular : ∃ a : ℚ, RingHom.id ℚ a = 1 :=
  regular_of_galoisQuadInputs Function.injective_id (fun x hx => by simpa using hx)
    exGaloisQuadInputs

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
