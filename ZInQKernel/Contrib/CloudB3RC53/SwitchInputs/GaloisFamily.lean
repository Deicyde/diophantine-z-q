import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSwitch
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.QuasiSide
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints

/-!
# RC53 SwitchInputs: the switching family over the genuine Galois Selmer complexes

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L4976–5195. The genuine
height-one switching data `GenuineSwitchData` (`GenuineSwitch.lean`) work over a configuration family
`SwitchFamily` fixed as a parameter; there its fibres were SelmerSES-style Selmer data (a recorded
DEPARTURE). This file builds the family from the genuine Galois Selmer data `galoisSelData` of the
Selmer-complex lane (continuous cochains of `G_{K,S}` and of the local groups `G_{K_v}`,
`RC/SelmerComplex/Galois.lean`), removing that departure.

* `condAt Δ₀ Δd c`: the genuine local conditions of a configuration `c` (a finite set of places of `S`
  used as derivative primes): the derivative condition `Δd` at `v ∈ c` and the base condition `Δ₀`
  elsewhere (tex L5068–5072: the new prime receives `D⁰ ⊕ (F ⊕ S)[−1]` or its finite/singular
  variant; all other conditions are retained).
* `galoisSwitchFamily`: the `SwitchFamily` with configurations `Finset (Places K S)`, `next c p =
  insert p c`, fibres `galoisSelData K S k M (condAt Δ₀ Δd c)`, and the actual class and paired
  functional as genuine cochains with their cocycle and closedness equations. PROVED (a definition;
  every field is genuine data).
* `regular_of_galoisSwitchData`, `galois_collapse_forces`: regularity and the collapse check
  (a fibre-dimension-one datum forces the genuine `H¹` of the actual Galois Selmer complex to have
  dimension one) for `GenuineSwitchData` over the genuine family. PROVED.
* `no_genuineSwitchData_of_zAct_zero`: no genuine switching datum exists over a family whose actual
  class is zero (the starting stage's primitive cycle must be the image of the actual class).
  PROVED — the starting link is a genuine condition, not a free choice.
* `quasiSwitchSideDims_of_h1Finite`: the (5.5a) dimension count for `QuasiSwitchSide` with
  finite-dimensionality required only of the cohomology `H¹(C(U₁))`, not of the cochain modules.
  PROVED. FINDING: the genuine continuous cochain modules `C¹_cont(G_{K,S}, M)` are not
  finite-dimensional, so the cochain-level `FiniteDimensional` hypotheses of `SwitchSide`,
  `QuasiSwitchSide`'s `quasiSwitchDims_of_selmerData` and the model steps cannot hold for
  `galoisSelData`; the homology-level version is the one that applies (finiteness of `H¹` is the
  finiteness of Galois cohomology).

GLUE that remains for the genuine family (stated in the types where it is consumed):
* the identification of the genuine derivative local conditions `Δd` with the cochain-level finite
  and singular planes `F`, `S` (the local computation at an inert prime, tex L5027–5037);
* the stage homotopy equivalences `selCx (galoisSelData …) ≃ twoTermFiberComplex ρ (stage c)` (the
  minimal models of the genuine fibres, tex L4976–4996), and the switch steps of `GenuineSwitchData`
  (whose model-step bundles are still stated over SelmerSES-style sides with cochain-level
  finiteness; their quasi, homology-level versions are not yet wired).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality Module
  ZInQ.Manuscript.RC.Uniform

section Family

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

open Classical in
/-- The local condition at `v` for configuration `c`: the derivative condition at derivative primes
`v ∈ c`, the base condition elsewhere (as a pair of the condition complex and its map to the local
cochains). -/
def condPair (Δ₀ Δd : GaloisLocalConditions K S k M) (c : Finset (Places K S)) (v : Places K S) :
    Σ U : GCx k, GHom U (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) M v) :=
  if v ∈ c then ⟨Δd.U v, Δd.i v⟩ else ⟨Δ₀.U v, Δ₀.i v⟩

/-- **The genuine local conditions of a configuration** (tex L5068–5072). -/
def condAt (Δ₀ Δd : GaloisLocalConditions K S k M) (c : Finset (Places K S)) :
    GaloisLocalConditions K S k M :=
  ⟨fun v => (condPair K S k M Δ₀ Δd c v).1, fun v => (condPair K S k M Δ₀ Δd c v).2⟩

open Classical in
/-- **The switching family over the genuine Galois Selmer complexes** (tex L4976–5195):
configurations are finite sets of derivative places, `next c p = insert p c`, the fibre of `c` is the
genuine Selmer data `galoisSelData K S k M (condAt Δ₀ Δd c)`, `actual = c₀`, and the actual class and
paired functional are genuine cochains of the actual fibre with their cocycle / closedness equations.
-/
def galoisSwitchFamily (A : Type) [CommRing A] (Δ₀ Δd : GaloisLocalConditions K S k M)
    (c₀ : Finset (Places K S)) (t : A)
    (zAct : (selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.X 1)
    (hzAct : ((selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.d 1 2).hom zAct = 0)
    (lamAct : (selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.X 2 →ₗ[k] k)
    (hlamAct : ∀ y, lamAct
      (((selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.d 1 2).hom y) = 0) :
    SwitchFamily k A where
  Config := Finset (Places K S)
  Prime := Places K S
  actual := c₀
  next c p := insert p c
  fibre c := galoisSelData K S k M (condAt K S k M Δ₀ Δd c)
  t := t
  zAct := zAct
  hzAct := hzAct
  lamAct := lamAct
  hlamAct := hlamAct

end Family

/-! ### Regularity and the collapse check over the genuine family -/

/-- **Regularity over the genuine Galois family** (tex L4976–5195): a `GenuineSwitchData` over the
family of genuine Galois Selmer complexes gives `∃ a, ι a = u`. Classification: PROVED (from the
inputs of the datum). -/
theorem regular_of_galoisSwitchData {k A F : Type} [Field k] [CommRing A] [IsLocalRing A] [Field F]
    (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (G : GenuineSwitchData Φ ι ρ u) :
    ∃ a : A, ι a = u :=
  regular_of_genuineSwitchData k A F Φ ι ρ u hι hρ G


section Collapse

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [Field k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
  {A F : Type} [CommRing A] [Field F] (Δ₀ Δd : GaloisLocalConditions K S k M)
  (c₀ : Finset (Places K S)) (t : A)
  (zAct : (selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.X 1)
  (hzAct : ((selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.d 1 2).hom zAct = 0)
  (lamAct : (selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.X 2 →ₗ[k] k)
  (hlamAct : ∀ y, lamAct
    (((selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.d 1 2).hom y) = 0)

/-- **The collapse check over the genuine Galois family**: a genuine switching datum
over `galoisSwitchFamily` whose starting stage has fibre dimension one forces the genuine first
cohomology of the actual Galois Selmer complex `galoisSelData K S k M (condAt Δ₀ Δd c₀)` to have
dimension one. Classification: PROVED. -/
theorem galois_collapse_forces (ι : A →+* F) (ρ : A →+* k) (u : F)
    (G : GenuineSwitchData (galoisSwitchFamily K S k M A Δ₀ Δd c₀ t zAct hzAct lamAct hlamAct)
      ι ρ u)
    (h : (G.stage c₀).fiberDim ρ = 1) :
    finrank k ((selCx (galoisSelData K S k M (condAt K S k M Δ₀ Δd c₀))).toCC.homology 1) = 1 := by
  have h' := G.fiberDim_eq c₀
  rw [h] at h'
  exact h'.symm

end Collapse

/-- **The starting link is genuine**: over any family whose actual class is zero there is no
genuine switching datum — the starting stage's cycle must be the image of the actual class
(`hz0`), while it must have a nonzero reduction (`primitive`, tex L4986–4992). Classification:
PROVED. -/
theorem no_genuineSwitchData_of_zAct_zero {k A F : Type} [Field k] [CommRing A] [Field F]
    (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) (hz : Φ.zAct = 0) :
    IsEmpty (GenuineSwitchData Φ ι ρ u) := by
  refine ⟨fun G => ?_⟩
  obtain ⟨i, hi⟩ := G.primitive Φ.actual Reach.start
  have h0 := congrFun G.hz0 i
  rw [hz, map_zero] at h0
  exact hi h0.symm

/-! ### (5.5a) with homology-level finiteness -/

/-- **(5.5a) for one quasi side, with finiteness only on cohomology** (tex L5055–5086): for a quasi
switch side whose `H¹(C(U₁))` is finite-dimensional, `dim H¹(C(U₁)) = dim H¹(C(U_str)) + dim(U ⊓ P)`.
The genuine continuous cochain modules are not finite-dimensional; this is the form that applies to
`galoisSelData`. Classification: PROVED. -/
theorem quasiSwitchSideDims_of_h1Finite {k : Type} [Field k] (R : QuasiRelaxedLocalization k)
    (P : Submodule k ((Fin 2 → k) × (Fin 2 → k))) (S : QuasiSwitchSide R P)
    (hfinCf : FiniteDimensional k ((selCx S.Dside).toCC.homology 1)) :
    finrank k ((selCx S.Dside).toCC.homology 1) =
      finrank k ((selCx S.Dstr).toCC.homology 1) + finrank k ↥(R.U ⊓ P) := by
  have hfinWr : FiniteDimensional k (R.Wrel.toCC.homology 1) :=
    LinearEquiv.finiteDimensional R.eR.symm
  have hdims := switchDimsOfSES_proof.{0} k _ _ _ _ _ _ _ _ _ _ _ _ _
    (changeSES S.Dside S.fs S.g₁ S.hfg₁).zero (changeSES R.D S.f₁ S.g₂ S.hfg₂).zero
    S.ses₁ S.ses₂ S.comm_lam S.fac_p S.h0 S.hi S.hpi hfinCf hfinWr
  have hdims' : finrank k ((selCx S.Dside).toCC.homology 1) =
      finrank k ((selCx S.Dstr).toCC.homology 1) +
        finrank k ↥(LinearMap.range (H1 (quotMap R.D R.gR)) ⊓ LinearMap.range (H1 S.i)) := hdims
  rw [hdims']
  congr 1
  conv_rhs => rw [QuasiRelaxedLocalization.U, ← S.hP, ← Submodule.map_inf _ R.eR.injective]
  exact ((Submodule.equivMapOfInjective _ R.eR.injective _).finrank_eq)

/-- **Both (5.5a) equations with homology-level finiteness**: the `hs`, `hs'` shapes of
`NonquadDims` for quasi sides whose side cohomologies are finite-dimensional. PROVED. -/
theorem quasiSwitchDims_of_h1Finite {k : Type} [Field k] (R : QuasiRelaxedLocalization k)
    (SF : QuasiSwitchSide R (finPlane k (Fin 2 → k) (Fin 2 → k)))
    (SS : QuasiSwitchSide R (singPlane k (Fin 2 → k) (Fin 2 → k)))
    (hF : FiniteDimensional k ((selCx SF.Dside).toCC.homology 1))
    (hS : FiniteDimensional k ((selCx SS.Dside).toCC.homology 1)) :
    finrank k ((selCx SF.Dside).toCC.homology 1) = finrank k ((selCx SF.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ finPlane k (Fin 2 → k) (Fin 2 → k)) ∧
    finrank k ((selCx SS.Dside).toCC.homology 1) = finrank k ((selCx SS.Dstr).toCC.homology 1) +
        finrank k ↥(R.U ⊓ singPlane k (Fin 2 → k) (Fin 2 → k)) :=
  ⟨quasiSwitchSideDims_of_h1Finite R _ SF hF, quasiSwitchSideDims_of_h1Finite R _ SS hS⟩

/-! ### Non-vacuity of the family (non-vacuity) -/

section NonVacuity

instance trivMod_continuousAdd (G V : Type) [AddCommGroup V] [TopologicalSpace V]
    [ContinuousAdd V] : ContinuousAdd (TrivMod G V) :=
  inferInstanceAs (ContinuousAdd V)

instance trivMod_continuousConstSMul (G V R : Type) [Semiring R] [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [ContinuousConstSMul R V] : ContinuousConstSMul R (TrivMod G V) :=
  inferInstanceAs (ContinuousConstSMul R V)

/-- **The genuine Galois family exists** (non-vacuity): over `ℚ` with no places, coefficients `k = ℚ`,
module `M = ℚ` with the trivial action, the strict conditions as base and derivative conditions,
the actual configuration `∅`, the actual class `0` and functional `0`. Every field is genuine Galois
data; by `no_genuineSwitchData_of_zAct_zero` no switching datum over this particular family exists,
so the family alone does not make `GenuineSwitchData` inhabited. -/
def exGaloisSwitchFamily : SwitchFamily ℚ ℚ :=
  galoisSwitchFamily ℚ (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ (TrivMod (GKS ℚ ∅) ℚ) ℚ
    (strictConditions ℚ _ _ _ _) (strictConditions ℚ _ _ _ _) ∅ 1 0 (map_zero _) 0
    (fun _ => rfl)

theorem exGaloisSwitchFamily_empty (ι : ℚ →+* ℚ) (ρ : ℚ →+* ℚ) (u : ℚ) :
    IsEmpty (GenuineSwitchData exGaloisSwitchFamily ι ρ u) :=
  no_genuineSwitchData_of_zAct_zero _ ι ρ u rfl

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
