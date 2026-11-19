import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericCoords
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GaloisWiringQuad

/-!
# RC53 SwitchInputs: the field-generic derivative sides wired into the Galois switching family

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L4976–5195, with the switch
exact sequences (5.5a), tex L5055–5086, and the derivative conditions, tex L5060–5061.

Field-generic restatement of `GaloisWiring.lean` (whose genuine instances have coefficients `𝔽₂`
and do not apply at the height-one primes `𝔭 ≠ (2)` where switching runs,
`isEmpty_ringHom_zmod_two_heightOne`). Here `k` is an arbitrary field and `M` any topological
`k`-module with a continuous action of `G_{K,S}`; no finiteness and no discreteness of `M` is
assumed (the fibres `V_𝔭 = k(𝔭) ⊗ T₂E` have neither). The local complexes are the genuine
`galLv (k := k) K S M`, the Selmer data are `galoisSelData K S k M (condAt …)`, so the Λ-adic fibres
instantiate the chain with `k = k(𝔭)`, `M = V_𝔭` directly (`GenericAtFibre.lean`).

Nodes:
* `gGvK`, `gMvK`, `locCxK_eq_galLv` (PROVED, `rfl`): with `G_v = Gloc K v` and
  `M_v = ResMod (locMap v) M`, the local complexes of `GenericCoords` are `galLv (k := k) K S M`.
* `condFamK`, `condAt_galCondK` (PROVED): the configuration conditions `condAt Δ₀ Δ_d c` of
  `GaloisFamily` are `galCond` of the family `condFamK A₀ A_d c`.
* `PlaceTameK` (data: inertia `I_v`, Frobenius lift `φ_v`, tame generator `σ_v`), its derivative
  sides `PlaceTameK.finCond`, `PlaceTameK.singCond`; `SwitchCondsK` (tame data and arbitrary finite
  / singular conditions `A₀ v`, `A_d v` at the places, e.g. the unramified conditions of the Λ-adic
  fibres), `SwitchCondsK.AdmissibleAt q` (at the switch place the conditions are the derivative
  sides), `PlaceTameK.std` (the standard choice, admissible everywhere); `finSwitch_sideK`,
  `singSwitch_sideK` (PROVED, at admissible `q`).
* `galRelK`, `galFinSideK`, `galSingSideK` (PROVED from the GLUE input `TameCoordinatesTrivialK`
  at the switch place): the relaxed localization and the finite / singular quasi sides at `q`.
* `galFinSideK_Dside`, `galSingSideK_Dside` (PROVED, at admissible `q`): their side Selmer data are
  the genuine fibres `galoisSelData K S k M (condAt Δ₀ Δ_d c)` and `… (insert q c)`, with
  `Δ₀ = galCond A₀`, `Δ_d = galCond A_d`; `galSidesK_Dstr` (PROVED).
* `galNonquadStepK` (PROVED from the stated inputs): a `QuasiNonquadStep` with residue map
  `ρ : A →+* k` and these sides.
* `GenuineNonquadStepsK` (GLUE input: at each reachable configuration a new admissible place with
  `TameCoordinatesTrivialK`, a `CoordStep`, the duality `LocalizationDualityInput` and the
  detection),
  `GenuineNonquadStepsK.exists_step` (PROVED); `GaloisNonquadInputsK`,
  `GaloisNonquadInputsK.toGaloisSwitchData`, `regular_of_galoisNonquadInputsK` (GLUE inputs, PROVED
  wiring): the nonquadratic case.
* `GaloisInputsK`, `GaloisInputsK.toGaloisQuadInputs`, `regular_of_galoisInputsK` (GLUE inputs,
  PROVED wiring): the nonquadratic genuine steps combined with the quadratic candidates of
  `GaloisWiringQuad.lean` (`GaloisQuadInputs`), giving regularity `∃ a, ι a = u` in all cases.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.UniformSwitch Module

section Global

variable (k : Type) [Field k] (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- The decomposition groups `G_v = Gal(K̄_v/K_v)` at the places of `S`. -/
abbrev gGvK : Places K S → Type := fun v => Gloc K v.1

/-- The coefficient module restricted to `G_v` along the localization map. -/
abbrev gMvK : Places K S → Type := fun v => ResMod (locMap K S v.1) M

/-- **The local complexes of the field-generic switch families are the genuine local complexes**
`galLv (k := k) K S M` of the Galois Selmer data (`rfl`). PROVED. -/
theorem locCxK_eq_galLv : locCxK k (gGvK K S) (gMvK K S M) = galLv (k := k) K S M := rfl

variable {k}

open Classical in
/-- The local conditions of a configuration `c`: `A_d v` at the places of `c` (the derivative
places, singular side), `A₀ v` elsewhere (tex L5060–5061). -/
def condFamK (A₀ Ad : ∀ v, SubFam (galLv (k := k) K S M v)) (c : Finset (Places K S))
    (v : Places K S) : SubFam (galLv (k := k) K S M v) :=
  if v ∈ c then Ad v else A₀ v

open Classical in
/-- **The configuration conditions of `GaloisFamily` are `galCond` of `condFamK`** (tex
L5060–5061). PROVED. -/
theorem condAt_galCondK (A₀ Ad : ∀ v, SubFam (galLv (k := k) K S M v))
    (c : Finset (Places K S)) :
    condAt K S k M (galCond K S M A₀) (galCond K S M Ad) c =
      galCond K S M (condFamK K S M A₀ Ad c) := by
  have h : condPair K S k M (galCond K S M A₀) (galCond K S M Ad) c =
      fun v => (⟨(condFamK K S M A₀ Ad c v).cx, (condFamK K S M A₀ Ad c v).incl⟩ :
        Σ U : GCx k, GHom U (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) M v)) := by
    funext v
    by_cases hv : v ∈ c
    · have e : condFamK K S M A₀ Ad c v = Ad v := ite_eq_left hv
      rw [e, condPair, ite_eq_left hv]; rfl
    · have e : condFamK K S M A₀ Ad c v = A₀ v := ite_eq_right hv
      rw [e, condPair, ite_eq_right hv]; rfl
  show (⟨fun v => (condPair K S k M (galCond K S M A₀) (galCond K S M Ad) c v).1,
      fun v => (condPair K S k M (galCond K S M A₀) (galCond K S M Ad) c v).2⟩ :
        GaloisLocalConditions K S k M) = galCond K S M (condFamK K S M A₀ Ad c)
  rw [h]
  rfl

/-! ### The finite and singular switch at a place `q ∉ c` -/

/-- The per-place tame data at the places of `S`: inertia `I_v`, a Frobenius lift `φ_v` and a tame
generator `σ_v` (tex L5027–5037). No coordinates of `M`: the rank-two clause `M ≃ k²` enters only
through the GLUE input `TameCoordinatesTrivialK` at the switch place. -/
structure PlaceTameK where
  /-- Inertia at `v`. -/
  I : ∀ v : Places K S, Subgroup (Gloc K v.1)
  /-- A Frobenius lift at `v`. -/
  φ : ∀ v : Places K S, Gloc K v.1
  /-- A tame inertia generator at `v`. -/
  σ : ∀ v : Places K S, Gloc K v.1

variable {K S}

variable (k) in
/-- The finite side conditions at the places: `sideOfSetK I_v` (cocycles vanishing on inertia,
`A = M^{I_v}`; tex L5057–5058, the unramified condition). -/
def PlaceTameK.finCond (D : PlaceTameK K S) (v : Places K S) : SubFam (galLv (k := k) K S M v) :=
  sideSubK (Gv := gGvK K S) (Mv := gMvK K S M) v
    (sideOfSetK k (gMvK K S M v) (D.I v : Set (Gloc K v.1)))

variable (k) in
/-- The singular side conditions at the places: `sideOfSetK {φ_v}` (cocycles vanishing at the
Frobenius lift; tex L5027–5037). -/
def PlaceTameK.singCond (D : PlaceTameK K S) (v : Places K S) : SubFam (galLv (k := k) K S M v) :=
  sideSubK (Gv := gGvK K S) (Mv := gMvK K S M) v
    (sideOfSetK k (gMvK K S M v) ({D.φ v} : Set (Gloc K v.1)))

variable (k K S) in
/-- **The configuration conditions of the switching family** over `k`: tame data `D` at the
places, and the finite conditions `A₀ v` and singular conditions `A_d v` at every place, as
subcomplexes of the genuine local complexes. Away from a switch place they are arbitrary (e.g. the
unramified cocycle conditions of the Λ-adic fibres); at a switch place `q` they are required to be
the derivative sides `finCond q`, `singCond q` (`SwitchCondsK.AdmissibleAt`). -/
structure SwitchCondsK where
  /-- The tame data at the places. -/
  D : PlaceTameK K S
  /-- The finite conditions. -/
  A₀ : ∀ v, SubFam (galLv (k := k) K S M v)
  /-- The singular conditions. -/
  Ad : ∀ v, SubFam (galLv (k := k) K S M v)

variable {M}

variable (k M) in
/-- The standard configuration conditions of `D`: `finCond` and `singCond` at every place. -/
def PlaceTameK.std (D : PlaceTameK K S) : SwitchCondsK k K S M :=
  ⟨D, D.finCond k M, D.singCond k M⟩

/-- **Admissibility at a switch place `q`**: the finite and singular conditions at `q` are the
derivative sides `sideOfSetK I_q`, `sideOfSetK {φ_q}` (tex L5060–5061). -/
def SwitchCondsK.AdmissibleAt (C : SwitchCondsK k K S M) (q : Places K S) : Prop :=
  C.A₀ q = C.D.finCond k M q ∧ C.Ad q = C.D.singCond k M q

/-- The standard conditions are admissible at every place. PROVED. -/
theorem PlaceTameK.std_admissibleAt (D : PlaceTameK K S) (q : Places K S) :
    (D.std k M).AdmissibleAt q :=
  ⟨rfl, rfl⟩

/-- The configuration conditions: singular at the places of `c`, finite elsewhere. -/
abbrev SwitchCondsK.old (C : SwitchCondsK k K S M) (c : Finset (Places K S)) :
    ∀ v, SubFam (locCxK k (gGvK K S) (gMvK K S M) v) :=
  condFamK K S M C.A₀ C.Ad c

/-- The finite side sets `I_v`. -/
abbrev PlaceTameK.finSet (D : PlaceTameK K S) : ∀ v : Places K S, Set (Gloc K v.1) :=
  fun v => (D.I v : Set (Gloc K v.1))

/-- The singular side sets `{φ_v}`. -/
abbrev PlaceTameK.singSet (D : PlaceTameK K S) : ∀ v : Places K S, Set (Gloc K v.1) :=
  fun v => {D.φ v}

variable (C : SwitchCondsK k K S M)

open Classical in
/-- **Switching at `q ∉ c` with the finite side gives the side family of `c`** (tex L5060–5082),
when the finite condition at `q` is the derivative side. PROVED. -/
theorem finSwitch_sideK (c : Finset (Places K S)) (q : Places K S) (hq : q ∉ c)
    (hA : C.A₀ q = C.D.finCond k M q) :
    (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.finSet).side =
      condFamK K S M C.A₀ C.Ad c := by
  funext v
  by_cases hv : v = q
  · subst hv
    have e : condFamK K S M C.A₀ C.Ad c v = C.D.finCond k M v := (ite_eq_right hq).trans hA
    rw [e]
    exact ite_eq_left rfl
  · exact ite_eq_right hv

open Classical in
/-- **Switching at `q` with the singular side gives the side family of `insert q c`** (tex
L5060–5082), when the singular condition at `q` is the derivative side. PROVED. -/
theorem singSwitch_sideK (c : Finset (Places K S)) (q : Places K S)
    (hA : C.Ad q = C.D.singCond k M q) :
    (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.singSet).side =
      condFamK K S M C.A₀ C.Ad (insert q c) := by
  funext v
  by_cases hv : v = q
  · subst hv
    have e : condFamK K S M C.A₀ C.Ad (insert v c) v = C.D.singCond k M v :=
      (ite_eq_left (Finset.mem_insert_self v c)).trans hA
    rw [e]
    exact ite_eq_left rfl
  · have e1 : (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.singSet).side v =
        C.old c v := ite_eq_right hv
    rw [e1]
    show (if v ∈ c then _ else _) = (if v ∈ insert q c then _ else _)
    have : (v ∈ insert q c) = (v ∈ c) := propext (by simp [hv])
    simp only [this]

variable (k K S M) in
/-- The global complex `C^•_cont(G_{K,S}, M)` over `k`. -/
abbrev galGK : GCx k := globalCx k (GKS K S) M

variable (k K S M) in
/-- The restriction `res_S` over `k`. -/
abbrev galResK : GHom (galGK k K S M) (piCx (locCxK k (gGvK K S) (gMvK K S M))) :=
  resS k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M

open Classical

variable (c : Finset (Places K S)) (q : Places K S)
  (T : TameCoordinatesTrivialK k (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

/-- **The genuine relaxed localization at the switch place `q`** over `k`, for the configuration
`c` (tex L5060–5086): global complex `C^•_cont(G_{K,S}, M)`, `res_S`, the relaxed condition at `q`,
the conditions of `c` elsewhere, the relaxed quotient `W_rel` and the coordinates `eRAtK` (with
`M ≃ k²` from the rank-two clause of `T`). -/
def galRelK : QuasiRelaxedLocalization k :=
  relLocK (Gv := gGvK K S) (Mv := gMvK K S M) q (galGK k K S M) (galResK k K S M) (C.old c)
    (eRAtK (switch_hsrK q (C.old c)) (switch_relAtK q (C.old c)) (C.D.φ q) (C.D.σ q) T.eM T)

/-- **The genuine finite quasi side at `q`** over `k` (tex L5060–5086). PROVED. -/
def galFinSideK : QuasiSwitchSide (galRelK C c q T) (finPlane k (Fin 2 → k) (Fin 2 → k)) :=
  switchQuasiSideK (Gv := gGvK K S) (Mv := gMvK K S M) (q := q) (C.D.φ q) (C.D.σ q) T.eM
    (galGK k K S M) (galResK k K S M) (C.old c) C.D.finSet T _
    (finite_side_iffK (Gv := gGvK K S) (Mv := gMvK K S M) (q := q) (C.D.φ q) (C.D.σ q) T.eM T)

/-- **The genuine singular quasi side at `q`** over `k`, over the same relaxed localization (tex
L5060–5086). PROVED. -/
def galSingSideK : QuasiSwitchSide (galRelK C c q T) (singPlane k (Fin 2 → k) (Fin 2 → k)) :=
  switchQuasiSideK (Gv := gGvK K S) (Mv := gMvK K S M) (q := q) (C.D.φ q) (C.D.σ q) T.eM
    (galGK k K S M) (galResK k K S M) (C.old c) C.D.singSet T _
    (singular_side_iffK (Gv := gGvK K S) (Mv := gMvK K S M) (q := q) (C.D.φ q) (C.D.σ q) T.eM)

/-- **The finite side's Selmer data is the genuine fibre of `c`** (tex L5060–5082):
`galoisSelData K S k M (condAt Δ₀ Δ_d c)` with `Δ₀ = galCond finCond`, `Δ_d = galCond singCond`.
PROVED. -/
theorem galFinSideK_Dside (hq : q ∉ c) (hA : C.A₀ q = C.D.finCond k M q) :
    (galFinSideK C c q T).Dside = galoisSelData K S k M
      (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad) c) := by
  rw [condAt_galCondK, ← finSwitch_sideK C c q hq hA]
  unfold galFinSideK switchQuasiSideK
  exact (DerivFamily.sideData_eq
    (F := switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.finSet)
    (G := galGK k K S M) (res := galResK k K S M) _ _ _).trans
    (galois_relaxedData_eq (k := k) K S M
      (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.finSet)).2

/-- **The singular side's Selmer data is the genuine fibre of `insert q c`** (tex L5060–5082).
PROVED. -/
theorem galSingSideK_Dside (hA : C.Ad q = C.D.singCond k M q) :
    (galSingSideK C c q T).Dside = galoisSelData K S k M
      (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
        (insert q c)) := by
  rw [condAt_galCondK, ← singSwitch_sideK C c q hA]
  unfold galSingSideK switchQuasiSideK
  exact (DerivFamily.sideData_eq
    (F := switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.singSet)
    (G := galGK k K S M) (res := galResK k K S M) _ _ _).trans
    (galois_relaxedData_eq (k := k) K S M
      (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.singSet)).2

/-- The Selmer data of a strict family `str` over `k` (global complex `G`, `res`, and the inclusion
of the strict conditions into the local complexes). -/
def strDataK {ι : Type} {Lv : ι → GCx k} (G : GCx k) (res : GHom G (piCx Lv))
    (str : ∀ v, SubFam (Lv v)) : SelData k :=
  ⟨G, piCx fun v => (str v).cx, piCx Lv, res, piMap fun v => (str v).incl⟩

/-- **The strict data of a quasi side depend only on the strict family** over `k` (tex
L5072–5083). PROVED. -/
theorem DerivFamily.Dstr_eqK {ι : Type} {Lv : ι → GCx k} (F : DerivFamily Lv)
    (G : GCx k) (res : GHom G (piCx Lv))
    (eR : F.Wrel.toCC.homology 1 ≃ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (P : Submodule k ((Fin 2 → k) × (Fin 2 → k)))
    (hP : (LinearMap.range (H1 F.i)).map eR.toLinearMap = P) :
    (F.toQuasiSide G res eR P hP).Dstr = strDataK G res F.str := by
  change restrictData (restrictData (F.relaxedData G res) F.f₁) F.fs = strDataK G res F.str
  unfold restrictData strDataK DerivFamily.relaxedData
  congr 1
  exact ghom_ext fun n x => rfl

/-- **The two sides share the strict Selmer data** over `k` (tex L5072–5083: "with `D⁰`
retained"). PROVED. -/
theorem galSidesK_Dstr : (galFinSideK C c q T).Dstr = (galSingSideK C c q T).Dstr := by
  have h1 : (galFinSideK C c q T).Dstr =
      strDataK (galGK k K S M) (galResK k K S M)
        (switchStrK k (gGvK K S) (gMvK K S M) q (C.old c)) :=
    DerivFamily.Dstr_eqK (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.finSet)
      (galGK k K S M) (galResK k K S M) _ _ _
  have h2 : (galSingSideK C c q T).Dstr =
      strDataK (galGK k K S M) (galResK k K S M)
        (switchStrK k (gGvK K S) (gMvK K S M) q (C.old c)) :=
    DerivFamily.Dstr_eqK (switchFamK k (gGvK K S) (gMvK K S M) q (C.old c) C.D.singSet)
      (galGK k K S M) (galResK k K S M) _ _ _
  exact h1.trans h2.symm

end Global

/-! ### The nonquadratic switch step and the Galois switching data over `k` -/

section Steps

variable {k : Type} [Field k] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
  (C : SwitchCondsK k K S M)
  {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* k)

open Classical

/-- **The genuine nonquadratic switch step at `q`** over `k` (tex L4997–5003, L5055–5086): the
homology-level nonquadratic step whose relaxed localization, finite side and singular side are the
genuine `galRelK`, `galFinSideK`, `galSingSideK`, with residue map `ρ : A →+* k`; the strict
dimensions agree by `galSidesK_Dstr`. The duality `hdual`, the detection `hdet` and the fibre
isomorphisms `φ`, `φ'` are the stated inputs. PROVED (from the inputs). -/
def galNonquadStepK (c : Finset (Places K S)) (q : Places K S)
    (T : TameCoordinatesTrivialK k (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))
    (S₀ S₁ : TwoTermStage ι) (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1) (hdual : LocalizationDualityInput ε σ J hε hσ hJ2 (galRelK C c q T).U)
    (hdet : finPlane k (Fin 2 → k) (Fin 2 → k) ≤ (galRelK C c q T).U)
    (φ : (selCx (galFinSideK C c q T).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S₀)
    (φ' : (selCx (galSingSideK C c q T).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ S₁) :
    QuasiNonquadStep ρ S₀ S₁ where
  R := galRelK C c q T
  SF := galFinSideK C c q T
  SS := galSingSideK C c q T
  hk0 := by rw [galSidesK_Dstr]
  ε := ε
  σ := σ
  J := J
  hε := hε
  hσ := hσ
  hJ2 := hJ2
  hdual := hdual
  hdet := hdet
  φ := φ
  φ' := φ'

variable (A) in
/-- **The genuine Galois switching family of `C` over `k`**: fibres
`galoisSelData K S k M (condAt Δ₀ Δ_d c)` with `Δ₀ = galCond A₀` (finite conditions) and
`Δ_d = galCond A_d` (singular conditions at the derivative places of `c`). -/
abbrev galΦK (c₀ : Finset (Places K S)) (t : A)
    (zAct : (selCx (galoisSelData K S k M
      (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
        c₀))).toCC.X 1)
    (hzAct : ((selCx (galoisSelData K S k M
      (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
        c₀))).toCC.d 1 2).hom zAct = 0)
    (lamAct : (selCx (galoisSelData K S k M
      (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
        c₀))).toCC.X 2 →ₗ[k] k)
    (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S k M
      (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
        c₀))).toCC.d 1 2).hom y) = 0) :
    SwitchFamily k A :=
  galoisSwitchFamily K S k M A (galCond K S M C.A₀) (galCond K S M C.Ad)
    c₀ t zAct hzAct lamAct hlamAct

variable (c₀ : Finset (Places K S)) (t : A)
  (zAct : (selCx (galoisSelData K S k M
    (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
      c₀))).toCC.X 1)
  (hzAct : ((selCx (galoisSelData K S k M
    (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
      c₀))).toCC.d 1 2).hom zAct = 0)
  (lamAct : (selCx (galoisSelData K S k M
    (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
      c₀))).toCC.X 2 →ₗ[k] k)
  (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S k M
    (condAt K S k M (galCond K S M C.A₀) (galCond K S M C.Ad)
      c₀))).toCC.d 1 2).hom y) = 0)

/-- **The genuine nonquadratic switch inputs over `k` at the reachable configurations** (tex
L4997–5003, L5055–5086), for stages `stage`: at every reachable configuration `c` of fibre dimension
`> 1` (in the nonquadratic case), a new place `q ∉ c` with the GLUE tame coordinates
`TameCoordinatesTrivialK` at `q`, admissible conditions at `q`, a `CoordStep`, and the duality and
detection for the genuine
relaxed localization `galRelK C c q T`. The sides are NOT inputs. Classification: GLUE (input). -/
def GenuineNonquadStepsK (stage : Finset (Places K S) → TwoTermStage ι) : Prop :=
  ∀ c : Finset (Places K S),
    Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    ¬ (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
    1 < (stage c).fiberDim ρ →
    ∃ (q : Places K S) (_ : q ∉ c)
      (T : TameCoordinatesTrivialK k (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q)),
      C.AdmissibleAt q ∧ Nonempty (CoordStep ι (stage c).u (stage (insert q c)).u) ∧
      ∃ (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0)
        (hJ2 : J * J = 1), LocalizationDualityInput ε σ J hε hσ hJ2 (galRelK C c q T).U ∧
          finPlane k (Fin 2 → k) (Fin 2 → k) ≤ (galRelK C c q T).U

variable {C ρ c₀ t zAct hzAct lamAct hlamAct}

/-- **The genuine steps give the nonquadratic switch field** (tex L4997–5003): from
`GenuineNonquadStepsK` and stage models of the genuine fibres, a place with a `CoordStep` and a
`QuasiNonquadStep` whose sides are the fibres of `c` and `insert q c`. PROVED. -/
theorem GenuineNonquadStepsK.exists_step {stage : Finset (Places K S) → TwoTermStage ι}
    (H : GenuineNonquadStepsK C ρ c₀ t zAct hzAct lamAct hlamAct stage)
    (model : ∀ c, HomotopyEquiv
      (selCx ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).fibre c)).toCC
        (twoTermFiberComplex ρ (stage c)))
    (c : Finset (Places K S)) (hc : Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c)
    (hnq : ¬ (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ)
    (h1 : 1 < (stage c).fiberDim ρ) :
    ∃ p : (galΦK C A c₀ t zAct hzAct lamAct hlamAct).Prime,
      Nonempty (CoordStep ι (stage c).u
        (stage ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c p)).u) ∧
      ∃ N : QuasiNonquadStep ρ (stage c)
          (stage ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c p)),
        N.SF.Dside = (galΦK C A c₀ t zAct hzAct lamAct hlamAct).fibre c ∧
        N.SS.Dside = (galΦK C A c₀ t zAct hzAct lamAct hlamAct).fibre
          ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c p) := by
  obtain ⟨q, hq, T, hadm, hcs, ε, σ, J, hε, hσ, hJ2, hdual, hdet⟩ := H c hc hnq h1
  obtain ⟨hA₀, hAd⟩ := hadm
  have φ : (selCx (galFinSideK C c q T).Dside).toCC.homology 1 ≃ₗ[k] fiberH1 ρ (stage c) := by
    rw [galFinSideK_Dside C c q T hq hA₀]
    exact h1EquivOfHomotopyEquiv ρ _ _ (model c)
  have φ' : (selCx (galSingSideK C c q T).Dside).toCC.homology 1 ≃ₗ[k]
      fiberH1 ρ (stage (insert q c)) := by
    rw [galSingSideK_Dside C c q T hAd]
    exact h1EquivOfHomotopyEquiv ρ _ _ (model (insert q c : Finset (Places K S)))
  exact ⟨q, hcs, galNonquadStepK C ρ c q T (stage c) (stage (insert q c)) ε σ J hε hσ hJ2 hdual
    hdet φ φ', galFinSideK_Dside C c q T hq hA₀, galSingSideK_Dside C c q T hAd⟩

variable (C ρ c₀ t zAct hzAct lamAct hlamAct) in
/-- **Nonquadratic Galois switching inputs over `k`** (tex L4976–5195) over the genuine family
`galΦK C A c₀ …`: the stage models of the genuine fibres, the starting link to the actual
class, functional and coordinate, primitivity, the nonquadratic specialization, and the genuine
nonquadratic steps `GenuineNonquadStepsK`. Classification: GLUE (inputs). -/
structure GaloisNonquadInputsK (ι : A →+* F) (u : F) where
  /-- The stage two-term models. -/
  stage : Finset (Places K S) → TwoTermStage ι
  /-- Each stage is the genuine fibre model. -/
  model : ∀ c, HomotopyEquiv
    (selCx ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).fibre c)).toCC
      (twoTermFiberComplex ρ (stage c))
  /-- The actual class. -/
  hz0 : ((model c₀).hom.f 1).hom zAct = fun i => ρ ((stage c₀).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, lamAct y = (fun i => ρ ((stage c₀).w i)) ⬝ᵥ (((model c₀).hom.f 2).hom y : Fin _ → k)
  /-- The actual coordinate. -/
  hu0 : (stage c₀).u = u
  /-- The specialization is nonquadratic. -/
  hnq : ¬ (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ
  /-- Primitivity of the stage classes. -/
  primitive : ∀ c : Finset (Places K S),
    Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c → ∃ i, ρ ((stage c).z i) ≠ 0
  /-- The genuine switch inputs at new places. -/
  step : GenuineNonquadStepsK C ρ c₀ t zAct hzAct lamAct hlamAct stage

/-- **Galois switching data from the nonquadratic inputs over `k`** (tex L4976–5195). PROVED. -/
noncomputable def GaloisNonquadInputsK.toGaloisSwitchData {u : F}
    (X : GaloisNonquadInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u) :
    GaloisSwitchData (galΦK C A c₀ t zAct hzAct lamAct hlamAct) ι ρ u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  σ := fun _ => LinearMap.id
  h2 := fun h => absurd h X.hnq
  hσ := fun h => absurd h X.hnq
  primitive := X.primitive
  switch_mixed c hc _ h1 := by
    obtain ⟨p, hcs, N, hF, hS⟩ := X.step.exists_step X.model c hc X.hnq h1
    exact ⟨p, hcs, fun h => absurd h X.hnq, fun _ => ⟨N, hF, hS⟩⟩
  switch_single _ _ h := absurd h X.hnq

/-- **Regularity from the nonquadratic Galois switching inputs over `k`** (tex L4976–5195):
`∃ a, ι a = u`. PROVED (from the inputs). -/
theorem regular_of_galoisNonquadInputsK [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {u : F}
    (X : GaloisNonquadInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u) : ∃ a : A, ι a = u :=
  regular_of_galoisSwitchData' hι hρ X.toGaloisSwitchData

variable (C ρ c₀ t zAct hzAct lamAct hlamAct) in
/-- **Galois switching inputs over `k`, all cases** (tex L4976–5195): the fields of
`GaloisQuadInputs` (`GaloisWiringQuad.lean`) for the genuine family `galΦK C A c₀ …`, with the
nonquadratic switch field replaced by the genuine steps `GenuineNonquadStepsK` (sides genuine by
construction); the quadratic switches are given by the candidate data `MixedCandidates`,
`SingleCandidates` of `GaloisWiringQuad.lean`. Classification: GLUE (inputs). -/
structure GaloisInputsK (ι : A →+* F) (u : F) where
  /-- The stage two-term models. -/
  stage : Finset (Places K S) → TwoTermStage ι
  /-- Each stage is the genuine fibre model. -/
  model : ∀ c, HomotopyEquiv
    (selCx ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).fibre c)).toCC
      (twoTermFiberComplex ρ (stage c))
  /-- The actual class. -/
  hz0 : ((model c₀).hom.f 1).hom zAct = fun i => ρ ((stage c₀).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, lamAct y = (fun i => ρ ((stage c₀).w i)) ⬝ᵥ (((model c₀).hom.f 2).hom y : Fin _ → k)
  /-- The actual coordinate. -/
  hu0 : (stage c₀).u = u
  /-- The involutions on the stage fibres (quadratic case). -/
  σ : ∀ c, fiberH1 ρ (stage c) →ₗ[k] fiberH1 ρ (stage c)
  /-- `2 ≠ 0` in the quadratic case. -/
  h2 : (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ → (2 : k) ≠ 0
  /-- The involution property in the quadratic case. -/
  hσ : (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ → ∀ c, σ c ∘ₗ σ c = LinearMap.id
  /-- Primitivity of the stage classes. -/
  primitive : ∀ c : Finset (Places K S),
    Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c → ∃ i, ρ ((stage c).z i) ≠ 0
  /-- The genuine nonquadratic switch inputs at new places. -/
  step : GenuineNonquadStepsK C ρ c₀ t zAct hzAct lamAct hlamAct stage
  /-- The mixed quadratic candidates. -/
  mixed : ∀ c, Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
    (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ →
    MixedCandidates (galΦK C A c₀ t zAct hzAct lamAct hlamAct) ρ stage σ c
  /-- The single-sign quadratic candidates. -/
  single : ∀ c, Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
    ¬ (0 < finrank k ↥(signPart (σ c) (1 : k)) ∧ 0 < finrank k ↥(signPart (σ c) (-1 : k))) →
    1 < (stage c).fiberDim ρ →
    SingleCandidates (galΦK C A c₀ t zAct hzAct lamAct hlamAct) ρ stage σ c

/-- **The combined inputs give `GaloisQuadInputs`** (tex L4976–5195): the nonquadratic field from
`GenuineNonquadStepsK.exists_step`. PROVED. -/
noncomputable def GaloisInputsK.toGaloisQuadInputs {u : F}
    (X : GaloisInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u) :
    GaloisQuadInputs (galΦK C A c₀ t zAct hzAct lamAct hlamAct) ι ρ u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  σ := X.σ
  h2 := X.h2
  hσ := X.hσ
  primitive := X.primitive
  nonquad c hc hnq h1 := X.step.exists_step X.model c hc hnq h1
  mixed := X.mixed
  single := X.single

/-- **Regularity from the field-generic Galois switching inputs** (tex L4976–5195): over any
coefficient field `k` (residue map `ρ : A →+* k` killing the maximal ideal), `∃ a, ι a = u`.
PROVED (from the inputs, via `regular_of_galoisQuadInputs`). -/
theorem regular_of_galoisInputsK [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {u : F}
    (X : GaloisInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u) : ∃ a : A, ι a = u :=
  regular_of_galoisQuadInputs hι hρ X.toGaloisQuadInputs

end Steps

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
