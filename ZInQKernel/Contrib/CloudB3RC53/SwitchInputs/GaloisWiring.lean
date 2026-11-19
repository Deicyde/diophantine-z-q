import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.DerivativeCoords
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenuineSteps
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.TameUnramified
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# RC53 SwitchInputs: the genuine derivative sides wired into the Galois switching family

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L4976–5195, with the switch
exact sequences (5.5a), tex L5055–5086, and the derivative conditions, tex L5060–5061.

`DerivativeCoords.lean` builds the switch families `switchFam` (strict ≤ side ≤ relaxed at the
switch place, the old conditions elsewhere) on families of genuine local complexes
`C^•_cont(G_v, M_v)`, with the coordinates `eRAt` and the plane equation, and the quasi sides
`switchQuasiSide` over the side-independent relaxed localization `relLoc`. Here they are placed at
the genuine decomposition groups inside `G_{K,S}`:

* `gGv`, `gMv`, `locCx_eq_galLv` (PROVED, `rfl`): with `G_v = Gloc K v` and
  `M_v = ResMod (locMap v) M`, the local complexes of `DerivativeCoords` are the genuine local
  complexes `galLv K S M` of the Galois Selmer data.
* `condFam`, `condAt_galCond` (PROVED): the configuration conditions of `GaloisFamily` (`condAt`,
  with `Δ₀ = galCond A₀` the finite side and `Δ_d = galCond A_d` the singular side at the places)
  are `galCond` of the family `condFam A₀ A_d c`.
* `finSwitch_side`, `singSwitch_side` (PROVED): switching at `q ∉ c` with the finite side gives the
  side family of `c`; with the singular side, that of `insert q c`.
* `galFinSide`, `galSingSide` (PROVED): the finite and singular quasi sides at `q`, over one
  relaxed localization `galRel`, with global complex `C^•_cont(G_{K,S}, M)` and `res_S`.
* `galFinSide_Dside`, `galSingSide_Dside` (PROVED): their side Selmer data are the genuine fibres
  `galoisSelData K S k M (condAt Δ₀ Δ_d c)` and `… (insert q c)`, i.e. the fibres of
  `galoisSwitchFamily` at `c` and at `next c q`.
* `galNonquadStep` (PROVED from the stated inputs): a `QuasiNonquadStep` with these sides, so the
  nonquadratic switch field of `GaloisSwitchData` has `hF`, `hS` discharged. `galSides_Dstr`
  (PROVED): the two sides share the strict data (`DerivFamily.Dstr_eq`).
* `GaloisNonquadInputs`, `GaloisNonquadInputs.toGaloisSwitchData` (GLUE): the stage models, the
  primitivity and, at each reachable non-terminal configuration, a place `q ∉ c` with tame
  coordinates, the coordinate step and the localization duality, give `GaloisSwitchData` for
  `galoisSwitchFamily` (nonquadratic case; the quadratic fields are absurd). DEPARTURE: the
  quadratic switch steps are not wired here.
* `regular_of_galoisNonquadInputs` (PROVED from `regular_of_galoisSwitchData'`): regularity.
* `PlaceTame.exists_at`, `exists_galSides` (PROVED; non-vacuity): at a place `q` with
  finite residue field of odd characteristic and trivial `M ≃ 𝔽₂²`, the tame coordinates of
  `G_{K_q}` give genuine finite and singular quasi sides for every configuration.

**Caveat (residue field `𝔽₂`).** The genuine instances in this file are specialised to the residue
field `𝔽₂`. They are not applicable at the height-one primes `𝔭 ≠ (2)` of `Λ` where the switching
runs (tex L4976: `R = Λ_𝔭`, residue field of characteristic `0`): there is no ring map
`Λ_𝔭 → ZMod 2` (`isEmpty_ringHom_zmod_two_heightOne`). See `GaloisWiringQuad.lean` for the
field-generic version.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex NumberField IsDedekindDomain ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53.UniformSwitch Module

section Global

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousAdd M] [ContinuousConstSMul (ZMod 2) M] [ContinuousSMul (GKS K S) M]

/-- The decomposition groups `G_v = Gal(K̄_v/K_v)` at the places of `S`. -/
abbrev gGv : Places K S → Type := fun v => Gloc K v.1

/-- The coefficient module restricted to `G_v` along the localization map. -/
abbrev gMv : Places K S → Type := fun v => ResMod (locMap K S v.1) M

/-- **The local complexes of the switch families are the genuine local complexes** of the Galois
Selmer data (`rfl`). PROVED. -/
theorem locCx_eq_galLv : locCx (gGv K S) (gMv K S M) = galLv (k := ZMod 2) K S M := rfl

open Classical in
/-- The local conditions of a configuration `c`: `A_d v` at the places of `c` (the derivative
places, singular side), `A₀ v` elsewhere (tex L5060–5061). -/
def condFam (A₀ Ad : ∀ v, SubFam (galLv (k := ZMod 2) K S M v)) (c : Finset (Places K S))
    (v : Places K S) : SubFam (galLv (k := ZMod 2) K S M v) :=
  if v ∈ c then Ad v else A₀ v

omit [DiscreteTopology M] in
open Classical in
/-- **The configuration conditions of `GaloisFamily` are `galCond` of `condFam`** (tex L5060–5061).
PROVED. -/
theorem condAt_galCond (A₀ Ad : ∀ v, SubFam (galLv (k := ZMod 2) K S M v))
    (c : Finset (Places K S)) :
    condAt K S (ZMod 2) M (galCond K S M A₀) (galCond K S M Ad) c =
      galCond K S M (condFam K S M A₀ Ad c) := by
  have h : condPair K S (ZMod 2) M (galCond K S M A₀) (galCond K S M Ad) c =
      fun v => (⟨(condFam K S M A₀ Ad c v).cx, (condFam K S M A₀ Ad c v).incl⟩ :
        Σ U : GCx (ZMod 2), GHom U (localCx (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) M v)) := by
    funext v
    by_cases hv : v ∈ c
    · have e : condFam K S M A₀ Ad c v = Ad v := if_pos hv
      rw [e, condPair, if_pos hv]; rfl
    · have e : condFam K S M A₀ Ad c v = A₀ v := if_neg hv
      rw [e, condPair, if_neg hv]; rfl
  show (⟨fun v => (condPair K S (ZMod 2) M (galCond K S M A₀) (galCond K S M Ad) c v).1,
      fun v => (condPair K S (ZMod 2) M (galCond K S M A₀) (galCond K S M Ad) c v).2⟩ :
        GaloisLocalConditions K S (ZMod 2) M) = galCond K S M (condFam K S M A₀ Ad c)
  rw [h]
  rfl

/-! ### The finite and singular switch at a place `q ∉ c` -/

/-- The per-place tame data at the places of `S`: inertia `I_v`, a Frobenius lift `φ_v`, a tame
generator `σ_v`, and coordinates `M ≃ 𝔽₂²` (tex L5027–5037). Specialised to residue field `𝔽₂`;
not applicable at height-one primes `≠ (2)` where switching runs
(`isEmpty_ringHom_zmod_two_heightOne`); see `GaloisWiringQuad.lean` for the field-generic version.
-/
structure PlaceTame where
  /-- Inertia at `v`. -/
  I : ∀ v : Places K S, Subgroup (Gloc K v.1)
  /-- A Frobenius lift at `v`. -/
  φ : ∀ v : Places K S, Gloc K v.1
  /-- A tame inertia generator at `v`. -/
  σ : ∀ v : Places K S, Gloc K v.1
  /-- Coordinates of the coefficients. -/
  eM : ∀ v : Places K S, gMv K S M v ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)

variable {K S M} (D : PlaceTame K S M)

/-- The finite side conditions at the places: `sideOfSet I_v` (cocycles vanishing on inertia,
`A = M^{I_v}`; tex L5057–5058, the unramified condition). -/
def PlaceTame.finCond (v : Places K S) : SubFam (galLv (k := ZMod 2) K S M v) :=
  sideSub (Gv := gGv K S) (Mv := gMv K S M) v (sideOfSet ((D.I v : Set (Gloc K v.1))))

/-- The singular side conditions at the places: `sideOfSet {φ_v}` (cocycles vanishing at the
Frobenius lift; tex L5027–5037). -/
def PlaceTame.singCond (v : Places K S) : SubFam (galLv (k := ZMod 2) K S M v) :=
  sideSub (Gv := gGv K S) (Mv := gMv K S M) v (sideOfSet ({D.φ v} : Set (Gloc K v.1)))

/-- The configuration conditions: singular at the places of `c`, finite elsewhere. -/
abbrev PlaceTame.old (c : Finset (Places K S)) : ∀ v, SubFam (locCx (gGv K S) (gMv K S M) v) :=
  condFam K S M D.finCond D.singCond c

/-- The finite side sets `I_v`. -/
abbrev PlaceTame.finSet : ∀ v : Places K S, Set (Gloc K v.1) := fun v => (D.I v : Set (Gloc K v.1))

/-- The singular side sets `{φ_v}`. -/
abbrev PlaceTame.singSet : ∀ v : Places K S, Set (Gloc K v.1) := fun v => {D.φ v}

open Classical in
/-- **Switching at `q ∉ c` with the finite side gives the side family of `c`** (tex L5060–5082).
PROVED. -/
theorem finSwitch_side (c : Finset (Places K S)) (q : Places K S) (hq : q ∉ c) :
    (switchFam (gGv K S) (gMv K S M) q (D.old c) D.finSet).side = condFam K S M D.finCond D.singCond c := by
  funext v
  by_cases hv : v = q
  · subst hv
    have e : condFam K S M D.finCond D.singCond c v = D.finCond v := if_neg hq
    rw [e]
    exact if_pos rfl
  · exact if_neg hv

open Classical in
/-- **Switching at `q ∉ c` with the singular side gives the side family of `insert q c`** (tex
L5060–5082). PROVED. -/
theorem singSwitch_side (c : Finset (Places K S)) (q : Places K S) :
    (switchFam (gGv K S) (gMv K S M) q (D.old c) D.singSet).side =
      condFam K S M D.finCond D.singCond (insert q c) := by
  funext v
  by_cases hv : v = q
  · subst hv
    have e : condFam K S M D.finCond D.singCond (insert v c) v = D.singCond v :=
      if_pos (Finset.mem_insert_self v c)
    rw [e]
    exact if_pos rfl
  · have e1 : (switchFam (gGv K S) (gMv K S M) q (D.old c) D.singSet).side v = D.old c v := if_neg hv
    rw [e1]
    show (if v ∈ c then _ else _) = (if v ∈ insert q c then _ else _)
    have : (v ∈ insert q c) = (v ∈ c) := propext (by simp [hv])
    simp only [this]

/-- The global complex `C^•_cont(G_{K,S}, M)`. -/
abbrev galG : GCx (ZMod 2) := globalCx (ZMod 2) (GKS K S) M

/-- The restriction `res_S`. -/
abbrev galRes : GHom (galG (K := K) (S := S) (M := M)) (piCx (locCx (gGv K S) (gMv K S M))) :=
  resS (ZMod 2) (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M

open Classical

variable (c : Finset (Places K S)) (q : Places K S)
  (T : TameCoordinates (M := gMv K S M q) (D.I q) (D.φ q) (D.σ q))

/-- **The genuine relaxed localization at the switch place `q`** for the configuration `c`
(tex L5060–5086): global complex `C^•_cont(G_{K,S}, M)`, `res_S`, the relaxed condition at `q`, the
conditions of `c` elsewhere, the relaxed quotient `W_rel` and the coordinates `eRAt`. -/
def galRel : QuasiRelaxedLocalization (ZMod 2) :=
  relLoc (Gv := gGv K S) (Mv := gMv K S M) q galG galRes (D.old c)
    (eRAt (switch_hsr q (D.old c)) (switch_relAt q (D.old c)) (D.φ q) (D.σ q) (D.eM q) T)

/-- **The genuine finite quasi side at `q`** (tex L5060–5086). PROVED. -/
def galFinSide : QuasiSwitchSide (galRel D c q T) (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) :=
  switchQuasiSide (Gv := gGv K S) (Mv := gMv K S M) (q := q) (D.φ q) (D.σ q) (D.eM q) galG galRes
    (D.old c) D.finSet T _
    (finite_side_iff (Gv := gGv K S) (Mv := gMv K S M) (q := q) (D.φ q) (D.σ q) (D.eM q) T)

/-- **The genuine singular quasi side at `q`**, over the same relaxed localization (tex
L5060–5086). PROVED. -/
def galSingSide : QuasiSwitchSide (galRel D c q T) (singPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) :=
  switchQuasiSide (Gv := gGv K S) (Mv := gMv K S M) (q := q) (D.φ q) (D.σ q) (D.eM q) galG galRes
    (D.old c) D.singSet T _
    (singular_side_iff (Gv := gGv K S) (Mv := gMv K S M) (q := q) (D.φ q) (D.σ q) (D.eM q))

/-- **The finite side's Selmer data is the genuine fibre of `c`** (tex L5060–5082):
`galoisSelData K S 𝔽₂ M (condAt Δ₀ Δ_d c)` with `Δ₀ = galCond finCond`, `Δ_d = galCond singCond`.
PROVED. -/
theorem galFinSide_Dside (hq : q ∉ c) :
    (galFinSide D c q T).Dside = galoisSelData K S (ZMod 2) M
      (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c) := by
  rw [condAt_galCond, ← finSwitch_side D c q hq]
  unfold galFinSide switchQuasiSide
  exact (DerivFamily.sideData_eq (F := switchFam (gGv K S) (gMv K S M) q (D.old c) D.finSet)
    (G := galG) (res := galRes) _ _ _).trans
    (galois_relaxedData_eq (k := ZMod 2) K S M
      (switchFam (gGv K S) (gMv K S M) q (D.old c) D.finSet)).2

/-- **The singular side's Selmer data is the genuine fibre of `insert q c`** (tex L5060–5082).
PROVED. -/
theorem galSingSide_Dside :
    (galSingSide D c q T).Dside = galoisSelData K S (ZMod 2) M
      (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) (insert q c)) := by
  rw [condAt_galCond, ← singSwitch_side D c q]
  unfold galSingSide switchQuasiSide
  exact (DerivFamily.sideData_eq (F := switchFam (gGv K S) (gMv K S M) q (D.old c) D.singSet)
    (G := galG) (res := galRes) _ _ _).trans
    (galois_relaxedData_eq (k := ZMod 2) K S M
      (switchFam (gGv K S) (gMv K S M) q (D.old c) D.singSet)).2

/-- The Selmer data of a strict family `str` (global complex `G`, `res`, and the inclusion of the
strict conditions into the local complexes). -/
def strData {ι : Type} {Lv : ι → GCx (ZMod 2)} (G : GCx (ZMod 2)) (res : GHom G (piCx Lv))
    (str : ∀ v, SubFam (Lv v)) : SelData (ZMod 2) :=
  ⟨G, piCx fun v => (str v).cx, piCx Lv, res, piMap fun v => (str v).incl⟩

/-- **The strict data of a quasi side depend only on the strict family** (tex L5072–5083). PROVED.
-/
theorem DerivFamily.Dstr_eq {ι : Type} {Lv : ι → GCx (ZMod 2)} (F : DerivFamily Lv)
    (G : GCx (ZMod 2)) (res : GHom G (piCx Lv))
    (eR : F.Wrel.toCC.homology 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
    (P : Submodule (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)))
    (hP : (LinearMap.range (H1 F.i)).map eR.toLinearMap = P) :
    (F.toQuasiSide G res eR P hP).Dstr = strData G res F.str := by
  change restrictData (restrictData (F.relaxedData G res) F.f₁) F.fs = strData G res F.str
  unfold restrictData strData DerivFamily.relaxedData
  congr 1
  exact ghom_ext fun n x => rfl

/-- **The two sides share the strict Selmer data** (tex L5072–5083: "with `D⁰` retained"): the
strict data of the finite and singular quasi sides agree. PROVED. -/
theorem galSides_Dstr : (galFinSide D c q T).Dstr = (galSingSide D c q T).Dstr := by
  have h1 : (galFinSide D c q T).Dstr =
      strData galG galRes (switchStr (gGv K S) (gMv K S M) q (D.old c)) :=
    DerivFamily.Dstr_eq (switchFam (gGv K S) (gMv K S M) q (D.old c) D.finSet) galG galRes _ _ _
  have h2 : (galSingSide D c q T).Dstr =
      strData galG galRes (switchStr (gGv K S) (gMv K S M) q (D.old c)) :=
    DerivFamily.Dstr_eq (switchFam (gGv K S) (gMv K S M) q (D.old c) D.singSet) galG galRes _ _ _
  exact h1.trans h2.symm

end Global


/-! ### The nonquadratic switch step and the Galois switching data -/

section Steps

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousAdd M] [ContinuousConstSMul (ZMod 2) M] [ContinuousSMul (GKS K S) M]
  (D : PlaceTame K S M)
  {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* ZMod 2)

open Classical

/-- **The genuine nonquadratic switch step at `q`** (tex L4997–5003, L5055–5086): the homology-level
nonquadratic step whose relaxed localization, finite side and singular side are the genuine
`galRel`, `galFinSide`, `galSingSide`; the strict dimensions agree by `galSides_Dstr`. The duality
input `hdual`, the detection `hdet` and the fibre isomorphisms `φ`, `φ'` are the stated inputs.
PROVED (from the inputs). Residual-field (`𝔽₂`) instance only; not applicable at height-one primes
`≠ (2)`, see `isEmpty_ringHom_zmod_two_heightOne`; the characteristic-zero version is the
field-generic chain. -/
def galNonquadStep (c : Finset (Places K S)) (q : Places K S)
    (T : TameCoordinates (M := gMv K S M q) (D.I q) (D.φ q) (D.σ q)) (S₀ S₁ : TwoTermStage ι)
    (ε σ : ZMod 2) (J : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1) (hdual : LocalizationDualityInput ε σ J hε hσ hJ2 (galRel D c q T).U)
    (hdet : finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ≤ (galRel D c q T).U)
    (φ : (selCx (galFinSide D c q T).Dside).toCC.homology 1 ≃ₗ[ZMod 2] fiberH1 ρ S₀)
    (φ' : (selCx (galSingSide D c q T).Dside).toCC.homology 1 ≃ₗ[ZMod 2] fiberH1 ρ S₁) :
    QuasiNonquadStep ρ S₀ S₁ where
  R := galRel D c q T
  SF := galFinSide D c q T
  SS := galSingSide D c q T
  hk0 := by rw [galSides_Dstr]
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
/-- The genuine Galois switching family of `D`: fibres `galoisSelData K S 𝔽₂ M (condAt Δ₀ Δ_d c)`
with `Δ₀ = galCond finCond` (finite sides) and `Δ_d = galCond singCond` (singular sides at the
derivative places of `c`). -/
abbrev galΦ (c₀ : Finset (Places K S)) (t : A)
    (zAct : (selCx (galoisSelData K S (ZMod 2) M
      (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.X 1)
    (hzAct : ((selCx (galoisSelData K S (ZMod 2) M
      (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.d
        1 2).hom zAct = 0)
    (lamAct : (selCx (galoisSelData K S (ZMod 2) M
      (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.X 2
        →ₗ[ZMod 2] ZMod 2)
    (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S (ZMod 2) M
      (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.d
        1 2).hom y) = 0) :
    SwitchFamily (ZMod 2) A :=
  galoisSwitchFamily K S (ZMod 2) M A (galCond K S M D.finCond) (galCond K S M D.singCond) c₀ t
    zAct hzAct lamAct hlamAct

variable (c₀ : Finset (Places K S)) (t : A)
  (zAct : (selCx (galoisSelData K S (ZMod 2) M
    (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.X 1)
  (hzAct : ((selCx (galoisSelData K S (ZMod 2) M
    (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.d
      1 2).hom zAct = 0)
  (lamAct : (selCx (galoisSelData K S (ZMod 2) M
    (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.X 2
      →ₗ[ZMod 2] ZMod 2)
  (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S (ZMod 2) M
    (condAt K S (ZMod 2) M (galCond K S M D.finCond) (galCond K S M D.singCond) c₀))).toCC.d
      1 2).hom y) = 0)

/-- **Nonquadratic Galois switching inputs** (tex L4976–5195) over the genuine family
`galΦ D A c₀ …`: the stage models of the genuine fibres, the starting link to the actual class,
functional and coordinate, primitivity, the nonquadratic specialization, and, at every reachable
configuration of fibre dimension `> 1`, a new place `q ∉ c` with tame coordinates, a `CoordStep`,
the duality input and the detection for the genuine relaxed localization `galRel D c q T`. The sides
of the switch steps are NOT inputs: they are the genuine `galFinSide`, `galSingSide`, whose Selmer
data are the fibres of `c` and `insert q c` by construction (`galFinSide_Dside`,
`galSingSide_Dside`). Residual-field (`𝔽₂`) instance only; not applicable at height-one primes
`≠ (2)`, see `isEmpty_ringHom_zmod_two_heightOne`; the characteristic-zero version is the
field-generic chain. -/
structure GaloisNonquadInputs (ι : A →+* F) (u : F) where
  /-- The stage two-term models. -/
  stage : Finset (Places K S) → TwoTermStage ι
  /-- Each stage is the genuine fibre model. -/
  model : ∀ c, HomotopyEquiv
    (selCx ((galΦ D A c₀ t zAct hzAct lamAct hlamAct).fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  /-- The actual class. -/
  hz0 : ((model c₀).hom.f 1).hom zAct = fun i => ρ ((stage c₀).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, lamAct y = (fun i => ρ ((stage c₀).w i)) ⬝ᵥ (((model c₀).hom.f 2).hom y : Fin _ → ZMod 2)
  /-- The actual coordinate. -/
  hu0 : (stage c₀).u = u
  /-- The specialization is nonquadratic. -/
  hnq : ¬ (galΦ D A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ
  /-- Primitivity of the stage classes. -/
  primitive : ∀ c : Finset (Places K S), Reach (galΦ D A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    ∃ i, ρ ((stage c).z i) ≠ 0
  /-- The switch inputs at a new place. -/
  step : ∀ c : Finset (Places K S), Reach (galΦ D A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    1 < (stage c).fiberDim ρ →
    ∃ (q : Places K S) (_ : q ∉ c) (T : TameCoordinates (M := gMv K S M q) (D.I q) (D.φ q) (D.σ q)),
      Nonempty (CoordStep ι (stage c).u (stage (insert q c)).u) ∧
      ∃ (ε σ : ZMod 2) (J : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
        (hJ2 : J * J = 1), LocalizationDualityInput ε σ J hε hσ hJ2 (galRel D c q T).U ∧
          finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ≤ (galRel D c q T).U

variable {D ρ c₀ t zAct hzAct lamAct hlamAct}

/-- **Galois switching data from the nonquadratic inputs** (tex L4976–5195): the switch steps are
`galNonquadStep` with the genuine sides, so `hF`, `hS` are `galFinSide_Dside`, `galSingSide_Dside`;
the fibre isomorphisms come from the stage models. PROVED. Residual-field (`𝔽₂`) instance only; not
applicable at height-one primes `≠ (2)`, see `isEmpty_ringHom_zmod_two_heightOne`; the
characteristic-zero version is the field-generic chain. -/
noncomputable def GaloisNonquadInputs.toGaloisSwitchData {u : F}
    (X : GaloisNonquadInputs D ρ c₀ t zAct hzAct lamAct hlamAct ι u) :
    GaloisSwitchData (galΦ D A c₀ t zAct hzAct lamAct hlamAct) ι ρ u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  σ := fun _ => LinearMap.id
  h2 := fun h => absurd h X.hnq
  hσ := fun h => absurd h X.hnq
  primitive := X.primitive
  switch_mixed c₁ hc _ h1 := by
    let c : Finset (Places K S) := c₁
    obtain ⟨q, hq, T, hcs, ε, σ, J, hε, hσ, hJ2, hdual, hdet⟩ := X.step c hc h1
    refine ⟨q, hcs, fun h => absurd h X.hnq, fun _ => ?_⟩
    have φ : (selCx (galFinSide D c q T).Dside).toCC.homology 1 ≃ₗ[ZMod 2] fiberH1 ρ (X.stage c) := by
      rw [galFinSide_Dside D c q T hq]
      exact h1EquivOfHomotopyEquiv ρ _ _ (X.model c)
    have φ' : (selCx (galSingSide D c q T).Dside).toCC.homology 1 ≃ₗ[ZMod 2]
        fiberH1 ρ (X.stage (insert q c)) := by
      rw [galSingSide_Dside D c q T]
      exact h1EquivOfHomotopyEquiv ρ _ _ (X.model (insert q c : Finset (Places K S)))
    exact ⟨galNonquadStep D ρ c q T (X.stage c) (X.stage (insert q c)) ε σ J hε hσ hJ2 hdual hdet φ φ',
      galFinSide_Dside D c q T hq, galSingSide_Dside D c q T⟩
  switch_single _ _ h := absurd h X.hnq

/-- **Regularity from the nonquadratic Galois switching inputs** (tex L4976–5195): `∃ a, ι a = u`.
PROVED (from the inputs). Residual-field (`𝔽₂`) instance only; not applicable at height-one primes
`≠ (2)`, see `isEmpty_ringHom_zmod_two_heightOne`; the characteristic-zero version is the
field-generic chain. -/
theorem regular_of_galoisNonquadInputs [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {u : F}
    (X : GaloisNonquadInputs D ρ c₀ t zAct hzAct lamAct hlamAct ι u) : ∃ a : A, ι a = u :=
  regular_of_galoisSwitchData' hι hρ X.toGaloisSwitchData

end Steps

/-! ### Non-vacuity: the genuine switch sides at an actual place -/

section Genuine

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousAdd M] [ContinuousConstSMul (ZMod 2) M] [ContinuousSMul (GKS K S) M]

open Classical ValuativeRel

/-- Tame data at the places prescribed at one place `q` (trivial away from `q`). GLUE. -/
theorem PlaceTame.exists_at (q : Places K S) (I₀ : Subgroup (Gloc K q.1)) (φ₀ σ₀ : Gloc K q.1)
    (eM : M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    ∃ D : PlaceTame K S M, D.I q = I₀ ∧ D.φ q = φ₀ ∧ D.σ q = σ₀ := by
  refine ⟨{ I := Function.update (fun v : Places K S => (⊥ : Subgroup (Gloc K v.1))) q I₀,
             φ := Function.update (fun v : Places K S => (1 : Gloc K v.1)) q φ₀,
             σ := Function.update (fun v : Places K S => (1 : Gloc K v.1)) q σ₀,
             eM := fun _ => eM }, ?_, ?_, ?_⟩ <;>
    (dsimp only; exact Function.update_self (α := Places K S) _ _ _)

/-- **The genuine switch sides exist at an actual place** (non-vacuity; tex L5027–5086): for a place
`q ∈ S` with finite residue field of odd characteristic, and coefficients `M ≃ 𝔽₂²` on which
`G_{K,S}` acts trivially, there are tame data `D` at the places with the tame coordinates at `q`
(from the tame quotient of `G_{K_q}`, `exists_tame_coordinates`), and for every configuration `c`
the genuine finite and singular quasi sides at `q` (over `C^•_cont(G_{K,S}, M)` with `res_S`).
PROVED. Residual-field (`𝔽₂`) instance only; not applicable at height-one primes `≠ (2)`, see
`isEmpty_ringHom_zmod_two_heightOne`; the characteristic-zero version is the field-generic chain. -/
theorem exists_galSides (q : Places K S) [Finite (𝓞 K ⧸ q.1.asIdeal)]
    (hp : ringChar 𝓀[q.1.adicCompletion K] ≠ 2) (htriv : ∀ (g : GKS K S) (m : M), g • m = m)
    (eM : M ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    ∃ (D : PlaceTame K S M) (T : TameCoordinates (M := gMv K S M q) (D.I q) (D.φ q) (D.σ q)),
      ∀ c : Finset (Places K S),
        Nonempty (QuasiSwitchSide (galRel D c q T) (finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2))) ∧
        Nonempty (QuasiSwitchSide (galRel D c q T) (singPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2))) := by
  obtain ⟨φ, σ, -, hσ, hbij, hI⟩ := TameQuotient.exists_tame_coordinates (K := q.1.adicCompletion K) hp
  obtain ⟨D, hDI, hDφ, hDσ⟩ := PlaceTame.exists_at (M := M) q
    (TauCeti.inertiaSubgroup (q.1.adicCompletion K) : Subgroup (Gloc K q.1)) φ σ eM
  have TT : TameCoordinatesTrivial (G := Gloc K q.1) (M := gMv K S M q)
      (TauCeti.inertiaSubgroup (q.1.adicCompletion K)) φ σ 2 :=
    ⟨fun g m => by rw [ResMod.smul_def]; exact htriv _ m, ⟨eM⟩, hσ, hbij, hI⟩
  have T0 := tameCoordinates_of_trivial TT
  have T : TameCoordinates (M := gMv K S M q) (D.I q) (D.φ q) (D.σ q) := by
    rw [hDI, hDφ, hDσ]; exact T0
  exact ⟨D, T, fun c => ⟨⟨galFinSide D c q T⟩, ⟨galSingSide D c q T⟩⟩⟩

end Genuine

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
