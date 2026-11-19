import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericWiring
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericNonVacuity
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.NonVacuity

/-!
# RC53 SwitchInputs: the field-generic switch chain at the Λ-adic fibres

Proposition `ex:limits-uniform-lower-bound`, tex L4976–5195 ("use the actual primitive scalar
Selmer complex over `R = Λ_𝔭`", `k = Frac(Λ/𝔭)` of characteristic zero), with the derivative
conditions, tex L5027–5086, and the unramified condition, tex 3479–3498.

The field-generic chain (`GenericSides`, `GenericCoords`, `GenericWiring`) instantiated at the
residue field `k = k(𝔭) = ResAt 𝔭` of a height-one prime `𝔭 ≠ (2)` and the fibre
`M = V_𝔭 = VP K S W 𝔭 α` of the other team's Λ-adic coefficient module:

* `fibreLv_eq_locCxK` (PROVED, `rfl`): the local complexes of the generic switch families are the
  fibre local complexes `fibreLv W 𝔭 α`.
* `urSubK`, `urSubK_S_eq_range` (PROVED): the unramified conditions `fibreUrConditions` (the cocycle
  conditions `U⁰ = C⁰`, `U¹ = Z_ur + B¹`, `Uⁿ = 0`) as subcomplexes of the fibre local complexes:
  in every degree `urSubK v` is the image of the inclusion of `fibreUrConditions` at `v`.
* `fibreConds D` (definition): the configuration conditions with the unramified conditions as the
  finite conditions at every place and the singular derivative sides `singCond` as the singular
  conditions.
* `urSubK_eq_finCond`, `fibreConds_admissibleAt` (PROVED): at a place where `G_{K_q}` acts trivially
  on `V_𝔭` and `I_q` is the inertia group (the kernel of `G_{K_q} → Gal(K_q^ur/K_q)`), the
  unramified condition is the finite derivative side `sideOfSetK I_q`; so the fibre conditions are
  admissible at such a switch place.
* `fibreEquivFin2`, `tameCoordinatesTrivialK_fibre` (PROVED from the other team's `vpBasis`): the
  rank-two clause of `TameCoordinatesTrivialK` at `V_𝔭` is discharged by `dim_k V_𝔭 = 2`; the
  remaining clauses (trivial action, `σ ∈ I`, bijectivity of the tame coordinates, the inertia
  clause) stay GLUE inputs.
* `fibreFinSideK_Dside`, `fibreSingSideK_Dside` (PROVED): the side Selmer data of the genuine
  finite / singular quasi sides at `q` are `fibreSelData W 𝔭 α (condAt Δ₀ Δ_d c)` and
  `… (insert q c)`, `Δ₀` the unramified conditions (given the tame coordinates at `q` and `I_q` the
  inertia group).
* `galΦK_fibre_eq` (PROVED, `rfl`): the fibres of the generic switching family at `V_𝔭` are the
  other team's `fibreSelData W 𝔭 α (condAt Δ₀ Δ_d c)`; `zAct`, `lamAct` stay inputs.
* Non-vacuity at `E_1 : y² = x(x − 1)(x + 3)`, `𝔭 = (t)` (the other team's example): the fibre
  conditions and the rank-two discharge `fibreEquivFin2` (`example`s).
* `regular_at_fibre` (PROVED from the inputs): regularity `∃ a, ι a = u` over `A = Λ_𝔭` with the
  residue map `ρ = resAt 𝔭`; the residue hypothesis `hρ` is discharged.

**Caveat.** The remaining GLUE input at a switch place is `TameCoordinatesTrivialK` (trivial action
of `G_{K_q}` on `V_𝔭`, bijective tame coordinates, inertia clause). By
`not_bijective_coordQK_of_tame` (`GenericNonVacuity.lean`) the tame coordinates are not bijective
whenever `φ_q`, `σ_q` act trivially and satisfy `φσφ⁻¹ = σ^q` with `(q : k(𝔭)) ≠ 1`; a Frobenius
lift and a tame generator of `G_{K_q}` satisfy this relation modulo the wild inertia, and
`(q : k(𝔭)) ≠ 1` in characteristic zero: the coordinates `H¹(W_rel) ≅ k² × k²` are an `𝔽₂`
phenomenon, not available as stated at the characteristic-zero fibres. The duality input
(`LocalizationDualityInput`, `DualityFromSelmer` in the quadratic candidates) is a named input; no
finite-discrete duality is used.

**Modelling constraint (the switch coordinates at a single derivative prime).** The `2 + 2`
switch coordinates (finite and singular planes `F`, `S` of dimension two each, the shape used by
`QuasiNonquadStep`, (5.5a) and `RelaxedImageFinite`) exist only when `q ≡ 1` in the coefficient
field. At a single inert derivative prime `ℓ` the Frobenius of the completion is `Φ = J² = 1` and
the residue norm is `q = ℓ²` (tex L3298–3300), so `H¹ ≅ coker(Φ − 1) × ker(Φ − q)`
(`UnrCoords.coordEquivUnr`). With `k = k(𝔭)` of characteristic zero, `q = ℓ² ≠ 1` kills the singular
part (`singular_zero_of_q_ne_one`), and `two_plus_two_iff_q_eq_one` / `two_plus_two_iff_ell` show
the `2 + 2` shape holds iff `(q : k) = 1`. Elliot's shape is reached in the inner limit, where the
retained congruences give `ℓᵢ → −1` (tex L5030–5032). So the switch must be formalised on
inner-limit / `Λ`-adic objects across the derivative primes, not on `V_𝔭` at one prime. Planned
duality route: the named duality input of this chain can be discharged by the fibre duality five
lemma `selmerDuality_of_global_local` (modulo the print `NekovarFibreGlobalDuality`, Nekovář
5.6.3(ii) localised at `Λ/𝔭`) once it lands, provided the inner-limit objects are `k(𝔭)`-linear and
lattice-topologised.

**The inner-limit counterpart, and a limitation of `GaloisInputsK`.** The inner-limit switching
objects are built in a separate lane (`RC53Assist.InnerLimit.Objects`, not imported here): the limit
`H¹` identified with the `H¹` of the limiting tame complex, closed complementary rank-two switch
planes, a fixed-`𝔭` specialisation to `V_𝔭 × V_𝔭`, both `QuasiSwitchSide` values, the connecting map
with exactness and a conditional `QuasiNonquadStep (ResAt 𝔭)` wiring; their duality is the explicit
hypothesis `FibreInnerLimitPairingCertificate`. That is the counterpart of this file's fixed-place
chain. The family `GaloisInputsK` used here works at a FIXED place `q ∈ S` of one arithmetic field:
it cannot identify a MOVING derivative label (the inner-limit index `ℓᵢ → −1`) with one arithmetic
prime. A consumer passing from the inner-limit objects to these steps needs actual side-to-stage
equivalences and the arithmetic Galois/cochain comparisons; neither is supplied here. (Comments
only.)
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Manuscript.RC.SelmerComplex
  NumberField IsDedekindDomain ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Manuscript.RC.CoefModules (contD contB1 cfun condP condP_d_mem)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex (resUr)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] [IsHeightOneOdd P]
  (α : GKS K S →* Lambdaˣ) [IsContChar α]

/-- **The local complexes of the generic switch families at `V_𝔭` are the fibre local complexes**
`fibreLv W 𝔭 α` (`rfl`). PROVED. -/
theorem fibreLv_eq_locCxK :
    locCxK (ResAt P) (gGvK K S) (gMvK K S (VP K S W P α)) = fibreLv W P α := rfl

/-! ### The unramified conditions as subcomplexes -/

variable (K S) in
/-- The continuous cochains of `V_𝔭` at the decomposition group of `v`. -/
abbrev fibC (v : Places K S) : CochainComplex (ModuleCat.{0} (ResAt P)) ℕ :=
  contCochains (ResAt P) (Gloc K v.1) (ResMod (locMap K S v.1) (VP K S W P α))

/-- The unramified cocycles `Z_ur` at `v` (the other team's `urZ`), as a submodule of the degree-one
term of the fibre local complex. -/
def urZX (v : Places K S) : Submodule (ResAt P) ((fibC K S W P α v).X 1) := urZ K S W P α v

/-- The continuous coboundaries `B¹` at `v`, as a submodule of the degree-one term. -/
def urB1X (v : Places K S) : Submodule (ResAt P) ((fibC K S W P α v).X 1) := contB1 _ _ _

/-- **The unramified conditions of `V_𝔭` at `v` as a subcomplex** of the fibre local complex: `C⁰`
in degree `0`, `Z_ur + B¹` in degree `1`, `0` elsewhere (tex 3479–3498). -/
def urSubK (v : Places K S) : SubFam (fibreLv W P α v) :=
  degSub (fibC K S W P α v) ⊤ (urZX W P α v ⊔ urB1X W P α v)
    (fun x _ => Submodule.mem_sup_right
      (show _ ∈ contB1 _ _ _ from LinearMap.mem_range_self (contD _ _ _ 0) x))
    (fun x hx => (Submodule.mem_bot (ResAt P)).1
      (condP_d_mem (urZ K S W P α v) (fun _ hz => hz.1) 1 x hx))

/-- **`urSubK` is `fibreUrConditions`** (tex 3479–3498): in every degree, `urSubK v` is the image of
the inclusion of the unramified condition `fibreUrConditions` at `v` into the fibre local complex.
PROVED. -/
theorem urSubK_S_eq_range (v : Places K S) (n : ℤ) :
    (urSubK W P α v).S n = LinearMap.range (((fibreUrConditions W P α).i v).f n n rfl) := by
  rcases n with (_ | _ | n) | n
  · exact (Submodule.range_subtype _).symm
  · exact (Submodule.range_subtype _).symm
  · exact (Submodule.range_subtype _).symm
  · exact (LinearMap.range_zero).symm

omit [NumberField K] in
/-- `degSub` depends only on its two submodules. PROVED. -/
theorem degSub_congr {k : Type} [Field k] (C : CochainComplex (ModuleCat.{0} k) ℕ)
    {A A' : Submodule k (C.X 0)} {B B' : Submodule k (C.X 1)} (hA : A = A') (hB : B = B')
    (h01 : ∀ x ∈ A, (C.d 0 1).hom x ∈ B) (h12 : ∀ x ∈ B, (C.d 1 2).hom x = 0)
    (h01' : ∀ x ∈ A', (C.d 0 1).hom x ∈ B') (h12' : ∀ x ∈ B', (C.d 1 2).hom x = 0) :
    degSub C A B h01 h12 = degSub C A' B' h01' h12' := by
  subst hA hB
  rfl

/-! ### The unramified condition is the finite derivative side at a trivial switch place -/

section Switch

variable {W P α}

/-- **The unramified condition is the finite derivative side** at a place `q` where `G_{K_q}` acts
trivially on `V_𝔭` and `I_q` is the inertia group (the kernel of `G_{K_q} → Gal(K_q^ur/K_q)`):
`urSubK q = finCond q` (tex 3479–3498, L5057–5058). PROVED. -/
theorem urSubK_eq_finCond (D : PlaceTameK K S) (q : Places K S)
    (htriv : ∀ (g : Gloc K q.1) (m : gMvK K S (VP K S W P α) q), g • m = m)
    (hI : ∀ h : Gloc K q.1, h ∈ D.I q ↔ resUr K q.1 h = 1) :
    urSubK W P α q = D.finCond (ResAt P) (VP K S W P α) q := by
  unfold urSubK PlaceTameK.finCond sideSubK
  apply degSub_congr
  · refine (top_unique ?_).symm
    intro a _
    simp only [sideOfSetK, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
      LinearMap.sub_apply, DistribSMul.toLinearMap_apply, LinearMap.id_apply]
    intro h
    rw [htriv, sub_self]
  · ext x
    constructor
    · intro hx
      have hZ1 : x ∈ Z1K (ResAt P) (Gloc K q.1) (gMvK K S (VP K S W P α) q) := by
        rw [LinearMap.mem_ker]
        exact (Submodule.mem_bot (ResAt P)).1
          (condP_d_mem (urZ K S W P α q) (fun _ hz => hz.1) 1 x hx)
      refine ⟨⟨x, hZ1⟩, (mem_sideOfSetK_BF _ _).2 ?_, rfl⟩
      intro h hh
      obtain ⟨z, hz, b, hb, rfl⟩ := (Submodule.mem_sup (p := urZX W P α q) (p' := urB1X W P α q)).1
          hx
      obtain ⟨c, rfl⟩ := (LinearMap.mem_range
        (f := contD (ResAt P) (Gloc K q.1) (gMvK K S (VP K S W P α) q) 0)).1 hb
      have hb0 : ev1K (contD _ _ _ 0 c : (fibC K S W P α q).X 1) h = 0 := by
        have := relaxedDK_ev (k := ResAt P) (G := Gloc K q.1) (M := gMvK K S (VP K S W P α) q) c h
        rw [htriv, sub_self] at this
        exact this
      have hzZ : z ∈ Z1K (ResAt P) (Gloc K q.1) (gMvK K S (VP K S W P α) q) := hz.1
      have hz1 := ev1K_one_of_trivial htriv ⟨z, hzZ⟩
      have hzh : ev1K (z : (fibC K S W P α q).X 1) h = 0 := by
        refine (hz.2 (fun _ => h) (fun _ => 1) ?_).trans hz1
        rw [(hI h).1 hh, map_one]
      change ev1K (z : (fibC K S W P α q).X 1) h +
        ev1K (contD _ _ _ 0 c : (fibC K S W P α q).X 1) h = 0
      rw [hzh, hb0, add_zero]
    · rintro ⟨z, hz, rfl⟩
      replace hz := (mem_sideOfSetK_BF _ _).1 hz
      refine Submodule.mem_sup_left (show (z : (fibC K S W P α q).X 1) ∈ urZ K S W P α q from
        ⟨z.2, fun g g' hg => ?_⟩)
      have hg1 : g = fun _ => g 0 := funext fun i => by rw [Subsingleton.elim i 0]
      have hg2 : g' = fun _ => g' 0 := funext fun i => by rw [Subsingleton.elim i 0]
      have hm : g' 0 = g 0 * ((g 0)⁻¹ * g' 0) := by group
      have hmem : (g 0)⁻¹ * g' 0 ∈ D.I q := by
        rw [hI, map_mul, map_inv, hg, inv_mul_cancel]
      have h2 := ev1K_mul_of_trivial htriv z (g 0) ((g 0)⁻¹ * g' 0)
      rw [← hm, hz _ hmem, add_zero] at h2
      rw [hg1, hg2]
      exact h2.symm

end Switch

/-! ### The configuration conditions and the inputs at the fibre -/

/-- **The configuration conditions at `V_𝔭`**: the unramified conditions `urSubK` (the other
team's `fibreUrConditions`, `urSubK_S_eq_range`) as the finite conditions at every place, and the
singular derivative sides `singCond` as the singular conditions. -/
def fibreConds (D : PlaceTameK K S) : SwitchCondsK (ResAt P) K S (VP K S W P α) :=
  ⟨D, urSubK W P α, D.singCond (ResAt P) (VP K S W P α)⟩

/-- **The fibre conditions are admissible at a trivial switch place** (tex L5060–5061): if
`G_{K_q}` acts trivially on `V_𝔭` and `I_q` is the inertia group, the finite and singular
conditions at `q` are the derivative sides. PROVED. -/
theorem fibreConds_admissibleAt (D : PlaceTameK K S) (q : Places K S)
    (htriv : ∀ (g : Gloc K q.1) (m : gMvK K S (VP K S W P α) q), g • m = m)
    (hI : ∀ h : Gloc K q.1, h ∈ D.I q ↔ resUr K q.1 h = 1) :
    (fibreConds W P α D).AdmissibleAt q :=
  ⟨urSubK_eq_finCond D q htriv hI, rfl⟩

/-- **`V_𝔭 ≃ k(𝔭)²` at the decomposition groups** (from the other team's basis `vpBasis`,
`dim_{k(𝔭)} V_𝔭 = 2`). -/
def fibreEquivFin2 [W.IsElliptic] [HasFullTwoTorsion K S W] (q : Places K S) :
    gMvK K S (VP K S W P α) q ≃ₗ[ResAt P] (Fin 2 → ResAt P) :=
  (vpBasis (K := K) (S := S) (W := W) (α := α) P).equivFun

/-- **The tame coordinates at `V_𝔭`, with the rank-two clause discharged** by `dim V_𝔭 = 2`
(`fibreEquivFin2`): the remaining clauses (trivial action, `σ ∈ I`, bijectivity of the tame
coordinates, the inertia clause) are the GLUE inputs. Classification: PROVED (from the inputs). -/
theorem tameCoordinatesTrivialK_fibre [W.IsElliptic] [HasFullTwoTorsion K S W] (q : Places K S)
    {I : Subgroup (Gloc K q.1)} {φ σ : Gloc K q.1}
    (htriv : ∀ (g : Gloc K q.1) (m : gMvK K S (VP K S W P α) q), g • m = m) (hσI : σ ∈ I)
    (hbij : Function.Bijective
      (coordQK (k := ResAt P) (M := gMvK K S (VP K S W P α) q) φ σ (htriv φ) (htriv σ)))
    (hI : ∀ z : Z1K (ResAt P) (Gloc K q.1) (gMvK K S (VP K S W P α) q),
      ev1K (z : (fibC K S W P α q).X 1) σ = 0 → ∀ h ∈ I, ev1K (z : (fibC K S W P α q).X 1) h = 0) :
    TameCoordinatesTrivialK (ResAt P) (gMvK K S (VP K S W P α) q) I φ σ :=
  ⟨htriv, ⟨fibreEquivFin2 W P α q⟩, hσI, hbij, hI⟩

/-- **The finite quasi side at `V_𝔭` has the fibre Selmer data of `c`** (tex L5060–5082): with tame
coordinates `T` at `q ∉ c` and `I_q` the inertia group, the side Selmer data of the genuine finite
quasi side is `fibreSelData W 𝔭 α (condAt Δ₀ Δ_d c)`, `Δ₀` the unramified conditions. PROVED. -/
theorem fibreFinSideK_Dside (D : PlaceTameK K S) (c : Finset (Places K S)) (q : Places K S)
    (T : TameCoordinatesTrivialK (ResAt P) (gMvK K S (VP K S W P α) q) (D.I q) (D.φ q) (D.σ q))
    (hq : q ∉ c) (hI : ∀ h : Gloc K q.1, h ∈ D.I q ↔ resUr K q.1 h = 1) :
    (galFinSideK (fibreConds W P α D) c q T).Dside =
      fibreSelData W P α (condAt K S (ResAt P) (VP K S W P α)
        (galCond K S _ (fibreConds W P α D).A₀) (galCond K S _ (fibreConds W P α D).Ad) c) :=
  galFinSideK_Dside (fibreConds W P α D) c q T hq (urSubK_eq_finCond D q T.htriv hI)

open Classical in
/-- **The singular quasi side at `V_𝔭` has the fibre Selmer data of `insert q c`** (tex
L5060–5082). PROVED. -/
theorem fibreSingSideK_Dside (D : PlaceTameK K S) (c : Finset (Places K S)) (q : Places K S)
    (T : TameCoordinatesTrivialK (ResAt P) (gMvK K S (VP K S W P α) q) (D.I q) (D.φ q) (D.σ q)) :
    (galSingSideK (fibreConds W P α D) c q T).Dside =
      fibreSelData W P α (condAt K S (ResAt P) (VP K S W P α)
        (galCond K S _ (fibreConds W P α D).A₀) (galCond K S _ (fibreConds W P α D).Ad)
        (insert q c)) :=
  galSingSideK_Dside (fibreConds W P α D) c q T rfl

section Family

variable (D : PlaceTameK K S) {A : Type} [CommRing A] (c₀ : Finset (Places K S)) (t : A)
  (zAct : (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
    (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
      (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.X 1)
  (hzAct : ((selCx (galoisSelData K S (ResAt P) (VP K S W P α)
    (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
      (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.d 1 2).hom zAct = 0)
  (lamAct : (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
    (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
      (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.X 2 →ₗ[ResAt P] ResAt P)
  (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S (ResAt P) (VP K S W P α)
    (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
      (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.d 1 2).hom y) = 0)

/-- **The fibres of the generic switching family at `V_𝔭` are the other team's fibre Selmer
data** `fibreSelData W 𝔭 α (condAt Δ₀ Δ_d c)` (`rfl`); the actual class `zAct` and functional
`lamAct` are inputs (placeholders `0` in the other team's `fibreFamily`). PROVED. -/
theorem galΦK_fibre_eq (c : Finset (Places K S)) :
    (galΦK (fibreConds W P α D) A c₀ t zAct hzAct lamAct hlamAct).fibre c =
      fibreSelData W P α (condAt K S (ResAt P) (VP K S W P α)
        (galCond K S _ (fibreConds W P α D).A₀) (galCond K S _ (fibreConds W P α D).Ad) c) :=
  rfl

end Family

/-- **Regularity at the fibre** (tex L4976–5195): over `A = Λ_𝔭` with the residue map
`ρ = resAt 𝔭 : Λ_𝔭 → k(𝔭)`, the field-generic Galois switching inputs `GaloisInputsK` for the
fibre conditions give `∃ a, ι a = u`; the residue hypothesis is discharged. PROVED (from the
inputs). -/
theorem regular_at_fibre (D : PlaceTameK K S) (c₀ : Finset (Places K S)) {F : Type} [Field F]
    {ι : Localization.AtPrime P →+* F}
    (hι : Function.Injective ι) (t : Localization.AtPrime P)
    (zAct : (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
        (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.X 1)
    (hzAct : ((selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
        (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.d 1 2).hom zAct = 0)
    (lamAct : (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
        (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.X 2 →ₗ[ResAt P] ResAt P)
    (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S _ (fibreConds W P α D).A₀)
        (galCond K S _ (fibreConds W P α D).Ad) c₀))).toCC.d 1 2).hom y) = 0) {u : F}
    (X : GaloisInputsK (fibreConds W P α D) (resAt P) c₀ t zAct hzAct lamAct hlamAct ι u) :
    ∃ a : Localization.AtPrime P, ι a = u :=
  regular_of_galoisInputsK hι (fun x hx => (IsLocalRing.residue_eq_zero_iff x).2 hx) X

/-! ### Non-vacuity at the curve `E_1 : y² = x(x − 1)(x + 3)` and `𝔭 = (t)` -/

/-- **Non-vacuity of the fibre conditions** (the other team's genuine example: `E_1` over `ℚ`,
`𝔭 = (t)`, `α = χ_1 Ψ_0`, all places): the configuration conditions with the unramified conditions
exist (any tame data). PROVED. -/
example : SwitchCondsK (ResAt Pt0) ℚ Set.univ (VP ℚ Set.univ curveE1 Pt0 (alphaLam ℚ Set.univ)) :=
  fibreConds curveE1 Pt0 (alphaLam ℚ Set.univ) ⟨fun _ => ⊥, fun _ => 1, fun _ => 1⟩

/-- **Non-vacuity of the rank-two discharge**: `V_(t)(E_1) ≃ k((t))²` at every decomposition group
(`HasFullTwoTorsion ℚ Set.univ E_1`). PROVED. -/
example (q : Places ℚ Set.univ) :
    gMvK ℚ Set.univ (VP ℚ Set.univ curveE1 Pt0 (alphaLam ℚ Set.univ)) q ≃ₗ[ResAt Pt0]
      (Fin 2 → ResAt Pt0) :=
  fibreEquivFin2 curveE1 Pt0 (alphaLam ℚ Set.univ) q

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
