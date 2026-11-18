import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.ExactSequences
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SignSplitting
import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.Regularity

/-!
# RC53 SwitchInputs: the sign-part switch count on the axes, and the Galois cocycle involution

Proof of Proposition `ex:limits-uniform-lower-bound`, quadratic case (tex L5003–5136).

**(5.5a) on the axes** (tex L5046–5054, L5076–5086). At a new inert derivative prime the local
involution is `(x, y) ↦ (Jx, −Jy)` on `F ⊕ S` (`localInv`, tex L5026–5027). Its `+`-part of the finite
plane is the finite axis `F(e₊)`, its `−`-part is `F(e₋)`; on the singular plane the `+`-part is
`S(e₋)` and the `−`-part is `S(e₊)`; and the sign parts of the relaxed image `U` are `U ∩ H_±`. So the
sign-part count `SignDimsOfExact` of `ExactSequences.lean` lands in the axis shape of the quadratic
switch data `QuadMixedDims` / `QuadSingleDims` of `UniformSwitch/Regularity.lean`.

Nodes (PROVED):
* `SignPartsAxes`: the identification of the sign parts of `F`, `S` (embedded by `inl`, `inr`) with
  the axes, and of `signPart (localInv J) (±1)` with `H_±`.
* `SignDimsAxes`: the four (5.5a) equations on the axes (`hVp`, `hVm`, `hVp'`, `hVm'` shapes).
* `quadMixedDimsOfInputs` (a constructor of `QuadMixedDims`) and `quadSingleDimsOfInputs` (of
  `QuadSingleDims`), from the sign-equivariant (5.5a) data, the localization-duality hypothesis
  (GLUE, Nekovář 6.3.3–6.3.4, in the type) and the detecting-prime inputs (GLUE).

**The Galois cocycle involution** (tex L5009–5013). `GaloisCocycleInvolution` is the explicitly named
GLUE input "the involution `σ` of the fibre Selmer complex is the cocycle action
`c ↦ J c(τ⁻¹ g τ)`": `Γ` a group, `Δ` an index-two subgroup, `τ ∉ Δ` with `τ² = 1` (the actual
complex conjugation), `ρ : Γ → End(T)` the coefficient action with `J = ρ(τ)`, a stated cochain model
`ev : K¹ → (Δ → T)` of the degree-one cochains, and the localization on cohomology at the derivative
prime. Its conclusion: an involutive chain automorphism `σ` of `K` whose degree-one component is the
cocycle action on the model, and whose action on `H¹` is compatible with the local involution
(`J` on `F`, `−J` on `S`, tex L5027–5037). `cocycleAct_involutive` (PROVED) is the cochain-level
identity behind it; `signSplitting_of_galois` and `quadSignFields_of_galois` consume it.
-/

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory Module ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

/-! ### Sign parts of the planes are the axes -/

section Axes

variable {k : Type} [Field k] {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)} {ep em : Fin 2 → k}

/-- The finite plane embedding `F → F ⊕ S`, `x ↦ (x, 0)`. -/
abbrev inlF : (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k) := LinearMap.inl k _ _

/-- The singular plane embedding `S → F ⊕ S`, `y ↦ (0, y)`. -/
abbrev inrS : (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k) := LinearMap.inr k _ _

theorem signPart_one_iff {X : Type} [AddCommGroup X] [Module k X] {σ : X →ₗ[k] X} {x : X} :
    x ∈ signPart σ (1 : k) ↔ σ x = x := by
  rw [mem_signPart, one_smul]

theorem signPart_neg_one_iff {X : Type} [AddCommGroup X] [Module k X] {σ : X →ₗ[k] X} {x : X} :
    x ∈ signPart σ (-1 : k) ↔ σ x = -x := by
  rw [mem_signPart, neg_one_smul]

theorem map_inl_plus (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    (signPart J (1 : k)).map inlF = finAxis ep := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, signPart_one_iff] at hx
    have hmem : ((x, 0) : (Fin 2 → k) × (Fin 2 → k)) ∈ signPlane ep em :=
      (mem_signPlane_plus_iff h2 hp hm he _).2 ⟨hx, by simp⟩
    obtain ⟨a, b, hab⟩ := mem_signPlane.1 hmem
    exact mem_finAxis.2 ⟨a, Prod.ext (by simpa using congrArg Prod.fst hab) (by simp)⟩
  · intro hu
    obtain ⟨a, rfl⟩ := mem_finAxis.1 hu
    exact ⟨a • ep, by rw [SetLike.mem_coe, signPart_one_iff, map_smul, hp], rfl⟩

theorem map_inl_minus (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    (signPart J (-1 : k)).map inlF = finAxis em := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, signPart_neg_one_iff] at hx
    have hmem : ((x, 0) : (Fin 2 → k) × (Fin 2 → k)) ∈ signPlane em ep :=
      (mem_signPlane_minus_iff h2 hp hm he _).2 ⟨hx, by simp⟩
    obtain ⟨a, b, hab⟩ := mem_signPlane.1 hmem
    exact mem_finAxis.2 ⟨a, Prod.ext (by simpa using congrArg Prod.fst hab) (by simp)⟩
  · intro hu
    obtain ⟨a, rfl⟩ := mem_finAxis.1 hu
    exact ⟨a • em, by rw [SetLike.mem_coe, signPart_neg_one_iff, map_smul, hm, smul_neg], rfl⟩

theorem map_inr_plus (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    (signPart (-J) (1 : k)).map inrS = singAxis em := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, signPart_one_iff, LinearMap.neg_apply, neg_eq_iff_eq_neg] at hy
    have hmem : ((0, y) : (Fin 2 → k) × (Fin 2 → k)) ∈ signPlane ep em :=
      (mem_signPlane_plus_iff h2 hp hm he _).2 ⟨by simp, hy⟩
    obtain ⟨a, b, hab⟩ := mem_signPlane.1 hmem
    exact mem_singAxis.2 ⟨b, Prod.ext (by simp) (by simpa using congrArg Prod.snd hab)⟩
  · intro hu
    obtain ⟨b, rfl⟩ := mem_singAxis.1 hu
    exact ⟨b • em, by rw [SetLike.mem_coe, signPart_one_iff, LinearMap.neg_apply, map_smul, hm,
      smul_neg, neg_neg], rfl⟩

theorem map_inr_minus (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0) :
    (signPart (-J) (-1 : k)).map inrS = singAxis ep := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, signPart_neg_one_iff, LinearMap.neg_apply, neg_inj] at hy
    have hmem : ((0, y) : (Fin 2 → k) × (Fin 2 → k)) ∈ signPlane em ep :=
      (mem_signPlane_minus_iff h2 hp hm he _).2 ⟨by simp, hy⟩
    obtain ⟨a, b, hab⟩ := mem_signPlane.1 hmem
    exact mem_singAxis.2 ⟨b, Prod.ext (by simp) (by simpa using congrArg Prod.snd hab)⟩
  · intro hu
    obtain ⟨b, rfl⟩ := mem_singAxis.1 hu
    exact ⟨b • ep, by rw [SetLike.mem_coe, signPart_neg_one_iff, LinearMap.neg_apply, map_smul,
      hp], rfl⟩

theorem signPart_localInv_one (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) : signPart (localInv J) (1 : k) = signPlane ep em := by
  rw [plus_eq_signPlane h2 hp hm he]
  ext u
  rw [signPart_one_iff, mem_plusPart]

theorem signPart_localInv_neg (h2 : (2 : k) ≠ 0) (hp : J ep = ep) (hm : J em = -em)
    (he : e₂ ep em ≠ 0) : signPart (localInv J) (-1 : k) = signPlane em ep := by
  rw [minus_eq_signPlane h2 hp hm he]
  ext u
  rw [signPart_neg_one_iff, mem_minusPart]

/-- **The sign parts of the planes are the axes** (tex L5026–5054). For `J² = 1`, `2 ≠ 0` and
eigenvectors `e_±` with `e₂(e₊, e₋) ≠ 0`: the `±`-parts of `F` (for `J`) embedded in `F ⊕ S` are the
finite axes `F(e_±)`, the `±`-parts of `S` (for `−J`) are `S(e_∓)`, and the `±`-parts of `F ⊕ S` for the
local involution are `H_±`. Classification: PROVED. -/
def SignPartsAxes : Prop :=
  ∀ (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k),
    (2 : k) ≠ 0 → J ep = ep → J em = -em → e₂ ep em ≠ 0 →
    (signPart J (1 : k)).map inlF = finAxis ep ∧ (signPart J (-1 : k)).map inlF = finAxis em ∧
    (signPart (-J) (1 : k)).map inrS = singAxis em ∧
    (signPart (-J) (-1 : k)).map inrS = singAxis ep ∧
    signPart (localInv J) (1 : k) = signPlane ep em ∧
    signPart (localInv J) (-1 : k) = signPlane em ep

theorem signPartsAxes_proof : SignPartsAxes := by
  intro k _ J ep em h2 hp hm he
  exact ⟨map_inl_plus h2 hp hm he, map_inl_minus h2 hp hm he, map_inr_plus h2 hp hm he,
    map_inr_minus h2 hp hm he, signPart_localInv_one h2 hp hm he,
    signPart_localInv_neg h2 hp hm he⟩

/-- The sign parts of the image of an equivariant map are the image of the sign parts. -/
theorem map_signPart_eq_inf {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y]
    [Module k Y] (h2 : (2 : k) ≠ 0) {ε : k} (hε : ε * ε = 1) {σX : X →ₗ[k] X}
    (hσX : σX ∘ₗ σX = LinearMap.id) {σY : Y →ₗ[k] Y} (f : X →ₗ[k] Y) (hf : f ∘ₗ σX = σY ∘ₗ f) :
    (signPart σX ε).map f = LinearMap.range f ⊓ signPart σY ε := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self f x, map_mem_signPart f hf hx⟩
  · intro u hu
    obtain ⟨⟨v, rfl⟩, hv⟩ := Submodule.mem_inf.1 hu
    refine ⟨(2 : k)⁻¹ • (v + ε • σX v), proj_mem_signPart hσX hε v, ?_⟩
    have hfσ : f (σX v) = σY (f v) := by rw [← LinearMap.comp_apply, hf, LinearMap.comp_apply]
    simp only [map_smul, map_add, hfσ]
    exact proj_eq_self h2 hε hv

end Axes

/-! ### (5.5a) on the axes -/

section Dims

variable {k : Type} [Field k]

theorem localInv_comp_inl (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    inlF ∘ₗ J = localInv J ∘ₗ inlF := by
  ext x <;> simp

theorem localInv_comp_inr (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    inrS ∘ₗ (-J) = localInv J ∘ₗ inrS := by
  ext x <;> simp

theorem snd_comp_localInv (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    LinearMap.snd k (Fin 2 → k) (Fin 2 → k) ∘ₗ localInv J =
      (-J) ∘ₗ LinearMap.snd k (Fin 2 → k) (Fin 2 → k) := by
  ext x <;> simp

theorem fst_comp_localInv (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) :
    LinearMap.fst k (Fin 2 → k) (Fin 2 → k) ∘ₗ localInv J =
      J ∘ₗ LinearMap.fst k (Fin 2 → k) (Fin 2 → k) := by
  ext x <;> simp

theorem negJ_involutive {J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)} (hJ2 : J ∘ₗ J = LinearMap.id) :
    (-J) ∘ₗ (-J) = LinearMap.id := by
  rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, hJ2]

/-- **The four (5.5a) equations on the axes** (tex L5046–5054, L5076–5086; the fields `hVp`, `hVm`,
`hVp'`, `hVm'` of `QuadMixedDims`). Over a field `k` with `2 ≠ 0`, let `J² = 1` with eigenvectors
`e_±` (`e₂(e₊, e₋) ≠ 0`). Let `K₀ = H¹(C_str ⊗ k)`, `V = H¹(C_F ⊗ k)`, `V' = H¹(C_S ⊗ k)`,
`V_rel = H¹(C_rel ⊗ k)` carry involutions (the cocycle action), with the sign-equivariant data of the
two cone triangles: `α : K₀ → V` injective onto the kernel of the finite localization `β : V → F`,
`γ : V → V_rel` onto the kernel of the singular component of the relaxed localization
`λ : V_rel → F ⊕ S`, `λγ = inl β`; symmetrically `α' : K₀ → V'`, `β' : V' → S`, `γ' : V' → V_rel`
with `λγ' = inr β'`. With `U = im λ`, `U_± = U ⊓ H_±`:
`dim V_+ = dim K₀_+ + dim (U_+ ⊓ F(e₊))`, `dim V_- = dim K₀_- + dim (U_- ⊓ F(e₋))`,
`dim V'_+ = dim K₀_+ + dim (U_+ ⊓ S(e₋))`, `dim V'_- = dim K₀_- + dim (U_- ⊓ S(e₊))`.
Classification: PROVED. -/
def SignDimsAxes : Prop :=
  ∀ (k : Type) [Field k] (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (ep em : Fin 2 → k)
    (K₀ V V' Vr : Type) [AddCommGroup K₀] [Module k K₀] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup Vr] [Module k Vr]
    [FiniteDimensional k V] [FiniteDimensional k V']
    (α : K₀ →ₗ[k] V) (β : V →ₗ[k] (Fin 2 → k)) (γ : V →ₗ[k] Vr)
    (α' : K₀ →ₗ[k] V') (β' : V' →ₗ[k] (Fin 2 → k)) (γ' : V' →ₗ[k] Vr)
    (lam : Vr →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (σK : K₀ →ₗ[k] K₀) (σV : V →ₗ[k] V) (σV' : V' →ₗ[k] V') (σr : Vr →ₗ[k] Vr),
    (2 : k) ≠ 0 → J ∘ₗ J = LinearMap.id → J ep = ep → J em = -em → e₂ ep em ≠ 0 →
    σK ∘ₗ σK = LinearMap.id → σV ∘ₗ σV = LinearMap.id → σV' ∘ₗ σV' = LinearMap.id →
    σr ∘ₗ σr = LinearMap.id →
    α ∘ₗ σK = σV ∘ₗ α → β ∘ₗ σV = J ∘ₗ β → γ ∘ₗ σV = σr ∘ₗ γ →
    α' ∘ₗ σK = σV' ∘ₗ α' → β' ∘ₗ σV' = (-J) ∘ₗ β' → γ' ∘ₗ σV' = σr ∘ₗ γ' →
    lam ∘ₗ σr = localInv J ∘ₗ lam →
    Function.Injective α → LinearMap.range α = LinearMap.ker β →
    LinearMap.range γ = LinearMap.ker (LinearMap.snd k _ _ ∘ₗ lam) → lam ∘ₗ γ = inlF ∘ₗ β →
    Function.Injective α' → LinearMap.range α' = LinearMap.ker β' →
    LinearMap.range γ' = LinearMap.ker (LinearMap.fst k _ _ ∘ₗ lam) → lam ∘ₗ γ' = inrS ∘ₗ β' →
      finrank k ↥(signPart σV (1 : k)) = finrank k ↥(signPart σK (1 : k)) +
        finrank k ↥((LinearMap.range lam ⊓ signPlane ep em) ⊓ finAxis ep) ∧
      finrank k ↥(signPart σV (-1 : k)) = finrank k ↥(signPart σK (-1 : k)) +
        finrank k ↥((LinearMap.range lam ⊓ signPlane em ep) ⊓ finAxis em) ∧
      finrank k ↥(signPart σV' (1 : k)) = finrank k ↥(signPart σK (1 : k)) +
        finrank k ↥((LinearMap.range lam ⊓ signPlane ep em) ⊓ singAxis em) ∧
      finrank k ↥(signPart σV' (-1 : k)) = finrank k ↥(signPart σK (-1 : k)) +
        finrank k ↥((LinearMap.range lam ⊓ signPlane em ep) ⊓ singAxis ep)

theorem signDimsAxes_proof : SignDimsAxes := by
  intro k _ J ep em K₀ V V' Vr _ _ _ _ _ _ _ _ _ _ α β γ α' β' γ' lam σK σV σV' σr h2 hJ2 hp hm he
    hK hV hV' hr hα' hβ' hγ' hα'' hβ'' hγ'' hl hα hαβ hγ hc hαS hαβS hγS hcS
  have hM := localInv_involutive J hJ2
  have hnJ := negJ_involutive hJ2
  have h1 : (1 : k) * 1 = 1 := one_mul 1
  have hm1 : (-1 : k) * -1 = 1 := by ring
  have hinl : Function.Injective (inlF (k := k)) := LinearMap.inl_injective
  have hinr : Function.Injective (inrS (k := k)) := LinearMap.inr_injective
  have hkerF : LinearMap.ker (LinearMap.snd k (Fin 2 → k) (Fin 2 → k)) = LinearMap.range inlF :=
    (LinearMap.range_inl k _ _).symm
  have hkerS : LinearMap.ker (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)) = LinearMap.range inrS :=
    (LinearMap.range_inr k _ _).symm
  -- the F-side and S-side sign counts
  have F_side := fun (ε : k) (hε : ε * ε = 1) =>
    signDimsOfExact_proof.{0} k K₀ V Vr ((Fin 2 → k) × (Fin 2 → k)) (Fin 2 → k) (Fin 2 → k)
      α β γ lam inlF (LinearMap.snd k _ _) σK σV σr (localInv J) J (-J) ε h2 hε hK hV hr hM hJ2
      hα' hβ' hγ' hl (localInv_comp_inl J) (snd_comp_localInv J) hα hαβ hγ hc hinl hkerF
  have S_side := fun (ε : k) (hε : ε * ε = 1) =>
    signDimsOfExact_proof.{0} k K₀ V' Vr ((Fin 2 → k) × (Fin 2 → k)) (Fin 2 → k) (Fin 2 → k)
      α' β' γ' lam inrS (LinearMap.fst k _ _) σK σV' σr (localInv J) (-J) J ε h2 hε hK hV' hr hM
      hnJ hα'' hβ'' hγ'' hl (localInv_comp_inr J) (fst_comp_localInv J) hαS hαβS hγS hcS hinr
      hkerS
  have imP : (signPart σr (1 : k)).map lam = LinearMap.range lam ⊓ signPlane ep em := by
    rw [map_signPart_eq_inf h2 h1 hr lam hl, signPart_localInv_one h2 hp hm he]
  have imM : (signPart σr (-1 : k)).map lam = LinearMap.range lam ⊓ signPlane em ep := by
    rw [map_signPart_eq_inf h2 hm1 hr lam hl, signPart_localInv_neg h2 hp hm he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := F_side 1 h1
    rwa [imP, map_inl_plus h2 hp hm he] at this
  · have := F_side (-1) hm1
    rwa [imM, map_inl_minus h2 hp hm he] at this
  · have := S_side 1 h1
    rwa [imP, map_inr_plus h2 hp hm he] at this
  · have := S_side (-1) hm1
    rwa [imM, map_inr_minus h2 hp hm he] at this

end Dims

/-! ### The quadratic switch data -/

section Constructors

variable {k : Type} [Field k]

/-- **GLUE input: a detecting prime for the `+` sign only** (tex L5123–5136, one sign only): the
localization of a class `c₊ ∈ V₊` is nonzero. Classification: GLUE (assumed input). -/
def DetectingPrimePlus {V : Type} [AddCommGroup V] [Module k V] (T : V →ₗ[k] V)
    (loc : V →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (cp : V) : Prop :=
  T cp = cp → loc cp ≠ 0

/-- **The mixed-sign quadratic switch data from the cone triangles** (tex L5003–5122). From the
sign-equivariant (5.5a) data of `SignDimsAxes`, the localization duality `U = U^⊥` for
`U = im λ` (GLUE: Nekovář 6.3.3–6.3.4, as the hypothesis `hU`), the detecting prime for classes
`c_± ∈ V_±` (GLUE `DetectingPrime`, for the localization `λ ∘ γ` of `V`), and the sign dimensions
`sp, sm, sp', sm'` of `V`, `V'`, this produces the data `QuadMixedDims sp sm sp' sm'` of the
UniformSwitch files, with `U_± = U ⊓ H_±` and `kp, km` the sign dimensions of `K₀`. -/
noncomputable def quadMixedDimsOfInputs (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k)
    (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0)
    {K₀ V V' Vr : Type} [AddCommGroup K₀] [Module k K₀] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup Vr] [Module k Vr]
    [FiniteDimensional k V] [FiniteDimensional k V']
    (α : K₀ →ₗ[k] V) (β : V →ₗ[k] (Fin 2 → k)) (γ : V →ₗ[k] Vr)
    (α' : K₀ →ₗ[k] V') (β' : V' →ₗ[k] (Fin 2 → k)) (γ' : V' →ₗ[k] Vr)
    (lam : Vr →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (σK : K₀ →ₗ[k] K₀) (σV : V →ₗ[k] V) (σV' : V' →ₗ[k] V') (σr : Vr →ₗ[k] Vr)
    (hK : σK ∘ₗ σK = LinearMap.id) (hV : σV ∘ₗ σV = LinearMap.id)
    (hV' : σV' ∘ₗ σV' = LinearMap.id) (hr : σr ∘ₗ σr = LinearMap.id)
    (hα' : α ∘ₗ σK = σV ∘ₗ α) (hβ' : β ∘ₗ σV = J ∘ₗ β) (hγ' : γ ∘ₗ σV = σr ∘ₗ γ)
    (hα'' : α' ∘ₗ σK = σV' ∘ₗ α') (hβ'' : β' ∘ₗ σV' = (-J) ∘ₗ β') (hγ'' : γ' ∘ₗ σV' = σr ∘ₗ γ')
    (hl : lam ∘ₗ σr = localInv J ∘ₗ lam)
    (hα : Function.Injective α) (hαβ : LinearMap.range α = LinearMap.ker β)
    (hγ : LinearMap.range γ = LinearMap.ker (LinearMap.snd k _ _ ∘ₗ lam))
    (hc : lam ∘ₗ γ = inlF ∘ₗ β)
    (hαS : Function.Injective α') (hαβS : LinearMap.range α' = LinearMap.ker β')
    (hγS : LinearMap.range γ' = LinearMap.ker (LinearMap.fst k _ _ ∘ₗ lam))
    (hcS : lam ∘ₗ γ' = inrS ∘ₗ β')
    (hU : ∀ u, u ∈ LinearMap.range lam ↔ ∀ w ∈ LinearMap.range lam, localPair ε J u w = 0)
    (cp cm : V) (hcp : σV cp = cp) (hcm : σV cm = -cm)
    (hdet : DetectingPrime σV (lam ∘ₗ γ) cp cm)
    (sp sm sp' sm' : ℕ) (hsp : sp = finrank k ↥(signPart σV (1 : k)))
    (hsm : sm = finrank k ↥(signPart σV (-1 : k))) (hsp' : sp' = finrank k ↥(signPart σV' (1 : k)))
    (hsm' : sm' = finrank k ↥(signPart σV' (-1 : k))) :
    QuadMixedDims (k := k) sp sm sp' sm' := by
  have hσU : ∀ u ∈ LinearMap.range lam, localInv J u ∈ LinearMap.range lam := by
    rintro _ ⟨v, rfl⟩
    exact ⟨σr v, by rw [← LinearMap.comp_apply, hl, LinearMap.comp_apply]⟩
  obtain ⟨-, hAp, hAm, -, -⟩ :=
    selfAnnihilatingSigns_proof k J ε ep em h2 hε hJ2 hp hm he (LinearMap.range lam) hσU hU
  have hloc : ∀ v, (lam ∘ₗ γ) (σV v) = localInv J ((lam ∘ₗ γ) v) := by
    intro v
    rw [← LinearMap.comp_apply (lam ∘ₗ γ), LinearMap.comp_assoc, hγ', ← LinearMap.comp_assoc, hl]
    rfl
  have hsnd : ∀ v, ((lam ∘ₗ γ) v).2 = 0 := by
    intro v
    rw [hc]; rfl
  obtain ⟨d1, d2⟩ := detectionFields_proof k J ep em h2 hp hm he V σV (lam ∘ₗ γ)
    (LinearMap.range lam) cp cm hloc hcp hcm (LinearMap.mem_range_self _ _)
    (LinearMap.mem_range_self _ _) (hsnd cp) (hsnd cm) hdet
  obtain ⟨e1, e2, e3, e4⟩ := signDimsAxes_proof k J ep em K₀ V V' Vr α β γ α' β' γ' lam σK σV σV' σr
    h2 hJ2 hp hm he hK hV hV' hr hα' hβ' hγ' hα'' hβ'' hγ'' hl hα hαβ hγ hc hαS hαβS hγS hcS
  exact
    { h2 := h2, ε := ε, hε := hε, J := J, ep := ep, em := em, hp := hp, hm := hm, he := he
      Up := LinearMap.range lam ⊓ signPlane ep em
      Um := LinearMap.range lam ⊓ signPlane em ep
      hUp := hAp, hUm := hAm, hdetp := d1, hdetm := d2
      kp := finrank k ↥(signPart σK (1 : k)), km := finrank k ↥(signPart σK (-1 : k))
      hVp := hsp.trans e1, hVm := hsm.trans e2, hVp' := hsp'.trans e3, hVm' := hsm'.trans e4 }

/-- **The one-sign quadratic switch data from the cone triangles** (tex L5123–5136). As
`quadMixedDimsOfInputs`, for an old configuration with `V_- = 0` and `dim V_+ = s > 1`, with a
detecting prime for a class `c₊ ∈ V₊` only (GLUE `DetectingPrimePlus`); produces
`QuadSingleDims s a b` with `a, b` the sign dimensions of `V'`. -/
noncomputable def quadSingleDimsOfInputs (h2 : (2 : k) ≠ 0) (ε : k) (hε : ε ≠ 0)
    (J : (Fin 2 → k) →ₗ[k] (Fin 2 → k)) (hJ2 : J ∘ₗ J = LinearMap.id) (ep em : Fin 2 → k)
    (hp : J ep = ep) (hm : J em = -em) (he : e₂ ep em ≠ 0)
    {K₀ V V' Vr : Type} [AddCommGroup K₀] [Module k K₀] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup Vr] [Module k Vr]
    [FiniteDimensional k V] [FiniteDimensional k V']
    (α : K₀ →ₗ[k] V) (β : V →ₗ[k] (Fin 2 → k)) (γ : V →ₗ[k] Vr)
    (α' : K₀ →ₗ[k] V') (β' : V' →ₗ[k] (Fin 2 → k)) (γ' : V' →ₗ[k] Vr)
    (lam : Vr →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
    (σK : K₀ →ₗ[k] K₀) (σV : V →ₗ[k] V) (σV' : V' →ₗ[k] V') (σr : Vr →ₗ[k] Vr)
    (hK : σK ∘ₗ σK = LinearMap.id) (hV : σV ∘ₗ σV = LinearMap.id)
    (hV' : σV' ∘ₗ σV' = LinearMap.id) (hr : σr ∘ₗ σr = LinearMap.id)
    (hα' : α ∘ₗ σK = σV ∘ₗ α) (hβ' : β ∘ₗ σV = J ∘ₗ β) (hγ' : γ ∘ₗ σV = σr ∘ₗ γ)
    (hα'' : α' ∘ₗ σK = σV' ∘ₗ α') (hβ'' : β' ∘ₗ σV' = (-J) ∘ₗ β') (hγ'' : γ' ∘ₗ σV' = σr ∘ₗ γ')
    (hl : lam ∘ₗ σr = localInv J ∘ₗ lam)
    (hα : Function.Injective α) (hαβ : LinearMap.range α = LinearMap.ker β)
    (hγ : LinearMap.range γ = LinearMap.ker (LinearMap.snd k _ _ ∘ₗ lam))
    (hc : lam ∘ₗ γ = inlF ∘ₗ β)
    (hαS : Function.Injective α') (hαβS : LinearMap.range α' = LinearMap.ker β')
    (hγS : LinearMap.range γ' = LinearMap.ker (LinearMap.fst k _ _ ∘ₗ lam))
    (hcS : lam ∘ₗ γ' = inrS ∘ₗ β')
    (hU : ∀ u, u ∈ LinearMap.range lam ↔ ∀ w ∈ LinearMap.range lam, localPair ε J u w = 0)
    (cp : V) (hcp : σV cp = cp) (hdet : DetectingPrimePlus σV (lam ∘ₗ γ) cp)
    (s a b : ℕ) (hs1 : 1 < s) (hs : s = finrank k ↥(signPart σV (1 : k)))
    (hs0 : 0 = finrank k ↥(signPart σV (-1 : k))) (ha : a = finrank k ↥(signPart σV' (1 : k)))
    (hb : b = finrank k ↥(signPart σV' (-1 : k))) :
    QuadSingleDims (k := k) s a b := by
  have hσU : ∀ u ∈ LinearMap.range lam, localInv J u ∈ LinearMap.range lam := by
    rintro _ ⟨v, rfl⟩
    exact ⟨σr v, by rw [← LinearMap.comp_apply, hl, LinearMap.comp_apply]⟩
  obtain ⟨-, hAp, hAm, -, -⟩ :=
    selfAnnihilatingSigns_proof k J ε ep em h2 hε hJ2 hp hm he (LinearMap.range lam) hσU hU
  have hloc : ∀ v, (lam ∘ₗ γ) (σV v) = localInv J ((lam ∘ₗ γ) v) := by
    intro v
    rw [← LinearMap.comp_apply (lam ∘ₗ γ), LinearMap.comp_assoc, hγ', ← LinearMap.comp_assoc, hl]
    rfl
  have hsnd : ((lam ∘ₗ γ) cp).2 = 0 := by rw [hc]; rfl
  have hplus : (lam ∘ₗ γ) cp ∈ signPlane ep em := by
    rw [plus_eq_signPlane h2 hp hm he, mem_plusPart, ← hloc, hcp]
  have hfin : (lam ∘ₗ γ) cp ∈ finAxis ep := by
    obtain ⟨x, y, hxy⟩ := mem_signPlane.1 hplus
    exact mem_finAxis.2 ⟨x, Prod.ext (by simpa using congrArg Prod.fst hxy) hsnd⟩
  obtain ⟨e1, e2, e3, e4⟩ := signDimsAxes_proof k J ep em K₀ V V' Vr α β γ α' β' γ' lam σK σV σV' σr
    h2 hJ2 hp hm he hK hV hV' hr hα' hβ' hγ' hα'' hβ'' hγ'' hl hα hαβ hγ hc hαS hαβS hγS hcS
  exact
    { h2 := h2, ε := ε, hε := hε, J := J, ep := ep, em := em, hp := hp, hm := hm, he := he
      Up := LinearMap.range lam ⊓ signPlane ep em
      Um := LinearMap.range lam ⊓ signPlane em ep
      hUp := hAp, hUm := hAm
      hdetp := ⟨(lam ∘ₗ γ) cp, Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ _, hplus⟩, hfin,
        hdet hcp⟩
      kp := finrank k ↥(signPart σK (1 : k)), km := finrank k ↥(signPart σK (-1 : k))
      hs := hs1, hVp := hs.trans e1, hVm := hs0.trans e2, hVp' := ha.trans e3,
      hVm' := hb.trans e4 }

end Constructors

/-! ### The Galois cocycle involution -/

section Galois

variable {k : Type} [Field k] {Γ : Type} [Group Γ] {T : Type} [AddCommGroup T] [Module k T]

/-- The conjugate `τ⁻¹ g τ` of an element of an index-two (hence normal) subgroup, as an element of
the subgroup (written `τ⁻¹ g (τ⁻¹)⁻¹`). -/
def conjSub (Δ : Subgroup Γ) (hidx : Δ.index = 2) (τ : Γ) (g : Δ) : Δ :=
  ⟨τ⁻¹ * g * τ⁻¹⁻¹, (Subgroup.normal_of_index_eq_two hidx).conj_mem _ g.2 τ⁻¹⟩

/-- **The cocycle action** `c^τ(g) = J c(τ⁻¹ g τ)` on degree-one cochains `Δ → T` of the
index-two subgroup, `J = ρ(τ)` (tex L5009–5011). -/
def cocycleAct (Δ : Subgroup Γ) (hidx : Δ.index = 2) (τ : Γ) (ρ : Γ →* (T →ₗ[k] T)) :
    (Δ → T) →ₗ[k] (Δ → T) where
  toFun c g := ρ τ (c (conjSub Δ hidx τ g))
  map_add' c d := by ext g; simp
  map_smul' a c := by ext g; simp

/-- **The cocycle action is an involution on cochains** when `τ² = 1` (tex L5009–5013: "gives a
`k`-linear involution"): `J² = ρ(τ²) = 1` and `τ⁻¹(τ⁻¹ g τ)τ = g`. Classification: PROVED. -/
theorem cocycleAct_involutive (Δ : Subgroup Γ) (hidx : Δ.index = 2) (τ : Γ)
    (ρ : Γ →* (T →ₗ[k] T)) (hττ : τ * τ = 1) :
    cocycleAct Δ hidx τ ρ ∘ₗ cocycleAct Δ hidx τ ρ = LinearMap.id := by
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hJ : ∀ x, ρ τ (ρ τ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, hττ, map_one, Module.End.one_apply]
  ext c g
  simp only [LinearMap.comp_apply, cocycleAct, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [hJ]
  congr 1
  apply Subtype.ext
  simp only [conjSub, hτ]
  rw [← mul_assoc, ← mul_assoc, hττ, one_mul, mul_assoc, hττ, mul_one]

/-- **GLUE input: the involution is the Galois cocycle action** (tex L5009–5013, L5026–5037). Data:
an index-two subgroup `Δ` of `Γ`, `τ ∉ Δ` with `τ² = 1` (the actual complex conjugation), the
coefficient action `ρ` (`J = ρ(τ)`), the fibre Selmer complex `K` with a model
`ev : K¹ → (Δ → T)` of its degree-one cochains, the local `J_ℓ` at the derivative prime
(`J_ℓ² = 1`, `det J_ℓ = −1`) and the localization on cohomology `loc : H¹(K) → F ⊕ S`. The input:
there is an involutive chain automorphism `σ` of `K` whose degree-one component is the cocycle
action on the model (`ev ∘ σ¹ = cocycleAct ∘ ev`) and whose action on `H¹` is compatible with the
local involution (`J_ℓ` on `F`, `−J_ℓ` on `S`). That these maps are the actual continuous cochains
and localization maps of `G_{K,S}` needs the Galois cochain complexes, so it is assumed.
Classification: GLUE (assumed input). -/
def GaloisCocycleInvolution (Δ : Subgroup Γ) (hidx : Δ.index = 2) (τ : Γ) (_hτ : τ ∉ Δ)
    (_hττ : τ * τ = 1) (ρ : Γ →* (T →ₗ[k] T)) (K : CochainComplex (ModuleCat.{0} k) ℤ)
    (ev : K.X 1 →ₗ[k] (Δ → T)) (Jl : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (_hJl2 : Jl ∘ₗ Jl = LinearMap.id) (_hJldet : LinearMap.det Jl = -1)
    (loc : K.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) : Prop :=
  ∃ σ : K ⟶ K, σ ≫ σ = 𝟙 K ∧ (∀ x, ev ((σ.f 1).hom x) = cocycleAct Δ hidx τ ρ (ev x)) ∧
    ∀ v, loc ((HomologicalComplex.homologyMap σ 1).hom v) = localInv Jl (loc v)

/-- **The cohomology signs from the Galois cocycle involution** (tex L5009–5013, L5026). Under the
GLUE input `GaloisCocycleInvolution`, the involution `T = H¹(σ)` splits `V = H¹(K)` as
`V₊ ⊕ V₋` (`CohomologySignSplitting`), and the localization is equivariant for `T` and the local
involution. Classification: PROVED (from the GLUE input). -/
theorem signSplitting_of_galois (Δ : Subgroup Γ) (hidx : Δ.index = 2) (τ : Γ) (hτ : τ ∉ Δ)
    (hττ : τ * τ = 1) (ρ : Γ →* (T →ₗ[k] T)) (K : CochainComplex (ModuleCat.{0} k) ℤ)
    (ev : K.X 1 →ₗ[k] (Δ → T)) (Jl : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJl2 : Jl ∘ₗ Jl = LinearMap.id) (hJldet : LinearMap.det Jl = -1)
    (loc : K.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (h2 : (2 : k) ≠ 0)
    (hG : GaloisCocycleInvolution Δ hidx τ hτ hττ ρ K ev Jl hJl2 hJldet loc) :
    ∃ σ : K ⟶ K, σ ≫ σ = 𝟙 K ∧
      let Tσ : K.homology 1 →ₗ[k] K.homology 1 := (HomologicalComplex.homologyMap σ 1).hom
      Tσ ∘ₗ Tσ = LinearMap.id ∧ plusPart Tσ ⊓ minusPart Tσ = ⊥ ∧
      plusPart Tσ ⊔ minusPart Tσ = ⊤ ∧ (∀ v, loc (Tσ v) = localInv Jl (loc v)) := by
  obtain ⟨σ, hσ, -, hloc⟩ := hG
  obtain ⟨hT, hinf, hsup, -⟩ := cohomologySignSplitting_proof k K σ h2 hσ
  exact ⟨σ, hσ, hT, hinf, hsup, hloc⟩

/-- **The sign fields of the quadratic switch from the Galois cocycle involution** (tex
L5003–5120): `QuadSignFields` with `T = H¹(σ)` for the `σ` of the GLUE input
`GaloisCocycleInvolution`, the duality hypothesis `U = U^⊥` (GLUE) and the detecting prime (GLUE).
Classification: PROVED (from the inputs). -/
theorem quadSignFields_of_galois (Δ : Subgroup Γ) (hidx : Δ.index = 2) (τ : Γ) (hτ : τ ∉ Δ)
    (hττ : τ * τ = 1) (ρ : Γ →* (T →ₗ[k] T)) (K : CochainComplex (ModuleCat.{0} k) ℤ)
    (ev : K.X 1 →ₗ[k] (Δ → T)) (Jl : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
    (hJl2 : Jl ∘ₗ Jl = LinearMap.id) (hJldet : LinearMap.det Jl = -1)
    (loc : K.homology 1 →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) (h2 : (2 : k) ≠ 0) (ε : k)
    (hε : ε ≠ 0) (hG : GaloisCocycleInvolution Δ hidx τ hτ hττ ρ K ev Jl hJl2 hJldet loc)
    (U : Submodule k ((Fin 2 → k) × (Fin 2 → k))) (hσU : ∀ u ∈ U, localInv Jl u ∈ U)
    (hU : ∀ u, u ∈ U ↔ ∀ w ∈ U, localPair ε Jl u w = 0) :
    ∃ σ : K ⟶ K, σ ≫ σ = 𝟙 K ∧ ∀ cp cm : K.homology 1,
      (HomologicalComplex.homologyMap σ 1).hom cp = cp →
      (HomologicalComplex.homologyMap σ 1).hom cm = -cm →
      loc cp ∈ U → loc cm ∈ U → (loc cp).2 = 0 → (loc cm).2 = 0 →
      DetectingPrime (HomologicalComplex.homologyMap σ 1).hom loc cp cm →
      ∃ (ep em : Fin 2 → k) (Up Um : Submodule k ((Fin 2 → k) × (Fin 2 → k))),
        Jl ep = ep ∧ Jl em = -em ∧ e₂ ep em ≠ 0 ∧
        IsSelfAnnihilatingIn ε Jl (signPlane ep em) Up ∧
        IsSelfAnnihilatingIn ε Jl (signPlane em ep) Um ∧
        (∃ x ∈ Up, x ∈ finAxis ep ∧ x ≠ 0) ∧ (∃ x ∈ Um, x ∈ finAxis em ∧ x ≠ 0) ∧
        U = Up ⊔ Um := by
  obtain ⟨σ, hσ, -, hloc⟩ := hG
  refine ⟨σ, hσ, fun cp cm hcp hcm hUp hUm hFp hFm hD => ?_⟩
  exact quadSignFields_proof k Jl ε h2 hε hJl2 hJldet U hσU hU (K.homology 1)
    (HomologicalComplex.homologyMap σ 1).hom loc cp cm hloc hcp hcm hUp hUm hFp hFm hD

end Galois

/-! ### Non-vacuity -/

/-- Non-vacuity of the axis identification over `ℚ`: `J = diag(1, −1)` with `e₊ = (1, 0)`,
`e₋ = (0, 1)` satisfies the hypotheses of `SignPartsAxes`. PROVED. -/
theorem signPartsAxes_example :
    let J : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := Matrix.toLin' !![1, 0; 0, -1]
    J ![1, 0] = ![1, 0] ∧ J ![0, 1] = -![0, 1] ∧ e₂ (![1, 0] : Fin 2 → ℚ) ![0, 1] ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [e₂, Matrix.det_fin_two]

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
