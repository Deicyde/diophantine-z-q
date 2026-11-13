import Mathlib
import ZInQKernel.HDecomp.Conductor.D1Local
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.RamificationGroup

/-!
# G15: the decomposition group is the local Galois group, with its lower filtration

For a Galois number field `L`, a finite place `w` of `L` (a nonzero prime `P = w.asIdeal` of
`𝓞 L`) and the place `v` of `ℚ` below it, Tau Ceti's `decompositionEquiv` identifies the
kernel's decomposition group `GlueD1Local.decompGroup L P = Stab(P) ≤ Gal(L/ℚ)` with the local
Galois group `Gal(L_w/ℚ_v)` (`ℚ_v = v.adicCompletion ℚ ≅ ℚ_p`, Mathlib's
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`), and carries the kernel's lower
ramification groups `GlueConductor.ramGroup L P i` (the inertia of `P^(i+1)`) onto Tau Ceti's
local `lowerRamificationGroup ℚ_v L_w i`.

No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain
open scoped AdicCompletionExtension

noncomputable section

namespace ZInQ.Contrib.G15

variable {L : Type} [Field L] [NumberField L]

section Basic

variable (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The local Galois group `Gal(L_w/ℚ_v)`. -/
abbrev LocalGal := w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L

/-- The local lower ramification group `G_i(L_w/ℚ_v)` (Tau Ceti). -/
abbrev localRam (i : ℕ) : Subgroup (LocalGal v w) :=
  TauCeti.LocalFieldsRamification.lowerRamificationGroup
    (v.adicCompletion ℚ) (w.adicCompletion L) (i : ℤ)

/-- The kernel's ramification group is Tau Ceti's `Ideal.ramificationGroup`. -/
theorem ramGroup_eq_ramificationGroup (P : Ideal (𝓞 L)) (i : ℕ) :
    GlueConductor.ramGroup L P i = P.ramificationGroup Gal(L/ℚ) i :=
  (Ideal.ramificationGroup_def P i).symm

/-- `G_i(P) ≤ D_P`. -/
theorem ramGroup_le_decompGroup (P : Ideal (𝓞 L)) (i : ℕ) :
    GlueConductor.ramGroup L P i ≤ GlueD1Local.decompGroup L P := by
  rw [ramGroup_eq_ramificationGroup]
  exact Ideal.ramificationGroup_le_stabilizer P i

/-- **Global vs local ramification groups, elementwise** (no Galois hypothesis):
`σ ∈ D_P` lies in `G_i(P)` iff its continuous extension lies in `G_i(L_w/ℚ_v)`. -/
theorem mem_ramGroup_iff_decompositionHom_mem (i : ℕ)
    (σ : GlueD1Local.decompGroup L w.asIdeal) :
    (σ : Gal(L/ℚ)) ∈ GlueConductor.ramGroup L w.asIdeal i ↔
      HeightOneSpectrum.decompositionHom v w σ ∈ localRam v w i := by
  rw [ramGroup_eq_ramificationGroup]
  exact HeightOneSpectrum.mem_ramificationGroup_iff_decompositionHom_mem v i σ

variable [IsGalois ℚ L]

/-- **`D_P ≅ Gal(L_w/ℚ_v)`** (Tau Ceti's `decompositionEquiv`, on the kernel's `decompGroup`). -/
def decompEquiv :
    GlueD1Local.decompGroup L w.asIdeal ≃* LocalGal v w :=
  HeightOneSpectrum.decompositionEquiv v w

theorem decompEquiv_apply (σ : GlueD1Local.decompGroup L w.asIdeal) :
    decompEquiv v w σ = HeightOneSpectrum.decompositionHom v w σ := rfl

/-- `decompEquiv` restricted to `L` is the global action: `σ̂ (x) = σ x` for `x ∈ L`. -/
theorem decompEquiv_algebraMap (σ : GlueD1Local.decompGroup L w.asIdeal) (x : L) :
    decompEquiv v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/ℚ)) x) :=
  HeightOneSpectrum.decompositionHom_algebraMap σ x

/-- **The lower filtration is transported**: `decompEquiv` maps `G_i(P) ∩ D_P = G_i(P)` onto
`G_i(L_w/ℚ_v)`. -/
theorem map_ramGroup_decompEquiv (i : ℕ) :
    ((GlueConductor.ramGroup L w.asIdeal i).subgroupOf (GlueD1Local.decompGroup L w.asIdeal)).map
      (decompEquiv v w).toMonoidHom = localRam v w i := by
  rw [ramGroup_eq_ramificationGroup, Ideal.ramificationGroup_subgroupOf]
  exact HeightOneSpectrum.map_ramificationGroup_decompositionHom v w i

/-- **`|G_i(P)| = |G_i(L_w/ℚ_v)|`**: the kernel's `ramCard` is the order of the local lower
ramification group. -/
theorem ramCard_eq_card_localRam (i : ℕ) :
    GlueConductor.ramCard L w.asIdeal i = Nat.card (localRam v w i) := by
  show Nat.card (GlueConductor.ramGroup L w.asIdeal i) = _
  rw [ramGroup_eq_ramificationGroup]
  exact HeightOneSpectrum.card_ramificationGroup_eq_card_lowerRamificationGroup v w i

/-- `ramCard L P = (i ↦ |G_i(L_w/ℚ_v)|)` as functions. -/
theorem ramCard_eq_card_localRam_fun :
    GlueConductor.ramCard L w.asIdeal = fun i => Nat.card (localRam v w i) :=
  funext (ramCard_eq_card_localRam v w)

/-- `G_i(P) ≠ 1 ↔ G_i(L_w/ℚ_v) ≠ 1`. -/
theorem ramGroup_ne_bot_iff (i : ℕ) :
    GlueConductor.ramGroup L w.asIdeal i ≠ ⊥ ↔ localRam v w i ≠ ⊥ := by
  rw [Ne, Ne, ← Subgroup.card_eq_one, ← Subgroup.card_eq_one]
  exact not_congr (by rw [← ramCard_eq_card_localRam v w i])

/-- `|D_P| = [L_w : ℚ_v]`. -/
theorem card_decompGroup_eq_finrank :
    Nat.card (GlueD1Local.decompGroup L w.asIdeal) =
      Module.finrank (v.adicCompletion ℚ) (w.adicCompletion L) :=
  HeightOneSpectrum.card_stabilizer_eq_finrank_adicCompletion v w

end Basic


/-! ## Intermediate fields: `Gal(L_w/K_u) ↔ D_P ∩ Gal(L/K)` and `[K_u : ℚ_v] = [D_P : D_P ∩ Gal(L/K)]` -/

section Intermediate

variable (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (K : IntermediateField ℚ L) (u : HeightOneSpectrum (𝓞 K))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]

/-- The canonical map `K_u → L_w` is `ℚ_v`-linear. -/
theorem completionAlgHom_algebraMap (x : v.adicCompletion ℚ) :
    HeightOneSpectrum.completionAlgHom u w (algebraMap (v.adicCompletion ℚ) (u.adicCompletion K) x) =
      algebraMap (v.adicCompletion ℚ) (w.adicCompletion L) x := by
  have h := HeightOneSpectrum.completionAlgHom_comp (K := ℚ) (M := K) (L := L) v u w
  have h2 := congrArg (fun f => f x) h
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h2
  rw [HeightOneSpectrum.algebraMap_eq_completionAlgHom,
    HeightOneSpectrum.algebraMap_eq_completionAlgHom]
  exact h2

/-- The canonical map `K_u → L_w` as a `ℚ_v`-algebra map. -/
def inclQv : u.adicCompletion K →ₐ[v.adicCompletion ℚ] w.adicCompletion L where
  toRingHom := (HeightOneSpectrum.completionAlgHom u w).toRingHom
  commutes' x := completionAlgHom_algebraMap v w K u x

theorem inclQv_apply (z : u.adicCompletion K) :
    inclQv v w K u z = HeightOneSpectrum.completionAlgHom u w z := rfl

/-- The image of `K_u` in `L_w`, an intermediate field of `L_w/ℚ_v`. -/
abbrev localField : IntermediateField (v.adicCompletion ℚ) (w.adicCompletion L) :=
  (inclQv v w K u).fieldRange

/-- `K_u ≅ (its image in L_w)` over `ℚ_v`. -/
def localFieldEquiv : u.adicCompletion K ≃ₐ[v.adicCompletion ℚ] localField v w K u :=
  AlgEquiv.ofInjectiveField (inclQv v w K u)

theorem finrank_localField :
    Module.finrank (v.adicCompletion ℚ) (localField v w K u) =
      Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K) :=
  (localFieldEquiv v w K u).toLinearEquiv.finrank_eq.symm

/-- The image of `x ∈ K` in `L_w` lies in the image of `K_u`. -/
theorem algebraMap_mem_localField (x : K) :
    algebraMap L (w.adicCompletion L) (x : L) ∈ localField v w K u := by
  refine ⟨algebraMap K (u.adicCompletion K) x, ?_⟩
  show HeightOneSpectrum.completionAlgHom u w _ = _
  exact HeightOneSpectrum.adicCompletionExtension_coe K L u w x

variable [IsGalois ℚ L]

/-- **`D_P ∩ Gal(L/K)` is `Gal(L_w/K_u)`, elementwise.** `σ ∈ D_P` fixes `K` iff its continuous
extension `σ̂ ∈ Gal(L_w/ℚ_v)` fixes the image of `K_u`. -/
theorem mem_localSub_iff (σ : GlueD1Local.decompGroup L w.asIdeal) :
    σ ∈ GlueD1Local.localSub L K w.asIdeal ↔
      decompEquiv v w σ ∈ (localField v w K u).fixingSubgroup := by
  rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ y hy
    obtain ⟨z, rfl⟩ := hy
    -- `σ̂ ∘ ι` and `ι` are continuous ring maps `K_u → L_w` that agree on `K`
    have key : ((decompEquiv v w σ).toRingEquiv.toRingHom.comp
        (HeightOneSpectrum.completionAlgHom u w).toRingHom) =
        (HeightOneSpectrum.completionAlgHom u w).toRingHom := by
      apply HeightOneSpectrum.eq_completionAlgHom_of_continuous u w
      · exact (HeightOneSpectrum.continuous_decompositionHom (v := v) (w := w) σ).comp
          (HeightOneSpectrum.continuous_completionAlgHom u w)
      · intro x
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        have hx : HeightOneSpectrum.completionAlgHom u w (algebraMap K (u.adicCompletion K) x) =
            algebraMap L (w.adicCompletion L) (algebraMap K L x) :=
          HeightOneSpectrum.adicCompletionExtension_coe K L u w x
        rw [hx]
        show decompEquiv v w σ (algebraMap L (w.adicCompletion L) (algebraMap K L x)) = _
        rw [decompEquiv_algebraMap]
        congr 1
        exact hσ x x.2
    have := congrArg (fun f => f z) key
    simpa [inclQv_apply] using this
  · intro h x hx
    apply (algebraMap L (w.adicCompletion L)).injective
    rw [← decompEquiv_algebraMap v w]
    exact h _ (algebraMap_mem_localField v w K u ⟨x, hx⟩)

/-- **`decompEquiv` maps `D_P ∩ Gal(L/K)` onto `Gal(L_w/K_u)`** (the fixing subgroup of the image
of `K_u` in `Gal(L_w/ℚ_v)`). -/
theorem map_localSub_decompEquiv :
    (GlueD1Local.localSub L K w.asIdeal).map (decompEquiv v w).toMonoidHom =
      (localField v w K u).fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (mem_localSub_iff v w K u σ).mp hσ
  · intro hτ
    refine ⟨(decompEquiv v w).symm τ, ?_, by simp⟩
    show (decompEquiv v w).symm τ ∈ GlueD1Local.localSub L K w.asIdeal
    rw [mem_localSub_iff v w K u]
    simpa using hτ

/-- **The local degree is the index**: `[K_u : ℚ_v] = [D_P : D_P ∩ Gal(L/K)]`. -/
theorem index_localSub_eq_finrank :
    (GlueD1Local.localSub L K w.asIdeal).index =
      Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K) := by
  rw [← finrank_localField v w K u, IntermediateField.finrank_eq_fixingSubgroup_index,
    ← map_localSub_decompEquiv v w K u]
  exact (Subgroup.index_map_of_bijective (f := (decompEquiv v w).toMonoidHom)
    (decompEquiv v w).bijective _).symm

/-- Galois theory: if `M/F` is finite Galois and `M` is the normal closure of `E`, then the fixing
subgroup of `E` has trivial normal core. -/
theorem normalCore_fixingSubgroup_eq_bot {F M : Type*} [Field F] [Field M] [Algebra F M]
    [FiniteDimensional F M] [IsGalois F M] (E : IntermediateField F M)
    (h : IntermediateField.normalClosure F E M = ⊤) : E.fixingSubgroup.normalCore = ⊥ := by
  set N := E.fixingSubgroup.normalCore
  have : N.Normal := Subgroup.normalCore_normal _
  have hK : E ≤ IntermediateField.fixedField N := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (IntermediateField.mem_fixingSubgroup_iff E σ).mp
      (Subgroup.normalCore_le _ hσ) x hx
  have htop : IntermediateField.fixedField N = ⊤ := by
    rw [eq_top_iff, ← h]
    exact (IntermediateField.normalClosure_le_iff_of_normal).mpr hK
  rw [← IntermediateField.fixingSubgroup_fixedField N, htop, IntermediateField.fixingSubgroup_top]

/-- A group isomorphism carrying `H` onto `H'` carries trivial normal core to trivial normal
core. -/
theorem normalCore_eq_bot_of_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (H' : Subgroup G') (hmap : H.map e.toMonoidHom = H')
    (hcore : H'.normalCore = ⊥) : H.normalCore = ⊥ := by
  have hN : (H.normalCore.map e.toMonoidHom).Normal :=
    (Subgroup.normalCore_normal H).map e.toMonoidHom e.surjective
  have hle : H.normalCore.map e.toMonoidHom ≤ H'.normalCore := by
    rw [Subgroup.normal_le_normalCore, ← hmap]
    exact Subgroup.map_mono (Subgroup.normalCore_le H)
  rw [hcore, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp hle

/-- **"`L_w` is the Galois closure of `K_u/ℚ_v`" gives the kernel's core condition**: if the
normal closure of the image of `K_u` in `L_w/ℚ_v` is `L_w`, then `D_P ∩ Gal(L/K)` has trivial
normal core in `D_P` (the hypothesis `hcore` of `GlueD1Local.D1_local`). -/
theorem normalCore_localSub_eq_bot
    (hclos : IntermediateField.normalClosure (v.adicCompletion ℚ) (localField v w K u)
      (w.adicCompletion L) = ⊤) :
    (GlueD1Local.localSub L K w.asIdeal).normalCore = ⊥ :=
  normalCore_eq_bot_of_map_equiv (decompEquiv v w) _ _ (map_localSub_decompEquiv v w K u)
    (normalCore_fixingSubgroup_eq_bot _ hclos)

end Intermediate

end ZInQ.Contrib.G15

end
