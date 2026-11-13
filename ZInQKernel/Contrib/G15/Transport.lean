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

end ZInQ.Contrib.G15

end
