import ZInQKernel.Contrib.CloudB3E1RingClass.RCPointData
import ZInQKernel.Contrib.CloudB3E1RingClass.CSTBridge
import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf

/-!
# The realized Heegner point is fixed by the elements fixing the ring class field

Manuscript `diophantine_zq.tex`, tex 2411–2416, 3080–3084 (`y ∈ E(H_f)`).

Lane E1's ring-class point `rcPoint G hS y hy hQ` takes a point `y ∈ W(K_S)` with
`hy : ∀ g, ringClassRes f hf S hS g = 1 → galPtS W g y = y` (`y` fixed by the elements that fix
lane E1's copy `ringClassFieldOf f` of `H_f` in `K_S`). Lane E2's realized Heegner point
`realize … (D.H f) … (D.y f)` (`H20PresClassOf`) is fixed by the elements fixing `heegnerL f`
(`realize_fixed`).

* `inflMap_refl` (PROVED): `G_{K,S} → G_{K,S}` along `S ⊆ S` is the identity.
* `mem_heegnerL_iff_mem_ringClassFieldOf` (PROVED): the two copies of `H_f` in `K_S` agree
  (`ringClassOrder_eq_conductorOrder`).
* `fixH_of_ringClassRes` (PROVED): `ringClassRes g = 1` puts `g` in the fixing group of
  `heegnerL f`.
* **`heegner_hy`** (PROVED, from the full anchor): the realized Heegner point of conductor `f`
  satisfies `hy` for `W = E.baseChange K`; **`heegnerPtG`** (definition), **`heegner_hy_G`**
  (PROVED): the same for the curve `G.W` of Kummer data `G` along `G.hW : G.W = E₀.baseChange K`
  — the input `hy` of `rcPoint G hS`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside resAbs resAbs_surjective resUnr_comp)
open ZInQ.Contrib.CloudB3E1RingClass (ringClassFieldOf ringClassRes ringClassOrder galPtS
  ringClassOrder_eq_conductorOrder)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open TauCeti.ClassFieldTheory
open scoped WeierstrassCurve

attribute [local instance] ptSAction

variable {K : Type} [Field K] [NumberField K]

/-- `G_{K,S} → G_{K,S}` along `S ⊆ S` is the identity (PROVED). -/
theorem inflMap_refl {S : Set (HeightOneSpectrum (𝓞 K))} (g : GKS K S) :
    inflMap K (subset_refl S) g = g := by
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S g
  exact resUnr_comp K (subset_refl S) σ

/-- **The two copies of `H_f` in `K_S` agree** (PROVED). -/
theorem mem_heegnerL_iff_mem_ringClassFieldOf {S : Set (HeightOneSpectrum (𝓞 K))} (f : ℕ)
    [NeZero f] (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (z : KS K S) :
    z ∈ heegnerL f hS ↔ z ∈ ringClassFieldOf f (NeZero.ne f) S hS := by
  rw [mem_heegnerL]
  change _ ↔ z ∈ IntermediateField.restrict _
  rw [IntermediateField.mem_restrict, ringClassOrder_eq_conductorOrder]

/-- **`ringClassRes g = 1` fixes `heegnerL f`** (PROVED). -/
theorem fixH_of_ringClassRes {S : Set (HeightOneSpectrum (𝓞 K))} (f : ℕ) [NeZero f]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S) (g : GKS K S)
    (hg : ringClassRes f (NeZero.ne f) S hS g = 1) :
    g ∈ fixH ((subset_refl S).trans (subset_refl S)) (heegnerL f hS) := by
  rw [mem_fixH, inflMap_refl]
  intro x hx
  rw [mem_heegnerL_iff_mem_ringClassFieldOf] at hx
  have := congrArg (fun τ => ((τ ⟨x, hx⟩ : ringClassFieldOf f (NeZero.ne f) S hS) : KS K S)) hg
  simp only [AlgEquiv.one_apply] at this
  have hc := AlgEquiv.restrictNormal_commutes (galS K S g) (ringClassFieldOf f (NeZero.ne f) S hS)
    ⟨x, hx⟩
  exact hc.symm.trans this

variable {E : WeierstrassCurve ℚ} {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ}
  {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K} {D : HeegnerPointData E}

/-- **The realized Heegner point of conductor `f` is fixed by `ker(ringClassRes)`** (PROVED, from
the full anchor): lane E1's input `hy` for `W = E.baseChange K`. -/
theorem heegner_hy (hA : FullAnchor E K cp emb κ D) {S : Set (HeightOneSpectrum (𝓞 K))}
    (f : ℕ) [NeZero f] (hcop : Nat.Coprime f (D.N * D.DK.natAbs))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hy : ∃ Y' : (E.baseChange (D.H f)).toAffine.Point,
      Affine.Point.map (W' := E) (D.H f).val Y' = D.y f) (g : GKS K S)
    (hg : ringClassRes f (NeZero.ne f) S hS g = 1) :
    galPtS (E.baseChange K) g
        (realize E S κ.toAlgHom (D.H f) (field_ii hA f hcop S hS) (D.y f) hy) =
      realize E S κ.toAlgHom (D.H f) (field_ii hA f hcop S hS) (D.y f) hy := by
  have h := realize_fixed (subset_refl S) (subset_refl S) hA f hcop hS hy g
    (fixH_of_ringClassRes f hS g hg)
  rw [inflMap_refl] at h
  exact h

/-- The realized Heegner point read on the curve `W = E.baseChange K`. Kind: definition. -/
def ptCast {W : WeierstrassCurve K} (hW : W = E.baseChange K) {S : Set (HeightOneSpectrum (𝓞 K))}
    (P : ((E.baseChange K).baseChange (KS K S)).toAffine.Point) :
    (W.baseChange (KS K S)).toAffine.Point :=
  hW ▸ P

theorem galPtS_ptCast {W : WeierstrassCurve K} (hW : W = E.baseChange K)
    {S : Set (HeightOneSpectrum (𝓞 K))} (g : GKS K S)
    (P : ((E.baseChange K).baseChange (KS K S)).toAffine.Point) :
    galPtS W g (ptCast hW P) = ptCast hW (galPtS (E.baseChange K) g P) := by
  subst hW
  rfl

/-- **The realized Heegner point on the curve of Kummer data `G`** (tex 2411–2416, 3080–3084).
Kind: definition. -/
def heegnerPtG {hZ : ℤ} (G : GenuineKummerData K E hZ) (hA : FullAnchor E K cp emb κ D)
    (f : ℕ) [NeZero f] (hcop : Nat.Coprime f (D.N * D.DK.natAbs))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ G.S) :
    (G.W.baseChange (KS K G.S)).toAffine.Point :=
  ptCast G.hW (realize E G.S κ.toAlgHom (D.H f) (field_ii hA f hcop G.S hS) (D.y f)
    (anchor_coords hA.anchor (Nat.pos_of_ne_zero (NeZero.ne f)) hcop))

/-- **Lane E1's input `hy` of `rcPoint G hS`** for the realized Heegner point (PROVED, from the
full anchor). -/
theorem heegner_hy_G {hZ : ℤ} (G : GenuineKummerData K E hZ) (hA : FullAnchor E K cp emb κ D)
    (f : ℕ) [NeZero f] (hcop : Nat.Coprime f (D.N * D.DK.natAbs))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ G.S) :
    ∀ g, ringClassRes f (NeZero.ne f) G.S hS g = 1 →
      galPtS G.W g (heegnerPtG G hA f hcop hS) = heegnerPtG G hA f hcop hS := by
  intro g hg
  rw [heegnerPtG, galPtS_ptCast, heegner_hy hA f hcop hS _ g hg]

end ZInQ.Contrib.CloudB3E2.NormCochain
