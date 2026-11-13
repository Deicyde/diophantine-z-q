import ZInQKernel.HDecomp.Descent.WP3

/-!
# T14 needs no reciprocity; T15 needs only its finite-place uniqueness half (kernel form)

The only consumer of the bundle fields `t14a : BrauerHasse2C`, `t14b : BrauerReciprocity2C`,
`t15 : LocalH2CardC` is `GlueWP3.b3_degree_le_QM_of_T14_T15`
(ZInQKernel/HDecomp/Descent/WP3.lean), which passes them through `leafHasse_of_T14` and
`leafLocalTwo_of_T15` to `GlueDescent.B3Q.b3_degree_le_QM`, which takes `LeafHasse` and
`LeafLocalTwo`.  Reciprocity is used there only to get the real place, which `LeafHasse`
(finite places only) does not need.

Here, over the kernel's definitions:
* `BrauerHasseFin2C`: the cochain form of `LeafHasse` (a `ℤ/2` cocycle of `G_ℚ` that is a
  coboundary at every finite prime is a coboundary); `brauerHasseFin2C_of_T14` shows it is a
  consequence of T14 (ABHN with reciprocity), hence of the published theorems;
  `leafHasse_iff_brauerHasseFin2C : LeafHasse ↔ BrauerHasseFin2C`.
* `LocalTwo2C`: the uniqueness half of T15 at the finite places; `localTwo2C_of_T15`,
  `leafLocalTwo_iff_localTwo2C`.
* `leaves_of_narrow : BrauerHasseFin2C → LocalTwo2C → LeafHasse ∧ LeafLocalTwo`.
So the three Props T14a, T14b, T15 can be announced as the two weaker Props `BrauerHasseFin2C`,
`LocalTwo2C`.
-/

open PkgI6 GlueDescent.B2 GlueDescent.B2Q

namespace TPurity2K

/-- **T14, narrowed** (cochain form of glue-descent's `LeafHasse`). -/
def BrauerHasseFin2C : Prop :=
  ∀ ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2, IsCocycle2 ε →
    (∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) → IsCoboundary2 ε

/-- **T15, narrowed** (finite-place uniqueness half of `LocalH2CardC`). -/
def LocalTwo2C : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ ε₁ ε₂, IsCocycle2 (G := Field.absoluteGaloisGroup ℚ_[p]) ε₁ → IsCocycle2 ε₂ →
      ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ → IsCoboundary2 (ε₁ - ε₂)

/-- The narrowed T14 is a consequence of T14. -/
theorem brauerHasseFin2C_of_T14 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) :
    BrauerHasseFin2C :=
  fun ε hε hp => hH ε hε (GlueWP3.real_of_finite hR ε hε hp) hp

/-- The narrowed T14 implies the Hasse half of T14 outright. -/
theorem brauerHasse2C_of_fin (h : BrauerHasseFin2C) : BrauerHasse2C :=
  fun ε hε _ hp => h ε hε hp

theorem leafHasse_of_brauerHasseFin2C (h : BrauerHasseFin2C) : LeafHasse := by
  intro η hη hloc
  obtain ⟨ε, hε, rfl⟩ := GlueWP3.exists_of_isSignCocycle hη
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε) := by
    intro p hpp
    rw [GlueWP3.isCoboundary2_iff]
    exact hloc ⟨p, hpp.out⟩
  rw [← GlueWP3.isCoboundary2_iff]
  exact h ε hε hp

theorem brauerHasseFin2C_of_leafHasse (h : LeafHasse) : BrauerHasseFin2C := by
  intro ε hε hp
  rw [GlueWP3.isCoboundary2_iff]
  rw [GlueWP3.isCocycle2_iff] at hε
  refine h _ hε fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [GlueWP3.pull_resp_sgnC, ← GlueWP3.isCoboundary2_iff]
  exact hp p

theorem leafHasse_iff_brauerHasseFin2C : LeafHasse ↔ BrauerHasseFin2C :=
  ⟨brauerHasseFin2C_of_leafHasse, leafHasse_of_brauerHasseFin2C⟩

theorem localTwo2C_of_T15 (hC : LocalH2CardC) : LocalTwo2C :=
  fun p _ => (hC.1 p).2

theorem leafLocalTwo_iff_localTwo2C : LeafLocalTwo ↔ LocalTwo2C :=
  GlueWP3.leafLocalTwo_iff

/-- **The consumer's two leaves from the narrowed Props.** -/
theorem leaves_of_narrow (hH : BrauerHasseFin2C) (hC : LocalTwo2C) :
    LeafHasse ∧ LeafLocalTwo :=
  ⟨leafHasse_of_brauerHasseFin2C hH, leafLocalTwo_iff_localTwo2C.mpr hC⟩

end TPurity2K

#print axioms TPurity2K.brauerHasseFin2C_of_T14
#print axioms TPurity2K.leafHasse_iff_brauerHasseFin2C
#print axioms TPurity2K.localTwo2C_of_T15
#print axioms TPurity2K.leaves_of_narrow
