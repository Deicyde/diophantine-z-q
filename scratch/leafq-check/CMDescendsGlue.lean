import TailK

/-!
# leafq-check: `CMDescends` from Shimura–Taniyama, rigidity and torsion descent

Over leaf-fold4's chain (`import TailK`). `CMDescends` (period-map, LEAF?) is reduced to
* `STQM` (LEAF, Shimura–Taniyama): a QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]`
  is isomorphic, as an abelian variety, to the base change of an abelian variety over `ℚ̄`;
* `T11b_Rigidity` (the bundle's textbook leaf T11b);
* `TorsionDescends` (LEAF, textbook): a torsion point of `A₀(ℂ)` comes from a unique point of `A₀(ℚ̄)`;
* `LeafAdopt.R1R2fpRep` (the bundle's research leaf `r1r2`, only its naturality clause);
and glue proved here.
Check: `scratch/leafq-check/chk.sh scratch/leafq-check/CMDescendsGlue.lean`.
-/

set_option linter.all false

namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

namespace LeafQCheck

/-- `A₀ ×_{ℚ̄, ιe} ℂ`. -/
noncomputable abbrev bcC (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) : PkgI3.AbVar ℂ :=
  @PkgI3.AbVar.baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra

/-- **LEAF (Shimura–Taniyama, QM form).** A QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` (an endomorphism `φ` commuting with `ι(𝒪)` with `φ² = −1`, `φ² − φ + 1 = 0` or `φ² = −6`) is
isomorphic, as an abelian variety, to `A₀ ×_{ℚ̄,ιe} ℂ` for some abelian variety `A₀/ℚ̄` and some
`ιe : ℚ̄ → ℂ`.

Published: an abelian variety over `ℂ` of CM type is isomorphic to the base change of an abelian variety
over a number field (Shimura–Taniyama, *Complex multiplication of abelian varieties*, 1961, §12.4;
Shimura, *Abelian varieties with complex multiplication and modular functions*, 1998, §12.4, Prop. 26;
UNVERIFIED numbers). It applies: `ι(i)` and `φ` commute, `ι(i)² = 2`, so `End⁰(A) ⊇ ℚ(√2, φ)`, a CM
field of degree `4 = 2 dim A`. A consequence of the published statement. -/
def STQM : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (q : QMStr A), A.dim = 2 → (HasCM4 q ∨ HasCM3 q ∨ HasCM24 q) →
    ∃ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (e : PkgI3.AbVar.Hom (bcC ιe A₀) A)
      (e' : PkgI3.AbVar.Hom A (bcC ιe A₀)), e.hom ≫ e'.hom = 𝟙 _ ∧ e'.hom ≫ e.hom = 𝟙 _

/-- **LEAF (textbook: torsion points over an algebraically closed field are rational).** For an
abelian variety `A₀` over `ℚ̄` and `ιe : ℚ̄ → ℂ`, every torsion point `v ∈ A₀(ℂ)` (as a `ℂ`-point of the
base change) is the image of a unique point `v₀ ∈ A₀(ℚ̄)`.

Published: `A₀[n]` is a finite étale group scheme of order `n^{2g}` over `ℚ̄` (Mumford, *Abelian
varieties*, §4 (iv) and §6 Application 2; Milne, *Abelian varieties*, §8; UNVERIFIED numbers), hence
constant, so `A₀[n](ℚ̄) = A₀[n](ℂ)`; uniqueness is `A₀(ℚ̄) ↪ A₀(ℂ)`. (Also a consequence of the kernel's
T5 `TorsionStructure` and the injectivity of `A₀(ℚ̄) → A₀(ℂ)`, by counting.) -/
def TorsionDescends : Prop :=
  ∀ (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar) (v : (bcC ιe A₀).Pt ℂ) (n : ℕ), 0 < n → v ^ n = 1 →
    ∃! v₀ : A₀.Pt Qbar,
      v.left ≫ (pullback.fst A₀.X.hom (Spec.map (CommRingCat.ofHom ιe)) : _ ⟶ A₀.X.left) =
        Spec.map (CommRingCat.ofHom ιe) ≫ v₀.left

section Glue

variable (ιe : Qbar →+* ℂ) (A₀ : PkgI3.AbVar Qbar)

/-- `endBC` along `ιe`. -/
noncomputable abbrev endBCe : PkgI3.AbVar.End A₀ →+* PkgI3.AbVar.End (bcC ιe A₀) :=
  @G0ModField.KernelField.endBC Qbar _ A₀ ℂ _ ιe.toAlgebra

theorem endBCe_bijective (hR : ZInQ.LeafPush2.T11b_Rigidity) : Function.Bijective (endBCe ιe A₀) := by
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  refine ⟨G0ModField.KernelField.endBC_injective A₀ ℂ, fun g => ?_⟩
  obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := hR Qbar ℂ A₀ A₀ g.hom inferInstance
  refine ⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.ext' ?_⟩
  exact hφe


section Conj

variable {A B : PkgI3.AbVar ℂ} (e : PkgI3.AbVar.Hom B A) (e' : PkgI3.AbVar.Hom A B)
  (h1 : e.hom ≫ e'.hom = 𝟙 _) (h2 : e'.hom ≫ e.hom = 𝟙 _)

/-- Conjugation `End A → End B`, `f ↦ e ≫ f ≫ e'`. -/
noncomputable def conjE : PkgI3.AbVar.End A →+* PkgI3.AbVar.End B where
  toFun f := PkgI3.AbVar.Hom.mk' (e.hom ≫ f.hom ≫ e'.hom)
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ 𝟙 _ ≫ e'.hom = 𝟙 _
    rw [Category.id_comp, h1]
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (g.hom ≫ f.hom) ≫ e'.hom =
      (e.hom ≫ g.hom ≫ e'.hom) ≫ (e.hom ≫ f.hom ≫ e'.hom)
    simp only [Category.assoc]
    rw [reassoc_of% h2]
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (1 : A.X ⟶ A.X) ≫ e'.hom = 1
    rw [MonObj.one_comp, MonObj.comp_one]
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (f.hom * g.hom) ≫ e'.hom = (e.hom ≫ f.hom ≫ e'.hom) * (e.hom ≫ g.hom ≫ e'.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul]

theorem conjE_hom (f : PkgI3.AbVar.End A) :
    (conjE e e' h1 h2 f).hom = e.hom ≫ f.hom ≫ e'.hom := rfl

theorem conjE_injective : Function.Injective (conjE e e' h1 h2) := by
  intro f g hfg
  apply PkgI3.AbVar.Hom.ext'
  have := congrArg PkgI3.AbVar.Hom.hom hfg
  rw [conjE_hom, conjE_hom] at this
  have h' := congrArg (fun t => e'.hom ≫ t ≫ e.hom) this
  simp only [Category.assoc] at h'
  simpa only [reassoc_of% h2, h2, Category.comp_id] using h'

end Conj


/-- The projection of the base change. -/
noncomputable abbrev fstC : (bcC ιe A₀).X.left ⟶ A₀.X.left :=
  pullback.fst A₀.X.hom (Spec.map (CommRingCat.ofHom ιe))

theorem bc_map_fst (φ : A₀.X ⟶ A₀.X) :
    (@Over.pullback _ _ _ _ (Spec.map (CommRingCat.ofHom (@algebraMap Qbar ℂ _ _ ιe.toAlgebra))) _
      |>.map φ).left ≫ fstC ιe A₀ = fstC ιe A₀ ≫ φ.left := by
  exact pullback.lift_fst _ _ _

theorem pb_map_fst {X Y : Over (Spec (CommRingCat.of Qbar))} (k : X ⟶ Y) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom ιe))).map k).left ≫
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom ιe)) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom ιe)) ≫ k.left :=
  pullback.lift_fst _ _ _

theorem endBCe_fst (f : PkgI3.AbVar.End A₀) :
    (endBCe ιe A₀ f).hom.left ≫ fstC ιe A₀ = fstC ιe A₀ ≫ f.hom.left :=
  bc_map_fst ιe A₀ f.hom

theorem bc_isPullback :
    IsPullback (fstC ιe A₀) (bcC ιe A₀).X.hom A₀.X.hom (Spec.map (CommRingCat.ofHom ιe)) :=
  IsPullback.of_hasPullback _ _

theorem eta_bc_fst : η[(bcC ιe A₀).X].left ≫ fstC ιe A₀ =
    Spec.map (CommRingCat.ofHom ιe) ≫ η[A₀.X].left := by
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  change (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))) ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map η[A₀.X]).left ≫
      fstC ιe A₀ = _
  rw [Over.comp_left, Category.assoc]
  erw [pb_map_fst ιe η[A₀.X]]
  rw [← Category.assoc]
  congr 1
  have hc : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom
      (Spec.map (CommRingCat.ofHom ιe)) ≫ (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ιe) := pullback.condition
  have hw := Over.w (Functor.LaxMonoidal.ε
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))))
  have h1 : (𝟙_ (Over (Spec (CommRingCat.of Qbar)))).hom = 𝟙 _ := rfl
  rw [h1, Category.comp_id] at hc
  erw [hc, ← Category.assoc]
  erw [hw]
  exact Category.id_comp _

end Glue

end LeafQCheck

end HDec.HSyn.G0Split.FibreQM.PeriodMapH
