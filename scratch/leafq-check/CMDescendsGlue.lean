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


/-- `ℂ`-points of the base change are determined by their projection to `A₀`. -/
theorem ptC_ext {u u' : (bcC ιe A₀).Pt ℂ} (h : u.left ≫ fstC ιe A₀ = u'.left ≫ fstC ιe A₀) :
    u = u' := by
  ext1
  exact (bc_isPullback ιe A₀).hom_ext h (by rw [Over.w u, Over.w u'])

/-- The identity points correspond. -/
theorem one_corr : (1 : (bcC ιe A₀).Pt ℂ).left ≫ fstC ιe A₀ =
    Spec.map (CommRingCat.ofHom ιe) ≫ (1 : A₀.Pt Qbar).left := by
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    PeriodGlue.ptObj_hom_self, PeriodGlue.ptObj_hom_self']
  erw [Category.id_comp, Category.id_comp]
  exact eta_bc_fst ιe A₀

/-- Endomorphisms act compatibly on corresponding points. -/
theorem endBCe_corr (f : PkgI3.AbVar.End A₀) {w : (bcC ιe A₀).Pt ℂ} {w₀ : A₀.Pt Qbar}
    (hw : w.left ≫ fstC ιe A₀ = Spec.map (CommRingCat.ofHom ιe) ≫ w₀.left) :
    (w ≫ (endBCe ιe A₀ f).hom).left ≫ fstC ιe A₀ =
      Spec.map (CommRingCat.ofHom ιe) ≫ (w₀ ≫ f.hom).left := by
  rw [Over.comp_left, Category.assoc, endBCe_fst, ← Category.assoc, hw, Over.comp_left]
  exact Category.assoc _ _ _

end Glue

/-- Isomorphic abelian varieties have the same dimension. -/
theorem dim_eq_of_iso {B A : PkgI3.AbVar ℂ} (e : PkgI3.AbVar.Hom B A) (e' : PkgI3.AbVar.Hom A B)
    (h1 : e.hom ≫ e'.hom = 𝟙 _) (h2 : e'.hom ≫ e.hom = 𝟙 _) : B.dim = A.dim := by
  obtain ⟨i⟩ : Nonempty (B.X.left ≅ A.X.left) := ⟨
    { hom := e.hom.left
      inv := e'.hom.left
      hom_inv_id := by rw [← Over.comp_left, h1, Over.id_left]
      inv_hom_id := by rw [← Over.comp_left, h2, Over.id_left] }⟩
  exact IsHomeomorph.topologicalKrullDim_eq _ i.hom.homeomorph.isHomeomorph

section Glue2



/-- `#A(k)[n] = n^{2g}` over an algebraically closed field of characteristic 0, from T5. -/
theorem card_torsion_algClosed (hT : PkgI2.TorsionStructure.{0}) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (A : PkgI3.AbVar k) (g : ℕ) (hg : A.dim = g) (n : ℕ) (hn : 0 < n) :
    Nat.card {x : A.Pt k // x ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨e, -⟩ := hT k (ObjBridge.toGrp A) g n hg hn (by exact_mod_cast hn.ne')
  let φ : AlgebraicClosure k ≃ₐ[k] k :=
    (AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  have h1 : Nat.card {x : A.Pt (AlgebraicClosure k) // x ^ n = 1} = n ^ (2 * g) := by
    have : Nat.card {x : A.Pt (AlgebraicClosure k) // x ^ n = 1} =
        Nat.card (PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure k) n) := rfl
    rw [this, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [← h1]
  exact Nat.card_congr ((UnramTate.trPt A φ).toEquiv.subtypeEquiv (fun x => by
    change x ^ n = 1 ↔ (UnramTate.trPt A φ x) ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff])).symm

/-- **`TorsionDescends` from T5 (proved).** `A₀(ℚ̄)[n] → A₀,ℂ(ℂ)[n]` is injective between sets of
`n^{2g}` elements. -/
theorem torsionDescends_of_t5 (hT : PkgI2.TorsionStructure.{0}) : TorsionDescends := by
  intro ιe A₀ v n hn hv
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A₀
  let κ : Qbar →ₐ[Qbar] ℂ := Algebra.ofId Qbar ℂ
  let ψ : A₀.Pt Qbar →* (bcC ιe A₀).Pt ℂ :=
    (E1Sub.bcPt ℂ A₀ ℂ).comp (ZInQ.Contrib.AbVarBC.extPt A₀ κ)
  have hψfst : ∀ p, (ψ p).left ≫ fstC ιe A₀ = Spec.map (CommRingCat.ofHom ιe) ≫ p.left := by
    intro p
    change (E1Sub.bcPt ℂ A₀ ℂ (ZInQ.Contrib.AbVarBC.extPt A₀ κ p)).left ≫ _ = _
    erw [E1Sub.bcPt_fst]
    rw [ZInQ.Contrib.AbVarBC.extPt_apply, Over.comp_left, ZInQ.Contrib.AbVarBC.extHom_left]
    rfl
  have hψinj : Function.Injective ψ :=
    (E1Sub.bcPt_injective A₀ ℂ).comp (ZInQ.Contrib.AbVarBC.extPt_injective A₀ κ)
  let ψn : {x : A₀.Pt Qbar // x ^ n = 1} → {x : (bcC ιe A₀).Pt ℂ // x ^ n = 1} :=
    fun x => ⟨ψ x.1, by rw [← map_pow, x.2, map_one]⟩
  have hinj : Function.Injective ψn := fun x y h => Subtype.ext (hψinj (congrArg Subtype.val h))
  have c0 := card_torsion_algClosed hT A₀ g hg n hn
  have c1 := card_torsion_algClosed hT (bcC ιe A₀) g
    ((@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).trans hg) n hn
  haveI : Finite {x : (bcC ιe A₀).Pt ℂ // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c1]; positivity)
  have hbij : Function.Bijective ψn := hinj.bijective_of_nat_card_le (by rw [c0, c1])
  obtain ⟨⟨v₀, hv₀⟩, hψv⟩ := hbij.2 ⟨v, hv⟩
  have hψv' : ψ v₀ = v := congrArg Subtype.val hψv
  refine ⟨v₀, by rw [← hψv']; exact hψfst v₀, fun v₀' hv₀' => hψinj ?_⟩
  rw [hψv']
  apply ptC_ext ιe A₀
  rw [hψfst]
  exact hv₀'.symm

/-- **The descended data** (glue, proved). -/
theorem descend_main (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRep) (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ)
      (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (QMIso Q.q Q'.q) ∧ ∀ a, κ (Q.q.iota a) = P.q.iota a := by
  obtain ⟨ιe, A₀, e, e', h1, h2⟩ := hST Q.A Q.q Q.surface hcm
  let β := RingEquiv.ofBijective (endBCe ιe A₀) (endBCe_bijective ιe A₀ hR)
  let κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End A₀ := β.symm.toRingHom.comp (conjE e e' h1 h2)
  have hβκ : ∀ f, endBCe ιe A₀ (κ f) = conjE e e' h1 h2 f := fun f => β.apply_symm_apply _
  have κinj : Function.Injective κ := β.symm.injective.comp (conjE_injective e e' h1 h2)
  let q₀ : QMStr A₀ := ⟨κ.comp Q.q.iota, κinj.comp Q.q.injective⟩
  have hdim : A₀.dim = 2 := by
    have := dim_eq_of_iso e e' h1 h2
    rw [← Q.surface, ← this]
    exact (@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).symm
  -- the level structure
  let v : (bcC ιe A₀).Pt ℂ := Additive.toMul (Q.e.eta 1) ≫ e'.hom
  have hv3 : v ^ 3 = 1 := by
    have h30 : Q.e.eta 3 = 0 := (Q.e.ker 3).2 ⟨1, by rw [_root_.mul_one]⟩
    have h3 : (Additive.toMul (Q.e.eta 1)) ^ 3 = 1 := by
      rw [← toMul_nsmul, ← map_nsmul, nsmul_eq_mul, _root_.mul_one]
      push_cast
      rw [h30]; rfl
    change (IsMonHom.monoidHom e'.hom _ (Additive.toMul (Q.e.eta 1))) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  obtain ⟨v₀, hv₀, huniq⟩ := hTD ιe A₀ v 3 (by norm_num) hv3
  let η₀ : LeafQM.O →+ Additive (A₀.Pt Qbar) :=
    { toFun := fun a => qmAct q₀ Qbar a (Additive.ofMul v₀)
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun a b => by rw [map_add]; rfl }
  have hη₀ : ∀ a, Additive.toMul (η₀ a) = v₀ ≫ (q₀.iota a).hom := fun a => rfl
  have lin : ∀ a b : LeafQM.O, η₀ (a * b) = qmAct q₀ Qbar a (η₀ b) := fun a b => by
    change qmAct q₀ Qbar (a * b) _ = _
    rw [map_mul]; rfl
  have ker : ∀ a : LeafQM.O, η₀ a = 0 ↔ ∃ b : LeafQM.O, a = 3 * b := by
    intro a
    have hw : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = Additive.toMul (Q.e.eta a) ≫ e'.hom := by
      rw [show q₀.iota a = κ (Q.q.iota a) from rfl, hβκ, conjE_hom]
      have hl := Q.e.linear a 1
      rw [_root_.mul_one] at hl
      have : Additive.toMul (Q.e.eta a) = Additive.toMul (Q.e.eta 1) ≫ (Q.q.iota a).hom := by
        rw [hl]; rfl
      rw [this]
      simp only [v, Category.assoc]
      rw [reassoc_of% h2]
    have hcorr := endBCe_corr ιe A₀ (q₀.iota a) hv₀
    constructor
    · intro h0
      have h0' : v₀ ≫ (q₀.iota a).hom = 1 := by rw [← hη₀, h0]; rfl
      have h1' : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = 1 :=
        ptC_ext ιe A₀ (by rw [hcorr, h0', one_corr])
      rw [hw] at h1'
      have h3 : Additive.toMul (Q.e.eta a) = 1 := by
        have := congrArg (· ≫ e.hom) h1'
        simp only [Category.assoc, h2, Category.comp_id] at this
        rw [this, MonObj.one_comp]
      exact (Q.e.ker a).1 h3
    · intro hb
      have h3 : Q.e.eta a = 0 := (Q.e.ker a).2 hb
      have h1' : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = 1 := by
        rw [hw, show Additive.toMul (Q.e.eta a) = 1 from congrArg Additive.toMul h3, MonObj.one_comp]
      obtain ⟨_, _, hu1⟩ := hTD ιe A₀ 1 1 one_pos (one_pow _)
      have e1 := hu1 (v₀ ≫ (q₀.iota a).hom) (by rw [← h1']; exact hcorr)
      have e2 := hu1 1 (one_corr ιe A₀)
      have : Additive.toMul (η₀ a) = 1 := by rw [hη₀, e1, ← e2]
      exact congrArg Additive.ofMul this
  let P : QML3 Qbar := ⟨A₀, hdim, q₀, ⟨η₀, lin, ker⟩⟩
  -- the base change from R1fp's naturality
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, hR1, -⟩ := hRep
  obtain ⟨Q', -, hBC⟩ := hR1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom ((Φ Qbar).symm (M3.mk P)) P (by simp)
  have hBC' : IsBaseChangeOf ιe P Q' := hBC
  refine ⟨ιe, P, Q', κ, hBC', ?_, fun a => rfl⟩
  obtain ⟨g', hg', hι', hl'⟩ := hBC'
  -- comparison `Q'.A ≅ A₀ ×_{ℚ̄} ℂ`
  let θ : Q'.A.X ⟶ (bcC ιe A₀).X :=
    Over.homMk ((bc_isPullback ιe A₀).lift g' Q'.A.X.hom hg'.w) ((bc_isPullback ιe A₀).lift_snd _ _ _)
  let θ' : (bcC ιe A₀).X ⟶ Q'.A.X :=
    Over.homMk (hg'.lift (fstC ιe A₀) (bcC ιe A₀).X.hom (bc_isPullback ιe A₀).w) (hg'.lift_snd _ _ _)
  have hθ : θ.left ≫ fstC ιe A₀ = g' := (bc_isPullback ιe A₀).lift_fst _ _ _
  have hθ' : θ'.left ≫ g' = fstC ιe A₀ := hg'.lift_fst _ _ _
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    ext1
    exact hg'.hom_ext (by rw [Over.comp_left, Category.assoc, hθ', hθ]; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ', Over.w θ]; simp)
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    ext1
    exact (bc_isPullback ιe A₀).hom_ext (by rw [Over.comp_left, Category.assoc, hθ, hθ']; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ, Over.w θ']; simp)
  have hη : η[Q'.A.X] ≫ θ = η[(bcC ιe A₀).X] := by
    ext1
    refine (bc_isPullback ιe A₀).hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, hθ, PeriodGlue.eta_comp hl', eta_bc_fst]
    · rw [Over.comp_left, Category.assoc, Over.w θ, Over.w η[Q'.A.X], Over.w η[(bcC ιe A₀).X]]
  have hη' : η[(bcC ιe A₀).X] ≫ θ' = η[Q'.A.X] := by
    rw [← hη, Category.assoc, hθθ', Category.comp_id]
  haveI : IsMonHom θ :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q'.A.X (bcC ιe A₀).X θ hη
  haveI : IsMonHom θ' :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral (bcC ιe A₀).X Q'.A.X θ' hη'
  let qC : QMStr (bcC ιe A₀) :=
    ⟨(endBCe ιe A₀).comp q₀.iota, (endBCe_bijective ιe A₀ hR).1.comp q₀.injective⟩
  let iso1 : QMIso Q.q qC :=
    { φ := e'
      ψ := e
      left := h2
      right := h1
      equivariant := fun a => by
        change _ = e'.hom ≫ (endBCe ιe A₀ (κ (Q.q.iota a))).hom
        rw [hβκ, conjE_hom, reassoc_of% h2] }
  let iso2 : QMIso Q'.q qC :=
    { φ := PkgI3.AbVar.Hom.mk' θ
      ψ := PkgI3.AbVar.Hom.mk' θ'
      left := by simpa using hθθ'
      right := by simpa using hθ'θ
      equivariant := fun a => by
        simp only [PkgI3.AbVar.Hom.hom_mk']
        ext1
        refine (bc_isPullback ιe A₀).hom_ext ?_ ?_
        · change ((Q'.q.iota a).hom.left ≫ θ.left) ≫ fstC ιe A₀ =
            (θ.left ≫ (endBCe ιe A₀ (q₀.iota a)).hom.left) ≫ fstC ιe A₀
          rw [Category.assoc, hθ, hι' a, Category.assoc, endBCe_fst, ← Category.assoc, hθ]
        · simp [Over.w] }
  exact ⟨iso1.trans iso2.symm⟩

/-- **`CMDescends` from `STQM`, `T11b_Rigidity`, `TorsionDescends` and `R1R2fpRep` (proved).** -/
theorem cmDescends_of (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRep) : CMDescends := by
  intro Q
  have com_of : ∀ (P : QML3 Qbar) (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      (∀ a, κ (Q.q.iota a) = P.q.iota a) → ∀ φ ∈ com Q.q, κ φ ∈ com P.q := by
    intro P κ hκ φ hφ
    rw [com, Subring.mem_centralizer_iff] at hφ ⊢
    rintro _ ⟨a, rfl⟩
    rw [← hκ, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_main hST hR hTD hRep Q (Or.inl h)
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_one]⟩, hiso⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_main hST hR hTD hRep Q (Or.inr (Or.inl h))
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by
      rw [← map_mul, ← map_sub, ← map_one κ, ← map_add, hφ2, map_zero]⟩, hiso⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_main hST hR hTD hRep Q (Or.inr (Or.inr h))
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_ofNat]⟩,
      hiso⟩

end Glue2

end LeafQCheck

end HDec.HSyn.G0Split.FibreQM.PeriodMapH

#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of
#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5
