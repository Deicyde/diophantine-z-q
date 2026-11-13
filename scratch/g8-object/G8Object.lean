import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.RhoCont
import ZInQKernel.HDecomp.I3Linalg.TateBC
import ZInQKernel.HDecomp.Conductor.Level
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.C10.Link
import ZInQKernel.Main
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Descent.WP3
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Textbook.Different
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Multiplication.Certificate.Constants

/-! Copied verbatim from scratch/g0-mod-field/ModField.lean L16-1036. -/
section ModFieldCopy

/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- The algebra `L → L'` for `L ≤ L'`. -/
@[instance_reducible] noncomputable def incAlg {L L' : IF} (h : L ≤ L') : Algebra L L' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **`A/L` is a QM model of `P`**: the base change to `L` of the abelian surface of an object
`PK` of `Y₃`'s moduli problem (QM by `𝒪` with level-3 structure) over a subfield `K ≤ L`, itself a
model of `P`'s surface. Such an `A` has good reduction away from `3` (G3,
`LeafQM.AV.QML3.goodReduction`), unlike an arbitrary model (a twist by a cocycle ramified at
`p ∉ T` has bad reduction at `p`), so the later steps (G11, G15) hold for every such `A`. -/
def IsQMModel (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (hKL : K ≤ L) (PK : QML3 K), IsModelOver K PK.A P ∧
    A = @PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-! ## The outputs of G2, G4, G7 -/

/-- **G2's output (Lemma PR(i), N5 L524-529).** A finite Galois `K ⊆ ℚ̄` with `[K:ℚ] ≤ F₀ = 324!`,
unramified outside `T`, with a rational fibre `PK/K` over `P` (Glazer: "Choose a fiber `A/K`";
`RationalFibre`). -/
def G2Out (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K),
    Module.finrank ℚ K ≤ heightF0 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) ∧
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK

/-- `A(ℚ̄)` as an additive group, for `A` over `L ⊆ ℚ̄`. -/
abbrev PtQ (L : IF) (A : PkgI3.AbVar L) : Type := Additive (A.Pt Qbar)

/-- **The descent datum of B1 on the actual `A` (N5 L632-663).** `ε` is a normalized
locally constant sign 2-cocycle of `G_ℚ` inflated from `Gal(L/ℚ)`, and it is the cocycle of `A`:
there are maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` (`μ_σ : ^σA → A` the `B`-linear conjugacy isogeny over
`L`, `σ` acting on coordinates) and reals `a_σ > 0` (`a_σ = (deg μ_σ)^{-1/4}`) with
* `a` inflated from `Gal(L/ℚ)` with `a = 1` on `G_L`,
* `m_σ` the Galois action of `σ` for `σ ∈ G_L` (`μ_σ = 1` there),
* `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L` (`μ` inflated from `Gal(L/ℚ)`, defined
  over `L`),
* `m_σ` commutes with every `L`-endomorphism of `A` (`μ_σ` is `B`-linear and `L` is the Hom
  field),
* `m_σ` surjective with finite kernel (an isogeny composed with a bijection),
* `m_σ m_τ = c(σ,τ) m_{στ}` with `c = n/d ∈ ℚ^×` (the discrepancy commutes with `B`), and
  `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` (N5 L651-660: `ν = aμ`, `ν_σ ^σν_τ = ε ν_{στ}`).
* `m_σ` is algebraic: it is induced by a finite surjective morphism of schemes
  `F_σ : A → A` (`μ_σ`, composed with the identification of the underlying schemes of `^σA` and
  `A`): `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` (G14's trace identities reduce `F_σ` modulo primes).
The maps `m_σ` are on points, hence independent of `ℓ`; on `V_ℓ(A)` they give G8's
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727). -/
def DescentDatum (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) : Prop :=
  IsSignCocycle ε ∧ InflatedFrom L ε ∧ ε 1 1 = 1 ∧
  ∃ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ),
    (∀ σ, 0 < a σ) ∧
    (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) ∧
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
    (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
    (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
    (∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ) ∧
        (((a σ * a τ * ((n : ℝ) / d) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) ∧
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ)

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-- The sign of a rational, as `±1 ∈ ℂ^×` (`1` for `q > 0`). -/
noncomputable def sgnU (q : ℚ) : ℂˣ := if 0 < q then 1 else -1

theorem sgnU_sq (q : ℚ) : sgnU q ^ 2 = 1 := by
  unfold sgnU; split_ifs <;> simp

theorem sgnU_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : sgnU (q * r) = sgnU q * sgnU r := by
  unfold sgnU
  rcases lt_or_gt_of_ne hq with hq' | hq' <;> rcases lt_or_gt_of_ne hr with hr' | hr'
  · rw [if_pos (mul_pos_of_neg_of_neg hq' hr'), if_neg (not_lt.2 hq'.le),
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_neg_of_pos hq' hr').le), if_neg (not_lt.2 hq'.le),
      if_pos hr']; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_pos_of_neg hq' hr').le), if_pos hq',
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_pos (mul_pos hq' hr'), if_pos hq', if_pos hr']; simp

/-- `sgn(q)·|q| = q`, in `ℂ`. -/
theorem sgnU_mul_abs (q : ℚ) : ((sgnU q : ℂˣ) : ℂ) * ((|(q : ℝ)| : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
  unfold sgnU
  split_ifs with h
  · have : (0 : ℝ) < q := by exact_mod_cast h
    rw [abs_of_pos this]; simp
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 h
    rw [abs_of_nonpos this]; push_cast; ring

/-- **The conjugacy isogenies before normalization (N5 L632-645; the content of G4 + B1's
geometric half).** Maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the first four clauses of
`DescentDatum`; the discrepancy `c(σ,τ) = n/d ∈ ℚ^×` with `d·m_σ m_τ = n·m_{στ}`, a 2-cocycle
inflated from `Gal(L/ℚ)` with `c(1,1) = 1`; and degree multiplicativity in the form
`|ker m_σ|·|ker m_τ| = c(σ,τ)⁴·|ker m_{στ}|` (`deg μ = |ker μ(ℚ̄)|` in characteristic 0,
`deg[n] = n⁴` on a surface); and algebraicity: `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite
surjective scheme morphism `F_σ : A → A`. -/
def ConjugacyData (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A))
    (c : GQ → GQ → ℚ) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, c σ τ ≠ 0 ∧ ∃ n d : ℤ, d ≠ 0 ∧ c σ τ = n / d ∧
      d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∀ σ τ ρ, c (σ * τ) ρ * c σ τ = c τ ρ * c σ (τ * ρ)) ∧
  (∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) →
      c σ τ = c σ' τ') ∧
  c 1 1 = 1 ∧
  (∀ σ τ, (Nat.card (m σ).ker : ℚ) * Nat.card (m τ).ker = c σ τ ^ 4 * Nat.card (m (σ * τ)).ker) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- The Galois action of `σ' ∈ Aut(ℚ̄/L)` on `A(ℚ̄)` is bijective. -/
theorem galAct_bijective {L : IF} (A : PkgI3.AbVar L) (σ' : Qbar ≃ₐ[L] Qbar) :
    Function.Bijective (A.galAct σ') := by
  have key : ∀ (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar),
      A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
    intro g h P
    show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]
  have one : ∀ P : A.Pt Qbar, A.galAct 1 P = P := by
    intro P
    show PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  refine ⟨fun P Q h => ?_, fun Q => ⟨A.galAct σ'⁻¹ Q, ?_⟩⟩
  · have := congrArg (A.galAct σ'⁻¹) h
    rwa [key, key, inv_mul_cancel, one, one] at this
  · rw [key, mul_inv_cancel, one]

/-- `k ∈ G_L` as an `L`-automorphism of `ℚ̄`. -/
noncomputable def toLAut {L : IF} (k : GQ) (hk : k ∈ GQL L) : Qbar ≃ₐ[L] Qbar :=
  AlgEquiv.ofRingEquiv (f := (act k).toRingEquiv) (fun x => mem_GQL.mp hk x x.2)

theorem toLAut_apply {L : IF} (k : GQ) (hk : k ∈ GQL L) (x : Qbar) : toLAut k hk x = act k x :=
  rfl

/-- The kernel sizes of `m_k`, `m_{σk}`, `m_{kσ}` for `k ∈ G_L` (from the first two clauses of
`ConjugacyData`). -/
theorem card_ker_GL {L : IF} {A : PkgI3.AbVar L} {m : GQ → (PtQ L A →+ PtQ L A)}
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (σ k : GQ) (hk : k ∈ GQL L) :
    Nat.card (m k).ker = 1 ∧ Nat.card (m (σ * k)).ker = Nat.card (m σ).ker ∧
      Nat.card (m (k * σ)).ker = Nat.card (m σ).ker := by
  have hmk : m k = MonoidHom.toAdditive (A.galAct (toLAut k hk)) :=
    hgal k (toLAut k hk) (toLAut_apply k hk)
  have hbij : Function.Bijective (m k) := by
    rw [hmk]; exact galAct_bijective A (toLAut k hk)
  have hker : (m k).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : m k x = m k 0 := by rw [map_zero]; exact hx
    exact hbij.1 this
  refine ⟨by rw [hker]; simp, ?_, ?_⟩
  · rw [(hinfl σ k hk).1]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨m k x, x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hbij.1 (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨⟨x, hy⟩, rfl⟩
  · have hk2 : ((m k).comp (m σ)).ker = (m σ).ker := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
      constructor
      · intro h
        have : m k (m σ x) = m k 0 := by rw [map_zero]; exact h
        exact hbij.1 this
      · intro h; rw [h, map_zero]
    rw [(hinfl σ k hk).2, hk2]

/-- `a_σ = |ker m_σ|^{-1/4}` (`= (deg μ_σ)^{-1/4}`, N5 L645). -/
noncomputable def normA {L : IF} {A : PkgI3.AbVar L} (m : GQ → (PtQ L A →+ PtQ L A)) (σ : GQ) :
    ℝ := (Nat.card (m σ).ker : ℝ) ^ (-(1 / 4 : ℝ))

/-- **B1's normalization, proved** (N5 L645-663): from the conjugacy isogenies, `ε = sgn c` is a
normalized locally constant sign cocycle inflated from `Gal(L/ℚ)`, and `(m, a = |ker m|^{-1/4},
ε)` is a descent datum. -/
theorem descentDatum_of_conjugacy (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (c : GQ → GQ → ℚ)
    (h : ConjugacyData L A m c) : DescentDatum L A (fun σ τ => sgnU (c σ τ)) := by
  obtain ⟨hgal, hinfl, hend, hfin, hc, hcoc, hcinf, hc11, hdeg, halg⟩ := h
  have hkerL := card_ker_GL hgal hinfl
  have hcard : ∀ σ, 0 < Nat.card (m σ).ker := fun σ => by
    haveI : Finite (m σ).ker := (hfin σ).2.to_subtype
    exact Nat.card_pos
  -- the sign cocycle
  have hloc : IsLocallyConstant (Function.uncurry fun σ τ => sgnU (c σ τ)) := by
    refine isLocallyConstant_of_openSubgroup ((GQL L).prod (GQL L))
      (by rw [Subgroup.coe_prod]; exact L.fixingSubgroup_isOpen.prod L.fixingSubgroup_isOpen)
      _ ?_
    rintro ⟨σ, τ⟩ ⟨k₁, k₂⟩ hk
    rw [Subgroup.mem_prod] at hk
    simp only [Function.uncurry_apply_pair, Prod.mk_mul_mk]
    congr 1
    refine (hcinf σ (σ * k₁) τ (τ * k₂) ?_ ?_).symm
    · intro x hx
      show act σ x = act σ (act k₁ x)
      rw [mem_GQL.mp hk.1 x hx]
    · intro x hx
      show act τ x = act τ (act k₂ x)
      rw [mem_GQL.mp hk.2 x hx]
  refine ⟨⟨hloc, fun σ τ => sgnU_sq _, fun σ τ ρ => ?_⟩, ?_, ?_, m, normA m, ?_, ?_, hgal, hinfl,
    hend, hfin, ?_, halg⟩
  · rw [← sgnU_mul (hc _ _).1 (hc _ _).1, ← sgnU_mul (hc _ _).1 (hc _ _).1, hcoc]
  · exact fun σ σ' τ τ' h1 h2 => by simp only [hcinf σ σ' τ τ' h1 h2]
  · show sgnU (c 1 1) = 1
    rw [hc11]; unfold sgnU; simp
  · intro σ; unfold normA; exact Real.rpow_pos_of_pos (by exact_mod_cast hcard σ) _
  · intro σ k hk
    obtain ⟨h1, h2, h3⟩ := hkerL σ k hk
    unfold normA
    rw [h1, h2, h3]
    simp
  · intro σ τ
    obtain ⟨hc0, n, d, hd, hcnd, hnd⟩ := hc σ τ
    have hn : n ≠ 0 := by
      rintro rfl; apply hc0; rw [hcnd]; simp
    refine ⟨n, d, hn, hd, hnd, ?_⟩
    have hx : (0 : ℝ) < Nat.card (m σ).ker := by exact_mod_cast hcard σ
    have hy : (0 : ℝ) < Nat.card (m τ).ker := by exact_mod_cast hcard τ
    have hz : (0 : ℝ) < Nat.card (m (σ * τ)).ker := by exact_mod_cast hcard (σ * τ)
    have hdegR : (Nat.card (m σ).ker : ℝ) * Nat.card (m τ).ker =
        |(c σ τ : ℝ)| ^ 4 * Nat.card (m (σ * τ)).ker := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hdeg σ τ)
      push_cast at this
      rw [this, pow_abs, abs_of_nonneg (by positivity)]
    have hcR : ((n : ℝ) / d) = (c σ τ : ℝ) := by rw [hcnd]; push_cast; rfl
    have habs : (0 : ℝ) < |(c σ τ : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
    have key : normA m σ * normA m τ * |(c σ τ : ℝ)| = normA m (σ * τ) := by
      unfold normA
      rw [← Real.mul_rpow hx.le hy.le, hdegR, Real.mul_rpow (by positivity) hz.le]
      rw [show |(c σ τ : ℝ)| ^ 4 = |(c σ τ : ℝ)| ^ ((4 : ℕ) : ℝ) by norm_cast,
        ← Real.rpow_mul habs.le]
      rw [show ((4 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    rw [hcR]
    have e1 : ((normA m σ * normA m τ * (c σ τ : ℝ) : ℝ) : ℂ) =
        ((sgnU (c σ τ) : ℂˣ) : ℂ) * ((normA m σ * normA m τ * |(c σ τ : ℝ)| : ℝ) : ℂ) := by
      have h := sgnU_mul_abs (c σ τ)
      push_cast at h ⊢
      linear_combination (-((normA m σ : ℂ) * (normA m τ : ℂ))) * h
    rw [e1, key]

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

theorem mem_GQL_bot (σ : GQ) : σ ∈ GQL (⊥ : IF) := by
  rw [mem_GQL]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact (act σ).commutes r

theorem galAct_mul {L : IF} (A : PkgI3.AbVar L) (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar) :
    A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
  show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- **Sanity check (proved).** For every abelian variety `A` over `ℚ` (here `L = ⊥ ⊆ ℚ̄`), the
Galois action itself is a descent datum with `ε = 1`, `a = 1`, `F_σ = id`. So `DescentDatum` is
not contradictory. -/
theorem descentDatum_bot (A : PkgI3.AbVar (⊥ : IF)) : DescentDatum ⊥ A (fun _ _ => 1) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  refine ⟨⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ => by simp⟩,
    fun _ _ _ _ _ _ => rfl, rfl, m, fun _ => 1, fun _ => one_pos, fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul, one_smul, hmul], by simp⟩
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **G4's output (N5 L532-563 and the B1 normalization L632-663).** A finite Galois `L ⊆ ℚ̄`
(the Hom field) with `[L:ℚ] ≤ D`, unramified outside `T`, a QM model `A/L` of `P` (`IsQMModel`), and
the descent datum `ε` of `A` (`DescentDatum`). -/
def G4Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Module.finrank ℚ L ≤ heightD ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
    ∃ (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ), IsQMModel L A P ∧ DescentDatum L A ε

/-- **G7's output (B2-B3, N5 L664-716).** The data of G4 (`L`, `A/L`, `ε`), and: a Dirichlet
character `χ` mod `N`, a locally constant cochain `β : G_ℚ → ℂ^×` with `β² = χ` and `∂β = ε`, and
the kernel field `L' ⊇ L` of `β|_{G_L}`: finite Galois, `G_{L'} = G_L ∩ ker β`,
`[L':ℚ] ≤ Q_D · M_{S_mul}(u)`, and the base change `A_{L'}` is a model of `P`'s surface. -/
def G7Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ),
    IsQMModel L A P ∧ DescentDatum L A ε ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
    (∀ x y, β x * β y = ε x y * β (x * y)) ∧
    (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
    (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-! ## Transitivity of base change -/

/-- `(A_{L'})_{ℚ̄} ≅ A_{ℚ̄}` for `L ≤ L' ⊆ ℚ̄` (pasting of pullbacks). -/
noncomputable def baseChangeTrans {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) :
    ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)).baseChange Qbar).X ≅
      (A.baseChange Qbar).X := by
  letI := incAlg h
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L L')) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp]
    congr 1
  exact ((Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)))
      (Spec.map (CommRingCat.ofHom (algebraMap L L')))).app A.X).symm ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj A.X) hcomp)

theorem isModelOver_baseChange {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) (P : QML3 Qbar)
    (hA : IsModelOver L A P) :
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)) P := by
  obtain ⟨e⟩ := hA
  exact ⟨baseChangeTrans h A ≪≫ e⟩

theorem IsQMModel.isModelOver {L : IF} {A : PkgI3.AbVar L} {P : QML3 Qbar}
    (h : IsQMModel L A P) : IsModelOver L A P := by
  obtain ⟨K, hKL, PK, hPK, rfl⟩ := h
  exact isModelOver_baseChange hKL PK.A P hPK

/-! ## G7 from G4 (proved) -/

/-- `max S_mul ≤ D` (copied from `ZInQKernel/Main.lean`, `ZInQ.Mult.le_heightD_of_mem_S_mul`). -/
theorem le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

theorem admissible_S_mul :
    (∀ p ∈ Mult.S_mul, p.Prime) ∧ (∀ p ∈ Mult.S_mul, (p : ℝ) ≤ (heightD : ℝ)) ∧
      (10 : ℝ) ^ 12 ≤ (heightD : ℝ) :=
  ⟨fun _ hp => Mult.prime_of_mem_S_mul hp,
   fun _ hp => by exact_mod_cast le_heightD_of_mem_S_mul hp,
   by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD⟩

/-- **G7 (B2-B3 on the actual descent datum), proved** from G4's output and glue-descent's four
B2 leaves, by `GlueDescent.B3Q.b3_degree_le_QM` at `S = S_mul`, `R = D`, `η = 1`. -/
theorem g7Out_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_degree_le_QM hHasse hTwo hSq hUnr Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u L hLD
      ε hε hinf h11 hram 1 (fun _ => by simp) (IsLocallyConstant.const 1)
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, isModelOver_baseChange hle A P hA.isModelOver⟩

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-- **B2 over `G_ℚ` with the level of `χ` exposed** (the proof of
`GlueDescent.B2Q.b2_of_leaves`, copied; the only change is the extra output
`N = chiLevel T₋ = ∏_{p ∈ T₋} lev p` with `T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`). -/
theorem b2_of_leaves_level (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∃ Tm ⊆ T, N = chiLevel Tm) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, ⟨Tm, Finset.filter_subset _ _, rfl⟩, hsupp, hord, hβl, hβs, hβe⟩

/-- **B3 from a given B2 cochain** (the proof of `GlueDescent.B3Q.b3_of_leaves`, copied, with
`b2_of_leaves`' output taken as hypotheses so that the twist `η` may depend on it). -/
theorem b3_of_cochain
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₁ : GQ → ℂˣ) (hβl₁ : IsLocallyConstant β₁)
    (hβs₁ : ∀ x, β₁ x ^ 2 = galChar χ x) (hβe₁ : ∀ x y, β₁ x * β₁ y = ε x y * β₁ (x * y))
    (tw : GQ →* ℂˣ) (htw : ∀ x, tw x ^ 2 = 1) (htwl : IsLocallyConstant tw) :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ),
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β₁ σ * tw σ = 1) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  let β : GQ → ℂˣ := fun x => β₁ x * tw x
  have hβl : IsLocallyConstant β := hβl₁.mul htwl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ tw htw
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ tw
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index
      (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨L', hle, hfd, hgal, hGL', ?_⟩
  rw [hL', hL]; exact hidx

theorem two_mem_T (u : ℚ) : 2 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_two (by norm_num))

/-- **The data of G7, clause by clause** (the interface handed to G8-G16). For the fibre `P`
over `J(u)`: the Hom field `L` (finite Galois, unramified outside `T`), the model `A/L` with its
descent datum `ε` (B1), the Dirichlet character `χ` mod `N` (`N = ∏_{p ∈ T₋} lev p` for some
`T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`: `χ` is a product of odd characters mod `p` and mod `4`, N5
L677-683, which bounds the conductor of `β` at every prime, as G15 needs), the
cochain `β` (locally constant, `β² = χ`, `∂β = ε`, twisted so that inertia outside `T` dies), and
the kernel field `L' ⊇ L` of `β|_{G_L}`: `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`,
`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface. -/
def G7Data (u : ℚ) (P : QML3 Qbar) (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF) (hLL' : L ≤ L') : Prop :=
  IsQMModel L A P ∧ DescentDatum L A ε ∧
  (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T u) ∧
  (∃ Tm ⊆ T u, N = chiLevel Tm) ∧
  IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
  (∀ x y, β x * β y = ε x y * β (x * y)) ∧
  (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
  (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-- **G7's output with the twist** (N5 L702-716): the data of `G7Data` exist. -/
def G7OutUnr (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL'

/-- **G7 with the twist, proved** from G4's output and the four B2 leaves: B2
(`b2_of_leaves`), the twist killing inertia outside `T` (`GlueB3Unram.unramified_outside_noLeaf`,
no leaf), B3 (`b3_of_cochain`) and the constants (`degree_le_QM`). -/
theorem g7OutUnr_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

theorem g7Out_of_g7OutUnr (u : ℚ) (P : QML3 Qbar) (h : G7OutUnr u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hA, hD, hram, -, -, hβl, hβs,
    hβe, hGL', hdeg, -, hM⟩ := h
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, hM⟩

/-! ## G2's bookkeeping (proved) -/

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK

/-- **G2, proved from the fibre cover**: the splitting field is Galois of degree `≤ 324!`
(`GlueRepo.Numerics.splitting_degree_le`). -/
theorem g2Out_of_cover (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ)
    (P : QML3 Qbar) (h : FibreCoverOut Y Φ u P) : G2Out Y Φ u P := by
  obtain ⟨f, hs, hd, hram, A, hA⟩ := h
  have hsp : f.IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  have hgal : IsGalois ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IsGalois.of_separable_splitting_field hs
  have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) ≤ heightF0 := by
    rw [(Polynomial.IsSplittingField.algEquiv _ f).toLinearEquiv.finrank_eq]
    exact GlueRepo.Numerics.splitting_degree_le f hs hd
  exact ⟨_, hfd, hgal, hdeg, hram, A, hA⟩

/-! ## G4's bookkeeping (proved) -/

/-- **Compositum of unramified fields (STANDARD; remaining, not in Mathlib v4.35).** If `E`
and `K` are finite over `ℚ` and unramified at `p`, so is `E ⊔ K` (Neukirch, *Algebraic Number
Theory*, I (8.?)/III, UNVERIFIED locator; a prime is unramified in a compositum iff it is in both
factors, for Galois factors). -/
def UnramifiedSup : Prop :=
  ∀ (E K : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ K] [IsGalois ℚ E] [IsGalois ℚ K]
    (p : ℕ), UnramifiedAt E p → UnramifiedAt K p → UnramifiedAt (E ⊔ K) p

/-- **G4's input, the kernel field (N5 L540-563 and B1, L632-663; remaining).** For a field `K`
and model `A/K` as in G2's output: `W₀ = Res_{K/ℚ} A` has endomorphism lattice of rank `r ≤ 16F₀²`;
the image of `G_ℚ` on it is a finite subgroup `G ≤ GL_r(ℤ)` with kernel field `E`
(`[E:ℚ] = |G|`), unramified outside `T` (inertia at `p ∉ T` acts trivially on the Tate module of
`W₀`, which has good reduction there); and the base change `A_L` of `A` to the Hom field
`L = E ⊔ K` carries conjugacy isogenies `μ_σ : ^σA → A` over `L`, `B`-linear after the
Skolem-Noether correction, with rational discrepancy (`ConjugacyData`; B1's normalization to a
sign cocycle is proved, `descentDatum_of_conjugacy`). -/
def KernelFieldOut (u : ℚ) (P : QML3 Qbar) (K : IF) (A : PkgI3.AbVar K) : Prop :=
  ∃ (r : ℕ), r ≤ 16 * heightF0 ^ 2 ∧
  ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IF) (_ : FiniteDimensional ℚ E)
    (_ : IsGalois ℚ E), Module.finrank ℚ E = Nat.card G ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt E p) ∧
    ∃ (m : GQ → (PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) →+
        PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right))))
      (c : GQ → GQ → ℚ),
      ConjugacyData (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) m c

/-- **G4, proved from the kernel field**: `L = E ⊔ K` is finite Galois, unramified outside `T`
(`UnramifiedSup`), `[L:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D` (Minkowski,
`GlueRepo.TorsionFree.card_le_three_pow`; `GlueRepo.Numerics.a8_field`), `A_L = (PK.A)_L` is a QM
model of `P` (`IsQMModel`), and B1's normalization gives the descent datum
(`descentDatum_of_conjugacy`). -/
theorem g4Out_of_kernelField (hSup : UnramifiedSup) (u : ℚ) (P : QML3 Qbar) (K : IF)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hK : Module.finrank ℚ K ≤ heightF0)
    (hramK : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) (PK : QML3 K)
    (hPK : IsModelOver K PK.A P) (h : KernelFieldOut u P K PK.A) : G4Out u P := by
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hCD⟩ := h
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hK hE hr
  have : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  exact ⟨E ⊔ K, inferInstance, inferInstance, hdeg,
    fun p hp => hSup E K p (hramE p hp) (hramK p hp), _, _,
    ⟨K, le_sup_right, PK, hPK, rfl⟩, descentDatum_of_conjugacy _ _ m c hCD⟩

/-! ## The remaining glue as Props, and the composite -/

/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P

/-- **Remaining (G4 + B1): the kernel field of `Res_{K/ℚ} A` and the descent datum on the Hom
field**, for every field `K` and rational fibre `PK/K` as in G2's output (h-decomposition G4: inputs R2, R3, T6,
R7a, T28; A7 proved, `LeafQM.AV.fibre_conjugates_isomorphic`; B1's algebra proved,
glue-descent `B1Quat`, `Cochain`; uses NoCM (G6) for `End⁰(A_ℚ̄) = B`). -/
def KernelFieldExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK → KernelFieldOut u P K PK.A

/-- **G2 → G4 → G7 (proved)**: from the two remaining glue Props and the four B2 leaves, every
fibre context has G7's output. -/
theorem fieldDescent (hCover : FibreCoverExists) (hKer : KernelFieldExists) (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7Out u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7Out_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-- **G2 → G4 → G7 with the twist (proved)**: as `fieldDescent`, with `L'` unramified outside `T`
and the clause list `G7Data`. -/
theorem fieldDescentUnr (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7OutUnr_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-! ## How G7's output feeds `ModularConstituent` -/

/-- (copied from scratch/g0-split/part_split.lean, `G0Split.CommonConstituent`, verbatim) The
hypotheses of E1: for some prime `ℓ` and field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a
common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- A finite-dimensional `L ⊆ ℚ̄` is a number field. -/
theorem numberField_of_fd (L : IF) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- **`ModularConstituent`** (scratch/g0-split/part_split.lean, piece 10), copied with
def-faltings' copy `ZInQ.DefFaltings.AbVar` and the bridge `LeafAdopt.abVarEquiv` (the identity on
the underlying scheme) replaced by the kernel's `PkgI3.AbVar`, which `ZInQKernel/HDecomp/`
already uses for both. -/
def ModularConstituentG : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : PkgI3.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent A (J.baseChange L.K)

/-- **The remaining ranges G8-G16 (the next tasks' target), as one Prop.** For every fibre
context and every G7 data (`G7Data`): a level `1 ≤ M ≤ Q_D·M_{S_mul}(u)²`, a `J₁(M)` over `ℚ`, and a
common constituent of `V_ℓ(A_{L'})` and `V_ℓ(J₁(M)_{L'})` as `G_{L'}`-representations (G8: `ρ_ℓ`
from `β`, `a_σ`, `m_σ`; G9-G12: de Rham, odd, modular; G13-G16: newform, level, Eichler-Shimura). -/
def AfterG7 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ (M : ℕ) (J : PkgI3.AbVar ℚ), 0 < M ∧ LeafModCurves.IsJ1 M J ∧
      (M : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      @CommonConstituent L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) (J.baseChange L')

/-- **`ModularConstituent` from this range and the next (proved)**: G2, G4, G7 here
(`fieldDescentUnr`) and the ranges G8-G16 as `AfterG7`. -/
theorem modularConstituent_of_ranges (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hy, hπ⟩
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdata⟩ :=
    fieldDescentUnr hCover hKer hSup hHasse hTwo hSq hUnr Y Φ π u P hctx
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ := hRest Y Φ π u P hctx L A ε N χ β L' hle hdata
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨⟨L'⟩, algebraMap L' Qbar, @PkgI3.AbVar.baseChange L _ A L' _ (incAlg hle), M, J,
    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩

/-- **The same, with glue-descent's `LeafHasse`, `LeafLocalTwo` replaced by the bundle's T14-T15**
(`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`; `GlueWP3.leafHasse_of_T14`,
`leafLocalTwo_of_T15`). -/
theorem modularConstituent_of_ranges_T14 (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup) (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges hCover hKer hSup (GlueWP3.leafHasse_of_T14 hH hR)
    (GlueWP3.leafLocalTwo_of_T15 hC) hSq hUnr hRest

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

/-- (copied) The restriction map `G_K → G_ℚ` (Mathlib's `Field.absoluteGaloisGroup.map`). -/
noncomputable def resQ (K : Type) [Field K] [NumberField K] :
    Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
noncomputable def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied) g0-mod-galois' input "output of G2": inertia at `p ∉ T` lies in `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- (copied) g0-mod-galois' input "output of G7 at the coefficient prime `ℓ`". -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

end GaloisCopy

/-- **Bridge 1 (Mathlib-level Galois theory; proved below, `resQRange`).** For a finite Galois `L' ⊆ ℚ̄`, the
image of `resQ L' : G_{L'} → G_ℚ` is `G_{L'} = Fix(L')` (true for every embedding of the
algebraic closures because `L'/ℚ` is normal). -/
def ResQRange : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    (@GaloisCopy.resQ L' _ (numberField_of_fd L')).range = L'.fixingSubgroup

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (GaloisCopy.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@GaloisCopy.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (GaloisCopy.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : Qbar ≃ₐ[ℚ] Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x


theorem resQRange : ResQRange := fun L' _ _ => resQ_range L'

/-- **g0-mod-galois' `G2Out` for `K = L'`, proved** from `G7Data` (B3(v): inertia outside `T`
fixes `L'`) and `ResQRange`. -/
theorem galoisG2Out_of_g7Data (hRes : ResQRange) (u : ℚ) (P : QML3 Qbar) (L : IF)
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (h : G7Data u P L A ε N χ β L' hLL') :
    @GaloisCopy.G2Out L' _ (numberField_of_fd L') (T u) := by
  intro p hp hpT v hv σ hσ
  rw [hRes L']
  have hv' : GlueB3Unram.LiesOver v p := hv
  exact h.2.2.2.2.2.2.2.2.2.2.1 p hp hpT v hv' (Subgroup.mem_map_of_mem _ hσ)

/-- **Bridge 2 (remaining; the Tate functor on the descent datum, §3 of the report).** From G7's
data, the rank-4 endomorphism ring and `dim A_{L'} = 2` (G5-G6, A9; `model_dim`), for every `ℓ`:
operators `Tm σ` (`ℚ̄_ℓ ⊗ T_ℓ(m_σ)` transported to `V_ℓ(A_{L'})`), `c = n/d`, `a`, `ε`, `β` mapped
into `ℚ̄_ℓ` by one embedding of the number field they generate, and matrix units of
`End_{L'}(A) ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`, satisfying g0-mod-galois' `G7Out`. -/
def TateBridge : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu

end G0ModField
end ModFieldCopy

/-! Copied verbatim from scratch/g14-trace/part_bridge.lean (without its #print axioms), inside a
section re-issuing ModField's file-level opens (active where g14-trace appended it). -/
section G14BridgeCopy
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
/-!
# g14-trace, second file: the linked Tate bridge at `ℓ = 3, 5`

Appended to a verbatim copy of `scratch/g0-mod-field/ModField.lean` (g0-mod-field's `G7Data`,
`TateBridge`, `GaloisCopy.G7Out`). `TateBridge` gives the `ℓ`-adic data at each `ℓ` separately
(`∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`), which does not determine the traces of `r₃` against `r₅`
(g14-trace §1, `g7Out_twist`). `TateBridge35` is the linked form at `ℓ = 3, 5` that
`G14Trace.g12Spec_g14_of_galois` consumes: one pair `a, β : G_ℚ → ℚ̄` mapped to `ℚ̄₅`, `ℚ̄₃` by
embeddings `j₅`, `j₃` (TateBridge's own docstring: "mapped into `ℚ̄_ℓ` by one embedding of the
number field they generate"), and the operators `Tm_ℓ` (from one points-level `m_σ`) in the
Frobenius link at Frobenius elements. No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Bridge

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField
open GlueC10Link (FrobCompare)

/-- (copy of `G14Trace.FrobTraceLink`, over `GaloisCopy.Vb`) **The Frobenius trace link (GLUE,
AV side; N5 L781-786).** Outside a finite set `S`, at every arithmetic Frobenius `τ` above `p`,
`N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian variety over a
field of characteristic `p`, at `ℓ = 3` and `ℓ = 5` (kernel's `GlueC10Link.FrobCompare`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (GaloisCopy.Vb A 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (GaloisCopy.Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
    PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The linked Tate bridge at `ℓ = 3, 5` (GLUE; replaces the `ℓ = 3, 5` instances of
`G0ModField.TateBridge`).** From G7's data, `dim A_{L'} = 2` and `rank End = 4`: one pair
`a, β : G_ℚ → ℚ̄` (N5's `a_σ` and `β(σ)`, algebraic), embeddings `j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃`, and
for `ℓ = 5, 3` the operators `Tm_ℓ` (`ℚ̄_ℓ ⊗ V_ℓ(m_σ)`), `c_ℓ`, `ε_ℓ` and matrix units with
`G7Out` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, `FrobTraceLink` for `Tm₅`, `Tm₃`, and `β` an
algebraic form of `G7Data`'s `β` (`ιC ∘ βQ = β`; G15 needs this `β`). `aQ` is not tied to
`DescentDatum`'s `a` in the statement (`a_σ = deg(μ_σ)^{-1/4}`, N5 L647, is algebraic), nor `Tm_ℓ` to
its `m_σ`, as in `TateBridge`; for G14 only the common `aQ` and `FrobTraceLink` matter (a joint
twist at both `ℓ` keeps the system compatible). -/
def TateBridge35 : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      ∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)

instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `TateBridge35` contains the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridge` (proved): it is a
strengthening at these two primes. -/
theorem tateBridge_five_three_of_35 (h : TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β' : PkgI4.GQ → PadicAlgCl 5)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm c ε' a β' uu) ∧
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a β' : PkgI4.GQ → PadicAlgCl 3)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm c ε' a β' uu) := by
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, -⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨⟨Tm5, c5, ε5, _, _, u5, h5⟩, ⟨Tm3, c3, ε3, _, _, u3, h3⟩⟩

end G14Bridge
end
end G14BridgeCopy

/-! Copied verbatim from scratch/g14-trace/G14Trace.lean L10-end. -/
/-! Copied from scratch/c9-rhof/C9.lean (compiled there), lines 4-632. -/
section C9Copy

/-!
# c9-rhof: glue C9 for R16's representation `ρ_{f,ι}` (`LeafModCurves.rhoF`)

Check with `lake env lean scratch/c9-rhof/C9.lean`.

* §1. `rhoF` is an equivariant quotient of `V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ` (`quotMap`, proved).
* §2. Semisimplicity of `rhoF` from Faltings' Satz 3 (`PkgI3.FaltingsSemisimple`), the leaf
  I3.M0 (`PkgI3.TateModuleFree`) and the kernel's proved base change of semisimplicity.
* §3. Continuity of `rhoF` (matrix coefficients in any basis) from I3.M0 and the kernel's
  continuity of `ρ_ℓ` (glue-rho-cont).
* §4. Density of arithmetic Frobenius elements (`FrobeniusDense`, leaf T18, copied verbatim from
  `scratch/h-decomposition/Leaves.lean`) ⇒ continuous functions agreeing on Frobenius agree.
* §5. Brauer–Nesbitt (`GlueC10.BrauerNesbittChar0`, leaf T19): `rhoF ≅ r` for every continuous
  semisimple `r` with the `AttachedTo` traces of `f` (outside a finite set).
* §6. Against R14 (`EigenformRepExists`'s `GaloisRep`), and against C8's `r₅` after the twist
  (EigenformTwist, NewformOfEigenform): C9 and the hypothesis `h₅` of `GlueC10.c10`.

Leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

namespace C9Rhof

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ## §1. `rhoF` as a quotient of `V_ℓ(A) ⊗ ℚ̄_ℓ` -/

section Quot

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

/-- Evaluation `v ↦ (φ ↦ φ v)`, `V_ℓ(A) → (ι-eigenfunctionals)^∨`, `ℚ_ℓ`-linear. -/
def ev : A.V ℓ →ₗ[ℚ_[ℓ]] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) where
  toFun v :=
    { toFun := fun φ => (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' v w := by
    ext φ
    simp
  map_smul' c v := by
    ext φ
    simp [Algebra.smul_def]

@[simp] theorem ev_apply (v : A.V ℓ) (φ : eigenFun ℓ A θ emb) :
    ev ℓ A θ emb v φ = (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v := rfl

/-- The `ℚ̄_ℓ`-linear extension `V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ → (ι-eigenfunctionals)^∨` of `ev`. -/
def quotMap : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) →ₗ[PadicAlgCl ℓ]
    Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
  (ev ℓ A θ emb).liftBaseChange (PadicAlgCl ℓ)

theorem rhoF_ev (σ : GQ) (v : A.V ℓ) :
    rhoF ℓ A θ emb σ (ev ℓ A θ emb v) = ev ℓ A θ emb (A.galRep ℓ σ v) := by
  ext φ
  rfl

/-- `quotMap` is `G_ℚ`-equivariant from the base change of `ρ_ℓ` to `rhoF`. -/
theorem quotMap_equivariant (σ : GQ) (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    quotMap ℓ A θ emb (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ x) =
      rhoF ℓ A θ emb σ (quotMap ℓ A θ emb x) := by
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    change quotMap ℓ A θ emb ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (e ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul]
    simp only [quotMap, LinearMap.liftBaseChange_tmul, map_smul, rhoF_ev]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `quotMap` is onto when the eigenfunctionals are finite-dimensional. -/
theorem quotMap_surjective [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    Function.Surjective (quotMap ℓ A θ emb) := by
  rw [← LinearMap.range_eq_top, quotMap, LinearMap.range_liftBaseChange]
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have : (z : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) ≠ 0 := by
    intro h; exact hz (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, (z : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v ≠ 0 := by
    by_contra h
    push Not at h
    exact this (LinearMap.ext h)
  exact ⟨ev ℓ A θ emb v, ⟨v, rfl⟩, hv⟩

end Quot

/-! ## §2. Semisimplicity -/

section SS

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

instance : CharZero (PadicAlgCl ℓ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `V_ℓ(A)` is finite-dimensional over `ℚ_ℓ` (from the leaf I3.M0). -/
theorem finiteDimensional_V (hT : TateModuleFree) : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨h1, h2, -⟩ := hT ℚ A ℓ hℓ
  infer_instance

/-- **Semisimplicity of `ρ_{f,ι}` (GLUE, proved from Faltings' Satz 3 and I3.M0).** -/
theorem rhoF_semisimple (hS : FaltingsSemisimple) (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation := by
  have := finiteDimensional_V ℓ A hT
  have h1 : (A.galRep ℓ).IsSemisimpleRepresentation := hS ℚ A ℓ
  have h2 := GlueI3.isSemisimpleRepresentation_baseChange (PadicAlgCl ℓ) (A.galRep ℓ) h1
  exact GlueI3.isSemisimple_of_surjective _ _ h2 (quotMap ℓ A θ emb)
    (quotMap_surjective ℓ A θ emb) (fun σ x => quotMap_equivariant ℓ A θ emb σ x)

/-- The same, in the form `GlueC10` consumes. -/
theorem rhoF_isSemisimpleModule (hS : FaltingsSemisimple) (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) (rhoF ℓ A θ emb).asModule :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
    (rhoF_semisimple ℓ A θ emb hS hT)

end SS

/-! ## §3. Continuity -/

section Cont

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

/-- For every `x ∈ V_ℓ(A) ⊗ ℚ̄_ℓ` and every linear form `c` on `(ι-eigenfunctionals)^∨`,
`σ ↦ c(ρ_{f,ι}(σ) (quotMap x))` is continuous. -/
theorem continuous_coord (hT : TateModuleFree)
    (c : Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) →ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ)
    (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    Continuous fun σ : GQ => c (rhoF ℓ A θ emb σ (quotMap ℓ A θ emb x)) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hρ : ∀ v : A.V ℓ, Continuous fun σ : GQ => A.galRep ℓ σ v := by
    intro v
    have h1 : Continuous fun σ : GQ => (σ, v) := continuous_id.prodMk continuous_const
    exact ((continuous_galRep_of_tateModuleFree hT A ℓ hℓ).1.comp h1).congr fun σ => rfl
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    have hL : Continuous ((c.restrictScalars ℚ_[ℓ]) ∘ₗ ev ℓ A θ emb) :=
      IsModuleTopology.continuous_of_linearMap _
    have : (fun σ : GQ => c (rhoF ℓ A θ emb σ (quotMap ℓ A θ emb (e ⊗ₜ v)))) =
        fun σ => e * ((c.restrictScalars ℚ_[ℓ]) ∘ₗ ev ℓ A θ emb) (A.galRep ℓ σ v) := by
      funext σ
      simp only [quotMap, LinearMap.liftBaseChange_tmul, map_smul, rhoF_ev, smul_eq_mul,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [this]
    exact continuous_const.mul (hL.comp (hρ v))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

/-- **Continuity of `ρ_{f,ι}` (GLUE, proved from I3.M0).** In any finite basis `b` of the
representation space, `σ ↦ [ρ_{f,ι}(σ)]_b` is continuous (Krull topology on `G_ℚ`, the
spectral-norm topology on `ℚ̄_ℓ`). -/
theorem rhoF_continuous (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))) :
    Continuous fun σ : GQ => LinearMap.toMatrix b b (rhoF ℓ A θ emb σ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  obtain ⟨x, hx⟩ := quotMap_surjective ℓ A θ emb (b j)
  refine (continuous_coord ℓ A θ emb hT (b.coord i) x).congr fun σ => ?_
  simp only [LinearMap.toMatrix_apply, Module.Basis.coord_apply, hx]

end Cont

/-! ## §4. Density of arithmetic Frobenius elements (leaf T18) -/

/-- **L18 = T18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. Copied verbatim from
`HSyn.FrobeniusDense` of `scratch/h-decomposition/Leaves.lean`. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- Two continuous functions on `G_ℚ` with Hausdorff values that agree at every arithmetic
Frobenius (`PkgI4.IsArithFrob`) above every prime outside `S` are equal (GLUE, proved from T18). -/
theorem eq_of_eq_on_arithFrob (hD : FrobeniusDense) {X : Type*} [TopologicalSpace X] [T2Space X]
    (S : Finset ℕ) (f₁ f₂ : GQ → X) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → f₁ τ = f₂ τ) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  have hU : IsOpen (E.fixingSubgroup : Set GQ) := IntermediateField.fixingSubgroup_isOpen E
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := hD E.fixingSubgroup hU g S
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    have := E.fixingSubgroup.inv_mem hU'
    simpa using this
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_ofPred_eq] at this
  exact this (hfr p hp hpS v τ hv hτ)

/-! ## §5. Brauer–Nesbitt (leaf T19) with arithmetic Frobenius traces -/

section BN

variable {k V W ι κ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Continuous representations with equal traces at arithmetic Frobenius outside `S` have equal
traces everywhere (GLUE, proved from T18). -/
theorem trace_eq_of_arithFrob (hD : FrobeniusDense) (S : Finset ℕ)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k GQ V) (σ : Representation k GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → LinearMap.trace k V (ρ τ) = LinearMap.trace k W (σ τ)) :
    ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g) :=
  congrFun (eq_of_eq_on_arithFrob hD S _ _ (GlueC10.continuous_trace bV ρ hρc)
    (GlueC10.continuous_trace bW σ hσc) htr)

/-- **C10-type comparison with `IsArithFrob` (GLUE, proved from T18 and T19).** -/
theorem iso_of_arithFrob [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense) (S : Finset ℕ)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k GQ V) (σ : Representation k GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k GQ) σ.asModule)
    (htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → LinearMap.trace k V (ρ τ) = LinearMap.trace k W (σ τ)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k GQ] σ.asModule) :=
  hBN k GQ V W ρ σ hρ hσ (trace_eq_of_arithFrob hD S bV bW ρ σ hρc hσc htr)

end BN

/-! ## §6. C9 -/

section C9

/-- The core of C9 for a fixed `A`, `θ`, `ι` (GLUE, proved). -/
theorem c9_core (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (N : ℕ) (hN : 0 < N) {F : Type} [Field F] (a : ℕ → F)
    (A : AbVar ℚ) (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    (h2 : Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2)
    (hfr : ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
      LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb (a p))
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p → LinearMap.trace (PadicAlgCl ℓ) W (r τ) = emb (a p)) :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ emb g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ] (rhoF ℓ A θ emb).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p)) := by
  have hfd : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hFrob : ∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p) := by
    intro g p hp hpN hg
    rw [trace_rhoF ℓ A θ emb h2]
    exact hfr p hp hpN g hg
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  have htr : ∀ p, p.Prime → p ∉ S ∪ (N * ℓ).primeFactors → ∀ (v : ValuationSubring Qbar)
      (τ : GQ), LiesOver v p → IsArithFrob τ v p → LinearMap.trace (PadicAlgCl ℓ) W (r τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb τ) := by
    intro p hp hpS v τ hv hτ
    have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpN : ¬ p ∣ N * ℓ := fun h =>
      hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩))
    rw [hatt p hp hpS1 hpN v τ hv hτ, hFrob τ p hp hpN (isFrobAt_of_isArithFrob τ v p hp hv hτ)]
  have hcont : ∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
      (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))),
      Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ emb g) :=
    fun b => rhoF_continuous ℓ A θ emb hT b
  let bV := Module.finBasis (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))
  refine ⟨rhoF_semisimple ℓ A θ emb hS hT, hcont, ?_, ?_, hFrob⟩
  · exact iso_of_arithFrob hBN hD _ bW bV r _ hrc (hcont bV) hr
      (rhoF_isSemisimpleModule ℓ A θ emb hS hT) htr
  · exact trace_eq_of_arithFrob hD _ bW bV r _ hrc (hcont bV) htr

/-- **C9 (GLUE, proved from R16, Faltings' Satz 3, I3.M0, T18 and T19).** Let `f` be a newform of
weight 2, level `N` and nebentypus `χ`, `J` a `J₁(N)`, `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`. Let `r` be a
continuous semisimple finite-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` whose arithmetic
Frobenius traces outside a finite set `S` are those of `f` (through `ιC`, `ιL`). Then for R16's
`A_f` and `ρ_{f,ι} = rhoF` with `ι = ιL ∘ ιC⁻¹` (`embOf`):
(i) `ρ_{f,ι}` is 2-dimensional, semisimple and continuous;
(ii) `r ≅ ρ_{f,ι}` (Brauer–Nesbitt);
(iii) `tr r(g) = tr ρ_{f,ι}(g)` for every `g ∈ G_ℚ` (needs T18 and continuity only), which is the
hypothesis `h₅` of `GlueC10.c10`;
(iv) `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `GlueC10.IsFrobAt g p`, `p ∤ Nℓ`: the hypothesis `hρ₅`. -/
theorem c9 (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ)
    (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∃ α : Qbar, ιC α = coeff f p ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        LinearMap.trace (PadicAlgCl ℓ) W (r τ) = ιL α) :
    ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
      (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
      Module.finrank (PadicAlgCl ℓ)
        (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f)))) = 2 ∧
      (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f))))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
        (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
          embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) := by
  obtain ⟨hfin, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  obtain ⟨h2, hfr⟩ := hrest ℓ (embOf ℓ ιC ιL (coeffField f))
  refine ⟨hfin, A, π, θ, hπ, finrank_rhoF ℓ A θ _ h2,
    c9_core ℓ hS hT hBN hD N hN (fun p => ⟨coeff f p, coeff_mem_coeffField f p⟩) A θ _ h2
      (fun p hp hpN σ hσ => (hfr p hp hpN σ hσ).1 _ rfl) S bW r hrc hr ?_⟩
  intro p hp hpS hpN v τ hv hτ
  obtain ⟨α, hα, hrα⟩ := hatt p hp hpS hpN
  rw [hrα v τ hv hτ]
  exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm

end C9

end C9Rhof

/-! ## §7. Leaves R14, T24, T25 and Pan's trace form, copied verbatim from
`scratch/h-decomposition/Leaves.lean` (namespace `PkgI4`, §2-§3 there) -/

namespace PkgI4

open scoped MatrixGroups ModularForm

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **I4-L1. Galois representations of eigenforms** (Eichler–Shimura and Shimura 1971 Thm 7.14
for `k = 2`; Deligne 1971 for `k ≥ 2`; Deligne–Serre 1974 Thm 6.1 for `k = 1`; theorem numbers
UNVERIFIED). Consequence form (the published statements also give the determinant
`ε_g χ^{k−1}`). Same as hdec-faithful L27(a). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **I4-L4. Twisting an eigenform** (Shimura 1971 Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978)
Prop. 3.1; locators UNVERIFIED). Consequence form. Same as hdec-faithful L28(a). -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p

/-- **I4-L5. Newform attached to an eigensystem** (Li, Math. Ann. 212 (1975), Thm 5 (strong
multiplicity one) with the decomposition `S_k = S_k^new ⊕ S_k^old`; Miyake Thm 4.6.19; locators
UNVERIFIED). Every normalized eigenform of level `M` has the Hecke eigenvalues away from `M` of a
newform of level dividing `M`. Consequence form. -/
def NewformOfEigenform : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p

/-- `ρ` is attached to `g` **up to the twist** `ψ`, outside a finite set `S`: Pan's conclusion
"comes from a cuspidal eigenform up to twist", in trace form (see `PanFor`). -/
def GaloisRep.AttachedUpToTwist (ρ : GaloisRep ℓ 2) (ψ : GaloisChar ℓ) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (g : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl ℓ) * ιL α

end PkgI4

namespace C9Rhof

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves

/-! ## §8. `GaloisRep` (matrix form) as a `Representation` -/

section Bridge

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- A `GaloisRep` as a `Representation` on `ℚ̄_ℓ^n`. -/
def toRep (ρ : GaloisRep ℓ n) : Representation (PadicAlgCl ℓ) GQ (Fin n → PadicAlgCl ℓ) where
  toFun σ := Matrix.toLin' (ρ.mat σ)
  map_one' := by
    simp only [GaloisRep.mat, map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' σ τ := by
    simp only [GaloisRep.mat, map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl

theorem toRep_apply (ρ : GaloisRep ℓ n) (σ : GQ) : toRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_toRep (ρ : GaloisRep ℓ n) (σ : GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (toRep ρ σ) = ρ.mat σ := by
  rw [toRep_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem toRep_continuous (ρ : GaloisRep ℓ n) :
    Continuous fun σ => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (toRep ρ σ) := by
  simp_rw [toMatrix_toRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem trace_toRep (ρ : GaloisRep ℓ n) (σ : GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (toRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_toRep]

/-- Invariant complements give a semisimple representation. -/
theorem semisimple_of_complements {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V)
    (h : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule k V, IsCompl W W' ∧ ∀ g, ∀ v ∈ W', ρ g v ∈ W') :
    ρ.IsSemisimpleRepresentation := by
  refine ⟨fun a => ?_⟩
  obtain ⟨W', hc, hW'⟩ := h a.toSubmodule (fun g v hv => a.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ⟨?_, ?_⟩⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact hc.inf_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact hc.sup_eq_top

/-- `GaloisRep.IsSemisimple` gives a semisimple `MonoidAlgebra`-module. -/
theorem toRep_semisimple (ρ : GaloisRep ℓ n) (h : ρ.IsSemisimple) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) (toRep ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  apply semisimple_of_complements
  intro W hW
  obtain ⟨W', hc, hW'⟩ := h W (fun σ => Submodule.map_le_iff_le_comap.mpr
    (fun v hv => hW σ v hv))
  exact ⟨W', hc, fun σ v hv => hW' σ (Submodule.mem_map_of_mem hv)⟩

/-- **Irreducible (Burnside form) implies semisimple (GLUE, proved).** If the image of `ρ` spans
`M_n(ℚ̄_ℓ)` as an algebra, the only invariant subspaces are `⊥` and `⊤`. -/
theorem isSemisimple_of_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) :
    ρ.IsSemisimple := by
  intro W hW
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | ∀ v ∈ W, M.mulVec v ∈ W}
      mul_mem' := fun {M N} hM hN v hv => by
        rw [← Matrix.mulVec_mulVec]; exact hM _ (hN v hv)
      add_mem' := fun {M N} hM hN v hv => by
        rw [Matrix.add_mulVec]; exact W.add_mem (hM v hv) (hN v hv)
      algebraMap_mem' := fun c v hv => by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem c hv }
  have hrange : Set.range ρ.mat ⊆ S := by
    rintro _ ⟨σ, rfl⟩ v hv
    exact hW σ ⟨v, hv, rfl⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ), ∀ v ∈ W, M.mulVec v ∈ W := by
    intro M
    have : M ∈ S := by
      have h1 := Algebra.adjoin_le hrange
      rw [h] at h1
      exact h1 Algebra.mem_top
    exact this
  by_cases hbot : W = ⊥
  · refine ⟨⊤, hbot ▸ isCompl_bot_top, fun σ => le_top⟩
  · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw0 (funext hc)
    have htop : W = ⊤ := by
      rw [eq_top_iff]
      intro u _
      let M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
        Matrix.of fun a b => if b = i then u a * (w i)⁻¹ else 0
      have hM : M.mulVec w = u := by
        funext a
        simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        field_simp
      rw [← hM]
      exact hall M w hwW
    refine ⟨⊥, htop ▸ isCompl_top_bot, fun σ => ?_⟩
    rw [Submodule.map_bot]

end Bridge

/-! ## §9. C9 against R14 and against C8's `r₅` -/

section Apps

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **C9 against R14 (GLUE, proved from R14, R16, Faltings' Satz 3, I3.M0, T18, T19).** For a
newform `f` of weight 2 and level `N`, a `J₁(N)` `J` and embeddings `ιC`, `ιL`: R14's semisimple
`ρ` attached to `f` is isomorphic to R16's `ρ_{f,ι}` (`ι = ιL ∘ ιC⁻¹`), and they have the same
trace at every `g ∈ G_ℚ`. -/
theorem c9_R14 (hR14 : PkgI4.EigenformRepExists) (hR16 : R16_EichlerShimuraJ1')
    (hS : FaltingsSemisimple) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep ρ).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        ∀ g : GQ, (ρ.mat g).trace =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) := by
  obtain ⟨ρ, hss, hatt⟩ := hR14 ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfin, A, π, θ, hπ, -, -, -, hiso, htr, -⟩ := c9 ℓ hR16 hS hT hBN hD N hN χ f hf J hJ
    ιC ιL (N * ℓ).primeFactors (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep ρ)
    (toRep_continuous ρ) (toRep_semisimple ρ hss) (by
      intro p hp hpS _
      have hpN : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩)
      obtain ⟨-, α, hα, h⟩ := hatt p hp hpN
      exact ⟨α, hα, fun v τ hv hτ => by rw [trace_toRep]; exact h v τ hv hτ⟩)
  exact ⟨ρ, hss, hatt, hfin, A, π, θ, hπ, hiso, fun g => by rw [← trace_toRep]; exact htr g⟩

/-- **C9 for C8's `r₅` (GLUE, proved from T24 EigenformTwist, T25 NewformOfEigenform, R16,
Faltings' Satz 3, I3.M0, T18, T19).** C8's output: a semisimple `r : G_ℚ → GL₂(ℚ̄_ℓ)` attached up
to the twist `ψ` to a normalized eigenform `g` of weight 2 and level `M` (Pan's trace form,
`PkgI4.GaloisRep.AttachedUpToTwist`), where `ψ` is (at arithmetic Frobenius outside `S`) the
Dirichlet character `ψD` mod `m` through `ιC`, `ιL` (C8 steps 1-4: determinant argument and
Kronecker–Weber). Then there is a newform `f` of weight 2 and level `N ∣ M m²` such that for every
`J₁(N)`: `r ≅ ρ_{f,ι}` (`ι = ιL ∘ ιC⁻¹`), their traces agree on all of `G_ℚ` (`h₅` of
`GlueC10.c10`), and `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `IsFrobAt g p`, `p ∤ Nℓ` (`hρ₅`).
The hypothesis `hr` follows from Pan's hypothesis `r.IsIrreducible` by
`isSemisimple_of_isIrreducible`. -/
theorem c9_r5 (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (M : ℕ) (hM : 0 < M) (χg : DirichletCharacter ℂ M) (g : CF M 2)
    (hg : IsNormalizedEigenform g χg) (m : ℕ) (hm : 0 < m) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hrg : r.AttachedUpToTwist ψ ιC ιL g S)
    (hψ : ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ N ∣ M * m ^ 2 ∧
      IsNewform f χ ∧ ∀ J : AbVar ℚ, IsJ1 N J →
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep r).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) _ (toRep r g) =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
        (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
            embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) := by
  obtain ⟨χ', g', hg', hcoef⟩ := hTw M m 2 χg ψD g hM hm hg
  obtain ⟨N, χ, f, hN, hNd, hf, hcf⟩ := hNew (M * m ^ 2) 2 χ' g' (by positivity) hg'
  refine ⟨N, χ, f, hN, hNd, hf, fun J hJ => ?_⟩
  have hMm : M * m ≠ 0 := Nat.mul_ne_zero hM.ne' hm.ne'
  obtain ⟨hfin, A, π, θ, hπ, -, -, -, hiso, htr, hFrob⟩ := c9 ℓ hR16 hS hT hBN hD N hN χ f hf J
    hJ ιC ιL (S ∪ (M * m).primeFactors) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep r)
    (toRep_continuous r) (toRep_semisimple r hr) (by
      intro p hp hpS _
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpMm : ¬ p ∣ M * m := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMm⟩))
      have hpMm2 : ¬ p ∣ M * m ^ 2 := by
        intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
        · exact hpMm (dvd_mul_of_dvd_left h1 _)
        · exact hpMm (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) _)
      obtain ⟨-, α, hα, htrα⟩ := hrg p hp hpS1
      obtain ⟨β, hβ, hψp⟩ := hψ p hp hpS1
      refine ⟨β * α, ?_, fun v τ hv hτ => ?_⟩
      · rw [map_mul, hβ, hα, hcf p hp hpMm2, hcoef p hp hpMm]
      · rw [trace_toRep, htrα v τ hv hτ, hψp v τ hv hτ, map_mul])
  exact ⟨hfin, A, π, θ, hπ, hiso, htr, hFrob⟩

/-- **C9's outputs fit `GlueC10.c10` (GLUE, proved).** With `ρ₅ := ρ_{f,ι}` (`rhoF`), C9's
trace identity `tr r₅ = tr ρ_{f,ι}` (from `c9`, `c9_r5`) is `h₅`, and its Frobenius clause is
`hρ₅` for every `S` containing the primes of `Nℓ`; the remaining inputs of `c10` (the
abelian-variety traces `hr₅`, `hr₃` and the data at 3) are passed through. -/
theorem c10_via_c9 (hC : GlueC10.ChebotarevExists) (hBN : GlueC10.BrauerNesbittChar0)
    (N : ℕ) {C : Type} [Field C] (c a : ℕ → C) (A : AbVar ℚ) (θ : C →+* A.End0)
    (emb : C →+* PadicAlgCl ℓ) (S : Finset ℕ) (hSN : ∀ p, p.Prime → p ∣ N * ℓ → p ∈ S)
    {V₅ : Type} [AddCommGroup V₅] [Module (PadicAlgCl ℓ) V₅]
    (r₅ : Representation (PadicAlgCl ℓ) GQ V₅)
    (h₅ : ∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) V₅ (r₅ g) =
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g))
    (hFrob : ∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) V₅ (r₅ g) = emb (c p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  GlueC10.c10 hC hBN S C c a (PadicAlgCl ℓ) V₅ _ emb r₅ (rhoF ℓ A θ emb)
    (fun g _ _ _ _ => h₅ g) hr₅
    (fun g p hp hpS hg => hFrob g p hp (fun h => hpS (hSN p hp h)) hg)
    k V W ι κ ι₃ bV bW r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end Apps

end C9Rhof
end
end C9Copy

/-! Copied from scratch/e1-sub/E1Sub.lean (compiled there), lines 4-870. -/
section E1Copy

/-! # e1-sub, part 1: `VSurjOfSurjective` (proved) and `ρ_{f,ι}` as a subrepresentation of
`V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` over `G_ℚ`.

* §1 `vSurjOfSurjective`: the glue target `LeafModCurves.VSurjOfSurjective` holds, from the I3
  leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree` (Faltings 1983 Satz 3, Satz 4 /
  Kor. 1; Mumford §4) and Mathlib's `ext_of_isDominant_of_isSeparated`. (No Poincaré
  reducibility is needed.)
* §2 `exists_subrep_equiv_of_surjective`: a surjective equivariant map out of a semisimple
  representation has an equivariant section onto a subrepresentation.
* §3 `rhoF_subrep_J`: R16's `ρ_{f,ι}` (`LeafModCurves.rhoF`) is isomorphic to a
  subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ`, for every `J₁(N)` `J`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open scoped TensorProduct

namespace E1Sub

/-! ## §1. A surjective homomorphism is surjective on `V_ℓ` -/

section VSurj

variable {K : Type} [Field K]

/-- Precomposition with `π : J → A`, `Hom(A, B) → Hom(J, B)`. -/
def precomp {J A B : AbVar K} (π : Hom J A) : Hom A B →ₗ[ℤ] Hom J B :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => Hom.mk' (π.hom ≫ f.hom)
      map_zero' := Hom.ext' (by simp)
      map_add' := fun f g => Hom.ext' (by simp [MonObj.comp_mul]) }

@[simp] lemma precomp_hom {J A B : AbVar K} (π : Hom J A) (f : Hom A B) :
    (precomp π f).hom = π.hom ≫ f.hom := rfl

lemma isReduced_left (A : AbVar K) : IsReduced A.X.left :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.X.hom

/-- Precomposition with a surjective homomorphism is injective (`A` is reduced, `B` separated). -/
lemma precomp_injective {J A B : AbVar K} (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Injective (precomp (B := B) π) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h1 : π.hom ≫ f.hom = π.hom ≫ (1 : A.X ⟶ B.X) := by
    have := congrArg Hom.hom hf
    simp only [precomp_hom, Hom.hom_zero] at this
    rw [this, MonObj.comp_one]
  have := isReduced_left A
  apply Hom.ext'
  rw [Hom.hom_zero]
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated B.X.hom (by simp) π.hom.left
    (by rw [← Over.comp_left, ← Over.comp_left, h1])

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ(π)` over any field. -/
def homVK {J A : AbVar K} (π : Hom J A) : J.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ :=
  (homT (ℓ := ℓ) π).baseChange ℚ_[ℓ]

lemma homT_comp {J A B : AbVar K} (π : Hom J A) (f : Hom A B) (x : J.T ℓ) :
    homT (ℓ := ℓ) (precomp π f) x = homT f (homT π x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ π.hom ≫ f.hom) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ π.hom) ≫ f.hom)
  rw [Category.assoc]

lemma tateHomZl_precomp {J A B : AbVar K} (π : Hom J A) (z : ℤ_[ℓ] ⊗[ℤ] Hom A B) (x : J.T ℓ) :
    tateHomZl ℓ J B ((precomp π).lTensor ℤ_[ℓ] z) x = tateHomZl ℓ A B z (homT π x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    simp only [LinearMap.lTensor_tmul]
    change (a • tateHom ℓ J B (precomp π f)) x = (a • tateHom ℓ A B f) (homT π x)
    simp only [LinearMap.smul_apply]
    exact congrArg (a • ·) (homT_comp ℓ π f x)
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]

lemma homVK_galRep {J A : AbVar K} (π : Hom J A) (σ : Field.absoluteGaloisGroup K) :
    homVK ℓ π ∘ₗ J.galRep ℓ σ = A.galRep ℓ σ ∘ₗ homVK ℓ π := by
  have h1 : homT (ℓ := ℓ) π ∘ₗ J.galT σ = A.galT σ ∘ₗ homT π :=
    LinearMap.ext fun t => homT_galT π σ t
  change (homT π).baseChange ℚ_[ℓ] ∘ₗ (J.galT σ).baseChange ℚ_[ℓ] =
    (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (homT π).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- Complement of a subrepresentation, as `IsCompl` of submodules. -/
lemma isCompl_toSubmodule {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {W W' : Subrepresentation ρ} (h : IsCompl W W') :
    IsCompl W.toSubmodule W'.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule h.inf_eq_bot
    simp only [Subrepresentation.toSubmodule_inf] at this
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule h.sup_eq_top
    simp only [Subrepresentation.toSubmodule_sup] at this
    exact this

/-- **`VSurjOfSurjective` over a number field (GLUE, proved from Faltings' Satz 3 and Satz 4 and
`TateModuleFree`).** If `π : J → A` is a homomorphism of abelian varieties over a number field
whose underlying morphism of schemes is surjective, then `V_ℓ(π) : V_ℓ(J) → V_ℓ(A)` is surjective.

Proof: the image `R` is `G_K`-stable; by semisimplicity it has an invariant complement `R'`. The
projection `p` onto `R'` is equivariant and kills `R`. Clearing denominators, `s • p` comes from an
equivariant `h : T_ℓ A → T_ℓ A`, which by Faltings is `tateHomZl z`, `z ∈ ℤ_ℓ ⊗ End(A)`. Since
`h ∘ T_ℓ(π) = 0`, injectivity of `tateHomZl` on `Hom(J, A)` and flatness of `ℤ_ℓ` over `ℤ` give
`z = 0` (precomposition with `π` is injective because `A` is reduced and `π` is dominant).
So `p = 0` and `R' = 0`. -/
theorem homVK_surjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    [NumberField K] (J A : AbVar K) (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Surjective (homVK ℓ π) := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfreeA, hfinA, -⟩ := hT K A ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  -- the image as a subrepresentation
  let R : Subrepresentation (A.galRep ℓ) :=
    { toSubmodule := LinearMap.range (homVK ℓ π)
      apply_mem_toSubmodule := by
        rintro σ _ ⟨w, rfl⟩
        exact ⟨J.galRep ℓ σ w, LinearMap.congr_fun (homVK_galRep ℓ π σ) w⟩ }
  obtain ⟨R', hR'⟩ := (hS K A ℓ).exists_isCompl R
  have hc := isCompl_toSubmodule hR'.symm
  -- if `R' = 0` we are done
  suffices hR'0 : R'.toSubmodule = ⊥ by
    have htop : R.toSubmodule = ⊤ := by
      have := hc.symm.sup_eq_top
      rwa [hR'0, sup_bot_eq] at this
    intro v
    have : v ∈ R.toSubmodule := htop ▸ Submodule.mem_top
    exact this
  by_contra hne
  -- the projection onto `R'` along `R`
  set p : A.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ := R'.toSubmodule.projection R.toSubmodule hc with hpdef
  have hpeq : ∀ σ, p ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ p :=
    GlueI3.projection_comm R' R hc
  have hpR : ∀ w, p (homVK ℓ π w) = 0 := fun w =>
    Submodule.projection_apply_of_mem_right hc ⟨w, rfl⟩
  obtain ⟨r, hrR', hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpr : p r = r := Submodule.projection_apply_of_mem_left hc hrR'
  -- lattice clearing (as in `PkgI3.exists_hom_ne_zero_of_equivariant`)
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιJ : J.T ℓ →ₗ[ℤ_[ℓ]] J.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (J.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιA := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιA ((p.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hιA : Function.Injective ιA := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιA).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hsp : ∀ x, ιA (h x) = (s : ℤ_[ℓ]) • p (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιA
    rw [hsp, hιAσ, hιAσ, hsp]
    have := congrArg (fun g => g (ιA x)) (hpeq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  -- `h ∘ T_ℓ(π) = 0`
  have hhπ : ∀ x, h (homT π x) = 0 := fun x => by
    apply hιA
    rw [hsp, map_zero]
    have : ιA (homT π x) = homVK ℓ π (ιJ x) := by
      simp [ιA, ιJ, homVK, LinearMap.baseChange_tmul]
    rw [this, hpR, smul_zero]
  -- Faltings: `h = tateHomZl z`
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A A) := by
    rw [(hF K A A ℓ).2]; exact hheq
  have hz0 : (precomp π).lTensor ℤ_[ℓ] z = 0 := by
    apply (hF K J A ℓ).1
    rw [map_zero]
    apply LinearMap.ext; intro x
    rw [tateHomZl_precomp, hz, hhπ, LinearMap.zero_apply]
  have hinj : Function.Injective ((precomp (B := A) π).lTensor ℤ_[ℓ]) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (precomp_injective π hπ)
  have hz' : z = 0 := hinj (by rw [hz0, map_zero])
  have hh0 : h = 0 := by rw [← hz, hz', map_zero]
  -- hence `p = 0`, contradicting `p r = r ≠ 0`
  have hpι : ∀ x, p (ιA x) = 0 := fun x => by
    have h1 : (s : ℤ_[ℓ]) • p (ιA x) = 0 := by rw [← hsp, hh0]; simp
    rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ])] at h1
    exact (smul_eq_zero.mp h1).resolve_left (by
      simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0)
  have hp0 : ∀ v, p v = 0 := fun v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q x =>
      have : (q ⊗ₜ[ℤ_[ℓ]] x : A.V ℓ) = q • ιA x := by simp [ιA, TensorProduct.smul_tmul']
      rw [this, map_smul, hpι, smul_zero]
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
  exact hr0 (by rw [← hpr, hp0])

end VSurj

/-- **`LeafModCurves.VSurjOfSurjective` (the glue target of leaf-modcurves), proved.** -/
theorem vSurjOfSurjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree) :
    LeafModCurves.VSurjOfSurjective := by
  intro J A π ℓ _ hπ
  exact homVK_surjective ℓ hS hF hT J A π hπ

/-! ## §2. Equivariant sections out of a semisimple representation -/

section Section

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- A surjective equivariant map `q : V → W` out of a semisimple representation restricts to an
equivariant isomorphism from a subrepresentation of `V` onto `W` (an invariant complement of
`ker q`). -/
theorem exists_subrep_equiv_of_surjective (ρ : Representation k G V) (σ : Representation k G W)
    (hss : ρ.IsSemisimpleRepresentation) (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (hqeq : ∀ g v, q (ρ g v) = σ g (q v)) :
    ∃ (U : Subrepresentation ρ) (e : U.toSubmodule ≃ₗ[k] W),
      ∀ g (u : U.toSubmodule), e ⟨ρ g u, U.apply_mem_toSubmodule g u.2⟩ = σ g (e u) := by
  let Kr : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker q
      apply_mem_toSubmodule := fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hqeq, hv, map_zero] }
  obtain ⟨U, hU⟩ := hss.exists_isCompl Kr
  have hc : IsCompl Kr.toSubmodule U.toSubmodule := isCompl_toSubmodule hU
  have hbij : Function.Bijective (q ∘ₗ U.toSubmodule.subtype) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have hK : (u : V) ∈ Kr.toSubmodule := hu
      exact Subtype.ext ((Submodule.disjoint_def.mp hc.disjoint) u hK u.2)
    · intro w
      obtain ⟨v, rfl⟩ := hq w
      have hv : v ∈ Kr.toSubmodule ⊔ U.toSubmodule := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      have ha' : q a = 0 := ha
      exact ⟨⟨b, hb⟩, by simp [ha']⟩
  refine ⟨U, LinearEquiv.ofBijective _ hbij, fun g u => ?_⟩
  simp [LinearEquiv.ofBijective_apply, hqeq]

end Section

/-- Base change of a surjective linear map is surjective. -/
lemma baseChange_surjective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (E : Type*) [CommRing E] [Algebra R E] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : Function.Surjective (f.baseChange E) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul e n =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨e ⊗ₜ m, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, map_add _ _ _⟩

/-! ## §3. `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (over `G_ℚ`) -/

section RhoSub

open LeafModCurves
open PkgI4 (GQ)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Evaluation of the `ι`-eigenfunctionals: `V_ℓ(A) → (eigenFun)^∨`, `v ↦ (φ ↦ φ v)`. -/
def evalEig (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    A.V ℓ →ₗ[ℚ_[ℓ]] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) where
  toFun v :=
    { toFun := fun φ => (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => rfl }
  map_add' v w := by ext φ; simp
  map_smul' c v := by ext φ; simp

/-- Its `ℚ̄_ℓ`-linear extension `V_ℓ(A) ⊗ ℚ̄_ℓ → (eigenFun)^∨`. -/
def evalEigE (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) →ₗ[PadicAlgCl ℓ]
      Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
  (evalEig ℓ A θ emb).liftBaseChange (PadicAlgCl ℓ)

theorem evalEigE_equivariant (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (σ : GQ) (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    evalEigE ℓ A θ emb (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ x) =
      rhoF ℓ A θ emb σ (evalEigE ℓ A θ emb x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e v =>
    change evalEigE ℓ A θ emb ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (e ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul]
    simp only [evalEigE, LinearMap.liftBaseChange_tmul, map_smul]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

theorem evalEigE_surjective (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    Function.Surjective (evalEigE ℓ A θ emb) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  set w := (Module.evalEquiv (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)).symm f
  have hfw : ∀ g, f g = g w := fun g => by
    have : f = Module.evalEquiv (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) w := by simp [w]
    rw [this]; rfl
  have hv : ∀ v, (w : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v = 0 := fun v => by
    have hx : evalEigE ℓ A θ emb (1 ⊗ₜ v) ∈ LinearMap.range (evalEigE ℓ A θ emb) := ⟨_, rfl⟩
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [hf, Submodule.mem_bot, hfw] at this
    simp only [evalEigE, LinearMap.liftBaseChange_tmul, one_smul] at this
    exact this
  have hw0 : w = 0 := Subtype.ext (LinearMap.ext hv)
  apply hf0
  ext g
  rw [hfw, hw0, map_zero]; rfl

/-- **`ρ_{f,ι}` as a subrepresentation (GLUE, proved).** If `V_ℓ(π) : V_ℓ(J) → V_ℓ(A)` is
surjective, the representation `rhoF ℓ A θ ι` of `G_ℚ` on `(eigenFun)^∨` is equivariantly
isomorphic to a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (Faltings' semisimplicity of `V_ℓ(J)`,
kept under extension of scalars by `GlueI3.semisimpleBaseChange`). -/
theorem rhoF_subrep_of_surj (hS : FaltingsSemisimple) (hT : TateModuleFree) (J A : AbVar ℚ)
    (π : Hom J A) (hπ : Function.Surjective (homV ℓ π)) {F : Type} [Field F]
    (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ)))
      (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
      ∀ g (u : U.toSubmodule),
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ =
          rhoF ℓ A θ emb g (e u) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT ℚ J ℓ hℓ
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hss := GlueI3.semisimpleBaseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ (J.galRep ℓ) (hS ℚ J ℓ)
  refine exists_subrep_equiv_of_surjective _ (rhoF ℓ A θ emb) hss
    (evalEigE ℓ A θ emb ∘ₗ (homV ℓ π).baseChange (PadicAlgCl ℓ))
    ((evalEigE_surjective ℓ A θ emb).comp (baseChange_surjective _ _ hπ)) ?_
  intro g v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [← evalEigE_equivariant]
  congr 1
  change ((homV ℓ π).baseChange _ ∘ₗ (J.galRep ℓ g).baseChange _) v =
    ((A.galRep ℓ g).baseChange _ ∘ₗ (homV ℓ π).baseChange _) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, homV_galRep]

/-- **`ρ_{f,ι}` is semisimple (GLUE, proved)**: it is an equivariant quotient of the semisimple
`V_ℓ(J) ⊗ ℚ̄_ℓ` (a C9 input). -/
theorem rhoF_semisimple_of_surj (hS : FaltingsSemisimple) (hT : TateModuleFree) (J A : AbVar ℚ)
    (π : Hom J A) (hπ : Function.Surjective (homV ℓ π)) {F : Type} [Field F]
    (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT ℚ J ℓ hℓ
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hss := GlueI3.semisimpleBaseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ (J.galRep ℓ) (hS ℚ J ℓ)
  refine GlueI3.isSemisimple_of_surjective _ (rhoF ℓ A θ emb) hss
    (evalEigE ℓ A θ emb ∘ₗ (homV ℓ π).baseChange (PadicAlgCl ℓ))
    ((evalEigE_surjective ℓ A θ emb).comp (baseChange_surjective _ _ hπ)) ?_
  intro g v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [← evalEigE_equivariant]
  congr 1
  change ((homV ℓ π).baseChange _ ∘ₗ (J.galRep ℓ g).baseChange _) v =
    ((A.galRep ℓ g).baseChange _ ∘ₗ (homV ℓ π).baseChange _) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, homV_galRep]

/-- **G13 as a subrepresentation (GLUE, proved from R16 and the I3 leaves).** For a newform `f`
of level `N` and any `J₁(N)` `J`: Shimura's `A_f`, `π : J ↠ A_f`, `θ : K_f → End⁰(A_f)` such that
for every prime `ℓ` and embedding `ι : K_f → ℚ̄_ℓ`, R16's `ρ_{f,ι} = rhoF ℓ A_f θ ι` is
2-dimensional, has Frobenius traces `ι(a_p(f))` at `p ∤ Nℓ`, and is equivariantly isomorphic to a
subrepresentation `U` of `V_ℓ(J) ⊗ ℚ̄_ℓ` (as `G_ℚ`-representations). This replaces the quotient
of `LeafModCurves.g13_constituent` by a sub, and discharges its hypothesis `VSurjOfSurjective`. -/
theorem rhoF_subrep_J (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) = emb a) ∧
        ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ)))
          (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
          ∀ g (u : U.toSubmodule),
            e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) g u,
                U.apply_mem_toSubmodule g u.2⟩ = rhoF ℓ A θ emb g (e u) := by
  obtain ⟨-, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  have : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by omega)
  have hVs := vSurjOfSurjective hS hF hT J A π ℓ hπ
  refine ⟨finrank_rhoF ℓ A θ emb h2, rhoF_semisimple_of_surj ℓ hS hT J A π hVs θ emb,
    fun p hp hpN σ hσ a ha => ?_,
    rhoF_subrep_of_surj ℓ hS hT J A π (vSurjOfSurjective hS hF hT J A π ℓ hπ) θ emb⟩
  rw [trace_rhoF ℓ A θ emb h2]
  exact (hfr p hp hpN σ hσ).1 a ha

/-- `LeafModCurves.g13_constituent` with its glue hypothesis `VSurjOfSurjective` discharged. -/
theorem g13_constituent' (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ emb : coeffField f →+* PadicAlgCl ℓ, ∃ W : Submodule (PadicAlgCl ℓ)
        (J.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ), Module.finrank (PadicAlgCl ℓ) W = 2 ∧
      ∃ hW : ∀ σ : GQ, ∀ φ ∈ W, dualAct ℓ J σ φ ∈ W,
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        (∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) W ((dualAct ℓ J σ).restrict (hW σ)) = emb a) ∧
        (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
            LinearMap.det ((dualAct ℓ J σ).restrict (hW σ)) = emb c * p) :=
  g13_constituent hR16 (vSurjOfSurjective hS hF hT) N hN χ f hf J hJ ℓ

end RhoSub

end E1Sub

/-! ## §4. `V_ℓ` under base change -/

section BCsec
open scoped CategoryTheory.Obj

namespace E1Sub

section BaseChange

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- `Spec M₂ → Spec M₁` over `K`, for a `K`-algebra map `M₁ → M₂`. -/
def specHom {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
    (i : M₁ →ₐ[K] M₂) : ptObj (K := K) M₂ ⟶ ptObj (K := K) M₁ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (i : M₁ →+* M₂))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- `Spec M → Spec M ×_{Spec K} Spec L` over `L` (graph of the structure maps). -/
def ptUnit (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    ptObj (K := L) M ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj (ptObj (K := K) M) :=
  Over.homMk (pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap L M))) (by
    simp only [ptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])) (pullback.lift_snd _ _ _)

variable (L) in
/-- Points of `A` with values in an `L`-algebra `M` become points of `A_L`. -/
def bcPt (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    J.Pt M →* (J.baseChange L).Pt M where
  toFun Q := ptUnit M ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q
  map_one' := by
    change ptUnit M ≫ (Over.pullback _).map (1 : ptObj (K := K) M ⟶ J.X) = 1
    rw [Functor.map_one, MonObj.comp_one]
    rfl
  map_mul' Q Q' := by
    change ptUnit M ≫ (Over.pullback _).map (Q * Q') =
      (ptUnit M ≫ (Over.pullback _).map Q) * (ptUnit M ≫ (Over.pullback _).map Q')
    rw [Functor.map_mul, MonObj.comp_mul]
    rfl

lemma bcPt_fst (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (Q : J.Pt M) :
    (bcPt L J M Q).left ≫ pullback.fst _ _ = Q.left := by
  change ((ptUnit (K := K) (L := L) M).left ≫
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q).left) ≫
      pullback.fst _ _ = Q.left
  simp only [ptUnit, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)

lemma bcPt_injective (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] : Function.Injective (bcPt L J M) := by
  intro Q Q' h
  apply Over.OverMorphism.ext
  rw [← bcPt_fst (L := L) J M Q, ← bcPt_fst (L := L) J M Q', h]

/-- Precomposition with `Spec ι`, `A(M₁) → A(M₂)`. -/
def precompPt (J : AbVar K) {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
    (i : M₁ →ₐ[K] M₂) : J.Pt M₁ →* J.Pt M₂ where
  toFun P := specHom i ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

lemma precompPt_injective (J : AbVar K) {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁]
    [Algebra K M₂] (i : M₁ →ₐ[K] M₂) : Function.Injective (precompPt J i) := by
  intro P P' h
  have hd : IsDominant (specHom (K := K) i).left := by
    constructor
    have : Subsingleton (ptObj (K := K) M₁).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum M₁))
    have hne : Nonempty (ptObj (K := K) M₂).left :=
      inferInstanceAs (Nonempty (PrimeSpectrum M₂))
    obtain ⟨x⟩ := hne
    intro y
    rw [Subsingleton.elim y ((specHom (K := K) i).left x)]
    exact subset_closure (Set.mem_range_self x)
  have : IsReduced (ptObj (K := K) M₁).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of M₁)))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated J.X.hom (by simp) (specHom (K := K) i).left
    (by rw [← Over.comp_left, ← Over.comp_left]; exact congrArg CommaMorphism.left h)

end BaseChange

section BC2

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The point map `A(K̄) → A_L(L̄)` along a `K`-embedding `i : K̄ → L̄`. -/
def bcPhi (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.Pt (AlgebraicClosure K) →* (J.baseChange L).Pt (AlgebraicClosure L) :=
  (bcPt L J (AlgebraicClosure L)).comp (precompPt J i)

lemma bcPhi_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcPhi J i) := by
  intro a b h
  exact precompPt_injective J i (bcPt_injective (L := L) J (AlgebraicClosure L) h)

variable (K) in
/-- `τ ∈ Gal(L̄/L)` acting on `Spec L̄` over `K`. -/
def galHomK (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    ptObj (K := K) (AlgebraicClosure L) ⟶ ptObj (K := K) (AlgebraicClosure L) :=
  specHom ((τ.restrictScalars K).toAlgHom)

lemma specHom_galHom (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) :
    specHom i ≫ galHom σ = galHomK K τ ≫ specHom i := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (i : AlgebraicClosure K →+* AlgebraicClosure L)) ≫
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) =
    Spec.map (CommRingCat.ofHom ((τ.restrictScalars K).toAlgHom :
        AlgebraicClosure L →+* AlgebraicClosure L)) ≫
      Spec.map (CommRingCat.ofHom (i : AlgebraicClosure K →+* AlgebraicClosure L))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact h x

lemma galHom_ptUnit (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    galHom τ ≫ ptUnit (K := K) (L := L) (AlgebraicClosure L) =
      ptUnit (AlgebraicClosure L) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (galHomK K τ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.pullback_map_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    erw [pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd]
    erw [pullback.lift_snd]
    change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure L →+* AlgebraicClosure L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) =
        Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact τ.commutes x

/-- **Equivariance of the point map.** For `τ ∈ G_L` and `σ ∈ G_K` with `i ∘ σ = τ ∘ i`. -/
lemma bcPhi_galAct (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (P : J.Pt (AlgebraicClosure K)) :
    bcPhi J i (J.galAct σ P) = (J.baseChange L).galAct τ (bcPhi J i P) := by
  change ptUnit (AlgebraicClosure L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
        (specHom i ≫ galHom σ ≫ P) =
    galHom τ ≫ ptUnit (AlgebraicClosure L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (specHom i ≫ P)
  rw [← Category.assoc (galHom τ), galHom_ptUnit, Category.assoc, ← Functor.map_comp,
    ← Category.assoc (specHom i), specHom_galHom i τ σ h, Category.assoc]

/-- Every `τ ∈ G_L` restricts along `i` to some `σ ∈ G_K`. -/
lemma exists_res (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, i (σ x) = τ (i x) := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := i.toRingHom.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun x => (i.commutes x).symm)
  refine ⟨(τ.restrictScalars K).restrictNormal (AlgebraicClosure K), fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) (AlgebraicClosure K) x

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) → T_ℓ(A_L)` along `i`. -/
def bcT (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.T ℓ →ₗ[ℤ_[ℓ]] (J.baseChange L).T ℓ :=
  Tate.map (MonoidHom.toAdditive (bcPhi J i))

lemma bcT_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcT ℓ J i) :=
  Tate.map_injective _ (bcPhi_injective J i)

lemma bcT_galT (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (x : J.T ℓ) :
    bcT ℓ J i (J.galT σ x) = (J.baseChange L).galT τ (bcT ℓ J i x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul (bcPhi J i (J.galAct σ (Additive.toMul (x.1 n)))) =
    Additive.ofMul ((J.baseChange L).galAct τ (bcPhi J i (Additive.toMul (x.1 n))))
  rw [bcPhi_galAct J i τ σ h]

/-- `V_ℓ(A) → V_ℓ(A_L)` along `i`. -/
def bcV (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.V ℓ →ₗ[ℚ_[ℓ]] (J.baseChange L).V ℓ :=
  (bcT ℓ J i).baseChange ℚ_[ℓ]

lemma bcV_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcV ℓ J i) := by
  haveI : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (bcT_injective ℓ J i)

lemma bcV_galRep (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) :
    bcV ℓ J i ∘ₗ J.galRep ℓ σ = (J.baseChange L).galRep ℓ τ ∘ₗ bcV ℓ J i := by
  have h1 : bcT ℓ J i ∘ₗ J.galT σ = (J.baseChange L).galT τ ∘ₗ bcT ℓ J i :=
    LinearMap.ext fun x => bcT_galT ℓ J i τ σ h x
  change (bcT ℓ J i).baseChange ℚ_[ℓ] ∘ₗ (J.galT σ).baseChange ℚ_[ℓ] =
    ((J.baseChange L).galT τ).baseChange ℚ_[ℓ] ∘ₗ (bcT ℓ J i).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- **`V_ℓ` under base change (GLUE, proved).** For an abelian variety `J` over `K`, a field
extension `L/K` and a `K`-embedding `i : K̄ → L̄`, `V_ℓ(i) : V_ℓ(J) → V_ℓ(J_L)` is injective and
intertwines `σ ∈ G_K` with `τ ∈ G_L` whenever `i ∘ σ = τ ∘ i`; after extension of scalars to any
field `E ⊇ ℚ_ℓ` it stays injective and equivariant. (With `TateModuleFree` over `K` and `L` and
`dim J_L = dim J` it is bijective, `PkgI3.Tate.map_bijective`; injectivity suffices for E1.) -/
theorem bcVE_injective (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective ((bcV ℓ J i).baseChange E) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ (bcV_injective ℓ J i)

theorem bcVE_equivariant (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (v : TensorProduct ℚ_[ℓ] E (J.V ℓ)) :
    (bcV ℓ J i).baseChange E (GlueI3.repBaseChange E (J.galRep ℓ) σ v) =
      GlueI3.repBaseChange E ((J.baseChange L).galRep ℓ) τ ((bcV ℓ J i).baseChange E v) := by
  change ((bcV ℓ J i).baseChange E ∘ₗ (J.galRep ℓ σ).baseChange E) v =
    (((J.baseChange L).galRep ℓ τ).baseChange E ∘ₗ (bcV ℓ J i).baseChange E) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, bcV_galRep ℓ J i τ σ h]

end BC2

/-! ### The restriction `G_L → G_K` along `i` and bijectivity under `TateModuleFree` -/

section Res

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The restriction `res_i : G_L → G_K`, `i ∘ res_i(τ) = τ ∘ i` (unique since `i` is injective). -/
def res (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) →* (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    where
  toFun τ := Classical.choose (exists_res i τ)
  map_one' := by
    apply AlgEquiv.ext; intro x
    apply i.toRingHom.injective
    exact (Classical.choose_spec (exists_res i 1) x).trans rfl
  map_mul' τ₁ τ₂ := by
    apply AlgEquiv.ext; intro x
    apply i.toRingHom.injective
    change i _ = i _
    rw [Classical.choose_spec (exists_res i (τ₁ * τ₂)) x]
    change τ₁ (τ₂ (i x)) = i (Classical.choose (exists_res i τ₁)
      (Classical.choose (exists_res i τ₂) x))
    rw [Classical.choose_spec (exists_res i τ₁), Classical.choose_spec (exists_res i τ₂)]

lemma res_spec (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (x : AlgebraicClosure K) :
    i (res i τ x) = τ (i x) :=
  Classical.choose_spec (exists_res i τ) x

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`T_ℓ` under base change is bijective (GLUE, proved from `TateModuleFree` and the
dimension being unchanged by base change).** `dim A_L = dim A` is a standard fact (dimension of
a scheme locally of finite type over a field is invariant under field extension; Stacks, Tag
00P4 for algebras, UNVERIFIED tag) taken here as a hypothesis; it is not needed for E1. -/
theorem bcT_bijective (hT : TateModuleFree) (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (hℓ : (ℓ : K) ≠ 0)
    (hdim : (J.baseChange L).dim = J.dim) : Function.Bijective (bcT ℓ J i) := by
  have hℓL : (ℓ : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).2 hℓ
  obtain ⟨hfr, hfi, hr⟩ := hT K J ℓ hℓ
  obtain ⟨-, hfiL, hrL⟩ := hT L (J.baseChange L) ℓ hℓL
  refine Tate.map_bijective _ (bcPhi_injective J i) ?_
  have : ((Module.finrank ℤ_[ℓ] (J.T ℓ) : ℕ∞) : WithBot ℕ∞) =
      ((Module.finrank ℤ_[ℓ] ((J.baseChange L).T ℓ) : ℕ∞) : WithBot ℕ∞) := by
    rw [hr, hrL, hdim]
  exact_mod_cast this

end Res

end E1Sub

end BCsec

/-! ## §5. E1 for R16: `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J₁(N)_L) ⊗ ℚ̄_ℓ` -/

namespace E1Sub

section Final

open LeafModCurves
open PkgI4 (GQ)

/-- **E1 for R16 (GLUE, proved from R16 and the I3 leaves `FaltingsSemisimple`, `FaltingsTate`,
`TateModuleFree`).** Let `f` be a weight-2 newform of level `N`, `J` a `J₁(N)` over `ℚ`, `L` any
field of characteristic `0` (in the application, the number field `L'` of N5 L861-867) and
`i : ℚ̄ → L̄` an embedding. Then there are Shimura's `A_f`, `π : J ↠ A_f` and `θ : K_f → End⁰(A_f)`
such that for every prime `ℓ` and embedding `ι : K_f → ℚ̄_ℓ`, R16's `ρ_{f,ι} = rhoF ℓ A_f θ ι` (on
a 2-dimensional `ℚ̄_ℓ`-space, with Frobenius traces `ι(a_p(f))` at `p ∤ Nℓ`) is equivariantly
isomorphic to a subrepresentation `U` of `V_ℓ(J_L) ⊗ ℚ̄_ℓ`, where `τ ∈ G_L` acts on `ρ_{f,ι}`
through any `σ ∈ G_ℚ` with `i ∘ σ = τ ∘ i` (such `σ` exists, `exists_res`, and is unique
because `i` is injective; `rhoFL_subrep_JL` restates this with `res i`). This is the `U'` that `PkgI3.E1_exists_hom_ne_zero`
consumes on the `J` side (with `K = L'`, `E = ℚ̄_ℓ`). -/
theorem rhoF_subrep_JL (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (L : Type) [Field L] [Algebra ℚ L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) = emb a) ∧
        ∃ (U : Subrepresentation
            (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
          (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
          ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
            (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
              e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
                  U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ A θ emb σ (e u) := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := rhoF_subrep_J hR16 hS hF hT N hN χ f hf J hJ
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, hss, htr, U0, e0, he0⟩ := hrest ℓ emb
  refine ⟨h2, hss, htr, ?_⟩
  let Ψ := (bcV ℓ J i).baseChange (PadicAlgCl ℓ)
  have hΨ : Function.Injective Ψ := bcVE_injective ℓ (PadicAlgCl ℓ) J i
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)) :=
    { toSubmodule := U0.toSubmodule.map Ψ
      apply_mem_toSubmodule := by
        rintro τ _ ⟨u, hu, rfl⟩
        obtain ⟨σ, hσ⟩ := exists_res i τ
        refine ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u,
          U0.apply_mem_toSubmodule σ hu, ?_⟩
        exact bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u }
  let eM := Submodule.equivMapOfInjective Ψ hΨ U0.toSubmodule
  refine ⟨U, eM.symm.trans e0, fun τ σ hσ u => ?_⟩
  obtain ⟨u0, rfl⟩ := eM.surjective u
  have hmap : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (eM u0),
      U.apply_mem_toSubmodule τ (eM u0).2⟩ : U.toSubmodule) =
      eM ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0,
        U0.apply_mem_toSubmodule σ u0.2⟩ := by
    apply Subtype.ext
    change GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (Ψ u0) =
      Ψ (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0)
    exact (bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u0).symm
  simp only [LinearEquiv.trans_apply]
  rw [hmap, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact he0 σ u0

/-- `ρ_{f,ι}|_{G_L}`: R16's representation restricted along `res_i : G_L → G_ℚ`. -/
def rhoFL (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) {L : Type} [Field L] [Algebra ℚ L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    Representation (PadicAlgCl ℓ) (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
      (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) :=
  (rhoF ℓ A θ emb).comp (res i)

/-- **E1 for R16, as `G_L`-representations.** `ρ_{f,ι}|_{G_L}` (`rhoFL`) is isomorphic to a
subrepresentation of `V_ℓ(J_L) ⊗ ℚ̄_ℓ`. -/
theorem rhoFL_subrep_JL (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (L : Type) [Field L] [Algebra ℚ L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        ∃ (U : Subrepresentation
            (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
          (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
          ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (u : U.toSubmodule),
            e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
                U.apply_mem_toSubmodule τ u.2⟩ = rhoFL ℓ A θ emb i τ (e u) := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := rhoF_subrep_JL hR16 hS hF hT N hN χ f hf J hJ L i
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, -, -, U, e, he⟩ := hrest ℓ emb
  exact ⟨h2, U, e, fun τ u => he τ (res i τ) (res_spec i τ) u⟩

/-- **E1 for R16, assembled (GLUE, proved).** In the situation of `rhoF_subrep_JL`, with `L` a
number field: for every abelian variety `A'` over `L` (the QM surface of N5) and every nonzero
subrepresentation `U` of `V_ℓ(A') ⊗ ℚ̄_ℓ` that is `G_L`-equivariantly isomorphic to
`ρ_{f,ι}|_{G_L}` (the output C9 must supply: `r_ℓ ≅ ρ_{f,ι}` on a constituent of `V_ℓ(A')`; the
dimension, semisimplicity and trace clauses for these `A_f, θ` are exported for that purpose), there
is a nonzero homomorphism `A' → J_L` over `L`; if moreover `End⁰(A')` is a division algebra,
Poincaré reducibility (leaf T8) gives an abelian variety `Z` and `g : Z → J_L` with
`(φ, g) : A' × Z → J_L` an isogeny (N5 L861-867). -/
theorem E1_R16 (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (hP : PoincareReducibility) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (L : Type) [Field L] [NumberField L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) = emb a) ∧
        ∀ (A' : AbVar L)
        (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ))),
        U ≠ ⊥ →
        ∀ eA : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb),
          (∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
            (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
              eA ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ) τ u,
                  U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ A θ emb σ (eA u)) →
          ∃ φ : Hom A' (J.baseChange L), φ ≠ 0 ∧
            (EndDivision A' → ∃ (Z : AbVar L) (g : Hom Z (J.baseChange L)),
              IsIsogenyMor (fst A'.X Z.X ≫ φ.hom * snd A'.X Z.X ≫ g.hom)) := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := rhoF_subrep_JL hR16 hS hF hT N hN χ f hf J hJ L i
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, hss, htr, U', eJ, heJ⟩ := hrest ℓ emb
  refine ⟨h2, hss, htr, fun A' U hU eA heA => ?_⟩
  let e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] U'.toSubmodule := eA.trans eJ.symm
  have he : ∀ (τ : Field.absoluteGaloisGroup L) (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ :
        TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) ((J.baseChange L).V ℓ)) =
        GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u) := by
    intro τ u
    obtain ⟨σ, hσ⟩ := exists_res i τ
    have h1 : eJ ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u),
        U'.apply_mem_toSubmodule τ (e u).2⟩ =
        eJ (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ) τ u,
          U.apply_mem_toSubmodule τ u.2⟩) := by
      rw [heJ τ σ hσ (e u)]
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [heA τ σ hσ u]
    exact congrArg Subtype.val (eJ.injective h1).symm
  obtain ⟨φ, hφ⟩ := E1_exists_hom_ne_zero' hS hF hT A' (J.baseChange L) ℓ (PadicAlgCl ℓ) U U' hU
    e he
  exact ⟨φ, hφ, fun hdiv => hP L A' (J.baseChange L) hdiv φ hφ⟩

end Final

end E1Sub
end
end E1Copy

/-! Copied verbatim from scratch/g0-mod-newform/part_new.lean. -/
/-!
# g0-mod-newform: glue G13-G16 of `docs/research/h-decomposition.md` §3

The last range of `ModularConstituent` (`scratch/g0-split/part_split.lean`, piece 10): from the
outputs of G8-G12 (the constituent `r_ℓ` of `V_ℓ(A)` as a `G_ℚ`-representation, and Pan-Berger's
eigenform up to a finite twist, `G12Out`) to the outputs of G16 (a newform `f` of weight 2 and
level `1 ≤ N ≤ Q_R M²`, and for every `J₁(N)` a common constituent of `V₅(A)` and
`V₅(J₁(N)_{L'})`, E1's hypothesis).

* G13 (`g13`, proved from T24, T25, R16, Faltings' Satz 3 and 4, I3.M0, T18, T19):
  `r₅` is attached to a newform `f` outside a finite set, and `r₅|G_{L'} ≅ ρ_{f,5}|G_{L'}` is a
  common constituent of `V₅(A)` and `V₅(J₁(N)_{L'})`.
* G14 (`g14`, proved from R14, T18, T19 and the named AV-side Prop `G14TraceCompat`):
  `r₃` is attached to the same `f` outside a finite set, and `r₃`, `r₅` are isomorphic to R14's
  semisimple representations attached to `f` (in `AttachedTo` form, unramified outside `Nℓ`).
* G15 (`g15`, proved from R17 (`CarayolR17'`), the glue `SwanIndependent` and the named Prop
  `G15LocalBounds`): the exponents of `N` (`r₅` at `p ≠ 5`, `r₃` at `p = 5`).
* G16 (`g16`, proved: `GlueConductor.level_le`): `N ≤ Q_R M²`.

Leaves and glue targets are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-! ## §1. Representation lemmas (proved) -/

section RepLemmas

variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An isomorphism of `k[G]`-modules `ρ.asModule ≅ σ.asModule` is a `G`-equivariant
`k`-linear equivalence `V ≃ W`. -/
theorem equivariant_of_asModule (ρ : Representation k G V) (σ : Representation k G W)
    (φ : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  refine ⟨{ toFun := fun v => σ.asModuleEquiv (φ (ρ.asModuleEquiv.symm v))
            invFun := fun w => ρ.asModuleEquiv (φ.symm (σ.asModuleEquiv.symm w))
            map_add' := fun v w => by simp
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul]
              simp
            left_inv := fun v => by simp
            right_inv := fun w => by simp }, fun g v => ?_⟩
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul]
  simp

end RepLemmas

/-! ## §2. The conductor exponent at a level is invariant under isomorphism (proved) -/

section CondIso

open LadicCond
open PkgI4 (GQp)

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] {n : ℕ}

/-- If `e` intertwines `ρ` and `ρ'`, then `e` maps `V^{ρ(S)}` onto `V^{ρ'(S)}`. -/
theorem invariants_eq_map (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    invariants ρ' S = (invariants ρ S).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    intro σ hσ
    apply e.injective
    rw [← he, e.apply_symm_apply]
    exact hw σ hσ
  · rintro ⟨v, hv, rfl⟩ σ hσ
    change (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) = e v
    rw [he]
    exact congrArg e (hv σ hσ)

theorem codimInv_eq (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    codimInv ρ' S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_eq_map ρ ρ' e he S, LinearEquiv.finrank_map_eq]

theorem eq_one_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (σ : GQp p) (h : ρ σ = 1) : ρ' σ = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [Matrix.toLin'_apply, he, h]
  simp

theorem isAdapted_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) (hL : IsAdapted L ρ) :
    IsAdapted L ρ' :=
  ⟨hL.1, fun σ hσ => eq_one_of_intertwine ρ ρ' e he σ (hL.2 σ hσ)⟩

theorem condAt_eq_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) :
    condAt L ρ' = condAt L ρ := by
  unfold condAt swanAt
  rw [codimInv_eq ρ ρ' e he]
  congr 1
  exact finsum_congr fun i => by rw [codimInv_eq ρ ρ' e he]

/-- An equivariant equivalence of `GaloisRep`s intertwines their restrictions to `G_{ℚ_p}`. -/
theorem restrictLocal_intertwine {ℓ : ℕ} [Fact ℓ.Prime] (r ρ : GaloisRep ℓ n)
    (e : (Fin n → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin n → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) :
    ∀ σ v, ((ρ.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec (e v) =
      e (((r.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec v) := by
  intro σ v
  have h := he (PkgI4.decomp p σ) v
  rw [toRep_apply, toRep_apply, Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  exact h.symm

end CondIso

/-! ## §3. The interface: data and outputs of G8-G12 -/

/-- **Pan-Berger's output on `r` (C7-C8 = G12's output, `docs/research/h-decomposition.md` §3).**
`r` is attached, up to the twist `ψ` and outside a finite set `S`, to a normalized eigenform `g`
of **weight 2** and level `M` (Pan's trace form, `PkgI4.GaloisRep.AttachedUpToTwist`), and `ψ` is,
at arithmetic Frobenius outside `S`, the Dirichlet character `ψD` mod `m` (N5 L758-768: the twist
is finite, then class field theory over `ℚ`; the weight comparison forces `k = 2`). -/
def PanOutput {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (r : GaloisRep ℓ 2) : Prop :=
  ∃ (M : ℕ) (χg : DirichletCharacter ℂ M) (g : CF M 2) (m : ℕ) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ),
    0 < M ∧ IsNormalizedEigenform g χg ∧ 0 < m ∧ r.AttachedUpToTwist ψ ιC ιL g S ∧
    ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **`r|_{G_L}` is a constituent of `V_ℓ(A) ⊗ ℚ̄_ℓ`** (G8's `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}`): a
nonzero subrepresentation `U` of `V_ℓ(A) ⊗ ℚ̄_ℓ` (`A` over `L`) with a linear isomorphism
`U ≃ ℚ̄_ℓ²` carrying `τ ∈ G_L` to `r(σ)` for every `σ ∈ G_ℚ` with `i ∘ σ = τ ∘ i`
(`i : ℚ̄ → L̄`; such `σ` exist and are unique, `E1Sub.exists_res`). -/
def IsConstituentOf (ℓ : ℕ) [Fact ℓ.Prime] {L : Type} [Field L] [Algebra ℚ L] (A : AbVar L)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) (r : GaloisRep ℓ 2) : Prop :=
  ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ)), U ≠ ⊥ ∧
    ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ), (∀ x, i (σ x) = τ (i x)) →
      ∀ u : U.toSubmodule,
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ =
          toRep r σ (e u)

/-- The data that G8-G12 produce for the model `A/L'`: an embedding `i : ℚ̄ → L̄'`, embeddings
`ιC : ℚ̄ → ℂ`, `ι₅ : ℚ̄ → ℚ̄₅`, `ι₃ : ℚ̄ → ℚ̄₃`, and the two `G_ℚ`-representations `r₅`, `r₃`
(N5 L719-734: `r_ℓ`, made a `G_ℚ`-representation by the Tate action and the descent of G7). -/
structure ModData (L : Type) [Field L] [NumberField L] (A : AbVar L) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L
  ιC : Qbar →ₐ[ℚ] ℂ
  ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3
  r5 : GaloisRep 5 2
  r3 : GaloisRep 3 2

/-- **G12Out: the output of G8-G12** (the range of task g0-mod-galois) on the data `D`:
`r₅`, `r₃` irreducible (C2, Burnside form), constituents of `V₅(A)`, `V₃(A)` on `G_{L'}` (C1),
and Pan-Berger's weight-2 eigenform up to a finite twist for `r₅` (C3-C8). -/
def G12Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) : Prop :=
  D.r5.IsIrreducible ∧ D.r3.IsIrreducible ∧ IsConstituentOf 5 A D.i D.r5 ∧
    IsConstituentOf 3 A D.i D.r3 ∧ PanOutput D.ιC D.ι5 D.r5

/-- `G12Out A`: some data `D` for `A` satisfy `G12Spec`. -/
def G12Out {L : Type} [Field L] [NumberField L] (A : AbVar L) : Prop :=
  ∃ D : ModData L A, G12Spec D

/-- **Open part of G14 (glue, AV side; N5 L776-795).** At every arithmetic Frobenius `τ` above
`p ∉ S`, the traces of `r₅` and `r₃` are the images of one algebraic number: if
`tr r₅(τ) = ι₅(c)` then `tr r₃(τ) = ι₃(c)`. Glazer's proof: for `p ∉ T ∪ {3, 5}` a lift `σ` of
Frobenius, the relative Frobenius of the reduction of `A` composed with `μ̄_σ` is an endomorphism
of `Ā_v` whose characteristic polynomial on `V_ℓ` is independent of `ℓ` (T7, with T3, T4); half
its trace times `β(σ)⁻¹a_σ` is the common value. It is a statement about the `r_ℓ` built in G8
from the descent data of G7 (not about arbitrary constituents: a constituent determines `r_ℓ`
only on `G_{L'}`), so it is to be proved together with that construction. -/
def G14TraceCompat {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p → ∀ c : Qbar,
      (D.r5.mat τ).trace = D.ι5 c → (D.r3.mat τ).trace = D.ι3 c

/-- Glazer's local bound for `r` at `p` (N5 L798-852), at a level `L_p` adapted to `r|G_{ℚ_p}`:
the conductor exponent is `≤ E₀` if `p ≤ R` (`R = D`), `≤ 2` if `p > R`, and `0` if
`p ∉ T = S ∪ supp M_S(u)`. -/
def LocalBound (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ∃ Lp : LadicCond.Fld p, LadicCond.IsAdapted Lp (r.restrictLocal p) ∧
    ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      LadicCond.condAt Lp (r.restrictLocal p) ≤ (ZInQ.heightE0 : ℚ)) ∧
    ((ZInQ.heightD : ℝ) < p → LadicCond.condAt Lp (r.restrictLocal p) ≤ 2) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u →
      LadicCond.condAt Lp (r.restrictLocal p) = 0)

/-- **Open part of G15 (glue, D1-D4 on the actual `A`; N5 L796-852).** `r₅` satisfies Glazer's
local bound at every prime `p ≠ 5` and `r₃` at `p = 5`. The cores are proved over the kernel's
finite-level objects (D1 `GlueConductor.D1_genuine`, D2 `PkgI2.D2_fixed_of_raynaud`, D3
`GlueConductor.fourth_pow_mem`, D4 `PkgI6.artinConductor_le_of_upper`,
`LadicCond.condAt_le_of_upper`); what is open is their instantiation on the `r_ℓ` built in G8
(Raynaud's semistability over `L'_v(A[3])`, wild inertia on `V_ℓ(A)`, the wild part of `β`). -/
def G15LocalBounds {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalBound u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalBound u p ⟨hp⟩ 3 _ D.r3)

/-! ## §4. G13: the newform and the common constituent -/

/-- `r` is attached to `f` outside `S`: at every arithmetic Frobenius above `p ∉ S`, the trace is
`ι_L(α)` with `ι_C(α) = a_p(f)` (`AttachedUpToTwist` with trivial twist, without the
unramifiedness clause). -/
def AttachedOutside {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (f : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ∃ α : Qbar, ιC α = coeff f p ∧
    ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
      (r.mat τ).trace = ιL α

/-- E1's hypothesis (copied from `scratch/g0-split/part_split.lean`): for some prime `ℓ` and
field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common nonzero constituent, as
`G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- **G13Out** on the data `D`: a newform `f` of weight 2, level `N ≥ 1` and nebentypus `χ`;
`r₅` is attached to `f` outside a finite set; and for every `J₁(N)` `J` over `ℚ`, `V₅(A)` and
`V₅(J_{L'})` have a common constituent (`r₅|G_{L'} ≅ ρ_{f,5}|G_{L'}`). -/
def G13Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) : Prop :=
  0 < N ∧ IsNewform f χ ∧ D.r5.IsSemisimple ∧ D.r3.IsSemisimple ∧
    (∃ S, AttachedOutside D.r5 D.ιC D.ι5 f S) ∧
    ∀ J : AbVar ℚ, IsJ1 N J → CommonConstituent A (J.baseChange L)

/-- The `J`-side of E1 for a given Shimura quotient `π : J ↠ A_f` (the proof of
`E1Sub.rhoF_subrep_JL`, for given `A_f`, `π`, `θ`). -/
theorem jSide (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    (J Af : AbVar ℚ) (π : Hom J Af) (hπ : Surjective π.hom.left) {F : Type} [Field F]
    (θ : F →+* Af.End0) (ℓ : ℕ) [Fact ℓ.Prime] (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb)]
    (L : Type) [Field L] [Algebra ℚ L] (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (U : Subrepresentation
        (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
      (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb)),
      ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
        (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
          e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
              U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ Af θ emb σ (e u) := by
  obtain ⟨U0, e0, he0⟩ := E1Sub.rhoF_subrep_of_surj ℓ hS hT J Af π
    (E1Sub.vSurjOfSurjective hS hF hT J Af π ℓ hπ) θ emb
  let Ψ := (E1Sub.bcV ℓ J i).baseChange (PadicAlgCl ℓ)
  have hΨ : Function.Injective Ψ := E1Sub.bcVE_injective ℓ (PadicAlgCl ℓ) J i
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)) :=
    { toSubmodule := U0.toSubmodule.map Ψ
      apply_mem_toSubmodule := by
        rintro τ _ ⟨u, hu, rfl⟩
        obtain ⟨σ, hσ⟩ := E1Sub.exists_res i τ
        refine ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u,
          U0.apply_mem_toSubmodule σ hu, ?_⟩
        exact E1Sub.bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u }
  let eM := Submodule.equivMapOfInjective Ψ hΨ U0.toSubmodule
  refine ⟨U, eM.symm.trans e0, fun τ σ hσ u => ?_⟩
  obtain ⟨u0, rfl⟩ := eM.surjective u
  have hmap : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (eM u0),
      U.apply_mem_toSubmodule τ (eM u0).2⟩ : U.toSubmodule) =
      eM ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0,
        U0.apply_mem_toSubmodule σ u0.2⟩ := by
    apply Subtype.ext
    change GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (Ψ u0) =
      Ψ (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0)
    exact (E1Sub.bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u0).symm
  simp only [LinearEquiv.trans_apply]
  rw [hmap, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact he0 σ u0

/-- **Twist bookkeeping (proved, from T24 and T25; the computation of `C9Rhof.c9_r5`).** From
Pan-Berger's output, a newform `f` of weight 2 and level `N ∣ M m²` to which `r` is attached
outside a finite set. -/
theorem newform_of_pan (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (r : GaloisRep ℓ 2) (h : PanOutput ιC ιL r) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ IsNewform f χ ∧
      ∃ S, AttachedOutside r ιC ιL f S := by
  obtain ⟨M, χg, g, m, ψD, ψ, S, hM, hg, hm, hrg, hψ⟩ := h
  obtain ⟨χ', g', hg', hcoef⟩ := hTw M m 2 χg ψD g hM hm hg
  obtain ⟨N, χ, f, hN, hNd, hf, hcf⟩ := hNew (M * m ^ 2) 2 χ' g' (by positivity) hg'
  refine ⟨N, χ, f, hN, hf, S ∪ (M * m).primeFactors, fun p hp hpS => ?_⟩
  have hMm : M * m ≠ 0 := Nat.mul_ne_zero hM.ne' hm.ne'
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hpMm : ¬ p ∣ M * m := fun h =>
    hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMm⟩))
  have hpMm2 : ¬ p ∣ M * m ^ 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hpMm (dvd_mul_of_dvd_left h1 _)
    · exact hpMm (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) _)
  obtain ⟨-, α, hα, htrα⟩ := hrg p hp hpS1
  obtain ⟨β, hβ, hψp⟩ := hψ p hp hpS1
  refine ⟨β * α, ?_, fun v τ hv hτ => ?_⟩
  · rw [map_mul, hβ, hα, hcf p hp hpMm2, hcoef p hp hpMm]
  · rw [htrα v τ hv hτ, hψp v τ hv hτ, map_mul]

/-- **E1 on `A` for a representation attached to `f` (proved from R16, Faltings' Satz 3 and 4,
I3.M0, T18, T19).** If `r` is semisimple, attached to the newform `f` outside a finite set, and
`r|_{G_L}` is a constituent of `V_ℓ(A)`, then for every `J₁(N)` `J`, `V_ℓ(A)` and `V_ℓ(J_L)` have
a common constituent: `r|G_L ≅ ρ_{f,ι}|G_L` (C9, Brauer–Nesbitt), which is a sub of
`V_ℓ(J_L) ⊗ ℚ̄_ℓ` (E1Sub). -/
theorem commonConstituent_of_attached (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {L : Type} [Field L] [NumberField L] (A : AbVar L)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) (ℓ : ℕ) [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hA : IsConstituentOf ℓ A i r) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (f : CF N 2) (hf : IsNewform f χ) (S : Finset ℕ) (hatt : AttachedOutside r ιC ιL f S)
    (J : AbVar ℚ) (hJ : IsJ1 N J) : CommonConstituent A (J.baseChange L) := by
  obtain ⟨hfin, Af, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  set emb := embOf ℓ ιC ιL (coeffField f) with hemb
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  haveI : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb) :=
    Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨-, -, ⟨φ⟩, -, -⟩ := c9_core ℓ hS hT hBN hD N hN
    (fun p => (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)) Af θ emb h2
    (fun p hp hpN σ hσ => (hfr p hp hpN σ hσ).1 _ rfl) S (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (toRep r) (toRep_continuous r) (toRep_semisimple r hr) (by
      intro p hp hpS _ v τ hv hτ
      obtain ⟨α, hα, hrα⟩ := hatt p hp hpS
      rw [trace_toRep, hrα v τ hv hτ]
      exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm)
  obtain ⟨eφ, heφ⟩ := equivariant_of_asModule _ _ φ
  obtain ⟨U, eR, hU, heR⟩ := hA
  obtain ⟨U', eJ, heJ⟩ := jSide hS hF hT J Af π hπ θ ℓ emb L i
  let e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] U'.toSubmodule := (eR.trans eφ).trans eJ.symm
  refine ⟨ℓ, inferInstance, PadicAlgCl ℓ, inferInstance, inferInstance, U, U', e, hU,
    fun τ u => ?_⟩
  obtain ⟨σ, hσ⟩ := E1Sub.exists_res i τ
  have h1 : eJ ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u),
      U'.apply_mem_toSubmodule τ (e u).2⟩ =
      eJ (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u,
        U.apply_mem_toSubmodule τ u.2⟩) := by
    rw [heJ τ σ hσ (e u)]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [heR τ σ hσ u, heφ]
  exact congrArg Subtype.val (eJ.injective h1).symm

/-- **G13 (GLUE, proved from T24, T25, R16, Faltings' Satz 3 and 4, I3.M0, T18, T19).** -/
theorem g13 (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hF : FaltingsTate)
    (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (h12 : G12Spec D) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), G13Spec D N χ f := by
  obtain ⟨hirr5, hirr3, hA5, -, hpan⟩ := h12
  obtain ⟨N, χ, f, hN, hf, S, hatt⟩ := newform_of_pan hTw hNew D.ιC D.ι5 D.r5 hpan
  have hss5 := isSemisimple_of_isIrreducible D.r5 hirr5
  refine ⟨N, χ, f, hN, hf, hss5, isSemisimple_of_isIrreducible D.r3 hirr3, ⟨S, hatt⟩,
    fun J hJ => ?_⟩
  exact commonConstituent_of_attached hR16 hS hF hT hBN hD A D.i 5 D.ιC D.ι5 D.r5 hss5 hA5 N hN
    χ f hf S hatt J hJ

/-! ## §5. G14: `r₃` and `r₅` against R14's representations of `f` -/

/-- **Brauer–Nesbitt against R14 (proved from R14, T18, T19).** A semisimple `r` attached to the
newform `f` outside a finite set is equivariantly isomorphic to R14's semisimple `ρ` attached to
`f` (in `AttachedTo` form: unramified outside `Nℓ`, traces `a_p` at every `p ∤ Nℓ`). -/
theorem iso_R14 (hR14 : PkgI4.EigenformRepExists) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (S : Finset ℕ) (hatt : AttachedOutside r ιC ιL f S) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ),
        ∀ g v, e (toRep r g v) = toRep ρ g (e v) := by
  obtain ⟨ρ, hss, hρ⟩ := hR14 ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨φ⟩ := iso_of_arithFrob hBN hD (S ∪ (N * ℓ).primeFactors)
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep r)
    (toRep ρ) (toRep_continuous r) (toRep_continuous ρ) (toRep_semisimple r hr)
    (toRep_semisimple ρ hss) (by
      intro p hp hpS v τ hv hτ
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpN : ¬ p ∣ N * ℓ := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩))
      obtain ⟨α, hα, hrα⟩ := hatt p hp hpS1
      obtain ⟨-, α', hα', hρα⟩ := hρ p hp hpN
      have : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
      rw [trace_toRep, trace_toRep, hrα v τ hv hτ, hρα v τ hv hτ, this])
  obtain ⟨e, he⟩ := equivariant_of_asModule _ _ φ
  exact ⟨ρ, hss, hρ, e, he⟩

/-- **G14Out** on the data `D` and the newform `f`: both `r₅` and `r₃` are equivariantly
isomorphic to semisimple representations attached to `f` in R14's `AttachedTo` form. -/
def G14Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (f : CF N 2) : Prop :=
  (∃ ρ : GaloisRep 5 2, ρ.IsSemisimple ∧ ρ.AttachedTo D.ιC D.ι5 f ∧
      ∃ e : (Fin 2 → PadicAlgCl 5) ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5),
        ∀ g v, e (toRep D.r5 g v) = toRep ρ g (e v)) ∧
    (∃ ρ : GaloisRep 3 2, ρ.IsSemisimple ∧ ρ.AttachedTo D.ιC D.ι3 f ∧
      ∃ e : (Fin 2 → PadicAlgCl 3) ≃ₗ[PadicAlgCl 3] (Fin 2 → PadicAlgCl 3),
        ∀ g v, e (toRep D.r3 g v) = toRep ρ g (e v))

/-- **G14 (GLUE, proved from R14, T18, T19 and the AV-side Prop `G14TraceCompat`).** -/
theorem g14 (hR14 : PkgI4.EigenformRepExists) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f)
    (hc : G14TraceCompat D) : G14Spec D N f := by
  obtain ⟨hN, hf, hss5, hss3, ⟨S, hatt⟩, -⟩ := h13
  obtain ⟨Sc, hSc⟩ := hc
  have hatt3 : AttachedOutside D.r3 D.ιC D.ι3 f (S ∪ Sc) := by
    intro p hp hpS
    have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpS2 : p ∉ Sc := fun h => hpS (Finset.mem_union_right _ h)
    obtain ⟨α, hα, hrα⟩ := hatt p hp hpS1
    exact ⟨α, hα, fun v τ hv hτ => hSc p hp hpS2 v τ hv hτ α (hrα v τ hv hτ)⟩
  exact ⟨iso_R14 hR14 hBN hD D.ιC D.ι5 N hN χ f hf D.r5 hss5 S hatt,
    iso_R14 hR14 hBN hD D.ιC D.ι3 N hN χ f hf D.r3 hss3 (S ∪ Sc) hatt3⟩

/-! ## §6. G15: the exponents of `N` -/

/-- **G15Out**: the exponents of the level, N5 L846-852 (`a_p = v_p(N)` by Carayol). -/
def G15Out (N : ℕ) (u : ℚ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ (ZInQ.heightD : ℝ) → N.factorization p ≤ ZInQ.heightE0) ∧
    (∀ p : ℕ, p.Prime → (ZInQ.heightD : ℝ) < p → N.factorization p ≤ 2) ∧
    (∀ p : ℕ, p.Prime → p ∣ N → p ∈ ZInQ.Mult.S_mul ∨ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u)

/-- Carayol at one prime, transported along an equivariant equivalence (proved from R17's
adapted-level form). -/
theorem factorization_eq_condAt (hCar : LadicCond.CarayolR17) {ℓ : ℕ} [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2)
    (ρ : GaloisRep ℓ 2) (hss : ρ.IsSemisimple) (hρ : ρ.AttachedTo ιC ιL f)
    (e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (Lp : LadicCond.Fld p) (hL : LadicCond.IsAdapted Lp (r.restrictLocal p)) :
    (N.factorization p : ℚ) = LadicCond.condAt Lp (r.restrictLocal p) := by
  have hint := restrictLocal_intertwine (p := p) r ρ e he
  rw [← hCar ℓ ιC ιL N χ f ρ p hN hf hss hρ hpℓ Lp
    (isAdapted_of_intertwine _ _ e hint Lp hL)]
  exact condAt_eq_of_intertwine _ _ e hint Lp

/-- **G15 (GLUE, proved from R17 (`CarayolR17'`), the glue `SwanIndependent` and the open Prop
`G15LocalBounds`).** -/
theorem g15 (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f) (h14 : G14Spec D N f)
    (u : ℚ) (hloc : G15LocalBounds D u) : G15Out N u := by
  have hC := LadicCond.carayolR17_of_R17' hSw hCar
  obtain ⟨hN, hf, -⟩ := h13
  obtain ⟨⟨ρ5, hss5, hρ5, e5, he5⟩, ⟨ρ3, hss3, hρ3, e3, he3⟩⟩ := h14
  -- the exponent at `p` is a conductor exponent of `r₅` (`p ≠ 5`) or `r₃` (`p = 5`)
  have key : ∀ p : ℕ, ∀ hp : p.Prime, ∃ (Lp : @LadicCond.Fld p ⟨hp⟩) (c : ℚ),
      (N.factorization p : ℚ) = c ∧ ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → c ≤ (ZInQ.heightE0 : ℚ)) ∧
      ((ZInQ.heightD : ℝ) < p → c ≤ 2) ∧
      (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → c = 0) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases h5 : p = 5
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).2 h5
      exact ⟨Lp, _, factorization_eq_condAt hC D.ιC D.ι3 N hN χ f hf D.r3 ρ3 hss3 hρ3 e3 he3 p
        (by omega) Lp had, h1, h2, h3⟩
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).1 h5
      exact ⟨Lp, _, factorization_eq_condAt hC D.ιC D.ι5 N hN χ f hf D.r5 ρ5 hss5 hρ5 e5 he5 p
        h5 Lp had, h1, h2, h3⟩
  refine ⟨fun p hp hpR => ?_, fun p hp hpR => ?_, fun p hp hpN => ?_⟩
  · obtain ⟨Lp, c, hc, h1, -, -⟩ := key p hp
    have := h1 hpR
    rw [← hc] at this
    exact_mod_cast this
  · obtain ⟨Lp, c, hc, -, h2, -⟩ := key p hp
    have := h2 hpR
    rw [← hc] at this
    exact_mod_cast this
  · by_contra hcon
    push_neg at hcon
    obtain ⟨Lp, c, hc, -, -, h3⟩ := key p hp
    have h0 := h3 hcon.1 hcon.2
    rw [h0] at hc
    have hfac : N.factorization p = 0 := by exact_mod_cast hc
    have hpos : 0 < N.factorization p := hp.factorization_pos_of_dvd hN.ne' hpN
    omega

/-! ## §7. G16: `N ≤ Q_R M²` -/

/-- **G16 (GLUE, proved: `GlueConductor.level_le` with `R = D`, `S = S_mul`).** -/
theorem g16 (N : ℕ) (hN : 0 < N) (u : ℚ) (h15 : G15Out N u) :
    (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD *
      (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 := by
  obtain ⟨hsmall, hlarge, hout⟩ := h15
  exact GlueConductor.level_le ZInQ.Mult.S_mul u ZInQ.heightD GlueAssembly.one_le_heightD_real
    (fun p hp => by exact_mod_cast ZInQ.Mult.le_heightD_of_mem_S_mul hp) N hN.ne'
    hsmall hlarge hout

/-! ## §7b. G15's local bounds from ramification statements (proved from L8 and
`AdaptedExists`) -/

section LocalRamSec

open LadicCond
open PkgI4 (GQp)

/-- Glazer's uniform bound for the last upper break, `U₀ = 4(DG₀)²` (N5 L826-830). -/
def U0 : ℝ := 4 * ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) ^ 2

/-- **The ramification of `r` at `p` that D1-D4 establish (N5 L819-852).** (i) for `p ≤ R`
(`R = D`): every absolute upper ramification group `G_{ℚ_p}^t`, `t > U₀`, acts trivially;
(ii) for `p > R`: wild inertia acts trivially (tame case); (iii) for `p ∉ T = S ∪ supp M_S(u)`:
inertia acts trivially (G11, in local form). -/
def LocalRam (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u →
      ∀ σ ∈ inertiaSet, r.restrictLocal p σ = 1)

/-- **Open part of G15, reduced (glue, D1-D4 on the actual `A`).** `LocalRam` for `r₅` at every
`p ≠ 5` and for `r₃` at `p = 5`. Proved cores over the kernel's finite-level objects: D1
(`GlueConductor.D1_genuine`, the break bound `≤ 4a²` from the different), D2
(`PkgI2.D2_fixed_of_raynaud`: wild inertia trivial on `V_ℓ(A)` after Raynaud), D3
(`GlueConductor.fourth_pow_mem`: the wild part of `β` at 2). Open: their instantiation on the
`r_ℓ` built in G8, and the transport from the finite-level filtrations to `upperAbs`. -/
def G15Ram {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRam u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRam u p ⟨hp⟩ 3 _ D.r3)

variable {p : ℕ} [Fact p.Prime]

/-- `ρ|_{G_{ℚ_p}}` is continuous (`Field.absoluteGaloisGroup.map` is a continuous hom). -/
theorem restrictLocal_continuous {ℓ n : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ n) :
    Continuous (r.restrictLocal p) :=
  r.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

/-- Trivial wild inertia ⇒ `Sw_L(ρ) = 0`. -/
theorem swanAt_eq_zero_of_wild {k : Type*} [Field k] {n : ℕ} {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ wildSet, ρ σ = 1) (L : Fld p) : swanAt L ρ = 0 := by
  rw [swanAt]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [codimInv_eq_zero (fun σ hσ => h σ hσ.2)]
  simp

/-- `2(1 + U₀) ≤ E₀`. -/
theorem two_one_add_U0_le : 2 * (1 + U0) ≤ (ZInQ.heightE0 : ℝ) := by
  have hD : 0 < ZInQ.heightD := by
    rw [ZInQ.Compiler.Precision.heightD_eq]
    exact Nat.mul_pos (Nat.factorial_pos 324) (by positivity)
  have h1 : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos hD (by unfold ZInQ.heightG0; norm_num)
  rw [ZInQ.Compiler.Precision.heightE0_eq, U0]
  generalize ZInQ.heightD * ZInQ.heightG0 = x at h1 ⊢
  have hx : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
  have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := one_le_pow₀ hx
  have hc : (((10 * x ^ 2 : ℕ)) : ℝ) = 10 * (x : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow]; rfl
  rw [hc]
  linarith

/-- **G15's local bound from the ramification (GLUE, proved from L8 `SwanIntegral` and
`AdaptedExists`):** `a ≤ 2(1 + U₀) ≤ E₀` for `p ≤ R` (`LadicCond.condAt_le_of_upper`), `a ≤ 2`
for tame `p`, `a = 0` if unramified. -/
theorem localBound_of_ram (hL8 : SwanIntegral) (hAd : AdaptedExists (p := p)) (u : ℚ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ) (r : GaloisRep ℓ 2) (h : LocalRam u p r) :
    LocalBound u p r := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨Lp, hL⟩ := hAd ℓ (Ne.symm hpℓ) 2 (r.restrictLocal p) (restrictLocal_continuous r)
  refine ⟨Lp, hL, fun hpR => ?_, fun hpR => ?_, fun hS hM => ?_⟩
  · have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hb := condAt_le_of_upper hL8 ℓ hpℓ (r.restrictLocal p) (restrictLocal_continuous r) Lp
      hL U0 hU0 (h1 hpR)
    have : ((condAt Lp (r.restrictLocal p) : ℚ) : ℝ) ≤ ((ZInQ.heightE0 : ℚ) : ℝ) := by
      push_cast at hb ⊢
      linarith [two_one_add_U0_le]
    exact_mod_cast this
  · rw [condAt, swanAt_eq_zero_of_wild (h2 hpR), add_zero]
    exact_mod_cast codimInv_le (r.restrictLocal p) inertiaSet
  · exact condAt_eq_zero_of_unramified (h3 hS hM) Lp

/-- **G15's local bounds from `G15Ram` (GLUE, proved).** -/
theorem g15LocalBounds_of_ram (hL8 : SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h : G15Ram D u) : G15LocalBounds D u := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · exact localBound_of_ram hL8 (hAd p) u h5 D.r5 ((h p hp).1 h5)
  · exact localBound_of_ram hL8 (hAd p) u (by omega) D.r3 ((h p hp).2 h5)

end LocalRamSec

/-! ## §8. The range G13-G16 assembled -/

/-- **G16Out**: what G13-G16 deliver to `ModularConstituent`: a level `1 ≤ N ≤ Q_R M²` (with
`R = D`, `M = M_{S_mul}(u)`) such that `V₅(A)` and `V₅(J_{L'})` have a common constituent for
every `J₁(N)` `J` over `ℚ`. -/
def G16Out {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ) : Prop :=
  ∃ N : ℕ, 0 < N ∧
    (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
    ∀ J : AbVar ℚ, IsJ1 N J → CommonConstituent A (J.baseChange L)

/-- The literature leaves this range uses (all already in `Leaves.lean` / the kernel). -/
structure NewformLeaves : Prop where
  t24 : PkgI4.EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  r14 : PkgI4.EigenformRepExists
  r16 : R16_EichlerShimuraJ1'
  r17 : LadicCond.CarayolR17'
  r9a : FaltingsSemisimple
  r9b : FaltingsTate
  m0 : TateModuleFree
  t18 : FrobeniusDense
  t19 : GlueC10.BrauerNesbittChar0

/-- **G13-G16 (GLUE, proved).** From G8-G12's output on data `D`, the two open AV-side Props
`G14TraceCompat D` and `G15LocalBounds D u` on the same data, the leaves, and the glue Prop
`SwanIndependent`: the level and the common constituent of `ModularConstituent`. -/
theorem g13_g16 (lv : NewformLeaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hloc : G15LocalBounds D u) : G16Out A u := by
  obtain ⟨N, χ, f, h13⟩ := g13 lv.t24 lv.t25 lv.r16 lv.r9a lv.r9b lv.m0 lv.t19 lv.t18 D h12
  have h14 := g14 lv.r14 lv.t19 lv.t18 D N χ f h13 hc
  have h15 := g15 lv.r17 hSw D N χ f h13 h14 u hloc
  exact ⟨N, h13.1, g16 N h13.1 u h15, h13.2.2.2.2.2⟩

/-- **G13-G16, reduced form (GLUE, proved).** As `g13_g16`, with G15's open part in the
ramification form `G15Ram` and the conductor arithmetic proved from the glue Props L8
(`SwanIntegral`) and `AdaptedExists` (both stated in the kernel's `LadicCond`). -/
theorem g13_g16_ram (lv : NewformLeaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hram : G15Ram D u) : G16Out A u :=
  g13_g16 lv hSw u D h12 hc (g15LocalBounds_of_ram hL8 hAd D u hram)

/-- With a `J₁(N)` from T33 (`JacobianExists`) and the glue target `X1ModelExists`: the `N`
of `G16Out` has a `J₁(N)`, as `ModularConstituent` asks. -/
theorem g16Out_with_J1 (hJac : JacobianExists ℚ) (hX : X1ModelExists)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (h : G16Out A u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨N, hN, hle, hcc⟩ := h
  obtain ⟨J, hJ⟩ := exists_J1 hJac hX N hN
  exact ⟨N, J, hN, hJ, hle, hcc J hJ⟩

/-- **The G13-G16 conclusion in the shape of `ModularConstituent`'s last conjuncts** (kernel
objects): for a model `A/L'` with G8-G12's data `D` and the two open Props on `D`, there are a level
`N` with `0 < N ≤ Q_R M²`, a `J₁(N)` `J` over `ℚ` and a common constituent of `V_ℓ(A)` and
`V_ℓ(J_{L'})`. -/
theorem modularConstituent_tail (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15Ram D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact g16Out_with_J1 hJac hX u (g13_g16_ram lv hSw hL8 hAd u D h12 hc hram)

/-! ## §9. Bridge from g0-mod-galois's interface (draft at origin/wip/g0-mod-galois ad7f14c2)

The definitions `resQ`, `Vb`, `tate`, `Intertwines`, `G8Out` (here `GalG8Out`), `G12Out` (here
`GalG12Out`) are copied verbatim from
`scratch/g0-mod-galois/part_galois.lean` (namespace `G0Galois` there), over the kernel's objects. -/

section Bridge

/-- (copied from g0-mod-galois) The restriction map `G_K → G_ℚ`. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied from g0-mod-galois) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied from g0-mod-galois) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied from g0-mod-galois) `e` intertwines `f g` with `r(g) ⊕ r(g)`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- (copied from g0-mod-galois) **Output of G8.** -/
def GalG8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

/-- (copied from g0-mod-galois) **Output of G12** at `ℓ = 5`: `ψ` of finite image. -/
def GalG12Out (r : GaloisRep 5 2) : Prop :=
  ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N ∧ PkgI4.IsNormalizedEigenform g χ ∧ (Set.range ψ.toHom).Finite ∧
    r.AttachedUpToTwist ψ ιC ιL g S

/-- **Kronecker–Weber at Frobenius (GLUE, unproved; from T17 `KroneckerWeber`).** A continuous
character `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius outside a finite set,
a Dirichlet character `ψD mod m` through `ιC`, `ιL`: `ψ` factors through
`Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` (T17), arithmetic Frobenius at `p ∤ m` maps to `p`, and the values
(roots of unity) lie in `ιL(ℚ̄)`. -/
def DirichletOfFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ), (Set.range ψ.toHom).Finite →
    ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
          (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **G12Out ⇒ PanOutput (GLUE, proved from `DirichletOfFinite`).** -/
theorem panOutput_of_G12Out (hDF : DirichletOfFinite) (r : GaloisRep 5 2) (h : GalG12Out r) :
    ∃ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl 5), PanOutput ιC ιL r := by
  obtain ⟨M, χ, g, ψ, ιC, ιL, S, hM, hg, hfin, hatt⟩ := h
  obtain ⟨m, ψD, S', hm, hψ⟩ := hDF 5 ψ hfin ιC ιL
  refine ⟨ιC, ιL, M, χ, g, m, ψD, ψ, S ∪ S', hM, hg, hm, fun p hp hpS => ?_,
    fun p hp hpS => hψ p hp (fun h => hpS (Finset.mem_union_right _ h))⟩
  exact hatt p hp (fun h => hpS (Finset.mem_union_left _ h))

/-- The embedding `ℚ̄ → K̄` underlying Mathlib's `Field.absoluteGaloisGroup.map`: it intertwines
`resQ K τ` with `τ`. -/
theorem resQ_spec (K : Type) [Field K] [NumberField K] :
    ∃ i : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x,
      i (resQ K τ x) = τ (i x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  refine ⟨g.toRingHom, fun τ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) τ)
    (AlgebraicClosure ℚ) x

/-- **G8Out ⇒ IsConstituentOf (GLUE, proved).** `U = ker(pr₂ ∘ e)` is the constituent. -/
theorem isConstituentOf_of_GalG8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (r : GaloisRep ℓ 2) (h : GalG8Out A ℓ ρ r)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (hi : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, i (resQ K τ x) = τ (i x)) :
    IsConstituentOf ℓ A i r := by
  obtain ⟨hres, e, he, -⟩ := h
  let W : Submodule (PadicAlgCl ℓ) (Vb A ℓ) :=
    LinearMap.ker ((LinearMap.snd (PadicAlgCl ℓ) _ _) ∘ₗ e.toLinearMap)
  have hW : ∀ v, v ∈ W ↔ (e v).2 = 0 := fun v => Iff.rfl
  have hstab : ∀ (σ : Field.absoluteGaloisGroup K) (w : Vb A ℓ), w ∈ W →
      GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ w ∈ W := by
    intro σ w hw
    rw [hW] at hw ⊢
    have h1 := he (resQ K σ) w
    rw [hres σ] at h1
    change (e (tate A ℓ σ w)).2 = 0
    rw [h1, hw, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)) :=
    { toSubmodule := W
      apply_mem_toSubmodule := fun σ w hw => hstab σ w hw }
  let f : U.toSubmodule →ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    (LinearMap.fst (PadicAlgCl ℓ) _ _) ∘ₗ e.toLinearMap ∘ₗ W.subtype
  have hmemW : ∀ w : Fin 2 → PadicAlgCl ℓ, e.symm (w, 0) ∈ W := fun w => by
    rw [hW, LinearEquiv.apply_symm_apply]
  let eU : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    { f with
      invFun := fun w => ⟨e.symm (w, 0), hmemW w⟩
      left_inv := fun u => by
        apply Subtype.ext
        change e.symm ((e u).1, 0) = u
        have hu : (e u).2 = 0 := (hW u).mp u.2
        rw [← hu, Prod.mk.eta, LinearEquiv.symm_apply_apply]
      right_inv := fun w => by
        change (e (e.symm (w, 0))).1 = w
        rw [LinearEquiv.apply_symm_apply] }
  have hσ : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (σ : GQ), (∀ x, i (σ x) = τ (i x)) →
      σ = resQ K τ := by
    intro τ σ hστ
    ext x
    apply i.toRingHom.injective
    change i (σ x) = i (resQ K τ x)
    rw [hστ, hi]
  refine ⟨U, eU, ?_, fun τ σ hστ u => ?_⟩
  · intro hbot
    have hmem : e.symm ((Pi.single 0 1 : Fin 2 → PadicAlgCl ℓ), 0) ∈ U.toSubmodule := hmemW _
    rw [hbot] at hmem
    have h0 : e.symm ((Pi.single 0 1 : Fin 2 → PadicAlgCl ℓ), 0) = 0 := hmem
    have h1 := congrArg (fun v => (e v).1 0) h0
    simp at h1
  · rw [hσ τ σ hστ]
    change (e (tate A ℓ τ u)).1 = toRep r (resQ K τ) ((e u).1)
    have h1 := he (resQ K τ) u
    rw [hres τ] at h1
    rw [h1, toRep_apply, Matrix.toLin'_apply]

/-- **G12Spec from g0-mod-galois's outputs (GLUE, proved from `DirichletOfFinite`).** Their
`G8Out` at `ℓ = 5` and `ℓ = 3` and `G12Out r₅` give `i`, `ιC`, `ι₅` such that the data
`⟨i, ιC, ι₅, ι₃, r₅, r₃⟩` satisfy `G12Spec` for **every** `ι₃` (`G12Spec` does not involve `ι₃`).
So `ι₃` can be chosen afterwards, compatibly with `ι₅`, as `G14TraceCompat` requires. -/
theorem g12Spec_of_galois (hDF : DirichletOfFinite) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (ρ5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (ρ3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2)
    (r3 : GaloisRep 3 2) (h5 : GalG8Out A 5 ρ5 r5) (h3 : GalG8Out A 3 ρ3 r3)
    (h12 : GalG12Out r5) :
    ∃ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) (ιC : Qbar →ₐ[ℚ] ℂ)
      (ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5),
      ∀ ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3, G12Spec (⟨i, ιC, ι5, ι3, r5, r3⟩ : ModData K A) := by
  obtain ⟨i0, hi0⟩ := resQ_spec K
  let i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := i0.toRatAlgHom
  have hi : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, i (resQ K τ x) = τ (i x) := hi0
  obtain ⟨ιC, ιL, hpan⟩ := panOutput_of_G12Out hDF r5 h12
  have hirr : ∀ {ℓ : ℕ} [Fact ℓ.Prime] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
      (r : GaloisRep ℓ 2), GalG8Out A ℓ ρ r → r.IsIrreducible := by
    intro ℓ _ ρ r h
    obtain ⟨-, -, -, hadj⟩ := h
    rw [PkgI4.GaloisRep.IsIrreducible, eq_top_iff, ← hadj]
    exact Algebra.adjoin_mono (Set.range_subset_iff.mpr fun σ => ⟨resQ K σ, rfl⟩)
  exact ⟨i, ιC, ιL, fun ι3 => ⟨hirr ρ5 r5 h5, hirr ρ3 r3 h3,
    isConstituentOf_of_GalG8Out A 5 ρ5 r5 h5 i hi, isConstituentOf_of_GalG8Out A 3 ρ3 r3 h3 i hi,
    hpan⟩⟩

end Bridge

/-! ## §10. Local unramifiedness from G11's global form (proved) -/

section LocalGlobal

open PkgI4 (GQp)
open scoped Pointwise

variable (p : ℕ) [Fact p.Prime]

/-- The embedding `ℚ̄ → ℚ̄_p` underlying `PkgI4.decomp p` (Mathlib's
`Field.absoluteGaloisGroup.map`): it intertwines `decomp p σ` with `σ`. -/
theorem decomp_spec : ∃ j : Qbar →+* PadicAlgCl p,
    ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, j (PkgI4.decomp p σ x) = σ (j x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) := g.toAlgebra
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ)
    (AlgebraicClosure ℚ) x

/-- The valuation subring `{x ∈ ℚ̄ : ‖j x‖ ≤ 1}` of the place of `ℚ̄` above `p` given by `j`. -/
def vj (j : Qbar →+* PadicAlgCl p) : ValuationSubring Qbar :=
  (PadicAlgCl.valued p).v.valuationSubring.comap j

theorem mem_vj (j : Qbar →+* PadicAlgCl p) (x : Qbar) : x ∈ vj p j ↔ ‖j x‖ ≤ 1 := by
  rw [vj, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  change ‖j x‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (spectral norm). -/
theorem norm_aut (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p) :
    ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

theorem mem_nonunits_vj (j : Qbar →+* PadicAlgCl p) (b : Qbar) (hb : ‖j b‖ < 1) :
    b ∈ (vj p j).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : b = 0
  · exact Or.inl h0
  · refine Or.inr fun hinv => ?_
    rw [mem_vj, map_inv₀, norm_inv] at hinv
    have hpos : 0 < ‖j b‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h0)
    rw [inv_le_one₀ hpos] at hinv
    linarith

theorem liesOver_vj (j : Qbar →+* PadicAlgCl p) : LiesOver (vj p j) p := by
  apply mem_nonunits_vj
  rw [map_natCast, LadicCond.norm_p_kbar]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- **Global unramified ⇒ local inertia acts trivially (GLUE, proved).** If `r` is unramified at
`p` in PkgI4's global sense (every inertia group of `G_ℚ` at a place above `p` acts trivially),
then `r|G_{ℚ_p}` is trivial on the local inertia set `LadicCond.inertiaSet`. -/
theorem localUnram_of_unramifiedAt {ℓ n : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ n)
    (hr : r.UnramifiedAt p) : ∀ σ ∈ LadicCond.inertiaSet, r.restrictLocal p σ = 1 := by
  obtain ⟨j, hj⟩ := decomp_spec p
  intro σ hσ
  set τ := PkgI4.decomp p σ with hτ
  have hdec : τ ∈ (vj p j).decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_vj, mem_vj, AlgEquiv.smul_def,
      hτ, ← map_inv, hj, norm_aut]
  have hin : (⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) ∈
      (vj p j).inertiaSubgroup ℚ := by
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change (⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • IsLocalRing.residue _ a =
      IsLocalRing.residue _ a
    rw [← IsLocalRing.ResidueField.residue_smul]
    apply Ideal.Quotient.eq.mpr
    have hb : ((⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • a - a : vj p j) =
        ⟨τ a - a, by
          have := ((⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • a - a).2
          exact this⟩ := rfl
    have hnorm : ‖j (τ (a : Qbar) - a)‖ < 1 := by
      rw [map_sub, hτ, hj]
      exact hσ (j a) ((mem_vj p j a).mp a.2)
    obtain ⟨hmem, hmax⟩ :=
      (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp
        (mem_nonunits_vj p j _ hnorm)
    rw [hb]
    exact hmax
  exact hr (vj p j) (liesOver_vj p j) ⟨τ, hdec⟩ hin

end LocalGlobal

/-- `LocalRam` with clause (iii) in G11's global form (`G0Galois.G11Out`: `r.UnramifiedAt p`). -/
def LocalRamG (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → r.UnramifiedAt p)

/-- **Open part of G15, final form.** Clauses (i)-(ii) of `LocalRam` (D1-D4 on G8's `r_ℓ`) and
clause (iii) as G11's output (proved by g0-mod-galois as `g11`, `G0Galois.G11Out`). -/
def G15RamG {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamG u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamG u p ⟨hp⟩ 3 _ D.r3)

theorem g15Ram_of_G {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h : G15RamG D u) : G15Ram D u := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (h p hp).1 h5
    exact ⟨h1, h2, fun hS hM => localUnram_of_unramifiedAt p D.r5 (h3 hS hM)⟩
  · obtain ⟨h1, h2, h3⟩ := (h p hp).2 h5
    exact ⟨h1, h2, fun hS hM => localUnram_of_unramifiedAt p D.r3 (h3 hS hM)⟩

/-- **G13-G16, final form (GLUE, proved).** As `modularConstituent_tail`, with G15's open part
`G15RamG` (D1-D4's ramification statements on G8's `r_ℓ`, and G11's output). -/
theorem modularConstituent_tail_G (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact modularConstituent_tail lv hJac hX hSw hL8 hAd A u ⟨D, h12, hc, g15Ram_of_G D u hram⟩

end G0ModNewform

end

#print axioms G0ModNewform.equivariant_of_asModule
#print axioms G0ModNewform.condAt_eq_of_intertwine
#print axioms G0ModNewform.newform_of_pan
#print axioms G0ModNewform.commonConstituent_of_attached
#print axioms G0ModNewform.g13
#print axioms G0ModNewform.iso_R14
#print axioms G0ModNewform.g14
#print axioms G0ModNewform.g15
#print axioms G0ModNewform.g16
#print axioms G0ModNewform.g13_g16
#print axioms G0ModNewform.g16Out_with_J1
#print axioms G0ModNewform.localBound_of_ram
#print axioms G0ModNewform.g13_g16_ram
#print axioms G0ModNewform.modularConstituent_tail
#print axioms G0ModNewform.isConstituentOf_of_GalG8Out
#print axioms G0ModNewform.g12Spec_of_galois
#print axioms G0ModNewform.localUnram_of_unramifiedAt
#print axioms G0ModNewform.g15Ram_of_G
#print axioms G0ModNewform.modularConstituent_tail_G

/-!
# g14-trace: `G14TraceCompat` (r₃ and r₅ in one compatible system), reduced

`G0ModNewform.G14TraceCompat D` (copied verbatim above, from `scratch/g0-mod-newform/`) is a
statement about the data `D : ModData L A`. It is proved here for the data that G8 constructs
(g0-mod-galois' `G8Out`, copied above as `GalG8Out`) from the descended operators
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` (`GlueDescent.rho`), from:

* the leaf T7 (`PkgI3.CharPolyIndepOfEll`, Mumford §19 Thm 4);
* the AV-side glue Prop `FrobTraceLink A Tm₅ Tm₃` (N5 L781-786: at a Frobenius `τ` above
  `p ∉ S`, `N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian variety
  over a field of characteristic `p`, at `ℓ = 3` and `ℓ = 5`; the kernel's
  `GlueC10Link.FrobCompare`), or its square form `FrobSquaresLink` (the kernel's
  `GlueC10Link.FrobSquares`: Galois transport, Serre–Tate reduction, Néron mapping);
* the scalar link: `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β` for one pair `a, β : G_ℚ → ℚ̄` (N5 L719-722:
  the scalars lie in the coefficient field `C` and are mapped to `ℚ̄_ℓ` by embeddings).

§1 proves that the scalar link is needed: G8's inputs at one `ℓ` (`G7Out`) are preserved by
twisting `a` by a character of `G_ℚ` trivial on `G_{L'}`, which multiplies the traces of `ρ_ℓ`
by the character. So `G14TraceCompat` does not follow from `G7Out` at `3` and at `5` separately
(the form in which g0-mod-field's `TateBridge` delivers them).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link

/-! ## §1. G7Out at one `ℓ` does not fix the traces: twisting `a` (proved) -/

section Twist

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]

/-- (copied from g0-mod-galois, `part_galois.lean`, as in g0-mod-field's `GaloisCopy`)
G7's output at the coefficient prime `ℓ`. -/
def G7Out (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

/-- **Twisting G7's output (proved).** If `χ : G_ℚ → ℚ̄_ℓ^×` is a continuous character trivial on
`G_K` (a character of `Gal(K/ℚ)`), then `(Tm, c, ε, χ·a, β, u)` satisfies `G7Out` whenever
`(Tm, c, ε, a, β, u)` does. -/
theorem g7Out_twist (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : GQ → GQ → PadicAlgCl ℓ) (a β : GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) (h : G7Out A ℓ Tm c ε a β u)
    (χ : GQ →* (PadicAlgCl ℓ)ˣ) (hχc : Continuous χ) (hχ : ∀ σ, χ (resQ K σ) = 1) :
    G7Out A ℓ Tm c ε (fun g => (χ g : PadicAlgCl ℓ) * a g) β u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, fun g k => ?_, h5, h6, fun σ => ?_, h8, fun f v => ?_⟩
  · simp only [map_mul, Units.val_mul]
    linear_combination (χ g : PadicAlgCl ℓ) * (χ k) * h4 g k
  · obtain ⟨t1, t2, t3⟩ := h7 σ
    exact ⟨t1, by simp only [t2, hχ σ, Units.val_one, mul_one], t3⟩
  · have hc : Continuous fun g => (χ g : PadicAlgCl ℓ) :=
      Units.continuous_val.comp hχc
    have : (fun g => f (GlueDescent.rho Tm (fun g => (χ g : PadicAlgCl ℓ) * a g) β g v)) =
        fun g => (χ g : PadicAlgCl ℓ) * f (GlueDescent.rho Tm a β g v) := by
      funext g
      simp only [GlueDescent.rho, LinearMap.smul_apply, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact hc.mul (h9 f v)

/-- The twist multiplies the traces of `ρ = β⁻¹ a Tm` by `χ`. -/
theorem trace_rho_twist (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (a β : GQ → PadicAlgCl ℓ) (χ : GQ → PadicAlgCl ℓ) (g : GQ) :
    LinearMap.trace _ _ (GlueDescent.rho Tm (fun g => χ g * a g) β g) =
      χ g * LinearMap.trace _ _ (GlueDescent.rho Tm a β g) := by
  rw [trace_rho, trace_rho]
  ring

end Twist

/-- **The twist obstruction (proved).** If data `D` and `D'` share `r₅`, `ι₅`, `ι₃`, and the traces
of `D'.r₃` are those of `D.r₃` times `χ`, then `G14TraceCompat` for both forces
`(χ(τ) − 1)·tr r₃(τ) = 0` at almost every arithmetic Frobenius `τ` at which `tr r₅(τ)` is
algebraic (all but finitely many, by G13). So at most one twist of `r₃` by a character of
`Gal(K/ℚ)` can satisfy `G14TraceCompat`, unless `r₃` is isomorphic to its twist; which one is
fixed by the descent data, not by `G7Out` at `ℓ = 3` (`g7Out_twist`). -/
theorem twist_obstruction {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D D' : ModData K A) (h5 : D'.r5 = D.r5) (hι5 : D'.ι5 = D.ι5) (hι3 : D'.ι3 = D.ι3)
    (χ : GQ → PadicAlgCl 3) (htw : ∀ τ, (D'.r3.mat τ).trace = χ τ * (D.r3.mat τ).trace)
    (hc : G14TraceCompat D) (hc' : G14TraceCompat D') :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p → ∀ c : Qbar, (D.r5.mat τ).trace = D.ι5 c →
        (χ τ - 1) * (D.r3.mat τ).trace = 0 := by
  obtain ⟨S, hS⟩ := hc
  obtain ⟨S', hS'⟩ := hc'
  refine ⟨S ∪ S', fun p hp hpS v τ hv hτ c hc5 => ?_⟩
  have h1 := hS p hp (fun h => hpS (Finset.mem_union_left _ h)) v τ hv hτ c hc5
  have h2 := hS' p hp (fun h => hpS (Finset.mem_union_right _ h)) v τ hv hτ c
    (by rw [h5, hι5]; exact hc5)
  rw [htw, hι3, ← h1] at h2
  linear_combination h2

/-! ## §2. Traces through G8's intertwining (proved) -/

/-- If `e : V ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `f g` with `m g ⊕ m g`, then `tr f(g) = 2 tr m(g)`. -/
theorem trace_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (f : G → Module.End (PadicAlgCl ℓ) V)
    (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : Intertwines f m e) (g : G) :
    LinearMap.trace (PadicAlgCl ℓ) V (f g) = 2 * (m g).trace := by
  haveI : Module.Finite (PadicAlgCl ℓ) V := Module.Finite.equiv e.symm
  have hconj : e.conj (f g) = LinearMap.prodMap (Matrix.toLin' (m g)) (Matrix.toLin' (m g)) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h g, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, Matrix.toLin'_apply]
  rw [← LinearMap.trace_conj' (f g) e, hconj, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq]
  ring

/-- One coefficient prime: if `N·tr T = t` and `tr(β⁻¹ a T) = 2 tr m` (images of
`a, β ∈ ℚ̄` under `j`), then `tr m = j(½ β⁻¹ a t/N)`. -/
theorem trace_eq_image {ℓ : ℕ} [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (T : Module.End (PadicAlgCl ℓ) V) (a β : Qbar)
    (N : ℕ) (hN : N ≠ 0) (t : ℤ) (hNT : (N : PadicAlgCl ℓ) * LinearMap.trace _ V T = t)
    (m : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (h2 : LinearMap.trace _ V (((j β)⁻¹ * j a) • T) = 2 * m.trace) :
    m.trace = j ((β)⁻¹ * a * ((t : Qbar) / N) / 2) := by
  have hNE : (N : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hT : LinearMap.trace _ V T = (t : PadicAlgCl ℓ) / N := by
    rw [eq_div_iff hNE, mul_comm, hNT]
  rw [map_smul, smul_eq_mul, hT] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : PadicAlgCl ℓ) * h2

/-! ## §3. The AV-side glue Props -/

/-- **The Frobenius trace link (GLUE, AV side; N5 L781-786).** There is a finite set `S` of
primes such that at every arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety
`Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and `N ≠ 0` with
`FrobCompare` (kernel, `GlueC10Link`) at `ℓ = 3` and at `ℓ = 5`: some isomorphism
`ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')`. In N5, `S = T ∪ {3, 5}`
(`T` = bad primes of `A/L'`), `Ā` is the reduction of `A` at the place `v ∩ L'`, `α' = N·(μ̄_τ ∘ F)`
(relative `p`-Frobenius `F`, reduction `μ̄_τ` of the isogeny `μ_τ : {}^τA → A`, defined over
`L ⊆ L'` by N5 L638-640), and the
isomorphism is the Serre–Tate reduction isomorphism. It concerns the operators `Tm_ℓ` that
g0-mod-field's `TateBridge` builds from the points-level `m_σ = μ_σ ∘ σ` (one `m_σ` for all `ℓ`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The Frobenius link in square form (GLUE, AV side; N5 L781-786).** As `FrobTraceLink`, with
`FrobCompare` replaced by its three inputs (kernel, `GlueC10Link.FrobSquares`): abelian
varieties `A₀, Aσ` over a field `L` (intended instance `A₀ = A`, `Aσ = {}^τA`; they are
existential and tied to `A` only through `Ψ`, so this Prop is no stronger than `FrobTraceLink`),
an isogeny `μ' : Aσ → A₀` (`N μ_τ`), abelian varieties `Ā, Ā'` over `k` of characteristic `p` (`Ā = Ā_v`,
`Ā' = Ā^{(p)}`), the relative Frobenius `F : Ā → Ā'` and the reduction `μ̄' : Ā' → Ā` of `μ'`,
with the three squares (descent instantiation `N·Tm_ℓ(τ) = μ' ∘ τ_*`; Serre–Tate
`red' ∘ τ_* = V_ℓ(F) ∘ red`; Néron mapping `red ∘ V_ℓ(μ') = V_ℓ(μ̄') ∘ red'`) at `ℓ = 3, 5`. -/
def FrobSquaresLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
      ∃ (A₀ Aσ : PkgI3.AbVar L) (mu : PkgI3.AbVar.Hom Aσ A₀) (Ab Ab' : PkgI3.AbVar k)
        (F : PkgI3.AbVar.Hom Ab Ab') (mub : PkgI3.AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
        FrobSquares 3 mu F mub (Tm3 τ) N ∧ FrobSquares 5 mu F mub (Tm5 τ) N

/-- `FrobSquaresLink ⇒ FrobTraceLink` (proved, kernel's `frobCompare_of_frobSquares`). -/
theorem frobTraceLink_of_squares {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (h : FrobSquaresLink A Tm5 Tm3) :
    FrobTraceLink A Tm5 Tm3 := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ => ?_⟩
  obtain ⟨L, _, k, _, hk, A₀, Aσ, mu, Ab, Ab', F, mub, N, hN, h3, h5⟩ := hS p hp hpS v τ hv hτ
  exact ⟨k, inferInstance, hk, Ab, homComp F mub, N, hN,
    frobCompare_of_frobSquares 3 mu F mub (Tm3 τ) N h3,
    frobCompare_of_frobSquares 5 mu F mub (Tm5 τ) N h5⟩

/-! ## §4. One algebraic number for both traces (proved from T7) -/

/-- **The common trace (GLUE, proved from T7, `FrobTraceLink` and the scalar link).** With
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ`, `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and G8's intertwining of `ρ_ℓ` with
`r_ℓ ⊕ r_ℓ` at `ℓ = 3, 5`: outside a finite set, at every arithmetic Frobenius `τ`, the traces of
`r₅(τ)` and `r₃(τ)` are `j₅(x)` and `j₃(x)` for one `x = ½ β(τ)⁻¹ a(τ) tr(α')/N ∈ ℚ̄`. -/
theorem common_trace (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (r5.mat τ).trace = j5 x ∧ (r3.mat τ).trace = j3 x := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨-, e5, he5, -⟩ := h5
  obtain ⟨-, e3, he3, -⟩ := h3
  haveI : Module.Finite (PadicAlgCl 5) (Vb A 5) := Module.Finite.equiv e5.symm
  haveI : Module.Finite (PadicAlgCl 3) (Vb A 3) := Module.Finite.equiv e3.symm
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hp3 : p ≠ 3 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  have hp5 : p ≠ 5 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  obtain ⟨k, _, hk, Ab, α, N, hN, hc3, hc5⟩ := hS p hp hpS1 v τ hv hτ
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM Ab α
  have hk3 : ((3 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp Nat.prime_three hp3
  have hk5 : ((5 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp (by norm_num) hp5
  have t5 := ht 5 hk5 (Tm5 τ) N hc5
  have t3 := ht 3 hk3 (Tm3 τ) N hc3
  refine ⟨(β τ)⁻¹ * a τ * ((t : Qbar) / N) / 2, ?_, ?_⟩
  · refine trace_eq_image j5 (Tm5 τ) (a τ) (β τ) N hN t t5 (r5.mat τ) ?_
    exact trace_of_intertwines _ r5.mat e5 he5 τ
  · refine trace_eq_image j3 (Tm3 τ) (a τ) (β τ) N hN t t3 (r3.mat τ) ?_
    exact trace_of_intertwines _ r3.mat e3 he3 τ

/-! ## §5. Choosing `ι₃` compatibly with Pan's `ι₅` (proved) -/

/-- Any two `ℚ`-embeddings of `ℚ̄` into a field differ by an endomorphism of `ℚ̄`:
`ι = j ∘ γ` (`ι(x)` is a root of the minimal polynomial of `x`, which splits in `j(ℚ̄)`). -/
theorem exists_comp_eq {F : Type*} [Field F] [Algebra ℚ F] (ι j : Qbar →ₐ[ℚ] F) :
    ∃ γ : Qbar →ₐ[ℚ] Qbar, ι = j.comp γ := by
  have hmem : ∀ x : Qbar, ∃ y : Qbar, j y = ι x := by
    intro x
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set P := minpoly ℚ x with hP
    have hP0 : P.map (algebraMap ℚ Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ Qbar)).map (j : Qbar →+* F)).IsRoot (ι x) := by
      rw [Polynomial.map_map, j.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (IsAlgClosed.splits (P.map (algebraMap ℚ Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose γf hγf using hmem
  have hj : Function.Injective j := j.toRingHom.injective
  refine ⟨{ toFun := γf
            map_one' := hj (by rw [hγf, map_one, map_one])
            map_mul' := fun x y => hj (by rw [hγf, map_mul, map_mul, hγf, hγf])
            map_zero' := hj (by rw [hγf, map_zero, map_zero])
            map_add' := fun x y => hj (by rw [hγf, map_add, map_add, hγf, hγf])
            commutes' := fun q => hj (by rw [hγf, AlgHom.commutes, AlgHom.commutes]) }, ?_⟩
  ext x
  exact (hγf x).symm

/-- **`G14TraceCompat` from the common trace (GLUE, proved).** If the traces of `r₅`, `r₃` at
Frobenius are `j₅(x)`, `j₃(x)`, and `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`, then `G14TraceCompat` holds for
any data with these `ι₅, ι₃, r₅, r₃`. -/
theorem g14TraceCompat_of_common {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (γ : Qbar →ₐ[ℚ] Qbar) (h5 : D.ι5 = j5.comp γ) (h3 : D.ι3 = j3.comp γ)
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (D.r5.mat τ).trace = j5 x ∧ (D.r3.mat τ).trace = j3 x) :
    G14TraceCompat D := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ c hc => ?_⟩
  obtain ⟨x, hx5, hx3⟩ := hS p hp hpS v τ hv hτ
  have hxc : x = γ c := by
    apply j5.toRingHom.injective
    change j5 x = j5 (γ c)
    rw [← hx5, hc, h5, AlgHom.comp_apply]
  rw [hx3, hxc, h3, AlgHom.comp_apply]

/-- **G14TraceCompat on G8's construction (GLUE, proved from T7, `FrobTraceLink` and the scalar
link).** For data `D` whose `r₅`, `r₃` are G8's outputs on `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` with
`a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and whose embeddings are `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`. -/
theorem g14TraceCompat_of_link (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar) (hι5 : D.ι5 = j5.comp γ)
    (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D :=
  g14TraceCompat_of_common D j5 j3 γ hι5 hι3
    (common_trace hM A j5 j3 a β Tm5 Tm3 D.r5 D.r3 h5 h3 hF)

/-! ## §6. With G12: data satisfying both `G12Spec` and `G14TraceCompat` (proved) -/

/-- **`G12Spec D ∧ G14TraceCompat D` from G8 at `3` and `5`, G12 at `5`, T7, `FrobTraceLink` and
the scalar link (GLUE, proved; with g0-mod-newform's `DirichletOfFinite`).** The embedding
`ι₅` is the one from Pan's output (`g12Spec_of_galois`); `ι₃ := j₃ ∘ γ` where `ι₅ = j₅ ∘ γ`
(`exists_comp_eq`). The data keep G8's `r₅`, `r₃`. -/
theorem g12Spec_g14_of_galois (hDF : DirichletOfFinite) (hM : CharPolyIndepOfEll) {K : Type}
    [Field K] [NumberField K] (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (h12 : GalG12Out r5) (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ D : ModData K A, D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D := by
  obtain ⟨i, ιC, ι5, hspec⟩ := g12Spec_of_galois hDF A _ _ r5 r3 h5 h3 h12
  obtain ⟨γ, hγ⟩ := exists_comp_eq ι5 j5
  refine ⟨⟨i, ιC, ι5, j3.comp γ, r5, r3⟩, rfl, rfl, hspec _, ?_⟩
  exact g14TraceCompat_of_link hM _ j5 j3 γ hγ rfl a β Tm5 Tm3 h5 h3 hF

/-- **From linked G7 data (GLUE, proved).** The `A`-level form of `G14Bridge.TateBridge35`'s
conclusion (`G7Out` at 5 and 3 with scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, and `FrobTraceLink`), with
g0-mod-galois' G8-G12 as the hypotheses `hG5` (their `g8_g12` at `ℓ = 5`: `G8Out ∧ G12Out`) and
`hG3` (their `g8_g11` at `ℓ = 3`: `G8Out`), gives G8's `r₅`, `r₃` (with their `G8Out`, so that
`G15RamG` can be proved for them) and data `D` carrying them with `G12Spec ∧ G14TraceCompat`. -/
theorem g12Spec_g14_of_linked (hDF : DirichletOfFinite) (hM : CharPolyIndepOfEll) {K : Type}
    [Field K] [NumberField K] (A : PkgI3.AbVar K) (a β : GQ → Qbar)
    (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5)) (c5 ε5 : GQ → GQ → PadicAlgCl 5)
    (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (c3 ε3 : GQ → GQ → PadicAlgCl 3)
    (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3) (Vb A 3))
    (h75 : G7Out A 5 Tm5 c5 ε5 (fun g => j5 (a g)) (fun g => j5 (β g)) u5)
    (h73 : G7Out A 3 Tm3 c3 ε3 (fun g => j3 (a g)) (fun g => j3 (β g)) u3)
    (hF : FrobTraceLink A Tm5 Tm3)
    (hG5 : G7Out A 5 Tm5 c5 ε5 (fun g => j5 (a g)) (fun g => j5 (β g)) u5 →
      ∃ r5 : GaloisRep 5 2,
        GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5 ∧
        GalG12Out r5)
    (hG3 : G7Out A 3 Tm3 c3 ε3 (fun g => j3 (a g)) (fun g => j3 (β g)) u3 →
      ∃ r3 : GaloisRep 3 2,
        GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3) :
    ∃ (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2) (D : ModData K A),
      GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5 ∧
      GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3 ∧
      D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D := by
  obtain ⟨r5, h5, h12⟩ := hG5 h75
  obtain ⟨r3, h3⟩ := hG3 h73
  obtain ⟨D, hD5, hD3, hs, hc⟩ :=
    g12Spec_g14_of_galois hDF hM A j5 j3 a β Tm5 Tm3 r5 r3 h5 h3 h12 hF
  exact ⟨r5, r3, D, h5, h3, hD5, hD3, hs, hc⟩

end G14Trace

end

#print axioms G14Trace.g7Out_twist
#print axioms G14Trace.trace_rho_twist
#print axioms G14Trace.twist_obstruction
#print axioms G14Trace.trace_of_intertwines
#print axioms G14Trace.trace_eq_image
#print axioms G14Trace.frobTraceLink_of_squares
#print axioms G14Trace.common_trace
#print axioms G14Trace.exists_comp_eq
#print axioms G14Trace.g14TraceCompat_of_common
#print axioms G14Trace.g14TraceCompat_of_link
#print axioms G14Trace.g12Spec_g14_of_galois
#print axioms G14Trace.g12Spec_g14_of_linked

/-! Copied verbatim from scratch/g15-ram/G15Ram.lean (G0Galois block, §1-§3). -/
noncomputable section
namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Output of G11:** `r` is unramified at every prime outside `T ∪ {ℓ}`. -/
def G11Out {ℓ : ℕ} [Fact ℓ.Prime] (T : Finset ℕ) (r : GaloisRep ℓ 2) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → r.UnramifiedAt p

end G0Galois
/-! ## §1. The smaller named Props -/

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

section Local

variable (p : ℕ) [Fact p.Prime]

/-- **Glue: T20 + T21 transported to `ℚ̄_p`** (Hilbert's formula for the different, Serre,
*Corps locaux* IV §1 Prop. 4, and Serre's bound `v_F(𝔇) ≤ e − 1 + v_F(e)`, III §6 remark after
Prop. 13; UNVERIFIED numbering). For a finite Galois `F ⊆ ℚ̄_p` with lower ramification groups
`G_i = ramSet F i` (pulled back to `G_{ℚ_p}`) and `g_i = ramCard F i`, some `G_n` is trivial and
`∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)` with `e = g_0`. Both parts are proved by t-different over
complete DVRs (`PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound`). This Prop is derived
below from them and the transport `LadicDVRModel` (`hilbertSerre_of_model`). The existence of
`n` alone is already proved (`LadicCond.eventuallyTrivial`). -/
def HilbertSerreLadic : Prop :=
  ∀ F : Fld p, IsFinGal F → ∃ n : ℕ, ramSet F n ⊆ fixSet F ∧
    ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0)

/-- **Glue (D1 at the level of `upperAbs`; N5 L796-812, L824-827).** For a finite Galois
`F ⊆ ℚ̄_p` with ramification index `e(F/ℚ_p) ≤ a!`, every absolute upper ramification group
`G_{ℚ_p}^t` with `t > 4a²` fixes `F`. Proved below from `HilbertSerreLadic`
(`upperBreakFix_of_hilbertSerre`). -/
def UpperBreakFix : Prop :=
  ∀ F : Fld p, IsFinGal F → ∀ a : ℕ, 1 ≤ a → ramCard F 0 ≤ a.factorial →
    ∀ t : ℝ, 4 * (a : ℝ) ^ 2 < t → upperAbs p t ⊆ fixSet F

/-- **Glue (Serre, *Corps locaux* IV §3: `G^t ⊆ G^0`'s wild part for `t > 0`; UNVERIFIED
numbering).** For `t > 0` every element of `G_{ℚ_p}^t` lies in wild inertia: `|σx − x| < |x|`
for all `x ≠ 0`. (Proof: take `F` = the Galois closure of `ℚ_p(x)`; `σ|_F ∈ G^t(F) = G_{ψ(t)}(F)`
with `ψ(t) > 0`, so `σ|_F ∈ G_1(F)`, and `σx/x ≡ 1 mod 𝔪_F` because `|F^×| = |ϖ|^ℤ`.)
Proved below (`upperWild`). -/
def UpperWild : Prop :=
  ∀ t : ℝ, 0 < t → upperAbs p t ⊆ wildSet

/-- **Glue (tame extensions; Serre, *Corps locaux* IV §2, Cor. 1-4 of Prop. 7: `G_1` is the
`p`-Sylow subgroup of `G_0`; UNVERIFIED numbering).** If `F ⊆ ℚ̄_p` is finite Galois and `p` does
not divide `e(F/ℚ_p)`, wild inertia fixes `F`. Proved below (`wildFixTame`). -/
def WildFixTame : Prop :=
  ∀ F : Fld p, IsFinGal F → ¬ p ∣ ramCard F 0 → wildSet ⊆ fixSet F

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G8's construction (G8 + G3 + R6 + D2; N5 L719-727, L819-823).** On `G_F ∩ P_p`
the representation `r` is the scalar `β(σ)` (`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ` with `a_σ μ_σ = 1`
on `G_L ⊇ G_F`, and the Tate action of `A` trivial on `P_p ∩ G_F`: by Raynaud's criterion (R6)
`A` is semistable over `F ⊇ L_v(A[3])` (`A[5]` if `p = 3`), and then wild inertia acts trivially
(D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D` by good reduction (G3) and
Néron–Ogg–Shafarevich). Here `β` is the local twist (the inverse of Glazer's `β`). -/
def TwistShape (r : GaloisRep ℓ 2) (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet,
    ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
      Matrix.scalar (Fin 2) (β σ)

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** The local twist is trivial on
`G_{ℚ_p}^t ∩ G_F` for `t > U`: at odd `p`, `β|_{G_F}` is trivial on wild inertia (its square is
the tame `χ`, and a pro-`p` group has no quotient of order two;
`GlueConductor.char_trivial_of_odd_pgroup`);
at `p = 2`, local reciprocity with the upper numbering theorem (T16) and `(U_F^{e+1})⁴ = U_F^{3e+1}`
(D3, `GlueConductor.fourth_pow_mem`) bound the relative upper break of `β` by `3e`, and
`ψ_{F/ℚ_2}(u) ≥ u` moves it to the absolute numbering; `max(4D², 3e) ≤ U₀`
(`GlueConductor.max_le_U0`). -/
def TwistUpper (F : Fld p) (β : GQp p → PadicAlgCl ℓ) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β σ = 1

/-- **Glue on G7's `β` at tame primes (N5 L848-851).** `β` is trivial on `P_p ∩ G_F` (for odd
`p`: `β²` is tame, `GlueConductor.char_trivial_of_odd_pgroup`). -/
def TwistTame (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β σ = 1

/-- **G8-G7 local data at `p ≤ D`** (N5 L819-844): `F` the Galois closure of `L_v(A[3])`
(`A[5]` if `p = 3`), of degree `≤ (DG₀)!`, so `e(F/ℚ_p) ≤ (DG₀)!`; the local twist `β`. -/
def SmallPrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧
    ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
    TwistShape p r F β ∧ TwistUpper p F β U0

/-- **G8-G7 local data at `p > D`** (N5 L848-851): `F` the Galois closure of `L_v`, tame since
`[L_v:ℚ_p] ≤ D < p` (the Galois closure of a tame extension is tame); the local twist `β`. -/
def LargePrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
    TwistShape p r F β ∧ TwistTame p F β

/-- The local data at `p` for `r`, by the size of `p`. -/
def LocalData (r : GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → SmallPrimeData p r) ∧
    ((ZInQ.heightD : ℝ) < p → LargePrimeData p r)

end Local

/-! ## §2. Local field: the break bound at the level of `upperAbs` (proved) -/

section Break

variable {p : ℕ} [Fact p.Prime] {F : Fld p}

theorem ramSet_anti {i j : ℕ} (h : i ≤ j) : ramSet F j ⊆ ramSet F i := by
  rintro σ ⟨ϖ, hϖ, hσ⟩
  refine ⟨ϖ, hϖ, fun x hx hx1 => (hσ x hx hx1).trans ?_⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

theorem card_image_mono (hF : IsFinGal F) {S T : Set (GQp p)} (h : S ⊆ T) :
    Nat.card (restr F '' S) ≤ Nat.card (restr F '' T) :=
  Nat.card_mono (finite_restr hF T) (Set.image_mono h)

theorem ramCard_anti (hF : IsFinGal F) : Antitone (ramCard F) := fun _ _ h =>
  card_image_mono hF (ramSet_anti h)

theorem one_le_ramCard (hF : IsFinGal F) (i : ℕ) : 1 ≤ ramCard F i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  exact Nat.one_le_iff_ne_zero.mpr (ramCard_ne_zero hF hϖ i)

/-- If `g_i ≤ 1`, then `G_i` (pulled back) fixes `F`. -/
theorem fix_of_ramCard_le_one (hF : IsFinGal F) {i : ℕ} (h : ramCard F i ≤ 1) :
    ramSet F i ⊆ fixSet F := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  have hfin : Finite (restr F '' ramSet F i) := (finite_restr hF (ramSet F i)).to_subtype
  have hsub : Subsingleton (restr F '' ramSet F i) := Finite.card_le_one_iff_subsingleton.mp h
  have h1 : (1 : GQp p) ∈ ramSet F i := fixSet_subset_ramSet hϖ i (fun x _ => rfl)
  intro σ hσ x hx
  have he : (⟨restr F σ, σ, hσ, rfl⟩ : restr F '' ramSet F i) = ⟨restr F 1, 1, h1, rfl⟩ :=
    Subsingleton.elim _ _
  have := congrFun (congrArg Subtype.val he) ⟨x, hx⟩
  exact this

theorem ramCardR_of_gt {t : ℝ} (ht : -1 < t) : ramCardR F t = ramCard F ⌈t⌉.toNat := by
  unfold ramCardR ramSetR
  rw [if_neg (not_le.mpr ht)]
  rfl

theorem ramCardR_anti (hF : IsFinGal F) : Antitone (ramCardR F) := by
  intro s t hst
  unfold ramCardR ramSetR
  by_cases ht : t ≤ -1
  · have hs : s ≤ -1 := hst.trans ht
    rw [if_pos ht, if_pos hs]
  · rw [if_neg ht]
    by_cases hs : s ≤ -1
    · rw [if_pos hs]
      exact card_image_mono hF (Set.subset_univ _)
    · rw [if_neg hs]
      exact card_image_mono hF (ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono hst)))

/-- The integrand of Herbrand's `φ` (`phiAt`). -/
def gInt (F : Fld p) (t : ℝ) : ℝ := (ramCardR F t : ℝ) / (ramCard F 0 : ℝ)

theorem phiAt_eq (u : ℝ) : phiAt F u = ∫ t in (0 : ℝ)..u, gInt F t := rfl

theorem gInt_anti (hF : IsFinGal F) : Antitone (gInt F) := fun _ _ h =>
  div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_anti hF h) (Nat.cast_nonneg _)

theorem gInt_int (hF : IsFinGal F) (a b : ℝ) :
    IntervalIntegrable (gInt F) MeasureTheory.volume a b :=
  (gInt_anti hF).intervalIntegrable

theorem g0_pos (hF : IsFinGal F) : (0 : ℝ) < ramCard F 0 := by
  exact_mod_cast one_le_ramCard hF 0

theorem gInt_le_one (hF : IsFinGal F) {t : ℝ} (ht : -1 < t) : gInt F t ≤ 1 := by
  rw [gInt, div_le_one (g0_pos hF), ramCardR_of_gt ht]
  exact_mod_cast ramCard_anti hF (Nat.zero_le _)

theorem gInt_ge (hF : IsFinGal F) (t : ℝ) : 1 / (ramCard F 0 : ℝ) ≤ gInt F t := by
  have h1 : 1 ≤ ramCardR F t := by
    have h0 : -1 < max t 0 := lt_of_lt_of_le (by norm_num) (le_max_right t 0)
    have := ramCardR_anti hF (le_max_left t 0)
    rw [ramCardR_of_gt h0] at this
    exact (one_le_ramCard hF _).trans this
  exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (Nat.cast_nonneg _)

theorem gInt_nonneg (hF : IsFinGal F) (t : ℝ) : 0 ≤ gInt F t :=
  le_trans (by have := g0_pos hF; positivity) (gInt_ge hF t)

theorem phi_mono (hF : IsFinGal F) {u w : ℝ} (h : u ≤ w) : phiAt F u ≤ phiAt F w := by
  have h1 := intervalIntegral.integral_interval_sub_left (gInt_int hF 0 w) (gInt_int hF 0 u)
  have h2 : 0 ≤ ∫ t in u..w, gInt F t :=
    intervalIntegral.integral_nonneg h (fun x _ => gInt_nonneg hF x)
  rw [phiAt_eq, phiAt_eq]
  linarith

theorem phi_sub_le (hF : IsFinGal F) {w u : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    phiAt F u - phiAt F w ≤ u - w := by
  rw [phiAt_eq, phiAt_eq,
    intervalIntegral.integral_interval_sub_left (gInt_int hF _ _) (gInt_int hF _ _)]
  calc ∫ t in w..u, gInt F t ≤ ∫ _ in w..u, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hwu (gInt_int hF _ _) intervalIntegrable_const
          (fun x hx => gInt_le_one hF (by linarith [hx.1]))
    _ = u - w := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

theorem phi_ge (hF : IsFinGal F) {u : ℝ} (hu : 0 ≤ u) :
    u * (1 / (ramCard F 0 : ℝ)) ≤ phiAt F u := by
  rw [phiAt_eq]
  calc u * (1 / (ramCard F 0 : ℝ)) = ∫ _ in (0 : ℝ)..u, (1 / (ramCard F 0 : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ ∫ t in (0 : ℝ)..u, gInt F t :=
        intervalIntegral.integral_mono_on hu intervalIntegrable_const (gInt_int hF _ _)
          (fun x _ => gInt_ge hF x)

theorem phi_nat (hF : IsFinGal F) (m : ℕ) :
    phiAt F m = ∑ k ∈ Finset.range m, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
  rw [phiAt_eq]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := gInt F) (a := fun k : ℕ => (k : ℝ)) (n := m) (fun k _ => gInt_int hF _ _)
  simp only [Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have : ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), gInt F x =
      ∫ _ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le hk] at hx
    have hx1 := hx.1
    have hx2 := hx.2
    push_cast at hx2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hxm : -1 < x := by linarith
    have hc : ⌈x⌉ = ((k + 1 : ℕ) : ℤ) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    simp only [gInt]
    rw [ramCardR_of_gt hxm, hc, Int.toNat_natCast]
  rw [this, intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

theorem phi_eq_sum (g : ℕ → ℕ) (m : ℕ) :
    GlueConductor.phi g m = ∑ k ∈ Finset.range m, (g (k + 1) : ℚ) / g 0 := by
  induction m with
  | zero => rw [GlueConductor.phi_zero, Finset.sum_range_zero]
  | succ m ih => rw [GlueConductor.phi_succ, ih, Finset.sum_range_succ]

/-- **D1 at the level of `upperAbs` (GLUE, proved from `HilbertSerreLadic`).** -/
theorem upperBreakFix_of_hilbertSerre (h : HilbertSerreLadic p) : UpperBreakFix p := by
  classical
  intro F hF a ha hea t ht σ hσ
  have hex : ∃ n, ramSet F n ⊆ fixSet F ∧ ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) := h F hF
  have hex' : ∃ n, ramSet F n ⊆ fixSet F := let ⟨n, hn, _⟩ := hex; ⟨n, hn⟩
  set n := Nat.find hex' with hn_def
  have hnfix : ramSet F n ⊆ fixSet F := Nat.find_spec hex'
  obtain ⟨N, hN, hsum⟩ := hex
  have hnN : n ≤ N := Nat.find_min' hex' hN
  have hsum' : ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) :=
    (Finset.sum_le_sum_of_subset (Finset.range_mono hnN)).trans hsum
  set w : ℕ := n - 1 with hw
  have ha2 : (0 : ℝ) ≤ 4 * (a : ℝ) ^ 2 := by positivity
  have hφw : phiAt F w < t := by
    have h4 : phiAt F w ≤ 4 * (a : ℝ) ^ 2 := by
      by_cases hn1 : n ≤ 1
      · have hw0 : w = 0 := by omega
        rw [hw0, Nat.cast_zero, phiAt_eq, intervalIntegral.integral_same]
        exact ha2
      · have hb : ¬ ramSet F w ⊆ fixSet F := Nat.find_min hex' (by omega)
        have hgb : 2 ≤ ramCard F w := by
          by_contra hlt
          exact hb (fix_of_ramCard_le_one hF (by omega))
        have hub := GlueConductor.upper_break_le p a (Fact.out) ha (ramCard F)
          (ramCard_anti hF) (one_le_ramCard hF) w n hgb (by omega) hea hsum'
        rw [phi_nat hF]
        have hcast : ((GlueConductor.phi (ramCard F) w : ℚ) : ℝ) =
            ∑ k ∈ Finset.range w, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
          rw [phi_eq_sum]
          push_cast
          rfl
        rw [← hcast]
        exact_mod_cast hub
    linarith
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have ht0 : 0 < t := by linarith
  have hg0 := g0_pos hF
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hne : S.Nonempty := by
    refine ⟨w + t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := w + t * ramCard F 0) (by positivity)
    have h2 : t ≤ (w + t * ramCard F 0) * (1 / (ramCard F 0 : ℝ)) := by
      rw [add_mul, mul_one_div, mul_one_div, mul_div_assoc, div_self hg0.ne', mul_one]
      have : (0 : ℝ) ≤ w / ramCard F 0 := div_nonneg hw0 hg0.le
      linarith
    exact h2.trans h1
  have hlb : ∀ u ∈ S, (w : ℝ) + (t - phiAt F w) ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases huw : u ≤ w
    · exact absurd (hu.trans (phi_mono hF huw)) (not_le.mpr hφw)
    · have := phi_sub_le hF hw0 (le_of_not_ge huw)
      linarith
  have hψ : (w : ℝ) < sInf S := lt_of_lt_of_le (by linarith) (le_csInf hne hlb)
  have hσF : σ ∈ ramSetR F (sInf S) := hσ F hF
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  apply hnfix
  refine ramSet_anti ?_ hσF
  have hz : ((w : ℕ) : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by exact_mod_cast hψ)
  omega

end Break

/-! ## §2b. Positive upper groups are wild (proved) -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (copied from g0-mod-newform's `norm_aut`). -/
theorem norm_aut' (σ : GQp p) (y : Kbar p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

/-- For `t > 0`, `G^t(F) ⊆ G_1(F)` (pulled back): `ψ_F(t) > 0`. -/
theorem ramSet_one_of_upperSet {F : Fld p} (hF : IsFinGal F) {t : ℝ} (ht : 0 < t) {σ : GQp p}
    (hσ : σ ∈ upperSet F t) : σ ∈ ramSet F 1 := by
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have hg0 := g0_pos hF
  have hφ0 : phiAt F 0 = 0 := by rw [phiAt_eq, intervalIntegral.integral_same]
  have hne : S.Nonempty := by
    refine ⟨t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := t * ramCard F 0) (by positivity)
    have h2 : t * ramCard F 0 * (1 / (ramCard F 0 : ℝ)) = t := by field_simp
    linarith
  have hlb : ∀ u ∈ S, t ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases hu0 : u ≤ 0
    · have := phi_mono hF hu0
      linarith
    · have := phi_sub_le hF le_rfl (le_of_not_ge hu0)
      linarith
  have hψ : t ≤ sInf S := le_csInf hne hlb
  have hσF : σ ∈ ramSetR F (sInf S) := hσ
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  refine ramSet_anti ?_ hσF
  have hz : (0 : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
  omega

/-- The predicate "`σ x / x ≡ 1`": `‖σ x − x‖ < ‖x‖`. -/
def WildAt (σ : GQp p) (y : Kbar p) : Prop := ‖σ y - y‖ < ‖y‖

theorem wildAt_mul {σ : GQp p} {y z : Kbar p} (hy : WildAt σ y) (hz : WildAt σ z) :
    WildAt σ (y * z) := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg _) hz
  have he : σ (y * z) - y * z = σ y * (σ z - z) + (σ y - y) * z := by rw [map_mul]; ring
  rw [he, norm_mul y z]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_aut']
    exact mul_lt_mul_of_pos_left hz hy0
  · rw [norm_mul]
    exact mul_lt_mul_of_pos_right hy hz0

theorem wildAt_inv {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) : WildAt σ y⁻¹ := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hy0' : y ≠ 0 := norm_pos_iff.mp hy0
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy0'
  have he : σ y⁻¹ - y⁻¹ = (y - σ y) / (σ y * y) := by
    rw [map_inv₀]; field_simp
  rw [he, norm_div, norm_mul, norm_aut', norm_sub_rev, norm_inv,
    div_lt_iff₀ (by positivity)]
  calc ‖σ y - y‖ < ‖y‖ := hy
    _ = ‖y‖⁻¹ * (‖y‖ * ‖y‖) := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := by
  unfold WildAt; simp

theorem wildAt_pow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (n : ℕ) : WildAt σ (y ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact wildAt_one σ
  | succ n ih => rw [pow_succ]; exact wildAt_mul ih hy

theorem wildAt_zpow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (k : ℤ) : WildAt σ (y ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact wildAt_pow hy n
  · rw [zpow_neg, zpow_natCast]; exact wildAt_inv (wildAt_pow hy n)

theorem natCast_mem (F : Fld p) : (p : Kbar p) ∈ F := by
  rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
  exact IntermediateField.algebraMap_mem _ _

/-- An element of `G_1(F)` (pulled back) satisfies `σx/x ≡ 1` for every `x ∈ F^×`. -/
theorem wild_of_ramSet_one {F : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet F 1) {x : Kbar p}
    (hx : x ∈ F) (hx0 : x ≠ 0) : ‖σ x - x‖ < ‖x‖ := by
  obtain ⟨ϖ, hϖ, h1⟩ := hσ
  have hϖ1 : ‖ϖ‖ < 1 := hϖ.2.1
  have hϖpos : 0 < ‖ϖ‖ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
    have hp := hϖ.2.2 _ (natCast_mem F) hpn
    exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hϖpos
  -- `ϖ` and the units of `F` satisfy `WildAt`
  have hwϖ : WildAt σ ϖ := by
    unfold WildAt
    have := h1 ϖ hϖ.1 hϖ1.le
    calc ‖σ ϖ - ϖ‖ ≤ ‖ϖ‖ ^ (1 + 1) := this
      _ < ‖ϖ‖ := by rw [pow_two]; exact mul_lt_of_lt_one_right hϖpos hϖ1
  have hwu : ∀ z ∈ F, ‖z‖ = 1 → WildAt σ z := by
    intro z hz hz1
    unfold WildAt
    rw [hz1]
    calc ‖σ z - z‖ ≤ ‖ϖ‖ ^ (1 + 1) := h1 z hz hz1.le
      _ < 1 := pow_lt_one₀ (norm_nonneg _) hϖ1 (by norm_num)
  -- discreteness: `x = ϖ^k z` with `‖z‖ = 1`
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxpos ((one_lt_inv₀ hϖpos).mpr hϖ1)
  set k : ℤ := -(n + 1) with hk
  set z := x * (ϖ ^ k)⁻¹ with hz
  have hzF : z ∈ F := mul_mem hx (inv_mem (zpow_mem hϖ.1 k))
  have hnk : ‖ϖ ^ k‖ = ‖ϖ‖⁻¹ ^ (n + 1) := by
    rw [norm_zpow, hk, zpow_neg, inv_zpow]
  have hnk' : ‖ϖ‖⁻¹ ^ n = ‖ϖ ^ k‖ * ‖ϖ‖ := by
    rw [hnk, zpow_add₀ (inv_ne_zero hϖpos.ne'), zpow_one, mul_assoc,
      inv_mul_cancel₀ hϖpos.ne', mul_one]
  have hpk : 0 < ‖ϖ ^ k‖ := by rw [hnk]; positivity
  have hz_le : ‖z‖ ≤ 1 := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpk, hnk]
    exact hn2
  have hz_gt : ‖ϖ‖ < ‖z‖ := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, lt_div_iff₀ hpk]
    rw [hnk'] at hn1
    linarith [mul_comm ‖ϖ ^ k‖ ‖ϖ‖]
  have hz1 : ‖z‖ = 1 := by
    by_contra hne
    exact absurd (hϖ.2.2 z hzF (lt_of_le_of_ne hz_le hne)) (not_le.mpr hz_gt)
  have hxz : x = ϖ ^ k * z := by
    rw [hz, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero k hϖ0), one_mul]
  have := wildAt_mul (wildAt_zpow hwϖ k) (hwu z hzF hz1)
  rw [← hxz] at this
  exact this

instance isGalois_Kbar : IsGalois ℚ_[p] (Kbar p) := ⟨⟩

/-- **`UpperWild` (GLUE, proved).** For `t > 0`, `G_{ℚ_p}^t ⊆ P_p`. -/
theorem upperWild : UpperWild p := by
  intro t ht σ hσ x hx0
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  exact wild_of_ramSet_one (ramSet_one_of_upperSet hF ht (hσ _ hF)) hxF hx0

end Wild

/-! ## §2d. Wild inertia fixes tame extensions (proved) -/

section Tame

variable {p : ℕ} [Fact p.Prime]

theorem wildSet_mul {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) : σ * τ ∈ wildSet := by
  intro x hx
  have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
  have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [he]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  have := hσ (τ x) hτx
  rwa [norm_aut'] at this

theorem wildSet_pow {σ : GQp p} (hσ : σ ∈ wildSet) (k : ℕ) : σ ^ k ∈ wildSet := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ k ih => rw [pow_succ]; exact wildSet_mul ih hσ

theorem norm_natCast_kbar {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have h := PadicAlgCl.norm_extends p (m : ℚ_[p])
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [e] at h
  rw [h, Padic.norm_natCast_eq_one_iff]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)

/-- In an ultrametric normed group, a finite sum of terms of norm `< c` has norm `< c`. -/
theorem norm_sum_range_lt {f : ℕ → Kbar p} {c : ℝ} (hc : 0 < c) (m : ℕ)
    (hf : ∀ k < m, ‖f k‖ < c) : ‖∑ k ∈ Finset.range m, f k‖ < c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (ih fun k hk => hf k (by omega)) (hf m (by omega)))

/-- **The averaging argument.** A wild `σ` with `σ^m x = x`, `p ∤ m`, fixes `x`. -/
theorem fix_of_wild_pow {σ : GQp p} (hσ : σ ∈ wildSet) {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    {x : Kbar p} (hx : (σ ^ m) x = x) : σ x = x := by
  set S := ∑ k ∈ Finset.range m, (σ ^ k) x with hS
  have hσS : σ S = S := by
    have h1 : σ S = ∑ k ∈ Finset.range m, (σ ^ (k + 1)) x := by
      rw [hS, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun k => (σ ^ k) x) m
    have h3 := Finset.sum_range_succ (fun k => (σ ^ k) x) m
    simp only [pow_zero, AlgEquiv.one_apply] at h2
    rw [hx] at h3
    rw [h1]
    rw [← hS] at h3
    linear_combination -(h3.symm.trans h2)
  have hkS : ∀ k : ℕ, (σ ^ k) S = S := by
    intro k
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσS]
  have hm : (m : Kbar p) ≠ 0 := by
    intro h
    have := norm_natCast_kbar (p := p) hpm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set y := (m : Kbar p)⁻¹ * S with hy
  have hky : ∀ k : ℕ, (σ ^ k) y = y := by
    intro k
    rw [hy, map_mul, map_inv₀, map_natCast, hkS]
  set z := x - y with hz
  have hz0 : z = 0 := by
    by_contra hne
    have hsum : ∑ k ∈ Finset.range m, (z - (σ ^ k) z) = (m : Kbar p) * z := by
      have hterm : ∀ k ∈ Finset.range m, z - (σ ^ k) z = x - (σ ^ k) x := by
        intro k _
        rw [hz, map_sub, hky]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hS, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, hz, hy, mul_sub, ← mul_assoc, mul_inv_cancel₀ hm,
        one_mul]
    have hlt : ‖∑ k ∈ Finset.range m, (z - (σ ^ k) z)‖ < ‖z‖ := by
      apply norm_sum_range_lt (norm_pos_iff.mpr hne)
      intro k _
      rw [norm_sub_rev]
      exact wildSet_pow hσ k z hne
    rw [hsum, norm_mul, norm_natCast_kbar hpm, one_mul] at hlt
    exact lt_irrefl _ hlt
  have hxy : x = y := sub_eq_zero.mp hz0
  rw [hxy]
  have := hky 1
  rwa [pow_one] at this

/-- The inertia subgroup at level `F`, pulled back: `{σ | ‖σx − x‖ < 1 for x ∈ 𝓞_F}`. -/
def inertiaSub (F : Fld p) (hF : IsFinGal F) : Subgroup (GQp p) where
  carrier := {σ | ∀ x ∈ F, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
  one_mem' := by
    intro x _ _
    simp
  mul_mem' := by
    intro σ τ hσ hτ x hx hx1
    have hτx : τ x ∈ F := apply_mem hF τ hx
    have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [he]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx hx1))
    exact hσ (τ x) hτx (by rw [norm_aut']; exact hx1)
  inv_mem' := by
    intro σ hσ x hx hx1
    have hσx : σ⁻¹ x ∈ F := apply_mem hF σ⁻¹ hx
    have h1 : ‖σ⁻¹ x‖ ≤ 1 := by rw [norm_aut']; exact hx1
    have h2 := hσ (σ⁻¹ x) hσx h1
    have he : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [he, norm_sub_rev] at h2
    exact h2

theorem ramSet_zero_eq (F : Fld p) (hF : IsFinGal F) :
    ramSet F 0 = (inertiaSub F hF : Set (GQp p)) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  ext σ
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx hx1
    have := h x hx hx1
    rw [zero_add, pow_one] at this
    exact lt_of_le_of_lt this hϖ'.2.1
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    rw [zero_add, pow_one]
    exact hϖ.2.2 _ (F.sub_mem (apply_mem hF σ hx) hx) (h x hx hx1)

/-- `e(F/ℚ_p) = |G_0|` as the order of a subgroup of `Gal(F/ℚ_p)`. -/
theorem ramCard_zero_eq (F : Fld p) (hF : IsFinGal F) :
    haveI : Normal ℚ_[p] F := hF.2.to_normal
    ramCard F 0 =
      Nat.card ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F)) := by
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    have := congrFun h x
    exact this
  have himg : restr F '' ramSet F 0 =
      φ '' ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) : Set _) := by
    rw [ramSet_zero_eq F hF, Subgroup.coe_map, Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    simp only [hφ, restr]
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj]
  rfl

/-- **`WildFixTame` (GLUE, proved).** If `F/ℚ_p` is finite Galois with `p ∤ e(F/ℚ_p)`, wild
inertia fixes `F`. The restriction `s` of a wild `σ` lies in the inertia subgroup, of order `e`,
so its order `m` is prime to `p`; the averaging `y = m⁻¹ ∑_{k<m} σ^k x` then gives `σx = x`. -/
theorem wildFixTame : WildFixTame p := by
  intro F hF hpe σ hσ x hx
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set s := AlgEquiv.restrictNormalHom F σ with hs
  have hσI : σ ∈ inertiaSub F hF := by
    intro y _ hy1
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact lt_of_lt_of_le (hσ y hy0) hy1
  have hsK : s ∈ (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) := ⟨σ, hσI, rfl⟩
  have hdvd : orderOf s ∣ ramCard F 0 := by
    rw [ramCard_zero_eq F hF]
    have := orderOf_dvd_natCard (⟨s, hsK⟩ : (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F))
    rwa [Subgroup.orderOf_mk] at this
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  have hm0 : 0 < orderOf s :=
    Nat.pos_of_ne_zero fun h => he0 (by rw [h] at hdvd; exact zero_dvd_iff.mp hdvd)
  have hpm : ¬ p ∣ orderOf s := fun h => hpe (h.trans hdvd)
  have hsm : AlgEquiv.restrictNormalHom F (σ ^ orderOf s) = 1 := by
    rw [map_pow, ← hs, pow_orderOf_eq_one]
  have hfix : (σ ^ orderOf s) x = x := by
    have := (AlgEquiv.restrictNormal_eq_one_iff F (σ ^ orderOf s)).mp hsm x hx
    exact this
  exact fix_of_wild_pow hσ hm0 hpm hfix

end Tame

/-! ## §2c. `HilbertSerreLadic` from T20 + T21 (proved by t-different) and a DVR model -/

section Bridge

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p`** (the transport between `LadicCond`'s
norm-defined filtrations and the ring-theoretic setting of T20-T22, `PkgI6`; Serre, *Corps
locaux*, II §2 and IV §1). There are a complete DVR `A` with perfect residue field and a DVR `B`
finite, torsion-free, separable and Galois over `A` (namely `A = ℤ_p` and `B = 𝓞_F`, the elements
of norm `≤ 1`), whose lower ramification groups `PkgI6.lowerRam A B i` have the orders
`ramCard F i` and are trivial only when `ramSet F i` fixes `F`, whose ramification index is
`e = ramCard F 0`, with `(p) = 𝔪_B^e` and every integer prime to `p` a unit of `B`. -/
def LadicDVRModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (A B : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : PerfectField (ResidueField A))
      (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : Module.IsTorsionFree A B)
      (_ : Algebra.IsSeparable (FractionRing A) (FractionRing B))
      (_ : IsGalois (FractionRing A) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam A B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam A B i = ⊥ → ramSet F i ⊆ fixSet F) ∧
      Ideal.ramificationIdx (maximalIdeal B) A = ramCard F 0 ∧
      Ideal.span {(p : B)} = maximalIdeal B ^ ramCard F 0 ∧
      (∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B))

/-- In `B` with `(p) = 𝔪^e` and integers prime to `p` units: `(e) = 𝔪^{e·v_p(e)}`. -/
theorem span_natCast_eq {B : Type} [CommRing B] [IsLocalRing B] {p : ℕ} (hp : p.Prime)
    {e : ℕ} (he : e ≠ 0) (hpB : Ideal.span {(p : B)} = maximalIdeal B ^ e)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B)) :
    Ideal.span {(e : B)} = maximalIdeal B ^ (e * padicValNat p e) := by
  have hdec := Nat.ordProj_mul_ordCompl_eq_self e p
  have hnd := Nat.not_dvd_ordCompl hp he
  rw [Nat.factorization_def e hp] at hdec hnd
  set v := padicValNat p e
  set u := e / p ^ v
  have hcast : (e : B) = (p : B) ^ v * (u : B) := by
    conv_lhs => rw [← hdec]
    push_cast
    rfl
  rw [hcast, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hpB,
    Ideal.span_singleton_eq_top.mpr (hunit u hnd), Ideal.mul_top, ← pow_mul]

variable {p : ℕ} [Fact p.Prime]

/-- **`HilbertSerreLadic` from T20 + T21 and the DVR model (GLUE, proved).** T20 and T21 are
the kernel's theorems `PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound` (t-different). -/
theorem hilbertSerre_of_model (hM : LadicDVRModel p) : HilbertSerreLadic p := by
  intro F hF
  obtain ⟨A, B, _, _, _, _, _, _, _, _, _, _, _, _, _, hcard, hbot, he, hpB, hunit⟩ := hM F hF
  obtain ⟨N, hN, hD⟩ := PkgI6.hilbertDifferentFormula A B
  have hB := PkgI6.differentBound A B
  refine ⟨N, hbot N hN, ?_⟩
  have hsum : ∑ i ∈ Finset.range N, (Nat.card (PkgI6.lowerRam A B i) - 1) =
      ∑ i ∈ Finset.range N, (ramCard F i - 1) :=
    Finset.sum_congr rfl fun i _ => by rw [hcard i]
  rw [hsum] at hD
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  rw [he, hD, span_natCast_eq (Fact.out) he0 hpB hunit, ← pow_add] at hB
  have hm0 : maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hmu : ¬ IsUnit (maximalIdeal B) := by
    rw [Ideal.isUnit_iff]
    exact (maximalIdeal.isMaximal B).ne_top
  exact (pow_dvd_pow_iff hm0 hmu).mp hB

end Bridge

/-! ## §2e. The DVR model over `ℤ_p`: the arithmetic conjuncts are automatic -/

section BridgeZp

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

instance perfectField_residueField_Zp (p : ℕ) [Fact p.Prime] :
    PerfectField (ResidueField ℤ_[p]) :=
  PerfectField.of_ringEquiv (K := ZMod p) PadicInt.residueField.symm

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p` over `ℤ_p`** (transport; Serre, *Corps
locaux* II §2, IV §1). There is a DVR `B` (namely `𝓞_F`, the elements of norm `≤ 1`), finite,
torsion-free, separable and Galois over `ℤ_p`, whose lower ramification groups
`PkgI6.lowerRam ℤ_p B i` have the orders `ramCard F i` and are trivial only when `ramSet F i`
fixes `F`. This is `LadicDVRModel` with `A = ℤ_p`; its other conjuncts are proved
(`ladicDVRModel_of_Zp`). -/
def LadicDVRModelZp (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B) (_ : Module.IsTorsionFree ℤ_[p] B)
      (_ : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing B))
      (_ : IsGalois (FractionRing ℤ_[p]) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam ℤ_[p] B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam ℤ_[p] B i = ⊥ → ramSet F i ⊆ fixSet F)

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModel` from its `ℤ_p` form (GLUE, proved).** `e(B/ℤ_p) = |G_0|`
(t-different's `TDifferent.card_lowerRam_zero`), `(p) = 𝔪_{ℤ_p}` maps to `𝔪_B^e`
(`TDifferent.map_maximalIdeal_eq_pow`), and integers prime to `p` are units of `ℤ_p`. -/
theorem ladicDVRModel_of_Zp (h : LadicDVRModelZp p) : LadicDVRModel p := by
  intro F hF
  obtain ⟨B, _, _, _, _, _, _, _, _, hcard, hbot⟩ := h F hF
  have : IsGaloisGroup (B ≃ₐ[ℤ_[p]] B) ℤ_[p] B := TDifferent.isGaloisGroup_algEquiv ℤ_[p] B
  have : Finite (B ≃ₐ[ℤ_[p]] B) := TDifferent.finite_algEquiv ℤ_[p] B
  have : PerfectField (maximalIdeal ℤ_[p]).ResidueField :=
    PerfectField.of_ringEquiv (K := ResidueField ℤ_[p])
      (RingEquiv.ofBijective
        (algebraMap (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p]).ResidueField :
          ResidueField ℤ_[p] →+* _)
        (maximalIdeal ℤ_[p]).bijective_algebraMap_quotient_residueField)
  have : Algebra.HasSeparableResidueFieldsAt ℤ_[p] B (maximalIdeal ℤ_[p]) := inferInstance
  have he : Ideal.ramificationIdx (maximalIdeal B) ℤ_[p] = ramCard F 0 := by
    rw [← TDifferent.card_lowerRam_zero ℤ_[p] B, hcard 0]
  refine ⟨ℤ_[p], B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcard, hbot, he, ?_, ?_⟩
  · have hmap := TDifferent.map_maximalIdeal_eq_pow ℤ_[p] B
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      he] at hmap
    exact hmap
  · intro n hn
    have hu : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn
    have := hu.map (algebraMap ℤ_[p] B)
    rwa [map_natCast] at this

end BridgeZp

/-! ## §2f. The `ℤ_p`-model `𝓞_F = integralClosure ℤ_p F` (proved): `LadicDVRModelZp` -/

section DVRModelSec

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

/-- `ℤ_p → ℚ_p → F`. -/
@[reducible] def algZpF : Algebra ℤ_[p] F :=
  ((algebraMap ℚ_[p] F).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

attribute [local instance] algZpF

instance towerZpF : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The ring of integers `𝓞_F = integralClosure ℤ_p F`. -/
abbrev OF := integralClosure ℤ_[p] F

theorem norm_eq_spectral (x : F) : ‖(x : Kbar p)‖ = spectralNorm ℚ_[p] F x := by
  rw [spectralNorm.eq_of_tower (L := Kbar p) x, PadicAlgCl.spectralNorm_eq]
  rfl

variable [FiniteDimensional ℚ_[p] F]

/-- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (copied from glue-sqrt-local's
`isIntegral_iff_spectralNorm_le_one`, with the norm of `ℚ̄_p`). -/
theorem isIntegral_iff_norm_le_one (y : F) :
    IsIntegral ℤ_[p] y ↔ ‖(y : Kbar p)‖ ≤ 1 := by
  rw [norm_eq_spectral]
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem mem_OF (y : F) : y ∈ OF F ↔ ‖(y : Kbar p)‖ ≤ 1 := isIntegral_iff_norm_le_one F y

theorem norm_le_one (b : OF F) : ‖((b : F) : Kbar p)‖ ≤ 1 := (mem_OF F b).mp b.2

theorem isUnit_iff_norm (b : OF F) : IsUnit b ↔ ‖((b : F) : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖(((u : OF F) : F) : Kbar p)‖ * ‖((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OF F) : F) * (((u⁻¹ : (OF F)ˣ) : OF F) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      have h2 : (((u : OF F) : F) : Kbar p) * ((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p) = 1 := by
        rw [← IntermediateField.coe_mul, this, IntermediateField.coe_one]
      rw [h2, norm_one]
    have a1 := norm_le_one F u
    have a2 := norm_le_one F (u⁻¹ : (OF F)ˣ)
    have b1 := norm_nonneg ((((u : OF F) : F) : Kbar p))
    have b2 := norm_nonneg (((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p))
    nlinarith
  · intro h
    have hx0 : (b : F) ≠ 0 := by
      intro h0
      rw [h0, IntermediateField.coe_zero, norm_zero] at h
      exact zero_ne_one h
    have hinv : ‖(((b : F)⁻¹ : F) : Kbar p)‖ = 1 := by
      rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    have hint : ((b : F)⁻¹) ∈ OF F := (mem_OF F _).mpr hinv.le
    refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : OF F) ?_
    apply Subtype.ext
    simp [hx0]

theorem isLocalRing_OF : IsLocalRing (OF F) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_norm] at ha hb ⊢
  have ha' : ‖((a : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F a) ha
  have hb' : ‖((b : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F b) hb
  have := IsUltrametricDist.norm_add_le_max ((a : F) : Kbar p) ((b : F) : Kbar p)
  intro hab
  rw [Subalgebra.coe_add, IntermediateField.coe_add] at hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

theorem finite_OF : Module.Finite ℤ_[p] (OF F) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] F (OF F)

theorem noeth_OF : IsNoetherianRing (OF F) :=
  IsIntegralClosure.isNoetherianRing ℤ_[p] ℚ_[p] F (OF F)

theorem dedekind_OF : IsDedekindDomain (OF F) :=
  IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] F (OF F)

omit [FiniteDimensional ℚ_[p] F] in
theorem coe_natCast_F (n : ℕ) : ((n : F) : Kbar p) = n := map_natCast (algebraMap F (Kbar p)) n

theorem p_mem : ((p : ℕ) : F) ∈ OF F := by
  rw [mem_OF, coe_natCast_F, norm_p_kbar]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)

theorem not_isField_OF : ¬ IsField (OF F) := by
  intro h
  have hp0 : (⟨((p : ℕ) : F), p_mem F⟩ : OF F) ≠ 0 := by
    intro h0
    have := congrArg (fun x : OF F => ((x : F) : Kbar p)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [coe_natCast_F] at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hp0
  have hu : IsUnit (⟨((p : ℕ) : F), p_mem F⟩ : OF F) := IsUnit.of_mul_eq_one _ hb
  rw [isUnit_iff_norm] at hu
  change ‖(((p : ℕ) : F) : Kbar p)‖ = 1 at hu
  rw [coe_natCast_F, norm_p_kbar, inv_eq_one] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

theorem dvr_OF : IsDiscreteValuationRing (OF F) := by
  haveI := isLocalRing_OF F
  haveI := noeth_OF F
  haveI := dedekind_OF F
  have h := (IsDiscreteValuationRing.TFAE (OF F) (not_isField_OF F)).out 1 3
  exact h.mpr (dedekind_OF F)

theorem torsionFree_OF : Module.IsTorsionFree ℤ_[p] (OF F) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap ℤ_[p] F) :=
    (algebraMap ℚ_[p] F).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  intro a b h
  apply hinj
  have := congrArg (fun x : OF F => (x : F)) h
  exact this

variable {F}

/-- The uniformizer `ϖ` as an element of `𝓞_F`. -/
def unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : OF F :=
  ⟨⟨ϖ, hϖ.1⟩, (mem_OF F _).mpr hϖ.2.1.le⟩

theorem coe_unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : (((unifB hϖ : OF F) : F) : Kbar p) = ϖ := rfl

theorem norm_unif_pos {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : 0 < ‖ϖ‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpF : (p : Kbar p) ∈ F := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  have hp := hϖ.2.2 _ hpF hpn
  exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp

theorem mem_span_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    b ∈ Ideal.span {unifB hϖ ^ k} ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  have hϖ0 := norm_unif_pos hϖ
  have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have : (((c * unifB hϖ ^ k : OF F) : F) : Kbar p) = ((c : F) : Kbar p) * ϖ ^ k := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, IntermediateField.coe_mul,
        IntermediateField.coe_pow, coe_unifB]
    rw [this, norm_mul, norm_pow]
    calc ‖((c : F) : Kbar p)‖ * ‖ϖ‖ ^ k ≤ 1 * ‖ϖ‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_le_one F c) (by positivity)
      _ = ‖ϖ‖ ^ k := one_mul _
  · intro h
    set ϖF : F := ⟨ϖ, hϖ.1⟩
    have hϖF : ϖF ≠ 0 := by
      intro h0
      exact hϖne (congrArg (fun x : F => (x : Kbar p)) h0)
    set c : F := (b : F) * (ϖF ^ k)⁻¹ with hc
    have hcn : ‖(c : Kbar p)‖ ≤ 1 := by
      rw [hc, IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow,
        norm_mul, norm_inv, norm_pow]
      have : ‖((ϖF : F) : Kbar p)‖ = ‖ϖ‖ := rfl
      rw [this]
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact h
    refine ⟨⟨c, (mem_OF F c).mpr hcn⟩, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
    change c * ϖF ^ k = (b : F)
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hϖF), mul_one]

theorem maximalIdeal_eq {ϖ : Kbar p} (hϖ : IsUnif F ϖ) :
    haveI := isLocalRing_OF F
    maximalIdeal (OF F) = Ideal.span {unifB hϖ} := by
  haveI := isLocalRing_OF F
  ext b
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm, ← pow_one (unifB hϖ),
    mem_span_pow_iff, pow_one]
  constructor
  · intro h
    exact hϖ.2.2 _ (b : F).2 (lt_of_le_of_ne (norm_le_one F b) h)
  · intro h h1
    rw [h1] at h
    exact absurd hϖ.2.1 (not_lt.mpr h)

theorem mem_maximalIdeal_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    haveI := isLocalRing_OF F
    b ∈ maximalIdeal (OF F) ^ k ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  haveI := isLocalRing_OF F
  rw [maximalIdeal_eq hϖ, Ideal.span_singleton_pow, mem_span_pow_iff]

end Model2

section Galois

attribute [local instance] algZpF FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] torsionFree_OF

instance faithful_OF : FaithfulSMul ℤ_[p] (OF F) := by
  rw [faithfulSMul_iff_algebraMap_injective, ← Module.isTorsionFree_iff_algebraMap_injective]
  exact torsionFree_OF F

instance faithful_frac_OF : FaithfulSMul ℤ_[p] (FractionRing (OF F)) := inferInstance


instance isFractionRing_OF : IsFractionRing (OF F) F :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] F

theorem hcomp :
    (algebraMap (FractionRing ℤ_[p]) (FractionRing (OF F))).comp
        ((FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv : ℚ_[p] →+* FractionRing ℤ_[p]) =
      ((FractionRing.algEquiv (OF F) F).symm.toRingEquiv : F →+* FractionRing (OF F)).comp
        (algebraMap ℚ_[p] F) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext z
  simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
  have h1 : (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap ℤ_[p] (FractionRing ℤ_[p]) z :=
    (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.commutes z
  have h2 : algebraMap ℚ_[p] F (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z) := rfl
  have h3 : (FractionRing.algEquiv (OF F) F).symm (algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z))
      = algebraMap (OF F) (FractionRing (OF F)) (algebraMap ℤ_[p] (OF F) z) :=
    (FractionRing.algEquiv (OF F) F).symm.commutes _
  rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p])
    (FractionRing (OF F)), IsScalarTower.algebraMap_apply ℤ_[p] (OF F) (FractionRing (OF F))]

theorem isGalois_frac [IsGalois ℚ_[p] F] :
    IsGalois (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  IsGalois.of_equiv_equiv (hcomp F)

theorem isSeparable_frac :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  Algebra.IsSeparable.of_equiv_equiv _ _ (hcomp F)

end Galois

section Filtration

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem coe_galRestrict (s : F ≃ₐ[ℚ_[p]] F) (b : OF F) :
    ((galRestrict ℤ_[p] ℚ_[p] F (OF F) s b : OF F) : F) = s (b : F) :=
  algebraMap_galRestrict_apply ℤ_[p] s b

theorem mem_lowerRam_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (s : F ≃ₐ[ℚ_[p]] F) :
    haveI := isLocalRing_OF F
    galRestrict ℤ_[p] ℚ_[p] F (OF F) s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i ↔
      ∀ x : F, ‖(x : Kbar p)‖ ≤ 1 → ‖((s x : F) : Kbar p) - x‖ ≤ ‖ϖ‖ ^ (i + 1) := by
  haveI := isLocalRing_OF F
  rw [PkgI6.mem_lowerRam]
  constructor
  · intro h x hx
    have := (mem_maximalIdeal_pow_iff hϖ (i + 1) _).mp (h ⟨x, (mem_OF F x).mpr hx⟩)
    rw [Subalgebra.coe_sub, coe_galRestrict, AddSubgroupClass.coe_sub] at this
    exact this
  · intro h b
    rw [mem_maximalIdeal_pow_iff hϖ, Subalgebra.coe_sub, coe_galRestrict,
      AddSubgroupClass.coe_sub]
    exact h b (norm_le_one F b)

end Filtration

section Card

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem mem_ramSet_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (σ : GQp p) :
    haveI := isLocalRing_OF F
    σ ∈ ramSet F i ↔ galRestrict ℤ_[p] ℚ_[p] F (OF F) (AlgEquiv.restrictNormalHom F σ) ∈
      PkgI6.lowerRam ℤ_[p] (OF F) i := by
  haveI := isLocalRing_OF F
  rw [mem_lowerRam_iff hϖ]
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx
    rw [AlgEquiv.restrictNormalHom_apply, ← IsUnif.norm_eq hϖ hϖ']
    exact h x x.2 hx
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    have := h ⟨x, hx⟩ hx1
    rwa [AlgEquiv.restrictNormalHom_apply] at this

theorem card_lowerRam (i : ℕ) :
    haveI := isLocalRing_OF F
    Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = ramCard F i := by
  haveI := isLocalRing_OF F
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  set G := galRestrict ℤ_[p] ℚ_[p] F (OF F) with hG
  set K : Set (F ≃ₐ[ℚ_[p]] F) := {s | G s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i} with hKdef
  have h1 : Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = Nat.card K :=
    (Nat.card_congr (G.toEquiv.subtypeEquiv (fun s => Iff.rfl))).symm
  have hK : K = AlgEquiv.restrictNormalHom F '' ramSet F i := by
    ext s
    constructor
    · intro hs
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (Kbar p) s
      exact ⟨σ, (mem_ramSet_iff hϖ i σ).mpr hs, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact (mem_ramSet_iff hϖ i σ).mp hσ
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    exact congrFun h x
  have himg : restr F '' ramSet F i = φ '' (AlgEquiv.restrictNormalHom F '' ramSet F i) := by
    rw [Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj, ← hK, h1]

theorem fix_of_lowerRam_bot (i : ℕ) :
    haveI := isLocalRing_OF F
    PkgI6.lowerRam ℤ_[p] (OF F) i = ⊥ → ramSet F i ⊆ fixSet F := by
  haveI := isLocalRing_OF F
  intro hbot σ hσ
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  have h := (mem_ramSet_iff hϖ i σ).mp hσ
  rw [hbot, Subgroup.mem_bot, ← map_one (galRestrict ℤ_[p] ℚ_[p] F (OF F))] at h
  have h1 := (galRestrict ℤ_[p] ℚ_[p] F (OF F)).injective h
  intro x hx
  exact (AlgEquiv.restrictNormal_eq_one_iff F σ).mp h1 x hx

end Card

section FinalZp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModelZp` (GLUE, proved).** `B = 𝓞_F = integralClosure ℤ_p F`: a DVR (local by the
ultrametric norm, Dedekind as an integral closure, `IsDiscreteValuationRing.TFAE`), finite and
torsion-free over `ℤ_p`, with `Frac(B) ≅ F` Galois over `Frac(ℤ_p) ≅ ℚ_p`
(`IsGalois.of_equiv_equiv`); `𝔪_B^k = {‖b‖ ≤ ‖ϖ‖^k}`, and `galRestrict` identifies
`PkgI6.lowerRam ℤ_p B i` with the restrictions of `ramSet F i`. -/
theorem ladicDVRModelZp : LadicDVRModelZp p := by
  intro F hF
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  letI := algZpF F
  haveI := torsionFree_OF F
  haveI := faithful_OF F
  haveI := dvr_OF F
  exact ⟨OF F, inferInstance, inferInstance, dvr_OF F, inferInstance, finite_OF F,
    torsionFree_OF F, isSeparable_frac F, isGalois_frac F, card_lowerRam, fix_of_lowerRam_bot⟩

end FinalZp

end DVRModelSec

/-! ## §3. The reduction (proved) -/

section Reduction

theorem gl_eq_one_of_scalar {ℓ : ℕ} [Fact ℓ.Prime] {g : GL (Fin 2) (PadicAlgCl ℓ)}
    {c : PadicAlgCl ℓ} (h : (g : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) c)
    (hc : c = 1) : g = 1 := by
  apply Units.ext
  rw [h, hc, map_one, Units.val_one]

/-- **`LocalRamG` from the local pieces (GLUE, proved).** -/
theorem localRamG_of {ℓ : ℕ} [Fact ℓ.Prime] (u : ℚ) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (r : GaloisRep ℓ 2) (hUB : UpperBreakFix p) (hUW : UpperWild p) (hWT : WildFixTame p)
    (hd : LocalData p r) (h11 : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) r) :
    LocalRamG u p r := by
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_, fun hS hM => ?_⟩
  · obtain ⟨F, β, hF, he, hsh, hup⟩ := hd.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := hUW t (by linarith) hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hwild⟩) (hup t ht σ ⟨hσ, hfix⟩)
  · obtain ⟨F, β, hF, he, hsh, htame⟩ := hd.2 hpD
    have hfix := hWT F hF he hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hσ⟩) (htame σ ⟨hfix, hσ⟩)
  · refine h11 p (Fact.out) ?_ hpℓ
    intro hT
    rcases Finset.mem_union.mp hT with h | h
    · exact hS h
    · exact hM (Nat.mem_primeFactors.mp h).2.1

/-- **`G15RamG` from smaller named Props (GLUE, proved).** Closed local-field Props
(`UpperBreakFix`, `UpperWild`, `WildFixTame`), the local data of G8/G7 on `D` (`LocalData`), and
G11's output on `D` for `T = S_mul ∪ supp M_{S_mul}(u)` (`GlueDescent.ramSet`). -/
theorem g15RamG_of_pieces
    (hUB : ∀ (p : ℕ) [Fact p.Prime], UpperBreakFix p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5' => localRamG_of u p h5' D.r5 (hUB p) (hUW p) (hWT p) (h5 p hp h5') h11₅,
    fun h5' => ?_⟩
  subst h5'
  exact localRamG_of u 5 (by norm_num) D.r3 (hUB 5) (hUW 5) (hWT 5) h3 h11₃

/-- **`G15RamG`, with D1 discharged (GLUE, proved).** As `g15RamG_of_pieces`, with
`UpperBreakFix` replaced by the transport `HilbertSerreLadic` of T20 + T21. -/
theorem g15RamG_of_hilbertSerre
    (hHS : ∀ (p : ℕ) [Fact p.Prime], HilbertSerreLadic p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_pieces (fun p _ => upperBreakFix_of_hilbertSerre (hHS p)) hUW hWT D u h5 h3
    h11₅ h11₃

/-- **`G15RamG` from the DVR model, T20-T21 (proved in the kernel), `WildFixTame` and the data
of G7-G8-G11 on `D` (GLUE, proved).** `UpperWild` is proved (`upperWild`). -/
theorem g15RamG_of_model
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_hilbertSerre (fun p _ => hilbertSerre_of_model (hM p)) (fun p _ => upperWild) hWT
    D u h5 h3 h11₅ h11₃

/-- **`G15RamG` with all closed local-field glue proved except the DVR model (GLUE, proved).**
Hypotheses: the transport `LadicDVRModel`, the data of G7-G8 on `D` (`LocalData`), and G11's
output on `D`. -/
theorem g15RamG_of_dvrModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_model hM (fun p _ => wildFixTame) D u h5 h3 h11₅ h11₃

/-- **`G15RamG` from the `ℤ_p`-model of finite Galois `F ⊆ ℚ̄_p` (GLUE, proved).** -/
theorem g15RamG_of_zpModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModelZp p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_dvrModel (fun p _ => ladicDVRModel_of_Zp (hM p)) D u h5 h3 h11₅ h11₃

/-- The trivial two-dimensional representation (for the non-vacuity check below). -/
def trivRep (ℓ : ℕ) [Fact ℓ.Prime] : GaloisRep ℓ 2 := ⟨1, continuous_const⟩

/-- **Non-vacuity check (proved).** `LocalData p r` holds for the trivial representation (with
`F = ℚ_p`, `β = 1`), so the hypotheses on `D` are not contradictory. -/
theorem localData_trivRep (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] :
    LocalData p (trivRep ℓ) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have hshape : TwistShape p (trivRep ℓ) ⊥ (fun _ => 1) := by
    intro σ _
    simp [trivRep, PkgI4.GaloisRep.restrictLocal]
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
      unfold ramCard
      have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
      refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
      apply Subtype.ext
      obtain ⟨σ, -, hσ⟩ := a.2
      obtain ⟨τ, -, hτ⟩ := b.2
      rw [← hσ, ← hτ]
      funext x
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
      simp only [restr, ← hq, AlgEquiv.commutes]
    omega
  refine ⟨fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G15RamG` from the data of G7-G8 on `D` and G11's output alone (GLUE, proved).** Every
closed local-field input is proved: `UpperBreakFix` (from T20, T21 and `ladicDVRModelZp`),
`UpperWild`, `WildFixTame`. -/
theorem g15RamG_of_localData
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_zpModel (fun _ _ => ladicDVRModelZp) D u h5 h3 h11₅ h11₃

end Reduction

end G15Ram
end

/-! Copied verbatim from scratch/g0-mod-galois/part_galois.lean L27-152 and part_matrix.lean L11-21. -/
noncomputable section
namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Objects -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmbRing` as a `ℚ`-algebra map (the `i` of g0-mod-newform's `ModData`). -/
def qEmb (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
  (qEmbRing K).toRatAlgHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- `resQ K τ` is the only `σ ∈ G_ℚ` with `qEmb K ∘ σ = τ ∘ qEmb K`. -/
lemma eq_resQ (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (σ : PkgI4.GQ) (h : ∀ x, qEmb K (σ x) = τ (qEmb K x)) : σ = resQ K τ := by
  apply AlgEquiv.ext; intro x
  exact (qEmbRing K).injective ((h x).trans (resQ_spec K τ x).symm)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- The restriction of a representation to an invariant subspace. -/
def restrictRep {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Submodule k V) (h : ∀ g, ∀ w ∈ W, ρ g w ∈ W) :
    Representation k G W where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext w; simp
  map_mul' g g' := by ext w; simp

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-! ### Outputs of the earlier glue steps (inputs of this range) -/

/-- **Output of G2 (Lemma PR(i)), the part used here.** The field `K` (= `L'`, which contains
the fibre field and the Hom field, both unramified outside `T`, and the kernel field of `β`,
unramified outside `T` by B3(v)) is unramified at every prime `p ∉ T`: every inertia element
of `G_ℚ` at a place above `p` lies in (the image of) `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- **Output of G3 (Lemma PR(ii)) with R7a (Néron–Ogg–Shafarevich), the part used here.** `A`
has good reduction at the places above `p ∉ T`, so for `p ≠ ℓ` the inertia elements of `G_K`
at those places act trivially on `V_ℓ(A)` (the instantiation of
`PkgI2.inertiaTrivial_of_goodReduction` on the actual `A`, glue G3/G11). -/
def G3Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ' : Field.absoluteGaloisGroup K,
      (∃ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = resQ K σ') →
      tate A ℓ σ' = 1

/-- **Output of G7 (scalar descent, N5 L632-716) at the coefficient prime `ℓ`**, together with
the outputs of G4-G6 that G8 uses. `A` is the model over `K = L'` (an abelian surface with
`End_K(A)` of rank 4, the maximal order case of `End⁰ = B`: A9's output). The data are:
operators `Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` (without `a_σ`: `GlueDescent.rho` multiplies by
`β_σ⁻¹ a_σ`, giving N5's `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ`) with the cocycle `c` (`Tm g Tm h = c(g,h) Tm(gh)`),
the scalars `a` and the cochain `β` with `a_g a_h c(g,h) = ε(g,h) a_{gh}` and
`β_g β_h = ε(g,h) β_{gh}` (`∂β = ε`, B2-B3), all trivial on `G_{L'}` where `Tm` is the Tate
action (`L'` contains the kernel field of `β|G_L`; it is taken finite Galois over `ℚ`, as
g0-mod-field's `G7Data` supplies, which `G10Glue` needs); a system of `2 × 2` matrix units (the image of
`B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`) commuting with every `Tm σ` (`μ_σ` is `B`-linear); and continuity of
`σ ↦ β_σ⁻¹ a_σ Tm σ` (glue-rho-cont proved continuity on `G_K`; finite index gives the rest). -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

/-- **Output of G5-G6 (QM dichotomy and NoCM), the part used by G10:** `End_K(A)` is a division
ring (`PkgI3.EndDivision`: every nonzero endomorphism is an isogeny) and is not commutative (so
`End⁰_K(A) = B`, not a field). -/
def G6Out {K : Type} [Field K] (A : PkgI3.AbVar K) : Prop :=
  PkgI3.EndDivision A ∧ ∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x

/-! ### Outputs of this range -/

/-- **Output of G8.** `r : G_ℚ → GL₂(ℚ̄_ℓ)` (continuous) and `e : ℚ̄_ℓ ⊗ V_ℓ(A) ≅ ℚ̄_ℓ² × ℚ̄_ℓ²`
with: (i) `e` intertwines the descended representation `ρ` (an operator family on
`ℚ̄_ℓ ⊗ V_ℓ(A)`, in the theorem `GlueDescent.rho Tm a β`) with `r ⊕ r` on all of `G_ℚ`;
(ii) `ρ` is the Tate action on `G_{L'}`; (iii) `r|G_{L'}` is absolutely irreducible, in
Burnside's form (the matrices `r(σ)`, `σ ∈ G_{L'}`, generate `M₂(ℚ̄_ℓ)`). -/
def G8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤


/-- **Burnside's theorem, absolutely irreducible form (textbook leaf; Lang, *Algebra*, XVII §3,
Cor. 3.4, and Curtis–Reiner §27 (Burnside, Frobenius–Schur); locators UNVERIFIED).** If a
finite-dimensional representation `ρ` of a monoid over a field `F` stays irreducible after every
field extension, then the matrices `ρ(g)` (in any basis) generate `M_n(F)` as an `F`-algebra.
Mathlib has the Jacobson density theorem (`jacobson_density`), from which it follows. -/
def BurnsideAbsIrred : Prop :=
  ∀ (F : Type) [Field F] (G : Type) [Monoid G] (W : Type) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (n : ℕ) (b : Module.Basis (Fin n) F W) (ρ : Representation F G W),
    (∀ (F' : Type) [Field F'] [Algebra F F'], (GlueI3.repBaseChange F' ρ).IsIrreducible) →
    Algebra.adjoin F (Set.range fun g => LinearMap.toMatrix b b (ρ g)) = ⊤

end G0Galois
end

/-! ## g8-object: G8's `r_ℓ` as a Lean object; the G8-G16 interface over it

Task g8-object, 2026-11-13. g15-ram found that `G15RamG D u` is false for arbitrary
`D : ModData L A`: the fields `r₅`, `r₃` of `ModData` are bare representations, while G15 is a claim
about the `r_ℓ` that G8 builds from G7's descent data. This section

* §A defines that `r_ℓ` (`DescData.r`) from G7's output (`G0Galois.G7Out`) and `dim = 4` (T26),
  by the construction of g0-mod-galois' `g8Matrix_of_burnside` (a basis of `W = e₀₀ V`), and
  proves G8's intertwining for it (`DescData.intertwines`, `DescData.rho_resQ`) and, with C2 and
  Burnside, the full `G0Galois.G8Out` (`DescData.g8Out`);
* §B proves that **every** `r` intertwined with `ρ = β⁻¹ a Tm` (G8's output for any choice of
  basis) is pinned at each `g` where `ρ(g)` is a scalar (`mat_eq_scalar_of_intertwines`), and
  G11 for such `r` (`g11_of_intertwines`);
* §C restates g15-ram's `LocalData` on the descent data (`Tm`, `a`, `β`), not on `r`
  (`LocalDataG`), and proves `LocalDataG → G15Ram.LocalData` for every intertwined `r`
  (`localData_of_intertwines`);
* §D proves `G15RamG` for the constructed object (`ModObj.toModData`) from `LocalDataG`, `G2Out`
  and `G3Out` (`g15RamG_obj`), using g15-ram's `g15RamG_of_localData`. -/

noncomputable section

namespace G8Object

open PkgI4 (GQ GQp GaloisRep decomp)
open LadicCond
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K] [NumberField K]

/-! ### §A. The object -/

/-- **G7's descent data at the coefficient prime `ℓ`, bundled (the input of G8).** The operators
`Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)`, the cocycle `c`, the scalars `a`, the sign cocycle `ε`, the
cochain `β`, and matrix units `u` (the image of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`), with g0-mod-galois'
`G7Out` and `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` (from T26 `PkgI3.TateModuleFree` and `dim A = 2`;
`DescData.ofG7Out`). -/
structure DescData (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] where
  Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)
  c : GQ → GQ → PadicAlgCl ℓ
  ε : GQ → GQ → PadicAlgCl ℓ
  a : GQ → PadicAlgCl ℓ
  β : GQ → PadicAlgCl ℓ
  u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)
  g7 : G0Galois.G7Out A ℓ Tm c ε a β u
  dim4 : Module.finrank (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) = 4

/-- `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` from T26 and `dim A = 2` (the argument of g0-mod-galois' `g8`). -/
theorem finrank_Vb_of (hT : PkgI3.TateModuleFree) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hdim : A.dim = 2) : Module.finrank (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) = 4 := by
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓK
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  rw [Module.finrank_baseChange, Module.finrank_baseChange]
  rw [hdim] at hrk
  have h22 : (2 : WithBot ℕ∞) * 2 = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    norm_num
  rw [h22] at hrk
  exact_mod_cast hrk

/-- The object from G7's output and T26. -/
def DescData.ofG7Out (hT : PkgI3.TateModuleFree) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) : DescData A ℓ :=
  ⟨Tm, c, ε, a, β, u, h7, finrank_Vb_of hT A ℓ h7.1⟩

namespace DescData

variable {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (D : DescData A ℓ)

theorem hTm : ∀ g h, D.Tm g * D.Tm h = D.c g h • D.Tm (g * h) := D.g7.2.2.1
theorem ha : ∀ g h, D.a g * D.a h * D.c g h = D.ε g h * D.a (g * h) := D.g7.2.2.2.1
theorem hβ : ∀ g h, D.β g * D.β h = D.ε g h * D.β (g * h) := D.g7.2.2.2.2.1
theorem hβ0 : ∀ g, D.β g ≠ 0 := D.g7.2.2.2.2.2.1
theorem hres : ∀ σ, D.Tm (G0Galois.resQ K σ) = G0Galois.tate A ℓ σ ∧
    D.a (G0Galois.resQ K σ) = 1 ∧ D.β (G0Galois.resQ K σ) = 1 := D.g7.2.2.2.2.2.2.1
theorem hcomm : ∀ g i j, Commute (D.Tm g) (D.u.e i j) := D.g7.2.2.2.2.2.2.2.1
theorem hcont : ∀ (f : Module.Dual (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (v : G0Galois.Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho D.Tm D.a D.β g v) := D.g7.2.2.2.2.2.2.2.2

/-- `ρ(1) = 1`. -/
theorem rho_one : GlueDescent.rho D.Tm D.a D.β 1 = 1 := by
  have := D.hres 1
  rw [map_one] at this
  refine (GlueDescent.rho_eq_act D.Tm (fun _ => G0Galois.tate A ℓ 1) D.a D.β 1 this.1 this.2.1
    this.2.2).trans ?_
  exact map_one (G0Galois.tate A ℓ)

/-- **G8's descended representation** `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727), as a
representation of `G_ℚ` (glue-descent's `rhoRep`). -/
def rho : Representation (PadicAlgCl ℓ) GQ (G0Galois.Vb A ℓ) :=
  GlueDescent.rhoRep D.Tm D.c D.ε D.a D.β D.hTm D.ha D.hβ D.hβ0 D.rho_one

theorem rho_apply (g : GQ) : D.rho g = GlueDescent.rho D.Tm D.a D.β g := rfl

/-- `ρ` is the Tate action on `G_{L'}`. -/
theorem rho_resQ (σ : Field.absoluteGaloisGroup K) :
    GlueDescent.rho D.Tm D.a D.β (G0Galois.resQ K σ) = G0Galois.tate A ℓ σ :=
  GlueDescent.rho_eq_act D.Tm (fun _ => G0Galois.tate A ℓ σ) D.a D.β (G0Galois.resQ K σ)
    (D.hres σ).1 (D.hres σ).2.1 (D.hres σ).2.2

theorem comm (g : GQ) (i j : Fin 2) : Commute (D.rho g) (D.u.e i j) :=
  GlueDescent.rho_commute D.Tm D.a D.β (D.u.e i j) (fun g => D.hcomm g i j) g

theorem finiteDimensional (D : DescData A ℓ) : FiniteDimensional (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) :=
  Module.finite_of_finrank_pos (by rw [D.dim4]; norm_num)

theorem finrank_W : Module.finrank (PadicAlgCl ℓ) D.u.W = 2 :=
  haveI := D.finiteDimensional
  D.u.finrank_W D.dim4

/-- A basis of `W = e₀₀(ℚ̄_ℓ ⊗ V_ℓ(A))` (chosen once; `dim W = 2`). -/
def basis : Module.Basis (Fin 2) (PadicAlgCl ℓ) D.u.W :=
  haveI := D.finiteDimensional
  Module.finBasisOfFinrankEq (PadicAlgCl ℓ) D.u.W D.finrank_W

/-- `ρ` restricted to `W` (the multiplicity space: `ρ ≅ r ⊕ r`). -/
def rW : Representation (PadicAlgCl ℓ) GQ D.u.W :=
  G0Galois.restrictRep D.rho D.u.W (fun g _ hw => D.u.mapsTo_W D.rho D.comm g hw)

/-- The matrices of `ρ|_W` in the basis `D.basis`. -/
def m : GQ →* Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) :=
  (LinearMap.toMatrixAlgEquiv D.basis).toRingEquiv.toMonoidHom.comp D.rW

theorem m_apply (g : GQ) : D.m g = LinearMap.toMatrix D.basis D.basis (D.rW g) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact LinearMap.toMatrixAlgEquiv_apply D.basis (D.rW g) i j

theorem continuous_m : Continuous fun g => D.m g := by
  refine continuous_matrix fun i j => ?_
  let f : Module.Dual (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) :=
    (D.basis.coord i).comp ((D.u.e 0 0).codRestrict D.u.W (fun v => D.u.mem_W_of_e0 0 v))
  refine (D.hcont f (D.basis j : G0Galois.Vb A ℓ)).congr fun g => ?_
  rw [D.m_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
  change D.basis.coord i _ = D.basis.coord i _
  congr 1
  exact Subtype.ext (D.u.e00_of_mem (D.u.mapsTo_W D.rho D.comm g (D.basis j).2))

theorem continuous_toHom : Continuous (D.m.toHomUnits : GQ →* GL (Fin 2) (PadicAlgCl ℓ)) := by
  rw [Units.continuous_iff]
  refine ⟨D.continuous_m, ?_⟩
  have hinv : (fun g => (((D.m.toHomUnits g)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))) = fun g => D.m g⁻¹ := by
    funext g
    rw [← map_inv]
    rfl
  rw [hinv]
  exact D.continuous_m.comp continuous_inv

/-- **G8's `r_ℓ`, as a Lean object** (N5 L729-730: "matrix units give `ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`"): the
continuous representation `G_ℚ → GL₂(ℚ̄_ℓ)` given by `ρ_ℓ|_{e₀₀ V}` in the basis `D.basis`. -/
def r : GaloisRep ℓ 2 := ⟨D.m.toHomUnits, D.continuous_toHom⟩

theorem r_mat (g : GQ) : D.r.mat g = LinearMap.toMatrix D.basis D.basis (D.rW g) := D.m_apply g

/-- G8's isomorphism `ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` (`splitEquiv` and the basis). -/
def e : G0Galois.Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ) :=
  D.u.splitEquiv.trans (D.basis.equivFun.prodCongr D.basis.equivFun)

/-- **G8 (i) for the object, proved:** `e` intertwines `ρ_ℓ` with `r_ℓ ⊕ r_ℓ` on all of `G_ℚ`. -/
theorem intertwines : G0Galois.Intertwines (GlueDescent.rho D.Tm D.a D.β) D.r.mat D.e := by
  intro g v
  have h1 := D.u.splitEquiv_intertwines D.rho D.comm g v
  change D.e (D.rho g v) = _
  simp only [e, LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply,
    Module.Basis.equivFun_apply, D.r_mat]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  · dsimp only
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl

/-- **G8 for the object, proved** from C2's inputs (the leaves R9a `FaltingsSemisimple`, R9b
`FaltingsTate`, T26 `TateModuleFree`, T6 `HomFreeFinite`, glue-ssbc's `SemisimpleBaseChange`)
and Burnside (`G0Galois.BurnsideAbsIrred`): g0-mod-galois' `G8Out` holds for `D.r`. -/
theorem g8Out (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate)
    (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hB : G0Galois.BurnsideAbsIrred) :
    G0Galois.G8Out A ℓ (GlueDescent.rho D.Tm D.a D.β) D.r := by
  haveI := D.finiteDimensional
  haveI hVne : Nontrivial (G0Galois.Vb A ℓ) :=
    Module.nontrivial_of_finrank_pos (R := PadicAlgCl ℓ) (by rw [D.dim4]; norm_num)
  haveI : Nontrivial D.u.W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    haveI := hW
    haveI : Subsingleton (D.u.W × D.u.W) := inferInstance
    exact not_subsingleton (G0Galois.Vb A ℓ) D.u.splitEquiv.toEquiv.subsingleton
  let rWK : Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) D.u.W :=
    D.rW.comp (G0Galois.resQ K)
  have he : ∀ σ v, D.u.splitEquiv (G0Galois.tate A ℓ σ v) =
      (rWK σ).prodMap (rWK σ) (D.u.splitEquiv v) := by
    intro σ v
    rw [← D.rho_resQ σ, ← D.rho_apply, D.u.splitEquiv_intertwines D.rho D.comm]
    rfl
  have hirr := fun (F : Type) [Field F] [Algebra (PadicAlgCl ℓ) F] =>
    PkgI3.C2_absolutelyIrreducible hS hF hT hH hSS A ℓ D.g7.2.1 (PadicAlgCl ℓ) rWK
      D.u.splitEquiv he F
  refine ⟨D.rho_resQ, D.e, D.intertwines, ?_⟩
  have hfun : (fun σ => D.r.mat (G0Galois.resQ K σ)) =
      fun σ => LinearMap.toMatrix D.basis D.basis (rWK σ) :=
    funext fun σ => D.r_mat _
  rw [hfun]
  exact hB (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) D.u.W 2 D.basis rWK hirr

end DescData

/-! ### §B. Every intertwined `r` is pinned where `ρ` is scalar; G11 -/

/-- **Scalar transfer (proved).** If `e` intertwines `f` with `m ⊕ m` and `f g = c • 1`, then
`m g` is the scalar matrix `c`. So any two `r` with G8's output on the same `ρ` agree at every
`g` where `ρ(g)` is a scalar (this is all that G11 and G15 use). -/
theorem mat_eq_scalar_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {f : G → Module.End (PadicAlgCl ℓ) V}
    {mm : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f mm e) {g : G} {c : PadicAlgCl ℓ} (hf : f g = c • 1) :
    mm g = Matrix.scalar (Fin 2) c := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  have h1 := h g (e.symm (w, 0))
  rw [hf, LinearMap.smul_apply, Module.End.one_apply, map_smul, LinearEquiv.apply_symm_apply]
    at h1
  have h2 := congrArg Prod.fst h1
  simp only [Prod.smul_mk] at h2
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← h2]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem toHom_eq_one_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {f : GQ → Module.End (PadicAlgCl ℓ) V} {r : GaloisRep ℓ 2}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f r.mat e) {g : GQ} (hf : f g = 1) : r.toHom g = 1 := by
  have h1 := mat_eq_scalar_of_intertwines h (c := 1) (by rw [hf, one_smul])
  apply Units.ext
  change r.mat g = _
  rw [h1, map_one, Units.val_one]

/-- **G11 for every `r` intertwined with G8's `ρ` (proved; the argument of g0-mod-galois' `g11`).**
At `p ∉ T`, `p ≠ ℓ`, an inertia element above `p` is in `G_K` (G2), acts trivially on `V_ℓ(A)`
(G3 with R7a), so `ρ` of it is `1`, and `r` of it is `1`. -/
theorem g11_of_intertwines {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (T : Finset ℕ)
    (h2 : G0Galois.G2Out K T) (h3 : G0Galois.G3Out A ℓ T)
    {ρ : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (hres : ∀ σ, ρ (G0Galois.resQ K σ) = G0Galois.tate A ℓ σ) {r : GaloisRep ℓ 2}
    {e : G0Galois.Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines ρ r.mat e) : G0Galois.G11Out T r := by
  intro p hp hpT hpℓ v hv σ hσ
  obtain ⟨σ', hσ'⟩ := h2 p hp hpT v hv σ hσ
  have ht : G0Galois.tate A ℓ σ' = 1 := h3 p hp hpT hpℓ v hv σ' ⟨σ, hσ, hσ'.symm⟩
  refine toHom_eq_one_of_intertwines h ?_
  rw [← hσ', hres, ht]

/-! ### §C. `LocalData` restated on the descent data -/

section LocalG

variable (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
  [Module (PadicAlgCl ℓ) V]

/-- **Glue on G7's data (G7's `G_L`-clause + R6 + D2; N5 L819-823, L848-851).** On `G_F ∩ P_p`
(through the decomposition map `G_{ℚ_p} → G_ℚ`), `a = 1` and `Tm = 1`. Why true for Glazer's
data with `F` the Galois closure of `L_v(A[3])` (`A[5]` if `p = 3`) at `p ≤ D`, and of `L_v` at
`p > D`: `F ⊇ L_v` puts `decomp(G_F)` in `G_L`, where `a = 1` and `Tm` is the Galois action of
`A/L` (`DescentDatum`, `μ_σ = 1` on `G_L`, N5 L831); at `p ≤ D`, Raynaud's criterion (R6) makes
`A` semistable over `F`, so wild inertia acts trivially on `V_ℓ(A)`, `ℓ ≠ p` (D2,
`PkgI2.D2_fixed_of_raynaud`); at `p > D`, N5 L848-851 ("the surface has good reduction").
This is a statement about G7's data, not about `r`: `G7Out` pins `Tm`, `a` only on `G_{L'}`, and
`F` cannot contain `L'_v` (the bound `e(F/ℚ_p) ≤ (DG₀)!` does not see `[L':ℚ]`). -/
def TmWild (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, a (decomp p σ) = 1 ∧ Tm (decomp p σ) = 1

/-- **Glue on G7's `β` (D3 + T16; N5 L832-844).** `β` is trivial on `G_{ℚ_p}^t ∩ G_F` for
`t > U` (through the decomposition map). g15-ram's `TwistUpper`, for the local twist
`σ ↦ β(decomp σ)⁻¹`. -/
def BetaUpper (β : GQ → PadicAlgCl ℓ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β (decomp p σ) = 1

/-- **Glue on G7's `β` at tame primes (N5 L848-851).** `β` is trivial on `G_F ∩ P_p`. -/
def BetaTame (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) = 1

/-- **g15-ram's `SmallPrimeData`, on the descent data.** -/
def SmallPrimeG (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F : Fld p, IsFinGal F ∧ ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
    TmWild p Tm a F ∧ BetaUpper p β F G0ModNewform.U0

/-- **g15-ram's `LargePrimeData`, on the descent data.** -/
def LargePrimeG (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧ TmWild p Tm a F ∧ BetaTame p β F

/-- **g15-ram's `LocalData`, restated on G7's descent data `(Tm, a, β)`** (the restatement this
task makes; g15-ram's `LocalData p r` is on a bare `r`). -/
def LocalDataG (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → SmallPrimeG p Tm a β) ∧
    ((ZInQ.heightD : ℝ) < p → LargePrimeG p Tm a β)

variable {p}

/-- On `G_F ∩ P_p`, `ρ = β⁻¹ a Tm` is the scalar `β⁻¹`, so an intertwined `r` is that scalar:
g15-ram's `TwistShape` for the local twist `σ ↦ β(decomp σ)⁻¹` (proved). -/
theorem twistShape_of_tmWild {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines (GlueDescent.rho Tm a β) r.mat e) {F : Fld p}
    (hw : TmWild p Tm a F) :
    G15Ram.TwistShape p r F (fun σ => (β (decomp p σ))⁻¹) := by
  intro σ hσ
  obtain ⟨ha, hT⟩ := hw σ hσ
  have hf : GlueDescent.rho Tm a β (decomp p σ) = (β (decomp p σ))⁻¹ • 1 := by
    simp [GlueDescent.rho, ha, hT]
  exact mat_eq_scalar_of_intertwines h hf

/-- **`LocalDataG` on the data gives g15-ram's `LocalData` for every intertwined `r` (proved).** -/
theorem localData_of_intertwines {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines (GlueDescent.rho Tm a β) r.mat e) (hd : LocalDataG p Tm a β) :
    G15Ram.LocalData p r := by
  refine ⟨fun hpD => ?_, fun hpD => ?_⟩
  · obtain ⟨F, hF, he, hw, hup⟩ := hd.1 hpD
    refine ⟨F, fun σ => (β (decomp p σ))⁻¹, hF, he, twistShape_of_tmWild h hw, ?_⟩
    intro t ht σ hσ
    simp only [hup t ht σ hσ, inv_one]
  · obtain ⟨F, hF, he, hw, htame⟩ := hd.2 hpD
    refine ⟨F, fun σ => (β (decomp p σ))⁻¹, hF, he, twistShape_of_tmWild h hw, ?_⟩
    intro σ hσ
    simp only [htame σ hσ, inv_one]

end LocalG

/-! ### §D. The interface over the object; `G15RamG` proved for it -/

/-- **The data of G8-G12 as an object**: the embeddings of g0-mod-newform's `ModData` and the two
descent data at `ℓ = 5`, `ℓ = 3`; the representations are *constructed* (`DescData.r`), not
free fields. -/
structure ModObj (A : PkgI3.AbVar K) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K
  ιC : PkgI4.Qbar →ₐ[ℚ] ℂ
  ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3
  D5 : DescData A 5
  D3 : DescData A 3

/-- The object as g0-mod-newform's `ModData` (`r₅ = D5.r`, `r₃ = D3.r`). The restated interface
is g0-mod-newform's `G12Spec`, `G14TraceCompat`, `G15RamG` applied to `M.toModData` only. -/
def ModObj.toModData {A : PkgI3.AbVar K} (M : ModObj A) : G0ModNewform.ModData K A :=
  ⟨M.i, M.ιC, M.ι5, M.ι3, M.D5.r, M.D3.r⟩

/-- **`G15RamG` for the constructed object (GLUE, proved).** From `LocalDataG` on the descent data
at `5` (for `p ≠ 5`) and at `3` (for `p = 5`), and G2, G3 (for G11's clause (iii)), by g15-ram's
`g15RamG_of_localData`. -/
theorem g15RamG_obj {A : PkgI3.AbVar K} (M : ModObj A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ M.D5.Tm M.D5.a M.D5.β)
    (h3 : LocalDataG 5 M.D3.Tm M.D3.a M.D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    G0ModNewform.G15RamG M.toModData u :=
  G15Ram.g15RamG_of_localData M.toModData u
    (fun p hp hp5 => @localData_of_intertwines p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ M.D5.intertwines
      (h5 p hp hp5))
    (localData_of_intertwines M.D3.intertwines h3)
    (g11_of_intertwines _ h2 h35 M.D5.rho_resQ M.D5.intertwines)
    (g11_of_intertwines _ h2 h33 M.D3.rho_resQ M.D3.intertwines)

/-- **`G15RamG` for every `ModData` whose `r₅`, `r₃` carry G8's intertwining on the data (proved).**
The same proof: only the intertwining is used, so the constructed basis plays no role. -/
theorem g15RamG_of_intertwines {A : PkgI3.AbVar K} (D : G0ModNewform.ModData K A) (u : ℚ)
    (D5 : DescData A 5) (D3 : DescData A 3)
    (e5 : G0Galois.Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (e3 : G0Galois.Vb A 3 ≃ₗ[PadicAlgCl 3] (Fin 2 → PadicAlgCl 3) × (Fin 2 → PadicAlgCl 3))
    (hi5 : G0Galois.Intertwines (GlueDescent.rho D5.Tm D5.a D5.β) D.r5.mat e5)
    (hi3 : G0Galois.Intertwines (GlueDescent.rho D3.Tm D3.a D3.β) D.r3.mat e3)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ D5.Tm D5.a D5.β)
    (h3 : LocalDataG 5 D3.Tm D3.a D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    G0ModNewform.G15RamG D u :=
  G15Ram.g15RamG_of_localData D u
    (fun p hp hp5 => @localData_of_intertwines p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hi5 (h5 p hp hp5))
    (localData_of_intertwines hi3 h3)
    (g11_of_intertwines _ h2 h35 D5.rho_resQ hi5)
    (g11_of_intertwines _ h2 h33 D3.rho_resQ hi3)

end G8Object

end

#print axioms G8Object.DescData.intertwines
#print axioms G8Object.DescData.g8Out
#print axioms G8Object.mat_eq_scalar_of_intertwines
#print axioms G8Object.g11_of_intertwines
#print axioms G8Object.localData_of_intertwines
#print axioms G8Object.g15RamG_obj
#print axioms G8Object.g15RamG_of_intertwines

/-! Copied verbatim from scratch/g0-assemble/parts/87_afterg7.lean L27-123 (the first `open`
line re-issues ModField's file-level opens, which were active there). -/
section G0AssembleAfterG7Sec
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue G3 + G5-G6 on G7's model** (g0-assemble; QM-PIN for the G6 part). For every fibre
context and G7 data of g0-mod-field: `End(A_{L'})` is a noncommutative division ring
(`G0Galois.G6Out`; NoCM, N5 G6), and inertia at primes outside `T(u)` acts trivially on
`ℚ̄_ℓ ⊗ V_ℓ(A_{L'})` for `ℓ = 5, 3` (`G0Galois.G3Out`; G3, good reduction of the QM model away
from `T` with Néron–Ogg–Shafarevich R7a). -/
def ModelG3G6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G6Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 (T u) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 (T u)

/-- Clauses (i)-(ii) of g0-mod-newform's `LocalRamG` (its clause (iii) is G11's output): for
`p ≤ D`, absolute upper ramification groups above `U₀` act trivially; for `p > D`, wild inertia
acts trivially (N5 L819-852, "D1-D4 on G8's `r_ℓ`"). -/
def LocalRamWild (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : PkgI4.GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1)

/-- g0-mod-newform's `G15RamG` without clause (iii): `LocalRamWild` for `r₅` at `p ≠ 5` and for
`r₃` at `p = 5`. -/
def G15RamWild {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : G0ModNewform.ModData L A) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamWild p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamWild p ⟨hp⟩ 3 _ D.r3)

/-- **`G15RamG` from its clauses (i)-(ii) and G11's output** (proved): clause (iii) at
`p ∉ S_mul`, `p ∤ M_{S_mul}(u)` is `G0Galois.G11Out (T u)`, since such `p` is not in
`T u = S_mul ∪ supp M_{S_mul}(u)`. -/
theorem g15RamG_of_wild {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : G0ModNewform.ModData L A) (u : ℚ) (hw : G15RamWild D)
    (h5 : G0Galois.G11Out (T u) D.r5) (h3 : G0Galois.G11Out (T u) D.r3) :
    G0ModNewform.G15RamG D u := by
  intro p hp
  have hT : p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → p ∉ T u := by
    intro hS hM hmem
    simp only [T, GlueDescent.ramSet, Finset.mem_union] at hmem
    rcases hmem with h | h
    · exact hS h
    · exact hM (Nat.dvd_of_mem_primeFactors h)
  refine ⟨fun h5' => ?_, fun h5' => ?_⟩
  · obtain ⟨hi, hii⟩ := (hw p hp).1 h5'
    exact ⟨hi, hii, fun hS hM => h5 p hp (hT hS hM) h5'⟩
  · obtain ⟨hi, hii⟩ := (hw p hp).2 h5'
    exact ⟨hi, hii, fun hS hM => h3 p hp (hT hS hM) (by omega)⟩

/-- **Glue: linked Tate data with G14-G15 on them** (g0-assemble; g0-mod-field's `TateBridge`
at `ℓ = 5, 3` from one descent datum, with g0-mod-newform's `G14TraceCompat` and `G15RamG`).
For every fibre context and G7 data: operator data at `ℓ = 5` and `ℓ = 3` satisfying
g0-mod-galois' `G7Out`, such that for all `r₅`, `r₃` with G8's output on these data and all
embeddings `i`, `ι_ℂ`, `ι₅`, some `ι₃` makes the traces compatible (`G14TraceCompat`, N5 L776-795)
and `r₅`, `r₃` have Glazer's wild local ramification (`G15RamWild`: clauses (i)-(ii) of
g0-mod-newform's `G15RamG`, N5 L819-852; clause (iii) is proved from G11, `g15RamG_of_wild`). -/
def LinkedTateData : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a₅ β₅ : PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a₃ β₃ : PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅ a₅ β₅ u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃ a₃ β₃ u₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ a₅ β₅) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ a₃ β₃) r₃ →
        ∀ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L') (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
          (ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5), ∃ ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3,
          G0ModNewform.G14TraceCompat
            (⟨i, ιC, ι5, ι3, r₅, r₃⟩ : G0ModNewform.ModData L'
              (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) ∧
          G15RamWild
            (⟨i, ιC, ι5, ι3, r₅, r₃⟩ : G0ModNewform.ModData L'
              (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
end HSyn.G0AssembleMod
end G0AssembleAfterG7Sec

/-! ## g8-object, part 2: the full G12-G16 interface on the object; the restated `GluePieces2`
field (`LinkedTateObj`) checked against g0-assemble's `LinkedTateData`

Appended after verbatim copies of g0-mod-field (`ModField.lean`), g14-trace (`G14Trace.lean`,
`part_bridge.lean`), g15-ram (`G15Ram.lean` §1-§3), g0-mod-galois' definitions, part 1
(`part_obj.lean`) and g0-assemble's `87_afterg7.lean` L27-122 (`ModelG3G6`, `LocalRamWild`,
`G15RamWild`, `g15RamG_of_wild`, `LinkedTateData`). -/

noncomputable section

namespace G8Object

open PkgI4 (GQ GQp GaloisRep decomp)
open LadicCond

/-! ### §E. Linked objects: `G12Spec ∧ G14TraceCompat ∧ G15RamG` on the constructed `r_ℓ` -/

section Linked

variable {K : Type} [Field K] [NumberField K]

/-- **The linked object at `ℓ = 5, 3`** (N5 L719-722): the descent data at `5` and `3` (each with
its constructed `r_ℓ`), whose scalars are the images `j_ℓ ∘ aQ`, `j_ℓ ∘ βQ` of one pair
`aQ, βQ : G_ℚ → ℚ̄` (the scalar link of g14-trace), with g14-trace's Frobenius link
`FrobTraceLink` for `Tm₅`, `Tm₃`. -/
structure LinkedObj (A : PkgI3.AbVar K) where
  D5 : DescData A 5
  D3 : DescData A 3
  aQ : GQ → PkgI4.Qbar
  βQ : GQ → PkgI4.Qbar
  j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5
  j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3
  ha5 : D5.a = fun g => j5 (aQ g)
  hb5 : D5.β = fun g => j5 (βQ g)
  ha3 : D3.a = fun g => j3 (aQ g)
  hb3 : D3.β = fun g => j3 (βQ g)
  frob : G14Trace.FrobTraceLink A D5.Tm D3.Tm

/-- G8's output for the constructed `r_ℓ`, in the form g14-trace consumes (scalars written
through the link). -/
theorem LinkedObj.galG8Out5 {A : PkgI3.AbVar K} (Lk : LinkedObj A) (hS : PkgI3.FaltingsSemisimple)
    (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite)
    (hSS : GlueI3.SemisimpleBaseChange) (hB : G0Galois.BurnsideAbsIrred) :
    G0ModNewform.GalG8Out A 5
      (GlueDescent.rho Lk.D5.Tm (fun g => Lk.j5 (Lk.aQ g)) (fun g => Lk.j5 (Lk.βQ g))) Lk.D5.r := by
  have h := Lk.D5.g8Out hS hF hT hH hSS hB
  rw [Lk.ha5, Lk.hb5] at h
  exact h

theorem LinkedObj.galG8Out3 {A : PkgI3.AbVar K} (Lk : LinkedObj A) (hS : PkgI3.FaltingsSemisimple)
    (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite)
    (hSS : GlueI3.SemisimpleBaseChange) (hB : G0Galois.BurnsideAbsIrred) :
    G0ModNewform.GalG8Out A 3
      (GlueDescent.rho Lk.D3.Tm (fun g => Lk.j3 (Lk.aQ g)) (fun g => Lk.j3 (Lk.βQ g))) Lk.D3.r := by
  have h := Lk.D3.g8Out hS hF hT hH hSS hB
  rw [Lk.ha3, Lk.hb3] at h
  exact h

/-- **The restated G12-G15 interface holds on the object (GLUE, proved).** For a linked object,
G12's output for the constructed `r₅` (`GalG12Out`, which g0-mod-galois' `g12` proves for any `r`
with G8's output), the restated local data `LocalDataG` on the descent data, and G2, G3: there is
`M : ModObj A` carrying the two descent data, with g0-mod-newform's `G12Spec`,
`G14TraceCompat` and `G15RamG` on `M.toModData`. Inputs: C2's leaves (R9a, R9b, T26, T6),
glue-ssbc's `SemisimpleBaseChange`, Burnside, T7 (`CharPolyIndepOfEll`) and g0-mod-newform's
`DirichletOfFinite`. -/
theorem interface_obj (hDF : G0ModNewform.DirichletOfFinite) (hM : PkgI3.CharPolyIndepOfEll)
    (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree)
    (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hB : G0Galois.BurnsideAbsIrred) {A : PkgI3.AbVar K} (Lk : LinkedObj A) (u : ℚ)
    (h12 : G0ModNewform.GalG12Out Lk.D5.r)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ Lk.D5.Tm Lk.D5.a Lk.D5.β)
    (h3 : LocalDataG 5 Lk.D3.Tm Lk.D3.a Lk.D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    ∃ M : ModObj A, M.D5 = Lk.D5 ∧ M.D3 = Lk.D3 ∧ G0ModNewform.G12Spec M.toModData ∧
      G0ModNewform.G14TraceCompat M.toModData ∧ G0ModNewform.G15RamG M.toModData u := by
  obtain ⟨⟨i, ιC, ι5, ι3, r5, r3⟩, hD5, hD3, hs, hc⟩ :=
    G14Trace.g12Spec_g14_of_galois hDF hM A Lk.j5 Lk.j3 Lk.aQ Lk.βQ Lk.D5.Tm Lk.D3.Tm Lk.D5.r
      Lk.D3.r (Lk.galG8Out5 hS hF hT hH hSS hB) (Lk.galG8Out3 hS hF hT hH hSS hB) h12 Lk.frob
  dsimp only at hD5 hD3
  subst hD5 hD3
  let M : ModObj A := ⟨i, ιC, ι5, ι3, Lk.D5, Lk.D3⟩
  exact ⟨M, rfl, rfl, hs, hc, g15RamG_obj M u h5 h3 h2 h35 h33⟩

open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof in
/-- **G13-G16 on the object (GLUE, proved).** g0-mod-newform's `modularConstituent_tail_G`, with
its hypothesis `∃ D, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u` discharged by `interface_obj`:
the open inputs are now Props on G7's data (`LocalDataG`, `FrobTraceLink`, the scalar link),
G12's output and the leaves. -/
theorem modularConstituent_tail_obj (lv : G0ModNewform.NewformLeaves) (hJac : LeafModCurves.JacobianExists ℚ)
    (hX : LeafModCurves.X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hDF : G0ModNewform.DirichletOfFinite) (hM : PkgI3.CharPolyIndepOfEll)
    (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree)
    (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hB : G0Galois.BurnsideAbsIrred) {A : PkgI3.AbVar K} (Lk : LinkedObj A) (u : ℚ)
    (h12 : G0ModNewform.GalG12Out Lk.D5.r)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ Lk.D5.Tm Lk.D5.a Lk.D5.β)
    (h3 : LocalDataG 5 Lk.D3.Tm Lk.D3.a Lk.D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      G0ModNewform.CommonConstituent A (J.baseChange K) := by
  obtain ⟨M, -, -, hs, hc, hr⟩ := interface_obj hDF hM hS hF hT hH hSS hB Lk u h12 h5 h3 h2 h35 h33
  exact G0ModNewform.modularConstituent_tail_G lv hJac hX hSw hL8 hAd A u ⟨M.toModData, hs, hc, hr⟩

end Linked

/-! ### §F. The β-clauses on G7's own `β`, and the restated `GluePieces2` field -/

section Restated

variable (p : ℕ) [Fact p.Prime]

/-- **Glue on G7Data's cochain `β : G_ℚ → ℂ^×` (D3 + T16; N5 L832-844).** `β` is trivial on
`G_{ℚ_p}^t ∩ G_F` for `t > U` (through `decomp`). A Prop on `G7Data`'s `β` and the local field
`F` only. -/
def BetaUpperC (βC : GQ → ℂˣ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, βC (decomp p σ) = 1

/-- **Glue on G7Data's `β` at tame primes (N5 L848-851).** `β` is trivial on `G_F ∩ P_p`. -/
def BetaTameC (βC : GQ → ℂˣ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, βC (decomp p σ) = 1

/-- **`LocalDataG` with its `β`-clauses on G7Data's own `β`** (`ℂ^×`-valued). The `Tm`, `a` clause
(`TmWild`) is on the `ℓ`-adic data. -/
def LocalDataC {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (βC : GQ → ℂˣ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TmWild p Tm a F ∧ BetaUpperC p βC F G0ModNewform.U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TmWild p Tm a F ∧ BetaTameC p βC F)

variable {p}

theorem eq_one_of_C {ℓ : ℕ} [Fact ℓ.Prime] {βC : GQ → ℂˣ} {βQ : GQ → PkgI4.Qbar}
    {ιC : PkgI4.Qbar →ₐ[ℚ] ℂ} (hι : ∀ g, ιC (βQ g) = (βC g : ℂ))
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) {g : GQ} (h : βC g = 1) : j (βQ g) = 1 := by
  have h1 : ιC (βQ g) = ιC 1 := by rw [hι, h, Units.val_one, map_one]
  rw [ιC.toRingHom.injective h1, map_one]

/-- **`LocalDataC` gives `LocalDataG` for `j_ℓ ∘ βQ` when `ιC ∘ βQ = β` (proved).** -/
theorem localDataG_of_C {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {βC : GQ → ℂˣ} {βQ : GQ → PkgI4.Qbar} {ιC : PkgI4.Qbar →ₐ[ℚ] ℂ}
    (hι : ∀ g, ιC (βQ g) = (βC g : ℂ)) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (h : LocalDataC p Tm a βC) : LocalDataG p Tm a (fun g => j (βQ g)) := by
  refine ⟨fun hpD => ?_, fun hpD => ?_⟩
  · obtain ⟨F, hF, he, hw, hb⟩ := h.1 hpD
    exact ⟨F, hF, he, hw, fun t ht σ hσ => eq_one_of_C hι j (hb t ht σ hσ)⟩
  · obtain ⟨F, hF, he, hw, hb⟩ := h.2 hpD
    exact ⟨F, hF, he, hw, fun σ hσ => eq_one_of_C hι j (hb σ hσ)⟩

/-- Clauses (i)-(ii) of `LocalRamG` on the descended operator family itself (linked-tate's
`RhoRamWild`, same text; there in namespace `HSyn.LinkedTate`). -/
def RhoRamWild (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, ρ (PkgI4.decomp p σ) = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
      ρ (PkgI4.decomp p σ) = 1)

/-- **`LocalDataG` on the data implies the wild clauses for `ρ = β⁻¹ a Tm` (proved, with
g15-ram's local-field theorems).** For `p ≤ D`, `σ ∈ G_{ℚ_p}^t` with `t > U₀` fixes `F`
(`UpperBreakFix`, from T20/T21) and is wild (`upperWild`), so `a = Tm = 1` (`TmWild`) and
`β = 1` (`BetaUpper`); for `p > D`, wild inertia fixes the tame `F` (`wildFixTame`). So
`LocalDataG` is no weaker than the `ρ`-level form, and strictly smaller in content (the
ramification theory is proved). -/
theorem rhoRamWild_of_localDataG (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V}
    {a β : GQ → PadicAlgCl ℓ} (h : @LocalDataG p ⟨hp⟩ ℓ _ V _ _ Tm a β) :
    RhoRamWild p hp (GlueDescent.rho Tm a β) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hUB : G15Ram.UpperBreakFix p := G15Ram.upperBreakFix_of_hilbertSerre
    (G15Ram.hilbertSerre_of_model (G15Ram.ladicDVRModel_of_Zp G15Ram.ladicDVRModelZp))
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩
  · obtain ⟨F, hF, he, hw, hup⟩ := h.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ G0ModNewform.U0 := by unfold G0ModNewform.U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold G0ModNewform.U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := G15Ram.upperWild t (by linarith) hσ
    obtain ⟨h1, h2⟩ := hw σ ⟨hfix, hwild⟩
    have h3 := hup t ht σ ⟨hσ, hfix⟩
    simp [GlueDescent.rho, h1, h2, h3]
  · obtain ⟨F, hF, he, hw, htame⟩ := h.2 hpD
    have hfix := G15Ram.wildFixTame F hF he hσ
    obtain ⟨h1, h2⟩ := hw σ ⟨hfix, hσ⟩
    have h3 := htame σ ⟨hfix, hσ⟩
    simp [GlueDescent.rho, h1, h2, h3]

theorem toHom_eq_one_of_rho {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {ρ : GQ → Module.End (PadicAlgCl ℓ) V} {r : GaloisRep ℓ 2}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines ρ r.mat e) {g : GQ} (hg : ρ g = 1) : r.toHom g = 1 :=
  toHom_eq_one_of_intertwines h hg

/-- `LocalRamWild` (g0-assemble) for every `r` intertwined with `ρ`, from `RhoRamWild` (proved). -/
theorem localRamWild_of_rhoRamWild (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] {ρ : GQ → Module.End (PadicAlgCl ℓ) V}
    {r : GaloisRep ℓ 2} {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines ρ r.mat e) (hR : RhoRamWild p hp ρ) :
    @HSyn.G0AssembleMod.LocalRamWild p ⟨hp⟩ ℓ _ r := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨fun hp' t ht σ hσ => toHom_eq_one_of_rho h (hR.1 hp' t ht σ hσ),
    fun hp' σ hσ => toHom_eq_one_of_rho h (hR.2 hp' σ hσ)⟩

end Restated

section Field

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent.B2 G0ModField

/-- **The restated `GluePieces2` field (replaces g0-assemble's `LinkedTateData`; GLUE).** For every
fibre context and G7 data: g14-trace's `TateBridge35` conclusion (one pair `aQ, βQ : G_ℚ → ℚ̄`,
embeddings `j₅`, `j₃`, `G7Out` at `ℓ = 5, 3` for the scalars `j_ℓ ∘ aQ`, `j_ℓ ∘ βQ`,
`FrobTraceLink` for `Tm₅`, `Tm₃`, and `ιC ∘ βQ = G7Data's β`), together with the local data of
G15 on these data (`LocalDataC`: `TmWild` on `(Tm_ℓ, j_ℓ ∘ aQ)` and the `β`-clauses on
`G7Data`'s `β`) for `ℓ = 5` at every `p ≠ 5` and for `ℓ = 3` at `p = 5`. Unlike `LinkedTateData`,
it does not mention `r₅`, `r₃`, `G14TraceCompat` or `G15RamG`: those are proved from it
(`linkedTateData_of_obj`). -/
def LinkedTateObj : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
        @LocalDataC p ⟨hp⟩ 5 _ _ _ _ Tm₅ (fun g => j5 (aQ g)) β) ∧
      LocalDataC 5 Tm₃ (fun g => j3 (aQ g)) β

/-- **g0-assemble's `LinkedTateData`, proved from the restated field (GLUE, proved).** Inputs: the
leaf T7 (`PkgI3.CharPolyIndepOfEll`, Mumford §19 Thm 4) and `LinkedTateObj`. For any `r₅`, `r₃`
with G8's output on the linked data and any `ι₅ = j₅ ∘ γ` (`exists_comp_eq`), `ι₃ := j₃ ∘ γ`
gives `G14TraceCompat` (g14-trace's `g14TraceCompat_of_link`), and `G15RamWild` holds by
`rhoRamWild_of_localDataG` (g15-ram's local-field theorems) carried to `r_ℓ` by G8's
intertwiner. -/
theorem linkedTateData_of_obj (hM : PkgI3.CharPolyIndepOfEll) (hO : LinkedTateObj) :
    HSyn.G0AssembleMod.LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h75, h73, hF, ⟨ιC0, hι⟩, hl5, hl3⟩ :=
    hO Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  refine ⟨Tm₅, c₅, ε₅, fun g => j5 (aQ g), fun g => j5 (βQ g), u₅,
    Tm₃, c₃, ε₃, fun g => j3 (aQ g), fun g => j3 (βQ g), u₃, h75, h73, ?_⟩
  intro r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨γ, hγ⟩ := G14Trace.exists_comp_eq ι5 j5
  refine ⟨j3.comp γ, ?_, ?_⟩
  · exact G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp γ, r₅, r₃⟩ j5 j3 γ hγ rfl aQ βQ
      Tm₅ Tm₃ h8₅ h8₃ hF
  · obtain ⟨-, e5, he5, -⟩ := h8₅
    obtain ⟨-, e3, he3, -⟩ := h8₃
    intro p hp
    refine ⟨fun hp5 => ?_, fun hp5 => ?_⟩
    · exact localRamWild_of_rhoRamWild p hp he5
        (rhoRamWild_of_localDataG p hp (@localDataG_of_C p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hι j5
          (hl5 p hp hp5)))
    · subst hp5
      exact localRamWild_of_rhoRamWild 5 hp he3
        (rhoRamWild_of_localDataG 5 hp (localDataG_of_C hι j3 hl3))

end Field

end G8Object

end

#print axioms G8Object.LinkedObj.galG8Out5
#print axioms G8Object.interface_obj
#print axioms G8Object.modularConstituent_tail_obj
#print axioms G8Object.localDataG_of_C
#print axioms G8Object.rhoRamWild_of_localDataG
#print axioms G8Object.localRamWild_of_rhoRamWild
#print axioms G8Object.linkedTateData_of_obj
