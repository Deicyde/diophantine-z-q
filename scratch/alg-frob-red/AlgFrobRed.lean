import ZInQKernel.HDecomp.C10.Link
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Descent.WP3
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
import ZInQKernel.HDecomp.I3Linalg.RhoCont

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

/-!
# unram-tate: `TateBridge` reduced to named glue pieces

Everything above `end G0ModField` is `scratch/g0-mod-field/ModField.lean` verbatim (lines 1-1036),
so `G0ModField.TateBridge` is the statement as written there. Below: the operators
`ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (`opV`, a ring homomorphism, proved), the quaternion matrix units
(`matrixUnits_of_quat`, copied from scratch/unram-tate/QuatUnits.lean), five named glue Props, and
the assembly `tateBridge_of_pieces` (proved).
-/

namespace UnramTate

open G0ModField

/-! ## The Tate functor on additive maps of points -/

section Ops

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `A(\bar K)` as an additive group. -/
abbrev PtA : Type := Additive (A.Pt (AlgebraicClosure K))

/-- `ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` on `Vb A ℓ = ℚ̄_ℓ ⊗ V_ℓ(A)`, for an additive endomorphism `φ` of
`A(\bar K)` (pkg-I3's `Tate.map`, base changed twice). -/
noncomputable def opV (φ : PtA A →+ PtA A) : Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ) :=
  ((PkgI3.Tate.map (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange (PadicAlgCl ℓ)

theorem tateMap_comp (φ ψ : PtA A →+ PtA A) :
    PkgI3.Tate.map (ℓ := ℓ) (φ.comp ψ) = (PkgI3.Tate.map (ℓ := ℓ) φ).comp (PkgI3.Tate.map ψ) := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMap_add (φ ψ : PtA A →+ PtA A) :
    PkgI3.Tate.map (ℓ := ℓ) (φ + ψ) = PkgI3.Tate.map φ + PkgI3.Tate.map ψ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMap_zero : PkgI3.Tate.map (ℓ := ℓ) (0 : PtA A →+ PtA A) = 0 := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMap_id : PkgI3.Tate.map (ℓ := ℓ) (AddMonoidHom.id (PtA A)) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

/-- `opV` is a ring homomorphism `End(A(\bar K)) → End_{ℚ̄_ℓ}(Vb A ℓ)`. -/
noncomputable def opVHom :
    AddMonoid.End (PtA A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ) where
  toFun := opV A ℓ
  map_one' := by
    show opV A ℓ (AddMonoidHom.id _) = 1
    simp only [opV, tateMap_id, LinearMap.baseChange_id]; rfl
  map_mul' f g := by
    show opV A ℓ (f.comp g) = opV A ℓ f * opV A ℓ g
    unfold opV
    rw [tateMap_comp A ℓ f g, LinearMap.baseChange_comp, LinearMap.baseChange_comp]; rfl
  map_zero' := by
    show opV A ℓ 0 = 0
    simp only [opV, tateMap_zero, LinearMap.baseChange_zero]
  map_add' f g := by
    show opV A ℓ (f + g) = opV A ℓ f + opV A ℓ g
    have h1 : PkgI3.Tate.map (ℓ := ℓ) (f + g : AddMonoid.End (PtA A)) =
        PkgI3.Tate.map f + PkgI3.Tate.map g := tateMap_add A ℓ f g
    unfold opV
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_add]

/-- The Tate action is `opV` of the Galois action on points. -/
theorem tate_eq_opV (σ : Field.absoluteGaloisGroup K) :
    GaloisCopy.tate A ℓ σ = opV A ℓ (MonoidHom.toAdditive (A.galAct σ)) := rfl

end Ops

/-- Conjugation by an additive equivalence, a ring homomorphism of endomorphism rings. -/
def conjE {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Θ : M ≃+ N) :
    AddMonoid.End M →+* AddMonoid.End N where
  toFun f := Θ.toAddMonoidHom.comp (f.comp Θ.symm.toAddMonoidHom)
  map_one' := DFunLike.ext _ _ fun x => by
    show Θ (Θ.symm x) = x
    exact Θ.apply_symm_apply x
  map_mul' f g := DFunLike.ext _ _ fun x => by
    show Θ (f (g (Θ.symm x))) = Θ (f (Θ.symm (Θ (g (Θ.symm x)))))
    rw [AddEquiv.symm_apply_apply]
  map_zero' := DFunLike.ext _ _ fun x => by
    show Θ 0 = 0
    exact map_zero Θ
  map_add' f g := DFunLike.ext _ _ fun x => by
    show Θ (f (Θ.symm x) + g (Θ.symm x)) = Θ (f (Θ.symm x)) + Θ (g (Θ.symm x))
    exact map_add Θ _ _

theorem conjE_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Θ : M ≃+ N)
    (f : AddMonoid.End M) (x : N) : conjE Θ f x = Θ (f (Θ.symm x)) := rfl

/-! ## Matrix units (copied from scratch/unram-tate/QuatUnits.lean, proved there) -/

section Quat

open GlueDescent

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

theorem quat_words (P J : Module.End E V) (hPP : P * P = P) (hPJ : P * J = J - J * P)
    (hJJ : J * J = (-3 : E) • (1 : Module.End E V)) :
    (∀ X, P * (P * X) = P * X) ∧ (∀ X, P * (J * X) = J * X - J * (P * X)) ∧
      (∀ X, J * (J * X) = (-3 : E) • X) := by
  refine ⟨fun X => by rw [← _root_.mul_assoc, hPP], fun X => by rw [← _root_.mul_assoc, hPJ, sub_mul, _root_.mul_assoc],
    fun X => by rw [← _root_.mul_assoc, hJJ, smul_mul_assoc, _root_.one_mul]⟩

theorem matrixUnits_of_quat (s : E) (hs : s ^ 2 = 2) (h2 : (2 : E) ≠ 0) (h3 : (3 : E) ≠ 0)
    (I J : Module.End E V) (hI : I * I = (2 : E) • (1 : Module.End E V))
    (hJ : J * J = (-3 : E) • (1 : Module.End E V)) (hIJ : I * J = -(J * I)) :
    ∃ u : MatrixUnits2 E V, ∀ (i j : Fin 2) (T : Module.End E V), Commute T I → Commute T J →
      Commute T (u.e i j) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact h2 hs.symm
  set X : Module.End E V := s⁻¹ • I with hXdef
  have hXX : X * X = 1 := by
    rw [hXdef, smul_mul_smul_comm, hI, smul_smul]
    have : s⁻¹ * s⁻¹ * 2 = 1 := by rw [← hs]; field_simp
    rw [this, one_smul]
  have hXJ : X * J = -(J * X) := by
    rw [hXdef, smul_mul_assoc, hIJ, mul_smul_comm, smul_neg]
  set P : Module.End E V := (2 : E)⁻¹ • (1 + X) with hPdef
  have hPP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, add_mul, _root_.one_mul, mul_add, _root_.mul_one, hXX]
    rw [show (1 + X + (X + 1) : Module.End E V) = (2 : E) • (1 + X) by
      rw [two_smul]; abel, smul_smul]
    congr 1; field_simp
  have hPJ : P * J = J - J * P := by
    rw [hPdef, smul_mul_assoc, mul_smul_comm, add_mul, _root_.one_mul, hXJ, mul_add, _root_.mul_one]
    have h12 : (1 : E) - 2⁻¹ = 2⁻¹ := by field_simp; norm_num
    rw [show J - (2 : E)⁻¹ • (J + J * X) = ((1 : E) - 2⁻¹) • J + (2 : E)⁻¹ • (-(J * X)) by module,
      h12, ← smul_add]
  obtain ⟨wPP, wPJ, wJJ⟩ := quat_words P J hPP hPJ hJ
  let c : E := -(3 : E)⁻¹
  let e : Fin 2 → Fin 2 → Module.End E V := fun i j =>
    if i = 0 then (if j = 0 then P else P * J) else (if j = 0 then c • (J * P) else 1 - P)
  have hc : c * (-3 : E) = 1 := by simp only [c]; field_simp
  refine ⟨⟨e, ?_, ?_⟩, ?_⟩
  · intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp only [e, Fin.zero_eta, Fin.mk_one, Fin.isValue, ite_true, one_ne_zero, zero_ne_one,
        ite_false, _root_.mul_assoc, mul_sub, sub_mul, _root_.mul_one, _root_.one_mul, smul_mul_assoc, mul_smul_comm,
        wPP, wPJ, wJJ, hPP, hPJ, hJ, smul_smul, smul_sub, sub_self, hc, one_smul, mul_zero,
        smul_zero, sub_zero, zero_sub, add_zero, zero_add, neg_zero] <;>
      first | rfl | abel | (simp only [sub_sub_cancel, sub_self, smul_zero]) | skip
  · show P + (1 - P) = 1
    abel
  · intro i j T hTI hTJ
    have hTX : Commute T X := hTI.smul_right _
    have hTP : Commute T P := ((Commute.one_right T).add_right hTX).smul_right _
    fin_cases i <;> fin_cases j
    · exact hTP
    · exact hTP.mul_right hTJ
    · exact (hTJ.mul_right hTP).smul_right _
    · exact (Commute.one_right T).sub_right hTP

end Quat

/-! ## The order elements `i`, `j` of `𝒪` -/

/-- `i ∈ 𝒪`. -/
def iO : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `(1 + j)/2 ∈ 𝒪`. -/
def hO : LeafQM.O := ⟨LeafQM.ofInt ![0, 0, 1, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def jO : LeafQM.O := hO + hO - 1

theorem iO_sq : iO * iO = 1 + 1 := by
  apply Subtype.ext
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, iO]
  ext <;> simp [LeafQM.ofInt] <;> norm_num

theorem jO_sq : jO * jO = -(1 + 1 + 1) := by
  apply Subtype.ext
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_add, Subring.coe_neg,
    Subring.coe_one, jO, hO]
  ext <;> simp [LeafQM.ofInt] <;> norm_num

theorem iO_jO : iO * jO = -(jO * iO) := by
  apply Subtype.ext
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_add, Subring.coe_neg,
    Subring.coe_one, jO, hO, iO]
  ext <;> simp [LeafQM.ofInt] <;> norm_num

/-! ## The named glue pieces -/

/-- **Glue piece TB-i (points of a base change; `\overline{L'} ≅ ℚ̄` over `L'`).** For
`L ≤ L'` with `L'/ℚ` finite Galois and `A/L`: an additive bijection
`Θ : A(ℚ̄) ≅ A_{L'}(\overline{L'})` and `h ∈ G_ℚ` such that `Θ` carries the action of
`h · resQ(σ) · h⁻¹` on `A(ℚ̄)` (an `L`-automorphism of `ℚ̄`) to the action of `σ ∈ G_{L'}` on
`A_{L'}(\overline{L'})`. Proof plan: `A_{L'}(Ω) = A(Ω)` for every `L'`-algebra `Ω` (universal
property of `Over.pullback`, compatible with the group law since the pullback functor is
monoidal), and `Θ` is induced by an `L'`-isomorphism `φ : \overline{L'} ≅ ℚ̄`
(`IsAlgClosure.equiv`); then `h = φ ∘ g` for the embedding `g : ℚ̄ → \overline{L'}` of
`Field.absoluteGaloisGroup.map` (`resQ_comm'`). Not in Mathlib v4.35 as such. -/
def TatePoints : Prop :=
  ∀ (L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L),
    ∃ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      ∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)

/-- **Glue piece TB-ii (base change of endomorphisms).** For `K ≤ L` and `A/K`, a ring
homomorphism `End_K(A) → End_L(A_L)` (`f ↦ f_L`: `Over.pullback` is a monoidal functor, so it
maps monoid morphisms to monoid morphisms and preserves composition, identities and the
pointwise sum). -/
def EndBaseChange : Prop :=
  ∀ (K L : IF) (hKL : K ≤ L) (A : PkgI3.AbVar K),
    Nonempty (PkgI3.AbVar.End A →+*
      PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)))

/-- **Glue piece TB-iii (scalars into `ℚ̄_ℓ`; algebra).** The data of B1/B2 (`a > 0` real,
`c = n/d`, `ε`, `β` complex, with `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` and `∂β = ε`, both constant
on cosets of the open subgroup `G_{L'}` and `1` on it) give `gam : G_ℚ → ℚ̄_ℓ^×` with `∂gam = c`,
constant on `G_{L'}`-cosets and `1` on `G_{L'}`. Proof plan: `gam_ℂ = β/a` satisfies
`gam_σ gam_τ = c(σ,τ) gam_{στ}`; it takes finitely many values (cosets of `G_{L'}`, finite index),
each algebraic (`gam_σ^r ∈ ℚ^×` for `σ^r ∈ G_{L'}`), so they generate a number field
`F ⊆ ℂ`; embed `F → ℚ̄_ℓ` (`IsAlgClosed.lift`). -/
def ScalarTransfer : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (ℓ : ℕ) [Fact ℓ.Prime] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ),
    (∀ σ τ, d σ τ ≠ 0) →
    (∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
    (∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)) →
    (∀ σ, 0 < a σ) →
    (∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ) →
    (∀ k ∈ GQL L', a k = 1 ∧ β k = 1) →
    ∃ gam : GQ → PadicAlgCl ℓ, (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1)

/-- **Glue piece TB-iv (continuity of the Tate representation over `ℚ̄_ℓ`).** For a number
field `K` and `A/K`, every matrix coefficient `σ ↦ f(ρ_ℓ(σ) v)` of `ℚ̄_ℓ ⊗ V_ℓ(A)` is continuous
on `G_K`. From glue-rho-cont (`ZInQKernel/HDecomp/I3Linalg/RhoCont.lean`,
`continuous_galRep_of_tateModuleFree`: continuity on `V_ℓ(A)`, given the leaf I3.M0
`TateModuleFree`) and the finite dimension of `V_ℓ(A)` (same leaf). -/
def TateCont : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (f : Module.Dual (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ)) (v : GaloisCopy.Vb A ℓ),
    Continuous fun σ : Field.absoluteGaloisGroup K => f (GaloisCopy.tate A ℓ σ v)

/-- **Glue piece TB-v (Galois topology).** For finite Galois `L' ⊆ ℚ̄`, `resQ L' : G_{L'} → G_ℚ`
is an open embedding (continuous by Mathlib, `Field.absoluteGaloisGroup.map` is a continuous
homomorphism; injective; `G_{L'}` compact, `G_ℚ` Hausdorff; image `Fix(L')` open, `ResQRange`). -/
def ResQEmbedding : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    Topology.IsOpenEmbedding (@GaloisCopy.resQ L' _ (numberField_of_fd L'))

/-! ## The assembly -/

/-- `ε(σ, k) = 1` for `k ∈ G_L` (inflation and normalization). -/
theorem eps_right_one (L : IF) (ε : GQ → GQ → ℂˣ) (hεc : IsSignCocycle ε)
    (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1) (σ k : GQ) (hk : k ∈ GQL L) : ε σ k = 1 := by
  have h1 : ε σ k = ε σ 1 :=
    hinf σ σ k 1 (fun _ _ => rfl) (fun x hx => by rw [mem_GQL.mp hk x hx]; rfl)
  have h2 := hεc.2.2 σ 1 1
  rw [_root_.mul_one, _root_.one_mul, h11, _root_.one_mul] at h2
  rw [h1]
  exact mul_left_cancel (a := ε σ 1) (by rw [h2, _root_.mul_one])

set_option maxHeartbeats 1000000 in
/-- **`TateBridge` from the five glue pieces** (and the proved `opVHom`, `matrixUnits_of_quat`,
`resQRange`, glue-descent's `rho_map_mul`). `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`,
`c = ε' = n/d` at `(hgh⁻¹, hg'h⁻¹)`, `a = 1`, `β' g = gam(hgh⁻¹)`; the matrix units are those of
`I, J`, the images of `i, j ∈ 𝒪` under `opV(Θ ∘ (QM action on A(ℚ̄)) ∘ Θ⁻¹)`. -/
theorem tateBridge_of_pieces (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransfer)
    (hC : TateCont) (hR : ResQEmbedding) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank ℓ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, -⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(hE K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := hP L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1⟩ := hS L' ℓ a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  -- notation
  let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  let m' : GQ → AddMonoid.End (PtQ L A) := m
  let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
  let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
    ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
  let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
  let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
  -- matrix units
  let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
  have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, iO_sq, map_add, map_one, two_smul]
  have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
    module
  have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
    rw [← map_mul, iO_jO, map_neg, map_mul]
  obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
  have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
    intro g o
    apply Commute.map _ R
    exact hmEnd (cj g) (iot o)
  -- the relations
  have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
    intro g g₂
    have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
      hnd (cj g) (cj g₂)
    have h1 := congrArg R h0
    rw [map_zsmul, map_zsmul, ← hcj] at h1
    have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
      show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
      rw [← map_mul]; exact h1
    have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
        (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
      (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
        (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
    have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
    show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
    rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
    intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
  have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
    intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
  have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hTres : ∀ σ : Field.absoluteGaloisGroup L',
      Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    have hτ := hres σ
    let σ' : Qbar ≃ₐ[L] Qbar :=
      AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
        (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
    have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
    rw [tate_eq_opV]
    show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
    congr 1
    refine DFunLike.ext _ _ fun x => ?_
    show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
    rw [hm]
    show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
    rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
  have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
      GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    unfold GlueDescent.rho
    rw [hTres σ]
    simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
  refine ⟨Tm, c', c', a', β', uu, _hdim, _hrank, hT, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
  -- continuity
  intro f v
  rw [continuous_iff_continuousAt]
  intro g₀
  let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
  have he₀ : Topology.IsOpenEmbedding e₀ :=
    (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
  have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
  have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
      fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
    funext σ
    simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
    rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
  have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
    rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
  rw [he₀.continuousAt_iff, he₀1] at hc
  exact hc

/-! ## Proofs of two pieces -/

/-- **`ResQEmbedding`, proved** (Mathlib Galois topology): `resQ L'` is continuous, injective
(the embedding `g : ℚ̄ → \overline{L'}` of `resQ_comm'` is onto), `G_{L'}` is compact, so it is a
closed embedding, with open image `Fix(L')` (`resQRange`). -/
theorem resQEmbedding : ResQEmbedding := by
  intro L' _ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hIG : IsGalois L' (AlgebraicClosure L') := {}
  haveI : CompactSpace (Field.absoluteGaloisGroup L') :=
    (inferInstance : CompactSpace (AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L'))
  have hcont : Continuous (@GaloisCopy.resQ L' _ hNF) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ L')).continuous_toFun
  obtain ⟨g0, hcomm⟩ := resQ_comm' L'
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L' := g0.toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') := by
    haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
    haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
    exact Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hinj : Function.Injective (@GaloisCopy.resQ L' _ hNF) := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hgbij.2 y
    have h1 := hcomm σ x
    have h2 := hcomm τ x
    rw [hστ] at h1
    exact h1.symm.trans h2
  refine ⟨(hcont.isClosedEmbedding hinj).isEmbedding, ?_⟩
  rw [← MonoidHom.coe_range, resQRange L']
  exact IntermediateField.fixingSubgroup_isOpen L'

set_option maxHeartbeats 1000000 in
/-- **`TateCont`, proved from the leaf I3.M0 `TateModuleFree`** (Mumford §18-19; pkg-I3) and
glue-rho-cont's `continuous_galRep_of_tateModuleFree`: on `ℚ̄_ℓ ⊗ V_ℓ(A)`, `f(ρ(σ)(c ⊗ w)) =
c · f(1 ⊗ ρ_ℓ(σ) w)` and `w ↦ f(1 ⊗ w)` is `ℚ_ℓ`-linear, hence continuous for the module
topology of `V_ℓ(A)`. -/
theorem tateCont_of_tateModuleFree (hT : PkgI3.TateModuleFree) : TateCont := by
  intro K _ _ A ℓ _ f v
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hρ := (PkgI3.continuous_galRep_of_tateModuleFree hT A ℓ hℓ).1
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact continuous_const
  | tmul c w =>
    let g : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ :=
      (f.restrictScalars ℚ_[ℓ]).comp (TensorProduct.mk ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) 1)
    have hg : Continuous g := IsModuleTopology.continuous_of_linearMap g
    have heq : (fun σ : Field.absoluteGaloisGroup K => f (GaloisCopy.tate A ℓ σ (c ⊗ₜ w))) =
        fun σ => c * g (A.galRep ℓ σ w) := by
      funext σ
      show f ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (c ⊗ₜ w)) = _
      rw [LinearMap.baseChange_tmul]
      have : c ⊗ₜ[ℚ_[ℓ]] (A.galRep ℓ σ w) = c • ((1 : PadicAlgCl ℓ) ⊗ₜ[ℚ_[ℓ]] (A.galRep ℓ σ w)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl
    have h3 := hρ.comp (Continuous.prodMk_left (X := Field.absoluteGaloisGroup K) w)
    have h4 := hg.comp h3
    rw [heq]
    exact continuous_const.mul h4
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

/-- **`ScalarTransfer`, proved** (algebra, no leaf). `γ_ℂ = β/a` has `∂γ_ℂ = n/d`, is constant
on `G_{L'}`-cosets and `1` on `G_{L'}`; `γ_ℂ(σ)^r ∈ ℚ` for `σ^r ∈ G_{L'}` (`r` the order of
`σ|_{L'}`), so every value is algebraic; `ψ : ℚ(γ_ℂ(G_ℚ)) → ℚ̄_ℓ` (`IsAlgClosed.lift`) and
`γ = ψ ∘ γ_ℂ`. -/
theorem scalarTransfer : ScalarTransfer := by
  intro L' _ _ ℓ _ a β ε n d hd hna hβe ha0 hcos hone
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range gC)
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨σ, rfl⟩; exact halg σ)
  let ψ : F →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ => IntermediateField.subset_adjoin ℚ _ ⟨σ, rfl⟩
  let gam : GQ → PadicAlgCl ℓ := fun σ => ψ ⟨gC σ, hmem σ⟩
  refine ⟨gam, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro σ k hk
    exact congrArg ψ (Subtype.ext (hgcos σ k hk))
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))

/-- **`TateBridge` from the two remaining glue pieces and the leaf I3.M0** (`TateModuleFree`). -/
theorem tateBridge_of_points (hP : TatePoints) (hE : EndBaseChange)
    (hT : PkgI3.TateModuleFree) : TateBridge :=
  tateBridge_of_pieces hP hE scalarTransfer (tateCont_of_tateModuleFree hT) resQEmbedding

/-! ## `EndBaseChange` (proof copied from scratch/bp-qmmoduli/QMAbVar.lean L533-557, `endBC`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from bp-qmmoduli's `endBC`):
`End_K(A) → End_L(A_L)`, `f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism
(functoriality, and `Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

end BaseChangeEnd

/-- **`EndBaseChange`, proved** (bp-qmmoduli's `endBC`). -/
theorem endBaseChange : EndBaseChange := fun K L hKL A =>
  ⟨@endBC K _ A L _ (incAlg hKL)⟩

/-- **`TateBridge` from the one remaining glue piece `TatePoints` and the leaf I3.M0**
(`PkgI3.TateModuleFree`, Mumford). -/
theorem tateBridge_of_tatePoints (hP : TatePoints) (hT : PkgI3.TateModuleFree) : TateBridge :=
  tateBridge_of_points hP endBaseChange hT

/-! ## `TatePoints` (generic parts copied from scratch/unram-tate/BCPoints.lean) -/

section BCPoints

open scoped CategoryTheory.Obj

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' p q := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr


/-- **`TatePoints`, proved.** `Θ = (trPt φ ∘ bcPt)⁻¹` for `φ : \overline{L'} ≃ₐ[L'] ℚ̄`
(`IsAlgClosure.equiv`), and `h = φ ∘ g` for the onto embedding `g : ℚ̄ → \overline{L'}` of
`resQ_comm'`, so that `h · resQ σ · h⁻¹ = φ σ φ⁻¹`. -/
theorem tatePoints : TatePoints := by
  intro L L' _ _ hLL' A
  haveI hNF : NumberField L' := numberField_of_fd L'
  letI iLL' : Algebra L L' := incAlg hLL'
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tLQ : IsScalarTower L L' Qbar := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic L' Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L'
  haveI : IsAlgClosure L' Qbar := ⟨inferInstance, inferInstance⟩
  let φ : AlgebraicClosure L' ≃ₐ[L'] Qbar := IsAlgClosure.equiv L' (AlgebraicClosure L') Qbar
  let φL : AlgebraicClosure L' ≃ₐ[L] Qbar := φ.restrictScalars L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L'
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L' := g0.toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') := by
    haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
    haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
    exact Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective g0 hgbij
  let hR : Qbar ≃+* Qbar := ge.trans φ.toRingEquiv
  let h : PkgI4.GQ := AlgEquiv.ofRingEquiv (f := hR) (fun q => by
    rw [eq_ratCast (algebraMap ℚ Qbar) q, map_ratCast])
  have hh : ∀ y, h y = φ (g0 y) := fun _ => rfl
  let E := (bcPt (K := L) (L := L') A (AlgebraicClosure L')).trans (trPt A φL)
  refine ⟨E.symm.toAdditive, h, ?_⟩
  intro σ σ' hσ' x
  have hkey : ∀ z, σ' (φL z) = φL ((actK σ).restrictScalars L z) := by
    intro z
    rw [hσ']
    have hinv : h⁻¹ (φ z) = ge.symm z := by
      apply h.injective
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hh]
      show φ z = φ (g0 (ge.symm z))
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z]
    have hres : (@GaloisCopy.resQ L' _ hNF σ) (ge.symm z) = ge.symm (actK σ z) := by
      apply ge.injective
      rw [ge.apply_symm_apply]
      have := hcomm σ (ge.symm z)
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z] at this
      exact this
    show h ((@GaloisCopy.resQ L' _ hNF σ) (h⁻¹ (φ z))) = φ (actK σ z)
    rw [hinv, hres, hh]
    show φ (g0 (ge.symm (actK σ z))) = φ (actK σ z)
    rw [show g0 (ge.symm (actK σ z)) = actK σ z from ge.apply_symm_apply (actK σ z)]
  show Additive.ofMul (E.symm (A.galAct σ' (Additive.toMul x))) =
    Additive.ofMul ((A.baseChange L').galAct (actK σ) (E.symm (Additive.toMul x)))
  congr 1
  apply E.injective
  rw [MulEquiv.apply_symm_apply]
  show A.galAct σ' (Additive.toMul x) = trPt A φL (bcPt A (AlgebraicClosure L')
    ((A.baseChange L').galAct (actK σ) (E.symm (Additive.toMul x))))
  rw [bcPt_galAct, trPt_galAct A φL ((actK σ).restrictScalars L) σ' hkey]
  congr 1
  exact (E.apply_symm_apply (Additive.toMul x)).symm

end BCPoints

/-- **`TateBridge` from the leaf I3.M0 alone** (`PkgI3.TateModuleFree`, Mumford §18-19). -/
theorem tateBridge_of_tateModuleFree (hT : PkgI3.TateModuleFree) : TateBridge :=
  tateBridge_of_tatePoints tatePoints hT

/-! ## `UnramifiedSup` in this context (proof copied from scratch/unram-tate/UnramSup.lean) -/

section Sup

open NumberField

instance instGaloisQbar' : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- A finite intermediate field is a number field. -/
theorem numberField_of_fd'' (L : IF) [FiniteDimensional ℚ L] : NumberField L :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

/-- For a finite Galois `L` unramified at `p` and a prime `P ∋ p` of `𝓞 L`, the inertia group
`I(P) ≤ Gal(L/ℚ)` is trivial (`#I(P) = e(P) = 1`). -/
theorem inertia_trivial' (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (p : ℕ)
    (hL : UnramifiedAt L p) (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P)
    (g : L ≃ₐ[ℚ] L) (hg : g ∈ P.inertia (L ≃ₐ[ℚ] L)) : g = 1 := by
  haveI : NumberField L := numberField_of_fd'' L
  have he : P.ramificationIdx ℤ = 1 := hL P hP hpP
  have hcard : Nat.card (P.inertia (L ≃ₐ[ℚ] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (P.under ℤ) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (L ≃ₐ[ℚ] L), he]
  have hsub : Subsingleton (P.inertia (L ≃ₐ[ℚ] L)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have := Subsingleton.elim (⟨g, hg⟩ : P.inertia (L ≃ₐ[ℚ] L)) 1
  exact congrArg Subtype.val this

/-- `𝓞 E → 𝓞 M` for `E ≤ M`. -/
noncomputable def incO' {E M : IF} (h : E ≤ M) : 𝓞 E →+* 𝓞 M :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom

theorem incO'_coe {E M : IF} (h : E ≤ M) (x : 𝓞 E) :
    (((incO' h x : 𝓞 M) : M) : Qbar) = ((x : E) : Qbar) := rfl

/-- **Restriction of inertia.** If `E ≤ M` are finite Galois, `E` unramified at `p`, `Q ∋ p` a
prime of `𝓞 M` and `g ∈ I(Q)`, then a lift `s ∈ G_ℚ` of `g` fixes `E` pointwise. -/
theorem lift_fixes' (E M : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ M] [IsGalois ℚ E]
    [IsGalois ℚ M] (hEM : E ≤ M) (p : ℕ) (hE : UnramifiedAt E p) (Q : Ideal (𝓞 M))
    [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 M) ∈ Q) (g : M ≃ₐ[ℚ] M)
    (hg : g ∈ Q.inertia (M ≃ₐ[ℚ] M)) (s : Qbar ≃ₐ[ℚ] Qbar)
    (hs : ∀ y : M, s (y : Qbar) = ((g y : M) : Qbar)) :
    ∀ x ∈ E, s x = x := by
  let QE : Ideal (𝓞 E) := Q.comap (incO' hEM)
  haveI : QE.IsPrime := Ideal.comap_isPrime _ _
  have hpQE : ((p : ℤ) : 𝓞 E) ∈ QE := by
    show incO' hEM ((p : ℤ) : 𝓞 E) ∈ Q
    rw [map_intCast]; exact hpQ
  let gE : E ≃ₐ[ℚ] E := s.restrictNormal E
  have hgE : ∀ x : E, ((gE x : E) : Qbar) = s (x : Qbar) :=
    fun x => AlgEquiv.restrictNormal_commutes s E x
  have hmem : gE ∈ QE.inertia (E ≃ₐ[ℚ] E) := by
    rw [Ideal.mem_inertia]
    intro x
    show incO' hEM (gE • x - x) ∈ Q
    have hx : incO' hEM (gE • x) = g • incO' hEM x := by
      apply Subtype.ext; apply Subtype.ext
      show ((gE (x : E) : E) : Qbar) = ((g ((incO' hEM x : 𝓞 M) : M) : M) : Qbar)
      rw [hgE, ← hs]; rfl
    rw [map_sub, hx]
    exact (Ideal.mem_inertia.mp hg) (incO' hEM x)
  have h1 := inertia_trivial' E p hE QE hpQE gE hmem
  intro x hx
  have := hgE ⟨x, hx⟩
  rw [h1] at this
  exact this.symm

/-- **`UnramifiedSup`, proved** (no leaf). -/
theorem unramifiedSup_mf : G0ModField.UnramifiedSup := by
  intro E K _ _ _ _ p hE hK
  let M : IF := E ⊔ K
  haveI : FiniteDimensional ℚ M := inferInstance
  haveI : IsGalois ℚ M := IsGalois.mk
  haveI : NumberField M := numberField_of_fd'' M
  intro Q hQ hpQ
  have htriv : ∀ g ∈ Q.inertia (M ≃ₐ[ℚ] M), g = 1 := by
    intro g hg
    let s : Qbar ≃ₐ[ℚ] Qbar := g.liftNormal Qbar
    have hs : ∀ y : M, s (y : Qbar) = ((g y : M) : Qbar) :=
      fun y => AlgEquiv.liftNormal_commutes g Qbar y
    have hEf := lift_fixes' E M le_sup_left p hE Q hpQ g hg s hs
    have hKf := lift_fixes' K M le_sup_right p hK Q hpQ g hg s hs
    have hE' : E ≤ IntermediateField.fixedField (Subgroup.zpowers s) :=
      (IntermediateField.le_iff_le _ _).mpr
        ((Subgroup.zpowers_le).mpr ((IntermediateField.mem_fixingSubgroup_iff E s).mpr hEf))
    have hK' : K ≤ IntermediateField.fixedField (Subgroup.zpowers s) :=
      (IntermediateField.le_iff_le _ _).mpr
        ((Subgroup.zpowers_le).mpr ((IntermediateField.mem_fixingSubgroup_iff K s).mpr hKf))
    have hM := sup_le hE' hK'
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have hy := hM y.2 ⟨s, Subgroup.mem_zpowers s⟩
    rw [← hs]
    exact hy
  have hcard : Nat.card (Q.inertia (M ≃ₐ[ℚ] M)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q (M ≃ₐ[ℚ] M),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) (Q.under ℤ) Q, hcard]


end Sup

/-- **G2 → G4 → G7 with the twist, without `UnramifiedSup`** (g0-mod-field's `fieldDescentUnr`
with `unramifiedSup_mf`). -/
theorem fieldDescentUnr' (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P :=
  fieldDescentUnr hCover hKer unramifiedSup_mf hHasse hTwo hSq hUnr Y Φ π u P hctx

/-- **Piece 10 without `UnramifiedSup`** (g0-mod-field's `modularConstituent_of_ranges_T14`). -/
theorem modularConstituent_of_ranges_T14' (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges_T14 hCover hKer unramifiedSup_mf hH hR hC hSq hUnr hRest

end UnramTate

#print axioms UnramTate.opVHom
#print axioms UnramTate.matrixUnits_of_quat
#print axioms UnramTate.jO_sq
#print axioms UnramTate.tateBridge_of_pieces
#print axioms UnramTate.resQEmbedding
#print axioms UnramTate.tateCont_of_tateModuleFree
#print axioms UnramTate.scalarTransfer
#print axioms UnramTate.tateBridge_of_points
#print axioms UnramTate.endBaseChange
#print axioms UnramTate.tateBridge_of_tatePoints
#print axioms UnramTate.tatePoints
#print axioms UnramTate.tateBridge_of_tateModuleFree
#print axioms UnramTate.unramifiedSup_mf
#print axioms UnramTate.modularConstituent_of_ranges_T14'

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

#print axioms G14Bridge.tateBridge_five_three_of_35

/-!
# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Appended (by `build.sh`) to verbatim copies of `scratch/unram-tate/TateBridge.lean` (which is
`scratch/g0-mod-field/ModField.lean` L1-1036 plus unram-tate's section `UnramTate`) and of
`scratch/g14-trace/part_bridge.lean` (`G14Bridge.FrobTraceLink`, `G14Bridge.TateBridge35`).

Main result: `FrobTrace.tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree)
(hR : AlgFrobRed) : G14Bridge.TateBridge35`, through the chain of proved implications
`AlgFrobRed → AlgFrobOne → AlgFrobLink` and `tateBridge35_of_algFrobLink`. The operators are
unram-tate's `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (one points-level `m`, one `Θ`,
one `h`), the scalars are `aQ g = βQ g / γQ(hgh⁻¹)` and `βQ` with `ιC ∘ βQ = β` in `ℚ̄` (proved,
`scalarsQbar`), and the conjunct `FrobTraceLink` for these operators is derived from the glue
Prop `AlgFrobRed` (one reduction homomorphism `A(ℚ̄) → Ā(k̄)` intertwining `f = F ∘ - ∘ Spec(σ)`
with an endomorphism of the reduction, bijective on prime-to-`p` torsion).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-! ## The Tate functor on an additive equivalence -/

/-- `T_ℓ(Θ)` for an additive equivalence `Θ : M ≃+ N`, as a `ℤ_ℓ`-linear equivalence. -/
def tateMapEquiv (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Θ : M ≃+ N) : PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ N :=
  LinearEquiv.ofLinear (PkgI3.Tate.map (ℓ := ℓ) Θ.toAddMonoidHom)
    (PkgI3.Tate.map (ℓ := ℓ) Θ.symm.toAddMonoidHom)
    (LinearMap.ext fun x => Subtype.ext (funext fun n => Θ.apply_symm_apply (x.1 n)))
    (LinearMap.ext fun x => Subtype.ext (funext fun n => Θ.symm_apply_apply (x.1 n)))

/-- Conjugation commutes with base change. -/
theorem conj_baseChange {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (f : Module.End R M) :
    (e.baseChange R A M N).conj (f.baseChange A) = (e.conj f).baseChange A := by
  rw [LinearEquiv.conj_apply, LinearEquiv.conj_apply, ← LinearEquiv.baseChange_symm,
    LinearEquiv.coe_baseChange, LinearEquiv.coe_baseChange, LinearMap.baseChange_comp,
    LinearMap.baseChange_comp]

/-! ## The glue Prop: reduction of the algebraic maps `m_σ` modulo `p` -/

/-- **`AlgFrobLink` (GLUE, AV side; Glazer N5 L777-786; reduction of abelian varieties).** Let
`A` be an abelian variety over a finite Galois `L ⊆ ℚ̄` and `m_σ` (`σ ∈ G_ℚ`) additive maps of
`A(ℚ̄)` with three of `DescentDatum`'s clauses, copied verbatim: `m_σ` is the Galois action for
`σ ∈ G_L`; `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L`; and `m_σ` is algebraic,
`m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite surjective morphism of schemes `F_σ : A → A`. Then there
is a finite set `S` of primes such that, for every arithmetic Frobenius `τ` at a place `v` above
`p ∉ S` and every `g ∈ G_ℚ` (`gτg⁻¹` is an arithmetic Frobenius at `g(v)`), there are an
abelian variety `Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and
`N ≠ 0` such that for every prime `ℓ ≠ p` some `ℚ_ℓ`-isomorphism
`ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carries `N · V_ℓ(m_{gτg⁻¹})` to `V_ℓ(α')`.

Why it is true (SPECULATIVE in its Lean details; `N = 1` works): by the first two clauses one
`F_{σ_s}` serves the whole coset `σ_s G_L`, so finitely many morphisms occur (this is the proved
step `algFrobLink_of_one`). Put `σ' = gτg⁻¹` and `w = g(v) ∩ L`, not `v ∩ L`: `σ'` lies in the
decomposition group of `g(v)`. Put in `S` the primes of bad reduction of `A` and the primes below
which some `F_{σ_s}` does not extend to the abelian scheme. For `p ∉ S`, `Ā` is the reduction of
`A` at `w` over `k = κ(w)`. On prime-to-`p` torsion, reduction is a bijection
`A(ℚ̄)[ℓⁿ] ≅ Ā(k̄)[ℓⁿ]` (leaf I2-Red, `PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1).
Under it, `σ'` acting on coordinates becomes the `p`-power map of `k̄` (`IsArithFrob`), which on
`k̄`-points is the absolute Frobenius of `Ā`, and `F_{σ'}` becomes its reduction `F̄_{σ'}` (Néron
mapping property of the abelian scheme, leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme`). So
`m_{σ'}` becomes `α' = F̄_{σ'} ∘ Fr_Ā`, a `k`-morphism
fixing `0`, hence an endomorphism of `Ā`, the same for every `ℓ ≠ p`. -/
def AlgFrobLink : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (m : GQ → (PtQ L A →+ PtQ L A)),
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ g : PkgI4.GQ,
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
            ∃ Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ,
              Ψ.conj ((N : ℚ_[ℓ]) •
                  (PkgI3.Tate.map (ℓ := ℓ) (m (g * τ * g⁻¹))).baseChange ℚ_[ℓ]) =
                (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]

/-- **`AlgFrobOne` (GLUE, AV side; Glazer N5 L777-786; reduction of one morphism modulo `p`).**
`AlgFrobLink` for a single morphism of schemes. Let `A` be an abelian variety over a finite Galois
`L ⊆ ℚ̄` and `F : A → A` a finite surjective morphism of schemes. There is a finite set `S` of
primes such that: for every arithmetic Frobenius `τ` at a place `v` above `p ∉ S`, every
`g ∈ G_ℚ`, and every additive map `f` of `A(ℚ̄)` of the form `f(x) = F ∘ x ∘ Spec(gτg⁻¹)`, there
are an abelian variety `Ā` over a field `k` of characteristic `p`, `α' ∈ End(Ā)` and `N ≠ 0`
such that for every prime `ℓ ≠ p` some `ℚ_ℓ`-isomorphism `ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carries
`N · V_ℓ(f)` to `V_ℓ(α')`.

Why it is true (SPECULATIVE in its Lean details; `N = 1` works). If such an `f` exists, `F` lies
over `Spec(s)` with `s = (gτg⁻¹)⁻¹|_L`, which is in the decomposition group of `w = g(v) ∩ L`;
so `F` is an `L`-morphism `A → A^{(s)}`. Put in `S` the primes below which `A` has bad
reduction or this `L`-morphism does not extend to the abelian-scheme models (spreading out; one
condition: `s` is determined by `F`, since `Γ(A, 𝒪) = L`; `S` depends on `F` only). For `p ∉ S`,
`Ā` is the reduction of `A` at `w`, over `k = κ(w)`. Reduction is a bijection on prime-to-`p`
torsion (leaf I2-Red, `PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1); under it,
`gτg⁻¹` acting on coordinates becomes the `p`-power map of `k̄`, i.e. the absolute Frobenius
`Fr_Ā` on `k̄`-points, and `F` becomes its reduction `F̄` (leaf I2-NMP,
`PkgI2.NeronMappingAbelianScheme`). So `f` becomes `F̄ ∘ Fr_Ā`, which lies over `Spec(id_k)`
and fixes `0` (`f` is additive), hence `α' := F̄ ∘ Fr_Ā ∈ End(Ā)` (rigidity, Mumford §4 Cor. 1,
UNVERIFIED locator), the same for every `ℓ ≠ p`. -/
def AlgFrobOne : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ (g : PkgI4.GQ)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
            ∃ Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ,
              Ψ.conj ((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) =
                (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]

/-- **`AlgFrobLink` from `AlgFrobOne` (proved).** The maps `m_σ` take only finitely many shapes:
for each `s ∈ Gal(L/ℚ)` fix one `σ_s` restricting to `s`; then
`m_{σ_s k}(x) = F_{σ_s} ∘ x ∘ Spec(σ_s k)` for `k ∈ G_L` (second and first clauses), so one
morphism `F_{σ_s}` serves the whole coset, and `S` is the union of the `|Gal(L/ℚ)|` sets
`AlgFrobOne` gives for the `F_{σ_s}`. -/
theorem algFrobLink_of_one (hO : AlgFrobOne) : AlgFrobLink := by
  classical
  intro L _ _ A m hmL hmLL hFalg
  obtain ⟨F, hF⟩ := hFalg
  let res : GQ →* (L ≃ₐ[ℚ] L) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L
  -- a representative of each restriction class
  let rep : (L ≃ₐ[ℚ] L) → GQ := fun s =>
    if h : ∃ σ : GQ, res σ = s then h.choose else 1
  have hrep : ∀ σ : GQ, res (rep (res σ)) = res σ := by
    intro σ
    have h : ∃ σ' : GQ, res σ' = res σ := ⟨σ, rfl⟩
    simp only [rep, h, dite_true]
    exact h.choose_spec
  choose Sf hSf using fun s : L ≃ₐ[ℚ] L => hO L A (F (rep s)) (hF (rep s)).1 (hF (rep s)).2.1
  refine ⟨Finset.univ.biUnion Sf, fun p hp hpS v τ hv hτ g => ?_⟩
  let σ' : GQ := g * τ * g⁻¹
  let σ0 : GQ := rep (res σ')
  have hpS0 : p ∉ Sf (res σ') := fun h' =>
    hpS (Finset.mem_biUnion.mpr ⟨res σ', Finset.mem_univ _, h'⟩)
  -- `k = σ0⁻¹ σ' ∈ G_L`
  have hk : σ0⁻¹ * σ' ∈ GQL L := by
    have h1 : res (σ0⁻¹ * σ') = 1 := by
      rw [map_mul, map_inv, hrep, inv_mul_cancel]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L _).mp h1 x hx
  have hσ' : σ' = σ0 * (σ0⁻¹ * σ') := by group
  have hf : ∀ x : PtQ L A, (Additive.toMul (m σ' x)).left =
      Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ F σ0 := by
    intro x
    have hm : m σ' = (m σ0).comp (m (σ0⁻¹ * σ')) := by
      conv_lhs => rw [hσ']
      exact (hmLL σ0 _ hk).1
    have hmk := hmL (σ0⁻¹ * σ') (toLAut _ hk) (fun _ => rfl)
    rw [hm, AddMonoidHom.comp_apply, (hF σ0).2.2, hmk]
    show Spec.map (CommRingCat.ofHom ((act σ0 : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (PkgI3.AbVar.galHom (toLAut _ hk) ≫ Additive.toMul x).left ≫ F σ0 = _
    have hSpec : Spec.map (CommRingCat.ofHom ((act σ0 : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        Spec.map (CommRingCat.ofHom ((toLAut _ hk : Qbar ≃ₐ[L] Qbar) : Qbar →+* Qbar)) =
        Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext y
      have h0 : σ0 * (σ0⁻¹ * σ') = σ' := by group
      exact congrArg (fun s : GQ => act s y) h0
    rw [← hSpec, Category.assoc]
    rfl
  exact hSf (res σ') p hp hpS0 v τ hv hτ g (m σ') hf

/-! ## `AlgFrobOne` from a reduction homomorphism on points -/

/-- `T_ℓ(r)` is bijective if `r` is injective on `ℓ`-power torsion and every `ℓⁿ`-torsion point
of the target has an `ℓⁿ`-torsion preimage. -/
theorem tateMap_bijective (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (r : M →+ N)
    (hinj : ∀ (n : ℕ) (x : M), (ℓ ^ n) • x = 0 → r x = 0 → x = 0)
    (hsurj : ∀ (n : ℕ) (y : N), (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ r x = y) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) r) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    funext n
    exact hinj n (x.1 n) (PkgI3.Tate.pow_smul_eq_zero x.2 n)
      (congrFun (congrArg Subtype.val hx) n)
  · intro y
    choose X hX using fun n => hsurj n (y.1 n) (PkgI3.Tate.pow_smul_eq_zero y.2 n)
    have h0 : X 0 = 0 := by simpa using (hX 0).1
    have hs : ∀ n, ℓ • X (n + 1) = X n := by
      intro n
      have := hinj n (ℓ • X (n + 1) - X n) (by
          rw [smul_sub, smul_smul, ← pow_succ, (hX (n + 1)).1, (hX n).1, sub_zero])
        (by rw [map_sub, map_nsmul, (hX (n + 1)).2, (hX n).2, y.2.2 n, sub_self])
      exact sub_eq_zero.mp this
    exact ⟨⟨X, h0, hs⟩, Subtype.ext (funext fun n => (hX n).2)⟩

/-- **`AlgFrobRed` (GLUE, AV side; Glazer N5 L777-786; the reduction map).** `AlgFrobOne` with
the `ℓ`-adic isomorphisms replaced by one homomorphism on points: for `F`, `S`, `p ∉ S`, `τ`, `g`
and `f(x) = F ∘ x ∘ Spec(gτg⁻¹)` as in `AlgFrobOne`, there are an abelian variety `Ā` over a
field `k` of characteristic `p`, `α' ∈ End(Ā)`, `N ≠ 0` and a group homomorphism
`red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`, injective on `ℓ`-power torsion and with
every `ℓⁿ`-torsion point of `Ā(k̄)` the image of an `ℓⁿ`-torsion point, for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`). `S` as in `AlgFrobOne`. Let
`v' = g(v)`, at which `σ' = gτg⁻¹` is an arithmetic Frobenius, `w = v' ∩ L`, `𝒜` the abelian
scheme over `O_w`, `Ā` its special fibre over `k = κ(w)`. `red` is the reduction map
`A(ℚ̄) = 𝒜(O_{v'}) → Ā(κ(v'))` (valuative criterion of properness), followed by a `k`-isomorphism
`κ(v') ≅ k̄`. Since `σ'` preserves `O_{v'}` and `F` extends to `𝒜` (leaf I2-NMP), `f` lifts to
`𝒜(O_{v'})` and reduces to `x̄ ↦ F̄ ∘ x̄ ∘ Spec(Frob_p) = (F̄ ∘ Fr_Ā)(x̄)`, which is
`α' := F̄ ∘ Fr_Ā ∈ End(Ā)` (see `AlgFrobOne`). The torsion clauses are leaf I2-Red
(`PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1) for `m = ℓⁿ`, prime to `p`. -/
def AlgFrobRed : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ (g : PkgI4.GQ)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobOne` from `AlgFrobRed` (proved):** `Ψ = ℚ_ℓ ⊗ T_ℓ(red)`. -/
theorem algFrobOne_of_red (hR : AlgFrobRed) : AlgFrobOne := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hR L A F hF1 hF2
  refine ⟨S, fun p hp hpS v τ hv hτ g f hf => ?_⟩
  obtain ⟨k, _, hk, Ab, α, N, hN, red, hred, hbij⟩ := hS p hp hpS v τ hv hτ g f hf
  refine ⟨k, _, hk, Ab, α, N, hN, fun ℓ _ hℓp => ?_⟩
  let Ψ0 := LinearEquiv.ofBijective (PkgI3.Tate.map (ℓ := ℓ) red)
    (tateMap_bijective ℓ red (fun n => (hbij ℓ (Fact.out) hℓp n).1)
      (fun n => (hbij ℓ (Fact.out) hℓp n).2))
  refine ⟨Ψ0.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _, ?_⟩
  have h1 : Ψ0.conj (N • PkgI3.Tate.map (ℓ := ℓ) f) = PkgI3.AbVar.homT (ℓ := ℓ) α := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := Ψ0.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    funext n
    show (PkgI3.Tate.map red ((N • PkgI3.Tate.map f) w)).1 n =
      (PkgI3.AbVar.homT (ℓ := ℓ) α (PkgI3.Tate.map red w)).1 n
    rw [LinearMap.smul_apply, map_nsmul]
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, PkgI3.Tate.map_apply, PkgI3.AbVar.homT]
    rw [← map_nsmul, hred]
  have h2 : (N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ] =
      (N • PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ] := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ] N (PkgI3.Tate.map (ℓ := ℓ) f), LinearMap.baseChange_smul,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, conj_baseChange, h1]

/-! ## From the points-level comparison to `FrobCompare` for `opV(Θ ∘ f ∘ Θ⁻¹)` -/

/-- The comparison for `f` on `V_ℓ(A(ℚ̄))` gives the kernel's `FrobCompare` for the transported
operator `opV(Θ ∘ f ∘ Θ⁻¹)` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, for any additive bijection `Θ`. -/
theorem frobCompare_opV_conjE {L : IF} (A : PkgI3.AbVar L) {K : Type} [Field K]
    (A' : PkgI3.AbVar K) (Θ : PtQ L A ≃+ PtA A') (f : PtQ L A →+ PtQ L A)
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] (Ab : PkgI3.AbVar k)
    (α : PkgI3.AbVar.End Ab) (N : ℕ)
    (Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (hΨ : Ψ.conj ((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) =
      (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]) :
    GlueC10Link.FrobCompare ℓ (opV A' ℓ (conjE Θ f)) α N := by
  let e := tateMapEquiv ℓ Θ
  let Ψ' : A'.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ :=
    (e.symm.baseChange ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtA A')) (PkgI3.Tate.T ℓ (PtQ L A))).trans Ψ
  refine ⟨Ψ'.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) (A'.V ℓ) (Ab.V ℓ), ?_⟩
  -- the `ℚ_ℓ`-level identity
  have h1 : Ψ'.conj ((N : ℚ_[ℓ]) •
      (PkgI3.Tate.map (ℓ := ℓ) (conjE Θ f)).baseChange ℚ_[ℓ]) =
      (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ] := by
    rw [← hΨ]
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply]
    show (e.symm.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans Ψ _ = _
    rw [LinearEquiv.trans_apply]
    congr 1
    rw [LinearEquiv.symm_trans_apply]
    generalize Ψ.symm x = y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q t =>
      rw [← LinearEquiv.baseChange_symm, LinearEquiv.symm_symm, LinearEquiv.baseChange_tmul,
        LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, map_smul, LinearEquiv.baseChange_tmul]
      congr 2
      apply Subtype.ext
      funext n
      show Θ.symm (Θ (f (Θ.symm (Θ (t.1 n))))) = f (t.1 n)
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  -- base change to `ℚ̄_ℓ`
  have h2 : ((N : PadicAlgCl ℓ) • opV A' ℓ (conjE Θ f)) =
      (((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) (conjE Θ f)).baseChange ℚ_[ℓ])).baseChange
        (PadicAlgCl ℓ) := by
    rw [LinearMap.baseChange_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rfl
  rw [h2, conj_baseChange, h1]

/-! ## Rescaling the scalars of `G7Out` -/

/-- `G7Out` is preserved by multiplying `a` and `β` by one nonzero `φ` that is `1` on `G_K`
(with `ε` multiplied by `∂φ`); `ρ = β⁻¹ a T` does not change. -/
theorem g7Out_rescale {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β a₂ β₂ φ : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (hφ0 : ∀ g, φ g ≠ 0) (hφ1 : ∀ σ, φ (GaloisCopy.resQ K σ) = 1)
    (ha₂ : ∀ g, a₂ g = φ g * a g) (hβ₂ : ∀ g, β₂ g = φ g * β g)
    (h : GaloisCopy.G7Out A ℓ Tm c ε a β u) :
    GaloisCopy.G7Out A ℓ Tm c (fun g g₂ => ε g g₂ * (φ g * φ g₂ / φ (g * g₂))) a₂ β₂ u := by
  obtain ⟨hdim, hrk, hT, ha, hβ, hβ0, hres, hcomm, hcont⟩ := h
  have hrho : ∀ g, GlueDescent.rho Tm a₂ β₂ g = GlueDescent.rho Tm a β g := by
    intro g
    unfold GlueDescent.rho
    rw [ha₂, hβ₂]
    congr 1
    have h0 := hφ0 g
    have h1 := hβ0 g
    field_simp
  refine ⟨hdim, hrk, hT, fun g g₂ => ?_, fun g g₂ => ?_, fun g => ?_, fun σ => ?_, hcomm, ?_⟩
  · rw [ha₂, ha₂, ha₂]
    have h0 := hφ0 (g * g₂)
    have := ha g g₂
    calc φ g * a g * (φ g₂ * a g₂) * c g g₂ = φ g * φ g₂ * (a g * a g₂ * c g g₂) := by ring
      _ = φ g * φ g₂ * (ε g g₂ * a (g * g₂)) := by rw [this]
      _ = ε g g₂ * (φ g * φ g₂ / φ (g * g₂)) * (φ (g * g₂) * a (g * g₂)) := by
        field_simp
  · rw [hβ₂, hβ₂, hβ₂]
    have h0 := hφ0 (g * g₂)
    have := hβ g g₂
    calc φ g * β g * (φ g₂ * β g₂) = φ g * φ g₂ * (β g * β g₂) := by ring
      _ = φ g * φ g₂ * (ε g g₂ * β (g * g₂)) := by rw [this]
      _ = ε g g₂ * (φ g * φ g₂ / φ (g * g₂)) * (φ (g * g₂) * β (g * g₂)) := by
        field_simp
  · rw [hβ₂]; exact mul_ne_zero (hφ0 g) (hβ0 g)
  · obtain ⟨h1, h2, h3⟩ := hres σ
    exact ⟨h1, by rw [ha₂, hφ1, h2, _root_.one_mul], by rw [hβ₂, hφ1, h3, _root_.one_mul]⟩
  · intro f v
    have : (fun g => f (GlueDescent.rho Tm a₂ β₂ g v)) = fun g => f (GlueDescent.rho Tm a β g v) :=
      funext fun g => by rw [hrho]
    rw [this]
    exact hcont f v

/-! ## The scalars in `ℚ̄` -/

/-- **The scalar link (proved, no leaf).** From the data of B1/B2 (`a > 0` real, `c = n/d`,
`ε` a sign cocycle with `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}`, `∂β = ε`, `a = β = 1` on `G_{L'}`):
`γQ : G_ℚ → ℚ̄^×` with `∂γQ = c` and `γQ = 1` on `G_{L'}` (the algebraic form of `β/a`), and
`βQ : G_ℚ → ℚ̄` with `ιC ∘ βQ = β` for one embedding `ιC : ℚ̄ → ℂ`. The values of `β/a` and of `β`
are algebraic because their `r`-th powers lie in `ℚ`, resp. are `±1`, where `r` is the order of
`σ|_{L'}`. -/
theorem scalarsQbar (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (hε2 : ∀ σ τ, ε σ τ ^ 2 = 1)
    (ha0 : ∀ σ, 0 < a σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gamQ βQ : GQ → Qbar) (ιC : Qbar →ₐ[ℚ] ℂ), (∀ σ, gamQ σ ≠ 0) ∧
      (∀ σ τ, gamQ σ * gamQ τ = ((n σ τ : Qbar) / (d σ τ : Qbar)) * gamQ (σ * τ)) ∧
      (∀ k ∈ GQL L', gamQ k = 1) ∧ (∀ σ, ιC (βQ σ) = (β σ : ℂ)) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) /
        ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  -- `β` is algebraic: `β(σ)^r = ±1`
  have hpowβ : ∀ (σ : GQ) (k : ℕ), ∃ e : ℂ, e ^ 2 = 1 ∧
      (β σ : ℂ) ^ k = e * (β (σ ^ k) : ℂ) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by norm_num, by rw [pow_zero, pow_zero, (hone 1 (one_mem _)).2]; simp⟩
    | succ k ih =>
      obtain ⟨e, he, hk⟩ := ih
      refine ⟨e * (ε (σ ^ k) σ : ℂ), ?_, ?_⟩
      · rw [mul_pow, he, _root_.one_mul, ← Units.val_pow_eq_pow_val, hε2, Units.val_one]
      · rw [pow_succ, hk, _root_.mul_assoc, ← Units.val_mul, hβe, Units.val_mul, pow_succ]
        ring
  have halgβ : ∀ σ, IsIntegral ℚ (β σ : ℂ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨e, he, ht⟩ := hpowβ σ r
    rw [(hone _ hr).2, Units.val_one, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ (r * 2) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [Polynomial.eval₂_sub, pow_mul, ht, he]
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (Set.range gC ∪ Set.range (fun σ => (β σ : ℂ)))
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    · exact halg σ
    · exact halgβ σ)
  let ψ : F →ₐ[ℚ] Qbar := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨σ, rfl⟩)
  have hmemβ : ∀ σ, (β σ : ℂ) ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨σ, rfl⟩)
  letI : Algebra F Qbar := ψ.toAlgebra
  haveI : IsScalarTower ℚ F Qbar := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  haveI : Algebra.IsAlgebraic F Qbar :=
    Algebra.IsAlgebraic.extendScalars (R := ℚ) (algebraMap ℚ F).injective
  let ιF : Qbar →ₐ[F] ℂ := IsAlgClosed.lift
  let ιC : Qbar →ₐ[ℚ] ℂ := ιF.restrictScalars ℚ
  have hιψ : ∀ x : F, ιC (ψ x) = x := fun x => ιF.commutes x
  refine ⟨fun σ => ψ ⟨gC σ, hmem σ⟩, fun σ => ψ ⟨β σ, hmemβ σ⟩, ιC, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ
    exact hιψ ⟨β σ, hmemβ σ⟩

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
/-- **`TateBridge35` from the leaf I3.M0 (`TateModuleFree`) and the glue `AlgFrobLink`.**
`Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (unram-tate's operators, built from the one
points-level descent datum `m` of `G7Data`), `aQ g = βQ g / γQ(hgh⁻¹)`, `βQ` with `ιC ∘ βQ = β`
(`scalarsQbar`), `j_ℓ = IsAlgClosed.lift`. `G7Out` at `ℓ` is unram-tate's construction with
`γ = j_ℓ ∘ γQ`, rescaled by `φ = j_ℓ(βQ)/j_ℓ(γQ(h·h⁻¹))` (`g7Out_rescale`). `FrobTraceLink`
comes from `AlgFrobLink` (applied to `m` with `g = h`) via `frobCompare_opV_conjE`, with
`S ∪ {3, 5}`. -/
theorem tateBridge35_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : AlgFrobLink) :
    G14Bridge.TateBridge35 := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, hFalg⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gamQ, βQ, ιC, hg0, hgc, hg1, hιβ⟩ := scalarsQbar L' a β ε n d hd hna hβe hεc.2.1 ha0
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hβQ0 : ∀ g, βQ g ≠ 0 := by
    intro g h0
    have := hιβ g
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k, k ∈ GQL L' → βQ k = 1 := by
    intro k hk
    apply ιC.toRingHom.injective
    show ιC (βQ k) = ιC 1
    rw [hιβ, hβL' k hk, map_one, Units.val_one]
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  -- the operators and `G7Out` at one `ℓ`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        @GaloisCopy.G7Out L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _
          (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
            (conjE Θ (m (h * g * h⁻¹)))) c ε'
          (fun g => j (βQ g / gamQ (h * g * h⁻¹))) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let gam : GQ → PadicAlgCl ℓ := fun σ => j (gamQ σ)
    have hgam0 : ∀ σ, gam σ ≠ 0 := fun σ => (map_ne_zero j).mpr (hg0 σ)
    have hgamc : ∀ σ τ, gam σ * gam τ =
        ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ) := by
      intro σ τ
      show j _ * j _ = _ * j _
      rw [← map_mul, hgc, map_mul, map_div₀, map_intCast, map_intCast]
    have hgam1 : ∀ k ∈ GQL L', gam k = 1 := by
      intro k hk; show j _ = 1; rw [hg1 k hk, map_one]
    -- (from here: unram-tate's `tateBridge_of_pieces`, with this `gam`)
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
    have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
      show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
      group
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    have hTm : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
    have hnorm : (L'.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
    have hres : ∀ σ : Field.absoluteGaloisGroup L',
        cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact hnorm.conj_mem _ this h
    have hres0 : ∀ σ : Field.absoluteGaloisGroup L',
        (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact this
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
    have hG7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c' c' a' β' uu := by
      refine ⟨_hdim, _hrank, hTm, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
        fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
      intro f v
      rw [continuous_iff_continuousAt]
      intro g₀
      let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
      have he₀ : Topology.IsOpenEmbedding e₀ :=
        (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
      have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
      have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
          fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
        funext σ
        simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
        rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hTm ha hβ hβ0, hrho1, Module.End.mul_apply]
      have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
        rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
      rw [he₀.continuousAt_iff, he₀1] at hc
      exact hc
    -- rescale by `φ = j(βQ)/γ(h·h⁻¹)`
    let φ : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g) / gam (cj g)
    have hφ0 : ∀ g, φ g ≠ 0 := fun g =>
      div_ne_zero ((map_ne_zero j).mpr (hβQ0 g)) (hgam0 _)
    have hφ1 : ∀ σ, φ (@GaloisCopy.resQ L' _ hNF σ) = 1 := by
      intro σ
      show j (βQ _) / gam (cj _) = 1
      rw [hβQ1 _ (hres0 σ), hgam1 _ (hres σ), map_one, div_one]
    refine ⟨c', _, uu, g7Out_rescale _ ℓ Tm c' c' a' β' _ _ φ uu hφ0 hφ1 (fun g => ?_)
      (fun g => ?_) hG7⟩
    · show j (βQ g / gamQ (cj g)) = j (βQ g) / j (gamQ (cj g)) * 1
      rw [map_div₀, _root_.mul_one]
    · show j (βQ g) = j (βQ g) / gam (cj g) * gam (cj g)
      rw [div_mul_cancel₀ _ (hgam0 _)]
  let j5 : Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 j3
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, j5, j3, _, c5, ε5, u5, _, c3, ε3, u3, h5, h3,
    ?_, ιC, hιβ⟩
  -- `FrobTraceLink` from `AlgFrobLink`
  obtain ⟨S, hS⟩ := hF L A m hmL hmLL hFalg
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  exact ⟨k, _, hk, Ab, α, N', hN',
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3,
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5⟩

/-- **Main result: `TateBridge35` from the leaf I3.M0 and the single-morphism glue
`AlgFrobOne`.** -/
theorem tateBridge35_of_algFrobOne (hT : PkgI3.TateModuleFree) (hO : AlgFrobOne) :
    G14Bridge.TateBridge35 :=
  tateBridge35_of_algFrobLink hT (algFrobLink_of_one hO)

/-- **Main result, finest form: `TateBridge35` from the leaf I3.M0 and the glue `AlgFrobRed`
(the reduction homomorphism on points).** -/
theorem tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree) (hR : AlgFrobRed) :
    G14Bridge.TateBridge35 :=
  tateBridge35_of_algFrobOne hT (algFrobOne_of_red hR)

end FrobTrace

end

#print axioms FrobTrace.tateMapEquiv
#print axioms FrobTrace.conj_baseChange
#print axioms FrobTrace.frobCompare_opV_conjE
#print axioms FrobTrace.g7Out_rescale
#print axioms FrobTrace.scalarsQbar
#print axioms FrobTrace.tateBridge35_of_algFrobLink
#print axioms FrobTrace.algFrobLink_of_one
#print axioms FrobTrace.tateBridge35_of_algFrobOne
#print axioms FrobTrace.tateMap_bijective
#print axioms FrobTrace.algFrobOne_of_red
#print axioms FrobTrace.tateBridge35_of_algFrobRed

/-!
# mul-rigidity: the textbook leaf `RigidityHom` proved from Mathlib

`RigidityHom` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4‴). The proof
follows Mathlib's proof that proper geometrically integral group schemes are commutative
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, Stacks 0BFD),
with the commutator replaced by an arbitrary `c : G ⊗ G ⟶ Z` that is constant on `{e} × G` and on
`G × {e}` (the rigidity lemma, Mumford §4).
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {K : Type u} [Field K]

theorem isClosedImmersion_point (G : Over (Spec (.of K))) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity lemma (two-sided form), over an algebraically closed field.** Let `G` be proper
over `K` with `G ×_K G` integral, `Z` separated of finite type, and `c : G × G → Z` with
`c(e, y) = z` and `c(x, e) = z` (as morphisms, for all `T`-points). Then `c` is constant. -/
theorem rigidity_algClosed [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ G) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z) (c : G ⊗ G ⟶ Z)
    (h1 : ∀ (T : Over (Spec (.of K))) (y : T ⟶ G), lift (toUnit T ≫ e) y ≫ c = toUnit T ≫ z)
    (h2 : ∀ (T : Over (Spec (.of K))) (x : T ⟶ G), lift x (toUnit T ≫ e) ≫ c = toUnit T ≫ z) :
    c = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion e.left := isClosedImmersion_point G e
  have : Nonempty G.left := ⟨e.left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (c.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift e z).left ≫ (fst G Z).left) := by
    simpa using inferInstanceAs (IsClosedImmersion e.left)
  have : IsClosedImmersion (lift e z).left := .of_comp _ (g := (fst G Z).left)
  let gm : G ⊗ G ⟶ G ⊗ Z := lift (fst _ _) c
  have : IsProper (gm.left ≫ (fst G Z).left) := by simpa [gm]
  have : IsProper gm.left := .of_comp _ (fst G Z).left
  ext1
  have H : gm.left '' ((fst G G).left ⁻¹' {e.left point}) ⊆ {(lift e z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift e z).left.isClosedMap _ hpoint).preimage gm.left.continuous).isOpen_compl
      · exact (e.left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨p, hp⟩, hpe⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : p point = c₀ := congr(($hpe).1)
    let pt : 𝟙_ (Over S) ⟶ G ⊗ G := Over.homMk p hp
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (pt ≫ snd G G)
    have : p ≫ pullback.fst G.hom G.hom = e.left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : p = fc.left ≫ (e ▷ G).left := by dsimp; ext <;> simp [fc, pt, S, this]
    have H₂ : fc ≫ e ▷ G ≫ gm = lift e z := by
      have h1' := h1 _ (pt ≫ snd G G)
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h1'
      ext1
      · simp [fc, gm, S]
      · simpa [fc, gm, S] using h1'
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gm.left (fst G Z).left (e.left point) (by
      dsimp [-Scheme.Hom.comp_base, gm]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom Z.hom) ⁻¹' {x.1} ∩ Set.range ⇑gm.left).Finite := by
    refine ((((gm.left.imageι ≫ (fst G Z).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gm.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G Z).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gm.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Z.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ Z).left := (lift (fst G G) (toUnit _ ≫ z)).left y
    have hgm : lift (fst G G) (toUnit _ ≫ e) ≫ gm = lift (fst G G) (toUnit _ ≫ z) := by
      ext1
      · simp [gm]
      · simpa [gm] using h2 _ (fst G G)
    have : gm.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ gm.left.continuous
        gm.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gm])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨(lift (fst G G) (toUnit _ ≫ e)).left y, subset_closure ?_, ?_⟩
        · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← Over.comp_left,
            lift_fst]
        · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hgm]
    convert congr((snd G Z).left $this) using 1
    · simp [gm, ← Scheme.Hom.comp_apply]
    · simp only [xe]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  · simp

/-- **A pointed morphism of proper group schemes is a homomorphism, over an algebraically closed
field** (rigidity, Mumford §4 Cor. 1). Apply `rigidity_algClosed` to
`c = (μ ≫ h) * ((h ⊗ h) ≫ μ)⁻¹`. -/
theorem isMonHom_of_algClosed [IsAlgClosed K]
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  have hone : ∀ (T : Over (Spec (.of K))), (1 : T ⟶ G) ≫ h = 1 := fun T => by
    rw [Hom.one_def, Hom.one_def, Category.assoc, h0]
  have key := rigidity_algClosed G B η[G] η[B] ((μ ≫ h) * ((h ⊗ₘ h) ≫ μ)⁻¹)
    (fun T y => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel,
        Hom.one_def])
    (fun T x => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel,
        Hom.one_def])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact ⟨h0, key⟩

/-- **Rigidity over any field** (Mumford §4 Cor. 1 / Milne Cor. 2.2): base change to `K̄` and
`isMonHom_of_algClosed`; `Over.pullback` along `Spec K̄ → Spec K` is faithful and monoidal. -/
theorem isMonHom_of_geometricallyIntegral
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let G' := F.obj G
  let B' := F.obj B
  have : IsProper G'.hom := by dsimp [G', F]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', F]; infer_instance
  have : IsSeparated B'.hom := by dsimp [B', F]; infer_instance
  have : LocallyOfFiniteType B'.hom := by dsimp [B', F]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have h0' : η[G'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, ← F.map_comp, h0]
  have := isMonHom_of_algClosed G' B' (F.map h) h0'
  refine ⟨h0, F.map_injective ?_⟩
  have hm := IsMonHom.mul_hom (F.map h)
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc]
    at hm
  simp only [← F.map_comp] at hm
  exact (cancel_epi _).mp hm

end MulRigidity

/-! ## The leaf, copied verbatim, and its proof -/

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (rigidity; Mumford, *Abelian varieties*, §4 Cor. 1; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Cor. 2.2, over any field; locators UNVERIFIED).** A morphism
of `k`-schemes between abelian varieties that sends the identity to the identity is a
homomorphism. -/
def RigidityHom : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X), η[A.X] ≫ h = η[B.X] → IsMonHom h

/-- **`RigidityHom` holds** (proved from Mathlib; no new hypotheses). -/
theorem rigidityHom : RigidityHom := fun _ _ A B h h0 =>
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

end G0FibreSimple

#print axioms G0FibreSimple.rigidityHom
/-!
# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Appended (by `build.sh`) to verbatim copies of frob-trace's three source parts
(`src_part_tate_src.lean`, `src_part_bridge_src.lean`, `src_part_frob.lean`, i.e.
`scratch/frob-trace/FrobTrace.lean` without its first import line, which `build.sh` re-adds).

Main results (namespace `AlgFrobRedRed`):
* `algFrobRed_of_at : AlgFrobRedAt → FrobTrace.AlgFrobRed` (proved): the place `g(v)` and the
  Frobenius `gτg⁻¹` are absorbed (`liesOver_smul`, `isArithFrob_conj`).
* `algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt` (proved): the finite
  set `S` is the set of primes of bad reduction (leaf `GoodRedCofinite`); what remains is local
  at one place of good reduction (`AlgFrobRedGood`).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField UnramTate
open scoped Pointwise

/-! ## 1. Conjugating the place -/

/-- Nonunits move with the place: `z ∈ v.nonunits → g z ∈ (g • v).nonunits`. -/
theorem smul_mem_nonunits (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {z : PkgI4.Qbar}
    (hz : z ∈ v.nonunits) : g z ∈ (g • v).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hz ⊢
  rcases hz with hz | hz
  · left; rw [hz, map_zero]
  · right
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact hz

/-- `g(v)` lies over `p` if `v` does. -/
theorem liesOver_smul (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hv : PkgI4.LiesOver v p) : PkgI4.LiesOver (g • v) p := by
  have := smul_mem_nonunits g hv
  rwa [map_natCast] at this

/-- `gτg⁻¹` is an arithmetic Frobenius at `g(v)` if `τ` is one at `v`. -/
theorem isArithFrob_conj (g : PkgI4.GQ) {τ : PkgI4.GQ} {v : ValuationSubring PkgI4.Qbar}
    {p : ℕ} (hτ : PkgI4.IsArithFrob τ v p) : PkgI4.IsArithFrob (g * τ * g⁻¹) (g • v) p := by
  obtain ⟨hD, hF⟩ := hτ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff] at hD ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hD]
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def] at hx
    have h := smul_mem_nonunits g (hF _ hx)
    have e1 : g (τ (g⁻¹ x)) = (g * τ * g⁻¹) x := rfl
    have e2 : g (g⁻¹ x) = x := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rwa [map_sub, map_pow, e1, e2] at h

/-- **`AlgFrobRedAt` (GLUE, AV side; Glazer N5 L777-786; the reduction map at the place of the
Frobenius).** `FrobTrace.AlgFrobRed` with the Frobenius `σ` at the place `v` itself (no
conjugating `g`): for `A/L`, `F : A → A` finite surjective there is a finite `S` such that for
`p ∉ S`, `v ∣ p`, `σ` an arithmetic Frobenius at `v` and `f(x) = F ∘ x ∘ Spec(σ)` additive, there
are `Ā/k` (`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with
`red ∘ (N·f) = α' ∘ red`, injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every
prime `ℓ ≠ p`. -/
def AlgFrobRedAt : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRed` from `AlgFrobRedAt` (proved):** apply `AlgFrobRedAt` at the place `g(v)` to
the arithmetic Frobenius `gτg⁻¹` there. -/
theorem algFrobRed_of_at (h : AlgFrobRedAt) : FrobTrace.AlgFrobRed := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := h L A F hF1 hF2
  exact ⟨S, fun p hp hpS v τ hv hτ g f hf =>
    hS p hp hpS (g • v) (g * τ * g⁻¹) (liesOver_smul g hv) (isArithFrob_conj g hτ) f hf⟩

/-! ## 2. Isolating the finite set: good reduction outside finitely many primes -/

/-- **`GoodRedCofinite` (LEAF candidate; good reduction almost everywhere).** An abelian variety
`A` over a number field `L ⊆ ℚ̄` has good reduction at every place of `L` above all but finitely
many primes `p`: there is a finite `S` with `A` having good reduction (I2's `HasGoodReduction`:
an abelian scheme over the valuation ring with generic fibre `≅ A`) at `v ∩ L` for every place
`v` of `ℚ̄` above `p ∉ S`. Source: spreading out, EGA IV₃ §8 (8.8.2, 8.10.5) and EGA IV₄ 17.7.8
for smoothness, with properness and geometric connectedness of fibres; in this form e.g.
Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), §1, and
Milne, *Abelian varieties* (in Cornell–Silverman, *Arithmetic Geometry*, 1986), §20
(all locators UNVERIFIED). -/
def GoodRedCofinite : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar))

/-- **`AlgFrobRedGood` (GLUE, AV side; Glazer N5 L777-786; the reduction map at one place of
good reduction).** `AlgFrobRedAt` at a single place `v ∣ p` at which `A` has good reduction
(`HasGoodReduction` at `v ∩ L`), with no finite set: for `σ` an arithmetic Frobenius at `v` and
`f(x) = F ∘ x ∘ Spec(σ)` additive (`F : A → A` finite surjective), there are `Ā/k`
(`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`,
injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`): `𝒜/O_w` (`w = v ∩ L`) the abelian
scheme, `Ā` its special fibre over `k = κ(w)`; `red` is `A(ℚ̄) = 𝒜(O_v) → Ā(κ(v)) ≅ Ā(k̄)`
(valuative criterion); `F` is an `L`-morphism `A → A^{(s)}`, `s = σ⁻¹|_L ∈ D(w)`, and `A^{(s)}`
has good reduction at `s(w) = w`, so `F` extends to `𝒜 → 𝒜^{(s)}` (leaf I2-NMP); `f` reduces to
`F̄ ∘ Fr_Ā`, a `k`-morphism fixing `0`, hence `α' ∈ End(Ā)` (rigidity); the torsion clauses are
leaf I2-Red. -/
def AlgFrobRedGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar)) →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRedAt` from the leaf `GoodRedCofinite` and the local glue `AlgFrobRedGood`
(proved):** `S` is the finite set of `GoodRedCofinite` for `A`. -/
theorem algFrobRedAt_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) : AlgFrobRedAt := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hG L A
  exact ⟨S, fun p hp hpS v σ hv hσ f hf =>
    hL L A F hF1 hF2 p hp v σ hv hσ (hS p hp hpS v hv) f hf⟩

/-- **`AlgFrobRed` from `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem algFrobRed_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_at (algFrobRedAt_of_good hG hL)

/-- **`TateBridge35` from I3.M0, `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem tateBridge35_of_good (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hL : AlgFrobRedGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_good hG hL)

/-! ## 3. The local glue: special fibre, reduction relation, Frobenius -/

/-- `O_w = v ∩ L`, the valuation ring of `L` below the place `v` of `ℚ̄`. -/
abbrev Ow (L : IF) (v : ValuationSubring PkgI4.Qbar) : ValuationSubring L :=
  v.comap (algebraMap L PkgI4.Qbar)

/-- The residue field `k = κ(w)` of `O_w`. -/
abbrev kw (L : IF) (v : ValuationSubring PkgI4.Qbar) : Type :=
  IsLocalRing.ResidueField (Ow L v)

/-- The special fibre `𝒜 ×_{O} κ(O)` of a group object over a local ring `O`, as a group object
over `Spec κ(O)` (base change along `Spec κ(O) → Spec O`). -/
def sf {O : Type} [CommRing O] [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) :
    Grp (Over (Spec (.of (IsLocalRing.ResidueField O)))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))).mapGrp.obj 𝒜

/-- **`SmoothGeomConnIntegral` (LEAF candidate, textbook; Stacks Project / EGA IV₂).** A smooth,
quasi-compact, geometrically connected scheme over a field is geometrically integral (smooth ⇒
geometrically normal, EGA IV₂ 6.8.1 / 6.7.4 (UNVERIFIED); a connected, quasi-compact, locally
Noetherian normal scheme is integral, Stacks Tag 033M (UNVERIFIED); applied after every field
base change, which preserves smoothness and connectedness). -/
def SmoothGeomConnIntegral : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (.of k)),
    Smooth f → GeometricallyConnected f → QuasiCompact f → GeometricallyIntegral f

/-- The special fibre of an abelian scheme over a local ring is an abelian variety (I2's
`IsAbelianVariety`): properness, smoothness and geometric connectedness are stable under base
change (Mathlib), and geometric integrality is `SmoothGeomConnIntegral`. -/
theorem sf_isAbelianVariety (hS : SmoothGeomConnIntegral) {O : Type} [CommRing O]
    [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) [h : PkgI2.IsAbelianScheme 𝒜] :
    PkgI2.IsAbelianVariety (sf 𝒜) := by
  haveI := h.proper; haveI := h.smooth; haveI := h.geomConnected
  have hp : IsProper (sf 𝒜).X.hom := by
    show IsProper (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  have hs : Smooth (sf 𝒜).X.hom := by
    show Smooth (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  have hc : GeometricallyConnected (sf 𝒜).X.hom := by
    show GeometricallyConnected
      (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  exact ⟨hp, hs, hS _ _ _ hs hc inferInstance⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **The reduction relation.** For `A/L`, an abelian scheme `𝒜/O_w` with `e : 𝒜_L ≅ A`, and a
ring map `j : κ(v) → κ(w)‾`: the `κ(w)‾`-point `y` of the special fibre is the reduction of
`x ∈ A(ℚ̄)` (via `j`) if some `O_w`-morphism `x' : Spec O_v → 𝒜` restricts to `x` on the generic
point (through `e`; the clause of I2's `IsReductionOf`, copied) and `y` followed by the projection
to `𝒜` is `x'` on `Spec κ(v)`, read through `Spec j`. -/
def RedRel {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (x : PtQ L A) (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
    ((Additive.toMul x) ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) =
      Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left ∧
    y.left ≫ pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        x'.left

/-- `char κ(w) = p` for `w = v ∩ L`, `v ∣ p`. -/
theorem charP_kw {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ} (hp : p.Prime)
    (hv : PkgI4.LiesOver v p) : CharP (kw L v) p := by
  have h1 : ((p : Ow L v) : L) ∈ (Ow L v).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hin
    rw [ValuationSubring.mem_comap, map_inv₀] at hin
    have he : (algebraMap L PkgI4.Qbar ((p : Ow L v) : L)) = (p : PkgI4.Qbar) := by simp
    rw [he] at hin
    have hv' := hv
    unfold PkgI4.LiesOver at hv'
    rw [ValuationSubring.mem_nonunits_iff_or] at hv'
    rcases hv' with h0 | h0
    · exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    · exact h0 hin
  have h2 : (p : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (ValuationSubring.coe_mem_nonunits_iff).mp h1
  have h3 : (p : kw L v) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Ow L v)), IsLocalRing.residue_eq_zero_iff]
    exact h2
  exact (CharP.charP_iff_prime_eq_zero hp).mpr h3

/-- `ℓⁿ` is a unit of `O_w` for a prime `ℓ ≠ p`. -/
theorem isUnit_cast_of_ne {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ} (hp : p.Prime)
    (hv : PkgI4.LiesOver v p) {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ p) (n : ℕ) :
    IsUnit (((ℓ ^ n : ℕ)) : Ow L v) := by
  by_contra hnu
  have hm : ((ℓ ^ n : ℕ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h0 : ((ℓ ^ n : ℕ) : kw L v) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Ow L v)), IsLocalRing.residue_eq_zero_iff]
    exact hm
  haveI := charP_kw (L := L) hp hv
  rw [CharP.cast_eq_zero_iff (kw L v) p] at h0
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h0)).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionMapGood` (GLUE; valuative criterion of properness, Stacks Tag 0BX5 / EGA II 7.3.8
(UNVERIFIED locators)).** At a place `v ∣ p` and an abelian scheme `𝒜/O_w` (`w = v ∩ L`) with
`e : 𝒜_L ≅ A`: there are a ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with the maps from
`O_w` (`κ(v)` is an algebraic closure of `κ(w)`) and a group homomorphism
`red : A(ℚ̄) → Ā(κ(w)‾)` (`Ā` the special fibre `sf 𝒜`) with `RedRel x (red x)` for every `x`
(existence of the lift `x' : Spec O_v → 𝒜`, valuative criterion: `𝒜` proper, `O_v` a valuation
ring with fraction field `ℚ̄`), and the reduction is unique (uniqueness of the lift, `𝒜`
separated, plus the universal property of the fibre product). `red` is a homomorphism since
restriction `𝒜(O_v) → 𝒜(ℚ̄)` is a bijective homomorphism and reduction `𝒜(O_v) → 𝒜(κ(v))` is
one. No Frobenius, no torsion. -/
def ReductionMapGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ), p.Prime →
    ∀ (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
        ObjBridge.toGrp A),
    ∃ j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v), Function.Bijective j ∧
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) ∧
      ∃ red : PtQ L A →+ Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
        (∀ x, RedRel v 𝒜 e j x (Additive.toMul (red x))) ∧
        (∀ x y y', RedRel v 𝒜 e j x y → RedRel v 𝒜 e j x y' → y = y')

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedTorsionQbar` (GLUE: leaf I2-Red, `PkgI2.ReductionTorsionBijective` (Serre–Tate 1968,
§1), transported).** For `m ≥ 1` invertible in `O_w` and any ring isomorphism
`j : κ(v) ≅ κ(w)‾` compatible with the maps from `O_w`: reduction (`RedRel`) is a bijection
`A(ℚ̄)[m] → Ā(κ(w)‾)[m]`, in I2-Red's form (`∃!` both ways). This is I2-Red for the abelian scheme
`𝒜` over the DVR `O_w` (a valuation ring of the number field `L` with `p` a nonunit), read
through the `L`-isomorphism `ℚ̄ ≅ L‾` (`ℚ̄` is an algebraic closure of `L`), the universal
property of `sf 𝒜 = 𝒜 ×_{O_w} κ(w)` (points of `𝒜` over `κ(v)` = `κ(w)`-points of `sf 𝒜` over
`κ(v)`) and `j`. -/
def RedTorsionQbar : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ), p.Prime →
    ∀ (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
        ObjBridge.toGrp A)
      (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)), Function.Bijective j →
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) →
      ∀ m : ℕ, 0 < m → IsUnit (m : Ow L v) →
        (∀ x : PtQ L A, m • x = 0 →
          ∃! y : Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
            m • y = 0 ∧ RedRel v 𝒜 e j x (Additive.toMul y)) ∧
        (∀ y : Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))), m • y = 0 →
          ∃! x : PtQ L A, m • x = 0 ∧ RedRel v 𝒜 e j x (Additive.toMul y))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionFrobGood` (GLUE, AV side; Glazer N5 L777-786; the Frobenius step).** At a place
`v ∣ p` with an abelian scheme `𝒜/O_w` and `e : 𝒜_L ≅ A`, `σ` an arithmetic Frobenius at `v`,
`F : A → A` finite surjective and `f(x) = F ∘ x ∘ Spec(σ)` additive: there is an endomorphism
`ᾱ` of the special fibre `Ā = sf 𝒜` (a morphism of group objects over `κ(w)`) such that for every
ring map `j : κ(v) → κ(w)‾`, if `y` is the reduction of `x` then `ᾱ ∘ y` is the reduction of
`f x`.

Why it is true (SPECULATIVE in its Lean details): `F` lies over `Spec(t)`, `t = σ⁻¹|_L ∈ D(w)`
(forced by `f(x)` being an `L`-point); `F` extends to `F̃ : 𝒜 → 𝒜` over `Spec(t|_{O_w})` (leaf
I2-NMP applied to `𝒜` and its base change along `t`); a lift of `f x` is
`Spec(σ|_{O_v}) ≫ x' ≫ F̃`; on `Spec κ(v)`, `σ` induces the `p`-power map (`IsArithFrob`), i.e.
the absolute Frobenius, which commutes with every morphism of schemes; so the reduction of
`f x` is `y ≫ Fr_Ā ≫ F̄` with `F̄` the base change of `F̃` (over `Spec(t̄) = Spec(Frob⁻¹)`), and
`ᾱ = Fr_Ā ≫ F̄` lies over `id_{κ(w)}` and fixes `0` (`f` is additive), hence is a homomorphism
(rigidity, Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED locator). -/
def ReductionFrobGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
          (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
            𝒜 ≅ ObjBridge.toGrp A)
          (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
            Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
              (Additive.toMul x).left ≫ F) →
        ∃ ab : sf 𝒜 ⟶ sf 𝒜,
          ∀ (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x : PtQ L A)
            (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
            RedRel v 𝒜 e j x y → RedRel v 𝒜 e j (f x) (y ≫ ab.hom.hom)

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AlgFrobRedGood` from `SmoothGeomConnIntegral`, `ReductionMapGood`, `RedTorsionQbar` and
`ReductionFrobGood` (proved).** `k = κ(w)`, `Ā = sf 𝒜` (an abelian variety by
`sf_isAbelianVariety`), `α' = ᾱ`, `N = 1`, `red` from `ReductionMapGood`; the intertwining is the
uniqueness of reductions, the torsion clauses are `RedTorsionQbar` at `m = ℓⁿ` (a unit of `O_w`,
`isUnit_cast_of_ne`). -/
theorem algFrobRedGood_of (hS : SmoothGeomConnIntegral) (h1 : ReductionMapGood)
    (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) : AlgFrobRedGood := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ hgood f hf
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hgood
  haveI := h𝒜
  haveI hAV := sf_isAbelianVariety hS 𝒜
  obtain ⟨j, hjb, hjc, red, hred, huniq⟩ := h1 L A p hp v hv 𝒜 e
  obtain ⟨ab, hab⟩ := h3 L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  refine ⟨kw L v, inferInstance, charP_kw hp hv, ObjBridge.ofGrp (sf 𝒜),
    ObjBridge.homOfGrp ab, 1, one_ne_zero, red, ?_, ?_⟩
  · intro x
    rw [one_smul]
    exact congrArg Additive.ofMul (huniq (f x) _ _ (hred (f x)) (hab j x _ (hred x)))
  · intro ℓ hℓ hne n
    have hu := isUnit_cast_of_ne (L := L) hp hv hℓ hne n
    obtain ⟨-, hB⟩ := h2 L A p hp v hv 𝒜 e j hjb hjc (ℓ ^ n) (pow_pos hℓ.pos n) hu
    refine ⟨fun x hx h0 => ?_, fun y hy => ?_⟩
    · have hx0 : RedRel v 𝒜 e j x (Additive.toMul 0) := h0 ▸ hred x
      have h00 : RedRel v 𝒜 e j 0 (Additive.toMul 0) := (map_zero red) ▸ hred 0
      exact (hB 0 (smul_zero _)).unique ⟨hx, hx0⟩ ⟨smul_zero _, h00⟩
    · obtain ⟨x, ⟨hx, hxr⟩, -⟩ := hB y hy
      exact ⟨x, hx, congrArg Additive.ofMul (huniq x _ _ (hred x) hxr)⟩

/-! ## 4. `ReductionMapGood` from the valuative criterion (Mathlib) and two smaller Props -/

set_option synthInstance.maxHeartbeats 400000 in
/-- `x ∈ A(ℚ̄)` as a `ℚ̄`-point of `𝒜_L` (through `e`). -/
def genPt {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X :=
  (Additive.toMul x) ≫ (e.inv.hom.hom : A.X ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X)

set_option synthInstance.maxHeartbeats 400000 in
/-- The generic point map `Spec ℚ̄ → 𝒜` of `x ∈ A(ℚ̄)` (through `e`), as in `RedRel`. -/
def genMap {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) : Spec (.of PkgI4.Qbar) ⟶ 𝒜.X.left :=
  (genPt v 𝒜 e x).left ≫
    pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))

set_option synthInstance.maxHeartbeats 400000 in
/-- The valuative square: `Spec ℚ̄ → 𝒜` over `Spec O_v → Spec O_w`. -/
theorem genMap_comm {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    genMap v 𝒜 e x ≫ 𝒜.X.hom = Spec.map (CommRingCat.ofHom (algebraMap v PkgI4.Qbar)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
  have key : ∀ (T : Scheme) (u : T ⟶ pullback 𝒜.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))),
      (u ≫ pullback.fst _ _) ≫ 𝒜.X.hom = (u ≫ pullback.snd _ _) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) := fun T u => by
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hw : (genPt v 𝒜 e x).left ≫ pullback.snd 𝒜.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) =
      Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) := Over.w (genPt v 𝒜 e x)
  have h2 : ((genPt v 𝒜 e x).left ≫ pullback.snd _ _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) :=
    congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) hw
  have h3 : Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap v PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact (key _ (genPt v 𝒜 e x).left).trans (h2.trans h3)

set_option synthInstance.maxHeartbeats 400000 in
/-- The valuative commutative square of `x`. -/
def vsq {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) : ValuativeCommSq 𝒜.X.hom where
  R := v
  K := PkgI4.Qbar
  i₁ := genMap v 𝒜 e x
  i₂ := Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))
  commSq := ⟨genMap_comm v 𝒜 e x⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Existence of the lift** `x' : Spec O_v → 𝒜` (proved: valuative criterion for the proper
`𝒜 → Spec O_w`, Mathlib `UniversallyClosed.eq_valuativeCriterion`). -/
theorem exists_lift {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
      genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left := by
  haveI := h𝒜.proper
  have h1 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.X.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, hl1, hl2⟩⟩ := h1.1 (vsq v 𝒜 e x)
  exact ⟨Over.homMk l hl2, hl1.symm⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Uniqueness of the lift** (proved: valuative criterion of separatedness, Mathlib
`IsSeparated.valuativeCriterion`). -/
theorem lift_unique {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A)
    (x₁ x₂ : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X)
    (h₁ : genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x₁.left)
    (h₂ : genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x₂.left) : x₁ = x₂ := by
  haveI := h𝒜.proper
  have hU := IsSeparated.valuativeCriterion 𝒜.X.hom (vsq v 𝒜 e x)
  have e1 : (⟨x₁.left, h₁.symm, Over.w x₁⟩ : (vsq v 𝒜 e x).commSq.LiftStruct) =
      ⟨x₂.left, h₂.symm, Over.w x₂⟩ := Subsingleton.elim _ _
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l e1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Every `x` has a reduction, for `j` compatible with the maps from `O_w` (proved). -/
theorem exists_redRel {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (x : PtQ L A) : ∃ y, RedRel v 𝒜 e j x y := by
  obtain ⟨x', hx'⟩ := exists_lift v 𝒜 e x
  have hw : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue v)) ≫ x'.left) ≫ 𝒜.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (kw L v) (AlgebraicClosure (kw L v)))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))) := by
    rw [Category.assoc, Category.assoc, Over.w x']
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hjc a
  refine ⟨Over.homMk (pullback.lift _ _ hw) (pullback.lift_snd _ _ hw), x', hx', ?_⟩
  exact pullback.lift_fst _ _ hw

set_option synthInstance.maxHeartbeats 400000 in
/-- Reductions are unique (proved: uniqueness of the lift and of maps into a fibre product). -/
theorem redRel_unique {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x : PtQ L A)
    (y y' : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) :
    RedRel v 𝒜 e j x y → RedRel v 𝒜 e j x y' → y = y' := by
  rintro ⟨x₁, h₁, h₁'⟩ ⟨x₂, h₂, h₂'⟩
  obtain rfl := lift_unique v 𝒜 e x x₁ x₂ h₁ h₂
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h₁'.trans h₂'.symm
  · exact (Over.w y).trans (Over.w y').symm

/-- **`ResidueAlgClosure` (GLUE, standard commutative algebra).** For a place `v ∣ p` of `ℚ̄` and
`w = v ∩ L`, there is a ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with the maps from `O_w`:
`κ(v)` is algebraically closed (the residue field of a valuation ring of an algebraically closed
field) and algebraic over `κ(w)` (`ℚ̄/L` is algebraic), hence an algebraic closure of `κ(w)`
(Engler–Prestel, *Valued fields* (2005), Thm 3.2.11 and §3.2; Bourbaki, *Alg. Comm.* VI §8;
locators UNVERIFIED). -/
def ResidueAlgClosure : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar) (p : ℕ), p.Prime →
    PkgI4.LiesOver v p →
    ∃ j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v), Function.Bijective j ∧
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedRelMul` (GLUE; reduction respects the group law).** If `y₁, y₂` are the reductions of
`x₁, x₂` then `y₁ y₂` is the reduction of `x₁ + x₂`: the product `x'₁ x'₂` of the lifts (in the
group `𝒜(O_v)`) lifts `x₁ + x₂` (restriction to the generic point and `e` respect the group
laws), and base change to the special fibre respects them too (`sf 𝒜` carries the base-changed
group law). -/
def RedRelMul : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x₁ x₂ : PtQ L A)
    (y₁ y₂ : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
    RedRel v 𝒜 e j x₁ y₁ → RedRel v 𝒜 e j x₂ y₂ → RedRel v 𝒜 e j (x₁ + x₂) (y₁ * y₂)

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionMapGood` from `ResidueAlgClosure` and `RedRelMul` (proved)**, with the valuative
criterion (existence and uniqueness of lifts) from Mathlib. -/
theorem reductionMapGood_of (hR : ResidueAlgClosure) (hM : RedRelMul) : ReductionMapGood := by
  intro L _ A p hp v hv 𝒜 _ e
  obtain ⟨j, hjb, hjc⟩ := hR L v p hp hv
  choose r hr using exists_redRel v 𝒜 e j hjc
  have hun := redRel_unique v 𝒜 e j
  let red : PtQ L A →+ Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (r x)) (fun a b => by
      show Additive.ofMul (r (a + b)) = Additive.ofMul (r a * r b)
      exact congrArg Additive.ofMul (hun _ _ _ (hr (a + b)) (hM L A v 𝒜 e j a b _ _ (hr a) (hr b))))
  exact ⟨j, hjb, hjc, red, fun x => hr x, hun⟩

/-- **`AlgFrobRed` from the leaves `GoodRedCofinite`, `SmoothGeomConnIntegral` and the glue
`ReductionMapGood`, `RedTorsionQbar`, `ReductionFrobGood` (proved).** -/
theorem algFrobRed_of_pieces (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h1 : ReductionMapGood) (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_good hG (algFrobRedGood_of hS h1 h2 h3)

/-- **`TateBridge35` from I3.M0 and the five pieces (proved).** -/
theorem tateBridge35_of_pieces (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h1 : ReductionMapGood) (h2 : RedTorsionQbar)
    (h3 : ReductionFrobGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_pieces hG hS h1 h2 h3)

/-- **Main result: `AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `ResidueAlgClosure`, `RedRelMul`, `RedTorsionQbar`,
`ReductionFrobGood` (proved).** The valuative criterion (existence and uniqueness of the lift
`Spec O_v → 𝒜`), the special fibre being an abelian variety (up to `SmoothGeomConnIntegral`), the
residue characteristic, the units `ℓⁿ` and the conjugation of the place are proved here. -/
theorem algFrobRed_of_split (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hR : ResidueAlgClosure) (hM : RedRelMul) (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_pieces hG hS (reductionMapGood_of hR hM) h2 h3

/-- **`TateBridge35` from I3.M0 and the six pieces (proved).** -/
theorem tateBridge35_of_split (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hR : ResidueAlgClosure) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_split hG hS hR hM h2 h3)

/-! ## 5. `ReductionFrobGood` from the extension of `F` and the twisted Frobenius -/

/-- `σ` restricted to `O_v`, for `σ` in the decomposition group of `v`. -/
def sigV {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ) (hσ : σ ∈ v.decompositionSubgroup ℚ) :
    v →+* v where
  toFun y := ⟨σ y, by
    have h : σ • v = v := hσ
    have h2 := ValuationSubring.smul_mem_pointwise_smul σ (y : PkgI4.Qbar) v y.2
    rw [h, AlgEquiv.smul_def] at h2
    exact h2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ _ _)

/-- An arithmetic Frobenius acts on `κ(v)` as `z ↦ z^p` (proved from `IsArithFrob`). -/
theorem residue_sigV {v : ValuationSubring PkgI4.Qbar} {σ : PkgI4.GQ} {p : ℕ}
    (hσ : PkgI4.IsArithFrob σ v p) (y : v) :
    IsLocalRing.residue v (sigV σ hσ.1 y) = IsLocalRing.residue v y ^ p := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have h := hσ.2 y y.2
  simpa [sigV] using h

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtend` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model).** At a place `v ∣ p` with an abelian scheme `𝒜/O_w`,
`e : 𝒜_L ≅ A`, `σ` an arithmetic Frobenius at `v`, `F : A → A` finite surjective and
`f(x) = F ∘ x ∘ Spec(σ)` additive: there are a ring endomorphism `t` of `O_w` (it is
`σ⁻¹|_{O_w}`) and a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` such that `t` induces
`Frob⁻¹` on `κ(w)` (`t(a)^p ≡ a`), `F̃` maps the unit section to itself (over `Spec t`), and
`F̃` extends `F`: whenever `x'` is the lift of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` is a lift of `f x`.

Why it is true: `f(x) ∈ A(ℚ̄)` for all `x` forces `F` to lie over `Spec(σ⁻¹|_L)`, so `F` is an
`L`-morphism `A → A^{(t)}`; `A^{(t)}` is the generic fibre of the base change `𝒜^{(t)}` of `𝒜`
along `t|_{O_w}` (`σ ∈ D(v)`, so `t(O_w) = O_w`), and I2-NMP extends it to `𝒜 → 𝒜^{(t)}`, i.e.
`F̃`; the lift identity holds on the generic point, and `F̃` fixes `0` since `f(0) = 0` and `𝒜`
is separated over the integral `Spec O_w`. `t(a)^p ≡ a` since `σ` acts on `κ(v)` as `z ↦ z^p`. -/
def FExtend : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (Ft : 𝒜.X.left ⟶ 𝒜.X.left) (t : Ow L v →+* Ow L v),
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom t) ∧
          (∀ a, IsLocalRing.residue (Ow L v) (t a) ^ p = IsLocalRing.residue (Ow L v) a) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom t) ≫ (η[𝒜.X]).left ∧
          ∀ (x : PtQ L A)
            (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
            genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
            ∃ x'' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
              genMap v 𝒜 e (f x) = Spec.map (CommRingCat.ofHom v.subtype) ≫ x''.left ∧
              x''.left = Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft

/-- **`FrobMorph` (GLUE; the absolute Frobenius of the special fibre twisted by `F̄`).** Let `O`
be a local ring with residue field `k` of characteristic `p`, `𝒜/O` an abelian scheme,
`t : O → O` a ring map inducing `Frob⁻¹` on `k` (`t(a)^p ≡ a`) and `F̃ : 𝒜 → 𝒜` a morphism over
`Spec(t)` fixing the unit section. Then there is a `k`-morphism `β` of the special fibre
`Ā = sf 𝒜` fixing `0` with `β ∘ y = F̃ ∘ y ∘ Spec(z ↦ z^p)` on `k̄`-points (after projecting to
`𝒜`).

Why it is true: `β = Fr_Ā ≫ F̄`, with `Fr_Ā` the absolute Frobenius of the `𝔽_p`-scheme `Ā`
(over `Fr_{Spec k} = Spec(z ↦ z^p)`) and `F̄ = F̃ ×_{Spec t} Spec(t̄)` the base change (over
`Spec t̄`, `t̄ = Frob⁻¹`); `β` lies over `Spec(t̄) ∘ Spec(Frob) = id`; on a point,
`y ≫ Fr_Ā = Fr_{Spec k̄} ≫ y` (naturality of the absolute Frobenius), and `Fr_Ā, F̄` fix `0`. The
absolute Frobenius of schemes is not in Mathlib 4.35. -/
def FrobMorph : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ), p.Prime →
    CharP (IsLocalRing.ResidueField O) p →
    ∀ (𝒜 : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜]
      (Ft : 𝒜.X.left ⟶ 𝒜.X.left) (t : O →+* O),
      Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom t) →
      (∀ a, IsLocalRing.residue O (t a) ^ p = IsLocalRing.residue O a) →
      (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom t) ≫ (η[𝒜.X]).left →
      ∃ β : (sf 𝒜).X ⟶ (sf 𝒜).X, η[(sf 𝒜).X] ≫ β = η[(sf 𝒜).X] ∧
        ∀ (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (IsLocalRing.ResidueField O)))
          (φ : AlgebraicClosure (IsLocalRing.ResidueField O) →+*
            AlgebraicClosure (IsLocalRing.ResidueField O)),
          (∀ z, φ z = z ^ p) →
          (y ≫ β).left ≫
              pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) =
            Spec.map (CommRingCat.ofHom φ) ≫ y.left ≫
              pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) ≫ Ft

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionFrobGood` from `SmoothGeomConnIntegral`, `FExtend` and `FrobMorph` (proved)**,
with rigidity (`G0FibreSimple.rigidityHom`, proved from Mathlib by mul-rigidity, copied
verbatim): `ᾱ = β` is a homomorphism because it fixes `0`; the reduction of `f x` is computed
from the lift `Spec(σ|_{O_v}) ≫ x' ≫ F̃` and `residue_sigV` (`σ` is `z ↦ z^p` on `κ(v)`, and
`j` commutes with `z ↦ z^p`). -/
theorem reductionFrobGood_of (hS : SmoothGeomConnIntegral) (hE : FExtend) (hFr : FrobMorph) :
    ReductionFrobGood := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, t, hover, hres, hzero, hlift⟩ := hE L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  haveI := charP_kw (L := L) hp hv
  obtain ⟨β, hβ0, hβ⟩ := hFr (Ow L v) p hp inferInstance 𝒜 Ft t hover hres hzero
  haveI hAV := sf_isAbelianVariety hS 𝒜
  haveI hmon : IsMonHom β := G0FibreSimple.rigidityHom _ (ObjBridge.ofGrp (sf 𝒜))
    (ObjBridge.ofGrp (sf 𝒜)) β hβ0
  refine ⟨Grp.homMk β, fun j x y ⟨x', hx', hy⟩ => ?_⟩
  obtain ⟨x'', hx'', hx''eq⟩ := hlift x x' hx'
  refine ⟨x'', hx'', ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure (kw L v)) p :=
    charP_of_injective_algebraMap (algebraMap (kw L v) _).injective p
  have h1 := hβ y (frobenius _ p) (fun z => rfl)
  have hring : Spec.map (CommRingCat.ofHom (frobenius (AlgebraicClosure (kw L v)) p)) ≫
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    simp only [RingHom.comp_apply, residue_sigV hσ, map_pow, frobenius_def]
  have h3 := congrArg (fun m => Spec.map (CommRingCat.ofHom
    (frobenius (AlgebraicClosure (kw L v)) p)) ≫ m ≫ Ft) hy
  have h5 : Spec.map (CommRingCat.ofHom (frobenius (AlgebraicClosure (kw L v)) p)) ≫
      (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        x'.left) ≫ Ft =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft := by
    have h4 := congrArg (fun m => m ≫ x'.left ≫ Ft) hring
    simp only [Category.assoc] at h4 ⊢
    exact h4
  have h2 := (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (frobenius (AlgebraicClosure (kw L v)) p)) ≫ m) (Category.assoc y.left _ Ft).symm).trans
    (h3.trans h5)
  rw [hx''eq]
  exact h1.trans h2

/-! ## 6. `ResidueAlgClosure` from two statements on residue fields -/

/-- `O_w → O_v` is a local homomorphism (proved). -/
instance isLocalHom_toW (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    IsLocalHom (PkgI2.toW (Ow L v) v rfl) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : ((a : Ow L v) : L) ∈ (Ow L v).nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  have h2 : ((PkgI2.toW (Ow L v) v rfl a : v) : PkgI4.Qbar) ∈ v.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at h1 ⊢
    show algebraMap L PkgI4.Qbar (a : L) = 0 ∨ (algebraMap L PkgI4.Qbar (a : L))⁻¹ ∉ v
    rcases h1 with h | h
    · left; rw [h, map_zero]
    · right; rw [← map_inv₀]; exact h
  exact (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp h2) ha

/-- **`ResidueAlgClosed` (GLUE, standard: the residue field of a valuation ring of an
algebraically closed field is algebraically closed; e.g. Engler–Prestel, *Valued fields* (2005),
Thm 3.2.11 (locator UNVERIFIED)).** Proof idea: lift a monic polynomial to `O_v`, take a root in
`ℚ̄`; it is integral over `O_v`, hence in `O_v`; reduce. -/
def ResidueAlgClosed : Prop :=
  ∀ v : ValuationSubring PkgI4.Qbar, IsAlgClosed (IsLocalRing.ResidueField v)

/-- **`ResidueAlgebraic` (GLUE, standard: the residue extension of an algebraic extension of
valued fields is algebraic; Bourbaki, *Alg. Comm.* VI §8.1, Engler–Prestel Cor. 3.2.3 (locators
UNVERIFIED)).** `κ(v)` is algebraic over `κ(w)`, `w = v ∩ L`, for the map induced by
`O_w → O_v`. -/
def ResidueAlgebraic : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar),
    @Algebra.IsAlgebraic (kw L v) (IsLocalRing.ResidueField v) _ _
      (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra

/-- **`ResidueAlgClosed` holds (proved from Mathlib):** lift a monic irreducible `q` over `κ(v)`
to a monic `Q` over `O_v`, take a root `z ∈ ℚ̄` of `Q`; `z` is integral over the integrally closed
`O_v`, so `z ∈ O_v`, and its residue is a root of `q`. -/
theorem residueAlgClosed : ResidueAlgClosed := by
  intro v
  refine IsAlgClosed.of_exists_root _ (fun q hq hirr => ?_)
  obtain ⟨Q, hQmap, hQdeg, hQmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective q) hq
  have hinj : Function.Injective (algebraMap v PkgI4.Qbar) := IsFractionRing.injective v PkgI4.Qbar
  have hdeg : (Q.map (algebraMap v PkgI4.Qbar)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    intro h
    have h1 : Q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some h
    rw [hQdeg] at h1
    exact (Irreducible.natDegree_pos hirr).ne' h1
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral v z := ⟨Q, hQmon, hz⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [Polynomial.eval₂_hom] at hz
  have h0 : Q.eval y = 0 := hinj (hz.trans (map_zero _).symm)
  refine ⟨IsLocalRing.residue v y, ?_⟩
  rw [← hQmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

/-- **`ResidueAlgebraic` holds (proved from Mathlib):** for `y ∈ O_v`, take `P ∈ L[X]`, `P ≠ 0`,
`P(y) = 0`, and divide by a coefficient of largest valuation for `O_w`: the result has
coefficients in `O_w` and a coefficient `1`, so its reduction is a nonzero polynomial over `κ(w)`
vanishing at the residue of `y`. -/
theorem residueAlgebraic : ResidueAlgebraic := by
  intro L _ v
  letI : Algebra (kw L v) (IsLocalRing.ResidueField v) :=
    (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  have hyalg : IsAlgebraic L (y : PkgI4.Qbar) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (y : PkgI4.Qbar)).tower_top L
  obtain ⟨P, hP0, hPy⟩ := hyalg
  obtain ⟨i, hi, hmax⟩ := P.support.exists_max_image (fun n => (Ow L v).valuation (P.coeff n))
    (Polynomial.support_nonempty.mpr hP0)
  have hci : P.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hlift : P * Polynomial.C (P.coeff i)⁻¹ ∈ Polynomial.lifts (algebraMap (Ow L v) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_mul_C]
    have hmem : P.coeff n * (P.coeff i)⁻¹ ∈ Ow L v := by
      rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
      by_cases hn : n ∈ P.support
      · exact mul_inv_le_one_of_le₀ (hmax n hn) zero_le'
      · rw [Polynomial.notMem_support_iff.mp hn, map_zero, zero_mul]
        exact zero_le'
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).mp hlift
  have hinjO : Function.Injective (algebraMap (Ow L v) L) := IsFractionRing.injective (Ow L v) L
  have hQi : Q.coeff i = 1 := by
    apply hinjO
    rw [← Polynomial.coeff_map, hQ, Polynomial.coeff_mul_C, mul_inv_cancel₀ hci, map_one]
  refine ⟨Q.map (IsLocalRing.residue (Ow L v)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun r => r.coeff i) h0
    simp only [Polynomial.coeff_map, hQi, map_one, Polynomial.coeff_zero] at h1
    exact one_ne_zero h1
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap (kw L v) (IsLocalRing.ResidueField v)).comp
        (IsLocalRing.residue (Ow L v)) =
        (IsLocalRing.residue v).comp (PkgI2.toW (Ow L v) v rfl) := by
      ext a
      exact IsLocalRing.ResidueField.map_residue _ a
    rw [hcomp, ← Polynomial.hom_eval₂]
    have hzero : Q.eval₂ (PkgI2.toW (Ow L v) v rfl) y = 0 := by
      apply IsFractionRing.injective v PkgI4.Qbar
      rw [map_zero]
      have e1 := Polynomial.hom_eval₂ Q (PkgI2.toW (Ow L v) v rfl) (algebraMap v PkgI4.Qbar) y
      have e2 : (algebraMap v PkgI4.Qbar).comp (PkgI2.toW (Ow L v) v rfl) =
          (algebraMap L PkgI4.Qbar).comp (algebraMap (Ow L v) L) := rfl
      rw [e1, e2, ← Polynomial.eval₂_map, hQ, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      have e3 : P.eval₂ (algebraMap L PkgI4.Qbar) (algebraMap v PkgI4.Qbar y) = 0 := hPy
      rw [e3, zero_mul]
    rw [hzero, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ResidueAlgClosure` from `ResidueAlgClosed` and `ResidueAlgebraic` (proved):** `κ(v)` is an
algebraic closure of `κ(w)`, so `IsAlgClosure.equiv` gives `j`. -/
theorem residueAlgClosure_of (h1 : ResidueAlgClosed) (h2 : ResidueAlgebraic) :
    ResidueAlgClosure := by
  intro L _ v p _ _
  letI : Algebra (kw L v) (IsLocalRing.ResidueField v) :=
    (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra
  haveI : IsAlgClosed (IsLocalRing.ResidueField v) := h1 v
  haveI : Algebra.IsAlgebraic (kw L v) (IsLocalRing.ResidueField v) := h2 L v
  haveI : IsAlgClosure (kw L v) (IsLocalRing.ResidueField v) := ⟨inferInstance, inferInstance⟩
  let e := IsAlgClosure.equiv (kw L v) (IsLocalRing.ResidueField v) (AlgebraicClosure (kw L v))
  refine ⟨e.toRingEquiv.toRingHom, e.bijective, fun a => ?_⟩
  have h3 : IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a) =
      algebraMap (kw L v) (IsLocalRing.ResidueField v) (IsLocalRing.residue (Ow L v) a) :=
    (IsLocalRing.ResidueField.map_residue _ a).symm
  show e (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) = _
  rw [h3, AlgEquiv.commutes]

/-! ## 7. `RedRelMul` from the adjunction `Over.map ⊣ Over.pullback` -/

section RedMul

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(T, g^* M) ≃ Hom(g_! T, M)` is multiplicative (as in
unram-tate's `homEquiv_mul`), here for the inverse map. -/
theorem pb_symm_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (u w : T ⟶ (Over.pullback g).obj M) :
    ((Over.mapPullbackAdj g).homEquiv T M).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T M).symm u *
        ((Over.mapPullbackAdj g).homEquiv T M).symm w := by
  obtain ⟨p, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective u
  obtain ⟨q, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective w
  have hm : (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]
  rw [← hm, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end RedMul

/-- `pb_symm_mul` for the group law of `(Over.pullback g).mapGrp.obj G` (the one of `sf 𝒜` and of
`𝒜_L`). -/
theorem pb_symm_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X) :
    ((Over.mapPullbackAdj g).homEquiv T G.X).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T G.X).symm u *
        ((Over.mapPullbackAdj g).homEquiv T G.X).symm w :=
  pb_symm_mul g G.X T u w

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedRelMul` holds (proved):** the product of the lifts lifts the sum, and on both the
generic point and the special fibre the passage to `𝒜` is the adjunction bijection, which is
multiplicative (`pb_symm_mul'`); `e.inv` is a homomorphism. -/
theorem redRelMul : RedRelMul := by
  intro L _ A v 𝒜 _ e j x₁ x₂ y₁ y₂ ⟨x'₁, g₁, c₁⟩ ⟨x'₂, g₂, c₂⟩
  refine ⟨x'₁ * x'₂, ?_, ?_⟩
  · have hw : Spec.map (CommRingCat.ofHom v.subtype) ≫
        (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom =
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj
          (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar)).hom := by
      simp only [Over.mk_hom, Over.map_obj_hom, PkgI3.AbVar.ptObj]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    let ι0 : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj
        (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) :=
      Over.homMk (Spec.map (CommRingCat.ofHom v.subtype)) hw
    let u : PtQ L A → (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar ⟶
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜).X) := fun x => genPt v 𝒜 e x
    have hs : ∀ (x : PtQ L A)
        (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
        genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).homEquiv
          _ 𝒜.X).symm (u x) = ι0 ≫ x' := fun x x' h => Over.OverMorphism.ext h
    have hmul : u (x₁ + x₂) = u x₁ * u x₂ := by
      show (Additive.toMul x₁ * Additive.toMul x₂) ≫ e.inv.hom.hom =
        (Additive.toMul x₁ ≫ e.inv.hom.hom) * (Additive.toMul x₂ ≫ e.inv.hom.hom)
      exact MonObj.mul_comp _ _ _
    have key : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
        (algebraMap (Ow L v) L)))).homEquiv _ 𝒜.X).symm (u (x₁ + x₂)) = ι0 ≫ (x'₁ * x'₂) :=
      (congrArg ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
        (algebraMap (Ow L v) L)))).homEquiv _ 𝒜.X).symm hmul).trans
        ((pb_symm_mul' _ 𝒜 _ (u x₁) (u x₂)).trans
          (by rw [hs x₁ x'₁ g₁, hs x₂ x'₂ g₂, MonObj.comp_mul]))
    exact congrArg Over.Hom.left key
  · have keyc : ∀ (T' : Scheme) (u : T' ⟶ pullback 𝒜.X.hom
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))),
        (u ≫ pullback.fst _ _) ≫ 𝒜.X.hom = (u ≫ pullback.snd _ _) ≫
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))) := fun T' u => by
      rw [Category.assoc, pullback.condition, Category.assoc]
    have h2 := (keyc _ y₁.left).trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v)))) (Over.w y₁))
    have h1 := congrArg (· ≫ 𝒜.X.hom) c₁
    have h3 : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue v)) ≫ x'₁.left) ≫ 𝒜.X.hom =
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue v))) ≫
          (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
      rw [Category.assoc, Category.assoc, Category.assoc, Over.w x'₁]
    have hw' : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue v))) ≫
          (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom =
        ((Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
          (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v)))).hom :=
      h3.symm.trans (h1.symm.trans h2)
    let ι1 : (Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
        (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) :=
      Over.homMk (Spec.map (CommRingCat.ofHom j) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue v))) hw'
    have hs : ∀ (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)))
        (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
        y.left ≫ pullback.fst 𝒜.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
          Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
            x'.left →
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm y = ι1 ≫ x' :=
      fun y x' h => Over.OverMorphism.ext (h.trans (Category.assoc _ _ _).symm)
    have key : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm (y₁ * y₂) =
        ι1 ≫ (x'₁ * x'₂) :=
      (pb_symm_mul' _ 𝒜 _ y₁ y₂).trans (by rw [hs y₁ x'₁ c₁, hs y₂ x'₂ c₂, MonObj.comp_mul])
    exact (congrArg Over.Hom.left key).trans (Category.assoc _ _ _)


/-- **Main result, finest form: `AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `ResidueAlgClosure`, `RedRelMul`, `RedTorsionQbar`,
`FExtend`, `FrobMorph` (proved).** -/
theorem algFrobRed_of_fine (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hR : ResidueAlgClosure) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_split hG hS hR hM h2 (reductionFrobGood_of hS hE hFr)

/-- **`TateBridge35` from I3.M0 and the seven pieces (proved).** -/
theorem tateBridge35_of_fine (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hR : ResidueAlgClosure) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_fine hG hS hR hM h2 hE hFr)

/-- **`AlgFrobRed` with `ResidueAlgClosure` split (proved).** Leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`; glue `ResidueAlgClosed`, `ResidueAlgebraic`,
`RedRelMul`, `RedTorsionQbar`, `FExtend`, `FrobMorph`. -/
theorem algFrobRed_of_finest (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hC : ResidueAlgClosed) (hA : ResidueAlgebraic) (hM : RedRelMul) (h2 : RedTorsionQbar)
    (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_fine hG hS (residueAlgClosure_of hC hA) hM h2 hE hFr

/-- **`AlgFrobRed` with `ResidueAlgClosed` discharged (proved).** Leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`; glue `ResidueAlgebraic`, `RedRelMul`,
`RedTorsionQbar`, `FExtend`, `FrobMorph`. -/
theorem algFrobRed_of_final (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hA : ResidueAlgebraic) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_finest hG hS residueAlgClosed hA hM h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the seven remaining pieces (proved).** -/
theorem tateBridge35_of_final (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hA : ResidueAlgebraic) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_final hG hS hA hM h2 hE hFr)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `RedRelMul`, `RedTorsionQbar`, `FExtend`, `FrobMorph`
(proved).** Everything else (conjugating the place, isolating the finite set, the special fibre
as an abelian variety, the residue characteristic, the valuative criterion, `κ(v) ≅ κ(w)‾`,
`σ = Frob` on `κ(v)`, rigidity) is proved here or by Mathlib / mul-rigidity. -/
theorem algFrobRed_of_main (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_final hG hS residueAlgebraic hM h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the six remaining pieces (proved).** -/
theorem tateBridge35_of_main (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_main hG hS hM h2 hE hFr)

end AlgFrobRedRed

end

#print axioms AlgFrobRedRed.algFrobRed_of_at
#print axioms AlgFrobRedRed.algFrobRedAt_of_good
#print axioms AlgFrobRedRed.algFrobRed_of_good
#print axioms AlgFrobRedRed.tateBridge35_of_good
#print axioms AlgFrobRedRed.sf_isAbelianVariety
#print axioms AlgFrobRedRed.charP_kw
#print axioms AlgFrobRedRed.isUnit_cast_of_ne
#print axioms AlgFrobRedRed.algFrobRedGood_of
#print axioms AlgFrobRedRed.algFrobRed_of_pieces
#print axioms AlgFrobRedRed.tateBridge35_of_pieces
#print axioms AlgFrobRedRed.genMap_comm
#print axioms AlgFrobRedRed.exists_lift
#print axioms AlgFrobRedRed.lift_unique
#print axioms AlgFrobRedRed.exists_redRel
#print axioms AlgFrobRedRed.redRel_unique
#print axioms AlgFrobRedRed.reductionMapGood_of
#print axioms AlgFrobRedRed.algFrobRed_of_split
#print axioms AlgFrobRedRed.tateBridge35_of_split
#print axioms AlgFrobRedRed.sigV
#print axioms AlgFrobRedRed.residue_sigV
#print axioms AlgFrobRedRed.reductionFrobGood_of
#print axioms AlgFrobRedRed.isLocalHom_toW
#print axioms AlgFrobRedRed.residueAlgClosure_of
#print axioms AlgFrobRedRed.residueAlgClosed
#print axioms AlgFrobRedRed.residueAlgebraic
#print axioms AlgFrobRedRed.pb_symm_mul
#print axioms AlgFrobRedRed.pb_symm_mul'
#print axioms AlgFrobRedRed.redRelMul
#print axioms AlgFrobRedRed.algFrobRed_of_fine
#print axioms AlgFrobRedRed.tateBridge35_of_fine
#print axioms AlgFrobRedRed.algFrobRed_of_finest
#print axioms AlgFrobRedRed.algFrobRed_of_final
#print axioms AlgFrobRedRed.tateBridge35_of_final
#print axioms AlgFrobRedRed.algFrobRed_of_main
#print axioms AlgFrobRedRed.tateBridge35_of_main
