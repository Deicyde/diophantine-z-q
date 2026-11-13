-- (leaf-fold2: copied from scratch/g0-assemble2/parts/77_newform.lean; 0 HDec name-resolution edits)
/-! ## g0-mod-newform: scratch/g0-mod-newform/part_new.lean, verbatim minus `#print axioms`, with two
changes: `LeafModCurves` is opened with `hiding` (as leaf-adopt3 did for `C9Rhof`), and
`ZInQ.Mult.le_heightD_of_mem_S_mul` (in `ZInQKernel/Main.lean`, not imported) is replaced by
g0-mod-field's verbatim copy `G0ModField.le_heightD_of_mem_S_mul` (same statement). -/
section G0ModNewformSec
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
-- g0-assemble (as leaf-adopt3 did for C9Rhof): `LeafModCurves` opened with `hiding`, since
-- Leaves.lean has `LeafModCurves` copies of these `PkgI4` names (the kernel has none)
open PkgI3 PkgI3.AbVar C9Rhof
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform
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
            map_add' := fun v w => by simp only [map_add]
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul, AlgHom.commutes, Module.algebraMap_end_apply]
              rfl
            left_inv := fun v => by
              dsimp only
              rw [σ.asModuleEquiv.symm_apply_apply, φ.symm_apply_apply,
                ρ.asModuleEquiv.apply_symm_apply]
            right_inv := fun w => by
              dsimp only
              rw [ρ.asModuleEquiv.symm_apply_apply, φ.apply_symm_apply,
                σ.asModuleEquiv.apply_symm_apply] }, fun g v => ?_⟩
  -- (leaf-fold2) explicit rewrites instead of `simp` (see mk_fix_tailA.py)
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]

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
    (fun p hp => by exact_mod_cast G0ModField.le_heightD_of_mem_S_mul hp) N hN.ne'
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

end G0ModNewformSec
