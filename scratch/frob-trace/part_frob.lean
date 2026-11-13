
/-!
# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Appended (by `build.sh`) to verbatim copies of `scratch/unram-tate/TateBridge.lean` (which is
`scratch/g0-mod-field/ModField.lean` L1-1036 plus unram-tate's section `UnramTate`) and of
`scratch/g14-trace/part_bridge.lean` (`G14Bridge.FrobTraceLink`, `G14Bridge.TateBridge35`).

Main result: `FrobTrace.tateBridge35_of_algFrobLink (hT : PkgI3.TateModuleFree)
(hF : AlgFrobLink) : G14Bridge.TateBridge35`. The operators are unram-tate's
`Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (one points-level `m`, one `Θ`, one `h`), the
scalars are `aQ g = βQ g / γQ(hgh⁻¹)` and `βQ` with `ιC ∘ βQ = β` in `ℚ̄` (proved,
`scalarsQbar`), and the conjunct `FrobTraceLink` for these operators is derived from the glue
Prop `AlgFrobLink` (reduction mod `p` of the algebraic maps `m_σ`, stated on `V_ℓ(A(ℚ̄))`).
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

Why it is true (SPECULATIVE in its Lean details; `N = 1` works): the maps `m_σ` take finitely many
values up to `G_L` (second clause), so finitely many `F_σ` occur. Put in `S` the primes of bad
reduction of `A` and the primes below which some such `F_σ` does not extend to the abelian
scheme. For `p ∉ S`, `Ā` is the reduction of `A` at `w = v ∩ L` over `k = κ(w)`. On prime-to-`p`
torsion, reduction is a bijection `A(ℚ̄)[ℓⁿ] ≅ Ā(k̄)[ℓⁿ]` (leaf I2-Red,
`PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1). Under it, `τ` acting on coordinates
becomes the `p`-power map of `k̄` (`IsArithFrob`), which on `k̄`-points is the absolute Frobenius
of `Ā`, and `F_τ` becomes its reduction `F̄_τ` (Néron mapping property of the abelian scheme, leaf
I2-NMP, `PkgI2.NeronMappingAbelianScheme`). So `m_τ` becomes `α' = F̄_τ ∘ Fr_Ā`, a `k`-morphism
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
condition for each of the finitely many `s ∈ Gal(L/ℚ)`; `S` depends on `F` only). For `p ∉ S`,
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
