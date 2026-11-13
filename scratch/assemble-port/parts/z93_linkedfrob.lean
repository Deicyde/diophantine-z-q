/-! ## assemble-port: linked-frob (LinkedFrob from N1-g1, ProperSmoothGenConnected, I2-Red, I2-NMP); see mk/mk_z93.py -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q


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
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField
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
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

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
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate
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


/-! ## 8. `RedTorsionQbar` from the leaf I2-Red (transport along `L‾ ≅ ℚ̄`) -/

section RedMul2

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(g_! T, M) ≃ Hom(T, g^* M)` is multiplicative. -/
theorem pb_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (p q : (Over.map g).obj T ⟶ M) :
    (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

set_option synthInstance.maxHeartbeats 400000 in
/-- The adjunction bijection sends `1` to `1`. -/
theorem pb_one {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S') :
    (Over.mapPullbackAdj g).homEquiv T M 1 = 1 := by
  rw [Adjunction.homEquiv_unit, Functor.map_one, MonObj.comp_one]

end RedMul2

/-- `pb_mul` at the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (p q : (Over.map g).obj T ⟶ G.X) (r u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X)
    (hr : r = (Over.mapPullbackAdj g).homEquiv T G.X (p * q))
    (hu : u = (Over.mapPullbackAdj g).homEquiv T G.X p)
    (hw : w = (Over.mapPullbackAdj g).homEquiv T G.X q) : r = u * w := by
  subst hr hu hw
  exact pb_mul g G.X T p q

set_option synthInstance.maxHeartbeats 400000 in
/-- `pb_one` at the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_one' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (r : T ⟶ ((Over.pullback g).mapGrp.obj G).X)
    (hr : r = (Over.mapPullbackAdj g).homEquiv T G.X 1) : r = 1 := by
  subst hr
  exact pb_one g G.X T

/-- **`OwDVR` (GLUE, standard: a valuation ring of a number field in which `p` is not a unit is
the localization of `𝓞_L` at a nonzero prime, a DVR; e.g. Neukirch, *Algebraic Number Theory*,
Ch. II (locator UNVERIFIED)).** Needed to apply I2-Red, whose base is a DVR. -/
def OwDVR : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar) (p : ℕ), p.Prime →
    PkgI4.LiesOver v p → IsDiscreteValuationRing (Ow L v)

/-- The place `w = ψ⁻¹(v)` of `L‾` for an `L`-isomorphism `ψ : L‾ ≅ ℚ̄`. -/
abbrev wOf {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar) :
    ValuationSubring (AlgebraicClosure L) :=
  v.comap (ψ : AlgebraicClosure L →+* PkgI4.Qbar)

theorem hw_of {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) :
    (wOf ψ v).comap (algebraMap L (AlgebraicClosure L)) = Ow L v := by
  ext x
  simp [ValuationSubring.mem_comap]

/-- `ψ` restricted to `O_w ≅ O_v`. -/
def psiW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar) :
    wOf ψ v ≃+* v where
  toFun y := ⟨ψ y, y.2⟩
  invFun z := ⟨ψ.symm z, by
    show ψ (ψ.symm z) ∈ v
    rw [AlgEquiv.apply_symm_apply]
    exact z.2⟩
  left_inv y := Subtype.ext (ψ.symm_apply_apply _)
  right_inv z := Subtype.ext (ψ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul ψ _ _)
  map_add' a b := Subtype.ext (map_add ψ _ _)

theorem psiW_toW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (a : Ow L v) :
    psiW ψ v (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v) a) = PkgI2.toW (Ow L v) v rfl a :=
  Subtype.ext (by
    show ψ (algebraMap L (AlgebraicClosure L) (a : L)) = algebraMap L PkgI4.Qbar (a : L)
    exact ψ.commutes _)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Spec(j ∘ κ(ψ)) : Spec κ(w)‾ → Spec κ(w')` over `Spec O_w`, where `w' = ψ⁻¹(v)` (an
isomorphism when `j` is bijective). -/
def iotaW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    (Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
        (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) (by
    simp only [Over.mk_hom, Over.map_obj_hom, PkgI2.specOver]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rw [psiW_toW ψ v a]
    exact hjc a)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Θ`: I2's `κ(w')`-points of `𝒜` to `κ(w)‾`-points of the special fibre (the adjunction
bijection applied to `ι ≫ y`, written out). -/
def thetaW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)) :=
  Over.homMk (pullback.lift (iotaW ψ v j hjc ≫ y).left
    (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))).hom (Over.w (iotaW ψ v j hjc ≫ y)))
    (pullback.lift_snd _ _ _)

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_left {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    (thetaW ψ v 𝒜 j hjc y).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
      Spec.map (CommRingCat.ofHom
        (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) ≫ y.left :=
  pullback.lift_fst _ _ _

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_symm {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm (thetaW ψ v 𝒜 j hjc y) =
      iotaW ψ v j hjc ≫ y :=
  Over.OverMorphism.ext (thetaW_left ψ v 𝒜 j hjc y)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Θ` as a monoid homomorphism. -/
def thetaHom {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) →*
      PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)) where
  toFun := thetaW ψ v 𝒜 j hjc
  map_one' := by
    apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
    rw [thetaW_symm, MonObj.comp_one]
    have h := pb_one' (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) 𝒜
      (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) _ rfl
    exact (((Over.mapPullbackAdj _).homEquiv _ 𝒜.X).symm_apply_eq.mpr h.symm).symm
  map_mul' y₁ y₂ := by
    apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
    rw [thetaW_symm, MonObj.comp_mul]
    exact ((pb_symm_mul' _ 𝒜 _ (thetaW ψ v 𝒜 j hjc y₁) (thetaW ψ v 𝒜 j hjc y₂)).trans
      (by rw [thetaW_symm, thetaW_symm])).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem iotaW_isIso_left {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j) :
    IsIso (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) := by
  have hb : Function.Bijective (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom) :=
    hjb.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).bijective
  haveI : IsIso (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_injective {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j)
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    Function.Injective (thetaW ψ v 𝒜 j hjc) := by
  intro y₁ y₂ h
  haveI := iotaW_isIso_left ψ v j hjb
  have h1 := congrArg ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm h
  rw [thetaW_symm, thetaW_symm] at h1
  have h2 := congrArg Over.Hom.left h1
  apply Over.OverMorphism.ext
  exact (cancel_epi (Spec.map (CommRingCat.ofHom
    (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)))).mp h2

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_surjective {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j)
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    Function.Surjective (thetaW ψ v 𝒜 j hjc) := by
  intro yt
  haveI := iotaW_isIso_left ψ v j hjb
  let z := ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm yt
  have hz2 : z.left ≫ 𝒜.X.hom = (iotaW ψ v j hjc).left ≫ (Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v)))))).hom :=
    (Over.w z).trans (Over.w (iotaW ψ v j hjc)).symm
  have hw : (inv (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) ≫ z.left) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v)))))).hom :=
    (Category.assoc _ _ _).trans ((congrArg (inv (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) ≫ ·) hz2).trans
      (IsIso.inv_hom_id_assoc _ _))
  refine ⟨Over.homMk _ hw, ?_⟩
  apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
  rw [thetaW_symm]
  apply Over.OverMorphism.ext
  exact IsIso.hom_inv_id_assoc (Spec.map (CommRingCat.ofHom
    (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) z.left

set_option synthInstance.maxHeartbeats 400000 in
/-- **I2's reduction relation gives `RedRel`** (transport along `ψ`; proved). -/
theorem redRel_of_isReductionOf {L : IF} {A : PkgI3.AbVar L}
    (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (x : A.Pt (AlgebraicClosure L))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X)
    (h : PkgI2.IsReductionOf 𝒜 e (wOf ψ v) (hw_of ψ v) x y) :
    RedRel v 𝒜 e j (Additive.ofMul (UnramTate.trPt A ψ x)) (thetaW ψ v 𝒜 j hjc y) := by
  obtain ⟨xw, hg, hc⟩ := h
  have hov : (Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) ≫ xw.left) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
    rw [Category.assoc, Over.w xw]
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact congrArg Subtype.val (psiW_toW ψ v a)
  refine ⟨Over.homMk _ hov, ?_, ?_⟩
  · have hring : Spec.map (CommRingCat.ofHom (ψ : AlgebraicClosure L →+* PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (wOf ψ v).subtype) =
        Spec.map (CommRingCat.ofHom v.subtype) ≫
          Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    have h1 := congrArg (Spec.map (CommRingCat.ofHom
      (ψ : AlgebraicClosure L →+* PkgI4.Qbar)) ≫ ·) hg
    have h2 := congrArg (· ≫ xw.left) hring
    simp only [Category.assoc] at h2
    exact ((Category.assoc _ _ _).trans h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ xw.left) hring).trans (Category.assoc _ _ _)))
  · have hring : Spec.map (CommRingCat.ofHom
        (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (wOf ψ v))) =
        Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
          Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine (thetaW_left ψ v 𝒜 j hjc y).trans ?_
    rw [hc]
    have h3 := congrArg (· ≫ xw.left) hring
    simp only [Category.assoc] at h3
    exact h3

/-- `t = σ⁻¹|_{O_w}` (for `σ ∈ D(v)`, `L/ℚ` Galois). -/
def tSig {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Ow L v →+* Ow L v where
  toFun a := ⟨(σ⁻¹).restrictNormal L (a : L), by
    show algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L)) ∈ v
    rw [AlgEquiv.restrictNormal_commutes]
    exact (sigV σ⁻¹ (inv_mem hσ) ⟨_, a.2⟩).2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

/-- `t = σ⁻¹|_{O_w}` induces `Frob⁻¹` on `κ(w)` (proved from `IsArithFrob`). -/
theorem tSig_residue {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} {σ : PkgI4.GQ}
    {p : ℕ} (hσ : PkgI4.IsArithFrob σ v p) (a : Ow L v) :
    IsLocalRing.residue (Ow L v) (tSig σ hσ.1 a) ^ p = IsLocalRing.residue (Ow L v) a := by
  apply (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).injective
  rw [map_pow, IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
    ← residue_sigV hσ]
  congr 1
  apply Subtype.ext
  show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L))) =
    algebraMap L PkgI4.Qbar (a : L)
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendCore` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model).** `FExtend` with `t = σ⁻¹|_{O_w}` fixed (`tSig`): there is
a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` fixing the unit section and extending `F`
(whenever `x'` is the lift of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` is a lift of `f x`). See `FExtend`
for why it is true. -/
def FExtendCore : Prop :=
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
        ∃ Ft : 𝒜.X.left ⟶ 𝒜.X.left,
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ≫ (η[𝒜.X]).left ∧
          ∀ (x : PtQ L A)
            (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
            genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
            ∃ x'' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
              genMap v 𝒜 e (f x) = Spec.map (CommRingCat.ofHom v.subtype) ≫ x''.left ∧
              x''.left = Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft

/-- **`FExtend` from `FExtendCore` (proved):** `t = tSig σ`, `t(a)^p ≡ a` by `tSig_residue`. -/
theorem fExtend_of_core (h : FExtendCore) : FExtend := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, h1, h2, h3⟩ := h L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  exact ⟨Ft, tSig σ hσ.1, h1, tSig_residue hσ, h2, h3⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendGen` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model `𝒜^{(t)}`).** For `F`, `σ`, `f` as in `FExtend` and
`t = σ⁻¹|_{O_w}`: there is a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` fixing the unit
section whose restriction to the generic fibre is `F` (through `e`):
`e⁻¹ ≫ pr₁ ≫ F̃ = F ≫ e⁻¹ ≫ pr₁` as maps `A → 𝒜`.

Why it is true: `f(x) ∈ A(ℚ̄)` for all `x` forces `F` to lie over `Spec(σ⁻¹|_L)`, so `F` is an
`L`-morphism `A → A^{(t)}`; I2-NMP for `𝒜` and its base change `𝒜^{(t)}` along `Spec t` extends
it; `F̃` fixes the unit section because both sides are sections of the separated `𝒜 → Spec O_w`
agreeing at the generic point (`f(0) = 0`). -/
def FExtendGen : Prop :=
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
        ∃ Ft : 𝒜.X.left ⟶ 𝒜.X.left,
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ≫ (η[𝒜.X]).left ∧
          (e.inv.hom.hom : A.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (Ow L v) L)))).obj 𝒜.X).left ≫
            pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) ≫ Ft =
          F ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (Ow L v) L)))).obj 𝒜.X).left ≫
            pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendCore` from `FExtendGen` (proved):** the lift of `f x` is
`Spec(σ|_{O_v}) ≫ x' ≫ F̃`; it lies over `Spec(toW)` since `σ ∘ t = id` on `O_w`, and restricts to
`f x` by `hf`, the generic compatibility and `Spec σ ≫ Spec(O_v ⊂ ℚ̄) = Spec(O_v ⊂ ℚ̄) ≫ Spec σ_v`. -/
theorem fExtendCore_of_gen (h : FExtendGen) : FExtendCore := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, h1, h2, h3⟩ := h L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  refine ⟨Ft, h1, h2, fun x x' hx' => ?_⟩
  have hring1 : Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) ≫
        Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) =
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L))) =
      algebraMap L PkgI4.Qbar (a : L)
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hov : (Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
    rw [Category.assoc, Category.assoc, h1, ← Category.assoc x'.left, Over.w x']
    exact hring1
  refine ⟨Over.homMk _ hov, ?_, rfl⟩
  have hring2 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom v.subtype) =
      Spec.map (CommRingCat.ofHom v.subtype) ≫ Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hfx := hf x
  have hx'' := (Category.assoc _ _ _).symm.trans hx'
  have hx3 := ((congrArg ((Additive.toMul x).left ≫ ·) (Category.assoc _ _ Ft).symm).trans
    (Category.assoc _ _ Ft).symm).trans ((congrArg (· ≫ Ft) hx'').trans (Category.assoc _ _ _))
  exact (Category.assoc _ _ _).trans <|
    (congrArg (· ≫ _) hfx).trans <|
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans <|
    (congrArg (fun m => _ ≫ (Additive.toMul x).left ≫ m) h3.symm).trans <|
    (congrArg (_ ≫ ·) hx3).trans <|
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x'.left ≫ Ft) hring2).trans
      (Category.assoc _ _ _))

/-! ## 9. `FrobMorph` from the existence of the absolute Frobenius -/

/-- **`AbsFrob` (GLUE; the absolute Frobenius of an `𝔽_p`-scheme; standard, e.g. SGA 5 XIV,
Stacks Tag 0CC6 (locators UNVERIFIED); not in Mathlib 4.35).** For a scheme `X` over a field `k`
of characteristic `p` there is an endomorphism `Fr_X` (the identity on the space, `f ↦ f^p` on
sections) lying over `Fr_{Spec k} = Spec(z ↦ z^p)`, and natural for points: for every ring `R` of
characteristic `p` and `g : Spec R → X`, `Spec(r ↦ r^p) ≫ g = g ≫ Fr_X`. -/
def AbsFrob : Prop :=
  ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (X : Over (Spec (.of k))),
    ∃ Fr : X.left ⟶ X.left,
      Fr ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (frobenius k p)) ∧
      ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ X.left),
        Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr

/-- A ring endomorphism inducing an inverse Frobenius on the residue field is local. -/
theorem isLocalHom_of_resPow {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime)
    (t : O →+* O) (hres : ∀ a, IsLocalRing.residue O (t a) ^ p = IsLocalRing.residue O a) :
    IsLocalHom t := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : IsLocalRing.residue O a = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  rw [← hres a] at h1
  have h2 : IsLocalRing.residue O (t a) = 0 := pow_eq_zero_iff hp.ne_zero |>.mp h1
  exact ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h2)) ha

/-- The unit section of the special fibre, followed by the projection to `𝒜`, is the closed
point followed by the unit section of `𝒜` (proved). -/
theorem sf_eta_fst {O : Type} [CommRing O] [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) :
    (η[(sf 𝒜).X]).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ (η[𝒜.X]).left := by
  let g' := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 (Spec (.of O))) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 (Spec (.of O))) g' = g' := by
    have hc : pullback.fst (𝟙 (Spec (.of O))) g' = pullback.snd (𝟙 (Spec (.of O))) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 (Spec (.of O))) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FrobMorph` from `AbsFrob` (proved):** `β = Fr_Ā ≫ F̄`, with `F̄ = F̃ ×_{Spec t} Spec(t̄)`
(`pullback.map`) and `t̄` the map induced by `t` on `κ(O)` (`t̄ = Frob⁻¹`); `β` lies over
`Spec(Frob ∘ t̄) = id`; it fixes `0` (`sf_eta_fst`, point-naturality at the unit section); the
point formula is point-naturality at `y`. -/
theorem frobMorph_of (hA : AbsFrob) : FrobMorph := by
  intro O _ _ p hp hk 𝒜 _ Ft t hover hres hzero
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isLocalHom_of_resPow hp t hres
  let tb := IsLocalRing.ResidueField.map t
  have htb : ∀ z, frobenius (IsLocalRing.ResidueField O) p (tb z) = z := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact hres a
  let g' := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  have heq2 : g' ≫ Spec.map (CommRingCat.ofHom t) = Spec.map (CommRingCat.ofHom tb) ≫ g' := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hid : Spec.map (CommRingCat.ofHom (frobenius (IsLocalRing.ResidueField O) p)) ≫
      Spec.map (CommRingCat.ofHom tb) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (frobenius (IsLocalRing.ResidueField O) p).comp tb = RingHom.id _ from
      RingHom.ext htb, CommRingCat.ofHom_id, Spec.map_id]
  let Fb : pullback 𝒜.X.hom g' ⟶ pullback 𝒜.X.hom g' :=
    pullback.map 𝒜.X.hom g' 𝒜.X.hom g' Ft (Spec.map (CommRingCat.ofHom tb))
      (Spec.map (CommRingCat.ofHom t)) hover.symm heq2
  have hFb1 : Fb ≫ pullback.fst 𝒜.X.hom g' = pullback.fst 𝒜.X.hom g' ≫ Ft :=
    pullback.lift_fst _ _ _
  have hFb2 : Fb ≫ pullback.snd 𝒜.X.hom g' =
      pullback.snd 𝒜.X.hom g' ≫ Spec.map (CommRingCat.ofHom tb) := pullback.lift_snd _ _ _
  obtain ⟨Fr0, hFr1, hFr2⟩ := hA (IsLocalRing.ResidueField O) p
    (Over.mk (pullback.snd 𝒜.X.hom g'))
  let Fr : pullback 𝒜.X.hom g' ⟶ pullback 𝒜.X.hom g' := Fr0
  have hFr1' : Fr ≫ pullback.snd 𝒜.X.hom g' = pullback.snd 𝒜.X.hom g' ≫
      Spec.map (CommRingCat.ofHom (frobenius (IsLocalRing.ResidueField O) p)) := hFr1
  have hFr2' : ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ pullback 𝒜.X.hom g'),
      Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr := fun R _ _ g => hFr2 R g
  have hw : (Fr ≫ Fb) ≫ pullback.snd 𝒜.X.hom g' = pullback.snd 𝒜.X.hom g' := by
    rw [Category.assoc, hFb2, ← Category.assoc, hFr1', Category.assoc, hid, Category.comp_id]
  let e0 : Spec (.of (IsLocalRing.ResidueField O)) ⟶ pullback 𝒜.X.hom g' := (η[(sf 𝒜).X]).left
  have he0 : e0 ≫ pullback.fst 𝒜.X.hom g' = g' ≫ (η[𝒜.X]).left := sf_eta_fst 𝒜
  have he0s : e0 ≫ pullback.snd 𝒜.X.hom g' = 𝟙 _ := Over.w η[(sf 𝒜).X]
  refine ⟨Over.homMk (U := (sf 𝒜).X) (V := (sf 𝒜).X) (Fr ≫ Fb) hw, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    show e0 ≫ Fr ≫ Fb = e0
    have hn := hFr2' (IsLocalRing.ResidueField O) e0
    rw [← Category.assoc, ← hn, Category.assoc]
    have hη : e0 ≫ Fb = Spec.map (CommRingCat.ofHom tb) ≫ e0 := by
      apply pullback.hom_ext
      · rw [Category.assoc, hFb1, ← Category.assoc, he0, Category.assoc, Category.assoc, he0,
          hzero, ← Category.assoc, heq2, Category.assoc]
      · rw [Category.assoc, hFb2, ← Category.assoc, he0s, Category.id_comp, Category.assoc, he0s,
          Category.comp_id]
    rw [hη, ← Category.assoc, hid, Category.id_comp]
  · intro y φ hφ
    haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField O)) p :=
      charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) _).injective p
    have hφ' : φ = frobenius _ p := RingHom.ext hφ
    subst hφ'
    let yl : Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField O))) ⟶ pullback 𝒜.X.hom g' :=
      y.left
    have hn := hFr2' (AlgebraicClosure (IsLocalRing.ResidueField O)) yl
    show (yl ≫ Fr ≫ Fb) ≫ pullback.fst 𝒜.X.hom g' = _ ≫ yl ≫ pullback.fst 𝒜.X.hom g' ≫ Ft
    rw [Category.assoc, Category.assoc, hFb1, ← Category.assoc, ← Category.assoc, ← hn,
      Category.assoc, Category.assoc]

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

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite` and
`SmoothGeomConnIntegral` and the glue `RedTorsionQbar`, `FExtend`, `FrobMorph` (proved).**
Proved here (or in Mathlib / mul-rigidity): conjugating the place, isolating the finite set, the
special fibre as an abelian variety (from `SmoothGeomConnIntegral`), the residue characteristic and
the units `ℓⁿ`, the valuative criterion (existence and uniqueness of lifts), `κ(v) ≅ κ(w)‾`
(`residueAlgClosed`, `residueAlgebraic`), the reduction map as a homomorphism (`redRelMul`),
`σ = Frob` on `κ(v)`, rigidity. -/
theorem algFrobRed_of_five (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_main hG hS redRelMul h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the five pieces (proved).** -/
theorem tateBridge35_of_five (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_five hG hS h2 hE hFr)

/-! ### `OwDVR` (proved; adapted from neron-lg's `dvrAt_center`) -/

section DVR

open NumberField

/-- The DVR `𝓞_{L,P}` of a nonzero prime `P` of `𝓞_L`, as a valuation subring of `L` (as in
neron-lg's `dvrAt`). -/
noncomputable def dvrAt' {K : Type} [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ValuationSubring K :=
  (P.valuation K).valuationSubring

instance {K : Type} [Field K] [NumberField K] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (dvrAt' P) := by
  unfold dvrAt'; infer_instance

theorem ringOfIntegers_mem' {K : Type} [Field K] [NumberField K] (O : ValuationSubring K)
    (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO' {K : Type} [Field K] [NumberField K] (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem' O)

/-- `p ∈ 𝔪_{O_w}` for `v ∣ p`. -/
theorem natCast_mem_maximalIdeal {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) :
    (p : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
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
  exact (ValuationSubring.coe_mem_nonunits_iff).mp h1

/-- **`OwDVR` holds (proved):** `O_w` contains `𝓞_L`; its center `P = 𝔪_{O_w} ∩ 𝓞_L` is a nonzero
prime (it contains `p`); `𝓞_{L,P} ⊆ O_w`, and a DVR is a maximal proper valuation subring
(`ValuationSubring.eq_of_le_of_ne_top`), so `O_w = 𝓞_{L,P}`. -/
theorem owDVR : OwDVR := by
  intro L _ v p hp hv
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    { asIdeal := (IsLocalRing.maximalIdeal (Ow L v)).comap (toO' (Ow L v))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have hmem : (p : 𝓞 L) ∈ (IsLocalRing.maximalIdeal (Ow L v)).comap (toO' (Ow L v)) := by
          rw [Ideal.mem_comap, map_natCast]; exact hpm
        rw [hbot, Ideal.mem_bot] at hmem
        exact hp.ne_zero (by exact_mod_cast hmem) }
  have hP : ∀ x : 𝓞 L, x ∈ P.asIdeal ↔ toO' (Ow L v) x ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    fun x => Iff.rfl
  have heq : dvrAt' P = Ow L v := by
    apply ValuationSubring.eq_of_le_of_ne_top
    · intro x hx
      obtain ⟨n, d, hnd⟩ :=
        IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P x hx
      have hd : IsUnit (toO' (Ow L v) d) := by
        by_contra h
        exact d.2 ((hP d).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have hvd : (Ow L v).valuation (algebraMap (𝓞 L) L d) = 1 :=
        ((Ow L v).valuation_eq_one_iff _).1 hd
      apply (Ow L v).mem_of_valuation_le_one
      have h2 := congrArg (Ow L v).valuation hnd
      rw [map_mul, hvd, _root_.mul_one] at h2
      rw [h2]
      exact (Ow L v).valuation_le_one (toO' (Ow L v) n)
    · intro htop
      have hall : ∀ y : L, y ∈ Ow L v := by
        intro y; rw [htop]; exact ValuationSubring.mem_top y
      have hp0 : ((p : Ow L v) : L) ≠ 0 := by
        simp only [ne_eq, map_natCast]
        push_cast
        exact_mod_cast hp.ne_zero
      have hu : IsUnit (p : Ow L v) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨_, hall (((p : Ow L v) : L))⁻¹⟩, Subtype.ext ?_⟩
        rw [Subring.coe_mul]
        exact mul_inv_cancel₀ hp0
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm hu
  have key : ∀ O' : ValuationSubring L, dvrAt' P = O' → IsDiscreteValuationRing O' := by
    rintro O' rfl; infer_instance
  exact key _ heq

end DVR

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedTorsionQbar` from the leaf I2-Red and `OwDVR` (proved).** Transport along an
`L`-isomorphism `ψ : L‾ ≅ ℚ̄` (`UnramTate.trPt`) and the bijective homomorphism `Θ` from I2's
`κ(w')`-points of `𝒜` to the `κ(w)‾`-points of `sf 𝒜`; I2's reductions are `RedRel`s
(`redRel_of_isReductionOf`), reductions are unique (`redRel_unique`) and additive
(`redRelMul`). -/
theorem redTorsionQbar_of (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR) :
    RedTorsionQbar := by
  intro L _ A p hp v hv 𝒜 _ e j hjb hjc m hm hmu
  haveI := hD L v p hp hv
  haveI : Algebra.IsAlgebraic L PkgI4.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : IsAlgClosure L PkgI4.Qbar := ⟨inferInstance, inferInstance⟩
  let ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar :=
    IsAlgClosure.equiv L (AlgebraicClosure L) PkgI4.Qbar
  obtain ⟨hR1, hR2⟩ := hRed L (Ow L v) (wOf ψ v) (hw_of ψ v) (ObjBridge.toGrp A) 𝒜 e m hm hmu
  let Φ := UnramTate.trPt A ψ
  let Θ := thetaHom ψ v 𝒜 j hjc
  have hΘinj := thetaW_injective ψ v 𝒜 j hjb hjc
  have hΘsurj := thetaW_surjective ψ v 𝒜 j hjb hjc
  have hT3 := redRel_of_isReductionOf (A := A) ψ v 𝒜 e j hjc
  have hun := redRel_unique v 𝒜 e j
  have hex := exists_redRel v 𝒜 e j hjc
  have hmul := redRelMul L A v 𝒜 e j
  have h01 : RedRel v 𝒜 e j 0 1 := by
    obtain ⟨z, hz⟩ := hex 0
    have h2 := hmul 0 0 z z hz hz
    rw [add_zero] at h2
    have h3 : z * z = z := hun 0 _ _ h2 hz
    have hz1 : z = 1 := mul_eq_right.mp h3
    rw [hz1] at hz
    exact hz
  have hΘ1 : ∀ y, thetaW ψ v 𝒜 j hjc y = 1 → y = 1 := fun y h =>
    hΘinj (h.trans (map_one Θ).symm)
  have htors : ∀ x : PtQ L A, m • x = 0 →
      Φ.symm (Additive.toMul x) ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) m := by
    intro x hx
    show (Φ.symm (Additive.toMul x)) ^ m = 1
    rw [← map_pow, ← toMul_nsmul, hx, toMul_zero, map_one]
  have hT3' : ∀ (x : PtQ L A) yw, PkgI2.IsReductionOf 𝒜 e (wOf ψ v) (hw_of ψ v)
      (Φ.symm (Additive.toMul x)) yw → RedRel v 𝒜 e j x (thetaW ψ v 𝒜 j hjc yw) := by
    intro x yw h
    have hr := hT3 _ yw h
    rw [show UnramTate.trPt A ψ (Φ.symm (Additive.toMul x)) = Additive.toMul x from
      Φ.apply_symm_apply _, ofMul_toMul] at hr
    exact hr
  constructor
  · intro x hx
    obtain ⟨yw, ⟨hyw1, hyw2⟩, -⟩ := hR1 _ (htors x hx)
    have hr := hT3' x yw hyw2
    refine ⟨Additive.ofMul (thetaW ψ v 𝒜 j hjc yw), ⟨?_, hr⟩, ?_⟩
    · rw [← ofMul_pow]
      show Additive.ofMul (Θ yw ^ m) = 0
      rw [← map_pow, hyw1, map_one]
      rfl
    · rintro y' ⟨-, hy'⟩
      exact Additive.toMul.injective (hun x _ _ hy' hr)
  · intro yt hyt
    obtain ⟨yw, hyw⟩ := hΘsurj (Additive.toMul yt)
    have hywt : yw ^ m = 1 := by
      apply hΘinj
      show Θ (yw ^ m) = Θ 1
      rw [map_pow, map_one]
      show (thetaW ψ v 𝒜 j hjc yw) ^ m = 1
      rw [hyw, ← toMul_nsmul, hyt, toMul_zero]
    obtain ⟨xw0, ⟨hxw1, hxw2⟩, -⟩ := hR2 yw hywt
    let xw : A.Pt (AlgebraicClosure L) := xw0
    have hr := hT3 xw yw hxw2
    rw [hyw] at hr
    have hx2t : m • Additive.ofMul (Φ xw) = 0 := by
      rw [← ofMul_pow, ← map_pow]
      have : xw ^ m = 1 := hxw1
      rw [this, map_one]
      rfl
    refine ⟨Additive.ofMul (Φ xw), ⟨hx2t, hr⟩, ?_⟩
    rintro x1 ⟨hx1t, hx1r⟩
    have hd : RedRel v 𝒜 e j (x1 - Additive.ofMul (Φ xw)) 1 := by
      obtain ⟨yd, hyd⟩ := hex (x1 - Additive.ofMul (Φ xw))
      have h3 := hmul _ _ yd (Additive.toMul yt) hyd hr
      rw [sub_add_cancel] at h3
      have h4 : yd * Additive.toMul yt = Additive.toMul yt := hun x1 _ _ h3 hx1r
      rw [mul_eq_right.mp h4] at hyd
      exact hyd
    have hdt : m • (x1 - Additive.ofMul (Φ xw)) = 0 := by
      rw [smul_sub, hx1t, hx2t, sub_zero]
    obtain ⟨yd', ⟨hyd'1, hyd'2⟩, -⟩ := hR1 _ (htors _ hdt)
    have hyd'eq : yd' = 1 := hΘ1 yd' (hun _ _ _ (hT3' _ yd' hyd'2) hd)
    have h1t : (1 : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure L)) ∈
        PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) m := one_pow m
    obtain ⟨y0, ⟨hy01, hy02⟩, -⟩ := hR1 1 h1t
    have hy0eq : y0 = 1 := by
      have hr0 := hT3 1 y0 hy02
      rw [map_one, ofMul_one] at hr0
      exact hΘ1 y0 (hun 0 _ _ hr0 h01)
    have hxd1 := (hR2 1 (one_pow m)).unique ⟨htors _ hdt, hyd'eq ▸ hyd'2⟩ ⟨h1t, hy0eq ▸ hy02⟩
    have h5 : Additive.toMul (x1 - Additive.ofMul (Φ xw)) = 1 := by
      have h6 := congrArg Φ hxd1
      rw [MulEquiv.apply_symm_apply] at h6
      exact h6.trans (map_one Φ)
    exact sub_eq_zero.mp (Additive.toMul.injective (h5.trans toMul_zero.symm))

/-- **`AlgFrobRed` from the leaves `GoodRedCofinite`, `SmoothGeomConnIntegral`, I2-Red (kernel
leaf `PkgI2.ReductionTorsionBijective`) and the glue `OwDVR`, `FExtend`, `FrobMorph` (proved).** -/
theorem algFrobRed_of_I2 (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_five hG hS (redTorsionQbar_of hRed hD) hE hFr

/-- **`TateBridge35` from I3.M0, I2-Red and the five other pieces (proved).** -/
theorem tateBridge35_of_I2 (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR)
    (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_I2 hG hS hRed hD hE hFr)

/-- **Main result, final form: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`
and `SmoothGeomConnIntegral`, the kernel leaf I2-Red (`PkgI2.ReductionTorsionBijective`), and the
glue `FExtend` and `FrobMorph` (proved).** -/
theorem algFrobRed_of_leaves (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_I2 hG hS hRed owDVR hE hFr

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`, `FExtend`,
`FrobMorph` (proved).** -/
theorem tateBridge35_of_leaves (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend)
    (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_leaves hG hS hRed hE hFr)

/-- **Main result, finest form: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendCore`
and `FrobMorph` (proved).** -/
theorem algFrobRed_of_core (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendCore) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_leaves hG hS hRed (fExtend_of_core hE) hFr

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendCore`, `FrobMorph` (proved).** -/
theorem tateBridge35_of_core (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendCore) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_core hG hS hRed hE hFr)

/-- **Main result with `FrobMorph` reduced: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendCore` and
`AbsFrob` (proved).** -/
theorem algFrobRed_of_absFrob (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendCore) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_core hG hS hRed hE (frobMorph_of hA)

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendCore`, `AbsFrob` (proved).** -/
theorem tateBridge35_of_absFrob (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendCore) (hA : AbsFrob) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_absFrob hG hS hRed hE hA)

/-- **Main result, finest form: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendGen` and
`AbsFrob` (proved).** -/
theorem algFrobRed_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_absFrob hG hS hRed (fExtendCore_of_gen hE) hA

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendGen`, `AbsFrob` (proved).** -/
theorem tateBridge35_of_gen (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendGen) (hA : AbsFrob) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_gen hG hS hRed hE hA)

end AlgFrobRedRed

end



/-!
# afr-absfrob: the absolute Frobenius of a scheme of characteristic `p`

Construction (not in Mathlib 4.35): for a scheme `X` with `(p : Γ(X, ⊤)) = 0`, `fr p X` is the
identity on the underlying space and `s ↦ s ^ p` on every ring of sections.
-/

noncomputable section

namespace AbsFrobDef

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- `x ↦ x ^ p` as a ring endomorphism of a commutative ring in which `p = 0` (the ring may be
trivial, so no `CharP` instance is assumed). -/
def powHom (R : Type*) [CommRing R] (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow _
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' x y := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · have := (CharP.charP_iff_prime_eq_zero hp.out).2 h
      exact add_pow_char x y p

@[simp] theorem powHom_apply (R : Type*) [CommRing R] (h : (p : R) = 0) (x : R) :
    powHom p R h x = x ^ p := rfl

omit hp in
/-- `p = 0` in every ring of sections of `X` if it is `0` in the global sections. -/
theorem natCast_sections {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom hX
  rwa [map_natCast, map_zero] at this

/-- The Frobenius on the structure presheaf. -/
def frobC (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat (𝟙 (X : TopCat))).obj X.presheaf where
  app U := CommRingCat.ofHom (powHom p _ (natCast_sections p hX U.unop))
  naturality U V i := by
    ext x
    exact (map_pow (X.presheaf.map i).hom x p).symm

/-- The absolute Frobenius as a morphism of presheafed spaces. -/
def frobPSh (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c := frobC p X hX

/-- The stalk map of the absolute Frobenius is `a ↦ a ^ p`. -/
theorem frob_stalkMap (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (x : X)
    (a : X.presheaf.stalk x) :
    ((frobPSh p X hX).stalkMap x).hom a = a ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have := PresheafedSpace.stalkMap_germ_apply (frobPSh p X hX) U x hxU s
  erw [this]
  show X.presheaf.germ U x hxU (s ^ p) = _
  rw [map_pow]

/-- **The absolute Frobenius** `Fr_X : X ⟶ X` of a scheme with `p = 0` on `X`: the identity on
the underlying space, `s ↦ s ^ p` on sections (local on stalks since `a ^ p` a unit forces `a` a
unit). -/
def fr (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) : X ⟶ X :=
  Scheme.Hom.mk
    { toHom := frobPSh p X hX
      prop := fun x => ⟨fun a ha => by
        rw [frob_stalkMap p X hX x a] at ha
        exact (isUnit_pow_iff hp.out.ne_zero).mp ha⟩ }

@[simp] theorem fr_base (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    (fr p X hX).base = 𝟙 _ := rfl

theorem fr_app (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (fr p X hX).app U = CommRingCat.ofHom (powHom p _ (natCast_sections p hX U)) := rfl

/-- **Naturality of the absolute Frobenius:** `f ≫ Fr_X = Fr_Y ≫ f` for every morphism
`f : Y ⟶ X` of schemes on which `p = 0`. -/
theorem fr_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) : f ≫ fr p X hX = fr p Y hY ≫ f := by
  have hb : (f ≫ fr p X hX).base = (fr p Y hY ≫ f).base := by
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, fr_base, fr_base, Category.comp_id,
      Category.id_comp]
  refine Scheme.Hom.ext hb fun U => ?_
  rw [show (eqToHom (congr((Opens.map $hb.symm).obj U))).op =
      𝟙 (op ((Opens.map (f ≫ fr p X hX).base).obj U)) from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app, fr_app, fr_app]
  ext s
  exact map_pow (f.app U).hom s p

omit hp in
theorem natCast_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) : (p : Γ(Spec R, ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso R).inv.hom h
  rwa [map_natCast, map_zero] at this

omit hp in
theorem natCast_of_hom {R : CommRingCat.{u}} (h : (p : R) = 0) {X : Scheme.{u}}
    (f : X ⟶ Spec R) : (p : Γ(X, ⊤)) = 0 := by
  have := congrArg f.appTop.hom (natCast_Spec p R h)
  rwa [map_natCast, map_zero] at this

/-- **The absolute Frobenius of an affine scheme** is `Spec` of `r ↦ r ^ p`. -/
theorem fr_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) :
    fr p (Spec R) (natCast_Spec p R h) = Spec.map (CommRingCat.ofHom (powHom p R h)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso R).hom, Scheme.ΓSpecIso_naturality]
  ext s
  exact map_pow (Scheme.ΓSpecIso R).hom.hom s p

end AbsFrobDef

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry


/-- `frobenius R p` is `AbsFrobDef.powHom`. -/
theorem frobenius_eq_powHom (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    frobenius R p = AbsFrobDef.powHom p R (CharP.cast_eq_zero R p) :=
  RingHom.ext fun _ => rfl

/-- **`AbsFrob` (proved):** `Fr_X = AbsFrobDef.fr`. -/
theorem absFrob : AbsFrob := by
  intro k _ p _ _ X
  have hk : ((p : ℕ) : CommRingCat.of k) = 0 := CharP.cast_eq_zero k p
  have hX := AbsFrobDef.natCast_of_hom p hk X.hom
  refine ⟨AbsFrobDef.fr p X.left hX, ?_, fun R _ _ g => ?_⟩
  · rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of k) hk,
      AbsFrobDef.fr_naturality p X.hom]
  · have hR : ((p : ℕ) : CommRingCat.of R) = 0 := CharP.cast_eq_zero R p
    rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of R) hR, AbsFrobDef.fr_naturality p g]

end AlgFrobRedRed



/-! # afr-absfrob, part 2: `FExtendGen` from the Néron mapping property (leaf I2-NMP)

Appended by `build.sh` after alg-frob-red's `AlgFrobRed.lean` (verbatim copy) and the
absolute-Frobenius part. -/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry Limits
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-- **Galois rigidity of embeddings (proved).** For a normal extension `L/ℚ`, a domain `R` and two
ring maps `ψ₁, ψ₂ : L → R` which agree after some ring map `χ : R → Q` to a nontrivial ring,
`ψ₁ = ψ₂`. (`ψ₂ ℓ` is a root of the minimal polynomial of `ℓ`, which splits in `L`; so
`ψ₂ ℓ = ψ₁ r` for a conjugate `r`, and `χ ∘ ψ₁` is injective.) -/
theorem ringHom_eq_of_normal {L R Q : Type*} [Field L] [Algebra ℚ L] [Normal ℚ L]
    [CommRing R] [IsDomain R] [CommRing Q] [Nontrivial Q]
    (ψ₁ ψ₂ : L →+* R) (χ : R →+* Q) (h : χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ := by
  ext ℓ
  have hint : IsIntegral ℚ ℓ := Normal.isIntegral inferInstance ℓ
  have hsp := Normal.splits (inferInstance : Normal ℚ L) ℓ
  have hc : ψ₁.comp (algebraMap ℚ L) = ψ₂.comp (algebraMap ℚ L) := RingHom.ext_rat _ _
  have hne : ((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁ ≠ 0 :=
    Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
  have hroot : ψ₂ ℓ ∈ (((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.map_map, hc,
      ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  rw [hsp.roots_map ψ₁, Multiset.mem_map] at hroot
  obtain ⟨r, -, hr⟩ := hroot
  have hrl : r = ℓ := (χ.comp ψ₁).injective (by
    show χ (ψ₁ r) = χ (ψ₁ ℓ)
    rw [hr]
    exact (RingHom.congr_fun h ℓ).symm)
  rw [← hr, hrl]

/-- **Morphisms from an integral scheme to `Spec L`, `L/ℚ` normal, agreeing at one field-valued
point, are equal (proved).** Via `Γ(X, ⊤)` (a domain) and `ringHom_eq_of_normal`. -/
theorem hom_spec_eq_of_point {L : Type} [Field L] [Algebra ℚ L] [Normal ℚ L] {X : Scheme.{0}}
    [IsIntegral X] {K : Type} [Field K] (g₁ g₂ : X ⟶ Spec (.of L)) (x : Spec (.of K) ⟶ X)
    (h : x ≫ g₁ = x ≫ g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  have key := ringHom_eq_of_normal ((Scheme.ΓSpecIso (.of L)).inv ≫ g₁.appTop).hom
    ((Scheme.ΓSpecIso (.of L)).inv ≫ g₂.appTop).hom (x.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
    (by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 1
      simp only [Category.assoc]
      rw [reassoc_of% h'])
  rw [← cancel_epi (Scheme.ΓSpecIso (.of L)).inv]
  exact CommRingCat.hom_ext key

/-- `Spec` of an injective ring map is dominant (proved; the kernel is `0 ≤ nilradical`). -/
theorem isDominant_Spec_map_of_injective {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (h : Function.Injective φ.hom) : IsDominant (Spec.map φ) := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap φ.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [h (hx.trans (map_zero _).symm)]
  exact zero_mem _

/-- Cancelling `Spec(s)` for an automorphism `s` of `ℚ̄` (proved). -/
theorem spec_aut_cancel (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {X : Scheme.{0}}
    {a b : Spec (.of (AlgebraicClosure ℚ)) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ a =
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ b) :
    a = b := by
  have hi : Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
          (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = RingHom.id _ from
        RingHom.ext fun x => s.symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  calc a = (Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) ≫ a := by
          rw [hi, Category.id_comp]
    _ = b := by rw [Category.assoc, h, ← Category.assoc, hi, Category.id_comp]

set_option synthInstance.maxHeartbeats 400000 in
/-- The unit section of a base change `(Over.pullback g').mapGrp.obj 𝒜`, followed by the first
projection, is `g'` followed by the unit section of `𝒜` (proved; `sf_eta_fst` for any `g'`). -/
theorem pb_eta_fst {S S' : Scheme.{0}} (g' : S' ⟶ S) (𝒜 : Grp (Over S)) :
    (η[((Over.pullback g').mapGrp.obj 𝒜).X]).left ≫ pullback.fst 𝒜.X.hom g' =
      g' ≫ (η[𝒜.X]).left := by
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 S) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 S) g' = g' := by
    have hc : pullback.fst (𝟙 S) g' = pullback.snd (𝟙 S) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 S) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

/-- `Spec(O_w → L)`. -/
abbrev jSpec (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    Spec (.of L) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))

/-- `Spec(t)`, `t = σ⁻¹|_{O_w}`. -/
abbrev tSpec {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Spec (.of (Ow L v)) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (tSig σ hσ))

/-- `τ = σ⁻¹|_L`. -/
abbrev tauL (L : IF) [IsGalois ℚ L] (σ : PkgI4.GQ) : L →+* L :=
  (((σ⁻¹).restrictNormal L : L ≃ₐ[ℚ] L) : L →+* L)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **`FExtendGen` from the leaf I2-NMP (proved).**
1. `F` lies over `Spec τ`, `τ = σ⁻¹|_L`: both `F ≫ A → Spec L` and `A → Spec L → Spec L` agree at
   the `ℚ̄`-point `0` (from `f 0 = 0`), and `A` is integral (`hom_spec_eq_of_point`).
2. `ℬ = 𝒜 ×_{Spec t} Spec O_w` (the conjugate model) is an abelian scheme (base change).
3. `φ = (e ≫ F ≫ e⁻¹ ≫ pr₁, pr₂) : 𝒜_L → ℬ_L` is an `L`-morphism; I2-NMP gives `G : 𝒜 → ℬ`
   over `O_w` with `G_L = φ`; `F̃ = G ≫ pr₁` lies over `Spec t` and restricts to `F`.
4. `F̃` fixes the unit section: both sides agree on `Spec L` (because `F(0) = 0` twisted, by
   separatedness of `A` and dominance of `Spec ℚ̄ → Spec L`), hence on `Spec O_w`
   (separatedness of `𝒜`, dominance of `Spec L → Spec O_w`). -/
theorem fExtendGen_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendGen := by
  intro L _ _ A F _ _ p hp v σ hv hσ 𝒜 h𝒜 e f hf
  generalize hσ.1 = hσ1
  haveI : IsDiscreteValuationRing (Ow L v) := owDVR L v p hp hv
  haveI : IsProper 𝒜.X.hom := h𝒜.proper
  haveI : Smooth 𝒜.X.hom := h𝒜.smooth
  haveI : GeometricallyConnected 𝒜.X.hom := h𝒜.geomConnected
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  -- ring identities
  have hR1 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L a)) = algebraMap L PkgI4.Qbar a
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hR2 : jSpec L v ≫ tSpec σ hσ1 = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ jSpec L v := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  -- the zero point
  let x0 : Spec (.of Qbar) ⟶ A.X.left := (Additive.toMul (0 : PtQ L A)).left
  have hu : (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    (Category.comp_id _).symm.trans
      (Over.w (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)))
  have hx0 : x0 = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ (η[A.X]).left := by
    show (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left ≫
      (η[A.X]).left = _
    rw [hu]
    rfl
  have hx0w : x0 ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    Over.w (Additive.toMul (0 : PtQ L A))
  have hηw : (η[A.X]).left ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  have hf0 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      x0 ≫ F = x0 := by
    have := hf 0
    rw [map_zero] at this
    exact this.symm
  have hpt : x0 ≫ F = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
      Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    apply spec_aut_cancel (act σ)
    rw [hf0, reassoc_of% hR1]
    exact hx0
  -- Step 1: `F` lies over `Spec τ`
  have hFover : F ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) := by
    apply hom_spec_eq_of_point _ _ x0
    rw [reassoc_of% hpt, hηw, reassoc_of% hx0w]
    erw [Category.comp_id]
  -- `F(0) = 0`, twisted
  have hF0 : (η[A.X]).left ≫ F = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap L Qbar))
      (algebraMap L Qbar).injective
    refine ext_of_isDominant_of_isSeparated (X := Spec (.of L)) A.X.hom ?_
      (Spec.map (CommRingCat.ofHom (algebraMap L Qbar))) ?_
    · simp only [Category.assoc]
      rw [hFover, reassoc_of% hηw, hηw]
      erw [Category.comp_id]
    · calc _ = x0 ≫ F := by rw [hx0, Category.assoc]
        _ = _ := hpt
  -- Step 2: the conjugate model
  let ℬ := (Over.pullback (tSpec σ hσ1)).mapGrp.obj 𝒜
  haveI hℬ : PkgI2.IsAbelianScheme ℬ :=
    ⟨show IsProper (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show Smooth (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show GeometricallyConnected (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance⟩
  -- Step 3: the generic morphism and I2-NMP
  let E : pullback 𝒜.X.hom (jSpec L v) ⟶ A.X.left := e.hom.hom.hom.left
  let Ei : A.X.left ⟶ pullback 𝒜.X.hom (jSpec L v) := e.inv.hom.hom.left
  have hEi : Ei ≫ E = 𝟙 _ := congrArg (fun m => m.hom.hom.left) e.inv_hom_id
  have hEw : E ≫ A.X.hom = pullback.snd 𝒜.X.hom (jSpec L v) := Over.w e.hom.hom.hom
  have hEiw : Ei ≫ pullback.snd 𝒜.X.hom (jSpec L v) = A.X.hom := Over.w e.inv.hom.hom
  have c1 : (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v)) ≫ 𝒜.X.hom =
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) ≫ tSpec σ hσ1 := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hEiw, reassoc_of% hFover, reassoc_of% hEw, hR2]
  let inner : pullback 𝒜.X.hom (jSpec L v) ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) :=
    pullback.lift (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v))
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) c1
  let φl : pullback 𝒜.X.hom (jSpec L v) ⟶
      pullback (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) :=
    pullback.lift inner (pullback.snd 𝒜.X.hom (jSpec L v)) (pullback.lift_snd _ _ _)
  let φ : (Over.pullback (jSpec L v)).obj 𝒜.X ⟶ (Over.pullback (jSpec L v)).obj ℬ.X :=
    Over.homMk φl (pullback.lift_snd _ _ _)
  obtain ⟨G, hG⟩ := (hN L (Ow L v) 𝒜 ℬ).2 φ
  have hG' : (Over.pullback (jSpec L v)).map G = φ := hG
  let Gl : 𝒜.X.left ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) := G.left
  let Ft : 𝒜.X.left ⟶ 𝒜.X.left := Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)
  have hGl : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl =
      φl ≫ pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) := by
    have h1 : ((Over.pullback (jSpec L v)).map G).left ≫
        pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) =
        pullback.fst 𝒜.X.hom (jSpec L v) ≫ G.left := pullback.lift_fst _ _ _
    have h2 : ((Over.pullback (jSpec L v)).map G).left = φl := congrArg (fun m => m.left) hG'
    rw [← h2]
    exact h1.symm
  have hfst : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    show pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1) = _
    rw [← Category.assoc (pullback.fst 𝒜.X.hom (jSpec L v)), hGl, Category.assoc φl]
    simp only [φl, inner, pullback.lift_fst_assoc, pullback.lift_fst]
  have hC3 : Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [hfst, ← Category.assoc Ei E, hEi, Category.id_comp]
  have hGw : Gl ≫ pullback.snd 𝒜.X.hom (tSpec σ hσ1) = 𝒜.X.hom := Over.w G
  have hC1 : Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ tSpec σ hσ1 := by
    show (Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)) ≫ 𝒜.X.hom = _
    rw [Category.assoc, pullback.condition, reassoc_of% hGw]
  refine ⟨Ft, hC1, ?_, hC3⟩
  -- Step 4: the unit section
  have hηO : (η[𝒜.X]).left ≫ 𝒜.X.hom = 𝟙 _ := Over.w η[𝒜.X]
  have hηL : jSpec L v ≫ (η[𝒜.X]).left =
      (η[A.X]).left ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [← pb_eta_fst (jSpec L v) 𝒜, ← Category.assoc]
    congr 1
    have h1 : η[A.X] ≫ e.inv.hom.hom = η[((Over.pullback (jSpec L v)).mapGrp.obj 𝒜).X] :=
      IsMonHom.one_hom _
    exact (congrArg (fun m => m.left) h1).symm
  haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap (Ow L v) L))
    (Subtype.val_injective)
  refine ext_of_isDominant_of_isSeparated (X := Spec (.of (Ow L v))) 𝒜.X.hom ?_ (jSpec L v) ?_
  · simp only [Category.assoc]
    rw [hC1, reassoc_of% hηO, hηO]
    erw [Category.comp_id]
  · rw [reassoc_of% hηL, hC3, reassoc_of% hF0, reassoc_of% hR2, hηL]

/-- **`FExtendCore` from I2-NMP (proved).** -/
theorem fExtendCore_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendCore :=
  fExtendCore_of_gen (fExtendGen_of_nmp hN)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the kernel leaves I2-Red, I2-NMP (proved).** alg-frob-red's two glue
Props are discharged: `AbsFrob` (`absFrob`, Mathlib only) and `FExtendGen` (`fExtendGen_of_nmp`). -/
theorem algFrobRed_of_nmp (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG hS hRed (fExtendGen_of_nmp hN) absFrob

/-- **`TateBridge35` from I3.M0, the two leaf candidates and I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_nmp (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : G14Bridge.TateBridge35 :=
  tateBridge35_of_gen hT hG hS hRed (fExtendGen_of_nmp hN) absFrob

end AlgFrobRedRed



/-! # frob-pieces: `GoodRedCofinite` from spreading out (task frob-pieces)

Appended (by `scratch/frob-pieces/build.sh`) to a verbatim copy of
`scratch/alg-frob-red/AlgFrobRed.lean`. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AbSchemeSpreadsOut` (LEAF candidate, published: spreading out an abelian variety to an
abelian scheme).** An abelian variety `A` over a number field `L ⊆ ℚ̄` extends to an abelian
scheme (I2's `IsAbelianScheme`: a group object, proper, smooth, geometrically connected) over a
finitely generated subring `R = ℤ[s] ⊆ L`, with generic fibre isomorphic to `A` as a group object.
Source: `L = colim R` over finitely generated subrings; the scheme, group law and axioms descend to
some `R` (EGA IV₃ 8.8.2), as do properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8);
geometric connectedness of the fibres holds after shrinking `R` to a normal ring with fraction
field `L`, e.g. `𝓞_L[1/N]` (finitely generated: an integral basis and `1/N`), by Zariski's
connectedness theorem (EGA III₁ 4.3; this is `FrobPiecesNeron.ProperSmoothGenConnected`), or
over a nonempty open of `Spec R` (EGA IV₃ 9.7.7, with a generic-point argument). Locators UNVERIFIED. Same input as
neron-lg's glue N1-g1 `AbVarSpreadsOut`, plus geometric connectedness of the fibres. -/
def AbSchemeSpreadsOut : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ (s : Finset L) (𝒜 : Grp (Over (Spec (.of (Subring.closure (s : Set L)))))),
      PkgI2.IsAbelianScheme 𝒜 ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (Subring.closure (s : Set L)) L)))).mapGrp.obj 𝒜 ≅ ObjBridge.toGrp A)

/-- A nonzero integer prime to `p` is a unit in `O_w` for `w ∣ p`. -/
theorem isUnit_intCast_of_coprime {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) {y : ℤ}
    (hpy : ¬ p ∣ y.natAbs) : IsUnit (y : Ow L v) := by
  by_contra hnu
  have hym : (y : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  have hcop : IsCoprime (p : ℤ) y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hp).2 hpy
    simpa [Int.gcd] using this
  obtain ⟨u, w, huw⟩ := hcop
  have h1 : ((u * p + w * y : ℤ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hym)
  rw [huw, Int.cast_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Base change of a group object along equal morphisms. -/
theorem pullbackGrp_congr {X Y : Scheme} {f f' : X ⟶ Y} (h : f = f') (𝒜 : Grp (Over Y)) :
    Nonempty ((Over.pullback f).mapGrp.obj 𝒜 ≅ (Over.pullback f').mapGrp.obj 𝒜) := by
  subst h; exact ⟨Iso.refl _⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from `AbSchemeSpreadsOut` (proved).** Let `𝒜/ℤ[s]` spread out `A`, and
`y ≠ 0` an integer with `y·a` integral for every `a ∈ s` (`exists_integral_multiples`). For a prime
`p ∤ y` and `w ∣ p`, `y` is a unit and integral elements lie in the valuation ring `O_w`, so
`ℤ[s] ⊆ O_w`; the base change of `𝒜` to `O_w` is an abelian scheme (base-change stability) whose
generic fibre is that of `𝒜` (`Over.pullbackComp`, `Functor.mapGrpNatIso`). -/
theorem goodRedCofinite_of (h : AbSchemeSpreadsOut) : GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨s, 𝒜, h𝒜, ⟨e⟩⟩ := h L A
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpy : ¬ p ∣ y.natAbs := fun hd =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, hd, Int.natAbs_ne_zero.2 hy0⟩)
  obtain ⟨u, hu⟩ := isUnit_intCast_of_coprime (L := L) hp hv hpy
  have hinv : (y : L)⁻¹ ∈ Ow L v := by
    have h2 : ((u⁻¹ : (Ow L v)ˣ) : Ow L v) * (y : Ow L v) = 1 := by rw [← hu]; exact u.inv_mul
    have h3 : (((u⁻¹ : (Ow L v)ˣ) : Ow L v) : L) * (y : L) = 1 := by
      have := congrArg (fun z : Ow L v => (z : L)) h2
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left h3]
    exact ((u⁻¹ : (Ow L v)ˣ) : Ow L v).2
  have hmem : ∀ a ∈ s, a ∈ Ow L v := by
    intro a ha
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (show IsIntegral (Ow L v) (y • a) from (hyint a ha).tower_top)
    have hyL : (y : L) ≠ 0 := by exact_mod_cast hy0
    have ha' : a = (y : L)⁻¹ * (y • a) := by
      rw [zsmul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ hyL, _root_.one_mul]
    rw [ha', ← hb]
    exact mul_mem hinv b.2
  have hle : Subring.closure (s : Set L) ≤ (Ow L v).toSubring :=
    Subring.closure_le.2 (fun a ha => hmem a ha)
  let φ : Subring.closure (s : Set L) →+* Ow L v := Subring.inclusion hle
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap (Subring.closure (s : Set L)) L)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫ ?_⟩
    exact (pullbackGrp_congr hcomp 𝒜).some ≪≫ e

end FrobPiecesGood

end



/-! # frob-pieces: `GoodRedCofinite` from neron-lg's glue N1-g1 `AbVarSpreadsOut` and Zariski's
connectedness theorem (task frob-pieces)

`HasAbelianSchemeAway` and `AbVarSpreadsOut` below are verbatim copies (docstring and `def`) of
the declarations of the same names in `scratch/neron-lg/NeronLG.lean` (namespace
`ZInQ.NeronLG`), under the same `open`s (checked by `scratch/frob-pieces/py/verbatim_check.py`). -/

noncomputable section

namespace FrobPiecesNeron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI3 (AbVar)
open scoped Obj

/-- `B` extends to an abelian scheme over `𝓞_L[1/f]`: a smooth proper group scheme whose generic
fibre is identified with `B` as a group scheme (over every presentation of `𝓞_L[1/f]`). -/
def HasAbelianSchemeAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L],
    ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom

/-- **Glue N1-g1 (spreading out an abelian variety).** An abelian variety `B` over a number field
`L` extends to an abelian scheme over `𝓞_L[1/f]` for some nonzero `f ∈ 𝓞_L`. Textbook (a
candidate for a textbook leaf): `L = colim 𝓞_L[1/f]`, so `B`, its group law, unit and inverse
and the group axioms (equalities of morphisms) descend to some `𝓞_L[1/f]` (EGA IV₃ 8.8.2), as do
properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8 (ii)); all locators UNVERIFIED.
Mathlib v4.35 has the descent of morphisms for affine transition maps
(`AlgebraicGeometry/.../AffineTransitionLimit.lean`, EGA IV 8.8.2) but not the descent of schemes
or of properness and smoothness. -/
def AbVarSpreadsOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), ∃ f : 𝓞 L, f ≠ 0 ∧ HasAbelianSchemeAway L B f

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ProperSmoothGenConnected` (LEAF candidate, published: Zariski's connectedness theorem).**
A smooth proper scheme `X` over `R = 𝓞_L[1/f]` (any presentation) whose generic fibre is
geometrically connected is geometrically connected over `R`. Proof (STANDARD): `R ≅ 𝓞_L[1/f]`
is normal with fraction field `L` (the case `f = 0` is vacuous: no ring map from the zero ring to
`L`), and `X_L` is geometrically reduced (smooth) and geometrically connected and proper, so
`H⁰(X_L, 𝒪) = L`; `f_*𝒪_X` is a finite `R`-algebra, torsion-free since `X` is flat (smooth), so
it lies inside `H⁰(X_L, 𝒪) = L` and is integral over the normal `R`, hence
`f_*𝒪_X = 𝒪_{Spec R}`; then all fibres of the proper `f` are geometrically connected (Zariski's
connectedness theorem, EGA III₁ 4.3.1–4.3.4; locators UNVERIFIED). The fibres are nonempty since
`X → Spec R` is open (smooth), closed (proper), `X ≠ ∅` and `Spec R` is connected. Not in Mathlib
v4.35 (no Stein factorization). -/
def ProperSmoothGenConnected : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (f : 𝓞 L) (R : Type) [CommRing R] [Algebra (𝓞 L) R]
    [IsLocalization.Away f R] [Algebra R L] [IsScalarTower (𝓞 L) R L]
    (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProper X.hom →
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj X).hom →
    GeometricallyConnected X.hom

/-- Geometrically integral implies geometrically connected. -/
theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{0}} (g : X ⟶ Y)
    [GeometricallyIntegral g] : GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

/-- `A` has good reduction at `O` if an abelian scheme over a ring `R` mapping to `O` (compatibly
with the maps to `K`) has generic fibre `≅ A`: base change along `Spec O → Spec R`. -/
theorem hasGoodReduction_of_base {K : Type} [Field K] (O : ValuationSubring K) {R : Type}
    [CommRing R] (ιR : R →+* K) (φ : R →+* O) (hφ : (algebraMap O K).comp φ = ιR)
    (A : Grp (Over (Spec (.of K)))) (𝒜 : Grp (Over (Spec (.of R))))
    (h𝒜 : PkgI2.IsAbelianScheme 𝒜)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom ιR))).mapGrp.obj 𝒜 ≅ A) :
    PkgI2.HasGoodReduction A O := by
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g =
        Spec.map (CommRingCat.ofHom ιR) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ]
    exact ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫
      (FrobPiecesGood.pullbackGrp_congr hcomp 𝒜).some ≪≫ e⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from neron-lg's N1-g1 `AbVarSpreadsOut` and `ProperSmoothGenConnected`
(proved).** Spread `A` out to `G/𝓞_L[1/f]` (presentation `Localization.Away f`); `G` is
geometrically connected by `ProperSmoothGenConnected` (its generic fibre is `≅ A`, geometrically
integral). `S` is the set of prime factors of `N = |N_{L/ℚ}(f)|`: for `p ∉ S` and `w ∣ p`, `N` is a
unit of `O_w` and `N ∈ (f)`, so `f` is a unit of `O_w`, and `𝓞_L[1/f] → L` factors through `O_w`
(`IsLocalization.Away.lift`); conclude by base change (`hasGoodReduction_of_base`). -/
theorem goodRedCofinite_of_neron (hsp : AbVarSpreadsOut) (hc : ProperSmoothGenConnected) :
    AlgFrobRedRed.GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨f, hf0, hf⟩ := hsp L A
  have hfL : IsUnit (algebraMap (𝓞 L) L f) :=
    isUnit_iff_ne_zero.2 (by simpa using hf0)
  let R := Localization.Away f
  letI : Algebra R L := (IsLocalization.Away.lift f hfL).toAlgebra
  haveI : IsScalarTower (𝓞 L) R L := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.Away.lift_eq f hfL x).symm)
  obtain ⟨G, hG, hGs, hGp, gen, hgen⟩ := hf R
  have hgc : GeometricallyConnected G.hom := by
    refine hc L f R G hGs hGp ?_
    have h1 : GeometricallyConnected A.X.hom := geometricallyConnected_of_geometricallyIntegral _
    have h2 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G).hom =
        gen.hom.left ≫ A.X.hom := (Over.w gen.hom).symm
    rw [h2]
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0})
      gen.hom.left A.X.hom).2 h1
  let N : ℕ := Ideal.absNorm (Ideal.span {f})
  have hN0 : N ≠ 0 := by
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hf0
  refine ⟨N.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpN : ¬ p ∣ (N : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    exact fun hd => hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hN0⟩)
  have hNu : IsUnit ((N : ℤ) : AlgFrobRedRed.Ow L v) :=
    FrobPiecesGood.isUnit_intCast_of_coprime (L := L) hp hv hpN
  have hfu : IsUnit (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f) := by
    by_contra hnu
    have hfm : AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f ∈
        IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {f}))
    have : ((N : ℤ) : AlgFrobRedRed.Ow L v) ∈ IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := by
      have := congrArg (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v)) hc'
      rw [map_mul, map_natCast] at this
      rw [Int.cast_natCast, ← this]
      exact Ideal.mul_mem_left _ _ hfm
    exact (IsLocalRing.mem_maximalIdeal _).1 this hNu
  let φ : R →+* AlgFrobRedRed.Ow L v := IsLocalization.Away.lift f hfu
  have hφ : (algebraMap (AlgFrobRedRed.Ow L v) L).comp φ = algebraMap R L := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift_eq]
    exact (IsLocalization.Away.lift_eq f hfL x).symm
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
    Functor.grpObjObj
  exact hasGoodReduction_of_base _ (algebraMap R L) φ hφ _ (Grp.mk G) ⟨hGp, hGs, hgc⟩
    (Grp.mkIso' gen)

end FrobPiecesNeron

end



/-! # frob-pieces: `AlgFrobRed` with `SmoothGeomConnIntegral` discharged and `GoodRedCofinite`
replaced by `AbSchemeSpreadsOut` -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **alg-frob-red's `SmoothGeomConnIntegral`, proved** (it is definitionally the verbatim copy
`FrobPieces.SmoothGeomConnIntegral` of `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean`,
proved there from the vendored Tau Ceti theorem `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). -/
theorem smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral :=
  FrobPieces.smoothGeomConnIntegral

/-- **`AlgFrobRed` from `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_spread (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hE hA

/-- **`AlgFrobRed` from `GoodRedCofinite`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_four (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG smoothGeomConnIntegral hRed hE hA

/-- **`TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob`
(proved).** -/
theorem tateBridge35_of_spread (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread hG hRed hE hA)

/-- **`AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`,
I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_neron (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral hRed
    hE hA

/-- **`TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, `FExtendGen`,
`AbsFrob` (proved).** -/
theorem tateBridge35_of_neron (hT : PkgI3.TateModuleFree) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron hsp hc hRed hE hA)

end FrobPiecesGood

end




/-! # frob-pieces: the combined form with afr-absfrob's `AbsFrob` and `FExtendGen`

Appended by `build_full.sh` after afr-absfrob's assembled `AfrAbsFrob.lean` (verbatim copy, which
begins with alg-frob-red's `AlgFrobRed.lean`) and this task's parts. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`FrobTrace.AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, the leaf candidate
`ProperSmoothGenConnected` and the kernel leaves I2-Red, I2-NMP (proved).** -/
theorem algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral
    hRed hN

/-- **`FrobTrace.AlgFrobRed` from `AbSchemeSpreadsOut` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_spread_nmp (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hN

/-- **`FrobTrace.AlgFrobRed` from `GoodRedCofinite` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp hG smoothGeomConnIntegral hRed hN

/-- **`G14Bridge.TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, I2-NMP
(proved).** -/
theorem tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron_nmp hsp hc hRed hN)

/-- **`G14Bridge.TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_spread_nmp (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread_nmp hG hRed hN)

end FrobPiecesGood

end



/-! # linked-frob: linked-tate's glue `UnramTate.LinkedFrob`, reduced to frob-trace's `AlgFrobLink`

`UnramTate.LinkedFrob` (scratch/linked-tate/parts/97_linkeddata.lean, compiled above, unchanged) asks
g14-trace's `FrobTraceLink` for the canonical operators `tmOf … ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at
`ℓ = 5, 3`. frob-trace's `AlgFrobLink` (copied above, verbatim) gives, outside a finite set `S` of
primes, at every arithmetic Frobenius `τ` above `p ∉ S` and for every `g` (here `g = h`), one abelian
variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)`, `N ≠ 0` and, for every `ℓ ≠ p`, a
`ℚ_ℓ`-isomorphism carrying `N·V_ℓ(m_{gτg⁻¹})` to `V_ℓ(α')`. frob-trace's `frobCompare_opV_conjE`
turns that into the kernel's `FrobCompare` for `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)`, which is `tmOf … ℓ τ`.
The set is `S ∪ {3, 5}`, so that `ℓ ≠ p` at `ℓ = 3, 5`. -/

section LinkedFrobSec

noncomputable section

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

namespace LinkedFrobRed

/-- `tmOf … ℓ τ` is `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)` (definitional). -/
theorem tmOf_eq {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (ℓ : ℕ) [Fact ℓ.Prime] (τ : PkgI4.GQ) :
    tmOf hLL' A Θ h m ℓ τ =
      opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m (h * τ * h⁻¹))) :=
  rfl

/-- **`LinkedFrob` from frob-trace's `AlgFrobLink` (proved).** Only three of the descent-datum
clauses are used (`m_σ` is the Galois action on `G_L`, the coset rule, algebraicity `F_σ`). -/
theorem linkedFrob_of_algFrobLink (hF : FrobTrace.AlgFrobLink) : UnramTate.LinkedFrob := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨S, hS⟩ := hF L A m h3 h4 h8
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  refine ⟨k, inferInstance, hk, Ab, α, N', hN', ?_, ?_⟩
  · rw [tmOf_eq]
    exact FrobTrace.frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3
  · rw [tmOf_eq]
    exact FrobTrace.frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5

/-- **`LinkedFrob` from frob-trace's `AlgFrobRed` (proved):** frob-trace's
`AlgFrobRed → AlgFrobOne → AlgFrobLink`. -/
theorem linkedFrob_of_algFrobRed (hR : FrobTrace.AlgFrobRed) : UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobLink (FrobTrace.algFrobLink_of_one (FrobTrace.algFrobOne_of_red hR))

end LinkedFrobRed

end

end LinkedFrobSec

/-! # linked-frob: `LinkedFrob` from the frob chain, and `GluePieces4`

`GluePieces4` is linked-tate's `GluePieces3` (scratch/linked-tate/parts/99_bundle3.lean; all fields
copied verbatim with their docstrings) with the field `linkedFrob` replaced by frob-pieces'
`AbVarSpreadsOut` (neron-lg's N1-g1) and `ProperSmoothGenConnected`; I2-NMP and I2-Red are the
textbook leaves `t.t3`, `t.t4` of the bundle. -/

section LinkedFrobBundleSec

noncomputable section

namespace LinkedFrobRed

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`LinkedFrob` from alg-frob-red's five inputs (proved).** -/
theorem linkedFrob_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (algFrobRed_of_gen hG hS hRed hE hA)

/-- **`LinkedFrob` from `GoodRedCofinite`, I2-Red and I2-NMP (proved;** frob-pieces' and
afr-absfrob's discharge of `SmoothGeomConnIntegral`, `FExtendGen`, `AbsFrob`). -/
theorem linkedFrob_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (FrobPiecesGood.algFrobRed_of_goodRed_nmp hG hRed hN)

/-- **`LinkedFrob` from N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`, I2-Red and I2-NMP
(proved).** -/
theorem linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (FrobPiecesGood.algFrobRed_of_neron_nmp hsp hc hRed hN)


end LinkedFrobRed

end

end LinkedFrobBundleSec


end  -- assemble-port: closes an unclosed `noncomputable section` of the copied files

end  -- assemble-port: closes an unclosed `noncomputable section` of the copied files

