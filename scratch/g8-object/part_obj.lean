
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
