/-! ## g0-assemble2: unram-tate (scratch/unram-tate/TateBridge.lean lines 1038-1942, verbatim; lines 1-1036 are
g0-mod-field's ModField.lean, i.e. part 75) -/

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
