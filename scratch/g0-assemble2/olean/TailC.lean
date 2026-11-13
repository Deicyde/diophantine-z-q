import TailB

section G0A2_a45_unramtate
/-! ## g0-assemble2: unram-tate (scratch/unram-tate/TateBridge.lean lines 1038-1942, verbatim; lines 1-1036 are
g0-mod-field's ModField.lean, i.e. part 75) -/
-- (g0-assemble2) the file-level `open`s of ModField.lean (part 75), which TateBridge.lean inherits:
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q


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

end G0A2_a45_unramtate

section G0A2_a50_x1dirichlet
/-! ## g0-assemble2: x1-dirichlet (scratch/x1-dirichlet/Dirichlet.lean lines 2-184 verbatim) -/

/-!
# x1-dirichlet: the glue Prop `DirichletOfFinite` from T17 (`KroneckerWeberCyclic`)

`DirichletOfFinite` is copied verbatim from `scratch/g0-mod-newform/part_new.lean` (lines
727-738; there in namespace `G0ModNewform`, with `open PkgI4 (Qbar GQ LiesOver IsArithFrob …
GaloisChar)`). It is proved here from the leaf T17 in its narrowed form
`TSkolemKW.KW.KroneckerWeberCyclic` (the bundle's field `t17`) and the kernel's proved C8 glue
`TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic`
(`ZInQKernel/HDecomp/Textbook/KroneckerWeberUse.lean`).

New glue proved here:
* `isOpen_ker` (continuity + finite image ⇒ open kernel, through the kernel's
  `isOpen_ker_of_continuous`);
* `exists_preimage_of_pow_eq_one`: roots of unity of `ℚ̄_ℓ` lie in `ιL(ℚ̄)`;
* `cycChar_frob`: an arithmetic Frobenius at a place above `p ∤ m` has mod-`m` cyclotomic
  character `p` (the `m`-th roots of unity are distinct modulo the place, via
  `∑_{i<m} η^i = 0` for an `m`-th root of unity `η ≠ 1`);
* `dirichletOfFinite_of_kroneckerWeberCyclic : KroneckerWeberCyclic → DirichletOfFinite`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace X1Dirichlet

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisChar)
open TSkolemKW.KW hiding Qbar GQ

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

/-! ## §1. Roots of unity of `ℚ̄_ℓ` come from `ℚ̄` -/

theorem exists_preimage_of_pow_eq_one {E : Type*} [Field E] [Algebra ℚ E] (ι : Qbar →ₐ[ℚ] E)
    (N : ℕ+) (z : E) (hz : z ^ (N : ℕ) = 1) : ∃ β : Qbar, ι β = z := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_qbar N
  have h : IsPrimitiveRoot (ι ζ) (N : ℕ) := hζ.map_of_injective (RingHom.injective ι.toRingHom)
  obtain ⟨i, -, hi⟩ := h.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/-! ## §2. Arithmetic Frobenius on roots of unity -/

/-- Roots of unity have valuation `1` at every place. -/
theorem valuation_eq_one_of_pow (v : ValuationSubring Qbar) {n : ℕ} (hn : n ≠ 0) {x : Qbar}
    (hx : x ^ n = 1) : v.valuation x = 1 := by
  have h := congrArg v.valuation hx
  rw [map_pow, map_one] at h
  exact (pow_eq_one_iff_of_nonneg zero_le hn).1 h

/-- **An arithmetic Frobenius at a place above `p ∤ m` has mod-`m` cyclotomic character `p`.** -/
theorem cycChar_frob (m : ℕ+) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ (m : ℕ))
    (v : ValuationSubring Qbar) (τ : GQ) (hv : LiesOver v p) (hτ : IsArithFrob τ v p) :
    ((cycChar m τ : (ZMod m)ˣ) : ZMod m) = (p : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_qbar m
  have hm0 : (m : ℕ) ≠ 0 := m.ne_zero
  have hζm : ζ ^ (m : ℕ) = 1 := hζ.pow_eq_one
  set a := ((cycChar m τ : (ZMod m)ˣ) : ZMod m).val with ha
  have hτζ : τ ζ = ζ ^ a := cycChar_spec m τ ζ hζm
  have hζval : v.valuation ζ = 1 := valuation_eq_one_of_pow v hm0 hζm
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).1 hζval.le
  have hdiff : v.valuation (ζ ^ a - ζ ^ p) < 1 := by
    have := hτ.2 ζ hζv
    rw [hτζ] at this
    exact (v.mem_nonunits_iff).1 this
  have hpv : v.valuation (p : Qbar) < 1 := (v.mem_nonunits_iff).1 hv
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have heq : ζ ^ a = ζ ^ p := by
    by_contra hne
    set η := ζ ^ a / ζ ^ p with hηdef
    have hη1 : η ≠ 1 := fun h => hne ((div_eq_one_iff_eq (pow_ne_zero _ hζ0)).1 h)
    have hηm : η ^ (m : ℕ) = 1 := by
      rw [hηdef, div_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm p, pow_mul, pow_mul, hζm,
        one_pow, one_pow, div_one]
    have hηval : v.valuation η = 1 := valuation_eq_one_of_pow v hm0 hηm
    have hηv : v.valuation (η - 1) < 1 := by
      have : η - 1 = (ζ ^ a - ζ ^ p) / ζ ^ p := by
        rw [sub_div, div_self (pow_ne_zero _ hζ0)]
      rw [this, map_div₀, map_pow, hζval, one_pow, div_one]
      exact hdiff
    have hsum : ∑ i ∈ Finset.range (m : ℕ), η ^ i = 0 := by
      rw [geom_sum_eq hη1, hηm, sub_self, zero_div]
    have hmv : v.valuation ((m : ℕ) : Qbar) < 1 := by
      have : ((m : ℕ) : Qbar) = ∑ i ∈ Finset.range (m : ℕ), (1 - η ^ i) := by
        rw [Finset.sum_sub_distrib, hsum, sub_zero]
        simp
      rw [this]
      apply Valuation.map_sum_lt _ one_ne_zero
      intro i _
      have h1 : 1 - η ^ i = -((η - 1) * ∑ j ∈ Finset.range i, η ^ j) := by
        rw [mul_comm, geom_sum_mul]
        ring
      rw [h1, Valuation.map_neg, map_mul]
      have hs : v.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        Valuation.map_sum_le _ (fun j _ => by rw [map_pow, hηval, one_pow])
      exact (mul_le_of_le_one_right' hs).trans_lt hηv
    -- `p` and `m` are coprime, but both lie in the maximal ideal of `v`
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    have h1 : ((p : ℤ) * Nat.gcdA p m + ((m : ℕ) : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hcop]
      rfl
    have hint : ∀ k : ℤ, v.valuation (k : Qbar) ≤ 1 := fun k =>
      (v.valuation_le_one_iff _).2 (intCast_mem v k)
    have hlt : v.valuation
        ((((p : ℤ) * Nat.gcdA p m + ((m : ℕ) : ℤ) * Nat.gcdB p m : ℤ)) : Qbar) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hpv (hint _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hmv (hint _)
    rw [h1, Int.cast_one, map_one] at hlt
    exact lt_irrefl _ hlt
  -- `ζ^a = ζ^p` with `ζ` primitive gives `a ≡ p (mod m)`
  have hmod : (a : ZMod m) = (p : ZMod m) := by
    rcases le_total p a with h | h
    · have hd : ζ ^ (a - p) = 1 := by
        have : ζ ^ (a - p) * ζ ^ p = 1 * ζ ^ p := by
          rw [← pow_add, Nat.sub_add_cancel h, one_mul, heq]
        exact mul_right_cancel₀ (pow_ne_zero _ hζ0) this
      have := (hζ.pow_eq_one_iff_dvd _).1 hd
      exact ((ZMod.natCast_eq_natCast_iff p a m).2 ((Nat.modEq_iff_dvd' h).2 this)).symm
    · have hd : ζ ^ (p - a) = 1 := by
        have : ζ ^ (p - a) * ζ ^ a = 1 * ζ ^ a := by
          rw [← pow_add, Nat.sub_add_cancel h, one_mul, heq]
        exact mul_right_cancel₀ (pow_ne_zero _ hζ0) this
      have := (hζ.pow_eq_one_iff_dvd _).1 hd
      exact (ZMod.natCast_eq_natCast_iff a p m).2 ((Nat.modEq_iff_dvd' h).2 this)
  rw [← hmod, ha, ZMod.natCast_zmod_val]

/-! ## §3. `DirichletOfFinite` -/

/-- **`DirichletOfFinite` (GLUE, proved from the leaf T17 in its cyclic form).** -/
theorem dirichletOfFinite_of_kroneckerWeberCyclic (hKW : KroneckerWeberCyclic) :
    DirichletOfFinite := by
  intro ℓ _ ψ hfin ιC ιL
  have hopen : IsOpen (ψ.toHom.ker : Set GQ) :=
    isOpen_ker_of_continuous ψ.toHom ψ.continuous_toHom hfin
  obtain ⟨m, χ, hχ⟩ := dirichletCharacter_of_kroneckerWeberCyclic hKW ψ.toHom hopen
  -- the values of `χ` on units are roots of unity of order dividing `N = #(ℤ/m)ˣ`
  let N : ℕ+ := ⟨Fintype.card (ZMod m)ˣ, Fintype.card_pos⟩
  have hpow : ∀ u : (ZMod m)ˣ, (χ u) ^ (N : ℕ) = 1 := by
    intro u
    have h1 : u ^ (N : ℕ) = 1 := pow_card_eq_one
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  choose β hβ using fun u : (ZMod m)ˣ => exists_preimage_of_pow_eq_one ιL N (χ u) (hpow u)
  have hβ0 : ∀ u, β u ≠ 0 := by
    intro u h
    have := hβ u
    rw [h, map_zero, ← MulChar.coe_toUnitHom] at this
    exact (χ.toUnitHom u).ne_zero this.symm
  have hinj : Function.Injective ιL := RingHom.injective ιL.toRingHom
  let χQ : (ZMod m)ˣ →* Qbarˣ :=
    { toFun := fun u => Units.mk0 (β u) (hβ0 u)
      map_one' := Units.ext (hinj (by simp [hβ]))
      map_mul' := fun u w => Units.ext (hinj (by simp [hβ, map_mul])) }
  let ψD : DirichletCharacter ℂ (m : ℕ) :=
    MulChar.ofUnitHom ((Units.map (ιC : Qbar →* ℂ)).comp χQ)
  refine ⟨m, ψD, (m : ℕ).primeFactors, m.pos, fun p hp hpS => ?_⟩
  have hpm : ¬ p ∣ (m : ℕ) := fun h =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, h, m.ne_zero⟩)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime p hcop
  have hu : ((u : (ZMod m)ˣ) : ZMod m) = (p : ZMod m) := ZMod.coe_unitOfCoprime p hcop
  refine ⟨β u, ?_, fun v τ hv hτ => ?_⟩
  · rw [← hu, MulChar.ofUnitHom_coe]
    rfl
  · rw [hχ τ, hβ u, cycChar_frob m p hp hpm v τ hv hτ, ← hu]

end X1Dirichlet

end

namespace G0ModNewform
/-- (x1-dirichlet) the two verbatim copies agree. -/
theorem dirichletOfFinite_copy : G0ModNewform.DirichletOfFinite ↔ X1Dirichlet.DirichletOfFinite :=
  Iff.rfl
/-- (x1-dirichlet) `DirichletOfFinite` from T17 (`TextbookLeaves.t17`). -/
theorem dirichletOfFinite_of_t17 (hKW : TSkolemKW.KW.KroneckerWeberCyclic) : DirichletOfFinite :=
  X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic hKW
end G0ModNewform

end G0A2_a50_x1dirichlet

section G0A2_a55_mobius
/-! ## g0-assemble2: mobius-glue (scratch/mobius-glue/MobiusGlue.lean), adapted to Leaves.lean after pin-apply

Changes (all mechanical): (1) its §0 copies of `QMFamily`, `IsFibreOf`, `R1famProps`,
`R1univProps` (lines 47-79, 89-100) are not repeated: pin-apply put the same text into Leaves.lean
(`LeafQM.AV.*`), which the names resolve to; (2) its copy of `MobiusGlue` (stated with
`R1fpPropsU`) is renamed `MobiusGlueU` throughout, because Leaves.lean's `LeafQM.AV.Pin.MobiusGlue`
is stated with the repaired `R1fpProps` (the same six clauses, associated differently);
`mobiusGlue_of_U` below converts; (3) §6 (lines 549-643, qm-pin's comparison lemmas, already in
Leaves.lean) and the two downstream corollaries at lines 1409-1434 are not repeated. -/

/-!
# mobius-glue: the `π`-half of qm-pin's comparison of two triples

Task mobius-glue (2026-11-13). See `docs/research/mobius-glue.md`.

**Main result** (`mobiusGlue_of_curves`): `LeafQM.AV.Pin.MobiusGlueU` (qm-pin §3.2, copied
verbatim from `scratch/qm-pin/QMPin.lean` together with the definitions it uses) follows from

* `CurveRatFactor` (curves): on a proper smooth curve over `ℚ`, a morphism `ρ` to `P¹` that is
  constant on the fibres of a morphism `σ` to `P¹` is a rational function of `σ` on `ℚ̄`-points;
* `CurveSurj` (curves): a morphism to `P¹` with finite fibres on `ℚ̄`-points, from a proper
  smooth curve over `ℚ` with a `ℚ̄`-point, is onto `P¹(ℚ̄)`;
* `ObjBridge.TorsionStructure` (the decomposition's textbook leaf T5, `A(K̄)[n] ≅ (ℤ/n)^{2g}`).

Contents.
* §0 the qm-pin definitions (verbatim).
* §1 an injective rational function on an algebraically closed field of characteristic 0 has
  degree at most one (`Mob.natDegree_le_one_of_injective`, Wronskian argument); one of degree at
  most one without finite pole fixing `0` and `c ≠ 0` is the identity (`Mob.ratEval_eq_self`).
* §2 the named facts; §3 `mobiusGlue_of_curveFacts` (from the curve facts and
  `TwistClassFinite`).
* §4 `TwistClassFinite` from T5 and `AutOInnerFinite` (finitely many level structures per pair via
  the kernel's `Level3.torsor`; transport of level structures; twists by conjugate automorphisms).
* §5-§6 the combined statements and the downstream comparison/transfer (qm-pin §4 copied).
* §7 `AutOInnerFinite` from Skolem–Noether (the kernel's `TSkolemKW.leafSkolemNoether`, through
  an explicit extension of `α ∈ Aut 𝒪` to `B`) and `NormalizerFinite`.
* §8 `NormalizerFinite` proved (`N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`, descent on the reduced norm), hence
  `autOInnerFinite`, `twistClassFinite`, `mobiusGlue_of_curves`, `sameTripleMor_of_curves`,
  `pointwise_of_witness_curves`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3


/-- **R1fp, repaired clause list** (to replace `LeafQM.AV.R1fpProps`): the four old clauses and
`R1famProps`. -/
def R1fpPropsPin (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ
/-- The fully repaired clause list: family and universal property. -/
def R1fpPropsU (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  R1fpPropsPin Y Φ ∧ R1univProps Y Φ

/-- **Glue (not compiled; argued in the report §3.4).** Given a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g`, and CM objects of the three kinds, the two morphisms `π'` and `π ∘ g` to `P¹`
agree on `ℚ̄`-points: they have the same fibres (both `R2fpProps`), so `π' = h ∘ π ∘ g` with `h`
a bijection of `P¹(ℚ̄)` which is a morphism (graph argument on each geometric component of
`Y'`), hence a Möbius map, and `h` fixes `0, ∞, −16/27`. Algebraic geometry of curves. -/
def MobiusGlueU : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) (g : Y' ⟶ Y),
    R1fpPropsU Y Φ → R2fpProps Y Φ π → R1fpPropsU Y' Φ' → R2fpProps Y' Φ' π' →
    ((∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) →
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g)) →
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

/-! ## §1 Rational functions on `P¹`: an injective one is a Möbius map -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]


open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

theorem eval_ne_zero_of_coprime {F G : K[X]} (h : IsCoprime F G) {a : K} (hG : G.eval a = 0) :
    F.eval a ≠ 0 := by
  intro hF
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Polynomial.eval a) huv
  simp [eval_add, eval_mul, hF, hG] at this

/-- The Wronskian `F' G - F G'` of a coprime pair of which one has positive degree is nonzero
(characteristic 0). -/
theorem wronskian_ne_zero [CharZero K] {F G : K[X]} (h : IsCoprime F G)
    (hdeg : F.natDegree ≠ 0 ∨ G.natDegree ≠ 0) :
    derivative F * G - F * derivative G ≠ 0 := by
  intro hW
  have hW' : derivative F * G = F * derivative G := sub_eq_zero.mp hW
  have key : ∀ {P Q : K[X]}, IsCoprime P Q → P ∣ derivative P * Q → P.natDegree = 0 := by
    intro P Q hPQ hd
    have hd' : P ∣ derivative P := hPQ.dvd_of_dvd_mul_right hd
    by_contra hP
    have hne : derivative P ≠ 0 := derivative_ne_zero.mpr hP
    have h1 := natDegree_le_of_dvd hd' hne
    have h2 := natDegree_derivative_lt hP
    omega
  have hF : F.natDegree = 0 := key h ⟨derivative G, hW'⟩
  have hG : G.natDegree = 0 := key h.symm ⟨derivative F, by rw [mul_comm, ← hW', mul_comm]⟩
  rcases hdeg with hdeg | hdeg <;> contradiction

/-- **An injective rational function has degree at most one** (algebraically closed field of
characteristic 0). -/
theorem natDegree_le_one_of_injective [IsAlgClosed K] [CharZero K] {F G : K[X]}
    (hcop : IsCoprime F G) (hinj : ∀ s t : K, ratEval F G s = ratEval F G t → s = t) :
    F.natDegree ≤ 1 ∧ G.natDegree ≤ 1 := by
  classical
  by_contra hcon
  set n := max F.natDegree G.natDegree with hn_def
  have hn : 2 ≤ n := by
    rw [not_and_or] at hcon
    rcases hcon with h | h <;> omega
  set W := derivative F * G - F * derivative G with hW_def
  have hW : W ≠ 0 := wronskian_ne_zero hcop (by omega)
  -- the good values of `c`
  set S : Set K := {c | F.coeff n - c * G.coeff n ≠ 0} with hS_def
  have hS : S.Infinite := by
    have hsub : Sᶜ.Subsingleton := by
      intro c hc d hd
      simp only [hS_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hc hd
      by_cases hG : G.coeff n = 0
      · have hF : F.coeff n ≠ 0 := by
          rcases le_total F.natDegree G.natDegree with h | h
          · have hnG : n = G.natDegree := by omega
            have : G.natDegree ≠ 0 := by omega
            rw [hnG] at hG
            exact absurd (leadingCoeff_eq_zero.mp hG) (by rintro rfl; simp at this)
          · have hnF : n = F.natDegree := by omega
            have : F.natDegree ≠ 0 := by omega
            rw [hnF]
            intro h0
            exact absurd (leadingCoeff_eq_zero.mp h0) (by rintro rfl; simp at this)
        rw [hG, mul_zero, sub_zero] at hc
        exact absurd hc hF
      · have e1 : c = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hc
        have e2 : d = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hd
        rw [e1, e2]
    have := hsub.finite.infinite_compl
    rwa [compl_compl] at this
  -- every good `c` is the value at a root of `W`
  have hgood : ∀ c ∈ S, ∃ a, W.IsRoot a ∧ F.eval a / G.eval a = c := by
    intro c hc
    set H := F - C c * G with hH_def
    have hHn : H.natDegree = n := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · refine (natDegree_sub_le _ _).trans (max_le (le_max_left _ _) ?_)
        exact (natDegree_C_mul_le _ _).trans (le_max_right _ _)
      · have hc' : F.coeff n - c * G.coeff n ≠ 0 := hc
        simpa [hH_def, coeff_sub, coeff_C_mul] using hc'
    have hH0 : H ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hHn; omega
    -- a root of `H` has value `c`
    have hval : ∀ b, H.IsRoot b → G.eval b ≠ 0 ∧ F.eval b / G.eval b = c := by
      intro b hb
      have hb' : F.eval b = c * G.eval b := by
        have := hb; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
        linear_combination this
      have hGb : G.eval b ≠ 0 := by
        intro h0
        exact eval_ne_zero_of_coprime hcop h0 (by rw [hb', h0, mul_zero])
      exact ⟨hGb, by rw [hb']; field_simp⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H (by
      rw [degree_eq_natDegree hH0]; exact_mod_cast (by omega : H.natDegree ≠ 0))
    obtain ⟨hGa, hFa⟩ := hval a ha
    -- all roots of `H` are `a`
    have hall : ∀ b ∈ H.roots, a = b := by
      intro b hb
      have hb' := (mem_roots hH0).mp hb
      obtain ⟨hGb, hFb⟩ := hval b hb'
      apply hinj
      simp only [ratEval, hGa, hGb, ite_false, hFa, hFb]
    have hcount : H.roots.count a = n := by
      rw [Multiset.count_eq_card.mpr hall, IsAlgClosed.card_roots_eq_natDegree, hHn]
    have hmult : 1 < H.rootMultiplicity a := by
      rw [← count_roots]; convert (show 1 < n by omega) using 2
    obtain ⟨-, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hH0).mp hmult
    refine ⟨a, ?_, hFa⟩
    have hd' : (derivative F).eval a = c * (derivative G).eval a := by
      have := hd
      simp only [IsRoot, hH_def, derivative_sub, derivative_mul, derivative_C, zero_mul,
        zero_add, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    have ha' : F.eval a = c * G.eval a := by
      have := ha; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    simp only [IsRoot, hW_def, eval_sub, eval_mul, hd', ha']
    ring
  -- so the good values lie in a finite set
  have hfin : S.Finite := by
    refine ((W.roots.toFinset.finite_toSet).image (fun a => F.eval a / G.eval a)).subset ?_
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hgood c hc
    exact ⟨a, by simpa [Multiset.mem_toFinset, mem_roots hW] using ha, rfl⟩
  exact hS hfin


/-- **A rational function of degree at most one with no finite pole, fixing `0` and some
`c ≠ 0`, is the identity on `K`.** (With `∞ ↦ ∞`, which "no finite pole" encodes: a Möbius map
fixing `0, ∞, c` is the identity.) -/
theorem ratEval_eq_self [IsAlgClosed K] {F G : K[X]} (hF1 : F.natDegree ≤ 1)
    (hpole : ∀ t, ratEval F G t ≠ OnePoint.infty) (h0 : ratEval F G 0 = OnePoint.some 0)
    {c : K} (hc : c ≠ 0) (hcc : ratEval F G c = OnePoint.some c) :
    ∀ t, ratEval F G t = OnePoint.some t := by
  classical
  have hGne : ∀ t, G.eval t ≠ 0 := fun t ht => hpole t (by simp [ratEval, ht])
  have hG0 : G.natDegree = 0 := by
    by_contra h
    have hG : G ≠ 0 := by rintro rfl; simp at h
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root G (by
      rw [degree_eq_natDegree hG]; exact_mod_cast h)
    exact hGne a ha
  have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero hG0
  have hFX : F = C (F.coeff 1) * X + C (F.coeff 0) := eq_X_add_C_of_natDegree_le_one hF1
  have hd : G.coeff 0 ≠ 0 := by
    have := hGne 0; rwa [hGC, eval_C] at this
  have hval : ∀ t, ratEval F G t =
      OnePoint.some ((F.coeff 1 * t + F.coeff 0) / G.coeff 0) := by
    intro t
    simp only [ratEval, hGne t, ite_false]
    congr 1
    conv_lhs => rw [hFX, hGC]
    simp
  have hb : F.coeff 0 = 0 := by
    have := h0; rw [hval, OnePoint.coe_eq_coe] at this
    simpa [hd] using this
  have ha : F.coeff 1 = G.coeff 0 := by
    have := hcc; rw [hval, OnePoint.coe_eq_coe, hb, add_zero, div_eq_iff hd] at this
    exact mul_right_cancel₀ hc (by rw [this, mul_comm])
  intro t
  rw [hval, hb, ha, add_zero, mul_div_cancel_left₀ _ hd]

end Mob

/-! ## §2 The named facts -/

open Polynomial in
/-- **Curve fact 1 (factorization through a rational function).** On a proper smooth curve
`S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then
`ρ = R ∘ σ` on `ℚ̄`-points with finite `σ`-value, for a rational function `R = [F : G]`,
`F, G ∈ ℚ̄[t]` coprime. (On a geometric component `C` where `σ` is nonconstant: the image of
`(σ, ρ) : C → P¹ × P¹` projects bijectively, hence birationally (char. 0), onto the normal
curve `P¹`, so its inverse is a morphism and `R = pr₂ ∘ pr₁⁻¹`; components where `σ` is
constant are absorbed by the fibre condition, or by Lagrange interpolation if every component
is. STANDARD; not in Mathlib.) -/
def CurveRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ σ ρ : ToP1 S.left,
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        σ.val (K := Qbar) y.left = OnePoint.some t → ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **Curve fact 2 (surjectivity).** A morphism `σ : S → P¹` from a proper smooth curve `S/ℚ`
with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)`. (The geometric
component through the given point has infinitely many `ℚ̄`-points, so `σ` is nonconstant on
it; its image is closed and irreducible, hence `P¹`; closed points of `P¹_ℚ̄` lift to
`ℚ̄`-points. STANDARD, e.g. Hartshorne II.6.8; not in Mathlib.) -/
def CurveSurj : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    Nonempty (fieldPt Qbar ⟶ S) → ∀ σ : ToP1 S.left,
      (∀ y : fieldPt Qbar ⟶ S, {y' : fieldPt Qbar ⟶ S |
        σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite) →
      ∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = t

/-- **Moduli fact (finite twist classes).** For a level-3 object `P` over `ℚ̄`, only finitely
many isomorphism classes `[Q]` have `(Q.A, Q.ι)` isomorphic to an `Aut(𝒪)`-twist of
`(P.A, P.ι)`. (The twists of a pair by `α` and by `α ∘ (conjugation by a unit)` are isomorphic
through `ι(u)`, and `Aut(𝒪)` modulo these is the finite group `N(𝒪)/ℚ^×𝒪^×` (Skolem–Noether);
for a fixed pair, `η` is determined by `η(1) ∈ A[3](ℚ̄)`, a finite group. STANDARD; not in
Mathlib.) -/
def TwistClassFinite : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧
    ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}.Finite

/-! ## §3 The reduction -/

/-- **`MobiusGlueU` from the two curve facts and the moduli fact.** -/
theorem mobiusGlue_of_curveFacts (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : TwistClassFinite) : MobiusGlueU := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg y
  set σ : ToP1 Y'.left := π.comp g.left with hσ_def
  have hσ : ∀ y : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y.left =
      π.val (K := Qbar) (y ≫ g).left := by
    intro y; exact ToP1.val_comp_right π g.left y.left
  rw [← hσ]
  -- representatives
  have hout : ∀ y : fieldPt Qbar ⟶ Y', Φ' Qbar y = M3.mk (Quotient.out (Φ' Qbar y)) :=
    fun y => (Quotient.out_eq _).symm
  -- the two maps have the same fibres
  have hrel : ∀ y₁ y₂ : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left
      ↔ π'.val (K := Qbar) y₁.left = π'.val (K := Qbar) y₂.left := by
    intro y₁ y₂
    rw [hσ, hσ, (h2 (y₁ ≫ g) (y₂ ≫ g) _ _ ((hg Qbar y₁).symm.trans (hout y₁))
      ((hg Qbar y₂).symm.trans (hout y₂))).1, (h2' y₁ y₂ _ _ (hout y₁) (hout y₂)).1]
  -- CM points of `Y'` and the values there
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  have hpt : ∀ P : QML3 Qbar, Φ' Qbar ((Φ' Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => (Φ' Qbar).apply_symm_apply _
  set y₄ := (Φ' Qbar).symm (M3.mk P₄)
  set y₃ := (Φ' Qbar).symm (M3.mk P₃)
  set y₂ := (Φ' Qbar).symm (M3.mk P₂)
  have hY : ∀ y : fieldPt Qbar ⟶ Y', ∀ P : QML3 Qbar, Φ' Qbar y = M3.mk P →
      Φ Qbar (y ≫ g) = M3.mk P := fun y P hP => (hg Qbar y).symm.trans hP
  have σ₄ : σ.val (K := Qbar) y₄.left = OnePoint.some 0 := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₄)) (hY _ _ (hpt P₄))).2.1 c₄
  have π₄ : π'.val (K := Qbar) y₄.left = OnePoint.some 0 :=
    (h2' _ _ _ _ (hpt P₄) (hpt P₄)).2.1 c₄
  have σ₃ : σ.val (K := Qbar) y₃.left = OnePoint.infty := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₃)) (hY _ _ (hpt P₃))).2.2.1 c₃
  have π₃ : π'.val (K := Qbar) y₃.left = OnePoint.infty :=
    (h2' _ _ _ _ (hpt P₃) (hpt P₃)).2.2.1 c₃
  have σ₂ : σ.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₂)) (hY _ _ (hpt P₂))).2.2.2 c₂
  have π₂ : π'.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) :=
    (h2' _ _ _ _ (hpt P₂) (hpt P₂)).2.2.2 c₂
  -- finite fibres
  have hfin : ∀ y : fieldPt Qbar ⟶ Y', {y' : fieldPt Qbar ⟶ Y' |
      σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite := by
    intro y
    refine ((hT (Quotient.out (Φ' Qbar y))).preimage
      (Set.injOn_of_injective (Φ' Qbar).injective)).subset ?_
    intro y' hy'
    have e : π'.val (K := Qbar) y.left = π'.val (K := Qbar) y'.left :=
      ((hrel y' y).1 hy').symm
    exact ⟨_, hout y', ((h2' y y' _ _ (hout y) (hout y')).1).1 e⟩
  obtain ⟨⟨hprop', hsmooth', hne', -, -⟩, -⟩ := h1'
  have hsurj := hSu Y' hprop' hsmooth' hne' σ hfin
  obtain ⟨F, G, hcop, hFG⟩ := hRF Y' hprop' hsmooth' σ π' (fun y₁ y₂ h => (hrel y₁ y₂).1 h)
  -- the rational function is injective, has no finite pole, and fixes `0` and `-16/27`
  have hinj : ∀ s t : Qbar, Mob.ratEval F G s = Mob.ratEval F G t → s = t := by
    intro s t hst
    obtain ⟨ys, hys⟩ := hsurj (OnePoint.some s)
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) ys.left = π'.val (K := Qbar) yt.left := by
      rw [hFG ys s hys, hFG yt t hyt, hst]
    have := (hrel ys yt).2 e
    rw [hys, hyt] at this
    exact OnePoint.coe_injective this
  have hdeg := Mob.natDegree_le_one_of_injective hcop hinj
  have hpole : ∀ t, Mob.ratEval F G t ≠ OnePoint.infty := by
    intro t ht
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) yt.left = π'.val (K := Qbar) y₃.left := by
      rw [hFG yt t hyt, ht, π₃]
    have := (hrel yt y₃).2 e
    rw [hyt, σ₃] at this
    exact OnePoint.coe_ne_infty t this
  have h0 : Mob.ratEval F G 0 = OnePoint.some 0 := by rw [← hFG y₄ 0 σ₄, π₄]
  have hc : Mob.ratEval F G (-16 / 27) = OnePoint.some (-16 / 27) := by
    rw [← hFG y₂ _ σ₂, π₂]
  have hid := Mob.ratEval_eq_self hdeg.1 hpole h0 (by norm_num) hc
  -- conclusion
  by_cases hinf : σ.val (K := Qbar) y.left = OnePoint.infty
  · rw [hinf]
    rw [← π₃]
    exact (hrel y y₃).1 (by rw [hinf, σ₃])
  · obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← ht, hFG y t ht.symm, hid t]

/-! ## §4 `TwistClassFinite` from the textbook leaf `TorsionStructure` (T5) and an algebra fact -/

/-- **Algebra fact (finiteness of `Aut(𝒪)` modulo inner automorphisms by units).** Every ring
automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many. (Every
automorphism of `𝒪` extends to `B = 𝒪 ⊗ ℚ`, hence is conjugation by some `x ∈ N(𝒪)`
(Skolem–Noether), and `N(𝒪)/ℚ^×𝒪^×` is finite: for the maximal order of the quaternion algebra
of discriminant 6 it is the Atkin–Lehner group `W ≅ (ℤ/2)²`. STANDARD (Vignéras, *Arithmétique
des algèbres de quaternions*; locator UNVERIFIED); not in Mathlib.) A statement about the concrete
order `O` of the kernel only. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

section FiniteTwist

variable {K : Type} [Field K]

/-- Every element of `𝒪` is congruent modulo `3𝒪` to some `liftO c`, `c ∈ (ℤ/3)⁴`. -/
theorem exists_liftO_congr (u : O) : ∃ c : Fin 4 → ZMod 3, ∃ k : O, u - liftO c = 3 * k := by
  obtain ⟨n, hn⟩ := u.2
  refine ⟨fun i => (n i : ZMod 3), ⟨ofInt (fun i => n i / 3), ⟨_, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33, liftO]
  rw [hn, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast, Nat.cast_ofNat]
  omega

/-- **Finitely many level structures on one `(A, ι)`** (characteristic 0, given the leaf
`TorsionStructure`): by the kernel's torsor glue `Level3.torsor`, a level structure is
`a ↦ η₀(a u₀)`, which depends only on `u₀ mod 3𝒪`. -/
theorem level3_finite (hT : ObjBridge.TorsionStructure) [CharZero K] {A : AbVar K}
    (s : A.dim = 2) (q : QMStr A) : Finite (Level3 q) := by
  rcases isEmpty_or_nonempty (Level3 q) with h | h
  · infer_instance
  · obtain ⟨e₀⟩ := h
    have key : ∀ e : Level3 q, ∃ c : Fin 4 → ZMod 3, ∀ a : O,
        e.eta a = e₀.eta (a * liftO c) := by
      intro e
      obtain ⟨u₀, -, -, hu⟩ := Level3.torsor hT ⟨A, s, q, e₀⟩ e
      obtain ⟨c, k, hk⟩ := exists_liftO_congr u₀
      refine ⟨c, fun a => (hu a).trans ((e₀.eq_iff _ _).2 ⟨a * k, ?_⟩)⟩
      calc a * u₀ - a * liftO c = a * (u₀ - liftO c) := by noncomm_ring
        _ = a * (3 * k) := by rw [hk]
        _ = 3 * (a * k) := by noncomm_ring
    choose f hf using key
    refine Finite.of_injective f fun e e' h => Level3.ext' ?_
    ext a
    rw [hf e a, hf e' a, h]

/-- Transport of a level structure along an isomorphism of QM pairs. -/
def transportLevel {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- An object is isomorphic to the transport of its level structure. -/
def QML3.isoTransport (Q : QML3 K) {A' : AbVar K} (s' : A'.dim = 2) {q' : QMStr A'}
    (f : QMIso Q.q q') : Q.Iso ⟨A', s', q', transportLevel f Q.e⟩ where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant
  level _ := rfl

/-- Twists by `t` and by `v t v⁻¹` (`v ∈ 𝒪^×`) are isomorphic through `ι(v)`. -/
def conjUnitIso {A : AbVar K} (q : QMStr A) (t α : O ≃+* O) (v : Oˣ)
    (hv : ∀ a, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)) : QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg AbVar.Hom.hom this

/-- **`TwistClassFinite` from the leaf `TorsionStructure` and `AutOInnerFinite`.** -/
theorem twistClassFinite_of (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistClassFinite := by
  obtain ⟨T, hTfin, hTα⟩ := hA
  intro P
  let R : (O ≃+* O) → Set (M3 Qbar) := fun t =>
    Set.range (fun e : Level3 (P.q.twist t) => M3.mk ⟨P.A, P.surface, P.q.twist t, e⟩)
  have hR : ∀ t, (R t).Finite := fun t => by
    have := level3_finite hT P.surface (P.q.twist t)
    exact Set.finite_range _
  refine (hTfin.biUnion fun t _ => hR t).subset ?_
  rintro m ⟨Q, rfl, α, ⟨f⟩⟩
  obtain ⟨t, ht, v, hv⟩ := hTα α
  let h : QMIso Q.q (P.q.twist t) := ((conjUnitIso P.q t α v hv).trans f).symm
  refine Set.mem_biUnion ht ⟨transportLevel h Q.e, ?_⟩
  exact Quotient.sound ⟨(QML3.isoTransport Q P.surface h).symm⟩

end FiniteTwist

/-! ## §5 The result -/

/-- **`MobiusGlueU` from two curve facts, the textbook leaf `TorsionStructure` (T5, Mumford §4)
and the algebra fact `AutOInnerFinite`.** -/
theorem mobiusGlue_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) : MobiusGlueU :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite_of hT hA)

end Pin

end AV

end LeafQM


/-! ## §7 `AutOInnerFinite` from Skolem–Noether (proved in the kernel) and `NormalizerFinite`

(Outside the `open MonObj` scope of §0-§6.) -/

namespace LeafQM

namespace AV

namespace Pin

namespace AutOExt

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-! ### `AutOInnerFinite` from Skolem–Noether and the normalizer -/

/-- **Normalizer fact (N(𝒪)/ℚ^×𝒪^× finite).** Every `u ∈ B^×` normalizing `𝒪` is
`q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t` in a fixed finite set. -/
def NormalizerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ, (∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) →
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B)

/-- Skolem–Noether (proved in the kernel, `TSkolemKW.leafSkolemNoether`) applied to `α̃`. -/
theorem conj_of_skolem : ∃ u : Bˣ, ∀ b : B, extFun α b = u * b * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner TSkolemKW.leafSkolemNoether (extAlgEquiv α)
  exact ⟨u, fun b => hu b⟩

/-- Conjugation by a unit of `𝒪`, `a ↦ v⁻¹ a v`. -/
def conjUnit (v : Oˣ) : O ≃+* O where
  toFun a := ((v⁻¹ : Oˣ) : O) * a * v
  invFun a := (v : O) * a * ((v⁻¹ : Oˣ) : O)
  left_inv a := by
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  right_inv a := by
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  map_mul' a b := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' a b := by
    simp only [mul_add, add_mul]

theorem key_conj {R : Type*} [Ring R] (x y w w' c c' t : R) (hvv : w' * w = 1) (hcc : c' * c = 1)
    (hc : c * x = x * c) (h : x * (c * w * t) = c * w * t * y) : w' * x * w * t = t * y := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc w' * x * w * t = w' * (x * w * t) := by simp only [mul_assoc]
    _ = w' * (w * t * y) := by rw [h1]
    _ = t * y := by simp only [← mul_assoc]; rw [hvv, one_mul]

/-- **`AutOInnerFinite` from the normalizer fact** (with Skolem–Noether from the kernel). -/
theorem autOInnerFinite_of_normalizer (hN : NormalizerFinite) : AutOInnerFinite := by
  classical
  obtain ⟨T, hT, hTu⟩ := hN
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hT' : T'.Finite := by
    refine Set.Finite.of_finite_image (f := f) (hT.subset (t := f '' T') ?_) ?_
    · rintro _ ⟨β, hβ, rfl⟩; exact (hf β hβ).1
    · intro β₁ h₁ β₂ h₂ heq
      apply RingEquiv.ext; intro a
      apply Subtype.ext
      have e1 := (hf β₁ h₁).2 a
      have e2 := (hf β₂ h₂).2 a
      rw [heq] at e1
      exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  refine ⟨T', hT', fun α => ?_⟩
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := hTu u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end AutOExt

/-- **`MobiusGlueU` from the two curve facts, the leaf `TorsionStructure` (T5) and
`NormalizerFinite` (`N(𝒪)/ℚ^×𝒪^×` finite).** Skolem–Noether enters through the kernel's proof
`TSkolemKW.leafSkolemNoether`. -/
theorem mobiusGlue_of_normalizer (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hN : AutOExt.NormalizerFinite) : MobiusGlueU :=
  mobiusGlue_of_named hRF hSu hT (AutOExt.autOInnerFinite_of_normalizer hN)

end Pin

end AV

end LeafQM


/-! ## §8 `NormalizerFinite`, proved: `N(𝒪)/ℚ^×𝒪^×` is represented by `{1, i, j, ij}`

Descent on `|nrd|`. A prime `p ∤ 6` dividing `nrd(u)` of a normalizing `u ∈ 𝒪` divides `u`: an
explicit identity `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`,
`scratch/mobius-glue/py/normalizer_identity.py`). If `2 | nrd(u)` then `u i⁻¹ ∈ 𝒪`, and if
`3 | nrd(u)` then `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by `decide`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace NormO

/-! ### Integer coordinates -/

/-- The reduced norm in the coordinates of `ofInt`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2

/-- The conjugate in the coordinates of `ofInt`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [mulCoord, nrdZ]; ring

theorem ofInt_scalar (z : ℤ) : ofInt ![z, 0, 0, 0] = algebraMap ℚ B (z : ℚ) := by
  ext <;> simp [ofInt]

theorem smul_ofInt (z : ℤ) (n : Fin 4 → ℤ) : (z : ℚ) • ofInt n = ofInt (fun l => z * n l) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O_iff (x : B) : x ∈ O ↔ ∃ n, x = ofInt n := Iff.rfl

/-- `(1/z) • ofInt m ∈ 𝒪` forces `z ∣ m`. -/
theorem dvd_of_smul_mem {z : ℤ} (hz : z ≠ 0) {m : Fin 4 → ℤ}
    (h : ((z : ℚ)⁻¹) • ofInt m ∈ O) : ∀ l, z ∣ m l := by
  obtain ⟨w, hw⟩ := h
  have : ofInt m = ofInt (fun l => z * w l) := by
    rw [← smul_ofInt, ← hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hz), one_smul]
  have e := AV.ofInt_injective this
  intro l
  exact ⟨w l, congrFun e l⟩

/-! ### The units `i`, `j` of `B` -/

def ei : Fin 4 → ℤ := ![0, 1, 0, 0]
def ej : Fin 4 → ℤ := ![-1, 0, 2, 0]

theorem nrdZ_ei : nrdZ ei = -2 := by simp [nrdZ, ei]
theorem nrdZ_ej : nrdZ ej = 3 := by simp [nrdZ, ej]

def ui : Bˣ where
  val := ofInt ei
  inv := ((2 : ℚ)⁻¹) • ofInt ei
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]

def uj : Bˣ where
  val := ofInt ej
  inv := ((-3 : ℚ)⁻¹) • ofInt ej
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]

/-- The representatives `{1, i, j, ij}` of `N(𝒪)/ℚ^×𝒪^×`. -/
def T : Set Bˣ := {1, ui, uj, ui * uj}

theorem T_finite : T.Finite := by
  simp only [T]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-! ### Normalizing units -/

/-- `u` normalizes `𝒪`. -/
def IsNorm (u : Bˣ) : Prop :=
  ∀ a ∈ O, (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O ∧ ((u⁻¹ : Bˣ) : B) * a * u ∈ O

theorem IsNorm.mul {u w : Bˣ} (hu : IsNorm u) (hw : IsNorm w) : IsNorm (u * w) := by
  intro a ha
  refine ⟨?_, ?_⟩
  · have := (hu _ (hw a ha).1).1
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this
  · have := (hw _ (hu a ha).2).2
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this

theorem IsNorm.inv {u : Bˣ} (hu : IsNorm u) : IsNorm u⁻¹ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hu a ha
  exact ⟨h2, by simpa using h1⟩

/-- The unit `c ∈ ℚ^×` of `B`. -/
def sc (c : ℚ) (hc : c ≠ 0) : Bˣ where
  val := algebraMap ℚ B c
  inv := algebraMap ℚ B c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem isNorm_sc (c : ℚ) (hc : c ≠ 0) : IsNorm (sc c hc) := by
  intro a ha
  have e1 : ((sc c hc : Bˣ) : B) * a * (((sc c hc)⁻¹ : Bˣ) : B) = a := by
    change algebraMap ℚ B c * a * algebraMap ℚ B c⁻¹ = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
  have e2 : (((sc c hc)⁻¹ : Bˣ) : B) * a * ((sc c hc : Bˣ) : B) = a := by
    change algebraMap ℚ B c⁻¹ * a * algebraMap ℚ B c = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  exact ⟨by rw [e1]; exact ha, by rw [e2]; exact ha⟩

theorem isNorm_ui : IsNorm ui := by
  rintro a ⟨n, rfl⟩
  have e : ((ui : Bˣ) : B) * ofInt n * ((ui⁻¹ : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change ofInt ei * ofInt n * (((2 : ℚ)⁻¹) • ofInt ei) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  have e' : ((ui⁻¹ : Bˣ) : B) * ofInt n * ((ui : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change (((2 : ℚ)⁻¹) • ofInt ei) * ofInt n * ofInt ei = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

theorem isNorm_uj : IsNorm uj := by
  rintro a ⟨n, rfl⟩
  have e : ((uj : Bˣ) : B) * ofInt n * ((uj⁻¹ : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change ofInt ej * ofInt n * (((-3 : ℚ)⁻¹) • ofInt ej) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  have e' : ((uj⁻¹ : Bˣ) : B) * ofInt n * ((uj : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change (((-3 : ℚ)⁻¹) • ofInt ej) * ofInt n * ofInt ej = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

/-! ### The norm of a unit in `𝒪` and its inverse -/

theorem nrdZ_ne_zero (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) : nrdZ n ≠ 0 := by
  intro h0
  have h1 : (u : B) * ofInt (conjC n) = 0 := by
    rw [hu, ofInt_mul, mulCoord_conjC, h0, ofInt_scalar]; simp
  have h2 : ofInt (conjC n) = 0 := by
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) * x) h1
    simpa [← mul_assoc] using this
  have h3 : conjC n = 0 := AV.ofInt_injective (h2.trans ofInt_zero.symm)
  have h4 : n = 0 := by
    funext l
    have e0 := congrFun h3 0; have e1 := congrFun h3 1
    have e2 := congrFun h3 2; have e3 := congrFun h3 3
    simp [conjC] at e0 e1 e2 e3
    fin_cases l <;> simp <;> omega
  have : (u : B) = 0 := by rw [hu, h4, ofInt_zero]
  exact u.ne_zero this

theorem inv_eq (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) :
    ((u⁻¹ : Bˣ) : B) = ((nrdZ n : ℚ)⁻¹) • ofInt (conjC n) := by
  have hN : (nrdZ n : ℚ) ≠ 0 := by exact_mod_cast nrdZ_ne_zero u n hu
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_smul_comm, hu, ofInt_mul, mulCoord_conjC, ofInt_scalar, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ hN, map_one]

def bas : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- For a normalizing `u = ofInt n`, `nrd(u)` divides every coordinate of `u e_k ū`. -/
theorem nrd_dvd_coords (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (k l : Fin 4) : nrdZ n ∣ mulCoord (mulCoord n (bas k)) (conjC n) l := by
  have h := (hN (ofInt (bas k)) ⟨_, rfl⟩).1
  rw [inv_eq u n hu, mul_smul_comm, hu, ofInt_mul, ofInt_mul] at h
  exact dvd_of_smul_mem (nrdZ_ne_zero u n hu) h l

/-- The identities `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`). -/
theorem six_sq_identities (n : Fin 4 → ℤ) :
    let F := fun k l => mulCoord (mulCoord n (bas k)) (conjC n) l
    6 * n 0 ^ 2 = 2 * F 0 0 + 2 * F 1 1 + 2 * F 1 3 + 2 * F 2 2 - 2 * F 3 1 ∧
    6 * n 1 ^ 2 = -F 1 1 - 2 * F 2 0 + F 3 1 + F 3 3 ∧
    6 * n 2 ^ 2 = 2 * F 0 0 - 2 * F 1 1 + 2 * F 2 2 - 2 * F 3 3 ∧
    6 * n 3 ^ 2 = F 1 1 + F 1 3 - 2 * F 2 0 - F 3 3 := by
  intro F
  simp only [F, mulCoord, bas, conjC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- A prime `p ≠ 2, 3` dividing `nrd(u)` of a normalizing `u = ofInt n` divides `n`. -/
theorem dvd_of_prime_dvd_nrd (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hpd : (p : ℤ) ∣ nrdZ n) :
    ∀ l, (p : ℤ) ∣ n l := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hF : ∀ k l, (p : ℤ) ∣ mulCoord (mulCoord n (bas k)) (conjC n) l :=
    fun k l => hpd.trans (nrd_dvd_coords u n hu hN k l)
  have h6 : ¬ (p : ℤ) ∣ 6 := by
    intro h
    have h' : p ∣ 6 := by exact_mod_cast h
    have : p ∣ 2 * 3 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  obtain ⟨i0, i1, i2, i3⟩ := six_sq_identities n
  have k0 : (p : ℤ) ∣ 6 * n 0 ^ 2 := by
    rw [i0]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 1 3) _))
      (dvd_mul_of_dvd_right (hF 2 2) _)) (dvd_mul_of_dvd_right (hF 3 1) _)
  have k1 : (p : ℤ) ∣ 6 * n 1 ^ 2 := by
    rw [i1]
    exact dvd_add (dvd_add (dvd_sub (dvd_neg.mpr (hF 1 1)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 1)) (hF 3 3)
  have k2 : (p : ℤ) ∣ 6 * n 2 ^ 2 := by
    rw [i2]
    exact dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 2 2) _))
      (dvd_mul_of_dvd_right (hF 3 3) _)
  have k3 : (p : ℤ) ∣ 6 * n 3 ^ 2 := by
    rw [i3]
    exact dvd_sub (dvd_sub (dvd_add (hF 1 1) (hF 1 3)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 3)
  have key : ∀ l, (p : ℤ) ∣ 6 * n l ^ 2 := by
    intro l; fin_cases l
    exacts [k0, k1, k2, k3]
  intro l
  rcases hpZ.dvd_or_dvd (key l) with h | h
  · exact absurd h h6
  · exact hpZ.dvd_of_dvd_pow h

/-! ### The primes 2 and 3 -/

theorem two_dvd_mulCoord_ei (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) :
    ∀ l, (2 : ℤ) ∣ mulCoord n ei l := by
  have hz : ((nrdZ n : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 2,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a = 0 ∧ c = 0 := by
    decide
  obtain ⟨h0, h2⟩ := key _ _ _ _ hz
  have d0 : (2 : ℤ) ∣ n 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
  have d2 : (2 : ℤ) ∣ n 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
  intro l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem three_dvd_mulCoord_ej (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) :
    ∀ l, (3 : ℤ) ∣ mulCoord n ej l := by
  have hz : ((nrdZ n : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 3,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a - c = 0 ∧ b - d = 0 := by
    decide
  obtain ⟨h0, h1⟩ := key _ _ _ _ hz
  have d0 : (3 : ℤ) ∣ n 0 - n 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h0)
  have d1 : (3 : ℤ) ∣ n 1 - n 3 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h1)
  intro l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

/-! ### Closure of `T` under right multiplication by `i` and `j` -/

theorem T_mem_iff (t : Bˣ) : t ∈ T ↔ t = 1 ∨ t = ui ∨ t = uj ∨ t = ui * uj := Iff.rfl

theorem T_mul_ui : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (ui : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, ui, by simp [T], by simp⟩
  · refine ⟨2, two_ne_zero, 1, by simp [T], ?_⟩
    change ofInt ei * ofInt ei = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ei, QuaternionAlgebra.algebraMap_eq]
  · refine ⟨-1, by norm_num, ui * uj, by simp [T], ?_⟩
    change ofInt ej * ofInt ei = _ * (ofInt ei * ofInt ej)
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-2, by norm_num, uj, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ei = _ * ofInt ej
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

theorem T_mul_uj : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (uj : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, uj, by simp [T], by simp⟩
  · exact ⟨1, one_ne_zero, ui * uj, by simp [T], by simp⟩
  · refine ⟨-3, by norm_num, 1, by simp [T], ?_⟩
    change ofInt ej * ofInt ej = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-3, by norm_num, ui, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ej = _ * ofInt ei
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

/-- Rearranging `q v t i = (q c) v t'` for central `c`. -/
theorem rearrange (q c : ℚ) (V Tt I T' : B) (h : Tt * I = algebraMap ℚ B c * T') :
    algebraMap ℚ B q * V * Tt * I = algebraMap ℚ B (q * c) * V * T' := by
  rw [mul_assoc (algebraMap ℚ B q * V), h, ← mul_assoc, mul_assoc (algebraMap ℚ B q),
    ← Algebra.commutes c V, ← mul_assoc, ← map_mul]

theorem mulCoord_smul_right (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord n (fun l => z * m l) = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem mulCoord_smul_left (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord (fun l => z * n l) m = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem nrdZ_smul (n : Fin 4 → ℤ) (z : ℤ) : nrdZ (fun l => z * n l) = z ^ 2 * nrdZ n := by
  simp [nrdZ]; ring

/-! ### The descent -/

theorem descent (m : ℕ) : ∀ (u : Bˣ) (n : Fin 4 → ℤ), (u : B) = ofInt n →
    (nrdZ n).natAbs = m → IsNorm u →
    ∃ q : ℚ, q ≠ 0 ∧ ∃ v : Oˣ, ∃ t ∈ T, (u : B) = algebraMap ℚ B q * ((v : O) : B) * t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u n hu hm hN
  have hN0 := nrdZ_ne_zero u n hu
  by_cases h1 : m = 1
  · have hsq : nrdZ n * nrdZ n = 1 := by
      have : (nrdZ n).natAbs = 1 := hm.trans h1
      rcases Int.natAbs_eq_iff.mp this with h | h <;> rw [h] <;> norm_num
    set w : Fin 4 → ℤ := fun l => nrdZ n * conjC n l with hw_def
    have hw1 : mulCoord n w = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_right, mulCoord_conjC]
      funext l; fin_cases l <;> simp [hsq]
    have hw2 : mulCoord w n = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_left, mulCoord_conjC']
      funext l; fin_cases l <;> simp [hsq]
    let v : Oˣ :=
      ⟨⟨ofInt n, n, rfl⟩, ⟨ofInt w, w, rfl⟩,
        Subtype.ext (by
          change ofInt n * ofInt w = 1
          rw [ofInt_mul, hw1, ofInt_one]),
        Subtype.ext (by
          change ofInt w * ofInt n = 1
          rw [ofInt_mul, hw2, ofInt_one])⟩
    refine ⟨1, one_ne_zero, v, 1, by simp [T], ?_⟩
    rw [map_one, one_mul, Units.val_one, mul_one]
    exact hu
  · have hm0 : m ≠ 0 := by
      rintro rfl; exact hN0 (Int.natAbs_eq_zero.mp hm)
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : (p : ℤ) ∣ nrdZ n := by
      rw [Int.natCast_dvd, hm]; exact Nat.minFac_dvd m
    have hp1 : 2 ≤ p := hp.two_le
    by_cases hp2 : p = 2
    · have h2 : (2 : ℤ) ∣ nrdZ n := by rw [hp2] at hpd; exact_mod_cast hpd
      have hc := two_dvd_mulCoord_ei n h2
      set n' : Fin 4 → ℤ := fun l => mulCoord n ei l / 2 with hn'_def
      have hn' : mulCoord n ei = fun l => 2 * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hc l)).symm
      have hu' : ((u * ui⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((2 : ℚ)⁻¹) • ofInt ei) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ei = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * ui⁻¹ : Bˣ) : B) * ((ui : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ei
        rw [hmul, nrdZ_ei] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h2' : (-2 : ℤ).natAbs = 2 := rfl
        rw [← hm, e, Int.natAbs_mul, h2']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * ui⁻¹) n' hu' rfl (hN.mul isNorm_ui.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_ui t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * ui⁻¹ : Bˣ) : B) * ui := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    by_cases hp3 : p = 3
    · have h3 : (3 : ℤ) ∣ nrdZ n := by rw [hp3] at hpd; exact_mod_cast hpd
      have hc := three_dvd_mulCoord_ej n h3
      set n' : Fin 4 → ℤ := fun l => -(mulCoord n ej l / 3) with hn'_def
      have hn' : mulCoord n ej = fun l => (-3) * n' l := by
        funext l
        simp only [hn'_def]
        rw [mul_neg, neg_mul, neg_neg, Int.mul_ediv_cancel' (hc l)]
      have hu' : ((u * uj⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((-3 : ℚ)⁻¹) • ofInt ej) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ej = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * uj⁻¹ : Bˣ) : B) * ((uj : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ej
        rw [hmul, nrdZ_ej] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [← hm, e, Int.natAbs_mul, h3']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * uj⁻¹) n' hu' rfl (hN.mul isNorm_uj.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_uj t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * uj⁻¹ : Bˣ) : B) * uj := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    · have hdiv := dvd_of_prime_dvd_nrd u n hu hN p hp hp2 hp3 hpd
      set n' : Fin 4 → ℤ := fun l => n l / p with hn'_def
      have hn' : n = fun l => (p : ℤ) * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hdiv l)).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpi : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero hp0
      have hu' : ((sc _ hpi * u : Bˣ) : B) = ofInt n' := by
        change algebraMap ℚ B ((p : ℚ)⁻¹) * u = _
        rw [← Algebra.smul_def, hu, hn', ← smul_ofInt, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hp0, one_smul]
      have hlt : (nrdZ n').natAbs < m := by
        have e : nrdZ n = (p : ℤ) ^ 2 * nrdZ n' := by rw [hn', nrdZ_smul]
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        rw [← hm, e, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have : 4 ≤ p ^ 2 := by nlinarith
        have : (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs := by
          have : 1 * (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa using this
        exact this
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (sc _ hpi * u) n' hu' rfl ((isNorm_sc _ hpi).mul hN)
      refine ⟨p * q, mul_ne_zero hp0 hq, v, t, ht, ?_⟩
      have : (u : B) = algebraMap ℚ B (p : ℚ) * ((sc _ hpi * u : Bˣ) : B) := by
        change _ = _ * (algebraMap ℚ B ((p : ℚ)⁻¹) * u)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
      rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

/-! ### `NormalizerFinite` -/

/-- **`N(𝒪)/ℚ^×𝒪^×` is finite** (represented by `{1, i, j, ij}`). -/
theorem normalizerFinite : AutOExt.NormalizerFinite := by
  refine ⟨T, T_finite, fun u hu => ?_⟩
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

end NormO

open CategoryTheory AlgebraicGeometry

/-- **`AutOInnerFinite`, proved** (Skolem–Noether from the kernel, the normalizer from §8). -/
theorem autOInnerFinite : AutOInnerFinite :=
  AutOExt.autOInnerFinite_of_normalizer NormO.normalizerFinite

/-- **`TwistClassFinite` from the leaf `TorsionStructure` alone.** -/
theorem twistClassFinite (hT : ObjBridge.TorsionStructure) : TwistClassFinite :=
  twistClassFinite_of hT autOInnerFinite

/-- **Main result: `MobiusGlueU` from the two curve facts and the textbook leaf
`TorsionStructure` (T5).** -/
theorem mobiusGlue_of_curves (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlueU :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite hT)


/-- (g0-assemble2) the repaired `R1fpProps` of Leaves.lean gives mobius-glue's `R1fpPropsU`. -/
theorem r1fpPropsU_of {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) : R1fpPropsU Y Φ :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩

/-- (g0-assemble2) mobius-glue's `MobiusGlueU` gives Leaves.lean's `MobiusGlue`. -/
theorem mobiusGlue_of_U (h : MobiusGlueU) : MobiusGlue := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hΦ y
  exact h Y Y' Φ Φ' π π' g (r1fpPropsU_of h1) h2 (r1fpPropsU_of h1') h2' hCM hΦ y

/-- **`MobiusGlue` (Leaves.lean's) from the two curve facts and T5** (mobius-glue). -/
theorem mobiusGlue_of_curves' (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_U (mobiusGlue_of_curves hRF hSu hT)

end Pin

end AV

end LeafQM
end

end G0A2_a55_mobius

section G0A2_a56_curvefacts
/-! ## g0-assemble2: curve-facts (scratch/curve-facts/CurveFacts.lean lines 3-38 and 84-end, verbatim; its §0
(lines 39-83) copies `Mob.ratEval`, `CurveRatFactor`, `CurveSurj` from mobius-glue, defined in part a55) -/

/-!
# curve-facts: `CurveRatFactor` and `CurveSurj` reduced to per-component curve facts

Task curve-facts (2026-11-13). See `docs/research/curve-facts.md`.

`CurveRatFactor` and `CurveSurj` are copied verbatim from `scratch/mobius-glue/MobiusGlue.lean`
(§2), together with `Mob.ratEval` (§1 there). Everything else they use (`ToP1`, `ToP1.val`,
`fieldPt`, `Qbar`) is imported from `ZInQKernel.HDecomp.QM.Pairs`, where mobius-glue took it from.

**Main results.**
* `curveSurj_of_comp : GeomCompInfinite → GeomCompConstOrOnto → CurveSurj`;
* `curveRatFactor_of_comp : GeomCompConstOrOnto → GeomCompRatFactor → CurveRatFactor`, using
  `geomCompFinite` (proved here from Mathlib: `S_ℚ̄` is a Noetherian scheme, so it has finitely
  many irreducible, hence connected, components) and `Mob.exists_interp` (proved here: rational
  interpolation of values in `P¹` at finitely many nodes by a coprime pair).

The named facts are stated over genuine definitions only: the base change
`S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's `pullback`), the `ℚ̄`-point of `S_ℚ̄` induced by a
`ℚ̄`-point of `S` (`pullback.lift`), its point (`Scheme.SpecToEquivOfField`), and Mathlib's
`connectedComponent` in the underlying space of `S_ℚ̄`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

/-! ## §1 Geometric components (genuine definitions) -/

/-- `S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's pullback). -/
abbrev bcQbar (S : Over (Spec (CommRingCat.of ℚ))) : Scheme.{0} :=
  pullback S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

/-- The `ℚ̄`-point `Spec ℚ̄ → S_ℚ̄` (a section over `Spec ℚ̄`) induced by a `ℚ̄`-point of `S`
over `ℚ`. -/
def bcPt {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) :
    Spec (CommRingCat.of Qbar) ⟶ bcQbar S :=
  pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)

/-- **The geometric component of a `ℚ̄`-point `y` of `S`**: the connected component of the
underlying space of `S_ℚ̄` containing the (closed) point of `S_ℚ̄` at which `bcPt y` sits. For
`S` smooth over `ℚ` the connected components of `S_ℚ̄` are its irreducible components (smooth
implies normal implies locally irreducible). -/
def geomComp {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) : Set (bcQbar S) :=
  connectedComponent (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1

/-! ## §2 The named facts -/

/-- **(C1) A geometric component of a smooth curve has infinitely many `ℚ̄`-points.**
Glue (STANDARD): a connected component `C` of `S_ℚ̄` is a smooth curve over `ℚ̄` (a nonempty
scheme of finite type over `ℚ̄` of dimension 1); its closed points are its `ℚ̄`-points
(Nullstellensatz) and there are infinitely many of them (a Jacobson scheme with finitely many
closed points is a finite discrete set, of dimension 0); a `ℚ̄`-point of `S_ℚ̄` over `ℚ̄` is
`bcPt y` for a unique `ℚ̄`-point `y` of `S` over `ℚ` (universal property of the pullback).
Properness is not needed. Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def GeomCompInfinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ y₀ : fieldPt Qbar ⟶ S, {y : fieldPt Qbar ⟶ S | geomComp y = geomComp y₀}.Infinite

/-- **(C2) Constant or onto on a geometric component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8: a morphism from a complete nonsingular curve to a curve is constant or
surjective; UNVERIFIED numbering, cited so in mobius-glue). On the geometric component of `y₀`,
`σ` either takes the single value `σ(y₀)` at every `ℚ̄`-point, or takes every value of
`P¹(ℚ̄)`. Textbook leaf (published; applied to the connected component of `S_ℚ̄`, a complete
nonsingular curve over `ℚ̄`, with the dictionary between `ℚ̄`-points of `S` and closed points of
`S_ℚ̄`). Not in Mathlib v4.35 (Mathlib has `IsProper → IsClosedMap`, but no `P¹` as a scheme
and no dimension theory of curves). -/
def GeomCompConstOrOnto : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ →
        σ.val (K := Qbar) y.left = σ.val (K := Qbar) y₀.left) ∨
      (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left = t)

open Polynomial in
/-- **(C3) Factorization on one geometric component where `σ` is nonconstant.** If `σ` is
nonconstant on the geometric component `C` of `y₀` and `ρ` is constant on the `σ`-fibres in `C`
(on `ℚ̄`-points), then `ρ = [F : G] ∘ σ` on the `ℚ̄`-points of `C` with finite `σ`-value, for
coprime `F, G ∈ ℚ̄[t]`. Textbook (STANDARD): `σ|_C : C → P¹` is finite of some degree `n`, and
`ℚ̄(σ) ⊆ ℚ̄(σ, ρ) ⊆ ℚ̄(C)`; the normalization `D` of the image of `(σ, ρ)` is a smooth complete
curve with `D → P¹` finite of degree `[ℚ̄(σ, ρ) : ℚ̄(σ)]`, separable (char. 0), so its general
fibre has that many points (Hartshorne II.6.9 and IV.2.2, UNVERIFIED numbering); the fibre
condition makes the general fibre a single point, so `ℚ̄(σ, ρ) = ℚ̄(σ)`, `ρ = R(σ)` in `ℚ̄(C)`,
and two morphisms `C → P¹` agreeing generically agree (C reduced, `P¹` separated).
Classified as glue (a standard consequence of textbook theorems, not one printed theorem). Not
in Mathlib v4.35 (no degree of a finite morphism of curves, no fibre count). -/
def GeomCompRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ ρ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left) →
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, geomComp y₁ = geomComp y₀ → geomComp y₂ = geomComp y₀ →
        σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        geomComp y = geomComp y₀ → σ.val (K := Qbar) y.left = OnePoint.some t →
        ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **(C4) Finitely many geometric components.** Proved below (`geomCompFinite`). -/
def GeomCompFinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom →
    (Set.range (geomComp (S := S))).Finite

/-! ## §3 `GeomCompFinite`, from Mathlib -/

theorem geomCompFinite : GeomCompFinite := by
  intro S hP
  have : IsNoetherian (bcQbar S) := { }
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := bcQbar S)
  classical
  refine (hfin.image (fun Z => if h : Z.Nonempty then connectedComponent h.some else ∅)).subset ?_
  rintro _ ⟨y, rfl⟩
  set x := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 with hx
  have hne : (irreducibleComponent x).Nonempty := ⟨x, mem_irreducibleComponent⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  simp only [dite_eq_left hne]
  exact (connectedComponent_eq (irreducibleComponent_subset_connectedComponent hne.some_mem)).symm

/-! ## §4 Rational interpolation by a coprime pair -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]

theorem isCoprime_X_sub_C_of_eval_one {F : K[X]} {a : K} (h : F.eval a = 1) :
    IsCoprime F (X - C a) := by
  have e := modByMonic_add_div F (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval, h, map_one] at e
  exact ⟨1, -(F /ₘ (X - C a)), by linear_combination (-1 : K[X]) * e⟩

/-- **Rational interpolation.** Any assignment of values in `P¹(K)` to finitely many nodes
`t ∈ T ⊆ K` is realised by `[F : G]` with `F, G` coprime. -/
theorem exists_interp (T : Finset K) (r : K → OnePoint K) :
    ∃ F G : K[X], IsCoprime F G ∧ ∀ t ∈ T, ratEval F G t = r t := by
  classical
  set Tinf := T.filter (fun t => r t = OnePoint.infty) with hTinf
  set G : K[X] := ∏ a ∈ Tinf, (X - C a) with hG
  have hGeval : ∀ t, G.eval t = ∏ a ∈ Tinf, (t - a) := by
    intro t; simp [hG, eval_prod]
  have hG0 : ∀ t ∈ Tinf, G.eval t = 0 := by
    intro t ht; rw [hGeval]; exact Finset.prod_eq_zero ht (sub_self t)
  have hGne : ∀ t, t ∉ Tinf → G.eval t ≠ 0 := by
    intro t ht; rw [hGeval, Finset.prod_ne_zero_iff]
    intro a ha e; exact ht (by rwa [sub_eq_zero.mp e])
  let w : K → K := fun t =>
    if h : ∃ v : K, r t = OnePoint.some v then h.choose * G.eval t else 1
  set F : K[X] := Lagrange.interpolate T id w with hF
  have hFeval : ∀ t ∈ T, F.eval t = w t := fun t ht =>
    Lagrange.eval_interpolate_at_node (v := id) w (Set.injOn_id _) ht
  refine ⟨F, G, ?_, ?_⟩
  · refine IsCoprime.prod_right fun a ha => isCoprime_X_sub_C_of_eval_one ?_
    have haT : a ∈ T := (Finset.mem_filter.mp ha).1
    have hra : r a = OnePoint.infty := (Finset.mem_filter.mp ha).2
    rw [hFeval a haT]
    have : ¬ ∃ v : K, r a = OnePoint.some v := by
      rintro ⟨v, hv⟩; rw [hra] at hv; exact OnePoint.infty_ne_coe v hv
    simp only [w, dite_eq_right this]
  · intro t ht
    by_cases hti : t ∈ Tinf
    · rw [(Finset.mem_filter.mp hti).2]; simp [ratEval, hG0 t hti]
    · have hrt : r t ≠ OnePoint.infty := fun e => hti (Finset.mem_filter.mpr ⟨ht, e⟩)
      have hex : ∃ v : K, r t = OnePoint.some v := by
        induction h : r t using OnePoint.rec with
        | infty => exact absurd h hrt
        | coe v => exact ⟨v, rfl⟩
      have hGt := hGne t hti
      rw [ratEval, ite_eq_right hGt, hFeval t ht]
      simp only [w, dite_eq_left hex]
      rw [mul_div_cancel_right₀ _ hGt]
      exact hex.choose_spec.symm

end Mob

/-! ## §5 The reductions -/

/-- **`CurveSurj` from (C1) and (C2).** -/
theorem curveSurj_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto) : CurveSurj := by
  intro S hP hS ⟨y₀⟩ σ hfin t
  rcases h2 S hP hS σ y₀ with hc | ho
  · exact absurd ((hfin y₀).subset fun y hy => hc y hy) (h1 S hP hS y₀)
  · obtain ⟨y, -, hy⟩ := ho t
    exact ⟨y, hy⟩

/-- **`CurveRatFactor` from (C2) and (C3)** (with (C4), proved, and rational interpolation). -/
theorem curveRatFactor_of_comp (h2 : GeomCompConstOrOnto) (h3 : GeomCompRatFactor) :
    CurveRatFactor := by
  classical
  intro S hP hS σ ρ hfib
  by_cases hnc : ∃ y₀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
      σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left
  · -- a component on which `σ` is nonconstant: it is onto, and carries the rational function
    obtain ⟨y₀, hne⟩ := hnc
    obtain ⟨F, G, hcop, hR⟩ := h3 S hP hS σ ρ y₀ hne (fun y₁ y₂ _ _ h => hfib y₁ y₂ h)
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    rcases h2 S hP hS σ y₀ with hc | ho
    · obtain ⟨y', hy', hne'⟩ := hne
      exact absurd (hc y' hy') hne'
    · obtain ⟨y', hy'c, hy't⟩ := ho (OnePoint.some t)
      rw [hfib y y' (hy.trans hy't.symm)]
      exact hR y' t hy'c hy't
  · -- `σ` constant on every component: finitely many values; interpolate
    push Not at hnc
    have hV : (Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left).Finite := by
      refine ((geomCompFinite S hP).image (fun c => if h : ∃ y : fieldPt Qbar ⟶ S,
        geomComp y = c then σ.val (K := Qbar) h.choose.left else OnePoint.infty)).subset ?_
      rintro _ ⟨y, rfl⟩
      have h : ∃ y' : fieldPt Qbar ⟶ S, geomComp y' = geomComp y := ⟨y, rfl⟩
      refine ⟨geomComp y, ⟨y, rfl⟩, ?_⟩
      simp only [dite_eq_left h]
      exact (hnc h.choose y h.choose_spec.symm).symm
    have hT : {t : Qbar | (OnePoint.some t) ∈
        Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left}.Finite :=
      hV.preimage (OnePoint.coe_injective.injOn)
    let r : Qbar → OnePoint Qbar := fun t =>
      if h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t then
        ρ.val (K := Qbar) h.choose.left else OnePoint.infty
    obtain ⟨F, G, hcop, hFG⟩ := Mob.exists_interp hT.toFinset r
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    have hmem : t ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨y, hy⟩
    have h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t := ⟨y, hy⟩
    rw [hFG t hmem]
    simp only [r, dite_eq_left h]
    exact hfib y h.choose (hy.trans h.choose_spec.symm)

/-- **Both curve facts from (C1), (C2), (C3).** -/
theorem curveFacts_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  ⟨curveRatFactor_of_comp h2 h3, curveSurj_of_comp h1 h2⟩

/-! ## §6 (C1) from "no isolated points" -/

/-- **(C1a) A scheme smooth of relative dimension 1 over a field has no isolated point.**
Glue (STANDARD): every point of `X` has an open neighbourhood étale over `𝔸¹_K`, so every
irreducible component of `X` has dimension 1 and every nonempty open of `X` is infinite; an open
point would be a nonempty finite open. Stated for any field `K` and any `X` (the use below is
`X = S_ℚ̄`, `K = ℚ̄`). Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def SmoothCurveNoIsolatedPoint : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, ¬ IsOpen ({x} : Set X)

/-- In a Noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      exact ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z,
        fun h => hz (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hzZ⟩ hzC
      apply hZC
      have : Z ⊆ connectedComponent z := hZ.1.isConnected.subset_connectedComponent hzZ
      rwa [← connectedComponent_eq hzC] at this
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- In a Jacobson space, a nonempty open set with finitely many closed points contains an open
point. -/
theorem exists_isOpen_singleton_of_finite_closedPoints {α : Type*} [TopologicalSpace α]
    [JacobsonSpace α] {U : Set α} (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (U ∩ closedPoints α).Finite) : ∃ z, IsOpen ({z} : Set α) := by
  classical
  set F := U ∩ closedPoints α with hF
  have hclosed : ∀ G ⊆ F, IsClosed G := by
    intro G hG
    rw [← G.biUnion_of_singleton]
    exact (hfin.subset hG).isClosed_biUnion fun w hw => mem_closedPoints_iff.mp (hG hw).2
  have hFc : IsClosed F := hclosed F le_rfl
  -- `U ⊆ F`: otherwise `U \ F` is a nonempty open with no closed point
  have hUF : U ⊆ F := by
    by_contra hsub
    obtain ⟨z, hzU, hzF⟩ := Set.not_subset.mp hsub
    obtain ⟨w, ⟨hwU, hwF⟩, hwc⟩ := nonempty_inter_closedPoints (Z := U ∩ Fᶜ)
      ⟨z, hzU, hzF⟩ (hU.inter hFc.isOpen_compl).isLocallyClosed
    exact hwF ⟨hwU, hwc⟩
  obtain ⟨z, hz⟩ := hne
  refine ⟨z, ?_⟩
  have hrest : IsClosed (F \ {z}) := hclosed _ Set.sdiff_subset
  have : ({z} : Set α) = U ∩ (F \ {z})ᶜ := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
      not_and, not_not]
    constructor
    · rintro rfl; exact ⟨hz, fun _ => rfl⟩
    · rintro ⟨hwU, h⟩; exact h (hUF hwU)
  rw [this]; exact hU.inter hrest.isOpen_compl

/-- **(C1) from (C1a).** -/
theorem geomCompInfinite_of (h : SmoothCurveNoIsolatedPoint) : GeomCompInfinite := by
  intro S hP hS y₀
  classical
  let f : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
    pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
  have : IsNoetherian (bcQbar S) := { }
  have : LocallyOfFiniteType f := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hsm : SmoothOfRelativeDimension 1 f := by
    show SmoothOfRelativeDimension 1 (pullback.snd _ _); infer_instance
  have : JacobsonSpace (bcQbar S) := LocallyOfFiniteType.jacobsonSpace f
  set x₀ := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y₀)).1 with hx₀
  -- the closed points of the component of `x₀` are infinitely many
  have hCinf : (connectedComponent x₀ ∩ closedPoints (bcQbar S)).Infinite := by
    intro hfin
    obtain ⟨z, hz⟩ := exists_isOpen_singleton_of_finite_closedPoints
      (isOpen_connectedComponent_of_noetherian x₀) ⟨x₀, mem_connectedComponent⟩ hfin
    exact h Qbar (bcQbar S) f hsm z hz
  -- each of them comes from a `ℚ̄`-point of `S` in the component
  intro hfin
  apply hCinf
  refine (hfin.image fun y => (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1).subset ?_
  rintro x ⟨hxC, hxc⟩
  let p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S := pointOfClosedPoint f x hxc
  have hp : p ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hxc
  let y : fieldPt Qbar ⟶ S := Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ f) ≫ _ = _
    rw [hp, Category.id_comp])
  have hy : bcPt y = p := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans hp.symm
  have hpt : (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 = x := by
    rw [hy]; exact pointOfClosedPoint_apply f x hxc _
  refine ⟨y, ?_, hpt⟩
  show geomComp y = geomComp y₀
  unfold geomComp
  rw [hpt, ← hx₀]
  exact (connectedComponent_eq hxC).symm

/-- **Both curve facts from (C1a), (C2), (C3).** -/
theorem curveFacts_of_named (h1 : SmoothCurveNoIsolatedPoint) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_comp (geomCompInfinite_of h1) h2 h3

/-! ## §7 C2 and C3 over an algebraically closed field (Hartshorne's setting)

The leaves C2 and C3 are restated for a proper smooth curve `X` over an arbitrary algebraically
closed field `K`, its `K`-points (sections `p : Spec K → X` of the structure map) and a connected
component of `X`. `GeomCompConstOrOnto` and `GeomCompRatFactor` follow by base change to `ℚ̄`. -/

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

/-- **(C2K) Constant or onto on a connected component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8, UNVERIFIED numbering: a morphism from a complete nonsingular curve over an
algebraically closed field to a curve is constant or surjective; here applied to a connected
component of `X`, a complete nonsingular irreducible curve, and the target `P¹`, whose closed
points are its `K`-points). Textbook leaf. -/
def ConstOrOntoAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀) ∨
      (∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t)

open Polynomial in
/-- **(C3K) Factorization on a connected component where `σ` is nonconstant**, over an
algebraically closed field of characteristic 0 (in characteristic `p` the Frobenius
`σ = ρ^p` is a counterexample). Glue (a standard consequence of textbook results, see
`docs/research/curve-facts.md` §3). -/
def RatFactorAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p₁ p₂ : Spec (CommRingCat.of K) ⟶ X, p₁ ≫ f = 𝟙 _ → p₂ ≫ f = 𝟙 _ →
        connectedComponent (ptOf p₁) = connectedComponent (ptOf p₀) →
        connectedComponent (ptOf p₂) = connectedComponent (ptOf p₀) →
        σ.val p₁ = σ.val p₂ → ρ.val p₁ = ρ.val p₂) →
      ∃ F G : K[X], IsCoprime F G ∧ ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
        σ.val p = OnePoint.some t → ρ.val p = Mob.ratEval F G t

section Dictionary

variable {S : Over (Spec (CommRingCat.of ℚ))}

/-- The structure map `S_ℚ̄ → Spec ℚ̄`. -/
abbrev bcSnd (S : Over (Spec (CommRingCat.of ℚ))) : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
  pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

theorem bcPt_snd (y : fieldPt Qbar ⟶ S) : bcPt y ≫ bcSnd S = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The `ℚ̄`-point of `S` over `ℚ` underlying a section of `S_ℚ̄ → Spec ℚ̄`. -/
def ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    fieldPt Qbar ⟶ S :=
  Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ bcSnd S) ≫ _ = _
    rw [hp, Category.id_comp])

theorem bcPt_ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    bcPt (ptOfSection p hp) = p := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans hp.symm

/-- `σ(y) = (σ ∘ pr₁)(bcPt y)`. -/
theorem val_bcPt (σ : ToP1 S.left) (y : fieldPt Qbar ⟶ S) :
    (σ.comp (pullback.fst _ _)).val (bcPt y) = σ.val (K := Qbar) y.left := by
  rw [ToP1.val_comp_right]
  exact congrArg _ (pullback.lift_fst _ _ _)

end Dictionary

/-- **C2 from C2K.** -/
theorem geomCompConstOrOnto_of (h : ConstOrOntoAlgClosed) : GeomCompConstOrOnto := by
  intro S hP hS σ y₀
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  rcases h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _)) (bcPt y₀)
    (bcPt_snd y₀) with hc | ho
  · left
    intro y hy
    rw [← val_bcPt, ← val_bcPt]
    exact hc (bcPt y) (bcPt_snd y) hy
  · right
    intro t
    obtain ⟨p, hp, hcc, hv⟩ := ho t
    refine ⟨ptOfSection p hp, ?_, ?_⟩
    · show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
      rw [bcPt_ptOfSection]; exact hcc
    · rw [← val_bcPt, bcPt_ptOfSection]; exact hv

/-- **C3 from C3K.** -/
theorem geomCompRatFactor_of (h : RatFactorAlgClosed) : GeomCompRatFactor := by
  intro S hP hS σ ρ y₀ hne hfib
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  have hcc : ∀ (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _),
      geomComp (ptOfSection p hp) = connectedComponent (ptOf p) := by
    intro p hp
    show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
    rw [bcPt_ptOfSection]
  obtain ⟨F, G, hcop, hR⟩ := h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _))
    (ρ.comp (pullback.fst _ _)) (bcPt y₀) (bcPt_snd y₀) (by
      obtain ⟨y, hy, hv⟩ := hne
      refine ⟨bcPt y, bcPt_snd y, hy, ?_⟩
      rw [val_bcPt, val_bcPt]; exact hv) (by
      intro p₁ p₂ hp₁ hp₂ h₁ h₂ hv
      have e₁ := val_bcPt σ (ptOfSection p₁ hp₁)
      have e₂ := val_bcPt σ (ptOfSection p₂ hp₂)
      have f₁ := val_bcPt ρ (ptOfSection p₁ hp₁)
      have f₂ := val_bcPt ρ (ptOfSection p₂ hp₂)
      rw [bcPt_ptOfSection] at e₁ e₂ f₁ f₂
      rw [f₁, f₂]
      refine hfib _ _ ((hcc p₁ hp₁).trans h₁) ((hcc p₂ hp₂).trans h₂) ?_
      rw [← e₁, ← e₂]; exact hv)
  refine ⟨F, G, hcop, fun y t hy ht => ?_⟩
  rw [← val_bcPt] at ht ⊢
  exact hR (bcPt y) (bcPt_snd y) hy t ht

/-- **Both curve facts from C1a, C2K, C3K** (the leaves in Hartshorne's setting). -/
theorem curveFacts_of_algClosed (h1 : SmoothCurveNoIsolatedPoint) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_named h1 (geomCompConstOrOnto_of h2) (geomCompRatFactor_of h3)

/-! ## §8 C1a from the dimension of local rings at closed points -/

/-- **(C1b) Local rings of a smooth curve at closed points have dimension 1.** If `X → Spec K`
is smooth of relative dimension 1 over a field `K` and `x` is a closed point, then
`dim 𝒪_{X,x} = 1` (STANDARD: smooth of relative dimension `n` over a field means `dim_x X = n`
at every point, and at a closed point of a scheme locally of finite type over a field
`dim 𝒪_{X,x} = dim_x X`; e.g. Stacks, *Morphisms*, smooth morphisms and dimension of fibres,
UNVERIFIED tags). Glue (dimension theory), not in Mathlib v4.35; Mathlib has
`ringKrullDim_stalk_eq_coheight` (Stacks 02IZ), used below. -/
def SmoothStalkDimOne : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = 1

/-- **C1a from C1b.** An open point is closed (Jacobson) and has no proper generalization, so its
local ring has dimension `coheight x = 0`. -/
theorem smoothCurveNoIsolatedPoint_of (h : SmoothStalkDimOne) : SmoothCurveNoIsolatedPoint := by
  intro K _ X f hf x hx
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hc : IsClosed ({x} : Set X) := isClosed_singleton_of_isLocallyClosed_singleton hx.isLocallyClosed
  have hd := h K X f hf x hc
  rw [ringKrullDim_stalk_eq_coheight] at hd
  have hmax : IsMax x := by
    intro y hxy
    have hyx : y ⤳ x := hxy
    have : y ∈ ({x} : Set X) := hyx.mem_open hx rfl
    rw [Set.mem_singleton_iff.mp this]
  rw [Order.coheight_eq_zero.mpr hmax] at hd
  exact absurd hd (by decide)

/-- **Both curve facts from C1b, C2K, C3K.** -/
theorem curveFacts_of_leaves (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_algClosed (smoothCurveNoIsolatedPoint_of h1) h2 h3

end Pin

end AV

end LeafQM

end


end G0A2_a56_curvefacts

section G0A2_a57_autoexact
/-! ## g0-assemble2: aut-o-finite §9 (scratch/aut-o-finite/AutOFinite.lean lines 794-1036, verbatim; its §7-§8 are
mobius-glue's, in part a55) -/
/-! ## §9 The explicit computation: `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes

Representatives: conjugation by `1, i, j, ij` (`rep 0, …, rep 3`). Every ring automorphism of `𝒪`
is `v · rep k · v⁻¹` for some `k` and `v ∈ 𝒪^×` (`rep_cover`), and `rep k`, `rep l` are conjugate
by a unit of `𝒪` only if `k = l` (`rep_distinct`: a conjugating unit would give
`nrd(t_k) = ± r² nrd(t_l)` with `r ∈ ℚ`, impossible as `nrd(1, i, j, ij) = 1, -2, 3, -6`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace Exact

open NormO AutOExt

/-- The reduced norm of `B = (2, -3)_ℚ`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem nrd_algebraMap (q : ℚ) : nrd (algebraMap ℚ B q) = q ^ 2 := by
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

theorem nrd_ofInt (n : Fin 4 → ℤ) : nrd (ofInt n) =
    ((n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2 : ℤ) : ℚ) := by
  simp [nrd, ofInt]; ring

theorem not_sq (s : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : s ^ 2 = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨s, by rw [← h]; ring⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

/-- An element of `B` commuting with `i` and `j` is a scalar. -/
theorem comm_scalar (w : B) (hi : w * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * w)
    (hj : w * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * w) : w = algebraMap ℚ B w.re := by
  have h1 := congrArg QuaternionAlgebra.imJ hi
  have h2 := congrArg QuaternionAlgebra.imK hi
  have h3 := congrArg QuaternionAlgebra.imI hj
  have h4 := congrArg QuaternionAlgebra.imK hj
  simp at h1 h2 h3 h4
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> linarith

/-- The norm of a unit of `𝒪` is `±1`. -/
theorem nrd_unit (v : Oˣ) : nrd ((v : O) : B) = 1 ∨ nrd ((v : O) : B) = -1 := by
  obtain ⟨n, hn⟩ := (v : O).2
  obtain ⟨m, hm⟩ := ((v⁻¹ : Oˣ) : O).2
  have h1 : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h2 := congrArg nrd h1
  rw [nrd_mul, hn, hm, nrd_ofInt, nrd_ofInt] at h2
  have h3 : nrd 1 = 1 := by simp [nrd]
  rw [h3] at h2
  have h4 := Int.eq_one_or_neg_one_of_mul_eq_one (by exact_mod_cast h2)
  rw [hn, nrd_ofInt]
  rcases h4 with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem isNorm_one : IsNorm 1 := by
  intro a ha
  exact ⟨by simpa using ha, by simpa using ha⟩

/-- Conjugation `a ↦ u a u⁻¹` by a unit `u ∈ B^×` normalizing `𝒪`, as a ring automorphism. -/
def conjO (u : Bˣ) (hu : IsNorm u) : O ≃+* O where
  toFun a := ⟨(u : B) * a * ((u⁻¹ : Bˣ) : B), (hu a a.2).1⟩
  invFun a := ⟨((u⁻¹ : Bˣ) : B) * a * u, (hu a a.2).2⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]
  map_add' a b := by apply Subtype.ext; simp [mul_add, add_mul]

theorem conjO_apply (u : Bˣ) (hu : IsNorm u) (a : O) :
    ((conjO u hu a : O) : B) = (u : B) * a * ((u⁻¹ : Bˣ) : B) := rfl

/-- The representatives `1, i, j, ij` of `N(𝒪)/ℚ^×𝒪^×`. -/
def tt : Fin 4 → Bˣ := ![1, ui, uj, ui * uj]

theorem tt_isNorm (k : Fin 4) : IsNorm (tt k) := by
  fin_cases k
  exacts [isNorm_one, isNorm_ui, isNorm_uj, isNorm_ui.mul isNorm_uj]

/-- The four representatives of `Aut(𝒪)/Inn(𝒪^×)`: conjugation by `1, i, j, ij`. -/
def rep (k : Fin 4) : O ≃+* O := conjO (tt k) (tt_isNorm k)

/-- The reduced norms `1, -2, 3, -6` of `1, i, j, ij`. -/
def N : Fin 4 → ℤ := ![1, -2, 3, -6]

theorem nrd_tt (k : Fin 4) : nrd (tt k : B) = (N k : ℚ) := by
  fin_cases k
  · simp [tt, N, nrd]
  · change nrd (ofInt ei) = _
    simp [nrd_ofInt, ei, N]
  · change nrd (ofInt ej) = _
    simp [nrd_ofInt, ej, N]
  · change nrd (ofInt ei * ofInt ej) = _
    rw [nrd_mul]
    simp [nrd_ofInt, ei, ej, N]; norm_num

theorem tt_of_T (t : Bˣ) (ht : t ∈ T) : ∃ k, tt k = t := by
  rcases (T_mem_iff t).1 ht with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The concrete normalizer statement (the body of `NormO.normalizerFinite`, with `T` named). -/
theorem normalizer_rep (u : Bˣ) (hu : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) :
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B) := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem key2 {R : Type*} [Ring R] (x y w w' c c' t t' : R) (hww : w * w' = 1)
    (hcc : c' * c = 1) (htt : t * t' = 1) (hc : c * x = x * c)
    (h : x * (c * w * t) = c * w * t * y) : x = w * (t * y * t') * w' := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc x = x * (w * (t * t') * w') := by rw [htt, mul_one, hww, mul_one]
    _ = x * w * t * t' * w' := by simp only [mul_assoc]
    _ = w * t * y * t' * w' := by rw [h1]
    _ = w * (t * y * t') * w' := by simp only [mul_assoc]

/-- **Every automorphism of `𝒪` is `v · rep k · v⁻¹`** for some `k` and some `v ∈ 𝒪^×`. -/
theorem rep_cover (α : O ≃+* O) : ∃ k : Fin 4, ∃ v : Oˣ, ∀ a : O,
    α a = (v : O) * rep k a * ((v⁻¹ : Oˣ) : O) := by
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := normalizer_rep u hnorm
  obtain ⟨k, rfl⟩ := tt_of_T t ht
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  refine ⟨k, v, fun a => Subtype.ext ?_⟩
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  change _ = ((v : O) : B) * ((tt k : B) * a * (((tt k)⁻¹ : Bˣ) : B)) * (((v⁻¹ : Oˣ) : O) : B)
  have hvv : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have h := hrel a
  rw [huq] at h
  exact key2 _ _ _ _ _ _ _ _ hvv hcc (Units.mul_inv _) (Algebra.commutes q _) h

/-- **The four representatives are pairwise non-conjugate by units of `𝒪`.** -/
theorem rep_distinct (k l : Fin 4) (v : Oˣ)
    (h : ∀ a : O, rep k a = (v : O) * rep l a * ((v⁻¹ : Oˣ) : O)) : k = l := by
  set V : B := ((v : O) : B) with hVdef
  set V' : B := (((v⁻¹ : Oˣ) : O) : B) with hV'def
  have hVV' : V * V' = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hV'V : V' * V = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.inv_mul]; rfl
  have hV'Vx : ∀ X : B, V' * (V * X) = X := fun X => by rw [← mul_assoc, hV'V, one_mul]
  set P : B := (tt k : B) with hP
  set P' : B := (((tt k)⁻¹ : Bˣ) : B) with hP'
  set Q : B := (tt l : B) with hQ
  set Q' : B := (((tt l)⁻¹ : Bˣ) : B) with hQ'
  have hP'P : P' * P = 1 := Units.inv_mul _
  have hQ'Qx : ∀ X : B, Q' * (Q * X) = X := fun X => by
    rw [← mul_assoc, show Q' * Q = 1 from Units.inv_mul _, one_mul]
  have hQQ'x : ∀ X : B, Q * (Q' * X) = X := fun X => by
    rw [← mul_assoc, show Q * Q' = 1 from Units.mul_inv _, one_mul]
  have hVV'x : ∀ X : B, V * (V' * X) = X := fun X => by rw [← mul_assoc, hVV', one_mul]
  have hcomm : ∀ a ∈ O, (Q' * V' * P) * a = a * (Q' * V' * P) := by
    intro a ha
    have e : P * a * P' = V * (Q * a * Q') * V' := by
      have := congrArg Subtype.val (h ⟨a, ha⟩)
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul] at this
      exact this
    calc Q' * V' * P * a = Q' * V' * (P * a * P') * P := by
          simp only [mul_assoc, hP'P, mul_one]
      _ = Q' * V' * (V * (Q * a * Q') * V') * P := by rw [e]
      _ = a * (Q' * V' * P) := by simp only [mul_assoc, hV'Vx, hQ'Qx]
  set W := Q' * V' * P with hW
  have hWs : W = algebraMap ℚ B W.re :=
    comm_scalar W (hcomm _ (mem_O_of_int 0 1 0 0)) (hcomm _ (mem_O_of_int 0 0 1 0))
  have hPW : P = V * Q * W := by
    rw [hW]; simp only [mul_assoc, hQQ'x, hVV'x]
  have e1 : (N k : ℚ) = nrd V * N l * W.re ^ 2 := by
    rw [← nrd_tt, ← nrd_tt, ← nrd_algebraMap, ← hWs, ← nrd_mul, ← nrd_mul]
    exact congrArg nrd hPW
  have hmain : ∀ ε : ℤ, nrd V = ε → ε ^ 2 = 1 →
      (W.re * N l) ^ 2 = ((ε * N k * N l : ℤ) : ℚ) := by
    intro ε hε hε2
    have hε2' : (ε : ℚ) ^ 2 = 1 := by exact_mod_cast hε2
    push_cast
    rw [e1, hε]
    linear_combination (-(W.re ^ 2 * (N l : ℚ) ^ 2)) * hε2'
  rcases nrd_unit v with h1 | h1
  · have hm := hmain 1 (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim
  · have hm := hmain (-1) (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim

/-- **Explicit computation of `Aut(𝒪)/Inn(𝒪^×)`: exactly four classes**, represented by
conjugation by `1, i, j, ij`. -/
theorem autO_mod_inner_exact : ∃ t : Fin 4 → (O ≃+* O),
    (∀ α : O ≃+* O, ∃ k, ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t k a * ((v⁻¹ : Oˣ) : O)) ∧
    ∀ k l, (∃ v : Oˣ, ∀ a : O, t k a = (v : O) * t l a * ((v⁻¹ : Oˣ) : O)) → k = l :=
  ⟨rep, rep_cover, fun k l ⟨v, hv⟩ => rep_distinct k l v hv⟩

/-- `AutOInnerFinite` again, from the explicit computation. -/
theorem autOInnerFinite' : AutOInnerFinite := by
  refine ⟨Set.range rep, Set.finite_range rep, fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := rep_cover α
  exact ⟨rep k, ⟨k, rfl⟩, v, hv⟩

end Exact

end Pin

end AV

end LeafQM

end G0A2_a57_autoexact

section G0A2_a60_fs5
/-! ## g0-assemble2: fs5-nocm (scratch/fs5-nocm/partB, partD, partE, partG, partH, partI, verbatim except three
edits forced by pin-apply, which made Leaves.lean's `R1fpProps` the repaired six-clause list (=`R1fpPropsFull`,
same text): `R1fpPropsFull.old` is now `h` itself; in `fibreComTrivialFull_of_own` the conversions
`(r1fpPropsFull_iff _ _).1` to mobius-glue's `R1fpPropsU` are dropped, since Leaves.lean's
`pointwise_of_witness_mor` takes `R1fpProps`. The qm-pin copies of its FS5NoCM.lean are Leaves.lean's.) -/
noncomputable section

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin ZInQ ZInQ.JHeight PkgI3

/-! ## §B The statement -/

/-- **FS5 as stated by g0-fibresimple** (verbatim from `scratch/g0-fibresimple/FibreSimple.lean`,
`HSyn.G0Split.FibreComTrivial`, with the old `R1fpProps`; kept for reference: g0-fibresimple §2
shows that the old clause list does not pin `Φ`, so this form is not a consequence of the leaves).

**Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- **`R1fpProps` after qm-pin's full edit** (text of `scratch/qm-pin/QM-Leaves-full.patch`,
lines 63-70: the four old clauses, `R1famProps` and `R1univProps`). After the integration this is
`LeafQM.AV.R1fpProps`. -/
def R1fpPropsFull (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ ∧ R1univProps Y Φ

theorem r1fpPropsFull_iff (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    R1fpPropsFull Y Φ ↔ R1fpPropsU Y Φ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d, e⟩, f⟩, fun ⟨⟨a, b, c, d, e⟩, f⟩ => ⟨a, b, c, d, e, f⟩⟩

theorem R1fpPropsFull.old {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsFull Y Φ) : R1fpProps Y Φ := h

/-- **FS5 with the repaired QM clauses** (the statement this task proves): `FibreComTrivial`
verbatim, with `R1fpProps` read as after qm-pin's full edit (`R1fpPropsFull`). -/
def FibreComTrivialFull : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpPropsFull Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- The clause list of the leaf bundle `LeafQM.AV.R1R2fp` on one witness, with `R1fpProps` as
after qm-pin's full edit. -/
def R1R2fpFullProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left) : Prop :=
  R1fpPropsFull Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
    CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- **The leaf bundle `LeafQM.AV.R1R2fp` after qm-pin's full edit** (same text, `R1fpProps`
repaired). -/
def R1R2fpFull : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆

theorem R1R2fp_of_full (h : R1R2fpFull) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, h⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1.old, h⟩

/-- **FS5 for the leaf's own triple** (the restatement that qm-pin's `pointwise_of_witness_mor`
allows): for every witness `(Y, Φ, X, Ψ, fY, π₆)` of the repaired leaf bundle, the objects over
`J(u)`, `u ∉ 𝒞`, of the triple `(Y, Φ, π₆ ∘ fY)` have `End_𝒪 = ℤ`. Quantified over all witnesses
(not a `Classical.choice` of one), so it is a statement about the published data, not about a
choice. -/
def FibreComTrivialOwn : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (π₆.comp fY.left).val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)

/-! ## §C The named Props NoCM needs -/

/-- **NoCM input N1a (glue; G5-G6, rv-h-cm §7.2 "the CM order"): `End_𝒪(A)` is `ℤ` or an order in
an imaginary quadratic field.** For a QM pair `(A, ι)` over `ℚ̄`, either every element of the
centralizer `com ι = End_𝒪(A)` is an integer, or `com ι` is isomorphic to a subring `R` of the
ring of integers of an imaginary quadratic field `k`, of finite index (`conductor R ≠ 0`).
*Why true* (STANDARD): by Yu's dichotomy (leaf T27, `PkgI3.QMDichotomyYu`, in characteristic 0)
`End⁰(A) ≅ B` or `≅ M₂(k)` with `k` imaginary quadratic; the centralizer of `B` is `ℚ`, resp. the
centre `k` (FS4's argument, `centralizerOfMatrixEnd0_of_homFree`); `com ι = End(A) ∩ com⁰` is a
finitely generated (T6) subring of `ℚ`, resp. of `k`, of rank 1, resp. 2, and integral over `ℤ`,
hence `ℤ`, resp. an order of `k`. Glue; **proved** from T27 and T6 in §G-§H
(`comIntOrQuadOrder_of_leaves`). -/
def ComIntOrQuadOrder : Prop :=
  ∀ P : QMPair Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com P.q ≃+* R)

/-- **NoCM input N1b (leaf; "(Emb)" of rv-h-cm §7.2 and rv-nocm §1.2): the CM order has conductor
prime to 6.** If `End_𝒪(A) ≅ R` for an order `R` of an imaginary quadratic field `k`, then the
conductor of `R` is prime to `6 = disc B`.
*Published statement*: the CM points of `X₀(D, 1)` by `R` correspond to optimal embeddings
`R ↪ 𝒪` (Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5;
locators UNVERIFIED), and an order of conductor `f` embeds optimally in the maximal order of the
quaternion division algebra over `ℚ_p` only if `p ∤ f` and `p` does not split in `k` (Vignéras,
*Arithmétique des algèbres de quaternions*, LNM 800, Ch. II §3 / Ch. III §5, theorem numbers
UNVERIFIED; for `p ∤ f`: `k ∩ 𝒪_p = 𝒪_{k,p}` because `𝒪_p` is the set of integral elements).
A consequence of the published statements (only the conductor half is kept). **Proved** in §I
from the leaf `CMOptimalEmbedding` (Shimura's description of CM points), `cmConductorCoprime6_of`. -/
def CMConductorCoprime6 : Prop :=
  ∀ (P : QMPair Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      conductor R ≠ 0 → Nonempty (com P.q ≃+* R) → Nat.Coprime (conductor R) 6

/-- **NoCM input N2 (glue; the Kummer model of `X₆ → X₆/W ≅ P¹`, rv-h-cm §2.3-2.4,
`GlueRepo.PR.fibre_iff`).** On the leaf bundle's `X₆`, for a rational value `j₀ ∉ {0, −16/27}`
of `π₆` (so `t₀ = 1 + 27 j₀/16 ∉ {0, 1, ∞}`):
(i) every `ℚ̄`-point `x` over `j₀` has residue field `ℚ(x) = ℚ(a, b)` for any `a, b ∈ ℚ̄` with
`a² = −t₀`, `b² = 3(t₀ − 1)`;
(ii) the fibre over `j₀` has (at least) four distinct `ℚ̄`-points.
*Why true* (argued; Elkies, "Shimura curve computations", ANTS-III, LNCS 1423 (1998), the curve
`X*(6)` and its double covers (section number UNVERIFIED); the constants `c₀ = −1`, `c₁ = 3` are
derived in rv-h-cm §2.3 and checked against González–Rotger Thm 5.12 on all 24 rows of Elkies'
table, rv-nocm §1.3 Part B (VERIFIED there)): `ℚ(X₆) = ℚ(t)(y₁, y₂)`, `y₁² = −t`,
`y₂² = 3(t − 1)`, with `W ≅ (ℤ/2)²` acting by the sign changes; the affine model is smooth over
`t ∉ {0, 1, ∞}`, so the points over `t₀` are `(t₀, ±a, ±b)` (four, as `ab ≠ 0`) with residue field
generated by their coordinates. On an arbitrary witness of the bundle the statement is the same
statement, transported: with the repaired `R1fpProps` the witness `Y` maps to the genuine `Y₃`
with `Φ = Φ₃ ∘ g`, `π = π₃ ∘ g` (qm-pin `phi_part`, mobius-glue), `fY` is onto `X(ℚ̄)` (`X6Surj`),
`Ψ(fY y) = [forget (Φ y)]` (`X6Props`), and a residue field is the fixed field of the Galois
stabilizer of the point, which `Ψ` matches with the stabilizer of the pair (Galois-equivariance in
`X6Props`). Glue: geometry of an explicit curve plus the identification (not compiled). -/
def X6KummerFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)


/-! ## §D Arithmetic -/

/-- In a number field containing a square root `ι` of `−1`, the prime `2` is not inert:
`(1 + ι)² = 2ι ∈ (2)` but `(1 + ι)/2` is not integral (its fourth power is `−1/4`). -/
theorem two_not_prime_of_sqrt_neg_one {k : Type} [Field k] [NumberField k] (ι : k)
    (hι : ι ^ 2 = -1) : ¬ (Ideal.span {(2 : NumberField.RingOfIntegers k)}).IsPrime := by
  intro hP
  have hint : IsIntegral ℤ ι := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).add_of_left
        (by rw [Polynomial.degree_one, Polynomial.degree_X_pow]; norm_num)
    · simp [hι]
  let ιO : NumberField.RingOfIntegers k := ⟨ι, hint⟩
  have hsq : (1 + ιO) ^ 2 = 2 * ιO := by
    apply NumberField.RingOfIntegers.ext
    simp only [map_pow, map_add, map_one, map_mul, map_ofNat]
    change (1 + ι) ^ 2 = 2 * ι
    linear_combination hι
  have hmem : (1 + ιO) ^ 2 ∈ Ideal.span {(2 : NumberField.RingOfIntegers k)} := by
    rw [hsq]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hP.mem_of_pow_mem 2 hmem)
  have hck : (c : k) * 2 = 1 + ι := congrArg (fun z : NumberField.RingOfIntegers k => (z : k)) hc
  have h4 : (c : k) ^ 4 = algebraMap ℚ k (-1 / 4) := by
    have : (c : k) ^ 4 = -1 / 4 := by
      linear_combination (1 / 16 : k) * ((c * 2) ^ 3 + (c * 2) ^ 2 * (1 + ι) +
        (c * 2) * (1 + ι) ^ 2 + (1 + ι) ^ 3) * hck + (1 / 16 : k) * (ι ^ 2 + 4 * ι + 5) * hι
    rw [this]; simp
  have hI : IsIntegral ℤ (algebraMap ℚ k (-1 / 4)) := by
    rw [← h4]; exact (NumberField.RingOfIntegers.isIntegral_coe c).pow 4
  have hI' : IsIntegral ℤ (-1 / 4 : ℚ) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
      (algebraMap ℚ k).injective).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  have : (n : ℚ) * 4 = -1 := by
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]; norm_num
  have : n * 4 = -1 := by exact_mod_cast this
  omega

/-- `[ℚ(i) : ℚ] = 2` inside `ℚ̄`. -/
theorem finrank_adjoin_sqrt_neg_one (i : Qbar) (hi : i ^ 2 = -1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) = 2 := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])
  have hmp : minpoly ℚ i = Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ?_).symm
    · simp [hi]
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hint : IsIntegral ℚ i := Algebra.IsIntegral.isIntegral i
  rw [IntermediateField.adjoin.finrank hint, hmp, Polynomial.natDegree_X_pow_sub_C]

/-- `ℚ(i h₁, i h₂) = ℚ(i)` for rational `h₁ ≠ 0`, `h₂`. -/
theorem adjoin_pair_eq (i : Qbar) (h₁ h₂ : ℚ) (hh : h₁ ≠ 0) :
    IntermediateField.adjoin ℚ {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} =
      IntermediateField.adjoin ℚ {i} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl <;>
      exact mul_mem (IntermediateField.mem_adjoin_simple_self ℚ i)
        (IntermediateField.algebraMap_mem _ _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h0 : algebraMap ℚ Qbar h₁ ≠ 0 := by simpa using hh
    have hm : i * algebraMap ℚ Qbar h₁ ∈ IntermediateField.adjoin ℚ
        {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    have := mul_mem hm (IntermediateField.algebraMap_mem _ (h₁⁻¹))
    rwa [map_inv₀, mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

/-- The Elkies identities at `t(u)` (`GlueRepo.PR.t_eq`, `t_sub_one`), in `ℚ̄`: with `i² = −1`,
`(i H/G³)² = −t(u)` and `(i·540F/G³)² = 3(t(u) − 1)`, `t(u) = 1 + 27 J(u)/16`. -/
theorem elkies_sq (u : ℚ) (i : Qbar) (hi : i ^ 2 = -1) :
    (i * algebraMap ℚ Qbar (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        -algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) ∧
      (i * algebraMap ℚ Qbar (540 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        3 * (algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1) := by
  have ht : (1 + 27 * Jmap u / 16 : ℚ) = (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := by
    rw [div_pow, ← pow_mul]; exact GlueRepo.PR.t_eq u
  have ht1 : (1 + 27 * Jmap u / 16 : ℚ) - 1 =
      -3 * (180 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := GlueRepo.PR.t_sub_one u
  constructor
  · rw [ht, mul_pow, hi, map_pow]; ring
  · have e : algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1 =
        algebraMap ℚ Qbar ((1 + 27 * Jmap u / 16 : ℚ) - 1) := by rw [map_sub, map_one]
    rw [e, ht1, mul_pow, hi]
    simp only [map_mul, map_pow, map_neg, map_div₀, map_ofNat]
    ring


/-! ## §E NoCM on the leaf's own witness, and FS5 -/

/-- **NoCM on the leaf bundle's witness** (rv-h-cm §7.2 with the corrected count of rv-nocm §1.1).
Let `y` be a `ℚ̄`-point of the witness `Y` over `J(u)`, `u ∉ 𝒞`, with object `P`, and
`x = fY(y) ∈ X₆`. If `End_𝒪(P.A) ≅ R` were an order of an imaginary quadratic `k` (N1a), its
conductor is prime to 6 (N1b). The residue field of `x` is `ℚ(i)` (N2 (i) with the Elkies
identities), so R5 (`R5ptProps`) gives `2 = h(R)` if `b(k) = 0`, and `2 = 2h(R)` with
`k ↪ ℚ(i)` if `b(k) ≥ 1`; in the second case `k ≅ ℚ(i)`, where `2` ramifies, so `b(k) = 1`.
Either way `#CM(R) = 2^{b(k)} h(R) = 2` (R5fpCount). But the four points of the fibre over
`J(u)` (N2 (ii)) are pairwise distinct points of `X₆`, hence (`Ψ` bijective) four distinct
classes, and each is an `Aut(𝒪)`-twist of `P` (`R2X6Props`), hence CM by `R` (`com_twist`,
`comEquiv`): `#CM(R) ≥ 4`. Contradiction; so `End_𝒪(P.A) = ℤ`. -/
theorem nocm_on_witness (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hW : R1R2fpFullProps Y Φ X Ψ fY π₆)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar)
    (hP : Φ Qbar y = M3.mk P)
    (hv : (π₆.comp fY.left).val (K := Qbar) y.left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A) := by
  obtain ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ := hW
  have hx : Ψ (y ≫ fY) = Quotient.mk _ P.forget := hX.2.2.2.2.2 y P hP
  have hv' : π₆.val (K := Qbar) (y ≫ fY).left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u)) := by
    exact (ToP1.val_comp_right π₆ fY.left y.left).symm.trans hv
  rcases hA P.forget with hZ | ⟨k, _, _, _, hk2, R, hR, hc0, ⟨e⟩⟩
  · exact hZ
  exfalso
  have hcop : Nat.Coprime (conductor R) 6 := hB P.forget k hk2 R hR hc0 ⟨e⟩
  obtain ⟨hdeg, hemb⟩ := h5 k hk2 R hR hcop (y ≫ fY) P.forget hx ⟨e⟩
  -- the fibre over `J(u)` (N2) and its residue field `ℚ(i)`
  obtain ⟨hres, f, hf, hfv⟩ := hK Y Φ X Ψ fY π₆ ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ (Jmap u)
    (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos
  obtain ⟨ha, hb⟩ := elkies_sq u i hi
  have hresEq : residueImage (X := X.left) (y ≫ fY).left = IntermediateField.adjoin ℚ {i} := by
    rw [hres _ hv' _ _ ha hb]
    exact adjoin_pair_eq i _ _ (GlueRepo.PR.h₁_ne_zero u)
  have hfin : Module.finrank ℚ (residueImage (X := X.left) (y ≫ fY).left) = 2 := by
    rw [hresEq]; exact finrank_adjoin_sqrt_neg_one i hi
  rw [hfin] at hdeg
  -- four distinct classes with CM by `R`
  have hcount := hC k hk2 R hR hcop ⟨P.forget, ⟨e⟩⟩
  have hmemS : ∀ j : Fin 4, ∃ P' : QMPair Qbar, Quotient.mk _ P' = Ψ (f j) ∧
      Nonempty (com P'.q ≃+* R) := by
    intro j
    refine ⟨Quotient.out (Ψ (f j)), Quotient.out_eq _, ?_⟩
    have hQ : Ψ (f j) = Quotient.mk _ (Quotient.out (Ψ (f j))) := (Quotient.out_eq _).symm
    obtain ⟨α, ⟨g⟩⟩ := ((h2 (y ≫ fY) (f j) P.forget _ hx hQ).1).1 (hv'.trans (hfv j).symm)
    exact ⟨((comEquiv g).symm.trans (RingEquiv.subringCongr (com_twist P.forget.q α))).trans e⟩
  let F : Fin 4 → {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    fun j => ⟨Ψ (f j), hmemS j⟩
  have hFinj : Function.Injective F := fun a b hab =>
    hf (Ψ.injective (congrArg Subtype.val hab))
  -- `#CM(R) = 2`
  have hcard2 : Nat.card {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} = 2 := by
    rw [hcount]
    by_cases hb0 : inertCount6 k = 0
    · simp only [hb0, ↓reduceIte] at hdeg
      rw [hb0]; omega
    · simp only [hb0, ↓reduceIte] at hdeg
      have hh1 : Nat.card (CommRing.Pic R) = 1 := by omega
      obtain ⟨e'⟩ := hemb hb0
      have hik : i ∈ residueImage (X := X.left) (y ≫ fY).left := by
        rw [hresEq]; exact IntermediateField.mem_adjoin_simple_self ℚ i
      have : FiniteDimensional ℚ (residueImage (X := X.left) (y ≫ fY).left) :=
        Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
      have hsurj : Function.Surjective e'.toLinearMap := by
        rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hk2, hfin])]
        exact e'.toRingHom.injective
      obtain ⟨ι, hι⟩ := hsurj ⟨i, hik⟩
      have hι2 : ι ^ 2 = -1 := by
        apply e'.toRingHom.injective
        change e' (ι ^ 2) = e' (-1)
        rw [map_pow, map_neg, map_one]
        have : e' ι = ⟨i, hik⟩ := hι
        rw [this]
        apply Subtype.ext
        simp [hi]
      have h2n := two_not_prime_of_sqrt_neg_one ι hι2
      have hb1 : inertCount6 k = 1 := by
        have : inertCount6 k ≤ 1 := by
          unfold inertCount6
          simp only [h2n, ↓reduceIte]
          split_ifs <;> omega
        omega
      rw [hb1, hh1]; norm_num
  have hfinS : Finite {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; norm_num)
  have := Nat.card_le_card_of_injective F hFinj
  rw [hcard2, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **FS5 for the leaf's own triple, from NoCM's inputs.** -/
theorem fibreComTrivialOwn_of (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialOwn :=
  fun _ _ _ _ _ _ hW u hu y P hP hv => nocm_on_witness hA hB hK hC hW u hu y P hP hv

/-- **From the leaf's own triple to every triple** (qm-pin's `pointwise_of_witness_mor`, with
`MobiusGlue` and the CM objects of the bundle, `cm_objects_of_R1R2fp`). -/
theorem fibreComTrivialFull_of_own (hL : R1R2fpFull) (hM : MobiusGlue)
    (hO : FibreComTrivialOwn) : FibreComTrivialFull := by
  obtain ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩ := hL
  have hCM := cm_objects_of_R1R2fp (R1R2fp_of_full ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩)
  have h1 : R1fpProps Y₀ Φ₀ := hW.1
  have h2 : R2fpProps Y₀ Φ₀ (π₆.comp fY.left) := R2fpProps_of_X6 hW.2.2.1 hW.2.2.2.1
  have key := pointwise_of_witness_mor hM hCM h1 h2
    (fun t P => ∀ u : ℚ, u ∉ contactSet → t = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A))
    (fun t y P hP ht u hu htu => hO Y₀ Φ₀ X Ψ fY π₆ hW u hu y P hP (ht.trans htu))
  intro Y Φ π h1' h2' u hu y P hP hv
  exact key Y Φ π h1' h2' _ y P hP hv u hu rfl

/-- **FS5 with the repaired QM clauses, proved** from the leaf bundle (after qm-pin's full edit),
`MobiusGlue` (proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and T5), N1a, N1b, N2 and
the leaf R5fpCount. -/
theorem fibreComTrivialFull_of (hL : R1R2fpFull) (hM : MobiusGlue) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) :
    FibreComTrivialFull :=
  fibreComTrivialFull_of_own hL hM (fibreComTrivialOwn_of hA hB hK hC)

end FS5NoCM


/-! ## §G N1a split: the case `End⁰(A) ≅ B` proved from T6; the CM case named

The block from `B6_isUnit` to `qm_embeds_end0` is copied verbatim from
`scratch/g0-fibresimple/olean/Tail.lean` (lines 40-116, proved there). -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩

/-- The centre of `B = ℍ[ℚ, 2, -3]` is `ℚ`. -/
theorem B6_central_eq (z : ℍ[ℚ, 2, -3]) (hz : ∀ y : ℍ[ℚ, 2, -3], z * y = y * z) :
    z = algebraMap ℚ _ z.re := by
  have hi := hz ⟨0, 1, 0, 0⟩
  have hj := hz ⟨0, 0, 1, 0⟩
  have hi2 := congrArg QuaternionAlgebra.imJ hi
  have hi3 := congrArg QuaternionAlgebra.imK hi
  have hj1 := congrArg QuaternionAlgebra.imI hj
  have hj3 := congrArg QuaternionAlgebra.imK hj
  simp at hi2 hi3 hj1 hj3
  ext <;> simp <;> linarith

/-- `m ↦ 1 ⊗ m`, `End(A) → End⁰(A)`, is injective when `End(A)` is a free `ℤ`-module (T6). -/
theorem tmul_one_injective {k : Type} [Field k] {A : PkgI3.AbVar k}
    (hfree : Module.Free ℤ (PkgI3.AbVar.End A)) (m : PkgI3.AbVar.End A)
    (hm : (1 : ℚ) ⊗ₜ[ℤ] m = 0) : m = 0 := by
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
  rw [Submonoid.smul_def] at hs'
  exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')

/-- **N1a, case `End⁰(A) ≅ B` (proved from T6).** If `End⁰(A) ≅ ℍ[ℚ, 2, -3]` for an abelian
variety with a QM structure `q`, then every element of `com q = End_𝒪(A)` is an integer: `1 ⊗ φ`
commutes with the image of `B`, which is all of `End⁰(A)` (an injective map of 4-dimensional
`ℚ`-spaces), so it is a rational scalar `c` (`B6_central_eq`); `φ` is integral over `ℤ` (`End(A)`
is a finitely generated `ℤ`-module, T6), hence so is `c`, so `c ∈ ℤ`; and `m ↦ 1 ⊗ m` is
injective (T6). -/
theorem com_int_of_end0_quat (hHF : PkgI3.HomFreeFinite) {k : Type} [Field k]
    {A : PkgI3.AbVar k} (q : QMStr A) (e : PkgI3.AbVar.End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) :
    ∀ φ ∈ com q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End A) := by
  intro φ hφ
  obtain ⟨hfree, hfin, -, -⟩ := hHF k A A
  let L : ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A := (qmBasis q).liftHom
  have : Nontrivial (PkgI3.AbVar.End0 A) := e.toRingEquiv.nontrivial
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have := (B6_isUnit b hb0).map L
    rw [hb] at this
    exact not_isUnit_zero this
  have : FiniteDimensional ℚ (PkgI3.AbVar.End0 A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hLsurj : Function.Surjective L.toLinearMap := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, e.toLinearEquiv.finrank_eq,
        QuaternionAlgebra.finrank_eq_four])]
    exact hLinj
  set x : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] φ with hx
  have e1 : ∀ a b : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hcomm_g : ∀ a : LeafQM.O, Commute x ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hφ
    have h := hφ (q.iota a) ⟨a, rfl⟩
    show x * _ = _ * x
    rw [hx, ← e1, ← e1, h]
  have hcomm : ∀ y : PkgI3.AbVar.End0 A, x * y = y * x := by
    intro y
    obtain ⟨b, rfl⟩ := hLsurj y
    change Commute x ((qmBasis q).lift b)
    simp only [QuaternionAlgebra.Basis.lift]
    have h0 : Commute x (algebraMap ℚ (PkgI3.AbVar.End0 A) b.re) := (Algebra.commutes _ _).symm
    exact ((h0.add_right ((hcomm_g oi).smul_right _)).add_right
      ((hcomm_g oj).smul_right _)).add_right (((hcomm_g oi).mul_right (hcomm_g oj)).smul_right _)
  -- `x` is a rational scalar
  have hex : e x = algebraMap ℚ _ (e x).re := by
    apply B6_central_eq
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hcomm]
  set c : ℚ := (e x).re
  have hxc : x = algebraMap ℚ _ c := by
    apply e.injective; rw [hex, AlgEquiv.commutes]
  -- `c` is an integer
  have hint : IsIntegral ℤ φ := Algebra.IsIntegral.isIntegral φ
  obtain ⟨p, hpm, hp⟩ := hint
  have hpc : Polynomial.aeval c p = 0 := by
    have h1 : Polynomial.aeval x p = 0 := by
      have := Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A)
        φ p
      rw [← Polynomial.aeval_def] at hp
      rw [hp, map_zero] at this
      exact this
    rw [hxc, Polynomial.aeval_algebraMap_apply] at h1
    exact (algebraMap ℚ (PkgI3.AbVar.End0 A)).injective (h1.trans (map_zero _).symm)
  have hcint : IsIntegral ℤ c := ⟨p, hpm, by rw [← Polynomial.aeval_def]; exact hpc⟩
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
  refine ⟨n, sub_eq_zero.mp (tmul_one_injective hfree _ ?_)⟩
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] (n : PkgI3.AbVar.End A) = (n : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
  have h2 : algebraMap ℚ (PkgI3.AbVar.End0 A) c = (n : PkgI3.AbVar.End0 A) := by
    rw [← hn, show algebraMap ℤ ℚ n = (n : ℚ) from rfl, map_intCast]
  rw [TensorProduct.tmul_sub, ← hx, hxc, h1, h2, sub_self]


/-- **N1a-CM (glue; G6, the CM case of Yu's dichotomy): the CM order.** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for a QM abelian surface `(A, ι)` over `ℚ̄`, then
`com ι = End_𝒪(A)` is isomorphic to a subring of finite index of `𝒪_k`, `k` imaginary quadratic.
*Why true* (STANDARD linear algebra; Shimura): `B ⊗ ℚ(√d) ≅ M₂(ℚ(√d))` (`B ⊗ k` is central simple
of `k`-dimension 4 and maps to `M₂(k)`), so the centralizer of `B` in `End⁰(A)` is the centre
`k = ℚ(√d)`; `com ι = End(A) ∩ k` is a finitely generated `ℤ`-module (T6) of integral elements
(`End(A)` is finite over `ℤ`), containing `ℤ` and a non-integer `n√d` (FS4,
`centralizerOfMatrixEnd0_of_homFree`), hence a subring of finite index of `𝒪_k`. Glue;
**proved** from T6 in §H (`comOfMatrixEnd0_of_homFree`). -/
def ComOfMatrixEnd0 : Prop :=
  ∀ (A : AbVar Qbar) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com q ≃+* R)

/-- **N1a from T27 (Yu), T6 and N1a-CM.** -/
theorem comIntOrQuadOrder_of (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite)
    (hCM : ComOfMatrixEnd0) : ComIntOrQuadOrder := by
  intro P
  rcases PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q) with
    he | ⟨d, hd, hM⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (com_int_of_end0_quat t6 P.q e)
  · exact Or.inr (hCM P.A P.q d hd hM)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 (in `TextbookLeaves`), N1b, and the glue `MobiusGlue`, N1a-CM, N2. -/
theorem fibreComTrivialFull_of_leaves (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hCM : ComOfMatrixEnd0)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of t27 t6 hCM) hB hK hC

end FS5NoCM


/-! ## §H N1a-CM proved from T6 (`End_𝒪(A)` is an order of `ℚ(√d)` when `End⁰(A) ≅ M₂(ℚ(√d))`) -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

section LinAlg

variable {K : Type} [Field K]

local notation "M2" => Matrix (Fin 2) (Fin 2) K

theorem quat_comm_I (I J : M2) (hI : I * I = (2 : K) • 1) (hJI : J * I = -(I * J))
    (a b c d : K) :
    I * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * I =
      (2 * c) • (I * J) + (4 * d) • J := by
  have r1 : I * (I * J) = (2 : K) • J := by rw [← mul_assoc, hI, smul_mul_assoc, one_mul]
  have r2 : (I * J) * I = -((2 : K) • J) := by
    rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hI, smul_mul_assoc, one_mul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hI, r1, r2, hJI]
  module

theorem quat_comm_J (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (a b c d : K) :
    J * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * J =
      (-2 * b) • (I * J) + (6 * d) • I := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have r4 : J * (I * J) = (3 : K) • I := by
    rw [← mul_assoc, hJI, neg_mul, mul_assoc, hJ, mul_smul_comm, mul_one, neg_smul]; module
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJ, r3, r4, hJI]
  module

/-- **A matrix commuting with `I` and `J` is scalar**, if `I² = 2`, `J² = −3`, `JI = −IJ` in
`M₂(K)`, `2, 3 ≠ 0` in `K` (then `1, I, J, IJ` is a `K`-basis of `M₂(K)`). -/
theorem commute_quat_scalar (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (Y : M2) (hYI : I * Y = Y * I) (hYJ : J * Y = Y * J) : ∃ a : K, Y = a • (1 : M2) := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have hinj : Function.Injective (fun x : K => x • (1 : M2)) := smul_left_injective K one_ne_zero
  have hIns : ∀ s : K, I ≠ s • (1 : M2) := by
    intro s hs
    have hc : I * J = J * I := by rw [hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hJI] at hc
    have h0 : I * J = 0 := by
      have : (2 : K) • (I * J) = 0 := by
        rw [two_smul]; nth_rewrite 2 [hc]; exact add_neg_cancel _
      exact (smul_eq_zero.mp this).resolve_left h2
    have hI0 : I = 0 := by
      have := r3; rw [h0, zero_mul] at this
      exact (smul_eq_zero.mp this.symm).resolve_left (neg_ne_zero.mpr h3)
    apply h2; apply hinj; simp only; rw [← hI, hI0, mul_zero, zero_smul]
  -- `(2c)•IJ + (4d)•J = 0 → c = 0 ∧ d = 0`
  have kill : ∀ c d : K, (2 * c) • (I * J) + (4 * d) • J = 0 → c = 0 ∧ d = 0 := by
    intro c d h
    have h' := congrArg (· * J) h
    simp only [add_mul, smul_mul_assoc, r3, hJ, zero_mul] at h'
    have hc : c = 0 := by
      by_contra hc
      have h6 : (-6 * c : K) ≠ 0 := mul_ne_zero (by
        rw [show (-6 : K) = -(2 * 3) by norm_num]; exact neg_ne_zero.mpr (mul_ne_zero h2 h3)) hc
      apply hIns ((-6 * c)⁻¹ * (12 * d))
      have : (-6 * c) • I = (12 * d) • (1 : M2) := by
        have e : (-6 * c) • I - (12 * d) • (1 : M2) =
            (2 * c) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by module
        rw [h'] at e; exact sub_eq_zero.mp e
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ h6, one_smul]
    subst hc
    refine ⟨rfl, ?_⟩
    have : (-12 * d) • (1 : M2) = 0 := by
      have e : (-12 * d) • (1 : M2) = ((2 : K) * 0) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by
        module
      rw [e]; exact h'
    have h12 : (-12 * d : K) = 0 := hinj (by simpa using this)
    have : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
    have := mul_eq_zero.mp (show (-12 : K) * d = 0 from h12)
    rcases this with h | h
    · exact absurd (neg_eq_zero.mp h) ‹(12 : K) ≠ 0›
    · exact h
  let v : Fin 4 → M2 := ![1, I, J, I * J]
  have hsum : ∀ g : Fin 4 → K, ∑ i, g i • v i = g 0 • 1 + g 1 • I + g 2 • J + g 3 • (I * J) := by
    intro g; simp [Fin.sum_univ_four, v]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hsum] at hg
    have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
    rw [hg, mul_zero, zero_mul, sub_zero] at hI0
    obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
    rw [hg2, hg3, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hIns (-(g 1)⁻¹ * g 0)
      have hb : g 1 • I = -(g 0 • (1 : M2)) := eq_neg_of_add_eq_zero_right hg
      calc I = (g 1)⁻¹ • (g 1 • I) := by rw [smul_smul, inv_mul_cancel₀ hg1, one_smul]
        _ = (-(g 1)⁻¹ * g 0) • 1 := by rw [hb]; module
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := hinj (by simpa using hg)
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
  have hY : Y ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hY
  rw [hsum] at hg
  subst hg
  have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYI, sub_self] at hI0
  obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
  have hJ0 := quat_comm_J I J hI hJ hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYJ, sub_self, hg3, mul_zero, zero_smul, add_zero] at hJ0
  have hg1 : g 1 = 0 := by
    have h' := congrArg (· * J) hJ0
    simp only [smul_mul_assoc, r3, zero_mul, smul_smul] at h'
    by_contra hg1
    apply hIns 0
    have hne : (-2 * g 1 * -3 : K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hg1) (neg_ne_zero.mpr h3)
    rw [zero_smul]
    exact (smul_eq_zero.mp h'.symm).resolve_left hne
  refine ⟨g 0, ?_⟩
  rw [hg1, hg2, hg3]; simp

section AdjRoot

open Polynomial

variable (d : ℚ)

/-- `X² − d` is irreducible over `ℚ` for `d < 0`. -/
theorem irred_sq_sub (hd : d < 0) : Irreducible (X ^ 2 - C d : ℚ[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])

theorem monic_sq_sub : (X ^ 2 - C d : ℚ[X]).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem finrank_adjRoot : Module.finrank ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_sq_sub d)).finrank]
  exact natDegree_X_pow_sub_C

theorem finite_adjRoot : Module.Finite ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
  (AdjoinRoot.powerBasis' (monic_sq_sub d)).finite

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- For `d < 0`, `ℚ(√d)` (as `AdjoinRoot`, with its field structure) is a totally complex
quadratic number field. -/
theorem adjRoot_numberField (hd : d < 0) :
    letI : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
    NumberField (AdjoinRoot (X ^ 2 - C d : ℚ[X])) ∧
      NumberField.IsTotallyComplex (AdjoinRoot (X ^ 2 - C d : ℚ[X])) := by
  let : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
  have : CharZero (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))).injective
  have := finite_adjRoot d
  refine ⟨{}, ⟨fun v => ?_⟩⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  rintro ⟨φ, hφ, -⟩
  have h2 : (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := by
    have := congrArg hφ.embedding (root_sq d)
    rwa [map_pow, eq_ratCast (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))) d,
      map_ratCast] at this
  have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])))]

end AdjRoot


end LinAlg

local notation "Kd[" d "]" => AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)

/-- `root` is not rational: `x + y·√d = 0` with `x, y ∈ ℚ` forces `x = y = 0` (`d < 0`). -/
theorem root_lin_indep (d : ℚ) (hd : d < 0) (x y : ℚ)
    (h : algebraMap ℚ Kd[d] x + algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = 0) : x = 0 ∧ y = 0 := by
  have : Nontrivial Kd[d] := AdjoinRoot.nontrivial _ (by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  have hinj := (algebraMap ℚ Kd[d]).injective
  by_cases hy : y = 0
  · subst hy
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨hinj (h.trans (map_zero _).symm), rfl⟩
  · exfalso
    have h1 : algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = -algebraMap ℚ Kd[d] x := by
      linear_combination h
    have h2 : (algebraMap ℚ Kd[d] y * AdjoinRoot.root _) ^ 2 = (algebraMap ℚ Kd[d] x) ^ 2 := by
      rw [h1]; ring
    rw [mul_pow, root_sq, ← map_pow, ← map_mul, ← map_pow] at h2
    have h3 := hinj h2
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]

/-- The same with integer coefficients. -/
theorem root_lin_indep_int (d : ℚ) (hd : d < 0) (a c : ℤ)
    (h : a • (1 : Kd[d]) + c • AdjoinRoot.root _ = 0) : a = 0 ∧ c = 0 := by
  have := root_lin_indep d hd a c (by
    rw [map_intCast, map_intCast]; rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at h; exact h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- **N1a-CM proved from T6.** If `End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, then `End_𝒪(A)` is isomorphic
to a subring of finite index of `𝒪_k`, `k = ℚ(√d)`: `1 ⊗ φ` (`φ ∈ End_𝒪(A)`) commutes with the
images `I, J` of `i, j ∈ 𝒪` (`I² = 2`, `J² = −3`, `JI = −IJ`), hence is a scalar
(`commute_quat_scalar`); `φ ↦` that scalar is an injective ring map `ψ` (T6); its image `R`
consists of integral elements (T6: `End(A)` is finite over `ℤ`), and contains `1` and `s√d`,
`s ≠ 0` (FS4's localization step), so it has rank 2 in `𝒪_k` and finite index. -/
theorem comOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) : ComOfMatrixEnd0 := by
  intro A q d hd hM
  obtain ⟨e⟩ := hM
  letI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) :=
    ⟨irred_sq_sub d hd⟩
  obtain ⟨hNF, hTC⟩ := adjRoot_numberField d hd
  obtain ⟨hfree, hfin, -, -⟩ := hHF Qbar A A
  let g : LeafQM.O →+* AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] AbVar.End A).toRingHom.comp
      q.iota
  have e1 : ∀ a b : AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hI : e (g oi) * e (g oi) = (2 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oi_mul_oi, map_ofNat, map_ofNat, Algebra.smul_def, mul_one,
      map_ofNat]
  have hJ : e (g oj) * e (g oj) = (-3 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oj_mul_oj, map_neg, map_neg, map_ofNat, map_ofNat,
      Algebra.smul_def, mul_one, map_neg, map_ofNat]
  have hJI : e (g oj) * e (g oi) = -(e (g oi) * e (g oj)) := by
    rw [← map_mul, ← map_mul, oj_mul_oi, map_neg, map_neg, map_mul, map_mul]
  have hcommφ : ∀ φ ∈ com q, ∀ a : LeafQM.O,
      ((1 : ℚ) ⊗ₜ[ℤ] φ) * g a = g a * ((1 : ℚ) ⊗ₜ[ℤ] φ) := by
    intro φ hφ a
    rw [com, Subring.mem_centralizer_iff] at hφ
    show ((1 : ℚ) ⊗ₜ[ℤ] φ) * ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) = ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) * _
    rw [← e1, ← e1, hφ _ ⟨a, rfl⟩]
  have hsc : ∀ φ ∈ com q, e ((1 : ℚ) ⊗ₜ[ℤ] φ) =
      (e ((1 : ℚ) ⊗ₜ[ℤ] φ) 0 0) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    intro φ hφ
    obtain ⟨a, ha⟩ := commute_quat_scalar (e (g oi)) (e (g oj)) hI hJ hJI two_ne_zero
      three_ne_zero (e ((1 : ℚ) ⊗ₜ[ℤ] φ))
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oi])
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oj])
    rw [ha]; simp
  -- the scalar map `ψ : End_𝒪(A) → ℚ(√d)`
  let ψ : com q →+* Kd[d] :=
    { toFun := fun φ => e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) 0 0
      map_one' := by
        simp only [OneMemClass.coe_one]
        rw [← Algebra.TensorProduct.one_def, map_one, Matrix.one_apply_eq]
      map_mul' := fun φ φ' => by
        simp only [MulMemClass.coe_mul]
        rw [e1, map_mul, hsc φ φ.2, hsc φ' φ'.2, smul_mul_smul_comm, one_mul]
        simp
      map_zero' := by simp
      map_add' := fun φ φ' => by simp [TensorProduct.tmul_add] }
  have hψ : ∀ φ : com q, e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = ψ φ • 1 := fun φ => hsc φ φ.2
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ0
    have h0 : e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = 0 := by rw [hψ, hφ0, zero_smul]
    rw [← map_zero e] at h0
    exact Subtype.ext (tmul_one_injective hfree _ (e.injective h0))
  -- an element `s√d` in the image (FS4's localization step)
  set c' : AbVar.End0 A :=
    e.symm ((AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) •
      (1 : Matrix (Fin 2) (Fin 2) Kd[d])) with hc'
  have hcen : ∀ x : AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  let f := TensorProduct.mk ℤ ℚ (AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ₀, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ₀ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hφ₀ : φ₀ ∈ com q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ₀ - φ₀ * q.iota a) = 0 := by
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (tmul_one_injective hfree _ key)
  have hw : ψ ⟨φ₀, hφ₀⟩ = (s : ℤ) • AdjoinRoot.root _ := by
    change e ((1 : ℚ) ⊗ₜ[ℤ] φ₀) 0 0 = _
    rw [hs', map_zsmul, hc', e.apply_symm_apply]
    simp
  -- the order `R = ψ(End_𝒪(A))`
  have hRint : ψ.range ≤ (integralClosure ℤ Kd[d]).toSubring := by
    rintro _ ⟨φ, rfl⟩
    have h1 : IsIntegral ℤ (φ : AbVar.End A) := Algebra.IsIntegral.isIntegral _
    have h2 : IsIntegral ℤ φ :=
      (isIntegral_algHom_iff ((com q).subtype.toIntAlgHom) Subtype.val_injective).mp h1
    exact h2.map ψ.toIntAlgHom
  refine ⟨Kd[d], inferInstance, hNF, hTC, finrank_adjRoot d, ψ.range, hRint, ?_,
    ⟨RingEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b h => hψinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩⟩⟩
  -- finite index: `R ∩ 𝒪_k` has rank 2 (it contains `1` and `s√d`)
  let fO : NumberField.RingOfIntegers Kd[d] →+ Kd[d] :=
    (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d]).toAddMonoidHom
  have hrange : (integralClosure ℤ Kd[d]).toSubring.toAddSubgroup =
      (⊤ : AddSubgroup (NumberField.RingOfIntegers Kd[d])).map fO := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩; exact y.2
  unfold LeafQM.AV.conductor
  suffices hsuff : (ψ.range.toAddSubgroup.comap fO).index ≠ 0 by
    convert hsuff using 1
    rw [← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, ← hrange]
    rfl
  let N' : Submodule ℤ (NumberField.RingOfIntegers Kd[d]) :=
    (ψ.range.toAddSubgroup.comap fO).toIntSubmodule
  have hw' : IsIntegral ℤ ((s : ℤ) •
      AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) := by
    rw [← hw]; exact hRint ⟨_, rfl⟩
  let w' : NumberField.RingOfIntegers Kd[d] := ⟨_, hw'⟩
  have h1N : (1 : NumberField.RingOfIntegers Kd[d]) ∈ N' := by
    show fO 1 ∈ ψ.range
    rw [show fO 1 = 1 from map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])]
    exact ψ.range.one_mem
  have hwN : w' ∈ N' := ⟨⟨φ₀, hφ₀⟩, hw⟩
  have hv : LinearIndependent ℤ ![(⟨1, h1N⟩ : N'), ⟨w', hwN⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hK := congrArg (fun z : N' => fO (z : NumberField.RingOfIntegers Kd[d])) hab
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul, Submodule.coe_zero,
      map_zero] at hK
    have e1' : fO 1 = 1 := map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])
    have e2' : fO w' = (s : ℤ) •
        AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) := rfl
    rw [e1', e2', smul_smul] at hK
    obtain ⟨ha, hbs⟩ := root_lin_indep_int d hd _ _ hK
    exact ⟨ha, (mul_eq_zero.mp hbs).resolve_right hs0⟩
  have hfr : Module.finrank ℤ N' = Module.finrank ℤ (NumberField.RingOfIntegers Kd[d]) := by
    apply le_antisymm (Submodule.finrank_le N')
    rw [NumberField.RingOfIntegers.rank, finrank_adjRoot]
    simpa using hv.fintype_card_le_finrank
  have := Submodule.finiteQuotientOfFreeOfRankEq N' hfr
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

/-- **N1a proved from the leaves T27 (Yu) and T6.** -/
theorem comIntOrQuadOrder_of_leaves (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) :
    ComIntOrQuadOrder :=
  comIntOrQuadOrder_of t27 t6 (comOfMatrixEnd0_of_homFree t6)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 and N1b (leaves), and `MobiusGlue` and N2 (glue). -/
theorem fibreComTrivialFull_of_leaves' (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of_leaves t27 t6) hB hK hC

end FS5NoCM


/-! ## §I N1b reduced to Shimura's description of CM points (`CMOptimalEmbedding`)

`R = φ⁻¹(𝒪)` for an embedding `φ : k → B` forces `(f(R), 6) = 1`: N5's `𝒪` is the set of
integral elements of `B_p` for `p = 2, 3` (finite checks `check2`, `check3` modulo `p²`). -/

namespace FS5NoCM


set_option maxRecDepth 100000 in
theorem check3 : ∀ a b c d : ZMod 9,
    a ^ 2 + a * c + c ^ 2 + 7 * (b ^ 2 + b * d + d ^ 2) = 0 →
      3 ∣ a.val ∧ 3 ∣ b.val ∧ 3 ∣ c.val ∧ 3 ∣ d.val := by decide

set_option maxRecDepth 100000 in
theorem check2 : ∀ a b c d : ZMod 4,
    a ^ 2 + a * c + c ^ 2 + 2 * (b ^ 2 + b * d + d ^ 2) = 0 →
      2 ∣ a.val ∧ 2 ∣ b.val ∧ 2 ∣ c.val ∧ 2 ∣ d.val := by decide

open LeafQM

/-- The reduced norm of `ofInt n`, as an integer quadratic form. -/
def Qf (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

theorem nrd_ofInt (n : Fin 4 → ℤ) : ofInt n * star (ofInt n) = algebraMap ℚ B (Qf n : ℚ) := by
  ext <;> simp [ofInt, Qf, QuaternionAlgebra.algebraMap_eq] <;> ring

/-- `p² ∣ nrd(ofInt n)` forces `p ∣ n` for `p = 2, 3` (`𝒪_p` is the set of integral elements of
the ramified `B_p`; a finite check modulo `p²`). -/
theorem dvd_of_sq_dvd_Qf (p : ℕ) (hp : p = 2 ∨ p = 3) (n : Fin 4 → ℤ) (h : (p : ℤ) ^ 2 ∣ Qf n) :
    ∀ i, (p : ℤ) ∣ n i := by
  rcases hp with rfl | rfl
  · have h0 : ((Qf n : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 4) ^ 2 + (n 0 : ZMod 4) * (n 2 : ZMod 4) + (n 2 : ZMod 4) ^ 2 +
        2 * ((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) + (n 3 : ZMod 4) ^ 2) = 0 := by
      have h4 : (4 : ZMod 4) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) +
        (n 3 : ZMod 4) ^ 2)) * h4
    obtain ⟨a, b, c, d⟩ := check2 _ _ _ _ e
    have key : ∀ m : ℤ, 2 ∣ ((m : ZMod 4)).val → (2 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 4)).val : ℤ) = m % 4 := ZMod.val_intCast m
      have h2 : (2 : ℤ) ∣ m % 4 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d
  · have h0 : ((Qf n : ℤ) : ZMod 9) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 9) ^ 2 + (n 0 : ZMod 9) * (n 2 : ZMod 9) + (n 2 : ZMod 9) ^ 2 +
        7 * ((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) + (n 3 : ZMod 9) ^ 2) = 0 := by
      have h9 : (9 : ZMod 9) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) +
        (n 3 : ZMod 9) ^ 2)) * h9
    obtain ⟨a, b, c, d⟩ := check3 _ _ _ _ e
    have key : ∀ m : ℤ, 3 ∣ ((m : ZMod 9)).val → (3 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 9)).val : ℤ) = m % 9 := ZMod.val_intCast m
      have h2 : (3 : ℤ) ∣ m % 9 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d

theorem ofInt_nsmul (p : ℕ) (w : Fin 4 → ℤ) : ofInt (fun i => (p : ℤ) * w i) = (p : ℚ) • ofInt w := by
  ext <;> simp [ofInt] <;> ring

theorem mul_star_comm (x : B) : star x * x = x * star x := by
  ext <;> simp <;> ring

/-- **Optimal embeddings have conductor prime to 6** (the algebra behind N1b). If `R ⊆ 𝒪_k` is
the preimage `φ⁻¹(𝒪)` of N5's maximal order under an embedding `φ : k → B` and has finite index,
then `p ∤ [𝒪_k : R]` for `p = 2, 3`: otherwise some `y ∈ 𝒪_k ∖ R` has `p y ∈ R`, so
`φ(p y) = ofInt v ∈ 𝒪`; `nrd φ(y) ∈ ℤ` (its minimal polynomial is that of `y`, integral), so
`p² ∣ nrd(ofInt v)`, hence `p ∣ v` (`dvd_of_sq_dvd_Qf`) and `φ(y) ∈ 𝒪`, i.e. `y ∈ R`. -/
theorem not_dvd_conductor_of_optimal {k : Type} [Field k] [NumberField k]
    (φ : k →ₐ[ℚ] B) (R : Subring k) (hR : R = O.comap φ.toRingHom)
    (hc0 : AV.conductor R ≠ 0) (p : ℕ) (hp : p = 2 ∨ p = 3) : ¬ p ∣ AV.conductor R := by
  intro hdvd
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  set L := (integralClosure ℤ k).toSubring.toAddSubgroup with hL
  set H := R.toAddSubgroup.addSubgroupOf L with hH
  have hidx : H.index = AV.conductor R := rfl
  have hcard : Nat.card (↥L ⧸ H) = AV.conductor R := by rw [← AddSubgroup.index_eq_card, hidx]
  have hfin : Finite (↥L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hc0)
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥L ⧸ H) p (by rw [hcard]; exact hdvd)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hyR : (y : k) ∉ R := by
    intro hy
    have h0 : ((y : ↥L) : ↥L ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    rw [h0, addOrderOf_zero] at hg
    exact hpp.one_lt.ne hg
  have hpy : p • (y : k) ∈ R := by
    have h1 : p • ((y : ↥L) : ↥L ⧸ H) = 0 := by rw [← hg]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h1
    exact h1
  have hyint : IsIntegral ℤ (y : k) := y.2
  have hynq : (y : k) ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq⟩
    have hqi : IsIntegral ℤ q :=
      (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
        (algebraMap ℚ k).injective).mp (by rw [← hq] at hyint; exact hyint)
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
    apply hyR
    rw [← hq, ← hm]
    have : algebraMap ℚ k (algebraMap ℤ ℚ m) = (m : k) := by simp
    rw [this]; exact intCast_mem R m
  set x : B := φ (y : k) with hx
  have hxint : IsIntegral ℤ x := hyint.map (φ.restrictScalars ℤ)
  have hxnq : x ∉ Set.range (algebraMap ℚ B) := by
    rintro ⟨q, hq⟩
    apply hynq
    refine ⟨q, φ.injective ?_⟩
    change φ (algebraMap ℚ k q) = φ y
    rw [AlgHom.commutes]; exact hq
  -- the minimal polynomial of `x` is `X² − t X + n`, with integer coefficients
  set t : ℚ := 2 * x.re with ht
  set n : ℚ := (x * star x).re with hn
  have hxx : x * star x = algebraMap ℚ B n := by
    rw [hn, QuaternionAlgebra.mul_star_eq_coe]; rfl
  have hsum : x + star x = algebraMap ℚ B t := by
    rw [QuaternionAlgebra.self_add_star', ht]; simp
  have hP : Polynomial.aeval x (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n) = 0 := by
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      map_one, one_mul, map_neg]
    rw [← hsum, ← hxx, ← mul_star_comm]
    noncomm_ring
  have hPm : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_quadratic one_ne_zero]
  have hPd : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  have hxintQ : IsIntegral ℚ x := hxint.tower_top
  have hmin : minpoly ℚ x = Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxintQ) hPm
      (minpoly.dvd ℚ x hP) ?_).symm
    rw [hPd]
    exact (minpoly.two_le_natDegree_iff hxintQ).mpr hxnq
  have hmin' : minpoly ℚ x = (minpoly ℤ (y : k)).map (algebraMap ℤ ℚ) := by
    rw [hx, minpoly.algHom_eq φ φ.injective]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hyint
  obtain ⟨N, hN⟩ : ∃ N : ℤ, (N : ℚ) = n := by
    refine ⟨(minpoly ℤ (y : k)).coeff 0, ?_⟩
    have := congrArg (fun P : Polynomial ℚ => P.coeff 0) (hmin.symm.trans hmin')
    simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at this
    simpa using this.symm
  -- `φ(p y) = p x ∈ 𝒪`, so `p² ∣ nrd`, so `x ∈ 𝒪`
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hz : (p : ℚ) • x ∈ O := by
    have h1 : p • (y : k) ∈ O.comap φ.toRingHom := hR ▸ hpy
    have h2 : φ (p • (y : k)) ∈ O := h1
    rwa [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h2
  obtain ⟨v, hv⟩ := hz
  have hQ : (Qf v : ℚ) = (p : ℚ) ^ 2 * N := by
    have h1 := nrd_ofInt v
    rw [← hv, star_smul, smul_mul_smul_comm, hxx, Algebra.smul_def, ← map_mul] at h1
    rw [hN, ← (algebraMap ℚ B).injective h1, star_trivial]; ring
  have hQ' : (p : ℤ) ^ 2 ∣ Qf v := ⟨N, by exact_mod_cast hQ⟩
  choose w hw using dvd_of_sq_dvd_Qf p hp v hQ'
  have hvw : v = fun i => (p : ℤ) * w i := funext hw
  have hxw : x = ofInt w := by
    apply smul_right_injective B hp0
    simp only
    rw [hv, hvw, ofInt_nsmul]
  apply hyR
  rw [hR]
  exact ⟨w, hxw⟩

/-- **N1b′ (leaf; Shimura's description of CM points on `X₀(6,1)`).** If `End_𝒪(A) ≅ R` for an order
`R` of an imaginary quadratic `k`, then `R` is the preimage `φ⁻¹(𝒪)` of N5's maximal order under
some `ℚ`-embedding `φ : k → B`.
*Published statement*: for `(A, ι)` over `ℂ` with CM, `A = ℂ²/𝒪 v_τ` and `End_𝒪(A) ≅ φ_τ(k) ∩ 𝒪`,
where `φ_τ : k → B` is the embedding whose image fixes `τ ∈ ℍ` (Shimura, Ann. of Math. 85 (1967);
Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5; locators
UNVERIFIED); in characteristic 0 the same holds over `ℚ̄`. Transport to the given `k ⊇ R`: an
isomorphism `R ≅ φ_τ(k) ∩ 𝒪` extends to the fraction fields `k ≅ k_τ` (`R` has rank 2), and the
composite embedding pulls `𝒪` back to `R`. A consequence of the published statement (up to
replacing `B` by `B^op ≅ B`, which preserves `𝒪`). -/
def CMOptimalEmbedding : Prop :=
  ∀ (P : AV.QMPair AV.Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      AV.conductor R ≠ 0 → Nonempty (AV.com P.q ≃+* R) →
        ∃ φ : k →ₐ[ℚ] B, R = O.comap φ.toRingHom

theorem cmConductorCoprime6_of (h : CMOptimalEmbedding) : CMConductorCoprime6 := by
  intro P k _ _ _ hk2 R hR hc0 he
  obtain ⟨φ, hφ⟩ := h P k hk2 R hR hc0 he
  have h2 := not_dvd_conductor_of_optimal φ R hφ hc0 2 (Or.inl rfl)
  have h3 := not_dvd_conductor_of_optimal φ R hφ hc0 3 (Or.inr rfl)
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  exact ⟨(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)),
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))⟩


/-- **FS5 with the repaired clauses, from leaves and named glue**: the bundle, R5fpCount, T27, T6,
N1b′ `CMOptimalEmbedding` (leaves), and `MobiusGlue`, N2 (glue). -/
theorem fibreComTrivialFull_of_leaves'' (hL : R1R2fpFull) (hM : LeafQM.AV.Pin.MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : LeafQM.AV.R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves' hL hM t27 t6 (cmConductorCoprime6_of hE) hK hC

end FS5NoCM


end

end G0A2_a60_fs5

section G0A2_a70_fibrecover
/-! ## g0-assemble2: fibre-cover (scratch/fibre-cover/FibreCover.lean lines 15-18 and 74-730, verbatim; lines
19-73 are verbatim copies of g0-mod-field's definitions, part 75) -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q
namespace G0ModField

/-! ## Part 1 (proved): `FibreCoverOut` is a statement about the residue field of `y` alone -/

/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree (copied from `scratch/rv-g0pieces/Exotic.lean`). -/
theorem spec_to_specQ_eq {K : Type} [Field K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- **A `ℚ̄`-point factors through every subfield `K ⊆ ℚ̄` containing its residue field.** -/
theorem exists_factor_of_residueImage_le (Y : Over (Spec (CommRingCat.of ℚ)))
    (y : fieldPt Qbar ⟶ Y) (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ yK : fieldPt K ⟶ Y, fieldMap K.val ≫ yK = y := by
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  unfold residueImage at hK
  rw [hp] at hK
  have hmem : ∀ a, emb a ∈ K := fun a => hK (IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩)
  let emb' : Y.left.residueField x ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (emb.hom.codRestrict K hmem)
  have aux : Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
      (Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩ = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply, hp]
    rfl
  exact ⟨Over.homMk ((Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩)
    (spec_to_specQ_eq _ _), Over.OverMorphism.ext aux⟩

/-- The residue field of `z ∘ Spec(K ⊆ ℚ̄)` lies in `K` (scheme form). -/
theorem residueImage_le_aux {X : Scheme.{0}} (K : IF) (z : Spec (CommRingCat.of K) ⟶ X) :
    residueImage (X := X)
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ z) ≤ K := by
  unfold residueImage
  rw [IntermediateField.adjoin_le_iff, specToEquivOfField_comp]
  rintro _ ⟨a, rfl⟩
  exact ((Scheme.SpecToEquivOfField K X z).2 a).2

/-- The residue field of `y ∘ Spec(K ⊆ ℚ̄)` lies in `K`. -/
theorem residueImage_comp_le (Y : Over (Spec (CommRingCat.of ℚ))) (K : IF)
    (yK : fieldPt K ⟶ Y) : residueImage (X := Y.left) (fieldMap K.val ≫ yK).left ≤ K :=
  residueImage_le_aux K yK.left

/-- A base change along `K ⊆ ℚ̄` of `PK`, isomorphic to `P`, makes `PK.A` a model of `P.A`. -/
theorem isModelOver_of_baseChange {K : IF} {PK : QML3 K} {Q P : QML3 Qbar}
    (hb : IsBaseChangeOf ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) PK Q) (e : Q.Iso P) :
    IsModelOver K PK.A P := by
  obtain ⟨g, hpb, -, -⟩ := hb
  refine ⟨Iso.trans ?_ ⟨e.φ.hom, e.ψ.hom, e.left, e.right⟩⟩
  exact Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd

/-- **The rational fibre (proved from R1fp alone)**: if `K ⊆ ℚ̄` contains the residue field of
the point `y` of `P`, there is a rational fibre `PK/K` over `P`. -/
theorem rationalFibre_of_le {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) {y : fieldPt Qbar ⟶ Y} {P : QML3 Qbar} (hy : Φ Qbar y = M3.mk P)
    (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK := by
  obtain ⟨yK, hyK⟩ := exists_factor_of_residueImage_le Y y K hK
  obtain ⟨-, -, -, hnat, -, -⟩ := h1
  have hPK : Φ K yK = M3.mk (Quotient.out (Φ K yK)) := (Quotient.out_eq _).symm
  obtain ⟨Q, hQ, hb⟩ := hnat K Qbar K.val yK _ hPK
  rw [hyK, hy] at hQ
  have e : Nonempty (P.Iso Q) := Quotient.exact hQ
  exact ⟨_, ⟨yK, hPK, hyK ▸ hy⟩, isModelOver_of_baseChange hb e.some.symm⟩

/-- **The field part of G2's output** for a subfield `F ⊆ ℚ̄`: `F` lies in the splitting field
of a separable `f ∈ ℚ[X]` of degree `≤ 324` unramified outside `T(u)`. -/
def FibreFieldOut (F : IF) (u : ℚ) : Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    F ≤ IntermediateField.adjoin ℚ (f.rootSet Qbar)

/-- **`FibreCoverOut` is exactly the field part for the residue field of `y`** (both
directions, from R1fp alone). -/
theorem fibreCoverOut_iff {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) {y : fieldPt Qbar ⟶ Y} {P : QML3 Qbar} (hy : Φ Qbar y = M3.mk P)
    (u : ℚ) : FibreCoverOut Y Φ u P ↔ FibreFieldOut (residueImage (X := Y.left) y.left) u := by
  constructor
  · rintro ⟨f, hs, hd, hram, PK, ⟨yK, -, hyK⟩, -⟩
    refine ⟨f, hs, hd, hram, ?_⟩
    have : fieldMap (IntermediateField.adjoin ℚ (f.rootSet Qbar)).val ≫ yK = y :=
      (Φ Qbar).injective (hyK.trans hy.symm)
    rw [← this]
    exact residueImage_comp_le Y _ yK
  · rintro ⟨f, hs, hd, hram, hle⟩
    obtain ⟨PK, hPK⟩ := rationalFibre_of_le h1 hy _ hle
    exact ⟨f, hs, hd, hram, PK, hPK⟩

/-- **Independence of the moduli bijection (the relabeling of rv-g0pieces keeps G2).** For two
bijections `Φ, Φ'` on the same `Y`, both with R1fp, and the same point `y`, `FibreCoverOut`
holds for `(Φ, P)` iff it holds for `(Φ', P')`, where `P`, `P'` are the objects of `y`.
In particular a relabeled triple `(Y, Φ ∘ τ, π)` (rv-g0pieces `relabel`, R1fp by
`r1fp_relabel`) satisfies G2 at `y` iff `(Y, Φ, π)` does. -/
theorem fibreCoverOut_indep {Y : Over (Spec (CommRingCat.of ℚ))} {Φ Φ' : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (h1' : R1fpProps Y Φ') {y : fieldPt Qbar ⟶ Y} {P P' : QML3 Qbar}
    (hy : Φ Qbar y = M3.mk P) (hy' : Φ' Qbar y = M3.mk P') (u : ℚ) :
    FibreCoverOut Y Φ u P ↔ FibreCoverOut Y Φ' u P' :=
  (fibreCoverOut_iff h1 hy u).trans (fibreCoverOut_iff h1' hy' u).symm

/-! ## Part 2 (proved): the field part from a degree bound and unramifiedness of `ℚ(y)` -/

/-- **Textbook (STANDARD): the Galois closure of an unramified field is unramified.** If
`ℚ(α) ⊆ ℚ̄` is unramified at `p`, so is the splitting field `ℚ(roots of minpoly α)`, which is
the compositum of the conjugates `σℚ(α) ≅ ℚ(α)`; a compositum of number fields unramified at `p`
is unramified at `p` (Neukirch, *Algebraic Number Theory*, Ch. I §9 or Ch. III §2, the
compositum of unramified extensions; UNVERIFIED locator). Not in Mathlib v4.35 for
`UnramifiedAt` (cf. g0-mod-field's `UnramifiedSup`, the Galois case). -/
def UnramifiedConjugates : Prop :=
  ∀ (α : Qbar) (p : ℕ), UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    UnramifiedAt (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar)) p

/-- **The field part from `[F:ℚ] ≤ 324` and `F` unramified outside `T(u)`**: take `f` the
minimal polynomial of a primitive element of `F` (separable in characteristic 0, of degree
`[F:ℚ]`); its splitting field contains `F` and is unramified outside `T(u)` by
`UnramifiedConjugates`. -/
theorem fibreFieldOut_of (hU : UnramifiedConjugates) (F : IF) [FiniteDimensional ℚ F]
    (hd : Module.finrank ℚ F ≤ 324) (u : ℚ)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt F p) : FibreFieldOut F u := by
  obtain ⟨β, hF⟩ : ∃ β : Qbar, IntermediateField.adjoin ℚ {β} = F := by
    obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
    refine ⟨α, le_antisymm ?_ ?_⟩
    · rw [IntermediateField.adjoin_simple_le_iff]; exact α.2
    · intro x hx
      have h1 : (⟨x, hx⟩ : F) ∈ IntermediateField.adjoin ℚ {α} := by
        rw [hα]; exact IntermediateField.mem_top
      have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map F.val := ⟨⟨x, hx⟩, h1, rfl⟩
      rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
      exact h2
  subst hF
  have hint : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly ℚ β, (minpoly.irreducible hint).separable, ?_, fun p hp => hU _ p (hram p hp), ?_⟩
  · rw [← IntermediateField.adjoin.finrank hint]; exact hd
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ _
      ((Polynomial.mem_rootSet).2 ⟨minpoly.ne_zero hint, minpoly.aeval ℚ _⟩)

/-! ## Part 3: the remaining glue as named Props, and `FibreCoverExists` from them -/

/-- **Glue (G2, degree; Glazer N5 L436-441 and L524-526): the residue field of a point over
`J(u)` has degree `≤ 324`.** For moduli data with R1fp, R2fp, `u ∉ 𝒞`, and a `ℚ̄`-point `y`
with object `P` over `J(u)`, the residue field `ℚ(y) ⊆ ℚ̄` is finite over `ℚ` of degree `≤ 324`.
Argument (glue): the `ℚ`-embeddings of `ℚ(y)` give distinct points `σy` of the fibre over the
rational value `J(u)` (`ToP1.val_comp`), which `Φ` maps injectively into the `Aut 𝒪`-twist class
of `P` (R2fp); that class has at most `4·|(𝒪/3𝒪)^×| ≤ 324` elements (`TwistClassCard`). This
step does not depend on which triple `(Y, Φ, π)` is used. -/
def FibreDegree : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (y : fieldPt Qbar ⟶ Y), R1fpProps Y Φ → R2fpProps Y Φ π →
    u ∉ contactSet → Φ Qbar y = M3.mk P →
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ _ : FiniteDimensional ℚ (residueImage (X := Y.left) y.left),
      Module.finrank ℚ (residueImage (X := Y.left) y.left) ≤ 324

/-- **Glue (G2, ramification: Prop. TS + Lemma NV, Glazer N5 L484-529; h-decomposition G2 with
inputs R1(d), R2, T1, T2): the residue field of a point over `J(u)` is unramified outside
`T(u) = S_mul ∪ supp M_{S_mul}(u)`.** For the genuine `(Y₃, π)` this is the manuscript's local
calculation: `Y₃ → P¹` has a proper smooth model over `ℤ[1/30]` branched only over `0, ∞, −16/27`
with tame indices; the pullback by `J` has indices `2, 6, 2`, normalized to `2, 1, 1`; the fibre
over `u` is unramified at `p ∉ T(u)` (the valuation case analysis is proved,
`GlueRepo.PR.inertia_orders_eq_one_iff`; Lemma NV step 2 is proved,
`LeafQM.AV.residue_unramified_over_branch`). **Pinning caveat** (fibre-cover §3): as stated it
quantifies over every `(Y, π)` satisfying R1fp, R2fp for some `Φ`; these clauses constrain
`(Y, π)` only through field points, so the genuine proof applies only once `(Y, π)` is pinned
(task qm-pin). Relabelings of `Φ` alone do not matter (`fibreCoverOut_indep`). -/
def FibreUnramified : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (y : fieldPt Qbar ⟶ Y), R1fpProps Y Φ → R2fpProps Y Φ π →
    u ∉ contactSet → Φ Qbar y = M3.mk P →
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt (residueImage (X := Y.left) y.left) p

/-- **`FibreCoverExists` from the degree bound, Prop. TS + Lemma NV on `ℚ(y)`, and the textbook
fact on Galois closures** (the rational fibre itself is proved from R1fp, `rationalFibre_of_le`). -/
theorem fibreCoverExists_of (hD : FibreDegree) (hR : FibreUnramified)
    (hU : UnramifiedConjugates) : FibreCoverExists := by
  intro Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩
  rw [fibreCoverOut_iff h1 hy u]
  obtain ⟨hfd, hd⟩ := hD Y Φ π u P y h1 h2 hu hy hπ
  exact fibreFieldOut_of hU _ hd u (hR Y Φ π u P y h1 h2 hu hy hπ)

/-! ## Part 4: `FibreDegree` from the intrinsic count `TwistClassCard` -/

/-- **Glue (Glazer N5 L425-441, the degree bound `≤ 4·|(𝒪/3𝒪)^×| ≤ 324`): the `Aut 𝒪`-twist
class of a level-3 object over `ℚ̄` has at most `324` isomorphism classes.** For `P = (A, ι, η)`
over `ℚ̄`, the classes `[Q]` whose QM pair is an `Aut 𝒪`-twist of `(A, ι)` number at most
`4·|(𝒪/3𝒪)^×|`: `Aut 𝒪` modulo inner automorphisms (which give isomorphic pairs) has order 4
(the Atkin–Lehner group `W`), and on a fixed pair the level structures `η : 𝒪 → A[3]` are
determined by `η(1)`, a free generator of the `𝒪/3𝒪`-module `A[3] ≅ 𝒪/3𝒪` (`|A[3]| = 3⁴`,
Mumford §4, UNVERIFIED locator), so there are `|(𝒪/3𝒪)^×| = |GL₂(𝔽₃)| = 48 ≤ 81` of them.
Intrinsic: it mentions no moduli scheme. -/
def TwistClassCard : Prop :=
  ∀ P : QML3 Qbar, ∃ s : Finset (M3 Qbar), s.card ≤ 324 ∧
    ∀ Q : QML3 Qbar, (∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (P.q.twist α) Q.q)) → M3.mk Q ∈ s

/-- Every finite subextension `K ⊆ F` has degree at most the number of embeddings `F → ℚ̄`. -/
theorem finrank_le_of_card_algHom_le (F : IF) (n : ℕ)
    (h : ∀ t : Finset (F →ₐ[ℚ] Qbar), t.card ≤ n) (K : IntermediateField ℚ F)
    [FiniteDimensional ℚ K] : Module.finrank ℚ K ≤ n := by
  classical
  have hext : ∀ e : K →ₐ[ℚ] Qbar, ∃ e' : F →ₐ[ℚ] Qbar, e'.domRestrict K = e := fun e =>
    IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := K) (M := Qbar) (E := F) e
  choose ext hext using hext
  have hinj : Function.Injective ext := fun e₁ e₂ h12 => by
    rw [← hext e₁, ← hext e₂, h12]
  calc Module.finrank ℚ K = Fintype.card (K →ₐ[ℚ] Qbar) := (AlgHom.card ℚ K Qbar).symm
    _ = (Finset.univ.image ext).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ n := h _

/-- **A subfield of `ℚ̄` with at most `n` embeddings into `ℚ̄` is finite of degree `≤ n`.** -/
theorem finiteDimensional_of_card_algHom_le (F : IF) (n : ℕ)
    (h : ∀ t : Finset (F →ₐ[ℚ] Qbar), t.card ≤ n) :
    ∃ _ : FiniteDimensional ℚ F, Module.finrank ℚ F ≤ n := by
  classical
  let Pm : ℕ → Prop := fun m => ∃ K : IntermediateField ℚ F,
    FiniteDimensional ℚ K ∧ Module.finrank ℚ K = m
  have h1 : Pm 1 := ⟨⊥, inferInstance, IntermediateField.finrank_bot⟩
  have hn : 1 ≤ n := by
    have := finrank_le_of_card_algHom_le F n h (⊥ : IntermediateField ℚ F)
    rwa [IntermediateField.finrank_bot] at this
  obtain ⟨K₀, hK₀, hK₀r⟩ := Nat.findGreatest_spec hn h1
  have htop : K₀ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    let K₁ : IntermediateField ℚ F := K₀ ⊔ IntermediateField.adjoin ℚ {x}
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : FiniteDimensional ℚ K₁ := IntermediateField.finiteDimensional_sup _ _
    have hle : K₀ ≤ K₁ := le_sup_left
    have hr : Module.finrank ℚ K₁ ≤ Module.finrank ℚ K₀ := by
      rw [hK₀r]
      exact Nat.le_findGreatest (finrank_le_of_card_algHom_le F n h K₁) ⟨K₁, inferInstance, rfl⟩
    have heq : K₀ = K₁ := IntermediateField.eq_of_le_of_finrank_le hle hr
    rw [heq]
    exact le_sup_right (a := K₀) (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : (⊤ : IntermediateField ℚ F) ≃ₗ[ℚ] F := IntermediateField.topEquiv.toLinearEquiv
  have : FiniteDimensional ℚ (⊤ : IntermediateField ℚ F) := htop ▸ hK₀
  have : FiniteDimensional ℚ F := e.finiteDimensional
  refine ⟨inferInstance, ?_⟩
  rw [← e.finrank_eq]
  have := finrank_le_of_card_algHom_le F n h (⊤ : IntermediateField ℚ F)
  exact this

/-- **`FibreDegree` from `TwistClassCard`** (no pinning needed): the embeddings `e` of
`F = ℚ(y)` give points `e ∘ y_F` over `J(u)`, pairwise distinct (`F` is generated by the image
of the residue field), whose classes lie in the twist class of `P` (R2fp). -/
theorem fibreDegree_of (hC : TwistClassCard) : FibreDegree := by
  classical
  intro Y Φ π u P y h1 h2 hu hy hπ
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  have hF : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range emb) := by
    unfold residueImage; rw [hp]
  rw [hF]
  set F : IF := IntermediateField.adjoin ℚ (Set.range emb) with hFdef
  have hmem : ∀ a, emb a ∈ F := fun a => IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩
  let emb' : Y.left.residueField x ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (emb.hom.codRestrict F hmem)
  let zF : Spec (CommRingCat.of F) ⟶ Y.left := (Scheme.SpecToEquivOfField F Y.left).symm ⟨x, emb'⟩
  have hz : ∀ e : F →ₐ[ℚ] Qbar, Scheme.SpecToEquivOfField Qbar Y.left
      (Spec.map (CommRingCat.ofHom (e : F →+* Qbar)) ≫ zF) = ⟨x, emb' ≫ CommRingCat.ofHom e⟩ := by
    intro e
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply]
  have hzy : Spec.map (CommRingCat.ofHom ((F.val : F →ₐ[ℚ] Qbar) : F →+* Qbar)) ≫ zF = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [hz, hp]
    rfl
  let yF : fieldPt F ⟶ Y := Over.homMk zF (spec_to_specQ_eq _ _)
  obtain ⟨s, hs, hsP⟩ := hC P
  apply finiteDimensional_of_card_algHom_le F 324
  intro t
  -- the value of `π` at the points `e ∘ y_F`
  have hy' : (π.val (K := F) zF).map (F.val : F →+* Qbar) =
      OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) := by
    rw [← π.val_comp (F.val : F →+* Qbar) zF, hzy]
    exact hπ
  have hval : ∀ e : F →ₐ[ℚ] Qbar, π.val (K := Qbar)
      (Spec.map (CommRingCat.ofHom (e : F →+* Qbar)) ≫ zF) =
      OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) := by
    intro e
    rw [π.val_comp]
    revert hy'
    induction π.val (K := F) zF using OnePoint.rec with
    | infty => intro h; simp at h
    | coe z =>
      intro h
      simp only [OnePoint.map_some] at h ⊢
      have hz' : z = algebraMap ℚ F (ZInQ.JHeight.Jmap u) := by
        apply (F.val : F →+* Qbar).injective
        have h' := OnePoint.coe_injective h
        rw [h']
        exact (F.val.commutes _).symm
      rw [hz']
      exact congrArg _ (e.commutes _)
  let g : (F →ₐ[ℚ] Qbar) → M3 Qbar := fun e => Φ Qbar (fieldMap e ≫ yF)
  have hmaps : ∀ e ∈ t, g e ∈ s := by
    intro e _
    have hQ : Φ Qbar (fieldMap e ≫ yF) = M3.mk (Quotient.out (Φ Qbar (fieldMap e ≫ yF))) :=
      (Quotient.out_eq _).symm
    have := ((h2 y _ P _ hy hQ).1).1 (hπ.trans (hval e).symm)
    show Φ Qbar (fieldMap e ≫ yF) ∈ s
    rw [hQ]
    exact hsP _ this
  have hinj : Set.InjOn g t := by
    intro e₁ _ e₂ _ h12
    have hpt : fieldMap e₁ ≫ yF = fieldMap e₂ ≫ yF := (Φ Qbar).injective h12
    have hl : Spec.map (CommRingCat.ofHom (e₁ : F →+* Qbar)) ≫ zF =
        Spec.map (CommRingCat.ofHom (e₂ : F →+* Qbar)) ≫ zF :=
      congrArg (fun z : fieldPt Qbar ⟶ Y => z.left) hpt
    have hl' := congrArg (Scheme.SpecToEquivOfField Qbar Y.left) hl
    rw [hz, hz] at hl'
    have hemb := eq_of_heq (Sigma.mk.inj_iff.mp hl').2
    apply IntermediateField.algHom_ext_of_eq_adjoin (hS := hFdef)
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun φ : Y.left.residueField x ⟶ CommRingCat.of Qbar => φ a) hemb
  calc t.card ≤ s.card := Finset.card_le_card_of_injOn g hmaps hinj
    _ ≤ 324 := hs

/-- **`FibreCoverExists` from the intrinsic count, Prop. TS + Lemma NV on `ℚ(y)`, and the textbook
fact on Galois closures.** -/
theorem fibreCoverExists_of_twistClassCard (hC : TwistClassCard) (hR : FibreUnramified)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of (fibreDegree_of hC) hR hU

/-! ## Part 5: what the ramification step needs from a pinning (only `(Y, π)` up to isomorphism) -/

/-- The residue field can only shrink along a morphism (scheme form). -/
theorem residueImage_comp_le_self_aux {X X' : Scheme.{0}} (h : X ⟶ X')
    (z : Spec (CommRingCat.of Qbar) ⟶ X) :
    residueImage (X := X') (z ≫ h) ≤ residueImage (X := X) z := by
  unfold residueImage
  rw [specToEquivOfField_comp_right]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _ ⟨_, rfl⟩

/-- The residue field can only shrink along a morphism: `ℚ(h ∘ y) ⊆ ℚ(y)`. -/
theorem residueImage_comp_le_self {Y Y' : Over (Spec (CommRingCat.of ℚ))} (h : Y ⟶ Y')
    (y : fieldPt Qbar ⟶ Y) :
    residueImage (X := Y'.left) (y ≫ h).left ≤ residueImage (X := Y.left) y.left :=
  residueImage_comp_le_self_aux h.left y.left

/-- Along an isomorphism the residue field is unchanged. -/
theorem residueImage_comp_iso {Y Y' : Over (Spec (CommRingCat.of ℚ))} (g : Y ≅ Y')
    (y : fieldPt Qbar ⟶ Y) :
    residueImage (X := Y'.left) (y ≫ g.hom).left = residueImage (X := Y.left) y.left := by
  apply le_antisymm (residueImage_comp_le_self g.hom y)
  have := residueImage_comp_le_self g.inv (y ≫ g.hom)
  rwa [Category.assoc, g.hom_inv_id, Category.comp_id] at this

/-- **Prop. TS + Lemma NV for one curve with one map to `P¹`** (the genuine `(Y₃, π)`): the
residue field of every `ℚ̄`-point over `J(u)`, `u ∉ 𝒞`, is unramified outside `T(u)`. This
mentions no moduli bijection. -/
def FibreUnramifiedOn (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (u : ℚ) (y : fieldPt Qbar ⟶ Y₀), u ∉ contactSet →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **The pin that `FibreUnramified` needs** (to be supplied by task qm-pin's repair): every
`(Y, π)` admitting a moduli bijection `Φ` with R1fp and R2fp is isomorphic to `(Y₀, π₀)` over
`P¹` on `ℚ̄`-points. `Φ` itself need not be pinned (`fibreCoverOut_indep`). -/
def CurvePinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∃ g : Y ≅ Y₀, ∀ y : fieldPt Qbar ⟶ Y,
      π.val (K := Qbar) y.left = π₀.val (K := Qbar) (y ≫ g.hom).left

/-- **`FibreUnramified` from Prop. TS on one curve and the pin of `(Y, π)`.** -/
theorem fibreUnramified_of_pinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀) : FibreUnramified := by
  intro Y Φ π u P y h1 h2 hu _ hπ p hp
  obtain ⟨g, hg⟩ := hpin Y Φ π h1 h2
  rw [← residueImage_comp_iso g y]
  exact h0 u (y ≫ g.hom) hu ((hg y).symm.trans hπ) p hp

/-- **The composite, corrected form**: `FibreCoverExists` from the intrinsic count, Prop. TS +
Lemma NV on the genuine `(Y₀, π₀)`, the pin of `(Y, π)`, and the textbook fact. -/
theorem fibreCoverExists_of_pinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hC : TwistClassCard) (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_twistClassCard hC (fibreUnramified_of_pinned Y₀ π₀ hpin h0) hU

/-! ## Part 6: `TwistClassCard` from 3-torsion and the Atkin–Lehner count -/

/-- **Glue + textbook leaf (`|A[3]| = 3⁴` for an abelian surface; Mumford §4, the kernel's leaf
`PkgI2.TorsionStructure`, which is stated for `A(K̄)[n]`, `K̄ = AlgebraicClosure K`): the
`3`-torsion of `A(ℚ̄)` has at most `81` points.** From `TorsionStructure` at `K = ℚ̄` and the
injection `A(ℚ̄) → A(AlgebraicClosure ℚ̄)` (glue, not compiled here). -/
def TorsionBound3 : Prop :=
  ∀ A : PkgI3.AbVar Qbar, A.dim = 2 → ∃ s : Finset (Additive (A.Pt Qbar)), s.card ≤ 81 ∧
    ∀ x : Additive (A.Pt Qbar), 3 • x = 0 → x ∈ s

/-- **Glue (computation on N5's maximal order `𝒪` of discriminant 6): `Aut 𝒪` modulo inner
automorphisms by units has at most 4 elements.** Every `α ∈ Aut 𝒪` is `w ∘ Ad u` with `w` in a
fixed set of `≤ 4` automorphisms and `u ∈ 𝒪^×`. Reason: `Aut 𝒪 = N_B(𝒪)/ℚ^×` (Skolem–Noether,
T13, proved) and `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²`, the Atkin–Lehner group `W` of the two ramified primes
(Vignéras, *Arithmétique des algèbres de quaternions*, Ch. II §1 / Ch. III §5, UNVERIFIED
locator; N5 L425-429: "at each of the two division primes its quotient … has order two"). -/
def InnerTwistCount : Prop :=
  ∃ W : Finset (LeafQM.O ≃+* LeafQM.O), W.card ≤ 4 ∧
    ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ w ∈ W, ∃ u : (LeafQM.O)ˣ,
      ∀ a : LeafQM.O, α a = w (u * a * ↑u⁻¹)

section TwistCount

variable {K : Type} [Field K]

/-- A level structure is determined by `η(1)`: `η(a) = a·η(1)`. -/
theorem level3_eta_eq {A : PkgI3.AbVar K} {q : QMStr A} (e : Level3 q) (a : LeafQM.O) :
    e.eta a = qmAct q K a (e.eta 1) := by
  rw [← e.linear, _root_.mul_one]

theorem level3_ext {A : PkgI3.AbVar K} {q : QMStr A} (e e' : Level3 q)
    (h : e.eta 1 = e'.eta 1) : e = e' := by
  have heta : e.eta = e'.eta :=
    AddMonoidHom.ext fun a => by rw [level3_eta_eq e a, level3_eta_eq e' a, h]
  cases e; cases e'
  cases heta
  rfl

/-- `η(1)` is a `3`-torsion point. -/
theorem level3_three {A : PkgI3.AbVar K} {q : QMStr A} (e : Level3 q) : 3 • e.eta 1 = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, _root_.mul_one]
  exact (e.ker _).mpr ⟨1, by rw [_root_.mul_one]; rfl⟩

/-- The inner twist `ι ∘ w ∘ Ad u` is isomorphic to `ι ∘ w`, by `ι(w(u))^{-1}`. -/
noncomputable def innerIso {A : PkgI3.AbVar K} (q : QMStr A) (w : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ)
    (α : LeafQM.O ≃+* LeafQM.O) (hα : ∀ a, α a = w (u * a * ↑u⁻¹)) :
    QMIso (q.twist α) (q.twist w) where
  φ := q.iota (w ↑u⁻¹)
  ψ := q.iota (w ↑u)
  left := by
    show (q.iota (w ↑u) * q.iota (w ↑u⁻¹)).hom = (1 : PkgI3.AbVar.End A).hom
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  right := by
    show (q.iota (w ↑u⁻¹) * q.iota (w ↑u)).hom = (1 : PkgI3.AbVar.End A).hom
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  equivariant a := by
    show (q.iota (w ↑u⁻¹) * q.iota (α a)).hom = (q.iota (w a) * q.iota (w ↑u⁻¹)).hom
    rw [hα, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← _root_.mul_assoc, ← _root_.mul_assoc,
      Units.inv_mul, _root_.one_mul]

/-- Transport of a level structure along a QM isomorphism. -/
noncomputable def transportLevel {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (θ : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (PkgI3.AbVar.ptMap (L := K) θ.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ θ.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ θ.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ θ.φ.hom) = _
    rw [Category.assoc, θ.equivariant a, Category.assoc]
  ker a := by
    have hinv : Function.LeftInverse (PkgI3.AbVar.ptMap (L := K) θ.ψ).toAdditive
        (PkgI3.AbVar.ptMap (L := K) θ.φ).toAdditive := fun x => by
      change Additive.ofMul ((Additive.toMul x ≫ θ.φ.hom) ≫ θ.ψ.hom) = x
      rw [Category.assoc, θ.left, Category.comp_id]; rfl
    rw [AddMonoidHom.comp_apply, map_eq_zero_iff _ hinv.injective, e.ker]

/-- The transported object is isomorphic to the original. -/
noncomputable def transportIso (Q : QML3 K) {A' : PkgI3.AbVar K} (hs : A'.dim = 2) {q' : QMStr A'}
    (θ : QMIso Q.q q') : Q.Iso ⟨A', hs, q', transportLevel θ Q.e⟩ where
  φ := θ.φ
  ψ := θ.ψ
  left := θ.left
  right := θ.right
  equivariant := θ.equivariant
  level _ := rfl

end TwistCount

/-- **`TwistClassCard` from the 3-torsion bound and the Atkin–Lehner count** (Glazer's
`4·81 = 324`): a class in the twist class of `P` is `[(A, ι∘w, η')]` for `w ∈ W` and a level
structure `η'`, which is determined by the `3`-torsion point `η'(1)`. -/
theorem twistClassCard_of (hT : TorsionBound3) (hW : InnerTwistCount) : TwistClassCard := by
  classical
  intro P
  obtain ⟨s3, hs3, hs3P⟩ := hT P.A P.surface
  obtain ⟨W, hWc, hWα⟩ := hW
  let F : (LeafQM.O ≃+* LeafQM.O) × Additive (P.A.Pt Qbar) → M3 Qbar := fun wx =>
    if h : ∃ e : Level3 (P.q.twist wx.1), e.eta 1 = wx.2 then
      M3.mk ⟨P.A, P.surface, P.q.twist wx.1, h.choose⟩ else M3.mk P
  refine ⟨(W ×ˢ s3).image F, ?_, ?_⟩
  · calc ((W ×ˢ s3).image F).card ≤ (W ×ˢ s3).card := Finset.card_image_le
      _ = W.card * s3.card := Finset.card_product _ _
      _ ≤ 4 * 81 := Nat.mul_le_mul hWc hs3
      _ = 324 := by norm_num
  · rintro Q ⟨α, ⟨f⟩⟩
    obtain ⟨w, hw, u, hu⟩ := hWα α
    let θ : QMIso Q.q (P.q.twist w) := f.symm.trans (innerIso P.q w u α hu)
    let e' := transportLevel θ Q.e
    have hx : e'.eta 1 ∈ s3 := hs3P _ (level3_three e')
    have hex : ∃ e : Level3 (P.q.twist w), e.eta 1 = e'.eta 1 := ⟨e', rfl⟩
    have hF : F (w, e'.eta 1) = M3.mk Q := by
      dsimp only [F]
      rw [dite_eq_left hex, level3_ext _ _ hex.choose_spec]
      exact (Quotient.sound (⟨transportIso Q P.surface θ⟩ : Nonempty _)).symm
    rw [← hF]
    exact Finset.mem_image_of_mem F (Finset.mem_product.mpr ⟨hw, hx⟩)

/-- **The composite with the twist count reduced**: `FibreCoverExists` from the 3-torsion
bound, the Atkin–Lehner count, the pin, Prop. TS + Lemma NV on one curve, and the textbook fact. -/
theorem fibreCoverExists_of_pinned' (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hT : TorsionBound3) (hW : InnerTwistCount) (hpin : CurvePinned Y₀ π₀)
    (h0 : FibreUnramifiedOn Y₀ π₀) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_pinned Y₀ π₀ (twistClassCard_of hT hW) hpin h0 hU

/-! ## Part 7: `TorsionBound3` from the kernel's leaf `TorsionStructure` -/

/-- Precomposition with `Spec L → Spec K` (a field extension) is injective on `K`-points. -/
theorem spec_comp_injective {X : Scheme.{0}} {K L : Type} [Field K] [Field L] (i : K →+* L)
    (z z' : Spec (CommRingCat.of K) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ z') : z = z' := by
  have h' := congrArg (Scheme.SpecToEquivOfField L X) h
  rw [specToEquivOfField_comp, specToEquivOfField_comp] at h'
  obtain ⟨⟨p1, f1⟩, hp1⟩ : ∃ q, Scheme.SpecToEquivOfField K X z = q := ⟨_, rfl⟩
  obtain ⟨⟨p2, f2⟩, hp2⟩ : ∃ q, Scheme.SpecToEquivOfField K X z' = q := ⟨_, rfl⟩
  rw [hp1, hp2] at h'
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h'
  have hf : f1 = f2 := by
    ext a
    apply i.injective
    exact congrArg (fun φ : X.residueField p1 ⟶ CommRingCat.of L => φ a) (eq_of_heq hh)
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [hp1, hp2, hf]

/-- `Spec(AlgebraicClosure ℚ̄) → Spec ℚ̄` over `ℚ̄`. -/
noncomputable def specIncl :
    PkgI2.specOver Qbar (AlgebraicClosure Qbar) ⟶ PkgI3.AbVar.ptObj (K := Qbar) Qbar :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar)))) (by
    simp only [PkgI2.specOver, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id])

/-- **`TorsionBound3` from the textbook leaf `TorsionStructure`** (`A(K̄)[3] ≅ (ℤ/3)⁴` at
`K = ℚ̄`, `K̄ = AlgebraicClosure ℚ̄`): `A(ℚ̄)[3]` injects into `A(K̄)[3]`, which has `81` points. -/
theorem torsionBound3_of (hT : ObjBridge.TorsionStructure) : TorsionBound3 := by
  classical
  intro A hA
  obtain ⟨e, -⟩ := hT Qbar (ObjBridge.toGrp A) 2 3 (by rw [Nat.cast_ofNat]; exact hA)
    (by norm_num) (by norm_num)
  set Tset := PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure Qbar) 3 with hTset
  have : Finite Tset := Finite.of_equiv _ e.symm
  have hTfin : Tset.Finite := Set.toFinite Tset
  have hcard : hTfin.toFinset.card = 81 := by
    rw [← Set.ncard_eq_toFinset_card Tset hTfin, ← Nat.card_coe_set_eq, Nat.card_congr e,
      Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  let incl : Additive (A.Pt Qbar) → PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure Qbar) :=
    fun x => specIncl ≫ Additive.toMul x
  have hinj : Function.Injective incl := by
    intro x y hxy
    have hl : Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) ≫
        (Additive.toMul x).left =
        Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) ≫
        (Additive.toMul y).left :=
      congrArg (fun f => f.left) hxy
    exact Additive.toMul.injective (Over.OverMorphism.ext (spec_comp_injective _ _ _ hl))
  have htors : ∀ x : Additive (A.Pt Qbar), 3 • x = 0 → incl x ∈ Tset := by
    intro x hx
    show (specIncl ≫ Additive.toMul x) ^ 3 = 1
    have h3 : Additive.toMul x ^ 3 = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    have hpow : ∀ n : ℕ, specIncl ≫ Additive.toMul x ^ n = (specIncl ≫ Additive.toMul x) ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
      | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
    rw [← hpow, h3, MonObj.comp_one]
  have hsfin : {x : Additive (A.Pt Qbar) | 3 • x = 0}.Finite :=
    Set.Finite.of_finite_image (hTfin.subset (by rintro _ ⟨x, hx, rfl⟩; exact htors x hx))
      hinj.injOn
  refine ⟨hsfin.toFinset, ?_, fun x hx => hsfin.mem_toFinset.mpr hx⟩
  rw [← hcard]
  exact Finset.card_le_card_of_injOn incl
    (fun x hx => hTfin.mem_toFinset.mpr (htors x (hsfin.mem_toFinset.mp hx))) hinj.injOn

/-- **The composite with the torsion count from the kernel's leaf.** -/
theorem fibreCoverExists_of_leafTorsion (Y₀ : Over (Spec (CommRingCat.of ℚ)))
    (π₀ : ToP1 Y₀.left) (hT : ObjBridge.TorsionStructure) (hW : InnerTwistCount)
    (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀) (hU : UnramifiedConjugates) :
    FibreCoverExists :=
  fibreCoverExists_of_pinned' Y₀ π₀ (torsionBound3_of hT) hW hpin h0 hU

/-- The same with the leaf exactly as it appears in the bundle (`TextbookLeaves.t5 :
PkgI2.TorsionStructure.{0}`, scratch/h-decomposition/Leaves.lean). -/
theorem torsionBound3_of_t5 (t5 : PkgI2.TorsionStructure.{0}) : TorsionBound3 :=
  torsionBound3_of (ObjBridge.torsionStructure_iff.mpr t5)

/-! ## Part 8: Prop. TS in Beckmann's inertia form; the valuation analysis is the repository's -/

/-- **Glue from leaves: Prop. TS (specialization inertia) on one cover `π₀ : Y₀ → P¹`**
(N5 L484-525; Beckmann, *On extensions of number fields obtained by specializing branched
coverings*, J. reine angew. Math. 419 (1991), Prop. 4.2, UNVERIFIED number; or T1-T2 with the
integral model R1(d)). For a rational non-branch value `t` and a prime `p > 324` (so
`p ∤ |G|`, `p ∤ 30`: good reduction, and the branch points `0, ∞, −16/27` stay distinct mod `p`),
the residue field of a `ℚ̄`-point over `t` is unramified at `p` once the three Beckmann inertia
orders `e_b / gcd(e_b, m_b)` are `1`: `e = 4, 6, 2` at `0, ∞, −16/27` (the indices of
`Y₃ → P¹`, `RvNocm.ramification_eq_orbifold_order`), `m_b` the intersection multiplicities
`v_p(t)⁺`, `(−v_p(t))⁺`, `v_p(t + 16/27)⁺`. -/
def PropTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (t : ℚ) (y : fieldPt Qbar ⟶ Y₀), t ≠ 0 → t ≠ -16 / 27 →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar t) →
    ∀ p : Nat.Primes, 324 < (p : ℕ) →
      4 ∣ (padicValRat p t).toNat → 6 ∣ (-padicValRat p t).toNat →
      2 ∣ (padicValRat p (t + 16 / 27)).toNat →
      UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **`FibreUnramifiedOn` from Prop. TS**: for `p ∉ T(u)` (so `p > 324` and `p ∤ M_S(u)`), the
three inertia orders at `t = J(u)` are `1` (`GlueRepo.PR.inertia_trivial_iff_not_dvd`, the
repository's valuation case analysis), and `J(u) ≠ 0, −16/27` for `u ∉ 𝒞`. -/
theorem fibreUnramifiedOn_of_propTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (h : PropTS Y₀ π₀) : FibreUnramifiedOn Y₀ π₀ := by
  intro u y hu hπ p hp
  have hp' : (p : ℕ) ∉ Mult.S_mul ∪ (contactSupport Mult.S_mul u).primeFactors := hp
  have hS : ∀ q, q.Prime → q ≤ 324 → q ∈ Mult.S_mul := fun q hq hq' =>
    Mult.mem_S_mul.mpr (Or.inl (Mult.mem_S_ht.mpr ⟨hq, hq'⟩))
  have hpS : (p : ℕ) ∉ Mult.S_mul := fun h' => hp' (Finset.mem_union_left _ h')
  have hp324 : 324 < (p : ℕ) := by
    by_contra h'
    exact hpS (hS _ p.2 (by omega))
  have hndvd : ¬ (p : ℕ) ∣ contactSupport Mult.S_mul u := fun hd =>
    hp' (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨p.2, hd, (GlueDescent.contactSupport_pos _ _).ne'⟩))
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨h4, h6, h2⟩ :=
    (GlueRepo.PR.inertia_trivial_iff_not_dvd (p := p) Mult.S_mul hS hpS hu).mpr hndvd
  exact h (ZInQ.JHeight.Jmap u) y (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u) hπ p
    hp324 h4 h6 h2

/-- **The composite on the leaves of the bundle**: `FibreCoverExists` from T5
(`TorsionStructure`), `InnerTwistCount`, the pin `CurvePinned Y₀ π₀`, Prop. TS on `(Y₀, π₀)`, and
`UnramifiedConjugates`. -/
theorem fibreCoverExists_of_propTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (t5 : PkgI2.TorsionStructure.{0}) (hW : InnerTwistCount) (hpin : CurvePinned Y₀ π₀)
    (hTS : PropTS Y₀ π₀) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_pinned' Y₀ π₀ (torsionBound3_of_t5 t5) hW hpin
    (fibreUnramifiedOn_of_propTS Y₀ π₀ hTS) hU

/-- **Prop. TS for every admissible cover** (the pin-free alternative to `CurvePinned`): every
`(Y, π)` admitting a moduli bijection with R1fp and R2fp satisfies Prop. TS. SPECULATIVE truth
argument (fibre-cover §3.2): R2fp makes every rational fibre of `π` isomorphic, as a Galois set
with residue fields, to a fibre of the genuine `π₀`, a `G`-torsor; by Hilbert irreducibility the
arithmetic monodromy of `π` then acts regularly, so `π` is Galois of degree `|G|` with the same
branch values and indices `4, 6, 2`, and Beckmann's theorem applies with the same inertia orders. -/
def PropTSAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → PropTS Y π

theorem fibreUnramified_of_propTSAll (h : PropTSAll) : FibreUnramified :=
  fun Y Φ π u _ y h1 h2 hu _ hπ => fibreUnramifiedOn_of_propTS Y π (h Y Φ π h1 h2) u y hu hπ

/-- **The pin-free composite**: `FibreCoverExists` from T5, `InnerTwistCount`, `PropTSAll` and
`UnramifiedConjugates`. -/
theorem fibreCoverExists_of_propTSAll (t5 : PkgI2.TorsionStructure.{0}) (hW : InnerTwistCount)
    (hTS : PropTSAll) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_twistClassCard (twistClassCard_of (torsionBound3_of_t5 t5) hW)
    (fibreUnramified_of_propTSAll hTS) hU

end G0ModField

namespace G0ModField

/-- **`InnerTwistCount` is proved** (g0-assemble2, from aut-o-finite's explicit computation
`Exact.autO_mod_inner_exact`: every `α ∈ Aut 𝒪` is `Ad v ∘ t_k` for one of four `t_k`; then
`α = t_k ∘ Ad (t_k⁻¹ v)`). -/
theorem innerTwistCount_proof : InnerTwistCount := by
  classical
  obtain ⟨t, ht, -⟩ := LeafQM.AV.Pin.Exact.autO_mod_inner_exact
  refine ⟨Finset.univ.image t, Finset.card_image_le.trans (by simp), fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := ht α
  refine ⟨t k, Finset.mem_image_of_mem t (Finset.mem_univ k),
    ⟨(t k).symm (v : LeafQM.O), (t k).symm ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O), ?_, ?_⟩, fun a => ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← map_mul, Units.inv_mul, map_one]
  · show α a = t k ((t k).symm (v : LeafQM.O) * a * (t k).symm ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O))
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hv a]

/-- **`FibreCoverExists` from T5, `PropTSAll` and `UnramifiedConjugates`** (fibre-cover's pin-free
composite with `InnerTwistCount` proved). -/
theorem fibreCoverExists_of_propTSAll' (t5 : PkgI2.TorsionStructure.{0}) (hTS : PropTSAll)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_propTSAll t5 innerTwistCount_proof hTS hU

end G0ModField

end G0A2_a70_fibrecover

section G0A2_a75_kernelfield
/-! ## g0-assemble2: kernel-field, assembled as in scratch/kernel-field/assemble.sh: morph-descend Descend.lean
3-401, inertia-homs InertiaHoms.lean 7-2089 (= g4-weilres G4.lean + inertia-homs), morph-descend G4Closed.lean
1867-1897, kernel-field New.lean (its Part 4, g0-dim's Dim.lean 107-305, is part 10; its Part 5 is part 75) -/
section PartDescend

/-!
# morph-descend: the input `MorphismsDescend` of G4 (EGA IV₃ 8.8.2), proved

Report: `docs/research/morph-descend.md`. Headline: `MorphDescend.morphismsDescend`, the Prop
`MorphismsDescend` of `scratch/g4-weilres/G4.lean` (copied verbatim below), proved with no
hypotheses, no `sorry`, only the standard axioms.

The geometric input is Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`, tagged Stacks 01ZC): for a cofiltered
diagram `Dᵢ` of qcqs schemes with affine transition maps and limit `lim Dᵢ`, every `S`-morphism
`lim Dᵢ → Y` with `Y` locally of finite presentation over `S` factors through some `Dᵢ`.
The glue proved here:
* `ringCoconeIsColimit`: `ℚ̄` is the filtered colimit in `CommRingCat` of its finite subextensions
  containing a number field `E₀`;
* `specConeIsLimit`: hence `Spec ℚ̄ = lim Spec L` in `Over (Spec K)` (`Spec` is a right adjoint,
  `Over.forget` reflects connected limits);
* `bcConeIsLimit`: hence `X ×_K ℚ̄ = lim X ×_K L` (`Over.pullback` is a right adjoint,
  `Over.forget` preserves connected limits), with affine transition maps (`bcDiag_isAffineHom`) and
  qcqs terms when `X → Spec K` is qcqs;
* `exists_descend`: the general descent statement, for `X` qcqs and `Y` LFP over any field `K`;
* `morphismsDescend`: the instance for `PkgI3.AbVar` (proper ⇒ qcqs, smooth ⇒ LFP).
-/

open CategoryTheory Limits AlgebraicGeometry

namespace MorphDescend

abbrev Qbar : Type := AlgebraicClosure ℚ

variable (E₀ : IntermediateField ℚ Qbar)

/-- The finite subextensions of `ℚ̄` containing `E₀`, ordered by inclusion. -/
abbrev Idx : Type := {L : IntermediateField ℚ Qbar // FiniteDimensional ℚ L ∧ E₀ ≤ L}

instance : IsDirectedOrder (Idx E₀) where
  directed L₁ L₂ := by
    obtain ⟨L₁, h₁, e₁⟩ := L₁
    obtain ⟨L₂, h₂, e₂⟩ := L₂
    exact ⟨⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, e₁.trans le_sup_left⟩,
      show L₁ ≤ L₁ ⊔ L₂ from le_sup_left, show L₂ ≤ L₁ ⊔ L₂ from le_sup_right⟩

instance [FiniteDimensional ℚ E₀] : Nonempty (Idx E₀) := ⟨⟨E₀, inferInstance, le_rfl⟩⟩

/-- The diagram `L ↦ L` of rings. -/
noncomputable def ringDiag : Idx E₀ ⥤ CommRingCat where
  obj L := CommRingCat.of L.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `ℚ̄` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag E₀) where
  pt := CommRingCat.of Qbar
  ι := { app L := CommRingCat.ofHom (algebraMap L.1 Qbar)
         naturality _ _ _ := rfl }

/-- `ℚ̄ = colim L` over the finite subextensions containing `E₀`. -/
noncomputable def ringCoconeIsColimit [FiniteDimensional ℚ E₀] : IsColimit (ringCocone E₀) := by
  haveI : ReflectsColimit (ringDiag E₀) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : Qbar)
    have hx : _root_.IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    refine ⟨⟨E₀ ⊔ IntermediateField.adjoin ℚ {x},
      IntermediateField.finiteDimensional_sup _ _, le_sup_left⟩, ⟨x, ?_⟩, rfl⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ {x} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩


/-! ### The base changes `X ×_K L` as a cofiltered limit -/

section Schemes

variable {K : Type} [Field K]

/-- `e : K → ℚ̄` with image in `L`, as a map `K → L`. -/
noncomputable def restrL (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀) (L : Idx E₀) : K →+* L.1 :=
  e.codRestrict L.1 (fun x => L.2.2 (he x))

/-- The inclusion `L ⊆ L'` in `CommRingCat`. -/
noncomputable abbrev inclL {L L' : Idx E₀} (h : L ≤ L') : CommRingCat.of L.1 ⟶ CommRingCat.of L'.1 :=
  CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom

/-- The inclusion `L ⊆ ℚ̄` in `CommRingCat`. -/
noncomputable abbrev toQbar (L : Idx E₀) : CommRingCat.of L.1 ⟶ CommRingCat.of Qbar :=
  CommRingCat.ofHom (algebraMap L.1 Qbar)

variable (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)

theorem restrL_inclL {L L' : Idx E₀} (h : L ≤ L') :
    CommRingCat.ofHom (restrL E₀ e he L) ≫ inclL E₀ h = CommRingCat.ofHom (restrL E₀ e he L') :=
  rfl

theorem restrL_toQbar (L : Idx E₀) :
    CommRingCat.ofHom (restrL E₀ e he L) ≫ toQbar E₀ L = CommRingCat.ofHom e :=
  rfl

theorem inclL_toQbar {L L' : Idx E₀} (h : L ≤ L') : inclL E₀ h ≫ toQbar E₀ L' = toQbar E₀ L :=
  rfl

/-- The diagram `L ↦ (Spec L → Spec K)` in `Over (Spec K)`. -/
noncomputable def specDiag : (Idx E₀)ᵒᵖ ⥤ Over (Spec (CommRingCat.of K)) where
  obj L := Over.mk (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop)))
  map f := Over.homMk (Spec.map (inclL E₀ (leOfHom f.unop))) (by
    dsimp
    rw [← Spec.map_comp, restrL_inclL])
  map_id L := by
    ext1
    show Spec.map (inclL E₀ _) = 𝟙 _
    rw [show inclL E₀ (leOfHom (𝟙 L).unop) = 𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    ext1
    show Spec.map (inclL E₀ _) = Spec.map (inclL E₀ _) ≫ Spec.map (inclL E₀ _)
    rw [← Spec.map_comp]
    rfl

/-- `Spec ℚ̄ → Spec K` as a cone over `specDiag`. -/
noncomputable def specCone : Cone (specDiag E₀ e he) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom e))
  π := { app L := Over.homMk (Spec.map (toQbar E₀ L.unop)) (by
          dsimp [specDiag]
          rw [← Spec.map_comp, restrL_toQbar])
         naturality L L' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          ext1
          show Spec.map (toQbar E₀ _) = Spec.map (toQbar E₀ _) ≫ Spec.map (inclL E₀ _)
          rw [← Spec.map_comp, inclL_toQbar] }

/-- `Spec ℚ̄ = lim Spec L` in `Over (Spec K)`. -/
noncomputable def specConeIsLimit [FiniteDimensional ℚ E₀] : IsLimit (specCone E₀ e he) := by
  haveI : IsConnected (Idx E₀)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit E₀).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro L L' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro L
    simp only [Iso.refl_hom, Category.id_comp]

variable (X : Over (Spec (CommRingCat.of K)))

/-- The diagram `L ↦ L ×_K X` of schemes, as a composite of functors. -/
noncomputable def bcDiag' : (Idx E₀)ᵒᵖ ⥤ Scheme :=
  (specDiag E₀ e he ⋙ Over.pullback X.hom) ⋙ Over.forget X.left

/-- `ℚ̄ ×_K X` as a cone over `bcDiag'`. -/
noncomputable def bcCone' : Cone (bcDiag' E₀ e he X) :=
  (Over.forget X.left).mapCone ((Over.pullback X.hom).mapCone (specCone E₀ e he))

/-- `ℚ̄ ×_K X = lim (L ×_K X)`, composite form. -/
noncomputable def bcCone'IsLimit [FiniteDimensional ℚ E₀] : IsLimit (bcCone' E₀ e he X) := by
  haveI : IsConnected (Idx E₀)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget X.left)
    (isLimitOfPreserves (Over.pullback X.hom) (specConeIsLimit E₀ e he))

/-- The diagram `L ↦ L ×_K X` of schemes, written with explicit pullbacks. -/
noncomputable abbrev bcDiag : (Idx E₀)ᵒᵖ ⥤ Scheme where
  obj L := pullback (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom
  map {L L'} f := pullback.lift
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom ≫
        Spec.map (inclL E₀ (leOfHom f.unop)))
      (pullback.snd _ _) (by
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL, pullback.condition])
  map_id L := (bcDiag' E₀ e he X).map_id L
  map_comp f g := (bcDiag' E₀ e he X).map_comp f g

/-- `ℚ̄ ×_K X` as a cone over `bcDiag`, written with explicit pullbacks. -/
noncomputable abbrev bcCone : Cone (bcDiag E₀ e he X) where
  pt := pullback (Spec.map (CommRingCat.ofHom e)) X.hom
  π := { app L := pullback.lift
          (pullback.fst (Spec.map (CommRingCat.ofHom e)) X.hom ≫ Spec.map (toQbar E₀ L.unop))
          (pullback.snd _ _) (by
            rw [Category.assoc, ← Spec.map_comp, restrL_toQbar, pullback.condition])
         naturality L L' f := (bcCone' E₀ e he X).π.naturality f }

/-- `ℚ̄ ×_K X = lim (L ×_K X)`. -/
noncomputable def bcConeIsLimit [FiniteDimensional ℚ E₀] : IsLimit (bcCone E₀ e he X) :=
  bcCone'IsLimit E₀ e he X

theorem bcDiag_obj (L : (Idx E₀)ᵒᵖ) :
    (bcDiag E₀ e he X).obj L =
      pullback (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom := rfl

theorem bcDiag_map_fst {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    (bcDiag E₀ e he X).map f ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom ≫
        Spec.map (inclL E₀ (leOfHom f.unop)) :=
  pullback.lift_fst _ _ _

theorem bcDiag_map_snd {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    (bcDiag E₀ e he X).map f ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom :=
  pullback.lift_snd _ _ _

theorem bcCone_π_app_fst (L : (Idx E₀)ᵒᵖ) :
    (bcCone E₀ e he X).π.app L ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom e)) X.hom ≫ Spec.map (toQbar E₀ L.unop) :=
  pullback.lift_fst _ _ _

theorem bcCone_π_app_snd (L : (Idx E₀)ᵒᵖ) :
    (bcCone E₀ e he X).π.app L ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom e)) X.hom :=
  pullback.lift_snd _ _ _

end Schemes

/-! ### Descent of morphisms (EGA IV₃ 8.8.2 via Mathlib's Stacks 01ZC) -/

section Main

variable {K : Type} [Field K]

/-- The comparison `ℚ̄ ×_K X → L ×_K X` (written `X ×_{K,e} ℚ̄ → X ×_{K,e|L} L`). -/
noncomputable def cmp (X : Over (Spec (CommRingCat.of K))) (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (L : Idx E₀) :
    pullback X.hom (Spec.map (CommRingCat.ofHom e)) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (restrL E₀ e he L))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (toQbar E₀ L)) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, restrL_toQbar])

theorem bcDiag_compactSpace (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (X : Over (Spec (CommRingCat.of K))) [QuasiCompact X.hom] (L : (Idx E₀)ᵒᵖ) :
    CompactSpace ((bcDiag E₀ e he X).obj L) := by
  rw [bcDiag_obj]
  infer_instance

theorem bcDiag_quasiSeparatedSpace (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (X : Over (Spec (CommRingCat.of K))) [QuasiSeparated X.hom] (L : (Idx E₀)ᵒᵖ) :
    QuasiSeparatedSpace ((bcDiag E₀ e he X).obj L) := by
  rw [bcDiag_obj]
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

theorem bcDiag_isAffineHom (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (X : Over (Spec (CommRingCat.of K))) {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    IsAffineHom ((bcDiag E₀ e he X).map f) := by
  have t := (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) X.hom).flip
  have s : IsPullback (pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom)
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom) X.hom
      (Spec.map (inclL E₀ (leOfHom f.unop)) ≫
        Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) := by
    rw [← Spec.map_comp, restrL_inclL]
    exact (IsPullback.of_hasPullback _ _).flip
  have hP := IsPullback.of_right (h₁₁ := (bcDiag E₀ e he X).map f) (by
    rw [bcDiag_map_snd]; exact s) (bcDiag_map_fst E₀ e he X f) t
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance

/-- **Descent of morphisms from `ℚ̄` to a number field (EGA IV₃ 8.8.2 (i), surjectivity, for
`ℚ̄ = colim L`), proved from Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC).** Let `X, Y` be `K`-schemes, `X` quasi-compact quasi-separated over `K`, `Y` locally
of finite presentation over `K`, and `e₁, e₂ : K → ℚ̄` with images in the number field `E₀`. Every
`ℚ̄`-morphism `φ : X ×_{K,e₁} ℚ̄ → Y ×_{K,e₂} ℚ̄` is the base change of a morphism
`ψ : X ×_{K,e₁} L → Y ×_{K,e₂} L` for some number field `E₀ ⊆ L ⊆ ℚ̄`. -/
theorem exists_descend [FiniteDimensional ℚ E₀] (X Y : Over (Spec (CommRingCat.of K)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (e₁ e₂ : K →+* Qbar) (he₁ : ∀ x, e₁ x ∈ E₀) (he₂ : ∀ x, e₂ x ∈ E₀)
    (φ : pullback X.hom (Spec.map (CommRingCat.ofHom e₁)) ⟶
      pullback Y.hom (Spec.map (CommRingCat.ofHom e₂)))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ (L : Idx E₀) (ψ : pullback X.hom (Spec.map (CommRingCat.ofHom (restrL E₀ e₁ he₁ L))) ⟶
        pullback Y.hom (Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L)))),
      φ ≫ cmp E₀ Y e₂ he₂ L = cmp E₀ X e₁ he₁ L ≫ ψ := by
  classical
  let D := bcDiag E₀ e₁ he₁ X
  let c := bcCone E₀ e₁ he₁ X
  have hc : IsLimit c := bcConeIsLimit E₀ e₁ he₁ X
  have h1 : ∀ i, CompactSpace (D.obj i) := bcDiag_compactSpace E₀ e₁ he₁ X
  have h2 : ∀ i, QuasiSeparatedSpace (D.obj i) := bcDiag_quasiSeparatedSpace E₀ e₁ he₁ X
  have h3 : ∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f) := bcDiag_isAffineHom E₀ e₁ he₁ X
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app L := pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e₁ he₁ L.unop))) X.hom ≫
        Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L.unop))
      naturality L L' f := by
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L'.unop)))
          (bcDiag_map_fst E₀ e₁ he₁ X f)).trans ?_
        dsimp only
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL]
        exact (Category.comp_id _).symm }
  let a : c.pt ⟶ Y.left :=
    (pullbackSymmetry _ _).hom ≫ φ ≫ pullback.fst _ _
  have ha : c.π ≫ t = (Functor.const _).map (a ≫ Y.hom) := by
    ext L
    simp only [NatTrans.comp_app, Functor.const_map_app, t, a, c]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L.unop)))
      (bcCone_π_app_fst E₀ e₁ he₁ X L)).trans ?_
    dsimp only
    rw [Category.assoc, ← Spec.map_comp, restrL_toQbar, Category.assoc, Category.assoc,
      pullback.condition, reassoc_of% hφ, pullbackSymmetry_hom_comp_snd_assoc]
  obtain ⟨L, g, hg1, hg2⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t Y.hom c hc a ha
  refine ⟨L.unop, (pullbackSymmetry _ _).hom ≫ pullback.lift g (pullback.fst _ _) hg2, ?_⟩
  have key : cmp E₀ X e₁ he₁ L.unop ≫ (pullbackSymmetry _ _).hom =
      (pullbackSymmetry _ _).inv ≫ c.π.app L := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc]
      simp [cmp]
    · simp only [c, Category.assoc]
      simp [cmp]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Category.assoc, pullback.lift_fst, reassoc_of% key, hg1]
    simp [cmp, a]
  · rw [Category.assoc, Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% key]
    simp only [c]
    simp [cmp, reassoc_of% hφ]

end Main

/-! ### `MorphismsDescend` of `scratch/g4-weilres/G4.lean`, for the project's abelian varieties

The definitions `specEmb`, `specIncl`, `cmpL` and the statement `MorphismsDescend` are copied
verbatim from `scratch/g4-weilres/G4.lean` (namespace `G4WeilRes`; there `Qbar` is
`GlueB3Unram.Qbar`, the same reducible abbreviation `AlgebraicClosure ℚ`). -/

section G4

open PkgI3

variable (K : IntermediateField ℚ Qbar)

/-- `Spec e : Spec ℚ̄ → Spec K` for an embedding `e : K → ℚ̄`. -/
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))

/-- `Spec ℚ̄ → Spec L` for a subfield `L ⊆ ℚ̄`. -/
noncomputable abbrev specIncl (L : IntermediateField ℚ Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L Qbar))

/-- `Spec e = Spec(ℚ̄ ← L) ≫ Spec e'` when `e = (L ↪ ℚ̄) ∘ e'`. -/
theorem specEmb_factor (L : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L)
    (he : ∀ x, (e' x : Qbar) = e x) :
    specEmb K e = specIncl L ≫ Spec.map (CommRingCat.ofHom (e' : K →+* L)) := by
  rw [specEmb, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (he x).symm

/-- The comparison `A ×_{K,e} ℚ̄ → A ×_{K,e'} L` (the base-change square along `Spec ℚ̄ → Spec L`). -/
noncomputable def cmpL (L : IntermediateField ℚ Qbar) (X : CategoryTheory.Over (Spec (CommRingCat.of K)))
    (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x) :
    Limits.pullback X.hom (specEmb K e) ⟶
      Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (e' : K →+* L))) :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ specIncl L)
    (by rw [Limits.pullback.condition, specEmb_factor K L e e' he, Category.assoc])

/-- **Input of G4 (EGA IV₃ 8.8.2 (i), surjectivity part, for `ℚ̄ = colim L`).** Verbatim from
`scratch/g4-weilres/G4.lean`. -/
def MorphismsDescend : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (e₁' e₂' : K →ₐ[ℚ] L)
      (he₁ : ∀ x, (e₁' x : Qbar) = e₁ x) (he₂ : ∀ x, (e₂' x : Qbar) = e₂ x)
      (ψ : Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom (e₁' : K →+* L))) ⟶
        Limits.pullback B.X.hom (Spec.map (CommRingCat.ofHom (e₂' : K →+* L)))),
      φ.left ≫ cmpL K L B.X e₂ e₂' he₂ = cmpL K L A.X e₁ e₁' he₁ ≫ ψ

/-- The restriction `K → L` of `e : K → ℚ̄`, as a `ℚ`-algebra map. -/
noncomputable def restrAlg {E₀ : IntermediateField ℚ Qbar} (e : K →ₐ[ℚ] Qbar)
    (he : ∀ x, (e : K →+* Qbar) x ∈ E₀) (L : Idx E₀) : K →ₐ[ℚ] L.1 :=
  { restrL E₀ (e : K →+* Qbar) he L with
    commutes' := fun r => Subtype.ext (e.commutes r) }

/-- **`MorphismsDescend` holds (proved; no hypotheses).** Abelian varieties are proper (so
quasi-compact and quasi-separated) and smooth (so locally of finite presentation); apply
`exists_descend` with `E₀ = e₁(K) ⊔ e₂(K)`. -/
theorem morphismsDescend : MorphismsDescend := by
  intro K _ A B e₁ e₂ φ
  let E₀ : IntermediateField ℚ Qbar := e₁.fieldRange ⊔ e₂.fieldRange
  have : FiniteDimensional ℚ e₁.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField e₁).toLinearEquiv
  have : FiniteDimensional ℚ e₂.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField e₂).toLinearEquiv
  have : FiniteDimensional ℚ E₀ := IntermediateField.finiteDimensional_sup _ _
  have he₁ : ∀ x, (e₁ : K →+* Qbar) x ∈ E₀ := fun x =>
    (le_sup_left : e₁.fieldRange ≤ E₀) ⟨x, rfl⟩
  have he₂ : ∀ x, (e₂ : K →+* Qbar) x ∈ E₀ := fun x =>
    (le_sup_right : e₂.fieldRange ≤ E₀) ⟨x, rfl⟩
  obtain ⟨L, ψ, hψ⟩ := exists_descend E₀ A.X B.X (e₁ : K →+* Qbar) (e₂ : K →+* Qbar) he₁ he₂
    φ.left (CategoryTheory.Over.w φ)
  exact ⟨L.1, L.2.1, restrAlg K e₁ he₁ L, restrAlg K e₂ he₂ L, fun _ => rfl, fun _ => rfl, ψ, hψ⟩

end G4

end MorphDescend
end PartDescend

section PartInertia

/-!
# inertia-homs: the input `InertiaFixesHoms` of g4-weilres, corrected and proved from leaves

Report: `docs/research/inertia-homs.md`. This file is `scratch/g4-weilres/G4.lean` verbatim
(everything up to `end G4WeilRes` of that file), followed by the new part (from
`section NewConj` on). Headlines:

* `G4WeilRes.inertiaFixesHomsMon_of_leaves : NeronOggShafarevich → HomFreeFinite →
  InertiaFixesHomsMon` (NOS = Serre–Tate 1968 Thm 1, leaf `PkgI2.NeronOggShafarevich`;
  Mumford §19 Thm 3, leaf `PkgI3.HomFreeFinite`).
* `G4WeilRes.conjAction_inertia'`: the inertia hypothesis of G4 from `InertiaFixesHomsMon`.
* `G4WeilRes.homField_of_model_leaves'`: G4 from `HomFreeFinite`, `MorphismsDescend` and
  `NeronOggShafarevich` (the input `InertiaFixesHoms` is eliminated).

`InertiaFixesHomsMon` differs from g4-weilres's `InertiaFixesHoms` in two ways: it quantifies
over homomorphisms `φ : AbVar.Hom (bcAlong A e₁) (bcAlong B e₂)` only (the original quantifies over
all morphisms of schemes and is false for constant maps to points not fixed by inertia), and over
places `w` over a prime `p` (`LiesOver w p`), which is how its only consumer uses it.

No `sorry`, no `axiom`.
-/

/-!
# g4-weilres: glue step G4 of `docs/research/h-decomposition.md` (Weil restriction, Hom field)

Report: `docs/research/g4-weilres.md`. Headline: `G4WeilRes.homField_of_model_leaves`.

Contents, in order:
* `G4Conj` (generic, any category with pullbacks): the comparison `cmp` between base changes
  along `f₂ = s ≫ f₁` respects multiplication and unit; the conjugate `conj` of a morphism; the
  conjugate of a monoid homomorphism is one (`conj_isMonHom`); multiplicativity, functoriality.
* The bridge `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` for finite Galois `L ⊆ ℚ̄`
  (`galUnramifiedOutside_iff`; the new direction via Mathlib's profinite transitivity and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, as in glue-b3b's `exists_inertia_neg`).
* The Hom-field core (`homField_core`: Minkowski + infinite Galois theory) and its numerical form
  (`homField_le_heightD`).
* The Hom lattice of a finite family of abelian varieties over `ℚ̄`, its rank (leaf
  `PkgI3.HomFreeFinite`), its `ℓ`-adic faithfulness.
* The conjugates of a model `A/K` (`conjData`) and the conjugation action of `G_ℚ` on their Hom
  lattice (`conjAction`, `conjActionExists`): the Weil-restriction step, constructed.
* Continuity from EGA IV₃ 8.8.2 (`MorphismsDescend` → `conjAction_continuous`), inertia from good
  reduction (`InertiaFixesHoms` → `conjAction_inertia`), the headline, and the consumers
  (`b3_of_homField` for G7, `cm_degree_of_homField` for the CM branch).

Inputs are `def … : Prop` hypotheses; no `sorry`, no `axiom`.
-/

section ConjSec

/-!
## Part A: conjugating homomorphisms of base-changed group objects

Generic category theory (any `C` with pullbacks). For a monoid object `X` over `S` and two base
changes along `f₁, f₂ : T → S` with `f₂ = s ≫ f₁`, the comparison `g : X ×_{S,f₂} T → X ×_{S,f₁} T`
(over `s : T → T`) respects the multiplications, and the conjugate of a monoid homomorphism along
`g` (the unique lift through the pullback square) is a monoid homomorphism.
In the application `S = Spec K`, `T = Spec ℚ̄`, `f₁ = Spec e`, `s = Spec σ`, `f₂ = Spec (σ ∘ e)`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace G4Conj

variable {C : Type*} [Category C] [HasPullbacks C] {S T : C}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- The multiplication of the base change, followed by the projection to `X`. -/
theorem mul_left_fst (f : T ⟶ S) (X : Over S) [MonObj X] :
    (μ[(Over.pullback f).obj X]).left ≫ pullback.fst X.hom f =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst X.hom f)
        (pullback.snd _ _ ≫ pullback.fst X.hom f)
        (by
          simp only [Category.assoc, pullback.condition]
          exact pullback.condition_assoc f) ≫ μ[X].left := by
  show ((Functor.LaxMonoidal.μ (Over.pullback f) X X) ≫ (Over.pullback f).map μ[X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact Over.μ_pullback_left_fst_fst X X
  · simp only [Category.assoc, pullback.lift_snd]
    exact Over.μ_pullback_left_fst_snd X X


/-- The unit of the base change, followed by the projection to `X`. -/
theorem one_left_fst (f : T ⟶ S) (X : Over S) [MonObj X] :
    (η[(Over.pullback f).obj X]).left ≫ pullback.fst X.hom f = f ≫ η[X].left := by
  show ((Functor.LaxMonoidal.ε (Over.pullback f)) ≫ (Over.pullback f).map η[X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc, Over.ε_pullback_left]
  congr 1
  rw [IsIso.inv_comp_eq]
  have := pullback.condition (f := 𝟙 S) (g := f)
  simpa using this

/-! ### The comparison map over `s` -/

section Cmp

variable (X : Over S) {f₁ f₂ : T ⟶ S} (s : T ⟶ T) (h : f₂ = s ≫ f₁)

/-- `X ×_{f₂} T → X ×_{f₁} T` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def cmp : pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

@[reassoc (attr := simp)]
theorem cmp_fst : cmp X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp_snd : cmp X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s :=
  pullback.lift_snd _ _ _

/-- The comparison square over `s` is a pullback. -/
theorem cmp_isPullback :
    IsPullback (cmp X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : cmp X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [cmp_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [cmp_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

/-- `cmp` on the self-products. -/
noncomputable def cmp2 :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ cmp X s h) (pullback.snd _ _ ≫ cmp X s h) (by
    show (pullback.fst _ _ ≫ cmp X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ cmp X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, cmp_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem cmp2_fst : cmp2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ cmp X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp2_snd : cmp2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ cmp X s h :=
  pullback.lift_snd _ _ _

/-- **The comparison respects the multiplications.** -/
theorem cmp_mul [MonObj X] :
    (μ[(Over.pullback f₂).obj X]).left ≫ cmp X s h =
      cmp2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, Category.assoc, mul_left_fst, mul_left_fst,
      ← Category.assoc (cmp2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, cmp2_fst_assoc, cmp_fst]
    · simp only [Category.assoc, pullback.lift_snd, cmp2_snd_assoc, cmp_fst]
  · rw [Category.assoc, cmp_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      cmp2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [cmp2_fst_assoc, cmp_snd, Category.assoc]

/-- **The comparison respects the units.** -/
theorem cmp_one [MonObj X] :
    (η[(Over.pullback f₂).obj X]).left ≫ cmp X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, one_left_fst, Category.assoc, one_left_fst, h, Category.assoc]
  · rw [Category.assoc, cmp_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end Cmp


/-! ### Conjugating morphisms -/

section ConjMor

variable (X Y : Over S) {f₁ f₂ g₁ g₂ : T ⟶ S} (s : T ⟶ T) (hf : f₂ = s ≫ f₁) (hg : g₂ = s ≫ g₁)

/-- Two maps into `Y ×_{g₂} T` agreeing after `cmp` and after the structure map are equal. -/
theorem ext_cmp {Z : C} (a b : Z ⟶ pullback Y.hom g₂) (h1 : a ≫ cmp Y s hg = b ≫ cmp Y s hg)
    (h2 : a ≫ pullback.snd Y.hom g₂ = b ≫ pullback.snd Y.hom g₂) : a = b := by
  apply pullback.hom_ext _ h2
  rw [← cmp_fst Y s hg, ← Category.assoc, h1, Category.assoc]

/-- **The conjugate of a morphism** `φ : X_{f₁} → Y_{g₁}` (over `T`): the morphism
`X_{f₂} → Y_{g₂}` with `σφ ∘ cmp = cmp ∘ φ` (`conj_cmp`), unique (`conj_unique`). -/
noncomputable def conj (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (Over.pullback f₂).obj X ⟶ (Over.pullback g₂).obj Y :=
  Over.homMk (pullback.lift (cmp X s hf ≫ φ.left ≫ pullback.fst Y.hom g₁)
    (pullback.snd X.hom f₂) (by
      rw [Category.assoc, Category.assoc, pullback.condition]
      have hw : φ.left ≫ pullback.snd Y.hom g₁ = pullback.snd X.hom f₁ := Over.w φ
      rw [reassoc_of% hw, cmp_snd_assoc, hg]))
    (pullback.lift_snd _ _ _)

@[reassoc]
theorem conj_cmp (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (conj X Y s hf hg φ).left ≫ cmp Y s hg = cmp X s hf ≫ φ.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, cmp_fst]
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, cmp_snd]
    have hw : φ.left ≫ pullback.snd Y.hom g₁ = pullback.snd X.hom f₁ := Over.w φ
    rw [hw, cmp_snd]
    exact pullback.lift_snd_assoc _ _ _ _

theorem conj_unique (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y)
    (ψ : (Over.pullback f₂).obj X ⟶ (Over.pullback g₂).obj Y)
    (hψ : ψ.left ≫ cmp Y s hg = cmp X s hf ≫ φ.left) : ψ = conj X Y s hf hg φ := by
  apply Over.OverMorphism.ext
  apply ext_cmp Y s hg
  · rw [hψ, conj_cmp]
  · exact (Over.w ψ).trans (Over.w (conj X Y s hf hg φ)).symm

theorem tensor_cmp2 (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (conj X Y s hf hg φ ⊗ₘ conj X Y s hf hg φ).left ≫ cmp2 Y s hg =
      cmp2 X s hf ≫ (φ ⊗ₘ φ).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, Category.assoc]
    erw [Over.tensorHom_left_fst_assoc, Over.tensorHom_left_fst]
    rw [conj_cmp, cmp2_fst_assoc]
  · rw [Category.assoc, cmp2_snd, Category.assoc]
    erw [Over.tensorHom_left_snd_assoc, Over.tensorHom_left_snd]
    rw [conj_cmp, cmp2_snd_assoc]

/-- **The conjugate of a monoid homomorphism is a monoid homomorphism.** -/
theorem conj_isMonHom [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) [IsMonHom φ] :
    IsMonHom (conj X Y s hf hg φ) where
  one_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s hg
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_one, Category.assoc,
        ← Over.comp_left, IsMonHom.one_hom, cmp_one]
    · exact (Over.w _).trans (Over.w _).symm
  mul_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s hg
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_mul, Category.assoc,
        ← Over.comp_left, IsMonHom.mul_hom, Over.comp_left, Over.comp_left, Category.assoc,
        cmp_mul, reassoc_of% (tensor_cmp2 X Y s hf hg φ)]
    · exact (Over.w _).trans (Over.w _).symm

/-- `conj_isMonHom` with the hypothesis explicit (for instances found only up to unfolding). -/
theorem conj_isMonHom' [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) (hφ : IsMonHom φ) :
    IsMonHom (conj X Y s hf hg φ) :=
  conj_isMonHom X Y s hf hg φ

theorem lift_cmp2 (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (lift (conj X Y s hf hg φ) (conj X Y s hf hg ψ)).left ≫ cmp2 Y s hg =
      cmp X s hf ≫ (lift φ ψ).left := by
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
      conj_cmp]
  · rw [Category.assoc, cmp2_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      conj_cmp]

/-- **Conjugation is multiplicative** for the pointwise product of morphisms into a monoid. -/
theorem conj_mul [MonObj Y] (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf hg (φ * ψ) = conj X Y s hf hg φ * conj X Y s hf hg ψ := by
  symm
  apply conj_unique
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_mul,
    ← Category.assoc, lift_cmp2, Category.assoc]

theorem conj_one [MonObj Y] :
    conj X Y s hf hg (1 : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) = 1 := by
  symm
  apply conj_unique
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_one,
    ← Category.assoc, ← Category.assoc]
  congr 1
  have e1 : (toUnit ((Over.pullback f₂).obj X)).left = pullback.snd X.hom f₂ :=
    (Category.comp_id _).symm.trans (Over.w (toUnit ((Over.pullback f₂).obj X)))
  have e2 : (toUnit ((Over.pullback f₁).obj X)).left = pullback.snd X.hom f₁ :=
    (Category.comp_id _).symm.trans (Over.w (toUnit ((Over.pullback f₁).obj X)))
  rw [e1, e2]
  exact (cmp_snd X s hf).symm

/-- Conjugation along equal maps `s = s'` agrees. -/
theorem conj_congr {s' : T ⟶ T} (hs : s = s') (hf' : f₂ = s' ≫ f₁) (hg' : g₂ = s' ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf hg φ = conj X Y s' hf' hg' φ := by
  subst hs; rfl

/-- `cmp` along the identity is the identity. -/
theorem cmp_self (hs : s = 𝟙 T) (hf₀ : f₁ = s ≫ f₁) : cmp X s hf₀ = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [cmp_snd, hs, Category.comp_id, Category.id_comp]

/-- Conjugation along the identity is the identity. -/
theorem conj_self (hs : s = 𝟙 T) (hf₀ : f₁ = s ≫ f₁) (hg₀ : g₁ = s ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf₀ hg₀ φ = φ := by
  symm
  apply conj_unique
  rw [cmp_self X s hs hf₀, cmp_self Y s hs hg₀]
  erw [Category.comp_id, Category.id_comp]

/-- `cmp` composes. -/
theorem cmp_comp {f₃ : T ⟶ S} (s' : T ⟶ T) (h₃₂ : f₃ = s' ≫ f₂) (h₃₁ : f₃ = (s' ≫ s) ≫ f₁) :
    cmp X (s' ≫ s) h₃₁ = cmp X s' h₃₂ ≫ cmp X s hf := by
  apply pullback.hom_ext
  · simp
  · simp

/-- **Conjugation composes.** -/
theorem conj_comp {f₃ g₃ : T ⟶ S} (s' : T ⟶ T) (hf₃₂ : f₃ = s' ≫ f₂) (hg₃₂ : g₃ = s' ≫ g₂)
    (hf₃₁ : f₃ = (s' ≫ s) ≫ f₁) (hg₃₁ : g₃ = (s' ≫ s) ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y (s' ≫ s) hf₃₁ hg₃₁ φ = conj X Y s' hf₃₂ hg₃₂ (conj X Y s hf hg φ) := by
  symm
  apply conj_unique
  rw [cmp_comp Y s hg s' hg₃₂ hg₃₁, cmp_comp X s hf s' hf₃₂ hf₃₁, conj_cmp_assoc, conj_cmp,
    Category.assoc]

end ConjMor

end G4Conj

end ConjSec

namespace G4WeilRes

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField
open scoped Pointwise

/-! ## Places over `p` exist -/

/-- There is a valuation subring of `ℚ̄` over every prime `p`. -/
theorem exists_liesOver (p : ℕ) (hp : p.Prime) : ∃ w : ValuationSubring Qbar, LiesOver w p := by
  let A : Subring Qbar := ⊥
  let pA : A := ⟨(p : Qbar), by simpa using (⊥ : Subring Qbar).natCast_mem p⟩
  let I : Ideal A := Ideal.span {pA}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
    have h2 : ((n * p : ℤ) : Qbar) = ((1 : ℤ) : Qbar) := by
      have := congrArg Subtype.val ha
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      push_cast
      rw [hn]; exact this
    have h3 : n * (p : ℤ) = 1 := Int.cast_injective h2
    have h4 : (p : ℤ) ∣ 1 := ⟨n, by rw [← h3]; ring⟩
    have := Int.eq_one_of_dvd_one (by positivity) h4
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, ?_⟩
  have hmem : (p : Qbar) ∈ B.nonunits := hB ⟨pA, Ideal.subset_span rfl, rfl⟩
  exact (ValuationSubring.mem_nonunits_iff B).mp hmem

/-! ## A Galois automorphism maps a normal subfield into itself -/

theorem map_mem_of_normal (L : IntermediateField ℚ Qbar) [Normal ℚ L] (σ : Gal) {y : Qbar}
    (hy : y ∈ L) : σ y ∈ L := by
  have h := AlgEquiv.restrictNormal_commutes σ L ⟨y, hy⟩
  rw [← show algebraMap L Qbar ⟨y, hy⟩ = y from rfl, ← h]
  exact (AlgEquiv.restrictNormal σ L ⟨y, hy⟩).2

/-! ## Lifting a residually trivial automorphism of `L` into an inertia group -/

/-- `σ` acts trivially modulo `w` on the algebraic integers of `L`. -/
def ResTrivOn (L : IntermediateField ℚ Qbar) (w : ValuationSubring Qbar) (σ : Gal) : Prop :=
  ∀ y : Qbar, IsIntegral ℤ y → y ∈ L → w.valuation (σ y - y) < 1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The inertia lift.** Let `L ⊆ ℚ̄` be finite Galois, `w` a place over `p` and `σ ∈ G_ℚ`
acting trivially modulo `w` on the algebraic integers of `L`. Then some `s ∈ I_w` agrees with
`σ` on `L`. -/
theorem exists_inertia_restrict (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (σ : Gal) (hσ : ResTrivOn L w σ) :
    ∃ s : Gal, s ∈ inertiaGQ w ∧ ∀ y ∈ L, s y = σ y := by
  classical
  let H : Subgroup Gal := L.fixingSubgroup
  have hH : ∀ g : Gal, g ∈ H ↔ ∀ y ∈ L, g y = y := fun g =>
    IntermediateField.mem_fixingSubgroup_iff L g
  have hHopen : IsOpen (H : Set Gal) := IntermediateField.fixingSubgroup_isOpen L
  have hHclosed : IsClosed (H : Set Gal) := Subgroup.isClosed_of_isOpen H hHopen
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  let Q := centerIdeal w
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  -- elements of `A` lie in `L`
  have hAL : ∀ a : A, ((a : B) : Qbar) ∈ L := by
    intro a
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro g hg
    have := a.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hAint : ∀ a : A, IsIntegral ℤ ((a : B) : Qbar) := fun a =>
    (mem_integralClosure_iff ℤ Qbar).mp (a : B).2
  -- the valuation input on `A`
  have hAval : ∀ (a : A) (τ : Gal), ResTrivOn L w τ →
      w.valuation (((a : B) : Qbar) - τ ((a : B) : Qbar)) < 1 := by
    intro a τ hτ
    rw [Valuation.map_sub_swap]
    exact hτ _ (hAint a) (hAL a)
  -- `σ⁻¹` is also residually trivial on `L`
  have hσi : ResTrivOn L w σ⁻¹ := by
    intro y hy hyL
    have hy' : IsIntegral ℤ ((σ⁻¹ : Gal) y) := hy.map ((σ⁻¹ : Gal) : Qbar →+* Qbar).toIntAlgHom
    have h := hσ _ hy' (map_mem_of_normal L σ⁻¹ hyL)
    have hss : σ ((σ⁻¹ : Gal) y) = y := by
      show (σ * σ⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [hss, Valuation.map_sub_swap] at h
    exact h
  -- step 1: `σ • Q` and `Q` lie over the same prime of `A`
  have hunder : (σ • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal]
    have h := hAval a σ⁻¹ hσi
    show w.valuation ((σ⁻¹ : Gal) ((a : B) : Qbar)) < 1 ↔ w.valuation ((a : B) : Qbar) < 1
    constructor
    · intro h1
      have : ((a : B) : Qbar) = (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) +
          (σ⁻¹ : Gal) ((a : B) : Qbar) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
    · intro h1
      have : (σ⁻¹ : Gal) ((a : B) : Qbar) = ((a : B) : Qbar) -
          (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h)
  -- step 2: transitivity over `A` gives `τ` stabilizing `Q` and agreeing with `σ` on `L`
  haveI hσQ : (σ • Q).IsPrime := by
    show (σ • centerIdeal w).IsPrime
    rw [← centerIdeal_smul]; infer_instance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (σ • Q) Q hunder
  let τ : Gal := (g : Gal) * σ
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * σ) • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτL : ∀ y ∈ L, τ y = σ y := by
    intro y hy
    show (g : Gal) (σ y) = σ y
    exact (hH g).mp g.2 _ (map_mem_of_normal L σ hy)
  have hτ : ResTrivOn L w τ := by
    intro y hy hyL
    rw [hτL y hyL]; exact hσ y hy hyL
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq, mem_centerIdeal]
    have h := hAval a τ hτ
    rw [Valuation.map_sub_swap] at h
    exact h)
  -- step 4: Mathlib's surjectivity gives `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  have hkL : ∀ y ∈ L, k y = y := (hH k).mp (h' : H).2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • Q = Q
      rw [mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · intro y hy
    show k⁻¹ (τ y) = σ y
    rw [hτL y hy]
    have hk' : k⁻¹ ∈ H := H.inv_mem (h' : H).2
    exact (hH _).mp hk' _ (map_mem_of_normal L σ hy)

/-! ## The bridge -/

/-- `P.under ℤ = (p)` for a prime of `𝓞 L` containing the prime `p`. -/
theorem under_eq_span {L : IntermediateField ℚ Qbar} [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P) :
    P.under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using hpP
  have hle : Ideal.span {(p : ℤ)} ≤ P.under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_isPrime (algebraMap ℤ (𝓞 L)) P).ne_top hle).symm

/-- **Bridge (glue, proved).** If every inertia group of `G_ℚ` over `p` fixes the finite Galois
field `L ⊆ ℚ̄`, then `L` is unramified at `p` in glue-descent's ideal-theoretic sense. -/
theorem unramifiedAt_of_inertia_le (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime)
    (h : ∀ w : ValuationSubring Qbar, LiesOver w p → inertiaGQ w ≤ L.fixingSubgroup) :
    UnramifiedAt L p := by
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  intro P hP hpP
  obtain ⟨w, hw⟩ := exists_liesOver p hp
  let P₀ : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal w).comap (embW L w)
  haveI hP₀prime : P₀.IsPrime := Ideal.comap_isPrime _ _
  have hpP₀ : ((p : ℤ) : 𝓞 L) ∈ P₀ := by
    show embW L w ((p : ℤ) : 𝓞 L) ∈ IsLocalRing.maximalIdeal w
    rw [ValuationSubring.valuation_lt_one_iff]
    have : ((embW L w ((p : ℤ) : 𝓞 L) : w) : Qbar) = (p : Qbar) := by
      simp [embW, emb]
    rw [this]; exact hw
  let G := L ≃ₐ[ℚ] L
  have hunder : P.under ℤ = P₀.under ℤ := by
    rw [under_eq_span p hp P hpP, under_eq_span p hp P₀ hpP₀]
  -- the inertia group of `P₀` in `Gal(L/ℚ)` is trivial
  have htriv : ∀ g ∈ P₀.inertia G, g = 1 := by
    intro g hg
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := Qbar) (K₁ := L) g
    have hσL : ∀ x : L, algebraMap L Qbar (g x) = σ (algebraMap L Qbar x) := by
      intro x
      rw [← hσ]; exact AlgEquiv.restrictNormal_commutes σ L x
    have hres : ResTrivOn L w σ := by
      intro y hy hyL
      let x : 𝓞 L := ⟨⟨y, hyL⟩, by
        rw [mem_integralClosure_iff]
        exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Qbar)
          (algebraMap L Qbar).injective).mp hy⟩
      have hx := (Ideal.mem_inertia.mp hg) x
      change embW L w (g • x - x) ∈ IsLocalRing.maximalIdeal w at hx
      rw [ValuationSubring.valuation_lt_one_iff] at hx
      have he1 : ((embW L w (g • x - x) : w) : Qbar) = emb L (g • x) - emb L x := by
        show emb L (g • x - x) = _
        rw [map_sub]
      have he2 : emb L (g • x) = σ y := by
        simp only [emb, RingHom.comp_apply]
        rw [show σ y = σ (algebraMap L Qbar ⟨y, hyL⟩) from rfl, ← hσL]
        rfl
      have he : ((embW L w (g • x - x) : w) : Qbar) = σ y - y := by
        rw [he1, he2]; rfl
      rw [he] at hx; exact hx
    obtain ⟨s, hs, hsL⟩ := exists_inertia_restrict L p hp w hw σ hres
    have hsfix := (IntermediateField.mem_fixingSubgroup_iff L s).mp (h w hw hs)
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L Qbar).injective
    rw [hσL x]
    show σ (x : Qbar) = (x : Qbar)
    rw [← hsL _ x.2, hsfix _ x.2]
  have hcard : Nat.card (P₀.inertia G) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  have e₀ : P₀.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G,
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P₀.under ℤ) P₀, hcard]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G, hunder,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G, e₀]

/-- The Galois form of "unramified outside `T`" gives glue-descent's form at every `p ∉ T`. -/
theorem unramifiedAt_of_galUnramifiedOutside (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) (h : GalUnramifiedOutside L T) :
    ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  fun p hpT => unramifiedAt_of_inertia_le L p p.2 (fun w hw => h p p.2 hpT w hw)

/-- And conversely (glue-b3-unram's bridge): the two forms agree on finite Galois fields. -/
theorem galUnramifiedOutside_iff (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) :
    GalUnramifiedOutside L T ↔ ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  ⟨unramifiedAt_of_galUnramifiedOutside L T, fun h p hp hpT w hw =>
    inertia_le_of_unramifiedAt L p hp (h ⟨p, hp⟩ hpT) w hw⟩


/-! ## The Hom field: the core theorem (Minkowski + infinite Galois theory + the bridge)

N5 L544-563, with the Weil restriction `W₀ = Res_{K/ℚ} A` replaced by what the argument uses of
it: a free `ℤ`-module `M` of rank `r` (the geometric endomorphism lattice of `W₀`, i.e. the direct
sum of the Hom groups among the conjugates of `A`) with a `ℤ`-linear action of `G_ℚ` that is
continuous (every element has an open stabilizer: each geometric homomorphism is defined over a
number field) and on which every inertia group over a prime `p ∉ T` acts trivially. -/

section Core

variable {M : Type*} [AddCommGroup M]

/-- The `GL_r(ℤ)`-realization of the automorphisms of a free `ℤ`-module with a basis. -/
noncomputable def toGL {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    (M ≃ₗ[ℤ] M) →* Matrix.GeneralLinearGroup (Fin r) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ M).symm.toMonoidHom

theorem toGL_injective {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    Function.Injective (toGL b) := by
  intro f g h
  have h1 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin r) ℤ =>
    (u : Matrix (Fin r) (Fin r) ℤ)) h
  have h2 : (f : M →ₗ[ℤ] M) = g := (LinearMap.toMatrixAlgEquiv b).injective h1
  exact LinearEquiv.toLinearMap_injective h2

theorem toGL_eq_one_iff {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (f : M ≃ₗ[ℤ] M) :
    toGL b f = 1 ↔ f = 1 :=
  ⟨fun h => toGL_injective b (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- An automorphism is the identity iff it fixes a basis. -/
theorem eq_one_iff_basis {ι : Type*} (b : Module.Basis ι ℤ M) (f : M ≃ₗ[ℤ] M) :
    f = 1 ↔ ∀ i, f (b i) = b i := by
  constructor
  · intro h i; rw [h]; rfl
  · intro h
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    simpa using h i

/-- **G4, the Hom field (core, proved).** Let `K ⊆ ℚ̄` be finite Galois, unramified outside `T`
(Galois form), and let `G_ℚ` act `ℤ`-linearly on a free `ℤ`-module `M` with basis indexed by
`Fin r`, continuously (open stabilizers), with every inertia group over every prime `p ∉ T`
acting trivially. Then there is a finite Galois `L ⊇ K` such that `G_L` acts trivially on `M`
(`L` defines every element of `M`), `[L:ℚ] ≤ [K:ℚ]·3^{r²}` (Minkowski), and `L` is unramified
outside `T`, in both the Galois form and glue-descent's ideal-theoretic form. -/
theorem homField_core (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ Module.finrank ℚ K * 3 ^ (r ^ 2) ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact toGL_eq_one_iff b (ρ σ)
  -- the kernel is open
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  haveI hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  haveI hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  -- `[E:ℚ] = |ρ(G_ℚ)| ≤ 3^{r²}`
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  have hE3 : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := by
    rw [hcardE]; exact GlueRepo.TorsionFree.card_le_three_pow ρ'.range
  -- `L = E ⊔ K`
  refine ⟨E ⊔ K, inferInstance, inferInstance, le_sup_right, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have h1 : σ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hσ
    rw [hE] at h1
    exact h1
  · calc Module.finrank ℚ ↥(E ⊔ K) ≤ Module.finrank ℚ E * Module.finrank ℚ K :=
          IntermediateField.finrank_sup_le E K
      _ ≤ 3 ^ (r ^ 2) * Module.finrank ℚ K := Nat.mul_le_mul_right _ hE3
      _ = Module.finrank ℚ K * 3 ^ (r ^ 2) := Nat.mul_comm _ _
  · have hgal : GalUnramifiedOutside (E ⊔ K) T := by
      intro p hp hpT w hw s hs
      rw [IntermediateField.fixingSubgroup_sup]
      refine ⟨?_, hK p hp hpT w hw hs⟩
      rw [hE]
      exact hinert p hp hpT w hw s hs
    exact hgal
  · apply unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨?_, hK p hp hpT w hw hs⟩
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 with the manuscript's numbers.** If `[K:ℚ] ≤ F₀ = 324!` and `r ≤ 16F₀²` (N5 L547-548),
the Hom field has `[L:ℚ] ≤ D = F₀·3^{256F₀⁴}` (`ZInQ.heightD`). -/
theorem homField_le_heightD (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨L, h1, h2, hKL, hdef, hdeg, hgal, hram⟩ := homField_core K b ρ hcont T hK hinert
  refine ⟨L, h1, h2, hKL, hdef, ?_, hgal, hram⟩
  exact hdeg.trans (GlueRepo.Numerics.a8_degree ZInQ.Compiler.Precision.heightD_eq hKF le_rfl hr)

end Core


/-! ## The lattice of the conjugates: rank, faithfulness, and the abelian-variety instantiation

The manuscript's `End(W₀_ℚ̄) = ⊕_{σ,τ} Hom(σA, τA)`: here the direct sum over ordered pairs of
`n` abelian varieties over `ℚ̄` (the conjugates of `A`, `n ≤ [K:ℚ] ≤ F₀`), as a product of
`PkgI3.AbVar.Hom` groups. -/

section Lattice

/-- **Rank of the lattice (glue, proved).** A product over ordered pairs `(i, j) ∈ n × n` of free
finite `ℤ`-modules of rank `≤ c` is free and finite of rank `≤ c·n²`. -/
theorem pi_rank_le {ι : Type*} [Fintype ι] {c : ℕ} (H : ι × ι → Type*) [∀ ij, AddCommGroup (H ij)]
    [∀ ij, Module.Free ℤ (H ij)] [∀ ij, Module.Finite ℤ (H ij)]
    (hH : ∀ ij, Module.finrank ℤ (H ij) ≤ c) :
    Module.finrank ℤ (∀ ij, H ij) ≤ c * Fintype.card ι ^ 2 := by
  rw [Module.finrank_pi_fintype]
  calc ∑ ij, Module.finrank ℤ (H ij) ≤ ∑ _ij : ι × ι, c :=
        Finset.sum_le_sum fun ij _ => hH ij
    _ = c * Fintype.card ι ^ 2 := by simp [Fintype.card_prod, sq, mul_comm]

/-- **Inertia acts trivially on the lattice (glue, proved; N5 L559-561).** If the lattice `M`
embeds equivariantly and injectively into a module `N` (in the application: `ℓ`-adic
realization, `Hom(σA, τA) → Hom_{ℤ_ℓ}(T_ℓ σA, T_ℓ τA)`, injective by Mumford §19 Thm 3, the leaf
`PkgI3.HomFreeFinite`), then every `s` acting trivially on `N` (in the application: inertia at
`p ∉ T`, by Néron–Ogg–Shafarevich, the leaf `PkgI2.NeronOggShafarevich`) acts trivially on `M`. -/
theorem trivial_of_faithful {G M N : Type*} [Group G] [AddCommGroup M] [AddCommGroup N]
    (ρ : G →* (M ≃ₗ[ℤ] M)) (τ : G →* (N ≃ₗ[ℤ] N)) (ι : M →+ N) (hι : Function.Injective ι)
    (heq : ∀ g m, ι (ρ g m) = τ g (ι m)) (s : G) (hs : τ s = 1) : ρ s = 1 := by
  apply LinearEquiv.ext
  intro m
  apply hι
  rw [heq, hs]
  rfl

/-- The `ℓ`-adic side: if `s` acts trivially on the Tate modules `T i`, it acts trivially on
`Hom_{ℤ_ℓ}(T i, T j)` by conjugation. -/
theorem conj_trivial {R : Type*} [CommRing R] {T₁ T₂ : Type*} [AddCommGroup T₁] [Module R T₁]
    [AddCommGroup T₂] [Module R T₂] (a₁ : T₁ ≃ₗ[R] T₁) (a₂ : T₂ ≃ₗ[R] T₂) (h₁ : a₁ = 1)
    (h₂ : a₂ = 1) (φ : T₁ →ₗ[R] T₂) :
    (a₂ : T₂ →ₗ[R] T₂) ∘ₗ φ ∘ₗ (a₁.symm : T₁ →ₗ[R] T₁) = φ := by
  subst h₁; subst h₂; rfl

open PkgI3 PkgI3.AbVar CategoryTheory MonObj

/-- The geometric Hom lattice of `n` abelian varieties over `ℚ̄`: `⊕_{(i,j)} Hom(A i, A j)`. -/
abbrev HomLattice {Idx : Type} (A : Idx → AbVar Qbar) : Type :=
  ∀ ij : Idx × Idx, AbVar.Hom (A ij.1) (A ij.2)

/-- **Mumford's bound on the lattice (from the leaf `HomFreeFinite`).** For abelian surfaces
`A i` over `ℚ̄`, the lattice `⊕ Hom(A i, A j)` is free and finite of rank `≤ 16n²`. -/
theorem homLattice_free (hHFF : HomFreeFinite) {Idx : Type} [Fintype Idx] (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2) :
    Module.Free ℤ (HomLattice A) ∧ Module.Finite ℤ (HomLattice A) ∧
      Module.finrank ℤ (HomLattice A) ≤ 16 * Fintype.card Idx ^ 2 := by
  haveI : ∀ ij : Idx × Idx, Module.Free ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).1
  haveI : ∀ ij : Idx × Idx, Module.Finite ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).2.1
  refine ⟨inferInstance, inferInstance, pi_rank_le _ fun ij => ?_⟩
  have h := (hHFF Qbar (A ij.1) (A ij.2)).2.2.1
  rw [hdim, hdim] at h
  have h16 : ((Module.finrank ℤ (AbVar.Hom (A ij.1) (A ij.2)) : ℕ∞) : WithBot ℕ∞) ≤
      (((16 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    refine h.trans (le_of_eq ?_)
    rfl
  exact_mod_cast h16

/-- **The `ℓ`-adic realization is faithful (from the leaf `HomFreeFinite`).** `Hom(A, B) →
Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective for `ℓ` invertible in `k`: `HomFreeFinite` gives
injectivity on `ℤ_ℓ ⊗ Hom(A, B)`, and `Hom(A, B) → ℤ_ℓ ⊗ Hom(A, B)` is injective because
`Hom(A, B)` is free (flat) and `ℤ → ℤ_ℓ` is injective. This is the `ι` of `trivial_of_faithful`
in the application (N5 L559-561). -/
theorem tateHom_injective (hHFF : HomFreeFinite) {k : Type} [Field k] (A B : AbVar k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) : Function.Injective (tateHom ℓ A B) := by
  have hinj := (hHFF k A B).2.2.2 ℓ hℓ
  haveI : Module.Free ℤ (AbVar.Hom A B) := (hHFF k A B).1
  let j : AbVar.Hom A B →ₗ[ℤ] TensorProduct ℤ ℤ_[ℓ] (AbVar.Hom A B) :=
    ((Algebra.linearMap ℤ ℤ_[ℓ]).rTensor (AbVar.Hom A B)).comp
      (TensorProduct.lid ℤ (AbVar.Hom A B)).symm.toLinearMap
  have hj : Function.Injective j := by
    have h1 : Function.Injective (Algebra.linearMap ℤ ℤ_[ℓ]) := by
      intro a b hab
      exact Int.cast_injective hab
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ h1).comp
      (TensorProduct.lid ℤ (AbVar.Hom A B)).symm.injective
  have hcomp : ∀ f, tateHomZl ℓ A B (j f) = tateHom ℓ A B f := by
    intro f
    have hjf : j f = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] f := by
      show (Algebra.linearMap ℤ ℤ_[ℓ]).rTensor (AbVar.Hom A B)
        ((TensorProduct.lid ℤ (AbVar.Hom A B)).symm f) = _
      erw [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
      congr 1
    rw [hjf]
    exact (TensorProduct.lift.tmul _ _).trans (one_smul _ _)
  intro f g hfg
  apply hj
  apply hinj
  rw [hcomp, hcomp]
  exact hfg


/-- The `ℓ`-adic realization of the lattice: `f ↦ (T_ℓ(f_{ij}))_{ij}`. -/
noncomputable def tateLattice (ℓ : ℕ) [Fact ℓ.Prime] {Idx : Type} (A : Idx → AbVar Qbar) :
    HomLattice A →+ (∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ) :=
  Pi.addMonoidHom fun ij => (tateHom ℓ (A ij.1) (A ij.2)).comp (Pi.evalAddMonoidHom _ ij)

/-- The realization of the lattice is injective (leaf `HomFreeFinite`; `ℓ ≠ 0` in `ℚ̄`). -/
theorem tateLattice_injective (hHFF : HomFreeFinite) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {Idx : Type}
    (A : Idx → AbVar Qbar) : Function.Injective (tateLattice ℓ A) := by
  intro f g h
  funext ij
  have hne : (ℓ : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero
  exact tateHom_injective hHFF (A ij.1) (A ij.2) ℓ hne (congrFun h ij)

/-- **The inertia hypothesis from the `ℓ`-adic side (glue, proved).** If `G_ℚ` acts on the
realization `∏ Hom_{ℤ_ℓ}(T_ℓ A_i, T_ℓ A_j)` compatibly with `ρ` (equivariance: open, needs the
action on points), and inertia over `p ∉ T` acts trivially there (Néron–Ogg–Shafarevich for the
conjugates, which have good reduction above `p ∉ T`, G3), then `hinert` of
`homField_of_conjugates` holds. -/
theorem inertia_of_tate (hHFF : HomFreeFinite) (ℓ : ℕ) [Fact ℓ.Prime] {Idx : Type}
    (A : Idx → AbVar Qbar) (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (τ : Gal →* ((∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ) ≃ₗ[ℤ]
      (∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ)))
    (heq : ∀ σ m, tateLattice ℓ A (ρ σ m) = τ σ (tateLattice ℓ A m)) (T : Finset ℕ)
    (htate : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, τ s = 1) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1 :=
  fun p hp hpT w hw s hs => trivial_of_faithful ρ τ (tateLattice ℓ A)
    (tateLattice_injective hHFF ℓ A) heq s (htate p hp hpT w hw s hs)


/-- **G4 on the abelian-variety layer.** Let `K ⊆ ℚ̄` be finite Galois with `[K:ℚ] ≤ F₀`,
unramified outside `T`; let `A 0, …, A (n-1)` be abelian surfaces over `ℚ̄` (the conjugates of
the fibre object, indexed by a finite type of size `≤ F₀`, e.g. the embeddings `K → ℚ̄`), and let `G_ℚ` act `ℤ`-linearly on `⊕ Hom(A i, A j)` (the conjugation
action; its construction is the open part of G4) continuously and with every inertia group over
`p ∉ T` acting trivially. Then the Hom field `L ⊇ K` exists: finite Galois, `[L:ℚ] ≤ D`, every
element of the lattice is fixed by `G_L`, and `L` is unramified outside `T` (both forms).
Leaf used: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3). -/
theorem homField_of_conjugates (hHFF : HomFreeFinite)
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {Idx : Type} [Fintype Idx] (hn : Fintype.card Idx ≤ ZInQ.heightF0) (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2)
    (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (hcont : ∀ m : HomLattice A, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨hfree, hfin, hrank⟩ := homLattice_free hHFF A hdim
  have hr : Module.finrank ℤ (HomLattice A) ≤ 16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  exact homField_le_heightD K hKF hr (Module.finBasisOfFinrankEq ℤ (HomLattice A) rfl) ρ hcont T
    hK hinert

/-! ### The conjugation action

For `σ ∈ G_ℚ`, a conjugate of an abelian variety `X` over `ℚ̄` is an `X'` with a pullback square
`X' → X` over `Spec σ : Spec ℚ̄ → Spec ℚ̄` (the relation used by leaf-qm-fp's `IsBaseChangeOf`).
`ConjData` records a finite family closed under conjugation: `A i` is the `σ`-conjugate of
`A (σ⁻¹·i)` through `g σ i : A i → A (σ⁻¹·i)`. `IsConjAction D ρ` says that `ρ σ` sends
`f : A (σ⁻¹·i) → A (σ⁻¹·j)` to its conjugate `σf : A i → A j`, the morphism with
`g σ j ∘ σf = f ∘ g σ i`. Such a `ρ` is unique (`isConjAction_unique`), and for the conjugates of
a model `A/K` it exists (`conjAction`, `conjActionExists`). -/

open AlgebraicGeometry

/-- `Spec σ : Spec ℚ̄ → Spec ℚ̄`. -/
noncomputable abbrev specGal (σ : Gal) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))

theorem specGal_mul (σ τ : Gal) : specGal (σ * τ) = specGal σ ≫ specGal τ := by
  rw [specGal, specGal, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specGal_one : specGal 1 = 𝟙 _ := by
  rw [specGal, show CommRingCat.ofHom ((1 : Gal) : Qbar →+* Qbar) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

/-- Conjugation data for a finite family of abelian varieties over `ℚ̄`: a permutation action of
`G_ℚ` on the indices and, for every `σ` and `i`, a pullback square exhibiting `A i` as the base
change of `A (σ⁻¹·i)` along `Spec σ`. -/
structure ConjData (Idx : Type) where
  A : Idx → AbVar Qbar
  act : Gal → Equiv.Perm Idx
  g : ∀ (σ : Gal) (i : Idx), (A i).X.left ⟶ (A ((act σ).symm i)).X.left
  pb : ∀ (σ : Gal) (i : Idx),
    IsPullback (g σ i) (A i).X.hom (A ((act σ).symm i)).X.hom (specGal σ)

/-- `ρ` is the conjugation action for the data `D`. -/
def IsConjAction {Idx : Type} (D : ConjData Idx)
    (ρ : Gal → HomLattice D.A → HomLattice D.A) : Prop :=
  ∀ (σ : Gal) (f : HomLattice D.A) (i j : Idx),
    (ρ σ f (i, j)).hom.left ≫ D.g σ j =
      D.g σ i ≫ (f ((D.act σ).symm i, (D.act σ).symm j)).hom.left

/-- **The conjugation action is unique (glue, proved).** -/
theorem isConjAction_unique {Idx : Type} (D : ConjData Idx)
    {ρ ρ' : Gal → HomLattice D.A → HomLattice D.A}
    (h : IsConjAction D ρ) (h' : IsConjAction D ρ') : ρ = ρ' := by
  funext σ f
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  apply CategoryTheory.Over.OverMorphism.ext
  apply (D.pb σ j).hom_ext
  · rw [h σ f i j, h' σ f i j]
  · rw [CategoryTheory.Over.w, CategoryTheory.Over.w]

/-- The conjugation action exists (proved below for the conjugates of a model, `conjActionExists`). -/
def ConjActionExists {Idx : Type} (D : ConjData Idx) : Prop :=
  ∃ ρ : Gal →* (HomLattice D.A ≃ₗ[ℤ] HomLattice D.A), IsConjAction D (fun σ f => ρ σ f)

/-! ### The conjugates of a model over a number field

For `A/K` with `K ⊆ ℚ̄` a number field, the conjugates are the base changes `A_e = A ×_{K,e} ℚ̄`
along the embeddings `e : K → ℚ̄`; `G_ℚ` permutes the embeddings, and the comparison maps
`G4Conj.cmp` give the squares `A_e → A_{σ⁻¹∘e}` over `Spec σ`. -/

/-- Base change of an abelian variety along a ring homomorphism `f : K → L` of fields
(as `PkgI3.AbVar.baseChange`, for an arbitrary embedding). -/
noncomputable def bcAlong {K L : Type} [Field K] [Field L] (A : AbVar K) (f : K →+* L) :
    AbVar L :=
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom f))
  letI : GrpObj (F.obj A.X) := Functor.grpObjObj
  haveI : IsProper (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : Smooth (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : GeometricallyIntegral (F.obj A.X).hom := by dsimp [F]; infer_instance
  { X := F.obj A.X }

variable (K : IntermediateField ℚ Qbar)

/-- `Spec e : Spec ℚ̄ → Spec K` for an embedding `e : K → ℚ̄`. -/
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))

/-- `G_ℚ` permutes the embeddings `K → ℚ̄`: `σ · e = σ ∘ e`. -/
noncomputable def embAct (σ : Gal) : Equiv.Perm (K →ₐ[ℚ] Qbar) where
  toFun e := (σ : Qbar →ₐ[ℚ] Qbar).comp e
  invFun e := ((σ⁻¹ : Gal) : Qbar →ₐ[ℚ] Qbar).comp e
  left_inv e := by
    ext x
    show (σ⁻¹ * σ) (e x) = e x
    rw [inv_mul_cancel]; rfl
  right_inv e := by
    ext x
    show (σ * σ⁻¹) (e x) = e x
    rw [mul_inv_cancel]; rfl

theorem specEmb_act (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K (embAct K σ e) = specGal σ ≫ specEmb K e := by
  rw [specEmb, specEmb, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specEmb_symm (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K e = specGal σ ≫ specEmb K ((embAct K σ).symm e) :=
  (congrArg (specEmb K) ((embAct K σ).apply_symm_apply e)).symm.trans (specEmb_act K σ _)

/-- **The conjugation data of a model `A/K`** (constructed, no hypothesis): the `[K:ℚ]`
conjugates `A_e`, permuted by `G_ℚ`, with their pullback squares over `Spec σ`. -/
noncomputable def conjData (A : AbVar K) : ConjData (K →ₐ[ℚ] Qbar) where
  A e := bcAlong A (e : K →+* Qbar)
  act σ := embAct K σ
  g σ e := G4Conj.cmp A.X (specGal σ) (specEmb_symm K σ e)
  pb σ e := G4Conj.cmp_isPullback A.X (specGal σ) (specEmb_symm K σ e)

/-- There are `[K:ℚ]` conjugates. -/
theorem card_conjugates [FiniteDimensional ℚ K] :
    Fintype.card (K →ₐ[ℚ] Qbar) = Module.finrank ℚ K :=
  AlgHom.card ℚ K Qbar

section Action

open CategoryTheory MonObj

variable (A : AbVar K)

/-- Conjugation of one Hom group: `Hom(A_{σ⁻¹i}, A_{σ⁻¹j}) → Hom(A_i, A_j)`, additive
(`G4Conj.conj_mul`, `conj_one`), landing in homomorphisms (`G4Conj.conj_isMonHom`). -/
noncomputable def conjHom (σ : Gal) (i j : K →ₐ[ℚ] Qbar) :
    AbVar.Hom ((conjData K A).A ((embAct K σ).symm i)) ((conjData K A).A ((embAct K σ).symm j)) →+
      AbVar.Hom ((conjData K A).A i) ((conjData K A).A j) where
  toFun φ :=
    haveI hc : IsMonHom (show ((conjData K A).A i).X ⟶ ((conjData K A).A j).X from
        G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom) :=
      G4Conj.conj_isMonHom' A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j)
        φ.hom (show IsMonHom φ.hom from inferInstance)
    AbVar.Hom.mk' (show ((conjData K A).A i).X ⟶ ((conjData K A).A j).X from
      G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom)
  map_zero' := AbVar.Hom.ext'
    (G4Conj.conj_one A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j))
  map_add' φ ψ := AbVar.Hom.ext'
    (G4Conj.conj_mul A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom ψ.hom)

theorem conjHom_hom (σ : Gal) (i j : K →ₐ[ℚ] Qbar) (φ) :
    (conjHom K A σ i j φ).hom =
      G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom := rfl

/-- The action of `σ` on the lattice `⊕ Hom(A_i, A_j)`. -/
noncomputable def conjAct (σ : Gal) :
    HomLattice (conjData K A).A →+ HomLattice (conjData K A).A :=
  AddMonoidHom.pi fun ij => (conjHom K A σ ij.1 ij.2).comp
    (Pi.evalAddMonoidHom (fun ij : (K →ₐ[ℚ] Qbar) × (K →ₐ[ℚ] Qbar) =>
      AbVar.Hom ((conjData K A).A ij.1) ((conjData K A).A ij.2))
      ((embAct K σ).symm ij.1, (embAct K σ).symm ij.2))

theorem conjAct_apply (σ : Gal) (m : HomLattice (conjData K A).A) (i j : K →ₐ[ℚ] Qbar) :
    conjAct K A σ m (i, j) = conjHom K A σ i j (m ((embAct K σ).symm i, (embAct K σ).symm j)) :=
  rfl

theorem conjAct_isConjAction : IsConjAction (conjData K A) (fun σ m => conjAct K A σ m) := by
  intro σ m i j
  dsimp only
  rw [conjAct_apply, conjHom_hom]
  exact G4Conj.conj_cmp A.X A.X _ _ _ _

theorem conjAct_one (m : HomLattice (conjData K A).A) : conjAct K A 1 m = m := by
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  exact G4Conj.conj_self A.X A.X (specGal 1) specGal_one _ _ _

theorem conjAct_mul (σ τ : Gal) (m : HomLattice (conjData K A).A) :
    conjAct K A (σ * τ) m = conjAct K A σ (conjAct K A τ m) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjAct_apply, conjHom_hom, conjHom_hom, conjAct_apply, conjHom_hom]
  have hi : specEmb K i = (specGal σ ≫ specGal τ) ≫
      specEmb K ((embAct K τ).symm ((embAct K σ).symm i)) := by
    rw [Category.assoc, ← specEmb_symm, ← specEmb_symm]
  have hj : specEmb K j = (specGal σ ≫ specGal τ) ≫
      specEmb K ((embAct K τ).symm ((embAct K σ).symm j)) := by
    rw [Category.assoc, ← specEmb_symm, ← specEmb_symm]
  exact (G4Conj.conj_congr A.X A.X (specGal (σ * τ)) _ _ (specGal_mul σ τ) hi hj _).trans
    (G4Conj.conj_comp A.X A.X (specGal τ) (specEmb_symm K τ _) (specEmb_symm K τ _)
      (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) hi hj _)

/-- **The conjugation action of `G_ℚ` on the Hom lattice of the conjugates (constructed).** -/
noncomputable def conjAction : Gal →* (HomLattice (conjData K A).A ≃ₗ[ℤ]
    HomLattice (conjData K A).A) where
  toFun σ := LinearEquiv.ofLinearMap (conjAct K A σ).toIntLinearMap
    (conjAct K A σ⁻¹).toIntLinearMap
    (LinearMap.ext fun m => by
      show conjAct K A σ (conjAct K A σ⁻¹ m) = m
      rw [← conjAct_mul, mul_inv_cancel, conjAct_one])
    (LinearMap.ext fun m => by
      show conjAct K A σ⁻¹ (conjAct K A σ m) = m
      rw [← conjAct_mul, inv_mul_cancel, conjAct_one])
  map_one' := LinearEquiv.ext fun m => conjAct_one K A m
  map_mul' σ τ := LinearEquiv.ext fun m => conjAct_mul K A σ τ m

theorem conjAction_apply (σ : Gal) (m : HomLattice (conjData K A).A) :
    conjAction K A σ m = conjAct K A σ m := rfl

/-- **The Weil-restriction step of G4 is glue, proved: the conjugation action exists.** -/
theorem conjActionExists : ConjActionExists (conjData K A) :=
  ⟨conjAction K A, conjAct_isConjAction K A⟩

end Action

/-- **G4 for a model `A/K` (the manuscript's statement, N5 L544-563).** Let `K ⊆ ℚ̄` be finite
Galois with `[K:ℚ] ≤ F₀`, unramified outside `T` (G2), and `A/K` an abelian surface whose
conjugates `A_e` are surfaces. Let `ρ = conjAction K A` be the conjugation action of `G_ℚ` on
`⊕_{e,e'} Hom(A_e, A_{e'})` (constructed; the unique action with `IsConjAction`). If `ρ` is
continuous and inertia outside `T` acts trivially, the Hom field `L ⊇ K` exists: finite Galois,
`[L:ℚ] ≤ D`, every geometric homomorphism among the conjugates is fixed by `G_L`, `L`
unramified outside `T` (both forms). Leaf: `PkgI3.HomFreeFinite`. -/
theorem homField_of_model (hHFF : HomFreeFinite) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (hcont : ∀ m : HomLattice (conjData K A).A, IsOpen {σ : Gal | conjAction K A σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_conjugates hHFF K hKF (by rw [card_conjugates]; exact hKF) (conjData K A).A hdim
    (conjAction K A) hcont T hK hinert

/-! ### Continuity of the conjugation action from the descent of morphisms

`HomDescends` is the input: a homomorphism between conjugates is fixed by conjugation through an
open subgroup of `G_ℚ`. It is a consequence of EGA IV₃ 8.8.2 (a morphism between base changes to
`ℚ̄ = colim L` of finitely presented `K`-schemes is the base change of a morphism over some number
field `L`; locator UNVERIFIED) together with the descent bookkeeping "conjugation by `σ ∈ G_L`
fixes a morphism defined over `L`" (`conj_unique` on the pasted squares `ℚ̄ → L → K`), which is
glue not formalized here. Stated as a `Prop` over the genuine objects (`PkgI3.AbVar`, Mathlib's
pullbacks, `G4Conj.conj`). -/

/-- **Input (EGA IV₃ 8.8.2 + descent bookkeeping; not formalized).** For abelian varieties
`A, B` over a number field `K ⊆ ℚ̄` and embeddings `e₁, e₂ : K → ℚ̄`, every morphism
`A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` over `ℚ̄` is fixed by the conjugation of an open subgroup of
`G_ℚ` (those `σ` fixing `e₁(K)`, `e₂(K)` and the field of definition). -/
def HomDescends : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ U : Subgroup Gal, IsOpen (U : Set Gal) ∧ ∀ σ ∈ U,
      ∀ (hf : specEmb K e₁ = specGal σ ≫ specEmb K e₁)
        (hg : specEmb K e₂ = specGal σ ≫ specEmb K e₂),
        G4Conj.conj A.X B.X (specGal σ) hf hg φ = φ

/-- `Spec ℚ̄ → Spec L` for a subfield `L ⊆ ℚ̄`. -/
noncomputable abbrev specIncl (L : IntermediateField ℚ Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L Qbar))

/-- `Spec e = Spec(ℚ̄ ← L) ≫ Spec e'` when `e = (L ↪ ℚ̄) ∘ e'`. -/
theorem specEmb_factor (L : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L)
    (he : ∀ x, (e' x : Qbar) = e x) :
    specEmb K e = specIncl L ≫ Spec.map (CommRingCat.ofHom (e' : K →+* L)) := by
  rw [specEmb, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (he x).symm

/-- The comparison `A ×_{K,e} ℚ̄ → A ×_{K,e'} L` (the base-change square along `Spec ℚ̄ → Spec L`). -/
noncomputable def cmpL (L : IntermediateField ℚ Qbar) (X : CategoryTheory.Over (Spec (CommRingCat.of K)))
    (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x) :
    Limits.pullback X.hom (specEmb K e) ⟶
      Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (e' : K →+* L))) :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ specIncl L)
    (by rw [Limits.pullback.condition, specEmb_factor K L e e' he, Category.assoc])

/-- **Input: EGA IV₃ 8.8.2 (i), surjectivity part, for `ℚ̄ = colim L` (locator UNVERIFIED).**
Every morphism `A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` over `ℚ̄` between base changes of abelian
varieties over a number field `K ⊆ ℚ̄` comes from a morphism `ψ : A ×_{K,e₁'} L → B ×_{K,e₂'} L`
over a number field `L ⊆ ℚ̄` through which `e₁, e₂` factor (`φ` is the base change of `ψ`: it
is the map compatible with `ψ` under the cartesian squares `cmpL`). Hypotheses of 8.8.2: `A`
quasi-compact quasi-separated (proper), `B` locally of finite presentation (smooth). -/
def MorphismsDescend : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (e₁' e₂' : K →ₐ[ℚ] L)
      (he₁ : ∀ x, (e₁' x : Qbar) = e₁ x) (he₂ : ∀ x, (e₂' x : Qbar) = e₂ x)
      (ψ : Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom (e₁' : K →+* L))) ⟶
        Limits.pullback B.X.hom (Spec.map (CommRingCat.ofHom (e₂' : K →+* L)))),
      φ.left ≫ cmpL K L B.X e₂ e₂' he₂ = cmpL K L A.X e₁ e₁' he₁ ≫ ψ

/-- `σ ∈ G_L` fixes `Spec ℚ̄ → Spec L`. -/
theorem specGal_specIncl (L : IntermediateField ℚ Qbar) (σ : Gal) (hσ : σ ∈ L.fixingSubgroup) :
    specGal σ ≫ specIncl L = specIncl L := by
  rw [specGal, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ x x.2

/-- **`HomDescends` from EGA IV₃ 8.8.2 (glue, proved): the descent bookkeeping.** A morphism
that is the base change of one over `L` is fixed by conjugation through `G_L`. -/
theorem homDescends_of_morphismsDescend (hM : MorphismsDescend) : HomDescends := by
  intro K _ A B e₁ e₂ φ
  obtain ⟨L, hL, e₁', e₂', he₁, he₂, ψ, hψ⟩ := hM K A B e₁ e₂ φ
  refine ⟨L.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen L, fun σ hσ hf hg => ?_⟩
  symm
  apply G4Conj.conj_unique
  -- `cmp_σ ≫ cmpL = cmpL`
  have hcL : ∀ (X : CategoryTheory.Over (Spec (CommRingCat.of K))) (e : K →ₐ[ℚ] Qbar)
      (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x)
      (h : specEmb K e = specGal σ ≫ specEmb K e),
      G4Conj.cmp X (specGal σ) h ≫ cmpL K L X e e' he = cmpL K L X e e' he := by
    intro X e e' he h
    apply Limits.pullback.hom_ext
    · simp [cmpL]
    · simp only [cmpL, Category.assoc, Limits.pullback.lift_snd]
      rw [G4Conj.cmp_snd_assoc, specGal_specIncl L σ hσ]
  apply Limits.pullback.hom_ext
  · have e1 : Limits.pullback.fst B.X.hom (specEmb K e₂) =
        cmpL K L B.X e₂ e₂' he₂ ≫ Limits.pullback.fst _ _ := by simp [cmpL]
    rw [Category.assoc, G4Conj.cmp_fst, Category.assoc, e1, reassoc_of% hψ,
      reassoc_of% (hcL A.X e₁ e₁' he₁ hf)]
  · rw [Category.assoc, G4Conj.cmp_snd, Category.assoc]
    have h1 : φ.left ≫ Limits.pullback.snd B.X.hom (specEmb K e₂) =
        Limits.pullback.snd A.X.hom (specEmb K e₁) := CategoryTheory.Over.w φ
    rw [reassoc_of% h1, h1, G4Conj.cmp_snd]

/-- `G_K` fixes every embedding of the Galois field `K`. -/
theorem embAct_symm_of_mem [IsGalois ℚ K] (σ : Gal) (hσ : σ ∈ K.fixingSubgroup)
    (e : K →ₐ[ℚ] Qbar) : (embAct K σ).symm e = e := by
  ext x
  have hx : e x ∈ K := by
    have hmem : e x ∈ e.fieldRange := ⟨x, rfl⟩
    rw [AlgHom.fieldRange_of_normal e] at hmem
    exact hmem
  have hσ' : σ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hσ
  exact (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ hx

/-- The stabilizer of a lattice element, as a subgroup. -/
def stabSub (A : AbVar K) (m : HomLattice (conjData K A).A) : Subgroup Gal where
  carrier := {σ | conjAction K A σ m = m}
  one_mem' := by simp
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, LinearEquiv.mul_apply, hτ, hσ]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hσ]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

/-- **Continuity of the conjugation action (glue, proved from `HomDescends`).** -/
theorem conjAction_continuous (hD : HomDescends) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (m : HomLattice (conjData K A).A) :
    IsOpen {σ : Gal | conjAction K A σ m = m} := by
  classical
  choose U hUo hU using fun ij : (K →ₐ[ℚ] Qbar) × (K →ₐ[ℚ] Qbar) =>
    hD K A A ij.1 ij.2 (m ij).hom
  let W : Set Gal := (K.fixingSubgroup : Set Gal) ∩ ⋂ ij, (U ij : Set Gal)
  have hWo : IsOpen W :=
    (IntermediateField.fixingSubgroup_isOpen K).inter (isOpen_iInter_of_finite fun ij => hUo ij)
  have hW1 : (1 : Gal) ∈ W :=
    ⟨K.fixingSubgroup.one_mem, Set.mem_iInter.mpr fun ij => (U ij).one_mem⟩
  have hWS : W ⊆ (stabSub K A m : Set Gal) := by
    rintro σ ⟨hσK, hσU⟩
    rw [Set.mem_iInter] at hσU
    show conjAction K A σ m = m
    rw [conjAction_apply]
    funext ij
    obtain ⟨i, j⟩ := ij
    apply AbVar.Hom.ext'
    rw [conjAct_apply, conjHom_hom]
    have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
        (hf : specEmb K i = specGal σ ≫ specEmb K i')
        (hg : specEmb K j = specGal σ ≫ specEmb K j'),
        G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
      intro i' j' hi hj hf hg
      subst hi hj
      exact hU (i', j') σ (hσU (i', j')) hf hg
    exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _
  have hS : IsOpen (stabSub K A m : Set Gal) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hWo.mem_nhds hW1) hWS)
  exact hS

/-- **G4 for a model `A/K`, continuity discharged.** As `homField_of_model`, with `hcont`
replaced by the input `HomDescends`. -/
theorem homField_of_model' (hHFF : HomFreeFinite) (hD : HomDescends) [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model K hHFF hKF A hdim (conjAction_continuous K hD A) T hK hinert



/-- **G4 for a model `A/K`, final form.** Leaves: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3) and
`MorphismsDescend` (EGA IV₃ 8.8.2). Remaining hypotheses: `hdim` (dimension of base change),
`hK` (G2's output) and `hinert` (inertia outside `T` trivial on the lattice: NOS + the action on
Tate modules, see `inertia_of_tate`). -/
theorem homField_of_model_final (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model' K hHFF (homDescends_of_morphismsDescend hM) hKF A hdim T hK hinert

/-! ### Inertia from good reduction

`InertiaFixesHoms` is the input: at a place `w` of `ℚ̄` where both varieties have good reduction,
inertia fixes every homomorphism between their base changes. It is a consequence of
Néron–Ogg–Shafarevich (Serre–Tate 1968, Thm 1: inertia acts trivially on `T_ℓ` for `ℓ ≠ p`; the
leaf `PkgI2.NeronOggShafarevich`) and the faithfulness of the `ℓ`-adic realization (Mumford §19
Thm 3; `tateHom_injective` above), through the equivariance of the realization under
conjugation. That equivariance is glue that is not formalized here. Stated over the genuine
objects (`PkgI2.HasGoodReduction`, `inertiaGQ`, `G4Conj.conj`). -/

/-- **Input (Serre–Tate 1968 Thm 1 + Mumford §19 Thm 3 + equivariance; derivation not
formalized).** -/
def InertiaFixesHoms : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X)
    (w : ValuationSubring Qbar),
    PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e₁ : K →+* Qbar)) →
    PkgI2.HasGoodReduction (ObjBridge.toGrp B) (w.comap (e₂ : K →+* Qbar)) →
    ∀ s ∈ inertiaGQ w, ∀ (hf : specEmb K e₁ = specGal s ≫ specEmb K e₁)
      (hg : specEmb K e₂ = specGal s ≫ specEmb K e₂),
      G4Conj.conj A.X B.X (specGal s) hf hg φ = φ

/-- **The inertia hypothesis of G4 (glue, proved from `InertiaFixesHoms`).** If `K` is unramified
outside `T` and `A` has good reduction at every place of `K` above every `p ∉ T` (G3's output),
inertia above `p ∉ T` acts trivially on the Hom lattice of the conjugates. -/
theorem conjAction_inertia (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1 := by
  intro p hp hpT w hw
  intro (σ : Gal) (hσ : σ ∈ inertiaGQ w)
  have hσK : σ ∈ K.fixingSubgroup := hK p hp hpT w hw hσ
  apply LinearEquiv.ext
  intro m
  show conjAct K A σ m = m
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
      (hf : specEmb K i = specGal σ ≫ specEmb K i')
      (hg : specEmb K j = specGal σ ≫ specEmb K j'),
      G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
    intro i' j' hi hj hf hg
    subst hi hj
    exact hI K A A i' j' (m (i', j')).hom w (hgood p hp hpT w hw i') (hgood p hp hpT w hw j')
      σ hσ hf hg
  exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _

/-- **G4 for a model `A/K`, all analytic inputs as leaves.** Leaves/inputs: `HomFreeFinite`
(Mumford §19 Thm 3), `MorphismsDescend` (EGA IV₃ 8.8.2), `InertiaFixesHoms` (Serre–Tate +
Mumford + equivariance). Hypotheses from other glue steps: `hK` (G2), `hgood` (G3), `hdim`
(dimension of base change, missing from Mathlib). -/
theorem homField_of_model_leaves (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_final K hHFF hM hKF A hdim T hK (conjAction_inertia K hI A T hK hgood)

end Lattice

/-! ## What G7 receives: the Hom field feeds `GlueDescent.B3Q.b3_degree_le_QM`

`b3_degree_le_QM` needs a finite Galois `L` with `[L:ℚ] ≤ D`, unramified outside `T = ramSet S u`
(ideal-theoretic form), and the cocycle `ε` of the scalar descent data inflated from `Gal(L/ℚ)`.
The first three are G4's output above; the last is G7's own instantiation (the descent data
`μ_σ` are elements of the lattice, so a field defining the lattice defines `ε`), kept here as the
hypothesis `hdesc`. -/

section Feed

/-- **G4 → G7.** The Hom field of `homField_le_heightD`, with `T = ramSet S u`, is a valid input
of `GlueDescent.B3Q.b3_degree_le_QM`: the scalar-descent output (`χ`, `β`, `L' ⊇ L` Galois with
`[L':ℚ] ≤ Q_R·M_S(u)`) follows. -/
theorem b3_of_homField (hHasse : GlueDescent.B2Q.LeafHasse)
    (hTwo : GlueDescent.B2Q.LeafLocalTwo) (hSq : GlueDescent.B2Q.LeafSqrtCrit)
    (hUnr : GlueDescent.B2Q.LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ) {M : Type*} [AddCommGroup M]
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (hK : GalUnramifiedOutside K (GlueDescent.ramSet S u))
    (hinert : ∀ p : ℕ, p.Prime → p ∉ GlueDescent.ramSet S u → ∀ w : ValuationSubring Qbar,
      LiesOver w p → ∀ s ∈ inertiaGQ w, ρ s = 1)
    (hdesc : ∀ L : IntermediateField ℚ Qbar, (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) →
      ∃ ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ, GlueDescent.B2.IsSignCocycle ε ∧
        GlueDescent.B2Q.InflatedFrom L ε ∧ ε 1 1 = 1)
    (η : GlueDescent.B2Q.GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (L : IntermediateField ℚ Qbar) (ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ)
      (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GlueDescent.B2Q.GQ → ℂˣ)
      (L' : IntermediateField ℚ Qbar),
      Module.finrank ℚ L ≤ ZInQ.heightD ∧ K ≤ L ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = GlueDescent.B2Q.galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u := by
  obtain ⟨L, hfd, hgal, hKL, hdef, hdeg, -, hram⟩ :=
    homField_le_heightD K hKF hr b ρ hcont (GlueDescent.ramSet S u) hK hinert
  obtain ⟨ε, hε, hinf, h11⟩ := hdesc L hdef
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', -, hdeg'⟩ :=
    GlueDescent.B3Q.b3_degree_le_QM hHasse hTwo hSq hUnr S hS R hRD hRS hR12 u L hdeg ε hε hinf
      h11 hram η hη hηl
  exact ⟨L, ε, N, hN, χ, β, L', hdeg, hKL, hβl, hβs, hβe, hle, hfd', hgal', hdeg'⟩

/-- **G4 → the CM branch.** `GlueAssembly.CMOutput` takes `d = [L:ℚ]` with `1 ≤ d ≤ D` (reals);
the Hom field supplies it. -/
theorem cm_degree_of_homField (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    (hL : Module.finrank ℚ L ≤ ZInQ.heightD) :
    (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) ∧ (Module.finrank ℚ L : ℝ) ≤ (ZInQ.heightD : ℝ) :=
  ⟨by exact_mod_cast Module.finrank_pos, by exact_mod_cast hL⟩


end Feed

end G4WeilRes


section NewConj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace G4Conj

variable {C : Type*} [Category C] [HasPullbacks C] {S T : C}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory


section Agree

variable (X Y : Over S) {f g : T ⟶ S} (s : T ⟶ T) (hf : f = s ≫ f) (hg : g = s ≫ g)

/-- **Equivariance on test points.** If a test point `Q : Z → X_f` and its image `Q ≫ φ` are
fixed by conjugation (relative to a lift `s'` of `s` on `Z`), then `σφ` and `φ` agree on `Q`. -/
theorem conj_agree (φ : (Over.pullback f).obj X ⟶ (Over.pullback g).obj Y) {Z : C}
    (Q : Z ⟶ pullback X.hom f) (s' : Z ⟶ Z)
    (hQ : Q ≫ cmp X s hf = s' ≫ Q)
    (hφQ : (Q ≫ φ.left) ≫ cmp Y s hg = s' ≫ Q ≫ φ.left) :
    Q ≫ (conj X Y s hf hg φ).left = Q ≫ φ.left := by
  rw [Category.assoc] at hφQ
  apply pullback.hom_ext
  · have e1 : Q ≫ (conj X Y s hf hg φ).left ≫ pullback.fst Y.hom g =
        Q ≫ (conj X Y s hf hg φ).left ≫ cmp Y s hg ≫ pullback.fst Y.hom g := by
      rw [cmp_fst]
    have e2 : Q ≫ φ.left ≫ pullback.fst Y.hom g =
        Q ≫ φ.left ≫ cmp Y s hg ≫ pullback.fst Y.hom g := by
      rw [cmp_fst]
    rw [Category.assoc, Category.assoc, e1, e2, conj_cmp_assoc, reassoc_of% hQ,
      reassoc_of% hφQ]
  · rw [Category.assoc, Category.assoc]
    have h1 : (conj X Y s hf hg φ).left ≫ pullback.snd Y.hom g = pullback.snd X.hom f :=
      Over.w _
    have h2 : φ.left ≫ pullback.snd Y.hom g = pullback.snd X.hom f := Over.w φ
    rw [h1, h2]

/-- A section `Q` of `X_f` is fixed by conjugation iff its `X`-component is fixed by `s`. -/
theorem cmp_fixed_of_fst (Q : T ⟶ pullback X.hom f) (hQ : Q ≫ pullback.snd X.hom f = 𝟙 T)
    (h : s ≫ Q ≫ pullback.fst X.hom f = Q ≫ pullback.fst X.hom f) :
    Q ≫ cmp X s hf = s ≫ Q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, Category.assoc, h]
  · rw [Category.assoc, cmp_snd, reassoc_of% hQ, Category.assoc, hQ]
    simp

end Agree

section Sections

variable (X : Over S) [MonObj X] (f : T ⟶ S)

/-- The `X`-component of a section of `X_f`, as a point of `X` over `S` with source `T` (via `f`). -/
noncomputable def secFst (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) : Over.mk f ⟶ X :=
  Over.homMk (Q.left ≫ pullback.fst X.hom f) (by
    rw [Category.assoc, pullback.condition]
    have hw : Q.left ≫ pullback.snd X.hom f = 𝟙 T := Over.w Q
    rw [reassoc_of% hw]
    simp)

omit [MonObj X] in
@[simp] theorem secFst_left (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) :
    (secFst X f Q).left = Q.left ≫ pullback.fst X.hom f := rfl

theorem secFst_mul (Q R : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) :
    secFst X f (Q * R) = secFst X f Q * secFst X f R := by
  apply Over.OverMorphism.ext
  rw [secFst_left, Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc,
    mul_left_fst, ← Category.assoc]
  congr 1
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · simp
  · simp

theorem secFst_one : secFst X f (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) = 1 := by
  apply Over.OverMorphism.ext
  rw [secFst_left, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc,
    one_left_fst, Over.toUnit_left, Over.toUnit_left]
  simp

/-- `secFst` as a monoid homomorphism. -/
noncomputable def secFstHom : (Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) →* (Over.mk f ⟶ X) where
  toFun := secFst X f
  map_one' := secFst_one X f
  map_mul' := secFst_mul X f

theorem secFst_pow (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) (n : ℕ) :
    secFst X f (Q ^ n) = secFst X f Q ^ n :=
  map_pow (secFstHom X f) Q n

end Sections

end G4Conj

end NewConj

namespace InertiaHoms

open GlueB3Unram
open scoped Pointwise

/-! ## Inertia membership in terms of the valuation subring alone -/

section InertiaChar

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- `v_w(x) < 1` in terms of membership only. -/
theorem valuation_lt_one_iff_mem (w : ValuationSubring L) (x : L) :
    w.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ w := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, false_or]
    rw [← w.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

/-- **Inertia, elementwise.** `σ` lies in the inertia group of `w` (Mathlib's
`decompositionSubgroup`/`inertiaSubgroup`) iff `σ` preserves `w` and `σ x - x` lies in the
maximal ideal of `w` for every `x ∈ w` (the latter written by membership only). -/
theorem isInertia_iff (w : ValuationSubring L) (σ : L ≃ₐ[F] L) :
    (∃ h : σ ∈ w.decompositionSubgroup F, (⟨σ, h⟩ : w.decompositionSubgroup F) ∈
        w.inertiaSubgroup F) ↔
      (∀ x, σ x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, σ x - x = 0 ∨ (σ x - x)⁻¹ ∉ w) := by
  have hinv : ∀ x, σ⁻¹ (σ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
  have hinv' : ∀ x, σ (σ⁻¹ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl
  constructor
  · rintro ⟨h, hin⟩
    have hstab : σ • w = w := h
    have hmem : ∀ y, y ∈ w ↔ σ⁻¹ y ∈ w := fun y => by
      conv_lhs => rw [← hstab]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have hD : ∀ x, σ x ∈ w ↔ x ∈ w := fun x => by rw [hmem (σ x), hinv]
    refine ⟨hD, fun x hx => ?_⟩
    rw [← valuation_lt_one_iff_mem]
    have hk := congrArg (fun φ : RingAut (IsLocalRing.ResidueField w) =>
      φ (IsLocalRing.residue w ⟨x, hx⟩)) (MonoidHom.mem_ker.mp hin)
    simp only [RingAut.one_apply, MulSemiringAction.toRingAut_apply] at hk
    change (⟨σ, h⟩ : w.decompositionSubgroup F) • IsLocalRing.residue w ⟨x, hx⟩ = _ at hk
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hk
    exact hk
  · rintro ⟨hD, hI⟩
    have hstab : σ • w = w := by
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hD, hinv']
    have hdec : σ ∈ w.decompositionSubgroup F := hstab
    refine ⟨hdec, ?_⟩
    unfold ValuationSubring.inertiaSubgroup
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, hdec⟩ : w.decompositionSubgroup F) • IsLocalRing.residue w a =
      IsLocalRing.residue w a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [valuation_lt_one_iff_mem]
    exact hI a.1 a.2

end InertiaChar

section Transport

/-- **Inertia transports along a ring isomorphism.** If `s` satisfies the elementwise inertia
conditions at `w`, then `ι⁻¹ ∘ s ∘ ι` satisfies them at `w.comap ι`. -/
theorem inertia_transport {L₁ L₂ : Type*} [Field L₁] [Field L₂] (ι : L₁ ≃+* L₂)
    (w : ValuationSubring L₂) (s : L₂ ≃+* L₂)
    (hD : ∀ x, s x ∈ w ↔ x ∈ w) (hI : ∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) :
    (∀ x, ι.symm (s (ι x)) ∈ w.comap (ι : L₁ →+* L₂) ↔ x ∈ w.comap (ι : L₁ →+* L₂)) ∧
      (∀ x ∈ w.comap (ι : L₁ →+* L₂), ι.symm (s (ι x)) - x = 0 ∨
        (ι.symm (s (ι x)) - x)⁻¹ ∉ w.comap (ι : L₁ →+* L₂)) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simp only [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact hD _
  · rw [ValuationSubring.mem_comap] at hx
    have key : ι (ι.symm (s (ι x)) - x) = s (ι x) - ι x := by
      rw [map_sub, RingEquiv.apply_symm_apply]
    rcases hI _ hx with h | h
    · left
      apply ι.injective
      have h' : s (ι x) - ι x = 0 := h
      rw [key, h', map_zero]
    · right
      rw [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, map_inv₀, key]
      exact h

end Transport

section Closure

/-- `ℚ̄` is an algebraic closure of `K` through any embedding `e : K → ℚ̄`: a ring isomorphism
`ι : K̄ ≃ ℚ̄` extending `e`. -/
theorem exists_closure_equiv (K : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) :
    ∃ ι : AlgebraicClosure K ≃+* Qbar, ∀ x, ι (algebraMap K (AlgebraicClosure K) x) = e x := by
  let R : IntermediateField ℚ Qbar := e.fieldRange
  let hSR : K ≃+* R := (AlgEquiv.ofInjectiveField e).toRingEquiv
  have : Algebra.IsAlgebraic R Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) R
  have : IsAlgClosure R Qbar := ⟨inferInstance, inferInstance⟩
  refine ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure K) Qbar hSR, fun x => ?_⟩
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  rfl

end Closure

section Unit

/-- At a place over `p`, every prime `ℓ ≠ p` is a unit of the valuation ring (of any subfield). -/
theorem isUnit_prime_of_liesOver {F : Type*} [Field F] [CharZero F] (f : F →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) : IsUnit ((ℓ : ℕ) : w.comap f) := by
  have hcop : IsCoprime (ℓ : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hℓ hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have hpw : ((p : w) : Qbar) = p := by simp
  have hℓw : ((ℓ : w) : Qbar) = ℓ := by simp
  have hpm : (p : w) ∈ IsLocalRing.maximalIdeal w := by
    rw [ValuationSubring.valuation_lt_one_iff, hpw]; exact hw
  have hv1 : w.valuation (ℓ : Qbar) = 1 := by
    rcases w.valuation_lt_one_or_eq_one (ℓ : w) with h | h
    · exfalso
      have hℓm : (ℓ : w) ∈ IsLocalRing.maximalIdeal w := by
        rw [ValuationSubring.valuation_lt_one_iff]; exact h
      have h1 : (1 : w) ∈ IsLocalRing.maximalIdeal w := by
        have : ((a : w) * (ℓ : w) + (b : w) * (p : w)) = 1 := by
          have := congrArg (Int.cast : ℤ → w) hab
          push_cast at this
          exact this
        rw [← this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓm) (Ideal.mul_mem_left _ _ hpm)
      exact (IsLocalRing.maximalIdeal.isMaximal w).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [← hℓw]; exact h
  have hℓF : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hinv : (ℓ : F)⁻¹ ∈ w.comap f := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast, ← w.valuation_le_one_iff, map_inv₀,
      hv1, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨(ℓ : F)⁻¹, hinv⟩, ?_⟩
  apply Subtype.ext
  simp [hℓF]

end Unit

section DVR

open NumberField IsDedekindDomain

/-- Algebraic integers lie in every valuation subring of `ℚ̄`. -/
theorem mem_of_isIntegral_int (w : ValuationSubring Qbar) (y : Qbar) (hy : IsIntegral ℤ y) :
    y ∈ w := by
  have hv := Valuation.valuationSubring.integers w.valuation
  have hy' : IsIntegral w.valuation.valuationSubring y := hy.tower_top
  exact (w.valuation_le_one_iff y).mp (hv.isIntegral_iff_v_le_one.mp hy')

/-- **A place of `ℚ̄` over `p` restricts to a DVR on every number field (glue, proved).** The
restriction `O = w ∩ F` contains `𝓞_F`; with `P = 𝔪_O ∩ 𝓞_F` (a nonzero prime, `p ∈ P`), the
`P`-adic valuation ring `𝓞_{F,P}` (Mathlib: a DVR) is contained in `O`, and `O ≠ F`, so
`O = 𝓞_{F,P}` (a valuation ring of Krull dimension `1` has no proper overrings but `F`). -/
theorem comap_isDVR {F : Type*} [Field F] [NumberField F] (f : F →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p) :
    IsDiscreteValuationRing (w.comap f) := by
  set Ov := w.comap f with hOv
  have hint : ∀ x : 𝓞 F, algebraMap (𝓞 F) F x ∈ Ov := fun x => by
    rw [ValuationSubring.mem_comap]
    exact mem_of_isIntegral_int w _ ((RingOfIntegers.isIntegral_coe x).map f.toIntAlgHom)
  let ι0 : 𝓞 F →+* Ov := (algebraMap (𝓞 F) F).codRestrict Ov.toSubring hint
  have hι0 : ∀ x, ((ι0 x : Ov) : F) = algebraMap (𝓞 F) F x := fun x => rfl
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal Ov).comap ι0
  have hPp : P.IsPrime := Ideal.comap_isPrime _ _
  have hpinv : ((p : F))⁻¹ ∉ Ov := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
    rcases (valuation_lt_one_iff_mem w (p : Qbar)).mp hw with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)
    · exact h
  have hmax : ∀ x : 𝓞 F, x ∈ P ↔ algebraMap (𝓞 F) F x = 0 ∨
      (algebraMap (𝓞 F) F x)⁻¹ ∉ Ov := fun x => by
    show ι0 x ∈ IsLocalRing.maximalIdeal Ov ↔ _
    rw [ValuationSubring.valuation_lt_one_iff, valuation_lt_one_iff_mem, hι0]
  have hpP : ((p : 𝓞 F)) ∈ P := by
    rw [hmax]
    right
    simpa using hpinv
  have hPne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hPne⟩
  have hle : (v.valuation F).valuationSubring ≤ Ov := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x hx
    have hdP : (d : 𝓞 F) ∉ P := d.2
    have hdu : IsUnit (ι0 d) := by
      by_contra h
      exact hdP ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have hd0 : algebraMap (𝓞 F) F d ≠ 0 := by
      intro h0
      apply hdP
      rw [hmax]
      left
      exact h0
    obtain ⟨u, hu⟩ := hdu
    have hinvmem : (algebraMap (𝓞 F) F d)⁻¹ ∈ Ov := by
      have h1 : ((u⁻¹ : Ovˣ) : Ov) * (u : Ov) = 1 := by simp
      have h2 : (((u⁻¹ : Ovˣ) : Ov) : F) * algebraMap (𝓞 F) F d = 1 := by
        rw [← hι0, ← hu]
        exact_mod_cast congrArg (fun t : Ov => (t : F)) h1
      have h3 : (((u⁻¹ : Ovˣ) : Ov) : F) = (algebraMap (𝓞 F) F d)⁻¹ :=
        eq_inv_of_mul_eq_one_left h2
      rw [← h3]
      exact ((u⁻¹ : Ovˣ) : Ov).2
    have hx : x = algebraMap (𝓞 F) F n * (algebraMap (𝓞 F) F d)⁻¹ := by
      rw [← hnd, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
    rw [hx]
    exact Ov.mul_mem _ _ (hint n) hinvmem
  have hne : Ov ≠ ⊤ := fun h => hpinv (by rw [h]; exact ValuationSubring.mem_top _)
  haveI : IsDiscreteValuationRing (v.valuation F).valuationSubring :=
    (inferInstance : IsDiscreteValuationRing (v.valuation F).integer)
  have heq : (v.valuation F).valuationSubring = Ov :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hne
  rw [← heq]
  infer_instance

end DVR

end InertiaHoms



namespace G4WeilRes

open GlueB3Unram CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms

variable (K : IntermediateField ℚ Qbar)


theorem specMap_comp {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (a : R →+* S)
    (b : S →+* U) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (b.comp a)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **Inertia fixes prime-to-`p` torsion points of a conjugate (NOS, transported).** Let `A/K`
have good reduction at `w ∩ e(K)` (a DVR), `s ∈ I_w` fix `e(K)`, and `m` be invertible at `w`.
A point `q : Spec ℚ̄ → A` over `Spec e` with `q^m = 1` is fixed by `s`: `Spec s ≫ q = q`.
Leaf: `PkgI2.NeronOggShafarevich` (Serre–Tate 1968 Thm 1), applied to `A/K` at `w ∩ e(K)`, with
`ℚ̄ ≅ K̄` extending `e` and the inertia group transported along it. -/
theorem point_fixed (hNOS : PkgI2.NeronOggShafarevich.{0})
    (A : AbVar K) (e : K →ₐ[ℚ] Qbar) (w : ValuationSubring Qbar)
    [IsDiscreteValuationRing (w.comap (e : K →+* Qbar))]
    (hgood : PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar)))
    (s : Gal) (hs : s ∈ inertiaGQ w) (hse : ∀ x, s (e x) = e x)
    (m : ℕ) (hm : 0 < m) (hmO : IsUnit ((m : ℕ) : w.comap (e : K →+* Qbar)))
    (q : CategoryTheory.Over.mk (specEmb K e) ⟶ A.X) (hq : q ^ m = 1) :
    specGal s ≫ q.left = q.left := by
  obtain ⟨ie, hie⟩ := exists_closure_equiv K e
  have hies : ∀ x : K, ie.symm (e x) = algebraMap K (AlgebraicClosure K) x := fun x => by
    rw [← hie, RingEquiv.symm_apply_apply]
  let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := (ie.trans s.toRingEquiv).trans ie.symm) (fun x => by
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hie, hse, hies])
  have hσ : ∀ x, σ x = ie.symm (s (ie x)) := fun x => rfl
  let w' : ValuationSubring (AlgebraicClosure K) := w.comap (ie : AlgebraicClosure K →+* Qbar)
  have hw' : w'.comap (algebraMap K (AlgebraicClosure K)) = w.comap (e : K →+* Qbar) := by
    ext x
    simp only [w', ValuationSubring.mem_comap, RingEquiv.coe_toRingHom]
    rw [hie]
    rfl
  have hsI : (∀ x, s x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) := by
    obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.mp hs
    have := (isInertia_iff w g.1).mp ⟨g.2, hg⟩
    rw [← hgs]
    exact this
  have hIσ : PkgI2.IsInertia w' σ := by
    rw [PkgI2.IsInertia, isInertia_iff]
    exact inertia_transport ie w s.toRingEquiv hsI.1 hsI.2
  let J : PkgI2.specOver K (AlgebraicClosure K) ⟶ CategoryTheory.Over.mk (specEmb K e) :=
    CategoryTheory.Over.homMk
      (Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K))) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [specMap_comp]
        congr 2
        ext x
        exact hies x)
  let x : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure K) := J ≫ q
  have hx : x ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure K) m := by
    show (J ≫ q) ^ m = 1
    rw [← MonObj.comp_pow, hq, MonObj.comp_one]
  have hfix := ((hNOS K (w.comap (e : K →+* Qbar)) w' hw' (ObjBridge.toGrp A)).1.mp hgood)
    m hm hmO σ hIσ x hx
  have h2 : Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left =
      Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left := by
    have := congrArg (fun t => Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      CategoryTheory.Over.Hom.left t) hfix
    exact this
  rw [← Category.assoc, ← Category.assoc, specMap_comp, specMap_comp, ← Category.assoc,
    specMap_comp] at h2
  have e1 : ((ie : AlgebraicClosure K →+* Qbar).comp
      (σ : AlgebraicClosure K →+* AlgebraicClosure K)).comp
      (ie.symm : Qbar →+* AlgebraicClosure K) = (s : Qbar →+* Qbar) := by
    ext y
    simp [hσ]
  have e2 : (ie : AlgebraicClosure K →+* Qbar).comp (ie.symm : Qbar →+* AlgebraicClosure K) =
      RingHom.id Qbar := by
    ext y
    simp
  rw [e1, e2] at h2
  rw [h2, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- A point `P` of `X ×_{K,e} ℚ̄` with values in `L = AlgebraicClosure ℚ̄` (the points used by
`PkgI3.AbVar.T`) factors through the section `J' ≫ P` over `Spec ℚ̄`, because `ℚ̄ → L` is an
isomorphism. -/
noncomputable def ptIso :
    PkgI3.AbVar.ptObj (K := Qbar) (AlgebraicClosure Qbar) ≅
      CategoryTheory.Over.mk (𝟙 (Spec (CommRingCat.of Qbar))) := by
  let ie : Qbar ≃+* AlgebraicClosure Qbar := RingEquiv.ofBijective
    (algebraMap Qbar (AlgebraicClosure Qbar))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Qbar) (K := AlgebraicClosure Qbar))
  have h1 : (ie.symm : AlgebraicClosure Qbar →+* Qbar).comp
      (algebraMap Qbar (AlgebraicClosure Qbar)) = RingHom.id Qbar := by
    ext y
    exact ie.symm_apply_apply y
  have h2 : (algebraMap Qbar (AlgebraicClosure Qbar)).comp
      (ie.symm : AlgebraicClosure Qbar →+* Qbar) = RingHom.id _ := by
    ext y
    exact ie.apply_symm_apply y
  refine
    { hom := CategoryTheory.Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar)))) (by simp [PkgI3.AbVar.ptObj])
      inv := CategoryTheory.Over.homMk
        (Spec.map (CommRingCat.ofHom (ie.symm : AlgebraicClosure Qbar →+* Qbar))) (by
          show _ ≫ Spec.map _ = 𝟙 _
          rw [specMap_comp, h1, CommRingCat.ofHom_id, Spec.map_id])
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [specMap_comp, h2, CommRingCat.ofHom_id, Spec.map_id]
  · apply CategoryTheory.Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [specMap_comp, h1, CommRingCat.ofHom_id, Spec.map_id]

/-- **The corrected input** (homomorphisms only, at a place over a prime). -/
def InertiaFixesHomsMon : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : AbVar.Hom (bcAlong A (e₁ : K →+* Qbar)) (bcAlong B (e₂ : K →+* Qbar)))
    (w : ValuationSubring Qbar) (p : ℕ), p.Prime → LiesOver w p →
    PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e₁ : K →+* Qbar)) →
    PkgI2.HasGoodReduction (ObjBridge.toGrp B) (w.comap (e₂ : K →+* Qbar)) →
    ∀ s ∈ inertiaGQ w, ∀ (hf : specEmb K e₁ = specGal s ≫ specEmb K e₁)
      (hg : specEmb K e₂ = specGal s ≫ specEmb K e₂),
      G4Conj.conj A.X B.X (specGal s) hf hg φ.hom = φ.hom

/-- **Glue Prop: valuation rings of number fields are DVRs** (standard; see `isDVR_comap`). -/
def ComapDVR : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (f : K →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ), p.Prime → LiesOver w p →
    IsDiscreteValuationRing (w.comap f)

theorem fixes_of_spec (s : Gal) (e : K →ₐ[ℚ] Qbar) (h : specEmb K e = specGal s ≫ specEmb K e) :
    ∀ x, s (e x) = e x := by
  intro x
  have h' := Spec.map_injective (h.trans (specMap_comp _ _))
  have := congrArg (fun φ => (CommRingCat.Hom.hom φ) x) h'
  exact this.symm

/-- **`InertiaFixesHomsMon` from NOS and Mumford §19 Thm 3 (glue, proved).** -/
theorem inertiaFixesHomsMon (hNOS : PkgI2.NeronOggShafarevich.{0}) (hHFF : HomFreeFinite)
    (hDVR : ComapDVR) : InertiaFixesHomsMon := by
  intro K _ A B e₁ e₂ φ w p hp hw hA hB s hs hf hg
  have := hDVR K (e₁ : K →+* Qbar) w p hp hw
  have := hDVR K (e₂ : K →+* Qbar) w p hp hw
  -- an auxiliary prime `ℓ ≠ p`
  obtain ⟨ℓ, hℓ, hℓp⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
    by_cases h2 : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h => h2 h.symm⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hse₁ := fixes_of_spec K s e₁ hf
  have hse₂ := fixes_of_spec K s e₂ hg
  have hunit : ∀ (e : K →ₐ[ℚ] Qbar) (n : ℕ),
      IsUnit (((ℓ ^ n : ℕ) : ℕ) : w.comap (e : K →+* Qbar)) := fun e n => by
    rw [Nat.cast_pow]
    exact (isUnit_prime_of_liesOver (e : K →+* Qbar) w p hp hw ℓ hℓ hℓp).pow n
  let A₁ := bcAlong A (e₁ : K →+* Qbar)
  let B₂ := bcAlong B (e₂ : K →+* Qbar)
  let ψ : A₁.X ⟶ B₂.X := G4Conj.conj A.X B.X (specGal s) hf hg φ.hom
  have hψ : IsMonHom ψ :=
    G4Conj.conj_isMonHom' A.X B.X (specGal s) hf hg φ.hom (show IsMonHom φ.hom from inferInstance)
  -- agreement on torsion sections over `Spec ℚ̄`
  have hsec : ∀ (n : ℕ) (Q : CategoryTheory.Over.mk (𝟙 (Spec (CommRingCat.of Qbar))) ⟶ A₁.X),
      Q ^ (ℓ ^ n) = 1 → Q.left ≫ ψ.left = Q.left ≫ φ.hom.left := by
    intro n Q hQ
    have hfixA : Q.left ≫ G4Conj.cmp A.X (specGal s) hf = specGal s ≫ Q.left := by
      apply G4Conj.cmp_fixed_of_fst A.X (specGal s) hf Q.left (CategoryTheory.Over.w Q)
      have hq : G4Conj.secFst A.X (specEmb K e₁) Q ^ (ℓ ^ n) = 1 :=
        (G4Conj.secFst_pow A.X (specEmb K e₁) Q (ℓ ^ n)).symm.trans
          ((congrArg (G4Conj.secFst A.X (specEmb K e₁)) hQ).trans (G4Conj.secFst_one _ _))
      have := point_fixed K hNOS A e₁ w hA s hs hse₁ (ℓ ^ n) (pow_pos hℓ.pos n) (hunit e₁ n)
        (G4Conj.secFst A.X (specEmb K e₁) Q) hq
      exact this
    have hfixB : (Q ≫ φ.hom).left ≫ G4Conj.cmp B.X (specGal s) hg =
        specGal s ≫ (Q ≫ φ.hom).left := by
      apply G4Conj.cmp_fixed_of_fst B.X (specGal s) hg (Q ≫ φ.hom).left (CategoryTheory.Over.w _)
      have hQφ : (Q ≫ φ.hom) ^ (ℓ ^ n) = 1 := by
        rw [← MonObj.pow_comp, hQ, MonObj.one_comp]
      have hq : G4Conj.secFst B.X (specEmb K e₂) (Q ≫ φ.hom) ^ (ℓ ^ n) = 1 :=
        (G4Conj.secFst_pow B.X (specEmb K e₂) (Q ≫ φ.hom) (ℓ ^ n)).symm.trans
          ((congrArg (G4Conj.secFst B.X (specEmb K e₂)) hQφ).trans (G4Conj.secFst_one _ _))
      have := point_fixed K hNOS B e₂ w hB s hs hse₂ (ℓ ^ n) (pow_pos hℓ.pos n) (hunit e₂ n)
        (G4Conj.secFst B.X (specEmb K e₂) (Q ≫ φ.hom)) hq
      exact this
    exact G4Conj.conj_agree A.X B.X (specGal s) hf hg φ.hom Q.left (specGal s) hfixA
      hfixB
  -- conclude with Mumford's injectivity into Hom of Tate modules
  have hne : (ℓ : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  let Ψ : AbVar.Hom A₁ B₂ := @AbVar.Hom.mk' _ _ A₁ B₂ ψ hψ
  have key : tateHom ℓ A₁ B₂ Ψ = tateHom ℓ A₁ B₂ φ := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    have htor : (Additive.toMul (t.1 n)) ^ (ℓ ^ n) = 1 :=
      congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero t.2 n)
    set P := Additive.toMul (t.1 n)
    have hP : (ptIso.inv ≫ P) ^ (ℓ ^ n) = 1 := by
      rw [← MonObj.comp_pow, htor, MonObj.comp_one]
    have h1 := hsec n (ptIso.inv ≫ P) hP
    have hPl : P.left = ptIso.hom.left ≫ (ptIso.inv ≫ P).left :=
      congrArg CategoryTheory.Over.Hom.left (Iso.hom_inv_id_assoc ptIso P).symm
    have h2 : P ≫ ψ = P ≫ φ.hom := by
      apply CategoryTheory.Over.OverMorphism.ext
      show P.left ≫ ψ.left = P.left ≫ φ.hom.left
      rw [hPl, Category.assoc, Category.assoc, h1]
    show Additive.ofMul (P ≫ ψ) = Additive.ofMul (P ≫ φ.hom)
    rw [h2]
  have := tateHom_injective hHFF A₁ B₂ ℓ hne key
  exact congrArg AbVar.Hom.hom this

/-- `ComapDVR` holds (glue, proved: `InertiaHoms.comap_isDVR`). -/
theorem comapDVR : ComapDVR := by
  intro K _ f w p hp hw
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  exact comap_isDVR f w p hp hw

/-- **`InertiaFixesHomsMon` from the two leaves (glue, proved).** Leaves:
`PkgI2.NeronOggShafarevich` (Serre–Tate 1968 Thm 1) and `PkgI3.HomFreeFinite` (Mumford §19
Thm 3). -/
theorem inertiaFixesHomsMon_of_leaves (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hHFF : HomFreeFinite) : InertiaFixesHomsMon :=
  inertiaFixesHomsMon hNOS hHFF comapDVR

end G4WeilRes

namespace G4WeilRes

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms

variable (K : IntermediateField ℚ Qbar)

/-- **The inertia hypothesis of G4 from the corrected input (glue, proved).** As
`conjAction_inertia`, with `InertiaFixesHomsMon` in place of `InertiaFixesHoms`. -/
theorem conjAction_inertia' (hI : InertiaFixesHomsMon) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1 := by
  intro p hp hpT w hw
  intro (σ : Gal) (hσ : σ ∈ inertiaGQ w)
  have hσK : σ ∈ K.fixingSubgroup := hK p hp hpT w hw hσ
  apply LinearEquiv.ext
  intro m
  show conjAct K A σ m = m
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
      (hf : specEmb K i = specGal σ ≫ specEmb K i')
      (hg : specEmb K j = specGal σ ≫ specEmb K j'),
      G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
    intro i' j' hi hj hf hg
    subst hi hj
    exact hI K A A i' j' (m (i', j')) w p hp hw (hgood p hp hpT w hw i')
      (hgood p hp hpT w hw j') σ hσ hf hg
  exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _

/-- **G4 for a model `A/K`, with the inertia input eliminated.** Leaves: `HomFreeFinite`
(Mumford §19 Thm 3), `MorphismsDescend` (EGA IV₃ 8.8.2), `NeronOggShafarevich` (Serre–Tate 1968
Thm 1). Hypotheses from other glue steps: `hK` (G2), `hgood` (G3), `hdim` (dimension of base
change). -/
theorem homField_of_model_leaves' (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_final K hHFF hM hKF A hdim T hK
    (conjAction_inertia' K (inertiaFixesHomsMon_of_leaves hNOS hHFF) A T hK hgood)

end G4WeilRes
end PartInertia

section PartClosed
namespace G4WeilRes

/-- **`MorphismsDescend` of G4 (EGA IV₃ 8.8.2), proved.** The statement here (over
`GlueB3Unram.Qbar`) is `MorphDescend.MorphismsDescend` (over `MorphDescend.Qbar`); both `Qbar`s
are the reducible abbreviation `AlgebraicClosure ℚ`. -/
theorem morphismsDescend : MorphismsDescend := MorphDescend.morphismsDescend

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField PkgI3 AlgebraicGeometry

variable (K : IntermediateField ℚ Qbar)

/-- **G4 for a model `A/K`, with `MorphismsDescend` discharged.** Remaining inputs:
`HomFreeFinite` (Mumford §19 Thm 3), `InertiaFixesHoms`; hypotheses `hK` (G2), `hgood` (G3),
`hdim`. -/
theorem homField_of_model_closed (hHFF : HomFreeFinite)
    (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_leaves K hHFF morphismsDescend hI hKF A hdim T hK hgood

/-- `HomDescends` (continuity input of G4), now unconditional. -/
theorem homDescends : HomDescends := homDescends_of_morphismsDescend morphismsDescend

end G4WeilRes
end PartClosed

/-! # Part 6 (new, task kernel-field): `KernelFieldExists` from the G4 leaves and two glue Props

Everything above is a verbatim copy (see `assemble.sh`). This part proves
`G0ModField.KernelField.kernelFieldExists_of_pieces`:

  `HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
  `RaynaudCriterion`, `TorsionStructure` (the kernel's leaves, used by `QML3.goodReduction`)
  + `ConjMapsOnHomField` (glue: the conjugacy maps `m_σ = μ_σ ∘ σ` on the Hom field, with an
    integral discrepancy) + `TorsionCountPts` (glue: `|A(ℚ̄)[n]| = n⁴` for abelian surfaces over
    subfields of `ℚ̄`)
  ⟹ `KernelFieldExists` (g0-mod-field's statement, unchanged).

* §6.1 `conjugacyData_of_maps`: pure algebra. The rational discrepancy `c`, its cocycle identity,
  inflation, `c(1,1) = 1` and the kernel-size identity `|ker m_σ||ker m_τ| = c⁴|ker m_στ|` all
  follow from the maps, an integral relation `d·m_σ m_τ = n·m_στ`, and `|V[n]| = n⁴`.
* §6.2 `kernelField_core`: `homField_core` with the kernel field `E = ℚ̄^{ker ρ}` and the finite
  group `G = ρ(G_ℚ) ≤ GL_r(ℤ)` exposed (`[E:ℚ] = |G|`).
* §6.3 `kernelField_of_model`: G4 (g4-weilres + inertia-homs + morph-descend) in
  `KernelFieldOut`'s shape: `r ≤ 16F₀²`, `G`, `E` unramified outside `T`, and `G_{E⊔K}` fixes
  every homomorphism between the conjugates of `A`.
* §6.4 the hypotheses of G4 on a rational fibre: `hdim` from `G0Dim.dim_baseChange` (g0-dim,
  proved), `hgood` from `QML3.goodReduction` (leaves NOS, Raynaud, TorsionStructure), `hK` from
  `galUnramifiedOutside_iff`.
* §6.5 the remaining glue Props and the headline.
-/

section Part61

open CategoryTheory AlgebraicGeometry Limits
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-! ## §6.1 The discrepancy: pure algebra -/

section Algebra

variable {V : Type*} [AddCommGroup V]

/-- `V[n]`, the `n`-torsion subgroup. -/
abbrev tors (V : Type*) [AddCommGroup V] (n : ℕ) : AddSubgroup V := (n • AddMonoidHom.id V).ker

/-- `|V[n]| = n⁴` for every `n ≥ 1` (the `ℚ̄`-points of an abelian surface in characteristic 0). -/
def TorsCount (V : Type*) [AddCommGroup V] : Prop :=
  ∀ n : ℕ, 0 < n → Nat.card (tors V n) = n ^ 4

theorem mem_tors {n : ℕ} {x : V} : x ∈ tors V n ↔ n • x = 0 := by
  simp [tors, AddMonoidHom.mem_ker]

theorem zsmul_eq_zero_iff_natAbs {d : ℤ} {y : V} : d • y = 0 ↔ d.natAbs • y = 0 := by
  rcases Int.natAbs_eq d with h | h
  · conv_lhs => rw [h]
    rw [natCast_zsmul]
  · conv_lhs => rw [h]
    rw [neg_smul, neg_eq_zero, natCast_zsmul]

/-- A group with `|V[n]| = n⁴` has no nonzero integer exponent. -/
theorem eq_zero_of_forall_zsmul (hT : TorsCount V) {k : ℤ} (hk : ∀ x : V, k • x = 0) : k = 0 := by
  by_contra hk0
  set N := k.natAbs with hN
  have hNpos : 0 < N := Int.natAbs_pos.mpr hk0
  have h1 : tors V N = ⊤ := by
    ext x; simp only [mem_tors, AddSubgroup.mem_top, iff_true]
    exact zsmul_eq_zero_iff_natAbs.mp (hk x)
  have h2 : tors V (2 * N) = ⊤ := by
    ext x; simp only [mem_tors, AddSubgroup.mem_top, iff_true]
    have hx : x ∈ tors V N := by rw [h1]; exact AddSubgroup.mem_top x
    rw [mem_tors] at hx
    rw [mul_smul, hx, smul_zero]
  have c1 := hT N hNpos
  have c2 := hT (2 * N) (by omega)
  rw [h1] at c1
  rw [h2, c1] at c2
  have h16 : (2 * N) ^ 4 = 16 * N ^ 4 := by ring
  rw [h16] at c2
  have hN4 : 0 < N ^ 4 := pow_pos hNpos 4
  omega

/-- `f = q·g` rationally: `d·f = n·g` with `q = n/d`. -/
def Rel (f g : V →+ V) (q : ℚ) : Prop := ∃ n d : ℤ, d ≠ 0 ∧ q = n / d ∧ d • f = n • g

theorem rel_unique (hT : TorsCount V) {f g : V →+ V} (hg : Function.Surjective g) {q q' : ℚ}
    (h : Rel f g q) (h' : Rel f g q') : q = q' := by
  obtain ⟨n, d, hd, rfl, e⟩ := h
  obtain ⟨n', d', hd', rfl, e'⟩ := h'
  have key : ∀ y : V, (d' * n - d * n') • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    have a := DFunLike.congr_fun e x
    have b := DFunLike.congr_fun e' x
    simp only [AddMonoidHom.smul_apply] at a b
    rw [sub_smul, mul_smul, mul_smul, ← a, ← b, smul_comm d' d, sub_self]
  have := eq_zero_of_forall_zsmul hT key
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdq' : (d' : ℚ) ≠ 0 := by exact_mod_cast hd'
  rw [div_eq_div_iff hdq hdq']
  have : (d' : ℚ) * n = d * n' := by exact_mod_cast sub_eq_zero.mp this
  linarith

theorem rel_comp_right {f g : V →+ V} {q : ℚ} (h : Rel f g q) (k : V →+ V) :
    Rel (f.comp k) (g.comp k) q := by
  obtain ⟨n, d, hd, hq, e⟩ := h
  refine ⟨n, d, hd, hq, AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e (k x)
  simpa only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] using a

theorem rel_comp_left {f g : V →+ V} {q : ℚ} (h : Rel f g q) (k : V →+ V) :
    Rel (k.comp f) (k.comp g) q := by
  obtain ⟨n, d, hd, hq, e⟩ := h
  refine ⟨n, d, hd, hq, AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e x
  simp only [AddMonoidHom.smul_apply] at a
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, ← map_zsmul, a]

theorem rel_trans {f g k : V →+ V} {q q' : ℚ} (h : Rel f g q) (h' : Rel g k q') :
    Rel f k (q * q') := by
  obtain ⟨n, d, hd, rfl, e⟩ := h
  obtain ⟨n', d', hd', rfl, e'⟩ := h'
  refine ⟨n * n', d * d', mul_ne_zero hd hd', by push_cast; rw [div_mul_div_comm],
    AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e x
  have b := DFunLike.congr_fun e' x
  simp only [AddMonoidHom.smul_apply] at a b ⊢
  rw [mul_comm d d', mul_smul, a, smul_comm, b, ← mul_smul]

theorem rel_self (f : V →+ V) : Rel f f 1 := ⟨1, 1, one_ne_zero, by simp, rfl⟩

/-- `|f⁻¹(H)| = |H|·|ker f|` for surjective `f`. -/
theorem card_comap {f : V →+ V} (hf : Function.Surjective f) (H : AddSubgroup V) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let g : H.comap f →+ H := f.addSubgroupComap H
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have e1 : (H.comap f ⧸ g.ker) ≃+ H := QuotientAddGroup.quotientKerEquivOfSurjective g hg
  have e2 : g.ker ≃ f.ker :=
    { toFun := fun x => ⟨x.1.1, AddMonoidHom.mem_ker.mpr
        (congrArg Subtype.val (AddMonoidHom.mem_ker.mp x.2))⟩
      invFun := fun y => ⟨⟨y.1, by
          show f y.1 ∈ H
          rw [AddMonoidHom.mem_ker.mp y.2]; exact H.zero_mem⟩,
        AddMonoidHom.mem_ker.mpr (Subtype.ext (AddMonoidHom.mem_ker.mp y.2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, Nat.card_congr e1.toEquiv,
    Nat.card_congr e2]

theorem card_ker_comp {f g : V →+ V} (hg : Function.Surjective g) :
    Nat.card (f.comp g).ker = Nat.card f.ker * Nat.card g.ker := by
  have : (f.comp g).ker = f.ker.comap g := by
    ext x; simp [AddMonoidHom.mem_ker]
  rw [this, card_comap hg]

theorem card_ker_zsmul (hT : TorsCount V) {f : V →+ V} (hf : Function.Surjective f) {d : ℤ}
    (hd : d ≠ 0) : Nat.card (d • f).ker = d.natAbs ^ 4 * Nat.card f.ker := by
  have : (d • f).ker = (tors V d.natAbs).comap f := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddSubgroup.mem_comap, mem_tors]
    exact zsmul_eq_zero_iff_natAbs
  rw [this, card_comap hf, hT _ (Int.natAbs_pos.mpr hd)]

/-- **The kernel identity from the integral relation** (`deg(d·φ) = d⁴ deg φ` on a surface). -/
theorem card_identity (hT : TorsCount V) {f g h : V →+ V} (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hh : Function.Surjective h) {n d : ℤ} (hn : n ≠ 0) (hd : d ≠ 0)
    (e : d • f.comp g = n • h) :
    (Nat.card f.ker : ℚ) * Nat.card g.ker = ((n : ℚ) / d) ^ 4 * Nat.card h.ker := by
  have h1 : Nat.card (d • f.comp g).ker = d.natAbs ^ 4 * Nat.card (f.comp g).ker :=
    card_ker_zsmul hT (f := f.comp g) (hf.comp hg) hd
  have h2 := card_ker_zsmul hT hh hn
  rw [card_ker_comp hg, e] at h1
  rw [h1] at h2
  have hq : ((d.natAbs : ℚ)) ^ 4 = (d : ℚ) ^ 4 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Even.pow_abs ⟨2, rfl⟩]
  have hq' : ((n.natAbs : ℚ)) ^ 4 = (n : ℚ) ^ 4 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Even.pow_abs ⟨2, rfl⟩]
  have h3 : ((d.natAbs ^ 4 * (Nat.card f.ker * Nat.card g.ker) : ℕ) : ℚ) =
      ((n.natAbs ^ 4 * Nat.card h.ker : ℕ) : ℚ) := by rw [h2]
  push_cast at h3
  rw [hq, hq'] at h3
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [div_pow]
  field_simp
  linarith

end Algebra

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem act_mul (σ τ : GQ) (x : Qbar) : act (σ * τ) x = act σ (act τ x) := rfl

theorem act_inv_act (σ : GQ) (x : Qbar) : act σ⁻¹ (act σ x) = x := by
  rw [← act_mul, inv_mul_cancel]; rfl

/-- **§6.1, the reduction of `ConjugacyData` to the maps (proved).** For `L` finite Galois and
`A/L` with `|A(ℚ̄)[n]| = n⁴`: maps `m_σ` on `A(ℚ̄)` with `ConjugacyData`'s clauses on the Galois
action, inflation, commutation with `End_L(A)`, surjectivity/finite kernel and algebraicity, and
an integral relation `d·m_σ m_τ = n·m_στ` (`d ≠ 0`), carry a rational discrepancy `c` with all of
`ConjugacyData`: `c = n/d` is well defined (`rel_unique`), `≠ 0`, a 2-cocycle, inflated from
`Gal(L/ℚ)`, `c(1,1) = 1`, and `|ker m_σ||ker m_τ| = c⁴|ker m_στ|`. -/
theorem conjugacyData_of_maps (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (hend : ∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ))
    (hfin : ∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite)
    (hdisc : ∀ σ τ, ∃ n d : ℤ, d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ))
    (halg : ∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ) :
    ∃ c : GQ → GQ → ℚ, ConjugacyData L A m c := by
  choose n d hd hnd using hdisc
  let c : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have hsurj : ∀ σ, Function.Surjective (m σ) := fun σ => (hfin σ).1
  have hR : ∀ σ τ, Rel ((m σ).comp (m τ)) (m (σ * τ)) (c σ τ) :=
    fun σ τ => ⟨n σ τ, d σ τ, hd σ τ, rfl, hnd σ τ⟩
  have hn : ∀ σ τ, n σ τ ≠ 0 := by
    intro σ τ hn0
    have key : ∀ y : PtQ L A, d σ τ • y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := ((hsurj σ).comp (hsurj τ)) y
      simp only [Function.comp_apply]
      have a := DFunLike.congr_fun (hnd σ τ) x
      rw [hn0] at a
      simpa only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, zero_smul] using a
    exact hd σ τ (eq_zero_of_forall_zsmul hT key)
  have hnorm : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hone : (1 : GQ) ∈ GQL L := (GQL L).one_mem
  refine ⟨c, hgal, hinfl, hend, hfin, fun σ τ => ⟨div_ne_zero (by exact_mod_cast hn σ τ)
    (by exact_mod_cast hd σ τ), n σ τ, d σ τ, hd σ τ, rfl, hnd σ τ⟩, ?_, ?_, ?_, ?_, halg⟩
  · -- the cocycle identity
    intro σ τ ρ
    have r1 := rel_trans (rel_comp_right (hR σ τ) (m ρ)) (hR (σ * τ) ρ)
    have r2 := rel_trans (rel_comp_left (hR τ ρ) (m σ)) (hR σ (τ * ρ))
    rw [← _root_.mul_assoc] at r2
    have := rel_unique hT (hsurj _) r1 r2
    rw [mul_comm]; exact this
  · -- inflation from `Gal(L/ℚ)`
    intro σ σ' τ τ' h1 h2
    set k := σ⁻¹ * σ' with hk
    set k' := τ⁻¹ * τ' with hk'
    have hkL : k ∈ GQL L := by
      rw [mem_GQL]; intro x hx
      rw [act_mul, ← h1 x hx, act_inv_act]
    have hk'L : k' ∈ GQL L := by
      rw [mem_GQL]; intro x hx
      rw [act_mul, ← h2 x hx, act_inv_act]
    have eσ : σ' = σ * k := by rw [hk, mul_inv_cancel_left]
    have eτ : τ' = τ * k' := by rw [hk', mul_inv_cancel_left]
    set k'' := τ⁻¹ * k * τ with hk''
    have hk''L : k'' ∈ GQL L := by
      have := hnorm.conj_mem k hkL τ⁻¹
      rwa [inv_inv] at this
    have hkτ : k * τ = τ * k'' := by rw [hk'']; group
    have hmm : (m σ').comp (m τ') = ((m σ).comp (m τ)).comp (m (k'' * k')) := by
      rw [eσ, eτ, (hinfl σ k hkL).1, (hinfl τ k' hk'L).1, (hinfl k'' k' hk'L).1]
      have h3 : (m k).comp (m τ) = (m τ).comp (m k'') := by
        rw [← (hinfl τ k hkL).2, hkτ, (hinfl τ k'' hk''L).1]
      refine AddMonoidHom.ext fun x => ?_
      have := DFunLike.congr_fun h3 (m k' x)
      simp only [AddMonoidHom.comp_apply] at this ⊢
      rw [this]
    have hgrp : σ' * τ' = σ * τ * (k'' * k') := by
      rw [eσ, eτ, hk'']; group
    have r1 : Rel ((m σ').comp (m τ')) (m (σ' * τ')) (c σ τ) := by
      rw [hmm, hgrp, (hinfl (σ * τ) (k'' * k') ((GQL L).mul_mem hk''L hk'L)).1]
      exact rel_comp_right (hR σ τ) _
    exact (rel_unique hT (hsurj _) (hR σ' τ') r1).symm
  · -- `c(1,1) = 1`
    have r : Rel ((m 1).comp (m 1)) (m (1 * 1)) 1 := by
      rw [← (hinfl 1 1 hone).1]; exact rel_self _
    exact rel_unique hT (hsurj _) (hR 1 1) r
  · -- the kernel identity
    intro σ τ
    exact card_identity hT (hsurj σ) (hsurj τ) (hsurj (σ * τ)) (hn σ τ) (hd σ τ) (hnd σ τ)

/-- **`ConjugacyData` without the discrepancy**: the maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the
Galois action on `G_L`, inflation from `Gal(L/ℚ)`, commutation with `End_L(A)`, surjectivity and
finite kernel, an integral relation `d·m_σ m_τ = n·m_στ` (`d ≠ 0`; Glazer N5 L640-644: the
discrepancy `μ_σ ^σμ_τ μ_στ⁻¹` commutes with `B`, hence is a rational scalar), and algebraicity
(`m_σ(x) = F_σ ∘ x ∘ Spec σ`, `F_σ` finite surjective). Clauses 1-4 and 10 of `ConjugacyData`
verbatim; clause 5 without `c`. -/
def ConjMaps (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, ∃ n d : ℤ, d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

theorem conjugacyData_of_conjMaps (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (h : ConjMaps L A m) : ∃ c : GQ → GQ → ℚ, ConjugacyData L A m c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact conjugacyData_of_maps L A m hT h1 h2 h3 h4 h5 h6

end G0ModField.KernelField

end Part61

/-! ## §6.2-6.3 The kernel field `E` and the group `G ≤ GL_r(ℤ)` (G4, exposed) -/

section KernelCore

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj

namespace G0ModField.KernelField

/-- **`homField_core` with the kernel field exposed (proved; the proof is `homField_core`'s).**
For a continuous `ℤ`-linear action `ρ` of `G_ℚ` on a free `ℤ`-module with basis `Fin r`, trivial
on inertia outside `T`: `E = ℚ̄^{ker ρ}` is finite Galois with `[E:ℚ] = |G|` for the finite group
`G = ρ(G_ℚ) ≤ GL_r(ℤ)`, `G_E` acts trivially, and `E` is unramified outside `T`. -/
theorem kernelField_core {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M)) (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧ (∀ σ ∈ E.fixingSubgroup, ρ σ = 1) ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (G4WeilRes.toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact G4WeilRes.toGL_eq_one_iff b (ρ σ)
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact G4WeilRes.eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  have hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  have hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  refine ⟨ρ'.range, inferInstance, E, hEfd, hEgal, hcardE, fun σ hσ => ?_, ?_⟩
  · rw [hE] at hσ; exact hσ
  · apply G4WeilRes.unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 in `KernelFieldOut`'s shape (proved from the leaves `HomFreeFinite` and
`NeronOggShafarevich`; `MorphismsDescend` is proved, morph-descend).** For `A/K` (`K` finite
Galois, `[K:ℚ] ≤ F₀`, unramified outside `T`) whose conjugates are surfaces and which has good
reduction at every place over every `p ∉ T`: the Hom lattice `⊕ Hom(A_e, A_e')` (the endomorphism
lattice of `Res_{K/ℚ} A ⊗ ℚ̄`) has rank `r ≤ 16F₀²`, the image `G` of `G_ℚ` in `GL_r(ℤ)` is
finite with kernel field `E`, `[E:ℚ] = |G|`, `E` is unramified outside `T`, and `G_{E⊔K}` fixes
every homomorphism between conjugates (`E ⊔ K` is the Hom field). -/
theorem kernelField_of_model (hHFF : HomFreeFinite) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((G4WeilRes.conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ r : ℕ, r ≤ 16 * ZInQ.heightF0 ^ 2 ∧
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) ∧
      (∀ σ ∈ (E ⊔ K).fixingSubgroup, G4WeilRes.conjAction K A σ = 1) := by
  obtain ⟨hfree, hfin, hrank⟩ := G4WeilRes.homLattice_free hHFF (G4WeilRes.conjData K A).A hdim
  have hr : Module.finrank ℤ (G4WeilRes.HomLattice (G4WeilRes.conjData K A).A) ≤
      16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by rw [G4WeilRes.card_conjugates]; exact hKF) 2))
  obtain ⟨G, hG, E, hfE, hgE, hEG, hfix, hram⟩ :=
    kernelField_core (Module.finBasisOfFinrankEq ℤ _ rfl) (G4WeilRes.conjAction K A)
      (G4WeilRes.conjAction_continuous K G4WeilRes.homDescends A) T
      (G4WeilRes.conjAction_inertia' K (G4WeilRes.inertiaFixesHomsMon_of_leaves hNOS hHFF) A T
        hK hgood)
  exact ⟨_, hr, G, hG, E, hfE, hgE, hEG, hram,
    fun σ hσ => hfix σ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ)⟩

end G0ModField.KernelField

end KernelCore

/-! ## §6.4-6.5 G4's hypotheses on a rational fibre; the remaining Props; the headline -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

theorem three_mem_T (u : ℚ) : 3 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- `hdim` of G4 (proved, from g0-dim's `G0Dim.dim_baseChange`): the conjugates
`A ×_{K,e} ℚ̄` of an abelian surface are surfaces. -/
theorem conj_dim (K : IF) (A : PkgI3.AbVar K) (hA : A.dim = 2) (e : K →ₐ[ℚ] Qbar) :
    ((G4WeilRes.conjData K A).A e).dim = 2 := by
  letI : Algebra K Qbar := (e : K →+* Qbar).toAlgebra
  exact (G0Dim.dim_baseChange (K := K) Qbar A.X.left A.X.hom).trans hA

/-- The base change `A_L` of an abelian surface `A/K` is a surface (g0-dim). -/
theorem bc_dim {K L : IF} (hKL : K ≤ L) (A : PkgI3.AbVar K) (hA : A.dim = 2) :
    (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)).dim = 2 := by
  letI : Algebra K L := incAlg hKL
  exact (G0Dim.dim_baseChange (K := K) L A.X.left A.X.hom).trans hA

/-- `hgood` of G4 on a `QML3` object (G3; proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` through `LeafQM.AV.QML3.goodReduction`, with
inertia-homs' `comap_isDVR` and `isUnit_prime_of_liesOver`): good reduction at every place over
every `p ∉ T` when `3 ∈ T`. -/
theorem good_of_QML3 (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (K : IF) [FiniteDimensional ℚ K] (PK : QML3 K)
    (T : Finset ℕ) (h3 : 3 ∈ T) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, GlueB3Unram.LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar,
        PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) (w.comap (e : K →+* Qbar)) := by
  intro p hp hpT w hw e
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI := InertiaHoms.comap_isDVR (e : K →+* Qbar) w p hp hw
  have h3u : IsUnit ((3 : ℕ) : w.comap (e : K →+* Qbar)) :=
    InertiaHoms.isUnit_prime_of_liesOver _ w p hp hw 3 Nat.prime_three
      (by rintro rfl; exact hpT h3)
  exact QML3.goodReduction (P := PK) hNOS hRay hTors _ (by simpa using h3u)

/-- **Remaining glue 1 (`|A(ℚ̄)[n]| = n⁴`).** For an abelian surface `A` over a subfield
`L ⊆ ℚ̄`, the `n`-torsion of `A(ℚ̄)` has `n⁴` elements for every `n ≥ 1` (Mumford, *Abelian
varieties*, §4 Application 2 / §6, UNVERIFIED locator: `[n]` is separable of degree `n^{2g}` in
characteristic 0). It is the leaf `PkgI2.TorsionStructure` (`A(K̄)[n] ≅ (ℤ/n)^{2g}` over
`K̄ = AlgebraicClosure K`) transported along `AlgebraicClosure L ≅ ℚ̄` over `L` and from
`PkgI2.Pts (toGrp A)` to `PkgI3.AbVar.Pt`: glue. -/
def TorsionCountPts : Prop :=
  ∀ (L : IF) (A : PkgI3.AbVar L), A.dim = 2 → TorsCount (PtQ L A)

/-- **`TorsionCountPts`, proved from the leaf `PkgI2.TorsionStructure`** (`A(K̄)[n] ≅ (ℤ/n)^{2g}`,
Mumford §4/§6, the kernel's leaf): `ℚ̄` is an algebraic closure of `L` (inertia-homs'
`exists_closure_equiv`), and precomposition with `Spec ι : Spec ℚ̄ ≅ Spec K̄` over `Spec L` is a
bijection of points respecting powers (`MonObj.comp_pow`). -/
theorem torsionCountPts_of_leaf (hTors : PkgI2.TorsionStructure.{0}) : TorsionCountPts := by
  intro L A hA n hn
  obtain ⟨jj, hjj⟩ := InertiaHoms.exists_closure_equiv L L.val
  have hcomp : CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) ≫
      CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) =
      CommRingCat.ofHom (algebraMap L Qbar) := by
    ext x; exact hjj x
  have hcomp' : CommRingCat.ofHom (algebraMap L Qbar) ≫
      CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) =
      CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) := by
    rw [← hcomp]; ext x; simp
  let s : PkgI3.AbVar.ptObj (K := L) Qbar ⟶ PkgI2.specOver L (AlgebraicClosure L) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, hcomp])
  let s' : PkgI2.specOver L (AlgebraicClosure L) ⟶ PkgI3.AbVar.ptObj (K := L) Qbar :=
    Over.homMk (Spec.map (CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, hcomp'])
  have h1 : CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) ≫
      CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) = 𝟙 _ := by
    ext x; simp
  have h2 : CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) ≫
      CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) = 𝟙 _ := by
    ext x; simp
  have hss' : s ≫ s' = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, h1, Spec.map_id]
  have hs's : s' ≫ s = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, h2, Spec.map_id]
  have hdim : topologicalKrullDim (ObjBridge.toGrp A).X.left = ((2 : ℕ) : WithBot ℕ∞) := by
    change A.dim = _
    rw [hA]; rfl
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨e, -⟩ := hTors L (ObjBridge.toGrp A) 2 n hdim hn (by exact_mod_cast hn.ne')
  let F : PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) n ≃ tors (PtQ L A) n :=
    { toFun := fun x => ⟨Additive.ofMul (s ≫ x.1), by
        rw [mem_tors, ← ofMul_pow, ← MonObj.comp_pow]
        have hx : x.1 ^ n = 1 := x.2
        rw [hx, MonObj.comp_one]; rfl⟩
      invFun := fun y => ⟨s' ≫ Additive.toMul y.1, by
        have hy : n • y.1 = 0 := mem_tors.mp y.2
        show (s' ≫ Additive.toMul y.1) ^ n = 1
        rw [← MonObj.comp_pow, ← toMul_nsmul, hy]
        exact MonObj.comp_one _⟩
      left_inv := fun x => by
        apply Subtype.ext
        show s' ≫ s ≫ x.1 = x.1
        rw [← Category.assoc, hs's, Category.id_comp]
      right_inv := fun y => by
        apply Subtype.ext
        show Additive.ofMul (s ≫ s' ≫ Additive.toMul y.1) = y.1
        rw [← Category.assoc, hss', Category.id_comp]; rfl }
  rw [← Nat.card_congr F, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **Remaining glue 2 (G4 + B1's geometric half on the Hom field: the conjugacy maps).** For
every fibre context, every rational fibre `PK/K` as in G2's output, and every finite Galois
`L ⊇ K` that is a Hom field of `PK.A` (`G_L` fixes every homomorphism between the conjugates of
`PK.A` over `ℚ̄`, g4-weilres' `conjAction`), the base change `A_L` carries the maps
`m_σ = μ_σ ∘ σ` of `ConjMaps` (N5 L632-645: `μ_σ : ^σA → A` the conjugacy isogenies, from A7
`conj_twist_of_rational` and Skolem–Noether, `B`-linear; rational discrepancy by
`End⁰(A_ℚ̄) = B`, i.e. NoCM). -/
def ConjMapsOnHomField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjMaps L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) m

/-- **Headline (proved): `KernelFieldExists` from four leaves and two glue Props.** Leaves:
`HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
`RaynaudCriterion`, `TorsionStructure` (the kernel's leaves behind `QML3.goodReduction`). Glue:
`TorsionCountPts`, `ConjMapsOnHomField`. Proved on the way: G4 with `E` and `G` exposed
(`kernelField_of_model`), `MorphismsDescend` (morph-descend), `hdim` (g0-dim), `hgood` (G3 on
`QML3` objects), and the discrepancy algebra (`conjugacyData_of_maps`). -/
theorem kernelFieldExists_of_pieces (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hCount : TorsionCountPts)
    (hMaps : ConjMapsOnHomField) : KernelFieldExists := by
  intro Y Φ π u P hctx K _ _ hKF hramK PK hPK
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model hHFF hNOS K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3 hNOS hRay hTors K PK (T u) (three_mem_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  obtain ⟨m, hm⟩ := hMaps Y Φ π u P hctx K hKF hramK PK hPK (E ⊔ K) le_sup_right hfix
  obtain ⟨c, hc⟩ := conjugacyData_of_conjMaps _ _ m
    (hCount _ _ (bc_dim le_sup_right PK.A PK.surface)) hm
  exact ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hc⟩

/-- **Headline, final form (proved): `KernelFieldExists` from four leaves and one glue Prop.**
Leaves: `HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
`RaynaudCriterion` (Raynaud / Grothendieck SGA 7 IX), `TorsionStructure` (Mumford §4/§6).
Glue: `ConjMapsOnHomField` (the conjugacy maps on the Hom field: A7 + Skolem–Noether + NoCM). -/
theorem kernelFieldExists_of_leaves (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hMaps : ConjMapsOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_pieces hHFF hNOS hRay hTors (torsionCountPts_of_leaf hTors) hMaps

end G0ModField.KernelField


/-! ## §6.6 The NoCM input made explicit: `FibreComTrivial` (g0-fibresimple's FS5, verbatim) -/

-- (g0-assemble2) section FS5Copy (verbatim copy of g0-fibresimple's `FibreComTrivial`) is not repeated: part 40 defines it.

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- **Remaining glue 2′ (the conjugacy maps, NoCM given).** As `ConjMapsOnHomField`, with the
NoCM input `End_𝒪(P.A) = ℤ` (FS5's conclusion) as an explicit hypothesis and with only what the
construction uses: moduli data with R1-R2's clauses, a `ℚ̄`-point `y` over a rational `j₀` with
object `P`, a rational fibre `PK/K` over `P`, and a Hom field `L ⊇ K` of `PK.A`. Construction
(N5 L632-645): A7 (`LeafQM.AV.conj_twist_of_rational`, compiled, for every such triple) gives
`^σP ≅ P` up to a twist `α_σ ∈ Aut 𝒪`; Skolem–Noether (T13, proved,
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`) writes `α_σ` as conjugation by `b_σ ∈ B^×`, and
`μ_σ = ι(b_σ)∘(iso)` is a `B`-linear isogeny, defined over the Hom field `L`; the discrepancy
`μ_σ ^σμ_τ μ_στ⁻¹` commutes with `ι(𝒪)`, hence is rational by `End_𝒪 = ℤ`; with T27 (Yu)
`End⁰ = B`, so `m_σ = μ_σ∘σ` commutes with `End_L(A_L)`. The quantifier over `(Y, Φ, π)` costs
nothing here: A7 holds for every triple with R1fp-R2fp, and the NoCM input is a hypothesis. -/
def ConjMapsNoCM : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjMaps L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) m

/-- **`ConjMapsOnHomField` from FS5 and the NoCM-given maps (proved).** -/
theorem conjMapsOnHomField_of (h5 : G0FibreSimple.FibreComTrivial) (h : ConjMapsNoCM) :
    ConjMapsOnHomField := by
  intro Y Φ π u P hctx K _ _ _ _ PK hPK L _ _ hKL hfix
  obtain ⟨hR1, hR2, hu, y, hy, hπ⟩ := hctx
  exact h Y Φ π hR1 hR2 (ZInQ.JHeight.Jmap u) y P hy hπ (h5 Y Φ π hR1 hR2 u hu y P hy hπ) K PK hPK
    L hKL hfix

/-- **Headline with the NoCM input explicit (proved).** `KernelFieldExists` from the leaves
`HomFreeFinite`, `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, the glue FS5
`FibreComTrivial` (g0-fibresimple; its truth for every triple is qm-pin's repair) and the glue
`ConjMapsNoCM`. -/
theorem kernelFieldExists_of_leaves_FS5 (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hMaps : ConjMapsNoCM) : KernelFieldExists :=
  kernelFieldExists_of_leaves hHFF hNOS hRay hTors (conjMapsOnHomField_of h5 hMaps)

end G0ModField.KernelField


/-! ## §6.7 Skolem–Noether on `𝒪` (proved): every twist `α ∈ Aut(𝒪)` is inner in `B`

A7 (`LeafQM.AV.conj_twist_of_rational`) gives `^σP ≅ P` only up to a twist of the QM action by a
ring automorphism `α_σ` of `𝒪`. The algebraic half of the Skolem–Noether descent (N5 L632-640):
`α` extends to a `ℚ`-automorphism of `B = (2,-3)_ℚ` (through the quaternion basis
`α(i), α(j)`), which is inner by Skolem–Noether (T13, proved in
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`). So `α(a) = u a u⁻¹` for some `u ∈ B^×`, and
`ι(Nu) ∘ (QM iso)` is a `B`-linear isogeny for any `N ≥ 1` with `Nu ∈ 𝒪`. -/

section AutO

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

theorem oj_mul_oi' : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- The quaternion basis `α(i), α(j), α(i)α(j)` of `B` given by a ring automorphism `α` of `𝒪`. -/
noncomputable def autBasis (α : O ≃+* O) : QuaternionAlgebra.Basis B (2 : ℚ) 0 (-3) where
  i := (α oi : B)
  j := (α oj : B)
  k := (α oi : B) * (α oj : B)
  i_mul_i := by
    rw [← Subring.coe_mul, ← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def,
      _root_.mul_one, map_ofNat]
    rfl
  j_mul_j := by
    rw [← Subring.coe_mul, ← map_mul, oj_mul_oj, map_neg, map_ofNat, Subring.coe_neg,
      Algebra.smul_def, _root_.mul_one, map_neg, map_ofNat]
    rfl
  i_mul_j := rfl
  j_mul_i := by
    rw [← Subring.coe_mul, ← map_mul, oj_mul_oi', map_neg, map_mul]
    simp

/-- **Skolem–Noether on `𝒪` (proved, from T13).** Every ring automorphism `α` of the maximal
order `𝒪 ⊂ B = (2,-3)_ℚ` is conjugation by a unit of `B`. -/
theorem aut_O_inner (α : O ≃+* O) : ∃ u : Bˣ, ∀ a : O, (α a : B) = u * a * (u⁻¹ : Bˣ) := by
  let φ : B →ₐ[ℚ] B := (autBasis α).liftHom
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := φ.toLinearMap)).mp hinj⟩
  obtain ⟨u, hu⟩ := TSkolemKW.leafSkolemNoether ℚ B (AlgEquiv.ofBijective φ hbij)
  refine ⟨u, fun a => ?_⟩
  rw [← hu]
  show (α a : B) = φ a
  let ψ1 : O →+* B := (Subring.subtype O).comp α.toRingHom
  let ψ2 : O →+* B := φ.toRingHom.comp (Subring.subtype O)
  have hi : ψ1 oi = ψ2 oi := by
    show (α oi : B) = (autBasis α).lift (oi : B)
    simp [QuaternionAlgebra.Basis.lift, oi, LeafQM.ofInt, autBasis]
  have hj : ψ1 oj = ψ2 oj := by
    show (α oj : B) = (autBasis α).lift (oj : B)
    simp [QuaternionAlgebra.Basis.lift, oj, LeafQM.ofInt, autBasis]
  obtain ⟨n, hn⟩ := a.2
  have h2 : (2 : O) * a = ((2 * n 0 + n 2 : ℤ) : O) + ((2 * n 1 + n 3 : ℤ) : O) * oi +
      ((n 2 : ℤ) : O) * oj + ((n 3 : ℤ) : O) * (oi * oj) := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
    rw [show ((2 : O) : B) = 2 from rfl, hn]
    ext <;> simp [oi, oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
  have key : ∀ ψ : O →+* B, ψ ((2 : O) * a) = ((2 * n 0 + n 2 : ℤ) : B) +
      ((2 * n 1 + n 3 : ℤ) : B) * ψ oi + ((n 2 : ℤ) : B) * ψ oj +
      ((n 3 : ℤ) : B) * (ψ oi * ψ oj) := by
    intro ψ
    rw [h2]; simp only [map_add, map_mul, map_intCast]
  have e : (2 : B) * ψ1 a = (2 : B) * ψ2 a := by
    have := key ψ1
    rw [map_mul, map_ofNat] at this
    rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
  have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
    rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e
  exact smul_right_injective B (two_ne_zero : (2 : ℚ) ≠ 0) e2

end G0ModField.KernelField

end AutO


/-! ## §6.8 Where NoCM enters (proved): integrality and commutation from `End(A_L) = ι(𝒪)`

`ConjMaps` splits into a geometric part with no NoCM content (`ConjIsogMaps`: the maps
`m_σ = μ_σ∘σ` are `𝒪`-linear, and the discrepancy is an endomorphism of `A_L` up to a nonzero
integer, which holds for any isogenies `μ_σ` by the quasi-inverse `ψ μ_στ = [e]`) and the NoCM
input `End_L(A_L) = ι(𝒪)` (FS5 + T27 + maximality of `𝒪`, on the Hom field). The passage is pure
algebra: an endomorphism commuting with `ι(𝒪)` is `ι(b)` with `b` central in `𝒪`, hence an
integer; faithfulness of `𝒪` on `A(ℚ̄)` follows from `|A[n]| = n⁴` and the anisotropy of the norm
form of `B` (`GlueDescent.aniso_rat`). -/

section NoCMAlg

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

/-- Every element of `B` has a nonzero integer multiple in `𝒪`. -/
theorem exists_nat_mul_mem_O (y : B) : ∃ N : ℕ, 0 < N ∧ (N : B) * y ∈ O := by
  set D : ℕ := y.re.den * y.imI.den * y.imJ.den * y.imK.den with hD
  have hD0 : 0 < D := by positivity
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * q.den := fun q =>
    (div_eq_iff (by positivity)).mp (Rat.num_div_den q)
  set a : ℤ := y.re.num * (y.imI.den * y.imJ.den * y.imK.den)
  set b : ℤ := y.imI.num * (y.re.den * y.imJ.den * y.imK.den)
  set c : ℤ := y.imJ.num * (y.re.den * y.imI.den * y.imK.den)
  set d : ℤ := y.imK.num * (y.re.den * y.imI.den * y.imJ.den)
  have ha : (a : ℚ) = D * y.re := by simp only [a, hD]; push_cast; rw [hnum]; ring
  have hb : (b : ℚ) = D * y.imI := by simp only [b, hD]; push_cast; rw [hnum]; ring
  have hc : (c : ℚ) = D * y.imJ := by simp only [c, hD]; push_cast; rw [hnum]; ring
  have hd : (d : ℚ) = D * y.imK := by simp only [d, hD]; push_cast; rw [hnum]; ring
  refine ⟨D, hD0, ![a - c, b - d, 2 * c, 2 * d], ?_⟩
  ext <;> simp [LeafQM.ofInt, QuaternionAlgebra.re_natCast, QuaternionAlgebra.imI_natCast,
    QuaternionAlgebra.imJ_natCast, QuaternionAlgebra.imK_natCast] <;> push_cast <;>
    linarith [ha, hb, hc, hd]

/-- A rational element of `𝒪` is an integer. -/
theorem int_of_rat_mem_O {r : ℚ} (h : algebraMap ℚ B r ∈ O) : ∃ k : ℤ, r = k := by
  obtain ⟨n, hn⟩ := h
  have e0 := congrArg QuaternionAlgebra.re hn
  have e1 := congrArg QuaternionAlgebra.imI hn
  have e2 := congrArg QuaternionAlgebra.imJ hn
  have e3 := congrArg QuaternionAlgebra.imK hn
  simp [LeafQM.ofInt, QuaternionAlgebra.algebraMap_eq] at e0 e1 e2 e3
  refine ⟨n 0, ?_⟩
  rw [e0]
  have h2 : (n 2 : ℚ) = 0 := by linarith
  simp [h2]

theorem coe_intCast_O (k : ℤ) : ((k : O) : B) = algebraMap ℚ B k := by
  rw [Subring.coe_intCast, map_intCast]

/-- **The centre of `𝒪` is `ℤ`.** -/
theorem center_O {b : O} (hb : ∀ a : O, b * a = a * b) : ∃ k : ℤ, b = k := by
  have hi : (b : B) * GlueDescent.qi = GlueDescent.qi * b := by
    have := congrArg Subtype.val (hb oi)
    rw [Subring.coe_mul, Subring.coe_mul] at this
    rwa [show ((oi : O) : B) = GlueDescent.qi by ext <;> simp [oi, LeafQM.ofInt, GlueDescent.qi]]
      at this
  have hj : (b : B) * GlueDescent.qj = GlueDescent.qj * b := by
    have := congrArg Subtype.val (hb oj)
    rw [Subring.coe_mul, Subring.coe_mul] at this
    rwa [show ((oj : O) : B) = GlueDescent.qj by ext <;> simp [oj, LeafQM.ofInt, GlueDescent.qj]]
      at this
  have hs := GlueDescent.B6_commute_i_j (b : B) hi hj
  obtain ⟨k, hk⟩ := int_of_rat_mem_O (hs ▸ b.2)
  refine ⟨k, Subtype.ext ?_⟩
  rw [coe_intCast_O, ← hk]
  exact hs

variable {V : Type*} [AddCommGroup V]

/-- **`𝒪` acts faithfully on a group with `|V[n]| = n⁴`.** -/
theorem faithful_O (hT : TorsCount V) (ρ : O →+* AddMonoid.End V) {c : O} (hc : ρ c = 0) :
    c = 0 := by
  by_contra hc0
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O (star (c : B))
  let c' : O := ⟨(N : B) * star (c : B), hmem⟩
  set nf : ℚ := (c : B).re ^ 2 - 2 * (c : B).imI ^ 2 + 3 * (c : B).imJ ^ 2 - 6 * (c : B).imK ^ 2
  have hprod : ((c' * c : O) : B) = algebraMap ℚ B (N * nf) := by
    rw [Subring.coe_mul]
    show (N : B) * star (c : B) * c = _
    rw [_root_.mul_assoc, GlueDescent.B6_star_mul, map_mul, map_natCast]
  obtain ⟨k, hk⟩ := int_of_rat_mem_O (hprod ▸ (c' * c).2)
  have hck : c' * c = (k : O) := Subtype.ext (by rw [hprod, coe_intCast_O, hk])
  have hρ : ρ (k : O) = 0 := by rw [← hck, map_mul, hc, mul_zero]
  rw [map_intCast] at hρ
  have hk0 : k = 0 := eq_zero_of_forall_zsmul hT (fun x => by
    have := DFunLike.congr_fun hρ x
    simpa using this)
  rw [hk0, Int.cast_zero] at hk
  have hnf : nf = 0 := by
    rcases mul_eq_zero.mp hk with h | h
    · exact absurd h (by exact_mod_cast hN.ne')
    · exact h
  obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ hnf
  exact hc0 (Subtype.ext (QuaternionAlgebra.ext h1 h2 h3 h4))

end G0ModField.KernelField

end NoCMAlg


section NoCMSplit

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

/-! Base change on endomorphisms, `End_K(A) → End_L(A_L)` (copied from
`scratch/bp-qmmoduli/QMAbVar.lean` §BaseChangeEnd, lines 528-556, with `AbVar` qualified). -/

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (first half of node N8): `End_K(A) → End_L(A_L)`,
`f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism (functoriality, and
`Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
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


/-- The geometric clauses of the conjugacy maps for a ring map `ι' : 𝒪 → End_L(A)` (the QM action
on `A`), with no NoCM content: `ConjMaps`' clauses 1, 2, 4, 6 verbatim; `m_σ` is `𝒪`-linear
(`μ_σ` is `B`-linear, A7 + Skolem–Noether `aut_O_inner`); and the discrepancy is an endomorphism up
to a nonzero integer, `e·m_σ m_τ = δ∘m_στ` with `δ ∈ End_L(A)` (`δ = μ_σ ^σμ_τ ψ` with `ψ` a
quasi-inverse, `ψ μ_στ = [e]`, Mumford §8; defined over `L` because `L` is a Hom field). -/
def ConjIsogMapsAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (m : GQ → (PtQ L A →+ PtQ L A)) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (a : O), (m σ).comp (endPt A Qbar (ι' a)) = (endPt A Qbar (ι' a)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, ∃ e : ℤ, e ≠ 0 ∧ ∃ δ : PkgI3.AbVar.End A,
      e • (m σ).comp (m τ) = (endPt A Qbar δ).comp (m (σ * τ))) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- **NoCM enters only through `End_L(A) = ι(𝒪)` (proved).** With `|A(ℚ̄)[n]| = n⁴`: the geometric
clauses and `End_L(A) = ι'(𝒪)` give `ConjMaps` (commutation with `End_L(A)`; the discrepancy
`δ = ι'(b)` commutes with `ι'(𝒪)` on points, so `b` is central by faithfulness, hence an
integer). -/
theorem conjMaps_of_qm (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (hEnd : ∀ f : PkgI3.AbVar.End A, ∃ a : O, f = ι' a)
    (h : ConjIsogMapsAt L A ι' m) : ConjMaps L A m := by
  obtain ⟨hgal, hinfl, hB, hfin, hdisc, halg⟩ := h
  let ρ : O →+* AddMonoid.End (PtQ L A) := (endPt A Qbar).comp ι'
  have hBx : ∀ σ a x, m σ (ρ a x) = ρ a (m σ x) := fun σ a x =>
    DFunLike.congr_fun (hB σ a) x
  refine ⟨hgal, hinfl, fun σ f => ?_, hfin, fun σ τ => ?_, halg⟩
  · obtain ⟨a, rfl⟩ := hEnd f
    exact hB σ a
  · obtain ⟨e, he, δ, hδ⟩ := hdisc σ τ
    obtain ⟨b, rfl⟩ := hEnd δ
    have hδx : ∀ x, e • m σ (m τ x) = ρ b (m (σ * τ) x) := fun x => by
      have := DFunLike.congr_fun hδ x
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] at this
      exact this
    have hcomm : ∀ a : O, b * a = a * b := by
      intro a
      have h2 : ρ (b * a) = ρ (a * b) := by
        refine AddMonoidHom.ext fun y => ?_
        obtain ⟨x, rfl⟩ := (hfin (σ * τ)).1 y
        rw [map_mul, map_mul]
        show ρ b (ρ a (m (σ * τ) x)) = ρ a (ρ b (m (σ * τ) x))
        rw [← hBx, ← hδx, ← hδx, hBx, hBx, map_zsmul]
      have : ρ (b * a - a * b) = 0 := by rw [map_sub, h2, sub_self]
      exact sub_eq_zero.mp (faithful_O hT ρ this)
    obtain ⟨k, rfl⟩ := center_O hcomm
    refine ⟨k, e, he, ?_⟩
    rw [hδ]
    refine AddMonoidHom.ext fun x => ?_
    have hk : ρ (k : O) = (k : AddMonoid.End (PtQ L A)) := map_intCast ρ k
    show ρ (k : O) (m (σ * τ) x) = _
    rw [hk, AddMonoid.End.intCast_apply, AddMonoidHom.smul_apply]

end G0ModField.KernelField

end NoCMSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField


/-! ### Sanity check (proved): the new clause lists are satisfiable

For an abelian variety over `ℚ` (`L = ⊥`) with any ring map `ι' : 𝒪 → End(A)`, the Galois action
`m_σ = σ` satisfies `ConjIsogMapsAt` (with `e = 1`, `δ = 1`, `F_σ = id`), hence `ConjMaps`. So
the definitions are not contradictory (as g0-mod-field's `descentDatum_bot` for `DescentDatum`). -/

theorem conjIsogMapsAt_bot (A : PkgI3.AbVar (⊥ : IF)) (ι' : LeafQM.O →+* PkgI3.AbVar.End A) :
    ConjIsogMapsAt ⊥ A ι' (fun σ => MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))) := by
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
  have hcomm : ∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ) := by
    intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  refine ⟨?_, ?_, fun σ a => hcomm σ (ι' a), ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
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
    refine ⟨1, one_ne_zero, 1, ?_⟩
    rw [one_smul, hmul, map_one]
    rfl
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **Remaining glue 3 (geometric: the conjugacy maps without NoCM).** For moduli data with
R1-R2's clauses, a `ℚ̄`-point over a rational `j₀` with object `P`, a rational fibre `PK/K` over
`P` and a Hom field `L ⊇ K` of `PK.A`: maps `m_σ = μ_σ∘σ` on `A_L(ℚ̄)` with `ConjIsogMapsAt` for
the base-changed QM action `ι_L = endBC ∘ PK.q.iota`. Inputs (N5 L632-645): A7
(`conj_twist_of_rational`, compiled, every triple), Skolem–Noether on `𝒪` (`aut_O_inner`,
proved), a quasi-inverse of an isogeny (Mumford §8, UNVERIFIED locator), Galois descent of
`G_L`-fixed morphisms to `L`, and the semilinear identification of `^σA` with `A` as schemes. -/
def ConjIsogMaps : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjIsogMapsAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) m

/-- **Remaining glue 4 (NoCM on the Hom field: `End_L(A_L) = ι_L(𝒪)`).** Given FS5's conclusion
`End_𝒪(P.A) = ℤ`: by Yu's dichotomy (T27, leaf) `End⁰(P.A) ≅ B`, so `End(P.A)` is an order of
`ι(B)` containing the maximal order `ι(𝒪)`, hence equal to it; `P ≅ (PK)_ℚ̄` as QM objects (R1's
naturality and `RationalFibre`), and `End_L(A_L) → End_ℚ̄` is injective (faithful base change). -/
def EndEqOOnHomField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
          ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- **`ConjMapsNoCM` from the geometric maps and `End_L(A_L) = ι(𝒪)` (proved; leaf
`TorsionStructure` for `|A(ℚ̄)[n]| = n⁴`).** -/
theorem conjMapsNoCM_of (hTors : PkgI2.TorsionStructure.{0}) (hG : ConjIsogMaps)
    (hE : EndEqOOnHomField) : ConjMapsNoCM := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hcom K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨m, hm⟩ := hG Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact ⟨m, conjMaps_of_qm L _ _ m
    (torsionCountPts_of_leaf hTors L _ (bc_dim hKL PK.A PK.surface))
    (hE Y Φ π hR1 hR2 j₀ y P hy hπ hcom K PK hPK L hKL hfix) hm⟩

/-- **Headline, split form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`,
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` and the glue `FibreComTrivial`
(FS5, g0-fibresimple), `ConjIsogMaps` (geometric) and `EndEqOOnHomField` (NoCM consequence). -/
theorem kernelFieldExists_of_split (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (hE : EndEqOOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_leaves_FS5 hHFF hNOS hRay hTors h5 (conjMapsNoCM_of hTors hG hE)

/-- **Remaining glue 4a (one QM surface over `ℚ̄`): `End_𝒪 = ℤ ⟹ End = ι(𝒪)`.** For an object `P`
(abelian surface over `ℚ̄` with QM by the maximal order `𝒪` of `(2,-3)_ℚ`) whose `𝒪`-centralizer
is `ℤ`, every endomorphism is `ι(a)`. *Argument* (model check): T27 (Yu 2013, leaf
`PkgI3.QMDichotomyYu`) gives `End⁰ ≅ B` or `M₂(ℚ(√d))`; FS4 (`CentralizerOfMatrixEnd0`, proved
from T6 by g0-fibresimple) excludes the second; `B → End⁰` (g0-fibresimple's `qm_embeds_end0`) is
injective (`B` simple) between 4-dimensional spaces, so `End⁰ = ι(B)`; `End` is an order (T6)
of `ι(B)` containing `ι(𝒪)`, which is maximal, so `End = ι(𝒪)`. No moduli data. -/
def EndEqOFibre : Prop :=
  ∀ P : QML3 Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a

/-- **Remaining glue 4b (transport to the Hom field).** If `End(P.A) = ι(𝒪)`, then
`End_L(A_L) = ι_L(𝒪)`: `P ≅ (PK)_ℚ̄` as QM objects (R1's naturality applied to
`RationalFibre`), and base change `End_L(A_L) → End_ℚ̄((A_L)_ℚ̄)` is injective and compatible
with `ι` (`endBC`, faithful base change: bp-qmmoduli's `endBC_injective`). -/
def EndTransport : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
          ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- `EndEqOOnHomField` from 4a and 4b (proved). -/
theorem endEqOOnHomField_of (ha : EndEqOFibre) (hb : EndTransport) : EndEqOOnHomField := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hcom K _ _ PK hPK L _ _ hKL hfix
  exact hb Y Φ π hR1 hR2 j₀ y P hy hπ (ha P hcom) K PK hPK L hKL hfix

/-- **Headline, finest form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`,
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` and the glue FS5
`FibreComTrivial`, `ConjIsogMaps`, `EndEqOFibre`, `EndTransport`. -/
theorem kernelFieldExists_of_split' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (ha : EndEqOFibre) (hb : EndTransport) : KernelFieldExists :=
  kernelFieldExists_of_split hHFF hNOS hRay hTors h5 hG (endEqOOnHomField_of ha hb)

end G0ModField.KernelField


/-! ## §6.9 `EndEqOFibre` from T27, T6 and the maximality of `𝒪`

Copied verbatim from `scratch/g0-fibresimple/olean/Tail.lean`: lines 38-117 (`B6_isUnit`,
`division_of_algEquiv`, `qmBasis`, `qm_embeds_end0`), 152-164 (FS4 `CentralizerOfMatrixEnd0`) and
208-282 (FS4 proved from T6, `centralizerOfMatrixEnd0_of_homFree`). -/

-- (g0-assemble2) section FS4Copy (verbatim copies of g0-fibresimple's §1, FS4) is not repeated: part 40 defines the same text.

section EndEqOSec

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Quaternion

namespace G0ModField.KernelField

/-- **Remaining glue 4a′ (pure algebra): `𝒪` is a maximal order of `B = (2,-3)_ℚ`.** A subring of
`B` containing `𝒪` whose elements are integral over `ℤ` is contained in `𝒪`. STANDARD (the
order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` has reduced discriminant `6 = disc B`; Vignéras,
*Arithmétique des algèbres de quaternions*, III §5, UNVERIFIED locator). A finite lattice
computation; not compiled here. -/
def OMaximal : Prop :=
  ∀ R : Subring LeafQM.B, LeafQM.O ≤ R → (∀ x ∈ R, IsIntegral ℤ x) → R ≤ LeafQM.O

/-- **`EndEqOFibre` from T27 (Yu), T6 (Mumford §19 Thm 3) and `OMaximal` (proved).** -/
theorem endEqOFibre_of (t27 : PkgI3.QMDichotomyYu) (hHF : PkgI3.HomFreeFinite)
    (hmax : OMaximal) : EndEqOFibre := by
  intro P hcom f
  have hY := PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface G0FibreSimple.B6_isUnit
    (G0FibreSimple.qm_embeds_end0 P.q)
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ :=
        G0FibreSimple.centralizerOfMatrixEnd0_of_homFree hHF Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := hcom φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  let φ : LeafQM.B →ₐ[ℚ] PkgI3.AbVar.End0 P.A := (G0FibreSimple.qmBasis P.q).liftHom
  haveI : Nontrivial (PkgI3.AbVar.End0 P.A) := e.toEquiv.nontrivial
  have hinj : Function.Injective φ := φ.toRingHom.injective
  haveI : FiniteDimensional ℚ (PkgI3.AbVar.End0 P.A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hrank : Module.finrank ℚ LeafQM.B = Module.finrank ℚ (PkgI3.AbVar.End0 P.A) :=
    e.toLinearEquiv.finrank_eq.symm
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).mp hinj
  let j : PkgI3.AbVar.End P.A →ₐ[ℤ] PkgI3.AbVar.End0 P.A := Algebra.TensorProduct.includeRight
  have hfree : Module.Free ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).1
  haveI : Module.Finite ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).2.1
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End P.A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End P.A) (S := ℚ))
  have hjinj : Function.Injective j := by
    intro x y hxy
    have hm : (1 : ℚ) ⊗ₜ[ℤ] (x - y) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s'))
  -- `φ` agrees with `j ∘ ι` on `𝒪`
  have hagree : ∀ a : LeafQM.O, φ (a : LeafQM.B) = j (P.q.iota a) := by
    let ψ1 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := φ.toRingHom.comp (Subring.subtype _)
    let ψ2 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := j.toRingHom.comp P.q.iota
    have hi : ψ1 G0FibreSimple.oi = ψ2 G0FibreSimple.oi := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oi : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oi, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    have hj : ψ1 G0FibreSimple.oj = ψ2 G0FibreSimple.oj := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oj : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oj, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    intro a
    obtain ⟨n, hn⟩ := a.2
    have h2 : (2 : LeafQM.O) * a = ((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
        ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * G0FibreSimple.oi +
        ((n 2 : ℤ) : LeafQM.O) * G0FibreSimple.oj +
        ((n 3 : ℤ) : LeafQM.O) * (G0FibreSimple.oi * G0FibreSimple.oj) := by
      apply Subtype.ext
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
      rw [show ((2 : LeafQM.O) : LeafQM.B) = 2 from rfl, hn]
      ext <;> simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat,
        QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;>
        ring
    have key : ∀ ψ : LeafQM.O →+* PkgI3.AbVar.End0 P.A, ψ ((2 : LeafQM.O) * a) =
        ((2 * n 0 + n 2 : ℤ) : PkgI3.AbVar.End0 P.A) +
        ((2 * n 1 + n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oi +
        ((n 2 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oj +
        ((n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * (ψ G0FibreSimple.oi * ψ G0FibreSimple.oj) := by
      intro ψ
      rw [h2]; simp only [map_add, map_mul, map_intCast]
    have e1 : (2 : PkgI3.AbVar.End0 P.A) * ψ1 a = (2 : PkgI3.AbVar.End0 P.A) * ψ2 a := by
      have := key ψ1
      rw [map_mul, map_ofNat] at this
      rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
    have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
      rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e1
    exact smul_right_injective (PkgI3.AbVar.End0 P.A) (two_ne_zero : (2 : ℚ) ≠ 0) e2
  -- the order `R = φ⁻¹(End)`
  let R : Subring LeafQM.B := (j.toRingHom.range).comap φ.toRingHom
  have hOR : LeafQM.O ≤ R := fun x hx => ⟨P.q.iota ⟨x, hx⟩, (hagree ⟨x, hx⟩).symm⟩
  have hint : ∀ x ∈ R, IsIntegral ℤ x := by
    rintro x ⟨g, hg⟩
    have h1 : IsIntegral ℤ g := Algebra.IsIntegral.isIntegral g
    have h2 : IsIntegral ℤ (φ x) := by
      have := h1.map j
      rwa [show j g = φ x from hg] at this
    exact (isIntegral_algHom_iff (φ.restrictScalars ℤ) hinj).mp h2
  obtain ⟨x, hx⟩ := hsurj (j f)
  have hxO : x ∈ LeafQM.O := hmax R hOR hint ⟨f, hx.symm⟩
  refine ⟨⟨x, hxO⟩, hjinj ?_⟩
  rw [← hagree, ← hx]

/-- **Headline, with the NoCM side down to leaves + FS5 + `OMaximal` (proved).** Leaves:
`HomFreeFinite` (T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`,
`QMDichotomyYu` (T27). Glue: FS5 `FibreComTrivial`, `OMaximal` (pure algebra),
`EndTransport`, `ConjIsogMaps`. -/
theorem kernelFieldExists_of_split'' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hmax : OMaximal) (hb : EndTransport)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_split' hHFF hNOS hRay hTors h5 hG (endEqOFibre_of t27 hHFF hmax) hb

end G0ModField.KernelField

end EndEqOSec


end G0A2_a75_kernelfield

section G0A2_a80_fqm
/-! ## g0-assemble2: fibre-qm-period (scratch/fibre-qm-period/part_fqm.lean, verbatim; its FQMBase.lean is part 80
(g0-thetapoint) over Leaves.lean, whose `R1fpProps` is qm-pin's full repair and which contains part_pin.lean's
eight declarations) -/

/-! ## §F. fibre-qm-period: `ThetaPt.FibreQMPeriod` for the leaf's own triple, from named Props

Task fibre-qm-period, 2026-11-13. `ThetaPt.FibreQMPeriod` (g0-thetapoint, above, unchanged; in
this file `R1fpProps` is qm-pin's fully repaired clause list) is proved here in two steps.

1. **qm-pin's reduction to the leaf's own triple** (`fibreQMPeriod_of_own`). `FibreQMPeriodAt Y Φ π`
   is the body of `FibreQMPeriod` for one triple (`fibreQMPeriod_iff`, `Iff.rfl`).
   `FibreQMPeriodOwn h` is `FibreQMPeriodAt` for the triple `ownY h, ownΦ h, ownπ h` that
   `Classical.choice` extracts from the leaf bundle `R1R2fp` (through `R1R2fp_Y`). Given qm-pin's
   `Pin.MobiusGlue` (proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and the textbook leaf
   T5), `FibreQMPeriodOwn h` implies `FibreQMPeriod` (`Pin.pointwise_of_witness_mor`).
2. **The own-triple statement from named Props** (`fibreQMPeriodAt_of`): for any triple satisfying
   `R1fpProps` (only its naturality clause is used), from
   * `PkgI1.QMHauptmodul` (existing composite leaf, pkg-I1),
   * `QMComplexUnif` (LEAF candidate: R1(b)(a), Shimura 1967: every QM surface over `ℂ` is
     `ℂ²/ι(𝒪)(τ, 1)ᵀ` compatibly with `ι`, for some `τ ∈ ℍ`, by an analytic uniformization),
   * `QMPeriodValue Y Φ π` (GLUE: the Hauptmodul comparison; the value of `π` at a point is the value
     of `QMHauptmodul`'s `f` at the period `τ` of the point),
   * `QMDenZeroCM3` (LEAF candidate: `Σθ_m⁸ ∘ Ω` vanishes on `ℍ` only at fixed points of `ι(x)`,
     `x² − x + 1 = 0`; Lin–Yang's divisor of `ψ₄` on the QM curve),
   * `UnifTransport` (GLUE: an analytic uniformization of the base change `Q/ℂ` of the fibre object
     gives one of `A(ℂ)_σ` with the same kernel; base change of complex points and rigidity). -/


/-! ## §N. fibre-qm-period: normalization of QM lattices (proved; used for `QMLatticeAlgebra`)

`qmOrbit w = ι(𝒪)w` (the `ℤ`-span of `ι(b_k)w` over N5's basis); `qmLattice τ = qmOrbit (τ, 1)`;
scaling; the unit `1 + i` (reduced norm `−1`) keeps the orbit (`qmOrbit_unit`, coefficients from
`py/unit_coeffs.py`); hence `normalize`: if `w` is not a complex multiple of a real vector, then
`ι(𝒪)w = c·Λ_τ` with `c ≠ 0` and `τ ∈ ℍ`. -/

section FibreQMNormSec

set_option linter.unusedSimpArgs false

open BPAnalytic.QM Matrix

noncomputable section

namespace FibreQMNorm


def qmMatB (x : B) : Matrix (Fin 2) (Fin 2) ℂ := (iota x).map (fun r : ℝ => (r : ℂ))

def qmOrbit (w : Fin 2 → ℂ) : Submodule ℤ (Fin 2 → ℂ) :=
  Submodule.span ℤ (Set.range fun k : Fin 4 => (qmMatB (oBasis k)).mulVec w)

theorem qmLattice_eq_orbit {τ : ℂ} (hτ : τ.im ≠ 0) : qmLattice hτ = qmOrbit ![τ, 1] := by
  rw [qmLattice_eq]; rfl

/-- The four generators, explicitly. -/
theorem gen_eq (a b : ℂ) : (fun k : Fin 4 => (qmMatB (oBasis k)).mulVec ![a, b]) =
    ![![a, b], ![√2 * a, -(√2 * b)], ![(a - 3 * b) / 2, (a + b) / 2],
      ![√2 * (a - 3 * b) / 2, -(√2 * (a + b)) / 2]] := by
  funext k; ext i
  fin_cases k <;> fin_cases i <;>
    simp [qmMatB, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

def smulMap (c : ℂ) : (Fin 2 → ℂ) →ₗ[ℤ] (Fin 2 → ℂ) :=
  ((c • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).restrictScalars ℤ

theorem qmOrbit_smul (c : ℂ) (v : Fin 2 → ℂ) : qmOrbit (c • v) = (qmOrbit v).map (smulMap c) := by
  unfold qmOrbit
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k
  simp [smulMap, Matrix.mulVec_smul]

theorem sqrt2_sq' : (√2 : ℂ) * √2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

/-- The unit `1 + i` (reduced norm `−1`) does not change the orbit. -/
theorem qmOrbit_unit (τ : ℂ) : qmOrbit ![τ, 1] = qmOrbit ![(1 + √2) * τ, 1 - √2] := by
  have s := sqrt2_sq'
  apply le_antisymm
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]
    set S := Submodule.span ℤ (Set.range ![![((1 + √2) * τ), (1 - √2)], ![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))], ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2], ![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2]]) with hS
    have m : ∀ j : Fin 4, (![![((1 + √2) * τ), (1 - √2)], ![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))], ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2], ![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2]] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    fin_cases k
    · have e : (![τ, 1] : Fin 2 → ℂ) = -(![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) + (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.neg_mem (m 0)) (m 1))
    · have e : (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) = ((![((1 + √2) * τ), (1 - √2)] + ![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) : Fin 2 → ℂ) - (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.add_mem (m 0) (m 0)) (m 1))
    · have e : (![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) = (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) - (![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) - (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ + 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.sub_mem (m 1) (m 2)) (m 3))
    · have e : (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) = ((![((1 + √2) * τ), (1 - √2)] + ![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) : Fin 2 → ℂ) - ((![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] + ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) : Fin 2 → ℂ) - (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination ((τ + 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.sub_mem (S.add_mem (m 0) (m 0)) (S.add_mem (m 2) (m 2))) (m 3))
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]
    set S := Submodule.span ℤ (Set.range ![![τ, 1], ![√2 * τ, -(√2 * 1)], ![(τ - 3 * 1) / 2, (τ + 1) / 2], ![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]]) with hS
    have m : ∀ j : Fin 4, (![![τ, 1], ![√2 * τ, -(√2 * 1)], ![(τ - 3 * 1) / 2, (τ + 1) / 2], ![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    fin_cases k
    · have e : (![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) = (![τ, 1] : Fin 2 → ℂ) + (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (m 0) (m 1))
    · have e : (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) = ((![τ, 1] + ![τ, 1] : Fin 2 → ℂ) : Fin 2 → ℂ) + (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.add_mem (m 0) (m 0)) (m 1))
    · have e : (![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) = (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) + (![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) - (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.add_mem (m 1) (m 2)) (m 3))
    · have e : (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) = ((![τ, 1] + ![τ, 1] : Fin 2 → ℂ) : Fin 2 → ℂ) - ((![(τ - 3 * 1) / 2, (τ + 1) / 2] + ![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) : Fin 2 → ℂ) + (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination ((τ + 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.sub_mem (S.add_mem (m 0) (m 0)) (S.add_mem (m 2) (m 2))) (m 3))


theorem smulMap_comp (a b : ℂ) : smulMap a ∘ₗ smulMap b = smulMap (a * b) := by
  ext v i; simp [smulMap, mul_smul]

theorem one_sub_sqrt2_ne : (1 - (√2 : ℂ)) ≠ 0 := by
  have h : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [show (1 - (√2 : ℂ)) = ((1 - √2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

/-- **Normalization (proved):** if `w` is not a complex multiple of a real vector, `ι(𝒪)w` is a
nonzero multiple of `Λ_τ` for some `τ ∈ ℍ` (using the unit `1 + i` of reduced norm `−1` when
`Im(w₀/w₁) < 0`). -/
theorem normalize (w : Fin 2 → ℂ) (hw : ¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) :
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (c : ℂ), c ≠ 0 ∧ qmOrbit w = (qmLattice hτ.ne').map (smulMap c) := by
  have hw2 : w 1 ≠ 0 := by
    intro h0; apply hw; refine ⟨w 0, ![1, 0], ?_⟩; ext i; fin_cases i <;> simp [h0]
  set t := w 0 / w 1 with ht_def
  have hwt : w = w 1 • ![t, 1] := by
    ext i; fin_cases i
    · simp [t]; field_simp
    · simp
  have ht : t.im ≠ 0 := by
    intro h0; apply hw; refine ⟨w 1, ![t.re, 1], ?_⟩
    rw [hwt]; ext i; fin_cases i
    · simp; left; exact Complex.ext (by simp) (by simp [h0])
    · simp
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · set k : ℝ := (1 + √2) / (1 - √2) with hk
    have hk0 : k < 0 := by
      have h1 : (1 : ℝ) < √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      exact div_neg_of_pos_of_neg (by positivity) (by linarith)
    set τ' : ℂ := (k : ℂ) * t with hτ'_def
    have hτ' : 0 < τ'.im := by
      rw [hτ'_def, Complex.im_ofReal_mul]; exact mul_pos_of_neg_of_neg hk0 hneg
    refine ⟨τ', hτ', w 1 * (1 - √2), mul_ne_zero hw2 one_sub_sqrt2_ne, ?_⟩
    have hv : (![(1 + √2) * t, 1 - √2] : Fin 2 → ℂ) = (1 - √2 : ℂ) • ![τ', 1] := by
      have hs := one_sub_sqrt2_ne
      ext i; fin_cases i
      · simp only [hτ'_def, hk, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply,
          smul_eq_mul]
        push_cast
        field_simp
      · simp
    rw [hwt, qmOrbit_smul, qmOrbit_unit, hv, qmOrbit_smul, ← qmLattice_eq_orbit hτ'.ne',
      ← Submodule.map_comp, smulMap_comp]
    simp
  · refine ⟨t, hpos, w 1, hw2, ?_⟩
    rw [hwt, qmOrbit_smul, ← qmLattice_eq_orbit hpos.ne']
    simp

end FibreQMNorm

end

end FibreQMNormSec

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

-- (g0-assemble2) as in part 80: leaf-adopt3 replaced g0-split's copies by leaf-push2's originals
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex

/-! ### Step 1: the statement for one triple, and qm-pin's reduction -/

/-- The conclusion of `FibreQMPeriod` for the model `A` over `K` of the fibre over `J(u)`
(verbatim). -/
def QMConcl (u : ℚ) (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
    (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu ∧
  ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
    Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **`FibreQMPeriod` for one triple `(Y, Φ, π)`** (the body of `ThetaPt.FibreQMPeriod`, unchanged:
`fibreQMPeriod_iff`). -/
def FibreQMPeriodAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) :
    Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      QMConcl u K A

/-- The restatement is the statement (checked by `Iff.rfl`). -/
theorem fibreQMPeriod_iff : ThetaPt.FibreQMPeriod ↔
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → FibreQMPeriodAt Y Φ π :=
  Iff.rfl

/-- The leaf's own `Y₃`: the triple that `Classical.choice` extracts from the bundle `R1R2fp`
(through `R1R2fp_Y`). -/
def ownY (h : R1R2fp) : Over (Spec (CommRingCat.of ℚ)) := (R1R2fp_Y h).choose

/-- The leaf's own moduli bijections. -/
def ownΦ (h : R1R2fp) : PtEquiv (ownY h) := (R1R2fp_Y h).choose_spec.choose

/-- The leaf's own `π : Y₃ → P¹`. -/
def ownπ (h : R1R2fp) : ToP1 (ownY h).left := (R1R2fp_Y h).choose_spec.choose_spec.choose

theorem own_spec (h : R1R2fp) : R1fpProps (ownY h) (ownΦ h) ∧ R1heckeProps (ownY h) (ownΦ h) ∧
    R2fpProps (ownY h) (ownΦ h) (ownπ h) :=
  (R1R2fp_Y h).choose_spec.choose_spec.choose_spec

/-- **`FibreQMPeriod` restated for the leaf's own triple** (qm-pin's option 3 form; with
`Pin.MobiusGlue` it is equivalent to `FibreQMPeriod`: `fibreQMPeriod_of_own` and
`own_of_fibreQMPeriod`). -/
def FibreQMPeriodOwn (h : R1R2fp) : Prop := FibreQMPeriodAt (ownY h) (ownΦ h) (ownπ h)

/-- **qm-pin's reduction (proved).** The own-triple statement implies `FibreQMPeriod` for every
triple satisfying the repaired clause list, given `Pin.MobiusGlue` (mobius-glue proves it from
`CurveRatFactor`, `CurveSurj` and T5) and the CM objects of the bundle. -/
theorem fibreQMPeriod_of_own (h : R1R2fp) (hM : Pin.MobiusGlue) (hOwn : FibreQMPeriodOwn h) :
    ThetaPt.FibreQMPeriod := by
  obtain ⟨h1, -, h2⟩ := own_spec h
  intro Y Φ π h1' h2' u hu K A hFib
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := hFib
  exact Pin.pointwise_of_witness_mor hM (Pin.cm_objects_of_R1R2fp h) h1 h2
    (fun t P => ∀ u : ℚ, u ∉ contactSet → t = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) (emb : K.K →+* Qbar),
        (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
        QMConcl u K A)
    (fun t y P hP ht u hu hJ K A emb hiso => hOwn u hu K A ⟨emb, y, P, hP, ht.trans hJ, hiso⟩)
    Y Φ π h1' h2' _ y P hP rfl u hu hy K A emb hiso

/-- The converse (trivial): `FibreQMPeriod` implies the own-triple statement. -/
theorem own_of_fibreQMPeriod (h : R1R2fp) (hQM : ThetaPt.FibreQMPeriod) : FibreQMPeriodOwn h :=
  hQM _ _ _ (own_spec h).1 (own_spec h).2.2

/-! ### Step 2: the named Props -/

/-- The clauses of `PkgI1.QMHauptmodul` for one function `f` (verbatim; `PkgI1.QMHauptmodul` is
`∃ f, QMHauptmodulFn f`, `qmHauptmodul_iff`). -/
def QMHauptmodulFn (f : UpperHalfPlane → OnePoint ℂ) : Prop :=
  Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
    Function.Surjective f ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem qmHauptmodul_iff : PkgI1.QMHauptmodul ↔ ∃ f, QMHauptmodulFn f := Iff.rfl

/-- `𝒪` acting on `ℂ²` through N5's real embedding: `z ↦ ι(a) z` (`ι(a) ∈ M₂(ℝ) ⊆ M₂(ℂ)`); it
preserves `Λ_τ = ι(𝒪)(τ, 1)ᵀ`. (`LeafQM.O` is `ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩ ⊆ B = (2, −3)`, the
order of pkg-I1 and bp-analytic, with the same basis.) -/
def qmMat (a : LeafQM.O) : Matrix (Fin 2) (Fin 2) ℂ :=
  (BPAnalytic.QM.iota (a : LeafQM.B)).map (fun r : ℝ => (r : ℂ))

/-- An analytic uniformization `Φ : ℂ² → Q.A(ℂ)` of a QM surface over `ℂ` is **`ι`-compatible**
if `Φ(ι(a) z) = ι_Q(a)(Φ z)` for all `a ∈ 𝒪`. -/
def IotaCompatible (Q : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)) : Prop :=
  ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), Φu ((qmMat a).mulVec z) = Φu z ≫ (Q.q.iota a).hom

/-- **LEAF candidate (R1(b)(a), the complex uniformization of QM surfaces).** Every abelian surface
`Q/ℂ` with QM by `𝒪` (and level-3 structure) has an analytic uniformization
`Φ : ℂ² → Q.A(ℂ)` (`IsUniformization`) whose kernel is exactly the QM lattice
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` for some `τ ∈ ℍ`, compatibly with `ι`.

Sources: Shimura, *Construction of class fields and zeta functions of algebraic curves*,
Ann. of Math. 85 (1967), Main Theorem I and §2 (the QM abelian varieties are the tori
`ℂ²/ι(𝒪)(τ,1)ᵀ`); also Birkenhake–Lange, *Complex abelian varieties*, §9.4, and the analytic
uniformization of `Q.A(ℂ)` with GAGA (the kernel's `UniformizationLeafAll`) (all locators
UNVERIFIED). Why it is a consequence: `H₁(Q.A, ℤ)` is a left `𝒪`-module, locally free of rank one
since `𝒪` is maximal, hence free because indefinite `B` has class number one (Eichler); the analytic
representation of `B ⊗ ℝ = M₂(ℝ)` on `ℂ²` is the standard one up to `GL₂(ℂ)`; so the kernel is
`ι(𝒪)w`, `w = c(τ, 1)ᵀ`, `τ ∉ ℝ`, and if `Im τ < 0` the unit `1 + i ∈ 𝒪` (reduced norm `−1`)
moves it to `ℍ`. Not one printed theorem with this exact normalization: a leaf candidate. -/
def QMComplexUnif : Prop :=
  ∀ Q : QML3 ℂ, ∃ (τ : ℂ) (hτ : 0 < τ.im) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice hτ.ne') Φu ∧ IotaCompatible Q Φu

/-- **GLUE (F1, the Hauptmodul comparison, for one triple).** Let `f` satisfy the clauses of
`PkgI1.QMHauptmodul`. For every `ℚ̄`-point `y` of `Y` with object `P`, every embedding
`ι : ℚ̄ → ℂ`, every base change `Q/ℂ` of `P` along `ι`, and every `ι`-compatible uniformization of
`Q.A` with kernel `Λ_τ` (`τ ∈ ℍ`): `f(τ) = ι(π(y))` in `P¹(ℂ)`.

Why true for the genuine triple (model argument, no human review): by R1(b)(b)-(c) (Shimura 1967;
Deligne 1971 §4.15) there is an analytic family `τ ↦ P_τ` over `ℍ` with `P_τ(ℂ) ≅ ℂ²/Λ_τ`
compatibly with `ι`, and `h(τ) = π(P_τ)` is holomorphic `ℍ → P¹(ℂ)`. Two `ι`-compatible tori
`ℂ²/Λ_τ`, `ℂ²/Λ_τ'` give `Aut(𝒪)`-twist-equivalent QM pairs iff `τ' ∈ Γ*τ` (Shimura; `Γ*` is the
positive-norm normalizer, and twists by `Aut 𝒪 = N_B(𝒪)/ℚ^×` are the Atkin–Lehner moves). With
R2fp's fibre clause (GAGA turns the analytic isomorphisms into algebraic ones), `h` is
`Γ*`-invariant with fibres exactly the `Γ*`-orbits. So `h` and `f` both induce bijections
`Γ*\ℍ ≅ P¹(ℂ)` that are holomorphic on the compact Riemann surface `X₆/W`; `h ∘ f⁻¹` is a
biholomorphism of `P¹`, a Möbius map, and it fixes `0, ∞, −16/27` (R2fp's CM clauses at the CM
points, which are the fixed points of `ι(x)`, `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`, `x² = −6`;
`QMHauptmodul`'s CM clauses), so `h = f`. Finally `Q ≅ P_τ` up to level structure (both are
`ι`-compatibly `ℂ²/Λ_τ`), so `ι(π(y)) = π(Q) = h(τ) = f(τ)` (naturality of `π`,
`ToP1.val_comp`). For other triples it follows from the genuine one by qm-pin's comparison. Inputs
that are not in Mathlib: analytification of `Y₃`, the analytic family (R1(b)(b)-(c)), GAGA, the
compact Riemann surface `X₆/W`. Size: large. -/
def QMPeriodValue (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) :
    Prop :=
  ∀ f : UpperHalfPlane → OnePoint ℂ, QMHauptmodulFn f →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (τ : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
      IotaCompatible Q Φu →
      f τ = (π.val (K := Qbar) y.left).map ιe

/-- **LEAF candidate (zeros of `ψ₄` on the QM curve).** `Σ_{m even} θ_m(Ω(τ))⁸ = 4ψ₄(Ω(τ))`
vanishes at `τ ∈ ℍ` only at the CM points of discriminant `−3`, the fixed points of `ι(x)` for
`x ∈ 𝒪` with `x² − x + 1 = 0`.

Source: Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020)
(arXiv:1807.00466v1, Example 29 with eqs. (13)-(14)): on the Shimura curve `X = X₆/W ≅ P¹` the
pull-back of `ψ₄` has its zeros only at the elliptic point `P₋₃` (so `j = χ₁₀²/ψ₄⁵`-type functions
have their only pole there), with Igusa's theta expression of `ψ₄` (R4) (locators UNVERIFIED; the
exact divisor statement was not read). Consistent with `QMHauptmodul` (`j_θ` has its only pole at
`P₋₃`) unless `ψ₄` and `χ₁₀` had a common zero on `Ω(ℍ)`. Numerically: `jDen(Ω(i√3)) = 0` with a
zero of order 30 in `τ` (pkg-I1's pole of order 6 of `j_θ`). SPECULATIVE as a reading of the
source. -/
def QMDenZeroCM3 : Prop :=
  ∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) = 0 →
    ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ g • τ = τ

/-- **GLUE (base change of complex points).** Let `A` be an abelian variety over a number field
`K`, `emb : K → ℚ̄` with `A_ℚ̄ ≅ P.A` as `ℚ̄`-schemes (`FibreOver`'s isomorphism), `ι : ℚ̄ → ℂ`, and
`Q/ℂ` a base change of `P` along `ι`. Every analytic uniformization of `Q.A(ℂ)` with kernel `Λ`
gives one of `A(ℂ)_σ`, `σ = ι ∘ emb`, with the same kernel `Λ`.

Why true: `A(ℂ)_σ = Hom_K(Spec ℂ, A) = Hom_ℂ(Spec ℂ, A ×_K ℂ)` and `A ×_K ℂ ≅ P.A ×_ℚ̄ ℂ ≅ Q.A` as
`ℂ`-schemes (pullback pasting; `IsBaseChangeOf`'s square). The resulting bijection
`ψ : Q.A(ℂ) → A(ℂ)_σ` comes from an isomorphism of `ℂ`-varieties, so by rigidity (Mumford,
*Abelian Varieties*, §4 Cor. 1) `x ↦ ψ(x)·ψ(1)⁻¹` is a group isomorphism; regular functions on
opens of `A` pull back to regular functions on opens of `Q.A` (translations are morphisms), so
`z ↦ ψ(Φ z)·ψ(1)⁻¹` satisfies every clause of `IsUniformization`, with kernel `Λ`. Size: medium
(scheme bookkeeping: pullbacks of points, `cEvalAt` along morphisms, rigidity, which is not in
Mathlib). -/
def UnifTransport : Prop :=
  ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) (emb : K.K →+* Qbar) (P : QML3 Qbar),
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) Λ Φu →
      ∃ Φa : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) (ιe.comp emb),
        IsUniformization (ιe.comp emb) Λ Φa

/-! ### Step 2b: `QMPeriodValue` from a moduli part and a complex-analysis part -/

/-- `h : ℍ → P¹(ℂ)` is holomorphic at `τ` (as a map to the Riemann sphere): near `τ` it is an
analytic function `g`, or `1/g` with `g` analytic and `g(τ) = 0` (a pole). -/
def IsHolP1At (h : UpperHalfPlane → OnePoint ℂ) (τ : UpperHalfPlane) : Prop :=
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in nhds (τ : ℂ), ∀ hz : 0 < z.im, h ⟨z, hz⟩ = (g z : OnePoint ℂ)) ∨
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
      ∀ᶠ z in nhds (τ : ℂ), ∀ hz : 0 < z.im,
        h ⟨z, hz⟩ = if g z = 0 then OnePoint.infty else (((g z)⁻¹ : ℂ) : OnePoint ℂ))

/-- The fibre and CM clauses of a normalized Hauptmodul of `Γ*`: fibres exactly the `Γ*`-orbits,
values `0, ∞, −16/27` at the fixed points of `ι(x)` for `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`,
`x² = −6` (as in `PkgI1.QMHauptmodul`). -/
def GammaStarFibresCM (h : UpperHalfPlane → OnePoint ℂ) : Prop :=
  (∀ τ τ' : UpperHalfPlane, h τ = h τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = ((-16/27 : ℂ) : OnePoint ℂ))

/-- The clauses shared by `QMHauptmodul`'s `f` and the period map `h`: continuous, holomorphic into
`P¹(ℂ)`, and `GammaStarFibresCM`. -/
def IsGammaStarHauptmodul (h : UpperHalfPlane → OnePoint ℂ) : Prop :=
  Continuous h ∧ (∀ τ, IsHolP1At h τ) ∧ GammaStarFibresCM h

/-- **GLUE (moduli side of F1: the period map of `Y`, for one triple).** There is a function
`h : ℍ → P¹(ℂ)` with the clauses `IsGammaStarHauptmodul` such that for every `ℚ̄`-point `y` with
object `P`, every `ι : ℚ̄ → ℂ`, every base change `Q/ℂ` of `P` along `ι` and every `ι`-compatible
uniformization of `Q.A` with kernel `Λ_τ`: `h(τ) = ι(π(y))`.

Why true for the genuine triple (model argument): `h(τ) = π(P_τ)` for R1(b)'s analytic family
`τ ↦ P_τ` (Shimura 1967 Main Thm I; Deligne 1971 §4.15; locators UNVERIFIED), holomorphic by
R1(b)(c). The value clause: `Q ≅ P_τ` compatibly with `ι` up to level structure (both are
`ι`-compatibly `ℂ²/Λ_τ`; GAGA), so they have the same `π` (R2fp's fibre clause; naturality of `π`,
`ToP1.val_comp`). Fibres: `ℂ²/Λ_τ ≅ ℂ²/Λ_τ'` up to an `Aut 𝒪`-twist iff `τ' ∈ Γ*τ` (Shimura;
`Aut 𝒪 = N_B(𝒪)/ℚ^×`, and `1 + i` of reduced norm `−1` is absorbed by `ι`-compatibility), with
R2fp's fibre clause. CM values: the fixed point `τ` of `ι(x)`, `x² = −1`, gives `ℂ²/Λ_τ` the
`𝒪`-linear automorphism `z ↦ λz`, `λ² = −1` (`ι(x)v_τ = λv_τ`), so `HasCM4`, and R2fp gives `0`;
likewise for `−3`, `−24`. Composite of R1(b), R2 and GAGA; not in Mathlib (analytification of `Y₃`
and of the universal family, rv-blueprints Q3). Size: large. -/
def QMPeriodMap (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∃ h : UpperHalfPlane → OnePoint ℂ, IsGammaStarHauptmodul h ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (τ : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
      IotaCompatible Q Φu →
      h τ = (π.val (K := Qbar) y.left).map ιe

/-- The clauses of R1(b)(b)-(c) for a map `τ ↦ y_τ` from `ℍ` to the complex points of `Y`: the
object at `y_τ` is `ι`-compatibly `ℂ²/Λ_τ` (an `ι`-compatible uniformization with kernel exactly
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`), and `τ ↦ π(y_τ) ∈ P¹(ℂ)` is continuous and holomorphic. -/
def IsR1bFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu) ∧
  Continuous (fun τ => π.val (K := ℂ) (yτ τ).left) ∧
  ∀ τ, IsHolP1At (fun τ => π.val (K := ℂ) (yτ τ).left) τ

/-- **LEAF (R1(b), complex uniformization, family form; a concrete replacement for the placeholder
`HSyn.R01b_ComplexUniformization` at the triple `(Y, Φ, π)`).** There is a map `τ ↦ y_τ` from `ℍ`
to `Y(ℂ)` such that the object at `y_τ` is `ℂ²/ι(𝒪)(τ, 1)ᵀ` with its `ι` (`IsR1bFamily`), and
`τ ↦ π(y_τ)` is holomorphic into `P¹(ℂ)`.

Source: Shimura, Ann. of Math. 85 (1967), Main Theorem I (the canonical model `V` of `Γ\ℍ` with a
holomorphic `φ : ℍ → V(ℂ)` whose value at `τ` is the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ`); Deligne,
Sém. Bourbaki 389 (1971), §4.15 (analytic families) (locators UNVERIFIED). Here
`y_τ = φ(τ)` on the component of `Y₃(ℂ)` given by the level structure `η_τ(a) = ι(a)v_τ/3`, and
`π ∘ φ` is holomorphic because `π` is a morphism. For the genuine `Y₃` this is the published
statement composed with `π`; for another triple satisfying the repaired `R1fpProps` it follows by
qm-pin's comparison (`g : Y' → Y` with `Φ' = Φ ∘ g` is bijective on points, hence an isomorphism,
qm-pin §3.3; and `π' = π ∘ g` on `ℚ̄`-points forces equality as morphisms), so its truth does not
depend on which triple `Classical.choice` picks. Rests on bp-qmmoduli §2.2 as `R1R2fpRep`. -/
def R1bFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), IsR1bFamily Y Φ π yτ

/-- **GLUE (the period map is a normalized Hauptmodul and computes `π`).** For a family as in
`R1bFamily`, `h(τ) = π(y_τ)` has the fibre and CM clauses `GammaStarFibresCM`, and for every
`ℚ̄`-point `y` with object `P`, every `ι : ℚ̄ → ℂ`, every base change `Q/ℂ` of `P` and every
`ι`-compatible uniformization of `Q.A` with kernel `Λ_τ`: `h(τ) = ι(π(y))`.

Why true (model argument): (value) `Q` and `P_τ` are both `ι`-compatibly `ℂ²/Λ_τ`, so `Q ≅ P_τ` as
QM pairs (GAGA: the analytic isomorphism is algebraic), and they differ at most in the level
structure, a twist that `π` does not see (R2fp's fibre clause, extended from `ℚ̄`-points to
`ℂ`-points because the fibre relation of `π` is algebraic); with `ToP1.val_comp`,
`ι(π(y)) = π(y_ℂ) = π(y_τ)`. (fibres) `P_τ`, `P_τ'` are `Aut 𝒪`-twist-equivalent iff `τ' ∈ Γ*τ`
(an `ι`-twisted-compatible linear isomorphism `ℂ²/Λ_τ → ℂ²/Λ_τ'` is `ι(u)` up to scalar,
`u ∈ N_B(𝒪)` of positive norm; Shimura). (CM) at the fixed point of `ι(x)`, `ι(x)v_τ = λv_τ` and
`z ↦ λz` is an `𝒪`-linear automorphism of `ℂ²/Λ_τ` with `λ² = −1` (resp. `λ² − λ + 1 = 0`,
`λ² = −6`), so the pair has `HasCM4` (resp. `HasCM3`, `HasCM24`) and R2fp gives the value. Inputs
not in Mathlib: GAGA, the extension of R2fp to `ℂ`-points, Shimura's description of isomorphisms
of QM tori. Size: large. -/
def PeriodMapGlue (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), IsR1bFamily Y Φ π yτ →
    GammaStarFibresCM (fun τ => π.val (K := ℂ) (yτ τ).left) ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∀ (τ : UpperHalfPlane) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
      IotaCompatible Q Φu →
      π.val (K := ℂ) (yτ τ).left = (π.val (K := Qbar) y.left).map ιe

/-- **`QMPeriodMap` from R1(b) in family form and the period-map glue (proved).** -/
theorem qmPeriodMap_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (hR : R1bFamily Y Φ π) (hG : PeriodMapGlue Y Φ π) : QMPeriodMap Y Φ π := by
  obtain ⟨yτ, hfam⟩ := hR
  obtain ⟨hFC, hval⟩ := hG yτ hfam
  exact ⟨fun τ => π.val (K := ℂ) (yτ τ).left, ⟨hfam.2.1, hfam.2.2, hFC⟩, hval⟩

/-- **GLUE (complex analysis: uniqueness of the normalized Hauptmodul of `Γ*`).** A function
`h : ℍ → P¹(ℂ)` with the clauses `IsGammaStarHauptmodul` equals `QMHauptmodul`'s `f`.

Proof sketch (model argument; every step is textbook complex analysis): `Γ*\ℍ` is compact (`B` is
a division algebra; Shimura, *Introduction to the arithmetic theory of automorphic functions*,
Prop. 9.2, UNVERIFIED number). `f` and `h` induce continuous injections `Γ*\ℍ → P¹`; `f`'s is
onto (`QMHauptmodul`), hence a homeomorphism, and `h`'s is open (open mapping theorem) with closed
image, hence onto. So `φ = h ∘ f⁻¹` is a homeomorphism of `P¹`. Away from the finitely many images
of elliptic points and of the zeros of `jDen ∘ Ω`, `f = jNum/jDen ∘ Ω` is holomorphic (theta
series are holomorphic on `𝔥₂`, `Ω` is holomorphic on `ℍ`) and locally injective, so `φ` is
holomorphic there; the finitely many remaining points are removable singularities (`φ` is
continuous). So `φ` is a biholomorphism of `P¹`, a Möbius map, fixing `0, ∞, −16/27` (both satisfy
the CM clauses, and the fixed points exist: `(i+j)² = −1`, `((1+j)/2)² − (1+j)/2 + 1 = 0`,
`(2j+ij)² = −6`), so `φ = id` and `h = f`. Statable over Mathlib as it stands; size: medium-large
(compactness of `Γ*\ℍ`, removable singularities on `P¹`, Möbius rigidity). -/
def HauptmodulUnique : Prop :=
  ∀ f h : UpperHalfPlane → OnePoint ℂ, QMHauptmodulFn f → IsGammaStarHauptmodul h → h = f

/-- **`QMPeriodValue` from the moduli part and the complex-analysis part (proved).** -/
theorem qmPeriodValue_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (hPM : QMPeriodMap Y Φ π) (hHU : HauptmodulUnique) : QMPeriodValue Y Φ π := by
  intro f hf y P hP ιe Q hQ τ Φu hΦu hc
  obtain ⟨h, hh, hval⟩ := hPM
  rw [← hHU f h hf hh]
  exact hval y P hP ιe Q hQ τ Φu hΦu hc

/-! ### Step 2d: `QMComplexUnif` from a textbook leaf, uniformization glue and lattice algebra -/

/-- **TEXTBOOK leaf (analytic uniformization over `ℂ`).** An abelian surface `A/ℂ` has an analytic
uniformization `Φ : ℂ² → A(ℂ)` (`IsUniformization` at `σ = id`). Mumford, *Abelian Varieties*, §1,
with Serre's GAGA (locators UNVERIFIED). In the build: bp-analytic's `UniformizationLeafAll` gives
one for some `g` (`ZInQ.LeafPush2.exists_isUniformization_of_leaf`); `g = dim A = 2` is the
missing identification. -/
def UniformizationExistsC : Prop :=
  ∀ A : PkgI3.AbVar ℂ, A.dim = (2 : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) Λ Φu

/-- **GLUE (structure of a uniformization).** For an analytic uniformization `Φ : ℂ² → A(ℂ)` with
kernel `Λ`: `Λ` is a full lattice (discrete, `ℝ`-span `ℂ²`), and endomorphisms lift to `ℂ²`: a ring
homomorphism `ρ : End(A) → End_ℂ(ℂ²)` (the analytic representation) with `Φ(ρ(e) z) = e(Φ z)`;
`ρ(e)` preserves `Λ`. bp-analytic proves the lifting for its form of uniformization
(`ZInQKernel/HDecomp/Analytic/Uniformization.lean`: `IsUniformization.exists_complexLinear_endo`,
`analyticRep_spec`, `analyticRep_mul`, `analyticRep_id`); the lattice clauses come with its leaf
`UniformizationLeafAll`. Missing: the translation from this file's `IsUniformization` back to
bp-analytic's (the converse of `ZInQ.LeafPush2.isUniformization_of_bp`). Size: small-medium. -/
def UnifStructure : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
    (Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)), IsUniformization (RingHom.id ℂ) Λ Φu →
    ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧
      ∃ ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ),
        (∀ e z, Φu (ρ e z) = Φu z ≫ e.hom) ∧ (∀ e, ∀ z ∈ Λ, ρ e z ∈ Λ)

/-- **GLUE (lattice algebra; one textbook input, class number one).** Let `Λ ⊆ ℂ²` be a full
lattice stable under a ring homomorphism `ρ : 𝒪 → End_ℂ(ℂ²)`. Then some `ℂ`-linear automorphism
`F` of `ℂ²` intertwines `ρ` with N5's `ι` (`F ρ(a) = ι(a) F`) and carries `Λ` onto
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` for some `τ ∈ ℍ`.

Proof sketch (model argument): `ρ` extends to `B ⊗ ℂ ≅ M₂(ℂ) → M₂(ℂ)` (via `ι ⊗ ℂ`), an
automorphism, inner by Skolem–Noether, so `ρ = g ι g⁻¹`. `g⁻¹Λ` is a left `𝒪`-lattice of rank 4 in
`B ⊗ ℝ`-terms, i.e. a locally free left `𝒪`-ideal; `𝒪` (maximal, in the indefinite algebra of
discriminant 6) has class number one (Eichler's theorem; Vignéras, *Arithmétique des algèbres de
quaternions*, Cor. III.5.7, or Voight, *Quaternion algebras*, Cor. 28.5.17; numbers UNVERIFIED), so
`g⁻¹Λ = ι(𝒪)w`. `w` is not a complex multiple of a real vector (else `ι(𝒪)w` spans a real plane),
so `w = c(τ, 1)ᵀ` with `τ ∉ ℝ`; scaling by `c⁻¹` commutes with `ι`; if `Im τ < 0`, the unit
`u = 1 + i` (reduced norm `−1`) gives `ι(𝒪)v_τ = ι(𝒪)ι(u)v_τ` and `ι(u)v_τ ∝ (τ', 1)ᵀ`,
`τ' = −(1+√2)²τ ∈ ℍ`. Statable and provable over Mathlib (Skolem–Noether is in the kernel,
`TSkolemKW`; class number one can be proved by a Euclidean argument as mobius-glue did for the
normalizer). Size: medium. -/
def QMLatticeAlgebra : Prop :=
  ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ], IsZLattice ℝ Λ →
    ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ), (∀ a, ∀ z ∈ Λ, ρ a z ∈ Λ) →
      ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
        Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
        ∀ a z, F (ρ a z) = (qmMat a).mulVec (F z)

/-- **Uniformizations transport along linear automorphisms (proved).** -/
theorem isUniformization_comp {K : Type} [Field K] {A : PkgI3.AbVar K} {σ : K →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φu : (Fin g → ℂ) → CPts A σ}
    (h : IsUniformization σ Λ Φu) (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) :
    IsUniformization σ (Λ.map (F.toLinearMap.restrictScalars ℤ)) (fun z => Φu (F.symm z)) := by
  obtain ⟨hadd, hker, hsurj, hopen, hhol⟩ := h
  let G : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap F.symm.toLinearMap
  have hG : ∀ z, G z = F.symm z := fun z => rfl
  refine ⟨fun z w => ?_, fun z => ?_, fun P => ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [map_add, hadd]
  · change Φu (F.symm z) = 1 ↔ _
    rw [hker, Submodule.mem_map]
    constructor
    · intro hz
      exact ⟨F.symm z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  · obtain ⟨z, rfl⟩ := hsurj P
    exact ⟨F z, by simp⟩
  · have : cDom (fun z => Φu (F.symm z)) U = G ⁻¹' cDom Φu U := rfl
    rw [this]
    exact (hopen U).preimage G.continuous
  · have hmaps : Set.MapsTo G (cDom (fun z => Φu (F.symm z)) U) (cDom Φu U) := fun z hz => hz
    exact (hhol U s).comp G.differentiableOn hmaps

/-- **`QMComplexUnif` from the textbook uniformization leaf and two glue Props (proved).** -/
theorem qmComplexUnif_of (hE : UniformizationExistsC) (hS : UnifStructure)
    (hL : QMLatticeAlgebra) : QMComplexUnif := by
  intro Q
  obtain ⟨Λ, Φu, hΦ⟩ := hE Q.A Q.surface
  obtain ⟨hd, hlat, ρ, hρ, hpres⟩ := hS Q.A Λ Φu hΦ
  obtain ⟨τ, hτ, F, hF, hFρ⟩ :=
    hL Λ hlat (ρ.comp Q.q.iota) (fun a z hz => hpres (Q.q.iota a) z hz)
  refine ⟨τ, hτ, fun z => Φu (F.symm z), ?_, fun a z => ?_⟩
  · rw [← hF]
    exact isUniformization_comp hΦ F
  · have e1 : F.symm ((qmMat a).mulVec z) = ρ (Q.q.iota a) (F.symm z) := by
      rw [LinearEquiv.symm_apply_eq]
      have := hFρ a (F.symm z)
      simp only [RingHom.comp_apply, LinearEquiv.apply_symm_apply] at this
      exact this.symm
    change Φu (F.symm ((qmMat a).mulVec z)) = Φu (F.symm z) ≫ (Q.q.iota a).hom
    rw [e1, hρ]

/-! ### Step 2e: `QMComplexUnif` from the decomposition's textbook leaves T35, T11a and lattice algebra

`UniformizationExistsT35` and `T11aRiemannEnd` are the kernel's textbook leaves
`ZInQ.LeafPush2.UniformizationExists` (T35) and `ZInQ.LeafPush2.T11a_RiemannEnd` (T11a)
(`ZInQKernel/HDecomp/LeafPush2/T.lean`), copied verbatim over this file's copies of `CPts` and
`IsUniformization` (the same text as the kernel's); both are in leaf-adopt3's `TextbookLeaves`.
With them, `UniformizationExistsC` and `UnifStructure` are proved (`unifStructure_of`,
`uniformizationExistsC_of`), and only `QMLatticeAlgebra` remains. -/

/-- (copied from `ZInQKernel/HDecomp/LeafPush2/T.lean`, `UniformizationExists`, T35) **AN3 for
abelian varieties (textbook leaf; the analytic half of T11/T12).** Every abelian variety over a
field `K` and every `σ : K → ℂ`: `A(ℂ)_σ` has an analytic uniformization by `ℂ^g`, `g = dim A`, with
kernel a full lattice (Mumford, *Abelian varieties*, §1, with GAGA, Serre 1956, for the complex Lie
group structure; UNVERIFIED numbers). -/
def UniformizationExistsT35 : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A σ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization σ Λ Φ

/-- (copied from `ZInQKernel/HDecomp/LeafPush2/T.lean`, `T11a_RiemannEnd`) **T11(a), Riemann/GAGA
for endomorphisms (textbook leaf).** For an abelian variety over `ℂ` with a uniformization `Φ`
(kernel `Λ`) at `σ = id`, the endomorphisms of `A` are exactly the `ℂ`-linear maps of `ℂ^g`
preserving `Λ`: each such `M` is induced by a unique endomorphism `f` (`Φ(Mz) = f ∘ Φ(z)`), and each
`f` is induced by some `M`. (Mumford §1 and §2, Birkenhake–Lange Prop. 1.2.1 for complex tori;
GAGA, Serre 1956, for "holomorphic ⇒ algebraic"; UNVERIFIED numbers.) -/
def T11aRiemannEnd : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) Λ Φ →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ) →
      ∃! f : PkgI3.AbVar.End A, ∀ z, Φ (M z) = Φ z ≫ f.hom) ∧
    (∀ f : PkgI3.AbVar.End A, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, Φ (M z) = Φ z ≫ f.hom)

/-- `UniformizationExistsC` from T35 (proved). -/
theorem uniformizationExistsC_of (h : UniformizationExistsT35) : UniformizationExistsC := by
  intro A hA
  obtain ⟨Λ, Φu, -, -, hU⟩ := h ℂ A (RingHom.id ℂ) 2 hA
  exact ⟨Λ, Φu, hU⟩

/-- **Lifts are unique (proved):** two `ℂ`-linear maps with the same image under a uniformization
with discrete kernel are equal (their difference maps `ℂ^g` into the discrete `Λ`; `ℝ` is
connected). -/
theorem lift_unique {K : Type} [Field K] {A : PkgI3.AbVar K} {σ : K →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] {Φu : (Fin g → ℂ) → CPts A σ}
    (h : IsUniformization σ Λ Φu) {M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hMM : ∀ z, Φu (M z) = Φu (M' z)) : M = M' := by
  obtain ⟨hadd, hker, -, -, -⟩ := h
  have hmem : ∀ z, (M - M') z ∈ Λ := by
    intro z
    rw [← hker, LinearMap.sub_apply]
    have e := hadd (M z - M' z) (M' z)
    rw [sub_add_cancel, hMM] at e
    exact mul_right_cancel (e.symm.trans (one_mul (Φu (M' z))).symm)
  refine LinearMap.ext fun z => ?_
  let N := M - M'
  have hc : Continuous (fun t : ℝ => N ((t : ℂ) • z)) :=
    (LinearMap.continuous_of_finiteDimensional N).comp
      (Complex.continuous_ofReal.smul continuous_const)
  let f : ℝ → Λ := fun t => ⟨N ((t : ℂ) • z), hmem _⟩
  have hf : Continuous f := hc.subtype_mk _
  have h01 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  have h2 : N (((0 : ℝ) : ℂ) • z) = N (((1 : ℝ) : ℂ) • z) := congrArg Subtype.val h01
  simp only [Complex.ofReal_zero, zero_smul, map_zero, Complex.ofReal_one, one_smul] at h2
  have h3 : M z - M' z = 0 := by
    rw [h2]; rfl
  exact sub_eq_zero.mp h3

/-- **The analytic representation as a ring homomorphism, from T11a (proved).** For a
uniformization with discrete kernel (as T35 provides), T11a's lifts `M_e` of the endomorphisms are
unique (`lift_unique`), hence form a ring homomorphism `ρ`, and they preserve `Λ`. This is
`UnifStructure`'s conclusion for T35's uniformizations (for an arbitrary uniformization the lattice
clauses would follow by comparison with T35's, bp-analytic's `exists_complexLinear`, not reproved
here; the reduction below only needs T35's). -/
theorem unif_ring_hom (hR : T11aRiemannEnd) (A : PkgI3.AbVar ℂ) (hA : A.dim = (2 : WithBot ℕ∞))
    (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ]
    (Φu : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)) (hU : IsUniformization (RingHom.id ℂ) Λ Φu) :
    ∃ ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ),
      (∀ e z, Φu (ρ e z) = Φu z ≫ e.hom) ∧ (∀ e, ∀ z ∈ Λ, ρ e z ∈ Λ) := by
  have hT := (hR A 2 Λ Φu hA hU).2
  choose ρf hρf using hT
  have hadd := hU.1
  have hker := hU.2.1
  let ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ) :=
    { toFun := ρf
      map_one' := lift_unique hU fun z => by
        rw [hρf]; exact Category.comp_id _
      map_mul' := fun e f => lift_unique hU fun z => by
        rw [hρf, Module.End.mul_apply, hρf, hρf]
        exact (Category.assoc _ _ _).symm
      map_zero' := lift_unique hU fun z => by
        rw [hρf, LinearMap.zero_apply, (hker 0).2 (zero_mem _)]
        exact MonObj.comp_one _
      map_add' := fun e f => lift_unique hU fun z => by
        rw [hρf, LinearMap.add_apply, hadd, hρf, hρf]
        exact MonObj.comp_mul _ _ _ }
  refine ⟨ρ, hρf, fun e z hz => ?_⟩
  rw [← hker] at hz ⊢
  change Φu (ρf e z) = 1
  rw [hρf, hz]
  exact MonObj.one_comp _

/-- **`QMComplexUnif` from the textbook leaves T35, T11a and `QMLatticeAlgebra` (proved).** -/
theorem qmComplexUnif_of_textbook (hE : UniformizationExistsT35) (hR : T11aRiemannEnd)
    (hL : QMLatticeAlgebra) : QMComplexUnif := by
  intro Q
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ Q.A (RingHom.id ℂ) 2 Q.surface
  obtain ⟨ρ, hρ, hpres⟩ := unif_ring_hom hR Q.A Q.surface Λ Φu hΦ
  obtain ⟨τ, hτ, F, hF, hFρ⟩ :=
    hL Λ hlat (ρ.comp Q.q.iota) (fun a z hz => hpres (Q.q.iota a) z hz)
  refine ⟨τ, hτ, fun z => Φu (F.symm z), ?_, fun a z => ?_⟩
  · rw [← hF]
    exact isUniformization_comp hΦ F
  · have e1 : F.symm ((qmMat a).mulVec z) = ρ (Q.q.iota a) (F.symm z) := by
      rw [LinearEquiv.symm_apply_eq]
      have := hFρ a (F.symm z)
      simp only [RingHom.comp_apply, LinearEquiv.apply_symm_apply] at this
      exact this.symm
    change Φu (F.symm ((qmMat a).mulVec z)) = Φu (F.symm z) ≫ (Q.q.iota a).hom
    rw [e1, hρ]

/-! ### Step 2f: `QMLatticeAlgebra` from its algebraic core (`normalize`, proved) -/

/-- **GLUE (lattice algebra core: Skolem–Noether over `ℂ` and class number one).** A full lattice
`Λ ⊆ ℂ²` stable under a ring homomorphism `ρ : 𝒪 → End_ℂ(ℂ²)` is carried by a `ℂ`-linear
automorphism `G` intertwining `ρ` with N5's `ι` onto `ι(𝒪)w` (`FibreQMNorm.qmOrbit w`) for a vector
`w` that is not a complex multiple of a real vector.

Proof sketch: `ρ ⊗ ℂ : B ⊗ ℂ ≅ M₂(ℂ) → M₂(ℂ)` is inner (Skolem–Noether; in the kernel as
`TSkolemKW`), giving `G` with `Gρ(a)G⁻¹ = ι(a)`; `GΛ` is a left `𝒪`-lattice of rank 4, hence
`ι(𝒪)w` because the maximal order of the indefinite algebra of discriminant 6 has class number one
(Eichler; Vignéras Cor. III.5.7, Voight Cor. 28.5.17; numbers UNVERIFIED); and `w` is not a
complex multiple `c·r` of a real vector `r`, since then `ι(𝒪)w ⊆ c·ℝ²` would not span `ℂ²` over
`ℝ`. Size: medium (class number one is the substantial part). -/
def QMLatticeFree : Prop :=
  ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ], IsZLattice ℝ Λ →
    ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ), (∀ a, ∀ z ∈ Λ, ρ a z ∈ Λ) →
      ∃ (G : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)) (w : Fin 2 → ℂ),
        (¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) ∧
        Λ.map (G.toLinearMap.restrictScalars ℤ) = FibreQMNorm.qmOrbit w ∧
        ∀ a z, G (ρ a z) = (qmMat a).mulVec (G z)

/-- **`QMLatticeAlgebra` from `QMLatticeFree` (proved)**, by `FibreQMNorm.normalize` and rescaling
(scalars commute with `ι`). -/
theorem qmLatticeAlgebra_of_free (h : QMLatticeFree) : QMLatticeAlgebra := by
  intro Λ _ hlat ρ hρ
  obtain ⟨G, w, hw, hG, hGρ⟩ := h Λ hlat ρ hρ
  obtain ⟨τ, hτ, c, hc, hcw⟩ := FibreQMNorm.normalize w hw
  refine ⟨τ, hτ, G.trans (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) c⁻¹ (inv_ne_zero hc)), ?_, ?_⟩
  · have e1 : ((G.trans (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) c⁻¹ (inv_ne_zero hc))).toLinearMap.restrictScalars ℤ) =
        FibreQMNorm.smulMap c⁻¹ ∘ₗ (G.toLinearMap.restrictScalars ℤ) := by
      ext v i; simp [FibreQMNorm.smulMap]
    rw [e1, Submodule.map_comp, hG, hcw, ← Submodule.map_comp, FibreQMNorm.smulMap_comp,
      inv_mul_cancel₀ hc]
    have e2 : FibreQMNorm.smulMap 1 = LinearMap.id := by
      ext v i; simp [FibreQMNorm.smulMap]
    rw [e2, Submodule.map_id]
  · intro a z
    simp [hGρ, Matrix.mulVec_smul]

/-! ### Step 2g: `QMLatticeFree` from Skolem–Noether over `ℂ` and class number one -/

/-- **Skolem–Noether over `ℂ`, for N5's order (now proved: `qmSkolemNoetherC_proof`).** Every unital ring homomorphism
`ρ : 𝒪 → End_ℂ(ℂ²)` is conjugate to N5's `ι` by a `ℂ`-linear automorphism `G`
(`G ρ(a) = ι(a) G`). Why: `ρ` extends to a `ℂ`-algebra map `B ⊗_ℚ ℂ → M₂(ℂ)`; `B ⊗ ℂ ≅ M₂(ℂ)`
(through `ι`) is simple, so the map is an isomorphism, and automorphisms of `M₂(ℂ)` are inner
(Skolem–Noether; e.g. Voight, *Quaternion algebras*, Cor. 7.7.4, UNVERIFIED number; the kernel's
`TSkolemKW.leafSkolemNoether` is a form of it). -/
def QMSkolemNoetherC : Prop :=
  ∀ ρ : LeafQM.O →+* Module.End ℂ (Fin 2 → ℂ),
    ∃ G : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ a z, G (ρ a z) = (qmMat a).mulVec (G z)

/-- **TEXTBOOK (class number one of `𝒪`, lattice form).** Every full lattice `Λ ⊆ ℂ²` stable under
N5's `ι(𝒪)` is `ι(𝒪)w` for a vector `w` that is not a complex multiple of a real vector. Why: `Λ`
is a left `𝒪`-module, torsion-free of rank 4, so `ℚΛ ≅ B` and `Λ` is a left `𝒪`-ideal, principal
because the maximal order of the indefinite algebra of discriminant 6 has class number one
(Eichler's theorem; Vignéras, *Arithmétique des algèbres de quaternions*, Cor. III.5.7; Voight,
Cor. 28.5.17; numbers UNVERIFIED); `w` is not `c·r` with `r` real, else `ι(𝒪)w ⊆ c·ℝ²` would not
span `ℂ²` over `ℝ`. -/
def QMClassNumberOne : Prop :=
  ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ], IsZLattice ℝ Λ →
    (∀ a : LeafQM.O, ∀ z ∈ Λ, (qmMat a).mulVec z ∈ Λ) →
    ∃ w : Fin 2 → ℂ, (¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) ∧
      Λ = FibreQMNorm.qmOrbit w

/-- `i ∈ 𝒪`. -/
def oI : LeafQM.O := ⟨⟨0, 1, 0, 0⟩, show LeafQM.InO _ from ⟨![0, 1, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩
/-- `j ∈ 𝒪`. -/
def oJ : LeafQM.O := ⟨⟨0, 0, 1, 0⟩, show LeafQM.InO _ from ⟨![-1, 0, 2, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩

theorem oI_sq : oI * oI = 1 + 1 := by
  apply Subtype.ext; ext <;> simp [oI] <;> norm_num

theorem oJ_sq : oJ * oJ = -(1 + 1 + 1) := by
  apply Subtype.ext; ext <;> simp [oJ] <;> norm_num

theorem oI_oJ : oI * oJ = -(oJ * oI) := by
  apply Subtype.ext; ext <;> simp [oI, oJ]

/-- `2a = 2n₀ + 2n₁ i + n₂(1 + j) + n₃(i + ij)` for `a = ofInt n`. -/
theorem two_mul_eq (a : LeafQM.O) : ∃ n : Fin 4 → ℤ, a + a =
    ((n 0 + n 0 : ℤ) : LeafQM.O) + ((n 1 + n 1 : ℤ) : LeafQM.O) * oI + ((n 2 : ℤ) : LeafQM.O) * (1 + oJ)
      + ((n 3 : ℤ) : LeafQM.O) * (oI + oI * oJ) ∧ (a : LeafQM.B) = LeafQM.ofInt n := by
  obtain ⟨n, hn⟩ := a.2
  refine ⟨n, ?_, hn⟩
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast, Subring.coe_one]
  rw [hn]
  ext <;> simp [LeafQM.ofInt, oI, oJ] <;> ring

/-- N5's `ι(i)` over `ℂ`. -/
def Mi' : Matrix (Fin 2) (Fin 2) ℂ := !![(√2 : ℂ), 0; 0, -(√2 : ℂ)]
/-- N5's `ι(j)` over `ℂ`. -/
def Mj' : Matrix (Fin 2) (Fin 2) ℂ := !![0, -3; 1, 0]

theorem two_qmMat (a : LeafQM.O) (n : Fin 4 → ℤ) (hn : (a : LeafQM.B) = LeafQM.ofInt n) :
    qmMat a + qmMat a = ((n 0 + n 0 : ℤ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ((n 1 + n 1 : ℤ) : ℂ) • Mi' + ((n 2 : ℤ) : ℂ) • (1 + Mj') + ((n 3 : ℤ) : ℂ) • (Mi' + Mi' * Mj') := by
  unfold qmMat
  rw [hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, LeafQM.ofInt, Mi', Mj',
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem s2sq : (√2 : ℂ) * (√2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

theorem s2ne : (√2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)

/-- **`QMSkolemNoetherC`, proved.** With `R = ρ(i)`, `S = ρ(j)` (`R² = 2`, `S² = −3`, `RS = −SR`):
an eigenvector `e₁` of `R` for `√2` exists (else `R = −√2`, forcing `S = 0`), `e₂ = S e₁` is one for
`−√2`, and in the basis `(e₁, e₂)` the maps `R`, `S` are N5's `ι(i) = diag(√2, −√2)`,
`ι(j) = [[0, −3], [1, 0]]`; every `a ∈ 𝒪` is `(2n₀ + 2n₁ i + n₂(1+j) + n₃(i+ij))/2`. -/
theorem qmSkolemNoetherC_proof : QMSkolemNoetherC := by
  intro ρ
  set R := ρ oI with hRdef
  set S := ρ oJ with hSdef
  have hRR : ∀ v, R (R v) = v + v := fun v => by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (show R * R = 1 + 1 by
      rw [hRdef, ← map_mul, oI_sq, map_add, map_one])
    simpa using this
  have hSS : ∀ v, S (S v) = -(v + v + v) := fun v => by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (show S * S = -(1 + 1 + 1) by
      rw [hSdef, ← map_mul, oJ_sq, map_neg, map_add, map_add, map_one])
    simpa using this
  have hRS : ∀ v, R (S v) = -(S (R v)) := fun v => by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) (show R * S = -(S * R) by
      rw [hRdef, hSdef, ← map_mul, ← map_mul, oI_oJ, map_neg])
    simpa using this
  set s2 : ℂ := (√2 : ℂ) with hs2
  have hs2sq : s2 * s2 = 2 := s2sq
  have hs2ne : s2 ≠ 0 := s2ne
  -- an eigenvector of `R` for `√2`
  obtain ⟨e1, he1, hRe1⟩ : ∃ e1 : Fin 2 → ℂ, e1 ≠ 0 ∧ R e1 = s2 • e1 := by
    by_cases h0 : ∀ v, R v + s2 • v = 0
    · exfalso
      set e : Fin 2 → ℂ := Pi.single 0 1
      have he : e ≠ 0 := by
        intro h; have := congrFun h 0; simp [e] at this
      have hR : ∀ v, R v = -(s2 • v) := fun v => eq_neg_of_add_eq_zero_left (h0 v)
      have h1 : S e = 0 := by
        have := hRS e
        rw [hR, hR, map_neg, map_smul, neg_neg] at this
        have h2 : (s2 + s2) • S e = 0 := by
          rw [add_smul]; linear_combination (norm := module) -this
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exfalso; apply hs2ne; linear_combination h3 / 2
        · exact h3
      have := hSS e
      rw [h1, map_zero] at this
      apply he
      have h4 : (3 : ℂ) • e = 0 := by linear_combination (norm := module) this
      rcases smul_eq_zero.mp h4 with h5 | h5
      · norm_num at h5
      · exact h5
    · push Not at h0
      obtain ⟨v, hv⟩ := h0
      refine ⟨R v + s2 • v, hv, ?_⟩
      rw [map_add, map_smul, hRR]
      linear_combination (norm := module) (-(hs2sq)) • v
  set e2 := S e1 with he2def
  have hRe2 : R e2 = -(s2 • e2) := by
    rw [he2def, hRS, hRe1, map_smul]
  have hSe2 : S e2 = -(e1 + e1 + e1) := hSS e1
  have he2 : e2 ≠ 0 := by
    intro h
    have := hSe2
    rw [h, map_zero] at this
    apply he1
    have h4 : (3 : ℂ) • e1 = 0 := by linear_combination (norm := module) this
    rcases smul_eq_zero.mp h4 with h5 | h5
    · norm_num at h5
    · exact h5
  have hli : LinearIndependent ℂ ![e1, e2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hR' : s • (s2 • e1) + t • (-(s2 • e2)) = 0 := by
      have := congrArg R hst
      rw [map_add, map_smul, map_smul, hRe1, hRe2, map_zero] at this
      exact this
    have hs : (s * s2 * 2) • e1 = 0 := by
      linear_combination (norm := module) s2 • hst + hR'
    have ht : (t * s2 * 2) • e2 = 0 := by
      linear_combination (norm := module) s2 • hst - hR'
    have hs' : s = 0 := by
      rcases smul_eq_zero.mp hs with h | h
      · simpa [hs2ne] using h
      · exact absurd h he1
    have ht' : t = 0 := by
      rcases smul_eq_zero.mp ht with h | h
      · simpa [hs2ne] using h
      · exact absurd h he2
    exact ⟨hs', ht'⟩
  let b : Module.Basis (Fin 2) ℂ (Fin 2 → ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb0 : b 0 = e1 := by simp [b]
  have hb1 : b 1 = e2 := by simp [b]
  refine ⟨b.equivFun, ?_⟩
  have hG0 : b.equivFun e1 = Pi.single 0 1 := by
    rw [← hb0]; ext j; simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have hG1 : b.equivFun e2 = Pi.single 1 1 := by
    rw [← hb1]; ext j; simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have hGR : ∀ x, b.equivFun (R x) = Mi'.mulVec (b.equivFun x) := by
    have : (b.equivFun.toLinearMap ∘ₗ R) = (Matrix.mulVecLin Mi') ∘ₗ b.equivFun.toLinearMap := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.zero_eta,
          Fin.isValue, hb0, hRe1, map_smul, hG0, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mi', Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs2]
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.mk_one,
          Fin.isValue, hb1, hRe2, map_neg, map_smul, hG1, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mi', Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs2]
    intro x
    exact congrArg (fun T => T x) this
  have hGS : ∀ x, b.equivFun (S x) = Mj'.mulVec (b.equivFun x) := by
    have : (b.equivFun.toLinearMap ∘ₗ S) = (Matrix.mulVecLin Mj') ∘ₗ b.equivFun.toLinearMap := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.zero_eta,
          Fin.isValue, hb0, ← he2def, hG1, hG0, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mj', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Fin.mk_one,
          Fin.isValue, hb1, hSe2, map_neg, map_add, hG0, hG1, Matrix.mulVecLin_apply]
        ext j; fin_cases j <;> simp [Mj', Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
    intro x
    exact congrArg (fun T => T x) this
  intro a z
  obtain ⟨n, h2a, hn⟩ := two_mul_eq a
  have hρ2 : ρ a z + ρ a z = ((n 0 + n 0 : ℤ) : ℂ) • z + ((n 1 + n 1 : ℤ) : ℂ) • R z +
      ((n 2 : ℤ) : ℂ) • (z + S z) + ((n 3 : ℤ) : ℂ) • (R z + R (S z)) := by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T z) (congrArg ρ h2a)
    simp only [map_add, map_mul, map_intCast, map_one, LinearMap.add_apply,
      Module.End.mul_apply, Module.End.intCast_apply, Module.End.one_apply] at this
    rw [← hRdef, ← hSdef] at this
    rw [this]
    simp only [← Int.cast_smul_eq_zsmul ℂ, map_add, smul_add]
  have h2 : (2 : ℂ) • b.equivFun (ρ a z) = (2 : ℂ) • (qmMat a).mulVec (b.equivFun z) := by
    rw [two_smul, two_smul, ← map_add, hρ2, ← Matrix.add_mulVec, two_qmMat a n hn]
    simp only [map_add, map_smul, hGR, hGS, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  exact smul_right_injective _ two_ne_zero h2

/-- **`QMLatticeFree` from Skolem–Noether over `ℂ` and class number one (proved):** transport the
lattice by the intertwiner `G` (still a full lattice: `ZLattice.comap` along `G⁻¹`). -/
theorem qmLatticeFree_of (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne) : QMLatticeFree := by
  intro Λ _ hlat ρ hρ
  obtain ⟨G, hG⟩ := hSN ρ
  let Gc : (Fin 2 → ℂ) ≃L[ℝ] (Fin 2 → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv (G.symm.restrictScalars ℝ)
  have hmap : Λ.map (G.toLinearMap.restrictScalars ℤ) = ZLattice.comap ℝ Λ Gc.toLinearMap := by
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      ZLattice.comap, Submodule.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change G.symm (G y) ∈ Λ
      simpa using hy
    · intro hz
      exact ⟨G.symm z, hz, by simp⟩
  have : IsZLattice ℝ Λ := hlat
  obtain ⟨w, hw, hΛw⟩ := hCN (ZLattice.comap ℝ Λ Gc.toLinearMap) inferInstance (by
    intro a z hz
    rw [← hmap] at hz ⊢
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨ρ a y, hρ a y hy, by simp [hG]⟩)
  exact ⟨G, w, hw, hmap.trans hΛw, hG⟩

/-! ### Step 2h: `UnifTransport` from the transport of complex points (algebraic geometry) -/

/-- **GLUE (complex points of the base change).** In the situation of `UnifTransport` there is a
group isomorphism `ψ : Q.A(ℂ) ≅ A(ℂ)_σ` (`σ = ι ∘ emb`) compatible with regular functions: for every
open `U` of `A` and `s ∈ Γ(U, 𝒪_A)` there are an open `U'` of `Q.A` and `s' ∈ Γ(U', 𝒪)` with
`ψ(x) ∈ U(ℂ) ↔ x ∈ U'(ℂ)` and `s(ψ x) = s'(x)` there.

Why true: `A(ℂ)_σ = Hom_K(Spec ℂ, A) = Hom_ℂ(Spec ℂ, A ×_K ℂ)`, and `A ×_K ℂ ≅ P.A ×_ℚ̄ ℂ ≅ Q.A`
as `ℂ`-schemes (pullback pasting with `FibreOver`'s isomorphism and `IsBaseChangeOf`'s square).
The bijection `χ : Q.A(ℂ) → A(ℂ)_σ` so obtained comes from an isomorphism of `ℂ`-varieties, so by
rigidity (Mumford, *Abelian Varieties*, §4 Cor. 1, UNVERIFIED number) `ψ(x) = χ(x)·χ(1)⁻¹` is a
group isomorphism. For `U`, `s`: `U'` is the image in `Q.A` of `t⁻¹(U_ℂ)`, `t` the translation by
`χ(1)⁻¹` on `A_ℂ`, and `s' = (s ⊗ 1) ∘ t` transported to `Q.A`. Not in Mathlib: pullbacks of points
over `Over` categories are routine; rigidity is a textbook leaf. Size: medium. -/
def CPtsTransport : Prop :=
  ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) (emb : K.K →+* Qbar) (P : QML3 Qbar),
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
    ∀ (ιe : Qbar →+* ℂ) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    ∃ ψ : CPts Q.A (RingHom.id ℂ) ≃* CPts (LeafAdopt.abVarEquiv K.K A) (ιe.comp emb),
      ∀ (U : (LeafAdopt.abVarEquiv K.K A).X.left.Opens)
        (s : Γ((LeafAdopt.abVarEquiv K.K A).X.left, U)),
        ∃ (U' : Q.A.X.left.Opens) (s' : Γ(Q.A.X.left, U')),
          ∀ x : CPts Q.A (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U') ∧
            (⊤ ≤ x.left ⁻¹ᵁ U' → cEvalAt (ψ x) U s = cEvalAt x U' s')

/-- **`UnifTransport` from `CPtsTransport` (proved):** `Φ_A = ψ ∘ Φ_Q`. -/
theorem unifTransport_of (hCP : CPtsTransport) : UnifTransport := by
  intro K A emb P hiso ιe Q hQ Λ Φu hU
  obtain ⟨ψ, hψ⟩ := hCP K A emb P hiso ιe Q hQ
  obtain ⟨hadd, hker, hsurj, hopen, hhol⟩ := hU
  have hdom : ∀ (U : (LeafAdopt.abVarEquiv K.K A).X.left.Opens)
      (U' : Q.A.X.left.Opens) (s' : Γ(Q.A.X.left, U')),
      (∀ x : CPts Q.A (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U')) →
      cDom (fun z => ψ (Φu z)) U = cDom Φu U' := by
    intro U U' s' h
    ext z
    exact h (Φu z)
  refine ⟨fun z => ψ (Φu z), fun z w => ?_, fun z => ?_, fun x => ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [hadd, map_mul]
  · rw [← hker]
    exact MulEquiv.map_eq_one_iff ψ
  · obtain ⟨y, rfl⟩ := ψ.surjective x
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, rfl⟩
  · obtain ⟨U', s', h⟩ := hψ U 0
    rw [hdom U U' s' (fun x => (h x).1)]
    exact hopen U'
  · obtain ⟨U', s', h⟩ := hψ U s
    rw [hdom U U' s' (fun x => (h x).1)]
    exact (hhol U' s').congr (fun z hz => (h (Φu z)).2 hz)

/-! ### Step 2c: the proofs -/

/-- An embedding `ℚ̄ → ℂ` over `ℚ`. -/
def qbarToC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- **The finite value forces `jDen ≠ 0` (proved)** from `QMDenZeroCM3` and the `−3` clause of
`QMHauptmodul`; then F1's quotient is the value of `f`. -/
theorem jRatio_of_value {f : UpperHalfPlane → OnePoint ℂ} (hf : QMHauptmodulFn f)
    (hD : QMDenZeroCM3) (τ : UpperHalfPlane) (t : ℂ) (ht : f τ = (t : OnePoint ℂ)) :
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = t := by
  have hden : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by
    intro h0
    obtain ⟨x, hxO, hx, g, hg, hfix⟩ := hD τ h0
    have h3 := hf.2.2.2.2.2.1 x hxO hx g hg τ hfix
    rw [ht] at h3
    exact OnePoint.coe_ne_infty _ h3
  have h2 := hf.2.1 τ hden
  rw [ht] at h2
  exact (OnePoint.coe_injective h2).symm

/-- **`FibreQMPeriod` for one triple from the named Props (proved).** -/
theorem fibreQMPeriodAt_of (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : QMPeriodValue Y Φ π) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    FibreQMPeriodAt Y Φ π := by
  intro u hu K A hFib
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := hFib
  obtain ⟨f, hf⟩ := hH
  obtain ⟨Q, -, hQ⟩ := h1.2.2.2.1 Qbar ℂ qbarToC y P hP
  obtain ⟨τ, hτ, Φu, hΦu, hc⟩ := hU Q
  obtain ⟨Φa, hΦa⟩ := hT K A emb P hiso (qbarToC : Qbar →+* ℂ) Q hQ _ Φu hΦu
  refine ⟨(qbarToC : Qbar →+* ℂ).comp emb, _, Φa, hΦa, τ, hτ, LinearEquiv.refl ℂ _, ?_, ?_⟩
  · ext v
    simp
  · have hval := hV f hf y P hP (qbarToC : Qbar →+* ℂ) Q hQ ⟨τ, hτ⟩ Φu hΦu hc
    rw [hy, OnePoint.map_some] at hval
    have e : (qbarToC : Qbar →+* ℂ) (algebraMap ℚ Qbar (Jmap u)) = ((Jmap u : ℚ) : ℂ) := by
      rw [RingHom.coe_coe, AlgHom.commutes, eq_ratCast]
    rw [e] at hval
    exact jRatio_of_value hf hD ⟨τ, hτ⟩ _ hval

/-- **`FibreQMPeriod` for the leaf's own triple from the named Props (proved).** -/
theorem fibreQMPeriodOwn_of (h : R1R2fp) (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : QMPeriodValue (ownY h) (ownΦ h) (ownπ h)) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    FibreQMPeriodOwn h :=
  fibreQMPeriodAt_of _ _ _ (own_spec h).1 hH hU hV hD hT

/-- **Main result: `FibreQMPeriod` from named Props (proved).** The Hauptmodul comparison is
needed only for the leaf's own triple; `Pin.MobiusGlue` carries it to every triple. -/
theorem fibreQMPeriod_of_named (h : R1R2fp) (hM : Pin.MobiusGlue) (hH : PkgI1.QMHauptmodul)
    (hU : QMComplexUnif) (hV : QMPeriodValue (ownY h) (ownΦ h) (ownπ h)) (hD : QMDenZeroCM3)
    (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_own h hM (fibreQMPeriodOwn_of h hH hU hV hD hT)

/-- **Variant without `MobiusGlue` (proved):** with the Hauptmodul comparison for every triple. -/
theorem fibreQMPeriod_of_named_all (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R2fpProps Y Φ π → QMPeriodValue Y Φ π)
    (hD : QMDenZeroCM3) (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fun Y Φ π h1 h2 => fibreQMPeriodAt_of Y Φ π h1 hH hU (hV Y Φ π h1 h2) hD hT

/-- The same from the decomposition's bundle form of the leaf (`LeafAdopt.R1R2fpRep`). -/
theorem fibreQMPeriod_of_named_rep (h : LeafAdopt.R1R2fpRep) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hU : QMComplexUnif)
    (hV : QMPeriodValue (ownY (LeafAdopt.R1R2fp_of_rep h)) (ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (ownπ (LeafAdopt.R1R2fp_of_rep h)))
    (hD : QMDenZeroCM3) (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_named _ hM hH hU hV hD hT

/-- **Main result, finest form (proved):** `FibreQMPeriod` from `MobiusGlue` (proved by mobius-glue
from two curve facts and T5), the existing leaf `QMHauptmodul`, the leaf candidates
`QMComplexUnif` and `QMDenZeroCM3`, and the glue `QMPeriodMap` (own triple), `HauptmodulUnique`,
`UnifTransport`. -/
theorem fibreQMPeriod_of_parts (h : R1R2fp) (hM : Pin.MobiusGlue) (hH : PkgI1.QMHauptmodul)
    (hU : QMComplexUnif) (hPM : QMPeriodMap (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_named h hM hH hU (qmPeriodValue_of _ _ _ hPM hHU) hD hT

/-- **Main result with `QMComplexUnif` split (proved).** -/
theorem fibreQMPeriod_of_parts' (h : R1R2fp) (hM : Pin.MobiusGlue) (hH : PkgI1.QMHauptmodul)
    (hE : UniformizationExistsC) (hS : UnifStructure) (hL : QMLatticeAlgebra)
    (hPM : QMPeriodMap (ownY h) (ownΦ h) (ownπ h)) (hHU : HauptmodulUnique)
    (hD : QMDenZeroCM3) (hT : UnifTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_parts h hM hH (qmComplexUnif_of hE hS hL) hPM hHU hD hT

/-- **Main result, finest form (proved):** `FibreQMPeriod` from
* `Pin.MobiusGlue` (glue; proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and T5),
* `PkgI1.QMHauptmodul` (existing composite leaf), `UniformizationExistsC` (textbook leaf),
  `R1bFamily` at the leaf's own triple (leaf: R1(b), concrete),
* `UnifStructure`, `QMLatticeAlgebra`, `PeriodMapGlue` (own triple), `HauptmodulUnique`,
  `QMDenZeroCM3`, `UnifTransport` (glue). -/
theorem fibreQMPeriod_of_leaves_glue (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsC)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hS : UnifStructure) (hL : QMLatticeAlgebra) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_parts' h hM hH hE hS hL (qmPeriodMap_of _ _ _ hR hG) hHU hD hT

/-- **Main result, final form (proved):** `FibreQMPeriod` from
* leaves: `PkgI1.QMHauptmodul` (existing composite leaf), the textbook leaves T35
  (`UniformizationExistsT35`) and T11a (`T11aRiemannEnd`), both already in leaf-adopt3's
  `TextbookLeaves`, and R1(b) in family form at the leaf's own triple (`R1bFamily`);
* glue: `Pin.MobiusGlue` (proved by mobius-glue), `QMLatticeAlgebra`, `PeriodMapGlue` (own triple),
  `HauptmodulUnique`, `QMDenZeroCM3`, `UnifTransport`. -/
theorem fibreQMPeriod_of_textbook (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hL : QMLatticeAlgebra) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_parts h hM hH (qmComplexUnif_of_textbook hE hR11 hL)
    (qmPeriodMap_of _ _ _ hR hG) hHU hD hT

/-- **Main result, final form (proved):** as `fibreQMPeriod_of_textbook`, with
`QMLatticeAlgebra` replaced by its algebraic core `QMLatticeFree` (Skolem–Noether and class number
one). -/
theorem fibreQMPeriod_final (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hF : QMLatticeFree) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_of_textbook h hM hH hE hR11 hR (qmLatticeAlgebra_of_free hF) hG hHU hD hT

/-- **Main result, final form with the lattice algebra split (proved).** Hypotheses:
* leaves: `PkgI1.QMHauptmodul` (existing composite leaf), T35 `UniformizationExistsT35`, T11a
  `T11aRiemannEnd` (both already in leaf-adopt3's `TextbookLeaves`), `QMSkolemNoetherC`,
  `QMClassNumberOne` (textbook), `R1bFamily` at the leaf's own triple (R1(b), concrete);
* glue: `Pin.MobiusGlue` (proved by mobius-glue from two curve facts and T5), `PeriodMapGlue` (own
  triple), `HauptmodulUnique`, `QMDenZeroCM3`, `UnifTransport`. -/
theorem fibreQMPeriod_final' (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hT : UnifTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_final h hM hH hE hR11 hR (qmLatticeFree_of hSN hCN) hG hHU hD hT

/-- **Main result, final form (proved).** As `fibreQMPeriod_final'`, with `UnifTransport` replaced
by `CPtsTransport` (complex points of the base change, as a group isomorphism compatible with
regular functions). -/
theorem fibreQMPeriod_final'' (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hSN : QMSkolemNoetherC) (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_final' h hM hH hE hR11 hSN hCN hR hG hHU hD (unifTransport_of hCP)

/-- **Main result (proved).** `FibreQMPeriod` from
* leaves: `PkgI1.QMHauptmodul` (existing composite leaf), T35 `UniformizationExistsT35` and T11a
  `T11aRiemannEnd` (verbatim copies of the kernel's textbook leaves, in leaf-adopt3's
  `TextbookLeaves`), `QMClassNumberOne` (textbook: Eichler's class number one, lattice form),
  `R1bFamily` at the leaf's own triple (R1(b), concrete);
* glue: `Pin.MobiusGlue` (proved by mobius-glue from two curve facts and T5), `PeriodMapGlue` (own
  triple), `HauptmodulUnique`, `QMDenZeroCM3`, `CPtsTransport`.
(`QMSkolemNoetherC` is proved here, `qmSkolemNoetherC_proof`.) -/
theorem fibreQMPeriod_main (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h)) (hG : PeriodMapGlue (ownY h) (ownΦ h) (ownπ h))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_final'' h hM hH hE hR11 qmSkolemNoetherC_proof hCN hR hG hHU hD hCP

/-- **Main result from the decomposition's bundle form of the leaf (`LeafAdopt.R1R2fpRep`,
proved).** -/
theorem fibreQMPeriod_main_rep (h : LeafAdopt.R1R2fpRep) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY (LeafAdopt.R1R2fp_of_rep h)) (ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (ownπ (LeafAdopt.R1R2fp_of_rep h)))
    (hG : PeriodMapGlue (ownY (LeafAdopt.R1R2fp_of_rep h)) (ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (ownπ (LeafAdopt.R1R2fp_of_rep h)))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_main _ hM hH hE hR11 hCN hR hG hHU hD hCP

end FibreQM

end G0Split

end HSyn

end


end G0A2_a80_fqm

section G0A2_a85_linked
/-! ## g0-assemble2: `LinkedTateData` reduced (g14-trace, g15-ram)

* kernel `ZInQKernel/HDecomp/C10/Link.lean` lines 26-473 (verbatim; namespace `GlueC10Link`, not in
  Leaves.lean; its imports `C10.C10`, `C10.Trace`, `Descent.ProjRep` are in Leaves.lean);
* scratch/g14-trace/part_g14.lean lines 26-348 (verbatim; namespace `G14Trace`);
* scratch/g15-ram/G15Ram.lean lines 88-1386 (verbatim; §1-§3, namespace `G15Ram`; its lines 31-86
  are copies of g0-mod-galois' `G11Out` and g0-mod-newform's `U0`, `LocalRamG`, `G15RamG`, parts 70, 77);
* new (g0-assemble2): `LocalRamWild` from `LocalData` (the first two bullets of g15-ram's
  `localRamG_of`, without G11), the joint glue `LinkedTateLocal`, and `LinkedTateData` from it and T7.
-/
noncomputable section

open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace GlueC10Link

/-! ## 1. `r = ρ|_W` and `tr ρ = 2 tr r` -/

section Sub

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] (u : MatrixUnits2 E V)
variable {G : Type*} [Monoid G]

/-- The descended two-dimensional representation `r_ℓ`: the restriction of `ρ_ℓ` to
`W = e₀₀ V` (N5 L729-730, "matrix units give `ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`"). -/
def subRep (ρ : Representation E G V) (hc : ∀ g i j, Commute (ρ g) (u.e i j)) :
    Representation E G u.W where
  toFun g := (ρ g).restrict (fun _ hw => u.mapsTo_W ρ hc g hw)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

@[simp] theorem subRep_apply (ρ : Representation E G V) (hc : ∀ g i j, Commute (ρ g) (u.e i j))
    (g : G) (w : u.W) : ((subRep u ρ hc g) w : V) = ρ g w := rfl

/-- Under `V ≃ W × W`, `ρ g` becomes `r g × r g`. -/
theorem conj_splitEquiv (ρ : Representation E G V) (hc : ∀ g i j, Commute (ρ g) (u.e i j))
    (g : G) : u.splitEquiv.conj (ρ g) = LinearMap.prodMap (subRep u ρ hc g) (subRep u ρ hc g) := by
  apply LinearMap.ext
  intro x
  have h := u.splitEquiv_intertwines ρ hc g (u.splitEquiv.symm x)
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, h]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp

/-- **`tr ρ(g) = 2 · tr r(g)`** (the hypothesis `h2` of `GlueC10.trace_half`, now proved from
the matrix units). -/
theorem trace_eq_two_mul_trace_subRep [FiniteDimensional E V] (ρ : Representation E G V)
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)) (g : G) :
    LinearMap.trace E V (ρ g) = 2 * LinearMap.trace E u.W (subRep u ρ hc g) := by
  rw [← LinearMap.trace_conj' (ρ g) u.splitEquiv, conj_splitEquiv u ρ hc g,
    LinearMap.trace_prodMap']
  ring

end Sub

/-! ## 2. `tr ρ(σ) = β(σ)⁻¹ a_σ tr T(σ)` -/

theorem trace_rho {G E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    (T : G → Module.End E V) (a β : G → E) (g : G) :
    LinearMap.trace E V (rho T a β g) = (β g)⁻¹ * a g * LinearMap.trace E V (T g) := by
  simp [rho, map_smul, smul_eq_mul]

/-! ## 3. The trace of an endomorphism of an abelian variety on `V_ℓ ⊗ E` -/

/-- If `E ⊗_K M` is finite over `E` then `M` is finite over `K` (fields). -/
theorem finite_of_baseChange {K E M : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup M]
    [Module K M] [Module.Finite E (E ⊗[K] M)] : Module.Finite K M := by
  let b := Module.Free.chooseBasis K M
  have : Finite (Module.Free.ChooseBasisIndex K M) :=
    Module.Finite.finite_basis (Algebra.TensorProduct.basis E b)
  exact Module.Finite.of_basis b

/-- `V_ℓ(φ)` extended to `E ⊗_{ℚ_ℓ} V_ℓ(Ā)`, for a field `E ⊇ ℚ_ℓ`. -/
abbrev endE {k : Type} [Field k] {A : AbVar k} (φ : AbVar.End A) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] : Module.End E (E ⊗[ℚ_[ℓ]] A.V ℓ) :=
  ((AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange E

set_option synthInstance.maxHeartbeats 400000 in
/-- **The ℓ-independent trace on `V_ℓ ⊗ E`** (from Mumford §19 Thm 4). One integer `t` is the
trace of `φ` on `E ⊗ V_ℓ(A)` for every prime `ℓ ≠ char k` and every field `E ⊇ ℚ_ℓ` over which
`E ⊗ V_ℓ(A)` is finite-dimensional. -/
theorem trace_endE_indep (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (φ : AbVar.End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE φ ℓ E) = (t : E) := by
  obtain ⟨t, ht⟩ := PkgI3.trace_indep_of_ell hM k A φ
  refine ⟨t, fun ℓ _ hℓ E _ _ _ => ?_⟩
  have : Module.Finite ℚ_[ℓ] (A.V ℓ) := finite_of_baseChange (E := E)
  classical
  let b := Module.Free.chooseBasis ℚ_[ℓ] (A.V ℓ)
  let _ : Fintype (Module.Free.ChooseBasisIndex ℚ_[ℓ] (A.V ℓ)) := Fintype.ofFinite _
  rw [endE, LinearMap.trace_baseChange, ht ℓ hℓ _ b, map_intCast]


/-! ## 4. The descended representation over the coefficient field `C` -/

section Desc

variable {G C : Type*} [Group G] [Field C] (c ε : G → G → C) (a β : G → C)
  (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
  (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
  (hβ1 : β 1 = 1)
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] (emb : C →+* E)
  (T : G → Module.End E V) (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)

/-- **`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ`** (N5 L723-727) with the scalars `a_σ, β(σ), c(σ,τ), ε(σ,τ)`
in the coefficient field `C` and mapped to `E` by the chosen embedding `emb : C → E`
(N5 L719-722); `T σ = μ_σ ∘ σ` on `V = V_ℓ(A) ⊗ E`. -/
def rhoL : Representation E G V :=
  rhoRep T (fun g h => emb (c g h)) (fun g h => emb (ε g h)) (fun g => emb (a g)) (fun g => emb (β
      g)) hT
    (fun g h => by simp only [← map_mul, ha]) (fun g h => by simp only [← map_mul, hβ])
    (fun g => (map_ne_zero emb).mpr (hβ0 g)) (by simp [rho, ha1, hβ1, hT1])

theorem rhoL_apply (g : G) :
    rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 g = rho T (fun g => emb (a g)) (fun g => emb (β g))
        g :=
  rfl

variable (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j))

include hu in
theorem rhoL_commute (g : G) (i j : Fin 2) :
    Commute (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 g) (u.e i j) :=
  rho_commute T _ _ (u.e i j) (fun g => hu g i j) g

/-- **`r_ℓ`**: the restriction of `ρ_ℓ` to `W = e₀₀ V`, so that `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`. -/
def rL : Representation E G u.W :=
  subRep u (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1)
    (rhoL_commute c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu)

end Desc

/-! ## 5. The Frobenius comparison (an input from the surface `A`) and the trace link -/

/-- **The Frobenius comparison at `ℓ` (from the surface `A`; not glue).** For `σ` a Frobenius
lift at a place `v` of good reduction with `ℓ ≠ p`, `Tσ = μ_σ ∘ σ` on `V = V_ℓ(A) ⊗ E`, `Ā = Ā_v`
over the residue field `k`, `α' = N·(μ̄_σ ∘ F) ∈ End(Ā)` (`N ≥ 1` clears the denominator of the
quasi-isogeny `μ_σ`): some `E`-linear isomorphism `Φ : V ≃ E ⊗ V_ℓ(Ā)` carries `N·Tσ` to
`V_ℓ(α')`. In the manuscript `Φ` is the reduction isomorphism (Serre–Tate), and the square
commutes by the Néron mapping property (reduction of `μ_σ`) and because `σ` acts on reduced
points as the relative `p`-Frobenius `F : Ā → Ā^{(p)} = \overline{{}^σA}` (N5 L781-786). -/
def FrobCompare (ℓ : ℕ) [Fact ℓ.Prime] {E V : Type*} [Field E] [Algebra ℚ_[ℓ] E]
    [AddCommGroup V] [Module E V] (Tσ : Module.End E V) {k : Type} [Field k] {A : AbVar k}
    (α : AbVar.End A) (N : ℕ) : Prop :=
  ∃ Φ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ, Φ.conj ((N : E) • Tσ) = endE α ℓ E

/-- Under the comparison, `N · tr T(σ) = t`, the ℓ-independent trace of `α'`. -/
theorem trace_T_of_frobCompare (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (α : AbVar.End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
        [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ), FrobCompare ℓ Tσ α N →
        (N : E) * LinearMap.trace E V Tσ = (t : E) := by
  obtain ⟨t, ht⟩ := trace_endE_indep hM A α
  refine ⟨t, fun ℓ _ hℓ E V _ _ _ _ _ Tσ N ⟨Φ, hΦ⟩ => ?_⟩
  have : Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ) := Module.Finite.equiv Φ
  rw [← ht ℓ hℓ E, ← hΦ, LinearMap.trace_conj', map_smul, smul_eq_mul]

/-- **The trace link (GLUE, proved from Mumford §19 Thm 4):
`c_p = ½ · β(σ)⁻¹ a_σ · tr α_σ`.** Given `Ā` and `α' ∈ End(Ā)` there is one integer `t`
(the trace of `α'` on `V_ℓ(Ā)`, the same for every `ℓ ≠ char k`) such that for every prime
`ℓ ≠ char k`, every coefficient field `E ⊇ ℚ_ℓ` with embedding `emb : C → E`, every descent datum
`(T, c, ε, a, β)` and matrix units `u`, and every `σ` whose `T σ` satisfies the Frobenius
comparison with `α'` and `N`:
`tr r_ℓ(σ) = emb(½ · β(σ)⁻¹ a_σ · t/N)`, and `t/N = tr α_σ` for `α_σ = α'/N`. -/
theorem trace_link (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A) :
    ∃ t : ℤ, (∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE α ℓ E) = (t : E)) ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {G C E V : Type} [Group G] [Field C] [CharZero C] [Field E] [Algebra ℚ_[ℓ] E]
        [AddCommGroup V] [Module E V] [FiniteDimensional E V]
        (c ε : G → G → C) (a β : G → C)
        (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
        (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
        (hβ1 : β 1 = 1) (emb : C →+* E) (T : G → Module.End E V)
        (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)
        (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j)) (σ : G) (N : ℕ),
        N ≠ 0 → FrobCompare ℓ (T σ) α N →
        LinearMap.trace E u.W (rL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ) =
          emb ((β σ)⁻¹ * a σ * ((t : C) / N) / 2) := by
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM A α
  obtain ⟨t', ht'⟩ := trace_endE_indep hM A α
  have htt : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
        [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ), FrobCompare ℓ Tσ α N →
        (N : E) * LinearMap.trace E V Tσ = (t' : E) := by
    intro ℓ _ hℓ E V _ _ _ _ _ Tσ N ⟨Φ, hΦ⟩
    have : Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ) := Module.Finite.equiv Φ
    rw [← ht' ℓ hℓ E, ← hΦ, LinearMap.trace_conj', map_smul, smul_eq_mul]
  clear ht t
  refine ⟨t', ht', fun ℓ _ hℓ G C E V _ _ _ _ _ _ _ _ c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ
      N
    hN hcmp => ?_⟩
  have hNT := htt ℓ hℓ (T σ) N hcmp
  have h2 := trace_eq_two_mul_trace_subRep u (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1)
    (rhoL_commute c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu) σ
  rw [rhoL_apply, trace_rho] at h2
  change LinearMap.trace E u.W (subRep u _ _ σ) = _
  have hNE : (N : E) ≠ 0 := by
    rw [← map_natCast emb]; exact (map_ne_zero emb).mpr (Nat.cast_ne_zero.mpr hN)
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat emb 2]; exact (map_ne_zero emb).mpr two_ne_zero
  have hβE : emb (β σ) ≠ 0 := (map_ne_zero emb).mpr (hβ0 σ)
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat,
    ← hNT, mul_div_cancel_left₀ _ hNE, h2, mul_div_cancel_left₀ _ h2E]


/-! ## 6. Connection to `GlueC10.c10`: its trace hypotheses `hr₃, hr₅` discharged -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `ℓ ≠ p` in a field of characteristic `p`. -/
theorem cast_ne_zero_of_charP {k : Type} [Field k] {p ℓ : ℕ} [CharP k p] (hp : p.Prime)
    (hℓ : ℓ.Prime) (hne : p ≠ ℓ) : (ℓ : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p ℓ]
  exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h)

/-- **The trace hypothesis of C10, from the link.** For every Frobenius `g` at `p ∉ S`
(`3, 5 ∈ S`) with a Frobenius comparison at `3` and at `5` against one `(Ā, α', N)` over a field
of characteristic `p`, there is one `x = ½ β(g)⁻¹ a_g tr α_g ∈ C` with `tr r₃(g) = ι₃(x)` and
`tr r₅(g) = ι₅(x)` (N5 L788-790: "one element of `C` whose images are the traces of every
`r_ℓ`"). -/
theorem trace_link_three_five (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S)
    (h5S : 5 ∈ S) {G C : Type} [Group G] [Field C] [CharZero C]
    (c ε : G → G → C) (a β : G → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1)
    {k₅ V₅ : Type} [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] (ι₅ : C →+* k₅) (T₅ : G → Module.End k₅ V₅)
    (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h)) (hT₅1 : T₅ 1 = 1)
    (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] (ι₃ : C →+* k₃) (T₃ : G → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (g : G) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S)
    (hFrob : ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
      N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N) :
    ∃ x : C,
      LinearMap.trace k₃ u₃.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g) = ι₃ x ∧
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) = ι₅ x := by
  obtain ⟨k, _, hk, A, α, N, hN, h3, h5⟩ := hFrob
  obtain ⟨t, -, ht⟩ := trace_link hM A α
  have h3k : ((3 : ℕ) : k) ≠ 0 :=
    cast_ne_zero_of_charP hp Nat.prime_three (fun h => hpS (h ▸ h3S))
  have h5k : ((5 : ℕ) : k) ≠ 0 :=
    cast_ne_zero_of_charP hp (by norm_num) (fun h => hpS (h ▸ h5S))
  exact ⟨_, ht 3 h3k c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g N hN h3,
    ht 5 h5k c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g N hN h5⟩

/-- **C10 with its abelian-variety trace hypotheses discharged by the link (GLUE, proved from
Chebotarev, Brauer–Nesbitt and Mumford §19 Thm 4).** `GlueC10.c10` is applied with
`r_ℓ = rL …` (the descended representation of B1/C1) and `c := a_f` (the modular coefficients).
Its hypotheses `hr₃, hr₅` are proved:
* `hr₅` from C9 (`h₅`) and Eichler–Shimura at 5 (`hρ₅`);
* `hr₃` from the link: `x = ½ β(g)⁻¹ a_g tr α_g` has `ι₅(x) = tr r₅(g) = ι₅(a_f(p))`, so
  `x = a_f(p)` and `tr r₃(g) = ι₃(x) = ι₃(a_f(p))`.
What remains as hypotheses: the descent data and matrix units (`T_ℓ, c, ε, a, β, u_ℓ`), the
Frobenius comparison `hFrob`, C9 `h₅`, Eichler–Shimura `hρ₅, hρ₃`, continuity and
semisimplicity of `r₃, ρ₃`. -/
theorem c10_of_trace_link (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    -- ℓ = 5
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    -- ℓ = 3
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    -- the Frobenius comparison, from the surface `A`
    (hFrob : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
        N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N) :
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule) := by
  refine GlueC10.c10 hC hBN S C af af k₅ u₅.W W₅ ι₅
    (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅) ρ₅ h₅
    (fun g p hp hpS hg => (h₅ g p hp hpS hg).trans (hρ₅ g p hp hpS hg)) hρ₅
    k₃ u₃.W W₃ ιI κ ι₃ bV bW (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃) ρ₃
    hrc hρc hr hρ ?_ hρ₃
  intro g p hp hpS hg
  obtain ⟨x, hx₃, hx₅⟩ := trace_link_three_five hM S h3S h5S c ε a β ha hβ hβ0 ha1 hβ1
    ι₅ T₅ hT₅ hT₅1 u₅ hu₅ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g p hp hpS (hFrob g p hp hpS hg)
  have hxa : x = af p := ι₅.injective (hx₅.symm.trans ((h₅ g p hp hpS hg).trans
    (hρ₅ g p hp hpS hg)))
  rw [hx₃, hxa]


/-! ## 8. `FrobCompare` from three squares (the inputs from `A`, separated)

`A, Aσ` abelian varieties over `L` (`Aσ` plays `{}^σA`), `μ' = N μ_σ : Aσ → A` (an isogeny,
genuine `Hom`), `Ā, Ā'` abelian varieties over the residue field `k` (`Ā'` plays
`Ā^{(p)} = \overline{{}^σA}`), `F : Ā → Ā'` (relative Frobenius) and `μ̄' : Ā' → Ā` (the
reduction of `μ'`), all genuine `Hom`s of pkg-I3 abelian varieties. The Galois transport
`σ_* : V_ℓ(A) → V_ℓ(Aσ)` and the reduction isomorphisms `red, red'` are abstract `ℚ_ℓ`-linear
isomorphisms, constrained only by the squares. -/

open CategoryTheory in
/-- Composition of homomorphisms of pkg-I3 abelian varieties (`f` then `g`). -/
def homComp {K : Type} [Field K] {A B C : AbVar K} (f : AbVar.Hom A B) (g : AbVar.Hom B C) :
    AbVar.Hom A C :=
  AbVar.Hom.mk' (f.hom ≫ g.hom)

open CategoryTheory in
/-- `T_ℓ` is functorial for `homComp`. -/
theorem homT_homComp {K : Type} [Field K] {A B C : AbVar K} (ℓ : ℕ) [Fact ℓ.Prime]
    (f : AbVar.Hom A B) (g : AbVar.Hom B C) :
    AbVar.homT (ℓ := ℓ) (homComp f g) = AbVar.homT (ℓ := ℓ) g ∘ₗ AbVar.homT (ℓ := ℓ) f := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (f.hom ≫ g.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ f.hom) ≫ g.hom)
  exact congrArg Additive.ofMul (Category.assoc _ _ _).symm

/-- `V_ℓ(f)`: the `ℚ_ℓ`-linear map of rational Tate modules. -/
abbrev Vmap {K : Type} [Field K] {A B : AbVar K} (ℓ : ℕ) [Fact ℓ.Prime] (f : AbVar.Hom A B) :
    A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ :=
  (AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]

/-- Conjugation commutes with base change. -/
theorem conj_baseChange {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (f : Module.End R M) :
    (e.baseChange R A M N).conj (f.baseChange A) = (e.conj f).baseChange A := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simp [LinearEquiv.conj_apply]

/-- **`FrobCompare` from the three inputs of the surface `A` (GLUE, proved).**
* `hΨ` (the instantiation of the descent: `T(σ) = μ_σ ∘ σ`, i.e. `N·T(σ) = μ' ∘ σ_*` on
  `V ≅ E ⊗ V_ℓ(A)`);
* `hS1` (Serre–Tate reduction and Frobenius: `red' ∘ σ_* = V_ℓ(F) ∘ red`);
* `hS2` (Néron mapping property: `red ∘ V_ℓ(μ') = V_ℓ(μ̄') ∘ red'`).
Then `FrobCompare ℓ (T σ) α' N` with `α' = μ̄' ∘ F`. -/
theorem frobCompare_of_squares (ℓ : ℕ) [Fact ℓ.Prime] {L k : Type} [Field L] [Field k]
    {A Aσ : AbVar L} (mu : AbVar.Hom Aσ A) {Ab Ab' : AbVar k} (F : AbVar.Hom Ab Ab')
    (mub : AbVar.Hom Ab' Ab) (σs : A.V ℓ ≃ₗ[ℚ_[ℓ]] Aσ.V ℓ) (red : A.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (red' : Aσ.V ℓ ≃ₗ[ℚ_[ℓ]] Ab'.V ℓ)
    (hS1 : red'.toLinearMap ∘ₗ σs.toLinearMap = Vmap ℓ F ∘ₗ red.toLinearMap)
    (hS2 : red.toLinearMap ∘ₗ Vmap ℓ mu = Vmap ℓ mub ∘ₗ red'.toLinearMap)
    {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
    (Tσ : Module.End E V) (N : ℕ) (Ψ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ)
    (hΨ : Ψ.conj ((N : E) • Tσ) = (Vmap ℓ mu ∘ₗ σs.toLinearMap).baseChange E) :
    FrobCompare ℓ Tσ (homComp F mub : AbVar.End Ab) N := by
  refine ⟨Ψ.trans (red.baseChange ℚ_[ℓ] E _ _), ?_⟩
  have hconj : red.conj (Vmap ℓ mu ∘ₗ σs.toLinearMap) = Vmap ℓ mub ∘ₗ Vmap ℓ F := by
    apply LinearMap.ext; intro x
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 := LinearMap.congr_fun hS2 (σs (red.symm x))
    have h1 := LinearMap.congr_fun hS1 (red.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 h2
    rw [h2, h1]
  rw [← LinearEquiv.conj_trans]
  change (red.baseChange ℚ_[ℓ] E _ _).conj (Ψ.conj ((N : E) • Tσ)) = _
  rw [hΨ, conj_baseChange, hconj, endE, homT_homComp]
  congr 1
  exact (LinearMap.baseChange_comp _ _).symm


/-- The three inputs of `frobCompare_of_squares` at one `ℓ`, for given `μ', F, μ̄'`. -/
def FrobSquares (ℓ : ℕ) [Fact ℓ.Prime] {L k : Type} [Field L] [Field k]
    {A Aσ : AbVar L} (mu : AbVar.Hom Aσ A) {Ab Ab' : AbVar k} (F : AbVar.Hom Ab Ab')
    (mub : AbVar.Hom Ab' Ab) {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V]
    [Module E V] (Tσ : Module.End E V) (N : ℕ) : Prop :=
  ∃ (σs : A.V ℓ ≃ₗ[ℚ_[ℓ]] Aσ.V ℓ) (red : A.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (red' : Aσ.V ℓ ≃ₗ[ℚ_[ℓ]] Ab'.V ℓ) (Ψ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ),
    red'.toLinearMap ∘ₗ σs.toLinearMap = Vmap ℓ F ∘ₗ red.toLinearMap ∧
    red.toLinearMap ∘ₗ Vmap ℓ mu = Vmap ℓ mub ∘ₗ red'.toLinearMap ∧
    Ψ.conj ((N : E) • Tσ) = (Vmap ℓ mu ∘ₗ σs.toLinearMap).baseChange E

theorem frobCompare_of_frobSquares (ℓ : ℕ) [Fact ℓ.Prime] {L k : Type} [Field L] [Field k]
    {A Aσ : AbVar L} (mu : AbVar.Hom Aσ A) {Ab Ab' : AbVar k} (F : AbVar.Hom Ab Ab')
    (mub : AbVar.Hom Ab' Ab) {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V]
    [Module E V] (Tσ : Module.End E V) (N : ℕ) (h : FrobSquares ℓ mu F mub Tσ N) :
    FrobCompare ℓ Tσ (homComp F mub : AbVar.End Ab) N := by
  obtain ⟨σs, red, red', Ψ, h1, h2, hΨ⟩ := h
  exact frobCompare_of_squares ℓ mu F mub σs red red' h1 h2 Tσ N Ψ hΨ

/-- **C10 from the squares (GLUE, proved from Chebotarev, Brauer–Nesbitt, Mumford §19 Thm 4).**
`c10_of_trace_link` with the Frobenius comparison replaced by its three inputs: for every
Frobenius `g` at `p ∉ S` there are abelian varieties `A, Aσ` over a field `L`, an isogeny
`μ' : Aσ → A`, abelian varieties `Ā, Ā'` over a field `k` of characteristic `p`, homomorphisms
`F : Ā → Ā'`, `μ̄' : Ā' → Ā`, and `N ≠ 0`, with `FrobSquares` at `ℓ = 3` and `ℓ = 5`. -/
theorem c10_of_squares (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (hM : CharPolyIndepOfEll) (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A) (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab')
          (mub : AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
          FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N) :
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule) := by
  refine c10_of_trace_link hC hBN hM S h3S h5S C c ε a β ha hβ hβ0 ha1 hβ1 af k₅ V₅ W₅ ι₅ T₅ hT₅
    hT₅1 u₅ hu₅ ρ₅ h₅ hρ₅ k₃ V₃ W₃ ιI κ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ bV bW ρ₃ hrc hρc hr hρ hρ₃ ?_
  intro g p hp hpS hg
  obtain ⟨L, _, k, _, hk, A, Aσ, mu, Ab, Ab', F, mub, N, hN, h3, h5⟩ := hSq g p hp hpS hg
  exact ⟨k, inferInstance, hk, Ab, homComp F mub, N, hN,
    frobCompare_of_frobSquares 3 mu F mub (T₃ g) N h3,
    frobCompare_of_frobSquares 5 mu F mub (T₅ g) N h5⟩

/-! ## 7. Checks -/

/-- `FrobCompare` is satisfiable (non-vacuity): `V = E ⊗ V_ℓ(Ā)`, `Tσ = V_ℓ(α')`, `N = 1`,
`Φ = id`. -/
example (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] : FrobCompare ℓ (endE α ℓ E) α 1 :=
  ⟨LinearEquiv.refl E _, by simp⟩

end GlueC10Link
end

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

noncomputable section
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

noncomputable section

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

/-- **Clauses (i)-(ii) of `LocalRamG` from the local data alone** (g0-assemble2; the first two
bullets of g15-ram's `localRamG_of`, whose third bullet is G11's output; the closed local-field
inputs `UpperBreakFix` (T20, T21), `UpperWild`, `WildFixTame` are g15-ram's theorems). -/
theorem localRamWild_of_localData {ℓ : ℕ} [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime]
    (r : GaloisRep ℓ 2) (hd : LocalData p r) :
    HSyn.G0AssembleMod.LocalRamWild p r := by
  have hUB : UpperBreakFix p :=
    upperBreakFix_of_hilbertSerre (hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp))
  have hUW : UpperWild p := upperWild
  have hWT : WildFixTame p := wildFixTame
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩
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

/-- **`G15RamWild` from the local data of `r₅`, `r₃`** (g0-assemble2). -/
theorem g15RamWild_of_localData {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3) : HSyn.G0AssembleMod.G15RamWild D := by
  intro p hp
  refine ⟨fun h5' => @localRamWild_of_localData 5 _ p ⟨hp⟩ D.r5 (h5 p hp h5'), fun h5' => ?_⟩
  subst h5'
  exact localRamWild_of_localData 5 D.r3 h3

end G15Ram

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue: linked Tate data with the Frobenius link and the local data** (g0-assemble2; replaces
g0-assemble's `LinkedTateData`, which asked for `G14TraceCompat` and `G15RamWild` themselves).
For every fibre context and G7 data: one pair `a, β : G_ℚ → ℚ̄` and embeddings `j₅, j₃` (the scalar
link, N5 L719-722), operator data at `ℓ = 5, 3` with g0-mod-galois' `G7Out` for the scalars
`j_ℓ ∘ a`, `j_ℓ ∘ β`, g14-trace's `FrobTraceLink` (N5 L781-786), and, for every `r₅`, `r₃` that G8
attaches to these data, g15-ram's `LocalData` (N5 L819-852: the local Galois closure and twist at
each `p`). `G14TraceCompat` then follows from T7 (g14-trace) and `G15RamWild` from the local
ramification theory (g15-ram, with T20, T21 proved in the kernel). -/
def LinkedTateLocal : Prop :=
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
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

/-- **g0-assemble's `LinkedTateData` from `LinkedTateLocal` and T7** (g0-assemble2): `ι₃ := j₃ ∘ γ`
where `ι₅ = j₅ ∘ γ` (g14-trace's `exists_comp_eq`); `G14TraceCompat` by g14-trace's
`g14TraceCompat_of_link`; `G15RamWild` by `G15Ram.g15RamWild_of_localData`. -/
theorem linkedTateData_of_local (hM : PkgI3.CharPolyIndepOfEll) (h : LinkedTateLocal) :
    LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  have h' := h Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h5, h3, hF, hloc⟩ := h'
  refine ⟨Tm₅, c₅, ε₅, _, _, u₅, Tm₃, c₃, ε₃, _, _, u₃, h5, h3,
    fun r₅ r₃ h8₅ h8₃ i ιC ι5 => ?_⟩
  obtain ⟨γ, hγ⟩ := G14Trace.exists_comp_eq ι5 j5
  obtain ⟨hl5, hl3⟩ := hloc r₅ r₃ h8₅ h8₃
  exact ⟨j3.comp γ,
    G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp γ, r₅, r₃⟩ j5 j3 γ hγ rfl aQ βQ
      Tm₅ Tm₃ h8₅ h8₃ hF,
    G15Ram.g15RamWild_of_localData _ hl5 hl3⟩

end HSyn.G0AssembleMod

end

end G0A2_a85_linked

section G0A2_a90_h5glue
/-! ## g0-assemble2: h5-glue (scratch/h5-glue/H5Final.lean lines 714-2627, verbatim except that the lines
`open PkgI3 (AbVar)` are deleted (as for parts a20, a25); its lines 19-712 are hodge-lattice's §1-§5, §9-§10,
which leaf-adopt3 folded into Leaves.lean) -/
/-! ## Part 2 -/

set_option linter.style.haveILetI false

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open scoped Obj


open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- `ptC τ = Over.map (jL L) (Spec ℂ over L via τ)`. -/
noncomputable def ptCIso (τ : L →+* ℂ) :
    GroupModel.ptC (L := L) τ ≅ (Over.map (jL L)).obj (Over.mk (Spec.map (CommRingCat.ofHom τ))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, Over.mk_hom, Over.map_obj_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- Complex points of a group model are complex points of its generic fibre. -/
noncomputable def ptsEquiv (𝒢 : GroupModel A L) (τ : L →+* ℂ) :
    𝒢.Pts τ ≃ (Over.mk (Spec.map (CommRingCat.ofHom τ)) ⟶ (Over.pullback (jL L)).obj 𝒢.G) :=
  ((ptCIso τ).homCongr (Iso.refl 𝒢.G)).trans ((Over.mapPullbackAdj (jL L)).homEquiv _ _)

theorem ptsEquiv_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) (τ : L →+* ℂ) (p : 𝒢.Pts τ) :
    ptsEquiv 𝒩 τ (p ≫ f) = ptsEquiv 𝒢 τ p ≫ (Over.pullback (jL L)).map f := by
  simp only [ptsEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **A morphism of group models that is an isomorphism on generic fibres is bijective on
complex points** (at every `τ : L → ℂ`). -/
theorem pts_comp_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) :
    Function.Bijective (fun p : 𝒢.Pts τ => p ≫ f) := by
  have key : (fun p : 𝒢.Pts τ => p ≫ f) = (ptsEquiv 𝒩 τ).symm ∘
      (fun q => q ≫ (Over.pullback (jL L)).map f) ∘ ptsEquiv 𝒢 τ := by
    funext p
    simp only [Function.comp, ← ptsEquiv_comp, Equiv.symm_apply_apply]
  rw [key]
  refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
  exact ⟨fun a b h => (cancel_mono _).mp h, fun c => ⟨c ≫ inv ((Over.pullback (jL L)).map f),
    by simp⟩⟩


/-- Values of regular functions along a morphism: `s(p ≫ f) = (f^* s)(p)`. -/
theorem evalAt_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (U : 𝒩.G.left.Opens) (s : Γ(𝒩.G.left, U)) :
    𝒩.evalAt (p ≫ f) U s = 𝒢.evalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem dom_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) {τ : L →+* ℂ} {g : ℕ}
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒩.G.left.Opens) :
    𝒩.dom (fun z => Φ z ≫ f) U = 𝒢.dom Φ (f.left ⁻¹ᵁ U) := rfl

/-- **Analytic uniformizations transport along generic isomorphisms** (proved). -/
theorem isAnalyticUniformization_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (h : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    𝒩.IsAnalyticUniformization τ Λ (fun z => Φ z ≫ f) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hb := pts_comp_bijective 𝒢 𝒩 f τ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    simp only
    rw [hmul, MonObj.mul_comp]
  · intro z
    rw [← hker z]
    constructor
    · intro h1
      apply hb.1
      have h1' : Φ z ≫ f = 1 := h1
      show Φ z ≫ f = 1 ≫ f
      rw [h1', MonObj.one_comp]
    · intro h1
      simp only
      rw [h1, MonObj.one_comp]
  · intro q
    obtain ⟨p, rfl⟩ := hb.2 q
    obtain ⟨z, rfl⟩ := hsurj p
    exact ⟨z, rfl⟩
  · intro U
    rw [dom_comp]
    exact hopen _
  · intro U s
    rw [dom_comp]
    simp only [evalAt_comp]
    exact hdiff _ _


/-- A homomorphism of group models sends `ξ_𝒢` to `ξ_𝒩` (as in `Stalk.lean`). -/
theorem map_genericUnit' (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    f.left 𝒢.genericUnit = 𝒩.genericUnit := by
  have h : 𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
    have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
    exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this
  have h2 := congrArg (fun φ => φ (genericPt L)) h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h2

/-! ### Jacobian determinants along a generic isomorphism -/

/-- Restriction does not change values at points that land in the smaller open. -/
theorem evalAt_res (𝒢 : GroupModel A L) {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The point `Spec ℂ → Spec 𝓞_L` (through `τ`) is the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The unit complex point lands in every open containing `ξ`. -/
theorem one_mem_dom (𝒢 : GroupModel A L) (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- `Φ(0) = 1` for a homomorphism `Φ`. -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

/-- **The germ along `Φ ≫ f` of `t` agrees near `0` with the germ along `Φ` of `φ(t)`**, for any
map `φ : 𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}` compatible with `f^*` on sections (the stalk map of `f`). -/
theorem germAlong_comp_eventuallyEq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (φ : 𝒩.genStalk → 𝒢.genStalk)
    (hφ : ∀ (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
      (s : Γ(𝒩.G.left, U)), φ (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
        𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s))
    (t : 𝒩.genStalk) :
    𝒩.germAlong (fun z => Φ z ≫ f) t =ᶠ[nhds 0] 𝒢.germAlong Φ (φ t) := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒩.exists_rep t).choose
  set m := (𝒩.exists_rep t).choose_spec.choose
  set s := (𝒩.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒩.G.left.presheaf.germ U 𝒩.genericUnit m s = t :=
    (𝒩.exists_rep t).choose_spec.choose_spec.choose_spec
  have hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U := by
    show f.left 𝒢.genericUnit ∈ U
    rw [map_genericUnit' 𝒢 𝒩 f]; exact m
  set U' := (𝒢.exists_rep (φ t)).choose
  set m' := (𝒢.exists_rep (φ t)).choose_spec.choose
  set s' := (𝒢.exists_rep (φ t)).choose_spec.choose_spec.choose
  have hs' : 𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' = φ t :=
    (𝒢.exists_rep (φ t)).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s) =
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' := by
    rw [hs', ← hs, hφ U m hx' s]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hx' m' _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒩.evalAt (Φ z ≫ f) U s = 𝒢.evalAt (Φ z) U' s'
  rw [evalAt_comp, evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- **Jacobian determinants along a generic isomorphism** (proved): with `φ` as above,
`jacDet (Φ ≫ f) t = jacDet Φ (φ ∘ t)`. -/
theorem jacDet_comp_map (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (φ : 𝒩.genStalk → 𝒢.genStalk)
    (hφ : ∀ (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
      (s : Γ(𝒩.G.left, U)), φ (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
        𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s))
    (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk)
    (t' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (ht : ∀ i, (t' i : 𝒢.genStalk) = φ (t i)) :
    𝒩.jacDet (fun z => Φ z ≫ f) t = 𝒢.jacDet Φ t' := by
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [(germAlong_comp_eventuallyEq 𝒢 𝒩 f Λ Φ hΦ φ hφ (t i)).fderiv_eq, ht i]

/-- The comparison `𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}` along a homomorphism `f` (`f(ξ_𝒢) = ξ_𝒩`). -/
noncomputable def genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒩.genStalk ⟶ 𝒢.genStalk :=
  𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes ≫
    f.left.stalkMap 𝒢.genericUnit

/-- `genMap` is `f^*` on germs. -/
theorem genMap_germ (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
    (s : Γ(𝒩.G.left, U)) : (genMap 𝒢 𝒩 f) (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
      𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s) := by
  unfold genMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- **Jacobian determinants along a homomorphism**, with the stalk map (proved). -/
theorem jacDet_comp_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk)
    (t' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (ht : ∀ i, (t' i : 𝒢.genStalk) = genMap 𝒢 𝒩 f (t i)) :
    𝒩.jacDet (fun z => Φ z ≫ f) t = 𝒢.jacDet Φ t' :=
  jacDet_comp_map 𝒢 𝒩 f Λ Φ hΦ (genMap 𝒢 𝒩 f) (genMap_germ 𝒢 𝒩 f) t t' ht

/-! ### The induced map on cotangent spaces -/

theorem isIso_stalkSpecializes_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    IsIso (𝒩.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes) :=
  Iso.isIso_hom (𝒩.G.left.presheaf.stalkCongr (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).symm)

theorem genMap_mem_maximalIdeal (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (t : 𝒩.genStalk) (ht : t ∈ IsLocalRing.maximalIdeal 𝒩.genStalk) :
    genMap 𝒢 𝒩 f t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  haveI := isIso_stalkSpecializes_genMap 𝒢 𝒩 f
  set e := 𝒩.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes
  have h1 : e t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e).hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  have h2 := map_nonunit (f.left.stalkMap 𝒢.genericUnit).hom _ h1
  exact h2

/-- `genMap` is compatible with the structure maps from `𝓞_L`. -/
theorem genMap_structMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (r : 𝓞 L) :
    genMap 𝒢 𝒩 f (𝒩.structMap r) = 𝒢.structMap r := by
  have e1 : 𝒩.structMap r = 𝒩.G.left.presheaf.germ ⊤ 𝒩.genericUnit trivial
      (𝒩.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  rw [e1, e2, genMap_germ 𝒢 𝒩 f ⊤ (show 𝒩.genericUnit ∈ (⊤ : 𝒩.G.left.Opens) from trivial)
    (show 𝒢.genericUnit ∈ f.left ⁻¹ᵁ (⊤ : 𝒩.G.left.Opens) from trivial)]
  have hw : f.left ≫ 𝒩.G.hom = 𝒢.G.hom := Over.w f
  have : 𝒢.G.hom.appTop = 𝒩.G.hom.appTop ≫ f.left.appTop := by
    rw [← hw, Scheme.Hom.comp_appTop]
  rw [this, CommRingCat.comp_apply]
  rfl

/-- **The induced `𝓞_L`-linear map `ω_{𝒩_L} → ω_{𝒢_L}` on cotangent spaces at `ξ`** (`f^*`). -/
noncomputable def cotMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒩.cotangent →ₗ[𝓞 L] 𝒢.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
    (IsLocalRing.maximalIdeal 𝒢.genStalk) (genMap 𝒢 𝒩 f).hom.toIntAlgHom
    (fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (genMap 𝒢 𝒩 f).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒩.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢.genStalk).comap ψ :=
      fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
        (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (𝒩.structMap r • Ideal.toCotangent _ m) =
      𝒢.structMap r • Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
        (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [genMap_structMap]

theorem cotMap_dCls (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (t : IsLocalRing.maximalIdeal 𝒩.genStalk) :
    cotMap 𝒢 𝒩 f (𝒩.dCls t) =
      𝒢.dCls ⟨genMap 𝒢 𝒩 f t, genMap_mem_maximalIdeal 𝒢 𝒩 f t t.2⟩ := rfl

/-! ### `f^*` maps `ω_𝒩` into `ω_𝒢` (step R1) -/

theorem stalkSpecializes_stalkSpecializes_apply {X : Scheme.{0}} {x y z : X} (h : x ⤳ y)
    (h' : y ⤳ z) (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem stalkSpecializes_self_apply {X : Scheme.{0}} {x : X} (h : x ⤳ x)
    (t : X.presheaf.stalk x) : X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem unitSection_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
  have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
  exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this

/-- At each point `s` of `Spec 𝓞_L`, `f^*` maps the local lattice `(ω_𝒩)_s` into `(ω_𝒢)_s`. -/
theorem cotMap_omegaAt (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (m : 𝒩.cotangent) (hm : m ∈ 𝒩.omegaAt s) :
    cotMap 𝒢 𝒩 f m ∈ 𝒢.omegaAt s := by
  have hE := unitSection_comp 𝒢 𝒩 f
  have hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ s) hE)
  let T := 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    set g' := f.left.stalkMap (𝒢.unitSection s) (T g)
    have hspec : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g' =
        genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.stalkSpecializes (𝒩.specializes_genericUnit s) g) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
      unfold genMap
      rw [CommRingCat.comp_apply]
      congr 1
      rw [stalkSpecializes_stalkSpecializes_apply, stalkSpecializes_stalkSpecializes_apply]
    have hker : g' ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
      rw [RingHom.mem_ker]
      have h1 := Scheme.Hom.stalkMap_comp 𝒢.unitSection f.left s
      have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s
      have h1' : (𝒢.unitSection.stalkMap s) g' = ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
        exact this.symm
      have h2' : ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) =
          (𝒩.unitSection.stalkMap s) ((𝒩.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
        exact this
      rw [h1', h2']
      have h4 : ∀ y : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s), y = g →
          (𝒩.unitSection.stalkMap s) y = 0 := by
        rintro y rfl; exact hg
      apply h4
      show 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes (T g) = g
      exact (stalkSpecializes_stalkSpecializes_apply _ _ g).trans (stalkSpecializes_self_apply _ g)
    have hmem' : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g' ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk := by
      rw [hspec]; exact genMap_mem_maximalIdeal 𝒢 𝒩 f _ hmem
    apply Submodule.subset_span
    refine ⟨g', hker, hmem', ?_⟩
    rw [cotMap_dCls]
    congr 1
    exact Subtype.ext hspec.symm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **Step R1: `f^* (ω_𝒩) ⊆ ω_𝒢`** (proved). -/
theorem cotMap_omega (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (m : 𝒩.cotangent)
    (hm : m ∈ 𝒩.omega) : cotMap 𝒢 𝒩 f m ∈ 𝒢.omega := by
  rw [GroupModel.omega, Submodule.mem_iInf] at hm ⊢
  exact fun s => cotMap_omegaAt 𝒢 𝒩 f s m (hm s)

/-! ### The map of Hodge lines (step R2, lattice part) -/

/-- `L ⊗ ⋀^g f^* : 𝒩.hodgeSpace g → 𝒢.hodgeSpace g`, `L`-linear. -/
noncomputable def hodgeMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ) :
    𝒩.hodgeSpace g →ₗ[L] 𝒢.hodgeSpace g :=
  (exteriorPower.map g (cotMap 𝒢 𝒩 f)).baseChange L

theorem hodgeMap_wedge (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ)
    (v : Fin g → 𝒩.cotangent) :
    hodgeMap 𝒢 𝒩 f g ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => cotMap 𝒢 𝒩 f (v i)) := by
  rw [hodgeMap, LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti]
  rfl

/-- **`L ⊗ ⋀^g f^*` maps `⋀^g ω_𝒩` into `⋀^g ω_𝒢`** (proved, from R1). -/
theorem hodgeMap_detLattice (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ)
    (x : 𝒩.hodgeSpace g) (hx : x ∈ 𝒩.detLattice g) : hodgeMap 𝒢 𝒩 f g x ∈ 𝒢.detLattice g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [hodgeMap_wedge]
    apply Submodule.subset_span
    exact ⟨fun i => ⟨cotMap 𝒢 𝒩 f (v i), cotMap_omega 𝒢 𝒩 f _ (v i).2⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul L r y, LinearMap.map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem hodgeMap_wedgeGerm (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] {g : ℕ}
    (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk) :
    hodgeMap 𝒢 𝒩 f g (𝒩.wedge t) =
      𝒢.wedge (fun i => ⟨genMap 𝒢 𝒩 f (t i), genMap_mem_maximalIdeal 𝒢 𝒩 f _ (t i).2⟩) := by
  unfold GroupModel.wedge
  rw [hodgeMap_wedge]
  rfl

/-! ### Assembly: `HeightAntitone` from two algebraic statements -/

section Assembly

variable {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
  [AddCommGroup V'] [Module L V'] [Module (𝓞 L) V'] [IsScalarTower (𝓞 L) L V']

omit [Algebra K L] in
/-- In a Hodge line, every nonzero lattice vector has finite index. -/
theorem secIndex_ne_zero_of_mem {g : ℕ} (D : HodgeData L g V) {v : V} (hv : v ∈ D.lattice)
    (hv0 : v ≠ 0) : secIndex D.lattice v ≠ 0 := by
  obtain ⟨s, hs, hs0, hsi⟩ := D.isLattice
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp D.finrank_eq_one v
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) c
  have hb0 : (b : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, zero_smul] at hc
    exact hv0 hc.symm
  have key : b • v = a • s := by
    rw [← hc, ← algebraMap_smul L b, smul_smul, ← algebraMap_smul L a]
    congr 1
    field_simp
  have h1 := secIndex_smul D.lattice hv hv0 b
  have h2 := secIndex_smul D.lattice hs hs0 a
  rw [key, h2] at h1
  intro h
  rw [h, mul_zero] at h1
  have hna : (Algebra.norm ℤ a).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0)
  exact mul_ne_zero hna hsi h1

omit [NumberField L] in
theorem map_span_singleton_toAddSubgroup (H : V' →ₗ[L] V) (v₀ : V') :
    (Submodule.span (𝓞 L) {v₀}).toAddSubgroup.map H.toAddMonoidHom =
      (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup := by
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
    LinearMap.toAddMonoidHom_coe]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by rw [← algebraMap_smul L c, ← algebraMap_smul L c, map_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • v₀, ⟨c, rfl⟩, by rw [← algebraMap_smul L c, ← algebraMap_smul L c, map_smul]⟩

omit [NumberField L] in
/-- Indices along an injective map into a lattice. -/
theorem secIndex_le_of_map (H : V' →ₗ[L] V) (hH : Function.Injective H)
    (Λ' : Submodule (𝓞 L) V') (Λ : Submodule (𝓞 L) V) (hle : ∀ x ∈ Λ', H x ∈ Λ) {v₀ : V'}
    (hv₀ : v₀ ∈ Λ') (hne : secIndex Λ (H v₀) ≠ 0) :
    secIndex Λ' v₀ ≠ 0 ∧ secIndex Λ' v₀ ≤ secIndex Λ (H v₀) := by
  have hinj : Function.Injective H.toAddMonoidHom := hH
  have e1 : secIndex Λ' v₀ = ((Submodule.span (𝓞 L) {v₀}).toAddSubgroup.map H.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.map H.toAddMonoidHom) :=
    (AddSubgroup.relIndex_map_map_of_injective _ _ hinj).symm
  rw [map_span_singleton_toAddSubgroup] at e1
  have hAB : (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup ≤ Λ'.toAddSubgroup.map H.toAddMonoidHom := by
    rw [← map_span_singleton_toAddSubgroup]
    exact AddSubgroup.map_mono (fun x hx => by
      simp only [Submodule.mem_toAddSubgroup] at hx ⊢
      exact (Submodule.span_le.mpr (by simpa using hv₀)) hx)
  have hBC : Λ'.toAddSubgroup.map H.toAddMonoidHom ≤ Λ.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hle y hy
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hAB hBC
  have hne' : secIndex Λ (H v₀) = (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup.relIndex
      Λ.toAddSubgroup := rfl
  rw [e1]
  have hmul' := hmul.trans hne'.symm
  exact ⟨left_ne_zero_of_mul (hmul'.symm ▸ hne), Nat.le_of_dvd (Nat.pos_of_ne_zero hne)
    (Dvd.intro _ hmul')⟩

omit [NumberField L] in
/-- Pull back Hodge data along an injective `L`-linear map onto a new lattice. -/
noncomputable def pullHodge {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) : HodgeData L g V' where
  lattice := Λ'
  finrank_eq_one := hfin
  isLattice := hlat
  periods := D.periods
  periods_discrete := D.periods_discrete
  periods_isZLattice := D.periods_isZLattice
  coeff τ := (D.coeff τ).comp H
  coeff_ne_zero τ := by
    obtain ⟨s, -, hs0, -⟩ := hlat
    intro h
    have h1 := LinearMap.congr_fun h s
    have hHs : H s ≠ 0 := fun h0 => hs0 (hH (h0.trans (map_zero H).symm))
    exact D.coeff_apply_ne_zero τ hHs h1

omit [Algebra K L] in
theorem modelHeight_pullHodge_le {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) (hle : ∀ x ∈ Λ', H x ∈ D.lattice) :
    (pullHodge D H hH Λ' hfin hlat).modelHeight ≤ D.modelHeight := by
  obtain ⟨v₀, hv₀, hv0, -⟩ := hlat
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hH (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem D (hle v₀ hv₀) hHv0
  obtain ⟨hpos, hle'⟩ := secIndex_le_of_map H hH Λ' D.lattice hle hv₀ hne
  rw [(pullHodge D H hH Λ' hfin _).modelHeight_eq hv₀ hv0,
    D.modelHeight_eq (hle v₀ hv₀) hHv0]
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  apply div_le_div_of_nonneg_right _ hd.le
  have : Real.log (secIndex Λ' v₀) ≤ Real.log (secIndex D.lattice (H v₀)) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpos) (by exact_mod_cast hle')
  show Real.log (secIndex Λ' v₀) - (1 / 2) * ∑ σ : L →+* ℂ,
      Real.log (torusMetricSq (D.periods σ) (D.coeff σ (H v₀))) ≤ _
  linarith

end Assembly

/-- **`L ⊗ ⋀^g f^*` is bijective for a generic isomorphism** (stated here; proved below as
`hodgeMapBijective`) (it is induced by the
ring isomorphism `genMap`, `stalkIso_of_genericIso`; STANDARD algebra). -/
def HodgeMapBijective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f], IsIso ((Over.pullback (jL L)).map f) →
    ∀ g : ℕ, Function.Bijective (hodgeMap 𝒢 𝒩 f g)

/-- **A Hodge line contains a nonzero lattice vector** (stated here; proved below as
`hodgeLatticeNonzero_of_omegaSpans omegaSpans`). If `hodgeSpace g` is an
`L`-line, then `⋀^g ω_𝒩 ≠ 0` (`ω_𝒩` spans `ω_{A_L}`: `OmegaSpans`, proved in hodge-lattice; then
the wedges of `ω_𝒩` span the line; STANDARD). -/
def HodgeLatticeNonzero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L) (g : ℕ), Module.finrank L (𝒩.hodgeSpace g) = 1 →
      ∃ v₀ ∈ 𝒩.detLattice g, v₀ ≠ 0

/-- **Glue (as in `Minimal.lean`)** -/
def HeightAntitone : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G), IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒩.height ≤ 𝒢.height

/-- **`HeightAntitone` from `HodgeMapBijective` and `HodgeLatticeNonzero`** (proved). -/
theorem heightAntitone_of (hb : HodgeMapBijective) (hn : HodgeLatticeNonzero) :
    HeightAntitone := by
  intro K _ A L _ _ _ 𝒢 𝒩 f hm hi
  haveI := hm
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
  subst hM
  have hbij := hb K A L M.model 𝒩 f hi g
  set H := hodgeMap M.model 𝒩 f g
  have hfin : Module.finrank L (𝒩.hodgeSpace g) = 1 :=
    (LinearEquiv.ofBijective H hbij).finrank_eq.trans M.hodge.finrank_eq_one
  obtain ⟨v₀, hv₀, hv0⟩ := hn K A L 𝒩 g hfin
  have hle : ∀ x ∈ 𝒩.detLattice g, H x ∈ M.hodge.lattice := fun x hx => by
    rw [M.lattice_eq]; exact hodgeMap_detLattice _ _ f g x hx
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hbij.1 (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem M.hodge (hle v₀ hv₀) hHv0
  have hlat : ∃ s ∈ 𝒩.detLattice g, s ≠ 0 ∧ secIndex (𝒩.detLattice g) s ≠ 0 :=
    ⟨v₀, hv₀, hv0, (secIndex_le_of_map H hbij.1 _ _ hle hv₀ hne).1⟩
  let M' : MetrizedModel A L g :=
    { model := 𝒩
      hodge := pullHodge M.hodge H hbij.1 (𝒩.detLattice g) hfin hlat
      lattice_eq := rfl
      arch := fun τ => by
        obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
        refine ⟨fun z => Φ z ≫ f, isAnalyticUniformization_comp _ _ f τ _ Φ hΦ, fun t => ?_⟩
        show M.hodge.coeff τ (H (𝒩.wedge t)) = _
        rw [hodgeMap_wedgeGerm, hc, jacDet_comp_genMap M.model 𝒩 f _ Φ hΦ t
          (fun i => ⟨genMap M.model 𝒩 f (t i), genMap_mem_maximalIdeal _ _ f _ (t i).2⟩)
          (fun i => rfl)] }
  calc (⨅ (g' : ℕ) (M'' : MetrizedModel A L g') (_ : M''.model = 𝒩),
        (M''.hodge.modelHeight : EReal)) ≤ (M'.hodge.modelHeight : EReal) :=
        iInf_le_of_le g (iInf_le_of_le M' (iInf_le_of_le rfl le_rfl))
    _ ≤ (M.hodge.modelHeight : EReal) :=
        EReal.coe_le_coe_iff.mpr (modelHeight_pullHodge_le M.hodge H hbij.1 _ hfin hlat hle)

/-! ### `HodgeMapBijective` (proved): local rings along a generic isomorphism

The lemmas below up to `genericFibreStalkIso` are copied verbatim from
`scratch/hodge-lattice/HodgeLattice.lean` §9-§10 (via `Stalk.lean`, with `toGeneric` renamed `jL`). -/

section StalkSec
open TensorProduct

/-! ### Copied from hodge-lattice §9 -/

/-- **(S')** The projection `X_L = X ×_{𝓞_L} L → X` induces isomorphisms on local rings. -/
def GenericFibreStalkIso : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (X : Over (Spec (CommRingCat.of (𝓞 L))))
    (x : (genericFibre L X).left), IsIso ((pullback.fst X.hom (jL L)).stalkMap x)

section
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem fst_genericFibre_unit :
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left ≫
      pullback.fst 𝒢.G.hom (jL L) = jL L ≫ 𝒢.unitSection := by
  let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  change (Functor.LaxMonoidal.ε (Over.pullback (jL L)) ≫
    (Over.pullback (jL L)).map η[𝒢.G]).left ≫ pullback.fst 𝒢.G.hom (jL L) = _
  rw [Over.comp_left, Category.assoc]
  have h1 : ((Over.pullback (jL L)).map η[𝒢.G]).left ≫
      pullback.fst 𝒢.G.hom (jL L) =
      pullback.fst _ (jL L) ≫ (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left := by
    simp
  rw [h1, ← Category.assoc]
  have h2 : (Functor.LaxMonoidal.ε (Over.pullback (jL L))).left ≫
      pullback.snd ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (jL L) = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε (Over.pullback (jL L)))
  have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
    (g := jL L)
  have hc' : pullback.fst ((𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) (jL L) =
      pullback.snd _ _ ≫ jL L := by
    rw [← hc]; exact (Category.comp_id _).symm
  rw [hc', ← Category.assoc, h2, Category.id_comp]
  rfl

omit [NumberField L] in
theorem toGeneric_pt [NumberField L] :
    (jL L) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) L) ⟨⊥, Ideal.isPrime_bot⟩ = _
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot, genericPt]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The identity `ξ_L` of the generic fibre. -/
noncomputable def genericFibreUnit : (genericFibre L 𝒢.G).left :=
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  (η[genericFibre L 𝒢.G] : 𝟙_ _ ⟶ genericFibre L 𝒢.G).left
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)

theorem fst_genericFibreUnit :
    pullback.fst 𝒢.G.hom (jL L) (genericFibreUnit 𝒢) = 𝒢.genericUnit := by
  have h := congrArg (fun φ => φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L))
    (fst_genericFibre_unit 𝒢)
  exact ((Scheme.Hom.comp_apply _ _ _).symm.trans h).trans
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => 𝒢.unitSection y) (toGeneric_pt (L := L))))

end

/-! ### Copied from hodge-lattice §10 -/

/-- Bijectivity of ring maps respects isomorphisms. -/
theorem bijective_respectsIso :
    RingHom.RespectsIso (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f) :=
  ⟨fun f e hf => e.bijective.comp hf, fun f e hf => hf.comp e.bijective⟩

local notation "Pb" => stalkwise (fun {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) =>
      Function.Bijective f)

/-- `Spec (A ⊗_R K) → Spec A` has bijective stalk maps when `K` is a localization of `R`. -/
theorem stalkwise_tensor_localization (R : Type) [CommRing R] (K : Type) [CommRing K]
    [Algebra R K] (M : Submonoid R) [IsLocalization M K] (A : Type) [CommRing A] [Algebra R A] :
    Pb (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] K)))) := by
  have := stalkwise_respectsIso bijective_respectsIso
  set M' := Algebra.algebraMapSubmonoid A M
  let e : A ⊗[R] K ≃ₐ[A] Localization M' := IsLocalization.algEquiv M' _ _
  have hfac : CommRingCat.ofHom (algebraMap A (A ⊗[R] K)) =
      CommRingCat.ofHom (algebraMap A (Localization M')) ≫
        CommRingCat.ofHom e.symm.toAlgHom.toRingHom := by
    ext a
    simp
  have : IsIso (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) :=
    ⟨⟨CommRingCat.ofHom e.toAlgHom.toRingHom,
      CommRingCat.hom_ext (RingHom.ext fun y => e.apply_symm_apply y),
      CommRingCat.hom_ext (RingHom.ext fun y => e.symm_apply_apply y)⟩⟩
  rw [hfac, Spec.map_comp]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  intro x
  have h := isIso_specMap_stalkMap_localization (CommRingCat.of A) M' x
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- On an affine chart: `Spec A ×_{𝓞_L} Spec L → Spec A` has bijective stalk maps. -/
theorem stalkwise_fst_toGeneric {L : Type} [Field L] [NumberField L] {A : CommRingCat}
    (g : Spec A ⟶ Spec (CommRingCat.of (𝓞 L))) : (Pb) (pullback.fst g (jL L)) := by
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  let φ := Spec.preimage g
  letI : Algebra (𝓞 L) A := φ.hom.toAlgebra
  have hg : g = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) A)) := by
    rw [← Spec.map_preimage g]; rfl
  have he2 : (pullback.congrHom hg rfl).hom ≫ pullback.fst _ _ = pullback.fst g (jL L) := by
    simp [pullback.congrHom]
  rw [← he2]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  rw [← pullbackSpecIso_hom_fst' (𝓞 L) A L]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_tensor_localization (𝓞 L) L (nonZeroDivisors (𝓞 L)) A

/-- **`GenericFibreStalkIso` holds**: base change along `Spec L → Spec 𝓞_L` does not change local
rings (Zariski-local on the target; on an affine chart it is `Spec (A ⊗_{𝓞_L} L) → Spec A`, a
localization). -/
theorem genericFibreStalkIso : GenericFibreStalkIso := by
  intro L _ _ X x
  have : (Pb).RespectsIso := stalkwise_respectsIso bijective_respectsIso
  have : IsZariskiLocalAtTarget (Pb) :=
    stalkwiseIsZariskiLocalAtTarget_of_respectsIso bijective_respectsIso
  suffices H : (Pb) (pullback.fst X.hom (jL L)) from
    (ConcreteCategory.isIso_iff_bijective _).mpr (H x)
  refine IsZariskiLocalAtTarget.of_openCover X.left.affineOpenCover.openCover ?_
  intro i
  show (Pb) (pullback.snd (pullback.fst X.hom (jL L)) (X.left.affineOpenCover.f i))
  have he : (pullbackSymmetry (pullback.fst X.hom (jL L)) (X.left.affineOpenCover.f i) ≪≫
      pullbackRightPullbackFstIso X.hom (jL L) (X.left.affineOpenCover.f i)).hom ≫
        pullback.fst (X.left.affineOpenCover.f i ≫ X.hom) (jL L) =
      pullback.snd (pullback.fst X.hom (jL L)) (X.left.affineOpenCover.f i) := by
    simp
  rw [← he]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  exact stalkwise_fst_toGeneric _



section NewStalk
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **A generic isomorphism induces an isomorphism of local rings at `ξ`.** -/
theorem stalkIso_of_genericIso (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [hF : IsIso ((Over.pullback (jL L)).map f)] :
    IsIso (f.left.stalkMap 𝒢.genericUnit) := by
  have hsq : pullback.fst 𝒢.G.hom (jL L) ≫ f.left =
      ((Over.pullback (jL L)).map f).left ≫ pullback.fst 𝒩.G.hom (jL L) := by
    simp
  haveI : IsIso ((Over.pullback (jL L)).map f).left := by
    have := Functor.map_isIso (Over.forget _) ((Over.pullback (jL L)).map f)
    exact this
  haveI : IsIso (((Over.pullback (jL L)).map f).left.stalkMap (genericFibreUnit 𝒢)) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  haveI : IsIso ((pullback.fst 𝒢.G.hom (jL L)).stalkMap (genericFibreUnit 𝒢)) :=
    genericFibreStalkIso L 𝒢.G _
  haveI : IsIso ((pullback.fst 𝒩.G.hom (jL L)).stalkMap
      (((Over.pullback (jL L)).map f).left (genericFibreUnit 𝒢))) :=
    genericFibreStalkIso L 𝒩.G _
  have h1 := Scheme.Hom.stalkMap_comp (pullback.fst 𝒢.G.hom (jL L)) f.left
    (genericFibreUnit 𝒢)
  have h2 := Scheme.Hom.stalkMap_comp ((Over.pullback (jL L)).map f).left
    (pullback.fst 𝒩.G.hom (jL L)) (genericFibreUnit 𝒢)
  have h3 := Scheme.Hom.stalkMap_congr_hom _ _ hsq (genericFibreUnit 𝒢)
  have hc : IsIso ((pullback.fst 𝒢.G.hom (jL L) ≫ f.left).stalkMap (genericFibreUnit 𝒢)) := by
    rw [h3, h2]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) ?_
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›
  haveI : IsIso (f.left.stalkMap ((pullback.fst 𝒢.G.hom (jL L)) (genericFibreUnit 𝒢)) ≫
      (pullback.fst 𝒢.G.hom (jL L)).stalkMap (genericFibreUnit 𝒢)) := by
    rw [← h1]; exact hc
  haveI := IsIso.of_isIso_comp_right
    (f.left.stalkMap ((pullback.fst 𝒢.G.hom (jL L)) (genericFibreUnit 𝒢)))
    ((pullback.fst 𝒢.G.hom (jL L)).stalkMap (genericFibreUnit 𝒢))
  rw [← fst_genericFibreUnit 𝒢]
  infer_instance

end NewStalk

end StalkSec

/-- `genMap` is an isomorphism for a generic isomorphism. -/
theorem isIso_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] : IsIso (genMap 𝒢 𝒩 f) := by
  haveI := isIso_stalkSpecializes_genMap 𝒢 𝒩 f
  haveI := stalkIso_of_genericIso 𝒢 𝒩 f
  unfold genMap
  infer_instance

/-- `f^*` on cotangent spaces is bijective for a generic isomorphism. -/
theorem cotMap_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] : Function.Bijective (cotMap 𝒢 𝒩 f) := by
  haveI := isIso_genMap 𝒢 𝒩 f
  let e : 𝒩.genStalk ≃+* 𝒢.genStalk := (asIso (genMap 𝒢 𝒩 f)).commRingCatIsoToRingEquiv
  have he : ∀ x, e x = genMap 𝒢 𝒩 f x := fun x => rfl
  have hmax : ∀ x, x ∈ IsLocalRing.maximalIdeal 𝒩.genStalk ↔
      e x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    intro x
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff e x).symm
  have hcomap : (IsLocalRing.maximalIdeal 𝒢.genStalk).comap e =
      IsLocalRing.maximalIdeal 𝒩.genStalk := by
    ext x; exact (hmax x).symm
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    have h0 := hx
    change Ideal.toCotangent _ ⟨genMap 𝒢 𝒩 f m, _⟩ = 0 at h0
    rw [Ideal.toCotangent_eq_zero] at h0
    change (IsLocalRing.maximalIdeal 𝒩.genStalk).toCotangent m =
      (0 : (IsLocalRing.maximalIdeal 𝒩.genStalk).Cotangent)
    rw [Ideal.toCotangent_eq_zero]
    have h1 : (m : 𝒩.genStalk) ∈ ((IsLocalRing.maximalIdeal 𝒢.genStalk) ^ 2).comap e := by
      rw [Ideal.mem_comap, he]; exact h0
    rw [← Ideal.map_symm, Ideal.map_pow, Ideal.map_symm, hcomap] at h1
    exact h1
  · intro y
    obtain ⟨m', rfl⟩ := Ideal.toCotangent_surjective _ y
    have hm : e.symm m' ∈ IsLocalRing.maximalIdeal 𝒩.genStalk := by
      rw [hmax, RingEquiv.apply_symm_apply]; exact m'.2
    refine ⟨Ideal.toCotangent _ ⟨e.symm m', hm⟩, ?_⟩
    change Ideal.toCotangent _ ⟨genMap 𝒢 𝒩 f (e.symm m'), _⟩ = _
    congr 1
    apply Subtype.ext
    show e (e.symm m') = m'
    exact RingEquiv.apply_symm_apply e m'

omit [NumberField L] in
/-- `L ⊗ ⋀^g φ` is bijective if `φ` is. -/
theorem baseChange_map_bijective {M N : Type*} [AddCommGroup M] [Module (𝓞 L) M] [AddCommGroup N]
    [Module (𝓞 L) N] (g : ℕ) (φ : M →ₗ[𝓞 L] N) (hφ : Function.Bijective φ) :
    Function.Bijective ((exteriorPower.map g φ).baseChange L) := by
  let e := LinearEquiv.ofBijective φ hφ
  let ψ := (exteriorPower.map g (e.symm : N →ₗ[𝓞 L] M)).baseChange L
  have h1 : ψ ∘ₗ (exteriorPower.map g φ).baseChange L = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, ← exteriorPower.map_comp]
    have : (e.symm : N →ₗ[𝓞 L] M) ∘ₗ φ = LinearMap.id := by
      ext x; exact e.symm_apply_apply x
    rw [this, exteriorPower.map_id, LinearMap.baseChange_id]
  have h2 : (exteriorPower.map g φ).baseChange L ∘ₗ ψ = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, ← exteriorPower.map_comp]
    have : φ ∘ₗ (e.symm : N →ₗ[𝓞 L] M) = LinearMap.id := by
      ext x; exact e.apply_symm_apply x
    rw [this, exteriorPower.map_id, LinearMap.baseChange_id]
  refine Function.bijective_iff_has_inverse.mpr ⟨ψ, fun x => ?_, fun x => ?_⟩
  · exact LinearMap.congr_fun h1 x
  · exact LinearMap.congr_fun h2 x

/-- **Glue `HodgeMapBijective`, proved.** -/
theorem hodgeMapBijective : HodgeMapBijective := by
  intro K _ A L _ _ _ 𝒢 𝒩 f _ hi g
  exact baseChange_map_bijective g _ (cotMap_bijective 𝒢 𝒩 f)

/-- **`HeightAntitone` from `HodgeLatticeNonzero` alone** (proved). -/
theorem heightAntitone_of_hodgeLatticeNonzero (hn : HodgeLatticeNonzero) : HeightAntitone :=
  heightAntitone_of hodgeMapBijective hn

/-! ### `HodgeLatticeNonzero` from `OmegaSpans` (proved; `OmegaSpans` is proved in hodge-lattice) -/

/-- (copied verbatim from `scratch/hodge-lattice/HodgeLattice.lean` §2, where it is proved as
`omegaSpans_of_omegaLocal omegaLocal`) `ω_𝒢` spans `ω_{A_L}` over `L`. -/
def OmegaSpans : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L),
    Submodule.span L (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤

/-- Every cotangent vector has a nonzero `𝓞_L`-multiple in `ω`. -/
theorem exists_smul_mem_omega (h : OmegaSpans) (𝒩 : GroupModel A L) (x : 𝒩.cotangent) :
    ∃ D : 𝓞 L, D ≠ 0 ∧ D • x ∈ 𝒩.omega := by
  have hx : (1 : L) ⊗ₜ[𝓞 L] x ∈ Submodule.span L
      (Set.range fun w : 𝒩.omega => (1 : L) ⊗ₜ[𝓞 L] (w : 𝒩.cotangent)) := by
    rw [h K A L 𝒩]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 L)) c.support c
  choose a ha using fun w (hw : w ∈ c.support) => hd w hw
  set y : 𝒩.cotangent := ∑ w ∈ c.support.attach, a w.1 w.2 • (w.1 : 𝒩.cotangent) with hy_def
  have hy : y ∈ 𝒩.omega := Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ w.1.2
  have key : (TensorProduct.mk (𝓞 L) L 𝒩.cotangent 1) ((d : 𝓞 L) • x) =
      TensorProduct.mk (𝓞 L) L 𝒩.cotangent 1 y := by
    simp only [TensorProduct.mk_apply, hy_def, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    rw [← hc, Finsupp.sum, Finset.smul_sum, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun w _ => ?_
    symm
    rw [← algebraMap_smul L (a w.1 w.2), ha w.1 w.2, smul_assoc]
  have : IsLocalizedModule (nonZeroDivisors (𝓞 L)) (TensorProduct.mk (𝓞 L) L 𝒩.cotangent 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L _).mpr
      (TensorProduct.isBaseChange _ _ _)
  obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 L)) key
  refine ⟨(e : 𝓞 L) * d, mul_ne_zero (nonZeroDivisors.ne_zero e.2)
    (nonZeroDivisors.ne_zero d.2), ?_⟩
  have he' : (e : 𝓞 L) • ((d : 𝓞 L) • x) = (e : 𝓞 L) • y := he
  rw [mul_smul, he']
  exact Submodule.smul_mem _ _ hy

/-- **`HodgeLatticeNonzero` from `OmegaSpans`** (proved). -/
theorem hodgeLatticeNonzero_of_omegaSpans (h : OmegaSpans) : HodgeLatticeNonzero := by
  intro K _ A L _ _ _ 𝒩 g hfin
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hpure : ∀ v : Fin g → 𝒩.cotangent,
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v = 0 := by
    intro v
    choose D hD hDm using fun i => exists_smul_mem_omega h 𝒩 (v i)
    have h1 : exteriorPower.ιMulti (𝓞 L) g (fun i => D i • v i) =
        (∏ i, D i) • exteriorPower.ιMulti (𝓞 L) g v :=
      MultilinearMap.map_smul_univ _ _ _
    have h2 : (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => D i • v i) = 0 :=
      hcon _ (Submodule.subset_span ⟨fun i => ⟨D i • v i, hDm i⟩, rfl⟩)
    rw [h1, TensorProduct.tmul_smul, ← algebraMap_smul L] at h2
    have hP : algebraMap (𝓞 L) L (∏ i, D i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr
        (Finset.prod_ne_zero_iff.mpr fun i _ => hD i)
    calc (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v
        = (algebraMap (𝓞 L) L (∏ i, D i))⁻¹ • (algebraMap (𝓞 L) L (∏ i, D i) •
          ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v)) := by
          rw [smul_smul, inv_mul_cancel₀ hP, one_smul]
      _ = 0 := by rw [h2, smul_zero]
  have hall : ∀ x : 𝒩.hodgeSpace g, x = 0 := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l y =>
      have hy : y ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨v, rfl⟩ := hz
        have : l ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v =
            l • ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, hpure, smul_zero]
      | zero => rw [TensorProduct.tmul_zero]
      | add a b _ _ ha hb => rw [TensorProduct.tmul_add, ha, hb, add_zero]
      | smul r a _ ha => rw [TensorProduct.tmul_smul, ha, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (𝒩.hodgeSpace g) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  rw [Module.finrank_zero_of_subsingleton] at hfin
  exact zero_ne_one hfin

/-- **`HeightAntitone` from `OmegaSpans`** (proved; `OmegaSpans` is a theorem of hodge-lattice). -/
theorem heightAntitone_of_omegaSpans (h : OmegaSpans) : HeightAntitone :=
  heightAntitone_of_hodgeLatticeNonzero (hodgeLatticeNonzero_of_omegaSpans h)


/-! ### The Néron comparison map (from `Minimal.lean`) -/

section Abstract

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor that is injective on `Hom(𝟙, Y)` and `Hom(X ⊗ X, Y)` reflects
monoid morphisms `X → Y`. -/
theorem isMonHom_of_map {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)]
    (h1 : ∀ g g' : 𝟙_ C ⟶ Y, F.map g = F.map g' → g = g')
    (h2 : ∀ g g' : X ⊗ X ⟶ Y, F.map g = F.map g' → g = g') : IsMonHom f where
  one_hom := by
    apply h1
    rw [← cancel_epi (Functor.LaxMonoidal.ε F), F.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (f := F.map f)
  mul_hom := by
    apply h2
    rw [← cancel_epi (Functor.LaxMonoidal.μ F X X), F.map_comp, ← Category.assoc]
    have hm := IsMonHom.mul_hom (f := F.map f)
    refine hm.trans ?_
    rw [F.map_comp, Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc]

end Abstract

section Neron

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

instance smooth_tensor (𝒢 : GroupModel A L) : Smooth (𝒢.G ⊗ 𝒢.G).hom := by
  show Smooth (pullback.fst 𝒢.G.hom 𝒢.G.hom ≫ 𝒢.G.hom); infer_instance

instance smooth_unit : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom := by
  dsimp; infer_instance

/-- The comparison map `𝒢 → 𝒩` to a Néron model (unique with `F(f) ≫ gen_𝒩 = gen_𝒢`). -/
theorem neron_lift {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) :
    ∃ f : 𝒢.G ⟶ 𝒩.G, (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom :=
  (h𝒩 𝒢.G).2 𝒢.gen.hom

/-- Injectivity of `F = Over.pullback (jL L)` on maps from a smooth scheme into a Néron model. -/
theorem neron_map_injective {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    {Y : Over (Spec (CommRingCat.of (𝓞 L)))} [Smooth Y.hom] (g g' : Y ⟶ 𝒩.G)
    (h : (Over.pullback (jL L)).map g = (Over.pullback (jL L)).map g') : g = g' :=
  (h𝒩 Y).1 (by simp only [h])

/-- **The Néron comparison map is a homomorphism of group schemes**, and an isomorphism on
generic fibres. -/
theorem neron_lift_isMonHom {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    (hf : (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom) :
    IsMonHom f ∧ IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  let e₂ : F.obj 𝒩.G ≅ (A.baseChange L).X := 𝒩.gen
  have g1 : IsMonHom e₁.hom := 𝒢.gen_hom
  have g2 : IsMonHom e₂.hom := 𝒩.gen_hom
  have hiso : F.map f = e₁.hom ≫ e₂.inv := by
    rw [Iso.eq_comp_inv]; exact hf
  refine ⟨?_, by rw [hiso]; infer_instance⟩
  have : IsMonHom (F.map f) := by rw [hiso]; infer_instance
  exact isMonHom_of_map F f (fun g g' => neron_map_injective h𝒩 g g')
    (fun g g' => neron_map_injective h𝒩 g g')

/-- **`NeronModelMinimal` from `HeightAntitone`.** -/
theorem neronModelMinimal_of_heightAntitone (h : HeightAntitone) : NeronModelMinimal := by
  intro K _ A L _ _ _ 𝒩 𝒢 h𝒩
  obtain ⟨f, hf⟩ := neron_lift h𝒩 𝒢
  obtain ⟨hm, hi⟩ := neron_lift_isMonHom h𝒩 𝒢 f hf
  exact h K A L 𝒢 𝒩 f hm hi

end Neron


/-! ### Final -/

/-- `OmegaSpans` (hodge-lattice's theorem). -/
theorem omegaSpans : OmegaSpans :=
  HodgeLattice.omegaSpans_of_omegaLocal HodgeLattice.omegaLocal

/-- **Glue `HeightAntitone`, proved.** A homomorphism of group models that is an isomorphism on
generic fibres does not increase the height. -/
theorem heightAntitone : HeightAntitone := heightAntitone_of_omegaSpans omegaSpans

/-- **`NeronModelMinimal`, proved.** Over every `L`, a Néron model has the least height among the
group models of `A_L`. -/
theorem neronModelMinimal : NeronModelMinimal :=
  neronModelMinimal_of_heightAntitone heightAntitone


/-! ## Part 3 -/
/-! ## §1 Base change of group models -/



/-- (copied from h5-neron) -/
def IsBaseChangeOf {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) : Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

/-- (copied from h5-neron) **Glue H4b.** -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

section Abstract

variable {S S' T T' B : Scheme.{0}}

/-- `(f ≫ g)^* G → f^* g^* G`, with the iterated target type. (copied from h5-neron) -/
noncomputable def pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ⟶ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  (Over.pullbackComp f g).hom.app G

/-- `f^* g^* G → (f ≫ g)^* G`. (copied from h5-neron) -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

/-- (copied from h5-neron) -/
theorem isMonHom_pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompHom f g G) := by
  have h := ((Functor.mapMonNatIso (Over.pullbackComp f g)).hom.app (Mon.mk G) ≫
    (Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).hom.app
      (Mon.mk G)).isMonHom_hom
  have e : pbCompHom f g G = pbCompHom f g G ≫ 𝟙 _ := (Category.comp_id _).symm
  rw [e]
  exact h

/-- (copied from h5-neron) -/
theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

/-- `(f ≫ g)^* G ≅ f^* g^* G` with explicit components. (copied from h5-neron) -/
noncomputable def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  ⟨pbCompHom f g G, pbCompInv f g G, ((Over.pullbackComp f g).app G).hom_inv_id,
    ((Over.pullbackComp f g).app G).inv_hom_id⟩

/-- `f^* G ≅ g^* G` for `f = g`. -/
noncomputable def pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (Over.pullback f).obj G ≅ (Over.pullback g).obj G :=
  eqToIso (by subst h; rfl)

theorem isMonHom_pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y)
    [MonObj G] : IsMonHom (pbEqIso h G).hom := by
  subst h
  exact (inferInstance : IsMonHom (𝟙 ((Over.pullback f).obj G)))

/-- The generic-fibre identification of a base change, for abstract morphisms:
`a^* b^* G ≅ (a ≫ b)^* G = (c ≫ d)^* G ≅ c^* d^* G ≅ c^* k^* X ≅ (c ≫ k)^* X = k'^* X`. -/
noncomputable def genBC (a : T' ⟶ S') (b : S' ⟶ S) (c : T' ⟶ T) (d : T ⟶ S) (k : T ⟶ B)
    (k' : T' ⟶ B) (h1 : a ≫ b = c ≫ d) (h2 : c ≫ k = k') (G : Over S) (X : Over B)
    (gen : (Over.pullback d).obj G ≅ (Over.pullback k).obj X) :
    (Over.pullback a).obj ((Over.pullback b).obj G) ≅ (Over.pullback k').obj X :=
  (pbCompIso a b G).symm ≪≫ pbEqIso h1 G ≪≫ pbCompIso c d G ≪≫
    (Over.pullback c).mapIso gen ≪≫ (pbCompIso c k X).symm ≪≫ pbEqIso h2 X

theorem genBC_isMonHom (a : T' ⟶ S') (b : S' ⟶ S) (c : T' ⟶ T) (d : T ⟶ S) (k : T ⟶ B)
    (k' : T' ⟶ B) (h1 : a ≫ b = c ≫ d) (h2 : c ≫ k = k') (G : Over S) [GrpObj G] (X : Over B)
    [GrpObj X] (gen : (Over.pullback d).obj G ≅ (Over.pullback k).obj X)
    (hgen : letI : GrpObj ((Over.pullback d).obj G) := Functor.grpObjObj
      letI : GrpObj ((Over.pullback k).obj X) := Functor.grpObjObj
      IsMonHom gen.hom) :
    letI : GrpObj ((Over.pullback b).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback a).obj ((Over.pullback b).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback k').obj X) := Functor.grpObjObj
    IsMonHom (genBC a b c d k k' h1 h2 G X gen).hom := by
  have c1 := isMonHom_pbCompInv a b G
  have c2 := isMonHom_pbEqIso h1 G
  have c3 := isMonHom_pbCompHom c d G
  have c5 := isMonHom_pbCompInv c k X
  have c6 := isMonHom_pbEqIso h2 X
  have c4 : IsMonHom ((Over.pullback c).map gen.hom) := inferInstance
  have e : (genBC a b c d k k' h1 h2 G X gen).hom = pbCompInv a b G ≫ (pbEqIso h1 G).hom ≫
      pbCompHom c d G ≫ (Over.pullback c).map gen.hom ≫ pbCompInv c k X ≫ (pbEqIso h2 X).hom :=
    rfl
  rw [e]
  infer_instance

end Abstract

section Concrete

variable {K : Type} [Field K] (L L' : Type) [Field L] [Algebra K L]
    [Field L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']

theorem square1 :
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))) =
      Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem square2 :
    Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable [NumberField L] [NumberField L']

/-- The base change `𝒢 ×_{𝓞_L} 𝓞_{L'}` of a group model, as a group model of `A_{L'}`. -/
noncomputable def GroupModel.baseChange {A : AbVar K} (𝒢 : GroupModel A L) : GroupModel A L' :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  { G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G
    gen := genBC _ _ _ _ _ _ (square1 L L') (square2 L L') 𝒢.G A.X 𝒢.gen
    gen_hom := genBC_isMonHom _ _ _ _ _ _ (square1 L L') (square2 L L') 𝒢.G A.X 𝒢.gen
      𝒢.gen_hom }

/-- **Glue H4b, proved.** -/
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  refine ⟨GroupModel.baseChange L L' 𝒢, Iso.refl (GroupModel.baseChange L L' 𝒢).G, ?_⟩
  exact (inferInstance : IsMonHom (𝟙 (GroupModel.baseChange L L' 𝒢).G))

end Concrete


/-! ## §3 Open subgroup models are generic isomorphisms -/

section OpenSubSec



variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]


/-- The base change of an open immersion along any `j` is an open immersion (for `Over.pullback`). -/
theorem isOpenImmersion_pullback_map {S S' : Scheme.{0}} (j : S' ⟶ S) {U G : Over S} (f : U ⟶ G)
    [IsOpenImmersion f.left] : IsOpenImmersion ((Over.pullback j).map f).left := by
  have t : IsPullback (pullback.fst G.hom j) (pullback.snd G.hom j) G.hom j :=
    IsPullback.of_hasPullback _ _
  have p : pullback.fst U.hom j ≫ f.left = ((Over.pullback j).map f).left ≫ pullback.fst G.hom j := by
    simp
  have s : IsPullback (pullback.fst U.hom j) (((Over.pullback j).map f).left ≫ pullback.snd G.hom j)
      (f.left ≫ G.hom) j := by
    have e1 : ((Over.pullback j).map f).left ≫ pullback.snd G.hom j = pullback.snd U.hom j := by
      simp
    have e2 : f.left ≫ G.hom = U.hom := Over.w f
    rw [e1, e2]
    exact IsPullback.of_hasPullback _ _
  have sq := IsPullback.of_bot s p t
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›

/-- An open immersion `h : X → X` over `Spec L` of an abelian variety is an isomorphism. -/
theorem isIso_of_openImmersion_self (B : AbVar L) (h : B.X ⟶ B.X) [IsOpenImmersion h.left] :
    IsIso h := by
  have hw : h.left ≫ B.X.hom = B.X.hom := Over.w h
  haveI : UniversallyClosed (h.left ≫ B.X.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed h.left := UniversallyClosed.of_comp_of_isSeparated h.left B.X.hom
  haveI : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
  have hrange : Set.range h.left = Set.univ := by
    have hc : IsClosed (Set.range h.left) := h.left.isClosedMap.isClosed_range
    have ho : IsOpen (Set.range h.left) := h.left.isOpenEmbedding.isOpen_range
    obtain ⟨x⟩ := (inferInstance : Nonempty B.X.left)
    exact IsClopen.eq_univ ⟨hc, ho⟩ ⟨h.left x, x, rfl⟩
  haveI : Surjective h.left := ⟨fun y => by
    have : y ∈ Set.range h.left := hrange ▸ Set.mem_univ y
    exact this⟩
  haveI : IsIso h.left := (isIso_iff_isOpenImmersion_and_surjective h.left).mpr ⟨‹_›, ‹_›⟩
  haveI : IsIso ((Over.forget _).map h) := inferInstanceAs (IsIso h.left)
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **Open subgroup models agree generically** (proved). -/
theorem genericIso_of_openImmersion (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G)
    [IsOpenImmersion f.left] : IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒰.G ≅ (A.baseChange L).X := 𝒰.gen
  let e₂ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  haveI : IsOpenImmersion (F.map f).left := isOpenImmersion_pullback_map (jL L) f
  let h : (A.baseChange L).X ⟶ (A.baseChange L).X := e₁.inv ≫ F.map f ≫ e₂.hom
  haveI : IsIso e₁.inv.left := Functor.map_isIso (Over.forget _) e₁.inv
  haveI : IsIso e₂.hom.left := Functor.map_isIso (Over.forget _) e₂.hom
  haveI : IsOpenImmersion h.left := by
    show IsOpenImmersion (e₁.inv.left ≫ (F.map f).left ≫ e₂.hom.left)
    infer_instance
  haveI := isIso_of_openImmersion_self (A.baseChange L) h
  have : F.map f = e₁.hom ≫ h ≫ e₂.inv := by
    simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance


end OpenSubSec


section Red
/-! ## §5 Copied statements (verbatim from `scratch/h5-neron/H5Neron.lean`) and the reduction -/

section Reduction

variable {K : Type} [Field K] {A : AbVar K}

/-- `𝒰 → 𝒢` is an open immersion of group schemes over `𝓞_L`. -/
def IsOpenSubgroupModel {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) : Prop :=
  ∃ f : 𝒰.G ⟶ 𝒢.G, IsOpenImmersion f.left ∧ IsMonHom f

/-- **Leaf N1 (Néron)**, as in `Reduction.lean` (BLR §1.4 Thm 3, UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

/-- **Leaf N2 (semistable reduction and base change of the identity component).** For `A` over
a number field `K` there are a finite extension `L₀/K` and a Néron model `𝒩₀` over `𝓞_{L₀}` such
that for every finite extension `L'/L₀` and every Néron model `𝒩'` over `𝓞_{L'}`, there is a group
model `𝒰` (the identity component `𝒩'⁰`) that is an open subgroup both of `𝒩'` and of a base
change `𝒱` of `𝒩₀` (namely `𝒱 = 𝒩₀ ×_{𝓞_{L₀}} 𝓞_{L'}`, with `𝒰 = 𝒩₀⁰ ×_{𝓞_{L₀}} 𝓞_{L'}`).
Consequence of SGA 7 IX Thm 3.6 (Grothendieck's semistable reduction theorem: `A_{L₀}` is
semistable for some finite `L₀`) and SGA 7 IX Prop./Cor. 3.3 (in the semistable case
`(𝒩_{L'})⁰ = (𝒩⁰)_{L'}`), with the openness of the identity component (SGA 3 VI_B 3.10) and
the compatibility of Néron models with localization (BLR §1.2); all locators UNVERIFIED. -/
def SemistableNeronIdentityComponent : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
          IsOpenSubgroupModel 𝒰 𝒱

/-! ## Glue (stated; to be proved by the project) -/

/-- **Glue H4a.** The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

/-- **Glue M6.** An open subgroup model has the same height: an open immersion `𝒰 → 𝒢` of group
schemes induces isomorphisms of the local rings along the unit section (so the same `ω`) and a
group bijection on complex points (on generic fibres it is an open immersion from a proper
connected scheme, hence an isomorphism; it need not be compatible with the two `gen`). -/
def OpenSubgroupHeight : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L), IsOpenSubgroupModel 𝒰 𝒢 → 𝒰.height = 𝒢.height

/-- **The compositum.** Two number fields `L, L₀` over a number field `K` embed `K`-linearly in a
common number field `L'`. Proved (inside `AlgebraicClosure K`). -/
theorem compositum (K : Type) [Field K] [NumberField K] (L L₀ : Type) [Field L] [NumberField L]
    [Algebra K L] [Field L₀] [NumberField L₀] [Algebra K L₀] :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra K L') (_ : Algebra L L')
      (_ : Algebra L₀ L'), IsScalarTower K L L' ∧ IsScalarTower K L₀ L' := by
  let Ω := AlgebraicClosure K
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite K L₀ := Module.Finite.of_restrictScalars_finite ℚ K L₀
  let eL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eL₀ : L₀ →ₐ[K] Ω := IsAlgClosed.lift
  let E : IntermediateField K Ω := eL.fieldRange ⊔ eL₀.fieldRange
  haveI : FiniteDimensional K eL.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL).toLinearEquiv
  haveI : FiniteDimensional K eL₀.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL₀).toLinearEquiv
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
  haveI : NumberField E := ⟨⟩
  let f : L →ₐ[K] E := (IntermediateField.inclusion le_sup_left).comp
    (AlgEquiv.ofInjectiveField eL).toAlgHom
  let f₀ : L₀ →ₐ[K] E := (IntermediateField.inclusion le_sup_right).comp
    (AlgEquiv.ofInjectiveField eL₀).toAlgHom
  letI : Algebra L E := f.toRingHom.toAlgebra
  letI : Algebra L₀ E := f₀.toRingHom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  · exact IsScalarTower.of_algebraMap_eq fun x => (f₀.commutes x).symm


/-- **An open immersion of group models does not increase the height** (stated here; proved
below as `openImmersionHeightLe`). If
`f : 𝒰 → 𝒢` is a homomorphism of group models of `A_L` whose underlying morphism is an open
immersion (so, by `genericIso_of_openImmersion`, an isomorphism on generic fibres), then
`h(𝒰) ≤ h(𝒢)`: the unit section of `𝒢` factors through `𝒰` (`e_𝒢 = e_𝒰 ≫ f`), `f` induces
isomorphisms of local rings along it, so `ω_𝒰 = ω_𝒢`; complex points correspond bijectively
(`pts_comp_bijective`). -/
def OpenImmersionHeightLe : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G), IsOpenImmersion f.left → IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒰.height ≤ 𝒢.height

/-- **Glue M6 from `HeightAntitone` and `OpenImmersionHeightLe`** (the generic-isomorphism
clause is proved, `genericIso_of_openImmersion`). -/
theorem openSubgroupHeight_of (hA : HeightAntitone) (hO : OpenImmersionHeightLe) :
    OpenSubgroupHeight := by
  intro K _ A L _ _ _ 𝒰 𝒢 ⟨f, hf, hm⟩
  haveI := hf
  have hi := genericIso_of_openImmersion 𝒰 𝒢 f
  exact le_antisymm (hO K A L 𝒰 𝒢 f hf hm hi) (hA K A L 𝒰 𝒢 f hm hi)

/-- **H5 in the form R19-R21 need**, from the leaves N1, N2 and `OpenImmersionHeightLe`,
`ModelHeightBaseChange` (the former is proved below, giving `stableFaltingsHeight_eq_neron_all'`) (`NeronModelMinimal`,
`GroupModelBaseChangeExists` are theorems; `OpenSubgroupHeight` follows). Same conclusion as h5-neron's
`stableFaltingsHeight_eq_neron_all`. -/
theorem stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hO : OpenImmersionHeightLe)
    (hbc : ModelHeightBaseChange) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height := by
  have hmin := neronModelMinimal
  have hbcE := groupModelBaseChangeExists
  have hop := openSubgroupHeight_of heightAntitone hO
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hbase⟩ := hN2 K A
  have heq : stableFaltingsHeight A = 𝒩₀.height := by
    rw [stableFaltingsHeight_eq_iInf_height]
    refine le_antisymm (iInf_le_of_le (FinExt.mk L₀) (iInf_le_of_le 𝒩₀ le_rfl)) ?_
    refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    obtain ⟨L', j1, j2, j3, j4, j5, t1, t2⟩ := compositum K E.L L₀
    obtain ⟨𝒢', h𝒢'⟩ := hbcE K A E.L L' 𝒢
    obtain ⟨𝒩', h𝒩'⟩ := hN1 K A L'
    obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hbase L' 𝒩' h𝒩'
    calc 𝒩₀.height = 𝒱.height := (hbc K A L₀ L' 𝒩₀ 𝒱 h𝒱).symm
      _ = 𝒰.height := (hop K A L' 𝒰 𝒱 h𝒰𝒱).symm
      _ = 𝒩'.height := hop K A L' 𝒰 𝒩' h𝒰𝒩
      _ ≤ 𝒢'.height := hmin K A L' 𝒩' 𝒢' h𝒩'
      _ = 𝒢.height := hbc K A E.L L' 𝒢 𝒢' h𝒢'
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, heq, ?_⟩
  intro L' j1 j2 j3 j4 j5 𝒩' h𝒩'
  obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hbase L' 𝒩' h𝒩'
  rw [heq, ← hbc K A L₀ L' 𝒩₀ 𝒱 h𝒱, ← hop K A L' 𝒰 𝒱 h𝒰𝒱, hop K A L' 𝒰 𝒩' h𝒰𝒩]

end Reduction

end Red

/-! ### Additivity -/

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

/-- The Néron mapping property of `N` (over `S`) for `A` (over `S'`) along `j`, tested on the
objects satisfying `P`. -/
def NeronProp (N : Over S) (A : Over S') (e : (Over.pullback j).obj N ≅ A) : Prop :=
  ∀ Y : Over S, P Y → Function.Bijective fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom

variable {j P}

/-- Existence and uniqueness of the extension. -/
theorem NeronProp.lift {N : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) {Y : Over S} (hY : P Y) (g : (Over.pullback j).obj Y ⟶ A) :
    ∃! f : Y ⟶ N, (Over.pullback j).map f ≫ e.hom = g := by
  obtain ⟨f, hf⟩ := (h Y hY).2 g
  exact ⟨f, hf, fun f' hf' => (h Y hY).1 (hf'.trans hf.symm)⟩

/-- **Uniqueness of Néron models**: two Néron models of `A` (each a test object) are isomorphic,
compatibly with the identifications of their generic fibres. -/
theorem NeronProp.uniqueIso {N N' : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    {e' : (Over.pullback j).obj N' ≅ A} (h : NeronProp j P N A e) (h' : NeronProp j P N' A e')
    (hN : P N) (hN' : P N') :
    ∃ φ : N ≅ N', (Over.pullback j).map φ.hom ≫ e'.hom = e.hom := by
  obtain ⟨f, hf⟩ := (h' N hN).2 e.hom
  obtain ⟨f', hf'⟩ := (h N' hN').2 e'.hom
  simp only at hf hf'
  have h1 : f ≫ f' = 𝟙 N := by
    apply (h N hN).1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  have h2 : f' ≫ f = 𝟙 N' := by
    apply (h' N' hN').1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  exact ⟨⟨f, f', h1, h2⟩, hf⟩

/-- The identification of the generic fibre of `N₁ ⊗ N₂` with `A₁ ⊗ A₂`. -/
noncomputable def tensorGen {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (Over.pullback j).obj (N₁ ⊗ N₂) ≅ A₁ ⊗ A₂ :=
  prodComparisonIso (Over.pullback j) N₁ N₂ ≪≫ tensorIso e₁ e₂

theorem tensorGen_fst {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ fst A₁ A₂ = (Over.pullback j).map (fst N₁ N₂) ≫ e₁.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_fst,
    CartesianMonoidalCategory.prodComparison_fst_assoc]

theorem tensorGen_snd {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ snd A₁ A₂ = (Over.pullback j).map (snd N₁ N₂) ≫ e₂.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_snd,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

/-- **A product of Néron models is a Néron model of the product.** -/
theorem NeronProp.tensor {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    {e₁ : (Over.pullback j).obj N₁ ≅ A₁} {e₂ : (Over.pullback j).obj N₂ ≅ A₂}
    (h₁ : NeronProp j P N₁ A₁ e₁) (h₂ : NeronProp j P N₂ A₂ e₂) :
    NeronProp j P (N₁ ⊗ N₂) (A₁ ⊗ A₂) (tensorGen e₁ e₂) := by
  intro Y hY
  have hfst : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      fst A₁ A₂ = (Over.pullback j).map (f ≫ fst N₁ N₂) ≫ e₁.hom := by
    intro f
    rw [Category.assoc, tensorGen_fst, Functor.map_comp, Category.assoc]
  have hsnd : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      snd A₁ A₂ = (Over.pullback j).map (f ≫ snd N₁ N₂) ≫ e₂.hom := by
    intro f
    rw [Category.assoc, tensorGen_snd, Functor.map_comp, Category.assoc]
  constructor
  · intro f f' hff'
    have a := hfst f
    have b := hfst f'
    have c := hsnd f
    have d := hsnd f'
    simp only at hff'
    rw [hff'] at a c
    apply CartesianMonoidalCategory.hom_ext
    · exact (h₁ Y hY).1 (a.symm.trans b)
    · exact (h₂ Y hY).1 (c.symm.trans d)
  · intro g
    obtain ⟨f₁, hf₁⟩ := (h₁ Y hY).2 (g ≫ fst A₁ A₂)
    obtain ⟨f₂, hf₂⟩ := (h₂ Y hY).2 (g ≫ snd A₁ A₂)
    refine ⟨CartesianMonoidalCategory.lift f₁ f₂, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [hfst, CartesianMonoidalCategory.lift_fst]; exact hf₁
    · rw [hsnd, CartesianMonoidalCategory.lift_snd]; exact hf₂

end General


section GroupModels2
variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
/-- The project's `IsNeronModel` is `NeronProp` for smooth test objects. -/
theorem GroupModel.isNeronModel_iff (𝒩 : GroupModel A L) :
    𝒩.IsNeronModel ↔ NeronProp (jL L) (fun Y => Smooth Y.hom) 𝒩.G (A.baseChange L).X 𝒩.gen :=
  ⟨fun h Y hY => @h Y hY, fun h Y hY => h Y hY⟩

end GroupModels2

section Transport

variable {S S' : Scheme.{0}} {j : S' ⟶ S} {P : Over S → Prop}

/-- The Néron property is invariant under isomorphisms of `N` and of `A`. -/
theorem NeronProp.of_iso {N N' : Over S} {A A' : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) (φ : N' ≅ N) (ψ : A ≅ A') (e' : (Over.pullback j).obj N' ≅ A')
    (he : (Over.pullback j).map φ.hom ≫ e.hom ≫ ψ.hom = e'.hom) : NeronProp j P N' A' e' := by
  intro Y hY
  have key : (fun f : Y ⟶ N' => (Over.pullback j).map f ≫ e'.hom) =
      (fun g => g ≫ ψ.hom) ∘ (fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom) ∘
        (fun f => f ≫ φ.hom) := by
    funext f
    simp only [Function.comp, Functor.map_comp, Category.assoc, ← he]
  rw [key]
  refine Function.Bijective.comp ?_ ((h Y hY).comp ?_)
  · exact ⟨fun a b hab => (cancel_mono ψ.hom).mp hab, fun c => ⟨c ≫ ψ.inv, by simp⟩⟩
  · exact ⟨fun a b hab => (cancel_mono φ.hom).mp hab, fun c => ⟨c ≫ φ.inv, by simp⟩⟩

end Transport

section Additivity

open NumberField DefFaltings

variable {K : Type} [Field K]

/-- `C ≅ A × B` as abelian varieties: an isomorphism `C ≅ A ⊗ B` of `K`-schemes whose two
components are homomorphisms. (Mathlib v4.35 cannot form `A × B` as an `AbVar`: it lacks the
stability of geometric integrality under composition; so the product enters as `C`.) -/
def IsProductAbVar (C A B : AbVar K) : Prop :=
  ∃ e : C.X ≅ A.X ⊗ B.X, IsMonHom (e.hom ≫ fst A.X B.X) ∧ IsMonHom (e.hom ≫ snd A.X B.X)

/-- `C_L ≅ A_L ⊗ B_L`. -/
noncomputable def bcProd {A B C : AbVar K} (L : Type) [Field L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) : (C.baseChange L).X ≅ (A.baseChange L).X ⊗ (B.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC ≪≫
    prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.X B.X

/-- `𝒢P ≅ 𝒢₁ × 𝒢₂` as group models of `C_L ≅ A_L × B_L`. -/
def IsProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) :
    Prop :=
  ∃ e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G, IsMonHom (e.hom ≫ fst _ _) ∧ IsMonHom (e.hom ≫ snd _ _) ∧
    (Over.pullback (jL L)).map e.hom ≫ (tensorGen 𝒢₁.gen 𝒢₂.gen).hom =
      𝒢P.gen.hom ≫ (bcProd L eC).hom

/-- **A product of Néron models is a Néron model** (for group models). -/
theorem isNeronModel_of_isProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] {eC : C.X ≅ A.X ⊗ B.X} {𝒢P : GroupModel C L} {𝒩₁ : GroupModel A L}
    {𝒩₂ : GroupModel B L} (h₁ : 𝒩₁.IsNeronModel) (h₂ : 𝒩₂.IsNeronModel)
    (hP : IsProductModel eC 𝒢P 𝒩₁ 𝒩₂) : 𝒢P.IsNeronModel := by
  obtain ⟨e, -, -, he⟩ := hP
  rw [GroupModel.isNeronModel_iff] at h₁ h₂ ⊢
  refine (h₁.tensor h₂).of_iso e (bcProd L eC).symm 𝒢P.gen ?_
  rw [← Category.assoc, he]
  erw [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- **Glue P1.** Group models of `A_L` and `B_L` give a group model of `C_L ≅ A_L × B_L`
(the fibre product over `𝓞_L`; smooth, separated, quasi-compact; `GrpObj` of a product). -/
def ProductGroupModelExists : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X),
    IsMonHom (eC.hom ≫ fst A.X B.X) → IsMonHom (eC.hom ≫ snd A.X B.X) →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (𝒢₁ : GroupModel A L)
      (𝒢₂ : GroupModel B L), ∃ 𝒢P : GroupModel C L, IsProductModel eC 𝒢P 𝒢₁ 𝒢₂

/-- **Glue P2** (the direction used). The height of a product model is at least the sum of the
heights: `ω_{𝒢₁×𝒢₂} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, the Arakelov degree is
additive, and a product of uniformizations is a uniformization of the product (equality holds). -/
def ProductModelHeight : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ → 𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height

/-- **`h(A) + h(B) ≤ h(A × B)`** (rv-blueprints F1, the direction step E4 uses) from Néron
existence, Néron minimality and the two product glue statements. No semistable reduction is
needed: the comparison is made over each `L` separately. -/
theorem stableFaltingsHeight_add_le (hN1 : NeronModelExists) (hmin : NeronModelMinimal)
    (hP : ProductGroupModelExists) (hH : ProductModelHeight) (A B C : AbVar K)
    (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C := by
  obtain ⟨eC, h1, h2⟩ := hC
  rw [stableFaltingsHeight_eq_iInf_height C]
  refine le_iInf fun E => le_iInf fun 𝒢 => ?_
  obtain ⟨𝒩₁, hN₁⟩ := hN1 K A E.L
  obtain ⟨𝒩₂, hN₂⟩ := hN1 K B E.L
  obtain ⟨𝒢P, h𝒢P⟩ := hP K A B C eC h1 h2 E.L 𝒩₁ 𝒩₂
  have hA : stableFaltingsHeight A ≤ 𝒩₁.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₁ le_rfl)
  have hB : stableFaltingsHeight B ≤ 𝒩₂.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₂ le_rfl)
  calc stableFaltingsHeight A + stableFaltingsHeight B ≤ 𝒩₁.height + 𝒩₂.height :=
        add_le_add hA hB
    _ ≤ 𝒢P.height := hH K A B C eC E.L 𝒢P 𝒩₁ 𝒩₂ h𝒢P
    _ ≤ 𝒢.height :=
        hmin K C E.L 𝒢P 𝒢 (isNeronModel_of_isProductModel hN₁ hN₂ h𝒢P)

end Additivity

section ProductProof

/-- `prodComparison` of a braided monoidal functor between cartesian categories is a monoid
morphism. -/
theorem isMonHom_prodComparisonIso {S S' : Scheme.{0}} (j : S' ⟶ S) (X Y : Over S) [GrpObj X]
    [GrpObj Y] :
    IsMonHom (prodComparisonIso (Over.pullback j) X Y).hom := by
  have h : (prodComparisonIso (Over.pullback j) X Y).hom =
      (Functor.Monoidal.μIso (Over.pullback j) X Y).inv := by
    rw [prodComparisonIso_hom, ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    rfl
  have h0 : IsMonHom (Functor.Monoidal.μIso (Over.pullback j) X Y).hom :=
    (inferInstance : IsMonHom (Functor.LaxMonoidal.μ (Over.pullback j) X Y))
  rw [h]
  infer_instance

/-- **Glue P1, proved.** -/
theorem productGroupModelExists : ProductGroupModelExists := by
  unfold ProductGroupModelExists
  intro K _ A B C eC h1 h2 L _ _ _ 𝒢₁ 𝒢₂
  haveI : Smooth (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show Smooth (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsSeparated (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show IsSeparated (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : QuasiCompact (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show QuasiCompact (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsMonHom eC.hom := by
    have : eC.hom = lift (eC.hom ≫ fst A.X B.X) (eC.hom ≫ snd A.X B.X) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this]; infer_instance
  let F := Over.pullback (jL L)
  let F' := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let gen : genericFibre L (𝒢₁.G ⊗ 𝒢₂.G) ≅ (C.baseChange L).X :=
    tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm
  have gen_hom : letI : GrpObj (genericFibre L (𝒢₁.G ⊗ 𝒢₂.G)) := Functor.grpObjObj
      IsMonHom gen.hom := by
    let g₁ : F.obj 𝒢₁.G ⟶ F'.obj A.X := 𝒢₁.gen.hom
    let g₂ : F.obj 𝒢₂.G ⟶ F'.obj B.X := 𝒢₂.gen.hom
    have g1 : IsMonHom g₁ := 𝒢₁.gen_hom
    have g2 : IsMonHom g₂ := 𝒢₂.gen_hom
    have p1 := isMonHom_prodComparisonIso (jL L) 𝒢₁.G 𝒢₂.G
    have p2 := isMonHom_prodComparisonIso (Spec.map (CommRingCat.ofHom (algebraMap K L))) A.X B.X
    have : IsMonHom ((prodComparisonIso F 𝒢₁.G 𝒢₂.G).hom ≫
        (g₁ ⊗ₘ g₂) ≫
        (prodComparisonIso F' A.X B.X).inv ≫ F'.map eC.inv) := inferInstance
    exact this
  refine ⟨⟨𝒢₁.G ⊗ 𝒢₂.G, gen, gen_hom⟩, Iso.refl _, ?_, ?_, ?_⟩
  · show IsMonHom (𝟙 _ ≫ fst _ _); infer_instance
  · show IsMonHom (𝟙 _ ≫ snd _ _); infer_instance
  · show F.map (𝟙 _) ≫ _ = (tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm).hom ≫ _
    rw [F.map_id, Category.id_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]



/-- **`h(A) + h(B) ≤ h(A × B)` from N1 and `ProductModelHeight`** (P1 and `NeronModelMinimal` are
theorems). -/
theorem stableFaltingsHeight_add_le_of_productModelHeight (hN1 : NeronModelExists)
    (hH : ProductModelHeight) {K : Type} [Field K] (A B C : AbVar K)
    (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C :=
  stableFaltingsHeight_add_le hN1 neronModelMinimal productGroupModelExists hH A B C hC

end ProductProof


/-! ## Part 4: `OpenImmersionHeightLe` (the inverse transport) -/

section OpenHeight

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The kernel computation of `cotMap_omegaAt`, as an equation. -/
theorem stalk_ker_eq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s)
    (g : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s)) :
    (𝒢.unitSection.stalkMap s) (f.left.stalkMap (𝒢.unitSection s)
      (𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes g)) =
      (𝒩.unitSection.stalkMap s) g := by
  have hE := unitSection_comp 𝒢 𝒩 f
  set T := 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  have h1 := Scheme.Hom.stalkMap_comp 𝒢.unitSection f.left s
  have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s
  have h1' : (𝒢.unitSection.stalkMap s) (f.left.stalkMap (𝒢.unitSection s) (T g)) =
      ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
    exact this.symm
  have h2' : ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) =
      (𝒩.unitSection.stalkMap s) ((𝒩.G.left.presheaf.stalkCongr
        (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
    exact this
  rw [h1', h2']
  have h4 : ∀ y : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s), y = g →
      (𝒩.unitSection.stalkMap s) y = (𝒩.unitSection.stalkMap s) g := by
    rintro y rfl; rfl
  apply h4
  show 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes (T g) = g
  exact (stalkSpecializes_stalkSpecializes_apply _ _ g).trans (stalkSpecializes_self_apply _ g)

/-- The specialization computation of `cotMap_omegaAt`, as an equation. -/
theorem stalk_spec_eq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s)
    (g : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s)) :
    𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)
      (f.left.stalkMap (𝒢.unitSection s)
        (𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes g)) =
      genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.stalkSpecializes (𝒩.specializes_genericUnit s) g) := by
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  unfold genMap
  rw [CommRingCat.comp_apply]
  congr 1
  rw [stalkSpecializes_stalkSpecializes_apply, stalkSpecializes_stalkSpecializes_apply]

theorem genMap_mem_maximalIdeal_iff (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] (x : 𝒩.genStalk) :
    genMap 𝒢 𝒩 f x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ↔
      x ∈ IsLocalRing.maximalIdeal 𝒩.genStalk := by
  haveI := isIso_genMap 𝒢 𝒩 f
  let e : 𝒩.genStalk ≃+* 𝒢.genStalk := (asIso (genMap 𝒢 𝒩 f)).commRingCatIsoToRingEquiv
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (isUnit_map_iff e x)

/-- **For an open immersion, `(ω_𝒰)_s ⊆ f^* (ω_𝒢)_s`** at every `s`. -/
theorem omegaAt_le_cotMap (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)]
    (s : Spec (CommRingCat.of (𝓞 L))) (x : 𝒰.cotangent) (hx : x ∈ 𝒰.omegaAt s) :
    ∃ y ∈ 𝒢.omegaAt s, cotMap 𝒰 𝒢 f y = x := by
  have hE := unitSection_comp 𝒰 𝒢 f
  have hp : f.left (𝒰.unitSection s) = 𝒢.unitSection s :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ s) hE)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    have hiso1 : IsIso (f.left.stalkMap (𝒰.unitSection s)) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have hiso2 : IsIso (𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes) :=
      Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq hp).symm)
    let Ψ := 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes ≫
      f.left.stalkMap (𝒰.unitSection s)
    haveI : IsIso Ψ := inferInstance
    set g₀ := (inv Ψ) g
    have hg₀ : f.left.stalkMap (𝒰.unitSection s)
        (𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes g₀) = g := by
      show Ψ (inv Ψ g) = g
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    have hker := stalk_ker_eq 𝒰 𝒢 f s hp g₀
    rw [hg₀] at hker
    have hspec := stalk_spec_eq 𝒰 𝒢 f s hp g₀
    rw [hg₀] at hspec
    have hmem₀ : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g₀ ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk := by
      rw [← genMap_mem_maximalIdeal_iff 𝒰 𝒢 f, ← hspec]; exact hmem
    refine ⟨𝒢.dCls ⟨_, hmem₀⟩, Submodule.subset_span ⟨g₀, ?_, hmem₀, rfl⟩, ?_⟩
    · rw [RingHom.mem_ker, ← hker]; exact hg
    · rw [cotMap_dCls]
      congr 1
      exact Subtype.ext hspec.symm
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨r • a, Submodule.smul_mem _ r ha, map_smul _ _ _⟩

/-- **For an open immersion, `ω_𝒰 ⊆ f^* ω_𝒢`.** -/
theorem omega_le_cotMap (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)]
    (x : 𝒰.cotangent) (hx : x ∈ 𝒰.omega) : ∃ y ∈ 𝒢.omega, cotMap 𝒰 𝒢 f y = x := by
  obtain ⟨y, hy⟩ := (cotMap_bijective 𝒰 𝒢 f).2 x
  refine ⟨y, ?_, hy⟩
  rw [GroupModel.omega, Submodule.mem_iInf] at hx ⊢
  intro s
  obtain ⟨y', hy', hy'x⟩ := omegaAt_le_cotMap 𝒰 𝒢 f s x (hx s)
  rwa [(cotMap_bijective 𝒰 𝒢 f).1 (hy'x.trans hy.symm)] at hy'

theorem detLattice_le_hodgeMap (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)] (g : ℕ)
    (x : 𝒰.hodgeSpace g) (hx : x ∈ 𝒰.detLattice g) :
    ∃ y ∈ 𝒢.detLattice g, hodgeMap 𝒰 𝒢 f g y = x := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    choose w hw hwv using fun i => omega_le_cotMap 𝒰 𝒢 f (v i : 𝒰.cotangent) (v i).2
    refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g w,
      Submodule.subset_span ⟨fun i => ⟨w i, hw i⟩, rfl⟩, ?_⟩
    rw [hodgeMap_wedge]
    simp only [hwv]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨d, hd, rfl⟩ := hb
    exact ⟨c + d, add_mem hc hd, map_add _ _ _⟩
  | smul r a _ ha =>
    obtain ⟨c, hc, rfl⟩ := ha
    refine ⟨r • c, Submodule.smul_mem _ r hc, ?_⟩
    rw [← algebraMap_smul L r c, LinearMap.map_smul, algebraMap_smul]

/-- **Inverse transport of analytic uniformizations through an open immersion.** -/
theorem isAnalyticUniformization_of_comp (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G) [IsMonHom f]
    [IsOpenImmersion f.left] [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Ψ : (Fin g → ℂ) → 𝒰.Pts τ)
    (h : 𝒢.IsAnalyticUniformization τ Λ (fun z => Ψ z ≫ f)) :
    𝒰.IsAnalyticUniformization τ Λ Ψ := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hb := pts_comp_bijective 𝒰 𝒢 f τ
  have hdom : ∀ V, 𝒰.dom Ψ V = 𝒢.dom (fun z => Ψ z ≫ f) (f.left ''ᵁ V) := by
    intro V
    ext z
    show ⊤ ≤ (Ψ z).left ⁻¹ᵁ V ↔ ⊤ ≤ (Ψ z ≫ f).left ⁻¹ᵁ (f.left ''ᵁ V)
    have : (Ψ z ≫ f).left ⁻¹ᵁ (f.left ''ᵁ V) = (Ψ z).left ⁻¹ᵁ V := by
      show (Ψ z).left ⁻¹ᵁ (f.left ⁻¹ᵁ (f.left ''ᵁ V)) = _
      rw [Scheme.Hom.preimage_image_eq]
    rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    apply hb.1
    show Ψ (z + w) ≫ f = (Ψ z * Ψ w) ≫ f
    rw [MonObj.mul_comp]
    exact hmul z w
  · intro z
    rw [← hker z]
    constructor
    · intro h1
      show Ψ z ≫ f = 1
      rw [h1, MonObj.one_comp]
    · intro h1
      apply hb.1
      show Ψ z ≫ f = 1 ≫ f
      rw [MonObj.one_comp]
      exact h1
  · intro p
    obtain ⟨z, hz⟩ := hsurj (p ≫ f)
    exact ⟨z, hb.1 hz⟩
  · intro V
    rw [hdom]
    exact hopen _
  · intro V s
    rw [hdom]
    refine (hdiff (f.left ''ᵁ V) ((f.left.appIso V).inv s)).congr fun z hz => ?_
    have hz' : z ∈ 𝒰.dom Ψ V := (hdom V).symm ▸ hz
    rw [evalAt_comp, evalAt_res 𝒰 (Ψ z) (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge) hz']
    congr 1
    have hh : f.left.app (f.left ''ᵁ V) ≫
        𝒰.G.left.presheaf.map (homOfLE (Scheme.Hom.preimage_image_eq f.left V).ge).op =
        (f.left.appIso V).hom := by
      rw [Scheme.Hom.appIso_hom]
      rfl
    rw [← CommRingCat.comp_apply, hh, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]

end OpenHeight

/-- **Glue `OpenImmersionHeightLe`, proved.** -/
theorem openImmersionHeightLe : OpenImmersionHeightLe := by
  intro K _ A L _ _ _ 𝒰 𝒢 f hf hm hi
  haveI := hf
  haveI := hm
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
  subst hM
  have hbij := hodgeMapBijective K A L 𝒰 M.model f hi g
  let e := LinearEquiv.ofBijective (hodgeMap 𝒰 M.model f g) hbij
  have hfin : Module.finrank L (𝒰.hodgeSpace g) = 1 :=
    e.finrank_eq.symm.trans M.hodge.finrank_eq_one
  obtain ⟨v, hv, hv0⟩ := hodgeLatticeNonzero_of_omegaSpans omegaSpans K A L 𝒰 g hfin
  let H : 𝒰.hodgeSpace g →ₗ[L] M.model.hodgeSpace g := e.symm
  have hinj : Function.Injective H := e.symm.injective
  have hle : ∀ x ∈ 𝒰.detLattice g, H x ∈ M.hodge.lattice := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := detLattice_le_hodgeMap 𝒰 M.model f g x hx
    have : H (hodgeMap 𝒰 M.model f g y) = y := e.symm_apply_apply y
    rw [this, M.lattice_eq]
    exact hy
  have hv0' : H v ≠ 0 := fun h0 => hv0 (hinj (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem M.hodge (hle v hv) hv0'
  have hlat : ∃ s ∈ 𝒰.detLattice g, s ≠ 0 ∧ secIndex (𝒰.detLattice g) s ≠ 0 :=
    ⟨v, hv, hv0, (secIndex_le_of_map H hinj _ _ hle hv hne).1⟩
  haveI := isIso_genMap 𝒰 M.model f
  let M' : MetrizedModel A L g :=
    { model := 𝒰
      hodge := pullHodge M.hodge H hinj (𝒰.detLattice g) hfin hlat
      lattice_eq := rfl
      arch := fun τ => by
        obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
        let Ψ : (Fin g → ℂ) → 𝒰.Pts τ := fun z =>
          (Equiv.ofBijective _ (pts_comp_bijective 𝒰 M.model f τ)).symm (Φ z)
        have hΦΨ : (fun z => Ψ z ≫ f) = Φ := funext fun z =>
          (Equiv.ofBijective _ (pts_comp_bijective 𝒰 M.model f τ)).apply_symm_apply (Φ z)
        have hU : 𝒰.IsAnalyticUniformization τ (M.hodge.periods τ) Ψ :=
          isAnalyticUniformization_of_comp 𝒰 M.model f τ _ Ψ (hΦΨ ▸ hΦ)
        refine ⟨Ψ, hU, fun t => ?_⟩
        let t₀ : Fin g → IsLocalRing.maximalIdeal M.model.genStalk := fun i =>
          ⟨(inv (genMap 𝒰 M.model f)) (t i), by
            rw [← genMap_mem_maximalIdeal_iff 𝒰 M.model f, ← CommRingCat.comp_apply,
              IsIso.inv_hom_id, CommRingCat.id_apply]
            exact (t i).2⟩
        have ht : ∀ i, (t i : 𝒰.genStalk) = genMap 𝒰 M.model f (t₀ i) := fun i => by
          show _ = genMap 𝒰 M.model f ((inv (genMap 𝒰 M.model f)) (t i))
          rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
        have hw : 𝒰.wedge t = hodgeMap 𝒰 M.model f g (M.model.wedge t₀) := by
          rw [hodgeMap_wedgeGerm]
          congr 1
          funext i
          exact Subtype.ext (ht i)
        show M.hodge.coeff τ (H (𝒰.wedge t)) = _
        have hH : H (𝒰.wedge t) = M.model.wedge t₀ := by
          rw [hw]; exact e.symm_apply_apply _
        rw [hH, hc, ← jacDet_comp_genMap 𝒰 M.model f _ Ψ hU t₀ t ht, hΦΨ] }
  calc (⨅ (g' : ℕ) (M'' : MetrizedModel A L g') (_ : M''.model = 𝒰),
        (M''.hodge.modelHeight : EReal)) ≤ (M'.hodge.modelHeight : EReal) :=
        iInf_le_of_le g (iInf_le_of_le M' (iInf_le_of_le rfl le_rfl))
    _ ≤ (M.hodge.modelHeight : EReal) :=
        EReal.coe_le_coe_iff.mpr (modelHeight_pullHodge_le M.hodge H hinj _ hfin hlat hle)

/-- **`OpenSubgroupHeight` (glue M6), proved.** -/
theorem openSubgroupHeight : OpenSubgroupHeight :=
  openSubgroupHeight_of heightAntitone openImmersionHeightLe

/-- **H5 in the form R19-R21 need, from the leaves N1, N2 and the one remaining glue statement
`ModelHeightBaseChange`.** -/
theorem stableFaltingsHeight_eq_neron_all' (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hbc : ModelHeightBaseChange) (K : Type) [Field K]
    [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height :=
  stableFaltingsHeight_eq_neron_all hN1 hN2 openImmersionHeightLe hbc K A

end ZInQ.H5Glue

/-- **The leaf H5 reduces to its finiteness half** (g0-assemble2, from h5-glue's
`neronModelMinimal`): `ResearchLeaves.h5 = StableHeightFinite ∧ NeronModelMinimal`. -/
theorem LeafAdopt.h5_iff_stableHeightFinite :
    LeafAdopt.H5 ↔ ZInQ.DefFaltings.StableHeightFinite :=
  ⟨fun h => h.1, fun h => ⟨h, ZInQ.H5Glue.neronModelMinimal⟩⟩

end G0A2_a90_h5glue

section G0A2_a95_g9
-- (g0-assemble2 edits: the `open PkgI4 …` lines name `_root_.PkgI4` explicitly, and also the extension namespace
-- `ZInQ.Contrib.G9.PkgI4` once it exists, since `open` resolves only the innermost match.)
/-! ## g0-assemble2: g9-derham (ZInQKernel/Contrib/G9/*.lean, verbatim minus imports and `#print` lines, in import
order; its I3Layer.lean, I4Layer.lean and Statement.lean are verbatim restatements, inside `ZInQ.Contrib.G9`,
of Leaves.lean's `PkgI3Sec`, `PkgI4Sec` and g0-mod-galois' `G9Glue`; they are omitted, so the names resolve to
Leaves.lean's and part 70's declarations) -/

-- ===== ZInQKernel/Contrib/G9/HenselEmb.lean

/-!
# G9: lifting a finite separable extension through a Henselian residue map

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Let `θ : R → Ω` be a surjective `K`-algebra map from a domain `R`, Henselian along `ker θ`, with
every `y ∉ ker θ` a unit (so `R` is local with maximal ideal `ker θ`), and `K` of characteristic
`0`. Then every `K`-embedding `ι_Ω : L → Ω` of a finite extension `L/K` lifts to `ι₀ : L → R`
(`exists_hensel_lift`), and the lift is unique and natural: for a `K`-algebra map `s : R → R` and
`τ : L → L` with `θ(s(ι₀ x)) = ι_Ω(τ x)`, `s ∘ ι₀ = ι₀ ∘ τ` (`hensel_lift_natural`).

Applied in `BdREmb.lean` to `θ⁺ : B_dR^+ → ℂ_p`: the classical embedding `ℚ̄_p ⊆ B_dR^+`
(STANDARD: Fontaine, Astérisque 223, Exp. II, §1.5; Brinon–Conrad, CMI notes, §4.4;
numbering UNVERIFIED), compatible with the Galois action.
-/

namespace ZInQ.Contrib.G9

open Polynomial

section Hensel

variable {K R Ω : Type*} [Field K] [CommRing R] [Algebra K R] [Field Ω] [Algebra K Ω]

/-- Two roots of `P` with the same residue at which `P'` does not vanish are equal. -/
theorem root_eq_of_theta [IsDomain R] (θ : R →ₐ[K] Ω) (P : K[X]) {a b : R}
    (ha : aeval a P = 0) (hb : aeval b P = 0) (hab : θ a = θ b)
    (hd : aeval (θ b) (derivative P) ≠ 0) : a = b := by
  set Q := P.map (algebraMap K R)
  obtain ⟨k, hk⟩ := Q.binomExpansion b (a - b)
  rw [add_sub_cancel, eval_map_algebraMap, eval_map_algebraMap, ha, hb, derivative_map,
    eval_map_algebraMap, zero_add] at hk
  have hfac : (a - b) * (aeval b (derivative P) + k * (a - b)) = 0 := by
    linear_combination -hk
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    apply hd
    have := congrArg θ h
    rwa [map_add, map_mul, map_sub, hab, sub_self, mul_zero, add_zero, map_zero,
      ← Polynomial.aeval_algHom_apply] at this

variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **Hensel lift** of `ι_Ω : L → Ω` through `θ`. -/
theorem exists_hensel_lift (θ : R →ₐ[K] Ω) (hsurj : Function.Surjective θ)
    [HenselianRing R (RingHom.ker θ.toRingHom)] (hunit : ∀ y, θ y ≠ 0 → IsUnit y) (ιΩ : L →ₐ[K] Ω) :
    ∃ ι₀ : L →ₐ[K] R, ∀ x, θ (ι₀ x) = ιΩ x := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  have hd : aeval (ιΩ pb.gen) (derivative P) ≠ 0 := by
    rw [Polynomial.aeval_algHom_apply]
    exact (map_ne_zero ιΩ).mpr (hsep.aeval_derivative_ne_zero hroot)
  obtain ⟨a₀, ha₀⟩ := hsurj (ιΩ pb.gen)
  obtain ⟨a, haroot, hamem⟩ := HenselianRing.is_henselian (I := RingHom.ker θ.toRingHom) (P.map (algebraMap K R))
    (hP.map _) a₀ (by
      change θ _ = 0
      rw [eval_map_algebraMap, ← Polynomial.aeval_algHom_apply, ha₀,
        Polynomial.aeval_algHom_apply, hroot, map_zero])
    (by
      apply IsUnit.map
      apply hunit
      rwa [derivative_map, eval_map_algebraMap, ← Polynomial.aeval_algHom_apply, ha₀])
  have haP : aeval a P = 0 := by
    rw [← eval_map_algebraMap]; exact haroot
  have hθa : θ a = ιΩ pb.gen := by
    change θ (a - a₀) = 0 at hamem
    rw [map_sub, sub_eq_zero] at hamem
    rw [← ha₀]; exact hamem
  refine ⟨pb.lift a haP, ?_⟩
  have : θ.comp (pb.lift a haP) = ιΩ := pb.algHom_ext (by
    rw [AlgHom.comp_apply, PowerBasis.lift_gen, hθa])
  intro x
  rw [← this, AlgHom.comp_apply]

/-- **Naturality of the Hensel lift.** -/
theorem hensel_lift_natural [IsDomain R] (θ : R →ₐ[K] Ω) (ιΩ : L →ₐ[K] Ω) (ι₀ : L →ₐ[K] R)
    (hι₀ : ∀ x, θ (ι₀ x) = ιΩ x) (s : R →ₐ[K] R) (τ : L →ₐ[K] L)
    (hs : ∀ x, θ (s (ι₀ x)) = ιΩ (τ x)) (x : L) : s (ι₀ x) = ι₀ (τ x) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  have hτroot : aeval (τ pb.gen) P = 0 := by
    rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  have key : (s.comp ι₀) = ι₀.comp τ := by
    apply pb.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine root_eq_of_theta θ P ?_ ?_ ?_ ?_
    · rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, hroot, map_zero,
        map_zero]
    · rw [Polynomial.aeval_algHom_apply, hτroot, map_zero]
    · rw [hs, hι₀]
    · rw [hι₀, Polynomial.aeval_algHom_apply]
      exact (map_ne_zero ιΩ).mpr (hsep.aeval_derivative_ne_zero hτroot)
  exact congrArg (fun φ => φ x) key

end Hensel

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Speiser.lean

/-!
# G9: Galois descent for semilinear actions (Speiser's lemma)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Let `L/K` be a finite Galois extension with group `Γ`, and `M` an `L`-vector space with a
semilinear action of `Γ` (`τ(c • m) = τ(c) • τ(m)`). Then `L ⊗_K M^Γ → M` is an isomorphism
(Speiser's lemma; STANDARD: Serre, *Local fields*, X §1, Lemma; Bourbaki *Algèbre* V §10).
We need only the dimension count `dim_K M = [L:K] · dim_K M^Γ`, `speiser_finrank`.

The proof: for a `K`-basis `b` of `L` indexed by `Γ`, the matrix `A = (τ(b_j))_{τ,j}` is
invertible by Dedekind's independence of characters; this gives both surjectivity (each `m` is an
`L`-combination of the traces `Σ_σ σ(b_j m)`) and injectivity.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct Classical

section Speiser

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A `K`-basis of `L` indexed by `Gal(L/K)`. -/
noncomputable def galBasis : Basis (L ≃ₐ[K] L) K L :=
  (Module.finBasisOfFinrankEq K L
    (by rw [← IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card])).reindex
    (Fintype.equivFin (L ≃ₐ[K] L)).symm

/-- The matrix `(τ(b_j))_{τ, j}`. -/
noncomputable def galMatrix : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  Matrix.of fun τ j => τ (galBasis (K := K) (L := L) j)

/-- Dedekind: `(τ(b_j))` is invertible. -/
theorem isUnit_galMatrix : IsUnit (galMatrix (K := K) (L := L)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have hli : LinearIndependent L
      (fun τ : L ≃ₐ[K] L => ((τ : L →ₐ[K] L)).toLinearMap) :=
    (linearIndependent_toLinearMap K L L).comp (fun τ : L ≃ₐ[K] L => (τ : L →ₐ[K] L))
      (fun _ _ h => AlgEquiv.coe_toAlgHom_injective h)
  have key : ∀ c : (L ≃ₐ[K] L) → L, Matrix.vecMul c galMatrix = 0 → c = 0 := by
    intro c hc
    have hsum : (∑ τ, c τ • ((τ : L →ₐ[K] L)).toLinearMap) = 0 := by
      refine (galBasis (K := K) (L := L)).ext fun j => ?_
      have := congrFun hc j
      simp only [Matrix.vecMul, dotProduct, galMatrix, Matrix.of_apply, Pi.zero_apply] at this
      simpa [LinearMap.sum_apply] using this
    funext τ
    exact (Fintype.linearIndependent_iff.mp hli) c hsum τ
  intro c d h
  have h' : Matrix.vecMul (c - d) galMatrix = 0 := by
    have h0 : Matrix.vecMul c galMatrix = Matrix.vecMul d (galMatrix (K := K) (L := L)) := h
    rw [Matrix.sub_vecMul, h0, sub_self]
  exact sub_eq_zero.mp (key _ h')

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]

variable (T : (L ≃ₐ[K] L) → M →+ M)
  (hsmul : ∀ τ (c : L) (m : M), T τ (c • m) = τ c • T τ m)
  (hone : ∀ m, T 1 m = m)
  (hmul : ∀ τ σ m, T (τ * σ) m = T τ (T σ m))

include hsmul in
theorem semilin_smulK (τ : L ≃ₐ[K] L) (k : K) (m : M) : T τ (k • m) = k • T τ m := by
  rw [← algebraMap_smul L k m, hsmul, AlgEquiv.commutes, algebraMap_smul]

/-- The fixed points `M^Γ`, a `K`-subspace. -/
def fixedK : Submodule K M where
  carrier := {m | ∀ τ, T τ m = m}
  zero_mem' := by intro τ; simp
  add_mem' := by
    intro x y hx hy τ
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx, hy]
  smul_mem' := by
    intro k x hx τ
    simp only [Set.mem_ofPred_eq] at hx
    rw [semilin_smulK T hsmul, hx]

/-- `L ⊗_K M^Γ → M`. -/
noncomputable def speiserMap : L ⊗[K] (fixedK T hsmul) →ₗ[K] M :=
  TensorProduct.lift (LinearMap.mk₂ K (fun (x : L) (n : fixedK T hsmul) => x • (n : M))
    (fun x y n => add_smul x y _)
    (fun k x n => by simp only [smul_assoc])
    (fun x n n' => by simp only [Submodule.coe_add, smul_add])
    (fun k x n => by simp only [SetLike.val_smul, smul_comm x k (n : M)]))

theorem speiserMap_tmul (x : L) (n : fixedK T hsmul) :
    speiserMap T hsmul (x ⊗ₜ n) = x • (n : M) := by
  simp [speiserMap]

include hone hmul in
theorem speiserMap_surjective : Function.Surjective (speiserMap T hsmul) := by
  intro m
  set b := galBasis (K := K) (L := L)
  set A := galMatrix (K := K) (L := L)
  have hA := isUnit_galMatrix (K := K) (L := L)
  -- the traces `y j = Σ_σ σ(b j • m)`
  let y : (L ≃ₐ[K] L) → M := fun j => ∑ σ, T σ (b j • m)
  have hy : ∀ j, y j ∈ fixedK T hsmul := by
    intro j τ
    simp only [y, map_sum, ← hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  have hy' : ∀ j, y j = ∑ σ, A σ j • T σ m := by
    intro j
    simp only [y, hsmul, A, galMatrix, Matrix.of_apply, b]
  refine ⟨∑ j, (A⁻¹ j (1 : L ≃ₐ[K] L)) ⊗ₜ ⟨y j, hy j⟩, ?_⟩
  rw [map_sum]
  simp only [speiserMap_tmul, hy', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hmul1 : ∀ σ, (∑ j, A⁻¹ j (1 : L ≃ₐ[K] L) * A σ j) =
      (1 : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) σ (1 : L ≃ₐ[K] L) := by
    intro σ
    rw [← Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hmul1, Matrix.one_apply]
  simp [hone]

include hone hmul in
theorem speiserMap_injective : Function.Injective (speiserMap T hsmul) := by
  set b := galBasis (K := K) (L := L)
  set A := galMatrix (K := K) (L := L)
  have hA := isUnit_galMatrix (K := K) (L := L)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  set n := TensorProduct.equivFinsuppOfBasisLeft b x
  have hxn : x = ∑ j, b j ⊗ₜ n j := by
    have h1 := LinearMap.congr_fun (TensorProduct.equivFinsuppOfBasisLeft_symm b) n
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, n] at h1
    rw [h1, Finsupp.lsum_apply, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [hxn, map_sum] at hx
  simp only [speiserMap_tmul] at hx
  -- apply every `τ`
  have hτ : ∀ τ, ∑ j, A τ j • (n j : M) = 0 := by
    intro τ
    have := congrArg (T τ) hx
    rw [map_sum, map_zero] at this
    simpa only [hsmul, (n _).2 τ, A, galMatrix, Matrix.of_apply, b] using this
  have hn : ∀ k, (n k : M) = 0 := by
    intro k
    have hinv : A⁻¹ * A = 1 :=
      Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
    have : (n k : M) = ∑ τ, A⁻¹ k τ • ∑ j, A τ j • (n j : M) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have h2 : ∀ j, (∑ τ, A⁻¹ k τ * A τ j) = (1 : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) k j := by
        intro j; rw [← hinv, Matrix.mul_apply]
      simp_rw [h2, Matrix.one_apply]
      simp
    rw [this]
    simp [hτ]
  rw [hxn]
  simp [show ∀ k, n k = 0 from fun k => Subtype.ext (hn k)]

include hone hmul in
/-- **Speiser's lemma, dimension form.** `dim_K M = [L:K] · dim_K M^Γ`. -/
theorem speiser_finrank :
    finrank K M = finrank K L * finrank K (fixedK T hsmul) := by
  have e := LinearEquiv.ofBijective (speiserMap T hsmul)
    ⟨speiserMap_injective T hsmul hone hmul, speiserMap_surjective T hsmul hone hmul⟩
  rw [← e.finrank_eq, Module.finrank_tensorProduct]

end Speiser

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Descent.lean

/-!
# G9: finite Galois descent for spaces of equivariant maps

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

A group `G` acts `K`-linearly on a `K`-algebra `B` (`act`) and on a `K`-space `V` (`ρ`). For
`S ⊆ G`, `Dsp act ρ S` is the space of `K`-linear maps `φ : V → B` with `φ(ρ(g) v) = act(g)(φ v)`
for `g ∈ S`. (pkg-I4's `ddrSpace`, `ddrSpaceOver`, `htSpace`, `htSpaceOver` are all of this
form: `B = B_dR` or `B = ℂ_p` with the twisted action `χ(g)^i · g`.)

**Descent (`descent_finrank`).** Let `L/K` be finite Galois, `γ : G → Gal(L/K)` a surjective
homomorphism, and `ι : L → B` a `K`-algebra map with `act(g)(ι(x) b) = ι(γ(g) x) · act(g)(b)`.
Then `dim_K Dsp(ker γ) = [L:K] · dim_K Dsp(G)`. Proof: `Dsp(ker γ)` is an `L`-space through `ι`,
with a semilinear action of `Gal(L/K) = G/ker γ`, whose invariants are `Dsp(G)`; apply Speiser's
lemma (`speiser_finrank`). This is the finite-descent paragraph of N5's Lemma
`lem:de-rham-descent` (`D_K = D_{F}^{Gal(F/K)}`, `F ⊗_K D_K ≅ D_F`).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct

section Dsp

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  {V : Type*} [AddCommGroup V] [Module K V]

/-- `S`-equivariant `K`-linear maps `V → B`. -/
def Dsp (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) :
    Submodule K (V →ₗ[K] B) where
  carrier := {φ | ∀ g ∈ S, ∀ v, φ (ρ g v) = act g (φ v)}
  zero_mem' := by intro g _ v; simp
  add_mem' := by
    intro φ ψ hφ hψ g hg v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ g hg v, hψ g hg v, map_add]
  smul_mem' := by
    intro c φ hφ g hg v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ g hg v, map_smul]

theorem mem_Dsp {act : G → B →ₗ[K] B} {ρ : G → V →ₗ[K] V} {S : Set G} {φ : V →ₗ[K] B} :
    φ ∈ Dsp act ρ S ↔ ∀ g ∈ S, ∀ v, φ (ρ g v) = act g (φ v) := Iff.rfl

end Dsp

section Descent

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [CommRing B] [Algebra K B]
  {V : Type*} [AddCommGroup V] [Module K V]
  (act : G →* (B →ₗ[K] B)) (ρ : G →* (V →ₗ[K] V))
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (ι : L →ₐ[K] B) (γ : G →* (L ≃ₐ[K] L))

theorem act_inv_act (g : G) (b : B) : act g (act g⁻¹ b) = b := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_rho (g : G) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- `g · φ = act(g) ∘ φ ∘ ρ(g)⁻¹`, on `Hom_K(V, B)`. -/
def twist (g : G) : (V →ₗ[K] B) →ₗ[K] (V →ₗ[K] B) where
  toFun φ := act g ∘ₗ φ ∘ₗ ρ g⁻¹
  map_add' φ ψ := by ext v; simp
  map_smul' c φ := by ext v; simp

theorem twist_apply (g : G) (φ : V →ₗ[K] B) (v : V) :
    twist act ρ g φ v = act g (φ (ρ g⁻¹ v)) := rfl

theorem twist_mul (g h : G) (φ : V →ₗ[K] B) :
    twist act ρ (g * h) φ = twist act ρ g (twist act ρ h φ) := by
  ext v
  simp only [twist_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

theorem twist_mem (g : G) {φ : V →ₗ[K] B} (hφ : φ ∈ Dsp act ρ (γ.ker : Set G)) :
    twist act ρ g φ ∈ Dsp act ρ (γ.ker : Set G) := by
  intro h hh v
  have hh' : γ h = 1 := hh
  have hk : g⁻¹ * h * g ∈ γ.ker := by
    show γ (g⁻¹ * h * g) = 1
    simp [hh']
  have e1 : ρ g⁻¹ (ρ h v) = ρ (g⁻¹ * h * g) (ρ g⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    group
  rw [twist_apply, twist_apply, e1, hφ _ hk]
  rw [← Module.End.mul_apply (act g), ← map_mul, ← Module.End.mul_apply (act h), ← map_mul]
  congr 2
  group

theorem twist_eq_self_of_mem_ker {h : G} (hh : h ∈ γ.ker) {φ : V →ₗ[K] B}
    (hφ : φ ∈ Dsp act ρ (γ.ker : Set G)) : twist act ρ h φ = φ := by
  ext v
  have hh' : h⁻¹ ∈ γ.ker := γ.ker.inv_mem hh
  rw [twist_apply, hφ _ hh', act_inv_act]

theorem twist_eq_self_of_mem_univ (g : G) {φ : V →ₗ[K] B}
    (hφ : φ ∈ Dsp act ρ Set.univ) : twist act ρ g φ = φ := by
  ext v
  rw [twist_apply, hφ _ (Set.mem_univ _), act_inv_act]

theorem mem_univ_of_twist (φ : V →ₗ[K] B) (h : ∀ g, twist act ρ g φ = φ) :
    φ ∈ Dsp act ρ Set.univ := by
  intro g _ v
  have := LinearMap.congr_fun (h g) (ρ g v)
  rw [twist_apply, rho_inv_rho] at this
  exact this.symm

variable (hγ : Function.Surjective γ)
  (hsemi : ∀ g x b, act g (ι x * b) = ι (γ g x) * act g b)

include hsemi in
theorem twist_smul (g : G) (x : L) (φ : V →ₗ[K] B) :
    twist act ρ g (ι x • φ) = ι (γ g x) • twist act ρ g φ := by
  ext v
  simp only [twist_apply, LinearMap.smul_apply, smul_eq_mul, hsemi]

include hγ hsemi in
/-- **Finite Galois descent for `Dsp`.** `dim_K Dsp(ker γ) = [L:K] · dim_K Dsp(G)`. -/
theorem descent_finrank :
    finrank K (Dsp act ρ (γ.ker : Set G)) = finrank K L * finrank K (Dsp act ρ Set.univ) := by
  classical
  -- `B` as an `L`-algebra through `ι`
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  -- the `L`-subspace `Dsp(ker γ)`
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ (γ.ker : Set G)}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ h hh v
        simp only [Set.mem_ofPred_eq] at hφ
        have hx : γ h x = x := by
          rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
          rw [hh]; rfl
        simp only [LinearMap.smul_apply, hLsmul, hφ h hh v, hsemi, hx] }
  have hDL : DL.restrictScalars K = Dsp act ρ (γ.ker : Set G) := Submodule.ext fun _ => Iff.rfl
  -- the action of `g ∈ G` on `DL`
  let Tg : G → DL →+ DL := fun g =>
    { toFun := fun φ => ⟨twist act ρ g φ, twist_mem act ρ γ g φ.2⟩
      map_zero' := by ext1; simp
      map_add' := by intro φ ψ; ext1; simp }
  have Tg_val : ∀ g (φ : DL), ((Tg g φ : DL) : V →ₗ[K] B) = twist act ρ g φ := fun _ _ => rfl
  let s : (L ≃ₐ[K] L) → G := Function.surjInv hγ
  have hs : ∀ τ, γ (s τ) = τ := Function.surjInv_eq hγ
  have hker : ∀ g, (s (γ g))⁻¹ * g ∈ γ.ker := by
    intro g; rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  let T : (L ≃ₐ[K] L) → DL →+ DL := fun τ => Tg (s τ)
  have hT_eq : ∀ g (φ : DL), Tg g φ = T (γ g) φ := by
    intro g φ
    apply Subtype.ext
    have hg : g = s (γ g) * ((s (γ g))⁻¹ * g) := by group
    change twist act ρ g φ = twist act ρ (s (γ g)) φ
    conv_lhs => rw [hg]
    rw [twist_mul, twist_eq_self_of_mem_ker act ρ γ (hker g) φ.2]
  have hsmul : ∀ τ (c : L) (φ : DL), T τ (c • φ) = τ c • T τ φ := by
    intro τ c φ
    apply Subtype.ext
    change twist act ρ (s τ) (ι c • (φ : V →ₗ[K] B)) = ι (τ c) • twist act ρ (s τ) φ
    rw [twist_smul act ρ ι γ hsemi, hs]
  have hone : ∀ φ, T 1 φ = φ := by
    intro φ
    apply Subtype.ext
    change twist act ρ (s 1) φ = φ
    have : s 1 ∈ γ.ker := by rw [MonoidHom.mem_ker, hs]
    exact twist_eq_self_of_mem_ker act ρ γ this φ.2
  have hmul : ∀ τ σ φ, T (τ * σ) φ = T τ (T σ φ) := by
    intro τ σ φ
    have h1 : T (τ * σ) φ = Tg (s τ * s σ) φ := by
      rw [hT_eq (s τ * s σ), map_mul, hs, hs]
    rw [h1]
    apply Subtype.ext
    change twist act ρ (s τ * s σ) φ = twist act ρ (s τ) (twist act ρ (s σ) φ)
    rw [twist_mul]
  have hsp := speiser_finrank (K := K) (L := L) (M := DL) T hsmul hone hmul
  -- the fixed points are `Dsp(G)`
  have hfix : Submodule.map (DL.subtype.restrictScalars K) (fixedK (K := K) (L := L) (M := DL) T hsmul)
      = Dsp act ρ Set.univ := by
    ext φ
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      apply mem_univ_of_twist
      intro g
      have := congrArg Subtype.val ((hT_eq g ψ).trans (hψ (γ g)))
      exact this
    · intro hφ
      refine ⟨⟨φ, fun g hg v => hφ g (Set.mem_univ _) v⟩, ?_, rfl⟩
      intro τ
      apply Subtype.ext
      exact twist_eq_self_of_mem_univ act ρ (s τ) hφ
  have e1 : finrank K (fixedK (K := K) (L := L) (M := DL) T hsmul) = finrank K (Dsp act ρ Set.univ) := by
    rw [← hfix]
    exact (Submodule.equivMapOfInjective (DL.subtype.restrictScalars K)
      (Submodule.injective_subtype DL) _).finrank_eq
  have e2 : finrank K DL = finrank K (Dsp act ρ (γ.ker : Set G)) := by
    rw [← hDL]
    rfl
  rw [← e2, hsp, e1]

end Descent

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/OverF.lean

/-!
# G9: counting equivariant maps through `V ⊗ C ≅ U ⊕ U`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Pure linear algebra on the spaces `Dsp act ρ S` of `Descent.lean`:
* `finrank_Dsp_congr`: an equivariant isomorphism `V ≅ V'` preserves `dim Dsp`;
* `finrank_Dsp_pi`: `dim Dsp(V^ι) = |ι| · dim Dsp(V)`;
* `finrank_Dsp_prod`: `dim Dsp(U × U) = 2 · dim Dsp(U)`;
* `overF_count`: if `C ⊗_K V ≅ U × U` equivariantly (`C/K` finite) and `Dsp(V) ≠ 0`, then
  `[C:K] · dim Dsp(V) = 2 · dim Dsp(U)`.
This is the step "extension of the coefficient field is, on underlying `ℚ_ℓ`-representations, a
finite direct sum; the displayed decomposition therefore makes `r|G_F` de Rham" of N5's Lemma
`lem:de-rham-descent`, done by counting (no closure property of de Rham representations is used).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct

noncomputable section

section OverF

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  (act : G → B →ₗ[K] B)

theorem finrank_Dsp_congr {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank K (Dsp act ρ S) = finrank K (Dsp act ρ' S) := by
  let L : (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B) := LinearEquiv.arrowCongr e (LinearEquiv.refl K B)
  have hL : ∀ φ v', L φ v' = φ (e.symm v') := fun _ _ => rfl
  have hL' : ∀ φ' v, L.symm φ' v = φ' (e v) := fun _ _ => rfl
  have hmap : (Dsp act ρ S).map (L : (V →ₗ[K] B) →ₗ[K] (V' →ₗ[K] B)) = Dsp act ρ' S := by
    ext φ'
    constructor
    · rintro ⟨φ, hφ, rfl⟩ g hg v'
      have h1 : e.symm (ρ' g v') = ρ g (e.symm v') := by
        apply e.injective
        rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      change L φ (ρ' g v') = act g (L φ v')
      rw [hL, hL, h1, hφ g hg]
    · intro hφ'
      refine ⟨L.symm φ', ?_, by simp⟩
      intro g hg v
      rw [hL', hL', he, hφ' g hg]
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- The diagonal action on `ι → V`. -/
def piRep {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (ι : Type*) :
    G → (ι → V) →ₗ[K] (ι → V) :=
  fun g => LinearMap.pi fun i => ρ g ∘ₗ LinearMap.proj i

theorem piRep_apply {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (ι : Type*)
    (g : G) (v : ι → V) (i : ι) : piRep ρ ι g v i = ρ g (v i) := rfl

theorem piRep_single {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (ι : Type*) [DecidableEq ι] (g : G) (i : ι) (v : V) :
    piRep ρ ι g (Pi.single i v) = Pi.single i (ρ g v) := by
  funext j
  rw [piRep_apply]
  by_cases hij : j = i
  · subst hij; simp
  · simp [Pi.single_eq_of_ne hij]

/-- `Dsp(V^ι) ≅ Dsp(V)^ι`. -/
def DspPiEquiv {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Dsp act (piRep ρ ι) S ≃ₗ[K] (ι → Dsp act ρ S) :=
  { toFun := fun φ i => ⟨(φ : (ι → V) →ₗ[K] B) ∘ₗ LinearMap.single K (fun _ => V) i, by
      intro g hg v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
      rw [← piRep_single, φ.2 g hg]⟩
    map_add' := fun φ ψ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    map_smul' := fun c φ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    invFun := fun ψ => ⟨∑ i, ((ψ i : Dsp act ρ S) : V →ₗ[K] B) ∘ₗ LinearMap.proj i, by
      intro g hg v
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [piRep_apply, (ψ i).2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
      rw [← map_sum, Finset.univ_sum_single v]
    right_inv := fun ψ => by
      funext i
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Pi.single_eq_of_ne hji, map_zero]
      · intro h; exact absurd (Finset.mem_univ i) h }

theorem finrank_Dsp_pi {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] [FiniteDimensional K (Dsp act ρ S)] :
    finrank K (Dsp act (piRep ρ ι) S) = Fintype.card ι * finrank K (Dsp act ρ S) := by
  rw [(DspPiEquiv act ρ S ι).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- `Dsp(U × U) ≅ Dsp(U) × Dsp(U)`. -/
def DspProdEquiv {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G) :
    Dsp act (fun g => (ρ g).prodMap (ρ g)) S ≃ₗ[K] (Dsp act ρ S × Dsp act ρ S) :=
  { toFun := fun φ => (⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inl K V V, by
        intro g hg v
        have := φ.2 g hg (v, 0)
        simpa using this⟩,
      ⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inr K V V, by
        intro g hg v
        have := φ.2 g hg (0, v)
        simpa using this⟩)
    map_add' := fun φ ψ => by ext <;> simp
    map_smul' := fun c φ => by ext <;> simp
    invFun := fun ψ => ⟨(ψ.1 : V →ₗ[K] B).coprod (ψ.2 : V →ₗ[K] B), by
      intro g hg v
      simp only [LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
      rw [ψ.1.2 g hg, ψ.2.2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      ext v <;> simp
    right_inv := fun ψ => by
      ext v <;> simp }

theorem finrank_Dsp_prod {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) [FiniteDimensional K (Dsp act (fun g => (ρ g).prodMap (ρ g)) S)] :
    finrank K (Dsp act (fun g => (ρ g).prodMap (ρ g)) S) = 2 * finrank K (Dsp act ρ S) := by
  let E := DspProdEquiv act ρ S
  have hfin : FiniteDimensional K (Dsp act ρ S × Dsp act ρ S) :=
    LinearEquiv.finiteDimensional E
  have : FiniteDimensional K (Dsp act ρ S) :=
    Module.Finite.of_surjective (LinearMap.fst K (Dsp act ρ S) (Dsp act ρ S))
      LinearMap.fst_surjective
  rw [E.finrank_eq, Module.finrank_prod, two_mul]

/-- `C ⊗_K V ≅ V^ι` for a basis of `C` indexed by `ι`. -/
def tensorPiEquiv {C : Type*} [Field C] [Algebra K C] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bC : Basis ι K C) : C ⊗[K] V ≃ₗ[K] (ι → V) :=
  (TensorProduct.equivFinsuppOfBasisLeft bC).trans (Finsupp.linearEquivFunOnFinite K V ι)

theorem tensorPiEquiv_baseChange {C : Type*} [Field C] [Algebra K C] {V : Type*}
    [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (bC : Basis ι K C)
    (f : V →ₗ[K] V)
    (x : C ⊗[K] V) :
    tensorPiEquiv bC (f.baseChange C x) = fun i => f (tensorPiEquiv bC x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    funext i
    simp [tensorPiEquiv, LinearMap.baseChange_tmul]
  | add x y hx hy =>
    funext i
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

/-- **Counting through `C ⊗_K V ≅ U × U`.** -/
theorem overF_count {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x))
    (hpos : 0 < finrank K (Dsp act ρV S)) :
    finrank K C * finrank K (Dsp act ρV S) = 2 * finrank K (Dsp act ρU S) := by
  classical
  have : FiniteDimensional K (Dsp act ρV S) := Module.finite_of_finrank_pos hpos
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  have h1 : finrank K (Dsp act ρCV S) = finrank K C * finrank K (Dsp act ρV S) := by
    rw [finrank_Dsp_congr act ρCV (piRep ρV (Fin (finrank K C))) S (tensorPiEquiv bC)
      (fun g x => tensorPiEquiv_baseChange bC (ρV g) x), finrank_Dsp_pi, Fintype.card_fin]
  have h2 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    finrank_Dsp_congr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  have hfin : FiniteDimensional K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) := by
    apply Module.finite_of_finrank_pos
    rw [← h2, h1]
    exact Nat.mul_pos Module.finrank_pos hpos
  rw [← h1, h2, finrank_Dsp_prod]

/-- **Reverse count**: if `Dsp(U) ≠ 0` (finite-dimensional), then `Dsp(V) ≠ 0`. -/
theorem overF_pos_rev {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x))
    (hU : 0 < finrank K (Dsp act ρU S)) :
    0 < finrank K (Dsp act ρV S) := by
  classical
  have : FiniteDimensional K (Dsp act ρU S) := Module.finite_of_finrank_pos hU
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  have hUU : FiniteDimensional K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    LinearEquiv.finiteDimensional (DspProdEquiv act ρU S).symm
  have h2 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    finrank_Dsp_congr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  have h1 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (piRep ρV (Fin (finrank K C))) S) :=
    finrank_Dsp_congr act ρCV (piRep ρV (Fin (finrank K C))) S (tensorPiEquiv bC)
      (fun g x => tensorPiEquiv_baseChange bC (ρV g) x)
  have hpos : 0 < finrank K (Dsp act (piRep ρV (Fin (finrank K C))) S) := by
    rw [← h1, h2, finrank_Dsp_prod]
    omega
  have : FiniteDimensional K (Dsp act (piRep ρV (Fin (finrank K C))) S) :=
    Module.finite_of_finrank_pos hpos
  have hfinpi : FiniteDimensional K (Fin (finrank K C) → Dsp act ρV S) :=
    LinearEquiv.finiteDimensional (DspPiEquiv act ρV S _)
  have hc : 0 < finrank K C := Module.finrank_pos
  have : FiniteDimensional K (Dsp act ρV S) :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : Fin (finrank K C) =>
      Dsp act ρV S) ⟨0, hc⟩) (fun x => ⟨fun _ => x, rfl⟩)
  rw [finrank_Dsp_pi, Fintype.card_fin] at hpos
  exact Nat.pos_of_mul_pos_left hpos

end OverF

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Galois.lean

/-!
# G9: the image of `G_F` in `G_{ℚ_p}`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

For a finite Galois extension `F/ℚ_p`, pkg-I4's map `gfToGqp p F : G_F → G_{ℚ_p}` (Mathlib's
`Field.absoluteGaloisGroup.map`, restriction along a chosen embedding `ℚ̄_p → F̄`) has image the
kernel of the restriction `G_{ℚ_p} → Gal(F'/ℚ_p)`, where `F' ⊆ ℚ̄_p` is a copy of `F`
(`range_gfToGqp`). `F'` is finite Galois over `ℚ_p` with `[F':ℚ_p] = [F:ℚ_p]`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 Module

noncomputable section

section Galois

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- An element of `G_F` as an automorphism of `F̄`. -/
abbrev galF (σ : Field.absoluteGaloisGroup F) : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ

/-- `gfToGqp` is restriction along an embedding `g : ℚ̄_p → F̄` over `ℚ_p`. -/
theorem exists_emb_gfToGqp : ∃ g : PadicAlgCl p →+* AlgebraicClosure F,
    (∀ c : ℚ_[p], g (algebraMap ℚ_[p] (PadicAlgCl p) c) =
      algebraMap F (AlgebraicClosure F) (algebraMap ℚ_[p] F c)) ∧
    ∀ (σ : Field.absoluteGaloisGroup F) (x : PadicAlgCl p), g (gfToGqp p F σ x) = galF F σ (g x) := by
  let _i1 : Algebra ℚ_[p] F := (algebraMap ℚ_[p] F).toAlgebra
  let g0 : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure F := IsAlgClosed.lift
  let _i2 : Algebra (AlgebraicClosure ℚ_[p]) (AlgebraicClosure F) := g0.toAlgebra
  refine ⟨g0.toRingHom, fun c => g0.commutes c, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars ℚ_[p] σ)
    (AlgebraicClosure ℚ_[p]) x

/-- The embedding `ℚ̄_p → F̄` behind `gfToGqp`. -/
def embF : PadicAlgCl p →+* AlgebraicClosure F := (exists_emb_gfToGqp p F).choose

theorem embF_algebraMap (c : ℚ_[p]) : embF p F (algebraMap ℚ_[p] (PadicAlgCl p) c) =
    algebraMap F (AlgebraicClosure F) (algebraMap ℚ_[p] F c) :=
  (exists_emb_gfToGqp p F).choose_spec.1 c

theorem embF_gfToGqp (σ : Field.absoluteGaloisGroup F) (x : PadicAlgCl p) :
    embF p F (gfToGqp p F σ x) = galF F σ (embF p F x) :=
  (exists_emb_gfToGqp p F).choose_spec.2 σ x

theorem embF_bijective : Function.Bijective (embF p F) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro y
  have : Algebra.IsIntegral ℚ_[p] (AlgebraicClosure F) :=
    Algebra.IsIntegral.trans (R := ℚ_[p]) F
  have hy : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  apply RingHom.IsIntegralElem.of_comp (f := algebraMap ℚ_[p] (PadicAlgCl p))
  have hc : (embF p F).comp (algebraMap ℚ_[p] (PadicAlgCl p)) =
      algebraMap ℚ_[p] (AlgebraicClosure F) := by
    ext c
    rw [RingHom.comp_apply, embF_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [hc]
  exact hy

/-- `ℚ̄_p ≃ F̄`. -/
def embFEquiv : PadicAlgCl p ≃+* AlgebraicClosure F :=
  RingEquiv.ofBijective (embF p F) (embF_bijective p F)

theorem embFEquiv_apply (x : PadicAlgCl p) : embFEquiv p F x = embF p F x := rfl

/-- `F → ℚ̄_p`, `y ↦ g⁻¹(y)`. -/
def phiF : F →ₐ[ℚ_[p]] PadicAlgCl p where
  toRingHom := (embFEquiv p F).symm.toRingHom.comp (algebraMap F (AlgebraicClosure F))
  commutes' c := by
    apply (embFEquiv p F).injective
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Function.comp_apply, RingEquiv.apply_symm_apply, embFEquiv_apply, embF_algebraMap]

theorem embF_phiF (y : F) : embF p F (phiF p F y) = algebraMap F (AlgebraicClosure F) y := by
  rw [← embFEquiv_apply]
  exact (embFEquiv p F).apply_symm_apply _

/-- `F' ⊆ ℚ̄_p`, the copy of `F` with `G_F = G_{F'}` under `gfToGqp`. -/
def fieldF : IntermediateField ℚ_[p] (PadicAlgCl p) := (phiF p F).fieldRange

/-- `F ≃ F'`. -/
def equivFieldF : F ≃ₐ[ℚ_[p]] fieldF p F := (phiF p F).equivFieldRange

instance : FiniteDimensional ℚ_[p] (fieldF p F) :=
  LinearEquiv.finiteDimensional (equivFieldF p F).toLinearEquiv

theorem finrank_fieldF : finrank ℚ_[p] (fieldF p F) = finrank ℚ_[p] F :=
  (equivFieldF p F).toLinearEquiv.finrank_eq.symm

variable [IsGalois ℚ_[p] F]

instance : IsGalois ℚ_[p] (fieldF p F) := IsGalois.of_algEquiv (equivFieldF p F)

/-- The restriction `G_{ℚ_p} → Gal(F'/ℚ_p)`. -/
def gammaF : GQp p →* (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) :=
  AlgEquiv.restrictNormalHom (fieldF p F)

theorem gammaF_surjective : Function.Surjective (gammaF p F) :=
  AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)

theorem gammaF_apply_coe (τ : GQp p) (x : fieldF p F) :
    ((gammaF p F τ x : fieldF p F) : PadicAlgCl p) = τ (x : PadicAlgCl p) :=
  AlgEquiv.restrictNormal_commutes τ (fieldF p F) x

theorem mem_ker_gammaF (τ : GQp p) :
    τ ∈ (gammaF p F).ker ↔ ∀ y : F, τ (phiF p F y) = phiF p F y := by
  rw [gammaF, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y
    exact h _ ⟨y, rfl⟩
  · rintro h _ ⟨y, rfl⟩
    exact h y

/-- **The image of `G_F` is `ker(G_{ℚ_p} → Gal(F'/ℚ_p))`.** -/
theorem range_gfToGqp : (gfToGqp p F).range = (gammaF p F).ker := by
  ext τ
  rw [MonoidHom.mem_range, mem_ker_gammaF]
  constructor
  · rintro ⟨σ, rfl⟩ y
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp, embF_phiF]
    exact (galF F σ).commutes y
  · intro h
    -- `σ = g ∘ τ ∘ g⁻¹`, an `F`-automorphism of `F̄`
    let e := embFEquiv p F
    let σr : AlgebraicClosure F ≃+* AlgebraicClosure F :=
      (e.symm.trans τ.toRingEquiv).trans e
    have hσr : ∀ x, σr x = e (τ (e.symm x)) := fun _ => rfl
    let σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F :=
      { σr with
        commutes' := by
          intro y
          change σr (algebraMap F (AlgebraicClosure F) y) = _
          rw [hσr, ← embF_phiF p F y, ← embFEquiv_apply, RingEquiv.symm_apply_apply, h y,
            embFEquiv_apply, embF_phiF] }
    let σ' : Field.absoluteGaloisGroup F := σ
    refine ⟨σ', ?_⟩
    ext x
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp p F σ' x]
    change σr (embF p F x) = embF p F (τ x)
    rw [hσr, ← embFEquiv_apply, RingEquiv.symm_apply_apply]
    rfl

end Galois

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/BdRAct.lean

/-!
# G9: pkg-I4's actions of `G_{ℚ_p}` on `ℂ_p` and on `B_dR` are group actions

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

pkg-I4 (`I4Layer.lean`, verbatim) defines `cpAct p σ` on `ℂ_p` and `bdrAct p σ` on `B_dR` for each
`σ ∈ G_{ℚ_p}` separately. Here: `cpAct (σ τ) = cpAct σ ∘ cpAct τ`, `cpAct 1 = id`, the same for
`bdrAct` (functoriality of Mathlib's `B_dR` construction: mod `p`, tilt, Witt vectors,
localization, adic completion, localization), and the cyclotomic twists `cycPow` are
multiplicative. Packaged as monoid homomorphisms `htAct p i : G_{ℚ_p} →* End_{ℚ_p}(ℂ_p)`
(`c ↦ χ(σ)^i σ(c)`) and `drAct p : G_{ℚ_p} →* End_{ℚ_p}(B_dR)`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 Ideal

noncomputable section

namespace PkgI4.DR
open _root_.PkgI4.DR  -- (g0-assemble2) the root namespace holds Leaves.lean's `PkgI4.DR`

variable (p : ℕ) [Fact p.Prime] {O : Type*} [CommRing O]

theorem modPMap_comp (f g : O →+* O) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) := by
  ext x
  rfl

theorem modPMap_id : modPMap p (RingHom.id O) = RingHom.id _ := by
  ext x
  rfl

variable [Fact ¬IsUnit (p : O)]

theorem preTiltMap_comp (f g : O →+* O) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) := by
  ext x
  refine Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap, modPMap_comp]
  rfl

theorem preTiltMap_id : preTiltMap p (RingHom.id O) = RingHom.id _ := by
  ext x
  refine Perfection.ext fun n => ?_
  rw [coeff_preTiltMap, modPMap_id]
  rfl

theorem locMap_comp (f g : O →+* O) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt O p)))
  ext w
  simp only [RingHom.comp_apply, locMap, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  congr 1
  ext n
  simp only [WittVector.map_coeff, preTiltMap_comp, RingHom.comp_apply]

theorem locMap_id : locMap p (RingHom.id O) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt O p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  congr 1
  ext n
  simp only [WittVector.map_coeff, preTiltMap_id, RingHom.id_apply]

section AdicComp

variable {A : Type*} [CommRing A] (J : Ideal A)

theorem adicMap_comp' (g0 g : A →+* A) (h0 : J ≤ J.comap g0) (h : J ≤ J.comap g)
    (g' : A →+* A) (h' : J ≤ J.comap g') (hg' : g' = g.comp g0) :
    adicMap J J g' h' = (adicMap J J g h).comp (adicMap J J g0 h0) := by
  subst hg'
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, adicMap_evalₐ, adicMap_evalₐ, adicMapAux, adicMapAux,
    RingHom.comp_apply, RingHom.comp_apply]
  erw [adicMap_evalₐ]
  rw [adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

theorem adicMap_id' (g' : A →+* A) (h' : J ≤ J.comap g') (hg' : g' = RingHom.id A) :
    adicMap J J g' h' = RingHom.id _ := by
  subst hg'
  refine RingHom.ext fun x => ?_
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ, adicMapAux, RingHom.comp_apply, RingHom.id_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

end AdicComp

variable [IsAdicComplete (span {(p : O)}) O]

theorem bdrPlusMap_comp (f g : O →+* O) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) :=
  adicMap_comp' _ (locMap p f) (locMap p g) (ker_le_comap_locMap p f) (ker_le_comap_locMap p g)
    _ _ (locMap_comp p f g)

theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id O) = RingHom.id _ :=
  adicMap_id' _ _ _ (locMap_id p)

theorem bdrMap_comp (f g f' g' : O →+* O) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (hgf' : ∀ x, g' (f' x) = x) (hfg' : ∀ y, f' (g' y) = y)
    (h : O →+* O) (k : O →+* O) (hkh : ∀ x, k (h x) = x) (hhk : ∀ y, h (k y) = y)
    (hh : h = f'.comp f) :
    bdrMap p h k hkh hhk = (bdrMap p f' g' hgf' hfg').comp (bdrMap p f g hgf hfg) := by
  subst hh
  unfold bdrMap
  rw [IsLocalization.map_comp_map]
  apply IsLocalization.ringHom_ext (genMonoid p O)
  ext x
  simp only [RingHom.comp_apply, IsLocalization.map_eq, bdrPlusMap_comp]
  erw [IsLocalization.map_eq]
  rfl

theorem bdrMap_id (h : O →+* O) (k : O →+* O) (hkh : ∀ x, k (h x) = x) (hhk : ∀ y, h (k y) = y)
    (hh : h = RingHom.id O) :
    bdrMap p h k hkh hhk = RingHom.id _ := by
  subst hh
  unfold bdrMap
  apply IsLocalization.ringHom_ext (genMonoid p O)
  ext x
  simp only [RingHom.comp_apply, IsLocalization.map_eq, bdrPlusMap_id, RingHom.id_apply]

end PkgI4.DR

namespace PkgI4
open _root_.PkgI4  -- (g0-assemble2) the root namespace holds Leaves.lean's `PkgI4`

variable (p : ℕ) [Fact p.Prime]

theorem cpAct_mul_apply (σ τ : GQp p) (x : ℂ_[p]) :
    cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one_apply (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) := by
  ext x
  exact congrArg Subtype.val (Subtype.ext (cpAct_mul_apply p σ τ x) :
    oAct p (σ * τ) x = oAct p σ (oAct p τ x))

theorem oAct_one : oAct p 1 = RingHom.id _ := by
  ext x
  exact congrArg Subtype.val (Subtype.ext (cpAct_one_apply p x) : oAct p 1 x = x)

theorem bdrAct_mul (σ τ : GQp p) : bdrAct p (σ * τ) = (bdrAct p σ).comp (bdrAct p τ) :=
  DR.bdrMap_comp p _ _ _ _ _ _ _ _ _ _ _ _ (oAct_mul p σ τ)

theorem bdrAct_one : bdrAct p 1 = RingHom.id _ :=
  DR.bdrMap_id p _ _ _ _ (oAct_one p)

theorem cycPow_mul (σ τ : GQp p) (i : ℤ) : cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  have h : cyc p (σ * τ) = cyc p σ * cyc p τ := by
    simp only [cyc]
    rw [← map_mul]
    rfl
  simp only [cycPow, h, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one (i : ℤ) : cycPow p 1 i = 1 := by
  have h : cyc p 1 = 1 := by
    simp only [cyc]
    rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
    rfl
  simp [cycPow, h]

/-- `σ ↦ (c ↦ χ(σ)^i σ(c))`, the action of `G_{ℚ_p}` on `ℂ_p(i)`, as a monoid homomorphism. -/
def htAct (i : ℤ) : GQp p →* (ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun σ :=
    { toFun := fun c => cycPow p σ i • cpAct p σ c
      map_add' := fun a b => by rw [map_add, smul_add]
      map_smul' := fun c a => by
        rw [Algebra.smul_def c a, map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]
        rfl }
  map_one' := by
    ext c
    simp [cycPow_one, cpAct_one_apply]
  map_mul' σ τ := by
    ext c
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, cycPow_mul,
      cpAct_mul_apply, mul_smul]
    rw [Algebra.smul_def (cycPow p τ i) (cpAct p τ c), map_mul, cpAct_algebraMap,
      ← Algebra.smul_def, smul_comm]

theorem htAct_apply (i : ℤ) (σ : GQp p) (c : ℂ_[p]) :
    htAct p i σ c = cycPow p σ i • cpAct p σ c := rfl

/-- `σ ↦ bdrAct σ`, the action of `G_{ℚ_p}` on `B_dR`, as a monoid homomorphism to
`ℚ_p`-linear endomorphisms. -/
def drAct : GQp p →* (BdR p →ₗ[ℚ_[p]] BdR p) where
  toFun σ :=
    { toFun := bdrAct p σ
      map_add' := map_add _
      map_smul' := bdrAct_smul p σ }
  map_one' := LinearMap.ext fun c => by
    change bdrAct p 1 c = c
    rw [bdrAct_one]
    rfl
  map_mul' σ τ := LinearMap.ext fun c => by
    change bdrAct p (σ * τ) c = bdrAct p σ (bdrAct p τ c)
    rw [bdrAct_mul]
    rfl

theorem drAct_apply (σ : GQp p) (c : BdR p) : drAct p σ c = bdrAct p σ c := rfl

end PkgI4

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/KerTheta.lean

/-!
# G9: `B_dR^+` is a complete DVR with residue map `θ⁺ : B_dR^+ → ℂ_p` (bdr-kertheta, restated)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

**Source.** `scratch/bdr-kertheta/KerTheta.lean` at fork main `883c4ddf` (task bdr-kertheta),
copied verbatim, wrapped in the namespace `ZInQ.Contrib.G9`, with one deletion: its section
`PkgI4.Cp` (lines 246-347 there) is byte-for-byte identical to the section `PkgI4.Cp` of
`I4Layer.lean` (checked with `diff`), so it is imported instead of repeated. Used here:
`isAdicComplete_BDeRhamPlus`, `isDomain_BDeRhamPlus`, `isLocalRing_BDeRhamPlus`,
`thetaPlusCp`, `thetaPlusCp_surjective`, `ker_thetaPlusCp`, `isFractionRing_BDeRham`.
-/

namespace ZInQ.Contrib.G9


/-!
# bdr-kertheta: `ker θ` is principal

Part A: a complete-Nakayama criterion for the kernel of a ring map out of a `p`-adically complete
ring. Part B: inverting `p`. Part C: Fontaine's `θ` for a general `p`-adically complete `O`,
reduced to one divisibility statement in the tilt.
-/

open Ideal

namespace BdrKer

section PartA

variable {A B : Type*} [CommRing A] [CommRing B] (p : ℕ)

theorem mem_span_pow_iff' (n : ℕ) (x : A) :
    x ∈ (span {(p : A)} ^ n • ⊤ : Submodule A A) ↔ ∃ c, x = (p : A) ^ n * c := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, mul_comm _ _⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, mul_comm _ _⟩

/-- **Part A.** If `A` is `p`-adically complete, `p` is a non-zero-divisor on `B`, and
`ker θ ⊆ ξ A + p A` for some `ξ ∈ ker θ`, then `ker θ = ξ A`. -/
theorem ker_eq_span_of_mod_p [IsAdicComplete (span {(p : A)}) A] (θ : A →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (ξ : A) (hξ : θ ξ = 0)
    (h : ∀ x, θ x = 0 → ∃ y z, x = ξ * y + p * z) :
    RingHom.ker θ = span {ξ} := by
  apply le_antisymm
  · intro x hx
    have h' : ∀ x : RingHom.ker θ, ∃ y : A, ∃ z : RingHom.ker θ, x.1 = ξ * y + p * z.1 := by
      intro x
      obtain ⟨y, z, hyz⟩ := h x.1 x.2
      refine ⟨y, ⟨z, ?_⟩, hyz⟩
      have : θ x.1 = 0 := x.2
      rw [hyz, map_add, map_mul, map_mul, hξ, zero_mul, zero_add, map_natCast] at this
      exact hB _ this
    choose Y Z hYZ using h'
    let s : ℕ → RingHom.ker θ := fun n => Nat.rec ⟨x, hx⟩ (fun _ w => Z w) n
    let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, (p : A) ^ k * Y (s k)
    have hS : ∀ n, x = ξ * S n + (p : A) ^ n * (s n).1 := by
      intro n
      induction n with
      | zero => simp [S, s]
      | succ n ih =>
        have e : (s (n + 1)) = Z (s n) := rfl
        rw [ih, hYZ (s n), ← e]
        simp only [S, Finset.sum_range_succ]
        ring
    have hdiff : ∀ m d, ∃ c, S (m + d) - S m = (p : A) ^ m * c := by
      intro m d
      induction d with
      | zero => exact ⟨0, by simp⟩
      | succ d ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨c + (p : A) ^ d * Y (s (m + d)), ?_⟩
        have : S (m + (d + 1)) = S (m + d) + (p : A) ^ (m + d) * Y (s (m + d)) := by
          simp only [S, ← add_assoc, Finset.sum_range_succ]
        rw [this, pow_add]
        linear_combination hc
    have hcauchy : ∀ {m n}, m ≤ n →
        S m ≡ S n [SMOD (span {(p : A)} ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [SModEq.sub_mem, mem_span_pow_iff']
      obtain ⟨c, hc⟩ := hdiff m d
      exact ⟨-c, by linear_combination -hc⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hcauchy
    have hx : x = ξ * L := by
      rw [← sub_eq_zero]
      apply IsHausdorff.haus' (I := span {(p : A)})
      intro n
      rw [SModEq.sub_mem, sub_zero, mem_span_pow_iff']
      have := hL n
      rw [SModEq.sub_mem, mem_span_pow_iff'] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨ξ * c + (s n).1, ?_⟩
      linear_combination hS n + ξ * hc
    rw [hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ξ)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hξ

end PartA


section PartB

variable {A B : Type*} [CommRing A] [CommRing B] (p : ℕ)

theorem pow_mul_eq_zero {B : Type*} [CommRing B] {p : ℕ}
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (k : ℕ) (b : B) (h : (p : B) ^ k * b = 0) :
    b = 0 := by
  induction k generalizing b with
  | zero => simpa using h
  | succ k ih => exact ih b (hB _ (by rw [← h]; ring))

/-- **Part B.** Inverting `p`: if `ker θ = ξ A` and `p` is a non-zero-divisor on `B`, then the
kernel of `θ[1/p] : A[1/p] → B[1/p]` is generated by `ξ`. -/
theorem ker_awayLift_eq_span (θ : A →+* B) (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (ξ : A)
    (hker : RingHom.ker θ = span {ξ})
    (hu : IsUnit (((algebraMap B (Localization.Away (p : B))).comp θ) (p : A))) :
    RingHom.ker (Localization.awayLift ((algebraMap B (Localization.Away (p : B))).comp θ)
      (p : A) hu) = span {algebraMap A (Localization.Away (p : A)) ξ} := by
  set L := Localization.awayLift ((algebraMap B (Localization.Away (p : B))).comp θ) (p : A) hu
  have hLa : ∀ a : A, L (algebraMap A _ a) = algebraMap B _ (θ a) := fun a =>
    IsLocalization.Away.lift_eq (p : A) hu a
  apply le_antisymm
  · intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : A)) z
    have hspec := IsLocalization.mk'_spec (Localization.Away (p : A)) a s
    have h1 : algebraMap B (Localization.Away (p : B)) (θ a) = 0 := by
      rw [← hLa, ← hspec, map_mul, RingHom.mem_ker.mp hz, zero_mul]
    obtain ⟨⟨m, k, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : B)) _ _).mp h1
    have h2 : θ a = 0 := pow_mul_eq_zero hB k _ hm
    have h3 : a ∈ span {ξ} := hker ▸ RingHom.mem_ker.mpr h2
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp h3
    refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' (Localization.Away (p : A)) c s, ?_⟩
    show _ = IsLocalization.mk' (Localization.Away (p : A)) (c * ξ) s
    rw [IsLocalization.mk'_eq_mul_mk'_one c, IsLocalization.mk'_eq_mul_mk'_one (c * ξ), map_mul]
    ring
  · have hξ : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ξ
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hLa, hξ,
      map_zero]

end PartB

section PartC

open WittVector

variable {O : Type*} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/-- **Part C.** For a `p`-adically complete, `p`-torsion-free ring `O` and `ϖ ∈ O♭` with
`ϖ♯ = p` such that every `c ∈ O♭` with `c♯ ∈ pO` is divisible by `ϖ`, the kernel of
Fontaine's `θ : W(O♭) → O` is generated by `p − [ϖ]`. -/
theorem ker_fontaineTheta_eq_span (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ϖ : PreTilt O p) (hϖ : ϖ.untilt = p)
    (hdiv : ∀ c : PreTilt O p, PreTilt.coeff 0 c = 0 → ∃ d, c = ϖ * d) :
    RingHom.ker (fontaineTheta O p) =
      span {(p : WittVector p (PreTilt O p)) - teichmuller p ϖ} := by
  apply ker_eq_span_of_mod_p p _ hO
  · simp [hϖ]
  · intro x hx
    have h0 : PreTilt.coeff 0 (x.coeff 0) = 0 := by
      rw [← mk_fontaineTheta, hx, map_zero]
    obtain ⟨d, hd⟩ := hdiv _ h0
    have hmem : x - teichmuller p (x.coeff 0) ∈ span {(p : WittVector p (PreTilt O p))} := by
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub]
      simp
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨-teichmuller p d, teichmuller p d + w, ?_⟩
    rw [hd, map_mul] at hw
    linear_combination -hw

/-- Part B specialised: the kernel of Mathlib's `fontaineThetaInvertP` is principal. -/
theorem ker_fontaineThetaInvertP_eq_span (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ξ : WittVector p (PreTilt O p)) (hker : RingHom.ker (fontaineTheta O p) = span {ξ}) :
    RingHom.ker (fontaineThetaInvertP O p) =
      span {algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ} :=
  ker_awayLift_eq_span p (fontaineTheta O p) hO ξ hker
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O))

variable (O p) in
/-- The submonoid of `B_dR^+(O)` inverted in Mathlib's `BDeRham O p` (copied from its body). -/
noncomputable abbrev genMonoid : Submonoid (BDeRhamPlus O p) :=
  Submonoid.closure <| AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP O p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP O p)) = Ideal.span {a}}

variable (O p) in
noncomputable abbrev BdR := Localization (genMonoid O p)

example : BdR O p = BDeRham O p := rfl

/-- Consequence for `B_dR`: the generator set Mathlib inverts is non-empty, and the image of
`ξ` is a unit of `BDeRham`. -/
theorem isUnit_xi_BDeRham (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ξ : WittVector p (PreTilt O p)) (hker : RingHom.ker (fontaineTheta O p) = span {ξ}) :
    IsUnit (algebraMap (BDeRhamPlus O p) (BdR O p)
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP O p)) _
        (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ))) :=
  IsLocalization.map_units (BdR O p) (⟨_, Submonoid.subset_closure
    ⟨_, (ker_fontaineThetaInvertP_eq_span hO ξ hker), rfl⟩⟩ : genMonoid O p)

variable (O p) in
/-- The canonical map `W(O♭)[1/p] → B_dR^+(O)`, typed into `BDeRhamPlus`. -/
noncomputable abbrev ofPlus (x : Localization.Away (p : WittVector p (PreTilt O p))) :
    BDeRhamPlus O p :=
  AdicCompletion.of (RingHom.ker (fontaineThetaInvertP O p)) _ x

theorem adicCompletion_of_mul {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
    AdicCompletion.of I R (x * y) = AdicCompletion.of I R x * AdicCompletion.of I R y :=
  show algebraMap R (AdicCompletion I R) (x * y) = algebraMap R _ x * algebraMap R _ y from
    map_mul _ x y

/-- **`B_dR = B_dR^+[1/ξ]`.** If `ker θ = (ξ)`, Mathlib's `BDeRham` (all generators of `ker θ[1/p]`
inverted) is the localization of `BDeRhamPlus` at the powers of the single element `ξ`:
`Localization.Away ξ` is a localization at Mathlib's submonoid. -/
theorem isLocalization_away_xi (hO : ∀ b : O, (p : O) * b = 0 → b = 0)
    (ξ : WittVector p (PreTilt O p)) (hker : RingHom.ker (fontaineTheta O p) = span {ξ}) :
    IsLocalization (genMonoid O p) (Localization.Away
      (ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ))) := by
  have hk := ker_fontaineThetaInvertP_eq_span hO ξ hker
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers
    (ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ)))
    (genMonoid O p) ?_ ?_
  · rw [Submonoid.powers_le]
    exact Submonoid.subset_closure ⟨_, hk, rfl⟩
  · intro n hn
    induction hn using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have : algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ ∈ span {a} := by
        rw [← (show _ = span {a} from ha), hk]; exact Ideal.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
      refine ⟨_, ⟨1, rfl⟩, ?_⟩
      show ofPlus O p a ∣
        ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ) ^ 1
      rw [pow_one, ← hc]
      exact ⟨ofPlus O p c, (adicCompletion_of_mul _ c a).trans (mul_comm _ _)⟩
    | one => exact ⟨1, ⟨0, pow_zero _⟩, one_dvd _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hy
      refine ⟨_, ⟨i + j, rfl⟩, ?_⟩
      show x * y ∣
        ofPlus O p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt O p))) ξ) ^ (i + j)
      rw [pow_add]
      exact mul_dvd_mul hi hj

end PartC

end BdrKer


/-! ## Part D: `𝓞_ℂ_[p]`.
The section `PkgI4.Cp` below is copied unchanged from `scratch/pkg-I4/I4.lean` (instances:
`𝓞_ℂ_[p]` is `p`-adically complete). -/


namespace BdrKer.Cp

open Ideal PkgI4.Cp WittVector

variable (p : ℕ) [hp : Fact p.Prime]

local notation "O" => (𝓞_ℂ_[p] : Type)

/-- The `n`-th `p`-power root `x^{(n)} = (F^{-n} x)♯` of `x♯`. -/
noncomputable def root {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime] [Fact ¬IsUnit (q : R)]
    [IsAdicComplete (span {(q : R)}) R] (x : PreTilt R q) (n : ℕ) : R :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt R q) q).symm^[n]) x)

section general
variable {R : Type*} [CommRing R] {q : ℕ} [Fact q.Prime] [Fact ¬IsUnit (q : R)]
    [IsAdicComplete (span {(q : R)}) R]

theorem root_pow (x : PreTilt R q) (n : ℕ) : root x n ^ q ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

theorem root_succ_pow (x : PreTilt R q) (n : ℕ) : root x (n + 1) ^ q = root x n := by
  rw [root, root, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem mk_root (x : PreTilt R q) (n : ℕ) :
    Ideal.Quotient.mk (span {(q : R)}) (root x n) = PreTilt.coeff n x := by
  rw [root, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

end general

theorem p_ne_zero : (p : O) ≠ 0 := fun h => by
  have h1 := norm_p_pos p
  have : ((p : O) : ℂ_[p]) = 0 := by rw [h]; rfl
  push_cast at this
  rw [this, norm_zero] at h1
  exact lt_irrefl _ h1

theorem p_regular (b : O) (h : (p : O) * b = 0) : b = 0 :=
  (mul_eq_zero.mp h).resolve_left (p_ne_zero p)

theorem norm_le_one (x : O) : ‖(x : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp x.2

/-- **Divisibility in the tilt.** If `ϖ♯ = p`, every `c ∈ O♭` with `coeff 0 c = 0` is a multiple
of `ϖ`. -/
theorem dvd_of_coeff_zero (ϖ : PreTilt O p) (hϖ : ϖ.untilt = p) (c : PreTilt O p)
    (hc : PreTilt.coeff 0 c = 0) : ∃ d, c = ϖ * d := by
  -- `‖c♯‖ ≤ ‖p‖`
  have hc0 : ‖((c.untilt : O) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
    have : c.untilt ∈ span {(p : O)} ^ 1 := by
      rw [pow_one, ← Ideal.Quotient.eq_zero_iff_mem, PreTilt.mk_untilt_eq_coeff_zero, hc]
    simpa using (mem_span_pow_iff p _ 1).mp this
  have hϖn : ∀ n, ‖((root ϖ n : O) : ℂ_[p])‖ ^ p ^ n = ‖(p : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : O => ‖(z : ℂ_[p])‖) (root_pow ϖ n)
    rw [hϖ] at h
    simpa [norm_pow] using h
  have hcn : ∀ n, ‖((root c n : O) : ℂ_[p])‖ ^ p ^ n = ‖((c.untilt : O) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : O => ‖(z : ℂ_[p])‖) (root_pow c n)
    simpa [norm_pow] using h
  have hne : ∀ n, ((root ϖ n : O) : ℂ_[p]) ≠ 0 := fun n h0 => by
    have := hϖn n
    rw [h0, norm_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at this
    exact (ne_of_lt (norm_p_pos p)) this
  have hle : ∀ n, ‖((root c n : O) : ℂ_[p])‖ ≤ ‖((root ϖ n : O) : ℂ_[p])‖ := fun n => by
    have hpn : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn).mp ?_
    rw [hcn, hϖn]; exact hc0
  let e : ℕ → O := fun n => ⟨((root c n : O) : ℂ_[p]) / ((root ϖ n : O) : ℂ_[p]),
    (mem_O_iff p _).mpr (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have he : ∀ n, e (n + 1) ^ p = e n := fun n => by
    apply Subtype.ext
    simp only [e, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, root_succ_pow, root_succ_pow]
  have hce : ∀ n, root c n = root ϖ n * e n := fun n => by
    apply Subtype.ext
    simp only [e, MulMemClass.coe_mul]
    field_simp [hne n]
  let d : PreTilt O p := ⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by
    rw [← map_pow, he]⟩
  refine ⟨d, ?_⟩
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n (ϖ * d)
  rw [map_mul]
  change PreTilt.coeff n c = PreTilt.coeff n ϖ * Ideal.Quotient.mk _ (e n)
  rw [← mk_root, ← mk_root, ← map_mul, hce]

/-- A compatible system of `p`-power roots of `p` in `ℂ_p`. -/
noncomputable def rootsOfP : ℕ → ℂ_[p]
  | 0 => p
  | n + 1 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (rootsOfP n) hp.out.pos)

theorem rootsOfP_succ_pow (n : ℕ) : rootsOfP p (n + 1) ^ p = rootsOfP p n :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (rootsOfP p n) hp.out.pos)

theorem rootsOfP_pow (n : ℕ) : rootsOfP p n ^ p ^ n = p := by
  induction n with
  | zero => simp [rootsOfP]
  | succ n ih => rw [pow_succ', pow_mul, rootsOfP_succ_pow, ih]

theorem norm_rootsOfP_le (n : ℕ) : ‖rootsOfP p n‖ ≤ 1 := by
  induction n with
  | zero => exact (mem_O_iff p _).mp (p : O).2
  | succ n ih =>
    rw [← rootsOfP_succ_pow] at ih
    rw [norm_pow] at ih
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp ih

/-- `p♭ = (p, p^{1/p}, p^{1/p²}, …) ∈ 𝓞_ℂ_p♭`. -/
noncomputable def pFlat : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk _ ⟨rootsOfP p n, (mem_O_iff p _).mpr (norm_rootsOfP_le p n)⟩,
    fun n => by
      rw [← map_pow]
      congr 1
      exact Subtype.ext (by simpa using rootsOfP_succ_pow p n)⟩

theorem untilt_pFlat : (pFlat p).untilt = p := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : O)})]
  intro n
  rw [SModEq.sub_mem, mem_span_pow_iff']
  have h1 : root (pFlat p) n - ⟨rootsOfP p n, (mem_O_iff p _).mpr (norm_rootsOfP_le p n)⟩ ∈
      span {(p : O)} := by
    rw [← Ideal.Quotient.eq, mk_root]; rfl
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow] at h2
  have h3 : (⟨rootsOfP p n, (mem_O_iff p _).mpr (norm_rootsOfP_le p n)⟩ : O) ^ p ^ n = p :=
    Subtype.ext (by simpa using rootsOfP_pow p n)
  rw [h3] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨p * c, by rw [hc]; ring⟩

/-- Fontaine's generator `ξ = p − [p♭] ∈ W(𝓞_ℂ_p♭)`. -/
noncomputable def xi : WittVector p (PreTilt O p) :=
  (p : WittVector p (PreTilt O p)) - teichmuller p (pFlat p)

/-- **Main theorem.** The kernel of Fontaine's `θ : W(𝓞_ℂ_p♭) → 𝓞_ℂ_p` is generated by
`ξ = p − [p♭]`. -/
theorem ker_fontaineTheta_Cp : RingHom.ker (fontaineTheta O p) = span {xi p} :=
  ker_fontaineTheta_eq_span (p_regular p) (pFlat p) (untilt_pFlat p)
    (dvd_of_coeff_zero p (pFlat p) (untilt_pFlat p))

/-- The image of `ξ` in `W(𝓞_ℂ_p♭)[1/p]`. -/
noncomputable def xi' : Localization.Away (p : WittVector p (PreTilt O p)) :=
  algebraMap _ _ (xi p)

/-- **Main theorem, Mathlib's form.** The kernel of `fontaineThetaInvertP` (θ with `p`
inverted, the ideal along which Mathlib completes to get `BDeRhamPlus`) is principal,
generated by the image of `ξ = p − [p♭]`. -/
theorem ker_fontaineThetaInvertP_Cp :
    RingHom.ker (fontaineThetaInvertP O p) = span {xi' p} :=
  ker_fontaineThetaInvertP_eq_span (p_regular p) _ (ker_fontaineTheta_Cp p)

/-- Hence `BDeRham 𝓞_ℂ_p` inverts `ξ` (Mathlib's generator set is non-empty). -/
theorem isUnit_xi_BDeRham_Cp :
    IsUnit (algebraMap (BDeRhamPlus O p) (BdR O p)
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP O p)) _ (xi' p))) :=
  isUnit_xi_BDeRham (p_regular p) _ (ker_fontaineTheta_Cp p)

/-- **`B_dR(𝓞_ℂ_p) ≅ B_dR^+[1/ξ]`**, `ξ = p − [p♭]`: Mathlib's `BDeRham 𝓞_ℂ_[p] p` is
isomorphic, as a `BDeRhamPlus`-algebra, to the localization of `BDeRhamPlus` away from `ξ`. -/
noncomputable def bdREquivAway :
    BdR O p ≃ₐ[BDeRhamPlus O p] Localization.Away (ofPlus O p (xi' p)) :=
  haveI : IsLocalization (genMonoid O p) (Localization.Away (ofPlus O p (xi' p))) :=
    isLocalization_away_xi (p_regular p) (xi p) (ker_fontaineTheta_Cp p)
  IsLocalization.algEquiv (genMonoid O p) _ _

/-! ### Toward the DVR property: `(ξ')` is a maximal ideal of `W(𝓞_ℂ_p♭)[1/p]`. -/

theorem frobenius_surjective : Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x' : ℂ_[p]) hp.out.pos
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_le_one p x'
    rw [← hy, norm_pow] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp h
  refine ⟨Ideal.Quotient.mk _ ⟨y, (mem_O_iff p _).mpr hy1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  congr 1
  exact Subtype.ext (by simpa using hy)

theorem fontaineTheta_surjective : Function.Surjective (fontaineTheta O p) :=
  surjective_fontaineTheta (frobenius_surjective p)

/-- `𝓞_ℂ_p[1/p]` is a field. -/
theorem isField_away_p : IsField (Localization.Away (p : O)) := by
  have h10 : (1 : Localization.Away (p : O)) ≠ 0 := by
    intro h
    rw [← map_one (algebraMap O (Localization.Away (p : O)))] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : O)) _ _).mp h
    exact pow_ne_zero k (p_ne_zero p) (by simpa using hk)
  refine ⟨⟨0, 1, h10.symm⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : O)) a
  have hx : (x : ℂ_[p]) ≠ 0 := by
    intro h0
    apply ha
    have : x = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hx) (norm_p_lt_one p)
  have hc : ‖(p : ℂ_[p]) ^ m / (x : ℂ_[p])‖ ≤ 1 := by
    rw [norm_div, norm_pow]; exact div_le_one_of_le₀ hm.le (norm_nonneg _)
  let c : O := ⟨(p : ℂ_[p]) ^ m / (x : ℂ_[p]), (mem_O_iff p _).mpr hc⟩
  have hxc : x * c = (p : O) ^ m := by
    apply Subtype.ext
    simp only [c, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    field_simp
    rfl
  refine ⟨IsLocalization.mk' _ (c * s) (⟨(p : O) ^ m, m, rfl⟩ : Submonoid.powers (p : O)), ?_⟩
  rw [← IsLocalization.mk'_mul, ← mul_assoc, hxc, IsLocalization.mk'_eq_iff_eq_mul, one_mul]
  congr 1
  rw [Submonoid.coe_mul, mul_comm]

/-- `θ[1/p] : W(𝓞_ℂ_p♭)[1/p] → 𝓞_ℂ_p[1/p]` is surjective. -/
theorem fontaineThetaInvertP_surjective : Function.Surjective (fontaineThetaInvertP O p) := by
  intro t
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : O)) t
  obtain ⟨w, rfl⟩ := fontaineTheta_surjective p r
  refine ⟨IsLocalization.mk' _ w
    (⟨(p : WittVector p (PreTilt O p)) ^ n, n, rfl⟩ : Submonoid.powers _), ?_⟩
  have hL : ∀ a, fontaineThetaInvertP O p (algebraMap _ _ a) =
      algebraMap O (Localization.Away (p : O)) (fontaineTheta O p a) := fun a =>
    IsLocalization.Away.lift_eq _ (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O)) a
  show _ = IsLocalization.mk' _ (fontaineTheta O p w) (⟨(p : O) ^ n, n, rfl⟩ : Submonoid.powers _)
  have hu : IsUnit (algebraMap O (Localization.Away (p : O)) ((p : O) ^ n)) :=
    IsLocalization.map_units _ (⟨(p : O) ^ n, n, rfl⟩ : Submonoid.powers (p : O))
  apply hu.mul_right_cancel
  have h1 := IsLocalization.mk'_spec (Localization.Away (p : WittVector p (PreTilt O p))) w
    (⟨(p : WittVector p (PreTilt O p)) ^ n, n, rfl⟩ : Submonoid.powers _)
  have h2 := IsLocalization.mk'_spec (Localization.Away (p : O)) (fontaineTheta O p w)
    (⟨(p : O) ^ n, n, rfl⟩ : Submonoid.powers (p : O))
  simp only at h1 h2
  rw [h2]
  have h3 := congrArg (fontaineThetaInvertP O p) h1
  rw [map_mul, hL, hL, map_pow, map_natCast] at h3
  exact h3

/-- **`ker θ[1/p] = (ξ')` is a maximal ideal** of `W(𝓞_ℂ_p♭)[1/p]` (residue field
`𝓞_ℂ_p[1/p]`). -/
theorem ker_fontaineThetaInvertP_isMaximal : (RingHom.ker (fontaineThetaInvertP O p)).IsMaximal :=
  letI := (isField_away_p p).toField
  RingHom.ker_isMaximal_of_surjective _ (fontaineThetaInvertP_surjective p)

/-! ### Step 1 of §3: `W(𝓞_ℂ_p♭)[1/p]` is a domain and `ξ'` is a non-zero-divisor. -/

instance isDomain_tilt : IsDomain (PreTilt O p) :=
  PreTilt.isDomain ℂ_[p] (PadicComplex.valued p).v O (PadicComplexInt.integers p) p

theorem witt_p_ne_zero : (p : WittVector p (PreTilt O p)) ≠ 0 := by
  intro h
  have : (1 : WittVector p (PreTilt O p)) = 0 :=
    WittVector.eq_zero_of_p_mul_eq_zero _ (by rw [one_mul, h])
  exact one_ne_zero this

instance isDomain_away : IsDomain (Localization.Away (p : WittVector p (PreTilt O p))) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))

theorem xi_ne_zero : xi p ≠ 0 := by
  intro h
  have h1 : WittVector.constantCoeff (xi p) = 0 := by rw [h, map_zero]
  rw [xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, neg_eq_zero] at h1
  have h2 : pFlat p = 0 := by simpa using h1
  have h3 := untilt_pFlat p
  rw [← fontaineTheta_teichmuller, h2, WittVector.teichmuller_zero, map_zero] at h3
  exact p_ne_zero p h3.symm

theorem xi'_ne_zero : xi' p ≠ 0 := by
  intro h
  apply xi_ne_zero p
  exact (IsLocalization.injective (Localization.Away (p : WittVector p (PreTilt O p)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))) (by rw [map_zero]; exact h)

/-- `ξ'` is a non-zero-divisor of `W(𝓞_ℂ_p♭)[1/p]`. -/
theorem xi'_mem_nonZeroDivisors :
    xi' p ∈ nonZeroDivisors (Localization.Away (p : WittVector p (PreTilt O p))) :=
  mem_nonZeroDivisors_of_ne_zero (xi'_ne_zero p)

/-! ### Non-triviality: `ξ` is not nilpotent in `B_dR^+`, so `B_dR = B_dR^+[1/ξ] ≠ 0`. -/

theorem ofPlus_xi'_pow_ne_zero (n : ℕ) : ofPlus O p (xi' p) ^ n ≠ 0 := by
  intro h
  set I := RingHom.ker (fontaineThetaInvertP O p)
  have h1 : AdicCompletion.evalₐ I (n + 1) (AdicCompletion.of I _ (xi' p ^ n)) = 0 := by
    have e : AdicCompletion.of I _ (xi' p ^ n) = ofPlus O p (xi' p) ^ n :=
      show algebraMap _ (AdicCompletion I _) (xi' p ^ n) = _ from map_pow _ _ _
    rw [e]; exact (congrArg _ h).trans (map_zero _)
  have hI : I = span {xi' p} := ker_fontaineThetaInvertP_Cp p
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem, hI,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, hc⟩ := h1
  have hx := xi'_ne_zero p
  have h2 : c * xi' p = 1 := by
    have : xi' p ^ n * (c * xi' p - 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hx
    · exact sub_eq_zero.mp h
  have h3 : RingHom.ker (fontaineThetaInvertP O p) = ⊤ := by
    rw [ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_eq_top]
    exact isUnit_iff_exists_inv.mpr ⟨c, by rw [mul_comm]; exact h2⟩
  exact (ker_fontaineThetaInvertP_isMaximal p).ne_top h3

instance nontrivial_away_xi : Nontrivial (Localization.Away (ofPlus O p (xi' p))) := by
  refine ⟨0, 1, fun h => ?_⟩
  have h' : algebraMap (BDeRhamPlus O p) (Localization.Away (ofPlus O p (xi' p))) 1 = 0 := by
    rw [map_one]; exact h.symm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (ofPlus O p (xi' p))) _ _).mp h'
  exact ofPlus_xi'_pow_ne_zero p k (by simpa using hk)

/-- **`BDeRham 𝓞_ℂ_[p] p` is not the zero ring.** -/
theorem nontrivial_BDeRham : Nontrivial (BdR O p) :=
  (bdREquivAway p).symm.injective.nontrivial

/-! ### `B_dR^+(𝓞_ℂ_p)` is a discrete valuation ring with uniformizer `ξ`. -/

theorem ker_fg : (RingHom.ker (fontaineThetaInvertP O p)).FG :=
  ⟨{xi' p}, by rw [Finset.coe_singleton, ker_fontaineThetaInvertP_Cp]⟩

theorem map_ker_eq :
    (RingHom.ker (fontaineThetaInvertP O p)).map
      (algebraMap _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP O p))
        (Localization.Away (p : WittVector p (PreTilt O p))))) =
      (span {ofPlus O p (xi' p)} : Ideal (BDeRhamPlus O p)) := by
  have h1 := congrArg (Ideal.map (algebraMap _ (AdicCompletion (RingHom.ker
    (fontaineThetaInvertP O p)) (Localization.Away (p : WittVector p (PreTilt O p))))))
    (ker_fontaineThetaInvertP_Cp p)
  rw [Ideal.map_span, Set.image_singleton] at h1
  exact h1

instance isAdicComplete_BDeRhamPlus :
    IsAdicComplete (span {ofPlus O p (xi' p)} : Ideal (BDeRhamPlus O p)) (BDeRhamPlus O p) := by
  have := AdicCompletion.isAdicComplete_self _ (ker_fg p)
  rw [map_ker_eq] at this
  exact this

instance isMaximal_span_xi : (span {ofPlus O p (xi' p)} : Ideal (BDeRhamPlus O p)).IsMaximal := by
  have := ker_fontaineThetaInvertP_isMaximal p
  have := AdicCompletion.isMaximal_map_of_le _ _ le_rfl (ker_fg p)
  rw [map_ker_eq] at this
  exact this

/-- **`B_dR^+(𝓞_ℂ_p)` is a local ring.** -/
instance isLocalRing_BDeRhamPlus : IsLocalRing (BDeRhamPlus O p) :=
  isLocalRing_of_isAdicComplete_maximal (span {ofPlus O p (xi' p)})

/-- Its maximal ideal is `(ξ)`. -/
theorem maximalIdeal_BDeRhamPlus :
    IsLocalRing.maximalIdeal (BDeRhamPlus O p) = span {ofPlus O p (xi' p)} :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_span_xi p)).symm

/-- Every non-zero element of `B_dR^+` is `ξⁿ · unit`. -/
theorem eq_xi_pow_mul_unit (x : BDeRhamPlus O p) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : BDeRhamPlus O p, IsUnit u ∧ x = ofPlus O p (xi' p) ^ n * u := by
  set ϖ := ofPlus O p (xi' p)
  have hex : ∃ n, x ∉ (span {ϖ ^ n} : Ideal (BDeRhamPlus O p)) := by
    by_contra hcon
    push Not at hcon
    apply hx
    apply IsHausdorff.haus' (I := (span {ϖ} : Ideal (BDeRhamPlus O p))) x
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hcon n
  classical
  let N := Nat.find hex
  have hN : x ∉ (span {ϖ ^ N} : Ideal (BDeRhamPlus O p)) := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    rw [h0, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxM : x ∈ (span {ϖ ^ M} : Ideal (BDeRhamPlus O p)) := by
    have := Nat.find_min hex (show M < N by omega)
    push Not at this
    exact this
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, u, ?_, by rw [← hu, mul_comm]⟩
  by_contra hnu
  have : u ∈ IsLocalRing.maximalIdeal (BDeRhamPlus O p) := hnu
  rw [maximalIdeal_BDeRhamPlus] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
  apply hN
  rw [hM, Ideal.mem_span_singleton']
  exact ⟨c, by rw [← hu, ← hc, Nat.succ_eq_add_one, pow_succ']; simp only [ϖ, mul_assoc]⟩

instance isDomain_BDeRhamPlus : IsDomain (BDeRhamPlus O p) := by
  have : NoZeroDivisors (BDeRhamPlus O p) := ⟨fun {x y} hxy => by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, u, hu, rfl⟩ := eq_xi_pow_mul_unit p x hcon.1
    obtain ⟨b, v, hv, rfl⟩ := eq_xi_pow_mul_unit p y hcon.2
    have : ofPlus O p (xi' p) ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ofPlus_xi'_pow_ne_zero p (a + b) ((hu.mul hv).mul_left_eq_zero.mp this)⟩
  exact NoZeroDivisors.to_isDomain _

/-- **`B_dR^+(𝓞_ℂ_p)` (Mathlib's `BDeRhamPlus`) is a discrete valuation ring.** -/
theorem isDiscreteValuationRing_BDeRhamPlus : IsDiscreteValuationRing (BDeRhamPlus O p) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ofPlus O p (xi' p), ?_, ?_⟩
  · exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (by simpa using ofPlus_xi'_pow_ne_zero p 1) (maximalIdeal_BDeRhamPlus p)
  · intro x hx
    obtain ⟨n, u, hu, rfl⟩ := eq_xi_pow_mul_unit p x hx
    exact ⟨n, ⟨hu.unit, rfl⟩⟩

/-! ### `B_dR(𝓞_ℂ_p)` is the fraction field of the DVR `B_dR^+`, hence a field. -/

/-- `B_dR^+[1/ξ]` is the fraction field of `B_dR^+`. -/
instance isFractionRing_away_xi :
    IsFractionRing (BDeRhamPlus O p) (Localization.Away (ofPlus O p (xi' p))) := by
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (ofPlus O p (xi' p)))
    (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by simpa using ofPlus_xi'_pow_ne_zero p 1)) ?_
  intro n hn
  obtain ⟨k, u, hu, rfl⟩ := eq_xi_pow_mul_unit p n (nonZeroDivisors.ne_zero hn)
  exact ⟨_, ⟨k, rfl⟩, hu.mul_right_dvd.mpr (dvd_refl _)⟩

/-- **`BDeRham 𝓞_ℂ_[p] p` is a field**: it is isomorphic to the fraction field `B_dR^+[1/ξ]` of the
discrete valuation ring `BDeRhamPlus 𝓞_ℂ_[p] p`. -/
theorem isField_BDeRham : IsField (BdR O p) := by
  have hF : IsField (Localization.Away (ofPlus O p (xi' p))) :=
    (IsFractionRing.toField (BDeRhamPlus O p)).toIsField
  exact MulEquiv.isField hF (bdREquivAway p).toMulEquiv

/-- `BDeRham 𝓞_ℂ_[p] p` is a fraction field of `BDeRhamPlus 𝓞_ℂ_[p] p` (Mathlib's own structure map). -/
theorem isFractionRing_BDeRham : IsFractionRing (BDeRhamPlus O p) (BdR O p) := by
  have : IsLocalization (genMonoid O p) (Localization.Away (ofPlus O p (xi' p))) :=
    isLocalization_away_xi (p_regular p) (xi p) (ker_fontaineTheta_Cp p)
  exact (IsLocalization.isLocalization_iff_of_algEquiv (nonZeroDivisors _)
    (bdREquivAway p)).mpr inferInstance

/-! ### The residue map `θ⁺ : B_dR^+ → 𝓞_ℂ_p[1/p] ≅ ℂ_p` (Mathlib's TODO 1), with kernel `(ξ)`. -/

/-- `θ⁺ : B_dR^+ → 𝓞_ℂ_p[1/p]`: reduction modulo `ker θ[1/p]` followed by `θ[1/p]`. -/
noncomputable def thetaPlus : BDeRhamPlus O p →+* Localization.Away (p : O) :=
  (RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p)).toRingHom.comp
    (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP O p))).toRingHom

theorem thetaPlus_ofPlus (x : Localization.Away (p : WittVector p (PreTilt O p))) :
    thetaPlus p (ofPlus O p x) = fontaineThetaInvertP O p x := rfl

theorem thetaPlus_surjective : Function.Surjective (thetaPlus p) := fun y => by
  obtain ⟨x, rfl⟩ := fontaineThetaInvertP_surjective p y
  exact ⟨ofPlus O p x, rfl⟩

/-- **`ker θ⁺ = (ξ)`**, the maximal ideal of the DVR `B_dR^+`. -/
theorem ker_thetaPlus : RingHom.ker (thetaPlus p) = span {ofPlus O p (xi' p)} := by
  have h1 : RingHom.ker (thetaPlus p) =
      RingHom.ker (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP O p))).toRingHom := by
    ext x
    exact map_eq_zero_iff (RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p))
      (RingEquiv.injective _)
  rw [h1, AdicCompletion.ker_evalOneₐ_eq_map _ (ker_fg p)]
  exact map_ker_eq p

/-- `𝓞_ℂ_p[1/p]` is the fraction field of `𝓞_ℂ_p`. -/
instance isFractionRing_away_p : IsFractionRing O (Localization.Away (p : O)) := by
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (p : O)) (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (p_ne_zero p)) ?_
  intro x hx
  have hx0 : (x : ℂ_[p]) ≠ 0 := fun h0 => nonZeroDivisors.ne_zero hx (Subtype.ext h0)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hx0) (norm_p_lt_one p)
  have hc : ‖(p : ℂ_[p]) ^ m / (x : ℂ_[p])‖ ≤ 1 := by
    rw [norm_div, norm_pow]; exact div_le_one_of_le₀ hm.le (norm_nonneg _)
  refine ⟨(p : O) ^ m, ⟨m, rfl⟩, ⟨⟨(p : ℂ_[p]) ^ m / (x : ℂ_[p]), (mem_O_iff p _).mpr hc⟩, ?_⟩⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  field_simp
  rfl

/-- **`𝓞_ℂ_p[1/p] ≅ ℂ_p`**, so `θ⁺` takes values in `ℂ_p`. -/
noncomputable def awayEquivCp : Localization.Away (p : O) ≃ₐ[O] ℂ_[p] :=
  IsLocalization.algEquiv (nonZeroDivisors O) _ _

/-- The residue map `B_dR^+ → ℂ_p`, surjective with kernel `(ξ)`. -/
noncomputable def thetaPlusCp : BDeRhamPlus O p →+* ℂ_[p] :=
  (awayEquivCp p).toRingEquiv.toRingHom.comp (thetaPlus p)

theorem thetaPlusCp_surjective : Function.Surjective (thetaPlusCp p) :=
  (awayEquivCp p).surjective.comp (thetaPlus_surjective p)

theorem ker_thetaPlusCp : RingHom.ker (thetaPlusCp p) = span {ofPlus O p (xi' p)} := by
  rw [← ker_thetaPlus p]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  exact map_eq_zero_iff (awayEquivCp p) (AlgEquiv.injective _)

end BdrKer.Cp

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/LocalCore.lean

/-!
# G9, the local core: descent of de Rham and Hodge–Tate data from `F` to `ℚ_p`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Setting of N5's Lemma `lem:de-rham-descent` after the choice of the local field (h-trust C3,
Galois choice): `F/ℚ_p` finite Galois, `V` a `ℚ_p`-linear representation of `G_F`,
`E ⊆ ℚ̄_p` a finite coefficient field, `ρE : G_{ℚ_p} → GL₂(E)`, and an `E`-linear
`E ⊗_{ℚ_p} V ≅ E² × E²` intertwining `V|G_F` with `ρE|G_F ⊕ ρE|G_F`.

* `core_ht`: if `V` has Hodge–Tate multiplicities (over `F`, pkg-I4's `htMultOver`) `2` at `0`,
  `2` at `−1` and `0` elsewhere, then `ρE` has Hodge–Tate weights `{0, −1}` (pkg-I4's
  `HasHTWeights`).
* `core_dR`: if `V` is de Rham over `F` (pkg-I4's `IsDeRhamOver`) and `ℚ̄_p` embeds
  `G_{ℚ_p}`-equivariantly into `B_dR` (Fontaine; here a hypothesis), then `ρE` is de Rham
  (pkg-I4's `IsDeRham`).

Proof: count dimensions of spaces of equivariant maps through `E ⊗ V ≅ U ⊕ U`
(`overF_count_gen`), then descend from `G_F` to `G_{ℚ_p}` (`descent_finrank`, Speiser's lemma),
using `F' ⊆ ℚ̄_p ⊆ ℂ_p` (resp. `⊆ B_dR`); divisibility of `dim_{ℚ_p}` by `[F:ℚ_p]` comes from
the `F'`-structure. No closure property of de Rham representations (T23) is used.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! ### Counting through `C ⊗ V ≅ U × U`, without finiteness hypotheses -/

section Count

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  (act : G → B →ₗ[K] B)

theorem map_arrowCongr_Dsp {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (Dsp act ρ S).map ((LinearEquiv.arrowCongr e (LinearEquiv.refl K B) :
      (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B)) : (V →ₗ[K] B) →ₗ[K] (V' →ₗ[K] B)) = Dsp act ρ' S := by
  set L : (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B) := LinearEquiv.arrowCongr e (LinearEquiv.refl K B)
  have hL : ∀ φ v', L φ v' = φ (e.symm v') := fun _ _ => rfl
  have hL' : ∀ φ' v, L.symm φ' v = φ' (e v) := fun _ _ => rfl
  ext φ'
  constructor
  · rintro ⟨φ, hφ, rfl⟩ g hg v'
    have h1 : e.symm (ρ' g v') = ρ g (e.symm v') := by
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change L φ (ρ' g v') = act g (L φ v')
    rw [hL, hL, h1, hφ g hg]
  · intro hφ'
    refine ⟨L.symm φ', ?_, by simp⟩
    intro g hg v
    rw [hL', hL', he, hφ' g hg]

/-- An equivariant isomorphism `V ≅ V'` gives `Dsp(V) ≅ Dsp(V')`. -/
def dspCongr {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) : Dsp act ρ S ≃ₗ[K] Dsp act ρ' S :=
  ((LinearEquiv.arrowCongr e (LinearEquiv.refl K B)).submoduleMap (Dsp act ρ S)).trans
    (LinearEquiv.ofEq _ _ (map_arrowCongr_Dsp act ρ ρ' S e he))

/-- `Dsp(V^ι) ≅ Dsp(V)^ι`. -/
def dspPi {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Dsp act (piRep ρ ι) S ≃ₗ[K] (ι → Dsp act ρ S) :=
  have hsingle : ∀ g i (v : V), piRep ρ ι g (Pi.single i v) = Pi.single i (ρ g v) := by
    intro g i v
    funext j
    rw [piRep_apply]
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  { toFun := fun φ i => ⟨(φ : (ι → V) →ₗ[K] B) ∘ₗ LinearMap.single K (fun _ => V) i, by
        intro g hg v
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
        rw [← hsingle, φ.2 g hg]⟩
    map_add' := fun φ ψ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    map_smul' := fun c φ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    invFun := fun ψ => ⟨∑ i, ((ψ i : Dsp act ρ S) : V →ₗ[K] B) ∘ₗ LinearMap.proj i, by
        intro g hg v
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [piRep_apply, (ψ i).2 g hg]⟩
    left_inv := fun φ => by
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          LinearMap.single_apply]
        rw [← map_sum, Finset.univ_sum_single v]
    right_inv := fun ψ => by
        funext i
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
          LinearMap.single_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji, map_zero]
        · intro h; exact absurd (Finset.mem_univ i) h }

/-- `Dsp(U × U) ≅ Dsp(U) × Dsp(U)`. -/
def dspProd {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G) :
    Dsp act (fun g => (ρ g).prodMap (ρ g)) S ≃ₗ[K] (Dsp act ρ S × Dsp act ρ S) :=
  { toFun := fun φ => (⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inl K V V, by
        intro g hg v
        have := φ.2 g hg (v, 0)
        simpa using this⟩,
      ⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inr K V V, by
        intro g hg v
        have := φ.2 g hg (0, v)
        simpa using this⟩)
    map_add' := fun φ ψ => by ext <;> simp
    map_smul' := fun c φ => by ext <;> simp
    invFun := fun ψ => ⟨(ψ.1 : V →ₗ[K] B).coprod (ψ.2 : V →ₗ[K] B), by
      intro g hg v
      simp only [LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
      rw [ψ.1.2 g hg, ψ.2.2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      ext v <;> simp
    right_inv := fun ψ => by
      ext v <;> simp }

/-- `d · dim X = 2 · dim Y` from `X^d ≅ Y × Y` (`d > 0`), finite-dimensional or not. -/
theorem finrank_of_pi_equiv_prod {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y]
    [Module K Y] (d : ℕ) (hd : 0 < d) (Φ : (Fin d → X) ≃ₗ[K] Y × Y) :
    d * finrank K X = 2 * finrank K Y := by
  by_cases hX : FiniteDimensional K X
  · have h1 : FiniteDimensional K (Y × Y) := LinearEquiv.finiteDimensional Φ
    have h2 : FiniteDimensional K Y :=
      Module.Finite.of_surjective (LinearMap.fst K Y Y) LinearMap.fst_surjective
    have := Φ.finrank_eq
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Module.finrank_prod] at this
    omega
  · have hY : ¬ FiniteDimensional K Y := by
      intro hY
      have h1 : FiniteDimensional K (Y × Y) := inferInstance
      have h2 : FiniteDimensional K (Fin d → X) := LinearEquiv.finiteDimensional Φ.symm
      exact hX (Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : Fin d => X)
        ⟨0, hd⟩) (fun x => ⟨fun _ => x, rfl⟩))
    rw [Module.finrank_of_not_finite hX, Module.finrank_of_not_finite hY]
    simp

/-- **Counting through `C ⊗_K V ≅ U × U`** (no finiteness hypothesis). -/
theorem overF_count_gen {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x)) :
    finrank K C * finrank K (Dsp act ρV S) = 2 * finrank K (Dsp act ρU S) := by
  classical
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  let Φ1 : Dsp act ρCV S ≃ₗ[K] Dsp act (piRep ρV (Fin (finrank K C))) S :=
    dspCongr act ρCV _ S (tensorPiEquiv bC) (fun g x => tensorPiEquiv_baseChange bC (ρV g) x)
  let Φ2 : Dsp act ρCV S ≃ₗ[K] Dsp act (fun g => (ρU g).prodMap (ρU g)) S :=
    dspCongr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  let Φ : (Fin (finrank K C) → Dsp act ρV S) ≃ₗ[K] Dsp act ρU S × Dsp act ρU S :=
    ((dspPi act ρV S (Fin (finrank K C))).symm.trans Φ1.symm).trans (Φ2.trans (dspProd act ρU S))
  exact finrank_of_pi_equiv_prod (finrank K C) Module.finrank_pos Φ

/-- If `L` acts on `B` through `ι`, commuting with `act g` for `g ∈ S`, then `[L:K]` divides
`dim_K Dsp(S)`. -/
theorem finrank_dvd_Dsp_core {B : Type*} [CommRing B] [Algebra K B] (act : G → B →ₗ[K] B)
    {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G)
    {L : Type*} [Field L] [Algebra K L] (ι : L →ₐ[K] B)
    (h : ∀ g ∈ S, ∀ x b, act g (ι x * b) = ι x * act g b) :
    finrank K L ∣ finrank K (Dsp act ρ S) := by
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ S}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ g hg v
        simp only [Set.mem_ofPred_eq] at hφ
        simp only [LinearMap.smul_apply, hLsmul, hφ g hg v, h g hg] }
  have e2 : finrank K DL = finrank K (Dsp act ρ S) := rfl
  haveI : Module.Free L DL := Module.Free.of_divisionRing L DL
  rw [← e2, ← Module.finrank_mul_finrank K L DL]
  exact Dvd.intro _ rfl

end Count

/-! ### The local setting -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ (v ↦ ρE(σ) v)` on `Eⁿ`, as `ℚ_p`-linear maps. -/
def matRep {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρE : GQp p →* GL (Fin n) E) :
    GQp p →* ((Fin n → E) →ₗ[ℚ_[p]] (Fin n → E)) where
  toFun σ := (Matrix.mulVecLin (ρE σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p]
  map_one' := LinearMap.ext fun v => by simp
  map_mul' σ τ := LinearMap.ext fun v => by simp [Matrix.mulVec_mulVec]

theorem matRep_apply {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρE : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    matRep p ρE σ v = Matrix.mulVec (ρE σ : Matrix (Fin n) (Fin n) E) v := rfl

variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E] {n : ℕ}

theorem ddrSpace_eq_DspMat (ρE : GQp p →* GL (Fin n) E) :
    ddrSpace p ρE = Dsp (drAct p) (matRep p ρE) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

theorem htSpace_eq_DspMat (ρE : GQp p →* GL (Fin n) E) (i : ℤ) :
    htSpace p ρE i = Dsp (htAct p i) (matRep p ρE) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

theorem ddrSpaceOver_eq_DspRep (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ddrSpaceOver p ρ = Dsp (fun σ => drAct p (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

theorem htSpaceOver_eq_DspRep (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    htSpaceOver p ρ i = Dsp (fun σ => htAct p i (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

variable [IsGalois ℚ_[p] F]

theorem gammaF_gfToGqp (σ : Field.absoluteGaloisGroup F) : gammaF p F (gfToGqp p F σ) = 1 := by
  have : gfToGqp p F σ ∈ (gammaF p F).ker := by
    rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
  exact this

theorem Dsp_gf_eq {B : Type*} [AddCommGroup B] [Module ℚ_[p] B]
    {U : Type*} [AddCommGroup U] [Module ℚ_[p] U]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ρU : GQp p →* (U →ₗ[ℚ_[p]] U)) :
    Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρU (gfToGqp p F σ)) Set.univ =
      Dsp act ρU ((gammaF p F).ker : Set (GQp p)) := by
  ext φ
  constructor
  · intro h τ hτ v
    rw [SetLike.mem_coe, ← range_gfToGqp] at hτ
    obtain ⟨σ, rfl⟩ := hτ
    exact h σ trivial v
  · intro h σ _ v
    exact h _ (by rw [SetLike.mem_coe, ← range_gfToGqp]; exact ⟨σ, rfl⟩) v

/-- **The count**, for an embedding of `F' ⊆ ℚ̄_p` into `B` semilinear for the action:
`[E:ℚ_p] · dim D_F(V) = 2 [F:ℚ_p] · dim D_{ℚ_p}(ρE)` and `[F:ℚ_p] ∣ dim D_F(V)`. -/
theorem core_count_F {B : Type*} [CommRing B] [Algebra ℚ_[p] B]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ι' : fieldF p F →ₐ[ℚ_[p]] B)
    (hsemi : ∀ g x b, act g (ι' x * b) = ι' (gammaF p F g x) * act g b)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x)) :
    finrank ℚ_[p] E * finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ)
      = 2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (matRep p ρE) Set.univ)) ∧
    finrank ℚ_[p] F ∣
      finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ) := by
  constructor
  · have h1 := overF_count_gen (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ)
      (fun σ => matRep p ρE (gfToGqp p F σ)) Set.univ eE he
    rw [h1, Dsp_gf_eq p F act (matRep p ρE),
      descent_finrank act (matRep p ρE) ι' (gammaF p F) (gammaF_surjective p F) hsemi,
      finrank_fieldF]
  · rw [← finrank_fieldF p F]
    refine finrank_dvd_Dsp_core _ _ _ ι' fun σ _ x b => ?_
    rw [hsemi, gammaF_gfToGqp]
    rfl

/-- **The count**, for an equivariant embedding of `ℚ̄_p` into `B`. -/
theorem core_count {B : Type*} [CommRing B] [Algebra ℚ_[p] B]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ι : PadicAlgCl p →ₐ[ℚ_[p]] B)
    (hι : ∀ σ x b, act σ (ι x * b) = ι (σ x) * act σ b)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x)) :
    finrank ℚ_[p] E * finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ)
      = 2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (matRep p ρE) Set.univ)) ∧
    finrank ℚ_[p] F ∣
      finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ) := by
  let ι' : fieldF p F →ₐ[ℚ_[p]] B := ι.comp (fieldF p F).val
  have hsemi : ∀ g x b, act g (ι' x * b) = ι' (gammaF p F g x) * act g b := by
    intro g x b
    simp only [ι', AlgHom.comp_apply, IntermediateField.coe_val, hι, gammaF_apply_coe]
  exact core_count_F p F act ι' hsemi ρ ρE eE he

/-- `ℚ̄_p → ℂ_p`. -/
def cpEmb : PadicAlgCl p →ₐ[ℚ_[p]] ℂ_[p] := IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]

theorem htAct_semi (i : ℤ) (σ : GQp p) (x : PadicAlgCl p) (b : ℂ_[p]) :
    htAct p i σ (cpEmb p x * b) = cpEmb p (σ x) * htAct p i σ b := by
  rw [htAct_apply, htAct_apply, map_mul, mul_smul_comm]
  congr 2
  change cpAct p σ ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p])
  exact cpAct_coe p σ x

theorem finrank_V_of_eE (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) :
    finrank ℚ_[p] V = 4 := by
  have := eE.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at this
  omega

theorem count_two_zero : Multiset.count (0 : ℤ) {0, -1} = 1 := by decide
theorem count_two_neg_one : Multiset.count (-1 : ℤ) {0, -1} = 1 := by decide
theorem count_two_other (w : ℤ) (h0 : w ≠ 0) (h1 : w ≠ -1) : Multiset.count w {0, -1} = 0 := by
  simp [h0, h1]

/-- **G9 local core, Hodge–Tate part.** -/
theorem core_ht (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (h0 : htMultOver p ρ 0 = 2) (h1 : htMultOver p ρ (-1) = 2)
    (hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p ρ w = 0) :
    HasHTWeights p ρE {0, -1} := by
  have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  -- the multiplicity at `w` is `M_w = dim H_{-w}(V) / [F:ℚ_p]`; then `htMult ρE w = M_w / 2`
  have key : ∀ w : ℤ, ∀ M : ℕ, htMultOver p ρ w = M →
      htMult p ρE w * 2 = M ∨ finrank ℚ_[p] E * M = 2 * finrank ℚ_[p] (htSpace p ρE (-w)) := by
    intro w M hM
    right
    obtain ⟨hc, hdvd⟩ := core_count p F (htAct p (-w)) (cpEmb p) (htAct_semi p (-w)) ρ ρE eE he
    rw [htMultOver, htSpaceOver_eq_DspRep] at hM
    rw [htSpace_eq_DspMat]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left _ hf] at hM
    subst hM
    rw [hk] at hc
    have : finrank ℚ_[p] F * (finrank ℚ_[p] E * k) =
        finrank ℚ_[p] F * (2 * finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ)) := by
      rw [← mul_assoc, mul_comm (finrank ℚ_[p] F), mul_assoc, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hf this
  intro w
  have hdiv : ∀ M : ℕ, finrank ℚ_[p] E * (2 * M) = 2 * finrank ℚ_[p] (htSpace p ρE (-w)) →
      htMult p ρE w = M := by
    intro M hM
    have : finrank ℚ_[p] (htSpace p ρE (-w)) = finrank ℚ_[p] E * M := by
      have := hM; rw [mul_left_comm] at this; omega
    rw [htMult, this, Nat.mul_div_cancel_left _ hd]
  by_cases hw0 : w = 0
  · subst hw0
    rw [count_two_zero]
    rcases key 0 2 h0 with h | h
    · omega
    · exact hdiv 1 (by simpa using h)
  by_cases hw1 : w = -1
  · subst hw1
    rw [count_two_neg_one]
    rcases key (-1) 2 h1 with h | h
    · omega
    · exact hdiv 1 (by simpa using h)
  rw [count_two_other w hw0 hw1]
  rcases key w 0 (hw w hw0 hw1) with h | h
  · omega
  · exact hdiv 0 (by simpa using h)

/-- **G9 local core, de Rham part**, given an embedding `F' → B_dR` with
`σ(ι x) = ι(σ|_{F'} x)` (task g9-derham's second run constructs one: `iotaDR`, `G9.lean`). -/
theorem core_dR_F (ι' : fieldF p F →ₐ[ℚ_[p]] BdR p)
    (hι' : ∀ (σ : GQp p) (x : fieldF p F), bdrAct p σ (ι' x) = ι' (gammaF p F σ x))
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (hdR : IsDeRhamOver p ρ) :
    IsDeRham p ρE := by
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hsemi : ∀ σ x b, drAct p σ (ι' x * b) = ι' (gammaF p F σ x) * drAct p σ b := by
    intro σ x b
    rw [drAct_apply, drAct_apply, map_mul, hι']
  obtain ⟨hc, -⟩ := core_count_F p F (drAct p) ι' hsemi ρ ρE eE he
  rw [IsDeRhamOver, ddrSpaceOver_eq_DspRep, finrank_V_of_eE p eE] at hdR
  rw [IsDeRham, ddrSpace_eq_DspMat]
  rw [hdR] at hc
  have : finrank ℚ_[p] F * (finrank ℚ_[p] (Dsp (drAct p) (matRep p ρE) Set.univ)) =
      finrank ℚ_[p] F * (2 * finrank ℚ_[p] E) := by
    have := hc; ring_nf at this ⊢; omega
  exact Nat.eq_of_mul_eq_mul_left hf this

/-- **G9 local core, de Rham part** (given an equivariant `ℚ̄_p → B_dR`). -/
theorem core_dR (ιB : PadicAlgCl p →ₐ[ℚ_[p]] BdR p)
    (hιB : ∀ (σ : GQp p) (x : PadicAlgCl p), bdrAct p σ (ιB x) = ιB (σ x))
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (hdR : IsDeRhamOver p ρ) :
    IsDeRham p ρE :=
  core_dR_F p F (ιB.comp (fieldF p F).val)
    (fun σ x => by
      simp only [AlgHom.comp_apply, IntermediateField.coe_val, hιB, gammaF_apply_coe])
    ρ ρE eE he hdR

end Local

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Local.lean

/-!
# G9: the local count (Hodge–Tate part, and the de Rham part modulo `ℚ̄_p ⊆ B_dR`)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

pkg-I4's spaces `htSpace`, `htSpaceOver`, `ddrSpace`, `ddrSpaceOver` are the spaces `Dsp` of
`Descent.lean` for the actions `σ ↦ χ(σ)^i · σ` on `ℂ_p` and `σ ↦ σ` on `B_dR`. From R10 over a
finite Galois `F/ℚ_p`, the decomposition `C ⊗ V_p(A) ≅ r|G_F ⊕ r|G_F` (G8's output), the count
`overF_count` and the descent `descent_finrank` give the conclusions of N5's Lemma
`lem:de-rham-descent` at `K = ℚ_p`.

Main results here:
* `htMult_eq_one_of_R10` (G9, Hodge–Tate part): `htMult p r 0 = 1` and `htMult p r (-1) = 1`.
* `isDeRham_of_R10_of_emb` (G9, de Rham part) under two hypotheses on `B_dR` that are proved in
  `BdREmb.lean`: `bdrAct` is multiplicative, and `F' ⊆ ℚ̄_p` embeds `G_{ℚ_p}`-equivariantly in
  `B_dR`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! `GlueI3.repBaseChange` (Leaves.lean, section `PkgI3Sec`) comes from `I3Layer.lean`, the
verbatim restatement of that section. -/

/-! ### A divisibility lemma -/

/-- If `ι : L → B` commutes with the action of `S`, then `Dsp act ρ S` is an `L`-space, so its
`K`-dimension is divisible by `[L:K]`. -/
theorem finrank_dvd_Dsp_of_emb {K G B V L : Type*} [Field K] [Group G] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] [Field L] [Algebra K L]
    (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) (ι : L →ₐ[K] B)
    (hlin : ∀ g ∈ S, ∀ x b, act g (ι x * b) = ι x * act g b) :
    finrank K L ∣ finrank K (Dsp act ρ S) := by
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ S}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ g hg v
        simp only [Set.mem_ofPred_eq] at hφ
        simp only [LinearMap.smul_apply, hLsmul, hφ g hg v, hlin g hg] }
  have hDL : DL.restrictScalars K = Dsp act ρ S := Submodule.ext fun _ => Iff.rfl
  have e2 : finrank K DL = finrank K (Dsp act ρ S) := by rw [← hDL]; rfl
  have : Module.Free L DL := Module.Free.of_divisionRing L DL
  rw [← e2, ← Module.finrank_mul_finrank K L DL]
  exact dvd_mul_right _ _

section Actions

variable (p : ℕ) [Fact p.Prime]

theorem cpAct_mul (σ τ : GQp p) (x : ℂ_[p]) : cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _)
      ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem cpAct_smul (σ : GQp p) (c : ℚ_[p]) (x : ℂ_[p]) : cpAct p σ (c • x) = c • cpAct p σ x := by
  rw [Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

theorem cyc_mul (σ τ : GQp p) : cyc p (σ * τ) = cyc p σ * cyc p τ := by
  simp only [cyc]
  rw [← map_mul]
  rfl

theorem cyc_one : cyc p 1 = 1 := by
  simp only [cyc]
  rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
  rfl

theorem cycPow_mul (σ τ : GQp p) (i : ℤ) :
    cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  simp only [cycPow, cyc_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one (i : ℤ) : cycPow p 1 i = 1 := by
  simp [cycPow, cyc_one]

/-- `x ↦ χ(σ)^i · σ(x)` on `ℂ_p`, `ℚ_p`-linear. -/
def cpActL (i : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := cycPow p σ i • cpAct p σ x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' c x := by
    rw [cpAct_smul, smul_comm]
    rfl

theorem cpActL_apply (i : ℤ) (σ : GQp p) (x : ℂ_[p]) :
    cpActL p i σ x = cycPow p σ i • cpAct p σ x := rfl

/-- The twisted action `σ ↦ χ(σ)^i · σ` as a representation on `ℂ_p`. -/
def cpActHom (i : ℤ) : GQp p →* (ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun := cpActL p i
  map_one' := by
    refine LinearMap.ext fun x => ?_
    rw [cpActL_apply, cpAct_one, cycPow_one, one_smul]
    rfl
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, cpActL_apply, cpActL_apply, cpActL_apply, cpAct_mul, cpAct_smul,
      cycPow_mul, mul_smul]

variable {C : Type*} [Field C] [Algebra ℚ_[p] C] {n : ℕ}

/-- `r : G_{ℚ_p} → GL_n(C)` as a `ℚ_p`-linear representation on `Cⁿ`. -/
def rRep (r : GQp p →* GL (Fin n) C) : Representation ℚ_[p] (GQp p) (Fin n → C) where
  toFun σ := (Matrix.mulVecLin (r σ : Matrix (Fin n) (Fin n) C)).restrictScalars ℚ_[p]
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_mulVec]

theorem rRep_apply (r : GQp p →* GL (Fin n) C) (σ : GQp p) (v : Fin n → C) :
    rRep p r σ v = Matrix.mulVec (r σ : Matrix (Fin n) (Fin n) C) v := rfl

variable [FiniteDimensional ℚ_[p] C]

theorem htSpace_eq_DspAct (r : GQp p →* GL (Fin n) C) (i : ℤ) :
    htSpace p r i = Dsp (cpActHom p i) (rRep p r) Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

theorem htSpaceOver_eq_DspAct (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    htSpaceOver p ρ i = Dsp ((cpActHom p i).comp (gfToGqp p F)) ρ Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

/-- `Dsp` over the kernel of `G_{ℚ_p} → Gal(F'/ℚ_p)` is `Dsp` over `G_F`. -/
theorem Dsp_ker_gammaF (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] {B W : Type*} [AddCommGroup B] [Module ℚ_[p] B] [AddCommGroup W]
    [Module ℚ_[p] W] (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ρ : Representation ℚ_[p] (GQp p) W) :
    Dsp act ρ ((gammaF p F).ker : Set (GQp p)) =
      Dsp (act.comp (gfToGqp p F)) (ρ.comp (gfToGqp p F)) Set.univ := by
  ext φ
  rw [← range_gfToGqp]
  constructor
  · intro h σ _ v
    exact h _ ⟨σ, rfl⟩ v
  · rintro h _ ⟨σ, rfl⟩ v
    exact h σ trivial v

/-- `F' → ℂ_p`. -/
def iotaCp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] :
    fieldF p F →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (fieldF p F).val

theorem cpAct_iotaCp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] (σ : GQp p) (x : fieldF p F) :
    cpAct p σ (iotaCp p F x) = iotaCp p F (gammaF p F σ x) := by
  simp only [iotaCp, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq, ← PadicComplex.coe_eq, cpAct_coe]
  congr 1
  exact (gammaF_apply_coe p F σ x).symm

theorem cpActHom_semi (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] (i : ℤ) (σ : GQp p) (x : fieldF p F) (b : ℂ_[p]) :
    cpActHom p i σ (iotaCp p F x * b) = iotaCp p F (gammaF p F σ x) * cpActHom p i σ b := by
  change cpActL p i σ _ = _ * cpActL p i σ b
  rw [cpActL_apply, cpActL_apply, map_mul, cpAct_iotaCp, mul_smul_comm]

end Actions

/-! ### G9, Hodge–Tate part -/

section HT

variable (p : ℕ) [Fact p.Prime]

/-- From the counts: if `dim Dsp_{G_F}(V) = 2[F:ℚ_p]·m`-type data hold, conclude. The core
arithmetic of both parts: `c · d_V = 2 · d_U`, `d_U = [F:ℚ_p] · d_G` give `d_G`. -/
theorem descended_finrank (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρV : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] V ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C ρV σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2))
    {B : Type*} [CommRing B] [Algebra ℚ_[p] B] (act : GQp p →* (B →ₗ[ℚ_[p]] B))
    (ι : fieldF p F →ₐ[ℚ_[p]] B)
    (hsemi : ∀ σ x b, act σ (ι x * b) = ι (gammaF p F σ x) * act σ b)
    (hpos : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) ρV Set.univ)) :
    finrank ℚ_[p] C * finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) ρV Set.univ) =
      2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ)) := by
  have hcount := overF_count (act.comp (gfToGqp p F)) (C := C) (fun σ => ρV σ)
    (fun σ => rRep p r (gfToGqp p F σ)) Set.univ e (fun σ x => he σ x) hpos
  have hdes := descent_finrank act (rRep p r) ι (gammaF p F) (gammaF_surjective p F) hsemi
  rw [Dsp_ker_gammaF, finrank_fieldF] at hdes
  rw [hcount, ← hdes]
  rfl

/-- **G9, Hodge–Tate part.** Hypotheses: R10 (`PkgI4.DeRhamComparison`) and G8's output localized
at `p`: a finite Galois `F/ℚ_p`, an abelian surface `A/F`, a finite `C/ℚ_p`,
`r : G_{ℚ_p} → GL₂(C)` and a `C`-linear `G_F`-equivariant `C ⊗ V_p(A) ≅ r|G_F ⊕ r|G_F`.
Conclusion: `r` has Hodge–Tate multiplicity `1` at the weights `0` and `−1`. -/
theorem htMult_eq_one_of_R10 (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    htMult p r 0 = 1 ∧ htMult p r (-1) = 1 := by
  obtain ⟨-, h0, h1⟩ := hR10 p F A 2 hA
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hC : 0 < finrank ℚ_[p] C := Module.finrank_pos
  -- the common computation, for `i = -w`
  have key : ∀ w : ℤ, htMultOver p (A.galRep p) w = 2 → htMult p r w = 1 := by
    intro w hw
    set i := -w
    set act := cpActHom p i
    set nV := finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ)
    have hnV : finrank ℚ_[p] (htSpaceOver p (A.galRep p) i) = nV := by
      rw [htSpaceOver_eq_DspAct]
    have hdvd : finrank ℚ_[p] F ∣ nV := by
      have := finrank_dvd_Dsp_of_emb (act.comp (gfToGqp p F)) (fun σ => A.galRep p σ) Set.univ
        (iotaCp p F) (fun σ _ x b => by
          have hk : gfToGqp p F σ ∈ (gammaF p F).ker := by
            rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
          rw [MonoidHom.mem_ker] at hk
          change act (gfToGqp p F σ) _ = _
          rw [cpActHom_semi, hk]
          rfl)
      rwa [finrank_fieldF] at this
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k = 2 := by
      have : htMultOver p (A.galRep p) w = k := by
        rw [htMultOver, hnV, hk, Nat.mul_div_cancel_left _ hF]
      rw [← this, hw]
    have hpos : 0 < nV := by rw [hk, hk2]; positivity
    have hd : finrank ℚ_[p] C * nV =
        2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ)) :=
      descended_finrank p F (A.galRep p) C r e he act (iotaCp p F) (cpActHom_semi p F i) hpos
    rw [hk, hk2] at hd
    have hG : finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) = finrank ℚ_[p] C := by
      have : finrank ℚ_[p] F * 2 * finrank ℚ_[p] C =
          finrank ℚ_[p] F * 2 * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
        linarith [hd]
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
    rw [htMult, htSpace_eq_DspAct, hG, Nat.div_self hC]
  exact ⟨key 0 h0, key (-1) h1⟩

end HT

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/CoefDescent.lean

/-!
# G9: from `ℚ̄_p`-coefficients to a finite coefficient field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`coef_descent`: let `F/ℚ_p` be finite Galois, `V` a `ℚ_p`-linear representation of `G_F`,
`R : G_{ℚ_p} → GL₂(ℚ̄_p)` a homomorphism, and `e' : ℚ̄_p ⊗ V ≅ ℚ̄_p² × ℚ̄_p²` (`ℚ̄_p`-linear)
intertwining `V|G_F` with `R|G_F ⊕ R|G_F`. Then there is a finite extension `E ⊆ ℚ̄_p` of `ℚ_p`
such that `R` takes values in `GL₂(E)` (`ρE`), and an `E`-linear `E ⊗ V ≅ E² × E²` intertwining
`V|G_F` with `ρE|G_F ⊕ ρE|G_F`. `E` is generated by the coordinates of `e'(1 ⊗ bₖ)` and of
`e'⁻¹` of the standard basis (`bₖ` a basis of `V`), and the entries of `R` at coset
representatives of `G_{ℚ_p}/G_F` (finite: `Gal(F'/ℚ_p)`). No topology is used (this replaces
the Baire argument of g0-mod-galois's docstring).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

section Lift

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {G : Type*} [Group G] {n : ℕ}

/-- A homomorphism to `GL_n(Ω)` with entries in an intermediate field `E` lifts to `GL_n(E)`. -/
def liftGL (E : IntermediateField K Ω) (f : G →* GL (Fin n) Ω)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) Ω) i j ∈ E) : G →* GL (Fin n) E :=
  let M : G → Matrix (Fin n) (Fin n) E := fun g i j => ⟨(f g : Matrix (Fin n) (Fin n) Ω) i j, h g i j⟩
  have hM : ∀ g, (M g).map (algebraMap E Ω) = (f g : Matrix (Fin n) (Fin n) Ω) := fun g => by
    ext i j; rfl
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) E => A.map (algebraMap E Ω)) :=
    Matrix.map_injective (algebraMap E Ω).injective
  have hmul : ∀ g g', M (g * g') = M g * M g' := fun g g' => hinj (by
    simp only [Matrix.map_mul, hM, map_mul, Units.val_mul])
  have hone : M 1 = 1 := hinj (by simp only [hM, map_one, Units.val_one, Matrix.map_one,
    map_zero, map_one])
  { toFun := fun g => ⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩
    map_one' := Units.ext hone
    map_mul' := fun g g' => Units.ext (hmul g g') }

theorem liftGL_map (E : IntermediateField K Ω) (f : G →* GL (Fin n) Ω)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) Ω) i j ∈ E) (g : G) :
    Matrix.GeneralLinearGroup.map (algebraMap E Ω) (liftGL E f h g) = f g := by
  ext i j; rfl

theorem liftGL_coe (E : IntermediateField K Ω) (f : G →* GL (Fin n) Ω)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) Ω) i j ∈ E) (g : G) (i j : Fin n) :
    ((liftGL E f h g : Matrix (Fin n) (Fin n) E) i j : Ω) = (f g : Matrix (Fin n) (Fin n) Ω) i j :=
  rfl

end Lift

section Pairs

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (E : IntermediateField K Ω)

/-- Pairs of vectors with coordinates in `E`, as a `K`-subspace of `Ω² × Ω²`. -/
def pairsIn : Submodule K ((Fin 2 → Ω) × (Fin 2 → Ω)) where
  carrier := {w | ∀ i, w.1 i ∈ E ∧ w.2 i ∈ E}
  zero_mem' := fun i => ⟨E.zero_mem, E.zero_mem⟩
  add_mem' := fun ha hb i => ⟨E.add_mem (ha i).1 (hb i).1, E.add_mem (ha i).2 (hb i).2⟩
  smul_mem' := fun c w hw i => ⟨by simpa using E.smul_mem (hw i).1 (x := c),
    by simpa using E.smul_mem (hw i).2 (x := c)⟩

theorem smul_mem_pairsIn {a : Ω} (ha : a ∈ E) {w : (Fin 2 → Ω) × (Fin 2 → Ω)}
    (hw : w ∈ pairsIn E) : a • w ∈ pairsIn E := fun i =>
  ⟨by simpa using E.mul_mem ha (hw i).1, by simpa using E.mul_mem ha (hw i).2⟩

/-- `E² × E² → Ω² × Ω²`. -/
def inclPair : (Fin 2 → E) × (Fin 2 → E) →ₗ[E] (Fin 2 → Ω) × (Fin 2 → Ω) :=
  ((Algebra.linearMap E Ω).compLeft (Fin 2)).prodMap ((Algebra.linearMap E Ω).compLeft (Fin 2))

theorem inclPair_apply (w : (Fin 2 → E) × (Fin 2 → E)) :
    inclPair E w = (fun i => (w.1 i : Ω), fun i => (w.2 i : Ω)) := rfl

theorem inclPair_injective : Function.Injective (inclPair E) := by
  intro w w' h
  rw [inclPair_apply, inclPair_apply, Prod.mk.injEq] at h
  ext i
  · exact congrFun h.1 i
  · exact congrFun h.2 i

end Pairs

section Coef

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local notation "Ω" => PadicAlgCl p

theorem matMap_mulVec {E : IntermediateField ℚ_[p] Ω} (A : Matrix (Fin 2) (Fin 2) E)
    (v : Fin 2 → E) (i : Fin 2) :
    ((A.mulVec v) i : Ω) = ((A.map (algebraMap E Ω)).mulVec (fun k => (v k : Ω))) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- **Finite coefficient field.** -/
theorem coef_descent (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (R : GQp p →* GL (Fin 2) Ω)
    (e' : Ω ⊗[ℚ_[p]] V ≃ₗ[Ω] (Fin 2 → Ω) × (Fin 2 → Ω))
    (he' : ∀ σ x, e' ((ρ σ).baseChange Ω x) =
      ((R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec (e' x).1,
        (R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec (e' x).2)) :
    ∃ (E : IntermediateField ℚ_[p] Ω) (_ : FiniteDimensional ℚ_[p] E)
      (ρE : GQp p →* GL (Fin 2) E) (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)),
      (∀ τ, Matrix.GeneralLinearGroup.map (algebraMap E Ω) (ρE τ) = R τ) ∧
      ∀ σ x, eE ((ρ σ).baseChange E x) =
        ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x) := by
  classical
  -- `dim V = 4`
  have hV4 : finrank ℚ_[p] V = 4 := by
    have := e'.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at this
    omega
  have : FiniteDimensional ℚ_[p] V := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasis ℚ_[p] V
  let bΩ := Algebra.TensorProduct.basis Ω b
  have hbΩ : ∀ k, bΩ k = (1 : Ω) ⊗ₜ b k := fun k => Algebra.TensorProduct.basis_apply b k
  -- `φ v = e'(1 ⊗ v)`
  let φ : V →ₗ[ℚ_[p]] (Fin 2 → Ω) × (Fin 2 → Ω) :=
    (e'.toLinearMap.restrictScalars ℚ_[p]).comp (TensorProduct.mk ℚ_[p] Ω V 1)
  have hφ : ∀ v, φ v = e' ((1 : Ω) ⊗ₜ v) := fun _ => rfl
  let y : Fin 2 → Ω ⊗[ℚ_[p]] V := fun j => e'.symm (Pi.single j 1, 0)
  let a : Fin 2 → Fin (finrank ℚ_[p] V) → Ω := fun j k => bΩ.repr (y j) k
  -- coset representatives of `G_{ℚ_p} / G_F`
  let s : (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) → GQp p := Function.surjInv (gammaF_surjective p F)
  have hs : ∀ γ, gammaF p F (s γ) = γ := Function.surjInv_eq (gammaF_surjective p F)
  -- the generating set
  let S1 : Set Ω := Set.range (fun ki : Fin (finrank ℚ_[p] V) × Fin 2 => (φ (b ki.1)).1 ki.2)
  let S2 : Set Ω := Set.range (fun ki : Fin (finrank ℚ_[p] V) × Fin 2 => (φ (b ki.1)).2 ki.2)
  let S3 : Set Ω := Set.range (fun jk : Fin 2 × Fin (finrank ℚ_[p] V) => a jk.1 jk.2)
  let S4 : Set Ω := Set.range (fun x : (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) × Fin 2 × Fin 2 =>
    (R (s x.1) : Matrix (Fin 2) (Fin 2) Ω) x.2.1 x.2.2)
  let S : Set Ω := S1 ∪ S2 ∪ S3 ∪ S4
  have hSfin : S.Finite :=
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)
  have : Finite S := hSfin.to_subtype
  let E : IntermediateField ℚ_[p] Ω := IntermediateField.adjoin ℚ_[p] S
  have hEfin : FiniteDimensional ℚ_[p] E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hSE : ∀ x ∈ S, x ∈ E := fun x hx => IntermediateField.subset_adjoin ℚ_[p] S hx
  -- C1: `φ(V) ⊆ E² × E²`
  have hC1 : ∀ v, φ v ∈ pairsIn E := by
    intro v
    have hspan : Submodule.span ℚ_[p] (Set.range b) ≤ (pairsIn E).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩ i
      exact ⟨hSE _ (Or.inl (Or.inl (Or.inl ⟨(k, i), rfl⟩))),
        hSE _ (Or.inl (Or.inl (Or.inr ⟨(k, i), rfl⟩)))⟩
    rw [b.span_eq] at hspan
    exact hspan Submodule.mem_top
  have ha : ∀ j k, a j k ∈ E := fun j k => hSE _ (Or.inl (Or.inr ⟨(j, k), rfl⟩))
  -- C2: entries of `R` on `G_F` lie in `E`
  have hC2 : ∀ σ i j, (R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω) i j ∈ E := by
    intro σ i j
    have hy : y j = ∑ k, a j k • bΩ k := (bΩ.sum_repr (y j)).symm
    have h1 : e' ((ρ σ).baseChange Ω (y j)) =
        ((R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec (Pi.single j 1),
          (R (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) Ω).mulVec 0) := by
      rw [he']
      simp only [y, LinearEquiv.apply_symm_apply]
    have h2 : e' ((ρ σ).baseChange Ω (y j)) = ∑ k, a j k • φ (ρ σ (b k)) := by
      rw [hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, map_smul, hbΩ, LinearMap.baseChange_tmul, hφ]
    have h3 : ∑ k, a j k • φ (ρ σ (b k)) ∈ pairsIn E :=
      Submodule.sum_mem _ fun k _ => smul_mem_pairsIn E (ha j k) (hC1 _)
    rw [← h2, h1] at h3
    have := (h3 i).1
    simpa [Matrix.mulVec_single_one] using this
  -- C3: entries of `R` everywhere lie in `E`
  have hC3 : ∀ τ i j, (R τ : Matrix (Fin 2) (Fin 2) Ω) i j ∈ E := by
    intro τ i j
    have hk : (s (gammaF p F τ))⁻¹ * τ ∈ (gfToGqp p F).range := by
      rw [range_gfToGqp, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    obtain ⟨σ, hσ⟩ := hk
    have hτ : τ = s (gammaF p F τ) * gfToGqp p F σ := by rw [hσ]; group
    rw [hτ, map_mul, Units.val_mul, Matrix.mul_apply]
    refine IntermediateField.sum_mem _ fun l _ => IntermediateField.mul_mem _ ?_ (hC2 σ l j)
    exact hSE _ (Or.inr ⟨(gammaF p F τ, i, l), rfl⟩)
  -- the lift `ρE`
  let ρE : GQp p →* GL (Fin 2) E := liftGL E R hC3
  -- `φE : V → E² × E²`
  let φE : V →ₗ[ℚ_[p]] (Fin 2 → E) × (Fin 2 → E) :=
    { toFun := fun v => (fun i => ⟨(φ v).1 i, (hC1 v i).1⟩, fun i => ⟨(φ v).2 i, (hC1 v i).2⟩)
      map_add' := fun v w => by ext i <;> simp
      map_smul' := fun c v => by ext i <;> simp [Algebra.smul_def] }
  have hφE : ∀ v, inclPair E (φE v) = φ v := fun v => rfl
  let eE0 : E ⊗[ℚ_[p]] V →ₗ[E] (Fin 2 → E) × (Fin 2 → E) := φE.liftBaseChange E
  -- `E ⊗ V → Ω ⊗ V`
  let ιbc : E ⊗[ℚ_[p]] V →ₗ[ℚ_[p]] Ω ⊗[ℚ_[p]] V :=
    LinearMap.rTensor V ((Algebra.ofId E Ω).toLinearMap.restrictScalars ℚ_[p])
  have hιbc_inj : Function.Injective ιbc :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap E Ω).injective
  have hcompat : ∀ x, inclPair E (eE0 x) = e' (ιbc x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      simp only [eE0, LinearMap.liftBaseChange_tmul, map_smul, hφE, ιbc, LinearMap.rTensor_tmul]
      rw [show ((Algebra.ofId E Ω).toLinearMap.restrictScalars ℚ_[p]) c ⊗ₜ[ℚ_[p]] v =
          (c : Ω) • ((1 : Ω) ⊗ₜ[ℚ_[p]] v) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl]
      rw [map_smul, ← hφ]
      rfl
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have heE0_inj : Function.Injective eE0 := by
    intro x x' h
    apply hιbc_inj
    apply e'.injective
    rw [← hcompat, ← hcompat, h]
  have hdim : finrank E (E ⊗[ℚ_[p]] V) = finrank E ((Fin 2 → E) × (Fin 2 → E)) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun, hV4]
  have : FiniteDimensional E (E ⊗[ℚ_[p]] V) := Module.finite_of_finrank_pos (by
    rw [Module.finrank_baseChange, hV4]; omega)
  have heE0_surj : Function.Surjective eE0 :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp heE0_inj
  let eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E) :=
    LinearEquiv.ofBijective eE0 ⟨heE0_inj, heE0_surj⟩
  refine ⟨E, hEfin, ρE, eE, fun τ => liftGL_map E R hC3 τ, fun σ x => ?_⟩
  apply inclPair_injective E
  change inclPair E (eE0 ((ρ σ).baseChange E x)) = _
  have hcomm : ιbc ((ρ σ).baseChange E x) = (ρ σ).baseChange Ω (ιbc x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => rfl
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  rw [hcompat, hcomm, he', ← hcompat]
  change _ = inclPair E ((matRep p ρE (gfToGqp p F σ)) (eE0 x).1,
    (matRep p ρE (gfToGqp p F σ)) (eE0 x).2)
  rw [inclPair_apply, inclPair_apply]
  simp only [Prod.mk.injEq]
  constructor <;> funext i <;> rw [matRep_apply, matMap_mulVec] <;> rfl

end Coef

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/BdREmb.lean

/-!
# G9: the action of `G_{ℚ_p}` on `B_dR`, and `F' ⊆ B_dR` equivariantly

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

* `bdrAct_mul`, `bdrAct_one`: pkg-I4's `bdrAct` is an action (functoriality of pkg-I4's
  `DR.bdrMap`, through the tilt, Witt vectors, `[1/p]` and the adic completion), packaged as the
  representation `bdrActHom : G_{ℚ_p} →* End_{ℚ_p}(B_dR)`.
* `thetaPlusCp_bdrPlusMap`: bdr-kertheta's residue map `θ⁺ : B_dR^+ → ℂ_p` is equivariant.
* `thetaPlusCp_qpToPlus`: `θ⁺` is `ℚ_p`-linear for pkg-I4's `ℚ_p ⊆ B_dR^+`.
* `iotaDR`, `bdrAct_iotaDR`: for a finite Galois `F/ℚ_p`, the copy `F' ⊆ ℚ̄_p` of `F` embeds in
  `B_dR` with `σ(ι x) = ι(σ x)`, by the Hensel lift (`HenselEmb.lean`) through `θ⁺`
  (`B_dR^+` is `(ξ)`-adically complete, local with maximal ideal `ker θ⁺ = (ξ)`, a domain:
  bdr-kertheta).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module Ideal

noncomputable section

namespace DRFunct

open _root_.PkgI4.DR ZInQ.Contrib.G9.PkgI4.DR

variable (p : ℕ) [Fact p.Prime]

section general

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem modPMap_comp (f : R →+* S) (g : S →+* T) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem modPMap_id : modPMap p (RingHom.id R) = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem wittMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) :
    WittVector.map (p := p) (g.comp f) = (WittVector.map g).comp (WittVector.map f) := by
  ext x n
  simp

theorem wittMap_id {A : Type*} [CommRing A] :
    WittVector.map (p := p) (RingHom.id A) = RingHom.id _ := by
  ext x n
  simp

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]

theorem preTiltMap_comp (f : R →+* S) (g : S →+* T) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) :=
  RingHom.ext fun x => Perfection.ext fun n => by
    rw [coeff_preTiltMap, RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, modPMap_comp]
    rfl

theorem preTiltMap_id : preTiltMap p (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => Perfection.ext fun n => by
    rw [coeff_preTiltMap, modPMap_id]
    rfl

theorem locMap_comp (f : R →+* S) (g : S →+* T) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, locMap, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  rw [preTiltMap_comp, wittMap_comp]
  rfl

theorem locMap_id : locMap p (RingHom.id R) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  rw [preTiltMap_id, wittMap_id]
  rfl

end general

section adic

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

theorem adicMap_congr (J : Ideal A) (J' : Ideal B) {g g' : A →+* B} (h : g = g')
    (hg : J ≤ J'.comap g) (hg' : J ≤ J'.comap g') : adicMap J J' g hg = adicMap J J' g' hg' := by
  subst h; rfl

theorem adicMap_comp_apply (J : Ideal A) (J' : Ideal B) (J'' : Ideal C) (g1 : A →+* B)
    (h1 : J ≤ J'.comap g1) (g2 : B →+* C) (h2 : J' ≤ J''.comap g2) (g3 : A →+* C)
    (h3 : J ≤ J''.comap g3) (hg : g3 = g2.comp g1) (x : AdicCompletion J A) :
    adicMap J J'' g3 h3 x = adicMap J' J'' g2 h2 (adicMap J J' g1 h1 x) := by
  subst hg
  refine AdicCompletion.ext_evalₐ fun n => ?_
  have hin := adicMap_evalₐ J J' g1 h1 n x
  rw [adicMap_evalₐ, adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply] at hin ⊢
  erw [hin]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

theorem evalOneₐ_adicMap (J : Ideal A) (J' : Ideal B) (g : A →+* B) (hg : J ≤ J'.comap g)
    (x : AdicCompletion J A) :
    AdicCompletion.evalOneₐ J' (adicMap J J' g hg x) =
      Ideal.quotientMap J' g hg (AdicCompletion.evalOneₐ J x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J 1 x)
  have e1 : AdicCompletion.evalOneₐ J x =
      Ideal.Quotient.factor (show J ^ 1 ≤ J by simp) (AdicCompletion.evalₐ J 1 x) := rfl
  have e2 : AdicCompletion.evalOneₐ J' (adicMap J J' g hg x) =
      Ideal.Quotient.factor (show J' ^ 1 ≤ J' by simp)
        (AdicCompletion.evalₐ J' 1 (adicMap J J' g hg x)) := rfl
  rw [e1, e2, adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply]
  erw [← ha]
  rfl

theorem adicMap_id_apply (J : Ideal A) (g : A →+* A) (h : J ≤ J.comap g)
    (hg : g = RingHom.id A) (x : AdicCompletion J A) : adicMap J J g h x = x := by
  subst hg
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

end adic

section bdr

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]
  [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
  [IsAdicComplete (span {(p : T)}) T]

theorem bdrPlusMap_comp (f : R →+* S) (g : S →+* T) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) :=
  RingHom.ext fun x => adicMap_comp_apply _ _ _ (locMap p f) (ker_le_comap_locMap p f)
    (locMap p g) (ker_le_comap_locMap p g) _ _ (locMap_comp p f g) x

theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => adicMap_id_apply _ _ _ (locMap_id p) x

theorem bdrMap_comp (f1 : R →+* S) (g1 : S →+* R) (hgf1 : ∀ x, g1 (f1 x) = x)
    (hfg1 : ∀ y, f1 (g1 y) = y) (f2 : S →+* T) (g2 : T →+* S) (hgf2 : ∀ x, g2 (f2 x) = x)
    (hfg2 : ∀ y, f2 (g2 y) = y) (f3 : R →+* T) (g3 : T →+* R) (hgf3 : ∀ x, g3 (f3 x) = x)
    (hfg3 : ∀ y, f3 (g3 y) = y) (hf : f3 = f2.comp f1) :
    bdrMap p f3 g3 hgf3 hfg3 = (bdrMap p f2 g2 hgf2 hfg2).comp (bdrMap p f1 g1 hgf1 hfg1) := by
  apply IsLocalization.ringHom_ext (genMonoid p R)
  ext x
  simp only [RingHom.comp_apply, bdrMap, IsLocalization.map_eq]
  subst hf
  rw [bdrPlusMap_comp]
  rfl

theorem bdrMap_id (f : R →+* R) (g : R →+* R) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) (hf : f = RingHom.id R) :
    bdrMap p f g hgf hfg = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (genMonoid p R)
  ext x
  simp only [RingHom.comp_apply, bdrMap, IsLocalization.map_eq, RingHom.id_apply]
  subst hf
  rw [bdrPlusMap_id]
  rfl

end bdr

end DRFunct

section Action

variable (p : ℕ) [Fact p.Prime]

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) :=
  RingHom.ext fun x => Subtype.ext (cpAct_mul p σ τ x)

theorem oAct_one : oAct p 1 = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (cpAct_one p x)

theorem bdrAct_mul (σ τ : GQp p) : bdrAct p (σ * τ) = (bdrAct p σ).comp (bdrAct p τ) :=
  DRFunct.bdrMap_comp p _ _ _ _ _ _ _ _ _ _ _ _ (oAct_mul p σ τ)

theorem bdrAct_one : bdrAct p 1 = RingHom.id _ :=
  DRFunct.bdrMap_id p _ _ _ _ (oAct_one p)

/-- `σ` acting `ℚ_p`-linearly on `B_dR`. -/
def bdrActL (σ : GQp p) : BdR p →ₗ[ℚ_[p]] BdR p where
  toFun := bdrAct p σ
  map_add' := map_add _
  map_smul' := bdrAct_smul p σ

/-- **The representation `G_{ℚ_p} → End_{ℚ_p}(B_dR)`.** -/
def bdrActHom : GQp p →* (BdR p →ₗ[ℚ_[p]] BdR p) where
  toFun := bdrActL p
  map_one' := LinearMap.ext fun x => by
    change bdrAct p 1 x = x
    rw [bdrAct_one]; rfl
  map_mul' σ τ := LinearMap.ext fun x => by
    change bdrAct p (σ * τ) x = bdrAct p σ (bdrAct p τ x)
    rw [bdrAct_mul]; rfl

theorem bdrActHom_apply (σ : GQp p) (x : BdR p) : bdrActHom p σ x = bdrAct p σ x := rfl

end Action

/-! ### `θ⁺` is equivariant and `ℚ_p`-linear -/

section Theta

variable (p : ℕ) [Fact p.Prime]

theorem thetaPlus_eq' (z : BDeRhamPlus 𝓞_ℂ_[p] p) : BdrKer.Cp.thetaPlus p z =
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) z) := rfl

theorem thetaPlus_mk (σ : GQp p) (x : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (Ideal.quotientMap _ (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ))
        (Ideal.Quotient.mk _ x)) =
    DR.locMapBase p (oAct p σ) ((RingHom.quotientKerEquivOfSurjective
      (BdrKer.Cp.fontaineThetaInvertP_surjective p)) (Ideal.Quotient.mk _ x)) := by
  rw [Ideal.quotientMap_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← RingHom.comp_apply, DR.fontaineThetaInvertP_naturality]
  rfl

theorem thetaPlus_quot (σ : GQp p)
    (q : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸
      RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) :
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (Ideal.quotientMap _ (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ)) q) =
    DR.locMapBase p (oAct p σ) ((RingHom.quotientKerEquivOfSurjective
      (BdrKer.Cp.fontaineThetaInvertP_surjective p)) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact thetaPlus_mk p σ x

theorem thetaPlus_bdrPlusMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlus p (DR.bdrPlusMap p (oAct p σ) y) =
      DR.locMapBase p (oAct p σ) (BdrKer.Cp.thetaPlus p y) := by
  have h := DRFunct.evalOneₐ_adicMap (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) (DR.locMap p (oAct p σ))
    (DR.ker_le_comap_locMap p (oAct p σ)) y
  rw [thetaPlus_eq', thetaPlus_eq']
  rw [show DR.bdrPlusMap p (oAct p σ) y = DR.adicMap _ _ (DR.locMap p (oAct p σ))
    (DR.ker_le_comap_locMap p (oAct p σ)) y from rfl, h]
  exact thetaPlus_quot p σ _

theorem awayEquivCp_locMapBase (σ : GQp p) (u : Localization.Away (p : 𝓞_ℂ_[p])) :
    BdrKer.Cp.awayEquivCp p (DR.locMapBase p (oAct p σ) u) =
      cpAct p σ (BdrKer.Cp.awayEquivCp p u) := by
  have h : (BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom.comp (DR.locMapBase p (oAct p σ)) =
      (cpAct p σ).comp (BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : 𝓞_ℂ_[p]))
    ext o
    simp only [RingHom.comp_apply, DR.locMapBase, Localization.awayLift,
      IsLocalization.Away.lift, IsLocalization.lift_eq]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.commutes]
    rfl
  exact congrArg (fun φ => φ u) h

/-- **`θ⁺` is `G_{ℚ_p}`-equivariant.** -/
theorem thetaPlusCp_bdrPlusMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) y) =
      cpAct p σ (BdrKer.Cp.thetaPlusCp p y) := by
  change BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p _) =
    cpAct p σ (BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p y))
  rw [thetaPlus_bdrPlusMap, awayEquivCp_locMapBase]

/-- `ℚ_p → B_dR^+` (pkg-I4's `ofLoc ∘ qpToLoc`). -/
def qpToPlus : ℚ_[p] →+* BDeRhamPlus 𝓞_ℂ_[p] p := (ofLoc p).comp (qpToLoc p)

theorem qpToBdR_eq (c : ℚ_[p]) :
    qpToBdR p c = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (qpToPlus p c) := rfl

theorem bdrPlusMap_qpToPlus (σ : GQp p) (c : ℚ_[p]) :
    DR.bdrPlusMap p (oAct p σ) (qpToPlus p c) = qpToPlus p c := by
  have h : (DR.bdrPlusMap p (oAct p σ)).comp (qpToPlus p) = qpToPlus p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToPlus]
    rw [qpToLoc_algebraMap, bdrPlusMap_ofLoc, locMap_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

theorem thetaPlusCp_zp_eq (z : ℤ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] z)) =
      ((WittVector.fontaineTheta (𝓞_ℂ_[p]) p (zpToW p z) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  simp only [qpToPlus, RingHom.comp_apply, qpToLoc_algebraMap]
  have e : ofLoc p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
      (zpToW p z)) = BdrKer.ofPlus _ p (algebraMap _ _ (zpToW p z)) := by
    rw [ofLoc]
    erw [AdicCompletion.algebraMap_apply]
    rfl
  rw [e]
  change BdrKer.Cp.awayEquivCp p (fontaineThetaInvertP _ p (algebraMap _ _ (zpToW p z))) = _
  simp only [fontaineThetaInvertP, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq, RingHom.comp_apply]
  rw [AlgEquiv.commutes]
  rfl

theorem norm_algebraMap_qp (c : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem thetaPlusCp_zp (z : ℤ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] z)) =
      algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] z) := by
  set g1 := (BdrKer.Cp.thetaPlusCp p).comp ((qpToPlus p).comp (algebraMap ℤ_[p] ℚ_[p]))
  set g2 := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  change g1 z = g2 z
  have hb1 : ∀ w, ‖g1 w‖ ≤ 1 := fun w => by
    change ‖BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] w))‖ ≤ 1
    rw [thetaPlusCp_zp_eq]
    exact (Cp.mem_O_iff p _).mp (Subtype.prop _)
  have hb2 : ∀ w, ‖g2 w‖ ≤ 1 := fun w => by
    change ‖algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] w)‖ ≤ 1
    rw [norm_algebraMap_qp]
    exact PadicInt.norm_le_one w
  by_contra hne
  have hd : 0 < ‖g1 z - g2 z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hd) (Cp.norm_p_lt_one p)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[p]) + w * (p : ℤ_[p]) ^ n := by
    rw [hw]; ring
  have hdiff : g1 z - g2 z = (g1 w - g2 w) * (p : ℂ_[p]) ^ n := by
    rw [hz, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  have hle : ‖g1 z - g2 z‖ ≤ 2 * ‖(p : ℂ_[p])‖ ^ n := by
    rw [hdiff, norm_mul, norm_pow]
    have : ‖g1 w - g2 w‖ ≤ 2 := by
      calc ‖g1 w - g2 w‖ ≤ ‖g1 w‖ + ‖g2 w‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hb1 w) (hb2 w)
        _ = 2 := by norm_num
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

/-- **`θ⁺` is `ℚ_p`-linear**: `θ⁺(c) = c` for `c ∈ ℚ_p ⊆ B_dR^+`. -/
theorem thetaPlusCp_qpToPlus (c : ℚ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p c) = algebraMap ℚ_[p] ℂ_[p] c := by
  have hext : (BdrKer.Cp.thetaPlusCp p).comp (qpToPlus p) = algebraMap ℚ_[p] ℂ_[p] := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply]
    exact thetaPlusCp_zp p z
  exact congrArg (fun φ => φ c) hext

end Theta

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/G9.lean

/-!
# G9: N5's appendix lemma — `r` is de Rham with Hodge–Tate weights `0, −1`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Glue step G9 of `docs/research/h-decomposition.md` (N5, Lemma `lem:de-rham-descent`,
`diophantine_zq.tex` L10939-11000), at `K = ℚ_p` with `F/ℚ_p` finite Galois (the case N5 uses:
`docs/research/h-trust.md` C3, "Galois choice of the field").

**`g9_deRham`.** Hypotheses: the leaf R10 (`PkgI4.DeRhamComparison`, restated verbatim in
`I4Layer.lean`) and G8's output localized at `p`: a finite Galois `F/ℚ_p`, an abelian surface
`A/F` (pkg-I3/I4's `AbVar`, `dim A = 2`), a finite `C/ℚ_p`, `r : G_{ℚ_p} → GL₂(C)` and a
`C`-linear isomorphism `e : C ⊗_{ℚ_p} V_p(A) ≅ C² × C²` intertwining `G_F` (acting through
pkg-I4's `gfToGqp`) with `r|G_F ⊕ r|G_F` (the form of G8's output in
`PkgI3.C2_absolutelyIrreducible`). Conclusion: `IsDeRham p r`, `htMult p r 0 = 1` and
`htMult p r (−1) = 1`.

T23 (Fontaine's closure properties) and T10 (Tate duality, an `opaque` placeholder) are not
used: R10's Lean form is already about `V_p(A)`, the subquotient step is a dimension count
(`overF_count`), and the finite descent is Speiser's lemma through `ℚ̄_p ⊆ B_dR^+`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module Ideal
open scoped TensorProduct

noncomputable section

section Emb

variable (p : ℕ) [Fact p.Prime]

/-- `B_dR^+` as a `ℚ_p`-algebra through pkg-I4's `ℚ_p ⊆ B_dR^+` (`ofLoc ∘ qpToLoc`). -/
@[instance_reducible] def algPlus : Algebra ℚ_[p] (BDeRhamPlus 𝓞_ℂ_[p] p) := (qpToPlus p).toAlgebra

attribute [local instance] algPlus

/-- `θ⁺ : B_dR^+ → ℂ_p` as a `ℚ_p`-algebra map. -/
def thetaAlg : BDeRhamPlus 𝓞_ℂ_[p] p →ₐ[ℚ_[p]] ℂ_[p] :=
  { BdrKer.Cp.thetaPlusCp p with commutes' := fun c => thetaPlusCp_qpToPlus p c }

theorem thetaAlg_apply (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    thetaAlg p y = BdrKer.Cp.thetaPlusCp p y := rfl

/-- `σ` acting on `B_dR^+`, as a `ℚ_p`-algebra map. -/
def sPlus (σ : GQp p) : BDeRhamPlus 𝓞_ℂ_[p] p →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p :=
  { DR.bdrPlusMap p (oAct p σ) with commutes' := fun c => bdrPlusMap_qpToPlus p σ c }

theorem ker_thetaAlg : RingHom.ker (thetaAlg p).toRingHom =
    span {BdrKer.ofPlus _ p (BdrKer.Cp.xi' p)} := BdrKer.Cp.ker_thetaPlusCp p

instance henselian_thetaAlg :
    HenselianRing (BDeRhamPlus 𝓞_ℂ_[p] p) (RingHom.ker (thetaAlg p).toRingHom) := by
  rw [ker_thetaAlg]
  infer_instance

theorem isUnit_of_thetaAlg_ne_zero (y : BDeRhamPlus 𝓞_ℂ_[p] p) (hy : thetaAlg p y ≠ 0) :
    IsUnit y := by
  by_contra hnu
  have hm : y ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := hnu
  rw [BdrKer.Cp.maximalIdeal_BDeRhamPlus, ← BdrKer.Cp.ker_thetaPlusCp] at hm
  exact hy (RingHom.mem_ker.mp hm)

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem exists_iotaPlus : ∃ ι₀ : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p,
    ∀ x, thetaAlg p (ι₀ x) = iotaCp p F x :=
  exists_hensel_lift (thetaAlg p) (BdrKer.Cp.thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) (iotaCp p F)

/-- **`F' ⊆ B_dR^+`**: the Hensel lift of `F' ⊆ ℚ̄_p ⊆ ℂ_p` through `θ⁺`. -/
def iotaPlus : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p := (exists_iotaPlus p F).choose

theorem thetaAlg_iotaPlus (x : fieldF p F) : thetaAlg p (iotaPlus p F x) = iotaCp p F x :=
  (exists_iotaPlus p F).choose_spec x

theorem bdrPlusMap_iotaPlus (σ : GQp p) (x : fieldF p F) :
    DR.bdrPlusMap p (oAct p σ) (iotaPlus p F x) = iotaPlus p F (gammaF p F σ x) :=
  hensel_lift_natural (thetaAlg p) (iotaCp p F) (iotaPlus p F) (thetaAlg_iotaPlus p F)
    (sPlus p σ) (gammaF p F σ : fieldF p F ≃ₐ[ℚ_[p]] fieldF p F).toAlgHom (fun y => by
      change BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) (iotaPlus p F y)) = _
      rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, thetaAlg_iotaPlus, cpAct_iotaCp]
      rfl) x

/-- **`F' ⊆ B_dR`**, a `ℚ_p`-algebra map for pkg-I4's `ℚ_p ⊆ B_dR`. -/
def iotaDR : fieldF p F →ₐ[ℚ_[p]] BdR p :=
  { (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp (iotaPlus p F).toRingHom with
    commutes' := fun c => by
      change algebraMap _ (BdR p) (iotaPlus p F (algebraMap ℚ_[p] _ c)) = qpToBdR p c
      rw [AlgHom.commutes]
      rfl }

theorem iotaDR_apply (x : fieldF p F) :
    iotaDR p F x = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (iotaPlus p F x) := rfl

/-- **Equivariance**: `σ(ι x) = ι(σ x)` in `B_dR`. -/
theorem bdrAct_iotaDR (σ : GQp p) (x : fieldF p F) :
    bdrAct p σ (iotaDR p F x) = iotaDR p F (gammaF p F σ x) := by
  rw [iotaDR_apply, iotaDR_apply, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_iotaPlus]

theorem bdrActHom_semi (σ : GQp p) (x : fieldF p F) (b : BdR p) :
    bdrActHom p σ (iotaDR p F x * b) = iotaDR p F (gammaF p F σ x) * bdrActHom p σ b := by
  rw [bdrActHom_apply, bdrActHom_apply, map_mul, bdrAct_iotaDR]

end Emb

section DeRham

variable (p : ℕ) [Fact p.Prime]

theorem ddrSpace_eq_DspAct {C : Type*} [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    {n : ℕ} (r : GQp p →* GL (Fin n) C) :
    ddrSpace p r = Dsp (bdrActHom p) (rRep p r) Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

theorem ddrSpaceOver_eq_DspAct (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ddrSpaceOver p ρ = Dsp ((bdrActHom p).comp (gfToGqp p F)) ρ Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

/-- **G9, de Rham part.** Same hypotheses as `htMult_eq_one_of_R10`; conclusion `IsDeRham p r`. -/
theorem isDeRham_of_R10 (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r := by
  obtain ⟨hdr, -, -⟩ := hR10 p F A 2 hA
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hC : 0 < finrank ℚ_[p] C := Module.finrank_pos
  have hV : finrank ℚ_[p] (A.V p) = 4 := by
    have h := e.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h
    exact h
  set act := bdrActHom p
  have hnV : finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ) =
      finrank ℚ_[p] F * 4 := by
    rw [← ddrSpaceOver_eq_DspAct, ← hV]
    exact hdr
  have hpos : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ) := by
    rw [hnV]; positivity
  have hd := descended_finrank p F (A.galRep p) C r e he act (iotaDR p F)
    (bdrActHom_semi p F) hpos
  rw [hnV] at hd
  rw [IsDeRham, ddrSpace_eq_DspAct]
  have : finrank ℚ_[p] F * 2 * (2 * finrank ℚ_[p] C) =
      finrank ℚ_[p] F * 2 * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
    linarith [hd]
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm

/-- **G9 (N5's appendix lemma at `K = ℚ_p`, `F/ℚ_p` Galois).** From the leaf R10 and G8's output
localized at `p`: `r` is de Rham, with Hodge–Tate multiplicity `1` at the weights `0` and `−1`. -/
theorem g9_deRham (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r ∧ htMult p r 0 = 1 ∧ htMult p r (-1) = 1 :=
  ⟨isDeRham_of_R10 p hR10 F A hA C r e he, htMult_eq_one_of_R10 p hR10 F A hA C r e he⟩

/-- **G9 in the `ℚ̄_p`-valued form used by `PanBerger`** (`LocalIsDeRham`): if the coefficient
field is a finite `E ⊆ ℚ̄_p` and `ρ` is `r` viewed in `GL₂(ℚ̄_p)`, then `ρ` is de Rham. -/
theorem g9_localIsDeRham (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (r : GQp p →* GL (Fin 2) E) (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p))
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) = ρ σ)
    (e : E ⊗[ℚ_[p]] A.V p ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ v, e (GlueI3.repBaseChange E (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).2)) :
    LocalIsDeRham p 2 ρ :=
  ⟨E, inferInstance, r, hρ, isDeRham_of_R10 p hR10 F A hA E r e he⟩

end DeRham

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/G9Weights.lean

/-!
# G9 with the full weight multiset `{0, −1}`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

R10's Lean form (`PkgI4.DeRhamComparison`) fixes the Hodge–Tate multiplicities of `V_p(A)` at
the weights `0` and `−1` only. N5's conclusion "the Hodge–Tate weights of `r` are `0, −1`", in
pkg-I4's form `HasHTWeights p r {0, −1}` (every multiplicity), also needs the vanishing of the
other multiplicities of `V_p(A)`. That vanishing is part of the published theorem (the Hodge–Tate
decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Faltings 1988 / Fontaine 1982 / Tate 1967,
together with Tate's `ℂ_p(i)^{G_F} = 0` for `i ≠ 0`; numbers UNVERIFIED), but not of R10's Lean
form. It is stated here as the separate Prop `DeRhamComparisonWeights` (a candidate strengthening
of R10's Lean form), and `g9_hasHTWeights` takes it as an extra hypothesis.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-- **R10, weight clause** (not in R10's Lean form; part of the published statement): `V_p(A)`
has no Hodge–Tate weight other than `0` and `−1`. -/
def DeRhamComparisonWeights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

section Weights

variable (p : ℕ) [Fact p.Prime]

theorem htMult_eq_zero_of_R10w (hR10w : DeRhamComparisonWeights) (F : Type) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2))
    (w : ℤ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : htMult p r w = 0 := by
  have hz := hR10w p F A 2 hA w hw0 hw1
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  set i := -w
  set act := cpActHom p i
  set nV := finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ)
  have hnV : finrank ℚ_[p] (htSpaceOver p (A.galRep p) i) = nV := by
    rw [htSpaceOver_eq_DspAct]
  have hdvd : finrank ℚ_[p] F ∣ nV := by
    have := finrank_dvd_Dsp_of_emb (act.comp (gfToGqp p F)) (fun σ => A.galRep p σ) Set.univ
      (iotaCp p F) (fun σ _ x b => by
        have hk : gfToGqp p F σ ∈ (gammaF p F).ker := by
          rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
        rw [MonoidHom.mem_ker] at hk
        change act (gfToGqp p F σ) _ = _
        rw [cpActHom_semi, hk]
        rfl)
    rwa [finrank_fieldF] at this
  obtain ⟨k, hk⟩ := hdvd
  have hnV0 : nV = 0 := by
    have : htMultOver p (A.galRep p) w = k := by
      rw [htMultOver, hnV, hk, Nat.mul_div_cancel_left _ hF]
    rw [hz] at this
    rw [hk, ← this, mul_zero]
  by_contra hne
  have hG : 0 < finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
    rw [htMult, htSpace_eq_DspAct] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by rw [h0, Nat.zero_div])
  have hdes := descent_finrank act (rRep p r) (iotaCp p F) (gammaF p F) (gammaF_surjective p F)
    (cpActHom_semi p F i)
  rw [Dsp_ker_gammaF, finrank_fieldF] at hdes
  have hU : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F))
      (fun σ => rRep p r (gfToGqp p F σ)) Set.univ) := by
    change 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F))
      ((rRep p r).comp (gfToGqp p F)) Set.univ)
    rw [hdes]
    positivity
  have := overF_pos_rev (act.comp (gfToGqp p F)) (C := C) (fun σ => A.galRep p σ)
    (fun σ => rRep p r (gfToGqp p F σ)) Set.univ e (fun σ x => he σ x) hU
  change 0 < nV at this
  omega

/-- **G9 with the full weight multiset.** From R10, its weight clause
`DeRhamComparisonWeights`, and G8's local output: `r` is de Rham with Hodge–Tate weights exactly
`{0, −1}` (pkg-I4's `HasHTWeights`). -/
theorem g9_hasHTWeights (hR10 : DeRhamComparison) (hR10w : DeRhamComparisonWeights)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r ∧ HasHTWeights p r {0, -1} := by
  obtain ⟨hdr, h0, h1⟩ := g9_deRham p hR10 F A hA C r e he
  refine ⟨hdr, fun w => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0; rw [h0]; decide
  by_cases hw1 : w = -1
  · subst hw1; rw [h1]; decide
  rw [htMult_eq_zero_of_R10w p hR10w F A hA C r e he w hw0 hw1]
  simp [hw0, hw1]

/-- The `ℚ̄_p`-valued form (`LocalIsDeRham`, `LocalHasHTWeights`) for a coefficient field
`E ⊆ ℚ̄_p`. -/
theorem g9_local (hR10 : DeRhamComparison) (hR10w : DeRhamComparisonWeights)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (r : GQp p →* GL (Fin 2) E) (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p))
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) = ρ σ)
    (e : E ⊗[ℚ_[p]] A.V p ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ v, e (GlueI3.repBaseChange E (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).2)) :
    LocalIsDeRham p 2 ρ ∧ LocalHasHTWeights p ρ {0, -1} := by
  obtain ⟨hdr, hht⟩ := g9_hasHTWeights p hR10 hR10w F A hA E r e he
  exact ⟨⟨E, inferInstance, r, hρ, hdr⟩, ⟨E, inferInstance, r, hρ, hht⟩⟩

end Weights

end

end ZInQ.Contrib.G9

-- ===== ZInQKernel/Contrib/G9/Reduction.lean

/-!
# G9: `G9Glue` from three named bridge statements

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

g0-mod-galois's `G9Glue` (restated verbatim in `Statement.lean`) assumes R10
(`PkgI4.DeRhamComparison`) and T23 (`PkgI4.T23_FontaineClosure`). Its conclusion `G9Out r` needs
three facts that are neither among these hypotheses nor in Mathlib (docs/research/g9-derham.md,
findings F1-F3):

* `G9Bridge.LocalModel` (F2): base change of the abelian surface `A/K` to a finite Galois
  `F/ℚ_ℓ` (a completion of a Galois closure at a place above `ℓ`), as an abelian variety of
  pkg-I4's copy `PkgI4.I3.AbVar`, with `V_ℓ(A_F) ≅ V_ℓ(A)|G_F` (every `ℓⁿ`-torsion point of `A`
  over `F̄` is defined over `K̄`), and the decomposition group compatible with `resQ` up to
  conjugation. STANDARD (Mumford, *Abelian varieties*, §4 Thm/§6 Prop on `[n]`; UNVERIFIED
  locators).
* `G9Bridge.R10Weights` (F1): the Hodge–Tate multiplicities of `V_p(A)` vanish outside
  `{0, −1}`. This is part of the published R10 (Hodge–Tate decomposition
  `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Tate 1967 / Faltings 1988, with Tate's
  `ℂ_p(j)^{G_F} = 0` for `j ≠ 0`); the Lean R10 records only the weights `0, −1`.
* `G9Bridge.BdRContainsQbar` (F3): `ℚ̄_p ⊆ B_dR` `G_{ℚ_p}`-equivariantly (Fontaine; Hensel's
  lemma in the complete DVR `B_dR^+`, whose residue field is `ℂ_p ⊇ ℚ̄_p`). STANDARD.

`g9Glue_of_bridges : LocalModel → R10Weights → BdRContainsQbar → G9Glue` is proved: the rest of
N5's argument (the finite coefficient field, the counting through `E ⊗ V ≅ r ⊕ r`, the Galois
descent from `F` to `ℚ_ℓ`) is in `CoefDescent.lean` and `LocalCore.lean`. T23 is not used.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 Module G0Galois
open scoped TensorProduct

noncomputable section

namespace G9Bridge

/-- **Bridge F2 (local model).** For an abelian surface `A` over a number field `K` and a prime
`ℓ`, there are a finite Galois extension `F/ℚ_ℓ`, an abelian surface `A'` over `F` (pkg-I4's copy
of pkg-I3's abelian varieties; `A' = A ×_K F` for an embedding `K → F`), a homomorphism
`j : G_F → G_K` (restriction along `K̄ → F̄`), a `ℚ_ℓ`-linear isomorphism `V_ℓ(A') ≅ V_ℓ(A)`
intertwining `G_F` with `G_K` through `j`, and `g ∈ G_ℚ` with
`resQ K (j σ) = g · decomp(σ) · g⁻¹` for `σ ∈ G_F` (the decomposition groups of `G_F` inside
`G_ℚ` through `K` and through `ℚ_ℓ` agree up to the choice of embeddings). -/
def LocalModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], A.dim = 2 →
    ∃ (F : Type) (_ : Field F) (_ : Algebra ℚ_[ℓ] F) (_ : FiniteDimensional ℚ_[ℓ] F)
      (_ : IsGalois ℚ_[ℓ] F) (A' : PkgI4.I3.AbVar F)
      (j : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup K)
      (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ) (g : PkgI4.GQ),
      A'.dim = 2 ∧ (∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (j σ) (c v)) ∧
      ∀ σ, resQ K (j σ) = g * PkgI4.decomp ℓ (PkgI4.gfToGqp ℓ F σ) * g⁻¹

/-- **Bridge F1 (the rest of R10).** For an abelian variety `A` over a finite `F/ℚ_p`, the
Hodge–Tate multiplicities of `V_p(A)` vanish at every weight other than `0` and `−1`. -/
def R10Weights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ), w ≠ 0 → w ≠ -1 → PkgI4.htMultOver p (A.galRep p) w = 0

/-- **Bridge F3.** `ℚ̄_p` embeds into `B_dR` as a `ℚ_p`-algebra, `G_{ℚ_p}`-equivariantly. -/
def BdRContainsQbar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ ι : PadicAlgCl p →ₐ[ℚ_[p]] PkgI4.BdR p,
    ∀ (σ : PkgI4.GQp p) (x : PadicAlgCl p), PkgI4.bdrAct p σ (ι x) = ι (σ x)

/-- `F' ⊆ B_dR` semilinearly, for every finite Galois `F/ℚ_p` (`F' = fieldF p F ⊆ ℚ̄_p`).
Not a bridge: implied by `BdRContainsQbar` (`fieldEmbBdR_of_bdRContainsQbar`) and proved outright
in `Final.lean` from the second run's `iotaDR` (`G9.lean`). -/
def FieldEmbBdR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F], ∃ ι' : fieldF p F →ₐ[ℚ_[p]] PkgI4.BdR p,
      ∀ (σ : PkgI4.GQp p) (x : fieldF p F), PkgI4.bdrAct p σ (ι' x) = ι' (gammaF p F σ x)

theorem fieldEmbBdR_of_bdRContainsQbar (h : BdRContainsQbar) : FieldEmbBdR := by
  intro p _ F _ _ _ _
  obtain ⟨ι, hι⟩ := h p
  exact ⟨ι.comp (fieldF p F).val, fun σ x => by
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, hι, gammaF_apply_coe]⟩

end G9Bridge

section Assembly

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem galoisRep_mat_mul (r : GaloisRep ℓ 2) (a b : PkgI4.GQ) :
    r.mat (a * b) = r.mat a * r.mat b := by
  simp [GaloisRep.mat, map_mul, Units.val_mul]

theorem galoisRep_mat_inv_mul (r : GaloisRep ℓ 2) (a : PkgI4.GQ) : r.mat a⁻¹ * r.mat a = 1 := by
  rw [← galoisRep_mat_mul, inv_mul_cancel]
  simp [GaloisRep.mat]

theorem galoisRep_mat_mul_inv (r : GaloisRep ℓ 2) (a : PkgI4.GQ) : r.mat a * r.mat a⁻¹ = 1 := by
  rw [← galoisRep_mat_mul, mul_inv_cancel]
  simp [GaloisRep.mat]

/-- Multiplication by `r(g)⁻¹` on both factors. -/
def twistPair (r : GaloisRep ℓ 2) (g : PkgI4.GQ) :
    ((Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) ≃ₗ[PadicAlgCl ℓ]
      ((Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) :=
  LinearEquiv.ofLinear
    ((Matrix.mulVecLin (r.mat g⁻¹)).prodMap (Matrix.mulVecLin (r.mat g⁻¹)))
    ((Matrix.mulVecLin (r.mat g)).prodMap (Matrix.mulVecLin (r.mat g)))
    (LinearMap.ext fun w => by
      change ((r.mat g⁻¹).mulVec ((r.mat g).mulVec w.1),
        (r.mat g⁻¹).mulVec ((r.mat g).mulVec w.2)) = w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, galoisRep_mat_inv_mul, Matrix.one_mulVec,
        Matrix.one_mulVec])
    (LinearMap.ext fun w => by
      change ((r.mat g).mulVec ((r.mat g⁻¹).mulVec w.1),
        (r.mat g).mulVec ((r.mat g⁻¹).mulVec w.2)) = w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, galoisRep_mat_mul_inv, Matrix.one_mulVec,
        Matrix.one_mulVec])

theorem twistPair_apply (r : GaloisRep ℓ 2) (g : PkgI4.GQ)
    (w : (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) :
    twistPair r g w = ((r.mat g⁻¹).mulVec w.1, (r.mat g⁻¹).mulVec w.2) := rfl

end Assembly

/-- **G9 (N5's Lemma `lem:de-rham-descent`), from `LocalModel`, `R10Weights` and an
embedding `F' ⊆ B_dR`.** -/
theorem g9Glue_of_fieldEmb (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights)
    (hB : G9Bridge.FieldEmbBdR) : G9Glue := by
  intro hR10 _hT23 K _ _ A ℓ _ r e hdim hint
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ := hLM K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := hB ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  have hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver ℓ (A'.galRep ℓ) w = 0 :=
    fun w hw0 hw1 => hW ℓ F A' w hw0 hw1
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    ⟨E, hE, ρE, hmap, core_ht ℓ F (A'.galRep ℓ) ρE eE he h0 h1 hw⟩⟩

/-- **G9 from the three bridges.** -/
theorem g9Glue_of_bridges (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights)
    (hB : G9Bridge.BdRContainsQbar) : G9Glue :=
  g9Glue_of_fieldEmb hLM hW (G9Bridge.fieldEmbBdR_of_bdRContainsQbar hB)

end

end ZInQ.Contrib.G9


-- ===== ZInQKernel/Contrib/G9/Final.lean

/-!
# G9: `G9Glue` from two bridge statements

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

The embedding `F' ⊆ B_dR` (`G9Bridge.FieldEmbBdR`) is proved by the second run of this task
(`iotaDR`, `bdrAct_iotaDR` in `G9.lean`: Hensel's lemma in `B_dR^+` through bdr-kertheta's
`θ⁺ : B_dR^+ → ℂ_p`, `KerTheta.lean`, `HenselEmb.lean`, `BdREmb.lean`). Hence

`g9Glue_of_localModel : G9Bridge.LocalModel → G9Bridge.R10Weights → G9Glue`

with the standard axioms only. The two remaining hypotheses are findings F2 (base change of
`A/K` to a local field with its Tate module) and F1 (Hodge–Tate multiplicities outside `{0, −1}`
vanish, a clause of the published R10 missing from its Lean form).
-/

namespace ZInQ.Contrib.G9

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 G0Galois

theorem fieldEmbBdR : G9Bridge.FieldEmbBdR := by
  intro p _ F _ _ _ _
  exact ⟨iotaDR p F, bdrAct_iotaDR p F⟩

/-- **G9 (N5's Lemma `lem:de-rham-descent`, g0-mod-galois's `G9Glue`) from F2 and F1.** -/
theorem g9Glue_of_localModel (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights) :
    G9Glue :=
  g9Glue_of_fieldEmb hLM hW fieldEmbBdR

end ZInQ.Contrib.G9


-- ===== ZInQKernel/Contrib/G9/LocalModel.lean

/-!
# G9: the local model, reduced to base change of abelian varieties

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`G9Bridge.LocalModel` (bridge F2 of `Reduction.lean`) mixes Galois theory with algebraic
geometry. Here the Galois theory is proved, and what remains is one statement about abelian
varieties, `G9Bridge.AbVarBaseChange`: for a field embedding `i : K → L` (characteristic 0) and an
abelian variety `A/K`, there is an abelian variety `A'/L` (pkg-I4's copy of pkg-I3's `AbVar`;
`A' = A ×_K L`) with `dim A' = dim A` and `V_ℓ(A') ≅ V_ℓ(A)` intertwining `G_L` with `G_K` through
Mathlib's `Field.absoluteGaloisGroup.map i`. STANDARD (base change of abelian varieties;
`A[ℓⁿ]` is finite étale over `K` in characteristic `≠ ℓ`, so its points over `K̄` and over `L̄`
agree: Mumford, *Abelian varieties*, §4 and §6, locators UNVERIFIED; dimension is invariant under
field extension, EGA IV 4.1.4, UNVERIFIED).

* `localModel_of_abVarBaseChange : AbVarBaseChange → LocalModel`: `K` embeds into a finite
  Galois `F/ℚ_ℓ` inside `ℚ̄_ℓ` (the normal closure of the `ℚ_ℓ`-span of the image of `K`), and
  the two maps `G_F → G_ℚ` (through `K` and through `ℚ_ℓ`) differ by conjugation, because any two
  embeddings `ℚ̄ → F̄` differ by an automorphism of `ℚ̄`.
* `g9Glue_of_abVarBaseChange : AbVarBaseChange → R10Weights → G9Glue`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 G0Galois Module

noncomputable section

namespace G9Bridge

/-- **Bridge F2' (base change of abelian varieties with their Tate modules).** -/
def AbVarBaseChange : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (L : Type) [Field L] (i : K →+* L)
    (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ (A' : PkgI4.I3.AbVar L) (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ), A'.dim = A.dim ∧
      ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

end G9Bridge

section Conj

/-- An element of `G_K` as an automorphism of `K̄`. -/
abbrev galK {K : Type*} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `Field.absoluteGaloisGroup.map f` is restriction along an embedding `K̄ → L̄`. -/
theorem exists_emb_map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    ∃ κ : AlgebraicClosure K →+* AlgebraicClosure L,
      ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
        κ (galK (Field.absoluteGaloisGroup.map f σ) x) = galK σ (κ x) := by
  letI : Algebra K L := f.toAlgebra
  let g0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g0.toAlgebra
  exact ⟨g0.toRingHom, fun σ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) (AlgebraicClosure K) x⟩

/-- Two embeddings of `k̄` into a field over `k` differ by an automorphism of `k̄`. -/
theorem exists_aut_comp {k M : Type*} [Field k] [Field M] [Algebra k M]
    (α1 α2 : AlgebraicClosure k →ₐ[k] M) :
    ∃ δ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, ∀ x, α2 x = α1 (δ x) := by
  letI : Algebra (AlgebraicClosure k) M := α1.toRingHom.toAlgebra
  haveI : IsScalarTower k (AlgebraicClosure k) M :=
    IsScalarTower.of_algebraMap_eq (fun c => (α1.commutes c).symm)
  let δ0 : AlgebraicClosure k →ₐ[k] AlgebraicClosure k :=
    α2.restrictNormal (K₁ := AlgebraicClosure k) (AlgebraicClosure k)
  have h : ∀ x, α1 (δ0 x) = α2 x := fun x =>
    AlgHom.restrictNormal_commutes (K₁ := AlgebraicClosure k) α2 (AlgebraicClosure k) x
  exact ⟨AlgEquiv.ofBijective δ0 (Algebra.IsAlgebraic.algHom_bijective δ0),
    fun x => (h x).symm⟩

/-- Restrictions along two embeddings `ℚ̄ → F̄` are conjugate. -/
theorem conj_of_two_embs {M : Type*} [Field M] [CharZero M] (G : Type*) [Group G] (act : G →* (M ≃+* M))
    (α1 α2 : AlgebraicClosure ℚ →+* M) (τ1 τ2 : G → PkgI4.GQ)
    (h1 : ∀ σ x, α1 (τ1 σ x) = act σ (α1 x)) (h2 : ∀ σ x, α2 (τ2 σ x) = act σ (α2 x)) :
    ∃ g : PkgI4.GQ, ∀ σ, τ1 σ = g * τ2 σ * g⁻¹ := by
  obtain ⟨δ, hδ⟩ := exists_aut_comp (k := ℚ) α1.toRatAlgHom α2.toRatAlgHom
  have hδ' : ∀ x, α2 x = α1 (δ x) := hδ
  refine ⟨δ, fun σ => ?_⟩
  apply AlgEquiv.ext
  intro x
  apply α1.injective
  rw [h1]
  change act σ (α1 x) = α1 (δ (τ2 σ (δ⁻¹ x)))
  rw [← hδ', h2, hδ']
  congr 2
  exact (AlgEquiv.apply_symm_apply δ x).symm

end Conj

section Model

variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]

/-- `K → ℚ̄_ℓ`. -/
def psiK : K →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift

/-- The `ℚ_ℓ`-span of the image of a `ℚ`-basis of `K`. -/
def spanK : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.adjoin ℚ_[ℓ] (Set.range fun k => psiK K ℓ (Module.finBasis ℚ K k))

instance : FiniteDimensional ℚ_[ℓ] (spanK K ℓ) :=
  have : Finite (Set.range fun k => psiK K ℓ (Module.finBasis ℚ K k)) := Set.finite_range _
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem psiK_mem (x : K) : psiK K ℓ x ∈ spanK K ℓ := by
  rw [← (Module.finBasis ℚ K).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun k _ => ?_
  rw [Algebra.smul_def, map_mul, AlgHom.commutes]
  refine IntermediateField.mul_mem _ ?_ (IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩)
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ _

/-- The local field: the normal closure of `spanK` in `ℚ̄_ℓ`. -/
def locF : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.normalClosure ℚ_[ℓ] (spanK K ℓ) (PadicAlgCl ℓ)

instance : FiniteDimensional ℚ_[ℓ] (locF K ℓ) := by
  unfold locF; infer_instance

instance : IsGalois ℚ_[ℓ] (locF K ℓ) := by
  unfold locF
  exact { }

/-- `K → F`. -/
def iK : K →+* locF K ℓ :=
  (psiK K ℓ).toRingHom.codRestrict (locF K ℓ) fun x =>
    IntermediateField.le_normalClosure (spanK K ℓ) (psiK_mem K ℓ x)

end Model

/-- `decomp ℓ` is restriction along an embedding `ℚ̄ → ℚ̄_ℓ`. -/
theorem exists_emb_decomp (ℓ : ℕ) [Fact ℓ.Prime] : ∃ κ : AlgebraicClosure ℚ →+* PadicAlgCl ℓ,
    ∀ (τ : GQp ℓ) (x : AlgebraicClosure ℚ), κ (decomp ℓ τ x) = τ (κ x) := by
  let g0 : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[ℓ]) := g0.toAlgebra
  exact ⟨g0.toRingHom, fun τ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars ℚ τ) (AlgebraicClosure ℚ) x⟩

/-- `σ ↦ σ` as ring automorphisms. -/
def galRingEquivHom (F : Type*) [Field F] :
    Field.absoluteGaloisGroup F →* (AlgebraicClosure F ≃+* AlgebraicClosure F) where
  toFun σ := (galK σ).toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

set_option maxHeartbeats 2000000 in
/-- **The local model from base change of abelian varieties.** -/
theorem localModel_of_abVarBaseChange (h : G9Bridge.AbVarBaseChange) : G9Bridge.LocalModel := by
  intro K _ _ A ℓ _ hdim
  obtain ⟨A', c, hdim', hc⟩ := h K A (locF K ℓ) (iK K ℓ) ℓ
  obtain ⟨κ1, h1⟩ := exists_emb_map (algebraMap ℚ K)
  obtain ⟨κ2, h2⟩ := exists_emb_map (iK K ℓ)
  obtain ⟨κ3, h3⟩ := exists_emb_decomp ℓ
  let j : Field.absoluteGaloisGroup (locF K ℓ) →* Field.absoluteGaloisGroup K :=
    (Field.absoluteGaloisGroup.map (iK K ℓ) : _ →* _)
  have e1 : ∀ σ x, (κ2.comp κ1) (resQ K (j σ) x) =
      galRingEquivHom (locF K ℓ) σ ((κ2.comp κ1) x) := by
    intro σ x
    change κ2 (κ1 (galK (Field.absoluteGaloisGroup.map (algebraMap ℚ K) (j σ)) x)) =
      galK σ (κ2 (κ1 x))
    rw [h1]
    exact h2 σ (κ1 x)
  have e2 : ∀ σ x, ((embF ℓ (locF K ℓ)).comp κ3) (decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) x) =
      galRingEquivHom (locF K ℓ) σ (((embF ℓ (locF K ℓ)).comp κ3) x) := by
    intro σ x
    change embF ℓ (locF K ℓ) (κ3 (decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) x)) =
      galF (locF K ℓ) σ (embF ℓ (locF K ℓ) (κ3 x))
    rw [h3]
    exact embF_gfToGqp ℓ (locF K ℓ) σ (κ3 x)
  obtain ⟨g, hg⟩ := conj_of_two_embs (M := AlgebraicClosure (locF K ℓ))
    (Field.absoluteGaloisGroup (locF K ℓ)) (galRingEquivHom (locF K ℓ))
    (κ2.comp κ1) ((embF ℓ (locF K ℓ)).comp κ3) (fun σ => resQ K (j σ))
    (fun σ => decomp ℓ (gfToGqp ℓ (locF K ℓ) σ)) e1 e2
  have i3 : FiniteDimensional ℚ_[ℓ] (locF K ℓ) := inferInstance
  have i4 : IsGalois ℚ_[ℓ] (locF K ℓ) := inferInstance
  have hc' : ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (j σ) (c v) := hc
  have hg' : ∀ σ, resQ K (j σ) = g * decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) * g⁻¹ := hg
  have hd2 : A'.dim = 2 := hdim'.trans hdim
  exact ⟨locF K ℓ, inferInstance, inferInstance, i3, i4, A', j, c, g, hd2, hc', hg'⟩

/-- **G9 from base change of abelian varieties and the weight clause of R10.** -/
theorem g9Glue_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) (hW : G9Bridge.R10Weights) :
    G9Glue :=
  g9Glue_of_localModel (localModel_of_abVarBaseChange hBC) hW

end

end ZInQ.Contrib.G9


-- ===== ZInQKernel/Contrib/G9/Partial.lean

/-!
# G9 without the weight clause: what R10's Lean form gives alone

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`g9_partial`: from `G9Bridge.AbVarBaseChange` and R10 (`PkgI4.DeRhamComparison`) alone, i.e.
without `G9Bridge.R10Weights`, the data of `G9Glue` give: `r|G_{ℚ_ℓ}` is de Rham
(`LocalIsDeRham`), and over the same finite coefficient field its Hodge–Tate multiplicities at
`0` and at `−1` are `1`. What is missing for `HasHTWeightsAtSelf ℓ {0, −1}` is exactly the
vanishing of the multiplicities at the other weights (finding F1 of docs/research/g9-derham.md).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 G0Galois Module
open scoped TensorProduct

noncomputable section

section Mult

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]

/-- One Hodge–Tate multiplicity: `htMultOver ρ w = 2M ⇒ htMult ρE w = M`. -/
theorem core_htMult (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (w : ℤ) (M : ℕ) (hM : htMultOver p ρ w = 2 * M) : htMult p ρE w = M := by
  have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  obtain ⟨hc, hdvd⟩ := core_count p F (htAct p (-w)) (cpEmb p) (htAct_semi p (-w)) ρ ρE eE he
  rw [htMultOver, htSpaceOver_eq_DspRep] at hM
  rw [htMult, htSpace_eq_DspMat]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.mul_div_cancel_left _ hf] at hM
  rw [hk, hM] at hc
  have h1 : finrank ℚ_[p] F * (finrank ℚ_[p] E * (2 * M)) =
      finrank ℚ_[p] F * (2 * finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ)) := by
    calc finrank ℚ_[p] F * (finrank ℚ_[p] E * (2 * M))
        = finrank ℚ_[p] E * (finrank ℚ_[p] F * (2 * M)) := by ring
      _ = _ := hc
      _ = _ := by ring
  have h2 := Nat.eq_of_mul_eq_mul_left hf h1
  have h3 : finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ) =
      finrank ℚ_[p] E * M := by
    rw [mul_left_comm] at h2; omega
  rw [h3, Nat.mul_div_cancel_left _ hd]

end Mult

/-- **G9 from base change and R10 alone** (no weight clause): de Rham, and multiplicity `1` at
the weights `0` and `−1`. -/
theorem g9_partial (hBC : G9Bridge.AbVarBaseChange) (hR10 : PkgI4.DeRhamComparison)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hint : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    PkgI4.LocalIsDeRham ℓ 2 (r.restrictLocal ℓ) ∧
      ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
        (ρE : GQp ℓ →* GL (Fin 2) E),
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl ℓ)) (ρE σ) =
          r.restrictLocal ℓ σ) ∧
        htMult ℓ ρE 0 = 1 ∧ htMult ℓ ρE (-1) = 1 := by
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ :=
    localModel_of_abVarBaseChange hBC K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := fieldEmbBdR ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    E, hE, ρE, hmap, core_htMult ℓ F (A'.galRep ℓ) ρE eE he 0 1 (by rw [h0]),
    core_htMult ℓ F (A'.galRep ℓ) ρE eE he (-1) 1 (by rw [h1])⟩

end

end ZInQ.Contrib.G9


end G0A2_a95_g9

