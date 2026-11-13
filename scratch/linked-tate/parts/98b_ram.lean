/-! ## linked-tate: `LinkedRam` reduced to a field statement about `L'`, G3, and the prime `3`

For the canonical data, `ρ_ℓ(g) = β'(g)⁻¹ Tm(g)` is the Tate action on `G_{L'}` (`β' = 1` there,
`tmOf_resQ`). So clauses (i)-(ii) of `RhoRamWild` follow once the relevant local elements land in
`G_{L'}` (`KernelFieldBreaks`, a statement about the field `L'` alone) and act trivially through
the Tate module: away from `3` this is G3 (`QMModelG3`, already reduced), with local inertia
landing in a global inertia group (`LocalInertiaGlobal`, `UpperAbsInertia`, definitions only);
at `p = 3` (only for `ρ₅`) it is `TateRamAtThree`.

**Caveat (linked-tate finding).** g0-mod-field's `G7Data` does not record `[L:ℚ] ≤ D` (its `G4Out`
does). For `G7Data` with an oversized `L` (e.g. `L ⊇ ℚ(ζ_{2^k})` with `k > U₀ + 1`, allowed when
`M_{S_mul}(u)` is large), `KernelFieldBreaks` (i) fails: `G_{ℚ_2}^t ⊄ G_L ⊇ G_{L'}` for `U₀ < t <
k − 1`; `TateRamAtThree` is likewise only justified for small `K`. `linkedRam_of` is a valid
implication, but its premises are expected to hold only under `[L:ℚ] ≤ D`; `GluePieces3` therefore
keeps `LinkedRam` itself as the field. -/

section LinkedRamSec

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **The canonical operators are the Tate action on `G_{L'}`** (proved; the step `hTres` of
unram-tate's assembly, for any `(Θ, h)` with the `TatePoints` property and any `m` equal to the
Galois action on `G_L`). -/
theorem tmOf_resQ {L L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (hΘ : ∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x))
    (m : GQ → (PtQ L A →+ PtQ L A))
    (hmL : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup L') :
    tmOf hLL' A Θ h m ℓ (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) =
      GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hτ : h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹ ∈ GQL L' := by
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hτL : h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹ ∈ GQL L :=
    mem_GQL.mpr (fun x hx => mem_GQL.mp hτ x (hLL' hx))
  let σ' : Qbar ≃ₐ[L] Qbar :=
    AlgEquiv.ofRingEquiv (f := (act (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹)).toRingEquiv)
      (fun x => (mem_GQL.mp hτL) x x.2)
  have hm := hmL (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹) σ' (fun x => rfl)
  rw [tate_eq_opV]
  show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
    (conjE Θ (m (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹))) = _
  congr 1
  refine DFunLike.ext _ _ fun x => ?_
  show Θ (m (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹) (Θ.symm x)) = _
  rw [hm]
  show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
  rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]

/-- **Glue: the ramification of the kernel field `L'`** (linked-tate; the field half of N5
L819-852, D1 and D3). For every G7 data: for `p ≤ D`, every element of an absolute upper
ramification group `G_{ℚ_p}^t`, `t > U₀`, maps into `G_{L'}` (the upper breaks of `L'` at `p` are
`≤ U₀`); for `p > D`, wild inertia maps into `G_{L'}` (`L'` is tame at `p`: `[L:ℚ] ≤ D < p`, and
`L'/L` is cut out by `β|_{G_L}` with `β² = χ` of order prime to `p` at `p`). GLUE. -/
def KernelFieldBreaks : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∀ t : ℝ, G0ModNewform.U0 < t →
          ∀ σ ∈ LadicCond.upperAbs p t, PkgI4.decomp p σ ∈ GQL L') ∧
        ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
          PkgI4.decomp p σ ∈ GQL L')

/-- **Glue (definitions): local inertia lands in a global inertia group.** For `σ` in the
inertia set of `G_{ℚ_p}`, `decomp p σ` lies in the inertia group of the place `v` of `ℚ̄` induced
by the embedding `ℚ̄ → ℚ̄_p` that `decomp` uses (`v` lies over `p`). GLUE (Mathlib-level). -/
def LocalInertiaGlobal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : PkgI4.GQp p), σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p)) →
    ∃ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = PkgI4.decomp p σ

/-- **Glue (definitions): upper ramification groups of positive index lie in inertia.** For
`t > 0`, `upperAbs p t ⊆ inertiaSet` (`G^t(L) ⊆ G_0(L)` for each finite Galois `L/ℚ_p`, and every
integral `x ∈ ℚ̄_p` lies in such an `L`). GLUE (Mathlib-level). -/
def UpperAbsInertia : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (t : ℝ), 0 < t →
    LadicCond.upperAbs p t ⊆ (LadicCond.inertiaSet : Set (PkgI4.GQp p))

/-- **Glue: the Tate module of the QM model at `p = 3`** (linked-tate; N5 L819-852, D1-D2 at the
prime `3`, where the model may have bad reduction). For a `QML3` object `PK` over `K ≤ L ≤ L'`
(`L'/ℚ` finite Galois) and `t > U₀`, every `σ' ∈ G_{L'}` whose image is an element of
`G_{ℚ_3}^t` acts trivially on `ℚ̄₅ ⊗ V₅((PK.A)_{L,L'})` (QM surfaces have potentially good
reduction; the inertia image is finite, cut out by a field whose upper breaks at `3` are `≤ U₀`).
GLUE. -/
def TateRamAtThree : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L')
    (PK : LeafQM.AV.QML3 K),
    letI : NumberField L' := numberField_of_fd L'
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      ∀ σ' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ' = PkgI4.decomp 3 σ →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 5 σ' = 1

/-- G3 at a local inertia element (proved from `LocalInertiaGlobal`). -/
theorem tate_trivial_of_g3 (hLI : LocalInertiaGlobal) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (h : G0Galois.G3Out A ℓ {3}) (p : ℕ)
    [Fact p.Prime] (hp3 : p ≠ 3) (hpl : p ≠ ℓ) (σ : PkgI4.GQp p)
    (hσ : σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p))) (σ'' : Field.absoluteGaloisGroup K)
    (hσ'' : G0Galois.resQ K σ'' = PkgI4.decomp p σ) : G0Galois.tate A ℓ σ'' = 1 := by
  obtain ⟨v, hv, τ, hτ, hτeq⟩ := hLI p σ hσ
  exact h p Fact.out (by simpa using hp3) hpl v hv σ'' ⟨τ, hτ, hτeq.trans hσ''.symm⟩

/-- `0 ≤ U₀`. -/
theorem U0_nonneg : 0 ≤ G0ModNewform.U0 := by
  unfold G0ModNewform.U0; positivity

/-- `3 ≤ D`. -/
theorem three_le_heightD : (3 : ℝ) ≤ (ZInQ.heightD : ℝ) := by
  exact_mod_cast G0ModField.le_heightD_of_mem_S_mul
    (ZInQ.Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- **`LinkedRam`, proved** from `QMModelG3` (G3), `KernelFieldBreaks`, `LocalInertiaGlobal`,
`UpperAbsInertia` and `TateRamAtThree`. -/
theorem linkedRam_of (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThree) : LinkedRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 hmL h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 hgam1 j5 j3
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hK' := hK u P L A ε N χ β L' hLL' hD
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  -- on `G_{L'}`, `ρ` is the Tate action
  have hρ : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (g : PkgI4.GQ),
      g ∈ GQL L' →
      (∀ σ'' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ'' = g →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1) →
      GlueDescent.rho (tmOf hLL' _ Θ h m ℓ) (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) g
        = 1 := by
    intro ℓ _ j g hg ht
    obtain ⟨σ'', hσ''⟩ : g ∈ (@GaloisCopy.resQ L' _ hNF).range := by
      rw [resQRange L']; exact hg
    subst hσ''
    have hcj : h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹ ∈ GQL L' := hnorm.conj_mem _ hg h
    unfold GlueDescent.rho
    rw [tmOf_resQ hLL' _ Θ h hΘ m hmL ℓ σ'']
    have ht' : GaloisCopy.tate (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1 :=
      ht σ'' rfl
    have hγ : gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹) = 1 := hgam1 _ hcj
    rw [ht']
    show ((j (gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹)))⁻¹ * j 1) • (1 : Module.End _ _) = 1
    rw [hγ, map_one, inv_one, _root_.one_mul, one_smul]
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hG5 := hG3 K L L' hKL hLL' PK 5
  have hG3' := hG3 K L L' hKL hLL' PK 3
  refine ⟨fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩,
    fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩⟩
  · -- `ρ₅`, `p ≠ 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    refine hρ 5 j5 _ ((hK' p hp).1 hpD t ht σ hσ) (fun σ'' hσ'' => ?_)
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 K L L' hKL hLL' PK t ht σ hσ σ'' hσ''
    · exact tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ''
  · -- `ρ₅`, `p ≠ 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by
      intro h3'
      subst h3'
      have := three_le_heightD
      push_cast at hpD
      linarith
    exact hρ 5 j5 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).1 hpD t ht σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')

end UnramTate

end

end LinkedRamSec

#print axioms UnramTate.tmOf_resQ
#print axioms UnramTate.tate_trivial_of_g3
#print axioms UnramTate.linkedRam_of
