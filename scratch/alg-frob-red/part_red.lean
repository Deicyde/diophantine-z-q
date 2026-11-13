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
#print axioms AlgFrobRedRed.algFrobRed_of_fine
#print axioms AlgFrobRedRed.tateBridge35_of_fine
#print axioms AlgFrobRedRed.algFrobRed_of_finest
#print axioms AlgFrobRedRed.algFrobRed_of_final
#print axioms AlgFrobRedRed.tateBridge35_of_final
#print axioms AlgFrobRedRed.algFrobRed_of_main
#print axioms AlgFrobRedRed.tateBridge35_of_main
