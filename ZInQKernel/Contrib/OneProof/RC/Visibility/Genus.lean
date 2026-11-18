import ZInQKernel.Contrib.OneProof.RC.Visibility.Kummer
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusTheoryReduction
import ZInQKernel.Contrib.OneProof.RC.Height.Torsion
import ZInQKernel.Contrib.OneProof.RC.Height.BaseZeroCST
import ZInQKernel.Contrib.CloudB3RC53.Assembly
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-!
# Lane RC23: the native-index bound and the torsion clause of (O.8) over the genuine genus points

Manuscript (11/5), Appendix F, Proposition `ex:app-visibility` (tex 9407–9445), proof:

"For a known simple-zero `D`, write `P_D = m_D G + T` in its native rank-one free lattice. The same
`L` kills `T`. An integral finite-field Kummer map cannot decrease `v₂(m_D)`, so (O.7) gives the lower
bound by the native index. […] If an odd-sign `D` is not a simple zero, the height formula gives a
torsion genus point, killed by `L`, and its coefficient is zero modulo `2^M`." (tex 9422–9441)

The objects are batch 3's genuine ones (`GenusOdd`):
* a **genus datum** for `D` is a `HeegnerDatum E f Lat κ (D h_*) 1 h_*`: the imaginary quadratic field
  `K_D = ℚ(√(D h_*))`, the genus character `χ_{h_*} ∘ N` on `Pic(𝒪_{K_D})`, a Heegner form and a point
  `y ∈ E(H₁)` over the Hilbert class field whose image under an embedding is the CM value `φ(τ)` of the
  modular parametrization (the analytic model of Cai–Shu–Tian's Heegner point);
* the **genus point** `P_D` of (O.1) (tex 8213–8217) is its unaveraged sum `heegnerSum`;
* the **native lattice** is the `χ`-eigen subgroup `eigenLattice` of `E(H₁)` (tex 2414, 9422);
* **`j_gen(D)`** is the index valuation of `P_D` there (`HeegnerDatum.index`), read off a selection of
  data by batch 3's `jgenOf` (tex 2411–2416).

The **stage maps** (`StageKummer`): at each stage `θ`, for each genus datum, the additive map
`E(H₁) → ℤ/2^{M_θ}`, `x ↦ λ_{M_θ}(\bar x)`: reduction at the place above `ℓ₀` chosen in (O.2)
(`ℓ₀` is inert in `K_D` because `(D h_*/ℓ₀) = −1`, tex 9206–9209, so it splits completely in `H₁/K_D`
and the residue field is `𝔽_{ℓ₀²}`, tex 9288–9290) followed by `λ_{M_θ} = b ∘ κ_{M_θ}` (tex 8378–8398,
8439–8456). Reduction of points of elliptic curves modulo primes of number fields is not in Mathlib,
so this composite is an interface: an arbitrary additive map. The theorems below use only its
additivity; (O.7) is where it is tied to the supersingular side (`Visibility/Models.lean`:
`lamOf_reduction`, the pointwise Cornut–Jetchev identity).

`λ_θ(D)` (`lamOf`) is the integer lift `val(λ_{M_θ}(\overline{L P_D}))` (tex 2512–2530, 9112–9113).

Results:
* `lamOf_native_bound` — **PROVED** (from `kummer_native_bound` and the GLUE
  `MultiplierKillsNativeTorsion`): `2^k ∣ λ_θ(D)` for every `k ≤ min(M_θ, j_gen(D))`; constant `0`.
* `genusPoint_isOfFinAddOrder` — **PROVED** from PRINT Cai–Shu–Tian Thm 1.1 (`Prints.cst`), batch 3's
  GLUE `ArtinFactorization` (the only GLUE used; the splitting criterion is batch 3's
  `splittingCriterion_proof`, PROVED) and the odd sign: an admissible `D` of odd sign that is not a
  simple zero has a torsion genus point.
* `lamOf_torsion` — **PROVED**: then `2^{M_θ} ∣ λ_θ(D)`.
* `genusPoint_index_ne_top` — **PROVED** from the same prints and lane RC19's heights
  (`ĥ = 0 ⇔ torsion` over number fields) with Northcott: at a known simple zero the genus point is
  nontorsion and `j_gen(D)` is finite (so the native bound is about the genuine index, not a junk value).

Remark (the index at most two of tex 9426–9428). Elliot also absorbs into `C_det` the index (at most two)
of the rational free line in the native lattice. Here the Kummer evaluation is applied in the native
lattice itself (to `L P_D = 2^j L G`), so that comparison is not needed and the constant is `0`; were
`λ_θ` read on the rational line `E^{(D)}(ℚ)`, batch 3's `datum_facts_core` (`j ≤ j(Q) ≤ j + 1`) would
give the bound with constant `1`.

Technical note: every statement about a datum `dat` names its field instances as `dat.field`, `dat.nf`
and its `NeZero 1` instance as `dat.nz` (exactly as batch 3's `HeegnerDatum.index` does), so that all
instance terms agree syntactically with batch 3's.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Manuscript.RC.Visibility

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd ZInQ.Contrib.CloudB3RC53.CST

/-- **PROVED.** The index valuation is monotone in the lattice. -/
theorem twoDivIndex_mono {A : Type*} [AddCommGroup A] {M M' : AddSubgroup A} (h : M ≤ M') (x : A) :
    twoDivIndex M x ≤ twoDivIndex M' x :=
  iSup_mono fun _ => iSup_le fun ⟨G, hG, hT⟩ => le_iSup_of_le ⟨G, h hG, hT⟩ le_rfl

/-! ## Field level: a fixed imaginary quadratic field `K` and conductor `c` -/

section FieldLevel

variable (E : WeierstrassCurve ℚ) {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

/-- `L` kills the torsion of the native lattice `E(H_c)^χ` (field-level form of
`MultiplierKillsNativeTorsion`). -/
def NativeTorsionKilledAt (χ : Pic (conductorOrder K c) →* ℂˣ) (L : ℕ) : Prop :=
  letI := Classical.decEq (ringClassField (conductorOrder K c))
  ∀ t ∈ eigenLattice E χ, IsOfFinAddOrder t → L • t = 0

/-- The integer lift `val(κ(L P_χ))` of a Kummer evaluation `κ : E(H_c) → ℤ/2^M` at `L` times the
unaveraged Heegner sum `P_χ` (field-level form of `lamOf`). -/
def kummerLift (M L : ℕ) (χ : Pic (conductorOrder K c) →* ℂˣ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (ev : letI := Classical.decEq (ringClassField (conductorOrder K c))
      (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+ ZMod (2 ^ M)) : ℤ :=
  letI := Classical.decEq (ringClassField (conductorOrder K c))
  ((ev (L • heegnerSum E χ y)).val : ℤ)

/-- **PROVED (tex 9422–9428), field level.** `2^k ∣ val(κ(L P_χ))` for `k ≤ min(M, j(P_χ))`. -/
theorem kummerLift_native_bound {M L : ℕ} (χ : Pic (conductorOrder K c) →* ℂˣ)
    (hχ : ∀ t, χ t * χ t = 1)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (ev : letI := Classical.decEq (ringClassField (conductorOrder K c))
      (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+ ZMod (2 ^ M))
    (hL : NativeTorsionKilledAt E χ L) {k : ℕ} (hkM : k ≤ M)
    (hkj : (k : ℤ) ≤ ((nativeIndex E χ y).toNat : ℤ)) :
    (2 : ℤ) ^ k ∣ kummerLift E M L χ y ev := by
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  exact native_bound_toNat (heegnerSum_mem_eigenLattice E hχ y) hL ev hkM hkj

/-- **PROVED.** If `L` kills the torsion of the native lattice and `P_χ` is torsion, the Kummer lift
is `0`. -/
theorem kummerLift_eq_zero_of_torsion {M L : ℕ} (χ : Pic (conductorOrder K c) →* ℂˣ)
    (hχ : ∀ t, χ t * χ t = 1)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (ev : letI := Classical.decEq (ringClassField (conductorOrder K c))
      (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point →+ ZMod (2 ^ M))
    (hL : NativeTorsionKilledAt E χ L)
    (htor : letI := Classical.decEq (ringClassField (conductorOrder K c))
      IsOfFinAddOrder (heegnerSum E χ y)) :
    kummerLift E M L χ y ev = 0 := by
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  have h0 : L • heegnerSum E χ y = 0 := hL _ (heegnerSum_mem_eigenLattice E hχ y) htor
  unfold kummerLift
  rw [h0, map_zero, ZMod.val_zero, Nat.cast_zero]

end FieldLevel

/-! ## Data level: the selected genus data -/

section Objects

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

/-- **The genus point `P_D`** of (O.1) (tex 8213–8217, 2411–2412): the unaveraged sum
`∑_{[𝔞] ∈ Pic(𝒪_{K_D})} χ_{h_*}(N𝔞) π(x_D^{[𝔞]})` in `E(H₁)` — batch 3's `heegnerSum` of the genus
datum. -/
def genusPoint {Dd : ℤ} (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) :
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    (E.baseChange (ringClassField (conductorOrder dat.K 1))).toAffine.Point :=
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
  heegnerSum E dat.χ dat.y

/-- **GLUE (tex 8274–8294, 9423: "the same `L` kills `T`").** `L` is a positive integer killing every
torsion point of every native lattice. Elliot's argument: a torsion point `T` of the `χ`-eigen subgroup
of `E(H₁)` is fixed by `ker χ`, hence lies in `E(F_D)` for the genus field `F_D = ℚ(√D, √h_*)` of degree
four (tex 8261–8263); the fixed multiplier `B = B₁B₂`, `B_j = ∏_{f ≤ 4} #E(𝔽_{p_j^f})` at two good primes,
kills the torsion of `E` over every number field of degree at most four (prime-to-`p_j` torsion injects
into the reduction, Silverman AEC VII.3.1 — locator UNVERIFIED), and `L` is a multiple of `4 B B_cusp`
(tex 8295–8297). -/
def MultiplierKillsNativeTorsion (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (hstar : ℤ) (L : ℕ) : Prop :=
  0 < L ∧ ∀ (Dd : ℤ) (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar),
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    NativeTorsionKilledAt E dat.χ L

/-- **The stage maps** (interface; tex 8378–8398, 8439–8456, 8476, 9283–9290): at stage `θ`, for every
genus datum, the additive map `x ↦ λ_{M_θ}(\bar x)` from `E(H₁)` to `ℤ/2^{M_θ}` (reduction at the chosen
place above `ℓ₀`, residue field `𝔽_{ℓ₀²}`, followed by `λ_{M_θ} = b ∘ κ_{M_θ}`). -/
abbrev StageKummer (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (hstar : ℤ) (Mθ : ℕ → ℕ) : Type 1 :=
  (θ : ℕ) → (Dd : ℤ) → (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) →
    (letI := dat.field
     letI := dat.nf
     letI := dat.nz
     letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
     (E.baseChange (ringClassField (conductorOrder dat.K 1))).toAffine.Point →+ ZMod (2 ^ Mθ θ))

/-- **`λ_θ(D)`** (tex 2512–2530, 9112–9113): the integer lift `val(λ_{M_θ}(\overline{L P_D}))` of the
stage map applied to `L P_D`, for the selected genus datum of `D` (`0` where none is selected). -/
def lamOf (Mθ : ℕ → ℕ) (L : ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar Mθ) (θ : ℕ) (Dd : ℤ) : ℤ :=
  match selG Dd with
  | some dat =>
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    kummerLift E (Mθ θ) L dat.χ dat.y (ev θ Dd dat)
  | none => 0

/-- **PROVED (tex 9422–9428): the native-index bound.** For every stage `θ` and every `D`, every
`k ≤ min(M_θ, j_gen(D))` gives `2^k ∣ λ_θ(D)`, with `j_gen = jgenOf` (batch 3) and constant `0`. -/
theorem lamOf_native_bound (Mθ : ℕ → ℕ) {L : ℕ}
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar Mθ)
    (hL : MultiplierKillsNativeTorsion E f Lat κ hstar L) (θ : ℕ) (Dd : ℤ)
    (k : ℕ) (hkM : k ≤ Mθ θ) (hkj : (k : ℤ) ≤ jgenOf E f Lat κ hstar selG Dd) :
    (2 : ℤ) ^ k ∣ lamOf Mθ L selG ev θ Dd := by
  unfold lamOf
  unfold jgenOf at hkj
  cases hsel : selG Dd with
  | none => exact dvd_zero _
  | some dat =>
    rw [hsel] at hkj
    exact (letI := dat.field; letI := dat.nf; letI := dat.nz
      kummerLift_native_bound E dat.χ dat.quad.1 dat.y (ev θ Dd dat) (hL.2 Dd dat) hkM hkj)

end Objects

/-! ## The height formula at a genus datum (Cai–Shu–Tian) -/

section CST

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ}

open Classical in
/-- **PROVED from PRINT + GLUE (tex 8268–8272, 9439–9440): the unaveraged height formula at a genus
datum.** For a genus datum of `D` (field `K` of discriminant `D h_*`, conductor `c = 1`, character
`χ = χ_{h_*} ∘ N`) and entire continuations `F_{h_*}`, `F_D` of `L(E^{(h_*)}, s)`, `L(E^{(D)}, s)`:
`(F_{h_*} F_D)'(1) = C / (c √|disc K|) · [H₁ : K]⁻¹ ĥ_{H₁}(P_D)`. Inputs: Cai–Shu–Tian Thm 1.1 in the
form `CSTFormula E f Lat κ C` (from `Prints.cst`, PRINT: Algebra & Number Theory 8 (2014), Theorem 1.1;
UNVERIFIED in the shared layer), batch 3's GLUE `ArtinFactorization`
(`L(E/K, χ_{h_*} ∘ N, s) = L(E^{(h_*)}, s) L(E^{(D)}, s)`), batch 3's PROVED splitting criterion (every
prime of `N` splits in `K` because `D h_*` is a unit square there) and `heightK_eq_canonicalHeight`. The
hypotheses `hgp`, `hprep` give: `D h_*` odd, `≠ −3, −4`, a square at the primes of `N`, prime to `N`. -/
theorem genus_cst_height (hArtin : ArtinFactorization) {C : ℝ} (hC : CSTFormula E f Lat κ C)
    {hstar Dd : ℤ} (hgp : GenusPartner E hstar) (hprep : Prepared E hstar Dd)
    (K : Type) [Field K] [NumberField K] {c : ℕ} [NeZero c] (hc : c = 1)
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hdisc : discr K = Dd * hstar)
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hquad : IsQuadRingClassChar K c hstar χ)
    (hprim : IsPrimitiveRingClassChar K c χ) (A B C' : ℤ)
    (hform : IsHeegnerForm (newformLevel E) (Dd * hstar * c ^ 2) A B C')
    (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (Dd * hstar * c ^ 2)))
    {Fs FD : ℂ → ℂ} (hFs : IsLContinuation (qtwist E hstar) Fs)
    (hFD : IsLContinuation (qtwist E Dd) FD) :
    deriv (fun s => Fs s * FD s) 1 =
      ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) *
        ((((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ)⁻¹ *
          (letI := Classical.decEq (ringClassField (conductorOrder K c))
           (heegnerSum E χ y).canonicalHeight) : ℝ)) : ℂ) := by
  subst hc
  obtain ⟨h0, -, hsqp, -⟩ := hprep
  obtain ⟨hs0, hs4, hssq, hs5, hsp, -⟩ := hgp
  have hN2 : ∀ p : ℕ, p ∣ newformLevel E → p ∣ 2 * newformLevel E :=
    fun p hp => dvd_mul_of_dvd_right hp 2
  have h2h : SquareAt 2 Dd := hsqp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h8 : Dd % 8 = 1 := h2h.2.1 rfl
  have hDg4 : 4 < |Dd * hstar| := by
    rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg hstar]
  have hDodd : Odd (discr K) := by
    rw [hdisc]
    exact Int.odd_iff.mpr (by
      rw [Int.mul_emod, show Dd % 2 = 1 by omega, show hstar % 2 = 1 by omega]; norm_num)
  have hD3 : discr K ≠ -3 := by
    rw [hdisc]; intro hD; rw [hD] at hDg4; norm_num at hDg4
  have hD4 : discr K ≠ -4 := by
    rw [hdisc]; intro hD; rw [hD] at hDg4; norm_num at hDg4
  have hsqDN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p (discr K) := fun p hp hpN => by
    rw [hdisc]; exact (hsqp p hp (hN2 p hpN)).mul (hsp p hp (hN2 p hpN)) hp
  have hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p := fun p hp hpN =>
    Splitting.splittingCriterion_proof K hK2 p hp (hsqDN p hp hpN)
  have hcopN : Nat.Coprime (hstar * Dd).natAbs (newformLevel E) :=
    coprime_of_squareAt fun p hp hpN => (hsp p hp (hN2 p hpN)).mul (hsqp p hp (hN2 p hpN)) hp
  have hform' : IsHeegnerForm (newformLevel E) (discr K * 1 ^ 2) A B C' := by
    rw [hdisc]; exact hform
  have hy' : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint A B (discr K * 1 ^ 2)) := by
    rw [hdisc]; exact hy
  have hCST := hC K hK2 hTC hD3 hD4 hsplit 1 (Nat.coprime_one_left _) χ hprim A B C' hform' ι y hy'
    (fun s => Fs s * FD s) (hFs.1.mul hFD.1) (fun s hs => by
      rw [hFs.2 s hs, hFD.2 s hs]
      exact (hArtin E K hK2 hTC hDodd hsplit 1 hstar Dd (by rw [hdisc]; ring) hs4 hssq
        (by simp) (Nat.coprime_one_left _) hcopN χ hquad s hs).symm)
  rw [heightK_eq_canonicalHeight E hquad.1 y] at hCST
  exact hCST

open Classical in
/-- **PROVED from PRINT + GLUE (tex 9439–9441): "if an odd-sign `D` is not a simple zero, the height
formula gives a torsion genus point".** At a genus datum of `D` with root number `w(E^{(D)}) = −1`
and `ord_{s=1} L(E^{(D)}, s) ≠ 1`: the entire continuation `F_D` vanishes at `1` (sign `−1`), to order
`≥ 2`, so `(F_{h_*} F_D)'(1) = 0`; the height formula then gives `ĥ_{H₁}(P_D) = 0`, so `P_D` is torsion
(lane RC19: `ĥ = 0 ⇔ torsion` over a number field). -/
theorem genus_torsion (hArtin : ArtinFactorization) {C : ℝ} (hC0 : 0 < C) (hC : CSTFormula E f Lat κ C)
    {hstar Dd : ℤ} (hgp : GenusPartner E hstar) (hprep : Prepared E hstar Dd)
    (hsign : RootNumber (qtwist E Dd) (-1)) (hnot : ¬ AnalyticRank (qtwist E Dd) 1)
    (K : Type) [Field K] [NumberField K] {c : ℕ} [NeZero c] (hc : c = 1)
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hdisc : discr K = Dd * hstar)
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hquad : IsQuadRingClassChar K c hstar χ)
    (hprim : IsPrimitiveRingClassChar K c χ) (A B C' : ℤ)
    (hform : IsHeegnerForm (newformLevel E) (Dd * hstar * c ^ 2) A B C')
    (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (Dd * hstar * c ^ 2))) :
    letI := Classical.decEq (ringClassField (conductorOrder K c))
    IsOfFinAddOrder (heegnerSum E χ y) := by
  -- the odd sign: `F_D(1) = 0`
  obtain ⟨N, hN, FD, hFD, hFE⟩ := hsign
  have hF1 : FD 1 = 0 := centralValueZeroNode_proof (qtwist E Dd) N hN FD (by simpa using hFE)
  -- not a simple zero: order at least two
  have hord : 2 ≤ analyticOrderAt FD 1 := by
    have hne0 : analyticOrderAt FD 1 ≠ 0 := by
      rw [ne_eq, (hFD.1.analyticAt 1).analyticOrderAt_eq_zero]
      exact not_not.mpr hF1
    have hne1 : analyticOrderAt FD 1 ≠ 1 := fun h => hnot ⟨FD, hFD.1, hFD.2, by exact_mod_cast h⟩
    generalize analyticOrderAt FD 1 = n at hne0 hne1 ⊢
    induction n using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      have h0 : n ≠ 0 := by exact_mod_cast hne0
      have h1 : n ≠ 1 := by exact_mod_cast hne1
      exact_mod_cast (show 2 ≤ n by omega)
  have hFD' : deriv FD 1 = 0 :=
    ZInQ.Manuscript.RC.Height.deriv_eq_zero_of_two_le_analyticOrderAt hFD.1 hord
  -- `L(E^{(h_*)}, s)` has an entire continuation
  obtain ⟨Fs, hFs, -⟩ := analyticRank_zero_iff.mp hgp.2.2.2.2.2
  have hder := genus_cst_height hArtin hC hgp hprep K hc hK2 hTC hdisc χ hquad hprim A B C' hform ι y hy
    hFs hFD
  have hd0 : deriv (fun s => Fs s * FD s) 1 = 0 := by
    rw [show (fun s => Fs s * FD s) = Fs * FD from rfl, deriv_mul (hFs.1 1) (hFD.1 1), hF1, hFD']
    ring
  rw [hd0] at hder
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  -- the scalar factors are nonzero
  have hD0 : (discr K : ℝ) ≠ 0 := by
    rw [hdisc]
    obtain ⟨h0, -, -, -⟩ := hprep
    have : Dd * hstar ≠ 0 := mul_ne_zero h0.ne' hgp.1.ne
    exact_mod_cast this
  have hcR : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hsq : 0 < Real.sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr hD0)
  have hfac : ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) := div_pos hC0 (mul_pos hcR hsq)
    exact_mod_cast this.ne'
  have hfin : (0 : ℝ) < (Module.finrank K (ringClassField (conductorOrder K c)) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hprod := (mul_eq_zero.mp hder.symm).resolve_left hfac
  have hh : (heegnerSum E χ y).canonicalHeight = 0 := by
    have : ((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ)⁻¹ *
        (heegnerSum E χ y).canonicalHeight : ℝ) = 0 := by exact_mod_cast hprod
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (inv_ne_zero hfin.ne')
    · exact h
  exact ZInQ.Manuscript.RC.Height.isOfFinAddOrder_of_canonicalHeight_eq_zero' _ hh

open Classical in
/-- **PROVED from PRINT + GLUE (tex 8268–8272, 9422): at a known simple zero the genus point is
nontorsion and its native index is finite.** With `ord_{s=1} L(E^{(D)}, s) = 1` and
`L(E^{(h_*)}, 1) ≠ 0`, `(F_{h_*} F_D)'(1) = F_{h_*}(1) F_D'(1) ≠ 0`, so the height formula gives
`ĥ_{H₁}(P_D) > 0`; then `P_D` is nontorsion and (Northcott, `ĥ(nP) = n² ĥ(P)`; batch 3's
`twoDivIndex_ne_top`) its index valuation in `E(H₁)`, hence in the native lattice, is finite. -/
theorem genus_nontorsion (hArtin : ArtinFactorization) {C : ℝ} (hC : CSTFormula E f Lat κ C)
    {hstar Dd : ℤ} (hgp : GenusPartner E hstar) (hprep : Prepared E hstar Dd)
    (hz : AnalyticRank (qtwist E Dd) 1)
    (K : Type) [Field K] [NumberField K] {c : ℕ} [NeZero c] (hc : c = 1)
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hdisc : discr K = Dd * hstar)
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hquad : IsQuadRingClassChar K c hstar χ)
    (hprim : IsPrimitiveRingClassChar K c χ) (A B C' : ℤ)
    (hform : IsHeegnerForm (newformLevel E) (Dd * hstar * c ^ 2) A B C')
    (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (Dd * hstar * c ^ 2))) :
    (letI := Classical.decEq (ringClassField (conductorOrder K c))
     ¬ IsOfFinAddOrder (heegnerSum E χ y)) ∧ nativeIndex E χ y ≠ ⊤ := by
  obtain ⟨FD, hFD, hF1, hFD'⟩ := analyticRank_one hz
  obtain ⟨Fs, hFs, hFs1⟩ := analyticRank_zero_iff.mp hgp.2.2.2.2.2
  have hder := genus_cst_height hArtin hC hgp hprep K hc hK2 hTC hdisc χ hquad hprim A B C' hform ι y hy
    hFs hFD
  have hd : deriv (fun s => Fs s * FD s) 1 = Fs 1 * deriv FD 1 := by
    rw [show (fun s => Fs s * FD s) = Fs * FD from rfl, deriv_mul (hFs.1 1) (hFD.1 1), hF1]
    ring
  rw [hd] at hder
  let _ := Classical.decEq (ringClassField (conductorOrder K c))
  have hh : (heegnerSum E χ y).canonicalHeight ≠ 0 := by
    intro h0
    rw [h0, mul_zero, Complex.ofReal_zero, mul_zero] at hder
    exact mul_ne_zero hFs1 hFD' hder
  have hpos : 0 < (heegnerSum E χ y).canonicalHeight :=
    lt_of_le_of_ne (WeierstrassCurve.Affine.Point.canonicalHeight_nonneg _) (Ne.symm hh)
  refine ⟨ZInQ.Manuscript.RC.Height.not_isOfFinAddOrder_of_canonicalHeight_ne_zero _ hh, ?_⟩
  have htop : twoDivIndex ⊤ (heegnerSum E χ y) ≠ ⊤ :=
    twoDivIndex_ne_top (fun n x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul n x)
      (fun B => Northcott.finite_le (h := WeierstrassCurve.Affine.Point.canonicalHeight) B) hpos
  exact ne_top_of_le_ne_top htop (twoDivIndex_mono le_top _)

end CST

/-! ## The torsion clause and the finiteness of `j_gen` over the selected data -/

section Clauses

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

/-- **PROVED from PRINT + GLUE (tex 9439–9441).** The genus point of a genus datum of an odd-sign
`D` in the prepared filter that is not a simple zero is torsion. Inputs: `Prints` (Cai–Shu–Tian),
batch 3's GLUE `ArtinFactorization`. -/
theorem genusPoint_isOfFinAddOrder (P : Prints) (hArtin : ArtinFactorization)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (hκ : IsParamScale (newformLevel E) f Lat κ) (hgp : GenusPartner E hstar) {Dd : ℤ}
    (hprep : Prepared E hstar Dd) (hsign : RootNumber (qtwist E Dd) (-1))
    (hnot : ¬ AnalyticRank (qtwist E Dd) 1)
    (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) :
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
    IsOfFinAddOrder (heegnerSum E dat.χ dat.y) := by
  obtain ⟨C, hC0, hC⟩ := cst_formula P E f hf Lat hLat hNC κ hκ
  exact (letI := dat.field; letI := dat.nf; letI := dat.nz
    genus_torsion hArtin hC0 hC hgp hprep hsign hnot dat.K rfl dat.finrank_two dat.totallyComplex
      dat.disc dat.χ dat.quad dat.prim dat.A dat.B dat.C dat.form dat.ι dat.y dat.hy)

/-- **PROVED from PRINT + GLUE (tex 8268–8272, 9422).** At a known simple zero `D` of the prepared
filter, the genus point of a genus datum is nontorsion and its native index `j_gen(D)` is finite. -/
theorem genusPoint_index_ne_top (P : Prints) (hArtin : ArtinFactorization)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (hκ : IsParamScale (newformLevel E) f Lat κ) (hgp : GenusPartner E hstar) {Dd : ℤ}
    (hprep : Prepared E hstar Dd) (hz : AnalyticRank (qtwist E Dd) 1)
    (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) :
    (letI := dat.field
     letI := dat.nf
     letI := dat.nz
     letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
     ¬ IsOfFinAddOrder (heegnerSum E dat.χ dat.y)) ∧ dat.index ≠ ⊤ := by
  obtain ⟨C, -, hC⟩ := cst_formula P E f hf Lat hLat hNC κ hκ
  exact (letI := dat.field; letI := dat.nf; letI := dat.nz
    genus_nontorsion hArtin hC hgp hprep hz dat.K rfl dat.finrank_two dat.totallyComplex
      dat.disc dat.χ dat.quad dat.prim dat.A dat.B dat.C dat.form dat.ι dat.y dat.hy)

/-- **PROVED (tex 9439–9444): the torsion clause.** For `D` in the prepared filter with odd sign that
is not a simple zero, `2^{M_θ} ∣ λ_θ(D)` at every stage. -/
theorem lamOf_torsion (P : Prints) (hArtin : ArtinFactorization)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (hκ : IsParamScale (newformLevel E) f Lat κ) (hgp : GenusPartner E hstar)
    (Mθ : ℕ → ℕ) {L : ℕ}
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (ev : StageKummer E f Lat κ hstar Mθ)
    (hL : MultiplierKillsNativeTorsion E f Lat κ hstar L) {Dd : ℤ}
    (hprep : Prepared E hstar Dd) (hsign : RootNumber (qtwist E Dd) (-1))
    (hnot : ¬ AnalyticRank (qtwist E Dd) 1) (θ : ℕ) :
    (2 : ℤ) ^ Mθ θ ∣ lamOf Mθ L selG ev θ Dd := by
  unfold lamOf
  cases hsel : selG Dd with
  | none => exact dvd_zero _
  | some dat =>
    have h0 := (letI := dat.field; letI := dat.nf; letI := dat.nz
      kummerLift_eq_zero_of_torsion E dat.χ dat.quad.1 dat.y (ev θ Dd dat) (hL.2 Dd dat)
        (genusPoint_isOfFinAddOrder P hArtin hf hLat hNC hκ hgp hprep hsign hnot dat))
    dsimp only
    rw [h0]
    exact dvd_zero _

/-- **PROVED.** At a known simple zero of the prepared filter with a selected genus datum,
`j_gen(D) = jgenOf …` is the genuine native index, which is finite. -/
theorem jgenOf_eq_index (P : Prints) (hArtin : ArtinFactorization)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    (hκ : IsParamScale (newformLevel E) f Lat κ) (hgp : GenusPartner E hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar)) {Dd : ℤ}
    (hprep : Prepared E hstar Dd) (hz : AnalyticRank (qtwist E Dd) 1)
    (dat : HeegnerDatum E f Lat κ (Dd * hstar) 1 hstar) (hsel : selG Dd = some dat) :
    ∃ j : ℕ, dat.index = (j : ℕ∞) ∧ jgenOf E f Lat κ hstar selG Dd = (j : ℤ) := by
  have hfin := (genusPoint_index_ne_top P hArtin hf hLat hNC hκ hgp hprep hz dat).2
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨j, hj.symm, ?_⟩
  unfold jgenOf
  rw [hsel]
  simp only
  rw [← hj, ENat.toNat_natCast]

end Clauses

end ZInQ.Manuscript.RC.Visibility
