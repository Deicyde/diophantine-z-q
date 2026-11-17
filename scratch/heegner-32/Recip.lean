import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd.Twist
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8

/-!
# heegner-32: `TwistTransportCd` from `hCM` and the lattice combinatorics at conductor `d`

`TwistTransportCd` (the Galois statement on `X₀(32)` used for the even-`c` Heegner point of `C_d`) follows from
the printed main theorem of CM (`T5Glue.ShimuraMainCM`, `hCM`), x0-32's eta route at level 32 (hx-used's
`X0EtaRoute.x_conj`, `y_conj`, with theta-wp8's `ThetaWP8.thetaWeierstrass8`, all proved) and one purely
algebraic statement, `TwistLatticeCd` (GLUE): the idele `s` of `σ` maps the conductor-`d` neighbours
`τ_Q + a/d` of each Heegner point `τ_Q` of level `32 d²` to the neighbours `τ_{πQ} + ν(a)/d` of another one, with
`(ν(a)/d) = (σ(g)/g)·(a/d)`.
-/

noncomputable section

open UpperHalfPlane Complex WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace ZInQ.Heegner32

open ZInQ.GZWeil (gaussD)
open ZInQ.GZDecomp (HeegnerHyp)
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm ιC)
open ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura
  ZInQ.Contrib.TYZDecomp.CurveA NumberField

/-! ## §1. The points `(x, y)(τ)` -/

theorem phiC_nonsingular (τ : ℍ) :
    ZInQ.Contrib.TYZGenus.X0.curveAC.toAffine.Nonsingular
      (ZInQ.Contrib.TYZGenus.X0.xC τ) (ZInQ.Contrib.TYZGenus.X0.yC τ) := by
  have he := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  have hΔ : ZInQ.Contrib.TYZGenus.X0.curveAC.Δ ≠ 0 := by
    simp [ZInQ.Contrib.TYZGenus.X0.curveAC, curveA, shortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
      WeierstrassCurve.baseChange, WeierstrassCurve.map]
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
  simp only [ZInQ.Contrib.TYZGenus.X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, map_zero, map_ofNat, zero_mul, add_zero, mul_zero]
  linear_combination he

/-- `σ` moves `(x, y)(τ)` to `(x, y)(τ')` if it moves both coordinates. -/
theorem map_phiC {σ : ℂ ≃+* ℂ} {τ τ' : ℍ}
    (hx : σ (ZInQ.Contrib.TYZGenus.X0.xC τ) = ZInQ.Contrib.TYZGenus.X0.xC τ')
    (hy : σ (ZInQ.Contrib.TYZGenus.X0.yC τ) = ZInQ.Contrib.TYZGenus.X0.yC τ') :
    Affine.Point.map (ZInQ.GZHeegner.sigA σ) (ZInQ.Contrib.TYZGenus.X0.phiC τ) =
      ZInQ.Contrib.TYZGenus.X0.phiC τ' := by
  unfold ZInQ.Contrib.TYZGenus.X0.phiC
  rw [dif_pos (phiC_nonsingular τ), dif_pos (phiC_nonsingular τ'), Affine.Point.map_some]
  simp only [Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

/-- `(x, y)` is `Γ₀(32)`-invariant. -/
theorem phiC_gamma0 {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma0 32)
    (τ : ℍ) : ZInQ.Contrib.TYZGenus.X0.phiC (γ • τ) = ZInQ.Contrib.TYZGenus.X0.phiC τ := by
  obtain ⟨hx, hy⟩ := ZInQ.Contrib.TYZGenus.Shimura.etaModelInvariant γ hγ τ
  unfold ZInQ.Contrib.TYZGenus.X0.phiC
  rw [dif_pos (phiC_nonsingular (γ • τ)), dif_pos (phiC_nonsingular τ)]
  simp only [Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

/-! ## §2. The lattice statement -/

/-- **(GLUE: Heegner-point combinatorics at conductor `d` and the genus character of `K(√d)/K`.)**
Setting of `TwistTransportCd`, with a normalized embedding `e : Kˢ → ℚ̄` and an idele `s` with `σ = [s, K]`
(`T5Glue.ArtinCond`). There is a permutation `π` of `S` and, for each `Q ∈ S`, a bijection `ν` of `ℤ/d` with
`(ν(a)/d) = ε_σ (a/d)`, `ε_σ = σ(g)/g` (`g = gaussD d`), such that for every `a` prime to `d` there are Heegner forms
`Q₁, Q₂` of level `32` and discriminant `−m d²` (`discOf m d`) with `s⁻¹(⟨1, τ_{Q₁}⟩, ⟨1/32, τ_{Q₁}⟩) =
c (⟨1, τ_{Q₂}⟩, ⟨1/32, τ_{Q₂}⟩)` (hx-used's `X0EtaRoute.TData` with idele `s`), `τ_{Q₁} ~ τ_Q + a/d` and
`τ_{Q₂} ~ τ_{πQ} + ν(a)/d` under `Γ₀(32)`.

Content (elementary; not proved here): `τ_Q + a/d`, `(a, d) = 1`, are the conductor-`d` sublattices of index `d` of
the `𝒪_K`-lattice `⟨1/d, τ_Q⟩`, with their 32-structures inside `⟨1/(32d), τ_Q⟩`; `s⁻¹` is `𝒪_K`-linear locally, so it
maps them to the conductor-`d` sublattices of `s⁻¹⟨1/d, τ_Q⟩ = c⟨1/d, τ_{πQ}⟩` (the Heegner-point action of the class
of `s`, Gross 1984 §3, as in gz-heegner's `exists_compose`); on these, `(a/d) = (β/d)·χ_gen`, where `χ_gen` is the
genus character of `−md²` attached to `d` (`χ_gen` of a form = `(n/d)` for `n` represented, prime to `d`), and
`χ_gen(class of s) = σ(√d)/√d` (genus theory: `K(√d) ⊆` the ring class field of conductor `d`, Cox, *Primes of the
form x² + ny²*, §6 and Thm 9.18; UNVERIFIED numbers). -/
def TwistLatticeCd : Prop :=
  ∀ (d : ℕ) [NeZero d], d % 8 = 5 → Squarefree d →
  ∀ (m : ℕ) [NeZero m], Squarefree m → m % 4 = 3 → 4 < m → HeegnerHyp (32 * d ^ 2) (-(m : ℤ)) →
  ∀ (β : ℤ) (S : Finset (HeegnerForm (32 * d ^ 2) (-(m : ℤ)))),
    ZInQ.GZHL3.IsHeegnerReps (32 * d ^ 2) (-(m : ℤ)) β S →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      Complex.I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), T5Glue.ArtinCond m e σ s →
  ∃ π : HeegnerForm (32 * d ^ 2) (-(m : ℤ)) → HeegnerForm (32 * d ^ 2) (-(m : ℤ)),
    Set.MapsTo π S S ∧ Set.InjOn π S ∧ ∀ Q ∈ S,
    ∃ ν : ZMod d ≃ ZMod d,
      (∀ a : ZMod d, jacobiSym ((ν a).val : ℤ) d =
        (if σ (gaussD d) = gaussD d then 1 else -1) * jacobiSym (a.val : ℤ) d) ∧
      ∀ a : ZMod d, jacobiSym (a.val : ℤ) d ≠ 0 →
        ∃ T : X0EtaRoute.TData m d (discOf m d), T.s = s ∧
          (∃ γ ∈ CongruenceSubgroup.Gamma0 32, γ • T.Q.tauH = shiftH d Q.tauH a) ∧
          (∃ γ ∈ CongruenceSubgroup.Gamma0 32, γ • T.Q'.tauH = shiftH d (π Q).tauH (ν a))

/-! ## §3. The reduction -/

/-- The level-32 transport, from `hCM` and the proved theta identity. -/
theorem phiC_transport (hCM : T5Glue.ShimuraMainCM) {m : ℕ} [NeZero m] {f : ℕ} [NeZero f] {D : ℤ}
    (T : X0EtaRoute.TData m f D) (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      Complex.I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (hs : T5Glue.ArtinCond m e σ T.s) :
    Affine.Point.map (ZInQ.GZHeegner.sigA σ) (ZInQ.Contrib.TYZGenus.X0.phiC T.Q.tauH) =
      ZInQ.Contrib.TYZGenus.X0.phiC T.Q'.tauH := by
  have hX := X0EtaRoute.xEtaWeierstrassPair_of
    (X0EtaRoute.xEtaWeierstrass_of_theta ThetaWP8.thetaWeierstrass8)
  exact map_phiC (X0EtaRoute.x_conj hX hCM T e he σ hs) (X0EtaRoute.y_conj hX hCM T e he σ hs)

/-- **`TwistTransportCd` from the main theorem of CM and the lattice statement.** -/
theorem twistTransportCd_of (hCM : T5Glue.ShimuraMainCM) (hL : TwistLatticeCd) : TwistTransportCd := by
  intro d _ hd hsq m _ hmsq hm3 hm4 hHH β S hS σ hσK
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  obtain ⟨s, hs⟩ := T5Glue.artinLift_of_abs T5Glue.absArtinSurjectiveQNeg m hmsq e he σ hσK
  obtain ⟨π, hπS, hπinj, hQ⟩ := hL d hd hsq m hmsq hm3 hm4 hHH β S hS e he σ s hs
  refine ⟨π, hπS, hπinj, fun Q hQS => ?_⟩
  obtain ⟨ν, hνχ, hT⟩ := hQ Q hQS
  set ε : ℤ := if σ (gaussD d) = gaussD d then 1 else -1 with hε
  have hε2 : ε * ε = 1 := by rw [hε]; split_ifs <;> norm_num
  have hpt : ∀ a : ZMod d, jacobiSym (a.val : ℤ) d •
      Affine.Point.map (ZInQ.GZHeegner.sigA σ) (ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d Q.tauH a)) =
      (ε * jacobiSym ((ν a).val : ℤ) d) •
        ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH (ν a)) := by
    intro a
    have hc : ε * jacobiSym ((ν a).val : ℤ) d = jacobiSym (a.val : ℤ) d := by
      rw [hνχ a, ← mul_assoc, hε2, one_mul]
    rw [hc]
    by_cases ha : jacobiSym (a.val : ℤ) d = 0
    · rw [ha]; simp
    · obtain ⟨T, hTs, ⟨γ, hγ, hγe⟩, ⟨γ', hγ', hγe'⟩⟩ := hT a ha
      rw [← hγe, ← hγe', phiC_gamma0 hγ, phiC_gamma0 hγ']
      congr 1
      exact phiC_transport hCM T e he σ (hTs ▸ hs)
  unfold zTw
  rw [map_sum]
  simp_rw [map_zsmul, hpt, mul_smul]
  rw [← Finset.smul_sum]
  have hre : ∑ a : ZMod d, jacobiSym ((ν a).val : ℤ) d •
      ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH (ν a)) =
      ∑ b : ZMod d, jacobiSym (b.val : ℤ) d • ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH b) :=
    Equiv.sum_comp ν (fun b => jacobiSym (b.val : ℤ) d • ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d (π Q).tauH b))
  rw [hre, hε]
  split_ifs <;> simp

/-- **`GZStatements.GrossZagierHeegnerCd` from the main theorem of CM, the lattice statement at conductor `d`
and the two printed Gross–Zagier statements** (no canonical model of `X₀(32 d²)`). -/
theorem grossZagierHeegnerCd_of_lattice (hCM : T5Glue.ShimuraMainCM) (hL : TwistLatticeCd)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_twist (twistTransportCd_of hCM hL) hGZ hGC

end ZInQ.Heegner32
