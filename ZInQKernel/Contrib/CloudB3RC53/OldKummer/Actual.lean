import ZInQKernel.Contrib.CloudB3RC53.OldKummer.Transport
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota

/-!
# Old Kummer, part 2: the cohomology of the actual Kummer condition at the residual level

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, tex 3413–3438, at `i = 1`
(`A_1 = 𝔽₂`, `M_1 = E[2] ⊗ A_1`, the residual level of the table, tex 4544–4573).

Lane RC29's actual Kummer condition `actualKummerAt W i s hs hs0 α hFull v hα` is lane RC28's
`kummerAt` for the actual local twist `B = E^{(h)}` over `K_v` with the genuine coefficient map
`ι_v = kummerIota`. At `i = 1`:

* `acoef_one_eq_intCast`, `intScalars_acoef_one`: every element of `A_1` is an integer;
* `oneTmul_surjective_one`: `t ↦ 1 ⊗ t` is onto `A_1 ⊗ T`; hence `kummerIota_bijective_one`:
  `ι_v : B(K̄_v)[2] → M_1` is a bijection (injective by RC29's `kummerIotaBase_injective`);
* `natCard_actualKummerAt_one`: `|H⁰(U_v)| = |B(K_v)[2]|` and `|H¹(U_v)| = |B(K_v)/2B(K_v)|`
  (part 1, `natCard_kummerConditionIn_H0`/`_H1`).

**Scope.**
* Only the level `i = 1` is treated. This is the level the consumers need: RC6's residual bound
  (Lemma `ex:limits-residual-bound`) works at the residue field `B_i/(t) = 𝔽₂` with the residual
  coefficient module `W = E[2]` (tex 4478–4480), and its old-Kummer row is the residual pair
  `(2, 2 + d_w)` (tex 4551–4556); `GenuineInst.genCondDim2` and RC6's `condDimAt` are residual
  (`𝔽₂`) dimensions. For `i > 1` the transport of part 1 does not apply: `ι_v` is injective but
  not onto (`|M_i| = |A_i|² = 2^(2i²) > 2^(2i) = |B[2^i]|` for `i > 1`), and the scalars of `A_i` are not integers.
* The text obtains the residual condition as the derived reduction of the Kummer condition; here
  the level-`1` actual condition (coefficients `M_1 = E[2] ⊗ A_1`) is computed directly. The
  comparison between the derived reduction of the level-`i` condition and the level-`1` condition
  is not formalized (no formal consumer uses it).
* The statements are cardinalities (`|H⁰|`, `|H¹|`), not lengths over `A_1`.

**Classification.** PROVED (from RC29's hypotheses of `actualKummerAt`: `FullTorsion` at `2`, GLUE
as in RC28, and `IsLocallyQuadAt`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OldKummer

open NumberField IsDedekindDomain WeierstrassCurve TensorProduct ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-- Every element of `A_1 = (ℤ/2)[t]/(t)` is an integer. PROVED. -/
theorem acoef_one_eq_intCast (a : Acoef 1) : ∃ n : ℤ, a = (n : Acoef 1) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨((p.coeff 0).val : ℤ), ?_⟩
  have hX : Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ 1))) ^ 1}) p =
      Ideal.Quotient.mk _ (Polynomial.C (p.coeff 0)) := by
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr ((pow_one _).dvd.trans Polynomial.X_dvd_sub_C)
  rw [hX, Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk _), ← map_natCast Polynomial.C,
    ZMod.natCast_zmod_val]

/-- Every scalar of `A_1` acts as an integer on an `A_1`-module. PROVED. -/
theorem intScalars_acoef_one (M : Type*) [AddCommGroup M] [Module (Acoef 1) M] :
    IntScalars (Acoef 1) M := fun a => by
  obtain ⟨n, rfl⟩ := acoef_one_eq_intCast a
  exact ⟨n, fun x => Int.cast_smul_eq_zsmul (Acoef 1) n x⟩

/-- `t ↦ 1 ⊗ t` is onto `A_1 ⊗ T`. PROVED. -/
theorem oneTmul_surjective_one {G : Type} [Group G] (α : G →* (Acoef 1)ˣ) (T : Type)
    [AddCommGroup T] : Function.Surjective (oneTmul (Acoef 1) α T) := by
  intro x
  obtain ⟨y, rfl⟩ := (CoefMod.equiv (Acoef 1) α T).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a t =>
    obtain ⟨n, rfl⟩ := acoef_one_eq_intCast a
    refine ⟨n • t, ?_⟩
    rw [oneTmul_apply]
    congr 1
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, mul_one]
  | add y y' hy hy' =>
    obtain ⟨t, ht⟩ := hy
    obtain ⟨t', ht'⟩ := hy'
    exact ⟨t + t', by rw [map_add, ht, ht', map_add]⟩

section Iota

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef 1)ˣ)
  (hFull : FullTorsion K S W (2 ^ 1))

/-- **At `i = 1` the Kummer coefficient map is a bijection** `B(K̄_v)[2] ≅ M_1` (injective by
RC29's `kummerIotaBase_injective`; onto since `φ_q`, `j⁻¹` are isomorphisms and `t ↦ 1 ⊗ t` is onto
`A_1 ⊗ T`). PROVED. -/
theorem kummerIotaBase_bijective_one (v : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (kummerIotaBase W 1 s hs hs0 α hFull v) := by
  refine ⟨kummerIotaBase_injective W 1 s hs hs0 α hFull v one_ne_zero, fun x => ?_⟩
  obtain ⟨t, rfl⟩ := oneTmul_surjective_one α _ x
  refine ⟨(twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
    two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) (2 ^ 1)).symm
      (compTorsEquiv W (2 ^ 1) hFull v t), ?_⟩
  rw [kummerIotaBase_apply, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

theorem kummerIota_bijective_one (v : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (kummerIota W 1 s hs hs0 α hFull v) :=
  kummerIotaBase_bijective_one W s hs hs0 α hFull v

open scoped Classical in
/-- **The cohomology of the actual Kummer condition at the residual level** (tex 3415–3418 at
`i = 1`): `|H⁰(U_v)| = |B(K_v)[2]|` and `|H¹(U_v)| = |B(K_v)/2B(K_v)|` for the actual local twist
`B = E^{(h)}` over `K_v` and RC29's genuine `ι_v`. PROVED. -/
theorem natCard_actualKummerAt_one [IsOpenKer α] (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1) :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) =
        Nat.card (AddSubgroup.torsionBy (localTwist W h v.1).toAffine.Point ((2 ^ 1 : ℕ) : ℤ)) ∧
      Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
        Nat.card ((localTwist W h v.1).toAffine.Point ⧸
          (nsmulAddMonoidHom (α := (localTwist W h v.1).toAffine.Point) (2 ^ 1)).range) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact ⟨natCard_kummerConditionIn_H0 (Acoef 1) (kummerIota W 1 s hs hs0 α hFull v.1)
      (kummerIota_smul W 1 s hs hs0 α hFull v.1 hα) (kummerIota_bijective_one W s hs hs0 α hFull v.1),
    natCard_kummerConditionIn_H1 (Acoef 1) (kummerIota W 1 s hs hs0 α hFull v.1)
      (kummerIota_smul W 1 s hs hs0 α hFull v.1 hα) (kummerIota_bijective_one W s hs hs0 α hFull v.1)
      (intScalars_acoef_one _)⟩

end Iota

end ZInQ.Contrib.CloudB3RC53.OldKummer
