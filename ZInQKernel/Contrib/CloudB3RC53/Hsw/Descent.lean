import ZInQKernel.Contrib.CloudB3RC53.Hsw.Coordinates
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.TruncIsotropy

/-!
# RC53 `hsw`: descent of the cone-trace cup product to `H¹(W_rel)`

Elliot's computation behind tex L2816–2818 (context L2790–2830). For a relaxed localization `R`
with strict condition `f : U_str → U_rel` (the switch exactness data of
`SwitchAdjunctionFromDuality`), Selmer pairing data `Q` and a trace `tr` killing cone
coboundaries, consider the left-hand side of `hsw`,

  `tr((0, s, −ι u) ∪ (0, t, 0)) = tr(0, h(s, t) − ι u ∪ ι t)`   (`lhs_eq`),

where `t` is a cocycle of `U_rel` and `du = f s`. The question is whether this depends only on the
classes `[g t], [g u] ∈ H¹(W_rel)`, and is bilinear there. That is `ResiduePairing` of
`Coordinates.lean` for some bilinear form `P`.

## Results

* `second_coboundary` (isotropy homotopy plus the Leibniz rule of `∪_L`): the expression is a local
  coboundary when `(u, s) = (dx + f u', du')`. That is exactly when `[g u] = 0`. So it **descends
  in the second variable**.
* `first_coboundary` (isotropy plus Leibniz): it is a local coboundary when `t = dx`.
* For `t = f t'` with `t'` a strict cocycle we have `[g t] = 0`, but nothing in `SelPairData`
  makes the expression vanish. The isotropy homotopy pairs `U_str × U_rel` in that order, and here
  the strict cochain sits in the second slot. This is `StrictOrth`.
* `exists_residuePairing` (**the descent**, PROVED): under the switch exactness data,
  `tr ∘ d = 0` and `StrictOrth`, the left-hand side is `P(eR[g t], eR[g u])` for a bilinear form
  `P`.
* `exists_residuePairing_iff`: under the same data, a residue pairing exists **iff**
  `StrictOrth` holds. So `StrictOrth` is necessary for `hsw` in any coordinates.
* `strictOrth_counterexample`: `StrictOrth` does **not** follow from the axioms of
  `SelPairData` and `tr ∘ d = 0`. There is an explicit model over `ℚ` with zero differentials
  where it fails.
* `strictOrth_of_reverseIsotropy`, `exists_residuePairing_of_reverseIsotropy`: a sufficient
  condition. Suppose there is a homotopy `h'` on `U_rel × U_str`, the reverse order of `Q.hU`,
  with `d h' = ι u ∪ ι f t'`, and suppose it agrees with `Q.hU` on strict × strict cochains
  (`ReverseIsotropy`). Then `StrictOrth` holds, and so does the descent.
* `exists_residuePairing_trunc`: the same descent for `SelPairDataTrunc`, i.e. for the truncated
  `hsw` of `switchAdjunction_of_trunc`.
* Non-vacuity: `symReverse` is a `ReverseIsotropy` instance in a model with a nonzero
  local cup product (`symForm_ne_zero`, `strictOrth_symQ`).

The first-variable descent along strict classes is therefore an extra input. In Nekovář's setting
it comes from the graded commutativity of the local cup product up to homotopy together with
`U_str ⊥ U_rel`. That is the content of `ReverseIsotropy`, which `SelPairData` does not record.

The descended form `P` is canonical only on `{[g t] : dt = 0} × H¹(W_rel)`. Off that subspace it
is extended arbitrarily. So the local-duality shape required by `hsw_of_residuePairing` is a
statement about the local Tate pairing on `H¹(W_rel)`, which is still an external input.

All results are `PROVED`. No new axioms.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {k : Type} [Field k]

/-! ### Bilinear descent over a field -/

/-- Over a field every linear map `β` has a quasi-section `σ` with `β ∘ σ ∘ β = β`. `PROVED`. -/
theorem exists_quasiSection {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] (β : V →ₗ[k] V') : ∃ σ : V' →ₗ[k] V, ∀ v, β (σ (β v)) = β v := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range β).subtype
    (Submodule.ker_subtype _)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective β.rangeRestrict
    (LinearMap.range_rangeRestrict β)
  refine ⟨s ∘ₗ r, fun v => ?_⟩
  have h1 : r (β v) = β.rangeRestrict v := LinearMap.congr_fun hr (β.rangeRestrict v)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (β.rangeRestrict v))
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply] at h2 ⊢
  rw [h1]
  exact h2

/-- **Bilinear descent**: a bilinear form `B` on `M × N` that vanishes on `ker α × N` and on
`M × ker β` is `P(α m, β n)` for a bilinear form `P` on the targets. `PROVED`. -/
theorem exists_bilin_factor {M N H H' : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']
    (B : M →ₗ[k] N →ₗ[k] k) (α : M →ₗ[k] H) (β : N →ₗ[k] H')
    (hα : ∀ m, α m = 0 → ∀ n, B m n = 0) (hβ : ∀ n, β n = 0 → ∀ m, B m n = 0) :
    ∃ P : H →ₗ[k] H' →ₗ[k] k, ∀ m n, B m n = P (α m) (β n) := by
  obtain ⟨σα, hσα⟩ := exists_quasiSection α
  obtain ⟨σβ, hσβ⟩ := exists_quasiSection β
  refine ⟨B.compl₁₂ σα σβ, fun m n => ?_⟩
  simp only [LinearMap.compl₁₂_apply]
  have e1 : B m n = B (σα (α m)) n := by
    have := hα (m - σα (α m)) (by rw [map_sub, hσα, sub_self]) n
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  have e2 : B (σα (α m)) n = B (σα (α m)) (σβ (β n)) := by
    have := hβ (n - σβ (β n)) (by rw [map_sub, hσβ, sub_self]) (σα (α m))
    rwa [map_sub, sub_eq_zero] at this
  rw [e1, e2]

/-! ### The cochain computation (tex L2790–2818) -/

section Loc

/-- The local summand `E_L² → Cone³`, `x ↦ (0, x)`. -/
def locT {D D' : SelData k} (Q : SelPairData D D') : Q.EL.X 2 →ₗ[k] (coneCx Q.resE).X 3 where
  toFun x := ((0 : Q.E.X 3), x)
  map_add' _ _ := Prod.ext (add_zero (0 : Q.E.X 3)).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl

/-- The trace kills local coboundaries: `tr(0, d z) = 0`. `PROVED`. -/
theorem tr_locT_d {D D' : SelData k} (Q : SelPairData D D')
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (z : Q.EL.X 1) :
    tr (locT Q (Q.EL.d 1 2 rfl z)) = 0 := by
  have h := htr ((0 : Q.E.X 2), -z)
  have e : (coneCx Q.resE).d 2 3 rfl ((0 : Q.E.X 2), -z) = locT Q (Q.EL.d 1 2 rfl z) := by
    change (Q.E.d 2 3 rfl 0, Q.resE.f 2 2 rfl 0 - Q.EL.d 1 2 rfl (-z)) = ((0 : Q.E.X 3), _)
    rw [map_zero, map_zero, map_neg, zero_sub, neg_neg]
  rw [← e]
  exact h

/-- **Strict orthogonality**: the cone-trace cup product of tex L2816 vanishes when the
second cochain is a strict cocycle `f t'`. It is stated for Selmer data `D` with a strict
condition `f : U_str → U`. Only `D = R.D` is used for a relaxed localization `R`. -/
def StrictOrth (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)
    (Q : SelPairData (restrictData D f) D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k) : Prop :=
  ∀ (t' : Ustr.X 1) (u : D.U.X 1) (s : Ustr.X 2), Ustr.d 1 2 rfl t' = 0 →
    D.U.d 1 2 rfl u = f.f 2 2 rfl s →
    tr (selCupFun Q 2 1 3 rfl ((0 : D.G.X 2), s, -(D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : D.G.X 1), f.f 1 1 rfl t', (0 : D.L.X (1 - 1)))) = 0

/-- **The left-hand side of `hsw`**: `tr((0, s, −ι u) ∪ (0, t, 0)) = tr(0, h(s, t) − ι u ∪ ι t)`.
`PROVED`. -/
theorem lhs_eq (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)
    (Q : SelPairData (restrictData D f) D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (t u : D.U.X 1) (s : Ustr.X 2) :
    tr (selCupFun Q 2 1 3 rfl ((0 : D.G.X 2), s, -(D.ι.f 1 (2 - 1) (by omega) u))
        ((0 : D.G.X 1), t, (0 : D.L.X (1 - 1)))) =
      tr (locT Q (Q.hU 2 1 2 rfl s t -
        Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl t))) := by
  congr 1
  refine Prod.ext ?_ ?_
  · change Q.cupG.P 2 1 3 rfl 0 0 = 0
    simp
  · change Q.cupL.P 1 1 2 rfl (-(D.ι.f 1 1 rfl u) : (restrictData D f).L.X 1)
        (D.ι.f 1 1 rfl t) +
      sgn 2 • Q.cupL.P 2 0 2 rfl ((restrictData D f).res.f 2 2 rfl 0) 0 + Q.hU 2 1 2 rfl s t =
        Q.hU 2 1 2 rfl s t - Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl t)
    have hneg : Q.cupL.P 1 1 2 rfl (-(D.ι.f 1 1 rfl u) : (restrictData D f).L.X 1) =
        -Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) := map_neg (Q.cupL.P 1 1 2 rfl) _
    rw [hneg, LinearMap.neg_apply]
    simp only [map_zero, smul_zero, add_zero]
    abel


end Loc

section Descent

variable (R : QuasiRelaxedLocalization k) (Ustr : GCx k) (f : GHom Ustr R.D.U)
  (Q : SelPairData (restrictData R.D f) R.D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)

theorem sgn_zero' : sgn 0 = 1 := by simp [sgn]

/-- **Coboundaries in the first variable** (Leibniz and isotropy): for `du = f s`,
`h(s, dx) − ι u ∪ ι dx = d(ι u ∪ ι x − h(s, x))`. `PROVED`. -/
theorem first_coboundary (hf3 : Function.Injective (f.f 3 3 rfl)) (x : R.D.U.X 0)
    (u : R.D.U.X 1) (s : Ustr.X 2) (hus : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) :
    Q.hU 2 1 2 rfl s (R.D.U.d 0 1 rfl x) -
        Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x)) =
      Q.EL.d 1 2 rfl (Q.cupL.P 1 0 1 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 0 0 rfl x) -
        Q.hU 2 0 1 rfl s x) := by
  have hs : Ustr.d 2 3 rfl s = 0 := hf3 (by
    rw [f.comm 2 3 2 3 rfl rfl rfl rfl s, ← hus, R.D.U.d_d, map_zero])
  have iso : Q.EL.d 1 2 rfl (Q.hU 2 0 1 rfl s x) + Q.hU 3 0 2 rfl (Ustr.d 2 3 rfl s) x +
      sgn 2 • Q.hU 2 1 2 rfl s (R.D.U.d 0 1 rfl x) =
      Q.cupL.P 2 0 2 rfl (R.D.ι.f 2 2 rfl (f.f 2 2 rfl s)) (R.D.ι.f 0 0 rfl x) :=
    Q.isotropy 2 3 0 1 1 2 rfl rfl rfl rfl s x
  have leib := Q.cupL.leib 1 2 0 1 1 2 rfl rfl rfl rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 0 0 rfl x)
  have c1 : R.D.L.d 1 2 rfl (R.D.ι.f 1 1 rfl u) = R.D.ι.f 2 2 rfl (f.f 2 2 rfl s) := by
    rw [← R.D.ι.comm 1 2 1 2 rfl rfl rfl rfl u, hus]
  have c0 : R.D.L.d 0 1 rfl (R.D.ι.f 0 0 rfl x) = R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x) :=
    (R.D.ι.comm 0 1 0 1 rfl rfl rfl rfl x).symm
  change Q.EL.d 1 2 rfl (Q.cupL.P 1 0 1 rfl (R.D.ι.f 1 1 rfl u) (R.D.ι.f 0 0 rfl x)) =
    Q.cupL.P 2 0 2 rfl (R.D.L.d 1 2 rfl (R.D.ι.f 1 1 rfl u)) (R.D.ι.f 0 0 rfl x) +
      sgn 1 • Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u)
        (R.D.L.d 0 1 rfl (R.D.ι.f 0 0 rfl x)) at leib
  have h0 : Q.hU 3 0 2 rfl (Ustr.d 2 3 rfl s) x = 0 :=
    (congrArg (fun z => Q.hU 3 0 2 rfl z x) hs).trans (LinearMap.map_zero₂ _ _)
  rw [h0, add_zero, sgn_two, one_smul] at iso
  rw [c1, c0, sgn_one, neg_one_smul] at leib
  rw [map_sub, leib, ← iso]
  abel

/-- **Coboundaries and strict cochains in the second variable** (Leibniz and isotropy): for a
cocycle `t`, `h(d u', t) − ι(dx + f u') ∪ ι t = d(−h(u', t) − ι x ∪ ι t)`. `PROVED`. -/
theorem second_coboundary (t : R.D.U.X 1) (ht : R.D.U.d 1 2 rfl t = 0) (x : R.D.U.X 0)
    (u' : Ustr.X 1) :
    Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl u') t -
        Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x + f.f 1 1 rfl u'))
          (R.D.ι.f 1 1 rfl t) =
      Q.EL.d 1 2 rfl (-Q.hU 1 1 1 rfl u' t - Q.cupL.P 0 1 1 rfl (R.D.ι.f 0 0 rfl x)
        (R.D.ι.f 1 1 rfl t)) := by
  have iso : Q.EL.d 1 2 rfl (Q.hU 1 1 1 rfl u' t) + Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl u') t +
      sgn 1 • Q.hU 1 2 2 rfl u' (R.D.U.d 1 2 rfl t) =
      Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl (f.f 1 1 rfl u')) (R.D.ι.f 1 1 rfl t) :=
    Q.isotropy 1 2 1 2 1 2 rfl rfl rfl rfl u' t
  have leib := Q.cupL.leib 0 1 1 2 1 2 rfl rfl rfl rfl (R.D.ι.f 0 0 rfl x) (R.D.ι.f 1 1 rfl t)
  have c1 : R.D.L.d 1 2 rfl (R.D.ι.f 1 1 rfl t) = 0 := by
    rw [← R.D.ι.comm 1 2 1 2 rfl rfl rfl rfl t, ht, map_zero]
  have c0 : R.D.L.d 0 1 rfl (R.D.ι.f 0 0 rfl x) = R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x) :=
    (R.D.ι.comm 0 1 0 1 rfl rfl rfl rfl x).symm
  change Q.EL.d 1 2 rfl (Q.cupL.P 0 1 1 rfl (R.D.ι.f 0 0 rfl x) (R.D.ι.f 1 1 rfl t)) =
    Q.cupL.P 1 1 2 rfl (R.D.L.d 0 1 rfl (R.D.ι.f 0 0 rfl x)) (R.D.ι.f 1 1 rfl t) +
      sgn 0 • Q.cupL.P 0 2 2 rfl (R.D.ι.f 0 0 rfl x)
        (R.D.L.d 1 2 rfl (R.D.ι.f 1 1 rfl t)) at leib
  rw [ht, map_zero, smul_zero, add_zero] at iso
  rw [c1, c0, map_zero, smul_zero, add_zero] at leib
  have hadd : Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x + f.f 1 1 rfl u'))
      (R.D.ι.f 1 1 rfl t) =
      Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x)) (R.D.ι.f 1 1 rfl t) +
        Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl (f.f 1 1 rfl u')) (R.D.ι.f 1 1 rfl t) := by
    rw [map_add]
    exact LinearMap.map_add₂ _ _ _ _
  rw [hadd, map_sub, map_neg, leib, ← iso]
  abel


/-- **Strict orthogonality is necessary**: a residue pairing (for any `P`) forces `StrictOrth`,
because `[g (f t')] = 0`. `PROVED`. -/
theorem strictOrth_of_residuePairing
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k))) (hP : ResiduePairing R Ustr f Q tr P) :
    StrictOrth R.D Ustr f Q tr := by
  intro t' u s ht' hu
  have ht : R.D.U.d 1 2 rfl (f.f 1 1 rfl t') = 0 := by
    rw [← f.comm 1 2 1 2 rfl rfl rfl rfl t', ht', map_zero]
  have hcu : R.gR.f 1 1 rfl u ∈ LinearMap.ker (R.Wrel.d 1 2 rfl) :=
    LinearMap.mem_ker.2 ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl u).symm.trans (by
      rw [hu]; exact hfg 2 s))
  rw [hP _ u s ht hu 0 ⟨_, hcu⟩ (hfg 1 t').symm rfl, map_zero, map_zero, map_zero,
    LinearMap.zero_apply]

/-- **The descent (Elliot's computation, tex L2790–2818)**, `PROVED`. Assume the switch exactness
data and that the trace kills cone coboundaries, and assume `StrictOrth`. Then the cone-trace cup
product `tr((0, s, −ι u) ∪ (0, t, 0))` depends only on the classes `[g t], [g u] ∈ H¹(W_rel)` and is
bilinear there: it is `ResiduePairing` for some bilinear form `P`. -/
theorem exists_residuePairing
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (hSO : StrictOrth R.D Ustr f Q tr) :
    ∃ P, ResiduePairing R Ustr f Q tr P := by
  let M := LinearMap.ker (R.D.U.d 1 2 rfl)
  let φ : (R.D.U.X 1 × Ustr.X 2) →ₗ[k] R.D.U.X 2 := (R.D.U.d 1 2 rfl).coprod (-(f.f 2 2 rfl))
  let N := LinearMap.ker φ
  have hN : ∀ n : N, R.D.U.d 1 2 rfl n.1.1 = f.f 2 2 rfl n.1.2 := fun n => by
    have h : R.D.U.d 1 2 rfl n.1.1 + (-(f.f 2 2 rfl)) n.1.2 = 0 := LinearMap.mem_ker.1 n.2
    rw [LinearMap.neg_apply, add_neg_eq_zero] at h
    exact h
  let hUpart : N →ₗ[k] M →ₗ[k] Q.EL.X 2 :=
    (Q.hU 2 1 2 rfl).compl₁₂ (LinearMap.snd k _ _ ∘ₗ N.subtype) M.subtype
  let cupPart : N →ₗ[k] M →ₗ[k] Q.EL.X 2 :=
    (Q.cupL.P 1 1 2 rfl).compl₁₂ (R.D.ι.f 1 1 rfl ∘ₗ LinearMap.fst k _ _ ∘ₗ N.subtype)
      (R.D.ι.f 1 1 rfl ∘ₗ M.subtype)
  let B : M →ₗ[k] N →ₗ[k] k := ((hUpart - cupPart).compr₂ (tr ∘ₗ locT Q)).flip
  have hB : ∀ m n, B m n = tr (locT Q (Q.hU 2 1 2 rfl n.1.2 m.1 -
      Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl n.1.1) (R.D.ι.f 1 1 rfl m.1))) := fun _ _ => rfl
  let α : M →ₗ[k] R.Wrel.toCC.homology 1 :=
    cls1 R.Wrel ∘ₗ LinearMap.codRestrict (LinearMap.ker (R.Wrel.d 1 2 rfl))
      (R.gR.f 1 1 rfl ∘ₗ M.subtype) (fun m => LinearMap.mem_ker.2
        ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl m.1).symm.trans (by
          rw [LinearMap.mem_ker.1 m.2, map_zero])))
  let β : N →ₗ[k] R.Wrel.toCC.homology 1 :=
    cls1 R.Wrel ∘ₗ LinearMap.codRestrict (LinearMap.ker (R.Wrel.d 1 2 rfl))
      (R.gR.f 1 1 rfl ∘ₗ LinearMap.fst k _ _ ∘ₗ N.subtype) (fun n => LinearMap.mem_ker.2
        ((R.gR.comm 1 2 1 2 rfl rfl rfl rfl n.1.1).symm.trans (by
          rw [hN n]; exact hfg 2 n.1.2)))
  have hα : ∀ m, α m = 0 → ∀ n, B m n = 0 := by
    rintro ⟨t, ht⟩ hm ⟨⟨u, s⟩, hus'⟩
    have hus : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s := hN ⟨(u, s), hus'⟩
    obtain ⟨y, hy⟩ := clsAt_eq_zero R.Wrel 0 1 2 rfl rfl _ hm
    obtain ⟨x, rfl⟩ := hg 0 y
    have hk : R.gR.f 1 1 rfl (t - R.D.U.d 0 1 rfl x) = 0 := by
      rw [map_sub, R.gR.comm 0 1 0 1 rfl rfl rfl rfl x]
      exact sub_eq_zero.2 hy.symm
    obtain ⟨t', ht'⟩ := hex 1 _ hk
    have hdt' : Ustr.d 1 2 rfl t' = 0 := hf 2 (by
      rw [f.comm 1 2 1 2 rfl rfl rfl rfl t', ht', map_sub, LinearMap.mem_ker.1 ht, R.D.U.d_d,
        sub_zero, map_zero])
    have ht_eq : t = R.D.U.d 0 1 rfl x + f.f 1 1 rfl t' := by rw [ht']; abel
    subst ht_eq
    rw [hB]
    have hs3 : Function.Injective (f.f 3 3 rfl) := hf 3
    have h1 := first_coboundary R Ustr f Q hs3 x u s hus
    have h2 := hSO t' u s hdt' hus
    rw [lhs_eq] at h2
    change tr (locT Q (Q.hU 2 1 2 rfl s (R.D.U.d 0 1 rfl x + f.f 1 1 rfl t') -
      Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u)
        (R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x + f.f 1 1 rfl t')))) = 0
    rw [(Q.hU 2 1 2 rfl s).map_add, (R.D.ι.f 1 1 rfl).map_add,
      (Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl u)).map_add, add_sub_add_comm, map_add, map_add, h1,
      tr_locT_d Q tr htr, h2, add_zero]
  have hβ : ∀ n, β n = 0 → ∀ m, B m n = 0 := by
    rintro ⟨⟨u, s⟩, hus'⟩ hn ⟨t, ht⟩
    have hus : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s := hN ⟨(u, s), hus'⟩
    obtain ⟨y, hy⟩ := clsAt_eq_zero R.Wrel 0 1 2 rfl rfl _ hn
    obtain ⟨x, rfl⟩ := hg 0 y
    have hk : R.gR.f 1 1 rfl (u - R.D.U.d 0 1 rfl x) = 0 := by
      rw [map_sub, R.gR.comm 0 1 0 1 rfl rfl rfl rfl x]
      exact sub_eq_zero.2 hy.symm
    obtain ⟨u', hu'⟩ := hex 1 _ hk
    have hu_eq : u = R.D.U.d 0 1 rfl x + f.f 1 1 rfl u' := by rw [hu']; abel
    have hs_eq : s = Ustr.d 1 2 rfl u' := hf 2 (by
      rw [← hus, hu_eq, map_add, R.D.U.d_d, zero_add, f.comm 1 2 1 2 rfl rfl rfl rfl u'])
    subst hs_eq hu_eq
    rw [hB]
    change tr (locT Q (Q.hU 2 1 2 rfl (Ustr.d 1 2 rfl u') t -
      Q.cupL.P 1 1 2 rfl (R.D.ι.f 1 1 rfl (R.D.U.d 0 1 rfl x + f.f 1 1 rfl u'))
        (R.D.ι.f 1 1 rfl t))) = 0
    rw [second_coboundary R Ustr f Q t (LinearMap.mem_ker.1 ht) x u']
    exact tr_locT_d Q tr htr _
  obtain ⟨P', hP'⟩ := exists_bilin_factor B α β hα hβ
  refine ⟨P'.compl₁₂ R.eR.symm.toLinearMap R.eR.symm.toLinearMap, ?_⟩
  intro t u s ht hu ct cu hct hcu
  have hus : (u, s) ∈ N := LinearMap.mem_ker.2 (by
    change R.D.U.d 1 2 rfl u + (-(f.f 2 2 rfl)) s = 0
    rw [LinearMap.neg_apply, hu, add_neg_cancel])
  have e := hP' ⟨t, LinearMap.mem_ker.2 ht⟩ ⟨(u, s), hus⟩
  rw [hB] at e
  have ea : α ⟨t, LinearMap.mem_ker.2 ht⟩ = cls1 R.Wrel ct :=
    congrArg (cls1 R.Wrel) (Subtype.ext hct.symm)
  have eb : β ⟨(u, s), hus⟩ = cls1 R.Wrel cu := congrArg (cls1 R.Wrel) (Subtype.ext hcu.symm)
  rw [lhs_eq, e, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, ea, eb]

/-- **The descent criterion**: under the switch exactness data and `tr ∘ d = 0`, the cone-trace cup
product is a residue pairing (for some `P`) iff it satisfies `StrictOrth`. `PROVED`. -/
theorem exists_residuePairing_iff
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) :
    (∃ P, ResiduePairing R Ustr f Q tr P) ↔ StrictOrth R.D Ustr f Q tr :=
  ⟨fun ⟨P, hP⟩ => strictOrth_of_residuePairing R Ustr f Q tr hfg P hP,
    exists_residuePairing R Ustr f Q tr hfg hf hg hex htr⟩

end Descent


/-! ### A sufficient condition for `StrictOrth`: reverse isotropy -/

section Reverse

variable (D : SelData k) (Ustr : GCx k) (f : GHom Ustr D.U)
  (Q : SelPairData (restrictData D f) D) (tr : (coneCx Q.resE).X 3 →ₗ[k] k)

/-- **Reverse isotropy** in the degrees of tex L2816: a homotopy `h'` on `U_rel × U_str` (the
reverse order of `Q.hU`) whose boundary is the local cup product `ι u ∪ ι f t'`, and which agrees
with `Q.hU` on strict × strict cochains in degree `(2, 1)`. In Nekovář's setting this comes from the
graded commutativity of the local cup product up to homotopy and `U_str ⊥ U_rel`. -/
structure ReverseIsotropy where
  /-- `h'` in degrees `(1, 1) → 1`. -/
  h11 : D.U.X 1 →ₗ[k] Ustr.X 1 →ₗ[k] Q.EL.X 1
  /-- `h'` in degrees `(2, 1) → 2`. -/
  h21 : D.U.X 2 →ₗ[k] Ustr.X 1 →ₗ[k] Q.EL.X 2
  /-- `h'` in degrees `(1, 2) → 2`. -/
  h12 : D.U.X 1 →ₗ[k] Ustr.X 2 →ₗ[k] Q.EL.X 2
  /-- The reverse isotropy identity `d h' + h'(d ·, ·) − h'(·, d ·) = ι u ∪ ι f t'`. -/
  iso : ∀ (u : D.U.X 1) (t' : Ustr.X 1),
    Q.EL.d 1 2 rfl (h11 u t') + h21 (D.U.d 1 2 rfl u) t' + sgn 1 • h12 u (Ustr.d 1 2 rfl t') =
      Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t'))
  /-- Agreement with `Q.hU` on strict × strict cochains. -/
  compat : ∀ (s : Ustr.X 2) (t' : Ustr.X 1),
    Q.hU 2 1 2 rfl s (f.f 1 1 rfl t') = h21 (f.f 2 2 rfl s) t'

/-- **Reverse isotropy gives `StrictOrth`**: `h(s, f t') − ι u ∪ ι f t' = d(−h'(u, t'))` when
`du = f s` and `dt' = 0`. `PROVED`. -/
theorem strictOrth_of_reverseIsotropy (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (Rv : ReverseIsotropy D Ustr f Q) : StrictOrth D Ustr f Q tr := by
  intro t' u s ht' hus
  have iso := Rv.iso u t'
  rw [ht', map_zero, smul_zero, add_zero, hus] at iso
  have e : Q.hU 2 1 2 rfl s (f.f 1 1 rfl t') -
      Q.cupL.P 1 1 2 rfl (D.ι.f 1 1 rfl u) (D.ι.f 1 1 rfl (f.f 1 1 rfl t')) =
      Q.EL.d 1 2 rfl (-Rv.h11 u t') := by
    rw [Rv.compat s t', ← iso, map_neg]
    abel
  refine (lhs_eq D Ustr f Q tr (f.f 1 1 rfl t') u s).trans ?_
  rw [e]
  exact tr_locT_d Q tr htr _

end Reverse

/-- **The descent from reverse isotropy** (tex L2790–2818), `PROVED`. Under the switch exactness
data, `tr ∘ d = 0`, and reverse isotropy, the cone-trace cup product is a residue pairing. -/
theorem exists_residuePairing_of_reverseIsotropy (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairData (restrictData R.D f) R.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) (Rv : ReverseIsotropy R.D Ustr f Q) :
    ∃ P, ResiduePairing R Ustr f Q tr P :=
  exists_residuePairing R Ustr f Q tr hfg hf hg hex htr
    (strictOrth_of_reverseIsotropy R.D Ustr f Q tr htr Rv)

/-- **The descent for truncated pairing data** (`SelPairDataTrunc`, the input of
`switchAdjunction_of_trunc`), `PROVED`. Suppose `StrictOrth` holds for the `τ≥2` data and trace.
Then the left-hand side of the truncated `hsw`, stated with the original cup formula `selCupFunT`
and trace `tr0`, is a residue pairing. -/
theorem exists_residuePairing_trunc (R : QuasiRelaxedLocalization k) (Ustr : GCx k)
    (f : GHom Ustr R.D.U) (Q : SelPairDataTrunc (restrictData R.D f) R.D)
    (tr0 : (coneCx Q.resE).X 3 →ₗ[k] k) (htr0 : ∀ z, tr0 ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hfg : ∀ n (u : Ustr.X n), R.gR.f n n rfl (f.f n n rfl u) = 0)
    (hf : ∀ n, Function.Injective (f.f n n rfl)) (hg : ∀ n, Function.Surjective (R.gR.f n n rfl))
    (hex : ∀ n (u : R.D.U.X n), R.gR.f n n rfl u = 0 → ∃ u', f.f n n rfl u' = u)
    (hSO : StrictOrth R.D Ustr f Q.toSelPairData (Q.trT tr0 htr0)) :
    ∃ P : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)),
      ∀ (t u : R.D.U.X 1) (s : Ustr.X 2) (_ht : R.D.U.d 1 2 rfl t = 0)
        (_hu : R.D.U.d 1 2 rfl u = f.f 2 2 rfl s) (ct cu : LinearMap.ker (R.Wrel.d 1 2 rfl))
        (_hct : ct.1 = R.gR.f 1 1 rfl t) (_hcu : cu.1 = R.gR.f 1 1 rfl u),
        tr0 (selCupFunT Q 2 1 3 rfl ((0 : R.D.G.X 2), s, -(R.D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : R.D.G.X 1), t, (0 : R.D.L.X (1 - 1)))) =
          P (R.eR (cls1 R.Wrel ct)) (R.eR (cls1 R.Wrel cu)) := by
  obtain ⟨P, hP⟩ := exists_residuePairing R Ustr f Q.toSelPairData (Q.trT tr0 htr0) hfg hf hg hex
    (Q.trT_kills tr0 htr0) hSO
  exact ⟨P, fun t u s ht hu ct cu hct hcu =>
    (trT_selCupFun Q tr0 htr0 2 1 rfl _ _).symm.trans (hP t u s ht hu ct cu hct hcu)⟩

/-! ### `StrictOrth` is an extra input -/

section Counterexample

/-- A constant complex over `ℚ` with zero differentials. -/
abbrev constZ (V : Type) [AddCommGroup V] [Module ℚ V] : GCx ℚ where
  X _ := ModuleCat.of ℚ V
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- A constant chain map between constant complexes. -/
abbrev zHom {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (φ : V →ₗ[ℚ] W) : GHom (constZ V) (constZ W) where
  f _ _ _ := φ
  comm _ _ _ _ _ _ _ _ _ := map_zero φ

/-- The constant pairing by a bilinear form `β` on `ℚ²`. All differentials are zero, so the
Leibniz rule is trivial. -/
def formCupL (β : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ) :
    GPair (constZ (Fin 2 → ℚ)) (constZ (Fin 2 → ℚ)) (constZ ℚ) where
  P _ _ _ _ := β
  leib _ _ _ _ _ _ _ _ _ _ x y := by
    change (0 : ℚ) = β 0 y + _ • β x 0
    simp

/-- The zero pairing. -/
def cexCupG : GPair (constZ (Fin 2 → ℚ)) (constZ (Fin 2 → ℚ)) (constZ ℚ) where
  P _ _ _ _ := 0
  leib _ _ _ _ _ _ _ _ _ _ _ _ := by
    change (0 : ℚ) = 0 + _ • (0 : ℚ)
    simp

/-- Selmer data with `G = U = L = ℚ²`, `res = 0`, `ι = id`. -/
def cexD : SelData ℚ :=
  ⟨constZ (Fin 2 → ℚ), constZ (Fin 2 → ℚ), constZ (Fin 2 → ℚ), zHom 0, zHom LinearMap.id⟩

/-- The strict condition `ℚ → ℚ²`, `c ↦ (c, 0)`. -/
def cexF : GHom (constZ ℚ) cexD.U := zHom (LinearMap.single ℚ (fun _ : Fin 2 => ℚ) 0)

/-- Selmer pairing data with zero global cup product, local cup product `β` and zero isotropy
homotopy. Isotropy holds when `β (c, 0) v = 0`. -/
def formQ (β : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ)
    (hβ : ∀ c v, β (Pi.single 0 c) v = 0) : SelPairData (restrictData cexD cexF) cexD where
  E := constZ ℚ
  EL := constZ ℚ
  resE := zHom 0
  cupG := cexCupG
  cupL := formCupL β
  compat _ _ _ _ _ _ _ _ _ _ _ a b := by
    change (0 : ℚ) = β 0 0
    simp
  hU _ _ _ _ := 0
  isotropy _ _ _ _ _ _ _ _ _ _ u v := by
    exact (show (0 : ℚ) + 0 + _ • (0 : ℚ) = 0 by simp).trans (hβ u v).symm

/-- The bilinear form `(a, b) ↦ a₁ b₀` on `ℚ²`. -/
def cexForm : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
  (LinearMap.mul ℚ ℚ).compl₁₂ (LinearMap.proj 1) (LinearMap.proj 0)

/-- The counterexample pairing data: local cup product `cexForm`. -/
def cexQ : SelPairData (restrictData cexD cexF) cexD :=
  formQ cexForm fun c v => by simp [cexForm]

/-- The trace `Cone³ = ℚ × ℚ → ℚ`, the second projection. -/
def cexTr : (coneCx cexQ.resE).X 3 →ₗ[ℚ] ℚ := LinearMap.snd ℚ ℚ ℚ

/-- **`StrictOrth` is not automatic** (`PROVED`). There is Selmer pairing data over `ℚ`, with an
injective strict condition and a trace killing cone coboundaries, for which `StrictOrth` fails.
Take `t' = 1`, `u = (0, 1)`, `s = 0`: the left-hand side of `hsw` is `−1`. -/
theorem strictOrth_counterexample :
    ∃ (D : SelData ℚ) (Ustr : GCx ℚ) (f : GHom Ustr D.U) (Q : SelPairData (restrictData D f) D)
      (tr : (coneCx Q.resE).X 3 →ₗ[ℚ] ℚ),
      (∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0) ∧ (∀ n, Function.Injective (f.f n n rfl)) ∧
        ¬ StrictOrth D Ustr f Q tr := by
  refine ⟨cexD, constZ ℚ, cexF, cexQ, cexTr, fun z => ?_, fun n => ?_, fun h => ?_⟩
  · change (0 : ℚ →ₗ[ℚ] ℚ) z.1 - (0 : ℚ →ₗ[ℚ] ℚ) z.2 = 0
    exact sub_self (0 : ℚ)
  · intro a b hab
    have h0 := congrArg (fun v : Fin 2 → ℚ => v 0) hab
    change (Pi.single (0 : Fin 2) (show ℚ from a) : Fin 2 → ℚ) 0 =
      (Pi.single (0 : Fin 2) (show ℚ from b) : Fin 2 → ℚ) 0 at h0
    rw [Pi.single_eq_same, Pi.single_eq_same] at h0
    exact h0
  · have h1 := h 1 (Pi.single 1 1) 0 rfl (by
      change (0 : Fin 2 → ℚ) = Pi.single 0 0
      simp)
    have h2 := (lhs_eq cexD (constZ ℚ) cexF cexQ cexTr (cexF.f 1 1 rfl 1) (Pi.single 1 1)
      0).symm.trans h1
    change (0 : ℚ →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ) 0 (Pi.single 0 1) -
      (Pi.single (1 : Fin 2) (1 : ℚ) : Fin 2 → ℚ) 1 *
        (Pi.single (0 : Fin 2) (1 : ℚ) : Fin 2 → ℚ) 0 = 0 at h2
    simp at h2

/-- The symmetric form `(a, b) ↦ a₁ b₁` on `ℚ²`. It kills `(c, 0)` on both sides. -/
def symForm : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
  (LinearMap.mul ℚ ℚ).compl₁₂ (LinearMap.proj 1) (LinearMap.proj 1)

theorem symForm_single (a : Fin 2 → ℚ) (c : ℚ) : symForm a (Pi.single 0 c) = 0 := by
  simp [symForm]

/-- Pairing data with the nonzero local cup product `symForm`. -/
def symQ : SelPairData (restrictData cexD cexF) cexD :=
  formQ symForm fun c v => by simp [symForm]

/-- **Non-vacuity of `ReverseIsotropy`**, `PROVED`. The model `symQ` has a nonzero local
cup product (`symForm (0,1) (0,1) = 1`) and reverse isotropy with `h' = 0`. -/
def symReverse : ReverseIsotropy cexD (constZ ℚ) cexF symQ where
  h11 := 0
  h21 := 0
  h12 := 0
  iso u t' := by
    exact (show (0 : ℚ) + 0 + sgn 1 • (0 : ℚ) = 0 by rw [smul_zero, add_zero, add_zero]).trans
      (symForm_single u t').symm
  compat _ _ := rfl

theorem symForm_ne_zero : symForm (Pi.single 1 1) (Pi.single 1 1) = 1 := by simp [symForm]

/-- The trace for `symQ`. -/
def cexTr' : (coneCx symQ.resE).X 3 →ₗ[ℚ] ℚ := LinearMap.snd ℚ ℚ ℚ

/-- `StrictOrth` holds in the model `symQ` (from `symReverse`). `PROVED`. -/
theorem strictOrth_symQ : StrictOrth cexD (constZ ℚ) cexF symQ cexTr' :=
  strictOrth_of_reverseIsotropy cexD (constZ ℚ) cexF symQ cexTr'
    (fun z => by
      change (0 : ℚ →ₗ[ℚ] ℚ) z.1 - (0 : ℚ →ₗ[ℚ] ℚ) z.2 = 0
      exact sub_self (0 : ℚ))
    symReverse

end Counterexample

end ZInQ.Contrib.CloudB3RC53.Hsw
