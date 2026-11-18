import ZInQKernel.Contrib.OneProof.RC.Wiring.TraceModelRel
import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.RedeiWitness

/-!
# A corrected trace model with a NONZERO reading (non-vacuity of `TraceModelRel`)

Consistency check, not part of the manuscript (LESSON 2). RC0's only witnesses of `TraceModelRel`
and `ConstituentModelRel` (`TraceModelRel.zero`, `ConstituentModelRel.zero`) have the zero reading.
Here, for every type data `T` over `𝔽₂`, every budget and every even `a_p`, `redeiTraceModel` is a
`TraceModelRel` whose reading is the Rédei reading `R(W) = det` (over `𝔽₂`) of the Rédei matrix of
the typed graph of `W` (`EvenUpper/RedeiWitness.lean`). It reads one at `{3}` for the sign type
data (`redeiR_three`), so the reading is nonzero (`traceModelRel_nonzero`). All `PROVED`.

Construction:
* group `G = 𝔽₂ × (ℕ → 𝔽₂)` (type and Legendre coordinates), elementary abelian; `frob q` is the
  type of `q` and its bits `(q/s)`. `N_U`, the characters, `N_anti`, `N_chi`, `kummer`,
  `chi_surj` (at every `U`), and Chebotarev in `G/N_U` (batch 3's `realizeNat`) are as in RC0's
  zero model;
* the value function `f_U(g)` is the Rédei symbol of the typed graph of `U` plus one abstract
  vertex carrying the labels of `g`. Its reverse bits come from reciprocity. The function factors
  through `G/N_U`, and `f_U(1) = 0` by primary isolation;
* module `M = (Finset ℕ → 𝔽₂)²`, `F_U = (e_U, 0)`, `t(g)(a, b) = (0, U ↦ a(U) f_U(g))`,
  `d = id`, `read_U(a, b) = b(U)`:
  * `t ∘ t = 0` gives `two_fresh`; with `g h⁻¹ = g h`, it also gives `trace_mul`;
  * `t(1) = 0 = 2` gives `trace_one`;
* `reading`: `R(U ∪ {q}) = f_U(Fr_q)` (`redeiR_insert`, an isomorphism of typed graphs);
* `o12` with `κ₀ = 1`, `τ` the flip at `p`, `φ = Fr_p`:
  * the right side is `f_U(gτ) + f_U(g) = f_{U∖p}(gφ)` by the Rédei contraction rule
    (`fval_o12`);
  * the left side is `(C_p(−1) − C_p(1)) f_{U∖p}(gφ) = f_{U∖p}(gφ)` by RC12's `cp_sum_odd`
    (even `a_p`).

No field of `TraceModelRel` is unsatisfiable with a nonzero reading.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TraceWitness

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.Wiring
  ZInQ.Contrib.CloudB3RC53.CoefficientDictionary ZInQ.Contrib.CloudB3RC53.EvenUpper Finset

/-- The witness group `𝔽₂ × (ℕ → 𝔽₂)` (type and Legendre coordinates). -/
abbrev Gw : Type := Multiplicative (ZMod 2 × (ℕ → ZMod 2))

/-- The type coordinate. -/
def typeOf (g : Gw) : ZMod 2 := (Multiplicative.toAdd g).1

/-- The Legendre coordinate at `s`. -/
def bitOf (g : Gw) (s : ℕ) : ZMod 2 := (Multiplicative.toAdd g).2 s

@[simp] theorem typeOf_mul (g h : Gw) : typeOf (g * h) = typeOf g + typeOf h := rfl
@[simp] theorem bitOf_mul (g h : Gw) (s : ℕ) : bitOf (g * h) s = bitOf g s + bitOf h s := rfl
@[simp] theorem typeOf_one : typeOf 1 = 0 := rfl
@[simp] theorem bitOf_one (s : ℕ) : bitOf 1 s = 0 := rfl
@[simp] theorem typeOf_ofAdd (x : ZMod 2 × (ℕ → ZMod 2)) : typeOf (Multiplicative.ofAdd x) = x.1 :=
  rfl
@[simp] theorem bitOf_ofAdd (x : ZMod 2 × (ℕ → ZMod 2)) (s : ℕ) :
    bitOf (Multiplicative.ofAdd x) s = x.2 s := rfl

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- The witness group has exponent two. -/
theorem inv_eq_self (h : Gw) : h⁻¹ = h := by
  apply Multiplicative.toAdd.injective
  show -Multiplicative.toAdd h = Multiplicative.toAdd h
  refine Prod.ext ?_ (funext fun s => ?_)
  · show -(Multiplicative.toAdd h).1 = _
    rcases zmod2_cases (Multiplicative.toAdd h).1 with e | e <;> rw [e] <;> decide
  · show -(Multiplicative.toAdd h).2 s = _
    rcases zmod2_cases ((Multiplicative.toAdd h).2 s) with e | e <;> rw [e] <;> decide

/-- A vertex name outside `U`. -/
def star (U : Finset ℕ) : ℕ := U.sup id + 1

theorem star_not_mem (U : Finset ℕ) : star U ∉ U := fun h => by
  have := Finset.le_sup (f := id) h
  simp only [star, id] at this
  omega

variable {ε : ZMod 2 →+ ZMod 2}

/-- The typed graph of `U` with one abstract vertex carrying the labels of `g`. -/
def cfg (T : TypeData (ZMod 2) ε) (U : Finset ℕ) (g : Gw) : Config (ZMod 2) where
  V := insert (star U) U
  t := fun v => if v = star U then typeOf g else T.typ v
  z := fun a b => if a = star U then bitOf g b else
    if b = star U then bitOf g a + ε (T.typ a) * ε (typeOf g) else legBit a b

/-- The value function: the Rédei symbol of `cfg U g`. -/
def fval (T : TypeData (ZMod 2) ε) (U : Finset ℕ) (g : Gw) : ZMod 2 :=
  redei (AddMonoidHom.id (ZMod 2)) (cfg T U g)

theorem fval_congr (T : TypeData (ZMod 2) ε) (U : Finset ℕ) {g g' : Gw}
    (ht : typeOf g = typeOf g') (hb : ∀ s ∈ U, bitOf g s = bitOf g' s) :
    fval T U g = fval T U g' := by
  unfold fval
  apply redei_iso
  refine isIso_of_map id (Set.injOn_id _) (by simp [cfg]) ?_ ?_
  · intro x _
    simp only [cfg, id]
    split_ifs <;> simp_all
  · intro x hx y hy hxy
    have hU := star_not_mem U
    simp only [cfg, id, Finset.mem_insert] at hx hy ⊢
    by_cases hxs : x = star U
    · subst hxs
      rcases hy with rfl | hy
      · exact absurd rfl hxy
      · simp [hb y hy]
    · by_cases hys : y = star U
      · subst hys
        rcases hx with rfl | hx
        · exact absurd rfl hxs
        · simp [hxs, hb x hx, ht]
      · simp [hxs, hys]

theorem fval_one (T : TypeData (ZMod 2) ε) (U : Finset ℕ) : fval T U 1 = 0 := by
  unfold fval
  refine redei_isolation _ (v := star U) (Finset.mem_insert_self _ _) (by simp [cfg]) ?_
  intro w _ hw
  simp [cfg]

/-- The Frobenius element of a prime: its type and its Legendre bits. -/
def frobOf (T : TypeData (ZMod 2) ε) (q : ℕ) : Gw :=
  Multiplicative.ofAdd (T.typ q, fun s => legBit q s)

/-- The Rédei reading on prime sets. -/
def redeiR (T : TypeData (ZMod 2) ε) (W : Finset ℕ) : ZMod 2 :=
  redei (AddMonoidHom.id (ZMod 2)) (primeConfig W T.typ)

/-- **The reading of a fresh prime is the value at its Frobenius** (`PROVED`). -/
theorem redeiR_insert (T : TypeData (ZMod 2) ε) {U : Finset ℕ} {q : ℕ}
    (hU : ∀ s ∈ U, T.Good s) (hq : T.Good q) (hqU : q ∉ U) :
    redeiR T (insert q U) = fval T U (frobOf T q) := by
  classical
  unfold redeiR fval
  apply redei_iso
  have hsU := star_not_mem U
  let m : ℕ → ℕ := fun x => if x = q then star U else x
  have hm_q : m q = star U := by simp [m]
  have hm_U : ∀ x ∈ U, m x = x := fun x hx => by
    have : x ≠ q := fun h => hqU (h ▸ hx)
    simp [m, this]
  refine isIso_of_map m ?_ ?_ ?_ ?_
  · intro x hx y hy hxy
    simp only [primeConfig, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · rw [hm_q, hm_U y hy] at hxy; exact absurd (hxy ▸ hy) hsU
    · rw [hm_q, hm_U x hx] at hxy; exact absurd (hxy.symm ▸ hx) hsU
    · rwa [hm_U x hx, hm_U y hy] at hxy
  · show insert (star U) U = (insert q U).image m
    rw [Finset.image_insert, hm_q, Finset.image_congr (g := id) hm_U, Finset.image_id]
  · intro x hx
    simp only [primeConfig, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simp [cfg, hm_q, frobOf, primeConfig]
    · have : x ≠ star U := fun h => hsU (h ▸ hx)
      simp [cfg, hm_U x hx, this, primeConfig]
  · intro x hx y hy hxy
    simp only [primeConfig, Finset.mem_insert] at hx hy ⊢
    rcases hx with hxq | hx <;> rcases hy with hyq | hy
    · exact absurd (hxq.trans hyq.symm) hxy
    · subst hxq
      have : y ≠ star U := fun h => hsU (h ▸ hy)
      simp [cfg, hm_q, hm_U y hy, frobOf]
    · subst hyq
      have hxs : x ≠ star U := fun h => hsU (h ▸ hx)
      simp only [cfg, hm_q, hm_U x hx, hxs, ↓reduceIte, bitOf_ofAdd, typeOf_ofAdd, frobOf]
      rw [T.legBit_rev (hU x hx) hq hxy]
    · have hxs : x ≠ star U := fun h => hsU (h ▸ hx)
      have hys : y ≠ star U := fun h => hsU (h ▸ hy)
      simp [cfg, hm_U x hx, hm_U y hy, hxs, hys]


/-- The inertia element at `p`: it flips only the Legendre coordinate at `p`. -/
def tauOf (p : ℕ) : Gw := Multiplicative.ofAdd (0, Pi.single p 1)

/-- **The contraction step of (O.12) for the value function** (`PROVED`, from the contraction rule
of the Rédei symbol): `f_U(gτ) + f_U(g) = f_{U∖p}(g φ_p)`. -/
theorem fval_o12 (T : TypeData (ZMod 2) ε) {U : Finset ℕ} {p : ℕ} (hp : p ∈ U)
    (hU : ∀ s ∈ U, T.Good s) (g : Gw) :
    fval T U (g * tauOf p) + fval T U g = fval T (U.erase p) (g * frobOf T p) := by
  classical
  have hsU := star_not_mem U
  have hsp : star U ≠ p := fun h => hsU (h ▸ hp)
  have hc := redei_contraction (AddMonoidHom.id (ZMod 2)) (cfg T U g) (v := star U) (w := p)
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hp) hsp
  -- the flip is the configuration of `gτ`
  have hflip : redei (AddMonoidHom.id (ZMod 2)) ((cfg T U g).flip (star U) p) =
      fval T U (g * tauOf p) := by
    unfold fval
    apply redei_iso
    refine isIso_of_map id (Set.injOn_id _) (by simp [cfg, Config.flip, Config.flipBy]) ?_ ?_
    · intro x _
      simp [cfg, Config.flip, Config.flipBy, tauOf]
    · intro x hx y hy hxy
      simp only [Config.flip, Config.flipBy, cfg, Finset.mem_insert, id] at hx hy ⊢
      rcases hx with hxs | hx <;> rcases hy with hys | hy
      · exact absurd (hxs.trans hys.symm) hxy
      · subst hxs
        have hy' : y ≠ star U := fun h => hsU (h ▸ hy)
        by_cases hyp : y = p
        · subst hyp; simp [tauOf, hsp]
        · simp [tauOf, hy', hyp, hsp]
      · subst hys
        have hx' : x ≠ star U := fun h => hsU (h ▸ hx)
        by_cases hxp : x = p
        · subst hxp; simp [tauOf, hx']; ring
        · simp [tauOf, hx', hxp]
      · have hx' : x ≠ star U := fun h => hsU (h ▸ hx)
        have hy' : y ≠ star U := fun h => hsU (h ▸ hy)
        simp [hx', hy']
  -- the contraction is the configuration of `gφ_p` on `U ∖ p`
  have hcon : redei (AddMonoidHom.id (ZMod 2)) ((cfg T U g).contract (star U) p) =
      fval T (U.erase p) (g * frobOf T p) := by
    unfold fval
    apply redei_iso
    have hsU' := star_not_mem (U.erase p)
    let m : ℕ → ℕ := fun x => if x = star U then star (U.erase p) else x
    have hm_s : m (star U) = star (U.erase p) := by simp [m]
    have hm_U : ∀ x ∈ U, m x = x := fun x hx => by
      have : x ≠ star U := fun h => hsU (h ▸ hx)
      simp [m, this]
    have hV : ((cfg T U g).contract (star U) p).V = insert (star U) (U.erase p) := by
      simp only [Config.contract, cfg]
      rw [Finset.erase_insert_of_ne hsp]
    have hmemU' : ∀ {x}, x ∈ U.erase p → x ∈ U := fun h => Finset.mem_of_mem_erase h
    have hct : ∀ x, ((cfg T U g).contract (star U) p).t x =
        Function.update (cfg T U g).t (star U) ((cfg T U g).t (star U) + (cfg T U g).t p) x :=
      fun _ => rfl
    have hcz : ∀ a b, ((cfg T U g).contract (star U) p).z a b =
        if a = star U then (cfg T U g).z (star U) b + (cfg T U g).z p b else
          if b = star U then (cfg T U g).z a (star U) + (cfg T U g).z a p else (cfg T U g).z a b :=
      fun _ _ => rfl
    have hps : p ≠ star U := Ne.symm hsp
    refine isIso_of_map m ?_ ?_ ?_ ?_
    · intro x hx y hy hxy
      rw [hV] at hx hy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with hxs | hx <;> rcases hy with hys | hy
      · exact hxs.trans hys.symm
      · rw [hxs, hm_s, hm_U y (hmemU' hy)] at hxy; exact absurd (hxy ▸ hy) hsU'
      · rw [hys, hm_s, hm_U x (hmemU' hx)] at hxy; exact absurd (hxy.symm ▸ hx) hsU'
      · rwa [hm_U x (hmemU' hx), hm_U y (hmemU' hy)] at hxy
    · rw [hV]
      show insert (star (U.erase p)) (U.erase p) = _
      rw [Finset.image_insert, hm_s, Finset.image_congr (g := id) (fun x hx => hm_U x (hmemU' hx)),
        Finset.image_id]
    · intro x hx
      rw [hV, Finset.mem_insert] at hx
      rw [hct]
      rcases hx with rfl | hx
      · rw [hm_s, Function.update_self]
        simp [cfg, hps, frobOf]
      · have hxs : x ≠ star U := fun h => hsU (h ▸ hmemU' hx)
        have hxs' : x ≠ star (U.erase p) := fun h => hsU' (h ▸ hx)
        rw [hm_U x (hmemU' hx), Function.update_of_ne hxs]
        simp [cfg, hxs, hxs']
    · intro x hx y hy hxy
      rw [hV, Finset.mem_insert] at hx hy
      rw [hcz]
      rcases hx with hxs | hx <;> rcases hy with hys | hy
      · exact absurd (hxs.trans hys.symm) hxy
      · subst hxs
        have hys : y ≠ star U := fun h => hsU (h ▸ hmemU' hy)
        have hys' : y ≠ star (U.erase p) := fun h => hsU' (h ▸ hy)
        rw [hm_s, hm_U y (hmemU' hy)]
        simp [cfg, hys, hps, frobOf]
      · subst hys
        have hxs : x ≠ star U := fun h => hsU (h ▸ hmemU' hx)
        have hxs' : x ≠ star (U.erase p) := fun h => hsU' (h ▸ hx)
        have hxp : x ≠ p := Finset.ne_of_mem_erase hx
        rw [hm_s, hm_U x (hmemU' hx)]
        simp only [cfg, hxs, hxs', hps, ↓reduceIte, bitOf_mul, typeOf_mul, frobOf, bitOf_ofAdd,
          typeOf_ofAdd, map_add]
        rw [T.legBit_rev (hU x (hmemU' hx)) (hU p hp) hxp]
        ring
      · have hxs : x ≠ star U := fun h => hsU (h ▸ hmemU' hx)
        have hys : y ≠ star U := fun h => hsU (h ▸ hmemU' hy)
        have hxs' : x ≠ star (U.erase p) := fun h => hsU' (h ▸ hx)
        have hys' : y ≠ star (U.erase p) := fun h => hsU' (h ▸ hy)
        rw [hm_U x (hmemU' hx), hm_U y (hmemU' hy)]
        simp [cfg, hxs, hys, hxs', hys']
  rw [hflip, hcon] at hc
  rw [add_comm, ← hc]
  rfl


/-- The reduced module of the witness: `F_U` in the first factor, the values in the second. -/
abbrev Mw : Type := (Finset ℕ → ZMod 2) × (Finset ℕ → ZMod 2)

/-- The trace operator: `t(g)(a, b) = (0, U ↦ a(U) f_U(g))`. -/
def tw (T : TypeData (ZMod 2) ε) (g : Gw) : Mw →ₗ[ZMod 2] Mw where
  toFun x := (0, fun U => x.1 U * fval T U g)
  map_add' x y := Prod.ext (by simp) (funext fun U => by simp [add_mul])
  map_smul' c x := Prod.ext (by simp) (funext fun U => by simp [mul_assoc])

@[simp] theorem tw_apply (T : TypeData (ZMod 2) ε) (g : Gw) (x : Mw) :
    tw T g x = (0, fun U => x.1 U * fval T U g) := rfl

/-- The forms `F_U`. -/
def Fw (U : Finset ℕ) : Mw := (Pi.single U 1, 0)

/-- The reading functionals. -/
def readw (U : Finset ℕ) : Mw →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj U).comp (LinearMap.snd _ _ _)

theorem readw_tw_Fw (T : TypeData (ZMod 2) ε) (U : Finset ℕ) (g : Gw) :
    readw U (tw T g (Fw U)) = fval T U g := by
  simp [readw, Fw]

theorem tw_tw (T : TypeData (ZMod 2) ε) (g h : Gw) (x : Mw) : tw T g (tw T h x) = 0 :=
  Prod.ext rfl (funext fun U => by simp)

/-- **A `TraceModelRel` of the Rédei reading** (`PROVED`): a model with a NONZERO reading (see
`redeiR_three`) for every type data over `𝔽₂`, budget and even `a_p`. -/
def redeiTraceModel (T : TypeData (ZMod 2) ε) (ap : ℕ → ℤ) (hap : ∀ p, Even (ap p)) (B : ℕ) :
    TraceModelRel T (redeiR T) ap B where
  G := Gw
  M := Mw
  t := tw T
  d _ := LinearMap.id
  F := Fw
  read := readw
  frob := frobOf T
  N := zeroN (ZMod 2)
  chiType := zeroChiType (ZMod 2)
  chiBit := zeroChiBit (ZMod 2)
  trace_mul g h x := by
    rw [tw_tw, inv_eq_self, LinearMap.id_apply]
    refine Prod.ext (by simp) (funext fun U => ?_)
    simp only [Prod.snd_add, Pi.add_apply, tw_apply, Prod.snd_zero, Pi.zero_apply]
    rw [← mul_add, EvenUpper.zmod2_add_self, mul_zero]
  det_orbit _ _ _ := rfl
  two_fresh _ _ _ := tw_tw T _ _ _
  trace_one x := by
    refine Prod.ext ?_ (funext fun U => ?_)
    · show (0 : Finset ℕ → ZMod 2) = ((2 : ZMod 2) • x).1
      rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]; rfl
    simp [fval_one, show (2 : ZMod 2) = 0 from rfl]
  level U g n hn := by
    rw [mem_zeroN] at hn
    refine Prod.ext rfl (funext fun U' => ?_)
    simp only [tw_apply, Fw]
    by_cases hUU : U' = U
    · subst hUU
      congr 1
      refine fval_congr T U' (by
        have := hn.1
        rw [zeroChiType_apply, ofAdd_eq_one] at this
        simp [typeOf, this]) fun s hs => ?_
      have := hn.2 s hs
      rw [zeroChiBit_apply, ofAdd_eq_one] at this
      simp [bitOf, this]
    · simp [Pi.single_eq_of_ne hUU]
  N_anti U U' hU' n hn := by
    rw [mem_zeroN] at hn ⊢
    exact ⟨hn.1, fun s hs => hn.2 s (hU' hs)⟩
  N_chi U n hn := mem_zeroN.mp hn
  kummer U g h1 h2 := Subgroup.mem_sup_right (mem_zeroN.mpr ⟨h1, h2⟩)
  chi_surj U _ ℓ b := ⟨Multiplicative.ofAdd (ℓ, b), rfl, fun _ _ => rfl⟩
  chebotarev U hU g avoid := by
    obtain ⟨x, -, hx, hold, -⟩ := realizeNat T U avoid hU
      (fun _ => (Multiplicative.toAdd g).1) (fun _ s => (Multiplicative.toAdd g).2 s)
      (fun _ _ => 0) 1
    obtain ⟨hq, hqU, hqa, htq⟩ := hx 0 (by norm_num)
    refine ⟨x 0, 1, g⁻¹ * frobOf T (x 0), mem_zeroN.mpr ⟨?_, fun s hs => ?_⟩, hq, hqa, by group⟩
    · rw [map_mul, map_inv, zeroChiType_apply, zeroChiType_apply, frobOf, toAdd_ofAdd, htq,
        inv_mul_cancel]
    · rw [map_mul, map_inv, zeroChiBit_apply, zeroChiBit_apply, frobOf, toAdd_ofAdd]
      dsimp only
      rw [hold 0 (by norm_num) s hs, inv_mul_cancel]
  t_class g h := by rw [mul_comm h g, mul_inv_cancel_right]
  typ_frob _ _ := rfl
  bit_frob _ _ _ _ _ := rfl
  reading U q hU hq hqU _ := by
    rw [readw_tw_Fw]
    exact redeiR_insert T hU hq hqU
  o12 U p hp hU _ g := by
    refine ⟨tauOf p, frobOf T p, 1, Or.inl rfl, ?_, fun s _ hsp => ?_, ?_, rfl,
      fun _ _ _ => rfl, ?_⟩
    · rw [zeroChiType_apply, tauOf, toAdd_ofAdd, ofAdd_zero]
    · rw [zeroChiBit_apply, tauOf, toAdd_ofAdd]
      dsimp only
      rw [Pi.single_eq_of_ne hsp, ofAdd_zero]
    · rw [zeroChiBit_apply, tauOf, toAdd_ofAdd]
      dsimp only
      rw [Pi.single_eq_same]
    · simp only [readw_tw_Fw]
      -- `τ` does not change the labels seen by `U ∖ p`
      have hτ : fval T (U.erase p) (g * tauOf p * frobOf T p) = fval T (U.erase p) (g * frobOf T p) := by
        refine fval_congr T _ (by simp [tauOf]) fun s hs => ?_
        have hsp : s ≠ p := Finset.ne_of_mem_erase hs
        simp [tauOf, Pi.single_eq_of_ne hsp]
      rw [hτ, ← fval_o12 T hp hU g]
      -- `C_p(1) + C_p(−1)` is odd for even `a_p`
      obtain ⟨-, hodd⟩ := cp_sum_odd (hap p) (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
      obtain ⟨k, hk⟩ := hodd
      have hc : ((Cp (ap p) (-1) : ℤ) : ZMod 2) = ((Cp (ap p) 1 : ℤ) : ZMod 2) + 1 := by
        have : (Cp (ap p) (-1) : ℤ) = 2 * k + 1 - Cp (ap p) 1 := by linarith
        rw [this]; push_cast
        rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
        generalize ((Cp (ap p) 1 : ℤ) : ZMod 2) = c
        revert c; decide
      rw [hc]
      generalize ((Cp (ap p) 1 : ℤ) : ZMod 2) = c
      generalize fval T U (g * tauOf p) = a
      generalize fval T U g = b
      revert a b c; decide

/-- The witness at the sign type data reads one at `{3}` (`PROVED`): the reading is nonzero. -/
theorem redeiR_three : redeiR signTypeData {3} = 1 := by
  unfold redeiR
  rw [redei_singleton _ (r := 3) rfl]
  rfl

/-- **Non-vacuity of `TraceModelRel` with a nonzero reading** (`PROVED`): for the sign type data,
`a_p = 0` and every budget there is a corrected trace model whose reading is one at `{3}`; RC0's
`coefficientRules_of_modelRel` then gives the coefficient rules for its symbol. -/
theorem traceModelRel_nonzero (B : ℕ) :
    ∃ R : Finset ℕ → ZMod 2, Nonempty (TraceModelRel signTypeData R (fun _ => 0) B) ∧
      R {3} = 1 :=
  ⟨redeiR signTypeData, ⟨redeiTraceModel signTypeData _ (fun _ => ⟨0, rfl⟩) B⟩, redeiR_three⟩

theorem coefficientRules_redeiTraceModel :
    CoefficientRules (AddMonoidHom.id (ZMod 2)) (symb signTypeData (redeiR signTypeData)) :=
  coefficientRules_of_modelRel (fun B => redeiTraceModel signTypeData _ (fun _ => ⟨0, rfl⟩) B)
    (fun _ _ => ⟨0, rfl⟩)


end ZInQ.Contrib.CloudB3RC53.TraceWitness
