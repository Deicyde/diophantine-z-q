import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-I6-rest/Inflation.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-I6-rest: inflation `H²(ℤ/f, M) → H²(ℤ/2f, M)` vanishes when `2M = 0`

pkg-I6 B2 glue item 1 (`[ε]_p = 0` at unramified `p`), finite-group part, on explicit
inhomogeneous 2-cochains with trivial coefficients.  For a 2-cocycle `c` of `ℤ/f`, with
`S(m) = Σ_{j<m} c(1, j)`, one has `c(a, b) = c(0,0) − S(a) − S(b) + S(a+b)` for natural `a, b`
(induction on `a` from the cocycle identity), hence `S(m + f) = S(m) + S(f)`, hence
`S(m + 2f) = S(m)` when `2M = 0`; so the inflated cocycle is the coboundary of
`x ↦ c(0,0) − S(x.val)` on `ℤ/2f`.
-/

namespace GlueI6Rest

variable {M : Type} [AddCommGroup M] {f : ℕ} [NeZero f]

/-- Inhomogeneous 2-cocycle condition, trivial action. -/
def IsCocycleTriv (c : ZMod f → ZMod f → M) : Prop :=
  ∀ a b d : ZMod f, c b d - c (a + b) d + c a (b + d) - c a b = 0

/-- `S(m) = Σ_{j<m} c(1, j)`. -/
def cocS (c : ZMod f → ZMod f → M) (m : ℕ) : M :=
  ∑ j ∈ Finset.range m, c 1 (j : ZMod f)

lemma cocycle_zero_left {c : ZMod f → ZMod f → M} (hc : IsCocycleTriv c) (b : ZMod f) :
    c 0 b = c 0 0 := by
  have := hc 0 0 b
  simp only [zero_add] at this
  exact sub_eq_zero.mp (by simpa using this)

lemma cocycle_eq {c : ZMod f → ZMod f → M} (hc : IsCocycleTriv c) (a b : ℕ) :
    c (a : ZMod f) (b : ZMod f) = c 0 0 - cocS c a - cocS c b + cocS c (a + b) := by
  induction a with
  | zero => simp [cocS, cocycle_zero_left hc]
  | succ n ih =>
    have h := hc 1 (n : ZMod f) (b : ZMod f)
    have e1 : ((n + 1 : ℕ) : ZMod f) = 1 + (n : ZMod f) := by push_cast; ring
    have e2 : cocS c (n + 1) = cocS c n + c 1 (n : ZMod f) := by
      simp [cocS, Finset.sum_range_succ]
    have e3 : cocS c (n + 1 + b) = cocS c (n + b) + c 1 ((n : ZMod f) + b) := by
      rw [show n + 1 + b = (n + b) + 1 by omega]
      simp [cocS, Finset.sum_range_succ]
    have h' : c (1 + (n : ZMod f)) b = c n b + c 1 ((n : ZMod f) + b) - c 1 n := by
      rw [← sub_eq_zero, ← neg_eq_zero, ← h]; abel
    rw [e1, e2, e3, h', ih]; abel

lemma cocS_add_f {c : ZMod f → ZMod f → M} (hc : IsCocycleTriv c) (m : ℕ) :
    cocS c (m + f) = cocS c m + cocS c f := by
  have h := cocycle_eq hc f m
  rw [ZMod.natCast_self, cocycle_zero_left hc] at h
  rw [add_comm m f]
  calc cocS c (f + m)
      = (c 0 0 - cocS c f - cocS c m + cocS c (f + m)) - c 0 0 + cocS c f + cocS c m := by abel
    _ = c 0 0 - c 0 0 + cocS c f + cocS c m := by rw [← h]
    _ = cocS c m + cocS c f := by abel

lemma cocS_add_two_f {c : ZMod f → ZMod f → M} (hc : IsCocycleTriv c)
    (h2 : ∀ x : M, x + x = 0) (r q : ℕ) : cocS c (r + 2 * f * q) = cocS c r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show r + 2 * f * (q + 1) = (r + 2 * f * q) + f + f by ring, cocS_add_f hc,
      cocS_add_f hc, ih, add_assoc, h2, add_zero]

/-- **Inflation from `ℤ/f` to `ℤ/2f` kills `H²` with coefficients killed by `2`.**  Every
2-cocycle of `ℤ/f`, pulled back along `ℤ/2f → ℤ/f`, is a coboundary. -/
theorem inflation_two_eq_coboundary {c : ZMod f → ZMod f → M} (hc : IsCocycleTriv c)
    (h2 : ∀ x : M, x + x = 0) :
    ∃ h : ZMod (2 * f) → M, ∀ x y : ZMod (2 * f),
      c (ZMod.castHom (Dvd.intro_left 2 rfl) (ZMod f) x)
        (ZMod.castHom (Dvd.intro_left 2 rfl) (ZMod f) y) = h x + h y - h (x + y) := by
  have : NeZero (2 * f) := ⟨by have := NeZero.ne f; omega⟩
  refine ⟨fun x => c 0 0 - cocS c x.val, fun x y => ?_⟩
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [cocycle_eq hc]
  have hv : cocS c (x.val + y.val) = cocS c (x + y).val := by
    rw [ZMod.val_add, ← cocS_add_two_f hc h2 ((x.val + y.val) % (2 * f)) ((x.val + y.val) / (2 *
        f)),
      Nat.mod_add_div]
  rw [hv]
  abel

end GlueI6Rest

