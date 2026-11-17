import Mathlib
theorem alg1 : ∀ (u Ku Kii lam v δ e1 e2 : ZMod 2), u = e1 → v = e2 →
    δ * lam + (Ku + Kii * u) = e1 * Kii + e2 * lam → Ku + lam * v = δ * lam := by decide
example (x y : ZMod 2) (h : x + y = 0) : x = y := by
  linear_combination (norm := (ring_nf; reduce_mod_char)) h
