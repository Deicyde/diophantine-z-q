G = ["![τ, 1]", "![√2 * τ, -(√2 * 1)]", "![(τ - 3 * 1) / 2, (τ + 1) / 2]", "![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]"]
a, b = "((1 + √2) * τ)", "(1 - √2)"
H = [f"![{a}, {b}]", f"![√2 * {a}, -(√2 * {b})]", f"![({a} - 3 * {b}) / 2, ({a} + {b}) / 2]", f"![√2 * ({a} - 3 * {b}) / 2, -(√2 * ({a} + {b})) / 2]"]
fwd = {0: ({0: -1, 1: 1}, ["-τ", "-1"]), 1: ({0: 2, 1: -1}, ["τ", "1"]), 2: ({1: 1, 2: -1, 3: -1}, ["-(τ - 3)/2", "-(τ + 1)/2"]), 3: ({0: 2, 2: -2, 3: -1}, ["(τ + 3)/2", "-(τ - 1)/2"])}
rev = {0: ({0: 1, 1: 1}, ["0", "0"]), 1: ({0: 2, 1: 1}, ["τ", "1"]), 2: ({1: 1, 2: 1, 3: -1}, ["0", "0"]), 3: ({0: 2, 2: -2, 3: 1}, ["(τ + 3)/2", "-(τ - 1)/2"])}
def vec(comb, V):
    terms = []
    for j, c in comb.items():
        t = V[j] if abs(c) == 1 else f"({V[j]} + {V[j]} : Fin 2 → ℂ)"
        terms.append((c > 0, t))
    s = ("" if terms[0][0] else "-") + f"({terms[0][1]} : Fin 2 → ℂ)"
    for pos, t in terms[1:]:
        s += (" + " if pos else " - ") + f"({t} : Fin 2 → ℂ)"
    return s
def mem(comb):
    items = list(comb.items())
    def one(j, c):
        base = f"(m {j})" if abs(c) == 1 else f"(S.add_mem (m {j}) (m {j}))"
        return base
    j0, c0 = items[0]
    e = one(j0, c0) if c0 > 0 else f"(S.neg_mem {one(j0, c0)})"
    for j, c in items[1:]:
        e = f"(S.add_mem {e} {one(j, c)})" if c > 0 else f"(S.sub_mem {e} {one(j, c)})"
    return e
SIMP = "simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]"
def block(L, R, table, Sname):
    out = []
    out.append(f"    set S := Submodule.span ℤ (Set.range ![{', '.join(R)}]) with hS")
    out.append(f"    have m : ∀ j : Fin 4, (![{', '.join(R)}] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩")
    out.append("    fin_cases k")
    for k in range(4):
        comb, q = table[k]
        out.append(f"    · have e : ({L[k]} : Fin 2 → ℂ) = {vec(comb, R)} := by")
        out.append("        ext i; fin_cases i")
        out.append(f"        · {SIMP}; linear_combination ({q[0]}) * s")
        out.append(f"        · {SIMP}; linear_combination ({q[1]}) * s")
        out.append(f"      show _ ∈ S")
        out.append(f"      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢")
        out.append(f"      rw [e]; exact {mem(comb)}")
    return "\n".join(out)
print("""theorem qmOrbit_unit (τ : ℂ) : qmOrbit ![τ, 1] = qmOrbit ![(1 + √2) * τ, 1 - √2] := by
  have s := sqrt2_sq'
  apply le_antisymm
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]""")
print(block(G, H, fwd, "S"))
print("""  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]""")
print(block(H, G, rev, "S"))
