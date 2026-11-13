"""t28-igusa: Lean text for M3 identities proved by `ring`. Usage: gen_m3proofs.py G11 G12 a111 ..."""
import sys
J10U = "J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9"
Y = {1: ["y1c0", "y1c1", "y1c2"], 2: ["y2c0", "y2c1", "y2c2"],
     3: ["y3c0", "y3c1", "y3c2"] + [f"y3c{k}_{m}" for k in range(3) for m in range(5)]}
deg = {1: 3, 2: 5, 3: 7}
out = ["\n/-! ## M3 identities proved by `ring` -/\n\nnamespace PkgI1\nopen T28SO3\n"]
for e in sys.argv[1:]:
    ys = [int(c) for c in e[1:]]
    if e[0] == 'G':
        lhs = f"pair (yv f {ys[0]-1}) (yv f {ys[1]-1})"; d = sum(deg[i] for i in ys)
    else:
        lhs = f"p6 f (cub (yv f {ys[0]-1}) (yv f {ys[1]-1}) (yv f {ys[2]-1}))"; d = 1 + sum(deg[i] for i in ys)
    unf = ", ".join(sorted(set(sum([Y[i] for i in ys], []))))
    uses10 = d >= 10
    pre = "  rw [J10_eq]\n" if uses10 else ""
    jun = "J2, J4, J6" + (", " + J10U if uses10 else "")
    out.append(f"""
set_option maxHeartbeats 40000000 in
theorem m3_{e} {{K : Type*}} [Field K] [CharZero K] (f : Fin 7 → K) :
    {lhs} = m3{e} (J2 f) (J4 f) (J6 f) (J10 f) := by
{pre}  simp only [pair, p6, cub, yv, Matrix.cons_val, {unf}, m3{e}, {jun}]
  ring
""")
out.append("\nend PkgI1\n")
print("".join(out))
