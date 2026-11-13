
/-! ## M3 identities proved by `ring` -/

namespace PkgI1
open T28SO3

set_option maxHeartbeats 40000000 in
theorem m3_a113 {K : Type*} [Field K] [CharZero K] (f : Fin 7 → K) :
    p6 f (cub (yv f 0) (yv f 0) (yv f 2)) = m3a113 (J2 f) (J4 f) (J6 f) (J10 f) := by
  rw [J10_eq]
  simp only [pair, p6, cub, yv, Matrix.cons_val, y1c0, y1c1, y1c2, y3c0, y3c0_0, y3c0_1, y3c0_2, y3c0_3, y3c0_4, y3c1, y3c1_0, y3c1_1, y3c1_2, y3c1_3, y3c1_4, y3c2, y3c2_0, y3c2_1, y3c2_2, y3c2_3, y3c2_4, m3a113, J2, J4, J6, J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9]
  ring

end PkgI1

