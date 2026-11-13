open Polynomial in
def trP {K : Type*} [Field K] (v : Fin 7 → K) : Fin 7 → Polynomial K :=
  ![C (v 0) + C (v 1) * X + C (v 2) * X ^ 2 + C (v 3) * X ^ 3 + C (v 4) * X ^ 4 + C (v 5) * X ^ 5 + C (v 6) * X ^ 6,
    C (v 1) + 2 * C (v 2) * X + 3 * C (v 3) * X ^ 2 + 4 * C (v 4) * X ^ 3 + 5 * C (v 5) * X ^ 4 + 6 * C (v 6) * X ^ 5,
    C (v 2) + 3 * C (v 3) * X + 6 * C (v 4) * X ^ 2 + 10 * C (v 5) * X ^ 3 + 15 * C (v 6) * X ^ 4,
    C (v 3) + 4 * C (v 4) * X + 10 * C (v 5) * X ^ 2 + 20 * C (v 6) * X ^ 3,
    C (v 4) + 5 * C (v 5) * X + 15 * C (v 6) * X ^ 2,
    C (v 5) + 6 * C (v 6) * X,
    C (v 6)]
