def cub {K : Type*} [Field K] (u v w : Fin 3 → K) : Fin 7 → K :=
  ![u 0 * v 0 * w 0,
    u 0 * v 0 * w 1 + u 0 * v 1 * w 0 + u 1 * v 0 * w 0,
    u 0 * v 0 * w 2 + u 0 * v 1 * w 1 + u 0 * v 2 * w 0 + u 1 * v 0 * w 1 + u 1 * v 1 * w 0 + u 2 * v 0 * w 0,
    u 0 * v 1 * w 2 + u 0 * v 2 * w 1 + u 1 * v 0 * w 2 + u 1 * v 1 * w 1 + u 1 * v 2 * w 0 + u 2 * v 0 * w 1 + u 2 * v 1 * w 0,
    u 0 * v 2 * w 2 + u 1 * v 1 * w 2 + u 1 * v 2 * w 1 + u 2 * v 0 * w 2 + u 2 * v 1 * w 1 + u 2 * v 2 * w 0,
    u 1 * v 2 * w 2 + u 2 * v 1 * w 2 + u 2 * v 2 * w 1,
    u 2 * v 2 * w 2]
