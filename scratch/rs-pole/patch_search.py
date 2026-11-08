"""One-off patch: cache 2-adic/3-adic/real local images and replace search_n by a prefiltered,
breadth-first search (few auxiliary primes first, across all multipliers m)."""
s = open('selmer_descent.py').read()
s = s.replace('''def local_image(N, a, b, p, rng, want):''', '''_IMG_CACHE = {}


def local_image(N, a, b, p, rng, want):
    if p in (0, 2, 3):
        key = (a, b, p, sqclass(N, p) if p else (N > 0,))
        if key not in _IMG_CACHE:
            _IMG_CACHE[key] = _local_image(N, a, b, p, rng, want)
        return _IMG_CACHE[key]
    return _local_image(N, a, b, p, rng, want)


def _local_image(N, a, b, p, rng, want):''', 1)
start = s.index('def search_n(')
end = s.index('if __name__ == "__main__":')
new = '''def legendre(a, p):
    return pow(a % p, (p - 1) // 2, p) == 1


def search_n(B, a, b, rng, primes, max_aux=3, budget=120):
    """Search m | 2730 (m > 0) and n = beta * n' (n' a product of <= max_aux auxiliary primes)
    with E_n, E_{n theta} both Selmer-minimal containing a class with first coordinate beta.
    Auxiliary primes are prefiltered by necessary local conditions at odd primes."""
    import time
    t0 = time.time()
    divs = [d for d in range(1, 2731) if 2730 % d == 0]
    data = []
    for m in divs:
        beta = core(m * B)
        theta = core(m * (m - B))
        if beta <= 1:
            continue
        bp = [p for p in factor_primes(beta) if p > 3]
        pool = [q for q in primes if beta % q and theta % q and q > 3
                and (legendre(beta, q) or legendre(-beta, q))]
        data.append((m, beta, theta, bp, pool))
    for k in range(0, max_aux + 1):
        for m, beta, theta, bp, pool in data:
            for combo in itertools.combinations(pool[:12], k):
                if time.time() - t0 > budget:
                    return 'timeout'
                nprime = 1
                for q in combo:
                    nprime *= q
                if not all(legendre(nprime, p) or legendre(-nprime, p) for p in bp):
                    continue
                n = beta * nprime
                try:
                    d1, g1, k1 = selmer_dim(n, a, b, rng)
                    if d1 != 3 or not class_with_first(g1, k1, beta):
                        continue
                    d2, g2, k2 = selmer_dim(n * theta, a, b, rng)
                    if d2 != 3 or not class_with_first(g2, k2, beta):
                        continue
                except RuntimeError as e:
                    print('  local image failure:', e, flush=True)
                    continue
                return m, beta, theta, combo, round(time.time() - t0, 1)
    return None


'''
s = s[:start] + new + s[end:]
open('selmer_descent.py', 'w').write(s)
