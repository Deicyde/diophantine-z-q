"""Symbolic auxiliary primes.  An instance is the list of odd primes of beta and of theta with their
true Legendre data.  An auxiliary prime q is specified symbolically by its class mod 8 and the
symbols sigma_p = [q/p] for p | beta theta (Dirichlet + CRT realise any such data; reciprocity
fixes [p/q]).  Several auxiliary primes also need their mutual symbols."""
import symsel


def build_cfg(base_primes, base_L, aux):
    """base_primes: list of odd primes (actual integers); base_L their Legendre matrix (bits);
    aux: list of dicts {mod8, sigma: list of bits over base primes, tau: list of bits [q_j/q_i] for
    earlier aux j}.  Returns a symsel config for d = prod base * prod aux."""
    k0 = len(base_primes)
    lam = [symsel.legbit(-1, p) for p in base_primes]
    mu = [symsel.legbit(2, p) for p in base_primes]
    dm = 1
    for p in base_primes:
        dm = dm * p % 8
    for a in aux:
        dm = dm * a["mod8"] % 8
        lam.append(1 if a["mod8"] in (3, 7) else 0)
        mu.append(1 if a["mod8"] in (3, 5) else 0)
    k = k0 + len(aux)
    L = [[0] * k for _ in range(k)]
    for i in range(k0):
        for j in range(k0):
            L[i][j] = base_L[i][j]
    for t, a in enumerate(aux):
        qi = k0 + t
        for i in range(k0):
            L[i][qi] = a["sigma"][i]                       # [q/p]
            L[qi][i] = a["sigma"][i] ^ (lam[i] & lam[qi])  # [p/q] by reciprocity
        for s in range(t):
            qj = k0 + s
            L[qi][qj] = a["tau"][s]                         # [q_s/q_t]
            L[qj][qi] = a["tau"][s] ^ (lam[qi] & lam[qj])
    return (dm, lam, mu, L)


def base_L(primes):
    k = len(primes)
    return [[0 if i == j else symsel.legbit(primes[j], primes[i]) for j in range(k)] for i in range(k)]


def good_cfg(cfg, umask):
    """dim Sel2 = 3 and the class with u = umask (a0 = 0) is a first coordinate."""
    if cfg[0] not in (5, 7):
        return False
    rows, n = symsel.equations(cfg)
    if len(symsel.kernel(rows, n)) != 3:
        return False
    return symsel.has_first(cfg, umask)
