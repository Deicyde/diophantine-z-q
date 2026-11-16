# Complete Version 18 cleanup comparison

Base commit `f7b803e3252fa955ab6dcdc2ac3e756a03fde184`, manuscript SHA256 `e594eba7c9634f445185f507f05d7436ea6e6b1acc0c226051ab40e3767aee12`. Candidate manuscript SHA256 `ffb7a39bbd45fc48d5d020b24c7f50a4ca11c795be293d5649f56257c9244f9b`. All line numbers and character offsets refer to these exact UTF-8-decoded sources. This is an author-produced comparison, not an independent verdict. Both sources are available at their pinned revisions.

The previous 546 KB paragraph comparison repeated unchanged paragraphs on both sides. This record instead gives every changed word/whitespace segment, with four tokens of unchanged context. Tokens partition the original text into whitespace runs or non-whitespace runs; neither source is normalized. Every changed character is printed below. Each JSON row below has six fields: change ID; base [first line, last line, start offset, end offset]; candidate with the same four fields; exact old text; exact replacement text; and [unchanged left context, unchanged right context]. JSON escapes preserve whitespace explicitly. No changed text is omitted. Offsets are zero-based half-open Unicode-character offsets, not UTF-8 byte offsets. Line ranges are one-based. Replacing the base ranges by the candidate segments in reverse offset order reconstructs the candidate exactly; that reconstruction was checked. Full statements and their adjacent consumers remain at the linked line locations.

The classes and occurrence checks help locate edits. They are not mathematical acceptance. [The status record](version18-cleanup-status.md) retains open H170, H201 and coverage qualifications. No theorem statement or construction is claimed accepted by this comparison.

## The two source-bound symbol restorations

### F0406: `h_{*}` to `h_*` in this PR

Base line 2328; candidate line 2323. These two spellings render identically. P14 fixes the progression h=h_* mod L; P16 invokes exactly that progression in the compatible CRT conditions.

Correction to the first PR description: the damaged spelling `h_{\cdot }` occurred only in an intermediate local typography proposal and was caught before publication. It is not the base spelling and is not a mathematical correction introduced by this PR. The final edit preserves the star already present in the base. The original supplier comparison is retained below to make the identity inspectable.

Supplier: [research/quartic214/proofs/uniform-existence.md](https://github.com/elliotglazer/diophantine-z-q/blob/f7b803e3252fa955ab6dcdc2ac3e756a03fde184/research/quartic214/proofs/uniform-existence.md), SHA256 `d13cc2b846dc72a3f5b5cce8dcf11d3f11b33c45ebc3883263840afb8d82f3bc`. The following are exact project-source passages, not excerpts of an external copyrighted paper.

Source line 67:

```text
[P14: scalar finite preparation in correct order] For a particular x,N, put D_s=1+149^2 r4. Both gcd(A_N r4,D_s) and gcd(A_N r4+9792D_s,D_s) equal1; thus R_s(R_s+9792) has square reduced denominator D_s^2. Direct integer parity/congruences give v2(R_s) in {2,3} and v3(R_s)=v17(R_s)=0. Hence 1+9792/R_s is a square at2,3,17 (its difference from1 has depth>=3,>=1,>=1 respectively), so R_s(R_s+9792) is a square there. At its finite odd-valuation numerator support choose an initial H formal enough; then choose the positive scalar index a still deeper and arbitrarily large, with [a]P in the fixed real neighborhood of O. This makes the three terms of W_s integral at that support and deep enough at2,3,17 for the actual zero-preparation pole bounds. Compact-group recurrence in finite-index progressions gives the finite and real conditions together. After a is fixed, continuity preserves the scalar conditions for H in one progression h=h_* mod L, with64|h_*,64|L and the component-order divisibility included. This ordering permits support and depth to depend on x,N; the common N_C does not. The retained scalar/root chart guards hold on the chosen neighborhoods. No new condition a=1 mod any modulus is imposed.
```

Source line 71:

```text
[P16: prime theorem quantifiers and CRT] Apply the actual V15 simultaneous-prime theorem to this fixed list, prescribed divisibility q|w, fixed avoidance modulus M=rad_odd(3*17*L) with7 omitted, and arbitrarily large slope/prime lower bounds. Choose these data before the analytic asymptotic parameter (call it X_sel, distinct from input x). Its fixed-field proof first fixes the cutoff so positive cutoff mass exceeds the full obstruction tail, then fixes the ray field, then lets X_sel grow along sufficiently slow diagonal strip widths. No uniform estimate in x,N,T,D,L or number of contacts is needed. The selected Gaussian generators have residues9 mod16,1+3i mod7,i modM; adjacent norms d_minus,d_plus have v2=6,2 and cross-sign gcd4, and all odd factors avoid L. Define U=lcm(d_minus/4), V=lcm(d_plus/4). Full two-torsion makes d/4 kill the reduction of the double P; gcd(U,V)=1, gcd(U,L)=16 and gcd(V,L)=1. Thus h=0 mod U, h=1 mod V, h=h_* mod L are compatible. The real progression lemma gives arbitrarily large h in the original fixed compact neighborhoods. Set H=[h]P, U_i=[hn_i]P, V_i=[(h-1)n_i]P. This gives natural formal depth>=1 at the correct primary/opposite places and preserves the scalar data. The optional strengthened separation p_i not dividing d_j is available from the weighted strip argument; natural depth1 alone suffices for this 214 construction. Every merged repeated coefficient carries one prime/generator and all its incidences; CRT is imposed once and supplies all those incidences.
```

Candidate consumer, line 2323:

```tex
[P16: prime theorem quantifiers and CRT] Apply the actual \(V_{15}\) simultaneous-prime theorem to this fixed list, prescribed divisibility q|w, fixed avoidance modulus \(M=\operatorname{rad}_{\text{odd}}(3\cdot 17\cdot L)\) with 7 omitted, and arbitrarily large slope/prime lower bounds. Choose these data before the analytic asymptotic parameter \((\text{call} it X_{\text{sel}}, \text{distinct} \text{from} \text{input} x)\). Its fixed-field proof first fixes the cutoff so positive cutoff mass exceeds the full obstruction tail, then fixes the ray field, then lets \(X_{\text{sel}}\) grow along sufficiently slow diagonal strip widths. No uniform estimate in x,N,T,D,L or number of contacts is needed. The selected Gaussian generators have residues 9 mod 16,1+3i mod 7,i modM; adjacent norms \(d_{-},d_{+}\) have \(v_{2}=6,2\) and cross-sign gcd 4, and all odd factors avoid \(L\). Define \(U=\text{lcm}(d_{-}/4)\), \(V=\text{lcm}(d_{+}/4)\). Full two-torsion makes d/4 kill the reduction of the double \(P\); \(\text{gcd}(U,V)=1\), \(\text{gcd}(U,L)=16\) and \(\text{gcd}(V,L)=1\). Thus \(h=0\) mod \(U\), \(h=1\) mod \(V\), \(h=h_*\) mod \(L\) are compatible. The real progression lemma gives arbitrarily large \(h\) in the original fixed compact neighborhoods. Set \(H=[h]P\), \(U_{i}=[hn_{i}]P\), \(V_{i}=[(h-1)n_{i}]P\). This gives natural formal \(\operatorname{depth}\ge 1\) at the correct primary/opposite places and preserves the scalar data. The optional strengthened separation \(p_{i}\) not dividing \(d_{j}\) is available from the weighted strip argument; natural depth 1 alone suffices for this 214 construction. Every merged repeated coefficient carries one prime/generator and all its incidences; CRT is imposed once and supplies all those incidences.
```

### F0407: `j_{*}` to `j_*` in this PR

Base line 3390; candidate line 3377. These two spellings render identically. C05 preserves the integral j_* condition before mapping to the open scheme; C06 compares the full/j_* local cones.

Correction to the first PR description: the damaged spelling `j_{\cdot }` occurred only in an intermediate local typography proposal and was caught before publication. It is not the base spelling and is not a mathematical correction introduced by this PR. The final edit preserves the star already present in the base. The original supplier comparison is retained below to make the identity inspectable.

Supplier: [research/quartic214/proofs/source-carry.md](https://github.com/elliotglazer/diophantine-z-q/blob/f7b803e3252fa955ab6dcdc2ac3e756a03fde184/research/quartic214/proofs/source-carry.md), SHA256 `f7f4e550a4dcfbbd3b5ffcf783b11411f7888c821dbab7febb5132b7b2b891ed`. The following are exact project-source passages, not excerpts of an external copyrighted paper.

Source line 19:

```text
[C05: Kato required full index set] Read the actual current proof at13347–13946 and the actual earlier v11 `norms.md` and `interface.md` arguments. For a fixed constituent with primitive conductor D=2^a*d, the retained construction defines y_m=cor_{Q(zeta_Dm)/Q(zeta_m)}(z_Dm tensor e_chi) for every m with (m,c*d_s)=1. K5 makes N_K=2Nd and Nprime=c*d_s coprime. Restricting to all m divisible by N_K gives every index required by Kato1999§0.1, not merely the smaller2004§13.1 set. The class has the integral j_* condition by the inertia/Leray and Mackey calculation before mapping to the open scheme with N_K inverted. The same fixed lattice-clearing factor2^c_E applies at every level. It is a unit at the height-one localizations away from2 used downstream.
```

Source line 26:

```text
Arithmetic Frobenius acts on T*chi and inverse deck action is in the substitution; the representation is not dualized again. For every n>=1 the supports S_(D*N_K*2^n) and S_(D*2^n) equal prime(2Nd). Corestriction transitivity through the common upper field gives cor(y_(N_K*2^n))=y_(2^n), without an Euler factor or a field-degree multiplier. These equalities commute with transition maps; the cofinal dyadic inverse limit is exactly the Section0.7 divisor-parameter-one class xi_K, distinguished from the modular symbol xi. Thus the localized coordinate ideal J in K15 is the ideal of this actual retained class. Rank-one proportionality would not suffice and is not used. The full/j_* local cone comparison preserves H^1 and the same class/ideal; paying for the actual H^2 cone and fixed local factors yields K2. This source repair is incorporated already and is unchanged in214's supplier. A narrow current connection locator13775–13778 summarizes the coordinate-ideal conclusion; it is not the whole index/class argument. This carry binds the actual13799–13899 argument as well as its complete application record, so that short locator is not mistaken for the proof.
```

Candidate consumer, line 3377:

```tex
[C05: Kato required full index set] The current proof at 13347--13946 and the earlier \(v_{11}\) \nolinkurl{norms.md} and \nolinkurl{interface.md} arguments supply the construction below. For a fixed constituent with primitive conductor \(D=2^{a}\cdot d\), the retained construction defines \(y_{m}=\text{cor}_{Q(\zeta _{Dm})/Q(\zeta _{m})}(z_{Dm} \otimes e_{\chi })\) for every \(m\) with \((m,c\cdot d_{s})=1\). \(K_{5}\) makes \(N_{K}=2Nd\) and \(N'_K=c\cdot d_{s}\) coprime. Restricting to all \(m\) divisible by \(N_{K}\) gives every index required by Kato 1999\S{}0.1, not merely the smaller 2004\S{}13.1 set. The class has the integral \(j_*\) condition by the inertia/Leray and Mackey calculation before mapping to the open scheme with \(N_{K}\) inverted. The same fixed lattice-clearing \(\text{factor}2^{{c}_{E}}\) applies at every level. It is a unit at the height-one localizations away from 2 used downstream.
```


## Inline mathematical changes and whole-file rename checks

The following inventory contains every changed single-line inline mathematical span after ignoring whitespace for comparison. Complete raw spelling changes, including whitespace, are in the W-segments. A changed span is listed even when its edit is typographical; no semantic verdict is inferred. Unmatched insertions/deletions are retained.

```json
[
  {
    "before": [
      {
        "line": 2006,
        "text": "\\(V_{16}\\)"
      },
      {
        "line": 2006,
        "text": "\\(V_{16}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [],
    "after": [
      {
        "line": 2063,
        "text": "\\(L'\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 2063,
        "text": "\\(L'\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2071,
        "text": "\\(V_{16}\\)"
      },
      {
        "line": 2073,
        "text": "\\(V_{16}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2132,
        "text": "\\(N_{0}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2144,
        "text": "\\(\\text{equals}149^{4N+2}+1\\)"
      },
      {
        "line": 2144,
        "text": "\\(N\\ge 53;53\\)"
      }
    ],
    "after": [
      {
        "line": 2139,
        "text": "\\(149^{4N+2}+1\\)"
      },
      {
        "line": 2139,
        "text": "\\(N\\ge 53\\)"
      },
      {
        "line": 2139,
        "text": "\\(53\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2146,
        "text": "\\(T*\\lambda \\)"
      }
    ],
    "after": [
      {
        "line": 2141,
        "text": "\\(T\\cdot \\lambda \\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2148,
        "text": "\\(\\Theta \\)"
      }
    ],
    "after": [
      {
        "line": 2143,
        "text": "\\(\\Theta \\cup(2-\\Theta)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2154,
        "text": "\\(q*s_{1}=1\\)"
      }
    ],
    "after": [
      {
        "line": 2149,
        "text": "\\(s_1,s_2,s_4\\)"
      },
      {
        "line": 2149,
        "text": "\\(q\\cdot s_{1}=1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2154,
        "text": "\\(s_{3}=s_{1}*s_{2}\\)"
      },
      {
        "line": 2154,
        "text": "\\(q_{3}*s_{3}=1\\)"
      }
    ],
    "after": [
      {
        "line": 2149,
        "text": "\\(s_{3}=s_{1}\\cdot s_{2}\\)"
      },
      {
        "line": 2149,
        "text": "\\(q_{3}\\cdot s_{3}=1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2156,
        "text": "\\(q_{0}*q_{1}\\ne 0\\)"
      }
    ],
    "after": [
      {
        "line": 2151,
        "text": "\\(q_{0}\\cdot q_{1}\\ne 0\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 2153,
        "text": "\\(Q_0,Q_1,Q_3\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2160,
        "text": "\\(D_{r}*T=N_{r}\\)"
      }
    ],
    "after": [
      {
        "line": 2155,
        "text": "\\(D_{r}\\cdot T=N_{r}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2164,
        "text": "\\(f(H)*F_{0}=g^{2}\\)"
      }
    ],
    "after": [
      {
        "line": 2159,
        "text": "\\(f(H)\\cdot F_{0}=g^{2}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2193,
        "text": "\\(H=C_{2}*B_{\\Sigma }^{\\alpha }\\)"
      }
    ],
    "after": [
      {
        "line": 2188,
        "text": "\\(H=C_{2}\\cdot B_{\\Sigma }^{\\alpha }\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2203,
        "text": "\\(B^{2}\\le M_{1}*h(T)+M_{2}\\)"
      }
    ],
    "after": [
      {
        "line": 2198,
        "text": "\\(B^{2}\\le M_{1}\\cdot h(T)+M_{2}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2209,
        "text": "\\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\)"
      }
    ],
    "after": [
      {
        "line": 2204,
        "text": "\\(L_{N}=\\left\\lfloor 9(2N-1)/4\\right\\rfloor+1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2217,
        "text": "\\(B^{2}\\le C*14^{7/18}*B^{14/9}+M_{2}\\)"
      }
    ],
    "after": [
      {
        "line": 2212,
        "text": "\\(B^{2}\\le C\\cdot 14^{7/18}\\cdot B^{14/9}+M_{2}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2219,
        "text": "\\(B^{5/6}\\le 2C*2^{7/6}*\\operatorname{exp}((7/6)h(\\beta ))\\)"
      }
    ],
    "after": [
      {
        "line": 2214,
        "text": "\\(B^{5/6}\\le 2C\\cdot 2^{7/6}\\cdot \\operatorname{exp}((7/6)h(\\beta ))\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2225,
        "text": "\\((7/5)C_{3}*149^{-{L}_{N}}\\)"
      }
    ],
    "after": [
      {
        "line": 2220,
        "text": "\\((7/5)C_{3}\\cdot 149^{-{L}_{N}}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2235,
        "text": "\\(q_{0}*q_{1}\\ne 0\\)"
      }
    ],
    "after": [
      {
        "line": 2230,
        "text": "\\(q_{0}\\cdot q_{1}\\ne 0\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2259,
        "text": "\\(\\Theta _{2}=\\Theta \\)"
      }
    ],
    "after": [
      {
        "line": 2254,
        "text": "\\(\\Theta _{2}=\\Theta \\cup(2-\\Theta)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2275,
        "text": "\\(w_{0}^{2}-2w_{0}*\\tau -2w_{1}^{2}=0\\)"
      },
      {
        "line": 2275,
        "text": "\\(W=w_{0}+\\sqrt{2}*w_{1}\\)"
      }
    ],
    "after": [
      {
        "line": 2270,
        "text": "\\(w_{0}^{2}-2w_{0}\\cdot \\tau -2w_{1}^{2}=0\\)"
      },
      {
        "line": 2270,
        "text": "\\(W=w_{0}+\\sqrt{2}\\cdot w_{1}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2297,
        "text": "\\(h(\\beta )\\le C_{3}*149^{-{L}_{N}}*c(1+\\operatorname{log}(c)/3)\\)"
      }
    ],
    "after": [
      {
        "line": 2292,
        "text": "\\(h(\\beta )\\le C_{3}\\cdot 149^{-{L}_{N}}\\cdot c(1+\\operatorname{log}(c)/3)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2297,
        "text": "\\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\)"
      }
    ],
    "after": [
      {
        "line": 2292,
        "text": "\\(L_{N}=\\left\\lfloor 9(2N-1)/4\\right\\rfloor+1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2297,
        "text": "\\(D=C*14^{7/18}\\)"
      }
    ],
    "after": [
      {
        "line": 2292,
        "text": "\\(D=C\\cdot 14^{7/18}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2299,
        "text": "\\(t^{2}-c*t*w+w^{2}=1\\)"
      }
    ],
    "after": [
      {
        "line": 2294,
        "text": "\\(t^{2}-c\\cdot t\\cdot w+w^{2}=1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2328,
        "text": "\\(M=\\operatorname{rad}_{\\text{odd}}(3*17*L)\\)"
      }
    ],
    "after": [
      {
        "line": 2323,
        "text": "\\(M=\\operatorname{rad}_{\\text{odd}}(3\\cdot 17\\cdot L)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2328,
        "text": "\\(d_{\\text{minus}},d_{\\text{plus}}\\)"
      }
    ],
    "after": [
      {
        "line": 2323,
        "text": "\\(d_{-},d_{+}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2328,
        "text": "\\(U=\\text{lcm}(d_{\\text{minus}}/4)\\)"
      },
      {
        "line": 2328,
        "text": "\\(V=\\text{lcm}(d_{\\text{plus}}/4)\\)"
      }
    ],
    "after": [
      {
        "line": 2323,
        "text": "\\(U=\\text{lcm}(d_{-}/4)\\)"
      },
      {
        "line": 2323,
        "text": "\\(V=\\text{lcm}(d_{+}/4)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2328,
        "text": "\\(h=h_{*}\\)"
      }
    ],
    "after": [
      {
        "line": 2323,
        "text": "\\(h=h_*\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2343,
        "text": "\\(D\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2349,
        "text": "\\(\\text{AUTHOR}_{{\\text{FREEZE}}_{001}}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2355,
        "text": "\\(H_{6}\\)"
      },
      {
        "line": 2355,
        "text": "\\(H_{01}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2355,
        "text": "\\(D_{210}\\)"
      },
      {
        "line": 2357,
        "text": "\\(\\text{FOUNDATION}_{\\text{MAP}}\\)"
      },
      {
        "line": 2357,
        "text": "\\(V_{14}\\)"
      },
      {
        "line": 2357,
        "text": "\\(H_{01}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [],
    "after": [
      {
        "line": 2360,
        "text": "\\(D_{210}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2393,
        "text": "\\(2400=2^{5}*3*5^{2}\\)"
      },
      {
        "line": 2393,
        "text": "\\(375=3*5^{3}\\)"
      },
      {
        "line": 2393,
        "text": "\\(77175=3^{2}*5^{2}*7^{3}\\)"
      }
    ],
    "after": [
      {
        "line": 2388,
        "text": "\\(2400=2^{5}\\cdot 3\\cdot 5^{2}\\)"
      },
      {
        "line": 2388,
        "text": "\\(375=3\\cdot 5^{3}\\)"
      },
      {
        "line": 2388,
        "text": "\\(77175=3^{2}\\cdot 5^{2}\\cdot 7^{3}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2411,
        "text": "\\(J=2^{10}*3^{2}*5^{3}*7^{4}\\)"
      }
    ],
    "after": [
      {
        "line": 2406,
        "text": "\\(J=2^{10}\\cdot 3^{2}\\cdot 5^{3}\\cdot 7^{4}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2411,
        "text": "\\(by4C_{\\text{met}}\\)"
      },
      {
        "line": 2417,
        "text": "\\(by120<128\\)"
      }
    ],
    "after": [
      {
        "line": 2406,
        "text": "\\(4C_{\\text{met}}\\)"
      },
      {
        "line": 2412,
        "text": "\\(120<128\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2437,
        "text": "\\(D_{210}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2459,
        "text": "\\(p_{122}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2468,
        "text": "\\(\\operatorname{GL}2\\)"
      }
    ],
    "after": [
      {
        "line": 2463,
        "text": "\\(\\operatorname{GL}_{2}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2470,
        "text": "\\(p_{352}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [],
    "after": [
      {
        "line": 2502,
        "text": "\\(\\mathbb Q_{11}^{\\times}\\operatorname{GL}_{2}(\\mathbb Z_{11})\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 2548,
        "text": "\\(\\mathbb Q^{\\times}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2585,
        "text": "\\((5^{-n} \\text{Lambda})/\\text{Lambda}\\)"
      },
      {
        "line": 2585,
        "text": "\\(\\text{Lambda}/5^{n}\\)"
      }
    ],
    "after": [
      {
        "line": 2580,
        "text": "\\((5^{-n}\\Lambda)/\\Lambda\\)"
      },
      {
        "line": 2580,
        "text": "\\(\\Lambda/5^{n}\\Lambda\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2587,
        "text": "\\(v_{2}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2603,
        "text": "\\(V_{15}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2685,
        "text": "\\(p_{296}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2685,
        "text": "\\(\\text{Qbar}_{5}\\)"
      }
    ],
    "after": [
      {
        "line": 2680,
        "text": "\\(\\overline{\\mathbb Q}_{5}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2697,
        "text": "\\(V_{14}\\)"
      },
      {
        "line": 2697,
        "text": "\\(V_{15}\\)"
      }
    ],
    "after": [
      {
        "line": 2692,
        "text": "\\(\\chi \\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2697,
        "text": "\\(\\chi \\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2831,
        "text": "\\(D\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2871,
        "text": "\\(v_{V}(n) = v_{V}(p) v_{p}(n) \\le  v_{V}(p) \\text{floor}(\\operatorname{log} d/\\operatorname{log} p)\\)"
      },
      {
        "line": 2873,
        "text": "\\(q=(\\text{pfrak})\\)"
      }
    ],
    "after": [
      {
        "line": 2864,
        "text": "\\(v_{V}(n) = v_{V}(p) v_{p}(n) \\le  v_{V}(p) \\left\\lfloor\\operatorname{log} d/\\operatorname{log} p\\right\\rfloor\\)"
      },
      {
        "line": 2866,
        "text": "\\(q=(\\mathfrak p)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2873,
        "text": "\\(V=O_{K}[t]_{\\text{pfrak}}\\)"
      },
      {
        "line": 2873,
        "text": "\\(k(\\text{pfrak})(t)\\)"
      }
    ],
    "after": [
      {
        "line": 2866,
        "text": "\\(V=O_{K}[t]_{\\mathfrak p}\\)"
      },
      {
        "line": 2866,
        "text": "\\(k(\\mathfrak p)(t)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2873,
        "text": "\\(v_{V}(p)=e_{\\text{pfrak}}\\)"
      }
    ],
    "after": [
      {
        "line": 2866,
        "text": "\\(v_{V}(p)=e_{\\mathfrak p}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2875,
        "text": "\\(r_{j} \\le  e_{j}-1 + e_{j} e_{\\text{pfrak}} \\text{floor}(\\operatorname{log} d/\\operatorname{log} p)\\)"
      }
    ],
    "after": [
      {
        "line": 2868,
        "text": "\\(r_{j} \\le  e_{j}-1 + e_{j} e_{\\mathfrak p} \\left\\lfloor\\operatorname{log} d/\\operatorname{log} p\\right\\rfloor\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2879,
        "text": "\\(d(1+e_{\\text{pfrak}} \\text{floor}(\\operatorname{log} d/\\operatorname{log} p))\\)"
      }
    ],
    "after": [
      {
        "line": 2872,
        "text": "\\(d(1+e_{\\mathfrak p} \\left\\lfloor\\operatorname{log} d/\\operatorname{log} p\\right\\rfloor)\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 2878,
        "text": "\\(\\mathfrak p\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2885,
        "text": "\\(f_{\\text{pfrak}}\\)"
      },
      {
        "line": 2885,
        "text": "\\(\\sum _{\\text{pfrak}|p}e_{\\text{pfrak}}\\)"
      },
      {
        "line": 2885,
        "text": "\\(f_{\\text{pfrak}}=[K:Q]\\)"
      },
      {
        "line": 2885,
        "text": "\\(\\sum f_{\\text{pfrak}}\\le [K:Q]\\)"
      }
    ],
    "after": [
      {
        "line": 2878,
        "text": "\\(f_{\\mathfrak p}\\)"
      },
      {
        "line": 2878,
        "text": "\\(\\sum _{\\mathfrak p|p}e_{\\mathfrak p}\\)"
      },
      {
        "line": 2878,
        "text": "\\(f_{\\mathfrak p}=[K:Q]\\)"
      },
      {
        "line": 2878,
        "text": "\\(\\sum f_{\\mathfrak p}\\le [K:Q]\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2933,
        "text": "\\(by\\pm 1\\)"
      },
      {
        "line": 2933,
        "text": "\\(by\\pm 1\\)"
      }
    ],
    "after": [
      {
        "line": 2926,
        "text": "\\(\\pm 1\\)"
      },
      {
        "line": 2926,
        "text": "\\(\\pm 1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2939,
        "text": "\\(p_{8}\\)"
      },
      {
        "line": 2939,
        "text": "\\(\\text{when}-I\\)"
      },
      {
        "line": 2939,
        "text": "\\(\\text{Here}-I\\)"
      },
      {
        "line": 2939,
        "text": "\\(\\text{because}-1\\in H\\)"
      },
      {
        "line": 2939,
        "text": "\\(\\text{from}0,1,\\infty \\)"
      }
    ],
    "after": [
      {
        "line": 2932,
        "text": "\\(-I\\)"
      },
      {
        "line": 2932,
        "text": "\\(-I\\)"
      },
      {
        "line": 2932,
        "text": "\\(-1\\in H\\)"
      },
      {
        "line": 2932,
        "text": "\\(0,1,\\infty\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2945,
        "text": "\\(\\text{pfrak}|p>3\\)"
      }
    ],
    "after": [
      {
        "line": 2938,
        "text": "\\(\\mathfrak p|p>3\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2945,
        "text": "\\(V=O_{K}[t]_{\\text{pfrak}}\\)"
      }
    ],
    "after": [
      {
        "line": 2938,
        "text": "\\(V=O_{K}[t]_{\\mathfrak p}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2947,
        "text": "\\(\\sum _{j} f_{j} r_{j} \\le  (\\sum _{j} f_{j} e_{j}) v_{V}(N) = d_{H} v_{\\text{pfrak}}(N)\\)"
      }
    ],
    "after": [
      {
        "line": 2940,
        "text": "\\(\\sum _{j} f_{j} r_{j} \\le  (\\sum _{j} f_{j} e_{j}) v_{V}(N) = d_{H} v_{\\mathfrak p}(N)\\)"
      },
      {
        "line": 2942,
        "text": "\\(\\mathfrak p\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 2963,
        "text": "\\(H_{4}\\)"
      },
      {
        "line": 2963,
        "text": "\\(n\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 2975,
        "text": "\\(p_{5}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3027,
        "text": "\\(v_{17}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3096,
        "text": "\\(\\operatorname{det}(r_{f})=\\epsilon *\\chi _{\\text{cyc}}\\)"
      }
    ],
    "after": [
      {
        "line": 3083,
        "text": "\\(\\operatorname{det}(r_{f})=\\epsilon \\cdot \\chi _{\\text{cyc}}\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 3087,
        "text": "\\(a\\notin\\{0,1,2401,-343/32\\}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3114,
        "text": "\\(by2v_{p}(e)\\)"
      },
      {
        "line": 3114,
        "text": "\\(by4v_{p}(e)\\)"
      }
    ],
    "after": [
      {
        "line": 3101,
        "text": "\\(2v_{p}(e)\\)"
      },
      {
        "line": 3101,
        "text": "\\(4v_{p}(e)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3140,
        "text": "\\(B \\text{tensor} \\text{Qbar}_{l}=M_{2}(\\text{Qbar}_{l})\\)"
      }
    ],
    "after": [
      {
        "line": 3127,
        "text": "\\(B \\otimes \\overline{\\mathbb Q}_{l}=M_{2}(\\overline{\\mathbb Q}_{l})\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3146,
        "text": "\\(\\epsilon *\\chi \\)"
      }
    ],
    "after": [
      {
        "line": 3133,
        "text": "\\(\\epsilon \\cdot \\chi \\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3157,
        "text": "\\(\\text{Qbar}_{5}\\)"
      }
    ],
    "after": [
      {
        "line": 3144,
        "text": "\\(\\overline{\\mathbb Q}_{5}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3224,
        "text": "\\(by1+x\\le \\operatorname{exp}(x)\\)"
      }
    ],
    "after": [
      {
        "line": 3211,
        "text": "\\(1+x\\le \\operatorname{exp}(x)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3241,
        "text": "\\(I\\)"
      },
      {
        "line": 3241,
        "text": "\\(I\\)"
      },
      {
        "line": 3241,
        "text": "\\(p\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3302,
        "text": "\\(H_{2}\\)"
      },
      {
        "line": 3302,
        "text": "\\(D\\)"
      },
      {
        "line": 3312,
        "text": "\\(I\\)"
      },
      {
        "line": 3312,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3316,
        "text": "\\(\\text{Qbar}_{5}\\)"
      },
      {
        "line": 3316,
        "text": "\\(M_{2}(\\text{Qbar}_{5})\\)"
      }
    ],
    "after": [
      {
        "line": 3303,
        "text": "\\(\\overline{\\mathbb Q}_{5}\\)"
      },
      {
        "line": 3303,
        "text": "\\(M_{2}(\\overline{\\mathbb Q}_{5})\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3322,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3338,
        "text": "\\(\\text{Qbar}_{5}\\)"
      }
    ],
    "after": [
      {
        "line": 3325,
        "text": "\\(\\overline{\\mathbb Q}_{5}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3347,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3355,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3355,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3363,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3363,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3378,
        "text": "\\((x_{\\text{new}},y_{\\text{new}})=(\\epsilon ^{4}*x_{\\text{old}},\\epsilon ^{6}*y_{\\text{old}})\\)"
      }
    ],
    "after": [
      {
        "line": 3365,
        "text": "\\((x_{\\text{new}},y_{\\text{new}})=(\\epsilon ^{4}\\cdot x_{\\text{old}},\\epsilon ^{6}\\cdot y_{\\text{old}})\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3378,
        "text": "\\(E:y^{2}=x^{3}-(3-\\sqrt{2})^{2}*x\\)"
      }
    ],
    "after": [
      {
        "line": 3365,
        "text": "\\((-660+417\\sqrt{2})/32\\)"
      },
      {
        "line": 3365,
        "text": "\\(E:y^{2}=x^{3}-(3-\\sqrt{2})^{2}\\cdot x\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3388,
        "text": "\\(n_{\\text{pole}}*\\theta \\)"
      }
    ],
    "after": [
      {
        "line": 3375,
        "text": "\\(n_{\\text{pole}}\\cdot \\theta \\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3390,
        "text": "\\(D=2^{a}*d\\)"
      },
      {
        "line": 3390,
        "text": "\\(y_{m}=\\text{cor}_{Q(\\zeta _{Dm})/Q(\\zeta _{m})}(z_{Dm} \\text{tensor} e_{\\chi })\\)"
      }
    ],
    "after": [
      {
        "line": 3377,
        "text": "\\(D=2^{a}\\cdot d\\)"
      },
      {
        "line": 3377,
        "text": "\\(y_{m}=\\text{cor}_{Q(\\zeta _{Dm})/Q(\\zeta _{m})}(z_{Dm} \\otimes e_{\\chi })\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3390,
        "text": "\\((m,c*d_{s})=1\\)"
      }
    ],
    "after": [
      {
        "line": 3377,
        "text": "\\((m,c\\cdot d_{s})=1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3390,
        "text": "\\(\\text{Nprime}=c*d_{s}\\)"
      }
    ],
    "after": [
      {
        "line": 3377,
        "text": "\\(N'_K=c\\cdot d_{s}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3390,
        "text": "\\(j_{*}\\)"
      }
    ],
    "after": [
      {
        "line": 3377,
        "text": "\\(j_*\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3392,
        "text": "\\(S_{\\text{Dmq}}=S_{Dm}\\)"
      }
    ],
    "after": [
      {
        "line": 3379,
        "text": "\\(N'_K\\)"
      },
      {
        "line": 3379,
        "text": "\\(S_{Dmq}=S_{Dm}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3399,
        "text": "\\(T*\\chi \\)"
      }
    ],
    "after": [
      {
        "line": 3386,
        "text": "\\(T\\otimes\\chi \\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3399,
        "text": "\\(S_{D*N_{K}*2^{n}}\\)"
      },
      {
        "line": 3399,
        "text": "\\(S_{D*2^{n}}\\)"
      },
      {
        "line": 3399,
        "text": "\\(\\text{cor}(y_{N_{K}*2^{n}})=y_{2^{n}}\\)"
      },
      {
        "line": 3399,
        "text": "\\(xi_{K}\\)"
      }
    ],
    "after": [
      {
        "line": 3386,
        "text": "\\(S_{DN_{K}2^{n}}\\)"
      },
      {
        "line": 3386,
        "text": "\\(S_{D2^{n}}\\)"
      },
      {
        "line": 3386,
        "text": "\\(\\operatorname{prime}(2Nd)\\)"
      },
      {
        "line": 3386,
        "text": "\\(\\text{cor}(y_{N_{K}2^{n}})=y_{2^{n}}\\)"
      },
      {
        "line": 3386,
        "text": "\\(\\xi_{K}\\)"
      },
      {
        "line": 3386,
        "text": "\\(\\xi\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3416,
        "text": "\\(\\alpha *\\delta /(4C_{\\text{star}})\\)"
      }
    ],
    "after": [
      {
        "line": 3403,
        "text": "\\(\\alpha \\cdot \\delta /(4C_*)\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3420,
        "text": "\\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\)"
      }
    ],
    "after": [
      {
        "line": 3407,
        "text": "\\(L_{N}=\\left\\lfloor 9(2N-1)/4\\right\\rfloor+1\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3722,
        "text": "\\(I\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 3735,
        "text": "\\(\\text{hence}14/9<2\\)"
      }
    ],
    "after": [
      {
        "line": 3722,
        "text": "\\(14/9<2\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 3738,
        "text": "\\(\\text{canonical}-\\text{height}-\\text{ to } -B^{2}\\)"
      }
    ],
    "after": []
  },
  {
    "before": [
      {
        "line": 4326,
        "text": "\\(Q_{2}=M*w+L\\)"
      },
      {
        "line": 4327,
        "text": "\\(M=B+(23335979380411305/9142573010269636-r*256685364214285/4571286505134818)f+(44649296511110307/111996519375803041-r*2886885451827729/447986077503212164)S+3317607896141091533/7167777240051394624+r*677690583653850567/1791944310012848656\\)"
      }
    ],
    "after": [
      {
        "line": 4313,
        "text": "\\(Q_{2}=M\\cdot w+L\\)"
      },
      {
        "line": 4314,
        "text": "\\(M=B+(23335979380411305/9142573010269636-r\\cdot 256685364214285/4571286505134818)f+(44649296511110307/111996519375803041-r\\cdot 2886885451827729/447986077503212164)S+3317607896141091533/7167777240051394624+r\\cdot 677690583653850567/1791944310012848656\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 4318,
        "text": "\\(Q_0,Q_1,Q_3\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 4318,
        "text": "\\(Q_5\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 4318,
        "text": "\\(Q_0,Q_1,Q_3\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 4331,
        "text": "\\(D=\\beta *S+\\alpha \\)"
      }
    ],
    "after": [
      {
        "line": 4318,
        "text": "\\(D=\\beta \\cdot S+\\alpha \\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 4333,
        "text": "\\(w*=g^{4}/f^{2}\\)"
      }
    ],
    "after": [
      {
        "line": 4320,
        "text": "\\(w_*=g^{4}/f^{2}\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 4333,
        "text": "\\(Q_{2}(f,S,B,w*,T)=0\\)"
      }
    ],
    "after": [
      {
        "line": 4320,
        "text": "\\(Q_{2}(f,S,B,w_*,T)=0\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 4333,
        "text": "\\(D*T=N\\)"
      }
    ],
    "after": [
      {
        "line": 4320,
        "text": "\\(D\\cdot T=N\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 4333,
        "text": "\\(w=w*\\)"
      }
    ],
    "after": [
      {
        "line": 4320,
        "text": "\\(w=w_*\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 4622,
        "text": "\\(l\\)"
      }
    ]
  },
  {
    "before": [
      {
        "line": 5197,
        "text": "$\\bullet$"
      }
    ],
    "after": [
      {
        "line": 5183,
        "text": "\\(C(\\Gamma,\\epsilon)\\)"
      }
    ]
  },
  {
    "before": [],
    "after": [
      {
        "line": 29540,
        "text": "$\\mathbb Z$"
      }
    ]
  }
]
```

The named renames use `d_{\text{minus}}`/`d_{\text{plus}}` for the two reduction orders and `Nprime` for the Kato auxiliary conductor. They are replaced by `d_-`/`d_+` and `N'_K` at the same consumers. The complete span inventory above includes the source TeX spellings. The star braces are unchanged mathematical symbols, as the earlier source comparison records. Whole-file literal counts below report surviving old spellings; an old spelling inside a historical filename is not silently rewritten.

- `d_{\text{minus}}`: base 2, candidate 0.
- `d_{\text{plus}}`: base 2, candidate 0.
- `d_-`: base 17, candidate 17.
- `d_+`: base 20, candidate 20.
- `Nprime`: base 2, candidate 0.
- `N'_K`: base 4, candidate 6.
- `h_{*}`: base 3, candidate 2.
- `h_*`: base 102, candidate 103.
- `j_{*}`: base 3, candidate 2.
- `j_*`: base 9, candidate 10.

## All word-level changes

```jsonl
["W0001",[2,2,55,68],[2,2,55,65],"Height-source","Historical",["% "," replacement: see"]]
["W0002",[2,2,69,81],[2,2,66,79],"replacement:","height-source",["% Height-source "," see work/remove-vkk-20261104/REPORT.md"]]
["W0003",[2,2,82,85],[2,2,80,92],"see","replacement;",["Height-source replacement: "," work/remove-vkk-20261104/REPORT.md for"]]
["W0004",[2,2,86,120],[2,2,93,99],"work/remove-vkk-20261104/REPORT.md","source",["replacement: see "," for scope"]]
["W0005",[2,2,121,130],[2,2,100,108],"for scope","identity",["see work/remove-vkk-20261104/REPORT.md "," and review"]]
["W0006",[2,2,135,141],[2,2,113,124],"review","limitations",["scope and "," status.\n"]]
["W0007",[2,2,142,149],[2,2,125,169],"status.","are retained in the companion status record.",["and review ","\n"]]
["W0008",[79,79,3485,3538],[79,79,3505,3505],"  This assembled manuscript is an author proposal for","",["coefficient threshold.","\nfresh review"]]
["W0009",[80,80,3539,3613],[80,80,3506,3506],"fresh review and does not itself confer Protocol~D or release acceptance.\n","",["proposal for\n",""]]
["W0010",[128,128,6109,6109],[127,130,6002,6263],"","\nThe separate \\href{https://github.com/elliotglazer/diophantine-z-q/blob/main/docs/research-review/version18-cleanup-status.md}{Version~18 source and incorporation record}\npreserves outstanding incorporation obligations and review limitations\nfor this edition.\n",["",""]]
["W0011",[187,187,9296,9340],[190,190,9450,9474],"\\paragraph{Attribution and review boundary.}","\\paragraph{Attribution.}",["","\n"]]
["W0012",[193,197,9718,10085],[196,196,9852,9852],"Source statements concerning earlier inspection, pending status or historical\nacceptance remain dated evidence.  They are not new acceptance records for\nthis exact TeX/PDF.  The independently authored public review overlay and\nprotected controller decision govern any later adoption.  Internal model\nreview is distinct from human peer review and formal verification.\n","",["",""]]
["W0013",[1999,1999,75394,75575],[1997,1997,75161,75161]," Author: model task \\nolinkurl{/root/q214_tex_coverage}, 12 November 2026. This is a new source-to-consumer comparison for independent review. It supplies no independent acceptance.","",["\\begin{quote}\\footnotesize"," The upstream"]]
["W0014",[2001,2001,75909,75928],[1999,1999,75495,75519],"\\subsection{Current","\\subsection{Mathematical",[""," source rule}"]]
["W0015",[2001,2001,75929,75941],[1999,1999,75520,75531],"source rule}","foundation}",["\\subsection{Current ","\n"]]
["W0016",[2004,2004,76309,76316],[2002,2002,75899,75909],"hashes,","hashes and",["source}. Their "," earlier arguments"]]
["W0017",[2004,2004,76335,76353],[2002,2002,75928,75928],"and review limits ","",["earlier arguments ","remain historical "]]
["W0018",[2004,2004,76371,76426],[2002,2002,75946,75955],"evidence; no old approval is transferred automatically.","evidence.",["remain historical "," The current"]]
["W0019",[2004,2004,76618,76624],[2002,2002,76147,76154],"raw224","raw 224",["polynomial, its "," branch, the"]]
["W0020",[2006,2006,76774,76785],[2004,2004,76304,76304],"Version~16 ","",["The historical ","comparison used "]]
["W0021",[2006,2006,76795,76930],[2004,2004,76314,76314]," used the actual complete normalized V15-to-current-V16 difference, the actual Fable audit passages concerning horizontal normalization","",[" Version~16 comparison"," and the"]]
["W0022",[2006,2006,76935,77121],[2004,2004,76319,76322],"the four follow-ups, the current \\(V_{16}\\) passages themselves, and the actual 214 consumers. It follows both the editorial amendment and the later Tao--Ziegler precision amendment: the","its",["normalization and "," intermediate \\nolinkurl{2f729...}"]]
["W0023",[2006,2006,77135,77190],[2004,2004,76336,76342],"\\nolinkurl{2f729...} and \\nolinkurl{a9cb...} \\(V_{16}\\)","source",["the intermediate "," hashes are"]]
["W0024",[2006,2006,77202,77205],[2004,2004,76354,76362],"not","recorded",["hashes are "," the final"]]
["W0025",[2006,2006,77206,77209],[2004,2004,76363,76374],"the","separately.",["are not "," final receiving"]]
["W0026",[2006,2006,77210,77245],[2004,2004,76375,76394],"final receiving source. Publication","Publication-version",["not the "," and pre-existing"]]
["W0027",[2006,2006,77250,77262],[2004,2004,76399,76417],"pre-existing","source-application",["Publication and "," source-review scopes"]]
["W0028",[2006,2006,77263,77283],[2004,2004,76418,76432],"source-review scopes","qualifications",["and pre-existing "," remain those"]]
["W0029",[2006,2006,77334,77454],[2004,2004,76483,76483]," This author does not claim a new reading of every external publication or a recursive reproof of the entire foundation.","",[" current foundation.","\n"]]
["W0030",[2063,2063,80522,80539],[2061,2061,79551,79569],"lines30658--30683","lines 30658--30683",["\\(V_{16}\\) "," now cite"]]
["W0031",[2063,2063,80651,80662],[2061,2061,79681,79693],"Helvetici89","Helvetici 89",["Commentarii Mathematici "," (2014),343--403, Section2.3"]]
["W0032",[2063,2063,80680,80690],[2061,2061,79711,79722],"Section2.3","Section 2.3",["Helvetici89 (2014),343--403, "," and Corollary8.4,"]]
["W0033",[2063,2063,80695,80708],[2061,2061,79727,79736],"Corollary8.4,","Corollary",["Section2.3 and "," DOI10.4171/CMH/322. The"]]
["W0034",[2063,2063,80709,80728],[2061,2061,79737,79762],"DOI10.4171/CMH/322.","8.4, DOI 10.4171/CMH/322.",["and Corollary8.4, "," The earlier"]]
["W0035",[2063,2063,80791,80810],[2061,2061,79825,79846],"Theorem1.4/Section9","Theorem 1.4/Section 9",["its own "," uses. The"]]
["W0036",[2065,2065,81175,81183],[2063,2063,80211,80218],"L-prime,","\\(L'\\),",["the actual "," chooses \\(r\\)"]]
["W0037",[2065,2065,81584,81592],[2063,2063,80619,80626],"L-prime,","\\(L'\\),",["field for "," replaces \\(r\\)"]]
["W0038",[2067,2067,81916,81946],[2065,2065,80950,80963],"uses and remaining acceptance}","applications}",["\\subsection{Related ","\n"]]
["W0039",[2071,2073,82876,83730],[2069,2069,81893,81893],"The Fable Bogolyubov-numbering concern is expressly withdrawn in its follow-up after comparison with the published numbering; no manuscript repair is imported for that item. Its audit's other unexamined portions remain review-scope limitations, without inventing new objections or treating them as verification. The original audit and its \\(V_{16}\\) findings remain preserved in their versioned locations.\n\nThis transition is a changed foundation application. A fresh non-author must assess its exact source passages, the corrected connections, the actual 214 consumers and the assembled TeX/PDF. Old component or \\(V_{16}\\) acceptance is evidence at its own bound scope, not automatic acceptance of this new receiving application. Until that decision and the matching release binding exist, assembled-proof and record-release acceptance remain pending.\n","",["",""]]
["W0040",[2079,2079,83926,84147],[2074,2074,82089,82089],"This is an author assembly for fresh public review. The construction and all source-to-consumer transitions below are proposed together. Historical source acceptance is separate from acceptance of this public adaptation. ","",["","\\href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/SOURCE_PATH_MAP.json}{\\nolinkurl{SOURCE_PATH_MAP.json}} records "]]
["W0041",[2079,2079,84415,84472],[2074,2074,82357,82357]," It deliberately contains no generated reviewer approval.","",[" public paths.","\n"]]
["W0042",[2083,2083,84564,84770],[2078,2078,82449,82656],"\\href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json}{raw224","\\href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json}{raw 224",["the public "," predecessor}, \\href{https://github.com/elliotglazer/diophantine-z-q/blob/110cf72565be326fd567cd1a64a3b2e00213dcd1/research/quartic214/construction/build.py}{the"]]
["W0043",[2098,2098,87817,87823],[2093,2093,85703,85710],"raw224","raw 224",["the actual "," reference, root"]]
["W0044",[2103,2103,91856,91865],[2098,2098,89743,89754],"Poincaré,","Poincar\\'e,",["the Faltings, "," Fricke and"]]
["W0045",[2104,2104,93106,93217],[2099,2099,90995,91004],"branch. Public review evidence is historical scope evidence, not a replacement for these statements and maps.\\\\","branch.\\\\",["into this ","\n"]]
["W0046",[2108,2108,93814,93959],[2103,2103,91601,91601]," The source metadata describes previous actual inspections; the present porter does not claim to have repeated all those primary-source readings.","",[" in full.","\n"]]
["W0047",[2128,2128,97319,97337],[2123,2123,94961,94984],"\\subsection{Review","\\subsection{Effectivity",[""," boundary}\n"]]
["W0048",[2128,2128,97338,97347],[2123,2123,94985,95003],"boundary}","and finite checks}",["\\subsection{Review ","\n"]]
["W0049",[2130,2130,97662,97689],[2125,2125,95318,95321],"are provenance; old private","and",["contract hashes "," line pins"]]
["W0050",[2130,2130,97700,97703],[2125,2125,95332,95335],"and","are",["line pins "," approvals do"]]
["W0051",[2130,2130,97704,97713],[2125,2125,95336,95346],"approvals","historical",["pins and "," do not"]]
["W0052",[2130,2130,97714,97761],[2125,2125,95347,95358],"do not become current public pins or approvals.","provenance.",["and approvals "," Required internal"]]
["W0053",[2132,2132,97882,97885],[2127,2127,95479,95482],"All","The",[""," current applications"]]
["W0054",[2132,2132,97886,97893],[2127,2127,95483,95491],"current","defining",["All "," applications above"]]
["W0055",[2132,2132,97894,97906],[2127,2127,95492,95501],"applications","threshold",["All current "," above require"]]
["W0056",[2132,2132,97907,97912],[2127,2127,95502,95509],"above","remains",["current applications "," require review"]]
["W0057",[2132,2132,97913,97962],[2127,2127,95510,95522],"require review of this exact public serialization","ineffective,",["applications above "," and its"]]
["W0058",[2132,2132,97967,97970],[2127,2127,95527,95529],"its","no",["serialization and "," dependencies. Prior"]]
["W0059",[2132,2132,97971,98065],[2127,2127,95530,95534],"dependencies. Prior scoped acceptance does not independently accept this assembly, establish a","full",["and its "," numerical \\(N_{0}\\),"]]
["W0060",[2132,2132,98076,98113],[2127,2127,95545,95545],"\\(N_{0}\\), or certify a full example ","",["a numerical ","witness tuple. "]]
["W0061",[2132,2132,98121,98127],[2127,2127,95553,95571],"tuple.","tuple is supplied.",["example witness "," The isolated"]]
["W0062",[2132,2132,98205,98217],[2127,2127,95649,95661],"conclusions.","conclusions;",["declared finite "," The public"]]
["W0063",[2132,2132,98218,98221],[2127,2127,95662,95666],"The","they",["finite conclusions. "," public Astra/controller"]]
["W0064",[2132,2132,98222,98228],[2127,2127,95667,95669],"public","do",["conclusions. The "," Astra/controller acceptance"]]
["W0065",[2132,2132,98229,98245],[2127,2127,95670,95673],"Astra/controller","not",["The public "," acceptance requirement"]]
["W0066",[2132,2132,98246,98256],[2127,2127,95674,95681],"acceptance","certify",["public Astra/controller "," requirement remains"]]
["W0067",[2132,2132,98257,98268],[2127,2127,95682,95685],"requirement","the",["Astra/controller acceptance "," remains in"]]
["W0068",[2132,2132,98269,98276],[2127,2127,95686,95694],"remains","retained",["acceptance requirement "," in force."]]
["W0069",[2132,2132,98277,98279],[2127,2127,95695,95705],"in","arithmetic",["requirement remains "," force.\n"]]
["W0070",[2132,2132,98280,98286],[2127,2127,95706,95715],"force.","premises.",["remains in ","\n"]]
["W0071",[2138,2138,98557,98824],[2133,2133,95986,95986]," Author: /root, integrating the attributed existence222 contribution. This is a new application on the literal public raw224 rows, not adoption of an earlier verdict. All source files and the author construction are bound by the author manifest for non-author review.","",["\\begin{quote}\\footnotesize"," This section"]]
["W0072",[2138,2138,98950,98959],[2133,2133,96112,96122],"Version15","Version 15",["the frozen "," source. Its"]]
["W0073",[2142,2142,99579,99586],[2137,2137,96742,96750],"with188","with 188",["214-variable family "," rows and"]]
["W0074",[2142,2142,99619,99626],[2137,2137,96783,96791],"with192","with 192",["218-variable control "," rows. Every"]]
["W0075",[2144,2144,99961,99973],[2139,2139,97126,97139],"coordinate1.","coordinate 1.",["of input "," This is"]]
["W0076",[2144,2144,100098,100127],[2139,2139,97264,97287],"\\(\\text{equals}149^{4N+2}+1\\)","equals \\(149^{4N+2}+1\\)",["coefficient height "," for \\(N\\ge"]]
["W0077",[2144,2144,100139,100146],[2139,2139,97299,97311],"53;53\\)","53\\); \\(53\\)",["for \\(N\\ge "," is solely"]]
["W0078",[2146,2146,100372,100378],[2141,2141,97537,97544],"raw224","raw 224",["source. The "," component bases,"]]
["W0079",[2146,2146,100515,100521],[2141,2141,97681,97684],"raw224","raw",["weights are "," coordinates87 and102."]]
["W0080",[2146,2146,100522,100535],[2141,2141,97685,97688],"coordinates87","224",["are raw224 "," and102. The"]]
["W0081",[2146,2146,100536,100543],[2141,2141,97689,97712],"and102.","coordinates 87 and 102.",["raw224 coordinates87 "," The physical"]]
["W0082",[2146,2146,100588,100599],[2141,2141,97757,97773],"\\(T*\\lambda","\\(T\\cdot \\lambda",["\\) and "," \\), with"]]
["W0083",[2148,2148,100867,100885],[2143,2143,98041,98058],"\\) union(2-Theta),","\\cup(2-\\Theta)\\),",["is \\(\\Theta "," \\(\\Theta =\\{0,-1/2,-1,1/2399,-32/407\\}\\);"]]
["W0084",[2148,2148,100979,100990],[2143,2143,98152,98164],"and2029147.","and 2029147.",["\\(\\text{primes}\\le 76176\\) "," Write \\(F_{2}\\)"]]
["W0085",[2148,2148,101270,101273],[2143,2143,98444,98448],"is1","is 1",["comparison radical "," and no"]]
["W0086",[2148,2148,101457,101463],[2143,2143,98632,98639],"raw224","raw 224",["with unrestricted "," is claimed."]]
["W0087",[2152,2152,101578,101584],[2147,2147,98754,98757],"raw224","raw",["coordinates are "," IDs23,24,29,30,33,34,37,38,133,134: the"]]
["W0088",[2152,2152,101585,101620],[2147,2147,98758,98798],"IDs23,24,29,30,33,34,37,38,133,134:","224 IDs 23,24,29,30,33,34,37,38,133,134:",["are raw224 "," the two"]]
["W0089",[2154,2154,102021,102029],[2149,2149,99199,99214],"s1,s2,s4","\\(s_1,s_2,s_4\\)",["slots as "," and impose"]]
["W0090",[2154,2154,102041,102055],[2149,2149,99226,99245],"\\(q*s_{1}=1\\),","\\(q\\cdot s_{1}=1\\),",["and impose "," \\(s_{2}=s_{1}^{2}\\), \\(s_{4}=s_{2}^{2}\\)."]]
["W0091",[2154,2154,102098,102104],[2149,2149,99288,99295],"The214","The 214",["\\(s_{2}=s_{1}^{2}\\), \\(s_{4}=s_{2}^{2}\\). "," factors use"]]
["W0092",[2154,2154,102148,102157],[2149,2149,99339,99349],"exponent3","exponent 3",["with special "," below. Multiplying"]]
["W0093",[2154,2154,102294,102300],[2149,2149,99486,99493],"The218","The 218",["stored squares. "," control retains"]]
["W0094",[2154,2154,102343,102353],[2149,2149,99536,99547],"exponent1;","exponent 1;",["exponents(7,2,4), special "," it also"]]
["W0095",[2154,2154,102399,102420],[2149,2149,99593,99619],"\\(s_{3}=s_{1}*s_{2}\\)","\\(s_{3}=s_{1}\\cdot s_{2}\\)",["\\(s_{3}\\), with "," and \\(q_{3}*s_{3}=1\\)."]]
["W0096",[2154,2154,102425,102443],[2149,2149,99624,99647],"\\(q_{3}*s_{3}=1\\).","\\(q_{3}\\cdot s_{3}=1\\).",["\\(s_{3}=s_{1}*s_{2}\\) and "," These equations"]]
["W0097",[2156,2156,102787,102793],[2151,2151,99991,99998],"all162","all 162",["It compares "," untouched rows"]]
["W0098",[2156,2156,102975,102981],[2151,2151,100180,100187],"For214","For 214",["sample points. "," the target"]]
["W0099",[2156,2156,103071,103077],[2151,2151,100277,100284],"For218","For 218",["order-four system. "," it is"]]
["W0100",[2156,2156,103112,103128],[2151,2151,100319,100340],"\\(q_{0}*q_{1}\\ne","\\(q_{0}\\cdot q_{1}\\ne",["system on "," 0\\).\n"]]
["W0101",[2158,2158,103235,103241],[2153,2153,100447,100454],"raw224","raw 224",["by the "," inverse maps."]]
["W0102",[2158,2158,103405,103411],[2153,2153,100618,100625],"raw224","raw 224",["removed in "," and has"]]
["W0103",[2158,2158,103541,103550],[2153,2153,100755,100765],"Version15","Version 15",["in \\nolinkurl{SOURCE_PATH_MAP.json,} "," \\nolinkurl{v222:reference} and"]]
["W0104",[2158,2158,103703,103711],[2153,2153,100918,100933],"Q0,Q1,Q3","\\(Q_0,Q_1,Q_3\\)",["recovery uses "," to obtain"]]
["W0105",[2158,2158,103795,103804],[2153,2153,101017,101027],"forced149","forced 149",["The unchanged "," scalar argument"]]
["W0106",[2160,2160,104135,104152],[2155,2155,101358,101380],"\\(D_{r}*T=N_{r}\\)","\\(D_{r}\\cdot T=N_{r}\\)",["recovered from "," with both"]]
["W0107",[2160,2160,104211,104217],[2155,2155,101439,101446],"at149.","at 149.",["valuation -m/2 "," Thus \\(T\\)"]]
["W0108",[2160,2160,104526,104535],[2155,2155,101755,101765],"forced149","forced 149",["untouched; the "," bound, real"]]
["W0109",[2162,2162,104794,104801],[2157,2157,102024,102032],"for214}","for 214}",["and soundness ","\n"]]
["W0110",[2164,2164,105369,105390],[2159,2159,102600,102626],"\\(f(H)*F_{0}=g^{2}\\).","\\(f(H)\\cdot F_{0}=g^{2}\\).",["supplied by "," Zeros have"]]
["W0111",[2176,2176,106110,106117],[2171,2171,103346,103352],"modulo4","modulo",["are -nu,nu,2 "," and4 modulo8."]]
["W0112",[2176,2176,106118,106122],[2171,2171,103353,103354],"and4","4",["-nu,nu,2 modulo4 "," modulo8. These"]]
["W0113",[2176,2176,106123,106131],[2171,2171,103355,103370],"modulo8.","and 4 modulo 8.",["modulo4 and4 "," These classes"]]
["W0114",[2176,2176,106172,106181],[2171,2171,103411,103421],"exclude0.","exclude 0.",["distinct and "," Omitting zero-test"]]
["W0115",[2176,2176,106327,106337],[2171,2171,103567,103578],"valuation0","valuation 0",["0\\); at "," its residue"]]
["W0116",[2176,2176,106350,106354],[2171,2171,103591,103596],"is1.","is 1.",["its residue "," This holds"]]
["W0117",[2187,2187,107351,107358],[2182,2182,104593,104601],"order3,","order 3,",["required high "," input orders"]]
["W0118",[2187,2187,107375,107382],[2182,2182,104618,104626],"least1,","least 1,",["orders at "," and positive"]]
["W0119",[2187,2187,107427,107435],[2182,2182,104671,104680],"least2).","least 2).",["valuations (at "," The source's"]]
["W0120",[2187,2187,107616,107622],[2182,2182,104861,104868],"raw224","raw 224",["actual recovered "," objects above."]]
["W0121",[2189,2189,107815,107825],[2184,2184,105061,105072],"precision4","precision 4",["has relative "," at depth1."]]
["W0122",[2189,2189,107829,107836],[2184,2184,105076,105084],"depth1.","depth 1.",["precision4 at "," Write \\(h=m/2\\)"]]
["W0123",[2189,2189,108482,108491],[2184,2184,105730,105740],"Version15","Version 15",["as in "," \\nolinkurl{Integrality before"]]
["W0124",[2193,2193,109339,109358],[2188,2188,106588,106612],"\\(H=C_{2}*B_{\\Sigma","\\(H=C_{2}\\cdot B_{\\Sigma",["with fixed "," }^{\\alpha }\\)."]]
["W0125",[2195,2195,109457,109464],[2190,2190,106711,106713],"to2+1/t","to",["this bound "," and2+1/(2-t), whose"]]
["W0126",[2195,2195,109465,109478],[2190,2190,106714,106734],"and2+1/(2-t),","2+1/t and 2+1/(2-t),",["bound to2+1/t "," whose inverse"]]
["W0127",[2195,2195,109522,109528],[2190,2190,106778,106783],"norms3","norms",["have row "," and7, and"]]
["W0128",[2195,2195,109529,109534],[2190,2190,106784,106792],"and7,","3 and 7,",["row norms3 "," and multiplying"]]
["W0129",[2195,2195,109590,109594],[2190,2190,106848,106853],"log7","log 7",["after subtracting "," gives\n"]]
["W0130",[2201,2201,109883,109894],[2196,2196,107142,107154],"(radical1).","(radical 1).",["\\(t=1\\) stratum "," All contact"]]
["W0131",[2203,2203,110181,110200],[2198,2198,107441,107465],"M_{1}*h(T)+M_{2}\\),","M_{1}\\cdot h(T)+M_{2}\\),",["gives \\(B^{2}\\le "," \\(B=\\operatorname{max}(|n|,|a|,|t|,|b|)\\), and"]]
["W0132",[2206,2206,110455,110470],[2201,2201,107720,107745],"C=2*M_{1}*H_{2}","C=2\\cdot M_{1}\\cdot H_{2}",["C |J_{0}|^{7/(6k)}+M_{2}, ","\n"]]
["W0133",[2209,2209,110572,110608],[2204,2204,107847,107895],"\\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\),","\\(L_{N}=\\left\\lfloor 9(2N-1)/4\\right\\rfloor+1\\),",["\\(c\\ge 149^{{L}_{N}}\\), "," and\n"]]
["W0134",[2212,2212,110643,110692],[2207,2207,107930,107994],"C_{3}*149^{-L_{N}}*c*(1+\\operatorname{log}(c)/3),","C_{3}\\cdot 149^{-L_{N}}\\cdot c\\cdot (1+\\operatorname{log}(c)/3),",["h(\\beta )\\le "," C_{3}=2^{330770}\n"]]
["W0135",[2215,2215,110787,110796],[2210,2210,108089,108099],"Version15","Version 15",["conclusions in "," \\nolinkurl{v222:fourcontact} and"]]
["W0136",[2217,2217,110966,110995],[2212,2212,108269,108308],"C*14^{7/18}*B^{14/9}+M_{2}\\).","C\\cdot 14^{7/18}\\cdot B^{14/9}+M_{2}\\).",["obtain \\(B^{2}\\le "," The right"]]
["W0137",[2217,2217,111027,111034],[2212,2212,108340,108348],"below2,","below 2,",["is strictly "," so \\(B\\)"]]
["W0138",[2219,2219,111489,111531],[2214,2214,108803,108855],"2C*2^{7/6}*\\operatorname{exp}((7/6)h(\\beta","2C\\cdot 2^{7/6}\\cdot \\operatorname{exp}((7/6)h(\\beta",["have \\(B^{5/6}\\le "," ))\\). Thus"]]
["W0139",[2225,2225,111686,111715],[2220,2220,109010,109044],"\\((7/5)C_{3}*149^{-{L}_{N}}\\)","\\((7/5)C_{3}\\cdot 149^{-{L}_{N}}\\)",["the coefficient "," becomes at"]]
["W0140",[2225,2225,111727,111733],[2220,2220,109056,109063],"most1.","most 1.",["becomes at "," The right"]]
["W0141",[2225,2225,111970,111974],[2220,2220,109300,109305],"of51","of 51",["and squarefreeness "," imply \\(v=1\\)."]]
["W0142",[2227,2227,112173,112179],[2222,2222,109504,109511],"the218","the 218",["completeness and "," control}\n"]]
["W0143",[2229,2229,112405,112414],[2224,2224,109737,109747],"Version15","Version 15",["the frozen "," construction. Neither"]]
["W0144",[2231,2231,113254,113258],[2226,2226,110587,110590],"are1","are",["trace residues "," or2. The"]]
["W0145",[2231,2231,113259,113263],[2226,2226,110591,110598],"or2.","1 or 2.",["residues are1 "," The comparison"]]
["W0146",[2231,2231,113317,113323],[2226,2226,110652,110659],"depth1","depth 1",["same odd "," at selected"]]
["W0147",[2233,2233,113437,113441],[2228,2228,110773,110778],"to0,","to 0,",["arbitrarily deeply "," so every"]]
["W0148",[2233,2233,113546,113557],[2228,2228,110883,110895],"depths4,2,2","depths 4,2,2",["squareclasses and "," for the"]]
["W0149",[2233,2233,113577,113585],[2228,2228,110915,110924],"at2,3,17","at 2,3,17",["pole input "," are unchanged."]]
["W0150",[2233,2233,113681,113685],[2228,2228,111020,111025],"to1,","to 1,",["\\(W\\) tends "," and the"]]
["W0151",[2233,2233,113732,113741],[2228,2228,111072,111082],"in(0,17).","in (0,17).",["\\(\\gamma ^{2}/4\\) "," The same"]]
["W0152",[2233,2233,114124,114130],[2228,2228,111465,111472],"raw224","raw 224",["inherited exact "," coordinate maps;"]]
["W0153",[2235,2235,114296,114302],[2230,2230,111638,111645],"For218","For 218",[""," keep the"]]
["W0154",[2235,2235,114424,114440],[2230,2230,111767,111788],"\\(q_{0}*q_{1}\\ne","\\(q_{0}\\cdot q_{1}\\ne",["ones on "," 0\\). Soundness"]]
["W0155",[2235,2235,114682,114688],[2230,2230,112030,112037],"the218","the 218",["needed for "," control. This"]]
["W0156",[2239,2239,115229,115258],[2234,2234,112578,112578],"new214 argument has explicit ","",["premises. The ","local, completeness "]]
["W0157",[2239,2239,115289,115289],[2234,2234,112609,112636],"","arguments use the explicit ",["and height ","consumers above; "]]
["W0158",[2239,2239,115299,115379],[2234,2234,112646,112652],"above; their independent review and inventory coverage will be bound separately.","above.",["height consumers "," No claim"]]
["W0159",[2239,2239,115382,115410],[2234,2234,112655,112655]," claim of public priority, a","",[" separately. No"," numerical defining"]]
["W0160",[2239,2239,115430,115466],[2234,2234,112675,112684],"parameter, or whole-proof completion","parameter",["numerical defining "," is made."]]
["W0161",[2239,2239,115470,115475],[2234,2234,112688,112697],"made.","supplied.",["completion is "," The construction"]]
["W0162",[2239,2239,115515,115521],[2234,2234,112737,112744],"at224;","at 224;",["deliberately branches "," the final"]]
["W0163",[2239,2239,115570,115581],[2234,2234,112793,112805],"yielding222","yielding 222",["paired-root/trace-quotient reductions "," are not"]]
["W0164",[2244,2244,115942,115957],[2239,2239,113166,113184],"\\textbf{Current","\\textbf{Foundation",["\\begin{quote}\\small "," foundation overlay:}"]]
["W0165",[2244,2244,115958,115978],[2239,2239,113185,113194],"foundation overlay:}","sources:}",["\\begin{quote}\\small \\textbf{Current "," The Version~15"]]
["W0166",[2244,2244,116334,116336],[2239,2239,113550,113559],"is","describes",["historical text "," retained as"]]
["W0167",[2244,2244,116337,116345],[2239,2239,113560,113563],"retained","the",["text is "," as evidence;"]]
["W0168",[2244,2244,116346,116348],[2239,2239,113564,113571],"as","earlier",["is retained "," evidence; it"]]
["W0169",[2244,2244,116349,116358],[2239,2239,113572,113578],"evidence;","source",["retained as "," it does"]]
["W0170",[2244,2244,116359,116438],[2239,2239,113579,113598],"it does not negate or independently accept that changed application.\\end{quote}","version.\\end{quote}",["as evidence; ","\n"]]
["W0171",[2246,2246,116467,116535],[2241,2241,113627,113631],"Author: \\nolinkurl{/root/d214_uniform_existence}, 2026-11-11. Author","This",["\\begin{quote}\\footnotesize "," argument only;"]]
["W0172",[2246,2246,116545,116711],[2241,2241,113641,113649],"only; fresh non-author acceptance is required. No source, old packet, coefficient, witness table or public repository is changed. This is an additive clarification of","concerns",["Author argument "," the frozen"]]
["W0173",[2246,2246,116715,116722],[2241,2241,113653,113653]," frozen","",[" of the"," existing 214"]]
["W0174",[2246,2246,116876,116913],[2241,2241,113807,113844],"\\nolinkurl{CONTRACT.json.}\\end{quote}","\\nolinkurl{CONTRACT.json}.\\end{quote}",["\\nolinkurl{SOURCE_USES.json} and ","\n"]]
["W0175",[2248,2248,117028,117122],[2243,2243,113959,114012],"\\nolinkurl{research/quadratic-ten-contact-integration/existence/artifacts/candidate214-brox/},","the historical \\nolinkurl{candidate214-brox} artifact",["residuals in "," at private"]]
["W0176",[2248,2248,117134,117138],[2243,2243,114024,114030],"HEAD","source",["at private "," \\nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed.} Its"]]
["W0177",[2248,2248,117139,117192],[2243,2243,114031,114233],"\\nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed.}","revision \\nolinkurl{bfeb8400982c9a169e4fdd39fb68ec053621e8ed}. Section~\\ref{q214:rows} prints the residuals used here; the revision identifies the historical artifact, not that later manuscript section.",["private HEAD "," Its parameter"]]
["W0178",[2257,2257,118489,118494],[2252,2252,115530,115536],"later","source",["here. The "," audit records"]]
["W0179",[2257,2257,118495,118500],[2252,2252,115537,115547],"audit","statements",["The later "," records can"]]
["W0180",[2257,2257,118501,118508],[2252,2252,115548,115551],"records","are",["later audit "," can justify"]]
["W0181",[2257,2257,118509,118549],[2252,2252,115552,115556],"can justify exact unchanged applications","used",["audit records "," at their"]]
["W0182",[2257,2257,118566,118571],[2252,2252,115573,115580],"scope","domains",["their stated "," only after"]]
["W0183",[2257,2257,118572,118576],[2252,2252,115581,115584],"only","and",["stated scope "," after source/consumer"]]
["W0184",[2257,2257,118577,118667],[2252,2252,115585,115592],"after source/consumer comparison; PR status is not an arithmetic premise. This author read","through",["scope only "," the actual"]]
["W0185",[2257,2257,118672,118678],[2252,2252,115597,115646],"actual","source-to-consumer maps. The application uses the",["read the "," source passages"]]
["W0186",[2257,2257,118933,118970],[2252,2252,115901,115906],"This author did not reconstruct every","Their",["zero-preparation proof. "," internal RC/analytic"]]
["W0187",[2257,2257,118980,118991],[2252,2252,115916,115935],"RC/analytic","restricted-converse",["every internal "," sublemma or"]]
["W0188",[2257,2257,118992,119000],[2252,2252,115936,115939],"sublemma","and",["internal RC/analytic "," or final"]]
["W0189",[2257,2257,119001,119057],[2252,2252,115940,115948],"or final published source anew. Those unchanged internal","analytic",["RC/analytic sublemma "," foundations and"]]
["W0190",[2257,2257,119070,119103],[2252,2252,115961,115961],"and their eligible source review ","",["internal foundations ","remain a "]]
["W0191",[2257,2257,119110,119111],[2252,2252,115968,115976],"a","separate",["review remain "," separately bound"]]
["W0192",[2257,2257,119112,119221],[2252,2252,115977,115991],"separately bound dependency; this packet closes the 214 application joins, not their entire recursive review.","prerequisites.",["remain a ","\n"]]
["W0193",[2259,2259,119680,119698],[2254,2254,116450,116467],"\\) union(2-Theta),","\\cup(2-\\Theta)\\),",["\\(\\Theta _{2}=\\Theta "," \\(\\Theta =\\{0,-1/2,-1,1/2399,-32/407\\}\\);"]]
["W0194",[2261,2261,120160,120166],[2256,2256,116929,116936],"raw224","raw 224",["clearing and "," inverse maps"]]
["W0195",[2261,2261,120310,120315],[2256,2256,117080,117086],"at149","at 149",["\\(Q_{2}\\) coefficient "," imply \\(w=g^{4}/f^{2}\\);"]]
["W0196",[2273,2273,122282,122289],[2268,2268,119053,119061],"modulo4","modulo 4",["\\), 2 "," and the"]]
["W0197",[2273,2273,122303,122306],[2268,2268,119075,119077],"is4","is",["the last "," modulo8. They"]]
["W0198",[2273,2273,122307,122315],[2268,2268,119078,119089],"modulo8.","4 modulo 8.",["last is4 "," They are"]]
["W0199",[2273,2273,122459,122467],[2268,2268,119233,119242],"residue1","residue 1",["and has "," whenever its"]]
["W0200",[2275,2275,122748,122771],[2270,2270,119523,119551],"\\(w_{0}^{2}-2w_{0}*\\tau","\\(w_{0}^{2}-2w_{0}\\cdot \\tau",["trace equation "," -2w_{1}^{2}=0\\), with"]]
["W0201",[2275,2275,122794,122821],[2270,2270,119574,119606],"\\(W=w_{0}+\\sqrt{2}*w_{1}\\),","\\(W=w_{0}+\\sqrt{2}\\cdot w_{1}\\),",["-2w_{1}^{2}=0\\), with "," forces \\(w_{0}\\ne"]]
["W0202",[2275,2275,123228,123241],[2270,2270,120013,120027],"outside2,3,17","outside 2,3,17",["odd valuations "," and hence"]]
["W0203",[2277,2277,124496,124502],[2272,2272,121282,121289],"order4","order 4",["error of "," used as"]]
["W0204",[2280,2280,124664,124690],[2275,2275,121451,121482],"=t^{2}-a(a-2)t*b+(a-2)^{2}","=t^{2}-a(a-2)t\\cdot b+(a-2)^{2}",["\\Delta "," b^{2}-1,\n"]]
["W0205",[2287,2287,126196,126206],[2282,2282,122988,122994],"Buhren2017","Buhren",["published Von "," Theorem1.1, printed308,"]]
["W0206",[2287,2287,126207,126218],[2282,2282,122995,122999],"Theorem1.1,","2017",["Von Buhren2017 "," printed308, to"]]
["W0207",[2287,2287,126219,126230],[2282,2282,123000,123025],"printed308,","Theorem 1.1, printed 308,",["Buhren2017 Theorem1.1, "," to \\(A=E_{0}^{8}\\),"]]
["W0208",[2287,2287,126577,126584],[2282,2282,123372,123380],"point0.","point 0.",["taking error "," Embed \\(E_{0}\\)"]]
["W0209",[2287,2287,126885,126899],[2282,2282,123681,123696],"condition(1.1)","condition (1.1)",["source's embedding "," for the"]]
["W0210",[2289,2289,128103,128113],[2284,2284,124900,124908],"separately","separate",["remains a "," reviewed interface."]]
["W0211",[2289,2289,128114,128133],[2284,2284,124909,124922],"reviewed interface.","prerequisite.",["a separately "," Put \\(B_{\\Sigma"]]
["W0212",[2289,2289,128603,128607],[2284,2284,125392,125395],"are3","are",["row norms "," and7. If"]]
["W0213",[2289,2289,128608,128613],[2284,2284,125396,125404],"and7.","3 and 7.",["norms are3 "," If \\(h(t_{j})>\\log"]]
["W0214",[2297,2297,129511,129563],[2292,2292,126302,126364],"C_{3}*149^{-{L}_{N}}*c(1+\\operatorname{log}(c)/3)\\),","C_{3}\\cdot 149^{-{L}_{N}}\\cdot c(1+\\operatorname{log}(c)/3)\\),",["\\(h(\\beta )\\le "," \\(C_{3}=2^{330770}\\), \\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\)."]]
["W0215",[2297,2297,129586,129622],[2292,2292,126387,126435],"\\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\).","\\(L_{N}=\\left\\lfloor 9(2N-1)/4\\right\\rfloor+1\\).",["C_{3}*149^{-{L}_{N}}*c(1+\\operatorname{log}(c)/3)\\), \\(C_{3}=2^{330770}\\), "," This uses"]]
["W0216",[2297,2297,129731,129749],[2292,2292,126544,126567],"\\(D=C*14^{7/18}\\).","\\(D=C\\cdot 14^{7/18}\\).",["\\(B^{14/9}+M_{2}\\) where "," Hence \\(B\\le"]]
["W0217",[2299,2299,130226,130250],[2294,2294,127044,127078],"\\(t^{2}-c*t*w+w^{2}=1\\).","\\(t^{2}-c\\cdot t\\cdot w+w^{2}=1\\).",["\\(w=\\text{sign}(a)(a-2)b\\). Then "," The elementary"]]
["W0218",[2303,2303,130909,130939],[2298,2298,127737,127772],"_{N}=(7/5)C_{3}*149^{-{L}_{N}}","_{N}=(7/5)C_{3}\\cdot 149^{-{L}_{N}}",["2, \\epsilon ","\n"]]
["W0219",[2313,2313,131547,131554],[2308,2308,128380,128388],"since51","since 51",["forces \\(v^{2}|51\\); "," is squarefree,"]]
["W0220",[2324,2324,133162,133169],[2319,2319,129996,130004],"equal1;","equal 1;",["\\(\\text{gcd}(A_{N} r_{4}+9792D_{s},D_{s})\\) "," thus \\(R_{s}(R_{s}+9792)\\)"]]
["W0221",[2324,2324,133383,133391],[2319,2319,130218,130227],"at2,3,17","at 2,3,17",["a square "," \\((\\text{its} \\text{difference}"]]
["W0222",[2324,2324,133850,133858],[2319,2319,130686,130695],"at2,3,17","at 2,3,17",["deep enough "," for the"]]
["W0223",[2326,2326,135555,135567],[2321,2321,132392,132405],"coefficient0","coefficient 0",["contact supplies "," and the"]]
["W0224",[2328,2328,135803,135848],[2323,2323,132641,132683],"\\(M=\\operatorname{rad}_{\\text{odd}}(3*17*L)\\)","\\(M=\\operatorname{rad}_{\\text{odd}}(3\\cdot",["avoidance modulus "," with7 omitted,"]]
["W0225",[2328,2328,135849,135854],[2323,2323,132684,132703],"with7","17\\cdot L)\\) with 7",["modulus \\(M=\\operatorname{rad}_{\\text{odd}}(3*17*L)\\) "," omitted, and"]]
["W0226",[2328,2328,136367,136376],[2323,2323,133216,133224],"residues9","residues",["generators have "," mod16,1+3i mod7,i"]]
["W0227",[2328,2328,136377,136387],[2323,2323,133225,133226],"mod16,1+3i","9",["have residues9 "," mod7,i modM;"]]
["W0228",[2328,2328,136388,136394],[2323,2323,133227,133246],"mod7,i","mod 16,1+3i mod 7,i",["residues9 mod16,1+3i "," modM; adjacent"]]
["W0229",[2328,2328,136416,136452],[2323,2323,133268,133283],"\\(d_{\\text{minus}},d_{\\text{plus}}\\)","\\(d_{-},d_{+}\\)",["adjacent norms "," have \\(v_{2}=6,2\\)"]]
["W0230",[2328,2328,136487,136492],[2323,2323,133318,133324],"gcd4,","gcd 4,",["and cross-sign "," and all"]]
["W0231",[2328,2328,136533,136570],[2323,2323,133365,133391],"\\(U=\\text{lcm}(d_{\\text{minus}}/4)\\),","\\(U=\\text{lcm}(d_{-}/4)\\),",["\\(L\\). Define "," \\(V=\\text{lcm}(d_{\\text{plus}}/4)\\). Full"]]
["W0232",[2328,2328,136571,136607],[2323,2323,133392,133418],"\\(V=\\text{lcm}(d_{\\text{plus}}/4)\\).","\\(V=\\text{lcm}(d_{+}/4)\\).",["Define \\(U=\\text{lcm}(d_{\\text{minus}}/4)\\), "," Full two-torsion"]]
["W0233",[2328,2328,136791,136802],[2323,2323,133602,133611],"\\(h=h_{*}\\)","\\(h=h_*\\)",["mod \\(V\\), "," mod \\(L\\)"]]
["W0234",[2328,2328,137244,137250],[2323,2323,134053,134060],"depth1","depth 1",["argument; natural "," alone suffices"]]
["W0235",[2330,2330,137697,137703],[2325,2325,134507,134514],"depth1","depth 1",["numerator has "," in each"]]
["W0236",[2330,2330,137931,137938],[2325,2325,134742,134750],"error4.","error 4.",["relative formal "," The changed"]]
["W0237",[2330,2330,138327,138330],[2325,2325,135139,135141],"to0","to",["\\(W^{-1}\\) reduces "," or1, so"]]
["W0238",[2330,2330,138331,138335],[2325,2325,135142,135149],"or1,","0 or 1,",["reduces to0 "," so \\(\\operatorname{Tr}(W^{-1})\\)"]]
["W0239",[2330,2330,138377,138380],[2325,2325,135191,135193],"to1","to",["\\(\\operatorname{Tr}(W^{-1})\\) reduces "," or2, a"]]
["W0240",[2330,2330,138381,138385],[2325,2325,135194,135201],"or2,","1 or 2,",["reduces to1 "," a unit"]]
["W0241",[2330,2330,138460,138470],[2325,2325,135276,135287],"valuation1","valuation 1",["\\(\\mathfrak{b}\\) has "," there. This"]]
["W0242",[2339,2339,139287,139290],[2334,2334,136104,136108],"to1","to 1",["as close "," as needed"]]
["W0243",[2339,2339,139522,139526],[2334,2334,136340,136345],"to2.","to 2.",["is close "," Choose closeness"]]
["W0244",[2339,2339,139565,139574],[2334,2334,136384,136394],"at2,3,17.","at 2,3,17.",["a square "," As \\(v_{2}(\\gamma"]]
["W0245",[2339,2339,139686,139698],[2334,2334,136506,136519],"depths4,2,2.","depths 4,2,2.",["square with "," At both"]]
["W0246",[2339,2339,139861,139865],[2334,2334,136682,136687],"to0;","to 0;",["\\(q>0\\) tends "," all factors"]]
["W0247",[2339,2339,139907,139911],[2334,2334,136729,136734],"to1.","to 1.",["\\(W\\) tends "," Thus \\(\\mathfrak{b}\\)"]]
["W0248",[2339,2339,139961,139970],[2334,2334,136784,136794],"in(0,17).","in (0,17).",["\\(\\gamma ^{2}/4\\) "," The prime"]]
["W0249",[2341,2341,140327,140335],[2336,2336,137151,137160],"at2,3,17","at 2,3,17",["local squares "," and depths4,2,2,"]]
["W0250",[2341,2341,140340,140352],[2336,2336,137165,137178],"depths4,2,2,","depths 4,2,2,",["at2,3,17 and "," meeting the"]]
["W0251",[2341,2341,140411,140426],[2336,2336,137237,137253],"requires3,1,2).","requires 3,1,2).",["Psi0 (source "," In its"]]
["W0252",[2341,2341,140614,140626],[2336,2336,137441,137454],"avoiding2,3,","avoiding 2,3,",["disjoint support "," \\(\\mu =17\\)"]]
["W0253",[2341,2341,140666,140672],[2336,2336,137494,137501],"mod24,","mod 24,",["\\(\\text{mod}24,\\theta =1\\) "," mutual local"]]
["W0254",[2341,2341,140718,140725],[2336,2336,137547,137555],"equal1.","equal 1.",["\\) may "," The simultaneous-descent"]]
["W0255",[2341,2341,140837,140843],[2336,2336,137667,137671],"both11","both",["\\(\\theta \\), "," mod12 and"]]
["W0256",[2341,2341,140844,140849],[2336,2336,137672,137681],"mod12","11 mod 12",["\\), both11 "," and with"]]
["W0257",[2341,2341,140859,140872],[2336,2336,137691,137705],"full2-primary","full 2-primary",["and with "," Selmer corank1;"]]
["W0258",[2341,2341,140880,140888],[2336,2336,137713,137722],"corank1;","corank 1;",["full2-primary Selmer "," this uses"]]
["W0259",[2341,2341,141064,141070],[2336,2336,137898,137905],"mod12.","mod 12.",["} ,l=11\\) "," These curves"]]
["W0260",[2341,2341,141318,141323],[2336,2336,138153,138159],"rank1","rank 1",["then gives "," and finite"]]
["W0261",[2343,2343,142082,142088],[2338,2338,138918,138925],"raw224","raw 224",["the exact "," coordinate maps"]]
["W0262",[2343,2343,142558,142596],[2338,2338,139395,139397],"This author did \\textbf{not} produce a","No",["retained interfaces. "," full numerical"]]
["W0263",[2343,2343,142624,142630],[2338,2338,139425,139443],"tuple,","tuple is supplied,",["214 witness "," even for"]]
["W0264",[2343,2343,142706,142726],[2338,2338,139519,139521],"This packet gives no","No",["universal completeness. "," numerical defining"]]
["W0265",[2343,2343,142746,142756],[2338,2338,139541,139550],"threshold,","threshold",["numerical defining "," no Busy"]]
["W0266",[2343,2343,142757,142759],[2338,2338,139551,139553],"no","or",["defining threshold, "," Busy Beaver"]]
["W0267",[2343,2343,142784,142796],[2338,2338,139578,139589],"replacement,","replacement",["Beaver coefficient "," no independent"]]
["W0268",[2343,2343,142797,142799],[2338,2338,139590,139592],"no","is",["coefficient replacement, "," independent acceptance"]]
["W0269",[2343,2343,142800,142811],[2338,2338,139593,139602],"independent","provided.",["replacement, no "," acceptance of"]]
["W0270",[2343,2343,142812,142931],[2338,2338,139603,139606],"acceptance of itself. Full Protocol \\(D\\) closure additionally requires the fresh eligible review and exact assembly of","The",["no independent "," unchanged RC/analytic"]]
["W0271",[2343,2343,142942,142953],[2338,2338,139617,139646],"RC/analytic","restricted-converse, analytic",["of unchanged "," and height"]]
["W0272",[2343,2343,142965,142977],[2338,2338,139658,139669],"foundations,","foundations",["and height "," not a"]]
["W0273",[2343,2343,142978,142981],[2338,2338,139670,139676],"not","remain",["height foundations, "," a green"]]
["W0274",[2343,2343,142982,142983],[2338,2338,139677,139685],"a","separate",["foundations, not "," green structural"]]
["W0275",[2343,2343,142984,143007],[2338,2338,139686,139700],"green structural check.","prerequisites.",["not a ","\n"]]
["W0276",[2349,2349,143281,143559],[2344,2344,139974,139974],"Author supplement to \\(\\text{AUTHOR}_{{\\text{FREEZE}}_{001}}\\), \\nolinkurl{/root/d214_modularity_closure}, 11 November 2026. Author proposal, pending nonauthor acceptance. This checks the actual earlier arguments and the changed application; it supplies no independent approval.","",["","\n"]]
["W0277",[2353,2353,143854,143873],[2348,2348,140269,140273],"merely by accepting","from",["fine cover "," its modular"]]
["W0278",[2353,2353,143878,143885],[2348,2348,140278,140291],"modular","modular-curve",["accepting its "," curve. V15-FOUNDATION's"]]
["W0279",[2353,2353,143886,143892],[2348,2348,140292,140302],"curve.","assertion.",["its modular "," V15-FOUNDATION's third"]]
["W0280",[2353,2353,144039,144101],[2348,2348,140449,140449]," These are locator corrections, not new arithmetic objections.","",[" argument either.","\n"]]
["W0281",[2355,2355,144321,144329],[2350,2350,140669,140673],"most324.","most",["degree at "," Reading their"]]
["W0282",[2355,2355,144330,144382],[2350,2350,140674,140678],"Reading their actual proofs exposed this difference.","324.",["at most324. "," They must"]]
["W0283",[2355,2355,144420,144435],[2350,2350,140716,140732],"discriminant210","discriminant 210",["for the "," \\(H_{01}\\) surface"]]
["W0284",[2355,2355,144458,144468],[2350,2350,140755,140761],"degree576.","degree",["surface of "," A preliminary"]]
["W0285",[2355,2355,144469,144579],[2350,2350,140762,140766],"A preliminary author message listing those \\(H_{6}\\) cards as if they were \\(H_{01}\\) providers was too broad.","576.",["of degree576. "," The actual"]]
["W0286",[2357,2357,144863,144866],[2352,2352,141050,141060],"old","historical",["The "," private \\(\\text{FOUNDATION}_{\\text{MAP}}\\)"]]
["W0287",[2357,2357,144867,144874],[2352,2352,141061,141071],"private","foundation",["The old "," \\(\\text{FOUNDATION}_{\\text{MAP}}\\) F-H01-GEOMETRY"]]
["W0288",[2357,2357,144875,144909],[2352,2352,141072,141075],"\\(\\text{FOUNDATION}_{\\text{MAP}}\\)","map",["old private "," F-H01-GEOMETRY already"]]
["W0289",[2357,2357,144910,144924],[2352,2352,141076,141086],"F-H01-GEOMETRY","identifies",["private \\(\\text{FOUNDATION}_{\\text{MAP}}\\) "," already points"]]
["W0290",[2357,2357,144925,144932],[2352,2352,141087,141090],"already","the",["\\(\\text{FOUNDATION}_{\\text{MAP}}\\) F-H01-GEOMETRY "," points to"]]
["W0291",[2357,2357,144933,144939],[2352,2352,141091,141107],"points","discriminant-210",["F-H01-GEOMETRY already "," to frozen"]]
["W0292",[2357,2357,144940,144990],[2352,2352,141108,141120],"to frozen \\(V_{14}\\) lines7605--8040 and8517--8655","construction",["already points "," and the"]]
["W0293",[2357,2357,144995,144999],[2352,2352,141125,141125],"the ","",["and8517--8655 and ","cutoff proof. "]]
["W0294",[2357,2357,145006,145012],[2352,2352,141132,141138],"proof.","proof,",["the cutoff "," Its REPORT"]]
["W0295",[2357,2357,145013,145016],[2352,2352,141139,141143],"Its","with",["cutoff proof. "," REPORT explicitly"]]
["W0296",[2357,2357,145017,145023],[2352,2352,141144,141149],"REPORT","their",["proof. Its "," explicitly retains"]]
["W0297",[2357,2357,145024,145034],[2352,2352,141150,141156],"explicitly","source",["Its REPORT "," retains \\(H_{01}\\)"]]
["W0298",[2357,2357,145035,145042],[2352,2352,141157,141172],"retains","qualifications.",["REPORT explicitly "," \\(H_{01}\\) source-closure"]]
["W0299",[2357,2357,145043,145079],[2352,2352,141173,141175],"\\(H_{01}\\) source-closure limits; it","It",["explicitly retains "," does not"]]
["W0300",[2357,2357,145089,145097],[2352,2352,141185,141188],"identify","use",["does not "," the D6/B11"]]
["W0301",[2357,2357,145102,145108],[2352,2352,141193,141209],"D6/B11","discriminant-six",["identify the "," construction as"]]
["W0302",[2357,2357,145122,145124],[2352,2352,141223,141225],"as","to",["D6/B11 construction "," proof of"]]
["W0303",[2357,2357,145125,145219],[2352,2352,141226,141232],"proof of the \\(D_{210}\\) field. Thus the newly corrected locator suggestion is not an error in","supply",["construction as "," that old"]]
["W0304",[2357,2357,145225,145265],[2352,2352,141238,141244],"old map. The old files remain untouched.","field.",["in that ","\n"]]
["W0305",[2361,2361,145532,145541],[2356,2356,141511,141511]," accepted","",[" \\(V_{15}\\) at"," PR26 head1a49013b."]]
["W0306",[2365,2365,146624,146663],[2360,2360,142594,142597],"\\nolinkurl{PUBLIC_GEOMETRY_SCOPES.json}","The",[""," extracts the"]]
["W0307",[2365,2365,146664,146672],[2360,2360,142598,142630],"extracts","retained source statements cover",["\\nolinkurl{PUBLIC_GEOMETRY_SCOPES.json} "," the precise"]]
["W0308",[2365,2365,146677,146684],[2360,2360,142635,142646],"precise","\\(D_{210}\\)",["extracts the "," final006 coverage"]]
["W0309",[2365,2365,146685,146693],[2360,2360,142647,142652],"final006","fiber",["the precise "," coverage decisions"]]
["W0310",[2365,2365,146694,146702],[2360,2360,142653,142658],"coverage","field",["precise final006 "," decisions for"]]
["W0311",[2365,2365,146703,146712],[2360,2360,142659,142841],"decisions","and geometric isogenies, the CM elliptic discriminant, CM height and GR2023 comparison, and Yuan's model, integral and metric applications. Their stated prerequisites remain required",["final006 coverage "," for ACTIVE-H19-D210-FIBER-FIELD,"]]
["W0312",[2365,2365,146717,147039],[2360,2360,142846,142846],"ACTIVE-H19-D210-FIBER-FIELD, ACTIVE-H19-D210-GEOMETRIC-ISOGENIES, ACTIVE-H19-CM-ELLIPTIC-DISCRIMINANT, ACTIVE-H19-CM-HEIGHT, ACTIVE-H19-CM-GR2023 and CURRENT-YUAN-MODEL/INTEGRAL/METRIC. These decisions reuse exact retained derivations and explicitly preserve their prerequisites. They are evidence of public acceptance at ","",["decisions for ","the recorded "]]
["W0313",[2365,2365,147042,147103],[2360,2360,142849,142849]," recorded scope, not a newly authored approval of the private","",[" at the"," \\(S_{10}\\) application."]]
["W0314",[2367,2367,147132,147144],[2362,2362,142878,142878]," actual full","",["The"," \\(D_{210}\\) source"]]
["W0315",[2367,2367,147169,147190],[2362,2362,142903,142903]," was read in full. It","",[" source proof"," constructs \\(\\text{Isom}_{O}(O/3O,A[3])\\),"]]
["W0316",[2367,2367,147276,147286],[2362,2362,142989,143000],"ramified3.","ramified 3.",["assertion at "," It distinguishes"]]
["W0317",[2367,2367,147318,147327],[2362,2362,143032,143042],"degree72,","degree 72,",["stack marking "," coarse degree36"]]
["W0318",[2367,2367,147335,147343],[2362,2362,143050,143059],"degree36","degree 36",["degree72, coarse "," and normalizer"]]
["W0319",[2367,2367,147359,147368],[2362,2362,143075,143085],"order576;","order 576;",["and normalizer "," proves trivial"]]
["W0320",[2367,2367,147653,147664],[2362,2362,143370,143382],"general8.17","general 8.17",["the corrected "," implication. Its"]]
["W0321",[2367,2367,147835,147855],[2362,2362,143553,143575],"Lemma2.1/Theorem2.2.","Lemma 2.1/Theorem 2.2.",["disputed coarse ","\n"]]
["W0322",[2369,2369,147857,147902],[2364,2364,143577,143580],"\\nolinkurl{GEOMETRY_PROVIDER_COMPARISON.json}","The",[""," honestly records"]]
["W0323",[2369,2369,147903,147911],[2364,2364,143581,143587],"honestly","source",["\\nolinkurl{GEOMETRY_PROVIDER_COMPARISON.json} "," records that"]]
["W0324",[2369,2369,147912,147919],[2364,2364,143588,143598],"records","comparison",["\\nolinkurl{GEOMETRY_PROVIDER_COMPARISON.json} honestly "," that these"]]
["W0325",[2369,2369,147920,147924],[2364,2364,143599,143610],"that","establishes",["honestly records "," these separately"]]
["W0326",[2369,2369,147925,147930],[2364,2364,143611,143685],"these","equality of the integrated proof text, without asserting byte equality for",["records that "," separately packaged"]]
["W0327",[2369,2369,147951,147960],[2364,2364,143706,143706],"supplier ","",["separately packaged ","files were "]]
["W0328",[2369,2369,147966,147970],[2364,2364,143712,143718],"were","absent",["supplier files "," not found"]]
["W0329",[2369,2369,147971,147986],[2364,2364,143719,143723],"not found under","from",["files were "," the queried"]]
["W0330",[2369,2369,147991,147998],[2364,2364,143728,143738],"queried","historical",["under the "," \\nolinkurl{current/...} names"]]
["W0331",[2369,2369,147999,148117],[2364,2364,143739,143747],"\\nolinkurl{current/...} names in the old private handoff zip. No byte equality of an absent archive member is claimed.","archive.",["the queried "," The \\textbf{integrated"]]
["W0332",[2369,2369,148121,148212],[2364,2364,143751,143751]," \\textbf{integrated proof text} equality above is established independently, and the actual","",[" claimed. The"," publicly retained"]]
["W0333",[2369,2369,148231,148231],[2364,2364,143770,143782],"","\\(D_{210}\\) ",["publicly retained ","supplier is "]]
["W0334",[2369,2369,148240,148308],[2364,2364,143791,143794],"is pinned and read. Its prior \\(D_{210}\\) index explicitly preserved","has",["retained supplier "," five source-prerequisite"]]
["W0335",[2369,2369,148334,148342],[2364,2364,143820,143828],"bundles;","bundles.",["five source-prerequisite "," public final006"]]
["W0336",[2369,2369,148343,148349],[2364,2364,143829,143834],"public","Those",["source-prerequisite bundles; "," final006 acceptance"]]
["W0337",[2369,2369,148350,148358],[2364,2364,143835,143845],"final006","transitive",["bundles; public "," acceptance preserves"]]
["W0338",[2369,2369,148359,148369],[2364,2364,143846,143859],"acceptance","prerequisites",["public final006 "," preserves its"]]
["W0339",[2369,2369,148370,148379],[2364,2364,143860,143866],"preserves","remain",["final006 acceptance "," its exact"]]
["W0340",[2369,2369,148380,148383],[2364,2364,143867,143876],"its","required;",["acceptance preserves "," exact source"]]
["W0341",[2369,2369,148384,148389],[2364,2364,143877,143880],"exact","the",["preserves its "," source scope."]]
["W0342",[2369,2369,148390,148396],[2364,2364,143881,143886],"source","index",["its exact "," scope. This"]]
["W0343",[2369,2369,148397,148419],[2364,2364,143887,143892],"scope. This supplement","alone",["exact source "," does not"]]
["W0344",[2369,2369,148429,148434],[2364,2364,143902,143911],"infer","establish",["does not "," resolution of"]]
["W0345",[2369,2369,148435,148527],[2364,2364,143912,143917],"resolution of any unexamined transitive prerequisite solely from that index or a PASS label.","them.",["not infer ","\n"]]
["W0346",[2373,2373,148962,148971],[2368,2368,144352,144362],"order576.","order 576.",["\\) of "," Its commuting"]]
["W0347",[2373,2373,149056,149065],[2368,2368,144447,144457],"order576.","order 576.",["also of "," The normal"]]
["W0348",[2375,2375,149558,149566],[2370,2370,144950,144959],"modulo3,","modulo 3,",["is trivial "," and the"]]
["W0349",[2375,2375,149605,149609],[2370,2370,144998,145003],"mod3","mod 3",["congruence subgroup "," is torsion-free;"]]
["W0350",[2377,2377,150201,150212],[2372,2372,145595,145607],"exponent19,","exponent 19,",["the old "," the large-primorial"]]
["W0351",[2393,2393,150840,150863],[2388,2388,146235,146252],"\\(2400=2^{5}*3*5^{2}\\),","\\(2400=2^{5}\\cdot",["\\(2401=7^{4}\\), \\(343=7^{3}\\), "," \\(375=3*5^{3}\\), \\(77175=3^{2}*5^{2}*7^{3}\\)."]]
["W0352",[2393,2393,150864,150880],[2388,2388,146253,146259],"\\(375=3*5^{3}\\),","3\\cdot",["\\(343=7^{3}\\), \\(2400=2^{5}*3*5^{2}\\), "," \\(77175=3^{2}*5^{2}*7^{3}\\). Hence"]]
["W0353",[2393,2393,150881,150909],[2388,2388,146260,146329],"\\(77175=3^{2}*5^{2}*7^{3}\\).","5^{2}\\), \\(375=3\\cdot 5^{3}\\), \\(77175=3^{2}\\cdot 5^{2}\\cdot 7^{3}\\).",["\\(2400=2^{5}*3*5^{2}\\), \\(375=3*5^{3}\\), "," Hence the"]]
["W0354",[2398,2398,151609,151618],[2393,2393,147029,147039],"because32","because 32",["are units "," is a"]]
["W0355",[2399,2399,151973,151978],[2394,2394,147394,147400],"and32","and 32",["all \\(v\\) "," denominators are"]]
["W0356",[2403,2403,152720,152731],[2398,2398,148142,148154],"cutoff76176","cutoff 76176",["with no "," hypothesis.\n"]]
["W0357",[2405,2405,152873,152881],[2400,2400,148296,148305],"over210,","over 210,",["places not "," irrespective of"]]
["W0358",[2407,2407,153731,153737],[2402,2402,149155,149162],"than7,","than 7,",["but larger "," and arbitrarily"]]
["W0359",[2411,2411,154039,154063],[2406,2406,149464,149489],"values(0,32,76832,-343),","values (0,32,76832,-343),",["\\(t=32a\\), branch "," sections \\(q_{0}=(dt)^{2}/P(t),q_{1}=tq_{0}\\),"]]
["W0360",[2411,2411,154115,154146],[2406,2406,149541,149587],"\\(J=2^{10}*3^{2}*5^{3}*7^{4}\\).","\\(J=2^{10}\\cdot 3^{2}\\cdot 5^{3}\\cdot 7^{4}\\).",["\\(q_{0}=(dt)^{2}/P(t),q_{1}=tq_{0}\\), and "," The actual"]]
["W0361",[2411,2411,154266,154288],[2406,2406,149707,149730],"\\(by4C_{\\text{met}}\\).","by \\(4C_{\\text{met}}\\).",["Petersson norms "," Yuan's final"]]
["W0362",[2417,2417,154467,154473],[2412,2412,149909,149916],"log210","log 210",["The positive "," sign is"]]
["W0363",[2417,2417,154552,154566],[2412,2412,149995,150010],"\\(by120<128\\),","by \\(120<128\\),",["additive term "," so\n"]]
["W0364",[2427,2427,155840,155852],[2422,2422,151284,151297],"multiplier4.","multiplier 4.",["the dyadic "," The individual-embedding"]]
["W0365",[2427,2427,155982,156001],[2422,2422,151427,151444],"Gaudron--Rémond2023","Gaudron--R\\'emond",["general dimension-two "," Theorem1.9(1), over"]]
["W0366",[2427,2427,156002,156016],[2422,2422,151445,151465],"Theorem1.9(1),","2023 Theorem 1.9(1),",["dimension-two Gaudron--Rémond2023 "," over \\(L\\)"]]
["W0367",[2433,2433,156523,156531],[2428,2428,151972,151978],"final006","source",["estimate. The "," H19-CM records"]]
["W0368",[2433,2433,156532,156538],[2428,2428,151979,151988],"H19-CM","interface",["The final006 "," records explicitly"]]
["W0369",[2433,2433,156539,156568],[2428,2428,151989,151991],"records explicitly state this","is",["final006 H19-CM "," universally quantified"]]
["W0370",[2433,2433,156592,156592],[2428,2428,152015,152020],"","over ",["universally quantified ","\\(R\\ge 1\\) "]]
["W0371",[2433,2433,156599,156613],[2428,2428,152027,152031],"1\\) interface.","1\\).",["quantified \\(R\\ge "," This is"]]
["W0372",[2435,2435,156722,156734],[2430,2430,152140,152145],"Dispositions","Scope",["\\subsection{\\(G_{5}\\). "," and acceptance"]]
["W0373",[2435,2435,156735,156738],[2430,2430,152146,152148],"and","of",["\\subsection{\\(G_{5}\\). Dispositions "," acceptance boundary}"]]
["W0374",[2435,2435,156739,156749],[2430,2430,152149,152152],"acceptance","the",["Dispositions and "," boundary}\n"]]
["W0375",[2435,2435,156750,156759],[2430,2430,152153,152174],"boundary}","geometric comparison}",["and acceptance ","\n"]]
["W0376",[2437,2437,156761,156910],[2432,2432,152176,152176],"Historical classification: prior substantive justification found and read for the actual \\(D_{210}\\) cover, same-L Hom, metric and CM854R arguments. ","",["","The \\(S_{10}\\) "]]
["W0377",[2437,2437,156952,156960],[2432,2432,152218,152218]," already","",[" cutoff/local-support bridge"," appears in"]]
["W0378",[2437,2437,156987,156993],[2432,2432,152245,152251],"\\S{}1;","\\S{}1.",["private cutoff "," this supplement"]]
["W0379",[2437,2437,156994,156998],[2432,2432,152252,152255],"this","The",["cutoff \\S{}1; "," supplement verifies"]]
["W0380",[2437,2437,156999,157009],[2432,2432,152256,152266],"supplement","comparison",["\\S{}1; this "," verifies its"]]
["W0381",[2437,2437,157010,157018],[2432,2432,152267,152281],"verifies","above includes",["this supplement "," its full"]]
["W0382",[2437,2437,157074,157088],[2432,2432,152337,152344],"primary-object","primary",["and exact "," joins. It"]]
["W0383",[2437,2437,157089,157305],[2432,2432,152345,152353],"joins. It is not claimed as a newly discovered missing arithmetic argument. Private heightH0 states these inputs but leaves their source qualifications inherited; incorporation of this additive comparison is pending.","objects.",["exact primary-object ","\n"]]
["W0384",[2439,2439,157307,157334],[2434,2434,152355,152355],"Current author conclusion: ","",["","H01's change "]]
["W0385",[2439,2439,157407,157411],[2434,2434,152428,152436],"once","provided",["mathematical hypothesis "," the retained"]]
["W0386",[2439,2439,157455,157467],[2434,2434,152480,152484],"are supplied","hold",["source statements "," at their"]]
["W0387",[2439,2439,157471,157476],[2434,2434,152488,152491],"their","the",["supplied at "," public accepted"]]
["W0388",[2439,2439,157477,157483],[2434,2434,152492,152498],"public","scopes",["at their "," accepted scopes."]]
["W0389",[2439,2439,157484,157492],[2434,2434,152499,152508],"accepted","specified",["their public "," scopes. The"]]
["W0390",[2439,2439,157493,157500],[2434,2434,152509,152514],"scopes.","here.",["public accepted "," The source-to-private"]]
["W0391",[2439,2439,157501,157504],[2434,2434,152515,152520],"The","Their",["accepted scopes. "," source-to-private application"]]
["W0392",[2439,2439,157505,157522],[2434,2434,152521,152531],"source-to-private","transitive",["scopes. The "," application and"]]
["W0393",[2439,2439,157523,157534],[2434,2434,152532,152538],"application","source",["The source-to-private "," and its"]]
["W0394",[2439,2439,157535,157538],[2434,2434,152539,152552],"and","prerequisites",["source-to-private application "," its consumer"]]
["W0395",[2439,2439,157539,157542],[2434,2434,152553,152559],"its","remain",["application and "," consumer are"]]
["W0396",[2439,2439,157543,157551],[2434,2434,152560,152569],"consumer","required:",["and its "," are now"]]
["W0397",[2439,2439,157552,157608],[2434,2434,152570,152577],"are now explicit. This is an author conclusion, awaiting","neither",["its consumer "," the assigned"]]
["W0398",[2439,2439,157613,157621],[2434,2434,152582,152597],"assigned","ten-determinant",["awaiting the "," nonauthor reviewer."]]
["W0399",[2439,2439,157622,157631],[2434,2434,152598,152609],"nonauthor","calculation",["the assigned "," reviewer. Public"]]
["W0400",[2439,2439,157632,157641],[2434,2434,152610,152613],"reviewer.","nor",["assigned nonauthor "," Public final006's"]]
["W0401",[2439,2439,157642,157648],[2434,2434,152614,152617],"Public","the",["nonauthor reviewer. "," final006's scoped"]]
["W0402",[2439,2439,157649,157659],[2434,2434,152618,152624],"final006's","source",["reviewer. Public "," scoped approvals"]]
["W0403",[2439,2439,157660,157666],[2434,2434,152625,152630],"scoped","index",["Public final006's "," approvals and"]]
["W0404",[2439,2439,157667,157676],[2434,2434,152631,152642],"approvals","establishes",["final006's scoped "," and byte"]]
["W0405",[2439,2439,157677,157680],[2434,2434,152643,152648],"and","those",["scoped approvals "," byte identity"]]
["W0406",[2439,2439,157681,157760],[2434,2434,152649,152662],"byte identity do not alone certify every transitive primary-source prerequisite","prerequisites",["approvals and "," or the"]]
["W0407",[2439,2439,157768,157782],[2434,2434,152670,152674],"entire private","full",["or the "," 214 proof."]]
["W0408",[2439,2439,157787,157958],[2434,2434,152679,152688],"proof. Any such unresolved prerequisite must remain open in the root closure assessment; neither the mistaken SF08--10/D6 locators nor the ten-determinant check closes it.","argument.",["private 214 ","\n"]]
["W0409",[2445,2445,158225,158331],[2440,2440,152955,152955],"Author supplement, \\nolinkurl{/root/d214_modularity_closure}, 11 November 2026. Pending nonauthor review. ","",["","Read together "]]
["W0410",[2445,2445,158384,158411],[2440,2440,153008,153035],"\\nolinkurl{PROOF_FINAL.md.}","\\nolinkurl{PROOF_FINAL.md}.",["\\nolinkurl{GEOMETRY_CARRY.md} and "," This supplies"]]
["W0411",[2445,2445,158439,158453],[2440,2440,153063,153063],"current-scope ","",["the detailed ","comparison requested "]]
["W0412",[2445,2445,158464,158479],[2440,2440,153074,153076],"requested after","of",["current-scope comparison "," the first"]]
["W0413",[2445,2445,158484,158489],[2440,2440,153081,153087],"first","source",["after the "," author freeze;"]]
["W0414",[2445,2445,158490,158551],[2440,2440,153088,153095],"author freeze; it does not rewrite the older limited reviews.","scopes.",["the first ","\n"]]
["W0415",[2449,2449,158637,158642],[2444,2444,153181,153188],"exact","sixteen",["The "," public final006"]]
["W0416",[2449,2449,158643,158649],[2444,2444,153189,153199],"public","full-cover",["The exact "," final006 decisions"]]
["W0417",[2449,2449,158650,158668],[2444,2444,153200,153212],"final006 decisions","applications",["exact public "," are in"]]
["W0418",[2449,2449,158673,158673],[2444,2444,153217,153227],"","specified ",["decisions are ","in \\nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json.} "]]
["W0419",[2449,2449,158676,158721],[2444,2444,153230,153298],"\\nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json.}","\\nolinkurl{research/quartic214/sources/public-provider-scopes.json},",["are in "," \\nolinkurl{FULL_COVER_SOURCE_PROFILES.json} extracts"]]
["W0420",[2449,2449,158722,158765],[2444,2444,153299,153303],"\\nolinkurl{FULL_COVER_SOURCE_PROFILES.json}","with",["in \\nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json.} "," extracts the"]]
["W0421",[2449,2449,158766,158785],[2444,2444,153304,153309],"extracts the actual","their",["\\nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json.} \\nolinkurl{FULL_COVER_SOURCE_PROFILES.json} "," incoming assertions,"]]
["W0422",[2449,2449,158826,158842],[2444,2444,153350,153370],"editions/hashes,","editions and hashes,",["hypotheses, source "," constructed objects"]]
["W0423",[2449,2449,158878,158882],[2444,2444,153406,153435],"maps","maps. Their scope is distinct",["and connecting "," from \\nolinkurl{protocol/current-coverage/INHERITED-TRANSPORT-PROPOSALS.json}."]]
["W0424",[2449,2449,158887,159046],[2444,2444,153440,153440]," \\nolinkurl{protocol/current-coverage/INHERITED-TRANSPORT-PROPOSALS.json}. These are the sixteen \\nolinkurl{ACTIVE-H19-FULL-COVER-*} applications, \\textbf{not}","",[" maps from"," a generic"]]
["W0425",[2449,2449,159068,159076],[2444,2444,153462,153472],"verdict,","assertion,",["generic \\(H_{19}\\) "," D6/B11 proof"]]
["W0426",[2449,2449,159077,159083],[2444,2444,153473,153476],"D6/B11","the",["\\(H_{19}\\) verdict, "," proof or"]]
["W0427",[2449,2449,159084,159089],[2444,2444,153477,153506],"proof","discriminant-six construction",["verdict, D6/B11 "," or modular"]]
["W0428",[2449,2449,159092,159092],[2444,2444,153509,153513],""," the",[" proof or"," modular SF08--10"]]
["W0429",[2449,2449,159127,159133],[2444,2444,153548,153554],"actual","source",["application. The "," entire \\nolinkurl{h5-full-three-v1/PROOF.md}"]]
["W0430",[2449,2449,159134,159140],[2444,2444,153555,153559],"entire","text",["The actual "," \\nolinkurl{h5-full-three-v1/PROOF.md} (SHA256054ec4a6...)"]]
["W0431",[2449,2449,159141,159178],[2444,2444,153560,153562],"\\nolinkurl{h5-full-three-v1/PROOF.md}","is",["actual entire "," (SHA256054ec4a6...) and"]]
["W0432",[2449,2449,159179,159198],[2444,2444,153563,153647],"(SHA256054ec4a6...)","\\nolinkurl{research/version14/proofs/h5-full-three-v1/PROOF.md} (SHA256 054ec4a6...)",["entire \\nolinkurl{h5-full-three-v1/PROOF.md} "," and its"]]
["W0433",[2449,2449,159240,159264],[2444,2444,153689,153703],"(f889eab0...) were read.","(f889eab0...).",["its \\nolinkurl{GEOMETRIC-ISOGENY.md} "," The composition"]]
["W0434",[2449,2449,159287,159299],[2444,2444,153726,153734],"explains how","supplies",["composition below "," the antecedents"]]
["W0435",[2449,2449,159316,159318],[2444,2444,153751,153753],"in","of",["the antecedents "," each source"]]
["W0436",[2449,2449,159331,159338],[2444,2444,153766,153777],"profile","application",["each source "," are supplied"]]
["W0437",[2449,2449,159339,159354],[2444,2444,153778,153782],"are supplied by","from",["source profile "," the previous"]]
["W0438",[2449,2449,159359,159367],[2444,2444,153787,153796],"previous","preceding",["by the "," construction.\n"]]
["W0439",[2456,2456,159589,159600],[2451,2451,154018,154030],"Chinese2024","Chinese 2024",["Yuan final "," \\S{}2.1, pp230--231,"]]
["W0440",[2456,2456,159610,159621],[2451,2451,154040,154053],"pp230--231,","pp.~230--231,",["Chinese2024 \\S{}2.1, "," aee74126...; use"]]
["W0441",[2456,2456,159841,159847],[2451,2451,154273,154280],"full3;","full 3;",["construction defines "," no literal"]]
["W0442",[2456,2456,159890,159902],[2451,2451,154323,154336],"ramified3.\\\\","ramified 3.\\\\",["used at ","\nTHREE-TORSION &"]]
["W0443",[2457,2457,159919,159928],[2452,2452,154353,154358],"Milne1986","Milne",["THREE-TORSION & "," Theorem8.2/Remark8.4, pp115--116,"]]
["W0444",[2457,2457,159929,159950],[2452,2452,154359,154363],"Theorem8.2/Remark8.4,","1986",["& Milne1986 "," pp115--116, 86259344...;"]]
["W0445",[2457,2457,159951,159962],[2452,2452,154364,154401],"pp115--116,","Theorem 8.2/Remark 8.4, pp.~115--116,",["Milne1986 Theorem8.2/Remark8.4, "," 86259344...; 3"]]
["W0446",[2457,2457,160012,160023],[2452,2452,154451,154463],"dimension2,","dimension 2,",["A has "," so A[3]"]]
["W0447",[2457,2457,160051,160057],[2452,2452,154491,154498],"rank81","rank 81",["etale of "," and \\(T_{3}\\)"]]
["W0448",[2457,2457,160076,160082],[2452,2452,154517,154524],"rank4.","rank 4.",["\\(T_{3}\\) has "," The projection"]]
["W0449",[2457,2457,160143,160161],[2452,2452,154585,154604],"multiplication-by3","multiplication-by 3",["O-action and "," transition maps.\\\\"]]
["W0450",[2458,2458,160200,160210],[2453,2453,154643,154654],"Voight2021","Voight 2021",["DIVISION-LATTICE & "," \\S{}13.3.4/13.3.11, pp206--207,"]]
["W0451",[2458,2458,160231,160242],[2453,2453,154675,154688],"pp206--207,","pp.~206--207,",["Voight2021 \\S{}13.3.4/13.3.11, "," exact final"]]
["W0452",[2458,2458,160255,160274],[2453,2453,154701,154721],"extract8f808986...;","extract 8f808986...;",["exact final "," \\(B_{3}\\) is"]]
["W0453",[2458,2458,160309,160314],[2453,2453,154756,154762],"Rank4","Rank 4",["not split. "," makes \\(V_{3}\\)"]]
["W0454",[2458,2458,160331,160336],[2453,2453,154779,154785],"rank1","rank 1",["makes \\(V_{3}\\) "," over \\(B_{3}\\)."]]
["W0455",[2459,2459,160574,160583],[2454,2454,155023,155028],"Milne1986","Milne",["TATE-FAITHFULNESS & "," Lemma12.2, \\(p_{122}\\);"]]
["W0456",[2459,2459,160584,160594],[2454,2454,155029,155033],"Lemma12.2,","1986",["& Milne1986 "," \\(p_{122}\\); inject"]]
["W0457",[2459,2459,160595,160607],[2454,2454,155034,155053],"\\(p_{122}\\);","Lemma 12.2, p.~122;",["Milne1986 Lemma12.2, "," inject the"]]
["W0458",[2459,2459,160704,160712],[2454,2454,155150,155159],"in1+3M4.","in 1+3M4.",["places it "," The written"]]
["W0459",[2460,2460,160858,160869],[2455,2455,155305,155317],"Stacks03YR,","Stacks 03YR,",["TRIVIAL-INERTIA & "," dated source82246ff7...;"]]
["W0460",[2461,2461,161212,161223],[2456,2456,155660,155672],"Stacks0ADD,","Stacks 0ADD,",["CURVE-FIBERS & "," f067c166...; the"]]
["W0461",[2461,2461,161294,161304],[2456,2456,155743,155754],"dimension1","dimension 1",["space have "," and regular"]]
["W0462",[2462,2462,161438,161449],[2457,2457,155888,155901],"pp937--941,","pp.~937--941,",["& Gonzalez--Rotger2006 "," e595d1a4..., for"]]
["W0463",[2462,2462,161599,161605],[2457,2457,156051,156058],"genus5","genus 5",["it. Its "," and Riemann--Hurwitz"]]
["W0464",[2462,2462,161699,161710],[2457,2457,156152,156164],"degree72.\\\\","degree 72.\\\\",["inferred from ","\n"]]
["W0465",[2468,2468,162868,162894],[2463,2463,157322,157328],"MilneClay2005,6336f0a2...,","Milne,",["& Original "," Theorem7.4's full"]]
["W0466",[2468,2468,162895,162907],[2463,2463,157329,157365],"Theorem7.4's","Clay 2005,6336f0a2..., Theorem 7.4's",["Original MilneClay2005,6336f0a2..., "," full Hodge-orbit"]]
["W0467",[2468,2468,163075,163097],[2463,2463,157533,157558],"\\(\\operatorname{GL}2\\)","\\(\\operatorname{GL}_{2}\\)",["the right-centralizer "," type-C1. On"]]
["W0468",[2468,2468,163291,163302],[2463,2463,157752,157764],"general8.17","general 8.17",["The erroneous "," implication is"]]
["W0469",[2469,2469,163355,163366],[2464,2464,157817,157829],"Buzzard1997","Buzzard 1997",["PRINCIPAL-POLARIZATION & "," p592,ed34a072..., before"]]
["W0470",[2470,2470,163653,163662],[2465,2465,158116,158121],"Milne2005","Milne",["ALGEBRAIC-FAMILY & "," Theorem14.8, \\(p_{352}\\);"]]
["W0471",[2470,2470,163663,163675],[2465,2465,158122,158126],"Theorem14.8,","2005",["& Milne2005 "," \\(p_{352}\\); every"]]
["W0472",[2470,2470,163676,163688],[2465,2465,158127,158148],"\\(p_{352}\\);","Theorem 14.8, p.~352;",["Milne2005 Theorem14.8, "," every arithmetic"]]
["W0473",[2470,2470,163859,163866],[2465,2465,158319,158327],"hence1.","hence 1.",["finite prime, "," Thus the"]]
["W0474",[2471,2471,164208,164217],[2466,2466,158669,158674],"Milne2005","Milne",["CANONICAL-MODEL & "," pp354--355 type-A/C"]]
["W0475",[2471,2471,164218,164228],[2466,2466,158675,158692],"pp354--355","2005 pp.~354--355",["& Milne2005 "," type-A/C criterion"]]
["W0476",[2471,2471,164248,164267],[2466,2466,158712,158732],"and13.6--13.7,p349;","and 13.6--13.7,p349;",["type-A/C criterion "," the comparison"]]
["W0477",[2479,2479,165862,165865],[2474,2474,160327,160336],"old","geometric",["The five "," pending bundles,"]]
["W0478",[2479,2479,165866,165873],[2474,2474,160337,160342],"pending","input",["five old "," bundles, and"]]
["W0479",[2479,2479,165874,165904],[2474,2474,160343,160350],"bundles, and what is retained}","groups}",["old pending ","\n"]]
["W0480",[2481,2481,165909,165991],[2476,2476,160355,160355]," older H5-FULL-COVER-SOURCE-INDEX-REVIEW accepted a role index and explicitly left","",["The"," five bundles"]]
["W0481",[2481,2481,165997,166004],[2476,2476,160361,160370],"bundles","geometric",["left five "," pending. That"]]
["W0482",[2481,2481,166005,166013],[2476,2476,160371,160376],"pending.","input",["five bundles "," That historical"]]
["W0483",[2481,2481,166014,166018],[2476,2476,160377,160383],"That","groups",["bundles pending. "," historical limited"]]
["W0484",[2481,2481,166019,166029],[2476,2476,160384,160387],"historical","are",["pending. That "," limited judgment"]]
["W0485",[2481,2481,166030,166037],[2476,2476,160388,160392],"limited","used",["That historical "," judgment is"]]
["W0486",[2481,2481,166038,166046],[2476,2476,160393,160395],"judgment","as",["historical limited "," is preserved."]]
["W0487",[2481,2481,166047,166230],[2476,2476,160396,160404],"is preserved. The later sixteen final006 source profiles above and the actual integrated proof support the following \\textbf{new author comparison}, whose acceptance is still pending:","follows:",["limited judgment ","\n"]]
["W0488",[2487,2487,167306,167314],[2482,2482,161480,161489],"degree1,","degree 1,",["curves with "," hence an"]]
["W0489",[2488,2488,167609,167614],[2483,2483,161784,161790],"and16","and 16",["marking classes "," normalizer parities,"]]
["W0490",[2488,2488,167636,167645],[2483,2483,161812,161822],"hence576.","hence 576.",["normalizer parities, "," Properness/good reduction"]]
["W0491",[2491,2491,168054,168169],[2486,2486,162231,162234],"The protocol does not require reproving their whole ancestry. The present author has not independently re-inspected","Not",["theorem inputs. "," every original"]]
["W0492",[2491,2491,168191,168201],[2486,2486,162256,162259],"PDF/Stacks","PDF",["original final "," HTML byte"]]
["W0493",[2491,2491,168202,168206],[2486,2486,162260,162262],"HTML","or",["final PDF/Stacks "," byte in"]]
["W0494",[2491,2491,168207,168211],[2486,2486,162263,162269],"byte","Stacks",["PDF/Stacks HTML "," in the"]]
["W0495",[2491,2491,168212,168214],[2486,2486,162270,162285],"in","page underlying",["HTML byte "," the sixteen"]]
["W0496",[2491,2491,168227,168230],[2486,2486,162298,162304],"old","source",["the sixteen "," profiles; exact"]]
["W0497",[2491,2491,168231,168240],[2486,2486,162305,162361],"profiles;","profiles has been independently re-inspected here. Their",["sixteen old "," exact public"]]
["W0498",[2491,2491,168247,168253],[2486,2486,162368,162379],"public","statements,",["profiles; exact "," accepted applications"]]
["W0499",[2491,2491,168254,168262],[2486,2486,162380,162390],"accepted","hypotheses",["exact public "," applications are"]]
["W0500",[2491,2491,168263,168305],[2486,2486,162391,162394],"applications are carried at their existing","and",["public accepted "," source scope,"]]
["W0501",[2491,2491,168313,168319],[2486,2486,162402,162408],"scope,","scopes",["existing source "," while the"]]
["W0502",[2491,2491,168320,168325],[2486,2486,162409,162428],"while","remain required for",["source scope, "," the actual"]]
["W0503",[2491,2491,168329,168352],[2486,2486,162432,162432]," actual entire internal","",[" while the"," \\(D_{210}\\) construction"]]
["W0504",[2491,2491,168386,168393],[2486,2486,162466,162473],"changed","current",["and its "," private application"]]
["W0505",[2491,2491,168394,168592],[2486,2486,162474,162486],"private application have been read and compared. This is the disclosed \\S{}33 carry boundary for nonauthor review. If that exact carry is not accepted, those precise source applications remain open;","application;",["its changed "," a broad"]]
["W0506",[2491,2491,168641,168644],[2486,2486,162535,162563],"it.","the individual applications.",["cannot replace ","\n"]]
["W0507",[2495,2495,168762,168772],[2490,2490,162681,162688],"privateV14","private",["predecessor passage, "," lines7532--7604/currentV15 lines7664--7736,"]]
["W0508",[2495,2495,168773,168799],[2490,2490,162689,162720],"lines7532--7604/currentV15","V14 lines7532--7604/current V15",["passage, privateV14 "," lines7664--7736, derives"]]
["W0509",[2495,2495,169068,169075],[2490,2490,162989,162997],"Genus5,","Genus 5,",["displayed there. "," \\(W=(C_{2})^{4}\\) and"]]
["W0510",[2495,2495,169171,169179],[2490,2490,163093,163102],"count40,","count 40,",["total fixed "," genus-zero full"]]
["W0511",[2495,2495,169286,169292],[2490,2490,163209,163216],"is210;","is 210;",["their product "," therefore the"]]
["W0512",[2495,2495,169342,169365],[2490,2490,163266,163290],"labels30,42,70,105,210.","labels 30,42,70,105,210.",["sections have "," Normalizing labels210,105,70"]]
["W0513",[2495,2495,169378,169394],[2490,2490,163303,163320],"labels210,105,70","labels 210,105,70",["labels30,42,70,105,210. Normalizing "," to infinity,0,1"]]
["W0514",[2497,2497,169584,169621],[2492,2492,163510,163548],"parameters1/2401,32/375,1/225,5/1029.","parameters 1/2401,32/375,1/225,5/1029.",["j-invariants for "," It exhausts"]]
["W0515",[2497,2497,169634,169639],[2492,2492,163561,163567],"the36","the 36",["It exhausts "," pairs from"]]
["W0516",[2499,2499,169976,169983],[2494,2494,163904,163912],"group36","group 36",["the level-change "," and \\(W\\)"]]
["W0517",[2499,2499,169997,170004],[2494,2494,163926,163934],"order16","order 16",["\\(W\\) of "," have invertible"]]
["W0518",[2501,2501,170895,170901],[2496,2496,164825,164832],"Full11","Full 11",["\\subsection{\\(P_{4}\\). "," semistability, torus"]]
["W0519",[2503,2503,171041,171047],[2498,2498,164972,164979],"full11","full 11",["actual public "," and torus"]]
["W0520",[2503,2503,171080,171102],[2498,2498,165012,165030],"Silverberg--Zarhin1995","Silverberg--Zarhin",["The final "," AIF45,403--420 PDF"]]
["W0521",[2503,2503,171103,171117],[2498,2498,165031,165051],"AIF45,403--420","1995 AIF 45,403--420",["final Silverberg--Zarhin1995 "," PDF was"]]
["W0522",[2503,2503,171122,171125],[2498,2498,165056,165058],"was","is",["AIF45,403--420 PDF "," reacquired from"]]
["W0523",[2503,2503,171126,171136],[2498,2498,165059,165069],"reacquired","identified",["PDF was "," from Numdam;"]]
["W0524",[2503,2503,171137,171141],[2498,2498,165070,165072],"from","by",["was reacquired "," Numdam; its"]]
["W0525",[2503,2503,171142,171149],[2498,2498,165073,165076],"Numdam;","the",["reacquired from "," its hash"]]
["W0526",[2503,2503,171150,171153],[2498,2498,165077,165083],"its","Numdam",["from Numdam; "," hash is"]]
["W0527",[2503,2503,171158,171161],[2498,2498,165088,165088]," is","",[" its hash"," \\textbf{\\nolinkurl{fc62ba1c9d1315a0c441a3dd7de46a254f379289e630c407a3336c0230d91052}}, exactly"]]
["W0528",[2503,2503,171280,171283],[2498,2498,165207,165214],"Its","Theorem",["source pin. "," actual Theorem3.4"]]
["W0529",[2503,2503,171284,171301],[2498,2498,165215,165218],"actual Theorem3.4","3.4",["pin. Its "," and Theorem3.5,"]]
["W0530",[2503,2503,171306,171317],[2498,2498,165223,165230],"Theorem3.5,","Theorem",["Theorem3.4 and "," printed406, were"]]
["W0531",[2503,2503,171318,171329],[2498,2498,165231,165234],"printed406,","3.5",["and Theorem3.5, "," were read."]]
["W0532",[2503,2503,171330,171334],[2498,2498,165235,165238],"were","are",["Theorem3.5, printed406, "," read. The"]]
["W0533",[2503,2503,171335,171340],[2498,2498,165239,165254],"read.","on printed 406.",["printed406, were "," The former"]]
["W0534",[2503,2503,171698,171709],[2498,2498,165612,165624],"over2,3,5,7","over 2,3,5,7",["every place "," is covered;"]]
["W0535",[2503,2503,171722,171731],[2498,2498,165637,165647],"residue11","residue 11",["is covered; "," is excluded."]]
["W0536",[2503,2503,171764,171767],[2498,2498,165680,165684],"or5","or 5",["earlier \\(n=3\\) "," occurrence is"]]
["W0537",[2505,2505,172105,172113],[2500,2500,166022,166031],"because1","because 1",["not allB "," maps to1."]]
["W0538",[2505,2505,172119,172123],[2500,2500,166037,166042],"to1.","to 1.",["because1 maps "," For \\(t=1\\)"]]
["W0539",[2505,2505,172221,172232],[2500,2500,166140,166152],"splitM2(Q),","split M2(Q),",["isomorphism onto "," contradicting divisionB."]]
["W0540",[2507,2507,172397,172407],[2502,2502,166317,166328],"prime-to11","prime-to-11",["the actual "," normalizer isogenies"]]
["W0541",[2507,2507,172441,172445],[2502,2502,166362,166367],"at11","at 11",["over \\(L:\\) "," the algebra"]]
["W0542",[2507,2507,172487,172500],[2502,2502,166409,166474],"Q11*GL2(Z11);","\\(\\mathbb Q_{11}^{\\times}\\operatorname{GL}_{2}(\\mathbb Z_{11})\\);",["normalizer is "," a rational"]]
["W0543",[2507,2507,172617,172622],[2502,2502,166591,166597],"to11.","to 11.",["integer prime "," The original"]]
["W0544",[2507,2507,172683,172696],[2502,2502,166658,166672],"the11-torsion","the 11-torsion",["therefore identify "," kernels over"]]
["W0545",[2510,2510,172828,172835],[2505,2505,166804,166813],"[E:Q] |","[E:Q]\\mid",[""," 576 |\\operatorname{GL}4(F_{11})|"]]
["W0546",[2510,2510,172840,172868],[2505,2505,166818,166849],"|\\operatorname{GL}4(F_{11})|","|\\operatorname{GL}_{4}(F_{11})|",["| 576 ","\n"]]
["W0547",[2513,2513,172895,172904],[2508,2508,166876,166876],"accepted ","",["The public ","source scope "]]
["W0548",[2513,2513,172911,172916],[2508,2508,166883,166891],"scope","argument",["accepted source "," needed only"]]
["W0549",[2513,2513,172995,173015],[2508,2508,166970,166991],"valuations(15,4,4,1)","valuations (15,4,4,1)",["private sharper "," follow from"]]
["W0550",[2527,2527,174018,174044],[2522,2522,167994,167994]," and its final006 decision","",["ACTIVE-H19-RAMIFICATION-NUMBERING"," retain the"]]
["W0551",[2533,2533,174698,174701],[2528,2528,168648,168652],"at2","at 2",["is tame, "," it adds"]]
["W0552",[2533,2533,174722,174730],[2528,2528,168673,168682],"factor2.","factor 2.",["most one "," Thus the"]]
["W0553",[2533,2533,174853,174863],[2528,2528,168805,168816],"at2,3,5,7,","at 2,3,5,7,",["already good "," and on"]]
["W0554",[2533,2533,174913,174918],[2528,2528,168866,168872],"are1,","are 1,",["scalar/isogeny corrections "," so the"]]
["W0555",[2535,2535,175513,175521],[2530,2530,169467,169473],"point to","record",["and \\nolinkurl{PUBLIC_FULL_COVER_DECISIONS.json} "," the nonauthor"]]
["W0556",[2535,2535,175526,175535],[2530,2530,169478,169484],"nonauthor","source",["to the "," public decisions"]]
["W0557",[2535,2535,175536,175552],[2530,2530,169485,169491],"public decisions","scopes",["the nonauthor "," for these"]]
["W0558",[2535,2535,175576,175789],[2530,2530,169515,169515]," They do not authorize an unreviewed changed application. This supplement, M1/M5's new lift and sharper arithmetic, and the exact same-form r3/r5 consumer remain subject to the assigned current independent review.","",[" exact inputs.","\n"]]
["W0559",[2538,2538,175900,175908],[2533,2533,169626,169626],"private ","",["for the ","214 construction}\\label{q214:modularity}\n"]]
["W0560",[2541,2541,176060,176254],[2536,2536,169778,169778]," Final author revision after the first freeze. Author: \\nolinkurl{/root/d214_modularity_closure}, internal Sol author lane, 11 November 2026. \\textbf{Author proposal; no independent acceptance.}","",["\\begin{quote}\\footnotesize"," The frozen"]]
["W0561",[2541,2541,176382,176411],[2536,2536,169906,169935],"\\nolinkurl{SOURCE_USES.json.}","\\nolinkurl{SOURCE_USES.json}.",["byte-bound in "," \\nolinkurl{INITIAL_AUTHOR_ANALYSIS.json} records"]]
["W0562",[2541,2541,176412,176649],[2536,2536,169936,169947],"\\nolinkurl{INITIAL_AUTHOR_ANALYSIS.json} records the actual order of exposure, including the scope summary read before reconstruction. This is an additive proof: no historical argument, verdict, count or polynomial is changed.\\end{quote}","\\end{quote}",["in \\nolinkurl{SOURCE_USES.json.} ","\n"]]
["W0563",[2545,2545,176748,176756],[2540,2540,170046,170046]," private","",[" domain of"," \\nolinkurl{height/PROOF.md} \\(H_{0}\\),"]]
["W0564",[2547,2547,178022,178128],[2542,2542,171312,171348],"\\nolinkurl{PROVIDER_SCOPE_CARRY.md.} These additive comparisons require the same current nonauthor review;","\\nolinkurl{PROVIDER_SCOPE_CARRY.md}.",["\\nolinkurl{GEOMETRY_CARRY.md} and "," H3's Rémond"]]
["W0565",[2547,2547,178134,178140],[2542,2542,171354,171362],"Rémond","R\\'emond",["review; H3's "," inequality and"]]
["W0566",[2547,2547,178160,178167],[2542,2542,171382,171390],"full214","full 214",["and the "," assembly are"]]
["W0567",[2553,2553,178634,178637],[2548,2548,171857,171880],"Q*.","\\(\\mathbb Q^{\\times}\\).",["}^{-1}\\) in "," Rational quasi-isogeny"]]
["W0568",[2583,2583,185172,185193],[2578,2578,178415,178415],"all four pages read, ","",["2016 corrigendum, ","restricts the "]]
["W0569",[2583,2583,185362,185371],[2578,2578,178584,178589],"Milne1986","Milne",["at 5. "," Theorem15.1(a), p.129,"]]
["W0570",[2583,2583,185372,185387],[2578,2578,178590,178611],"Theorem15.1(a),","1986 Theorem 15.1(a),",["5. Milne1986 "," p.129, identifies"]]
["W0571",[2583,2583,185589,185601],[2578,2578,178813,178821],"Fontaine1994","Fontaine",["weights \\{0,-1\\}. "," Theorem3.8, p.142,"]]
["W0572",[2583,2583,185602,185613],[2578,2578,178822,178839],"Theorem3.8,","1994 Theorem 3.8,",["\\{0,-1\\}. Fontaine1994 "," p.142, supplies"]]
["W0573",[2583,2583,185667,185675],[2578,2578,178893,178902],"Kato2004","Kato 2004",["tensor/dual/subobject closure. "," \\S{}9.2, p.187,"]]
["W0574",[2585,2585,186056,186067],[2580,2580,179283,179295],"Milne2005's","Milne 2005's",["trace zero. "," complex uniformization"]]
["W0575",[2585,2585,186095,186119],[2580,2580,179323,179349],"Theorem6.8/Corollary6.9,","Theorem 6.8/Corollary 6.9,",["uniformization and "," p.319, identify"]]
["W0576",[2585,2585,186203,186243],[2580,2580,179433,179460],"\\((5^{-n} \\text{Lambda})/\\text{Lambda}\\)","\\((5^{-n}\\Lambda)/\\Lambda\\)",["\\(5^{n}\\) identifies "," with \\(\\text{Lambda}/5^{n}\\)"]]
["W0577",[2585,2585,186249,186280],[2580,2580,179466,179491],"\\(\\text{Lambda}/5^{n}\\) Lambda.","\\(\\Lambda/5^{n}\\Lambda\\).",["\\text{Lambda})/\\text{Lambda}\\) with "," Exponentiation commutes"]]
["W0578",[2587,2587,186607,186614],[2582,2582,179818,179821],"ICM2022","ICM",["final EMS "," volume2 chapter,"]]
["W0579",[2587,2587,186615,186622],[2582,2582,179822,179835],"volume2","2022 volume 2",["EMS ICM2022 "," chapter, published"]]
["W0580",[2587,2587,187049,187064],[2582,2582,180262,180262],"The historical ","",["being inserted. ","Pan \\(v_{2}\\) "]]
["W0581",[2587,2587,187068,187077],[2582,2582,180266,180273],"\\(v_{2}\\)","version",["historical Pan "," Theorem1.0.4, p.5,"]]
["W0582",[2587,2587,187078,187091],[2582,2582,180274,180291],"Theorem1.0.4,","2, Theorem 1.0.4,",["Pan \\(v_{2}\\) "," p.5, was"]]
["W0583",[2587,2587,187097,187100],[2582,2582,180297,180300],"was","has",["Theorem1.0.4, p.5, "," also read;"]]
["W0584",[2587,2587,187101,187115],[2582,2582,180301,180303],"also read; its","an",["p.5, was "," exceptional residual"]]
["W0585",[2587,2587,187147,187154],[2582,2582,180335,180335],"occurs ","",["residual condition ","only at "]]
["W0586",[2587,2587,187165,187170],[2582,2582,180346,180349],"Final","Its",["at 3. "," Pan JAMS"]]
["W0587",[2587,2587,187171,187174],[2582,2582,180350,180355],"Pan","final",["3. Final "," JAMS body"]]
["W0588",[2587,2587,187185,187214],[2582,2582,180366,180369],"retrieval returned 403. We do","has",["JAMS body "," not claim"]]
["W0589",[2587,2587,187219,187232],[2582,2582,180374,180378],"claim to have","been",["do not "," compared that"]]
["W0590",[2587,2587,187242,187242],[2582,2582,180388,180393],"","with ",["have compared ","that body, "]]
["W0591",[2587,2587,187247,187252],[2582,2582,180398,180404],"body,","author",["compared that "," or to"]]
["W0592",[2587,2587,187253,187297],[2582,2582,180405,180413],"or to have recursively re-audited its proof.","version.",["that body, "," The immediate"]]
["W0593",[2587,2587,187311,187311],[2582,2582,180427,180440],""," input is the",[" The immediate"," final published"]]
["W0594",[2587,2587,187347,187398],[2582,2582,180476,180476],"is independently available and directly applicable ","",["Calegari statement ","under the "]]
["W0595",[2587,2587,187408,187418],[2582,2582,180486,180496],"protocol's","hypotheses",["under the "," published-theorem boundary."]]
["W0596",[2587,2587,187419,187436],[2582,2582,180497,180504],"published-theorem","checked",["the protocol's "," boundary.\n"]]
["W0597",[2587,2587,187437,187446],[2582,2582,180505,180511],"boundary.","above.",["protocol's published-theorem ","\n"]]
["W0598",[2593,2593,188219,188230],[2588,2588,181284,181296],"Theorem4.1,","Theorem 4.1,",["\\(k=1\\), Deligne--Serre "," pp.513--514, gives"]]
["W0599",[2595,2595,188794,188801],[2590,2590,181860,181868],"and9.4,","and 9.4,",["}(f)\\), \\S{}\\S{}6.3 "," pp.161--162,188. Its"]]
["W0600",[2595,2595,189018,189038],[2590,2590,182085,182106],"Equations14.10.2--3,","Equations 14.10.2--3,",["divide \\(N\\). "," p.240, put"]]
["W0601",[2599,2599,190074,190086],[2594,2594,183142,183155],"Theorem14.1;","Theorem 14.1;",["inherited Washington "," its final"]]
["W0602",[2599,2599,190184,190206],[2594,2594,183253,183257],"ADT already inspected:","ADT:",["published Milne "," I.1.3 and1.6(c),"]]
["W0603",[2599,2599,190213,190223],[2594,2594,183264,183275],"and1.6(c),","and 1.6(c),",["inspected: I.1.3 "," pp.18--19, give"]]
["W0604",[2599,2599,191181,191185],[2594,2594,184233,184238],"and1","and 1",["at \\(q\\) "," elsewhere is"]]
["W0605",[2599,2599,191265,191277],[2594,2594,184318,184331],"component1/q","component 1/q",["positive real "," and finite"]]
["W0606",[2599,2599,191326,191330],[2594,2594,184380,184385],"and1","and 1",["\\(p\\ne q\\) "," at \\(q\\)."]]
["W0607",[2601,2601,191844,191855],[2596,2596,184899,184911],"Shimura1973","Shimura 1973",[""," \\S{}4 equation4.1,"]]
["W0608",[2601,2601,191862,191874],[2596,2596,184918,184931],"equation4.1,","equation 4.1,",["Shimura1973 \\S{}4 "," p.531, sends"]]
["W0609",[2603,2603,192616,192625],[2598,2598,185673,185675],"Precision","Li",[""," repair: Li1975"]]
["W0610",[2603,2603,192626,192633],[2598,2598,185676,185680],"repair:","1975",["Precision "," Li1975 Theorem5,"]]
["W0611",[2603,2603,192634,192640],[2598,2598,185681,185688],"Li1975","Theorem",["Precision repair: "," Theorem5, p.298,"]]
["W0612",[2603,2603,192641,192650],[2598,2598,185689,185691],"Theorem5,","5,",["repair: Li1975 "," p.298, proves"]]
["W0613",[2603,2603,192805,192808],[2598,2598,185846,185855],"The","Existence",["primitive constituent. "," current \\(V_{15}\\)"]]
["W0614",[2603,2603,192809,192816],[2598,2598,185856,185858],"current","is",["constituent. The "," \\(V_{15}\\) p294/Theorem5"]]
["W0615",[2603,2603,192817,192827],[2598,2598,185859,185867],"\\(V_{15}\\)","supplied",["The current "," p294/Theorem5 citation"]]
["W0616",[2603,2603,192828,192841],[2598,2598,185868,185870],"p294/Theorem5","by",["current \\(V_{15}\\) "," citation should"]]
["W0617",[2603,2603,192842,192898],[2598,2598,185871,185874],"citation should not bear that existence claim alone. The","the",["\\(V_{15}\\) p294/Theorem5 "," explicit Deligne--Serre"]]
["W0618",[2603,2603,192934,193007],[2598,2598,185910,185916],"above repairs the application without changing its arithmetic conclusion.","above.",["Deligne--Serre extraction "," Li's actual"]]
["W0619",[2607,2607,193327,193332],[2602,2602,186236,186242],"and3;","and 3;",["at 5 "," do not"]]
["W0620",[2615,2615,194265,194274],[2610,2610,187175,187180],"Milne1986","Milne",["residue-cardinality Frobenius. "," Proposition12.9 and"]]
["W0621",[2615,2615,194275,194290],[2610,2610,187181,187202],"Proposition12.9","1986 Proposition 12.9",["Frobenius. Milne1986 "," and its"]]
["W0622",[2618,2618,194712,194727],[2613,2613,187624,187644],"_{p}))*q_{p}/2)","_{p}))\\cdot q_{p}/2)",["}((a_{{\\sigma }_{p}}/b(\\sigma ","\n"]]
["W0623",[2621,2621,194921,194924],[2616,2616,187838,187842],"at5","at 5",["The isomorphism "," gives \\(\\iota"]]
["W0624",[2621,2621,195164,195174],[2616,2616,188082,188093],"Corollary2","Corollary 2",["ChapterI \\S{}2.2 "," and \\S{}2.3"]]
["W0625",[2623,2623,195659,195663],[2618,2618,188578,188583],"and3","and 3",["pair 5 "," is needed:"]]
["W0626",[2627,2627,195920,195931],[2622,2622,188840,188852],"Carayol1987","Carayol 1987",["Use "," final Astérisque147--148,"]]
["W0627",[2627,2627,195938,195957],[2622,2622,188859,188881],"Astérisque147--148,","Ast\\'erisque 147--148,",["Carayol1987 final "," \\S{}\\S{}2.1/2.4/4.1, printed36,37,42."]]
["W0628",[2627,2627,195979,195995],[2622,2622,188903,188920],"printed36,37,42.","printed 36,37,42.",["Astérisque147--148, \\S{}\\S{}2.1/2.4/4.1, "," Its normalized"]]
["W0629",[2627,2627,196105,196113],[2622,2622,189030,189039],"Theorem4","Theorem 4",["The full "," removes the"]]
["W0630",[2627,2627,196167,196176],[2622,2622,189093,189103],"Theorem3;","Theorem 3;",["condition of "," the following"]]
["W0631",[2627,2627,196338,196347],[2622,2622,189265,189275],"Theorem4.","Theorem 4.",["restriction on "," \\(Q\\) has"]]
["W0632",[2627,2627,196362,196370],[2622,2622,189290,189299],"degree1.","degree 1.",["has odd "," Thus all"]]
["W0633",[2633,2633,196947,196964],[2628,2628,189876,189882],"purport to accept","supply",["does not "," that separately"]]
["W0634",[2635,2635,197206,197216],[2630,2630,190124,190135],"prime-to11","prime-to-11",["the retained "," normalizer isogenies."]]
["W0635",[2635,2635,197327,197341],[2630,2630,190246,190261],"full11-torsion","full 11-torsion",["(15,4,4,1). The "," semistability criterion"]]
["W0636",[2635,2635,197700,197703],[2630,2630,190620,190624],"at2","at 2",["are tame; "," the \\(\\chi"]]
["W0637",[2643,2643,198520,198529],[2638,2638,191441,191451],"least1/2,","least 1/2,",["is at "," so \\(b_{\\text{last}}\\le"]]
["W0638",[2643,2643,198836,198847],[2638,2638,191758,191770],"divides576,","divides 576,",["its degree "," A/L has"]]
["W0639",[2643,2643,199027,199037],[2638,2638,191950,191961],"residue11.","residue 11.",["used at "," \\nolinkurl{PROVIDER_SCOPE_CARRY.md} \\(P_{4}\\)"]]
["W0640",[2643,2643,199158,199173],[2638,2638,192082,192090],"Theorems3.4/3.5","Theorems",["final Silverberg--Zarhin1995 "," have been"]]
["W0641",[2643,2643,199174,199178],[2638,2638,192091,192098],"have","3.4/3.5",["Silverberg--Zarhin1995 Theorems3.4/3.5 "," been directly"]]
["W0642",[2643,2643,199179,199183],[2638,2638,192099,192102],"been","are",["Theorems3.4/3.5 have "," directly read"]]
["W0643",[2643,2643,199184,199192],[2638,2638,192103,192113],"directly","identified",["have been "," read at"]]
["W0644",[2643,2643,199193,199200],[2638,2638,192114,192116],"read at","by",["been directly "," the same"]]
["W0645",[2643,2643,199237,199247],[2638,2638,192153,192158],"previously","Serre",["the exact "," accepted Serre1967"]]
["W0646",[2643,2643,199248,199256],[2638,2638,192159,192163],"accepted","1967",["exact previously "," Serre1967 chapterVI"]]
["W0647",[2643,2643,199257,199266],[2638,2638,192164,192171],"Serre1967","chapter",["previously accepted "," chapterVI ramification"]]
["W0648",[2643,2643,199267,199276],[2638,2638,192172,192174],"chapterVI","VI",["accepted Serre1967 "," ramification application"]]
["W0649",[2643,2643,199376,199383],[2638,2638,192274,192282],"the1979","the 1979",["is not "," Local Fields"]]
["W0650",[2645,2645,199507,199516],[2640,2640,192406,192416],"exponent2","exponent 2",["Absorb baseline "," at 2,3,5,7"]]
["W0651",[2677,2677,201714,201717],[2672,2672,194614,194618],"of2","of 2",["even power "," and m|U,"]]
["W0652",[2685,2685,202137,202148],[2680,2680,195038,195044],"\\(p_{296}\\)","p.~296",["actual final "," formula \\(f|H_{N}=\\gamma"]]
["W0653",[2685,2685,202474,202485],[2680,2680,195370,195377],"Shimura1973","Shimura",["after absorption. "," Theorem1, pp.526--527,"]]
["W0654",[2685,2685,202486,202495],[2680,2680,195378,195393],"Theorem1,","1973 Theorem 1,",["absorption. Shimura1973 "," pp.526--527, then"]]
["W0655",[2685,2685,202666,202685],[2680,2680,195564,195592],"\\(\\text{Qbar}_{5}\\)","\\(\\overline{\\mathbb Q}_{5}\\)",["module over "," is the"]]
["W0656",[2687,2687,203059,203069],[2682,2682,195966,195977],"embedding5","embedding 5",["the fixed "," to half"]]
["W0657",[2689,2689,204065,204074],[2684,2684,196973,196978],"Milne1986","Milne",["Poincare reducibility, "," Proposition12.1 and"]]
["W0658",[2689,2689,204075,204090],[2684,2684,196979,197000],"Proposition12.1","1986 Proposition 12.1",["reducibility, Milne1986 "," and following"]]
["W0659",[2691,2691,204667,204670],[2686,2686,197577,197581],"of2","of 2",["a power "," use \\(\\phi"]]
["W0660",[2695,2695,205609,205619],[2690,2690,198520,198526],"Historical","Source",["\\subsection{\\(M_{7}\\). "," and current"]]
["W0661",[2695,2695,205620,205645],[2690,2690,198527,198533],"and current dispositions}","scope}",["\\subsection{\\(M_{7}\\). Historical ","\n"]]
["W0662",[2697,2697,205647,206141],[2692,2692,198535,198538],"Actual earlier arguments read include private frozen \\(V_{14}\\) lemma481--660, b-family8097--8347 (including original r5/r3 and CL1/CL2); cutoff \\S{}1; parent9 \\S{}\\S{}1--3; heightH0--H4; the published-source Faltings/Poincare/Li bridge; public \\(V_{15}\\) lemma505--705, baseline1334--1505 and b-family; direct-p5 PROOF, FAMILY-CONNECTION, FIVE-TO-THREE and CLASSICAL-LOCAL; the later direct Carayol proof and source statement. These establish \\textbf{prior justification found} for the general","The",[""," normalized modularity,"]]
["W0663",[2697,2697,206209,206221],[2692,2692,198606,198716],"derivations.","arguments use the source applications specified above. General source statements are independent of \\(\\chi \\).",["numerical conductor "," The new"]]
["W0664",[2697,2697,206225,206229],[2692,2692,198720,198720]," new","",[" derivations. The"," minimal-character choice"]]
["W0665",[2697,2697,206258,206271],[2692,2692,198749,198750],"an explicitly","a",["choice is "," changed application"]]
["W0666",[2697,2697,206292,206301],[2692,2692,198771,198774],"requiring","and",["changed application "," this fresh"]]
["W0667",[2697,2697,206302,206306],[2692,2692,198775,198783],"this","requires",["application requiring "," fresh proof"]]
["W0668",[2697,2697,206307,206312],[2692,2692,198784,198787],"fresh","the",["requiring this "," proof and"]]
["W0669",[2697,2697,206319,206322],[2692,2692,198794,198799],"and","given",["fresh proof "," fresh review."]]
["W0670",[2697,2697,206323,206328],[2692,2692,198800,198805],"fresh","here;",["proof and "," review. The"]]
["W0671",[2697,2697,206329,206336],[2692,2692,198806,198901],"review.","a general source statement alone does not supply its application to the revised representation.",["and fresh "," The old"]]
["W0672",[2697,2697,206341,206344],[2692,2692,198906,198911],"old","final",["review. The "," qualification rollup's"]]
["W0673",[2697,2697,206345,206358],[2692,2692,198912,198915],"qualification","Pan",["The old "," rollup's final-Pan"]]
["W0674",[2697,2697,206359,206367],[2692,2692,198916,198920],"rollup's","JAMS",["old qualification "," final-Pan access"]]
["W0675",[2697,2697,206368,206377],[2692,2692,198921,198925],"final-Pan","body",["qualification rollup's "," access limitation"]]
["W0676",[2697,2697,206378,206384],[2692,2692,198926,198929],"access","has",["rollup's final-Pan "," limitation is"]]
["W0677",[2697,2697,206385,206395],[2692,2692,198930,198979],"limitation","not been compared. The immediate modularity input",["final-Pan access "," is preserved"]]
["W0678",[2697,2697,206399,206465],[2692,2692,198983,198983],"preserved as history; it is not a reason to deny applicability of ","",["limitation is ","Calegari's actually "]]
["W0679",[2697,2697,206475,206489],[2692,2692,198993,198993]," actually read","",[" of Calegari's"," final published"]]
["W0680",[2697,2697,206515,206521],[2692,2692,199019,199040],"The Li","Primitive-constituent",["published theorem. "," existence locator"]]
["W0681",[2697,2697,206532,206545],[2692,2692,199051,199055],"locator needs","uses",["Li existence "," the explicit"]]
["W0682",[2697,2697,206550,206558],[2692,2692,199060,199074],"explicit","Deligne--Serre",["needs the "," repair \\(M_{3}\\)."]]
["W0683",[2697,2697,206559,206565],[2692,2692,199075,199088],"repair","extraction in",["the explicit "," \\(M_{3}\\). General"]]
["W0684",[2697,2699,206577,206923],[2692,2692,199100,199100],"General source statements carry independently of \\(\\chi \\); no approval carries to a revised constructed representation by itself.\n\nCurrent incorporation is \\textbf{pending} for this additive bridge. Current acceptance is \\textbf{pending} a nonauthor reviewer on the final hashes. No final-Pan-body comparison or complete214 theorem is inferred. ","",["repair \\(M_{3}\\). ","The actual "]]
["W0685",[2699,2699,206926,206933],[2692,2692,199103,199103]," actual","",[" inferred. The"," \\(D_{210}\\) \\(H_{01}\\)"]]
["W0686",[2699,2699,206957,206984],[2692,2692,199127,199139],"provider/source composition","construction",["\\(D_{210}\\) \\(H_{01}\\) "," and the"]]
["W0687",[2699,2699,206993,206999],[2692,2692,199148,199148],"exact ","",["and the ","retained Serre1967/full11 "]]
["W0688",[2699,2699,207008,207024],[2692,2692,199157,199175],"Serre1967/full11","Serre 1967/full 11",["exact retained "," conductor applications"]]
["W0689",[2699,2699,207052,207064],[2692,2692,199203,199212],"now supplied","specified",["applications are "," in \\nolinkurl{GEOMETRY_CARRY.md}"]]
["W0690",[2699,2699,207102,207138],[2692,2692,199250,199286],"\\nolinkurl{PROVIDER_SCOPE_CARRY.md;}","\\nolinkurl{PROVIDER_SCOPE_CARRY.md}.",["\\nolinkurl{GEOMETRY_CARRY.md} and "," their current"]]
["W0691",[2699,2699,207139,207144],[2692,2692,199287,199290],"their","The",["and \\nolinkurl{PROVIDER_SCOPE_CARRY.md;} "," current acceptance"]]
["W0692",[2699,2699,207145,207152],[2692,2692,199291,199300],"current","remaining",["\\nolinkurl{PROVIDER_SCOPE_CARRY.md;} their "," acceptance is"]]
["W0693",[2699,2699,207153,207163],[2692,2692,199301,199307],"acceptance","source",["their current "," is pending"]]
["W0694",[2699,2699,207164,207166],[2692,2692,199308,199314],"is","scopes",["current acceptance "," pending the"]]
["W0695",[2699,2699,207167,207174],[2692,2692,199315,199318],"pending","are",["acceptance is "," the nonauthor"]]
["W0696",[2699,2699,207175,207178],[2692,2692,199319,199327],"the","recorded",["is pending "," nonauthor reviewer."]]
["W0697",[2699,2699,207179,207198],[2692,2692,199328,199330],"nonauthor reviewer.","in",["pending the "," \\nolinkurl{SOURCE_USES_FINAL.json} and"]]
["W0698",[2699,2699,207238,207304],[2692,2692,199370,199394],"\\nolinkurl{FINDINGS.md} name the remaining scope limits precisely.","\\nolinkurl{FINDINGS.md}.",["\\nolinkurl{SOURCE_USES_FINAL.json} and ","\n"]]
["W0699",[2705,2705,207579,207738],[2698,2698,199669,199669]," Author: internal model agent \\nolinkurl{/root/d214_integral_evaluation}, 2026-11-10. This is a proposed source/application bridge, not independent acceptance.","",["\\begin{quote}\\footnotesize"," Frozen private"]]
["W0700",[2705,2705,207857,207941],[2698,2698,199788,199788],"\\nolinkurl{research/quadratic-ten-contact-integration/height/sources/brox-v17.tex}, ","",["Brox \\(v_{17}\\), ","lines 87--99, "]]
["W0701",[2705,2705,207993,207993],[2698,2698,199840,199939],""," The retained public excerpt is \\nolinkurl{research/quartic214/sources/evaluation-sections1-4.tex}.",[" at 218--225."," Whole-file and"]]
["W0702",[2732,2732,211914,211919],[2725,2725,203860,203867],"étale","\\'etale",["finite prime, "," over \\(R\\),"]]
["W0703",[2779,2779,217406,217412],[2772,2772,209354,209362],"étale.","\\'etale.",["map is "," The usual"]]
["W0704",[2781,2781,217994,217999],[2774,2774,209944,209951],"étale","\\'etale",["use an "," neighbourhood splitting"]]
["W0705",[2781,2781,218035,218040],[2774,2774,209987,209994],"étale","\\'etale",["the finite "," cover (04HN)."]]
["W0706",[2809,2809,220429,220504],[2802,2802,212383,212395],"calculation, reconstructed here rather than imported from a review verdict.","calculation.",["elementary local "," For every"]]
["W0707",[2827,2827,222406,222421],[2820,2820,214297,214303],"bounded status}","scope}",["consumer and ","\n"]]
["W0708",[2831,2831,222997,223704],[2824,2824,214879,214879],"History: the earlier foundation report had already read a complete project proof of this route and specifically requested source/application closure. The retained quadratic integration review explicitly checked \\(v_{17}\\) at component scope and kept inherited foundational qualifications. Accordingly this is prior justification found plus an expanded source bridge, proposed for incorporation; it is not evidence that no earlier reviewer had supplied these details. No historical verdict is rewritten. A non-author must review this frozen bridge and its sources before the application can be called independently accepted. This component does not close the full arithmetic theorem or all of Protocol \\(D\\).","",["","\n"]]
["W0709",[2837,2837,223994,224184],[2830,2830,215169,215169]," Author: internal model \\nolinkurl{/root/d214_different_bounds}, 2026-11-10. This is an author proposal for fresh non-author review. It neither writes nor supplies an independent acceptance.","",["\\begin{quote}\\footnotesize"," Frozen target:"]]
["W0710",[2837,2837,224199,224199],[2830,2830,215184,215203],""," Brox \\(v_{17}\\) at",[" Frozen target:"," private repository"]]
["W0711",[2837,2837,224280,224363],[2830,2830,215284,215294],"\\nolinkurl{research/quadratic-ten-contact-integration/height/sources/brox-v17.tex},","whole-file",["commit \\nolinkurl{a81afd7996a20e6b7bb5e48670418541c036d7aa}, "," SHA-256 \\nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}.\\end{quote}"]]
["W0712",[2837,2837,224372,224460],[2830,2830,215303,215490],"\\nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}.\\end{quote}","\\nolinkurl{2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c}. The retained public excerpt is \\nolinkurl{research/quartic214/sources/evaluation-sections1-4.tex}.\\end{quote}",["\\nolinkurl{research/quadratic-ten-contact-integration/height/sources/brox-v17.tex}, SHA-256 ","\n"]]
["W0713",[2843,2843,224868,224911],[2836,2836,215898,215898]," which require their own non-author review,","",[" evaluation interfaces,"," this is"]]
["W0714",[2843,2843,225098,225110],[2836,2836,216085,216098],"Lemma49.12.6","Lemma 49.12.6",["citation to "," is valid"]]
["W0715",[2843,2843,225155,225163],[2836,2836,216143,216152],"tag0BWJ.","tag 0BWJ.",["exact current "," The mathematical"]]
["W0716",[2843,2843,225234,225311],[2836,2836,216223,216235],"comparisons; incorporation and current independent acceptance remain pending.","comparisons.",["explicit source ","\n"]]
["W0717",[2847,2847,225592,225596],[2840,2840,216516,216524],"lane","argument",["The integral-evaluation "," supplies finite"]]
["W0718",[2863,2863,228371,228382],[2856,2856,219299,219311],"ANT8(2014),","ANT 8(2014),",["is Javanpeykar, "," \\S{}4.1, printed"]]
["W0719",[2863,2863,228400,228411],[2856,2856,219329,219342],"pp112--113,","pp.~112--113,",["\\S{}4.1, printed "," Propositions4.1.1 and4.1.3"]]
["W0720",[2863,2863,228412,228429],[2856,2856,219343,219355],"Propositions4.1.1","Propositions",["printed pp112--113, "," and4.1.3 and"]]
["W0721",[2863,2863,228430,228438],[2856,2856,219356,219361],"and4.1.3","4.1.1",["pp112--113, Propositions4.1.1 "," and Remark4.1.2."]]
["W0722",[2863,2863,228443,228455],[2856,2856,219366,219389],"Remark4.1.2.","4.1.3 and Remark 4.1.2.",["and4.1.3 and "," The retained"]]
["W0723",[2863,2863,228505,228530],[2856,2856,219439,219465],"DOI10.2140/ant.2014.8.89;","DOI 10.2140/ant.2014.8.89;",["publisher article, "," see \\nolinkurl{SOURCE_USES.json}."]]
["W0724",[2863,2863,228797,228813],[2856,2856,219732,219749],"Proposition4.1.3","Proposition 4.1.3",["imperfect-residue application. "," obtains a"]]
["W0725",[2871,2871,229881,229912],[2864,2864,220817,220847],"\\text{floor}(\\operatorname{log}","\\left\\lfloor\\operatorname{log}",["\\le  v_{V}(p) "," d/\\operatorname{log} p)\\)."]]
["W0726",[2871,2871,229934,229939],[2864,2864,220869,220886],"p)\\).","p\\right\\rfloor\\).",["\\text{floor}(\\operatorname{log} d/\\operatorname{log} ","\n"]]
["W0727",[2873,2873,229976,229996],[2866,2866,220923,220942],"\\(q=(\\text{pfrak})\\)","\\(q=(\\mathfrak p)\\)",["vertical point "," of Spec"]]
["W0728",[2873,2873,230024,230054],[2866,2866,220970,220999],"\\(V=O_{K}[t]_{\\text{pfrak}}\\),","\\(V=O_{K}[t]_{\\mathfrak p}\\),",["\\(O_{K}[t]\\). Then "," residue field"]]
["W0729",[2873,2873,230069,230092],[2866,2866,221014,221036],"\\(k(\\text{pfrak})(t)\\),","\\(k(\\mathfrak p)(t)\\),",["residue field "," which generally"]]
["W0730",[2873,2873,230161,230191],[2866,2866,221105,221134],"\\(v_{V}(p)=e_{\\text{pfrak}}\\).","\\(v_{V}(p)=e_{\\mathfrak p}\\).",["\\(K(t)\\), and "," \\(V\\) is"]]
["W0731",[2875,2875,230435,230451],[2868,2868,221378,221390],"e_{\\text{pfrak}}","e_{\\mathfrak",["+ e_{j} "," \\text{floor}(\\operatorname{log} d/\\operatorname{log}"]]
["W0732",[2875,2875,230452,230483],[2868,2868,221391,221424],"\\text{floor}(\\operatorname{log}","p} \\left\\lfloor\\operatorname{log}",["e_{j} e_{\\text{pfrak}} "," d/\\operatorname{log} p)\\)."]]
["W0733",[2875,2875,230505,230510],[2868,2868,221446,221463],"p)\\).","p\\right\\rfloor\\).",["\\text{floor}(\\operatorname{log} d/\\operatorname{log} ","\n"]]
["W0734",[2879,2879,230625,230647],[2872,2872,221578,221596],"\\(d(1+e_{\\text{pfrak}}","\\(d(1+e_{\\mathfrak",[""," \\text{floor}(\\operatorname{log} d/\\operatorname{log}"]]
["W0735",[2879,2879,230648,230679],[2872,2872,221597,221630],"\\text{floor}(\\operatorname{log}","p} \\left\\lfloor\\operatorname{log}",["\\(d(1+e_{\\text{pfrak}} "," d/\\operatorname{log} p))\\)."]]
["W0736",[2879,2879,230701,230707],[2872,2872,221652,221670],"p))\\).","p\\right\\rfloor)\\).",["\\text{floor}(\\operatorname{log} d/\\operatorname{log} ","\n"]]
["W0737",[2883,2883,231367,231372],[2876,2876,222330,222337],"étale","\\'etale",["is finite "," over \\(O_{K_{0}}[S^{-1},t,t^{-1},(t-1)^{-1}]\\),"]]
["W0738",[2883,2883,231464,231469],[2876,2876,222429,222436],"étale","\\'etale",["stays finite "," there. The"]]
["W0739",[2883,2883,231509,231514],[2876,2876,222476,222483],"étale","\\'etale",["a finite "," algebra over"]]
["W0740",[2885,2885,231955,231960],[2878,2878,222924,222930],"log2.","log 2.",["normalized value "," At pfrak"]]
["W0741",[2885,2885,231964,231969],[2878,2878,222934,222949],"pfrak","\\(\\mathfrak p\\)",["log2. At "," above \\(p\\)"]]
["W0742",[2885,2885,232011,232031],[2878,2878,222991,223005],"\\(f_{\\text{pfrak}}\\)","\\(f_{\\mathfrak",["intersection is "," logp. Summing"]]
["W0743",[2885,2885,232032,232037],[2878,2878,223006,223017],"logp.","p}\\) log p.",["is \\(f_{\\text{pfrak}}\\) "," Summing the"]]
["W0744",[2885,2885,232075,232110],[2878,2878,223055,223066],"_{\\text{pfrak}|p}e_{\\text{pfrak}}\\)","_{\\mathfrak",["using \\(\\sum "," \\(f_{\\text{pfrak}}=[K:Q]\\) and"]]
["W0745",[2885,2885,232111,232137],[2878,2878,223067,223114],"\\(f_{\\text{pfrak}}=[K:Q]\\)","p|p}e_{\\mathfrak p}\\) \\(f_{\\mathfrak p}=[K:Q]\\)",["\\(\\sum _{\\text{pfrak}|p}e_{\\text{pfrak}}\\) "," and \\(\\sum"]]
["W0746",[2885,2885,232149,232168],[2878,2878,223126,223144],"f_{\\text{pfrak}}\\le","f_{\\mathfrak p}\\le",["and \\(\\sum "," [K:Q]\\), gives"]]
["W0747",[2893,2893,232830,232836],[2886,2886,223806,223814],"étale;","\\'etale;",["is finite "," it need"]]
["W0748",[2893,2893,232963,232974],[2886,2886,223941,223947],"Stacks0BFG,","Stacks",["field theorem "," Lemma39.9.8, on"]]
["W0749",[2893,2893,232975,232987],[2886,2886,223948,223967],"Lemma39.9.8,","0BFG, Lemma 39.9.8,",["theorem Stacks0BFG, "," on every"]]
["W0750",[2893,2893,233050,233068],[2886,2886,224030,224049],"Stacks49.12.6/0BWJ","Stacks 49.12.6/0BWJ",["give finiteness. "," applies with"]]
["W0751",[2893,2893,233144,233155],[2886,2886,224125,224137],"dimension1,","dimension 1,",["of relative "," and \\(f=[n]\\)"]]
["W0752",[2893,2893,233445,233451],[2886,2886,224427,224435],"étale.","\\'etale.",["\\([n]\\) is ","\n"]]
["W0753",[2897,2897,234329,234339],[2890,2890,225313,225319],"Stacks0BWE","Stacks",["\\(V\\to A\\), "," (Lemma49.10.1) checks"]]
["W0754",[2897,2897,234340,234354],[2890,2890,225320,225340],"(Lemma49.10.1)","0BWE (Lemma 49.10.1)",["A\\), Stacks0BWE "," checks the"]]
["W0755",[2897,2897,234393,234403],[2890,2890,225379,225390],"Stacks0BWF","Stacks 0BWF",["syntomic hypotheses, "," (49.10.4) gives"]]
["W0756",[2897,2897,234460,234470],[2890,2890,225447,225458],"Stacks0BWG","Stacks 0BWG",["_{A/V}\\), and "," (49.12.3, on"]]
["W0757",[2897,2897,234497,234509],[2890,2890,225485,225498],"section0BWB)","section 0BWB)",["the archived "," identifies the"]]
["W0758",[2897,2897,234597,234618],[2890,2890,225586,225608],"Definition49.9.1/0BW4","Definition 49.9.1/0BW4",["_{A/V}=(n)\\). Stacks "," defines that"]]
["W0759",[2903,2903,235093,235103],[2896,2896,226083,226094],"(from0BWF)","(from 0BWF)",["fractional A-ideal "," and contains1,"]]
["W0760",[2903,2903,235108,235118],[2896,2896,226099,226110],"contains1,","contains 1,",["(from0BWF) and "," this is"]]
["W0761",[2907,2907,235424,235430],[2900,2900,226416,226424],"Kähler","K\\\"ahler",["how the "," different equals"]]
["W0762",[2907,2907,235480,235498],[2900,2900,226474,226493],"Stacks49.12.4/0BWH","Stacks 49.12.4/0BWH",["here. In "," the local"]]
["W0763",[2907,2907,235625,235640],[2900,2900,226620,226636],"citation49.12.6","citation 49.12.6",["equality. Brox's "," is the"]]
["W0764",[2907,2907,235662,235670],[2900,2900,226658,226667],"tag0BWJ.","tag 0BWJ.",["valid current "," It applies"]]
["W0765",[2907,2907,235785,235796],[2900,2900,226782,226794],"section0BWB","section 0BWB",["The archived "," includes Lemmas49.12.1--4,"]]
["W0766",[2907,2907,235806,235823],[2900,2900,226804,226810],"Lemmas49.12.1--4,","Lemmas",["section0BWB includes "," Example49.12.5 and"]]
["W0767",[2907,2907,235824,235838],[2900,2900,226811,226838],"Example49.12.5","49.12.1--4, Example 49.12.5",["includes Lemmas49.12.1--4, "," and Lemma49.12.6;"]]
["W0768",[2907,2907,235843,235856],[2900,2900,226843,226857],"Lemma49.12.6;","Lemma 49.12.6;",["Example49.12.5 and "," a shortened"]]
["W0769",[2907,2907,235917,236073],[2900,2900,226918,226918]," This author initially misclassified the citation as absent; fresh review caught that error before freeze. \\nolinkurl{FINDINGS.md} preserves the correction.","",[" latter part.","\n"]]
["W0770",[2929,2929,238157,238163],[2922,2922,229002,229010],"étale.","\\'etale.",["is finite "," Its primitive"]]
["W0771",[2929,2929,238298,238303],[2922,2922,229145,229152],"étale","\\'etale",["of components "," locally on"]]
["W0772",[2929,2929,238361,238366],[2922,2922,229210,229217],"étale","\\'etale",["is finite "," as well,"]]
["W0773",[2931,2931,238550,238555],[2924,2924,229401,229408],"Étale","\\'Etale",["\\(a=1\\) modN. "," locally the"]]
["W0774",[2931,2931,238727,238732],[2924,2924,229580,229587],"étale","\\'etale",["a finite "," quotient even"]]
["W0775",[2933,2933,239192,239199],[2926,2926,230047,230055],"\\(by\\pm","by \\(\\pm",["choices differ "," 1\\) and"]]
["W0776",[2933,2933,239347,239354],[2926,2926,230203,230211],"\\(by\\pm","by \\(\\pm",["differs only "," 1\\). Thus"]]
["W0777",[2933,2933,239400,239405],[2926,2926,230257,230264],"étale","\\'etale",["the finite "," \\(Q(t)-\\text{algebras}\\), not"]]
["W0778",[2933,2933,239645,239650],[2926,2926,230504,230511],"étale","\\'etale",["normal finite "," cover over"]]
["W0779",[2935,2935,239833,239839],[2928,2928,230694,230702],"Bézout","B\\'ezout",["matrix by "," modN. This"]]
["W0780",[2939,2939,240310,240319],[2932,2932,231173,231185],"Känel2021","K\\\"anel 2021",["Published von "," \\S{}4, \\(p_{8}\\),"]]
["W0781",[2939,2939,240327,240337],[2932,2932,231193,231198],"\\(p_{8}\\),","p.~8,",["Känel2021 \\S{}4, "," (4.1) independently"]]
["W0782",[2939,2939,240425,240442],[2932,2932,231286,231297],"\\(\\text{when}-I\\)","when \\(-I\\)",["occurs exactly "," is absent,"]]
["W0783",[2939,2939,240524,240541],[2932,2932,231379,231390],"\\(\\text{Here}-I\\)","Here \\(-I\\)",["and cusp. "," is present"]]
["W0784",[2939,2939,240553,240574],[2932,2932,231402,231417],"\\(\\text{because}-1\\in","because \\(-1\\in",["is present "," H\\), so"]]
["W0785",[2939,2939,240633,240638],[2932,2932,231476,231483],"étale","\\'etale",["The finite "," model already"]]
["W0786",[2939,2939,240683,240706],[2932,2932,231528,231532],"\\(\\text{from}0,1,\\infty","from",["branch away "," \\) in"]]
["W0787",[2939,2939,240707,240709],[2932,2932,231533,231547],"\\)","\\(0,1,\\infty\\)",["away \\(\\text{from}0,1,\\infty "," in characteristic"]]
["W0788",[2945,2945,241363,241383],[2938,2938,232201,232220],"\\(\\text{pfrak}|p>3\\)","\\(\\mathfrak p|p>3\\)",["every prime "," of \\(K\\),"]]
["W0789",[2945,2945,241399,241429],[2938,2938,232236,232265],"\\(V=O_{K}[t]_{\\text{pfrak}}\\).","\\(V=O_{K}[t]_{\\mathfrak p}\\).",["\\(K\\), take "," Both \\(t\\)"]]
["W0790",[2945,2945,241470,241477],[2938,2938,232306,232314],"and1728","and 1728",["units there, "," is a"]]
["W0791",[2945,2945,241570,241575],[2938,2938,232407,232414],"étale","\\'etale",["the finite "," model \\(U\\)"]]
["W0792",[2947,2947,241997,242019],[2940,2940,232836,232857],"v_{\\text{pfrak}}(N)\\).","v_{\\mathfrak p}(N)\\).",["= d_{H} ","\n"]]
["W0793",[2949,2949,242073,242078],[2942,2942,232911,232926],"pfrak","\\(\\mathfrak p\\)",["summation over "," and division"]]
["W0794",[2951,2951,242314,242318],[2944,2944,233162,233167],"and3","and 3",["At \\(p=2\\) "," use \\S{}2"]]
["W0795",[2951,2951,242611,242616],[2944,2944,233460,233466],"log2.","log 2.",["most \\(d_{H}\\) "," Altogether\n"]]
["W0796",[2955,2955,242764,242780],[2948,2948,233614,233631],"Broxv17:461--488","Brox v17:461--488",["This is "," with every"]]
["W0797",[2955,2955,242842,242854],[2948,2948,233693,233693],"independent ","",["objects. The ","evaluation conclusion, "]]
["W0798",[2955,2955,242877,242879],[2948,2948,233716,233723],"if","applied",["evaluation conclusion, "," accepted for"]]
["W0799",[2955,2955,242880,242892],[2948,2948,233724,233726],"accepted for","to",["conclusion, if "," this same"]]
["W0800",[2959,2959,243096,243106],[2952,2952,233930,233938],"interfaces","required",["are separate "," assigned to"]]
["W0801",[2959,2959,243107,243201],[2952,2952,233939,233946],"assigned to the other two author lanes; this document does not self-approve their conclusions.","inputs.",["separate interfaces "," The prime"]]
["W0802",[2961,2961,243329,243379],[2954,2954,234074,234074],"\\subsection{6. History, incorporation and limits}\n","",["",""]]
["W0803",[2963,2965,243380,245142],[2955,2955,234075,234075],"Actual earlier proof text read: frozen Broxv17 \\S{}\\S{}3--4 at274--488; \\nolinkurl{height/PROOF.md} H0.3 and \\(H_{4}\\); \\nolinkurl{research/v14-brox-order8/PROOF.md}45--56; its actual \\nolinkurl{review/SOURCE_ASSESSMENT.md} sections ``The lattice and discriminant argument'' and ``The modular cover and surface''; its \\nolinkurl{review/REPORT.md}19--33; \\nolinkurl{research/v14-small-prime-conductor/review/REPORT.md} section ``Fresh height estimate''; and retained Protocol-D foundationREPORT/H04. The earlier source assessment already states the imperfect-residue Lenstra application, exact torsion derivative \\(n\\), reversed trace dual and intermediate-field conclusion. Its final review expressly retains published-source/whole-assembly limits. Therefore \\textbf{prior justification found and read} is the historical disposition for these arguments. This packet is a source-pinned expansion and precise current-tag binding, not a claim to have first repaired a newly discovered arithmetic error.\n\nCurrent incorporation: Broxv17 contains the substantive arguments but not this expanded bridge and current-tag expansion; the private height H0.3 retains their inherited status. This packet proposes the bridge for additive incorporation. Current acceptance: pending a reviewer other than this author after the packet is frozen, including the precise joins to the other two evaluation lanes. No global modularity, height-transfer, 214 existence or256 theorem is accepted by this bounded work. The source inventory records what was inspected; it does not claim exhaustive search of every historical archive, nor a new inspection of the complete Serre book. The relevant trace, different, tower and tame-horizontal assertions are instead derived explicitly above.\n","",["",""]]
["W0804",[2971,2971,245398,245569],[2960,2960,234331,234331]," Author: internal model task \\nolinkurl{/root/d214_metric_evaluation} (requested Sol61 lane), 2026-11-10. This is an author proposal awaiting a separately authored review.","",["\\begin{quote}\\footnotesize"," It supplies"]]
["W0805",[2971,2971,245603,245614],[2960,2960,234365,234370],"lines62--78","lines",["Brox \\(v_{17}\\) "," and210--251, conditional"]]
["W0806",[2971,2971,245615,245627],[2960,2960,234371,234391],"and210--251,","62--78 and 210--251,",["\\(v_{17}\\) lines62--78 "," conditional on"]]
["W0807",[2971,2971,245707,245746],[2960,2960,234471,234476],"It supplies neither acceptance of those","Those",["specified below. "," algebraic inputs"]]
["W0808",[2971,2971,245764,245767],[2960,2960,234494,234497],"nor","and",["algebraic inputs "," whole-214/256 closure."]]
["W0809",[2971,2971,245768,245781],[2960,2960,234498,234501],"whole-214/256","the",["inputs nor "," closure. The"]]
["W0810",[2971,2971,245782,245790],[2960,2960,234502,234588],"closure.","remaining arguments for the full 214 and 256 constructions are separate prerequisites.",["nor whole-214/256 "," The immutable"]]
["W0811",[2971,2971,245933,245973],[2960,2960,234731,234771],"\\nolinkurl{SOURCE_USES.json.}\\end{quote}","\\nolinkurl{SOURCE_USES.json}.\\end{quote}",["are in ","\n"]]
["W0812",[2975,2975,246036,246044],[2964,2964,234834,234837],"Read the","The",[""," final published"]]
["W0813",[2975,2975,246061,246077],[2964,2964,234854,234871],"Javanpeykar2014,","Javanpeykar 2014,",["final published "," \\S{}\\S{}2.1/2.3, printed"]]
["W0814",[2975,2975,246103,246119],[2964,2964,234897,234915],"pp93--94/97--98,","pp.~93--94/97--98,",["\\S{}\\S{}2.1/2.3, printed "," and final"]]
["W0815",[2975,2975,246134,246143],[2964,2964,234930,234942],"Känel2021","K\\\"anel 2021",["final von "," \\S{}2.1, printed"]]
["W0816",[2975,2975,246161,246171],[2964,2964,234960,234999],"\\(p_{5}\\).","p.~5 give the following normalizations.",["\\S{}2.1, printed "," The former"]]
["W0817",[2975,2975,246465,246470],[2964,2964,235293,235300],"Néron","N\\'eron",["using the "," top-differential line"]]
["W0818",[2975,2975,246615,246625],[2964,2964,235445,235456],"after(2.2)","after (2.2)",["Its paragraph "," explicitly distinguishes"]]
["W0819",[2975,2975,246757,246821],[2964,2964,235588,235594],"Sources were acquired from their publishers on2026-11-10; hashes","Hashes",["used here. "," and exact"]]
["W0820",[2975,2975,246865,246894],[2964,2964,235638,235667],"\\nolinkurl{SOURCE_USES.json.}","\\nolinkurl{SOURCE_USES.json}.",["retained in ","\n"]]
["W0821",[2983,2983,248619,248625],[2972,2972,237392,237400],"Kähler","K\\\"ahler",["occurs. A "," form raised"]]
["W0822",[2989,2989,249520,249525],[2978,2978,238295,238301],"over2","over 2",["split fibre "," be \\(P_{1},\\ldots"]]
["W0823",[2995,2995,250531,250531],[2984,2984,239307,239316],""," required",["The"," algebraic lane"]]
["W0824",[2995,2995,250542,250546],[2984,2984,239327,239332],"lane","input",["The algebraic "," must supply"]]
["W0825",[2995,2995,250547,250558],[2984,2984,239333,239335],"must supply","is",["algebraic lane "," the actual"]]
["W0826",[2995,2995,250940,250946],[2984,2984,239717,239725],"packet","argument",["here. This "," does not"]]
["W0827",[3021,3021,253756,253761],[3010,3010,242535,242544],"lanes","arguments",["and different "," must establish"]]
["W0828",[3021,3021,254227,254232],[3010,3010,243010,243019],"lane.","argument.",["this metric ","\n"]]
["W0829",[3023,3023,254464,254471],[3012,3012,243251,243259],"genus1.","genus 1.",["covered, including "," Possible elliptic/cusp"]]
["W0830",[3023,3023,254582,254588],[3012,3012,243370,243377],"over2.","over 2.",["the disc "," \\(N=1\\) and"]]
["W0831",[3023,3023,254649,254657],[3012,3012,243438,243445],"degrees1","degrees",["covers have "," and3); the"]]
["W0832",[3023,3023,254658,254664],[3012,3012,243446,243455],"and3);","1 and 3);",["have degrees1 "," the modular"]]
["W0833",[3023,3023,255032,255039],[3012,3012,243823,243831],"genus0,","genus 0,",["inequality to "," its left"]]
["W0834",[3027,3027,255196,255200],[3016,3016,243988,243991],"This","The",[""," is a"]]
["W0835",[3027,3027,255201,255203],[3016,3016,243992,244001],"is","algebraic",["This "," a source/application"]]
["W0836",[3027,3027,255204,255395],[3016,3016,244002,244012],"a source/application explanation of an already written argument; no numerical repair or manuscript edit is proposed. Historical justification was found in the actual earlier source assessment","evaluation",["This is "," and report,"]]
["W0837",[3027,3027,255400,255407],[3016,3016,244017,244026],"report,","different",["assessment and "," including their"]]
["W0838",[3027,3027,255408,255754],[3016,3016,244027,244033],"including their withdrawn normalization concern, and in the current frozen \\(v_{17}\\) proof. We do not call this a newly repaired gap. The explanation can be incorporated by an exact pointer from an additive height-closure packet. Its author status, the still-separate algebraic/different inputs, and the need for fresh non-author acceptance must","bounds",["and report, "," remain explicit."]]
["W0839",[3027,3027,255762,255771],[3016,3016,244041,244057],"explicit.","separate inputs.",["must remain "," The 214"]]
["W0840",[3027,3027,255794,255797],[3016,3016,244080,244088],"the","proposed",["existence and "," proposed256 work"]]
["W0841",[3027,3027,255798,255809],[3016,3016,244089,244092],"proposed256","256",["and the "," work both"]]
["W0842",[3027,3027,255810,255814],[3016,3016,244093,244102],"work","arguments",["the proposed256 "," both consume"]]
["W0843",[3027,3027,255815,255827],[3016,3016,244103,244106],"both consume","use",["proposed256 work "," the same"]]
["W0844",[3033,3033,256210,256318],[3022,3022,244489,244489]," Author/integrator: \\nolinkurl{/root}, 2026-11-10. This is an author proposal for a fresh non-author review.","",["\\begin{quote}\\footnotesize"," It supplements"]]
["W0845",[3033,3033,256598,256669],[3022,3022,244769,244838],"\\nolinkurl{research/quadratic-ten-contact-integration/height/PROOF.md}.","the height supplier reproduced in Section~\\ref{q214:height-supplier}.",["H0.3/H4 in "," No polynomial,"]]
["W0846",[3049,3049,257690,257720],[3038,3038,245859,245894],"\\nolinkurl{different/PROOF.md}","Section~\\ref{q214:height-different}",["construction in "," \\S{}4 identifies"]]
["W0847",[3049,3049,257878,257883],[3038,3038,246052,246059],"étale","\\'etale",["the finite "," model away"]]
["W0848",[3051,3051,258892,258923],[3040,3040,247068,247104],"\\nolinkurl{evaluation/PROOF.md}","Section~\\ref{q214:height-evaluation}",["\\(X_{H}\\). Then "," supplies the"]]
["W0849",[3083,3083,263180,263187],[3072,3072,251361,251370],"History","Remaining",["\\subsection{\\(E\\). "," and remaining"]]
["W0850",[3083,3083,263188,263210],[3072,3072,251371,251384],"and remaining closure}","dependencies}",["\\subsection{\\(E\\). History ","\n"]]
["W0851",[3085,3087,263212,263685],[3074,3074,251386,251394],"The earlier source assessment and review already explained integral evaluation, trace duality, different bounds and the metric constant. This round compares those actual arguments to final primary sources and expands the joins. It does not claim a newly discovered arithmetic error or priority for the underlying proof. The old packets and verdicts stay immutable; the new reviewer decision applies only to the exact new supplement and its stated interfaces.\n\nAcceptance of","Argument",[""," A does"]]
["W0852",[3087,3087,263697,263703],[3074,3074,251406,251412],"accept","supply",["does not "," \\(H_{0}\\) geometry/CM"]]
["W0853",[3087,3087,263949,263955],[3074,3074,251658,251666],"Rémond","R\\'emond",["final 2022 "," body comparison"]]
["W0854",[3087,3087,263997,264000],[3074,3074,251708,251713],"The","Those",["separate item. "," current status"]]
["W0855",[3087,3087,264001,264008],[3074,3074,251714,251720],"current","source",["item. The "," status overlay"]]
["W0856",[3087,3087,264009,264015],[3074,3074,251721,251733],"status","applications",["The current "," overlay must"]]
["W0857",[3087,3087,264016,264023],[3074,3074,251734,251740],"overlay","remain",["current status "," must carry"]]
["W0858",[3087,3087,264024,264028],[3074,3074,251741,251749],"must","separate",["status overlay "," carry those"]]
["W0859",[3087,3087,264029,264133],[3074,3074,251750,251764],"carry those obligations forward rather than infer whole-proof closure from the success of this supplier.","prerequisites.",["overlay must ","\n"]]
["W0860",[3094,3094,264725,264853],[3081,3081,252356,252356]," Author: internal model task \\nolinkurl{/root/sol61_height_foundation}, 2026-11-10. Author proposal, not independent acceptance.","",["\\begin{quote}\\footnotesize"," This selected"]]
["W0861",[3094,3094,265162,265164],[3081,3081,252665,252668],"It","The",["specified below}. "," does not"]]
["W0862",[3094,3094,265165,265169],[3081,3081,252669,252675],"does","source",["below}. It "," not silently"]]
["W0863",[3094,3094,265170,265218],[3081,3081,252676,252690],"not silently claim full published-source closure","qualifications",["It does "," of those"]]
["W0864",[3094,3094,265238,265245],[3081,3081,252710,252733],"proofs.","proofs remain required.",["those inherited "," Publication-version limitations"]]
["W0865",[3094,3094,265323,265358],[3081,3081,252811,252846],"\\nolinkurl{FINDINGS.md.}\\end{quote}","\\nolinkurl{FINDINGS.md}.\\end{quote}",["\\nolinkurl{SOURCES.json} and ","\n"]]
["W0866",[3096,3096,265546,265551],[3083,3083,253034,253044],"*\\chi","\\cdot \\chi",["and \\(\\operatorname{det}(r_{f})=\\epsilon "," _{\\text{cyc}}\\). Added"]]
["W0867",[3100,3100,265955,265994],[3087,3087,253448,253480],"\\nolinkurl{a notin {0,1,2401,-343/32}},","\\(a\\notin\\{0,1,2401,-343/32\\}\\),",["\\(v>0\\), with "," define \\(M=M_{S}(a)\\)"]]
["W0868",[3104,3104,266525,266536],[3091,3091,254011,254023],"outside210,","outside 210,",["indicated contacts; "," even contact"]]
["W0869",[3104,3104,266655,266667],[3091,3091,254142,254155],"dividing576,","dividing 576,",["has degree "," is unramified"]]
["W0870",[3104,3104,266816,266824],[3091,3091,254304,254313],"from210.","from 210.",["\\(L\\) away "," The same"]]
["W0871",[3108,3108,267227,267243],[3095,3095,254716,254733],"discriminant210,","discriminant 210,",["\\(B\\) of "," hence is"]]
["W0872",[3108,3108,267501,267522],[3095,3095,254991,255014],"passages481ff,8110ff;","passages 481ff, 8110ff;",["parent \\nolinkurl{quartic_v14.tex} "," the latter"]]
["W0873",[3110,3110,268055,268064],[3097,3097,255547,255555],"dividing4","dividing",["Dirichlet conductor "," at2. It"]]
["W0874",[3110,3110,268065,268069],[3097,3097,255556,255563],"at2.","4 at 2.",["conductor dividing4 "," It proves"]]
["W0875",[3114,3114,268425,268434],[3101,3101,255919,255921],"at2,3,5,7","at",["that integer "," are15,4,4,1. Adjoining"]]
["W0876",[3114,3114,268435,268447],[3101,3101,255922,255943],"are15,4,4,1.","2,3,5,7 are 15,4,4,1.",["integer at2,3,5,7 "," Adjoining the"]]
["W0877",[3114,3114,268745,268761],[3101,3101,256241,256258],"\\(by2v_{p}(e)\\),","by \\(2v_{p}(e)\\),",["upper break "," the Swan"]]
["W0878",[3114,3114,268817,268833],[3101,3101,256314,256331],"\\(by4v_{p}(e)\\),","by \\(4v_{p}(e)\\),",["two-dimensional representation "," and its"]]
["W0879",[3114,3114,268859,268863],[3101,3101,256357,256359],"by2.","by",["tame codimension "," Exponents70,18,18,6 follow."]]
["W0880",[3114,3114,268864,268883],[3101,3101,256360,256383],"Exponents70,18,18,6","2. Exponents 70,18,18,6",["codimension by2. "," follow. At"]]
["W0881",[3114,3114,269096,269100],[3101,3101,256596,256601],"at5,","at 5,",["original \\(r_{3}\\) "," so the"]]
["W0882",[3122,3122,269784,269796],[3109,3109,257285,257298],"Corollary4.3","Corollary 4.3",["Brox \\(v_{17}\\) "," (label cor:modularheight),"]]
["W0883",[3126,3126,270721,270729],[3113,3113,258223,258232],"factor2,","factor 2,",["one fewer "," the character"]]
["W0884",[3126,3126,270825,270828],[3113,3113,258328,258332],"At2","At 2",["local character. "," choose the"]]
["W0885",[3126,3126,270861,270868],[3113,3113,258365,258373],"modulo4","modulo 4",["nontrivial character "," only if"]]
["W0886",[3126,3126,271005,271014],[3113,3113,258510,258518],"dividing4","dividing",["has conductor "," at2.\n"]]
["W0887",[3126,3126,271015,271019],[3113,3113,258519,258526],"at2.","4 at 2.",["conductor dividing4 ","\n"]]
["W0888",[3132,3132,272050,272054],[3119,3119,259557,259562],"at2,","at 2,",["support only "," already in"]]
["W0889",[3136,3136,272541,272547],[3123,3123,260049,260056],"equal1","equal 1",["_{\\sigma })^{-1/4}\\) "," on \\(G_{L}\\)."]]
["W0890",[3140,3140,273002,273015],[3127,3127,260511,260518],"\\text{tensor}","\\otimes",["commutant \\(B "," \\text{Qbar}_{l}=M_{2}(\\text{Qbar}_{l})\\) imply"]]
["W0891",[3140,3140,273016,273056],[3127,3127,260519,260577],"\\text{Qbar}_{l}=M_{2}(\\text{Qbar}_{l})\\)","\\overline{\\mathbb Q}_{l}=M_{2}(\\overline{\\mathbb Q}_{l})\\)",["\\(B \\text{tensor} "," imply that"]]
["W0892",[3140,3140,273407,273411],[3127,3127,260928,260933],"at3.","at 3.",["same identity "," For the"]]
["W0893",[3140,3140,273459,273464],[3127,3127,260981,260987],"say5,","say 5,",["one prime, "," suffices; no"]]
["W0894",[3146,3146,274342,274347],[3133,3133,261865,261875],"*\\chi","\\cdot \\chi",["and \\(\\epsilon "," \\) have"]]
["W0895",[3157,3157,275031,275050],[3144,3144,262559,262587],"\\(\\text{Qbar}_{5}\\)","\\(\\overline{\\mathbb Q}_{5}\\)",["and over "," its Tate"]]
["W0896",[3157,3157,275204,275212],[3144,3144,262741,262750],"Theorem1","Theorem 1",["published Shimura "," gives the"]]
["W0897",[3159,3159,275810,275815],[3146,3146,263348,263354],"from5","from 5",["\\(L'\\) away "," and the"]]
["W0898",[3159,3159,276269,276272],[3146,3146,263808,263812],"at5","at 5",["chosen embedding "," to a"]]
["W0899",[3165,3165,277653,277657],[3152,3152,265193,265198],"or2,","or 2,",["if \\(s=1\\) "," use \\(r\\ge"]]
["W0900",[3169,3169,278340,278349],[3156,3156,265881,265891],"and(H2.1)","and (H2.1)",["Base change "," supply an"]]
["W0901",[3173,3173,278944,278952],[3160,3160,266486,266496],"Rémond's","R\\'emond's",["to \\(A_{a}\\). "," stable subvariety/quotient"]]
["W0902",[3182,3182,279331,279346],[3169,3169,266875,266892],"Gaudron--Rémond","Gaudron--R\\'emond",["Apply "," Theorem1.9(1) with"]]
["W0903",[3182,3182,279347,279360],[3169,3169,266893,266907],"Theorem1.9(1)","Theorem 1.9(1)",["Apply Gaudron--Rémond "," with reference"]]
["W0904",[3182,3182,279397,279408],[3169,3169,266944,266956],"dimension2,","dimension 2,",["\\(C_{i}\\) of "," base field"]]
["W0905",[3190,3190,280194,280201],[3177,3177,267742,267751],"pp7--8.","pp.~7--8.",["publisher PDF, "," Rémond's authorJune2021"]]
["W0906",[3190,3190,280202,280210],[3177,3177,267752,267762],"Rémond's","R\\'emond's",["PDF, pp7--8. "," authorJune2021 source"]]
["W0907",[3190,3190,280211,280225],[3177,3177,267763,267779],"authorJune2021","author June 2021",["pp7--8. Rémond's "," source explicitly"]]
["W0908",[3190,3190,280276,280289],[3177,3177,267830,267844],"Corollary1.3;","Corollary 1.3;",["version after "," its final2022"]]
["W0909",[3190,3190,280294,280303],[3177,3177,267849,267859],"final2022","final 2022",["Corollary1.3; its "," journal body"]]
["W0910",[3198,3198,281039,281045],[3185,3185,268595,268602],"with1,","with 1,",["its max "," because \\(k\\)"]]
["W0911",[3206,3206,281536,281547],[3193,3193,269093,269105],"with(H0.1),","with (H0.1),",["Combining "," \\(216+128/\\log B_{S}"]]
["W0912",[3210,3210,281823,281839],[3197,3197,269381,269398],"whereas1708R+128","whereas 1708R+128",["with \\(R\\) "," is linear."]]
["W0913",[3224,3224,282368,282376],[3211,3211,269927,269936],"least19.","least 19.",["is at "," With \\(\\theta"]]
["W0914",[3224,3224,282669,282679],[3211,3211,270229,270240],"\\(by1+x\\le","by \\(1+x\\le",["M^{1/\\log B_{S}}\\) "," \\operatorname{exp}(x)\\). The"]]
["W0915",[3235,3235,283264,283385],[3222,3222,270825,270825]," Author: \\nolinkurl{/root}, 2026-11-11. This is a new application proof for independent review, not an acceptance record.","",["\\begin{quote}\\footnotesize"," It changes"]]
["W0916",[3237,3237,283578,283625],[3224,3224,271018,271038],"\\subsection{Sources and historical disposition}","\\subsection{Sources}",["","\n"]]
["W0917",[3239,3239,283703,283710],[3226,3226,271116,271125],"Rémond,","R\\'emond,",["inequality in "," \\emph{Propriétés de"]]
["W0918",[3239,3239,283711,283727],[3226,3226,271126,271146],"\\emph{Propriétés","\\emph{Propri\\'et\\'es",["in Rémond, "," de la"]]
["W0919",[3241,3241,284230,284298],[3228,3228,271649,271649],"\\(I\\) read that argument and its recorded source-route disposition. ","",["lines 30617--30636. ","It consumes "]]
["W0920",[3241,3241,284353,284369],[3228,3228,271704,271722],"Gaudron--Rémond,","Gaudron--R\\'emond,",["proof of "," \\emph{Nouveaux théorèmes"]]
["W0921",[3241,3241,284385,284394],[3228,3228,271738,271751],"théorèmes","th\\'eor\\`emes",["Gaudron--Rémond, \\emph{Nouveaux "," d'isogénie}, Mémoires"]]
["W0922",[3241,3241,284395,284407],[3228,3228,271752,271766],"d'isogénie},","d'isog\\'enie},",["\\emph{Nouveaux théorèmes "," Mémoires SMF"]]
["W0923",[3241,3241,284408,284416],[3228,3228,271767,271777],"Mémoires","M\\'emoires",["théorèmes d'isogénie}, "," SMF 176"]]
["W0924",[3241,3241,284468,284502],[3228,3228,271829,271832],"\\(I\\) independently downloaded the","The",["pp. 97--98. "," final publisher"]]
["W0925",[3241,3241,284519,284523],[3228,3228,271849,271856],"PDF,","PDF has",["final publisher "," SHA256 \\nolinkurl{b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4},"]]
["W0926",[3241,3241,284531,284658],[3228,3228,271864,271941],"\\nolinkurl{b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4}, and read the text and image of printed \\(p\\). 98.","\\nolinkurl{b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4}.",["PDF, SHA256 "," The source"]]
["W0927",[3243,3243,284922,284928],[3230,3230,272205,272213],"Rémond","R\\'emond",["proof uses "," 2022, Corollary"]]
["W0928",[3243,3243,284954,284960],[3230,3230,272239,272247],"Rémond","R\\'emond",["1.3, and "," 2017, Theorem"]]
["W0929",[3243,3243,285248,285254],[3230,3230,272535,272538],"Public","The",["stated scope. "," Version 15's"]]
["W0930",[3243,3243,285263,285276],[3230,3230,272547,272549],"15's accepted","15",["Public Version "," single-surface application"]]
["W0931",[3243,3243,285304,285340],[3230,3230,272577,272581],"is historical support for the route,","does",["single-surface application "," not approval"]]
["W0932",[3243,3243,285345,285353],[3230,3230,272586,272588],"approval","by",["route, not "," of the"]]
["W0933",[3243,3243,285354,285356],[3230,3230,272589,272602],"of","itself supply",["not approval "," the new"]]
["W0934",[3243,3243,285360,285364],[3230,3230,272606,272606]," new","",[" of the"," multiplicity application"]]
["W0935",[3251,3251,286396,286404],[3238,3238,273638,273648],"Poincaré","Poincar\\'e",[""," complete reducibility"]]
["W0936",[3263,3263,287902,287962],[3250,3250,275146,275188],"\\nolinkurl{quartic214-protocol-d/PRIMARY_SOURCE_BRIDGES.md}.","Section~\\ref{q214:primary-source-bridges}.",["recorded in "," It holds"]]
["W0937",[3286,3286,289558,289597],[3273,3273,276784,276787],"This proof does not itself accept those","The",["are unchanged. "," receiving applications"]]
["W0938",[3286,3286,289621,289623],[3273,3273,276811,276818],"or","require",["receiving applications "," their other"]]
["W0939",[3286,3286,289636,289636],[3273,3273,276831,276838],"","stated ",["their other ","premises.\n"]]
["W0940",[3299,3299,292095,292148],[3286,3286,279297,279310],"modification, subject to review of this substitution.","modification.",["need no "," The indirect"]]
["W0941",[3299,3299,292162,292168],[3286,3286,279324,279332],"Rémond","R\\'emond",["The indirect "," dependencies and"]]
["W0942",[3302,3302,292247,292460],[3289,3289,279411,279411],"Acceptance, if obtained, must bind this proof, these nine obligations, the actual \\(H_{2}\\) construction, H3/H4 consumer and published source version. The author makes no whole-214 Protocol \\(D\\) completion claim.","",["","\n"]]
["W0943",[3308,3308,292768,292807],[3295,3295,279719,279719]," Author: \\nolinkurl{/root}, 2026-11-10.","",["\\begin{quote}\\footnotesize"," This is"]]
["W0944",[3308,3308,292865,292930],[3295,3295,279777,279842],"\\nolinkurl{../quadratic-ten-contact-integration/height/PROOF.md},","height supplier reproduced in Section~\\ref{q214:height-supplier},",["the unchanged "," H1--H3. It"]]
["W0945",[3308,3308,292942,293007],[3295,3295,279854,279862],"is author work awaiting the separately recorded review. It closes","supplies",["H1--H3. It "," only the"]]
["W0946",[3308,3308,293028,293041],[3295,3295,279883,279889],"source-access","source",["the identified "," and application"]]
["W0947",[3308,3308,293042,293066],[3295,3295,279890,279903],"and application records;","applications;",["identified source-access "," it does"]]
["W0948",[3312,3312,293212,293240],[3299,3299,280049,280052],"\\(I\\) retrieved and read the","The",[""," published second"]]
["W0949",[3312,3312,293292,293299],[3299,3299,280104,280110],"(1986),","(1986)",["\\emph{Rational Points} "," including the"]]
["W0950",[3312,3312,293300,293347],[3299,3299,280111,280119],"including the printed title/copyright pages and","contains",["Points} (1986), "," Faltings, ``Complements"]]
["W0951",[3312,3312,293358,293371],[3299,3299,280130,280147],"``Complements","\\emph{Complements",["and Faltings, "," to Mordell'',"]]
["W0952",[3312,3312,293375,293385],[3299,3299,280151,280160],"Mordell'',","Mordell},",["``Complements to "," Theorem 1(a)--(b),"]]
["W0953",[3312,3312,293434,293496],[3299,3299,280209,280209]," \\(I\\) inspected the page image as well as its extracted text.","",[" page 212)."," The exact"]]
["W0954",[3312,3312,293710,293771],[3299,3299,280423,280431],"edition, not an identification inferred from a search result.","edition.",["the published "," The publisher's"]]
["W0955",[3316,3316,294885,294904],[3303,3303,281545,281573],"\\(\\text{Qbar}_{5}\\)","\\(\\overline{\\mathbb Q}_{5}\\)",["scalars to "," it becomes"]]
["W0956",[3316,3316,294916,294943],[3303,3303,281585,281621],"\\(M_{2}(\\text{Qbar}_{5})\\).","\\(M_{2}(\\overline{\\mathbb Q}_{5})\\).",["it becomes "," The semisimple"]]
["W0957",[3322,3322,296558,296572],[3309,3309,283236,283239],"\\(I\\) read the","The",[""," author-hosted scan"]]
["W0958",[3322,3322,296660,296660],[3309,3309,283327,283336],"","contains ",["Geometry} (1986), ","Proposition 12.1 "]]
["W0959",[3322,3322,296709,296719],[3309,3309,283385,283397],"paragraph,","paragraph on",["following decomposition "," printed p.122"]]
["W0960",[3322,3322,296921,296971],[3309,3309,283599,283610],"image-only; the page image was inspected directly.","image-only.",["scan is "," The theorem"]]
["W0961",[3338,3338,299651,299670],[3325,3325,286290,286318],"\\(\\text{Qbar}_{5}\\)","\\(\\overline{\\mathbb Q}_{5}\\)",["\\(Q_{5}\\), with "," used only"]]
["W0962",[3341,3341,300394,300400],[3328,3328,287042,287050],"Rémond","R\\'emond",["inputs. The "," averaging inequality,"]]
["W0963",[3347,3347,300606,300617],[3334,3334,287256,287256],"\\(I\\) read ","",["","Li, ``Newforms "]]
["W0964",[3347,3347,300714,300714],[3334,3334,287353,287366],"","is available ",["(1975), pp.294--296, ","in Göttingen's "]]
["W0965",[3347,3347,300717,300728],[3334,3334,287369,287382],"Göttingen's","G\\\"ottingen's",["pp.294--296, in "," digitized published"]]
["W0966",[3347,3347,300979,300986],[3334,3334,287633,287641],"Page294","Page 294",["and hashes. "," defines normalized"]]
["W0967",[3347,3347,301026,301033],[3334,3334,287681,287689],"page296","page 296",["primitive newforms; "," defines the"]]
["W0968",[3347,3347,301139,301146],[3334,3334,287795,287803],"Lemma6,","Lemma 6,",["immediately before "," gives \\(F|H_{M}=\\gamma"]]
["W0969",[3349,3349,302176,302192],[3336,3336,288833,288833],"already checked ","",["of the ","published Shimura "]]
["W0970",[3349,3349,302210,302218],[3336,3336,288851,288860],"Theorem1","Theorem 1",["published Shimura "," used in"]]
["W0971",[3351,3351,303207,303211],[3338,3338,289849,289852],"This","The",["premises explicit. "," is a"]]
["W0972",[3351,3351,303212,303214],[3338,3338,289853,289859],"is","stated",["explicit. This "," a source/application"]]
["W0973",[3351,3351,303215,303216],[3338,3338,289860,289870],"a","modularity",["This is "," source/application bridge"]]
["W0974",[3351,3351,303217,303235],[3338,3338,289871,289874],"source/application","and",["is a "," bridge awaiting"]]
["W0975",[3351,3351,303236,303310],[3338,3338,289875,289891],"bridge awaiting the new independent review, not a new assertion that those","Galois-conjugacy",["a source/application "," premises were"]]
["W0976",[3351,3351,303320,303324],[3338,3338,289901,289907],"were","remain",["those premises "," all audited"]]
["W0977",[3351,3351,303325,303342],[3338,3338,289908,289917],"all audited here.","required.",["premises were ","\n"]]
["W0978",[3355,3355,303411,303433],[3342,3342,289986,289989],"\\(I\\) also checked the","The",[""," publisher PDF"]]
["W0979",[3355,3355,303451,303467],[3342,3342,290007,290025],"Gaudron--Rémond,","Gaudron--R\\'emond,",["PDF of "," ``Théorème des"]]
["W0980",[3355,3355,303468,303478],[3342,3342,290026,290040],"``Théorème","``Th\\'eor\\`eme",["of Gaudron--Rémond, "," des périodes"]]
["W0981",[3355,3355,303483,303491],[3342,3342,290045,290055],"périodes","p\\'eriodes",["``Théorème des "," et degrés"]]
["W0982",[3355,3355,303495,303501],[3342,3342,290059,290067],"degrés","degr\\'es",["périodes et "," minimaux d'isogénies'',"]]
["W0983",[3355,3355,303511,303525],[3342,3342,290077,290093],"d'isogénies'',","d'isog\\'enies'',",["degrés minimaux "," \\emph{Commentarii Mathematici"]]
["W0984",[3355,3355,303630,303630],[3342,3342,290198,290211],""," is available",[" DOI \\url{https://doi.org/10.4171/CMH/322},"," from \\url{https://ems.press/content/serial-article-files/43351?nt=1}."]]
["W0985",[3355,3355,303775,303788],[3342,3342,290356,290370],"Definition2.1","Definition 2.1",["in \\nolinkurl{PRIMARY_SOURCE_ACCESS.json}. "," and \\S{}2.3,"]]
["W0986",[3355,3355,303928,303941],[3342,3342,290510,290524],"Corollary8.4,","Corollary 8.4,",["\\(\\pi \\). "," printed p.400,"]]
["W0987",[3355,3355,304061,304093],[3342,3342,290644,290644]," \\(I\\) checked both page images.","",[" polarization hypothesis."," Combining the"]]
["W0988",[3357,3357,304761,304767],[3344,3344,291312,291317],"closes","lower",["normalization. This "," that particular"]]
["W0989",[3357,3357,304768,304864],[3344,3344,291318,291323],"that particular Bost-normalization source/application record at author level, pending review; it","bound",["This closes "," does not"]]
["W0990",[3357,3357,304881,304889],[3344,3344,291340,291350],"Rémond's","R\\'emond's",["not supply "," superadditivity inequality."]]
["W0991",[3361,3361,305622,305640],[3348,3348,292083,292103],"\\subsection{Rémond","\\subsection{R\\'emond",[""," publication-version check"]]
["W0992",[3363,3363,305682,305715],[3350,3350,292145,292148],"On 2026-11-10 \\(I\\) rechecked the","The",[""," publisher record"]]
["W0993",[3363,3363,305733,305736],[3350,3350,292166,292176],"for","identifies",["publisher record "," \\emph{Propriétés de"]]
["W0994",[3363,3363,305737,305753],[3350,3350,292177,292197],"\\emph{Propriétés","\\emph{Propri\\'et\\'es",["record for "," de la"]]
["W0995",[3363,3363,306284,306347],[3350,3350,292728,292728],"\\(I\\) compared those actual passages, not merely the abstract. ","",["in \\(H_{3}\\). ","The final "]]
["W0996",[3365,3365,306477,306591],[3352,3352,292858,292866],"new Faltings, Milne and Li source checks narrow the previous access qualification. They neither resolve the Rémond","R\\'emond",["The "," version comparison"]]
["W0997",[3365,3365,306611,306620],[3352,3352,292886,292889],"nor close","and",["version comparison "," the \\(H_{0}\\)"]]
["W0998",[3365,3365,306672,306674],[3352,3352,292941,292944],"or","and",["modularity, modular-height "," analytic prime-pattern"]]
["W0999",[3365,3365,306698,306734],[3352,3352,292968,292974],"chain. Historical files and verdicts","inputs",["analytic prime-pattern "," remain unchanged."]]
["W1000",[3365,3365,306742,306752],[3352,3352,292982,293004],"unchanged.","separate requirements.",["verdicts remain "," The new"]]
["W1001",[3365,3365,306756,306760],[3352,3352,293008,293008]," new","",[" unchanged. The"," sources are"]]
["W1002",[3365,3365,306858,306863],[3352,3352,293106,293116],"added","reproduced",["are not "," to this"]]
["W1003",[3365,3365,306864,306883],[3352,3352,293117,293122],"to this repository.","here.",["not added ","\n"]]
["W1004",[3368,3368,307014,307051],[3355,3355,293253,293291],"existing214}\\label{q214:source-carry}","existing 214}\\label{q214:source-carry}",["carry to ","\n"]]
["W1005",[3370,3370,307158,307173],[3357,3357,293398,293416],"\\textbf{Current","\\textbf{Foundation",["\\begin{quote}\\small "," foundation overlay:}"]]
["W1006",[3370,3370,307174,307194],[3357,3357,293417,293426],"foundation overlay:}","sources:}",["\\begin{quote}\\small \\textbf{Current "," The Version~15"]]
["W1007",[3370,3370,307550,307552],[3357,3357,293782,293791],"is","describes",["historical text "," retained as"]]
["W1008",[3370,3370,307553,307561],[3357,3357,293792,293795],"retained","the",["text is "," as evidence;"]]
["W1009",[3370,3370,307562,307564],[3357,3357,293796,293803],"as","earlier",["is retained "," evidence; it"]]
["W1010",[3370,3370,307565,307574],[3357,3357,293804,293810],"evidence;","source",["retained as "," it does"]]
["W1011",[3370,3370,307575,307654],[3357,3357,293811,293830],"it does not negate or independently accept that changed application.\\end{quote}","version.\\end{quote}",["as evidence; ","\n"]]
["W1012",[3372,3372,307656,307775],[3359,3359,293832,293832],"Author \\nolinkurl{/root/d214_uniform_existence}, 2026-11-11. This is an author comparison, not independent acceptance. ","",["","The prior "]]
["W1013",[3372,3372,307940,307959],[3359,3359,293997,294006],"root-frozen104-file","specified",["is the "," subset at"]]
["W1014",[3372,3372,307960,307966],[3359,3359,294007,294015],"subset","104-file",["the root-frozen104-file "," at \\nolinkurl{../../public-carry/},"]]
["W1015",[3372,3372,307967,308002],[3359,3359,294016,294023],"at \\nolinkurl{../../public-carry/},","subset,",["root-frozen104-file subset "," manifest SHA256\\nolinkurl{4137a55c240edb06d39f6332dc1145d8591f98045ff2ec62d817c97c0f8ab487}."]]
["W1016",[3372,3372,308096,308110],[3359,3359,294117,294120],"Full read-only","The",["manifest SHA256\\nolinkurl{4137a55c240edb06d39f6332dc1145d8591f98045ff2ec62d817c97c0f8ab487}. "," public checkout"]]
["W1017",[3372,3372,308117,308117],[3359,3359,294127,294134],""," source",[" read-only public"," checkout is"]]
["W1018",[3372,3372,308130,308219],[3359,3359,294147,294208],"HEAD\\nolinkurl{1a49013b5683f58d2f88bb018a07d13770354157}. No acceptance is authored here.","revision\\nolinkurl{1a49013b5683f58d2f88bb018a07d13770354157}.",["checkout is ","\n"]]
["W1019",[3374,3374,308305,308314],[3361,3361,294294,294304],"frozen214","frozen 214",["the entire "," \\nolinkurl{existence/sources/quartic_v15.tex} are"]]
["W1020",[3374,3374,308369,308380],[3361,3361,294359,294371],"same1924438","same 1924438",["are the "," raw bytes,"]]
["W1021",[3374,3374,308580,308588],[3361,3361,294571,294574],"Protocol","The",["source applications. "," D's permitted"]]
["W1022",[3374,3374,308589,308592],[3361,3361,294575,294581],"D's","source",["applications. Protocol "," permitted reuse"]]
["W1023",[3374,3374,308593,308602],[3361,3361,294582,294592],"permitted","statements",["Protocol D's "," reuse of"]]
["W1024",[3374,3374,308603,308608],[3361,3361,294593,294596],"reuse","are",["D's permitted "," of exact"]]
["W1025",[3374,3374,308609,308611],[3361,3361,294597,294601],"of","used",["permitted reuse "," exact accepted"]]
["W1026",[3374,3374,308612,308753],[3361,3361,294602,294609],"exact accepted derivations does not require pretending that this author re-proved every published theorem or every old proof. It does require","through",["reuse of "," the object/domain/map/consumer"]]
["W1027",[3374,3374,308758,308784],[3361,3361,294614,294621],"object/domain/map/consumer","object,",["require the "," comparison made"]]
["W1028",[3374,3374,308785,308795],[3361,3361,294622,294629],"comparison","domain,",["the object/domain/map/consumer "," made here."]]
["W1029",[3374,3374,308796,308851],[3361,3361,294630,294633],"made here. The source-first public final006 application","map",["object/domain/map/consumer comparison "," and connection"]]
["W1030",[3374,3374,308856,308866],[3361,3361,294638,294646],"connection","consumer",["application and "," decisions, source-profile"]]
["W1031",[3374,3374,308867,308877],[3361,3361,294647,294658],"decisions,","comparisons",["and connection "," source-profile decisions"]]
["W1032",[3374,3374,308878,308892],[3361,3361,294659,294665],"source-profile","below,",["connection decisions, "," decisions and"]]
["W1033",[3374,3374,308893,308902],[3361,3361,294666,294698],"decisions","with all their stated hypotheses",["decisions, source-profile "," and findings"]]
["W1034",[3374,3374,308907,308915],[3361,3361,294703,294709],"findings","source",["decisions and "," retain their"]]
["W1035",[3374,3374,308916,309135],[3361,3361,294710,294725],"retain their original scopes and limitations. Their green result is not a premise of an arithmetic implication. Eligible review must decide whether these exact bindings carry; this author does not certify that decision.","qualifications.",["and findings ","\n"]]
["W1036",[3376,3376,309512,309518],[3363,3363,295102,295109],"new214","new 214",["deduce a "," solution; only"]]
["W1037",[3376,3376,309688,309696],[3363,3363,295279,295288],"degree75","degree 75",["old eleven-witness "," predicate. The"]]
["W1038",[3376,3376,309712,309718],[3363,3363,295304,295311],"raw224","raw 224",["predicate. The "," construction branches"]]
["W1039",[3376,3376,309752,309765],[3363,3363,295345,295359],"public223/222","public 223/222",["before the "," paired-root/trace-quotient reductions."]]
["W1040",[3376,3376,309805,309876],[3363,3363,295399,295399],"No approval of the latter is required to infer their unused equations. ","",["paired-root/trace-quotient reductions. ","The retained "]]
["W1041",[3376,3376,309889,309917],[3363,3363,295412,295441],"scalar/root/reference/raw224","scalar/root/reference/raw 224",["The retained "," inverse maps"]]
["W1042",[3376,3376,309995,310004],[3363,3363,295519,295529],"frozen214","frozen 214",["in the "," algebra packet."]]
["W1043",[3378,3378,310058,310073],[3365,3365,295583,295586],"Read the actual","The",["and normalization] "," generator proof"]]
["W1044",[3378,3378,310093,310106],[3365,3365,295606,295629],"V15:347--443:","V15:347--443 shows that",["proof at "," two-isogeny descent,"]]
["W1045",[3378,3378,310467,310495],[3365,3365,295990,295999],"^{4}*x_{\\text{old}},\\epsilon","^{4}\\cdot",["and \\((x_{\\text{new}},y_{\\text{new}})=(\\epsilon "," ^{6}*y_{\\text{old}})\\). Explicitly"]]
["W1046",[3378,3378,310496,310519],[3365,3365,296000,296052],"^{6}*y_{\\text{old}})\\).","x_{\\text{old}},\\epsilon ^{6}\\cdot y_{\\text{old}})\\).",["\\((x_{\\text{new}},y_{\\text{new}})=(\\epsilon ^{4}*x_{\\text{old}},\\epsilon "," Explicitly \\((75-53\\sqrt{2})(17+12\\sqrt{2})=3-\\sqrt{2}\\)"]]
["W1047",[3378,3378,310669,310690],[3365,3365,296202,296228],"-660+417sqrt2 over32.","\\((-660+417\\sqrt{2})/32\\).",["transformation gives "," Thus the"]]
["W1048",[3378,3378,310743,310779],[3365,3365,296281,296322],"\\(E:y^{2}=x^{3}-(3-\\sqrt{2})^{2}*x\\)","\\(E:y^{2}=x^{3}-(3-\\sqrt{2})^{2}\\cdot x\\)",["are exactly "," and \\(P=2(1+\\sqrt{2},2\\sqrt{2})\\),"]]
["W1049",[3378,3378,311023,311034],[3365,3365,296566,296578],"profileSF27","profile SF27",["(n,a,t,b). Current "," explicitly records"]]
["W1050",[3378,3378,311166,311172],[3365,3365,296710,296717],"the214","the 214",["step of "," supplement needs"]]
["W1051",[3388,3388,311899,311923],[3375,3375,297444,297473],"\\(n_{\\text{pole}}*\\theta","\\(n_{\\text{pole}}\\cdot \\theta",["\\(n_{\\text{pole}}\\) and "," \\), including"]]
["W1052",[3388,3388,311981,311988],[3375,3375,297531,297539],"corank1","corank 1",["full Selmer "," before invoking"]]
["W1053",[3388,3388,312119,312133],[3375,3375,297670,297685],"at11656--11739","at 11656--11739",["preparation-zero proof "," then rescales"]]
["W1054",[3388,3388,312228,312234],[3375,3375,297780,297783],"new214","new",["\\(b\\). The "," supplementP19 verifies"]]
["W1055",[3388,3388,312235,312248],[3375,3375,297784,297802],"supplementP19","214 supplement P19",["The new214 "," verifies every"]]
["W1056",[3390,3390,312721,312736],[3377,3377,298275,298278],"Read the actual","The",["index set] "," current proof"]]
["W1057",[3390,3390,312751,312765],[3377,3377,298293,298308],"at13347--13946","at 13347--13946",["current proof "," and the"]]
["W1058",[3390,3390,312773,312780],[3377,3377,298316,298316]," actual","",[" and the"," earlier \\(v_{11}\\)"]]
["W1059",[3390,3390,312850,312860],[3377,3377,298386,298426],"arguments.","arguments supply the construction below.",["and \\nolinkurl{interface.md} "," For a"]]
["W1060",[3390,3390,312910,312924],[3377,3377,298476,298495],"\\(D=2^{a}*d\\),","\\(D=2^{a}\\cdot d\\),",["primitive conductor "," the retained"]]
["W1061",[3390,3390,313016,313029],[3377,3377,298587,298594],"\\text{tensor}","\\otimes",["_{Dm})/Q(\\zeta _{m})}(z_{Dm} "," e_{\\chi })\\)"]]
["W1062",[3390,3390,313064,313082],[3377,3377,298629,298652],"\\((m,c*d_{s})=1\\).","\\((m,c\\cdot d_{s})=1\\).",["\\(m\\) with "," \\(K_{5}\\) makes"]]
["W1063",[3390,3390,313117,313142],[3377,3377,298687,298708],"\\(\\text{Nprime}=c*d_{s}\\)","\\(N'_K=c\\cdot d_{s}\\)",["\\(N_{K}=2Nd\\) and "," coprime. Restricting"]]
["W1064",[3390,3390,313230,313246],[3377,3377,298796,298813],"Kato1999\\S{}0.1,","Kato 1999\\S{}0.1,",["required by "," not merely"]]
["W1065",[3390,3390,313262,313281],[3377,3377,298829,298849],"smaller2004\\S{}13.1","smaller 2004\\S{}13.1",["merely the "," set. The"]]
["W1066",[3390,3390,313314,313323],[3377,3377,298882,298889],"\\(j_{*}\\)","\\(j_*\\)",["the integral "," condition by"]]
["W1067",[3390,3390,313572,313577],[3377,3377,299138,299144],"from2","from 2",["localizations away "," used downstream."]]
["W1068",[3392,3392,313681,313688],[3379,3379,299248,299257],"Nprime,","\\(N'_K\\),",["not dividing "," if q|m"]]
["W1069",[3392,3392,313701,313726],[3379,3379,299270,299288],"\\(S_{\\text{Dmq}}=S_{Dm}\\)","\\(S_{Dmq}=S_{Dm}\\)",["q|m then "," and Proposition8.12"]]
["W1070",[3392,3392,313731,313746],[3379,3379,299293,299309],"Proposition8.12","Proposition 8.12",["\\(S_{\\text{Dmq}}=S_{Dm}\\) and "," contributes the"]]
["W1071",[3392,3392,313778,313786],[3379,3379,299341,299350],"factor1.","factor 1.",["empty product, "," If \\(q\\)"]]
["W1072",[3392,3392,313844,313855],[3379,3379,299408,299420],"outside2Nd;","outside 2Nd;",["forces \\(q\\) "," it is"]]
["W1073",[3395,3395,313958,313970],[3382,3382,299523,299535],"1-a_{q}*\\chi","1-a_{q}\\cdot",[""," (q)*q^{-1}*\\sigma _{q}^{-1}+q^{-1}*\\sigma"]]
["W1074",[3395,3395,313971,313988],[3382,3382,299536,299540],"(q)*q^{-1}*\\sigma","\\chi",["1-a_{q}*\\chi "," _{q}^{-1}+q^{-1}*\\sigma _{q}^{-2}\\\\"]]
["W1075",[3395,3395,313989,314012],[3382,3382,299541,299597],"_{q}^{-1}+q^{-1}*\\sigma","(q)\\cdot q^{-1}\\cdot \\sigma _{q}^{-1}+q^{-1}\\cdot \\sigma",["1-a_{q}*\\chi (q)*q^{-1}*\\sigma "," _{q}^{-2}\\\\\n=P_{q}(q^{-1}*\\sigma"]]
["W1076",[3396,3396,314025,314045],[3383,3383,299610,299635],"=P_{q}(q^{-1}*\\sigma","=P_{q}(q^{-1}\\cdot \\sigma",["_{q}^{-1}+q^{-1}*\\sigma _{q}^{-2}\\\\\n"," _{q}^{-1}), P_{q}(X)=1-a_{q}*\\chi"]]
["W1077",[3396,3396,314058,314079],[3383,3383,299648,299669],"P_{q}(X)=1-a_{q}*\\chi","P_{q}(X)=1-a_{q}\\cdot",["=P_{q}(q^{-1}*\\sigma _{q}^{-1}), "," (q)*X+q*X^{2}\n"]]
["W1078",[3396,3396,314080,314093],[3383,3383,299670,299698],"(q)*X+q*X^{2}","\\chi (q)\\cdot X+q\\cdot X^{2}",["_{q}^{-1}), P_{q}(X)=1-a_{q}*\\chi ","\n"]]
["W1079",[3399,3399,314138,314146],[3386,3386,299743,299757],"\\(T*\\chi","\\(T\\otimes\\chi",["acts on "," \\) and"]]
["W1080",[3399,3399,314274,314295],[3386,3386,299885,299904],"\\(S_{D*N_{K}*2^{n}}\\)","\\(S_{DN_{K}2^{n}}\\)",["the supports "," and \\(S_{D*2^{n}}\\)"]]
["W1081",[3399,3399,314300,314315],[3386,3386,299909,299923],"\\(S_{D*2^{n}}\\)","\\(S_{D2^{n}}\\)",["\\(S_{D*N_{K}*2^{n}}\\) and "," equal prime(2Nd)."]]
["W1082",[3399,3399,314322,314333],[3386,3386,299930,299960],"prime(2Nd).","\\(\\operatorname{prime}(2Nd)\\).",["\\(S_{D*2^{n}}\\) equal "," Corestriction transitivity"]]
["W1083",[3399,3399,314398,314440],[3386,3386,300025,300066],"\\(\\text{cor}(y_{N_{K}*2^{n}})=y_{2^{n}}\\),","\\(\\text{cor}(y_{N_{K}2^{n}})=y_{2^{n}}\\),",["field gives "," without an"]]
["W1084",[3399,3399,314590,314600],[3386,3386,300216,300227],"Section0.7","Section 0.7",["exactly the "," divisor-parameter-one class"]]
["W1085",[3399,3399,314629,314640],[3386,3386,300256,300268],"\\(xi_{K}\\),","\\(\\xi_{K}\\),",["divisor-parameter-one class "," distinguished from"]]
["W1086",[3399,3399,314679,314682],[3386,3386,300307,300315],"xi.","\\(\\xi\\).",["modular symbol "," Thus the"]]
["W1087",[3399,3399,315021,315027],[3386,3386,300654,300659],"source","index",["\\(K_{2}\\). This "," repair is"]]
["W1088",[3399,3399,315028,315034],[3386,3386,300660,300678],"repair","and class argument",["This source "," is incorporated"]]
["W1089",[3399,3399,315038,315050],[3386,3386,300682,300685],"incorporated","the",["repair is "," already and"]]
["W1090",[3399,3399,315051,315058],[3386,3386,300686,300689],"already","one",["is incorporated "," and is"]]
["W1091",[3399,3399,315059,315062],[3386,3386,300690,300694],"and","used",["incorporated already "," is unchanged"]]
["W1092",[3399,3399,315063,315065],[3386,3386,300695,300697],"is","by",["already and "," unchanged in214's"]]
["W1093",[3399,3399,315066,315075],[3386,3386,300698,300701],"unchanged","the",["and is "," in214's supplier."]]
["W1094",[3399,3399,315076,315083],[3386,3386,300702,300705],"in214's","214",["is unchanged "," supplier. A"]]
["W1095",[3399,3399,315122,315141],[3386,3386,300744,300764],"locator13775--13778","locator 13775--13778",["current connection "," summarizes the"]]
["W1096",[3399,3399,315249,315267],[3386,3386,300872,300891],"actual13799--13899","actual 13799--13899",["binds the "," argument as"]]
["W1097",[3401,3401,315707,315712],[3388,3388,301331,301337],"at2N.","at 2N.",["local squareclasses "," The common"]]
["W1098",[3401,3401,315904,315916],[3388,3388,301529,301542],"at6650--6721","at 6650--6721",["terminal argument "," compares the"]]
["W1099",[3401,3401,316293,316299],[3388,3388,301919,301926],"New214","New 214",["via V15-PROJECT-CLOSURE. "," only consumes"]]
["W1100",[3401,3401,316557,316593],[3388,3388,302184,302184],"this does not assert a new proof of ","",["fixed curve; ","all RC "]]
["W1101",[3401,3401,316597,316599],[3388,3388,302188,302196],"RC","internal",["of all "," internals by"]]
["W1102",[3401,3401,316600,316609],[3388,3388,302197,302216],"internals","restricted-converse",["all RC "," by this"]]
["W1103",[3401,3401,316610,316612],[3388,3388,302217,302227],"by","hypotheses",["RC internals "," this author."]]
["W1104",[3401,3401,316613,316617],[3388,3388,302228,302234],"this","remain",["internals by "," author.\n"]]
["W1105",[3401,3401,316618,316625],[3388,3388,302235,302244],"author.","required.",["by this ","\n"]]
["W1106",[3416,3416,318010,318017],[3403,3403,303629,303634],"*\\delta","\\cdot",["least \\(\\alpha "," /(4C_{\\text{star}})\\); no"]]
["W1107",[3416,3416,318018,318040],[3403,3403,303635,303652],"/(4C_{\\text{star}})\\);","\\delta /(4C_*)\\);",["\\(\\alpha *\\delta "," no monotonicity"]]
["W1108",[3416,3416,318062,318071],[3403,3403,303674,303684],"constant1","constant 1",["monotonicity with "," for normalized"]]
["W1109",[3416,3416,318553,318559],[3403,3403,304166,304173],"the214","the 214",["prime theorem; "," coefficient list"]]
["W1110",[3418,3418,318711,318725],[3405,3405,304325,304340],"at17545--20359","at 17545--20359",["actual proof "," uses fixed"]]
["W1111",[3418,3418,319413,319424],[3405,3405,305028,305040],"rational214","rational 214",["obstruction. The "," coefficient list"]]
["W1112",[3418,3418,319733,319738],[3405,3405,305349,305352],"mod16","mod",["\\(\\pi =9\\) "," and1+3i mod7"]]
["W1113",[3418,3418,319739,319746],[3405,3405,305353,305355],"and1+3i","16",["=9\\) mod16 "," mod7 imply"]]
["W1114",[3418,3418,319747,319751],[3405,3405,305356,305370],"mod7","and 1+3i mod 7",["mod16 and1+3i "," imply \\(p=1\\)"]]
["W1115",[3418,3418,319766,319770],[3405,3405,305385,305390],"mod8","mod 8",["imply \\(p=1\\) "," and \\((7/p)=-1\\)."]]
["W1116",[3420,3420,320288,320434],[3407,3407,305908,305988],"and\\nolinkurl{881213958ad12b1af53e3c6758361ea8e1c371833453bcac7d63ee48909ad971}, exactly the subject hashes in the public source-profile decision.","and\\nolinkurl{881213958ad12b1af53e3c6758361ea8e1c371833453bcac7d63ee48909ad971}.",["raw hashes\\nolinkurl{3668753afd46bff7e3a1bc3bed63d2f102009d5bd3d379fa67411c55b2aaa2d2} "," Their actual"]]
["W1117",[3420,3420,320440,320447],[3407,3407,305994,305994]," actual","",[" decision. Their"," mathematical statements"]]
["W1118",[3420,3420,320472,320530],[3407,3407,306019,306025],"were read, as well as selected current connection records;","supply",["mathematical statements "," the review"]]
["W1119",[3420,3420,320535,320541],[3407,3407,306030,306039],"review","following",["records; the "," verdict is"]]
["W1120",[3420,3420,320542,320590],[3407,3407,306040,306047],"verdict is not substituted for those statements.","inputs.",["the review "," SF22--26 give"]]
["W1121",[3420,3420,320966,320978],[3407,3407,306423,306436],"exponent9/4;","exponent 9/4;",["parity criterion's "," the four-contact232"]]
["W1122",[3420,3420,320983,320998],[3407,3407,306441,306457],"four-contact232","four-contact 232",["exponent9/4; the "," application retains"]]
["W1123",[3420,3420,321046,321082],[3407,3407,306505,306553],"\\(L_{N}=\\text{floor}(9(2N-1)/4)+1\\).","\\(L_{N}=\\left\\lfloor 9(2N-1)/4\\right\\rfloor+1\\).",["and supplies "," SF45 gives"]]
["W1124",[3420,3420,321235,321241],[3407,3407,306706,306713],"raw224","raw 224",["the literal "," system.\n"]]
["W1125",[3422,3422,321257,321264],[3409,3409,306729,306738],"changes","arguments",["[C12: "," that are"]]
["W1126",[3422,3422,321265,321269],[3409,3409,306739,306748],"that","requiring",["[C12: changes "," are freshly"]]
["W1127",[3422,3422,321270,321273],[3409,3409,306749,306757],"are","separate",["changes that "," freshly checked,"]]
["W1128",[3422,3422,321274,321281],[3409,3409,306758,306764],"freshly","source",["that are "," checked, not"]]
["W1129",[3422,3422,321282,321324],[3409,3409,306765,306777],"checked, not carried by their conclusions]","comparisons]",["are freshly "," SF28's old"]]
["W1130",[3422,3422,321346,321357],[3409,3409,306799,306811],"exponent7/4","exponent 7/4",["old reflected "," is replaced"]]
["W1131",[3422,3422,321370,321375],[3409,3409,306824,306830],"in214","in 214",["is replaced "," by the"]]
["W1132",[3422,3422,321415,321425],[3409,3409,306870,306881],"giving7/6;","giving 7/6;",["height transfer "," its arithmetic"]]
["W1133",[3422,3422,321598,321609],[3409,3409,307054,307066],"supply214's","supply 214's",["cannot directly "," order-three factor"]]
["W1134",[3422,3422,321947,321947],[3409,3409,307404,307445],"","separate source applications required by ",["These are ","the substantive "]]
["W1135",[3422,3422,321951,321962],[3409,3409,307449,307452],"substantive","214",["are the "," new214 joins"]]
["W1136",[3422,3422,321963,322012],[3409,3409,307453,307462],"new214 joins requiring fresh eligible acceptance.","argument.",["the substantive "," The source"]]
["W1137",[3422,3422,322151,322161],[3409,3409,307601,307607],"previously","stated",["unchanged; their "," checked statement/domain/map"]]
["W1138",[3422,3422,322162,322169],[3409,3409,307608,307615],"checked","domains",["their previously "," statement/domain/map scopes"]]
["W1139",[3422,3422,322170,322190],[3409,3409,307616,307619],"statement/domain/map","and",["previously checked "," scopes can"]]
["W1140",[3422,3422,322191,322197],[3409,3409,307620,307624],"scopes","maps",["checked statement/domain/map "," can be"]]
["W1141",[3422,3422,322198,322201],[3409,3409,307625,307631],"can","remain",["statement/domain/map scopes "," be carried"]]
["W1142",[3422,3422,322202,322217],[3409,3409,307632,307640],"be carried only","required",["scopes can "," with the"]]
["W1143",[3424,3424,322258,322263],[3411,3411,307681,307686],"exact","scope",["[C13: "," disposition] Within"]]
["W1144",[3424,3424,322264,322276],[3411,3411,307687,307690],"disposition]","and",["[C13: exact "," Within the"]]
["W1145",[3424,3424,322277,322283],[3411,3411,307691,307734],"Within","limitations] The comparisons above identify",["exact disposition] "," the inspected"]]
["W1146",[3424,3424,322288,322297],[3411,3411,307739,307748],"inspected","analytic,",["Within the "," source-to214 analytic/RC/rank/prime/scalar/pole"]]
["W1147",[3424,3424,322298,322310],[3411,3411,307749,307769],"source-to214","restricted-converse,",["the inspected "," analytic/RC/rank/prime/scalar/pole joins,"]]
["W1148",[3424,3424,322311,322345],[3411,3411,307770,307775],"analytic/RC/rank/prime/scalar/pole","rank,",["inspected source-to214 "," joins, no"]]
["W1149",[3424,3424,322346,322352],[3411,3411,307776,307792],"joins,","prime-selection,",["source-to214 analytic/RC/rank/prime/scalar/pole "," no unmatched"]]
["W1150",[3424,3424,322353,322355],[3411,3411,307793,307799],"no","scalar",["analytic/RC/rank/prime/scalar/pole joins, "," unmatched mathematical"]]
["W1151",[3424,3424,322356,322365],[3411,3411,307800,307803],"unmatched","and",["joins, no "," mathematical required"]]
["W1152",[3424,3424,322366,322378],[3411,3411,307804,307808],"mathematical","pole",["no unmatched "," required input"]]
["W1153",[3424,3424,322379,322387],[3411,3411,307809,307815],"required","inputs",["unmatched mathematical "," input remains"]]
["W1154",[3424,3424,322388,322393],[3411,3411,307816,307820],"input","used",["mathematical required "," remains after"]]
["W1155",[3424,3424,322394,322407],[3411,3411,307821,307823],"remains after","by",["required input "," the frozen"]]
["W1156",[3424,3424,322412,322418],[3411,3411,307828,307831],"frozen","214",["after the "," supplement is"]]
["W1157",[3424,3424,322419,322429],[3411,3411,307832,307841],"supplement","argument.",["the frozen "," is included."]]
["W1158",[3424,3424,322430,322512],[3411,3411,307842,307847],"is included. This is a bounded author conclusion: it does not newly validate every","Their",["frozen supplement "," source theorem,"]]
["W1159",[3424,3424,322520,322528],[3411,3411,307855,307869],"theorem,","hypotheses and",["every source "," the separate"]]
["W1160",[3424,3424,322561,322567],[3411,3411,307902,307910],"chain,","argument",["full-family height "," contributor identities"]]
["W1161",[3424,3424,322568,322579],[3411,3411,307911,307917],"contributor","remain",["height chain, "," identities or"]]
["W1162",[3424,3424,322580,322590],[3411,3411,307918,307927],"identities","required.",["chain, contributor "," or final"]]
["W1163",[3424,3424,322591,322593],[3411,3411,307928,307929],"or","A",["contributor identities "," final release."]]
["W1164",[3424,3424,322594,322691],[3411,3411,307930,307936],"final release. It gives concrete current application matching sufficient for an eligible reviewer","change",["identities or "," to decide"]]
["W1165",[3424,3424,322695,322726],[3411,3411,307940,307941],"decide reuse at the established","a",["reviewer to "," source scopes."]]
["W1166",[3424,3424,322734,322962],[3411,3411,307949,307959],"scopes. The public final006 coverage decision expressly permits retained accepted source proofs while declining a fresh line-by-line reproof of all history; this author retains that distinction. Any source profile, theorem body,","statement,",["established source "," construction, consumer"]]
["W1167",[3424,3424,323010,323016],[3411,3411,308007,308015],"change","requires",["inherited dependency "," invalidates this"]]
["W1168",[3424,3424,323017,323224],[3411,3411,308016,308017],"invalidates this carry. Historical classification is prior justification found and read, with current incorporation already present in the identical supplier; the fresh214 boundary supplement remains pending","a",["dependency change "," new independent"]]
["W1169",[3424,3424,323229,323240],[3411,3411,308022,308040],"independent","source-to-consumer",["pending new "," acceptance. The"]]
["W1170",[3424,3424,323241,323252],[3411,3411,308041,308052],"acceptance.","comparison.",["new independent "," The defining"]]
["W1171",[3424,3424,323308,323320],[3411,3411,308108,308121],"numerical214","numerical 214",["no full "," witness tuple"]]
["W1172",[3426,3426,323845,323905],[3413,3413,308646,308654],"visible; no new acceptance is inferred from their inclusion.","visible.",["qualifications remain ","\n"]]
["W1173",[3440,3440,324465,324471],[3427,3427,309214,309221],"by210,","by 210,",["squarefree, divisible "," and \\(R\\ge"]]
["W1174",[3444,3444,324667,324679],[3431,3431,309417,309430],"dividing576;","dividing 576;",["has degree "," all geometric"]]
["W1175",[3445,3445,324761,324771],[3432,3432,309512,309523],"Outside210","Outside 210",["over \\(L\\). "," the quotient"]]
["W1176",[3450,3450,325112,325124],[3437,3437,309864,309877],"dividing210,","dividing 210,",["and primes "," not the"]]
["W1177",[3450,3450,325133,325145],[3437,3437,309886,309899],"cutoff76176.","cutoff 76176.",["not the ","\n"]]
["W1178",[3463,3463,325712,325715],[3450,3450,310466,310470],"at2","at 2",["dividing p-1; "," its conductor"]]
["W1179",[3463,3463,325730,325739],[3450,3450,310485,310495],"divides4.","divides 4.",["its conductor "," The combined"]]
["W1180",[3476,3476,326427,326438],[3463,3463,311183,311195],"divides576,","divides 576,",["field degree "," so the"]]
["W1181",[3478,3478,326555,326561],[3465,3465,311312,311319],"most2.","most 2.",["is at "," The unchanged"]]
["W1182",[3478,3478,326592,326601],[3465,3465,311350,311360],"at2,3,5,7","at 2,3,5,7",["crude exponents "," are below300."]]
["W1183",[3478,3478,326606,326615],[3465,3465,311365,311375],"below300.","below 300.",["at2,3,5,7 are ","\n"]]
["W1184",[3508,3508,328158,328170],[3495,3495,312918,312931],"dividing576,","dividing 576,",["[L:Q] "," \\(L\\) unramified"]]
["W1185",[3509,3509,328255,328263],[3496,3496,313016,313025],"from210.","from 210.",["\\(L\\) away "," All geometric"]]
["W1186",[3524,3524,329031,329036],[3511,3511,313793,313799],"to11,","to 11,",["degree prime "," since the"]]
["W1187",[3525,3525,329072,329076],[3512,3512,313835,313840],"at11","at 11",["maximal-order normalizer\n"," is \\(Q_{11}^{*}\\)"]]
["W1188",[3543,3543,329830,329839],[3530,3530,314594,314604],"at2,3,5,7","at 2,3,5,7",["Its valuations "," are respectively15,4,4,1."]]
["W1189",[3543,3543,329844,329865],[3530,3530,314609,314621],"respectively15,4,4,1.","respectively",["at2,3,5,7 are "," Full11-torsion makes"]]
["W1190",[3543,3543,329866,329880],[3530,3530,314622,314647],"Full11-torsion","15,4,4,1. Full 11-torsion",["are respectively15,4,4,1. "," makes\n\\(A_{a}\\)"]]
["W1191",[3544,3544,329961,329968],[3531,3531,314728,314736],"from11;","from 11;",["characteristic different ","\nthe preceding"]]
["W1192",[3545,3545,330025,330036],[3532,3532,314793,314805],"Only2,3,5,7","Only 2,3,5,7",["good reduction. ","\n"]]
["W1193",[3552,3552,330490,330499],[3539,3539,315259,315267],"dividing4","dividing",["has conductor "," at2, and"]]
["W1194",[3552,3552,330500,330504],[3539,3539,315268,315275],"at2,","4 at 2,",["conductor dividing4 "," and has"]]
["W1195",[3571,3571,331549,331553],[3558,3558,316320,316325],"At2,","At 2,",["ramification index. ","\nthe inertia"]]
["W1196",[3572,3572,331598,331604],[3559,3559,316370,316377],"most2,","most 2,",["order at "," and the"]]
["W1197",[3573,3573,331662,331668],[3560,3560,316435,316442],"most2.","most 2.",["degree at "," Unramified degrees"]]
["W1198",[3583,3583,332080,332086],[3570,3570,316854,316861],"by(4),","by (4),",["not bounded "," and will"]]
["W1199",[3632,3632,334443,334446],[3619,3619,319218,319222],"or0","or 0",["upper break, "," when there"]]
["W1200",[3634,3634,334557,334562],[3621,3621,319333,319339],"in(6)","in (6)",["integrand "," is at"]]
["W1201",[3634,3634,334569,334578],[3621,3621,319346,319356],"least1/2,","least 1/2,",["is at "," except at"]]
["W1202",[3642,3642,334837,334843],[3629,3629,319615,319622],"in(7).","in (7).",["extra term ","\n"]]
["W1203",[3678,3678,336506,336517],[3665,3665,321285,321297],"dividing576","dividing 576",["\\(p>7\\), [L:Q] "," implies that"]]
["W1204",[3681,3681,336783,336789],[3668,3668,321563,321570],"most2;","most 2;",["order at ","\n"]]
["W1205",[3683,3683,336899,336906],[3670,3670,321680,321688],"prime11","prime 11",["\\(T\\). The "," argument does"]]
["W1206",[3683,3683,336935,336949],[3670,3670,321717,321732],"full11-torsion","full 11-torsion",["apply the ","\ncriterion in"]]
["W1207",[3684,3684,336971,336988],[3671,3671,321754,321772],"characteristic11.","characteristic 11.",["in residue ","\n"]]
["W1208",[3686,3686,337001,337006],[3673,3673,321785,321791],"in(8)","in (8)",["The object "," is the"]]
["W1209",[3704,3704,338167,338172],[3691,3691,322952,322958],"in(8)","in (8)",["four primes "," divide \\(R\\)."]]
["W1210",[3704,3704,338212,338221],[3691,3691,322998,323008],"exponent2","exponent 2",["their baseline ","\n"]]
["W1211",[3713,3713,338428,338435],[3700,3700,323215,323224],"packet.","argument.",["in this ","\n"]]
["W1212",[3720,3720,338714,338860],[3707,3707,323503,323503]," Author: model task \\nolinkurl{/root/d214_foundation_trace}, 2026-11-10. This is a proposed source/application bridge, not independent acceptance.","",["\\begin{quote}\\footnotesize"," All file"]]
["W1213",[3722,3722,339380,339389],[3709,3709,324023,324033],"Version15","Version 15",["the frozen "," source, lines31238--31643,"]]
["W1214",[3722,3722,339398,339416],[3709,3709,324042,324061],"lines31238--31643,","lines 31238--31643,",["Version15 source, "," consumed explicitly"]]
["W1215",[3722,3722,339437,339452],[3709,3709,324082,324084],"at32449--32468.","at",["consumed explicitly "," \\(I\\) read"]]
["W1216",[3722,3722,339453,339458],[3709,3709,324085,324098],"\\(I\\)","32449--32468.",["explicitly at32449--32468. "," read the"]]
["W1217",[3722,3722,339459,339463],[3709,3709,324099,324120],"read","This application uses",["at32449--32468. \\(I\\) "," the sum-pole,"]]
["W1218",[3722,3722,339538,339591],[3709,3709,324195,324205],"arguments, rather than inferring this conclusion from","arguments;",["and canonical-height "," the product"]]
["W1219",[3722,3722,339604,339612],[3709,3709,324218,324264],"version.","version alone does not supply this conclusion.",["the product ","\n"]]
["W1220",[3724,3724,339641,339668],[3711,3711,324293,324295],"was retrieved on2026-11-10:","is",["published source "," \\(J\\). Von"]]
["W1221",[3724,3724,339734,339742],[3711,3711,324361,324371],"problème","probl\\`eme",["pour le "," de Mordell--Lang"]]
["W1222",[3724,3724,339769,339776],[3711,3711,324398,324409],"variété","vari\\'et\\'e",["dans une "," abélienne}, JTNB29(2017),307--320,"]]
["W1223",[3724,3724,339777,339788],[3711,3711,324410,324423],"abélienne},","ab\\'elienne},",["une variété "," JTNB29(2017),307--320, DOI10.5802/jtnb.981,"]]
["W1224",[3724,3724,339789,339811],[3711,3711,324424,324428],"JTNB29(2017),307--320,","JTNB",["variété abélienne}, "," DOI10.5802/jtnb.981, publisher-distributed"]]
["W1225",[3724,3724,339812,339832],[3711,3711,324429,324469],"DOI10.5802/jtnb.981,","29(2017),307--320, DOI 10.5802/jtnb.981,",["abélienne}, JTNB29(2017),307--320, "," publisher-distributed PDF"]]
["W1226",[3724,3724,339918,339928],[3711,3711,324555,324566],"Theorem1.1","Theorem 1.1",["at \\url{https://www.numdam.org/item/10.5802/jtnb.981.pdf}. "," and preceding"]]
["W1227",[3724,3724,339956,339967],[3711,3711,324594,324606],"printed308,","printed 308,",["preceding definitions, "," require a"]]
["W1228",[3727,3727,341014,341028],[3714,3714,325653,325668],"condition(1.1)","condition (1.1)",["source's embedding "," can be"]]
["W1229",[3730,3730,342629,342633],[3717,3717,327269,327274],"is7,","is 7,",["its norm "," and \\(dd'=7\\)"]]
["W1230",[3731,3731,343430,343437],[3718,3718,328071,328079],"factor2","factor 2",["2\\), the "," is absorbed"]]
["W1231",[3731,3731,343545,343551],[3718,3718,328187,328194],"raw224","raw 224",["the literal "," recovery and"]]
["W1232",[3732,3732,343987,343991],[3719,3719,328630,328635],"log2","log 2",["the preceding "," loss give"]]
["W1233",[3734,3734,345470,345474],[3721,3721,330114,330119],"at2,","at 2,",["formal parameter "," lines31544--31568; full"]]
["W1234",[3735,3735,345643,345682],[3722,3722,330288,330328],"\\nolinkurl{existence/PROOF.md:9,62–78.}","\\nolinkurl{existence/PROOF.md:9,62--78}.",["occur in "," The nonzero"]]
["W1235",[3735,3735,345904,345919],[3722,3722,330550,330558],"exponent7/(6k),","exponent",["the displayed "," \\(\\text{hence}14/9<2\\) for"]]
["W1236",[3735,3735,345920,345942],[3722,3722,330559,330583],"\\(\\text{hence}14/9<2\\)","7/(6k), hence \\(14/9<2\\)",["displayed exponent7/(6k), "," for the"]]
["W1237",[3738,3738,346165,346175],[3725,3725,330806,330809],"Historical","The",[""," disposition: prior"]]
["W1238",[3738,3738,346176,346424],[3725,3725,330810,330819],"disposition: prior justification found, including the independent effective-aggregate assessment in \\nolinkurl{research/v14-small-prime-height/exploration/effective-aggregate/ASSESSMENT.md.} That assessment already distinguishes a valid qualitative","aggregate",["Historical "," bound from"]]
["W1239",[3738,3738,346431,346435],[3725,3725,330826,330828],"from","is",["qualitative bound "," the unprovided"]]
["W1240",[3738,3738,346436,346439],[3725,3725,330829,330841],"the","qualitative:",["bound from "," unprovided effective"]]
["W1241",[3738,3738,346440,346450],[3725,3725,330842,330844],"unprovided","no",["from the "," effective additive"]]
["W1242",[3738,3738,346470,346479],[3725,3725,330864,330872],"constant;","constant",["effective additive "," it is"]]
["W1243",[3738,3738,346480,346482],[3725,3725,330873,330900],"it","has been supplied, and none",["additive constant; "," is not"]]
["W1244",[3738,3738,346486,346489],[3725,3725,330904,330910],"not","needed",["it is "," an objection"]]
["W1245",[3738,3738,346490,346505],[3725,3725,330911,330914],"an objection to","for",["is not "," the current"]]
["W1246",[3738,3738,346509,346517],[3725,3725,330918,330918]," current","",[" to the"," ineffective theorem."]]
["W1247",[3738,3738,346539,346549],[3725,3725,330940,330943],"Manuscript","The",["ineffective theorem. "," disposition: the"]]
["W1248",[3738,3738,346550,346562],[3725,3725,330944,330990],"disposition:","sum, graph and quarter-trace argument supplies",["theorem. Manuscript "," the sum/graph/quarter-trace"]]
["W1249",[3738,3738,346567,346590],[3725,3725,330995,331001],"sum/graph/quarter-trace","stated",["disposition: the "," argument is"]]
["W1250",[3738,3738,346591,346599],[3725,3725,331002,331011],"argument","aggregate",["the sum/graph/quarter-trace "," is incorporated"]]
["W1251",[3738,3738,346600,346602],[3725,3725,331012,331018],"is","input.",["sum/graph/quarter-trace argument "," incorporated in"]]
["W1252",[3738,3738,346603,346648],[3725,3725,331019,331023],"incorporated in the frozen Version15 supplier","Rank",["argument is "," and referenced"]]
["W1253",[3738,3738,346653,347042],[3725,3725,331028,331036],"referenced by the 214 proof. The explicit embedding choice and the \\(\\text{canonical}-\\text{height}-\\text{ to } -B^{2}\\) derivation above are supplemental author explanations pending non-author comparison. Current review: the old component review retains the aggregate interface conditionally; this new final-source bridge has no independent acceptance yet. It does not close rank/descent,","descent,",["supplier and "," modularity, prime"]]
["W1254",[3738,3738,347070,347072],[3725,3725,331064,331067],"or","and",["prime patterns "," pole realization."]]
["W1255",[3738,3738,347078,347090],[3725,3725,331073,331115],"realization.","realization remain separate prerequisites.",["or pole ","\n"]]
["W1256",[4324,4324,371453,371476],[4311,4311,355478,355490],"author-frozen successor","construction",["This "," removes Q5's"]]
["W1257",[4324,4324,371519,371527],[4311,4311,355533,355536],"accepted","raw",["components from "," raw224, retaining224"]]
["W1258",[4324,4324,371528,371535],[4311,4311,355537,355541],"raw224,","224,",["from accepted "," retaining224 variables"]]
["W1259",[4324,4324,371536,371548],[4311,4311,355542,355555],"retaining224","retaining 224",["accepted raw224, "," variables and198"]]
["W1260",[4324,4324,371559,371565],[4311,4311,355566,355573],"and198","and 198",["retaining224 variables "," residuals. Coordinates"]]
["W1261",[4324,4324,371647,371822],[4311,4311,355655,355732],"\\nolinkurl{a907e6dab18305d6b0f9443578c123d854eda6643d6e6c8b83db5c8dcaef0487} and its independent acceptance is7f79535dd88fcec653370ce495eaef4d4080e8791bdb40bc7cf205ac3710639f.","\\nolinkurl{a907e6dab18305d6b0f9443578c123d854eda6643d6e6c8b83db5c8dcaef0487}.",["manifest is "," The normative"]]
["W1262",[4326,4326,371989,372005],[4313,4313,355899,355920],"\\(Q_{2}=M*w+L\\).","\\(Q_{2}=M\\cdot w+L\\).",["Write "," Its coefficient"]]
["W1263",[4327,4327,372025,372265],[4314,4314,355940,356195],"\\(M=B+(23335979380411305/9142573010269636-r*256685364214285/4571286505134818)f+(44649296511110307/111996519375803041-r*2886885451827729/447986077503212164)S+3317607896141091533/7167777240051394624+r*677690583653850567/1791944310012848656\\).","\\(M=B+(23335979380411305/9142573010269636-r\\cdot 256685364214285/4571286505134818)f+(44649296511110307/111996519375803041-r\\cdot 2886885451827729/447986077503212164)S+3317607896141091533/7167777240051394624+r\\cdot 677690583653850567/1791944310012848656\\).",["coefficient is\n","\n"]]
["W1264",[4329,4329,372284,372299],[4316,4316,356214,356230],"are149-integral","are 149-integral",["The coefficients "," and the"]]
["W1265",[4331,4331,372613,372622],[4318,4318,356544,356560],"Q0,Q1,Q3,","\\(Q_0,Q_1,Q_3\\),",["use only "," so these"]]
["W1266",[4331,4331,372687,372692],[4318,4318,356625,356636],"orQ5.","or \\(Q_5\\).",["without \\(Q_{2}\\) "," The same"]]
["W1267",[4331,4331,372741,372754],[4318,4318,356685,356706],"onlyQ0,Q1,Q3.","only \\(Q_0,Q_1,Q_3\\).",["also uses "," Thus \\(f\\)"]]
["W1268",[4331,4331,372912,372921],[4318,4318,356864,356874],"forced149","forced 149",["the inherited "," bound on"]]
["W1269",[4331,4331,372957,372967],[4318,4318,356910,356921],"referencew","reference w",["independently of "," and its"]]
["W1270",[4331,4331,372976,372984],[4318,4318,356930,356939],"outputW.","output W.",["and its "," Therefore \\(\\operatorname{ord}(f)=m>0\\),"]]
["W1271",[4331,4331,373136,373145],[4318,4318,357091,357105],"*S+\\alpha","\\cdot S+\\alpha",["and \\(D=\\beta "," \\) is"]]
["W1272",[4333,4333,373280,373288],[4320,4320,357240,357249],"order2m,","order 2m,",["\\(B\\) has "," the \\(f\\)"]]
["W1273",[4333,4333,373308,373315],[4320,4320,357269,357277],"orderm,","order m,",["term has "," and the"]]
["W1274",[4333,4333,373406,373425],[4320,4320,357368,357388],"\\(w*=g^{4}/f^{2}\\).","\\(w_*=g^{4}/f^{2}\\).",["expected value "," The parent's"]]
["W1275",[4333,4333,373482,373506],[4320,4320,357445,357470],"\\(Q_{2}(f,S,B,w*,T)=0\\);","\\(Q_{2}(f,S,B,w_*,T)=0\\);",["\\(Q_{2}\\) gives "," it uses"]]
["W1276",[4333,4333,373564,373574],[4320,4320,357528,357543],"\\(D*T=N\\),","\\(D\\cdot T=N\\),",["F/E, and "," with f,A,D"]]
["W1277",[4333,4333,373658,373671],[4320,4320,357627,357641],"coefficientM,","coefficient M,",["with nonzero "," the retained"]]
["W1278",[4333,4333,373704,373713],[4320,4320,357674,357684],"\\(w=w*\\).","\\(w=w_*\\).",["\\(Q_{2}=0\\) forces "," Retained \\(Q_{4}\\)"]]
["W1279",[4337,4337,374236,374244],[4324,4324,358207,358216],"gives224","gives 224",["full expansion "," variables,198 residuals,degree4,content1,3014"]]
["W1280",[4337,4337,374259,374290],[4324,4324,358231,358264],"residuals,degree4,content1,3014","residuals,degree 4,content 1,3014",["gives224 variables,198 "," coordinate monomials"]]
["W1281",[4337,4337,374312,374319],[4324,4324,358286,358294],"and3015","and 3015",["coordinate monomials "," parameter terms."]]
["W1282",[4337,4337,374462,374545],[4324,4324,358437,358437]," No manuscript adoption or independent acceptance is claimed by this author packet.","",[" coefficient threshold.","\n"]]
["W1283",[4339,4339,374909,374944],[4326,4326,358801,358809],"theorem and from review acceptance.","theorem.",["the arithmetic ","\n"]]
["W1284",[4381,4381,380615,380627],[4368,4368,364480,364493],"threshold53.","threshold 53.",["and coefficient-only ","\n"]]
["W1285",[4384,4384,380993,381036],[4371,4371,364859,364896],"inspection catalogue}\\label{q214:catalogue}","qualifications}\\label{q214:catalogue}",["editions and ","\n"]]
["W1286",[4386,4386,381076,381083],[4373,4373,364936,364946],"retains","identifies",["This catalogue "," the complete"]]
["W1287",[4386,4386,381084,381087],[4373,4373,364947,364954],"the","primary",["catalogue retains "," complete primary-source"]]
["W1288",[4386,4386,381088,381390],[4373,4373,364955,364962],"complete primary-source metadata accompanying the author packet.  An inspection statement describes its original named author and date.  It is not an assertion that the typesetter repeated that inspection, nor an independent acceptance of the present manuscript.  External books and PDFs are identified","sources",["retains the "," by their"]]
["W1289",[4386,4386,381394,381399],[4373,4373,364966,364974],"their","edition,",["identified by "," editions, locators,"]]
["W1290",[4386,4386,381400,381409],[4373,4373,364975,364983],"editions,","locator,",["by their "," locators, URLs"]]
["W1291",[4386,4386,381410,381424],[4373,4373,364984,364987],"locators, URLs","URL",["their editions, "," and byte"]]
["W1292",[4386,4386,381434,381441],[4373,4373,364997,365002],"hashes;","hash.",["and byte "," their complete"]]
["W1293",[4386,4386,381442,381447],[4373,4373,365003,365008],"their","Their",["byte hashes; "," complete contents"]]
["W1294",[4386,4386,381474,381485],[4373,4373,365035,365045],"republished","reproduced",["are not "," here.\n"]]
["W1295",[4386,4386,381491,381491],[4373,4373,365051,365132],""," Source-access and edition-comparison limitations remain stated with the entries.",[" republished here.","\n"]]
["W1296",[4388,4389,381511,381621],[4375,4376,365152,365154],"\\noindent\\textbf{format}: height-sources-v1\\par\n\\noindent\\textbf{author}: /root/sol61\\_height\\_foundation\\par\n","\n\n",["",""]]
["W1297",[4400,4400,382432,382453],[4387,4387,365965,365989],"Theorem1.9(1),pp7--8;","Theorem 1.9(1),pp.~7--8;",["\\noindent\\textbf{locator}: "," original stable"]]
["W1298",[4400,4401,382487,382553],[4387,4388,366023,366025],"\n\\noindent\\textbf{omitted\\_local\\_path}: GR2023-published.pdf\\par\n","\n\n",[" stable normalization\\par",""]]
["W1299",[4406,4406,382843,382868],[4393,4393,366315,366347],"\\noindent\\textbf{status}:","\\noindent\\textbf{qualification}:",[""," authorJune2021PD\\allowbreak{}F checked;"]]
["W1300",[4406,4406,382869,382899],[4393,4393,366348,366352],"authorJune2021PD\\allowbreak{}F","June",["\\noindent\\textbf{status}: "," checked; final2022body"]]
["W1301",[4406,4406,382900,382908],[4393,4393,366353,366357],"checked;","2021",["\\noindent\\textbf{status}: authorJune2021PD\\allowbreak{}F "," final2022body unavailable"]]
["W1302",[4406,4406,382909,382922],[4393,4393,366358,366390],"final2022body","author PDF used; final 2022 body",["authorJune2021PD\\allowbreak{}F checked; "," unavailable via"]]
["W1303",[4406,4406,382935,382938],[4393,4393,366403,366414],"via","through the",["final2022body unavailable "," subscription redirect\\par"]]
["W1304",[4406,4406,382952,382964],[4393,4393,366428,366458],"redirect\\par","redirect and not compared.\\par",["via subscription ","\n\\noindent\\textbf{locator}: Corollary1.2,stable"]]
["W1305",[4407,4407,382992,383011],[4394,4394,366486,366495],"Corollary1.2,stable","Corollary",["redirect\\par\n\\noindent\\textbf{locator}: "," remark,Proposition2.1\\par\n\\noindent\\textbf{omitted\\_local\\_path}:"]]
["W1306",[4407,4408,383012,383077],[4394,4394,366496,366506],"remark,Proposition2.1\\par\n\\noindent\\textbf{omitted\\_local\\_path}:","1.2,stable",["\\noindent\\textbf{locator}: Corollary1.2,stable "," Remond2021-author.pdf\\par\n"]]
["W1307",[4408,4408,383078,383104],[4394,4395,366507,366535],"Remond2021-author.pdf\\par\n","remark,Proposition 2.1\\par\n\n",["remark,Proposition2.1\\par\n\\noindent\\textbf{omitted\\_local\\_path}: ",""]]
["W1308",[4414,4414,383494,383513],[4401,4401,366925,366947],"Theorem1,pp526--527","Theorem 1,pp.~526--527",["\\noindent\\textbf{locator}: "," including Fricke"]]
["W1309",[4414,4415,383544,383615],[4401,4402,366978,366980],"\n\\noindent\\textbf{omitted\\_local\\_path}: Shimura1973-published.pdf\\par\n","\n\n",[" Fricke condition\\par",""]]
["W1310",[4422,4422,384033,384093],[4409,4409,367398,367398],"\\noindent\\textbf{omitted\\_local\\_path}: Ribet-author.pdf\\par","",["","\n"]]
["W1311",[4445,4445,384722,384736],[4432,4432,368027,368045],"Rémond2022body","R\\'emond 2022 body",["$\\bullet$ Final "," not compared\\par"]]
["W1312",[4447,4447,384905,384980],[4434,4434,368214,368214],"\\noindent $\\bullet$ No independent inventory-coverage decision supplied\\par","",["","\n\\noindent\\textbf{copyright}: Local"]]
["W1313",[4448,4448,385010,385027],[4435,4435,368244,368255],"Local third-party","Third-party",["supplied\\par\n\\noindent\\textbf{copyright}: "," PDFs are"]]
["W1314",[4448,4448,385037,385043],[4435,4435,368265,368275],"source","identified",["PDFs are "," evidence. Do"]]
["W1315",[4448,4448,385044,385053],[4435,4435,368276,368278],"evidence.","by",["are source "," Do not"]]
["W1316",[4448,4448,385054,385056],[4435,4435,368279,368308],"Do","URL, hash and locator and are",["source evidence. "," not infer"]]
["W1317",[4448,4448,385061,385066],[4435,4435,368313,368323],"infer","reproduced",["Do not "," redistribution permission;"]]
["W1318",[4448,4448,385067,385153],[4435,4435,368324,368333],"redistribution permission; release may retain URL/hash/locator without PDF copies.\\par","here.\\par",["not infer ","\n"]]
["W1319",[4456,4456,385555,385567],[4443,4443,368735,368742],"edition1986,","edition",["\\noindent\\textbf{locator}: Second "," Theorem1a-b, printed204/PDF212;"]]
["W1320",[4456,4456,385568,385580],[4443,4443,368743,368748],"Theorem1a-b,","1986,",["Second edition1986, "," printed204/PDF212; title"]]
["W1321",[4456,4456,385581,385599],[4443,4443,368749,368756],"printed204/PDF212;","Theorem",["edition1986, Theorem1a-b, "," title pages"]]
["W1322",[4456,4456,385600,385605],[4443,4443,368757,368762],"title","1a-b,",["Theorem1a-b, printed204/PDF212; "," pages checked\\par"]]
["W1323",[4456,4456,385606,385611],[4443,4443,368763,368770],"pages","printed",["printed204/PDF212; title "," checked\\par\n"]]
["W1324",[4456,4456,385612,385623],[4443,4443,368771,368786],"checked\\par","204/PDF 212\\par",["title pages ","\n"]]
["W1325",[4458,4460,385669,385889],[4445,4447,368832,368835],"\\noindent\\textbf{inspectedBy}: /root\\par\n\\noindent\\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\\par\n\\noindent\\textbf{repositoryCopy}: false\\par\n","\n\n\n",["",""]]
["W1326",[4466,4466,386246,386260],[4453,4453,369192,369201],"Published1986,","Published",["\\noindent\\textbf{locator}: "," Proposition12.1, printed122/PDF20\\par"]]
["W1327",[4466,4466,386261,386277],[4453,4453,369202,369207],"Proposition12.1,","1986,",["\\noindent\\textbf{locator}: Published1986, "," printed122/PDF20\\par\n"]]
["W1328",[4466,4466,386278,386298],[4453,4453,369208,369248],"printed122/PDF20\\par","Proposition 12.1, printed 122/PDF 20\\par",["Published1986, Proposition12.1, ","\n"]]
["W1329",[4468,4470,386344,386564],[4455,4457,369294,369297],"\\noindent\\textbf{inspectedBy}: /root\\par\n\\noindent\\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\\par\n\\noindent\\textbf{repositoryCopy}: false\\par\n","\n\n\n",["",""]]
["W1330",[4476,4476,386972,386989],[4463,4463,369705,369712],"Annalen212(1975),","Annalen",["\\noindent\\textbf{locator}: Mathematische "," printed294\\par\n"]]
["W1331",[4476,4476,386990,387004],[4463,4463,369713,369739],"printed294\\par","212(1975), printed 294\\par",["Mathematische Annalen212(1975), ","\n"]]
["W1332",[4478,4480,387050,387270],[4465,4467,369785,369788],"\\noindent\\textbf{inspectedBy}: /root\\par\n\\noindent\\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\\par\n\\noindent\\textbf{repositoryCopy}: false\\par\n","\n\n\n",["",""]]
["W1333",[4486,4486,387678,387695],[4473,4473,370196,370203],"Annalen212(1975),","Annalen",["\\noindent\\textbf{locator}: Mathematische "," printed295\\par\n"]]
["W1334",[4486,4486,387696,387710],[4473,4473,370204,370230],"printed295\\par","212(1975), printed 295\\par",["Mathematische Annalen212(1975), ","\n"]]
["W1335",[4488,4490,387756,387976],[4475,4477,370276,370279],"\\noindent\\textbf{inspectedBy}: /root\\par\n\\noindent\\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\\par\n\\noindent\\textbf{repositoryCopy}: false\\par\n","\n\n\n",["",""]]
["W1336",[4496,4496,388384,388401],[4483,4483,370687,370694],"Annalen212(1975),","Annalen",["\\noindent\\textbf{locator}: Mathematische "," printed296\\par\n"]]
["W1337",[4496,4496,388402,388416],[4483,4483,370695,370721],"printed296\\par","212(1975), printed 296\\par",["Mathematische Annalen212(1975), ","\n"]]
["W1338",[4498,4500,388462,388682],[4485,4487,370767,370770],"\\noindent\\textbf{inspectedBy}: /root\\par\n\\noindent\\textbf{status}: published page image directly read; current application authored separately, awaiting independent review\\par\n\\noindent\\textbf{repositoryCopy}: false\\par\n","\n\n\n",["",""]]
["W1339",[4506,4506,389037,389050],[4493,4493,371125,371135],"Definition2.1","Definition",["\\noindent\\textbf{locator}: "," and\\S{}2.3 pp351--352;"]]
["W1340",[4506,4506,389051,389061],[4493,4493,371136,371139],"and\\S{}2.3","2.1",["\\noindent\\textbf{locator}: Definition2.1 "," pp351--352; Corollary8.4"]]
["W1341",[4506,4506,389062,389073],[4493,4493,371140,371143],"pp351--352;","and",["Definition2.1 and\\S{}2.3 "," Corollary8.4 p400;"]]
["W1342",[4506,4506,389074,389086],[4493,4493,371144,371151],"Corollary8.4","\\S{}2.3",["and\\S{}2.3 pp351--352; "," p400; PDFpages9--10,58\\par"]]
["W1343",[4506,4506,389087,389092],[4493,4493,371152,371165],"p400;","pp.~351--352;",["pp351--352; Corollary8.4 "," PDFpages9--10,58\\par\n"]]
["W1344",[4506,4506,389093,389113],[4493,4493,371166,371210],"PDFpages9--10,58\\par","Corollary 8.4 p.~400; PDF pages~9--10,58\\par",["Corollary8.4 p400; ","\n"]]
["W1345",[4508,4510,389159,389386],[4495,4497,371256,371259],"\\noindent\\textbf{inspectedBy}: /root\\par\n\\noindent\\textbf{status}: Published definition,corollary proof and pageimages read; source/application bridge awaiting independent review\\par\n\\noindent\\textbf{repositoryCopy}: false\\par\n","\n\n\n",["","\\noindent\\textbf{qualification}: URLs "]]
["W1346",[4511,4511,389522,389543],[4498,4498,371395,371395],"local review copies, ","",["images are ","not redistributed "]]
["W1347",[4511,4511,389547,389560],[4498,4498,371399,371409],"redistributed","reproduced",["copies, not "," in the"]]
["W1348",[4511,4511,389561,389575],[4498,4498,371410,371415],"in the packet.","here.",["not redistributed "," Source/application discussion"]]
["W1349",[4512,4512,389723,389736],[4499,4499,371563,371578],"final2022body","final 2022 body",["to subscription; "," not compared."]]
["W1350",[4512,4512,389760,389774],[4499,4499,371602,371618],"authorJune2021","author June 2021",["compared. Existing "," version remains"]]
["W1351",[4514,4514,389826,389865],[4501,4501,371670,371670],"\\noindent\\textbf{role}: AUTHOR only\\par","",["","\n"]]
["W1352",[4521,4521,390198,390218],[4508,4508,372003,372014],"definitions611--612;","definitions",["\\noindent\\textbf{locator}: "," statement624\\par\n"]]
["W1353",[4521,4521,390219,390235],[4508,4508,372015,372042],"statement624\\par","611--612; statement 624\\par",["\\noindent\\textbf{locator}: definitions611--612; ","\n"]]
["W1354",[4523,4523,390360,390367],[4510,4510,372167,372170],"ICM2022","ICM",["\\noindent\\textbf{publication}: EMS "," vol2 (2023),610--651\\par"]]
["W1355",[4523,4523,390368,390372],[4510,4510,372171,372182],"vol2","2022 vol. 2",["EMS ICM2022 "," (2023),610--651\\par\n\\noindent\\textbf{actual\\_inspection}:"]]
["W1356",[4523,4524,390392,390531],[4510,4511,372202,372204],"\n\\noindent\\textbf{actual\\_inspection}: actual statement text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","\n\n",[" vol2 (2023),610--651\\par",""]]
["W1357",[4526,4526,390583,390693],[4513,4513,372256,372256],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1358",[4531,4531,390958,391001],[4517,4517,372521,372555],"\\S{}\\S{}1.4,2.1,2.4,3.4.2,4.1/fullTheorem4;","\\S{}\\S{}1.4,2.1,2.4,3.4.2,4.1/full",["\\noindent\\textbf{locator}: "," printed36,37,41,42\\par\n"]]
["W1359",[4531,4531,391002,391024],[4517,4517,372556,372590],"printed36,37,41,42\\par","Theorem 4; printed 36,37,41,42\\par",["\\noindent\\textbf{locator}: \\S{}\\S{}1.4,2.1,2.4,3.4.2,4.1/fullTheorem4; ","\n"]]
["W1360",[4533,4534,391145,391218],[4519,4519,372711,372723],"Astérisque147--148(1987),33--47\\par\n\\noindent\\textbf{actual\\_inspection}:","Ast\\'erisque",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1361",[4534,4534,391219,391319],[4519,4520,372724,372751],"actual statement text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","147--148(1987),33--47\\par\n\n",["Astérisque147--148(1987),33--47\\par\n\\noindent\\textbf{actual\\_inspection}: ",""]]
["W1362",[4536,4536,391371,391481],[4522,4522,372803,372803],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1363",[4541,4541,391745,391758],[4526,4526,373067,373071],"Cor1.8pp5--6;","Cor.",["\\noindent\\textbf{locator}: "," Thms9.1,9.3pp74--75\\par\n"]]
["W1364",[4541,4541,391759,391782],[4526,4526,373072,373117],"Thms9.1,9.3pp74--75\\par","1.8, pp.~5--6; Thms. 9.1, 9.3, pp.~74--75\\par",["\\noindent\\textbf{locator}: Cor1.8pp5--6; ","\n"]]
["W1365",[4543,4544,391981,392040],[4528,4528,373316,373321],"Math.Pi1(2013),e1\\par\n\\noindent\\textbf{actual\\_inspection}:","Math.",["\\noindent\\textbf{publication}: Forum "," actual statement"]]
["W1366",[4544,4544,392041,392047],[4528,4528,373322,373324],"actual","Pi",["Math.Pi1(2013),e1\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1367",[4544,4544,392048,392141],[4528,4529,373325,373341],"statement text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","1(2013),e1\\par\n\n",["\\noindent\\textbf{actual\\_inspection}: actual ",""]]
["W1368",[4546,4546,392193,392303],[4531,4531,373393,373393],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1369",[4551,4551,392567,392578],[4535,4535,373657,373669],"whole4-page","whole 4-page",["\\noindent\\textbf{locator}: "," correction, especiallyp2\\par"]]
["W1370",[4551,4551,392591,392607],[4535,4535,373682,373701],"especiallyp2\\par","especially p.~2\\par",["whole4-page correction, ","\n"]]
["W1371",[4553,4554,392806,392865],[4537,4537,373900,373905],"Math.Pi4(2016),e6\\par\n\\noindent\\textbf{actual\\_inspection}:","Math.",["\\noindent\\textbf{publication}: Forum "," actual statement"]]
["W1372",[4554,4554,392866,392872],[4537,4537,373906,373908],"actual","Pi",["Math.Pi4(2016),e6\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1373",[4554,4554,392873,392966],[4537,4538,373909,373925],"statement text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","4(2016),e6\\par\n\n",["\\noindent\\textbf{actual\\_inspection}: actual ",""]]
["W1374",[4556,4556,393018,393128],[4540,4540,373977,373977],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1375",[4561,4561,393412,393430],[4544,4544,374261,374284],"Theorem3.8p142\\par","Theorem 3.8, p.~142\\par",["\\noindent\\textbf{locator}: \\S{}\\S{}3.4--3.8; ","\n"]]
["W1376",[4563,4564,393548,393618],[4546,4546,374402,374414],"Astérisque223(1994),113--184\\par\n\\noindent\\textbf{actual\\_inspection}:","Ast\\'erisque",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1377",[4564,4564,393619,393719],[4546,4547,374415,374439],"actual statement text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","223(1994),113--184\\par\n\n",["Astérisque223(1994),113--184\\par\n\\noindent\\textbf{actual\\_inspection}: ",""]]
["W1378",[4566,4566,393775,393885],[4549,4549,374495,374495],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1379",[4571,4571,394188,394223],[4553,4553,374798,374835],"pp155,161--162,181,187--188,240\\par","pp.~155,161--162,181,187--188,240\\par",["\\noindent\\textbf{locator}: \\S{}\\S{}5.4,6.3,8.3,9.2,9.4,14.10.2--3; ","\n"]]
["W1380",[4573,4574,394341,394411],[4555,4555,374953,374965],"Astérisque295(2004),117--290\\par\n\\noindent\\textbf{actual\\_inspection}:","Ast\\'erisque",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1381",[4574,4574,394412,394512],[4555,4556,374966,374990],"actual statement text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","295(2004),117--290\\par\n\n",["Astérisque295(2004),117--290\\par\n\\noindent\\textbf{actual\\_inspection}: ",""]]
["W1382",[4576,4576,394568,394678],[4558,4558,375046,375046],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1383",[4581,4581,394961,395011],[4562,4562,375329,375362],"\\S{}\\S{}1.6--1.9,3.1--3.2,Theorem4.1,8.2,8.5--8.6;","\\S{}\\S{}1.6--1.9,3.1--3.2,Theorem",["\\noindent\\textbf{locator}: "," pp509--510,513--514,525--526\\par\n"]]
["W1384",[4581,4581,395012,395044],[4562,4562,375363,375415],"pp509--510,513--514,525--526\\par","4.1,8.2,8.5--8.6; pp.~509--510,513--514,525--526\\par",["\\noindent\\textbf{locator}: \\S{}\\S{}1.6--1.9,3.1--3.2,Theorem4.1,8.2,8.5--8.6; ","\n"]]
["W1385",[4583,4584,395108,395180],[4564,4564,375479,375483],"Ann.Sci.ENS(4)7(1974),507--530\\par\n\\noindent\\textbf{actual\\_inspection}:","Ann.",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1386",[4584,4584,395181,395187],[4564,4564,375484,375488],"actual","Sci.",["Ann.Sci.ENS(4)7(1974),507--530\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1387",[4584,4584,395188,395197],[4564,4564,375489,375492],"statement","ENS",["\\noindent\\textbf{actual\\_inspection}: actual "," text read;"]]
["W1388",[4584,4584,395198,395202],[4564,4564,375493,375496],"text","(4)",["actual statement "," read; image-only"]]
["W1389",[4584,4584,395203,395281],[4564,4565,375497,375519],"read; image-only Milne and Faltings pages additionally visually inspected\\par\n","7(1974),507--530\\par\n\n",["statement text ",""]]
["W1390",[4586,4586,395337,395447],[4567,4567,375575,375575],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1391",[4591,4591,395710,395723],[4571,4571,375838,375843],"Prop12.1p122;","Prop.",["\\noindent\\textbf{locator}: "," Prop12.9p125; Thm15.1(a)p129;"]]
["W1392",[4591,4591,395724,395737],[4571,4571,375844,375849],"Prop12.9p125;","12.1,",["\\noindent\\textbf{locator}: Prop12.1p122; "," Thm15.1(a)p129; scanpages20,23,27"]]
["W1393",[4591,4591,395738,395753],[4571,4571,375850,375857],"Thm15.1(a)p129;","p.~122;",["Prop12.1p122; Prop12.9p125; "," scanpages20,23,27 visually"]]
["W1394",[4591,4591,395754,395771],[4571,4571,375858,375921],"scanpages20,23,27","Prop. 12.9, p.~125; Thm. 15.1(a), p.~129; scan pages 20, 23, 27",["Prop12.9p125; Thm15.1(a)p129; "," visually read\\par"]]
["W1395",[4593,4594,395853,395950],[4573,4573,376003,376013],"ArithmeticGeomet\\allowbreak{}ry,Springer(1986),103--150\\par\n\\noindent\\textbf{actual\\_inspection}:","Arithmetic",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1396",[4594,4594,395951,395957],[4573,4573,376014,376023],"actual","Geometry,",["ArithmeticGeomet\\allowbreak{}ry,Springer(1986),103--150\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1397",[4594,4594,395958,395967],[4573,4573,376024,376032],"statement","Springer",["\\noindent\\textbf{actual\\_inspection}: actual "," text read;"]]
["W1398",[4594,4594,395968,396051],[4573,4574,376033,376054],"text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","(1986),103--150\\par\n\n",["actual statement ",""]]
["W1399",[4601,4601,396501,396527],[4581,4581,376504,376512],"Mordell,Theorem1(a,b)p204;","Mordell,",["Complements to "," scanp212 visually"]]
["W1400",[4601,4601,396528,396536],[4581,4581,376513,376548],"scanp212","Theorem 1(a,b), p.~204; scan p.~212",["to Mordell,Theorem1(a,b)p204; "," visually read\\par"]]
["W1401",[4603,4604,396618,396701],[4583,4583,376630,376638],"RationalPoints,secondedition,Vieweg(1986)\\par\n\\noindent\\textbf{actual\\_inspection}:","Rational",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1402",[4604,4604,396702,396708],[4583,4583,376639,376646],"actual","Points,",["RationalPoints,secondedition,Vieweg(1986)\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1403",[4604,4604,396709,396718],[4583,4583,376647,376653],"statement","second",["\\noindent\\textbf{actual\\_inspection}: actual "," text read;"]]
["W1404",[4604,4604,396719,396723],[4583,4583,376654,376662],"text","edition,",["actual statement "," read; image-only"]]
["W1405",[4604,4604,396724,396729],[4583,4583,376663,376669],"read;","Vieweg",["statement text "," image-only Milne"]]
["W1406",[4604,4604,396730,396802],[4583,4584,376670,376682],"image-only Milne and Faltings pages additionally visually inspected\\par\n","(1986)\\par\n\n",["text read; ",""]]
["W1407",[4606,4606,396857,396967],[4586,4586,376737,376737],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1408",[4611,4611,397234,397261],[4590,4590,377004,377023],"I.1.3,1.5,1.6(b,c)pp18--19;","I.1.3,1.5,1.6(b,c),",["\\noindent\\textbf{locator}: "," II.2.1proofp164\\par\n"]]
["W1409",[4611,4611,397262,397281],[4590,4590,377024,377061],"II.2.1proofp164\\par","pp.~18--19; II.2.1, proof, p.~164\\par",["\\noindent\\textbf{locator}: I.1.3,1.5,1.6(b,c)pp18--19; ","\n"]]
["W1410",[4613,4614,397391,397496],[4592,4592,377171,377181],"ArithmeticDualit\\allowbreak{}yTheorems,2ndedition,BookSurge2006\\par\n\\noindent\\textbf{actual\\_inspection}:","Arithmetic",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1411",[4614,4614,397497,397503],[4592,4592,377182,377189],"actual","Duality",["ArithmeticDualit\\allowbreak{}yTheorems,2ndedition,BookSurge2006\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1412",[4614,4614,397504,397513],[4592,4592,377190,377199],"statement","Theorems,",["\\noindent\\textbf{actual\\_inspection}: actual "," text read;"]]
["W1413",[4614,4614,397514,397518],[4592,4592,377200,377203],"text","2nd",["actual statement "," read; image-only"]]
["W1414",[4614,4614,397519,397524],[4592,4592,377204,377212],"read;","edition,",["statement text "," image-only Milne"]]
["W1415",[4614,4614,397525,397535],[4592,4592,377213,377222],"image-only","BookSurge",["text read; "," Milne and"]]
["W1416",[4614,4614,397536,397597],[4592,4593,377223,377233],"Milne and Faltings pages additionally visually inspected\\par\n","2006\\par\n\n",["read; image-only ",""]]
["W1417",[4621,4621,398073,398098],[4600,4600,377709,377742],"Theorem6.8,Cor6.9p319\\par","Theorem 6.8, Cor. 6.9, p.~319\\par",["uniformization and ","\n"]]
["W1418",[4623,4624,398210,398281],[4602,4602,377854,377858],"ClayMath.Proc4(2005),265--378\\par\n\\noindent\\textbf{actual\\_inspection}:","Clay",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1419",[4624,4624,398282,398288],[4602,4602,377859,377864],"actual","Math.",["ClayMath.Proc4(2005),265--378\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1420",[4624,4624,398289,398298],[4602,4602,377865,377870],"statement","Proc.",["\\noindent\\textbf{actual\\_inspection}: actual "," text read;"]]
["W1421",[4624,4624,398299,398382],[4602,4603,377871,377893],"text read; image-only Milne and Faltings pages additionally visually inspected\\par\n","4(2005),265--378\\par\n\n",["actual statement ",""]]
["W1422",[4631,4631,398810,398829],[4610,4610,378321,378331],"Theorem1pp526--527;","Theorem~1,",["\\noindent\\textbf{locator}: "," \\S{}4equation4.1p531\\par\n"]]
["W1423",[4631,4631,398830,398854],[4610,4610,378332,378377],"\\S{}4equation4.1p531\\par","pp.~526--527; \\S{}4, equation~4.1, p.~531\\par",["\\noindent\\textbf{locator}: Theorem1pp526--527; ","\n"]]
["W1424",[4633,4634,398981,399056],[4612,4612,378504,378506],"J.Math.Soc.Japan25(1973),523--544\\par\n\\noindent\\textbf{actual\\_inspection}:","J.",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1425",[4634,4634,399057,399063],[4612,4612,378507,378512],"actual","Math.",["J.Math.Soc.Japan25(1973),523--544\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1426",[4634,4634,399064,399073],[4612,4612,378513,378517],"statement","Soc.",["\\noindent\\textbf{actual\\_inspection}: actual "," text read;"]]
["W1427",[4634,4634,399074,399078],[4612,4612,378518,378523],"text","Japan",["actual statement "," read; image-only"]]
["W1428",[4634,4634,399079,399157],[4612,4613,378524,378547],"read; image-only Milne and Faltings pages additionally visually inspected\\par\n","25(1973),523--544\\par\n\n",["statement text ",""]]
["W1429",[4636,4636,399212,399253],[4615,4615,378602,378636],"\\noindent\\textbf{authoritative\\_version}:","\\noindent\\textbf{access}: Retained",[""," published source;"]]
["W1430",[4636,4636,399264,399271],[4615,4615,378647,378651],"source;","PDF;",["\\noindent\\textbf{authoritative\\_version}: published "," Milne author-hosted"]]
["W1431",[4636,4637,399272,399422],[4615,4615,378652,378655],"Milne author-hosted published chapter/edition\\par\n\\noindent\\textbf{access}: Copied exact already-frozen published PDF from private height packet after","the",["published source; "," current JStage500;"]]
["W1432",[4637,4637,399431,399441],[4615,4615,378664,378670],"JStage500;","JStage",["after current "," source text"]]
["W1433",[4637,4637,399442,399448],[4615,4615,378671,378680],"source","retrieval",["current JStage500; "," text directly"]]
["W1434",[4637,4637,399449,399453],[4615,4615,378681,378689],"text","returned",["JStage500; source "," directly read\\par"]]
["W1435",[4637,4637,399454,399471],[4615,4615,378690,378698],"directly read\\par","500.\\par",["source text ","\n"]]
["W1436",[4642,4642,399748,399811],[4620,4620,378975,379056],"ChapterI\\S{}2.2Corollary2pI-8;\\S{}2.3theorem/lemmapI-10--11\\par","Chapter I, \\S{}2.2, Corollary 2, p.~I-8; \\S{}2.3, theorem/lemma, pp.~I-10--11\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1437",[4644,4645,399944,400101],[4622,4622,379189,379196],"Abelianl-AdicRepresentati\\allowbreak{}onsandEllipticCu\\allowbreak{}rves,1968,Addison-Wesley1989reprin\\allowbreak{}t\\par\n\\noindent\\textbf{actual\\_inspection}:","Abelian",["\\noindent\\textbf{publication}: "," actual statement"]]
["W1438",[4645,4645,400102,400108],[4622,4622,379197,379207],"actual","\\(l\\)-Adic",["Abelianl-AdicRepresentati\\allowbreak{}onsandEllipticCu\\allowbreak{}rves,1968,Addison-Wesley1989reprin\\allowbreak{}t\\par\n\\noindent\\textbf{actual\\_inspection}: "," statement text"]]
["W1439",[4645,4645,400109,400146],[4622,4622,379208,379223],"statement text read; image-only Milne","Representations",["\\noindent\\textbf{actual\\_inspection}: actual "," and Faltings"]]
["W1440",[4645,4645,400151,400159],[4622,4622,379228,379236],"Faltings","Elliptic",["Milne and "," pages additionally"]]
["W1441",[4645,4645,400160,400165],[4622,4622,379237,379244],"pages","Curves,",["and Faltings "," additionally visually"]]
["W1442",[4645,4645,400166,400178],[4622,4622,379245,379250],"additionally","1968,",["Faltings pages "," visually inspected\\par"]]
["W1443",[4645,4645,400179,400187],[4622,4622,379251,379265],"visually","Addison-Wesley",["pages additionally "," inspected\\par\n"]]
["W1444",[4645,4645,400188,400202],[4622,4623,379266,379284],"inspected\\par\n","1989 reprint\\par\n\n",["additionally visually ",""]]
["W1445",[4647,4647,400257,400367],[4625,4625,379339,379339],"\\noindent\\textbf{authoritative\\_version}: published source; Milne author-hosted published chapter/edition\\par\n","",["",""]]
["W1446",[4652,4652,400632,400665],[4629,4629,379604,379638],"Math.Ann.212(1975),printed294\\par","Math.Ann.212(1975),printed 294\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1447",[4654,4654,400805,400842],[4631,4631,379778,379810],"\\noindent\\textbf{actual\\_inspection}:","\\noindent\\textbf{qualification}:",[""," p296,p298 visually"]]
["W1448",[4654,4654,400843,400852],[4631,4631,379811,379838],"p296,p298","Printed pp.296 and 298 were",["\\noindent\\textbf{actual\\_inspection}: "," visually read;"]]
["W1449",[4654,4654,400862,400867],[4631,4631,379848,379856],"read;","checked;",["p296,p298 visually "," p294,p295 acquired,"]]
["W1450",[4654,4654,400868,400877],[4631,4631,379857,379863],"p294,p295","pp.294",["visually read; "," acquired, prior"]]
["W1451",[4654,4654,400878,400887],[4631,4631,379864,379867],"acquired,","and",["read; p294,p295 "," prior bridge"]]
["W1452",[4654,4654,400888,400893],[4631,4631,379868,379871],"prior","295",["p294,p295 acquired, "," bridge read;"]]
["W1453",[4654,4654,400894,400900],[4631,4631,379872,379876],"bridge","were",["acquired, prior "," read; no"]]
["W1454",[4654,4654,400901,400906],[4631,4631,379877,379885],"read;","acquired",["prior bridge "," no false"]]
["W1455",[4654,4654,400907,400909],[4631,4631,379886,379889],"no","but",["bridge read; "," false claim"]]
["W1456",[4654,4654,400910,400915],[4631,4631,379890,379894],"false","were",["read; no "," claim of"]]
["W1457",[4654,4654,400916,400921],[4631,4631,379895,379898],"claim","not",["no false "," of visual"]]
["W1458",[4654,4654,400922,400924],[4631,4631,379899,379907],"of","visually",["false claim "," visual reading"]]
["W1459",[4654,4654,400925,400953],[4631,4631,379908,379920],"visual reading p294/p295\\par","checked.\\par",["claim of ","\n\\noindent\\textbf{consumer\\_proof\\_sections}: M3precision"]]
["W1460",[4655,4655,400999,401010],[4632,4632,379966,379978],"M3precision","M3 precision",["p294/p295\\par\n\\noindent\\textbf{consumer\\_proof\\_sections}: "," finding; M6Fricke\\par"]]
["W1461",[4655,4655,401020,401032],[4632,4632,379988,380001],"M6Fricke\\par","M6 Fricke\\par",["M3precision finding; ","\n"]]
["W1462",[4660,4660,401298,401331],[4637,4637,380267,380301],"Math.Ann.212(1975),printed295\\par","Math.Ann.212(1975),printed 295\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1463",[4662,4662,401471,401508],[4639,4639,380441,380473],"\\noindent\\textbf{actual\\_inspection}:","\\noindent\\textbf{qualification}:",[""," p296,p298 visually"]]
["W1464",[4662,4662,401509,401518],[4639,4639,380474,380501],"p296,p298","Printed pp.296 and 298 were",["\\noindent\\textbf{actual\\_inspection}: "," visually read;"]]
["W1465",[4662,4662,401528,401533],[4639,4639,380511,380519],"read;","checked;",["p296,p298 visually "," p294,p295 acquired,"]]
["W1466",[4662,4662,401534,401543],[4639,4639,380520,380526],"p294,p295","pp.294",["visually read; "," acquired, prior"]]
["W1467",[4662,4662,401544,401553],[4639,4639,380527,380530],"acquired,","and",["read; p294,p295 "," prior bridge"]]
["W1468",[4662,4662,401554,401559],[4639,4639,380531,380534],"prior","295",["p294,p295 acquired, "," bridge read;"]]
["W1469",[4662,4662,401560,401566],[4639,4639,380535,380539],"bridge","were",["acquired, prior "," read; no"]]
["W1470",[4662,4662,401567,401572],[4639,4639,380540,380548],"read;","acquired",["prior bridge "," no false"]]
["W1471",[4662,4662,401573,401575],[4639,4639,380549,380552],"no","but",["bridge read; "," false claim"]]
["W1472",[4662,4662,401576,401581],[4639,4639,380553,380557],"false","were",["read; no "," claim of"]]
["W1473",[4662,4662,401582,401587],[4639,4639,380558,380561],"claim","not",["no false "," of visual"]]
["W1474",[4662,4662,401588,401590],[4639,4639,380562,380570],"of","visually",["false claim "," visual reading"]]
["W1475",[4662,4662,401591,401619],[4639,4639,380571,380583],"visual reading p294/p295\\par","checked.\\par",["claim of ","\n\\noindent\\textbf{consumer\\_proof\\_sections}: M3precision"]]
["W1476",[4663,4663,401665,401676],[4640,4640,380629,380641],"M3precision","M3 precision",["p294/p295\\par\n\\noindent\\textbf{consumer\\_proof\\_sections}: "," finding; M6Fricke\\par"]]
["W1477",[4663,4663,401686,401698],[4640,4640,380651,380664],"M6Fricke\\par","M6 Fricke\\par",["M3precision finding; ","\n"]]
["W1478",[4668,4668,401964,401997],[4645,4645,380930,380964],"Math.Ann.212(1975),printed296\\par","Math.Ann.212(1975),printed 296\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1479",[4670,4670,402137,402174],[4647,4647,381104,381136],"\\noindent\\textbf{actual\\_inspection}:","\\noindent\\textbf{qualification}:",[""," p296,p298 visually"]]
["W1480",[4670,4670,402175,402184],[4647,4647,381137,381164],"p296,p298","Printed pp.296 and 298 were",["\\noindent\\textbf{actual\\_inspection}: "," visually read;"]]
["W1481",[4670,4670,402194,402199],[4647,4647,381174,381182],"read;","checked;",["p296,p298 visually "," p294,p295 acquired,"]]
["W1482",[4670,4670,402200,402209],[4647,4647,381183,381189],"p294,p295","pp.294",["visually read; "," acquired, prior"]]
["W1483",[4670,4670,402210,402219],[4647,4647,381190,381193],"acquired,","and",["read; p294,p295 "," prior bridge"]]
["W1484",[4670,4670,402220,402225],[4647,4647,381194,381197],"prior","295",["p294,p295 acquired, "," bridge read;"]]
["W1485",[4670,4670,402226,402232],[4647,4647,381198,381202],"bridge","were",["acquired, prior "," read; no"]]
["W1486",[4670,4670,402233,402238],[4647,4647,381203,381211],"read;","acquired",["prior bridge "," no false"]]
["W1487",[4670,4670,402239,402241],[4647,4647,381212,381215],"no","but",["bridge read; "," false claim"]]
["W1488",[4670,4670,402242,402247],[4647,4647,381216,381220],"false","were",["read; no "," claim of"]]
["W1489",[4670,4670,402248,402253],[4647,4647,381221,381224],"claim","not",["no false "," of visual"]]
["W1490",[4670,4670,402254,402256],[4647,4647,381225,381233],"of","visually",["false claim "," visual reading"]]
["W1491",[4670,4670,402257,402285],[4647,4647,381234,381246],"visual reading p294/p295\\par","checked.\\par",["claim of ","\n\\noindent\\textbf{consumer\\_proof\\_sections}: M3precision"]]
["W1492",[4671,4671,402331,402342],[4648,4648,381292,381304],"M3precision","M3 precision",["p294/p295\\par\n\\noindent\\textbf{consumer\\_proof\\_sections}: "," finding; M6Fricke\\par"]]
["W1493",[4671,4671,402352,402364],[4648,4648,381314,381327],"M6Fricke\\par","M6 Fricke\\par",["M3precision finding; ","\n"]]
["W1494",[4676,4676,402630,402663],[4653,4653,381593,381627],"Math.Ann.212(1975),printed298\\par","Math.Ann.212(1975),printed 298\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1495",[4678,4678,402803,402840],[4655,4655,381767,381799],"\\noindent\\textbf{actual\\_inspection}:","\\noindent\\textbf{qualification}:",[""," p296,p298 visually"]]
["W1496",[4678,4678,402841,402850],[4655,4655,381800,381827],"p296,p298","Printed pp.296 and 298 were",["\\noindent\\textbf{actual\\_inspection}: "," visually read;"]]
["W1497",[4678,4678,402860,402865],[4655,4655,381837,381845],"read;","checked;",["p296,p298 visually "," p294,p295 acquired,"]]
["W1498",[4678,4678,402866,402875],[4655,4655,381846,381852],"p294,p295","pp.294",["visually read; "," acquired, prior"]]
["W1499",[4678,4678,402876,402885],[4655,4655,381853,381856],"acquired,","and",["read; p294,p295 "," prior bridge"]]
["W1500",[4678,4678,402886,402891],[4655,4655,381857,381860],"prior","295",["p294,p295 acquired, "," bridge read;"]]
["W1501",[4678,4678,402892,402898],[4655,4655,381861,381865],"bridge","were",["acquired, prior "," read; no"]]
["W1502",[4678,4678,402899,402904],[4655,4655,381866,381874],"read;","acquired",["prior bridge "," no false"]]
["W1503",[4678,4678,402905,402907],[4655,4655,381875,381878],"no","but",["bridge read; "," false claim"]]
["W1504",[4678,4678,402908,402913],[4655,4655,381879,381883],"false","were",["read; no "," claim of"]]
["W1505",[4678,4678,402914,402919],[4655,4655,381884,381887],"claim","not",["no false "," of visual"]]
["W1506",[4678,4678,402920,402922],[4655,4655,381888,381896],"of","visually",["false claim "," visual reading"]]
["W1507",[4678,4678,402923,402951],[4655,4655,381897,381909],"visual reading p294/p295\\par","checked.\\par",["claim of ","\n\\noindent\\textbf{consumer\\_proof\\_sections}: M3precision"]]
["W1508",[4679,4679,402997,403008],[4656,4656,381955,381967],"M3precision","M3 precision",["p294/p295\\par\n\\noindent\\textbf{consumer\\_proof\\_sections}: "," finding; M6Fricke\\par"]]
["W1509",[4679,4679,403018,403030],[4656,4656,381977,381990],"M6Fricke\\par","M6 Fricke\\par",["M3precision finding; ","\n"]]
["W1510",[4684,4684,403297,403312],[4661,4661,382257,382264],"Theorem1.0.4p5;","Theorem",["\\noindent\\textbf{locator}: "," Conjecture1.0.1p2\\par\n"]]
["W1511",[4684,4684,403313,403334],[4661,4661,382265,382304],"Conjecture1.0.1p2\\par","1.0.4, p.~5; Conjecture 1.0.1, p.~2\\par",["\\noindent\\textbf{locator}: Theorem1.0.4p5; ","\n"]]
["W1512",[4687,4687,403501,403574],[4664,4664,382471,382471],"\\noindent\\textbf{actual\\_inspection}: actual theorem/definitions read\\par","",["","\n\\noindent\\textbf{use}: proof"]]
["W1513",[4688,4688,403662,403678],[4665,4665,382559,382576],"Calegari2023\\par","Calegari 2023\\par",["input is ","\n"]]
["W1514",[4693,4693,403967,404002],[4670,4670,382865,382902],"Theorems3.4/3.5,printed405--406\\par","Theorems 3.4/3.5,printed 405--406\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1515",[4695,4696,404123,404217],[4672,4672,383023,383030],"AnnalesInstitutF\\allowbreak{}ourier45(1995),403--420\\par\n\\noindent\\textbf{actual\\_inspection}:","Annales",["\\noindent\\textbf{publication}: "," actualfinalTheor\\allowbreak{}ems3.4/3.5andSection3text\\allowbreak{}read;hashmatchesretai\\allowbreak{}nedpublicsource\\par\n\\noindent\\textbf{consumer}:"]]
["W1516",[4696,4696,404218,404339],[4672,4673,383031,383071],"actualfinalTheor\\allowbreak{}ems3.4/3.5andSection3text\\allowbreak{}read;hashmatchesretai\\allowbreak{}nedpublicsource\\par\n","Institut Fourier 45(1995),403--420\\par\n\n",["AnnalesInstitutF\\allowbreak{}ourier45(1995),403--420\\par\n\\noindent\\textbf{actual\\_inspection}: ","\\noindent\\textbf{consumer}: PROVIDER\\_SCOPE\\_CARRYP4;PROOF\\_FINALM5\\par\n"]]
["W1517",[4697,4697,404367,404410],[4674,4674,383099,383145],"PROVIDER\\_SCOPE\\_CARRYP4;PROOF\\_FINALM5\\par","PROVIDER\\_SCOPE\\_CARRY P4; PROOF\\_FINAL M5\\par",["actualfinalTheor\\allowbreak{}ems3.4/3.5andSection3text\\allowbreak{}read;hashmatchesretai\\allowbreak{}nedpublicsource\\par\n\\noindent\\textbf{consumer}: ","\n"]]
["W1518",[4700,4700,404557,404672],[4677,4677,383292,383392],"Cassels--FrohlichAlgebrai\\allowbreak{}cNumberTheory(1967),ChapterVI,Localclassfieldt\\allowbreak{}heory,128--161\\par","Cassels--Frohlich, Algebraic Number Theory (1967), Chapter VI, Local class field theory,128--161\\par",["\\noindent\\textbf{publication}: ","\n\\noindent\\textbf{locator}: \\S{}\\S{}4.1--4.3pp155--159\\par"]]
["W1519",[4701,4701,404700,404730],[4678,4678,383420,383454],"\\S{}\\S{}4.1--4.3pp155--159\\par","\\S{}\\S{}4.1--4.3, pp.~155--159\\par",["Cassels--FrohlichAlgebrai\\allowbreak{}cNumberTheory(1967),ChapterVI,Localclassfieldt\\allowbreak{}heory,128--161\\par\n\\noindent\\textbf{locator}: ","\n"]]
["W1520",[4703,4703,404902,404916],[4680,4680,383626,383641],"retainedsource","retained source",["unknown in "," record; no"]]
["W1521",[4703,4703,404928,404961],[4680,4680,383653,383675],"newlyinventedURL\\allowbreak{}\\par","newly invented URL\\par",["record; no ","\n\\noindent\\textbf{actual\\_inspection}: retainedexactsou\\allowbreak{}rceapplicationan\\allowbreak{}dgeneraltheoremp\\allowbreak{}rofilecheckedaga\\allowbreak{}instcurrentobjec\\allowbreak{}ts;notafreshprimary\\allowbreak{}extractread\\par"]]
["W1522",[4704,4704,404962,404999],[4681,4681,383676,383708],"\\noindent\\textbf{actual\\_inspection}:","\\noindent\\textbf{qualification}:",["no newlyinventedURL\\allowbreak{}\\par\n"," retainedexactsou\\allowbreak{}rceapplicationan\\allowbreak{}dgeneraltheoremp\\allowbreak{}rofilecheckedaga\\allowbreak{}instcurrentobjec\\allowbreak{}ts;notafreshprimary\\allowbreak{}extractread\\par\n"]]
["W1523",[4704,4704,405000,405192],[4681,4681,383709,383825],"retainedexactsou\\allowbreak{}rceapplicationan\\allowbreak{}dgeneraltheoremp\\allowbreak{}rofilecheckedaga\\allowbreak{}instcurrentobjec\\allowbreak{}ts;notafreshprimary\\allowbreak{}extractread\\par","The retained source application was compared with the current objects; the primary extract was not freshly read.\\par",["newlyinventedURL\\allowbreak{}\\par\n\\noindent\\textbf{actual\\_inspection}: ","\n"]]
["W1524",[4717,4717,405946,405977],[4694,4694,384579,384611],"PROVIDER\\_SCOPE\\_CARRY.mdP4\\par","PROVIDER\\_SCOPE\\_CARRY.md P4\\par",["\\noindent $\\bullet$ ","\n"]]
["W1525",[4723,4723,406282,406300],[4700,4700,384916,384928],"constructionH0/H1;","construction",["\\noindent\\textbf{locator}: H0--H4; "," applicationsH0.2/H1/H2; consumersH2--H4\\par"]]
["W1526",[4723,4723,406301,406324],[4700,4700,384929,384935],"applicationsH0.2/H1/H2;","H0/H1;",["H0--H4; constructionH0/H1; "," consumersH2--H4\\par\n"]]
["W1527",[4723,4723,406325,406344],[4700,4700,384936,384981],"consumersH2--H4\\par","applications H0.2/H1/H2; consumers H2--H4\\par",["constructionH0/H1; applicationsH0.2/H1/H2; ","\n"]]
["W1528",[4728,4728,406645,406670],[4705,4705,385282,385308],"originalr5/r3/CL1/CL2\\par","original r5/r3/CL1/CL2\\par",["481--660;8097--8347 actual ","\n"]]
["W1529",[4743,4743,407482,407496],[4720,4720,386120,386125],"lemma505--705;","lemma",["\\noindent\\textbf{locator}: "," baseline1334--1505; b-family8252--8495\\par"]]
["W1530",[4743,4743,407497,407516],[4720,4720,386126,386135],"baseline1334--1505;","505--705;",["\\noindent\\textbf{locator}: lemma505--705; "," b-family8252--8495\\par\n"]]
["W1531",[4743,4743,407517,407539],[4720,4720,386136,386180],"b-family8252--8495\\par","baseline 1334--1505; b-family 8252--8495\\par",["lemma505--705; baseline1334--1505; ","\n"]]
["W1532",[4783,4783,409976,409986],[4760,4760,388617,388622],"wholeproof","whole",["\\noindent\\textbf{locator}: "," \\S{}\\S{}1--9,16sourceapplicat\\allowbreak{}ions\\par\n"]]
["W1533",[4783,4783,409987,410037],[4760,4760,388623,388670],"\\S{}\\S{}1--9,16sourceapplicat\\allowbreak{}ions\\par","proof, \\S{}\\S{}1--9, 16 source applications\\par",["\\noindent\\textbf{locator}: wholeproof ","\n"]]
["W1534",[4788,4788,410325,410361],[4765,4765,388958,388983],"wholeactualargum\\allowbreak{}ent\\par","whole actual argument\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1535",[4793,4793,410631,410705],[4770,4770,389253,389307],"wholeactualmaxim\\allowbreak{}alstackandisomet\\allowbreak{}rycomparison\\par","whole actual maximal-stack and isometry comparison\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1536",[4798,4798,410980,411039],[4775,4775,389582,389651],"16FULL-COVER+4conductor+H19RAMIFICATION+CM/D210profiles\\par","16 FULL-COVER + 4 conductor + H19 RAMIFICATION + CM/D210 profiles\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1537",[4803,4803,411332,411369],[4780,4780,389944,389970],"exactextractedsc\\allowbreak{}opes\\par","exact extracted scopes\\par",["\\noindent\\textbf{locator}: ","\n"]]
["W1538",[4806,4806,411480,411513],[4783,4783,390081,390104],"PanfinalJAMS2022\\allowbreak{}\\par","Pan final JAMS 2022\\par",["\\noindent\\textbf{source}: ","\n"]]
["W1539",[4812,4812,411966,412008],[4789,4789,390557,390589],"Washington1997Th\\allowbreak{}eorem14.1\\par","Washington 1997 Theorem 14.1\\par",["\\noindent\\textbf{source}: ","\n\\noindent\\textbf{result}: not"]]
["W1540",[4813,4813,412051,412065],[4790,4790,390632,390648],"proofM3instead","proof M3 instead",["not reacquired; "," derives finiteDirichletc\\allowbreak{}haracter"]]
["W1541",[4813,4813,412074,412111],[4790,4790,390657,390685],"finiteDirichletc\\allowbreak{}haracter","a finite Dirichlet character",["proofM3instead derives "," from published"]]
["W1542",[4813,4813,412127,412165],[4790,4790,390701,390729],"MilneADTglobalre\\allowbreak{}ciprocity","Milne ADT global reciprocity",["from published "," and Qidele"]]
["W1543",[4813,4813,412170,412176],[4790,4790,390734,390752],"Qidele","the rational idele",["MilneADTglobalre\\allowbreak{}ciprocity and "," decomposition\\par\n"]]
["W1544",[4815,4815,412268,412331],[4792,4792,390844,390848],"exactpublicfullD\\allowbreak{}210sourceapplica\\allowbreak{}tions","full",["The sixteen "," are carried"]]
["W1545",[4815,4815,412332,412335],[4792,4792,390849,390853],"are","D210",["sixteen exactpublicfullD\\allowbreak{}210sourceapplica\\allowbreak{}tions "," carried at"]]
["W1546",[4815,4815,412336,412343],[4792,4792,390854,390860],"carried","source",["exactpublicfullD\\allowbreak{}210sourceapplica\\allowbreak{}tions are "," at their"]]
["W1547",[4815,4815,412344,412346],[4792,4792,390861,390880],"at","applications retain",["are carried "," their accepted"]]
["W1548",[4815,4815,412353,412361],[4792,4792,390887,390893],"accepted","stated",["at their "," scope, not"]]
["W1549",[4815,4815,412362,412368],[4792,4792,390894,390904],"scope,","hypotheses",["their accepted "," not freshly"]]
["W1550",[4815,4815,412369,412372],[4792,4792,390905,390967],"not","and source scopes. Not every final PDF or HTML source has been",["accepted scope, "," freshly reaudited"]]
["W1551",[4815,4815,412381,412605],[4792,4792,390976,390992],"reaudited from every finalPDF/HTML; the wholeinternalpro\\allowbreak{}of and currentprivateco\\allowbreak{}nnection are directlyread. Independentcurre\\allowbreak{}ntreviewmustacce\\allowbreak{}ptthisexactcarry\\allowbreak{}.\\par","re-examined.\\par",["not freshly ","\n\\noindent $\\bullet$"]]
["W1552",[4816,4816,412629,412689],[4793,4793,391016,391023],"primaryfinalPanJ\\allowbreak{}AMSbodycompariso\\allowbreak{}n;","primary",["$\\bullet$ No "," immediatefinalpu\\allowbreak{}blishedCalegarit\\allowbreak{}heoremisdirectly\\allowbreak{}checked.\\par\n\\noindent"]]
["W1553",[4816,4816,412690,412789],[4793,4793,391024,391127],"immediatefinalpu\\allowbreak{}blishedCalegarit\\allowbreak{}heoremisdirectly\\allowbreak{}checked.\\par","final Pan JAMS body comparison; the immediate final published Calegari theorem is directly checked.\\par",["No primaryfinalPanJ\\allowbreak{}AMSbodycompariso\\allowbreak{}n; ","\n\\noindent $\\bullet$"]]
["W1554",[4817,4817,412810,412895],[4794,4794,391148,391242],"SeparateheightH3\\allowbreak{}Remond/final214assembly\\allowbreak{}remainrootlanes.\\par","The height H3 R\\'emond application and the full 214 argument remain separate requirements.\\par",["\\noindent $\\bullet$ ","\n\\noindent\\textbf{supersedes\\_scope\\_statements\\_only}: SOURCE\\_USES.json"]]
["W1555",[4818,4818,412896,412950],[4795,4795,391243,391274],"\\noindent\\textbf{supersedes\\_scope\\_statements\\_only}:","\\noindent\\textbf{source scope}:",["$\\bullet$ SeparateheightH3\\allowbreak{}Remond/final214assembly\\allowbreak{}remainrootlanes.\\par\n"," SOURCE\\_USES.json remains"]]
["W1556",[4818,4818,412969,412976],[4795,4795,391293,391300],"remains","records",["\\noindent\\textbf{supersedes\\_scope\\_statements\\_only}: SOURCE\\_USES.json "," frozen initialauthorhis\\allowbreak{}tory;"]]
["W1557",[4818,4818,412977,412983],[4795,4795,391301,391304],"frozen","the",["SOURCE\\_USES.json remains "," initialauthorhis\\allowbreak{}tory; this"]]
["W1558",[4818,4818,412984,413018],[4795,4795,391305,391324],"initialauthorhis\\allowbreak{}tory;","initial source use;",["remains frozen "," this finalinventory"]]
["W1559",[4818,4818,413024,413038],[4795,4795,391330,391339],"finalinventory","inventory",["initialauthorhis\\allowbreak{}tory; this "," adds exactH01andcondu\\allowbreak{}ctorcarry,"]]
["W1560",[4818,4818,413039,413043],[4795,4795,391340,391344],"adds","also",["this finalinventory "," exactH01andcondu\\allowbreak{}ctorcarry, without"]]
["W1561",[4818,4818,413044,413083],[4795,4795,391345,391355],"exactH01andcondu\\allowbreak{}ctorcarry,","identifies",["finalinventory adds "," without changing"]]
["W1562",[4818,4818,413084,413091],[4795,4795,391356,391359],"without","the",["adds exactH01andcondu\\allowbreak{}ctorcarry, "," changing initialfiles.\\par"]]
["W1563",[4818,4818,413092,413100],[4795,4795,391360,391363],"changing","H01",["exactH01andcondu\\allowbreak{}ctorcarry, without "," initialfiles.\\par\n"]]
["W1564",[4818,4818,413101,413118],[4795,4795,391364,391395],"initialfiles.\\par","and conductor applications.\\par",["without changing ","\n"]]
["W1565",[5082,5082,433350,433369],[5059,5059,411627,411630],"ANT8(2014),89--140,","ANT",["\\noindent\\textbf{version}: "," DOI10.2140/ant.2014.8.89\\par\n\\noindent\\textbf{publication\\_scope}:"]]
["W1566",[5082,5082,433370,433398],[5059,5059,411631,411677],"DOI10.2140/ant.2014.8.89\\par","8(2014),89--140, DOI 10.2140/ant.2014.8.89\\par",["\\noindent\\textbf{version}: ANT8(2014),89--140, ","\n\\noindent\\textbf{publication\\_scope}: Full"]]
["W1567",[5083,5083,433437,433441],[5060,5060,411716,411724],"Full","The full",["DOI10.2140/ant.2014.8.89\\par\n\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1568",[5083,5083,433458,433466],[5060,5060,411741,411743],"retained","is",["third-party PDF "," only as"]]
["W1569",[5083,5083,433467,433471],[5060,5060,411744,411747],"only","not",["PDF retained "," as local"]]
["W1570",[5083,5083,433472,433474],[5060,5060,411748,411758],"as","reproduced",["retained only "," local reviewer"]]
["W1571",[5083,5083,433475,433480],[5060,5060,411759,411764],"local","here;",["only as "," reviewer source;"]]
["W1572",[5083,5083,433481,433489],[5060,5060,411765,411768],"reviewer","its",["as local "," source; publication"]]
["W1573",[5083,5083,433490,433497],[5060,5060,411769,411773],"source;","URL,",["local reviewer "," publication bundle"]]
["W1574",[5083,5083,433498,433536],[5060,5060,411774,411778],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1575",[5083,5083,433541,433547],[5060,5060,411783,411789],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1576",[5083,5083,433548,433556],[5060,5060,411790,411798],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1577",[5083,5083,433557,433569],[5060,5060,411799,411816],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1578",[5091,5091,434137,434141],[5068,5068,412384,412392],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1579",[5091,5091,434158,434166],[5068,5068,412409,412411],"retained","is",["third-party PDF "," only as"]]
["W1580",[5091,5091,434167,434171],[5068,5068,412412,412415],"only","not",["PDF retained "," as local"]]
["W1581",[5091,5091,434172,434174],[5068,5068,412416,412426],"as","reproduced",["retained only "," local reviewer"]]
["W1582",[5091,5091,434175,434180],[5068,5068,412427,412432],"local","here;",["only as "," reviewer source;"]]
["W1583",[5091,5091,434181,434189],[5068,5068,412433,412436],"reviewer","its",["as local "," source; publication"]]
["W1584",[5091,5091,434190,434197],[5068,5068,412437,412441],"source;","URL,",["local reviewer "," publication bundle"]]
["W1585",[5091,5091,434198,434236],[5068,5068,412442,412446],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1586",[5091,5091,434241,434247],[5068,5068,412451,412457],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1587",[5091,5091,434248,434256],[5068,5068,412458,412466],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1588",[5091,5091,434257,434269],[5068,5068,412467,412484],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1589",[5099,5099,434837,434841],[5076,5076,413052,413060],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1590",[5099,5099,434858,434866],[5076,5076,413077,413079],"retained","is",["third-party PDF "," only as"]]
["W1591",[5099,5099,434867,434871],[5076,5076,413080,413083],"only","not",["PDF retained "," as local"]]
["W1592",[5099,5099,434872,434874],[5076,5076,413084,413094],"as","reproduced",["retained only "," local reviewer"]]
["W1593",[5099,5099,434875,434880],[5076,5076,413095,413100],"local","here;",["only as "," reviewer source;"]]
["W1594",[5099,5099,434881,434889],[5076,5076,413101,413104],"reviewer","its",["as local "," source; publication"]]
["W1595",[5099,5099,434890,434897],[5076,5076,413105,413109],"source;","URL,",["local reviewer "," publication bundle"]]
["W1596",[5099,5099,434898,434936],[5076,5076,413110,413114],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1597",[5099,5099,434941,434947],[5076,5076,413119,413125],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1598",[5099,5099,434948,434956],[5076,5076,413126,413134],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1599",[5099,5099,434957,434969],[5076,5076,413135,413152],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1600",[5107,5107,435537,435541],[5084,5084,413720,413728],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1601",[5107,5107,435558,435566],[5084,5084,413745,413747],"retained","is",["third-party PDF "," only as"]]
["W1602",[5107,5107,435567,435571],[5084,5084,413748,413751],"only","not",["PDF retained "," as local"]]
["W1603",[5107,5107,435572,435574],[5084,5084,413752,413762],"as","reproduced",["retained only "," local reviewer"]]
["W1604",[5107,5107,435575,435580],[5084,5084,413763,413768],"local","here;",["only as "," reviewer source;"]]
["W1605",[5107,5107,435581,435589],[5084,5084,413769,413772],"reviewer","its",["as local "," source; publication"]]
["W1606",[5107,5107,435590,435597],[5084,5084,413773,413777],"source;","URL,",["local reviewer "," publication bundle"]]
["W1607",[5107,5107,435598,435636],[5084,5084,413778,413782],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1608",[5107,5107,435641,435647],[5084,5084,413787,413793],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1609",[5107,5107,435648,435656],[5084,5084,413794,413802],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1610",[5107,5107,435657,435669],[5084,5084,413803,413820],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1611",[5115,5115,436237,436241],[5092,5092,414388,414396],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1612",[5115,5115,436258,436266],[5092,5092,414413,414415],"retained","is",["third-party PDF "," only as"]]
["W1613",[5115,5115,436267,436271],[5092,5092,414416,414419],"only","not",["PDF retained "," as local"]]
["W1614",[5115,5115,436272,436274],[5092,5092,414420,414430],"as","reproduced",["retained only "," local reviewer"]]
["W1615",[5115,5115,436275,436280],[5092,5092,414431,414436],"local","here;",["only as "," reviewer source;"]]
["W1616",[5115,5115,436281,436289],[5092,5092,414437,414440],"reviewer","its",["as local "," source; publication"]]
["W1617",[5115,5115,436290,436297],[5092,5092,414441,414445],"source;","URL,",["local reviewer "," publication bundle"]]
["W1618",[5115,5115,436298,436336],[5092,5092,414446,414450],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1619",[5115,5115,436341,436347],[5092,5092,414455,414461],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1620",[5115,5115,436348,436356],[5092,5092,414462,414470],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1621",[5115,5115,436357,436369],[5092,5092,414471,414488],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1622",[5123,5123,436937,436941],[5100,5100,415056,415064],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1623",[5123,5123,436958,436966],[5100,5100,415081,415083],"retained","is",["third-party PDF "," only as"]]
["W1624",[5123,5123,436967,436971],[5100,5100,415084,415087],"only","not",["PDF retained "," as local"]]
["W1625",[5123,5123,436972,436974],[5100,5100,415088,415098],"as","reproduced",["retained only "," local reviewer"]]
["W1626",[5123,5123,436975,436980],[5100,5100,415099,415104],"local","here;",["only as "," reviewer source;"]]
["W1627",[5123,5123,436981,436989],[5100,5100,415105,415108],"reviewer","its",["as local "," source; publication"]]
["W1628",[5123,5123,436990,436997],[5100,5100,415109,415113],"source;","URL,",["local reviewer "," publication bundle"]]
["W1629",[5123,5123,436998,437036],[5100,5100,415114,415118],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1630",[5123,5123,437041,437047],[5100,5100,415123,415129],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1631",[5123,5123,437048,437056],[5100,5100,415130,415138],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1632",[5123,5123,437057,437069],[5100,5100,415139,415156],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1633",[5131,5131,437637,437641],[5108,5108,415724,415732],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1634",[5131,5131,437658,437666],[5108,5108,415749,415751],"retained","is",["third-party PDF "," only as"]]
["W1635",[5131,5131,437667,437671],[5108,5108,415752,415755],"only","not",["PDF retained "," as local"]]
["W1636",[5131,5131,437672,437674],[5108,5108,415756,415766],"as","reproduced",["retained only "," local reviewer"]]
["W1637",[5131,5131,437675,437680],[5108,5108,415767,415772],"local","here;",["only as "," reviewer source;"]]
["W1638",[5131,5131,437681,437689],[5108,5108,415773,415776],"reviewer","its",["as local "," source; publication"]]
["W1639",[5131,5131,437690,437697],[5108,5108,415777,415781],"source;","URL,",["local reviewer "," publication bundle"]]
["W1640",[5131,5131,437698,437736],[5108,5108,415782,415786],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1641",[5131,5131,437741,437747],[5108,5108,415791,415797],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1642",[5131,5131,437748,437756],[5108,5108,415798,415806],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1643",[5131,5131,437757,437769],[5108,5108,415807,415824],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1644",[5139,5139,438337,438341],[5116,5116,416392,416400],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1645",[5139,5139,438358,438366],[5116,5116,416417,416419],"retained","is",["third-party PDF "," only as"]]
["W1646",[5139,5139,438367,438371],[5116,5116,416420,416423],"only","not",["PDF retained "," as local"]]
["W1647",[5139,5139,438372,438374],[5116,5116,416424,416434],"as","reproduced",["retained only "," local reviewer"]]
["W1648",[5139,5139,438375,438380],[5116,5116,416435,416440],"local","here;",["only as "," reviewer source;"]]
["W1649",[5139,5139,438381,438389],[5116,5116,416441,416444],"reviewer","its",["as local "," source; publication"]]
["W1650",[5139,5139,438390,438397],[5116,5116,416445,416449],"source;","URL,",["local reviewer "," publication bundle"]]
["W1651",[5139,5139,438398,438436],[5116,5116,416450,416454],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1652",[5139,5139,438441,438447],[5116,5116,416459,416465],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1653",[5139,5139,438448,438456],[5116,5116,416466,416474],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1654",[5139,5139,438457,438469],[5116,5116,416475,416492],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1655",[5147,5147,439037,439041],[5124,5124,417060,417068],"Full","The full",["\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1656",[5147,5147,439058,439066],[5124,5124,417085,417087],"retained","is",["third-party PDF "," only as"]]
["W1657",[5147,5147,439067,439071],[5124,5124,417088,417091],"only","not",["PDF retained "," as local"]]
["W1658",[5147,5147,439072,439074],[5124,5124,417092,417102],"as","reproduced",["retained only "," local reviewer"]]
["W1659",[5147,5147,439075,439080],[5124,5124,417103,417108],"local","here;",["only as "," reviewer source;"]]
["W1660",[5147,5147,439081,439089],[5124,5124,417109,417112],"reviewer","its",["as local "," source; publication"]]
["W1661",[5147,5147,439090,439097],[5124,5124,417113,417117],"source;","URL,",["local reviewer "," publication bundle"]]
["W1662",[5147,5147,439098,439136],[5124,5124,417118,417122],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1663",[5147,5147,439141,439147],[5124,5124,417127,417133],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1664",[5147,5147,439148,439156],[5124,5124,417134,417142],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1665",[5147,5147,439157,439169],[5124,5124,417143,417160],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1666",[5154,5154,439780,439796],[5131,5131,417771,417776],"Sigma9(2021)e39,","Sigma",["\\noindent\\textbf{version}: FoM "," DOI10.1017/fms.2021.29\\par\n\\noindent\\textbf{publication\\_scope}:"]]
["W1667",[5154,5154,439797,439823],[5131,5131,417777,417816],"DOI10.1017/fms.2021.29\\par","9(2021)e39, DOI 10.1017/fms.2021.29\\par",["FoM Sigma9(2021)e39, ","\n\\noindent\\textbf{publication\\_scope}: Full"]]
["W1668",[5155,5155,439862,439866],[5132,5132,417855,417863],"Full","The full",["DOI10.1017/fms.2021.29\\par\n\\noindent\\textbf{publication\\_scope}: "," third-party PDF"]]
["W1669",[5155,5155,439883,439891],[5132,5132,417880,417882],"retained","is",["third-party PDF "," only as"]]
["W1670",[5155,5155,439892,439896],[5132,5132,417883,417886],"only","not",["PDF retained "," as local"]]
["W1671",[5155,5155,439897,439899],[5132,5132,417887,417897],"as","reproduced",["retained only "," local reviewer"]]
["W1672",[5155,5155,439900,439905],[5132,5132,417898,417903],"local","here;",["only as "," reviewer source;"]]
["W1673",[5155,5155,439906,439914],[5132,5132,417904,417907],"reviewer","its",["as local "," source; publication"]]
["W1674",[5155,5155,439915,439922],[5132,5132,417908,417912],"source;","URL,",["local reviewer "," publication bundle"]]
["W1675",[5155,5155,439923,439961],[5132,5132,417913,417917],"publication bundle may retain URL/hash","hash",["reviewer source; "," and scoped"]]
["W1676",[5155,5155,439966,439972],[5132,5132,417922,417928],"scoped","source",["URL/hash and "," excerpts instead.\\par"]]
["W1677",[5155,5155,439973,439981],[5132,5132,417929,417937],"excerpts","locators",["and scoped "," instead.\\par\n"]]
["W1678",[5155,5155,439982,439994],[5132,5132,417938,417955],"instead.\\par","are retained.\\par",["scoped excerpts ","\n"]]
["W1679",[5167,5167,440589,440644],[5144,5144,418550,418550],"\\noindent\\textbf{path}: sources/javanpeykar2014.pdf\\par","",["","\n"]]
["W1680",[5171,5171,440806,440861],[5148,5148,418712,418712],"\\noindent\\textbf{path}: sources/javanpeykar2014.txt\\par","",["","\n"]]
["W1681",[5175,5175,441062,441071],[5152,5152,418913,418924],"pp93--94:","pp.~93--94:",["\\S{}2.1 printed "," H0 inner"]]
["W1682",[5176,5176,441152,441161],[5153,5153,419005,419016],"pp97--98:","pp.~97--98:",["\\S{}2.3 printed "," minimal regular"]]
["W1683",[5181,5181,441687,441696],[5158,5158,419542,419553],"Känel\\par","K\\\"anel\\par",["Rafael von ","\n"]]
["W1684",[5188,5188,442196,442248],[5165,5165,420053,420053],"\\noindent\\textbf{path}: sources/vonkanel2021.pdf\\par","",["","\n"]]
["W1685",[5192,5192,442409,442461],[5169,5169,420214,420214],"\\noindent\\textbf{path}: sources/vonkanel2021.txt\\par","",["","\n"]]
["W1686",[5196,5196,442662,442665],[5173,5173,420415,420420],"p5:","p.~5:",["\\S{}2.1 printed "," Néron differential-line"]]
["W1687",[5196,5196,442666,442671],[5173,5173,420421,420428],"Néron","N\\'eron",["printed p5: "," differential-line norm,"]]
["W1688",[5197,5197,442786,442788],[5174,5174,420543,420547],"p5","p.~5",["\\S{}2.1 printed "," after(2.2): hF=hB-(g/2)log\\ensuremath{\\pi"]]
["W1689",[5197,5197,442789,442800],[5174,5174,420548,420560],"after(2.2):","after (2.2):",["printed p5 "," hF=hB-(g/2)log\\ensuremath{\\pi }\\par"]]
["W1690",[5198,5198,442974,442985],[5175,5175,420734,420747],"Néron-model","N\\'eron-model",["semistable-reduction and "," theorems.\\par\n"]]
["W1691",[5201,5201,443114,443120],[5178,5178,420876,420886],"Jérôme","J\\'er\\^ome",["\\noindent\\textbf{author}: "," Von Buhren\\par"]]
["W1692",[5202,5202,443201,443209],[5179,5179,420967,420977],"problème","probl\\`eme",["pour le "," de Mordell--Lang"]]
["W1693",[5202,5202,443236,443243],[5179,5179,421004,421015],"variété","vari\\'et\\'e",["dans une "," abélienne\\par\n\\noindent\\textbf{edition}:"]]
["W1694",[5202,5202,443244,443257],[5179,5179,421016,421031],"abélienne\\par","ab\\'elienne\\par",["une variété ","\n\\noindent\\textbf{edition}: JTNB29(2017),307--320,"]]
["W1695",[5203,5203,443285,443307],[5180,5180,421059,421082],"JTNB29(2017),307--320,","JTNB 29(2017),307--320,",["abélienne\\par\n\\noindent\\textbf{edition}: "," final published\\par"]]
["W1696",[5206,5206,443481,443491],[5183,5183,421256,421263],"printed308","printed",["\\noindent\\textbf{locator}: "," Theorem1.1, definition"]]
["W1697",[5206,5206,443492,443503],[5183,5183,421264,421280],"Theorem1.1,","308 Theorem 1.1,",["\\noindent\\textbf{locator}: printed308 "," definition of"]]
["W1698",[5206,5206,443518,443534],[5183,5183,421295,421317],"C(Gamma,epsilon)","\\(C(\\Gamma,\\epsilon)\\)",["definition of "," and embedding(1.1)\\par"]]
["W1699",[5206,5206,443539,443557],[5183,5183,421322,421341],"embedding(1.1)\\par","embedding (1.1)\\par",["C(Gamma,epsilon) and ","\n\\noindent\\textbf{distribution}: local"]]
["W1700",[5207,5207,443590,443595],[5184,5184,421374,421380],"local","source",["embedding(1.1)\\par\n\\noindent\\textbf{distribution}: "," read-only source;"]]
["W1701",[5207,5207,443596,443605],[5184,5184,421381,421391],"read-only","identified",["\\noindent\\textbf{distribution}: local "," source; no"]]
["W1702",[5207,5207,443606,443613],[5184,5184,421392,421394],"source;","by",["local read-only "," no third-party"]]
["W1703",[5207,5207,443614,443616],[5184,5184,421395,421420],"no","URL and locator; the full",["read-only source; "," third-party PDF"]]
["W1704",[5207,5207,443633,443639],[5184,5184,421437,421439],"copied","is",["third-party PDF "," into this"]]
["W1705",[5207,5207,443640,443644],[5184,5184,421440,421443],"into","not",["PDF copied "," this packet\\par"]]
["W1706",[5207,5207,443645,443649],[5184,5184,421444,421454],"this","reproduced",["copied into "," packet\\par\n"]]
["W1707",[5207,5207,443650,443660],[5184,5184,421455,421463],"packet\\par","here\\par",["into this ","\n"]]
["W1708",[5210,5210,444233,444306],[5187,5187,422036,422036],"  They are not rewritten into current acceptance for this new manuscript.","",[" application contracts.","\n"]]
["W1709",[5219,5219,445073,445139],[5196,5196,422803,422832],"\\item[\\nolinkurl{quartic214-protocol-d/PRIMARY_SOURCE_BRIDGES.md}]","\\item[Primary-source bridges]",[""," \\nolinkurl{research/quartic214/proofs/primary-source-bridges.md}\n"]]
["W1710",[5232,5232,446437,447122],[5209,5209,424130,424130],"\\paragraph{Historical assembly procedure.} The command \\nolinkurl{python3 -B research/quartic214-manuscript/assemble.py} was run from the repository root.  It read bounded source files and emitted the assembled TeX source and \\nolinkurl{SOURCE_SPANS.json}, and performs no polynomial expansion or TeX build.  Its \\nolinkurl{--check} mode verifies byte-for-byte deterministic output.  The separate PDF build and release metadata record the exact generated-source hash, toolchain and PDF hash.  The Version~18 draft is subsequently amended and its source and built PDF are identified separately. Source mapping and successful compilation concern serialization, not arithmetic acceptance.","",["","\n"]]
["W1711",[5241,5241,447921,448057],[5218,5218,424929,424929],"Historical review and incorporation statements belong to that upstream edition; they do not accept the newly assembled 214 manuscript.  ","",["in Part~I.  ","Section, theorem, "]]
["W1712",[5292,5292,451719,451724],[5269,5269,428591,428597],"in222","in 222",["in Section~\\ref{v222:equations}, "," coordinates. Put"]]
["W1713",[5296,5296,452020,452027],[5273,5273,428893,428901],"has2277","has 2277",["$N\\ge53$ it "," coordinate monomials"]]
["W1714",[5344,5344,455095,455140],[5321,5321,431969,431979],"templates, following the review in repository","templates.",["the saved ","\nIssue~2. It"]]
["W1715",[5345,5345,455141,455150],[5322,5322,431980,431980],"Issue~2. ","",["in repository\n","It also "]]
["W1716",[13568,13568,861656,861664],[13545,13545,838486,838494],"accepted","retained",["$11$. The ","\n"]]
["W1717",[14672,14672,912002,912009],[14649,14649,888832,888838],"audited","stated",[""," original height"]]
["W1718",[15433,15433,945941,945950],[15410,15410,922770,922770]," accepted","",["The"," realization of"]]
["W1719",[18138,18138,1066205,1066212],[18115,18115,1043025,1043025]," frozen","",["The"," package includes"]]
["W1720",[18141,18141,1066425,1066456],[18118,18118,1043238,1043245],"proofs and independent reviews.","proofs.",["source-equivalence "," Its manifest"]]
["W1721",[18665,18665,1094485,1094486],[18642,18642,1071274,1071279],"A","These",["supporting-note index}. "," source identity"]]
["W1722",[18665,18665,1094494,1094502],[18642,18642,1071287,1071297],"identity","identities",["A source "," is not"]]
["W1723",[18665,18665,1094503,1094505],[18642,18642,1071298,1071300],"is","do",["source identity "," not a"]]
["W1724",[18665,18665,1094510,1094511],[18642,18642,1071305,1071307],"a","by",["is not "," proof verdict."]]
["W1725",[18665,18665,1094512,1094517],[18642,18642,1071308,1071318],"proof","themselves",["not a "," verdict.\n"]]
["W1726",[18665,18665,1094518,1094526],[18642,18642,1071319,1071358],"verdict.","establish the mathematical conclusions.",["a proof ","\n"]]
["W1727",[19198,19198,1120797,1120809],[19175,19175,1097629,1097643],"\\emph{étale}","\\emph{\\'etale}",["$C_S$ for ","\n"]]
["W1728",[26658,26658,1485271,1485326],[26635,26635,1462105,1462105],"Both full packages have passed fresh independent runs. ","",["every coefficient. ","A separate "]]
["W1729",[26660,26660,1485529,1485735],[26637,26637,1462308,1462308]," The arithmetic assertions in Sections~\\ref{v9:sec:height}--\\ref{v9:sec:depth} received separate adversarial AI review; they have not received independent human peer review or a complete formal proof check.","",[" algebraic transformations."," The inherited"]]
["W1730",[27763,27763,1533474,1533481],[27740,27740,1510047,1510055],"most37.","most 37.",["primes at "," Consequently\n"]]
["W1731",[27767,27767,1533687,1533699],[27744,27744,1510261,1510274],"precision12,","precision 12,",["of relative "," and use"]]
["W1732",[27776,27776,1534028,1534035],[27753,27753,1510603,1510611],"orders1","orders 1",["tests have "," on $f(U_i)$"]]
["W1733",[27776,27776,1534073,1534080],[27753,27753,1510649,1510657],"order40","order 40",["and $\\overline{f(V_i)}$, ","\non $f(H)$,"]]
["W1734",[27777,27777,1534092,1534099],[27754,27754,1510669,1510677],"order10","order 10",["on $f(H)$, "," on $L_1-L'_1,L_1-\\beta$,"]]
["W1735",[27777,27777,1534129,1534136],[27754,27754,1510707,1510715],"order40","order 40",["$L_1-L'_1,L_1-\\beta$, and "," on the"]]
["W1736",[27787,27787,1534509,1534515],[27764,27764,1511088,1511095],"equal1","equal 1",["These units "," at $O$."]]
["W1737",[27793,27793,1534942,1534949],[27770,27770,1511522,1511530],"least20","least 20",["depth at "," for\n"]]
["W1738",[27795,27795,1535024,1535032],[27772,27772,1511605,1511614],"order80.","order 80.",[""," Multiplication by"]]
["W1739",[27898,27898,1539369,1539376],[27875,27875,1515951,1515959],"equal1.","equal 1.",["contact radicals "," Equation~\\eqref{eq:v13-height}\n"]]
["W1740",[27993,27993,1543275,1543282],[27970,27970,1519858,1519866],"order40","order 40",["The retained "," f(H)\n"]]
["W1741",[27995,27995,1543359,1543366],[27972,27972,1519943,1519951],"equal1,","equal 1,",["would "," contradicting the"]]
["W1742",[27997,27997,1543520,1543528],[27974,27974,1520105,1520112],"neither0","neither",["m is "," nor2, H"]]
["W1743",[27997,27997,1543529,1543534],[27974,27974,1520113,1520121],"nor2,","0 nor 2,",["is neither0 "," H and"]]
["W1744",[28021,28021,1544466,1544475],[27998,27998,1521053,1521063],"modulo71,","modulo 71,",[""," and Q(w)"]]
["W1745",[28021,28021,1544497,1544505],[27998,27998,1521085,1521094],"modulo7.","modulo 7.",["no root "," At the"]]
["W1746",[28024,28024,1544705,1544708],[28001,28001,1521294,1521298],"of2","of 2",["square roots "," equal to12,59"]]
["W1747",[28024,28024,1544715,1544722],[28001,28001,1521305,1521307],"to12,59","to",["of2 equal "," modulo71\nand3,4"]]
["W1748",[28024,28024,1544723,1544731],[28001,28001,1521308,1521323],"modulo71","12,59 modulo 71",["equal to12,59 ","\nand3,4 modulo7."]]
["W1749",[28025,28025,1544732,1544738],[28002,28002,1521324,1521327],"and3,4","and",["to12,59 modulo71\n"," modulo7. A"]]
["W1750",[28025,28025,1544739,1544747],[28002,28002,1521328,1521341],"modulo7.","3,4 modulo 7.",["modulo71\nand3,4 "," A K-root"]]
["W1751",[28038,28038,1545353,1545357],[28015,28015,1521947,1521952],"by1.","by 1.",["and differ "," The earlier"]]
["W1752",[28049,28049,1545846,1545854],[28026,28026,1522441,1522450],"depth24.","depth 24.",["the selected "," The proof"]]
["W1753",[28075,28075,1547195,1547202],[28052,28052,1523791,1523797],"primes3","primes",["the exceptional "," and17.\n"]]
["W1754",[28075,28075,1547203,1547209],[28052,28052,1523798,1523807],"and17.","3 and 17.",["exceptional primes3 ","\n"]]
["W1755",[28079,28079,1547396,1547404],[28056,28056,1523994,1524003],"modulo8.","modulo 8.",["odd parts "," The\nother"]]
["W1756",[28080,28080,1547428,1547442],[28057,28057,1524027,1524042],"residues3,7,5.","residues 3,7,5.",["factors have "," Therefore $v_2(r)=2$"]]
["W1757",[28081,28081,1547488,1547492],[28058,28058,1524088,1524093],"At3,","At 3,",["and\n$r/4\\equiv1\\pmod8$. "," $\\beta\\equiv2$ and"]]
["W1758",[28082,28082,1547540,1547548],[28059,28059,1524141,1524148],"product1","product",["factors\nhave "," modulo3. Furthermore"]]
["W1759",[28082,28082,1547549,1547557],[28059,28059,1524149,1524160],"modulo3.","1 modulo 3.",["have product1 "," Furthermore\n"]]
["W1760",[28086,28086,1547660,1547665],[28063,28063,1524263,1524269],"At17,","At 17,",["Thus $v_3(r)=1$. "," the contact"]]
["W1761",[28087,28087,1547707,1547717],[28064,28064,1524311,1524322],"product15,","product 15,",["5,4,1,10,9 with "," a nonzero"]]
["W1762",[28090,28090,1547873,1547876],[28067,28067,1524478,1524480],"at2","at",["square units "," and17,\nand"]]
["W1763",[28090,28090,1547877,1547883],[28067,28067,1524481,1524490],"and17,","2 and 17,",["units at2 ","\nand their"]]
["W1764",[28091,28091,1547905,1547908],[28068,28068,1524512,1524516],"at3","at 3",["unit parts "," are respectively1"]]
["W1765",[28091,28091,1547913,1547926],[28068,28068,1524521,1524533],"respectively1","respectively",["at3 are "," and2, correcting"]]
["W1766",[28091,28091,1547927,1547932],[28068,28068,1524534,1524542],"and2,","1 and 2,",["are respectively1 "," correcting the"]]
["W1767",[28097,28097,1548100,1548103],[28074,28074,1524710,1524714],"At2","At 2",[""," the quotient"]]
["W1768",[28098,28098,1548161,1548164],[28075,28075,1524772,1524774],"at3","at",["$1+8\\mathbb Z_2$;\n"," and17 it"]]
["W1769",[28098,28098,1548165,1548170],[28075,28075,1524775,1524783],"and17","3 and 17",["Z_2$;\nat3 "," it belongs"]]
["W1770",[28101,28101,1548393,1548402],[28078,28078,1525006,1525016],"since4896","since 4896",["using $c$; "," is a"]]
["W1771",[28157,28157,1550729,1550737],[28134,28134,1527343,1527352],"least24.","least 24.",["are at ","\n"]]
["W1772",[28200,28200,1552850,1552858],[28177,28177,1529465,1529474],"order40.","order 40.",["$F=t^2-a(a-2)tb+(a-2)^2b^2-1$ to ","\n"]]
["W1773",[28207,28207,1553221,1553229],[28184,28184,1529837,1529846],"order10.","order 10.",["radicals to "," Since $B^2-6>(5/8)B^2$"]]
["W1774",[28214,28214,1553589,1553597],[28191,28191,1530206,1530215],"order40;","order 40;",["contradiction uses "," lowering only"]]
["W1775",[28219,28219,1553782,1553788],[28196,28196,1530400,1530407],"order1","order 1",["$\\prod_i(1+qY_i)$. In "," group the"]]
["W1776",[28224,28224,1553953,1553960],[28201,28201,1530572,1530580],"Order10","Order 10",["conjugations. "," uses its"]]
["W1777",[28224,28224,1553976,1553983],[28201,28201,1530596,1530604],"order40","order 40",["its pair; "," retains its"]]
["W1778",[28324,28324,1558471,1558476],[28301,28301,1535092,1535098],"at17.","at 17.",["coefficient depth "," Density permits"]]
["W1779",[28331,28331,1558860,1558864],[28308,28308,1535482,1535487],"at17","at 17",["depths also "," and\n"]]
["W1780",[28346,28346,1559727,1559731],[28323,28323,1536350,1536355],"At17","At 17",["hold. "," both $r,c$"]]
["W1781",[28348,28348,1559879,1559883],[28325,28325,1536503,1536508],"of17","of 17",["b)\\ge8$. Inclusion "," does not"]]
["W1782",[28401,28401,1562761,1562766],[28378,28378,1539386,1539392],"and1,","and 1,",["by $e$ "," and\n"]]
["W1783",[28408,28408,1562977,1562985],[28385,28385,1539603,1539612],"reviewed","specified",["of the "," component, the"]]
["W1784",[28441,28441,1564617,1564620],[28418,28418,1541244,1541248],"of3","of 3",["powers "," in the"]]
["W1785",[28444,28444,1564802,1564805],[28421,28421,1541430,1541434],"of1","of 1",["Independence "," and $\\rho$"]]
["W1786",[28532,28532,1569250,1569258],[28509,28509,1545879,1545889],"Isolated","Historical",["% "," Version 14"]]
["W1787",[28532,28532,1569277,1569325],[28509,28509,1545908,1545914],"draft; assembled independent review is required.","draft.",["14 author ","\n"]]
["W1788",[28658,28658,1574811,1574817],[28635,28635,1551400,1551407],"norm16","norm 16",["$c_*+b_*=12-8\\rho$ has "," and\n"]]
["W1789",[28697,28697,1576386,1576389],[28674,28674,1552976,1552980],"At3","At 3",[""," the reduction"]]
["W1790",[28703,28703,1576701,1576709],[28680,28680,1553292,1553301],"modulo3.","modulo 3.",["imaginary coefficient "," This proves"]]
["W1791",[28705,28705,1576751,1576755],[28682,28682,1553343,1553348],"At2,","At 2,",[""," $z(P)=(232+86\\rho)/357$ has"]]
["W1792",[28705,28705,1576794,1576805],[28682,28682,1553387,1553397],"valuations3","valuations",["has component "," and1.\n"]]
["W1793",[28705,28705,1576806,1576811],[28682,28682,1553398,1553406],"and1.","3 and 1.",["component valuations3 ","\n"]]
["W1794",[28711,28711,1577156,1577160],[28688,28688,1553751,1553756],"at2.","at 2.",["good reduction ","\n"]]
["W1795",[28724,28724,1577655,1577658],[28701,28701,1554251,1554255],"at2","at 2",["is integral ","\nand3. Its3-integrality"]]
["W1796",[28725,28725,1577659,1577664],[28702,28702,1554256,1554262],"and3.","and 3.",["integral at2\n"," Its3-integrality forces"]]
["W1797",[28728,28728,1577876,1577883],[28705,28705,1554474,1554482],"modulo3","modulo 3",["uses anisotropy "," and~\\eqref{eq:v14-X}.\nA"]]
["W1798",[28729,28729,1577959,1577970],[28706,28706,1554558,1554570],"are3-units,","are 3-units,",["Thus $X_A,X_T,X_Z$ ","\nso the"]]
["W1799",[28730,28730,1578018,1578030],[28707,28707,1554618,1554631],"is3-integral","is 3-integral",["Also $F_s/C$ ","\n"]]
["W1800",[28753,28753,1578994,1578997],[28730,28730,1555595,1555597],"at2","at",["$q$ integral "," and3 by"]]
["W1801",[28753,28753,1578998,1579002],[28730,28730,1555598,1555605],"and3","2 and 3",["integral at2 "," by\n"]]
["W1802",[28856,28856,1583039,1583052],[28833,28833,1559642,1559656],"periods4,8,16","periods 4,8,16",[""," before formality"]]
["W1803",[28872,28872,1583680,1583688],[28849,28849,1560284,1560293],"modulo16","modulo 16",["the classes "," are disjoint"]]
["W1804",[28894,28894,1584576,1584584],[28871,28871,1561181,1561184],"are157.5","are",["worst bounds "," and37.5; for"]]
["W1805",[28894,28894,1584585,1584593],[28871,28871,1561185,1561200],"and37.5;","157.5 and 37.5;",["bounds are157.5 "," for\n$\\alpha=3$"]]
["W1806",[28895,28895,1584614,1584622],[28872,28872,1561221,1561224],"are312.5","are",["$\\alpha=3$ they "," and72.5; for"]]
["W1807",[28895,28895,1584623,1584631],[28872,28872,1561225,1561240],"and72.5;","312.5 and 72.5;",["they are312.5 "," for $\\alpha\\geq5$"]]
["W1808",[28905,28905,1584933,1584953],[28882,28882,1561542,1561563],"respectively40,20,22","respectively 40,20,22",["these give "," for the"]]
["W1809",[28917,28917,1585574,1585581],[28894,28894,1562184,1562192],"order40","order 40",[""," test. A"]]
["W1810",[29102,29102,1593623,1593630],[29079,29079,1570234,1570242],"least10","least 10",["depth at "," for its"]]
["W1811",[29103,29103,1593709,1593716],[29080,29080,1570321,1570329],"least10","least 10",["depth at ","\n"]]
["W1812",[29107,29107,1593839,1593846],[29084,29084,1570452,1570460],"order40","order 40",["precedes the "," estimate. At"]]
["W1813",[29107,29107,1593860,1593867],[29084,29084,1570474,1570482],"depth10","depth 10",["estimate. At "," the\nrelative"]]
["W1814",[29108,29108,1593922,1593930],[29085,29085,1570537,1570546],"least40.","least 40.",["valuation at ","\nThe alternate"]]
["W1815",[29109,29109,1593960,1593967],[29086,29086,1570576,1570584],"order40","order 40",["estimates have "," for the"]]
["W1816",[29110,29110,1594005,1594012],[29087,29087,1570622,1570630],"order12","order 12",["approximants and "," for the"]]
["W1817",[29115,29115,1594327,1594335],[29092,29092,1570945,1570951],"orders10","orders",["their required "," or40.\n"]]
["W1818",[29115,29115,1594336,1594341],[29092,29092,1570952,1570961],"or40.","10 or 40.",["required orders10 ","\n"]]
["W1819",[29130,29130,1594788,1594796],[29107,29107,1571408,1571417],"modulo71","modulo 71",["unchanged certificates "," for $N$"]]
["W1820",[29130,29130,1594809,1594816],[29107,29107,1571430,1571438],"modulo7","modulo 7",["$N$ and "," for $Q$"]]
["W1821",[29143,29143,1595526,1595533],[29120,29120,1572148,1572156],"depth24","depth 24",["the scalar "," transfer\n"]]
["W1822",[29153,29153,1595993,1596000],[29130,29130,1572616,1572624],"depth19","depth 19",["Use its "," preparation.\nThe"]]
["W1823",[29154,29154,1596057,1596065],[29131,29131,1572681,1572690],"least20,","least 20,",["are at "," the high"]]
["W1824",[29155,29155,1596099,1596107],[29132,29132,1572724,1572733],"least40,","least 40,",["valuation at "," and the"]]
["W1825",[29156,29156,1596147,1596155],[29133,29133,1572773,1572782],"least12.","least 12.",["valuation at "," The fixed"]]
["W1826",[29160,29160,1596333,1596339],[29137,29137,1572960,1572967],"least1","least 1",["are at ","\nor2 and"]]
["W1827",[29161,29161,1596340,1596343],[29138,29138,1572968,1572972],"or2","or 2",["at least1\n"," and the"]]
["W1828",[29161,29161,1596378,1596384],[29138,29138,1573007,1573012],"least9","least",["valuations at "," or10. The"]]
["W1829",[29161,29161,1596385,1596390],[29138,29138,1573013,1573021],"or10.","9 or 10.",["at least9 "," The primary"]]
["W1830",[29162,29162,1596420,1596437],[29139,29139,1573051,1573069],"bounds159,3,83,76","bounds 159,3,83,76",["have lower "," in root"]]
["W1831",[29163,29163,1596473,1596480],[29140,29140,1573105,1573113],"bound8.","bound 8.",["has\nlower "," The alternate"]]
["W1832",[29248,29248,1600101,1600104],[29225,29225,1576734,1576738],"at2","at 2",["$t=T/C$ odd "," and integral"]]
["W1833",[29249,29249,1600118,1600122],[29226,29226,1576752,1576757],"at3.","at 3.",["and integral\n"," The retained"]]
["W1834",[29256,29256,1600426,1600429],[29233,29233,1577061,1577065],"At2","At 2",["bounds. "," take\n"]]
["W1835",[29261,29261,1600526,1600534],[29238,29238,1577162,1577168],"modulo8.","modulo",["is one "," At3 take"]]
["W1836",[29261,29261,1600535,1600538],[29238,29238,1577169,1577176],"At3","8. At 3",["one modulo8. "," take\n"]]
["W1837",[29266,29266,1600630,1600638],[29243,29243,1577268,1577274],"modulo3.","modulo",["is one "," At17 take"]]
["W1838",[29266,29266,1600639,1600643],[29243,29243,1577275,1577283],"At17","3. At 17",["one modulo3. "," take\n"]]
["W1839",[29272,29272,1600787,1600796],[29249,29249,1577427,1577437],"modulo17.","modulo 17.",["is one "," Each construction"]]
["W1840",[29280,29280,1601120,1601123],[29257,29257,1577761,1577765],"if3","if 3",["product "," is a"]]
["W1841",[29405,29405,1606488,1606496],[29382,29382,1583130,1583139],"count326","count 326",["above. The "," replaces\n"]]
["W1842",[29408,29408,1606631,1606639],[29385,29385,1583274,1583283],"count315","count 315",["directly. The "," precedes common"]]
["W1843",[29410,29410,1606776,1606786],[29387,29387,1583420,1583431],"giving314.","giving 314.",["test coordinates, ","\n"]]
["W1844",[29412,29412,1606847,1606857],[29389,29389,1583492,1583503],"giving313.","giving 313.",[""," Reciprocal A,"]]
["W1845",[29412,29412,1606892,1606900],[29389,29389,1583538,1583547],"give307,","give 307,",["root charts ","\nalternate-ordinate elimination"]]
["W1846",[29413,29413,1606932,1606941],[29390,29390,1583579,1583589],"gives301,","gives 301,",["alternate-ordinate elimination "," and the"]]
["W1847",[29414,29414,1606982,1606991],[29391,29391,1583630,1583640],"gives299.","gives 299.",["auxiliary chart ","\n"]]
["W1848",[29418,29418,1607118,1607124],[29395,29395,1583767,1583774],"has279","has 279",["final system "," quadratic component"]]
["W1849",[29419,29419,1607155,1607160],[29396,29396,1583805,1583811],"in299","in 299",["component\nequations "," active rational"]]
["W1850",[29423,29423,1607417,1607426],[29400,29400,1584068,1584078],"give6,630","give 6,630",["zero coefficients "," monomials,\n"]]
["W1851",[29443,29443,1608150,1608160],[29420,29420,1584802,1584813],"eleven2048","eleven 2048",["After the "," steps $e_{11}=2^{23}$,"]]
["W1852",[29473,29473,1609141,1609148],[29450,29450,1585794,1585802],"of1,514","of 1,514",[""," bits. The"]]
["W1853",[29481,29481,1609415,1609425],[29458,29458,1586069,1586080],"has222,890","has 222,890",["identifiers and "," bytes. A"]]
["W1854",[29563,29563,1618691,1618691],[29540,29542,1595346,1595521],"","The inverse-theorem derivation uses polynomial maps on $\\mathbb Z$.\nThe clauses below concerning limit polynomial maps and limit functions\nare not invoked by this derivation.\n",["",""]]
["W1855",[29601,29604,1620484,1620770],[29581,29581,1597314,1597314],"% Standalone proposal for insertion after the unchanged GI target.\n% This fragment changes no manuscript.  The integrator supplies the bibliography\n% keys cs2022, candela2017compact, candela2017algebraic, and v15-gi-14-GTZ.\n% It invokes the retained local theorem v15:gi:14:thm:linear.\n","",["",""]]
["W1856",[29610,29610,1620911,1620924],[29586,29586,1597455,1597479],"\\cite{cs2022}","\\cite{cs2022}, published",[""," in the"]]
["W1857",[29610,29610,1620928,1620931],[29586,29586,1597483,1597489],"the","Crelle",["\\cite{cs2022} in "," 39-page author"]]
["W1858",[29610,29610,1620932,1620939],[29586,29586,1597490,1597502],"39-page","\\textbf{789}",["in the "," author version"]]
["W1859",[29610,29610,1620940,1620946],[29586,29586,1597503,1597510],"author","(2022),",["the 39-page "," version\n\\texttt{arXiv:1902.01098v3},"]]
["W1860",[29610,29610,1620947,1620954],[29586,29586,1597511,1597517],"version","1--42.",["39-page author ","\n\\texttt{arXiv:1902.01098v3}, dated"]]
["W1861",[29611,29613,1620955,1621108],[29587,29587,1597518,1597518],"\\texttt{arXiv:1902.01098v3}, dated 13 March 2022.  The arXiv record\nidentifies this as the final version to appear, with referee comments\nincorporated.  ","",["author version\n","All page "]]
["W1862",[29613,29613,1621117,1621124],[29587,29587,1597527,1597537],"numbers","references",["All page "," for that"]]
["W1863",[29613,29613,1621125,1621128],[29587,29587,1597538,1597540],"for","to",["page numbers "," that source"]]
["W1864",[29613,29616,1621156,1621313],[29587,29587,1597568,1597568],"this\nauthor version.  The 42-page Crelle version of record has not been\nobtained for comparison; no identity of its pagination or individual\nstatements with ","",["refer to ","the author "]]
["W1865",[29616,29616,1621317,1621323],[29587,29587,1597572,1597579],"author","journal",["with the "," version is"]]
["W1866",[29616,29616,1621324,1621349],[29587,29587,1597580,1597588],"version is asserted here.","edition.",["the author ","\n"]]
["W1867",[29619,29619,1621534,1621534],[29590,29590,1597773,1597783],"","on page~5 ",["Theorem 1.7 ","alone.\n"]]
["W1868",[29629,29629,1622076,1622080],[29600,29600,1598325,1598331],"(5),","(6.1),",["\\cite[\\S6, equation "," pp.~26--27]{cs2022}.\n"]]
["W1869",[29629,29629,1622081,1622101],[29600,29600,1598332,1598347],"pp.~26--27]{cs2022}.","p.~29]{cs2022}.",["equation (5), ","\n"]]
["W1870",[29644,29644,1622923,1622938],[29615,29615,1599169,1599184],"p.~23]{cs2022}.","p.~25]{cs2022}.",["\\cite[Definition 5.1, ","\n"]]
["W1871",[29671,29671,1623898,1623912],[29642,29642,1600144,1600158],"p.~27]{cs2022}","p.~29]{cs2022}",["\\cite[Theorem 6.1, "," at complexity"]]
["W1872",[29681,29681,1624334,1624354],[29652,29652,1600580,1600600],"\\cite[p.~26]{cs2022}","\\cite[p.~28]{cs2022}",["5.2 of "," allows this"]]
["W1873",[29838,29838,1631801,1631815],[29809,29809,1608047,1608061],"p.~27]{cs2022}","p.~30]{cs2022}",["\\cite[Proposition 6.3, "," to the"]]
["W1874",[29842,29842,1632031,1632045],[29813,29813,1608277,1608291],"p.~34]{cs2022}","p.~36]{cs2022}",["\\cite[Lemma A.5, "," writes it"]]
["W1875",[30011,30012,1638652,1638712],[29982,29982,1614898,1614906],"theorem, with the source-version\nqualification stated above.","theorem.",["same-step linearization ","  It does"]]
["W1876",[33005,33005,1780391,1780398],[32975,32975,1756585,1756593],"row491,","row 491,",["source "," let $K$"]]
["W1877",[33005,33005,1780442,1780449],[32975,32975,1756637,1756645],"row499,","row 499,",["b$ in ","\nand let"]]
["W1878",[33006,33006,1780500,1780507],[32976,32976,1756696,1756704],"row494.","row 494.",["p^2$ in "," The exact"]]
["W1879",[33673,33673,1814805,1814828],[33643,33643,1791002,1791002]," independently accepted","",[" is the"," composition in"]]
["W1880",[33682,33682,1816873,1817002],[33652,33652,1793047,1793047]," Its independent review is identified by the prefix \\texttt{07f3b18c}; the complete receipt is included in the delivery evidence.","",[" the input.","\n"]]
["W1881",[33984,33984,1830298,1830303],[33954,33954,1806343,1806349],"is87.","is 87.",["raw row "," For every"]]
["W1882",[33984,33984,1830465,1830476],[33954,33954,1806511,1806523],"deletion87.","deletion 87.",["apart from ","\n"]]
["W1883",[37545,37545,1956290,1956296],[37515,37515,1932337,1932344],"raw233","raw 233",["the corrected ","\n"]]
["W1884",[37554,37554,1956662,1956670],[37524,37524,1932710,1932719],"other205","other 205",["The "," equations retain"]]
["W1885",[37554,37554,1956704,1956713],[37524,37524,1932753,1932763],"giving232","giving 232",["their meanings, "," coordinates\nand206"]]
["W1886",[37555,37555,1956726,1956732],[37525,37525,1932776,1932783],"and206","and 206",["giving232 coordinates\n"," quadratic equations."]]
["W1887",[37559,37559,1956884,1956889],[37529,37529,1932935,1932941],"At149","At 149",["$A/(1+149^2)\\le R<A/149^2$. "," the four"]]
["W1888",[37565,37565,1957290,1957299],[37535,37535,1933342,1933352],"forced149","forced 149",["gives the "," depth\n"]]
["W1889",[37570,37570,1957486,1957491],[37540,37540,1933539,1933545],"and32","and 32",[""," are units"]]
["W1890",[37578,37578,1957900,1957912],[37548,37548,1933954,1933967],"squarefree51","squarefree 51",["and the "," denominator\n"]]
["W1891",[37582,37582,1958067,1958075],[37552,37552,1934122,1934131],"Modulo3,","Modulo 3,",["$v_2(r_4)\\in\\{2,3\\}$. "," $r_4=1$ and"]]
["W1892",[37583,37583,1958104,1958113],[37553,37553,1934160,1934170],"modulo17,","modulo 17,",["and $1+149^2r_4=2$;\n"," $r_4=13$ and"]]
["W1893",[37608,37608,1959442,1959452],[37578,37578,1935499,1935510],"version18,","version 18,",["\\emph{Fixed-difference charts}, "," public revision"]]
["W1894",[37611,37611,1959641,1959650],[37581,37581,1935699,1935709],"scalar149","scalar 149",["from the "," argument; no"]]
["W1895",[37614,37614,1959722,1959728],[37584,37584,1935781,1935788],"raw232","raw 232",["In "," coordinates write"]]
["W1896",[37639,37639,1960522,1960530],[37609,37609,1936582,1936591],"prime149","prime 149",["the inert "," the unchanged"]]
["W1897",[37651,37651,1961099,1961105],[37621,37621,1937160,1937163],"raw232","raw",["directly. Delete "," slots21--28,\n"]]
["W1898",[37651,37651,1961106,1961118],[37621,37621,1937164,1937181],"slots21--28,","232 slots 21--28,",["Delete raw232 ","\n"]]
["W1899",[37653,37653,1961184,1961192],[37623,37623,1937247,1937256],"gives226","gives 226",["This "," coordinates and200"]]
["W1900",[37653,37653,1961205,1961211],[37623,37623,1937269,1937276],"and200","and 200",["gives226 coordinates "," equations.\n"]]
["W1901",[37753,37753,1967956,1967965],[37723,37723,1944021,1944031],"scalar149","scalar 149",["The unchanged "," argument gives"]]
["W1902",[37763,37763,1968441,1968457],[37733,37733,1944507,1944524],"are149-integral,","are 149-integral,",["All coefficients "," and the"]]
["W1903",[37771,37771,1968962,1968968],[37741,37741,1945029,1945032],"raw226","raw",["Delete "," slots126,127 and"]]
["W1904",[37771,37771,1968969,1968981],[37741,37741,1945033,1945050],"slots126,127","226 slots 126,127",["Delete raw226 "," and compact."]]
["W1905",[37771,37771,1969000,1969008],[37741,37741,1945069,1945078],"gives224","gives 224",["compact. This "," coordinates and198"]]
["W1906",[37771,37771,1969021,1969027],[37741,37741,1945091,1945098],"and198","and 198",["gives224 coordinates ","\n"]]
["W1907",[37773,37773,1969111,1969117],[37743,37743,1945182,1945189],"raw224","raw 224",["branches. In "," the actual"]]
["W1908",[37781,37781,1969406,1969413],[37751,37751,1945478,1945486],"raw224.","raw 224.",["refer to "," Set\n"]]
["W1909",[37787,37787,1969753,1969761],[37757,37757,1945826,1945835],"Modulo5,","Modulo 5,",["$(1+q)P_5(r)=r^5$, $r=(t-1)^2$. ","\n$P_5(r)=(r-1)^2(r-4)^3$. If"]]
["W1910",[37788,37788,1969804,1969817],[37758,37758,1945878,1945892],"is5-integral,","is 5-integral,",["and $t$ "," the square"]]
["W1911",[37790,37790,1969906,1969913],[37760,37760,1945981,1945989],"degree4","degree 4",["$P_5(r)-r^5$ has "," and unit"]]
["W1912",[37793,37793,1970019,1970042],[37763,37763,1946095,1946119],"slots62,63,66,67,68,69.","slots 62,63,66,67,68,69.",["Delete "," For each"]]
["W1913",[37805,37805,1970401,1970413],[37775,37775,1946478,1946491],"\\text{raw224","\\text{raw 224",[""," slots}&\\text{new value}\\\\\\hline"]]
["W1914",[37823,37823,1971194,1971202],[37793,37793,1947272,1947281],"factor2,","factor 2,",["only in ","\n"]]
["W1915",[37827,37827,1971259,1971272],[37797,37797,1947338,1947352],"factors1,2,4,","factors 1,2,4,",["this to "," retaining the"]]
["W1916",[37840,37840,1971872,1971885],[37810,37810,1947952,1947966],"coefficient2.","coefficient 2.",["pairs with "," The new"]]
["W1917",[37843,37843,1972063,1972069],[37813,37813,1948144,1948151],"are223","are 223",["There "," coordinates and197"]]
["W1918",[37843,37843,1972082,1972088],[37813,37813,1948164,1948171],"and197","and 197",["are223 coordinates "," quadrics. No"]]
["W1919",[37847,37847,1972222,1972228],[37817,37817,1948305,1948312],"raw223","raw 223",["In "," the only"]]
["W1920",[37859,37859,1972751,1972757],[37829,37829,1948835,1948840],"slots1","slots",["inverted. Keep "," through221\nand"]]
["W1921",[37859,37859,1972758,1972768],[37829,37829,1948841,1948854],"through221","1 through 221",["Keep slots1 ","\nand number"]]
["W1922",[37860,37860,1972786,1972792],[37830,37830,1948872,1948879],"as222.","as 222.",["number $U_*$ "," This proves222"]]
["W1923",[37860,37860,1972798,1972807],[37830,37830,1948885,1948895],"proves222","proves 222",["as222. This "," variables and196"]]
["W1924",[37860,37860,1972818,1972824],[37830,37830,1948906,1948913],"and196","and 196",["proves222 variables "," quadrics with"]]
["W1925",[37865,37865,1973074,1973080],[37835,37835,1949163,1949170],"raw223","raw 223",["substitutions use "," indices and"]]
["W1926",[37866,37866,1973154,1973169],[37836,37836,1949244,1949260],"slots222,223,98","slots 222,223,98",["not touch ","\nor119, so"]]
["W1927",[37867,37867,1973170,1973176],[37837,37837,1949261,1949268],"or119,","or 119,",["touch slots222,223,98\n"," so commute"]]
["W1928",[37966,37966,1978289,1978295],[37936,37936,1954381,1954388],"row124","row 124",["Then replace "," by $3Q_{124}+11Q_{125}$,"]]
["W1929",[37966,37966,1978329,1978335],[37936,37936,1954422,1954429],"row125","row 125",["$3Q_{124}+11Q_{125}$, leaving "," fixed;\nthe"]]
["W1930",[37967,37967,1978389,1978393],[37937,37937,1954483,1954488],"by3.","by 3.",["and divides "," The common"]]
["W1931",[37968,37968,1978429,1978436],[37938,37938,1954524,1954532],"row186,","row 186,",["removes former "," and all"]]
["W1932",[37978,37978,1978899,1978904],[37948,37948,1954995,1955001],"are2;","are 2;",["Unlisted weights "," the exceptions"]]
["W1933",[37987,37987,1979078,1979084],[37957,37957,1955175,1955182],"to428.","to 428.",["weights sum "," Thus this"]]
["W1934",[37987,37987,1979109,1979114],[37957,37957,1955207,1955213],"of428","of 428",["a sum "," repeated squares,"]]
["W1935",[37988,37988,1979133,1979139],[37958,37958,1955232,1955239],"not196","not 196",["repeated squares,\n"," unit-weight squares."]]
["W1936",[39539,39539,2021603,2021609],[39509,39509,1997703,1997710],"the196","the 196",["Expanding "," weighted squares"]]
["W1937",[39539,39539,2021627,2021636],[39509,39509,1997728,1997738],"gives2277","gives 2277",["weighted squares "," coordinate monomials,"]]
["W1938",[39540,39540,2021659,2021665],[39510,39510,1997761,1997768],"or2278","or 2278",["coordinate monomials,\n"," terms if"]]
["W1939",[39541,39541,2021767,2021773],[39511,39511,1997870,1997877],"all222","all 222",["one, and "," coordinates occur."]]
["W1940",[39544,39544,2021947,2021957],[39514,39514,1998051,1998062],"most44402;","most 44402;",[""," every parameter-free"]]
["W1941",[39550,39550,2022318,2022337],[39520,39520,1998423,1998443],"decimal314-variable","decimal 314-variable",["full ordinary "," example and"]]
["W1942",[39552,39552,2022446,2022452],[39522,39522,1998552,1998559],"The222","The 222",["family. "," construction does"]]
["W1943",[39692,39692,2029581,2029652],[39662,39662,2005688,2005688],"The adjacent Baba--Granath product-map finding is preserved separately.","",["","\n"]]
["W1944",[39969,39969,2045112,2045117],[39939,39939,2021148,2021153],"Exact","Proof",["version 1. "," proof, explicit"]]
["W1945",[39969,39969,2045118,2045124],[39939,39939,2021154,2021157],"proof,","and",["1. Exact "," explicit retained"]]
["W1946",[39969,39969,2045150,2045169],[39939,39939,2021183,2021183],"and bounded review ","",["retained inputs ","at\n"]]
["W1947",[40149,40149,2055155,2055163],[40119,40119,2031169,2031174],"Authored","Proof",["version 1. "," proof, supporting"]]
["W1948",[40149,40149,2055164,2055170],[40119,40119,2031175,2031178],"proof,","and",["1. Authored "," supporting sources"]]
["W1949",[40149,40150,2055190,2055217],[40119,40119,2031198,2031198],"and bounded\nreview records ","",["supporting sources ","at\n"]]
["W1950",[40156,40156,2055529,2055544],[40125,40125,2031510,2031528],"qualifications,","qualifications and",["Exact source "," integral proof"]]
["W1951",[40156,40157,2055560,2055591],[40125,40125,2031544,2031544],"and bounded\nindependent review ","",["integral proof ","at\n"]]
["W1952",[40163,40163,2055880,2055886],[40131,40131,2031833,2031842],"Proof,","Proof and",["version 1. "," exact source"]]
["W1953",[40163,40163,2055915,2055934],[40131,40131,2031871,2031871],"and bounded review ","",["source qualifications ","at\n"]]
["W1954",[40172,40172,2056627,2056630],[40140,40140,2032564,2032568],"and","with",["\\href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/cj-good-reduction-v1/README.md}{proof "," independent scoped"]]
["W1955",[40172,40172,2056631,2056642],[40140,40140,2032569,2032572],"independent","its",["\\href{https://github.com/elliotglazer/diophantine-z-q/blob/main/research/version14/proofs/cj-good-reduction-v1/README.md}{proof and "," scoped review}."]]
["W1956",[40172,40172,2056643,2056649],[40140,40140,2032573,2032579],"scoped","stated",["and independent "," review}.\n"]]
["W1957",[40172,40172,2056650,2056658],[40140,40140,2032580,2032592],"review}.","hypotheses}.",["independent scoped ","\n"]]
["W1958",[40285,40285,2061061,2061120],[40253,40253,2036995,2036997],"The text and page locators used here are those of the final","An",[""," author version,"]]
["W1959",[40285,40285,2061128,2061137],[40253,40253,2037005,2037029],"version,\n","version is available as ",["final author ","arXiv:1902.01098v3, 13 "]]
["W1960",[40286,40286,2061171,2061181],[40253,40253,2037063,2037063]," 39 pages,","",[" March 2022,","\n"]]
["W1961",[40288,40288,2061224,2061275],[40255,40255,2037106,2037106],"The 42-page journal edition has not been compared.\n","",["",""]]
["W1962",[40308,40308,2062186,2062210],[40274,40274,2038017,2038017]," and internally reviewed","",[" were developed"," by separate"]]
["W1963",[40308,40308,2062288,2062291],[40274,40274,2038095,2038098],"its","the",["those arguments; "," companion audit"]]
["W1964",[40308,40308,2062323,2062332],[40274,40274,2038130,2038142],"versions,","versions and",["records source "," equation generation,"]]
["W1965",[40308,40308,2062342,2062542],[40274,40274,2038152,2038163],"generation, and subsequent review separately. Internal model review is not independent human peer review or formal verification. The earlier complete development follows with its provenance preserved.","generation.",["versions, equation ","\n"]]
["W1966",[40310,40310,2062912,2062939],[40276,40276,2038533,2038533],"and independently reviewed ","",["agents authored ","the scalar-S "]]
["W1967",[40310,40310,2063124,2063216],[40276,40276,2038718,2038718],"These are internal model reviews, not independent human peer review or formal verification. ","",["Glazer's direction. ","The companion "]]
["W1968",[40310,40310,2063305,2063343],[40276,40276,2038807,2038807]," Earlier provenance follows unchanged.","",[" transformation provenance.","\n"]]
```

## Exact historical coverage dispositions

These are transcripts of the selected project-review fields returned by GitHub, with original comment IDs. They preserve scope and opposing dispositions, not new reviewer execution or approval. The complete original reports remain at their links.

### Comment 6887128932

[Original report](https://github.com/elliotglazer/diophantine-z-q/pull/107#issuecomment-6887128932), fetched November 15, 2026.

```json
{
  "reviewer": "fable",
  "model": "claude-fable-5-2",
  "head": "9b34ffb9902f8a0086e5f2efa434bb6076e4eda5",
  "run": "43661223026",
  "attempt": "1",
  "complete": true,
  "decision": "changes_requested",
  "coverage_findings": [
    {
      "id": "F107-1",
      "location": "docs/research-review/version18-citation-cleanup.md (second table and the 'global-sign paragraph' row); manuscripts/quartic_v18.tex, whole-file diff (874 additions / 830 deletions over 45,516 lines)",
      "objection": "The changed scope cannot be located or fully read. Twelve changed source applications and the Atkin–Lehner global-sign/odd-twist paragraph have no line locators, and about 850 scattered changed lines are asserted, not shown, to be prose-only with byte-identical statements and labels. The reviewer tools give no diff or text search and the file cannot be read twice within the allowance, so the claim that no mathematics changed is unverified. Requested: head line ranges for every changed source application; a committed hunk manifest or diff classifying each hunk (citation-only, new derivation, notation repair, prose, status-wording removal); preferably a split into (A) source applications and derivations, (B) prose/typesetting only with the statement/label identity check as a CI artifact, (C) status-wording changes."
    },
    {
      "id": "F107-3",
      "location": "manuscripts/quartic_v18.tex: base abstract 78–79 vs head 77–79; base 2229 and 2234–2236 vs head 2224–2233; base bibitems 45426–45428 and 45436–45439 vs head 45449 and 45457; base 45458 and 45460 vs head 45502 and 45504",
      "objection": "The cleanup removes current review-status qualifiers without disclosing it, while the PR body and note say qualifications are preserved. Removed: the abstract sentence that the manuscript is an author proposal for fresh review conferring no acceptance; 'Author argument only; fresh non-author acceptance is required' at the P01 section; 'Pending independent review' on the local Lemma 13.2 bibliography entry; the independent-scope-decision reference on the tautification entry; the internal-model-review-only statements in the provenance sections. The abstract still says 'proposed' and the AI-usage statement remains, but the item-level argued/reviewed distinction for load-bearing local proofs no longer appears and the note does not say where it now lives. Requested: restore these, or add one consolidated status paragraph naming the repository record that carries each state, and enumerate every removed status sentence in the delta note. Further instances may exist in unread hunks."
    }
  ],
  "prior_findings": [],
  "limitations": [
    "All changed hunks of manuscripts/quartic_v18.tex outside the head line ranges listed in sources_read (the bulk of the 874/830-line change)",
    "The Atkin–Lehner global-sign (weight-two Mellin) and successive-Legendre-twist paragraph: not located",
    "Nekovář Cor. 8.4.8.2(i), p. 215, and its erratum status: source not obtained (argument checked, citation not)",
    "Atkin–Lehner 1970, Lemmas 8, 9, Theorem 3(iii), Lemma 33(iii), Theorem 6: source not obtained",
    "Guillot 2018, Lemma 1.20 and Theorem 1.22: source not obtained",
    "Cox 1989, §§7 and 9, Prop. 7.22, proof of Thm 7.24, Lemma 9.3: source not obtained",
    "All second-table applications in the delta note: Milne (Abelian varieties §16, Prop. 12.9), Silverman Ex. III.3.7 with 2015 correction, Deligne–Serre §§1.6–1.9, Allen–Newton–Thorne Prop. 3.1 for the Pan inputs, Serre LCFT §2.4, Silverman VII.2.1–2.2 with Lang 1956, Milne ADT I.1.6(b)/II.2.1, Rémond 2017 Thm 1.6, Chaiken 1982, the 15,845-call precision-circuit traversal, the maximal-stack height comparison and Gross–Zagier key change",
    "The claim that every theorem/proposition/lemma/corollary/definition environment and every label is byte-identical to the PR98 text",
    "The P01 blob-identity and 214-coordinate/188-residual/1,008-term parser claims",
    "The seventeen archive-link byte-identity claims, the LaTeX build and the PDF hash",
    "Whether the local GI proof is unchanged",
    "All unchanged foundations of Versions 16–18 (outside this change's scope; not re-audited)"
  ]
}
```

### Comment 6887374746

[Original report](https://github.com/elliotglazer/diophantine-z-q/pull/107#issuecomment-6887374746), fetched November 15, 2026.

```json
{
  "reviewer": "astra",
  "model": "gpt-6-astra",
  "head": "ba146eb06920da043037b60b45d1ec2d73f7a7a3",
  "run": "43663199880",
  "attempt": "1",
  "complete": true,
  "decision": "changes_requested",
  "coverage_findings": [],
  "prior_findings": [
    {
      "id": "43661223026-1-astra-C107",
      "resolution": "unresolved",
      "reason": "The 213-hunk map and source locators improve reviewability, and selected base/head arguments plus preserved PR98 observations were inspected. Complete changed-scope coverage, artifact/link identity, the actual nonnegative power-call-argument check, and remaining history/source checks were not completed. The large circuit read and final manuscript reads were rejected and are not inspected evidence. This remains a review-completion blocker, not a mathematical counterexample."
    },
    {
      "id": "43661223026-1-fable-F107-1",
      "resolution": "resolved",
      "reason": "Resolved as the navigation/locator defect: the committed change-map index at lines 1–222 provides paired base/head ranges for H001–H213, and the cleanup note at lines 13–40 locates the source applications, including the global-sign paragraph. These records were read and used to inspect selected current and base passages. Exhaustive diff coverage and mathematical classification are not inferred from this resolution; they remain explicitly unresolved under C107."
    },
    {
      "id": "43661223026-1-fable-F107-3",
      "resolution": "unresolved",
      "reason": "The disclosure defect is substantially repaired by cleanup-note lines 74–91 and the 70-block status index. The inspected abstract, P01, bibliography and provenance changes confirm the stated removals. The requested manuscript-level consolidated pointer to the continuing component/assembly status is not present at the inspected locations, and the remaining status blocks have not been compared. Pending review is not resolved merely by relocating or deleting its wording."
    }
  ],
  "limitations": [
    "Complete PR107 base-to-head change and its incorporation; only the expressly described manuscript-level implications were checked here.",
    "Changed published-theorem applications whose final statements, hypotheses, normalizations or relevant corrections were not fully compared, including the unresolved S107 and F107-2 scope.",
    "The new nonnegative power-call-argument assertion on the actual frozen precision circuit and its computational certificate.",
    "All uninspected prose/status hunks, artifact identities, archival links and historical-report completeness checks covered by C107.",
    "Pending 214-variable assembly, uniform existence, geometry/modularity carries, height/aggregate joins, mean-two/LP13 and tautification review states retained in the cleanup note; no new status is conferred by this edit.",
    "Inherited final-Pan and final-2022-Rémond source-version limitations; no new acceptance of those steps.",
    "Version 18 source/PDF correspondence, record-release readiness, the complete arithmetic theorem, and any numerical defining member."
  ]
}
```

### Comment 6887409411

[Original report](https://github.com/elliotglazer/diophantine-z-q/pull/107#issuecomment-6887409411), fetched November 15, 2026.

```json
{
  "reviewer": "fable",
  "model": "claude-fable-5-2",
  "head": "ba146eb06920da043037b60b45d1ec2d73f7a7a3",
  "run": "43663199880",
  "attempt": "1",
  "complete": true,
  "decision": "changes_requested",
  "coverage_findings": [
    {
      "id": "N107-2",
      "location": "manuscripts/quartic_v18.tex base 33724–33729 vs head 33746–33747 (H170); status index row H170 in version18-citation-cleanup.md",
      "objection": "The base text said that other current copies of the smaller-domain frequency claim or the illustrative filtration must be corrected or marked historical when the proof is incorporated, and pointed to an occurrence record. The head replaces this with a general remark that the integral-extension argument is needed wherever those claims are used. The index describes the block as a removed historical qualification. It was an open incorporation obligation. Neither the manuscript nor the note shows that the listed copies were corrected, or carries the obligation forward. State where each copy was corrected, with locations, or keep the obligation in the status record."
    }
  ],
  "prior_findings": [
    {
      "id": "43661223026-1-astra-C107",
      "resolution": "unresolved",
      "reason": "Coverage is still incomplete. Done in this round: the Atkin–Lehner, Montgomery–Vaughan and Cox comparisons, the five short arguments, and a both-sides sample of ten status blocks. The power-call assertion was examined and has no committed evidence (N107-1). Not done before the context allowance ran out: the full base-to-head comparison of the remaining blocks, the statement/label/display identity check, artifact and link identity, and most second-table sources. The report lists the remaining scope and a three-way split."
    },
    {
      "id": "43661223026-1-fable-F107-1",
      "resolution": "unresolved",
      "reason": "The locating half is repaired: the note gives head ranges for every source application, and the change map gives base and head ranges for all 213 blocks. I used them and found them accurate where tested. The reading half is not: the Part I blocks are long single-line paragraphs, and the full two-sided comparison plus about twenty external sources does not fit one standard-budget review. The requested split, or a committed CI identity check for the prose-only class, was not provided. The claim that no mathematics changed outside the source applications remains unverified for the unread blocks."
    },
    {
      "id": "43661223026-1-fable-F107-3",
      "resolution": "resolved",
      "reason": "The removal is now disclosed in the PR description. The note's section 'Review status moved out of the exposition' carries the assembly, component, GI, source-access and no-human-review limits and indexes 70 status blocks by base and head lines. Across the ten blocks I compared on both sides, plus the head P01 and closing sections, the manuscript keeps 'proposed' in the abstract and theorem, the 'Subject to…' condition in P01 and the AI-review disclaimer, and no pending item is restated as established. One indexed block (H170) removed an obligation, not a qualifier; that is raised separately as N107-2. Verification of the remaining indexed blocks falls under the coverage findings."
    }
  ],
  "limitations": [
    "The Version 18 214-variable assembly as a whole, its uniform-existence, height, modularity and aggregate applications, and every inherited component: unchanged by this review and not accepted by it",
    "Local control at two: application of Nekovář Corollary 8.4.8.2(i), p. 215, and Kato (12.2.3) — the derivation was checked, the published statements were not read",
    "Kummer pairing application of Guillot Lemma 1.20 and Theorem 1.22",
    "Allen–Newton–Thorne §3.1/Proposition 3.1 paragraph and the project local-ring supplements (head 5788–5797)",
    "Locator-only citations not opened: Milne 1986 §16 and Proposition 12.9; Milne ADT I.1.6(b) and II.2.1; Serre §2.4 p. 141; Silverman Exercise III.3.7 with 2015 errata and VII.2.1–2.2; Lang 1956; Rémond 2017 Theorem 1.6; Chaiken 1982; Waldspurger Propositions 17–18 and Lemma 41; Deligne Variante 4.8; Gross–Zagier 1985",
    "The natural-valued power-call-argument assertion at head 12245–12247 (N107-1)",
    "All changed blocks not compared on both sides, including the prose/notation class and the status blocks listed under 'Not reviewed'",
    "Statement/label/display identity, archive-link identity, P01 row-parser identity and build claims",
    "The local GI proof units (mean-two join, LP13, tautification, plain quadruples, converse): status unchanged, argued only for this draft"
  ]
}
```

