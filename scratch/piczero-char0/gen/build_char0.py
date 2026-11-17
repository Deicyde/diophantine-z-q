"""piczero-char0: writes ZInQKernel/Contrib/OneProof/PicZeroAbVarCharZero.lean (the characteristic-0 forms of
picZeroAbVar and of its consumers' statements, proved).  Proof bodies are copied verbatim from the cited files."""
import re, sys
OUT = sys.argv[1]
def L(f): return open(f).read().split("\n")
def block(f, start_pat, stop_pat=None, n=None):
    ls = L(f)
    i = next(k for k, l in enumerate(ls) if re.match(start_pat, l))
    j = i + 1
    while j < len(ls) and not (ls[j].strip() == "" and (j + 1 >= len(ls) or not ls[j + 1].startswith(" "))):
        j += 1
    return "\n".join(ls[i:j])
PS = "scratch/piczero-char0/gen/PicZeroSmoothCartier.pic-smooth.lean"
ps = L(PS)
# pic-smooth lines 35..142 (At-statements, picZeroAbVarAt_of, Cartier part) verbatim
ps_body = "\n".join(ps[33:142])
assert "picZeroAbVarAt_charZero_of_cartier" in ps_body and "PicZeroSmoothPosChar" not in ps_body
MK = "ZInQKernel/Contrib/OneProof/MumfordKLFinite.lean"
kl = block(MK, r"^theorem mumfordKLFiniteAC_of_open ")
kl_body = kl.split(":= by\n", 1)[1]
kl_body = kl_body.replace("  intro k _ _ X c₀ hc₀\n", "  intro k _ _ _ X c₀ hc₀\n", 1)
assert "intro k _ _ _ X c₀ hc₀" in kl_body
PA = "ZInQKernel/Contrib/OneProof/PhiAmpleIsogeny.lean"
sec = block(PA, r"^theorem mumfordKLFiniteAC_of_section ")
sec_body = sec.split(":= by\n", 1)[1].replace("  intro k _ _ X c₀ hc₀\n", "  intro k _ _ _ X c₀ hc₀\n", 1)
assert "intro k _ _ _ X" in sec_body
PD = "ZInQKernel/Contrib/OneProof/PicDictionary.lean"
ac = block(PD, r"^theorem mumfordKLFinite_of_ac ")
ac_body = ac.split(":= by\n", 1)[1].replace("  intro K _ A c₀ hc₀\n", "  intro K _ _ A c₀ hc₀\n", 1)
assert "intro K _ _ A" in ac_body
pr = block(PD, r"^theorem phiAmpleIsogeny_of_printed ")
pr_body = pr.split(":= by\n", 1)[1].replace("  intro K _ A P rep B j hj L hL lam hlam\n", "  intro K _ _ A P rep B j hj L hL lam hlam\n", 1)
assert "intro K _ _ A P" in pr_body
PC = "ZInQKernel/Contrib/OneProof/PoincareComplement.lean"
psi = block(PC, r"^theorem exists_psi ")
psi_body = psi.split(":= by\n", 1)[1]
T24 = "ZInQKernel/OneProof/H/TailZ24.lean"
t9l = block(T24, r"^theorem t09SymmIsogenyExists_of_leaves ")
t9l_body = t9l.split(":= by\n", 1)[1].replace("  intro K _ A\n", "  intro K _ _ A\n", 1)
assert "intro K _ _ A" in t9l_body

src = open("scratch/piczero-char0/gen/char0_template.lean").read()
for k, v in {"@PS_BODY@": ps_body, "@KL_BODY@": kl_body, "@SEC_BODY@": sec_body, "@AC_BODY@": ac_body,
             "@PR_BODY@": pr_body, "@PSI_BODY@": psi_body, "@T9L_BODY@": t9l_body}.items():
    assert k in src, k
    src = src.replace(k, v)
open(OUT, "w").write(src)
print("wrote", OUT)
