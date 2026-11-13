"""period-map: exact multiplier of G8 = S/dF^4: chi(g) = G8(g t) det(g)^4 / ((c t + d)^8 G8(t)) (complex), several g in Gamma*.
Run: ~/pyenv/bin/python -I multiplier.py"""
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'al_weight.py')).read().split("print(\"check iota")[0]
exec(src)
dF = lambda t: (t-3)*(t+1)
G8 = lambda t: SP(t)[0]/dF(t)**4
for name, x in {"(1+j)/2": (R(1,2),0,R(1,2),0), "j": (0,0,1,0), "i+j": (0,1,1,0), "3+2i": (3,2,0,0), "mu": (0,0,2,1), "1+i+j": (1,1,1,0), "2+i": (2,1,0,0)}.items():
    a,b,c,d = mob(x); det = a*d-b*c
    for t in [mp.mpc('0.3','1.1'), mp.mpc('-0.7','0.9')]:
        gt = (a*t+b)/(c*t+d)
        print(f"{name}: t={mp.nstr(t,3)} chi = {mp.nstr(G8(gt)*det**4/((c*t+d)**8*G8(t)), 12)}")
