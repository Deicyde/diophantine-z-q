exec(open('cusps.py').read().split("for name")[0])
for t in [0.1+0.3j, -0.13+0.21j]:
    W=-1/(32*t)
    x,y=xy(W)
    e=eta
    print(y, -4*e(2*t)**2*e(4*t)**4/(e(t)**4*e(8*t)**2))
    f=lambda z: e(4*z)**2*e(8*z)**2
    print(f(W), -32*t*t*f(t))
