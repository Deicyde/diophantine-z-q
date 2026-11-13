import cmath, math, itertools
s2=math.sqrt(2)
def Omega(t):
    a=(t-3)/2; b=(t+1)/2
    F=[[-(2+s2)*a, -(1+s2)*a],[-(2-s2)*b, -(1-s2)*b]]
    E=[[t, s2*t],[1, -s2]]
    d=F[0][0]*F[1][1]-F[0][1]*F[1][0]
    Fi=[[F[1][1]/d, -F[0][1]/d],[-F[1][0]/d, F[0][0]/d]]
    return [[sum(Fi[i][k]*E[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
chars=[((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1) if (a1*b1+a2*b2)%2==0]
def theta(ch,O,N=12):
    (a1,a2),(b1,b2)=ch; s=0
    for n1 in range(-N,N+1):
        for n2 in range(-N,N+1):
            x1=n1+a1/2; x2=n2+a2/2
            Q=x1*x1*O[0][0]+2*x1*x2*O[0][1]+x2*x2*O[1][1]
            s+=cmath.exp(1j*math.pi*(Q+x1*b1+x2*b2))
    return s
if __name__ == "__main__":
    O=Omega(s2+1j)
    print(O)
    Y=[[O[i][j].imag for j in range(2)] for i in range(2)]
    X=[[O[i][j].real for j in range(2)] for i in range(2)]
    tr=Y[0][0]+Y[1][1]; det=Y[0][0]*Y[1][1]-Y[0][1]*Y[1][0]
    print("Y",Y,"eig",(tr-math.sqrt(tr*tr-4*det))/2,(tr+math.sqrt(tr*tr-4*det))/2)
    print("X",X)
    S=0
    for ch in chars:
        t=theta(ch,O); S+=t**8
        print(ch, t, abs(t), t**8)
    print("S",S)
