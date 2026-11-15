from pathlib import Path
import sys,json
ROOT=Path('C:/Users/glaze/Documents/Codex/2026-11-02/lo')
sys.path.insert(0,str(ROOT/'work/jose200-audit-20261114/python-deps'))
import sympy as s
OUT=Path(__file__).resolve().parent
passed=[]
def zero(name,e):
 assert s.cancel(e)==0,name
 passed.append(name)
f,g,h,k,t,D=s.symbols('f g h k t D')
e1=t*(f-g)-h-k
e2=t*(h-k)-1+D*(f*f+f*g+g*g)
e3=h*h-f+D*f**3
x=t*t+D*(f+g)
y=D*h-t*(D*f+x)
zero('reciprocal second curve',k*k-g+D*g**3-(e3-(f-g)*e2+(h-k)*e1))
zero('reciprocal difference curve',y*y-x**3+D*x-(D**2*e3-D*(D*f+x)*(e2-t*e1)))
r,inv=s.symbols('r inv')
a1,a2,a3,a4,a5=s.symbols('a1 a2 a3 a4 a5')
poly=r**5-a1*r**4+a2*r**3-a3*r*r+a4*r-a5
v=r**3-a1*(1+inv)*r*r+a2*(1+inv)*r
zero('contact elimination',r*r*v-(1+inv)*(a3*r*r-a4*r+a5)-((1+inv)*poly-inv*r**5))
U,V,W,M,R=s.symbols('U V W M R',nonzero=True)
rr=U*V*W/R**2
dd=-rr*(U+V+W+2*M)/R**2
xs=[V*W/R**2,U*W/R**2,U*V/R**2]
for j,xx in enumerate(xs):
 expr=s.expand(xx**3-M*M/R**2*xx**2-(dd+2*M*rr/R**2)*xx-(rr/R)**2)
 expr=expr.subs(M*M,U*V+U*W+V*W)
 zero('inverse Vieta curve '+str(j+1),expr)
S,TH=s.symbols('S TH',nonzero=True)
zero('primary ratio sign and R factor',2*(-R/(M+U))/(-1/S)-2*R*S/(M+U))
zero('opposite ratio sign and R factor',2*(R/(M+V))/(-1/TH)+2*R*TH/(M+V))
zero('scalar stored R factor',2*(R/(M+W))/(-1/S)-R*(-2*S/(M+W)))
r1,r2,r3=s.symbols('r1 r2 r3')
xp=(r1*r1+r2*r2+r3*r3)/3
roots=[xp-r1*r1,xp-r2*r2,xp-r3*r3]
ac=roots[0]*roots[1]+roots[0]*roots[2]+roots[1]*roots[2]
bc=-roots[0]*roots[1]*roots[2]
yp=-r1*r2*r3
s1=r1+r2+r3;s2=r1*r2+r1*r3+r2*r3
xq=xp+s2;yq=-yp-s1*s2
zero('halving point curve',yq*yq-xq**3-ac*xq-bc)
zero('halving tangent slope',2*yq*(-s1)-(3*xq*xq+ac))
zero('halving doubled x',s1*s1-2*xq-xp)
zero('halving doubled y',-yq-s1*(xq-xp)-yp)
result={'scope':'Exact symbolic checks of selected identities written in the component, not a proof of its infinite arithmetic premises.','passed':passed,'count':len(passed)}
(OUT/'IDENTITY-CHECK.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
print(json.dumps(result,indent=2))
