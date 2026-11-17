default(realprecision, 40);
w(t) = eta(16*t,1)^3/(eta(8*t,1)*eta(32*t,1)^2);
check(A,B,C,D,t) = abs(w((A*t+B)/(C*t+D))/w(t) - kronecker(2,D));
run() = {
  my(cnt=0, bad=0, dd, b, t, e);
  forstep(c=32, 32*12, 32,
    for(a=1, 60,
      if(gcd(a,c)==1,
        dd = lift(Mod(a,c)^-1); b = (a*dd-1)/c; t = 0.1 + 0.7*I + 0.013*a;
        e = check(a,b,c,dd,t); cnt++; if(e > 1e-20, bad++; print("BAD ", [a,b,c,dd], " ", e));
        e = check(-a,-b,-c,-dd,t); cnt++; if(e > 1e-20, bad++; print("BAD ", [-a,-b,-c,-dd], " ", e)))));
  print("checked ", cnt, " bad ", bad);
}
run();
