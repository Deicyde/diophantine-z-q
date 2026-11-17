import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
E = pari.ellinit([0,0,0,-25,0])
W = pari.ellweilcurve(E)
print(W)
print(pari('?ellweilcurve') if False else '')
