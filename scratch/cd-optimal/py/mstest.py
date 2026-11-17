import cypari2
pari = cypari2.Pari(); pari.allocatemem(4*10**9)
pari('E=ellinit([0,0,0,-25,0]); [M,xpm]=msfromell(E)')
print(pari('xpm'))
print(pari('mseval(M, xpm[1], [oo, 1/32])'), pari('mseval(M, xpm[2], [oo, 1/32])'))

print(pari('E.omega'))
