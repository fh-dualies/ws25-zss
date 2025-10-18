1)
a)
Terminierungsargument: "decreases n"
Begründung: 
    - werden Argumente in Rekursion streng kleiner ?
    - G(n-1) -> n-1 < n
    - G(n-1) <= n-1

b)
Nein, da
    G'(1) 
      = 1 - G'(G'(0)) 
      = 1 - G'(1)
      unendliche Rekursion

3)
a)
    - Terminierung bei  = 0
    - 2 Rekursive Aufrufe
        - 1. Inner(a, b-1) -> a bleibt gleich, b sinkt
        - 2. Outer(a-1) -> a sinkt, b bleibt gleich
    -> (a, b) wird insgesamt immer kleiner

