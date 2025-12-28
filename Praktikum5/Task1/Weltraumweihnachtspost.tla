------------------------------ MODULE Weltraumweihnachtspost ------------------------------
EXTENDS Naturals

CONSTANTS 
    ProximaCentauri, \* start 
    Enceladus, \* end

    Bob,

    Glubsch,
    Knork,
    Fruntz

VARIABLES 
    pos

Actors == {Bob, Glubsch, Knork, Fruntz}
Places == {ProximaCentauri, Enceladus}

Init == 
    /\ pos = [i \in Actors |-> ProximaCentauri]

TypeOK == /\ pos \in [Actors -> Places]
          
Other(p) == IF p = ProximaCentauri THEN Enceladus ELSE ProximaCentauri

NoBeefPos(p) == 
    /\ ~(p[Knork] = ProximaCentauri /\ p[Glubsch] = ProximaCentauri /\ p[Bob] # ProximaCentauri)
    /\ ~(p[Glubsch] = ProximaCentauri /\ p[Fruntz] = ProximaCentauri /\ p[Bob] # ProximaCentauri)

    /\ ~(p[Knork] = Enceladus /\ p[Glubsch] = Enceladus /\ p[Bob] # Enceladus)
    /\ ~(p[Glubsch] = Enceladus /\ p[Fruntz] = Enceladus /\ p[Bob] # Enceladus)

SpaceshipBobAlone == 
    /\ NoBeefPos(pos)
    /\ pos' = [pos EXCEPT ![Bob] = Other(pos[Bob])]
    /\ NoBeefPos(pos') 
                         
SpaceshipWithPassenger(x) == 
    /\ x \in Actors \ {Bob}
    /\ pos[x] = pos[Bob]
    /\ pos' = [pos EXCEPT 
                ![Bob] = Other(pos[Bob]), 
                ![x] = Other(pos[x])]
    /\ NoBeefPos(pos')

Nobeef == NoBeefPos(pos)

Next == SpaceshipBobAlone \/ (\E x \in Actors \ {Bob} : SpaceshipWithPassenger(x))

Impossible == 
    ~(
        pos[Glubsch] = Enceladus
        /\ pos[Knork] = Enceladus
        /\ pos[Fruntz] = Enceladus
     )


Spec == 
    Init /\ [][Next]_pos

=============================================================================
