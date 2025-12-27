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


SpaceshipBobAlone == /\ pos' = [pos EXCEPT ![Bob] = Other(pos[Bob])]
                         
SpaceshipWithPassenger(x) == 
    /\ x \in Actors \ {Bob}
    /\ pos[x] = pos[Bob]
    /\ pos' = [pos EXCEPT 
                ![Bob] = Other(pos[Bob]), 
                ![x] = Other(pos[x])]

Nobeef == 
    /\ ~(pos[Knork] = ProximaCentauri /\ pos[Glubsch] = ProximaCentauri /\ pos[Bob] # ProximaCentauri)
    /\ ~(pos[Glubsch] = ProximaCentauri /\ pos[Fruntz] = ProximaCentauri /\ pos[Bob] # ProximaCentauri)

    /\ ~(pos[Knork] = Enceladus /\ pos[Glubsch] = Enceladus /\ pos[Bob] # Enceladus)
    /\ ~(pos[Glubsch] = Enceladus /\ pos[Fruntz] = Enceladus /\ pos[Bob] # Enceladus)

Next ==
    /\ Nobeef
    /\ (SpaceshipBobAlone \/ \E x \in Actors \ {Bob} : SpaceshipWithPassenger(x))

Spec == 
    Init /\ [][Next]_pos

=============================================================================
