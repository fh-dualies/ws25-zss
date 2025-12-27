------------------------------ MODULE TrafficLight ------------------------------
EXTENDS Naturals

VARIABLES TrafficLight, turn

States == {"green", "red"}

vars == <<TrafficLight, turn>>

Init ==
  /\ turn = 1
  /\ TrafficLight = [i \in 0 .. 1 |-> "red"]

TypeOK == /\ \A i \in 0..1: TrafficLight[i] \in States 
          /\   turn \in {0, 1}

OtherTL(a) == (a + 1) % 2


Control ==  /\ TrafficLight[turn] = "green"
            /\ turn' = OtherTL(turn)
            /\ UNCHANGED TrafficLight
                  

SwitchToRed == /\ TrafficLight[OtherTL(turn)] = "green"
               /\ TrafficLight' = [TrafficLight EXCEPT ![OtherTL(turn)] = "red"]
               /\ UNCHANGED turn

SwitchToGreen == /\ TrafficLight[OtherTL(turn)] = "red"
                 /\ TrafficLight' = [TrafficLight EXCEPT ![turn] = "green"]
                 /\ UNCHANGED turn

Next == 
    \/ Control
    \/ SwitchToGreen
    \/ SwitchToRed

NeverBothGreen == TrafficLight[0] = "red" \/ TrafficLight[1] = "red"

SwitchOnlyAfterGreen == [][TrafficLight[turn] = "red" => turn' = turn]_vars

SwitchNotDirectlyToGreen == [][\A i \in 0..1: 
                                /\ TrafficLight[i] = "green"
                                /\ TrafficLight[OtherTL(i)] = "red"
                                =>
                                \/ TrafficLight' = TrafficLight
                                \/ TrafficLight' = [TrafficLight EXCEPT  ![i] = "red"] ]_vars

SwitchToGreenWhoseTurnItIs == [][\A i \in 0..1:
                                /\ TrafficLight[i] = "red"
                                /\ TrafficLight[OtherTL(i)] = "red"
                                => 
                                \/ TrafficLight' = TrafficLight
                                \/ TrafficLight' = [TrafficLight EXCEPT ![turn] = "green"] ]_vars 

AlwaysEventuallyGreen == [](\A i \in 0..1: TrafficLight[i] = "red" => <>(TrafficLight[i] = "green"))                               
AlwaysEventuallyRed == [](\A i \in 0..1: TrafficLight[i] = "green" => <>(TrafficLight[i] = "red"))
AlwaysEventuallyBothRed == []<>(\A i \in 0..1: TrafficLight[i] = "red")                                                              
                                

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Sei Ampel 1 am Zug. Dann kann Ampel 2 erst dann dran kommen, nach dem Ampel 1 auf Grün geschaltet wurde.


=============================================================================
\* Modification History
\* Last modified Wed Mar 20 15:38:46 CET 2024 by moritz
\* Created Sat Dec 30 18:44:33 CET 2023 by moritz
