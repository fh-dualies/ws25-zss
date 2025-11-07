function Reduce(m: nat, x: int): int
{
    if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} Reduce_Possible(m: nat, x: int)
    ensures x - 2*m <= Reduce(m, x)
{
    if m == 0 {
        assert x - 2 * m <= Reduce(m, x);
        assert x - 2 * 0 <= Reduce(0, x);
        assert x <= x;
    } else {
        calc {
            Reduce(m, x);
            ==
            Reduce(m / 2, x + 1) - m;
            >= {Reduce_Possible(m / 2, x + 1);}
            (x + 1) - 2 * (m / 2) - m;
            >=
            (x + 1) - m - m;
            >=
            x - 2 * m;
        }
    }
}

lemma {:induction false} Reduce_Impossible(m: nat, x: int)
    ensures x - 2*m < Reduce(m, x)
{
    if m == 0 {
        calc {
            x - 2 * m < Reduce(m, x);
            ==
            x - 2 * 0 < Reduce(0, x);
            ==
            x < x;
        }
        assert x - 2*m < Reduce(m, x);
    } else {
        calc {
            Reduce(m, x);
            ==
            Reduce(m / 2, x + 1) - m;
            >= {Reduce_Impossible(m / 2, x + 1);}
            (x + 1) - 2 * (m / 2) - m;
            >=
            (x + 1) - m - m;
            >
            x - 2 * m;
        }
    }
}