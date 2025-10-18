/*function F(n: nat): nat
decreases n
{
    if n == 0 then 1 else n - M(F(n-1))
}

function M(n: nat): nat
decreases n
{
    if n == 0 then 0 else n - F(M(n-1))
}
*/ 
