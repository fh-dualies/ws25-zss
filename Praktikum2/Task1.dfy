function G(n: nat): nat
{
    if n==0 then 0 else n - G(G(n - 1))
}

function G'(n: nat): nat
{
    //if n==0 then 1 else n - G'(G'(n - 1))
    1
}
