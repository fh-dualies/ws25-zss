function K(x: nat, y: nat, z: nat): int
decreases 6*x + y + z
{
    if x < 10 || y < 5 then
        x + y
    else if z == 0 then
        K(x-1, y, 5)
    else 
        K(x, y-1, z-1)
}

function K'(x: nat, y: nat, z: nat): int
decreases x,z
{
    if x < 10 || y < 5 then 
        x + y
    else if z == 0 then
        K'(x-1, y-2, 5)
    else 
        K'(x, y+1, z-1)
}