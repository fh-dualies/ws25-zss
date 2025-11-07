datatype BYTree = BlueLeaf | YellowLeaf | Node ( left : BYTree , right: BYTree )

function Oceanize(t: BYTree): BYTree
{
  match t
  case BlueLeaf => BlueLeaf
  case YellowLeaf => BlueLeaf
  case Node(left, right) => Node(Oceanize(left), Oceanize(right))
}

function BlueCount(t: BYTree) : int{
    match t
    case BlueLeaf => 1
    case YellowLeaf => 0
    case Node(left, right) => BlueCount(left) + BlueCount(right)
}

lemma{:induction false} OceanizeCanOnlyIncreaseBlueCount( t : BYTree )
ensures BlueCount( Oceanize(t) ) >= BlueCount( t )
{ 
match t
case BlueLeaf => {
    calc {
        BlueCount( Oceanize( BlueLeaf ) );
        ==
        BlueCount( BlueLeaf );
        ==
        1;
    }
}
case YellowLeaf => {
    calc {
        BlueCount( Oceanize( YellowLeaf ) );
        ==
        BlueCount( BlueLeaf );
        ==
        1;
    }
}
case Node(left, right) => {
    calc {
        BlueCount( Oceanize( Node(left, right) ) );
        ==
        BlueCount( Node (Oceanize(left), Oceanize( right)));
        ==
        BlueCount( Oceanize(left)) + BlueCount(Oceanize( right));
        >= {OceanizeCanOnlyIncreaseBlueCount(left); OceanizeCanOnlyIncreaseBlueCount(right);}
        BlueCount(left) + BlueCount(right);
        ==
        BlueCount(Node(left, right));
    }
}
}