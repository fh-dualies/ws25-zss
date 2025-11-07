datatype BYTree = BlueLeaf | YellowLeaf | Node ( left : BYTree , right: BYTree )

function ReverseColors(t: BYTree): BYTree
{
  match t
  case BlueLeaf => YellowLeaf
  case YellowLeaf => BlueLeaf
  case Node(left, right) => Node(ReverseColors(left), ReverseColors(right))
}

method TestReverseColors ( ) {
var a := Node ( BlueLeaf , Node ( BlueLeaf ,  YellowLeaf ) ) ;
var b := Node ( YellowLeaf , Node ( YellowLeaf , BlueLeaf ) ) ;
assert ReverseColors ( a ) == b ;
assert ReverseColors ( b ) == a ;
}

lemma{:induction false} ReverseColorsIsAnInvolution( t : BYTree )
ensures ReverseColors( ReverseColors( t ) ) == t
{
    match t
    case BlueLeaf => {
        calc {
            ReverseColors( ReverseColors( BlueLeaf ) );
            ==
            ReverseColors( YellowLeaf );
            ==
            BlueLeaf;
        }
    }
    case YellowLeaf => {
        calc {
            ReverseColors( ReverseColors( YellowLeaf ) );
            ==
            ReverseColors( BlueLeaf );
            ==
            YellowLeaf;
        }
    }
    case Node(left, right) => {
        calc {
            ReverseColors( ReverseColors( Node(left, right) ) );
            ==
            ReverseColors( Node( ReverseColors(left), ReverseColors(right) ) );
            ==
            Node( ReverseColors( ReverseColors(left) ), ReverseColors( ReverseColors(right) ) );
            == {ReverseColorsIsAnInvolution(left); ReverseColorsIsAnInvolution(right);}
            Node( left, right );
        }
    }
}