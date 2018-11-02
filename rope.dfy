datatype Node = Leaf(value: string) | InternalNode(left: Rope?, right: Rope?)

class Rope {
  ghost var Repr: set<object>

  var len: int
  var val: Node

  constructor Init()
  ensures Valid()
  ensures ValidLen()
  {
    val := InternalNode(null, null);
    len := 0;
    Repr := {this};
  }

  function method Len(): int
    requires Valid()
    reads Repr
    decreases Repr
  {
    match this.val
    case Leaf(v) => |v|
    case InternalNode(left, right) =>
      if left != null && right != null then left.Len() + right.Len()
      else if left == null && right != null then right.Len()
      else if left != null && right == null then left.Len()
      else if left == null && right == null then 0
      else 0
  }

  predicate ValidLen()
    requires Valid()
    reads this, Repr
  {
    match this.val
    case Leaf(v) => this.len == |v|
    case InternalNode(left, right) =>
      (left != null ==> this.len == left.Len() && left.ValidLen()) &&
      (left == null ==> this.len == 0) &&
      (right != null ==> right.ValidLen())
  }

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (
      match this.val
      case Leaf(v) => true
      case InternalNode(left, right) =>
        (left != null ==>
          left in this.Repr && this.Repr >= left.Repr && this !in left.Repr && left.Valid()
        ) &&
        (right != null ==>
          right in this.Repr && this.Repr >= right.Repr && this !in right.Repr && right.Valid()
        ) &&
        (left != null && right != null ==>
          left.Repr !! right.Repr
        )
    )
  }

  method Concat(rope: Rope) returns (concatenatedRope: Rope)
    requires Valid()
    requires ValidLen()
    requires rope.Valid()
    requires rope.ValidLen()
    requires this.Repr !! rope.Repr   // prevents cycles and concatenating the same rope with itself [todo?]
    ensures concatenatedRope.Valid()
    ensures concatenatedRope.ValidLen()
  {
    concatenatedRope := new Rope.Init();
    concatenatedRope.val := InternalNode(this, rope);
    concatenatedRope.len := this.Len();
    concatenatedRope.Repr := concatenatedRope.Repr + this.Repr + rope.Repr;
  }

  method Index(i: int) returns (charAtIndex: string)
    requires Valid()
    requires ValidLen()
    ensures i >= 0 && this.Len() > i ==> charAtIndex != ""
    //ensures i < 0 || this.Len() <= i ==> charAtIndex == ""
    decreases Repr
  {
    match this.val
    case Leaf(v) =>
      if |v| <= i || i < 0
        { charAtIndex := ""; }
      else
        { charAtIndex := [v[i]]; }
    case InternalNode(left, right) =>
      if this.len <= i
        {
          if right == null
            { charAtIndex := ""; }
          else
            { charAtIndex := right.Index(i - this.len); }
        }
      else
        {
          if left != null
            { charAtIndex := left.Index(i); }
          else
            { charAtIndex := ""; }
        }
  }
}
