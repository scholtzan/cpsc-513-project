// Basically a binary tree with Strings as leaves and len
// Based on https://github.com/Microsoft/dafny/blob/master/Test/dafny1/BinaryTree.dfy


datatype Node = Leaf(value: string) | InternalNode(left: Rope, right: Rope)

class Rope {
  ghost var Repr: set<object>
  ghost var Content: set<string>

  var len: int
  var val: Node

  constructor Init(v: string)
  ensures Valid()
  ensures ValidLen()
  {
    val := Leaf(v);
    len := |v|;
    Repr := {this};
    Content := {v};
  }

  function Len(): int
    requires Valid()
    reads Repr
    decreases Repr
  {
    match this.val
    case Leaf(v) => |v|
    case InternalNode(left, right) => left.Len() + right.Len()
  }

  predicate ValidLen()
    requires Valid()
    reads this, Repr
  {
    match this.val
    case Leaf(v) => this.len == |v|
    case InternalNode(left, right) => this.len == left.Len()
  }

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (
      match this.val
      case Leaf(v) => true
      case InternalNode(left, right) =>
        left != null && right != null &&
        left in this.Repr && right in this.Repr &&
        this !in left.Repr && this !in right.Repr &&
        this.Repr >= left.Repr && this.Repr >= right.Repr &&
        left.Valid() && right.Valid()
    )
  }
}
