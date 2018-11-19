# Rope

## Properties

1. Every node has at most m children.
2. Every non-leaf node (except root) has at least ⌈m/2⌉ child nodes.
3. The root has at least two children if it is not a leaf node.
4. MIN_LEAF MAX LEAF: maximum value length in leaf
5. All leaves appear in the same level. (so it seems...)
  * todo: Height function => height of all children must be identical? [todo]
6. Only leaves contain data
  * already ensured by the data structure itself
7. Weight values (left subtrees)



## Operations

* Index
  * not really necessary, but should be easy to implement

* Concat
  * yes

* Split
  * Copy?

* Insert
  * yes

* Delete
  * does not exists
    * every time some delta is applied to the text, the `text` rope gets rebuilt from scratch by performing copy and insertion operations
      * (which is probably faster than deletion)

* Report (output the string)
  * never the case that entire tree is converted to string
  * instead only segments of the tree converted into string (eg. only visible parts)
  * slice_to_cow


## Future

* deltas?


module Rope {
  const MAX_CHILDREN: nat := 4
  const MIN_CHILDREN: nat := 2
  const MAX_LEAF_LEN: nat := 10
  const MIN_LEAF_LEN: nat := 2   // minimum size requirement when splitting

  datatype Node = Leaf(value: string) | InternalNode(children: seq<Rope>)

  class Rope {
    ghost var Repr: set<Rope>
    ghost var Content: seq<string>
    ghost var HasParent: bool

    var val: Node
    var len: int

    constructor Init()
      ensures Valid()
//      ensures ValidLen()
    {
      val := Leaf("");
      len := 0;
      Repr := {this};
      Content := [""];
      HasParent := false;
    }

    constructor FromNodes(nodes: seq<Rope>)
      requires forall c: Rope :: c in nodes ==> c.Valid()// && c.ValidLen()
      requires |nodes| >= MIN_CHILDREN && |nodes| <= MAX_CHILDREN
      ensures Valid()
//      ensures r.ValidLen()
      modifies nodes
    {
      var i := 0;
      Content := [];
      Repr := {};
      HasParent := false;
      var totalLen := 0;

      while i < |nodes|
      {
        totalLen := totalLen + nodes[i].len;
        Content := Content + nodes[i].Content;
        nodes[i].HasParent := true;
        Repr := Repr + nodes[i].Repr;

        i := i + 1;
      }

      len := totalLen;
      val := InternalNode(nodes);
      Repr := Repr + {this};
    }

    function ContentLen(c: seq<string>): int
      decreases |c|
    {
      if |c| == 0 then 0
      else |c[0]| + ContentLen(c[1..])
    }

    function Len(): int
      requires Valid()
      reads Repr
      decreases Repr
    {
      match this.val
      case Leaf(v) => |v|
      case InternalNode(children) => ContentLen(this.Content)
    }

//    predicate ValidLen()
//      requires Valid()
//      reads this, Repr
//    {
//      match this.val
//      case Leaf(v) => this.len == |v| && ContentLen(this.Content) == |v| && |Content| == 1
//      case InternalNode(children) => this.len == this.Len() && forall c: Rope :: c in children ==> c.len <= this.len && c.ValidLen()
//    }

    predicate Valid()
      reads this, Repr
      requires MAX_LEAF_LEN >= MIN_LEAF_LEN
      requires MIN_CHILDREN <= MAX_CHILDREN && MIN_CHILDREN >= 2
    {
      this in Repr &&
      (
        match this.val
        case Leaf(v) => |v| <= MAX_LEAF_LEN && Content == [v]
        case InternalNode(children) =>
          (HasParent ==>
            |children| >= MIN_CHILDREN &&
            |children| <= MAX_CHILDREN &&
            forall c: Rope :: c in children ==> c in Repr && this !in c.Repr && c.Repr <= Repr && c.Valid() && c.Content <= Content && forall cont: string :: cont in c.Content ==> cont in this.Content
          ) &&
          (!HasParent ==>
            |children| >= 2 &&
            |children| <= MAX_CHILDREN  &&
            forall c: Rope :: c in children ==> c in Repr && this !in c.Repr// && c.Repr <= Repr && c.Valid() && c.Content <= Content && forall cont: string :: cont in c.Content ==> cont in this.Content
          )
      )
    }
  }
}
