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
      ensures ValidLen()
    {
      val := Leaf("");
      len := 0;
      Repr := {this};
      Content := [""];
      HasParent := false;
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

    predicate ValidLen()
      requires Valid()
      reads this, Repr
    {
      match this.val
      case Leaf(v) => this.len == |v| && ContentLen(this.Content) == |v| && |Content| == 1
      case InternalNode(children) => this.len == this.Len() && forall c: Rope :: c in children ==> c.len <= this.len && c.ValidLen()
    }

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
            |children| <= MAX_CHILDREN &&
            forall c: Rope :: c in children ==> c in Repr && this !in c.Repr && c.Repr <= Repr && c.Valid() && c.Content <= Content && forall cont: string :: cont in c.Content ==> cont in this.Content
          )
      )
    }

    method Index(i: int) returns (charAtIndex: string)
      requires Valid()
      requires ValidLen()
//      ensures i >= 0 && i < this.len ==> charAtIndex != ""
      ensures i < 0 || i >= this.len ==> charAtIndex == ""
      decreases Repr
    {
      if this.len <= i || i < 0
        { charAtIndex := ""; }
      else
        {
          match this.val
          case Leaf(v) =>
            charAtIndex := [v[i]];
          case InternalNode(children) =>
            var c := 0;
            var newI := i;

            while (c + 1 < |children| && children[c].len <= newI)
              invariant 0 <= c < |children|
              {
                newI := newI - children[c].len;
                c := c + 1;
              }

            charAtIndex := children[c].Index(newI);
        }
    }

    method SliceToString(i: int, j: int) returns (slice: string)
      requires Valid()
      requires ValidLen()
      ensures i < 0 || i >= this.len || j >= this.len || i > j || j < 0 ==> slice == ""
//      ensures slice != "" ==> |slice| == j - i
      decreases Repr
    {
        if i < 0 || j < 0 || i >= this.len || j >= this.len || i > j
          {
            slice := "";
          }
        else
          {
            match this.val
            case Leaf(v) =>
              slice := v[i..j];
            case InternalNode(children) =>
              var c := 0;
              var newI := i;
              var newJ := j;

              while (c + 1 < |children| && children[c].len <= newI)
              invariant 0 <= c < |children|
              {
                newI := newI - children[c].len;
                newJ := newJ - children[c].len;
                c := c + 1;
              }

              var finalSlice := "";

              while (c < |children| && newJ >= 0)
              invariant 0 <= c <= |children|
              {
                if newJ >= children[c].len
                  {
                    var s := children[c].SliceToString(newI, children[c].len - 1);
                    finalSlice := finalSlice + s;
                  }
                else
                  {
                    var s := children[c].SliceToString(newI, newJ);
                    finalSlice := finalSlice + s;
                  }

                newJ := newJ - children[c].len;
                newI := 0;
                c := c + 1;
              }

              slice := finalSlice;
          }
    }
  }
}
