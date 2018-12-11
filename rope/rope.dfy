// This file contains an implementation of the standard rope data structure in Dafny,
// followed by an implementation of the rope data structure used in xi-editor.

module Rope {
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
            left in this.Repr &&
            this.Repr >= left.Repr &&
            this !in left.Repr &&
            left.Valid()
          ) &&
          (right != null ==>
            right in this.Repr &&
            this.Repr >= right.Repr &&
            this !in right.Repr &&
            right.Valid()
          )
      )
    }

    function method Report(): string
      requires Valid()
      requires ValidLen()
      reads Repr
      decreases Repr
      ensures |this.Report()| == this.Len()
    {
      if this.Len() == 0 then ""
      else
        match this.val
        case Leaf(v) => v
        case InternalNode(left, right) =>
          if left != null && right != null then left.Report() + right.Report()
          else if left == null && right != null then right.Report()
          else if left != null && right == null then left.Report()
          else if left == null && right == null then ""
          else ""
    }

    method Delete(i: int, j: int) returns (newRope: Rope?)
      requires Valid()
      requires ValidLen()
      ensures newRope != null ==> newRope.Valid()
      ensures newRope != null ==> newRope.ValidLen()
      ensures j < i ==> newRope == null
      ensures i < 0 || i >= this.Len() || j < j || j >= this.Len() ==> newRope == null
    {
      if i < 0 || j < 0 || i >= this.Len() || j >= this.Len() || i > j
        {
          newRope := null;
        }
      else
        {
          var newLeft, _ := this.Split(i);
          var _, newRight := this.Split(j);

          if newLeft == null
            {
              if newRight == null
                {
                  newRope := new Rope.Init();
                }
              else
                {
                  newRope := newRight;
                }
            }
          else
            {
              if newRight == null
                {
                  newRope := newLeft;
                }
              else
                {
                  newRope := newLeft.Concat(newRight);
                }
            }
        }
    }

    method Insert(i: int, s: string) returns (newRope: Rope?)
      requires Valid()
      requires ValidLen()
      ensures Valid()
      ensures ValidLen()
      ensures newRope != null ==> newRope.Valid()
      ensures newRope != null ==> newRope.ValidLen()
      ensures i < 0 || i >= this.Len() <==> newRope == null
    {
      if i < 0
        {
          newRope := null;
        }
      else if i >= this.Len()
        {
          newRope := null;
        }
      else
        {
          var insertedLeaf := new Rope.Init();
          insertedLeaf.val := Leaf(s);
          insertedLeaf.len := |s|;

          var leftSplit, rightSplit := this.Split(i);

          if leftSplit == null
            {
              if rightSplit == null
                {
                  newRope := insertedLeaf;
                }
              else
                {
                  newRope := insertedLeaf.Concat(rightSplit);
                }
            }
          else
            {
              var leftConcat := leftSplit.Concat(insertedLeaf);

              if rightSplit != null
                {
                  newRope := leftConcat.Concat(rightSplit);
                }
              else
                {
                  newRope := leftConcat;
                }
            }
        }
    }

    method Split(i: int) returns (leftSplit: Rope?, rightSplit: Rope?)
      requires Valid()
      requires ValidLen()
      ensures leftSplit != null ==> leftSplit.Valid()
      ensures rightSplit != null ==> rightSplit.Valid()
      ensures rightSplit != null ==> rightSplit.ValidLen()
      ensures leftSplit != null ==> leftSplit.ValidLen()
      ensures i >= 0 && i < this.Len() ==> leftSplit != null || rightSplit != null
      ensures i <= 0 ==> leftSplit == null
      ensures i > 0 && i >= this.Len() ==> rightSplit == null
      decreases Repr
    {
      if i <= 0
        {
          leftSplit := null;
          rightSplit := this;
        }
      else if i >= this.Len()
        {
          leftSplit := this;
          rightSplit := null;
        }
      else
        {
          match this.val
          case Leaf(v) =>
            var rightNode := new Rope.Init();
            rightNode.val := Leaf(v[i..]);
            rightNode.len := |v[i..]|;
            rightNode.Repr := {rightNode};
            rightSplit := rightNode;

            var leftLeaf := new Rope.Init();
            leftLeaf.val := Leaf(v[0..i]);
            leftLeaf.len := |v[0..i]|;
            leftLeaf.Repr := {leftLeaf};

            var leftNode := new Rope.Init();
            leftNode.val := InternalNode(leftLeaf, null);
            leftNode.Repr := {leftNode, leftLeaf};
            leftNode.len := leftLeaf.Len();
            leftSplit := leftNode;

          case InternalNode(left, right) =>
            if this.len >= i
              {
                var postLeft, postRight := left.Split(i);

                if postRight != null
                  {
                    var rightParent := new Rope.Init();
                    rightParent.val := InternalNode(postRight, right);
                    rightParent.len := postRight.Len();

                    if right != null
                      {
                        rightParent.Repr := rightParent.Repr + postRight.Repr + right.Repr;
                      }
                    else
                      {
                        rightParent.Repr := rightParent.Repr + postRight.Repr;
                      }

                    rightSplit := rightParent;
                  }
               else
                  {
                     rightSplit := right;
                  }

                var leftNode := new Rope.Init();
                leftNode.val := InternalNode(postLeft, null);

                if postLeft != null
                  {
                    leftNode.Repr := leftNode.Repr + postLeft.Repr;
                    leftNode.len := postLeft.Len();
                  }
                else
                  {
                    leftNode.Repr := leftNode.Repr;
                    leftNode.len := 0;
                  }

                leftSplit := leftNode;
              }
            else
              {
                var postLeft, postRight := right.Split(i);

                var leftNode := new Rope.Init();
                leftNode.val := InternalNode(left, postLeft);
                leftNode.len := 0;

                if postLeft != null
                  {
                    if left != null
                      {
                        leftNode.Repr := leftNode.Repr + left.Repr + postLeft.Repr;
                        leftNode.len := left.Len();
                      }
                    else
                      {
                        leftNode.Repr := leftNode.Repr + postLeft.Repr;
                      }
                  }
                else
                  {
                    if left != null
                      {
                        leftNode.Repr := leftNode.Repr + left.Repr;
                        leftNode.len := left.Len();
                      }
                  }

                leftSplit := leftNode;

                rightSplit := postRight;
              }
        }
    }

    method Concat(rope: Rope) returns (concatenatedRope: Rope)
      requires Valid()
      requires ValidLen()
      requires rope.Valid()
      requires rope.ValidLen()
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
}


/////////////////////////// xi-editor //////////////////////////////////////////

module XiRope {
  const MAX_CHILDREN: nat := 4
  const MIN_CHILDREN: nat := 2
  const MAX_LEAF_LEN: nat := 10
  const MIN_LEAF_LEN: nat := 2   // minimum size requirement when splitting

  datatype Node = Leaf(value: string) | InternalNode(children: seq<Rope>)

  class Rope {
    ghost var Repr: set<Rope>
    ghost var Content: seq<string>

    var val: Node
    var len: int
    var height: int

    constructor Init()
      ensures Valid()
      ensures ValidLen()
    {
      val := Leaf("");
      len := 0;
      height := 0;
      Repr := {this};
      Content := [""];
    }

    constructor FromNodes(left: Rope, right: Rope)
      requires left.ValidNonRoot() &&
               left.ValidLen() &&
               right.ValidNonRoot() &&
               right.ValidLen() &&
               left.height == right.height &&
               left.len == left.Len() &&
               right.len == right.Len()
      ensures Valid()
      ensures ValidLen()
    {
      Repr := left.Repr + right.Repr + {this};
      val := InternalNode([left, right]);
      height := left.height + 1;
      len := left.len + right.len;
      Content := left.Content + right.Content;

    }

    function method ContentLen(c: seq<string>): int
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
      case Leaf(v) =>
        this.len == |v| &&
        ContentLen(this.Content) == |v| &&
        |Content| == 1
      case InternalNode(children) =>
        this.len >= 0 && forall c: Rope :: c in children ==>
          c.len <= this.len && c.ValidLen()
    }

    predicate ValidNonRoot()
      reads this, Repr
      requires MAX_LEAF_LEN >= MIN_LEAF_LEN
      requires MIN_CHILDREN <= MAX_CHILDREN && MIN_CHILDREN >= 2
    {
      this in Repr &&
      (
        match this.val
        case Leaf(v) => |v| <= MAX_LEAF_LEN && Content == [v] && height == 0
        case InternalNode(children) =>
          height >= 0 &&
          |children| >= MIN_CHILDREN &&
          |children| <= MAX_CHILDREN &&
          forall c: Rope :: c in children ==>
            c in Repr && this !in c.Repr && c.Repr < Repr && c.ValidNonRoot() &&
            c.height == height - 1 && |c.Content| <= |Content| &&
            forall cont: string :: cont in c.Content ==> cont in this.Content
      )
    }

    predicate Valid()
      reads this, Repr
      requires MAX_LEAF_LEN >= MIN_LEAF_LEN
      requires MIN_CHILDREN <= MAX_CHILDREN && MIN_CHILDREN >= 2
    {
      this in Repr &&
      (
        match this.val
        case Leaf(v) => |v| <= MAX_LEAF_LEN && Content == [v] && height == 0
        case InternalNode(children) =>
          height >= 0 &&
          |children| >= 2 &&
          |children| <= MAX_CHILDREN &&
          forall c: Rope :: c in children ==>
            c in Repr && this !in c.Repr && c.Repr < Repr &&
            c.ValidNonRoot() && c.height == height - 1 && |c.Content| <= |Content| &&
            forall cont: string :: cont in c.Content ==> cont in this.Content
      )
    }

    method Index(i: int) returns (charAtIndex: string)
      requires Valid()
      requires ValidLen()
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

    //method MergeNodes(rope1: Rope, rope2: Rope) returns (newRope: Rope)
    //  requires rope1.Valid()
    //  requires rope1.ValidLen()
    //  requires rope2.Valid()
    //  requires rope2.ValidLen()
    //  ensures newRope.Valid()
    //  ensures newRope.ValidLen()
    //{
    //  var children1: seq<Node> = [];
    //  var children2: seq<Node> = []
    //  match rope1.val
    //  case Leaf(v) =>
    //    children1 := [rope1.val];
    //  case InternalNode(c) =>
    //    children1 := c;
    //
    //  match rope2.val
    //  case Leaf(v) =>
    //    children2 := [rope2.val];
    //  case InternalNode(c) =>
    //    children2 := c;
    //
    //  if |children1| + |children2| <= MAX_CHILDREN
    //    {
    //      newRope := Rope.FromNodes();
    //    }
    //}

    method Concat(rope: Rope) returns (newRope: Rope)
      requires Valid()
      requires ValidLen()
      requires rope.Valid()
      requires rope.ValidLen()
      requires rope.height == this.height &&
        this.len == this.Len() &&
        rope.len == rope.Len()
      ensures newRope.Valid()
      ensures newRope.ValidLen()
    {
      // todo: implement for any input rope structure
      newRope := new Rope.FromNodes(this, rope);
    }

    method SliceToString(i: int, j: int) returns (slice: string)
      requires Valid()
      requires ValidLen()
      ensures i < 0 || i >= this.len || j >= this.len || i > j || j < 0 ==> slice == ""
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
