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
        )
    )
  }

  method Delete(i: int, j: int) returns (newRope: Rope?)
    requires Valid()
    requires ValidLen()
    ensures newRope != null ==> newRope.Valid()
    ensures newRope != null ==> newRope.ValidLen()
    ensures j < i ==> newRope == null
    ensures i < 0 || i >= this.Len() || j < j || j >= this.Len() ==> newRope == null
    //ensures i == 0 && j == this.Len() - 1 && newRope != null ==> newRope.len == 0
    // todo: len
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
//    ensures newRope != null ==> newRope.Len() >= this.Len() [todo]
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
    //requires this.Repr !! rope.Repr   // prevents cycles and concatenating the same rope with itself [todo?]
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
