module Rope {
  const MAX_CHILDREN: nat
  const MIN_CHILDREN: nat
  const MAX_LEAF_LEN: nat
  const MIN_LEAF_LEN: nat   // minimum size requirement when splitting

  datatype Node = Leaf(value: string) | InternalNode(children: seq<Rope>)

  class Rope {
    ghost var Repr: set<Rope>
    ghost var Content: seq<string>
    ghost var HasParent: bool

    var val: Node
    var len: int

    constructor Init()
      ensures Valid()
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
      case Leaf(v) => this.len == |v|
      case InternalNode(children) => this.len == this.Len()
    }

    predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      (
        match this.val
        case Leaf(v) => |v| <= MAX_LEAF_LEN
        case InternalNode(children) =>
          (HasParent ==>
            |children| >= MIN_CHILDREN &&
            |children| <= MAX_CHILDREN &&
            forall c: Rope :: c in children ==> c in Repr && this !in c.Repr && c.Repr <= Repr && c.Valid()
          ) &&
          (!HasParent ==>
            |children| >= 2 &&
            |children| <= MAX_CHILDREN &&
            forall c: Rope :: c in children ==> c in Repr && this !in c.Repr && c.Repr <= Repr && c.Valid()
          )
      )
    }
  }
}


----


const max: int
const min: int

datatype Node<T> = Leaf(value: T) | InternalNode(children: seq<Rope<T>>)

class Rope<T> {
  ghost var Repr: set<object>

  var val: Node<T>
  var len: int

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (
      match this.val
      case Leaf(v) => true
      case InternalNode(children) =>
        |children| >= min &&
        |children| <= max &&
        (forall i :: 0 <= i < |children| ==> children[i] in Repr && Repr >= children[i].Repr && this !in children[i].Repr && children[i].Valid())
    )
  }

  constructor Init(v: T)
  {
    val := Leaf(v);
    len := 0;
    Repr := {this};
  }
}

----


module Rope {
  datatype Node<T> = Leaf(value: T) | InternalNode(children: seq<Rope<T>>)

  class Rope<T> {
    var val: Node<T>
    var len: int
    var max: int
    var min: int


    function sum<T>(c: seq<Rope<T>>): int
      requires |c| > 0
    {
      if |c| == 1 then countLeaves(c[0])
      else countLeaves(c[0]) + sum(c[1..])
    }


    function countLeaves(r: Rope): int
      decreases r
    {
      match r
      case Leaf(v) => 1
      case Node(children) =>
        if |children| <= 0 then 0
        else sum(children)
    }
  }
}


class Node {
  ghost var Contents: set<int>
  ghost var Repr: set<object>

  var data: int
  var nodes: set<Node>

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (|nodes| > 0 ==>
      forall n :: n in nodes ==> n in Repr && n.Repr <= Repr && this !in n.Repr && n.Valid()
    ) &&
    (|nodes| == 0 ==>
      Contents == {data})
  }
}


module Rope {
  datatype Node<T> = Leaf(value: T) | InternalNode(children: seq<Rope<T>>)

  class Rope<T> {
    var val: Node<T>
    var len: int
    var max: int
    var min: int


    function sum<T>(c: seq<Rope<T>>): int
      reads c
      requires |c| > 0
      decreases c
    {
      if |c| == 1 then c[0].countLeaves()
      else c[0].countLeaves() + sum(c[1..])
    }


    function countLeaves(): int
      reads this
      decreases this.val
    {
      match this.val
      case Leaf(v) => 1
      case InternalNode(children) =>
        if |children| <= 0 then 0
        else this.sum(children)
    }
  }
}





predicate validChildren(rope: Rope<T>)
  reads rope
{
  match rope.val
  case Leaf(t) => true    // todo: all children must be either leaves or internal nodes? not mixed?
  case InternalNode(children) => |children| >= min && |children| <= max && forall k: int :: 0 <= k < |children| ==> validChildren(children[k])
}




predicate childCount(rope: Rope<T>)
  reads rope
{
  match rope.val
  case Leaf(t) => true
  case InternalNode(children) => forall k: int :: 0 <= k < children.Length ==> minChildren(a[k])
}




datatype Rope<T> = Leaf(value: T) | Node(children: seq<Rope<T>>)

function sum<T>(c: seq<Rope<T>>): int
  requires |c| > 0
{
  if |c| == 1 then countLeaves(c[0])
  else countLeaves(c[0]) + sum(c[1..])
}


function countLeaves(r: Rope): int
  decreases r
{
  match r
  case Leaf(v) => 1
  case Node(children) =>
    if |children| <= 0 then 0
    else sum(children)
}



module Rope {
  datatype Node<T> = Leaf(value: T) | InternalNode(children: seq<Rope<T>>)

  class Rope<T> {
    var val: Node<T>
    var len: int
    var max: int
    var min: int

    function sum<T>(c: seq<Rope<T>>): int
      reads c
      decreases |c|
    {
      if |c| == 0 then 0
      else if |c| == 1 then c[0].countLeaves()
      else c[0].countLeaves() + sum(c[1..])
    }


    function countLeaves(): int
      reads this
      decreases this
    {
      match this.val
      case Leaf(v) => 1
      case InternalNode(children) => sum(children)
    }
  }
}


module Rope {
  datatype Node<T> = Leaf(value: T) | InternalNode(children: seq<Rope<T>>)

  class Rope<T> {
    var val: Node<T>
    var len: int
    var max: int
    var min: int

    predicate childCount(rope: Rope<T>)
      reads rope
    {
      match rope.val
      case Leaf(t) => true
      case InternalNode(children) => forall k: int :: 0 <= k < |rope.val.children| ==> minChildren(rope.val.children[k])
    }

    predicate minChildren(rope: Rope<T>)
      reads rope
    {
      match rope.val
      case Leaf(t) => true
      case InternalNode(children) => |rope.val.children| >= min && forall k: int :: 0 <= k < |rope.val.children| ==> minChildren(rope.val.children[k])
    }

  }
}





datatype Rope<T> = Leaf(value: T) | Node(children: seq<Rope<T>>)

function sum<T>(q: seq<Rope<T>>): int
  requires |q| > 0
{
  if |q| == 1 then toList(1, q[0])
  else toList(1, q[0]) + sum(q[1..])
}


function toList(d: int, t: Rope): int
  decreases t
{
  match t
  case Leaf(v) => d
  case Node(children) =>
    if |children| <= 0 then d
    else sum(children)
}








predicate childCount(rope: Rope<T>)
  reads rope
{
  match rope
  case Leaf(t) => true
  case
}



const max: int
const min: int

datatype Node<T> = Leaf(value: T) | InternalNode(children: seq<Rope<T>>)

class Rope<T> {
  ghost var Repr: set<object>

  var val: Node<T>
  var len: int

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    (
      match this.val
      case Leaf(v) => true
      case InternalNode(children) =>
        |children| >= min &&
        |children| <= max &&
        (forall i :: 0 <= i < |children| ==> children[i] in Repr && this !in children[i].Repr && children[i].Valid())
    )
  }

  constructor Init(v: T)
  {
    val := Leaf(v);
    len := 0;
    Repr := {this};
  }

}





lemma countLemma(rope: Rope<T>, i: int)
   requires i >= 0 && i < 5
   ensures rope.Node? && (LeafCount(Node(rope.children[0..i-1], i - 1) + LeafCount(rope.children[i], 1) == LeafCount(rope, i)
{

}

datatype Rope<T> = Leaf(value: T) | Node(children: seq<Rope<T>>)

function rec(t: Rope): seq<int> {
  match t
  case Leaf(v) => 1
  case Node(children) =>
    if |children| <= 0 then 1
    else toList(d+1, children[0]) + toList(d+1, Node(children[1..]))
}

function toList(d: int, t: Rope): seq<int>
  decreases t
{
  match t
  case Leaf(v) => [d]
  case Node(children) =>
    if |children| == 0 then [d]
    else toList(d+1, children[0]) + toList(d+1, Node(children[1..]))
}


function LeafCount<T>(rope: Rope<T>, i: int): int {
    match rope
    case Leaf(t) => 1
    case Node(children) =>
      if |children| == 0 || i == 0 then 0
      else LeafCount(children[0], 5) + LeafCount(Node(children[1..]), i - 1)
}



lemma sumLemma(s: seq<int>, i: int)
   requires i >= 0 && i < |s|
   ensures (sum(s, i) + s[i]) == sum(s, i + 1)
{

}
