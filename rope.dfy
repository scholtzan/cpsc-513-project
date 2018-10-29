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
      case InternalNode(children) => forall k: int :: 0 <= k < children.Length ==> minChildren(a[k])
    }

    predicate minChildren(rope: Rope<T>)
      reads rope
    {
      match rope.val
      case Leaf(t) => true
      case InternalNode(children) => children.Length >= min && forall k: int :: 0 <= k < children.Length ==> minChildren(a[k])
    }

  }
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
