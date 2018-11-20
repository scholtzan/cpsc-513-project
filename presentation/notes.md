# Notes

## Motivation

* wide variety of text editors
  * some are quite old and built on old concepts and technologies
  * some are new and rich on functionality but quite slow
* still need for good text editors
* one very recent project that found popularity in the text editor community but also Rust community is Xi Editor
  * Xi combines newer concepts for storing text to allow very high performance
    * core idea: modified rope data structure for storing text as well as an edit history
* Goal: verify that certain properties hold after applying operations to the data structure
  * not only interesting in a single user case but also in collaborative text editing (which xi intends to support in the future)
  * since ropes are such an important part of xi, it makes sense to verify that they are working correctly

## Background

### Xi-Editor

* modern editor with a backend written in Rust
  * found wide popularity in Rust community

* text engine and backend written in rust
  * frontends can be written in any language
* goal: high performance, Reliability, Beauty, developer friendliness

* one of the core concepts in the text engine is that the text is represented as ropes
  * special adapted rope


### Rope Data Structures

* ropes not new, relatively old concept and already used before to store text
* binary tree where each leaf holds a string and a length
* each node further up the tree holds the sum of the lengths of all the leafs in its left subtree
* node's weight is the sum of the left child's weight along with all of the nodes contained in its subtree


### Rope Data Structures in Xi-Editor

* BTree
* similar operations but a little bit different
* no delete, instead it is faster to copy parts of the tree that remain and concatenate them
* want to get slices of the tree instead of the entire text
  * only part of the text visible in the editor, don't have to transmit everything every time


## Verifying ropes

* Goal verifying xi-editor rope
* for this Define properties of ropes
* Verify that after applying operations, these properties still hold
* Verify that this also works for distributed ropes (collaborative editing)

* Approach: decided to first verify standard rope data structure (simpler), then verify rope data structure of xi-editor
  * standard rope simpler and gives me the opportunity to get familiar with verification and tools

### Dafny

* for verification first tried to use TLA+ and Pluscal
  * spend so much time and tried to implement simple B-Tree, but couldn't get it to work
* decided to look for alternative:
  * found Dafny
     * Language and verifier
     * looks very similar to C#, Java, Scala
     * Support verification through pre-conditions, post-conditions, loop invariants, ...
     * Dafny programs are translated into Boogie 2 which is used to generate first-order verification conditions that are passed to the SMT solver Z3
      * Boogie 2 = verification language
      * translation happens in a way that if the Boogie program is proved correct, then also the Dafny program is correct

### Properties Standard Rope

* Shares some properties with ordinary Binary Trees
* Every node has at most two children
  * can also have only one or none
* Only leaves contain data
  * don't have children
* Weight values of non-leaf nodes is the length of all children in the left subtree
* Weight values of leaf nodes is the length of the stored text


### Verifying Standard Rope

* implementation of rope in dafny
  * Rope is a node that can either be an internal node or a leave
  * nodes have lengths
  * need to have a ghost variable that is not part of the actual implementation but will help in proving things and make sure that recursion terminates while traversing the tree

* valid checks if general structure is valid
* validLen to check if len is correct
  * left subtree



### Properties Xi-Editor Rope

* Shares some properties with ordinary BTrees

* Not more than a certain number of children in each node
* At least certain number of children
  * all configurable using variables
*
