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
