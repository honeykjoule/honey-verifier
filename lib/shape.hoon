~%  %shape  ..part  ~
|%
::
::  dyck: produce the Dyck word describing the shape of a tree
++  dyck
  ~/  %dyck
  |=  t=*
  %-  flop
  ^-  (list @)
  =|  vec=(list @)
  |-
  ?@  t  vec
  $(t +.t, vec [1 $(t -.t, vec [0 vec])])
::
::  grow: grow the tree with given shape and leaves
++  grow
  ~/  %grow
  |=  [shape=(list @) leaves=(list @)]
  ^-  *
  ?>  ?&(=((lent shape) (mul 2 (dec (lent leaves)))) (valid-shape shape))
  ?~  shape
    ?>  ?=([@ ~] leaves)
      i.leaves
  =/  lr-shape  (left-right-shape shape)
  =/  split-idx  (shape-size -:lr-shape)
  =/  split-leaves  (split split-idx leaves)
  :-  (grow -:lr-shape -:split-leaves)
  (grow +:lr-shape +:split-leaves)
::
::  shape-size: size of the tree in #leaves described by a given Dyck word
++  shape-size
  ~/  %shape-size
  |=  shape=(list @)
  ^-  @
  (add 1 (div (lent shape) 2))
::
++  leaf-sequence
  ~/  %leaf-sequence
  |=  t=*
  %-  flop
  ^-  (list @)
  =|  vec=(list @)
  |-
  ?@  t  t^vec
  $(t +.t, vec $(t -.t))
::
++  num-of-leaves
  ~/  %num-of-leaves
  |=  t=*
  ?@  t  1
  %+  add
    (num-of-leaves -:t)
  (num-of-leaves +:t)
::
::  left-right-shape: extract left and right tree shapes from given tree shape
++  left-right-shape
  ~/  %left-right-shape
  |=  shape=(list @)
  ^-  [(list @) (list @)]
  ?>  (valid-shape shape)
  ?:  =((lent shape) 0)
    ~|  "Empty tree has no left subtree."
    !!
  =.  shape  (slag 1 shape)
  =/  stack-height  1
  =|  lefsh=(list @)
  |-
  ?:  =(stack-height 0)
    ?<  ?=(~ lefsh)
    [(flop t.lefsh) shape]
  ?<  ?=(~ shape)
  ?:  =(i.shape 0)
    $(lefsh [i.shape lefsh], shape t.shape, stack-height +(stack-height))
  $(lefsh [i.shape lefsh], shape t.shape, stack-height (dec stack-height))
::
++  axis-to-axes
  ~/  %axis-to-axes
  |=  axi=@
  ^-  (list @)
  =|  lis=(list @)
  |-
  ?:  =(1 axi)  lis
  =/  hav  (dvr axi 2)
  $(axi p.hav, lis [?:(=(q.hav 0) 2 3) lis])
::
::  valid-shape: computes whether a given vector is a valid tree shape
++  valid-shape
  ~/  %valid-shape
  |=  shape=(list @)
  ^-  ?
  =/  stack-height  0
  |-
  ?:  ?=(~ shape)
    ?:  =(stack-height 0)
      %.y
    %.n
  ?>  ?|(=(i.shape 0) =(i.shape 1))
  ?:  =(i.shape 0)
    $(shape t.shape, stack-height +(stack-height))
  ?:  =(stack-height 0)
    %.n
  $(shape t.shape, stack-height (dec stack-height))
::
::  split: split ~[a_1 ... a_n] into [~[a)1 ... a_{idx -1}] ~[a_{idx} ... a_n]]
++  split
  ~/  %split
  |=  [idx=@ lis=(list @)]
  ^-  [(list @) (list @)]
  ~|  "Index argument must be less than list length."
  ?>  (lth idx (lent lis))
  =|  lef=(list @)
  =/  i  0
  |-
  ?:  =(i idx)
    [(flop lef) lis]
  ?<  ?=(~ lis)
  $(lef [i.lis lef], lis t.lis, i +(i))
::
++  shape-axis-to-index
  ~/  %shape-axis-to-index
  |=  [tre=* axis=@]
  ^-  [dyck-index=@ leaf-index=@]
  =/  axes   (axis-to-axes axis)
  =/  shape  (dyck tre)
  =/  dyck-index  0
  =/  leaf-index  0
  |-
  ?~  axes
    [dyck-index leaf-index]
  =/  lr-shape  (left-right-shape shape)
  ?:  =(i.axes 2)
    $(axes t.axes, shape -.lr-shape)
  ?>  =(i.axes 3)
  %_  $
    axes        t.axes
    shape       +.lr-shape
    dyck-index  (add dyck-index (lent -.lr-shape))
    leaf-index  (add leaf-index (shape-size -.lr-shape))
  ==
--
