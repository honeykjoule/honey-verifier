::  flib
!.
=>  %flib60
|%
::
::  Section 1 - Arithmetic
::
++  dec
  |=  a=@
  ~>  %dec
  =+  b=0
  |-  ^-  @
  ?:  =(a +(b))  b
  $(b +(b))
::
++  add
  |=  [a=@ b=@]
  ~>  %add
  ^-  @
  ?:  =(0 a)  b
  $(a (dec a), b +(b))
::
++  neg
  |=  a=@
  ~>  %neg
  =+  b=0
  |-  ^-  @
  ?:  =(0 (add a b))  b
  $(b +(b))
::
++  sub
  |=  [a=@ b=@]
  ~>  %sub
  ^-  @
  (add a (neg b))
::
++  mul
  |:  [a=`@`1 b=`@`1]
  ~>  %mul
  ^-  @
  =+  c=0
  |-
  ?:  =(0 a)  c
  $(a (dec a), c (add b c))
::
++  inv
  |=  a=@
  ~>  %inv
  ^-  @
  ?:  =(0 a)  !!
  =+  b=1
  |-  ^-  @
  ?:  =(1 (mul a b))  b
  $(b +(b))
::
++  div
  |=  [a=@ b=@]
  ~>  %div
  ^-  @
  (mul a (inv b))
::
::  Section 2 - Data Structures
::
++  list
  |$  [item]
  ::    null-terminated list
  ::
  ::  mold generator: produces a mold of a null-terminated list of the
  ::  homogeneous type {a}.
  ::
  $@(~ [i=item t=(list item)])
::
++  tree
  |$  [node]
  ::    tree mold generator
  ::
  ::  a `++tree` can be empty, or contain a node of a type and
  ::  left/right sub `++tree` of the same type. pretty-printed with `{}`.
  ::
  $@(~ [n=node l=(tree node) r=(tree node)])
::
++  each
  |$  [this that]
  ::    either {a} or {b}, defaulting to {a}.
  ::
  ::  mold generator: produces a discriminated fork between two types,
  ::  defaulting to {a}.
  ::
  $%  [%| p=that]
      [%& p=this]
  ==
::
++  unit
  |$  [item]
  ::    maybe
  ::
  ::  mold generator: either `~` or `[~ u=a]` where `a` is the
  ::  type that was passed in.
  ::
  $@(~ [~ u=item])
::
::  Section 3 - Miscellaneous
::
+$  u32  @uthirtytwo
+$  bignum
  ::  LSB order
  ::  empty array is 0
  [%bignum (each (list u32) @)]
::
++  lth
  |=  [a=@ b=@]
  ~>  %lth
  ^-  ?
  ?&  !=(a b)
      |-
      ?|  =(0 a)
          ?&  !=(0 b)
              $(a (dec a), b (dec b))
  ==  ==  ==
::
++  range                                                ::  range exclusive
  |=  [a=@ b=@]
  ?>  (lth a b)
  |-  ^-  (list @)
  ?:(=(a b) ~ [a $(a +(a))])
::
++  schnorr-sign
  |=  [sk=bignum m=bignum a=bignum]
  ~>  %sosi
  ^-  bignum
  !!
::
++  schnorr-verify
  |=  [pk=bignum m=bignum sig=bignum]
  ~>  %sove
  ^-  ?
  !!
::
++  hash
  ::  generic hash function: produces a hash of the provided noun
  |=  n=*
  ~>  %hash
  ^-  bignum
  !!
--
