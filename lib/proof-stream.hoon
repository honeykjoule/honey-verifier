/-  *proof-stream
/+  *list, *goldilocks
::
|%
::
++  proof-stream
  |_  stream-state
  ++  push
    |=  dat=proof-data
    ^-  stream-state
    :-  (snoc objects dat)
    read-index
  ::
  ++  pull
    ^-  [proof-data stream-state]
    ?>  (lth read-index (lent objects))
    :-  (snag read-index objects)
    [objects +(read-index)]
  ::
  ++  prover-fiat-shamir
    ^-  @uv
    (sham serialize)
  ::
  ++  verifier-fiat-shamir
    ^-  @uv
    (sham (scag read-index serialize))
  ::
  ++  serialize
    ^-  (list @)
    %+  turn  objects
    |=  d=proof-data
    ?-  -.d
      %merk-root    p.d
      %computation  (jam p.d)
      %terminals    (jam p.d)
      %codeword     (jam p.d)
      %merk-path    (jam p.d)
      %merk-paths   (jam [a b c]:d)
      %jets         (jam p.d)
    ==
  --
::
++  sample
  |%
  ++  new-indices
    |=  [num=@ seed=@ bound=@]
    ^-  (list @)
    %+  turn  (range num)
    |=  i=@
    (index:sample (shax (cat 3 seed i)) bound)
  ::
  ++  indices
    |=  [seed=@ size=@ reduced-size=@ num=@]
    ^-  (list @)
    ~|  "cannot sample more indices than available in last codeword"
    ?>  (lte num reduced-size)
    =|  indices=(list @)
    =|  reduced-indices=(list @)
    =|  counter=@
    |-
    ?:  (gte (lent indices) num)
      (flop indices)
    =/  index          (index:sample (shax (cat 3 seed counter)) size)
    =/  reduced-index  (mod index reduced-size)
    ?^  (find reduced-index^~ reduced-indices)
      $(counter +(counter))
    %_  $
      counter          +(counter)
      indices          [index indices]
      reduced-indices  [reduced-index reduced-indices]
    ==
  ::
  ++  index
    |=  [r=@ size=@]
    =-  (mod - size)
    (generic r)
  ::
  ++  field
    |=  r=@
    ^-  felt:f
    %-  frep:f
    %+  turn  (gulf 1 ext-degree)
    |=  sal=@
    =-  (mod - p:f)
    (generic (cat 3 r sal))
  ::
  ++  generic
    |=  r=@
    ^-  @
    %+  roll  (rip 3 r)
    |=  [b=@ acc=@]
    (con (lsh 3 acc) b)
  ::
  ++  weights
    |=  [n=@ seed=@]
    ^-  (list felt:f)
    %+  turn  (gulf 1 n)
    |=  i=@
    (field (shax (cat 3 seed i)))
  --
--
