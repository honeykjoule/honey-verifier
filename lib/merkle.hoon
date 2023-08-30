::  merkle
|%
::
+$  merk         [h=@uv n=$@(@ (pair merk merk))]
::
+$  vector       (list @)         ::  replace with bitvector
::
+$  merk-cap     (list @uv)         ::  hashes of vertices at height h
::
+$  merk-proof   [root=@uv path=(list @uv)]
::
++  build-merk
  |=  n=*
  ^-  merk
  ?@  n  [(shax n) n]
  =/  l=merk  $(n -.n)
  =/  r=merk  $(n +.n)
  [(shax (cat 3 h.l h.r)) l r]
::
++  index-to-axis
  |=  [h=@ i=@]
  ^-  axis
  =/   min  (bex (dec h))
  (add min i)
::
++  list-to-balanced-merk
  |=  lis=(list @)
  ^-  (pair @ merk)
  =-  [h (build-merk t)]
  (list-to-balanced-tree lis)
::
++  list-to-balanced-tree
  |=  lis=(list @)
  ^-  [h=@ t=*]
  :-  (xeb (lent lis))
  |-
  ?>  ?=(^ lis)
  ?:  ?=([@ ~] lis)
    i.lis
  ?:  ?=([@ @ ~] lis)
    [i.lis i.t.lis]
  =/  len  (lent lis)
  =/  l=*
    ?:  =((mod len 2) 0)
      $(lis (scag (div len 2) `(list @)`lis))
    $(lis (scag +((div len 2)) `(list @)`lis))
  =/  r=*
    ?:  =((mod len 2) 0)
      $(lis (slag (div len 2) `(list @)`lis))
    $(lis (slag +((div len 2)) `(list @)`lis))
  [l r]
::
++  build-merk-proof
  |=  [=merk axis=@]
  ^-  merk-proof
  ?:  =(0 axis)  !!
  :-  h.merk
  ?:  =(1 axis)  ~
  =/  pat  (axis-to-path axis)
  =|  lis=(list @)
  |-
  ?~  pat  lis
  ?>  ?=(^ n.merk)
  ?:  i.pat
    $(pat t.pat, lis [h.q.n.merk lis], merk p.n.merk)
  $(pat t.pat, lis [h.p.n.merk lis], merk q.n.merk)
::
++  axis-to-path
  |=  axi=@
  ^-  (list ?)
  =|  lis=(list ?)
  |-
  ?:  =(1 axi)  lis
  =/  hav  (dvr axi 2)
  $(axi p.hav, lis [=(q.hav 0) lis])
::
++  build-merk-cap
  =|  lis=merk-cap
  |=  [=merk h=@]
  ^-  merk-cap
  ?:  =(h 0)
    [h.merk lis]
  ?>  ?=(^ n.merk)
  =/  l=merk-cap  $(h (dec h), merk p.n.merk)
  =/  r=merk-cap  $(h (dec h), merk q.n.merk)
  (weld l r)
::
++  verify-merk-proof
  |=  [leaf=@ axis=@ merk-proof]
  ^-  ?
  ?:  =(0 axis)  %.n
  |-
  ?:  =(1 axis)  =(root leaf)
  ?~  path           %.n
  =*  sib  i.path
  ?:  =(2 axis)
    =(root (shax (cat 3 leaf sib)))
  ?:  =(3 axis)
    =(root (shax (cat 3 sib leaf)))
  ?:  =((mod axis 2) 0)
    $(axis (div axis 2), leaf (shax (cat 3 leaf sib)), path t.path)
  $(axis (div (dec axis) 2), leaf (shax (cat 3 sib leaf)), path t.path)
::
++  verify-merk-proof-to-cap
  |=  [leaf=@ axis=@ cap=merk-cap merk-proof]
  ^-  ?
  =/  xeb-axi  (xeb axis)
  =/  cap-index  (sub axis (bex (dec xeb-axi)))
  ?>  =((lent cap) (bex +(xeb-axi)))
  ?:  =(0 axis)  %.n
  ?:  =(1 axis)  =(root leaf)
  |-
  ?:  =(cap-index axis)
    =(leaf (snag cap-index cap))
  ?~  path           %.n
  =*  sib  i.path
  ?:  =((mod axis 2) 0)
    $(axis (div axis 2), leaf (shax (cat 3 leaf sib)), path t.path)
  $(axis (div (dec axis) 2), leaf (shax (cat 3 sib leaf)), path t.path)
--

