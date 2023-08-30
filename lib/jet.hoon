/-  fock
/+  *goldilocks, *challenges, *bignum
=,  f
|%
++  ecc  secp256k1:secp:crypto
::
+$  jet-data  [name=@tas sam=tree-data:fock prod=tree-data:fock]
+$  jet-map  (map @tas @)
++  f0  (lift 0)
++  f1  (lift 1)
++  one-poly  (mp-c (lift 1))
++  zero-poly  (mp-c (lift 0))
++  var
  |_  variables=(map term multi-poly:f)
  ++  v
    |=  nam=term
    ^-  multi-poly:f
    ~+
    ~|  var-not-found+nam
    (~(got by variables) nam)
  --
::  map jet name -> index. used to pick which selector goes with which jet.
::  we sort the list so the order is deterministic.
++  compute-jet-map
  |=  jets=(list [@tas sam=* prod=*])
  ^-  jet-map
  ?~  jets  ~
  =/  jet-list=(list term)
    %-  sort
    :_  gth
    %~  tap  in
    %-  ~(gas in *(set @tas))
    (turn jets |=([name=@tas *] name))
  %-  ~(gas by *(map term @))
  (zip-up jet-list (range (lent jet-list)))
::
::  data for each atom in the sample used in the jet.
::
::  register: name of the register to hold the decoded atom
::  axis: axis into the sample of the atom. 1 if the sample is itself an atom.
::  interim-mem-set: to constrain degree we only multiply
::  one tuple onto the memory multiset per register.
::  So for more than one atom we need to know where to put the interim
::  memory multiset values. The last atom in the list should set this
::  to ~ which means multiply the final value onto the %mem register.
+$  atom-data  [register=@tas axis=@ interim-mem-set=(unit @tas)]
+$  register-map  (map @tas felt)
+$  encoder  [a=felt c=felt]
++  enc
  |_  st=encoder
  ++  encode
    |=  poly=multi-poly
    ^-  multi-poly
    (mpadd (mp-c a.st) (mpscal c.st poly))
  --
++  make-encoder
  |=  [vars=(map term multi-poly) challenges=(list felt)]
  ^-  encoder
  =/  r   ~(r rnd (make-challenge-map challenges %jet))
  [(r %a) (r %c)]
::
::  jet interface
++  jet-funcs
  ::
  ::
  $+  jet-funcs
  $_  ^|
  |%
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::  compute the actual jet.
  ++  compute
    |~  sample=*
    ^-  *
    0
  ::
  ::  write base row of the jet table for this jet
  ++  build
    |~  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ~
  ::
  ::  write extension columns for this jet
  ++  extend
    |~  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ::  transition constraints for this jet
  ++  transition-constraints
    |~  [vars=(map term multi-poly) challenges=(list felt)]
    *(map term multi-poly)
  --
::  TODO move these out of this file and into a dedicated directory
++  dec-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=(@ sam)
    (bsub sam 1)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?^  sam.jet-info  !!
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~[[%e0 1 ~]]
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    =/  v  ~(v var vars)
    =/  e  ~(. enc (make-encoder vars challenges))
    %-  ~(gas by *(map term multi-poly))
    :~  :-  %dec-poly
        (mpsub (v %prod) (encode.e (mpsub (v %e0) one-poly)))
    ==
  --
::
::
++  add-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=([@ @] sam)
    (badd -.sam +.sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?>  ?=([@ @] sam.jet-info)
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    :~  [%e1 2 (some %e2)]
        [%e3 3 ~]
    ==
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    =/  v  ~(v var vars)
    =/  e  ~(. enc (make-encoder vars challenges))
    %-  ~(gas by *(map term multi-poly))
    :~  :-  %add-poly
        (mpsub (v %prod) (encode.e (mpadd (v %e1) (v %e3))))
    ==
  --
++  neg-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=(@ sam)
    (bneg sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?^  sam.jet-info  !!
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  sub-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=([@ @] sam)
    (bsub -.sam +.sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?>  ?=([@ @] sam.jet-info)
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  mul-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=([@ @] sam)
    (bmul -.sam +.sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?>  ?=([@ @] sam.jet-info)
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  inv-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=(@ sam)
    (binv sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?^  sam.jet-info  !!
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  div-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=([@ @] sam)
    (bdiv -.sam +.sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?>  ?=([@ @] sam.jet-info)
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  lth-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  @
    ?>  ?=([@ @] sam)
    (lth -.sam +.sam)
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ?>  ?=([@ @] sam.jet-info)
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  schnorr-sign-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  bignum
    =>  .(sam ;;([sk=bignum m=bignum a=bignum] sam))
    (chunk (sign:schnorr:ecc [(merge sk.sam) (merge m.sam) (merge a.sam)]))
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    *(map @tas felt)
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
++  schnorr-verify-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  ?
    =>  .(sam ;;([pk=bignum m=bignum sig=bignum] sam))
    (verify:schnorr:ecc [(merge pk.sam) (merge m.sam) (merge sig.sam)])
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    *(map @tas felt)
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
++  hash-jet
  ^-  jet-funcs
  |%
  ++  compute
    |=  sam=*
    ^-  bignum
    (chunk (sham sam))
  ::
  ++  build
    |=  jet-info=[name=@tas sam=* prod=*]
    ^-  (map @tas felt)
    ~
  ::
  ++  atoms
    ^-  (list atom-data)
    ~
  ::
  ++  extend
    |=  [=jet-data challenges=(list felt)]
    ^-  (map @tas felt)
    ~
  ::
  ++  transition-constraints
    |=  [vars=(map term multi-poly) challenges=(list felt)]
    ^-  (map term multi-poly)
    ~
  --
::
::
::
::
++  jet-func-map
  %-  ~(gas by *(map @tas jet-funcs))
  :~  [%dec dec-jet]
      [%add add-jet]
      [%neg neg-jet]
      [%sub sub-jet]
      [%mul mul-jet]
      [%inv inv-jet]
      [%div div-jet]
      [%lth lth-jet]
      [%sosi schnorr-sign-jet]
      [%sove schnorr-verify-jet]
      [%hash hash-jet]
  ==
--
