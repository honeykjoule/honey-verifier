/+  goldilocks
=,  f:goldilocks
|%
++  unlabel-constraints
  |=  mp=(map term multi-poly)
  ^-  (list multi-poly)
  (turn ~(tap by mp) tail)
+$  felt-stack
  $:  alf=felt
      alf-inv=felt
      len=@
      dat=felt
  ==
+$  multiset
  $:  bet=felt
      dat=felt
  ==
+$  tupler  (list felt)  :: challenges
::  TODO rename to init-fstack
++  init-felt-stack
  |=  alf=felt
  ^-  felt-stack
  =/  alf-inv=felt  (finv alf)
  [alf alf-inv 0 (lift 0)]
++  init-multiset
  |=  bet=felt
  ^-  multiset
  [bet (lift 1)]
++  fstack
  ::  bottom [a b c] top
  ::  empty stack [] <-> dat 0
  |_  fs=felt-stack
  ++  push
    ::  [a b c] =>  [a b c x]
    |=  x=felt
    ^-  felt-stack
    fs(len +(len.fs), dat (fadd (fmul dat.fs alf.fs) x))
  ++  pop
    ::  [a b c x] => [a b c]
    |=  x=felt
    ^-  felt-stack
    ?>  (gth len.fs 0)
    fs(len (dec len.fs), dat (fmul (fsub dat.fs x) alf-inv.fs))
  ++  push-all
    ::  [a b c] => [a b c x1 ... xn]
    |=  xs=(list felt)
    ^-  felt-stack
    %+  roll  xs
    |=  [x=felt fs-new=_fs]
    (~(push fstack fs-new) x)
  ++  push-bottom
    ::  [a b c] => [x a b c]
    |=  x=felt
    ^-  felt-stack
    ::  alf^len * x + dat.fs
    fs(len +(len.fs), dat (fadd (fmul (fpow alf.fs len.fs) x) dat.fs))
  ++  push-bottom-all
    ::  [a b c] => [x0 ... xn a b c]
    |=  xs=(list felt)
    ^-  felt-stack
    %+  roll  (flop xs)
    ::  let sx = (flop xs)
    ::    [a b c] => [sx2 sx1 sx0 a b c]
    ::  = [a b c] => [xs0 sx1 sx2 a b c]
    |=  [x=felt fs-new=_fs]
    (~(push-bottom fstack fs-new) x)
  ++  cons
    ::  stack cons: [a b], [c d] => [a b c d]
    |=  other=felt-stack
    ^-  felt-stack
    ?>  =(alf.fs alf.other)
    ::  alf^len(other) * dat.fs + dat.other
    %_  fs
      len  (add len.fs len.other)
      dat  (fadd (fmul (fpow alf.fs len.other) dat.fs) dat.other)
    ==
  ++  pop-all
    |=  xs=(list felt)
    ^-  felt-stack
    %+  roll  xs
    |=  [x=felt fs-new=_fs]
    ?>  (gth len.fs 0)
    (~(pop fstack fs-new) x)
  ::
  ++  is-empty  =(len.fs 0)
  --
++  mset
  |_  ms=multiset
  ++  mult
    |=  f=felt
    ^-  multiset
    ms(dat (fmul dat.ms (fsub bet.ms f)))
  ++  mult-all
    |=  fs=(list felt)
    ^-  multiset
    %+  roll  fs
    |=  [f=felt ms-new=_ms]
    (~(mult mset ms-new) f)
  --
::  A multiset based on the logarithmic derivative
+$  ld-mset
  $~  [(lift 0) (lift 1)]
  $:  bet=felt    :: beta - random challenge for polynomial
      dat=felt    :: data - actual value of multiset to write into trace
  ==
++  init-ld-mset
  |=  bet=felt
  ^-  ld-mset
  [bet (lift 1)]
::
++  ld
  |_  ms=ld-mset
  ::  Add f to the multiset n times
  ::
  ::  dat' = dat + n/(bet - f)
  ++  add
    |=  [f=felt n=@]
    ^-  ld-mset
    :-  bet.ms
    (fadd dat.ms (fmul (lift n) (finv (fsub bet.ms f))))
  :: Add a list of [felt, multiplicity] pairs to the multiset.
  :: Adds them one at a time starting with ms and returns a list of
  :: each intermediate memset in order.
  ++  add-all
    |=  l=(list [f=felt n=@])
    ^-  (list ld-mset)
    %+  spun  l
    |=  [[f=felt n=@] acc=_ms]
    =/  ret  (~(add ld acc) f n)
    [ret ret]
  --
::
::  Polynomial constraints for log derivative multiset
++  poly-ld
  |_  bet=felt
  ::
  ::  Add element v with n multiplicity to the old multiset in mold and store in
  ::  the new multiset mnew.
  ::
  ::  ldc' = ldc + n / (bet - value)
  ::  => (bet-value)*ldc' = (bet-value)*ldc + n
  ::  => (bet-value)*ldc' - [(bet-value)*ldc) + n] = 0
  ++  add
    |=  [mold=multi-poly mnew=multi-poly v=multi-poly n=multi-poly]
    ^-  multi-poly
    %+  mpsub  (mpmul (mpsub (mp-c bet) v) mnew)
    (mpadd n (mpmul (mpsub (mp-c bet) v) mold))
  --
::  Utilities for creating zeroes and tens for the log derivative memory multiset
++  subtree-ld-utils
  |_  cs=(list felt)
  :: Create a compressed felt of a zero access which can be added to a multiset
  ++  make-zero
    |=  [noun=multi-poly axis=multi-poly child=multi-poly]
    ^-  multi-poly
    (make-ten noun axis child noun child)
  ++  make-ten
    |=  $:  noun=multi-poly
            axis=multi-poly
            child=multi-poly
            new-noun=multi-poly
            new-child=multi-poly
        ==
    ^-  multi-poly
    (~(compress poly-tupler cs) ~[noun axis child new-noun new-child])
  --
::
++  tuple
  |_  cs=(list felt)
  ++  compress
    |=  fs=(list felt)
    ^-  felt
    %^  zip-roll  cs  fs
    |=  [[c=felt f=felt] acc=_(lift 0)]
    (fadd acc (fmul c f))
  --
++  poly-stack
  |_  [alf=felt alf-inv=felt vars=(map term multi-poly)]
  ++  v
    |=  nam=term
    ^-  multi-poly
    ~+
    ~|  var-not-found+nam
    (~(got by vars) nam)
  ++  push
    |=  [s=multi-poly nam=multi-poly]
    ^-  multi-poly
    (mpadd (mpscal alf s) nam)
  ++  push-all
    |=  [s=multi-poly nams=(list multi-poly)]
    ^-  multi-poly
    %+  roll  nams
    |:  [nam=`multi-poly`(mp-c (lift 0)) mp=`multi-poly`s]
    (push mp nam)
  ++  pop
    |=  [s=multi-poly nam=multi-poly]
    ^-  multi-poly
    (mpscal alf-inv (mpsub s nam))
  ++  pop-all
    |=  [s=multi-poly nams=(list multi-poly)]
    ^-  multi-poly
    %+  roll  nams
    |:  [nam=`multi-poly`(mp-c (lift 0)) mp=`multi-poly`s]
    (pop mp nam)
  --
::
++  poly-tupler
  |_  cs=(list felt)
  ++  compress
    |=  nams=(list multi-poly)
    ^-  multi-poly
    %^  zip-roll  cs  nams
    |=  [[c=felt n=multi-poly] acc=_(mp-c (lift 0))]
    (mpadd acc (mpscal c n))
  --
::
+$  poly-multiset  [bet=felt m=multi-poly]
++  poly-mset
  |_  ms=poly-multiset
  ++  mult
    |=  nam=multi-poly
    ^-  poly-multiset
    :-  bet.ms
    (mpmul m.ms (mpsub (mp-c bet.ms) nam))
  ++  mult-all
    |=  nams=(list multi-poly)
    ^-  poly-multiset
    %+  roll  nams
    |=  [nam=multi-poly acc=_ms]
    (~(mult poly-mset acc) nam)
  --
::
++  build-atom
  |=  [atom=felt a=felt b=felt c=felt]
  ^-  felt
  (fadd a (fmul c atom))
::
++  compress
  |=  [fs=(list felt) chals=(list felt)]
  ^=  felt
  %^  zip-roll  chals  fs
  |=  [[c=felt f=felt] acc=_(lift 0)]
  (fadd acc (fmul c f))
::
++  poly-nock-zero
  |_  [ms=poly-multiset tupler=(list felt)]
  ++  make-zero
    |=  [noun=multi-poly axis=multi-poly child=multi-poly]
    ^-  multi-poly
    =<  m
    %-  ~(mult poly-mset ms)
    (~(compress poly-tupler tupler) ~[noun axis child noun child])
  ++  make-zeroes
    |=  zs=(list [noun=multi-poly axis=multi-poly child=multi-poly])
    ^-  multi-poly
    =<  m
    %-  ~(mult-all poly-mset ms)
    %+  turn  zs
    |=  [noun=multi-poly axis=multi-poly child=multi-poly]
    (~(compress poly-tupler tupler) ~[noun axis child noun child])
  --
::
++  table-dbg
  |%
  ++  print-row
    |=  [row=(list felt) names=(list term)]
    ^-  @
    ~&  >  "["
    =+
      %+  turn  (zip-up row names)
      |=  [c=felt name=term]
      ~&  >  "{<name>}:{<c>}"
      0
    ~&  >  "]"
    0
  ::
  ++  print-table
    |=  col-names=(list term)
    |=  tab=(list fpoly)
    ^-  (list fpoly)
    =-  tab
    %^  zip  tab  (range (lent tab))
    |=  [r=fpoly i=@]
    ~&  >  "row={<i>}"
    (print-row (fpoly-to-list r) col-names)
  --
::
++  noun-utils
  |_  $:  noun-chals=[a=felt b=felt c=felt alf=felt]
          tuple-chals=[p=felt q=felt r=felt s=felt t=felt]
      ==
  ++  build-atom
    |=  atom=@
    ^-  felt
    ::  general format: (a * len) + (b * dyck) + (c * leaf)
    ::  for atoms: (a * 1) + (b * 0) + (c * <atom>)
    (fadd a.noun-chals (fmul c.noun-chals (lift atom)))
  ::
  ++  make-zero
    |=  [memset=multiset noun=felt axis=@ child=felt]
    ^-  multiset
    %-  ~(mult mset memset)
    %-  ~(compress tuple [p q r s t ~]:tuple-chals)
    ~[noun (build-atom axis) child noun child]
  ::
  ++  make-zeroes
    |=  [memset=multiset zs=(list [noun=felt axis=@ child=felt])]
    ^-  multiset
    %-  ~(mult-all mset memset)
    %+  turn  zs
    |=  [noun=felt axis=@ child=felt]
    %-  ~(compress tuple [p q r s t ~]:tuple-chals)
    ~[noun (build-atom axis) child noun child]
  ::
  ++  make-zero-ld
    |=  [memset=ld-mset noun=felt axis=@ child=felt num=@]
    ^-  ld-mset
    %-  ~(add ld memset)
    :_  num
    %-  ~(compress tuple [p q r s t ~]:tuple-chals)
    ~[noun (build-atom axis) child noun child]
  ::
  ++  make-zeroes-ld
    |=  [memset=ld-mset zs=(list [noun=felt axis=@ child=felt num=@])]
    ^-  (list ld-mset)
    %-  ~(add-all ld memset)
    %+  turn  zs
    |=  [noun=felt axis=@ child=felt num=@]
    :_  num
    %-  ~(compress tuple [p q r s t ~]:tuple-chals)
    ~[noun (build-atom axis) child noun child]
  --
++  noun-poly-utils
  |_  $:  noun-chals=[a=felt b=felt c=felt alf=felt]
          vars=(map term multi-poly)
      ==
  ++  v
    |=  nam=term
    ^-  multi-poly
    ~+
    ~|  var-not-found+nam
    (~(got by vars) nam)
  ++  build-atom-literal
    |=  atom=@
    ^-  multi-poly
    (mp-c (fadd a.noun-chals (fmul c.noun-chals (lift atom))))
  ++  build-atom-reg
    |=  atom=@tas
    ^-  multi-poly
    (mpadd (mp-c a.noun-chals) (mpscal c.noun-chals (v atom)))
  ++  build-atom-poly
    |=  atom=multi-poly
    ^-  multi-poly
    (mpadd (mp-c a.noun-chals) (mpscal c.noun-chals atom))
  --
--
