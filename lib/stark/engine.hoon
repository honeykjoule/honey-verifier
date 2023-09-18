/+  *list, *merkle, *table, *proof-stream, permutation-arg, evaluation-arg, fri, chal=challenges,
    fock, stack-common=table-stack, util=table-util, jet, jet-common=table-jet, common=nock-common
::
~%  %stark  ..part  ~
::
::  TODO rename this to common
|%
+$  zerofier-cache
  $+  zerofier-cache
  (map (list @) (map @ [boundary=fpoly:f transition=fpoly:f terminal=fpoly:f]))
::
::  TODO this type could potentially be improved
::  all-table-funcs is really engine/prover.hoon specific, and is null when instantiating a verifier stark, while 
::  all-verifier-funcs is general, and is always valid
+$  stark-input
  $:  num-states=@
      input-data=@
      output-data=@
      table-names=(list term)
      all-table-funcs=(list table-funcs)
      all-verifier-funcs=(list verifier-funcs)
      table-base-widths=(list @)
      table-full-widths=(list @)
      cache=zerofier-cache
  ==
::
+$  table-relation
  $:  tables=(pair @ @)
      columns=(pair @ @)
  ==
--
::
~%  %stark-engine  ..stark-input  ~
::
=,  f
::
|_  stark-input
++  num-challenges     num-total-chals:chal
++  log-expand-factor  3  ::  could set to 1 for faster proofs but then small computations are maybe too small
++  expand-factor      (bex log-expand-factor)
++  security-level     17
++  num-colinear-t     (div security-level log-expand-factor)
++  num-randomizers    1  ::  TODO: must stay this num until we un-hardcode it elsewhere, then it will be ::  security-level
++  generator          7
::
++  permutation-args
  ^-  (list table-relation)
  ~
::
++  evaluation-args
  ^-  (list table-relation)
  ~
::
::  Working name: Just-in-time constraints or linking constraints...
::  Wraps existing stack table table-funcs with input linking constraint
::  We should probably have this function return a tuple of modified table-funcs
::  One per core, if we want to scale.
::
++  wrap-linking-constraints
  |=  [old=verifier-funcs [s=* f=*] prod=* challenges=(list felt)]
  ^-  verifier-funcs
  =/  rnd=(map term felt)
    (make-challenge-map:chal challenges %stack)
  =/  a    (~(got by rnd) %a)
  =/  b    (~(got by rnd) %b)
  =/  c    (~(got by rnd) %c)
  =/  alf  (~(got by rnd) %alf)
  ::
  =/  computation-fp=felt
    =<  dat
    %-  ~(push-all fstack:util (init-felt-stack:util alf))
    ~[tre:(build-tree-data:fock f a b c alf) tre:(build-tree-data:fock s a b c alf)]
  =/  product-fp=felt
    =<  dat
    %-  ~(push fstack:util (init-felt-stack:util alf))
    tre:(build-tree-data:fock prod a b c alf)
  ::
  =/  input-linking-boundary=multi-poly
    (mpsub (~(got by variables:stack-common) %cs) (mp-c computation-fp))
  =/  output-linking-terminal=multi-poly
    (mpsub (~(got by variables:stack-common) %ps) (mp-c product-fp))
  ::  TODO enable output linking
  (wrap-verifier-funcs old ~[input-linking-boundary] ~)
++  calc
  |_  [heights=(list @) jet-map=(map @tas @)]
  ::
  ++  omega           ~+((ordered-root fri-domain-len))
  ++  fri-domain-len  ~+((mul +(max-degree) expand-factor))
  ++  fri
    ~+
    ~(. fri:^fri generator omega fri-domain-len expand-factor num-colinear-t)
  ::
  ++  max-degree
    ::  XX totally broken. reconsider your life
    ~+
    %-  dec  %-  bex  %-  xeb  %-  dec
    %^  zip-roll  (range (lent heights))
      (zip heights table-full-widths same)
    |=  [[i=@ h=@ fw=@] d=_5]
    %+  max  d
    =/  funcs  (get-verifier-funcs i)
    =/  chals  (weights:sample num-challenges (mod (shax 0x0) p))
    %+  roll
      %-  zing
      :~  (unlabel-constraints:util (transition-constraints:funcs chals jet-map))
          (boundary-constraints:funcs chals)
          :: TODO: Include terminal constraints when computing max degree
          :: (this doesn't work at the moment).
          ::
          ::(terminal-constraints:funcs chals ~)
      ==
    |=  [constraint=multi-poly d=@]
    =/  degree-bounds
      %+  reap  (mul fw 2)
      (static-interpolant-degree-bound h num-randomizers)
    %+  max  d
    (sub (substitution-degree-bound constraint degree-bounds) (dec h))
  --
::
++  get-table-funcs
  |=  i=@
  ^-  table-funcs
  ~?  =(0 (lent all-table-funcs))  'all-table-funcs is empty. you may be calling a prover-side function from verify.'
  ~|("table-func i={<i>} not found. total table-funcs: {<(lent all-table-funcs)>}" (snag i all-table-funcs))
::
++  get-verifier-funcs
  |=  i=@
  ^-  verifier-funcs
  ~|("verifier-func i={<i>} not found. total verifier-funcs: {<(lent all-verifier-funcs)>}" (snag i all-verifier-funcs))
--
