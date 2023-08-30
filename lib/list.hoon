~%  %list-lib  ..part  ~
|%
++  i
  ::  reverse index lookup:
  ::    given an item and a list,
  ::    produce the index of the item in the list
  ::
  ~+
  |=  [item=@tas lis=(list @tas)]
  ::  todo make this wet
  ^-  @
  (need (find ~[item] lis))
++  zip-up
  ~/  %zip-up
  |*  [p=(list) q=(list)]
  ^-  (list _?>(?&(?=(^ p) ?=(^ q)) [i.p i.q]))
  (zip p q same)
::
++  zip
  ~/  %zip
  |*  [p=(list) q=(list) r=gate]
  ^-  (list _?>(?&(?=(^ p) ?=(^ q)) (r i.p i.q)))
  |-
  ?:  ?&(?=(~ p) ?=(~ q))
    ~
  ?.  ?&(?=(^ p) ?=(^ q))  ~|(%zip-fail-unequal-lengths !!)
  [i=(r i.p i.q) t=$(p t.p, q t.q)]
::
++  sum
  ~/  %sum
  |=  lis=(list @)
  ^-  @
  %+  roll  lis
  |=  [a=@ r=@]
  (add a r)
::
++  mul-all
  ~/  %mul-all
  |=  [lis=(list @) x=@]
  ^-  (list @)
  %+  turn  lis
  |=(a=@ (mul a x))
::
++  add-all
  ~/  %add-all
  |=  [lis=(list @) x=@]
  ^-  (list @)
  %+  turn  lis
  |=(a=@ (add a x))
::
++  mod-all
  ~/  %mod-all
  |=  [lis=(list @) x=@]
  ^-  (list @)
  %+  turn  lis
  |=(a=@ (mod a x))
::
++  zip-roll
  ~/  %zip-roll
  |*  [p=(list) q=(list) r=_=>(~ |=([[* *] *] +<+))]
  |-  ^+  ,.+<+.r
  ?~  p
    ?~  q
      +<+.r
    !!
  ?.  ?=(^ q)  ~|(%zip-roll-fail-unequal-lengths !!)
  $(p t.p, q t.q, r r(+<+ (r [i.p i.q] +<+.r)))
::
++  gen-random-list
  ~/  %gen-random-list
  |=  [n=@ p=@ rng=_og]
  ^-  [(list @) _og]
  ?:  =(n 0)  `rng
  =-  [l rng]
  %+  roll  (range n)
  |=  [i=@ [l=(list @) rng=_rng]]
  =^  ran  rng  (rads:rng p)
  [[ran l] rng]
::
++  range
  ~/  %range
  |=  $@(@ ?(@ (pair @ @)))
  ^-  (list @)
  ?@  +<  ?~(+< ~ (gulf 0 (dec +<)))
  (gulf p (dec q))
::
++  mevy
  ::  mevy: maybe error levy
  ::  product: ~ if no failures or (some err) of the first error encountered
  |*  [a=(list) b=$-(* (unit))]
  =*  b-product  _?>(?=(^ a) (b i.a))
  |-  ^-  b-product
  ?~  a  ~
  ?^  err=(b i.a)  err
  $(a t.a)
--
