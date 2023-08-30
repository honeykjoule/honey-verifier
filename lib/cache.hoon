/+  *table, nock-verifier
=,  f
|%
++  eng  engine:nock-verifier
++  height-triples
  ^-  (list (list @))
  :~  [1 1 4 ~]
      [16 4 64 ~]
  ==
::
++  precompute
  ^-  zerofier-cache:stark:nock-verifier
  %+  roll  height-triples
  |=  [triple=(list @) cax=zerofier-cache:stark:nock-verifier]
  =/  calc  ~(. calc:eng triple)
  =/  domain  eval-domain:fri:calc
  %+  ~(put by cax)  triple
  (compute-zerofiers domain triple)
::
::  height: target padding height for given table
::          defined to be the next smallest power of 2
::          e.g. if (lent p.table) == 5, ~(height tab table) == 8
::
++  omicron
  |=  len=@
  ~+((ordered-root len))
::
++  compute-zerofiers
  |=  [domain=(list @) heights=(list @)]
  ^-  (map @ [fpoly fpoly fpoly])
  %-  ~(gas by *(map @ [fpoly fpoly fpoly]))
  %+  turn  heights
  |=  height=@
  =/  omicron   (omicron height)
  :-  height
  :+  (boundary-zerofier-inverse domain)
    (transition-zerofier-inverse domain height omicron)
  (terminal-zerofier-inverse domain omicron)
::
++  boundary-zerofier-inverse
  |=  domain=(list @)
  ^-  fpoly
  %-  init-fpoly:f
  %-  mass-inversion:f
  %+  turn  domain
  |=(a=felt:f (fsub:f a (lift:f 1)))
::
++  transition-zerofier-inverse
  |=  [domain=(list @) height=@ omicron=@]
  ^-  fpoly
  %-  init-fpoly
  %^    zip
      %+  turn  domain
      |=  d=felt
      (fsub d (finv (lift omicron)))
    %-  mass-inversion
    %+  turn  domain
    |=  d=felt
    (fsub (fpow d height) (lift 1))
  fmul
::
++  terminal-zerofier-inverse
  |=  [domain=(list @) omicron=@]
  ^-  fpoly
  %-  init-fpoly
  %-  mass-inversion
  %+  turn  domain
  |=  a=felt
  (fsub a (finv (lift omicron)))
--
