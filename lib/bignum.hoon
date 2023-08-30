|%
::  mirrors bignum from flib
::  32 bits = 2^5 bits => bloq size of 5
+$  u32     @uthirtytwo
+$  bignum
  ::  LSB order (based on result of rip)
  ::  empty array is 0
  [%bignum (each (list u32) @)]
++  chunk
  |=  a=@
  ^-  bignum
  [%bignum %& (rip 5 a)]
++  merge
  |=  b=bignum
  ^-  @
  ?>  ?=(%& +<.b)  ::  fock always turns unchunked bignums into chunked case
  (rap 5 p.b)
++  valid
  ::  are all elements of the list valid big int chunks, i.e., less than u32.max_val
  |=  b=bignum
  ^-  ?
  ?>  ?=(%& +<.b)
  (levy p.b |=(c=@ (lth c (bex 32))))
--