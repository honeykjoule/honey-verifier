|=  a=@
::  pk from https://github.com/urbit/urbit/blob/d52826e570/tests/sys/zuse/crypto/secp256k1.hoon#L119
=.  a  (div (mul a 2) (neg (neg 1)))
=/  sk=bignum  [%bignum %| 0x3]
=/  pk=bignum  [%bignum %| 0xf930.8a01.9258.c310.4934.4f85.f89d.5229.b531.c845.836f.99b0.8601.f113.bce0.36f9]
=/  msg        [%bignum %| 'hello']
=/  aux        [%bignum %| 0]
=/  sig  (schnorr-sign sk msg aux)
=/  success
  (schnorr-verify pk msg sig)
[success a]
