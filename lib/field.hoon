/-  field
/+  *list
::
::  prelude: field constants, type definitions, etc.
~%  %f50  ..part  ~
|%
::  field characteristic p = 2^64 - 2^32 + 1 = (2^32)*3*5*17*257*65537 + 1
++  p  0xffff.ffff.0000.0001
::
::  radix r = 2^64
++  r  0x1.0000.0000.0000.0000
::
::  r-mod-p = r - p
++  r-mod-p  4.294.967.295
::
::  r^2 mod p = (2^32 - 1)^2 = 2^64 - 2*2^32 + 1 = p - 2^32
++  r2  0xffff.fffe.0000.0001
::
::  r*p
++  rp  0xffff.ffff.0000.0001.0000.0000.0000.0000
::
::  ord(g) = p - 1, i.e. g generates the (multiplicative group of the) field
++  g  7
::
::  ord(h) = 2^32, i.e. h = (2^32)th root of unity
++  h  20.033.703.337
::  TODO find a better way to do this. 
::       hack because /+  *list imports stdlib, which shadows poly:field
::       but, normal solutions such as doing =,  field don't work
::       because core structure changes, messing up jets
::
++  belt   belt:field
++  felt   felt:field
++  melt   melt:field
++  bpoly  bpoly:field
++  fpoly  fpoly:field
++  poly   poly:field
++  multi-poly  multi-poly:field
--
::
~%  %field-basic  ..p  ~
::
::  base field math
|%
::
::  based: in base field?
++  based
  ~/  %based
  |=  a=@
  ^-  ?
  (lth a p)
::
::  badd: base field addition
++  badd
  ~/  %badd
  |=  [a=belt b=belt]
  ^-  belt
  ?>  ?&((based a) (based b))
  (mod (add a b) p)
::
::  bneg: base field negation
++  bneg
  ~/  %bneg
  |=  a=belt
  ^-  belt
  ?>  (based a)
  ?:  =(a 0)
    0
  (sub p a)
::
::  bsub: base field subtraction
++  bsub
  ~/  %bsub
  |=  [a=belt b=belt]
  ^-  belt
  (badd a (bneg b))
::
::  bmul: base field multiplication
++  bmul
  ~/  %bmul
  |=  [a=belt b=belt]
  ^-  belt
  ?>  ?&((based a) (based b))
  (mod (mul a b) p)
::
::  Montgomery reduction: special algorithm; computes x•r^{-1} = (xr^{-1} mod p).
::
::    Note this is the inverse of x --> r•x, so conceptually this is a map from
::    Montgomery space to the base field.
::
::    It's `special` bc we gain efficiency by examining the general algo by hand
::    and deducing the form of the final answer, which we can code directly.
::    If you compute the algo by hand you will find it convenient to write
::    x = x_2*2^64 + x_1*2^32 + x_0 where x_2 is a 64-bit number less than
::    p (so x < pr) and x_1, x_0 are 32-bit numbers.
::    The formula comes, basically, to (x_2 - (2^32(x_0 + x_1) - x_1 - f*p));
::    f is a flag bit for the overflow of 2^32(x_0 + x_1) past 64 bits.
::    "Basically" means we have to add p if the formula is negative.
++  mont-reduction
  ~/  %mont-reduction
  |=  x=melt
  ^-  belt
  ?>  (lth x rp)
  =/  x1  (cut 5 [1 1] x)
  =/  x2  (rsh 6 x)
  =/  c
    =/  x0  (end 5 x)
    (lsh 5 (add x0 x1))
  =/  f   (rsh 6 c)
  =/  d   (sub c (add x1 (mul f p)))
  ?:  (gte x2 d)
    (sub x2 d)
  (sub (add x2 p) d)
::
::  montiply: computes a*b = (abr^{-1} mod p); note mul, not fmul: avoids mod p reduction!
++  montiply
  ~/  %montiply
  |:  [a=`melt`r-mod-p b=`melt`r-mod-p]
  ^-  belt
  ~+
  ?>  ?&((based a) (based b))
  (mont-reduction (mul a b))
::
::  montify: transform to Montgomery space, i.e. compute x•r = xr mod p
++  montify
  ~/  %montify
  |=  x=belt
  ^-  melt
  ~+
  (montiply x r2)
::
::  bpow: fast modular exponentiation using x^n mod p = 1*(xr)*...*(xr)
++  bpow
  ~/  %bpow
  |=  [x=belt n=@]
  ^-  belt
  ?>  (based x)
  ~+
  %.  [1 (montify x) n]
  |=  [y=melt x=melt n=@]
  ^-  melt
  ?:  =(n 0)
    y
  ::  parity flag
  =/  f=@  (end 0 n)
  ?:  =(0 f)
    $(x (montiply x x), n (rsh 0 n))
  $(y (montiply y x), x (montiply x x), n (rsh 0 n))
::
::  binv: base field multiplicative inversion
++  binv
  ~/  %binv
  |=  x=belt
  ^-  belt
  ~+
  |^
  ~|  "x not in field"
  ?>  (based x)
  ~|  "cannot divide by 0"
  ?<  =(x 0)
  =/  y=melt  (montify x)
  =/  y2    (montiply y (montiply y y))
  =/  y3    (montiply y (montiply y2 y2))
  =/  y5    (montiply y2 (montwop y3 2))
  =/  y10   (montiply y5 (montwop y5 5))
  =/  y20   (montiply y10 (montwop y10 10))
  =/  y30   (montiply y10 (montwop y20 10))
  =/  y31   (montiply y (montiply y30 y30))
  %-  mont-reduction
  %+  montiply  y
  =+  (montiply (montwop y31 32) y31)
  (montiply - -)
  ++  montwop
    |=  [a=melt n=@]
    ^-  melt
    ~+
    ?>  (based a)
    ?:  =(n 0)
      a
    $(a (montiply a a), n (sub n 1))
  --
::
::  bdiv: base field division
++  bdiv
  ~/  %bdiv
  |=  [a=belt b=belt]
  ^-  belt
  (bmul a (binv b))
::
::  ordered-root: from n = 2^s, gives h^(2^(32 - s)), which has order n
++  ordered-root
  ~/  %ordered-root
  |=  n=@
  ^-  @
  ?>  (lte n (bex 32))
  ?>  =((dis n (dec n)) 0)
  =/  order  (bex 32)
  (bpow h (div order n))
--
::
::  basic polynomial methods independent of extension field deg, and bpoly math
~%  %polynomial-basic  ..based  ~
|%
::
::  bcan: gives the canonical leading-zero-stripped representation of p(x)
++  bcan
  |=  p=poly
  ^-  poly
  =.  p  (flop p)
  |-
  ?~  p
    ::  TODO: fix this
    ~[0]
  ?:  =(i.p 0)
    $(p t.p)
  (flop p)
::
::  bdegree: computes the degree of a polynomial
::
::    Not just (dec (lent p)) because we need to discard possible extraneous "leading zeroes"!
::    Be very careful in using lent vs. degree!
::    NOTE: degree(~) = 0 when it should really be -∞ to preserve degree(fg) = degree(f) +
::    degree(g). So if we use the RHS of this equation to compute the LHS the cases where
::    either are the zero polynomial must be handled separately.
++  bdegree
  |=  p=poly
  ^-  @
  =/  cp=poly  (bcan p)
  ?~  cp  0
  (dec (lent cp))
::
::  bzero-extend: make the zero coefficients for powers of x higher than deg(p) explicit
++  bzero-extend
  |=  [p=poly much=@]
  ^-  poly
  (weld p (reap much 0))
::
::  binary-zero-extend: extend with zeroes until the length is the next power of 2
++  bbinary-zero-extend
  |=  [p=poly]
  ^-  poly
  ?~  p  ~
  =/  l=@  (lent p)
  ?:  =((dis l (dec l)) 0)
    p
  (bzero-extend p (sub (bex (xeb l)) l))
::
::  poly-to-map: takes list (a_i) and makes map i --> a_i
++  poly-to-map
  |=  p=poly
  ^-  (map @ felt)
  =|  mp=(map @ felt)
  =/  i=@  0
  |-
  ?~  p
    mp
  $(mp (~(put by mp) i i.p), p t.p, i +(i))
::
::  map-to-poly: inverse of poly-to-map
++  map-to-poly
  ::  keys need to be 0, 1, 2, ... which is enforced by "got" below
  |=  mp=(map @ felt)
  ^-  poly
  =|  p=poly
  =/  size=@  ~(wyt by mp)
  =/  i=@  size
  |-
  ?:  =(i 0)
    p
  $(p [(~(got by mp) (dec i)) p], i (dec i))
::
++  init-bpoly
  ~/  %init-bpoly
  |=  poly=(list belt)
  ^-  bpoly
  ?:  =(~ poly)
    zero-bpoly
  ?>  (lth (lent poly) (bex 32))
  :-  (lent poly)
  =/  high-bit  (lsh [0 (mul (bex 6) (lent poly))] 1)
  (add (rep 6 poly) high-bit)
::
++  bpoly-to-list
  ~/  %bpoly-to-list
  |=  bp=bpoly
  ^-  poly
  ?>  !=(len.bp 0)
  (snip (rip 6 dat.bp))
::
++  zero-bpoly  ~+((init-bpoly ~[0]))
++  one-bpoly   ~+((init-bpoly ~[1]))
::
::  bpadd: base field polynomial addition
++  bpadd
  ~/  %bpadd
  |:  [bp=`bpoly`zero-bpoly bq=`bpoly`zero-bpoly]
  ^-  bpoly
  ?>  &(!=(len.bp 0) !=(len.bq 0))
  =/  p  (bpoly-to-list bp)
  =/  q  (bpoly-to-list bq)
  =/  lp  (lent p)
  =/  lq  (lent q)
  =/  m  (max lp lq)
  =:  p  (weld p (reap (sub m lp) 0))
      q  (weld q (reap (sub m lq) 0))
    ==
  %-  init-bpoly
  (zip p q badd)
::
::  bpneg: additive inverse of a base field polynomial
++  bpneg
  ~/  %bpneg
  |=  bp=bpoly
  ^-  bpoly
  ?>  !=(len.bp 0)
  =/  p  (bpoly-to-list bp)
  %-  init-bpoly
  (turn p bneg)
::
::  bpsub:  field polynomial subtraction
++  bpsub
  ~/  %bpsub
  |=  [p=bpoly q=bpoly]
  ^-  bpoly
  (bpadd p (bpneg q))
::
::  bpscal:  multiply base field scalar c by base field polynomial p
++  bpscal
  ~/  %bpscal
  |=  [c=belt bp=bpoly]
  ^-  bpoly
  =/  p  (bpoly-to-list bp)
  %-  init-bpoly
  %+  turn  p
  (cury bmul c)
::
::  bpmul: base field polynomial multiplication; naive algorithm; necessary for fmul!
++  bpmul
  |:  [bp=`bpoly`one-bpoly bq=`bpoly`one-bpoly]
  ^-  bpoly
  ?>  &(!=(len.bp 0) !=(len.bq 0))
  %-  init-bpoly
  ?:  ?|(=(bp zero-bpoly) =(bq zero-bpoly))
    ~[0]
  =/  p  (bpoly-to-list bp)
  =/  q  (bpoly-to-list bq)
  =/  v=(list melt)
    %-  weld
    :_  (turn p montify)
    (reap (dec (lent q)) 0)
  =/  w=(list melt)  (flop (turn q montify))
  =|  prod=poly
  |-
  ?~  v
    (flop prod)
  %=  $
    v  t.v
    ::
      prod
    :_  prod
    %.  [v w]
    ::  computes a dot product of v and w by implicitly zero-extending if lengths unequal
    ::  we don't actually zero-extend to save a constant time factor
    |=  [v=(list melt) w=(list melt)]
    ^-  melt
    =|  dot=belt
    |-
    ?:  ?|(?=(~ v) ?=(~ w))
      (mont-reduction dot)
    $(v t.v, w t.w, dot (badd dot (montiply i.v i.w)))
  ==
::
::  bpdvr: base field polynomial division with remainder
::
::    Analogous to integer division: (bpdvr a b) = [q r] where a = bq + r and degree(r)
::    < degree(b). (Using the mathematical degree where degree(~) = -∞.)
::    This implies q and r are unique.
::
::    Algorithm is the usual one taught in high school.
++  bpdvr
  ~/  %bpdvr
  |:  [ba=`bpoly`one-bpoly bb=`bpoly`one-bpoly]
  ^-  [q=bpoly r=bpoly]
  ?>  &(!=(len.ba 0) !=(len.bb 0))
  =/  a  (bpoly-to-list ba)
  =/  b  (bpoly-to-list bb)
  ::  rem = remainder; a is effectively first candidate since (degree a) < (degree b) => done
  ::  rem, b are written high powers to low, as in high school algorithm
  =^  rem  b
    :-  (flop (bcan a))
    (flop (bcan b))
  ~|  "Cannot divide by the zero polynomial."
  ?<  ?=(~ b)
  =/  db  (dec (lent b))
  ::  db = 0, rem = ~ => condition below this one is false and we fail the subsequent assertion;
  ::  Problem is (degree ~) = 0 is wrong mathematically; so we simply handle db = 0 separately.
  ?:  =(db 0)
    :_  zero-bpoly
    (bpscal (binv i.b) ba)
  ::  coeff = next coefficient added to the quotient, starting with highest power
  =|  coeff=belt
  =|  quot=poly
  |-
  ?:  (lth (bdegree (flop rem)) db)
    :-  (init-bpoly quot)
    (init-bpoly (bcan (flop rem)))
  ?<  ?=(~ rem)
  =/  new-coeff  (bdiv i.rem i.b)
  =/  new-rem
    %-  bpoly-to-list
    (bpsub (init-bpoly rem) (bpscal new-coeff (init-bpoly b)))
  ?<  ?=(~ new-rem)
  %=  $
    coeff  new-coeff
    quot  [new-coeff quot]
    rem   t.new-rem
  ==
::
::  bpdiv: a/b for base field polynomials; q component of bpdvr
++  bpdiv
  ~/  %bpdiv
  |=  [a=bpoly b=bpoly]
  ^-  bpoly
  q:(bpdvr a b)
::
::  bpmod: a mod b for base field polynomials; r component of bpdvr
++  bpmod
  ~/  %bpmod
  |=  [a=bpoly b=bpoly]
  ^-  bpoly
  r:(bpdvr a b)
::
::  bpegcd: base field polynomial extended Euclidean algorithm
::
::    Gives gcd = d and u, v such that d = ua + vb from the Euclidean algorithm.
::    The algorithm is based on repeatedly dividing-with-remainder: a = bq + r,
::    b = rq_1 + r_1, etc. since gcd(a, b) = gcd(b, r) = ... (exercise) etc. The
::    pairs being divided in sequence are (a, b), (b, r), (r, r_1), etc. with update
::    rule new_first = old_second, new_second = remainder upon division of old_first
::    and old_second. One stops when a division by 0 would be necessary to generate
::    new_second, and then d = gcd is the second of the last full pair generated.
::    To see that u and v exist, repeatedly write d in terms of earlier and earlier
::    dividing pairs. To progressively generate the correct u, v, reexamine the original
::    calculation and write the remainders in terms of a, b at each step. Since each
::    remainder depends on the previous two, the same is true of u and v. This is the
::    reason for e.g. m1.u, which semantically is `u at time minus 1`; one can verify
::    the given initialization of these quantities.
::    NOTE: mathematically, gcd is not unique (only up to a scalar).
++  bpegcd
  ~/  %bpegcd
  |=  [a=bpoly b=bpoly]
  ^-  [d=bpoly u=bpoly v=bpoly]
  =/  [u=[m1=bpoly m2=bpoly] v=[m1=bpoly m2=bpoly]]
    :-  zero-bpoly^one-bpoly
    one-bpoly^zero-bpoly
  |-
  ?:  =((bcan (bpoly-to-list b)) ~[0])
    :+  a
      m2.u
    m2.v
  =/  q-r  (bpdvr a b)
  %=  $
    a  b
    b  r:q-r
    u  [(bpsub m2.u (bpmul q:q-r m1.u)) m1.u]
    v  [(bpsub m2.v (bpmul q:q-r m1.v)) m1.v]
  ==
::
::  deg3-mont-reduction: a(x)(x^4)^{-1} mod (x^3 - x + 1), (degree a) < 7, w/o poly division
::
::    This is Montgomery reduction, ported to the world of polynomials. We have "prime"
::    p = x^3 - x + 1, "radix" r = x^4 with inverse mod p given by r^{-1} = -r' = -(x+1).
++  deg3-mont-reduction
  |=  ba=bpoly
  ^-  bpoly
  =/  a  (bpoly-to-list ba)
  %-  init-bpoly
  ?:  =(~[0] a)
    ~[0]
  =|  [u=belt v=belt w=belt]
  =/  idx  0
  |-
  ?~  a
    ~[u v w]
  ?:  =(idx 0)
    $(idx +(idx), a t.a, u (bsub u i.a), v (bsub v i.a))
  ?:  =(idx 1)
    $(idx +(idx), a t.a, v (bsub v i.a), w (bsub w i.a))
  ?:  =(idx 2)
    $(idx +(idx), a t.a, u (badd u i.a), v (bsub v i.a), w (bsub w i.a))
  ?:  =(idx 3)
    $(idx +(idx), a t.a, u (badd u i.a), w (bsub w i.a))
  ?:  =(idx 4)
    $(idx +(idx), a t.a, u (badd u i.a))
  ?:  =(idx 5)
    $(idx +(idx), a t.a, v (badd v i.a))
  ?:  =(idx 6)
    $(idx +(idx), a t.a, w (badd w i.a))
  ::  degree < 7 is enforced by this crash
  ~|  "Degree too high to reduce!"
  !!
::
::  deg3-pmontiply: analog of Montgomery multiplication
::
::    Will work for any a, b such that (degree (bpmul a b)) < 7, but will primarily be
::    called from within the main door with deg set to 3, so (degree (bpmul a b)) < 5.
++  deg3-pmontiply
  |=  [a=bpoly b=bpoly]
  ^-  bpoly
  (deg3-mont-reduction (bpmul a b))
::
::  deg3-pmontify: calculate a(x)•x^4 mod (x^3 - x +1); i.e. send a(x) to poly-Montgomery space
++  deg3-pmontify
  |=  ba=bpoly
  ^-  bpoly
  =/  a  (bpoly-to-list ba)
  ?>  (lte (lent a) 3)
  ::  2x^2 -3x +2 is (x^4)^2 mod (x^3 - x + 1)
  (deg3-pmontiply (init-bpoly a) (init-bpoly ~[2 (bneg 3) 2]))
::
::  deg3-pfastex
++  deg3-pfastex
  |=  [xb=bpoly n=@]
  ^-  bpoly
  ~+
  =/  x  (bpoly-to-list xb)
  ?>  (lte (lent x) 3)
  %.  [(init-bpoly ~[1]) (deg3-pmontify xb) n]
  |=  [y=bpoly x=bpoly n=@]
  ^-  bpoly
  ?:  =(n 0)
    y
  ::  parity flag
  =/  f=@  (end 0 n)
  ?:  =(0 f)
    $(x (deg3-pmontiply x x), n (rsh 0 n))
  $(y (deg3-pmontiply y x), x (deg3-pmontiply x x), n (rsh 0 n))
--
~%  %field-extension  ..bcan  ~
::
::  fm: general field math, supporting extensions of degree = deg
|_  deg=@
::
::  deg-to-irp
++  deg-to-irp
  ^-  (map @ bpoly)
  %-  ~(gas by *(map @ bpoly))
  :~  [1 (init-bpoly ~[0 1])]
      [2 (init-bpoly ~[2 18.446.744.069.414.584.320 1])]
      [3 (init-bpoly ~[1 18.446.744.069.414.584.320 0 1])]
  ==
::
++  lift
  |=  =belt
  ~+
  ^-  felt
  %-  frep
  :-  belt
  (reap (dec deg) 0)
::
++  drop
  |=  =felt
  ^-  belt
  ::  inverse of lift
  ::  (lift 7) => <felt ~[7 0 0 0]>
  ::  (snag 0 <felt ~[7 0 0 0]>)  => 7
  (snag 0 (felt-to-list felt))
::
++  felt-to-list
  |=  fel=felt
  ^-  (list belt)
  (bpoly-to-list [deg fel])
::
++  zero-fpoly
  ~+
  ^-  fpoly
  (init-fpoly ~[(lift 0)])
::
++  one-fpoly
  ~+
  ^-  fpoly
  (init-fpoly ~[(lift 1)])
::
++  init-fpoly
  ~/  %init-fpoly
  |=  poly=(list felt)
  ^-  fpoly
  ?:  =(~ poly)
    zero-fpoly
  ?>  (levy poly fat)
  ?>  (lth (lent poly) (bex 32))
  :-  (lent poly)
  =/  high-bit  (lsh [0 (mul (bex 6) (mul deg (lent poly)))] 1)
  (add (rep [6 deg] poly) high-bit)
::
::  fcan: gives the canonical leading-zero-stripped representation of p(x)
++  fcan
  |=  p=poly
  ^-  poly
  =.  p  (flop p)
  |-
  ?~  p
    ~
  ?:  =(i.p (lift 0))
    $(p t.p)
  (flop p)
::
::  fdegree: computes the degree of a polynomial
++  fdegree
  |=  p=poly
  ^-  @
  =/  cp=poly  (fcan p)
  ?~  cp  0
  (dec (lent cp))
::
::  fzero-extend: make the zero coefficients for powers of x higher than deg(p) explicit
++  fzero-extend
  |=  [p=poly much=@]
  ^-  poly
  (weld p (reap much (lift 0)))
::
++  lift-to-fpoly
  ~/  %lift-to-fpoly
  |=  poly=(list belt)
  ^-  fpoly
  ?>  (levy poly based)
  (init-fpoly (turn poly lift))
::
++  fpoly-to-list
  ~/  %fpoly-to-list
  |=  fp=fpoly
  ^-  (list felt)
  ~|  "len.fp must not be 0"
  ?>  !=(len.fp 0)
  %+  turn  (snip (rip [6 deg] dat.fp))
  |=  elem=@
  ^-  felt
  %+  add  elem
  (lsh [6 deg] 1)
::
++  fop
  ~/  %fop
  =|  fp=fpoly
  |%
  ++  flop
    ^-  fpoly
    =/  p  to-poly
    %-  init-fpoly
    (^flop p)
  ::
  ++  can
    ^-  fpoly
    =/  p  to-poly
    %-  init-fpoly
    (fcan p)
  ::
  ++  zip
    ~/  %zip
    |=  [gp=fpoly a=$-([felt felt] felt)]
    ^-  fpoly
    ?>  =(len.fp len.gp)
    :-  len.fp
    =/  i  0
    |-
    ?:  =(i len.fp)
      dat.fp
    =/  fi  (snag i)
    =/  gi  (~(snag fop gp) i)
    $(i +(i), fp (stow i (a fi gi)))
  ::
  ++  turn
    ~/  %turn
    |=  a=$-(felt felt)
    ^-  fpoly
    :-  len.fp
    =/  i  0
    |-
    ?:  =(i len.fp)
      dat.fp
    $(i +(i), fp (stow i (a (snag i))))
  ::
  ++  zero-extend
    ~/  %zero-extend
    |=  n=@
    :-  (add len.fp n)
    =/  i  0
    =/  dat  dat.fp
    |-
    ?:  =(i n)
      dat
    %_  $
      dat  dat:(~(snoc fop [(add len.fp i) dat]) (lift 0))
      i    +(i)
    ==
  ::
  ++  weld
    ~/  %weld
    |=  fp2=fpoly
    ^-  fpoly
    :-  (add len.fp len.fp2)
    =/  i  0
    =/  dat  dat.fp
    |-
    ?:  =(i len.fp2)
      dat
    %_  $
      dat  dat:(~(snoc fop [(add len.fp i) dat]) (~(snag fop fp2) i))
      i    +(i)
    ==
  ::
  ++  head
    ~/  %head
    ^-  felt
    (snag 0)
  ::
  ++  rear
    ~/  %rear
    ^-  felt
    (snag (dec len.fp))
  ::
  ++  snag
    ~/  %snag
    |=  i=@
    ^-  felt
    ?>  (lth i len.fp)
    =/  high-bit  (lsh [0 (mul (bex 6) deg)] 1)
    %+  add  high-bit
    (cut 6 [(mul i deg) deg] dat.fp)
  ::
  ++  scag
    ~/  %scag
    |=  i=@
    ^-  fpoly
    ?:  =(i 0)
      zero-fpoly
    ?:  (gte i len.fp)  fp
    :-  i
    =/  high-bit  (lsh [0 (mul i (mul (bex 6) deg))] 1)
    %+  add  high-bit
    (cut 6 [0 (mul i deg)] dat.fp)
  ::
  ++  slag
    ~/  %slag
    |=  i=@
    ^-  fpoly
    ?:  (gte i len.fp)
      zero-fpoly
    [(sub len.fp i) (rsh [6 (mul i deg)] dat.fp)]
  ::
  ++  snoc
    ~/  %snoc
    |=  j=felt
    ^-  fpoly
    ?>  (fat j)
    :-  +(len.fp)
    =/  new-high-bit  (lsh [0 (mul (bex 6) (mul deg +(len.fp)))] 1)
    =/  old-high-bit  (lsh [0 (mul (bex 6) (mul deg len.fp))] 1)
    %^  sew  6
      [(mul len.fp deg) deg j]
    (sub (add new-high-bit dat.fp) old-high-bit)
  ::
  ++  stow
    ~/  %stow
    |=  [i=@ j=felt]
    ^-  fpoly
    ?>  (fat j)
    ?>  (lth i len.fp)
    =/  item  (rep 6 (snip (rip 6 j)))
    [len.fp (sew 6 [(mul i deg) deg item] dat.fp)]
  ::
  ++  to-poly
    ^-  poly
    (fpoly-to-list fp)
  --
::
::  fat: is the atom a felt?
++  fat
  ~/  %fat
  |=  a=@
  ^-  ?
  ~+
  =/  v  (rip 6 a)
  ?&  =((lent v) +(deg))
      (levy v based)
  ==
::
::  field rip: rip a felt into a list of belts
++  frip
  ~/  %frip
  |=  a=felt
  ^-  (list belt)
  ~+
  ?>  (fat a)
  (bpoly-to-list [deg a])
::
::  frep: inverse of frip; list of belts are rep'd to a felt
++  frep
  ~/  %frep
  |=  x=(list belt)
  ^-  felt
  ~+
  ?>  =((lent x) deg)
  ?>  (levy x based)
  dat:(init-bpoly x)
::
::  fadd: field addition
++  fadd
  ~/  %fadd
  |:  [a=`felt`(lift 0) b=`felt`(lift 0)]
  ~+
  ~|  a
  ?>  (fat a)
  ~|  b
  ?>  (fat b)
  %-  frep
  (zip (frip a) (frip b) badd)
::
::  fneg: field negation
++  fneg
  ~/  %fneg
  |:  a=`felt`(lift 0)
  ~+
  ?>  (fat a)
  %-  frep
  (turn (frip a) bneg)
::
::  fsub: field subtraction
++  fsub
  ~/  %fsub
  |:  [a=`felt`(lift 0) b=`felt`(lift 0)]
  ^-  felt
  ~+
  (fadd a (fneg b))
::
::  fmul: field multiplication
++  fmul
  ~/  %fmul
  |:  [a=`felt`(lift 1) b=`felt`(lift 1)]
  ^-  felt
  ~+
  ~|  `@ux`a
  ?>  (fat a)
  ~|  `@ux`b
  ?>  (fat b)
  =/  result-poly
    %-  bpoly-to-list
    %+  bpmod
      (bpmul deg^a deg^b)
    (~(got by deg-to-irp) deg)
  %-  frep
  %+  bzero-extend  result-poly
  (sub deg (lent result-poly))
::
::  finv: field inversion
++  finv
  ~/  %finv
  |:  a=`felt`(lift 1)
  ^-  felt
  ~+
  ?>  (fat a)
  ?<  =(a (lift 0))
  =/  egcd=[d=bpoly u=bpoly v=bpoly]
    %+  bpegcd
      (~(got by deg-to-irp) deg)
    deg^a
  =/  d  (bpoly-to-list d.egcd)
  =/  u  (bpoly-to-list u.egcd)
  =/  v  (bpoly-to-list v.egcd)
  ?>  =((bdegree d) 0)
  ?<  ?=(~ d)
  =/  result-poly
    %-  bpoly-to-list
    (bpscal (binv i.d) v.egcd)
  %-  frep
  %+  bzero-extend  result-poly
  (sub deg (lent result-poly))
::
::  mass-inversion: inverts list of elements by cleverly performing only a single inversion
++  mass-inversion
  ~/  %mass-inversion
  |=  lis=(list felt)
  ^-  (list felt)
  |^
  =/  all-prods  (accumulate-products lis)
  ?<  ?=(~ all-prods)
  =.  lis    (flop lis)
  =/  acc    (finv i.all-prods)
  =/  prods  t.all-prods
  =|  invs=(list felt)
  |-
  ?~  prods
    [acc invs]
  ?<  ?=(~ lis)
  %=  $
    lis    t.lis
    prods  t.prods
    acc    (fmul acc i.lis)
    invs    [(fmul acc i.prods) invs]
  ==
  ++  accumulate-products
    |=  lis=(list felt)
    ^-  (list felt)
    =|  res=(list felt)
    =/  acc  (lift 1)
    |-
    ?~  lis
      res
    ?:  =(i.lis (lift 0))
      ~|  "Cannot invert 0!"
      !!
    =/  new  (fmul acc i.lis)
    $(acc new, res [new res], lis t.lis)
  --
::
::  fdiv: division of field elements
++  fdiv
  ~/  %fdiv
  |:  [a=`felt`(lift 1) b=`felt`(lift 1)]
  ^-  felt
  ~+
  (fmul a (finv b))
::
::  fpow: field power; computes x^n
++  fpow
  ~/  %fpow
  |:  [x=`felt`(lift 1) n=`@`0]
  ^-  felt
  ~+
  ?>  (fat x)
  ~?  (gte (met 3 n) (met 3 (lift 0)))  "fpow: n is wayy too high and is likely a felt on accident."
  ::  TODO: why is this not working?
  ::?:  =(deg 3)
  ::  dat:(deg3-pfastex deg^x n)
  %.  [(lift 1) x n]
  |=  [y=felt x=felt n=@]
  ^-  felt
  ?>  (fat y)
  ?:  =(n 0)
    y
  ::  parity flag
  =/  f=@  (end 0 n)
  ?:  =(0 f)
    $(x (fmul x x), n (rsh 0 n))
  $(y (fmul y x), x (fmul x x), n (rsh 0 n))
::
::  general field polynomial methods and math
::
::  fpadd: field polynomial addition
++  fpadd
  ~/  %fpadd
  |:  [fp=`fpoly`zero-fpoly fq=`fpoly`zero-fpoly]
  ^-  fpoly
  ?>  &(!=(len.fp 0) !=(len.fq 0))
  =/  p  ~(to-poly fop fp)
  =/  q  ~(to-poly fop fq)
  =/  lp  (lent p)
  =/  lq  (lent q)
  =/  m  (max lp lq)
  =:  p  (weld p (reap (sub m lp) (lift 0)))
      q  (weld q (reap (sub m lq) (lift 0)))
    ==
  %-  init-fpoly
  (zip p q fadd)
::
::  fpneg: additive inverse of a field polynomial
++  fpneg
  ~/  %fpneg
  |:  fp=`fpoly`zero-fpoly
  ^-  fpoly
  ?>  !=(len.fp 0)
  ~+
  =/  p  ~(to-poly fop fp)
  %-  init-fpoly
  (turn p fneg)
::
::  fpscal: scale a polynomial by a field element
++  fpscal
  ~/  %fpscal
  |:  [c=`felt`(lift 1) fp=`fpoly`one-fpoly]
  ^-  fpoly
  ~+
  =/  p  ~(to-poly fop fp)
  %-  init-fpoly
  %+  turn
    p
  (cury fmul c)
::
::  fpsub:  field polynomial subtraction
++  fpsub
  ~/  %fpsub
  |:  [p=`fpoly`zero-fpoly q=`fpoly`zero-fpoly]
  ^-  fpoly
  ~+
  ?>  &(!=(len.p 0) !=(len.q 0))
  (fpadd p (fpneg q))
::
::  +ntt: number theoretic transform based on anatomy of a stark
++  ntt
  ~/  %ntt
  |=  [fp=fpoly root=felt]
  ^-  fpoly
  ~+
  ?:  =(len.fp 1)
    fp
  =/  half  (div len.fp 2)
  ?>  =((fpow root len.fp) (lift 1))
  ?<  =((fpow root half) (lift 1))
  =/  odds
    %+  ntt
      %-  init-fpoly
      %+  murn  (range len.fp)
      |=  i=@
      ?:  =(0 (mod i 2))
        ~
      `(~(snag fop fp) i)
    (fmul root root)
  =/  evens
    %+  ntt
      %-  init-fpoly
      %+  murn  (range len.fp)
      |=  i=@
      ?:  =(1 (mod i 2))
        ~
      `(~(snag fop fp) i)
    (fmul root root)
  %-  init-fpoly
  %+  turn  (range len.fp)
  |=  i=@
  %+  fadd  (~(snag fop evens) (mod i half))
  %+  fmul  (fpow root i)
  (~(snag fop odds) (mod i half))
::
::  fft: Discrete Fourier Transform (DFT) with Fast Fourier Transform (FFT) algorithm
++  fft
  ~/  %fft
  |=  p=fpoly
  ^-  fpoly
  ~+
  ~|  "fft: must have power-of-2-many coefficients."
  ?>  =(0 (dis len.p (dec len.p)))
  (ntt p (lift (ordered-root len.p)))
::
::  ifft: Inverse DFT with FFT algorithm
++  ifft
  ~/  %ifft
  |=  p=fpoly
  ^-  fpoly
  ~+
  ~|  "ifft: must have power-of-2-many coefficients."
  ?>  =((dis len.p (dec len.p)) 0)
  %+  fpscal  (lift (binv len.p))
  (ntt p (lift (binv (ordered-root len.p))))
::
::  fpmul-naive: high school polynomial multiplication
++  fpmul-naive
  ~/  %fpmul-naive
  |=  [fp=fpoly fq=fpoly]
  ^-  fpoly
  ~+
  =/  p  ~(to-poly fop fp)
  =/  q  ~(to-poly fop fq)
  %-  init-fpoly
  ?:  ?|(=(~ p) =(~ q))
    ~
  =/  v=(list felt)
    %-  weld
    :_  p
    (reap (dec (lent q)) (lift 0))
  =/  w=(list felt)  (flop q)
  =|  prod=poly
  |-
  ?~  v
    (flop prod)
  %=  $
    v  t.v
    ::
      prod
    :_  prod
    %.  [v w]
    ::  computes a dot product of v and w by implicitly zero-extending if lengths unequal
    ::  we don't actually zero-extend to save a constant time factor
    |=  [v=(list felt) w=(list felt)]
    ^-  felt
    =/  dot=felt  (lift 0)
    |-
    ?:  ?|(?=(~ v) ?=(~ w))
      dot
    $(v t.v, w t.w, dot (fadd dot (fmul i.v i.w)))
  ==
::
::  fpmul-fast: polynomial multiplication with fft
++  fpmul-fast
  ~/  %fpmul-fast
  |=  [fp=fpoly fq=fpoly]
  ^-  fpoly
  ~+
  =:  fp  ~(can fop fp)
      fq  ~(can fop fq)
    ==
  ?:  ?|(=(fp zero-fpoly) =(fq zero-fpoly))
    zero-fpoly
  =*  deg-p  len.fp
  =*  deg-q  len.fq
  =/  deg-prod  (bex (xeb (dec (add deg-p deg-q))))
  %~  can  fop
  %-  ifft
  %+  %~  zip  fop
      (fft (~(zero-extend fop fp) (sub deg-prod deg-p)))
    (fft (~(zero-extend fop fq) (sub deg-prod deg-q)))
  fmul
::
::  fpmul: polynomial multiplication
++  fpmul
  ~/  %fpmul
  |:  [fp=`fpoly`one-fpoly fq=`fpoly`one-fpoly]
  ^-  fpoly
  ~+
  ?:  |(=(len.fp 0) =(len.fq 0))
    (init-fpoly ~[(lift 0)])
  =/  p  ~(to-poly fop fp)
  =/  q  ~(to-poly fop fq)
  ?:  (lth (add (fdegree p) (fdegree q)) 8)
    (fpmul-naive fp fq)
  (fpmul-fast fp fq)
::
::  fppow: compute (p(x))^k
++  fppow
  ~/  %fppow
  |=  [fp=fpoly k=@]
  ^-  fpoly
  ~+
  ?>  !=(len.fp 0)
  %.  [(init-fpoly ~[(lift 1)]) fp k]
  |=  [q=fpoly p=fpoly k=@]
  ?:  =(k 0)
    q
  =/  f=@  (end 0 k)
  ?:  =(f 0)
    %_  $
      p  (fpmul p p)
      k  (rsh 0 k)
    ==
  %_  $
    q  (fpmul q p)
    p  (fpmul p p)
    k  (rsh 0 k)
  ==
::
::  fpdvr
++  fpdvr
  ~/  %fpdvr
  |:  [fa=`fpoly`one-fpoly fb=`fpoly`one-fpoly]
  ^-  [q=fpoly r=fpoly]
  ~+
  ?>  &(!=(len.fa 0) !=(len.fb 0))
  =/  a  ~(to-poly fop fa)
  =/  b  ~(to-poly fop fb)
  =^  rem  b
    :-  (flop (fcan a))
    (flop (fcan b))
  ~|  "Cannot divide by the zero polynomial."
  ?<  ?=(~ b)
  =/  db  (dec (lent b))
  ?:  =(db 0)
    :_  (init-fpoly ~)
    (fpscal (finv i.b) fa)
  =|  quot=poly
  |-
  ?:  (lth (fdegree (flop rem)) db)
    :-  (init-fpoly quot)
    %-  init-fpoly
    (fcan (flop rem))
  ?<  ?=(~ rem)
  =/  new-coeff  (fdiv i.rem i.b)
  =/  new-rem
    %~  to-poly  fop
    %+  fpsub
      (init-fpoly rem)
    (fpscal new-coeff (init-fpoly b))
  ?<  ?=(~ new-rem)
  %=  $
    quot  [new-coeff quot]
    rem   t.new-rem
  ==
::
::  fpdiv: polynomial division
::
::    Quasilinear algo, faster than naive. Based on the formula
::    rev(p/q) = rev(q)^{-1} rev(p) mod x^{deg(p) - deg(q) + 1}.
::    Why?: we can compute rev(f)^{-1} mod x^l quickly.
++  fpdiv
  ~/  %fpdiv
  |:  [p=`fpoly`one-fpoly q=`fpoly`one-fpoly]
  ^-  fpoly
  ~+
  ?>  &(!=(len.p 0) !=(len.q 0))
  |^
  =:  p  ~(can fop p)
      q  ~(can fop q)
    ==
  ?:  =(q zero-fpoly)
    ~|  "Cannot divide by the zero polynomial!"
    !!
  ?:  =(p zero-fpoly)
    zero-fpoly
  =/  [c=felt f=fpoly]  (con-mon p)
  =/  [d=felt g=fpoly]  (con-mon q)
  =/  lead=felt  (fdiv c d)
  =/  rf=fpoly  ~(flop fop f)
  =/  rg=fpoly  ~(flop fop g)
  =/  df=@  (fdegree ~(to-poly fop f))
  =/  dg=@  (fdegree ~(to-poly fop g))
  ?:  (lth df dg)
    zero-fpoly
  =/  dq=@  (sub df dg)
  %+  fpscal
    lead
  %~  flop  fop
  %.  +(dq)
  %~  scag  fop
  (fpmul (pinv-mod-x-to +(dq) rg) rf)
  ::
  ::  pinv-mod-x-to: computes p^{-1} mod x^l
  ++  pinv-mod-x-to
    |=  [l=@ p=fpoly]
    ^-  fpoly
    (~(scag fop (hensel-lift-inverse p (xeb l))) l)
  ::
  ::  hensel-lift-inverse: if p_0 = 1, compute p^{-1} mod x^{2^l} (l = level parameter below)
  ::
  ::    Given a(x) such that p(x)a(x) = 1 mod x^{2^i}, then a*p = 1 + x^{2^i}s(x) (see s below).
  ::    Letting t(x) = -a(x)*s(x) mod x^{2^i}, then p's inverse modulo x^{2^{i+1}} is
  ::    a(x) + x^{2^i}t(x)
  ++  hensel-lift-inverse
    |=  [p=fpoly level=@]
    ^-  fpoly
    ~|  "Polynomial must have constant term equal to 1."
    ?>  =(~(head fop p) (lift 1))
    ::  since p_0 = 1, 1 is p's inverse mod x (x = x^{2^0})
    =/  inv=fpoly  one-fpoly
    ::  have solution for level i, i.e. mod x^{2^i}, bootstrapping to next level
    =/  i=@  0
    |-
    ?:  =(i level)
      inv
    =/  bex-i=@  (bex i)
    =/  s  (~(slag fop (fpmul p inv)) bex-i)
    =/  t  (~(scag fop (fpmul (fpscal (lift (bneg 1)) inv) s)) bex-i)
    $(i +(i), inv (fpadd inv (pmul-by-x-to bex-i t)))
  ::
  ::  pmul-by-x-to: multiply by x to the power l
  ++  pmul-by-x-to
    |=  [l=@ p=fpoly]
    ^-  fpoly
    %.  p
    ~(weld fop (init-fpoly (reap l (lift 0))))
  ::
  ::  con-mon: split p(x)!=0 uniquely into c*f(x) where c is constant f monic
  ++  con-mon
    |=  fp=fpoly
    ^-  [felt fpoly]
    ~+
    =.  fp  ~(flop fop ~(can fop fp))
    ~|  "Cannot accept the zero polynomial!"
    ?<  =(zero-fpoly fp)
    :-  ~(head fop fp)
    %~  flop  fop
    (fpscal (finv ~(head fop fp)) fp)
  --
::
::  fpmod: f(x) mod g(x), gives remainder r of f/g
++  fpmod
  ~/  %fpmod
  |:  [f=`fpoly`one-fpoly g=`fpoly`one-fpoly]
  ^-  fpoly
  ~+
  ::  f - g*q, stripped of leading zeroes
  %~  can  fop
  (fpsub f (fpmul g (fpdiv f g)))
::
::  fpeval: evaluate a polynomial with Horner's method.
++  fpeval
  ~/  %fpeval
  |:  [fp=`fpoly`one-fpoly x=`felt`(lift 1)]
  ^-  felt
  ~+
  =/  p  ~(to-poly fop fp)
  =.  p  (flop p)
  =/  res=@  (lift 0)
  |-
  ?~  p    !!
  ?~  t.p
    (fadd (fmul res x) i.p)
  ::  based on p(x) = (...((a_n)x + a_{n-1})x + a_{n-2})x + ... )
  $(res (fadd (fmul res x) i.p), p t.p)
::
::  codeword: compute a Reed-Solomon codeword, i.e. evaluate a poly on a domain
++  codeword
  ~/  %codeword
  |=  [fp=fpoly fdomain=fpoly]
  ^-  fpoly
  ?:  =(fdomain zero-fpoly)
    fdomain
  ?:  =(1 len.fdomain)
    (init-fpoly (fpeval fp ~(head fop fdomain))^~)
  =/  half  (div len.fdomain 2)
  =/  lef-zerofier  (zerofier (~(scag fop fdomain) half))
  =/  rig-zerofier  (zerofier (~(slag fop fdomain) half))
  =/  lef
    $(fp (fpmod fp lef-zerofier), fdomain (~(scag fop fdomain) half))
  =/  rig
    $(fp (fpmod fp rig-zerofier), fdomain (~(slag fop fdomain) half))
  (~(weld fop lef) rig)
::
++  zerofier
  ~/  %zerofier
  |=  fdomain=fpoly
  ^-  fpoly
  ~+
  ?:  =(fdomain zero-fpoly)
    fdomain
  ?:  =(1 len.fdomain)
    %-  init-fpoly
    [(fneg ~(head fop fdomain)) (lift 1) ~]
  =/  half  (div len.fdomain 2)
  =/  lef   $(fdomain (~(scag fop fdomain) half))
  =/  rig   $(fdomain (~(slag fop fdomain) half))
  (fpmul lef rig)
::
::  interpolate: compute the poly of minimal degree which evaluates to values on domain
++  interpolate
  ~/  %interpolate
  |=  [fdomain=fpoly fvalues=fpoly]
  ^-  fpoly
  ~+
  ?>  =(len.fdomain len.fvalues)
  ?:  =(fdomain zero-fpoly)
    fdomain
  ?:  =(1 len.fdomain)  fvalues
  =/  half  (div len.fdomain 2)
  =/  half-1  (~(scag fop fdomain) half)
  =/  half-2  (~(slag fop fdomain) half)
  =/  lef-zerofier  (zerofier half-1)
  =/  rig-zerofier  (zerofier half-2)
  =/  lef-offset  (codeword rig-zerofier half-1)
  =/  rig-offset  (codeword lef-zerofier half-2)
  =/  lef-target
    %+  ~(zip fop (~(scag fop fvalues) half))
      lef-offset
    fdiv
  =/  rig-target
    %+  ~(zip fop (~(slag fop fvalues) half))
      rig-offset
    fdiv
  =/  lef-interpolant
    $(fdomain half-1, fvalues lef-target)
  =/  rig-interpolant
    $(fdomain half-2, fvalues rig-target)
  %+  fpadd
    (fpmul lef-interpolant rig-zerofier)
  (fpmul rig-interpolant lef-zerofier)
::
++  test-colinearity
  |=  points=(list (pair felt felt))
  ^-  ?
  ?<  ?|(?=(~ points) ?=(~ t.points))
  =*  x0  p.i.points
  =*  y0  q.i.points
  =*  x1  p.i.t.points
  =*  y1  q.i.t.points
  ~|  "x-coordinates must be distinct"
  ?<  =(x0 x1)
  =/  line=fpoly
    (interpolate (init-fpoly ~[x0 x1]) (init-fpoly ~[y0 y1]))
  =/  bool=?  %.y
  =/  iter  t.t.points
  |-
  ?~  iter
    bool
  %=  $
    iter  t.iter
    bool  ?&  bool
              =((fpeval line p.i.iter) q.i.iter)
          ==
  ==
::  shift: produces the polynomial q(x) such that p(c*x) = q(x), i.e. q_i = (p_i)*(c^i)
::
::    Usecase:
::    If p is a polynomial you want to evaluate on coset cH of subgroup H, then you can
::    instead evaluate q on H. The value of q on h is that of p on ch: q(h) = p(ch).
++  shift
  ~/  %shift
  |:  [fp=`fpoly`one-fpoly c=`felt`(lift 1)]
  ^-  fpoly
  =/  p  ~(to-poly fop fp)
  =/  power=felt  (lift 1)
  =|  q=poly
  |-
  ?~  p
    (init-fpoly (flop q))
  $(q [(fmul i.p power) q], power (fmul power c), p t.p)
::
++  turn-coseword
  ~/  %turn-coseword
  |=  [polys=(list fpoly) offset=felt order=@]
  ^-  (list fpoly)
  %+  turn  polys
  |=  fp=fpoly
  (coseword fp offset order)
::
::  coseword: fast evaluation on a coset of a binary subgroup
::
::    Portmanteau of coset and codeword. If we want to evaluate a polynomial p on a coset of
::    a subgroup H, this is the same as evaluating the shifted polynomial q on H. If H is
::    generated by a binary root of unity, this evaluation is the same as an FFT.
::    NOTE: the polynomial being evaluated should have length less than the size of H.
::    This is because an FFT of a polynomial uses a root of unity of order the power of 2
::    which is larger than the length of the polynomial.
::    NOTE: 'order' is the size of H. It suffices for this single number to be our proxy for
::    H because there is a unique subgroup of this size. (Follows from the fact that F* is cyclic.)
++  coseword
  ~/  %coseword
  |=  [p=fpoly offset=felt order=@]
  ^-  fpoly
  ~|  "Order must be a power of 2."
  ?>  =((dis order (dec order)) 0)
  %-  fft
  %-  ~(zero-extend fop (shift p offset))
  (sub order len.p)
::
::  intercosate: interpolate a polynomial taking particular values over a binary subgroup coset
::
::    Returns a polynomial p satisfying p(c*w^i) = v_i where w generates a cyclic subgroup of
::    binary order. This is accomplished by first obtaining q = (ifft values), which satisfies
::    q(w^i) = v_i. This is equivalent to q(c^{-1}*(c*w^i)) = v_i so comparing to our desired
::    equation we want p(x) = q(c^{-1}*x); i.e. we need to shift q by c^{-1}.
++  intercosate
  ~/  %intercosate
  |=  [offset=felt order=@ values=fpoly]
  ^-  fpoly
  ~+
  ::  order = |H| is a power of 2
  ?>  =((dis order (dec order)) 0)
  ::  number of values should match the number of points in the coset
  ?>  =(len.values order)
  (shift (ifft values) (finv offset))
::
::  multi-polynomial math
::
::  mp-degree
++  mp-degree
  |=  f=multi-poly
  ^-  @
  %-  roll
  :_  max
  %+  turn  ~(tap by f)
  |=  [k=bpoly v=felt]
  ^-  @
  =/  kl  (bpoly-to-list k)
  ?:  =(v (lift 0))
    0
  (roll kl add)
::
::  mp-c: return the constant multi-poly c
++  mp-c
  |=  c=felt
  ^-  multi-poly
  ~+
  ?>  (fat c)
  ?:  =(c (lift 0))
    ~
  (my [[zero-bpoly c] ~])
::
::  mp-cb: return the constant multi-poly c
++  mp-cb
  |=  b=belt
  ^-  multi-poly
  ~+
  ?>  (based b)
  ?:  =(b 0)
    ~
  (my [[zero-bpoly (lift b)] ~])
::
::  make-variable: on input i return the multipolynomial x_i; variable list is 0-indexed
++  make-variable
  |=  which-variable=@
  ^-  multi-poly
  ~+
  (my [[(init-bpoly (weld (reap which-variable 0) ~[1])) (lift 1)] ~])
::
::  make-variables: make variables from a list of indices
++  make-variables
  |=  which-variables=(list @)
  ^-  (list multi-poly)
  ~+
  ?<  ?=(~ which-variables)
  [(make-variable i.which-variables) $(which-variables t.which-variables)]
::
::  valid-mp: Are all keys of uniform length? (If not, see +clean-mp.)
++  valid-mp
  |=  f=multi-poly
  ^-  ?
  =/  k-vs  ~(tap by f)
  ?:  ?=(~ k-vs)
    %.y
  =/  key-length  len.p.i.k-vs
  ?>  (fat q.i.k-vs)
  %+  levy  t.k-vs
  |=  [key=bpoly v=felt]
  ^-  ?
  =/  k  (bpoly-to-list key)
  ?&  (fat v)
      =((lent k) key-length)
  ==
::
::  clean: clean up a multi-poly to get rid of 0 values and uniformize key length
++  clean-mp
  |=  f=multi-poly
  ^-  multi-poly
  |^
  =/  kvs  ~(tap by f)
  =|  vars=(set @)
  ::  vars: variables (represented by index) necessary to write f
  =.  vars
    |-
    ?~  kvs
      vars
    %=  $
      kvs   t.kvs
      vars  (~(uni in vars) (variables-in-term i.kvs))
    ==
  =/  num-variables
    .+  (~(rep in vars) max)
  =|  res=multi-poly
  |-
  ?~  kvs
    res
  =/  [bk=bpoly v=felt]  i.kvs
  =/  k  (bpoly-to-list bk)
  ?:  =(v (lift 0))
    $(kvs t.kvs)
  =/  new-key
    %-  init-bpoly
    ?:  (lte num-variables (lent k))
      (scag num-variables k)
    (weld k (reap (sub num-variables (lent k)) 0))
  ::  it's possible that we have key collisions now
  ?.  (~(has by res) new-key)
    $(kvs t.kvs, res (~(put by res) new-key v))
  %=  $
    kvs  t.kvs
    res  %+  ~(put by res)
           new-key
         (fadd v (~(got by res) new-key))
  ==
  ::  variables-in-term: returns set of variable indices strictly necessary to write the monomial
  ++  variables-in-term
    |=  [bkey=bpoly value=felt]
    ^-  (set @)
    =|  vars=(set @)
    ?:  =(value (lift 0))
      vars
    =/  var  0
    =/  key  (bpoly-to-list bkey)
    |-
    ?~  key
      vars
    ?:  =(i.key 0)
      $(var +(var), key t.key)
    $(var +(var), key t.key, vars (~(put in vars) var))
  --
::
::  num-variables: number of explicit variables present, i.e. key size, of a valid multi-poly
++  num-variables
  |=  f=multi-poly
  ^-  @
  ~|  "invalid muti-poly"
  ?>  (valid-mp f)
  =/  k-vs  ~(tap by f)
  ?:  ?=(~ k-vs)
    0
  len.p.i.k-vs
::
::  pad: add `thickness` many variables to valid f by adding as many 0's to the keys
++  pad
  |=  [f=multi-poly thickness=@]
  ^-  multi-poly
  ?>  (valid-mp f)
  ?:  =(thickness 0)
    f
  =/  k-vs=(list (pair bpoly @))  ~(tap by f)
  =/  padding=(list @)  (reap thickness 0)
  ?:  =((lent k-vs) 0)
    (my [[(init-bpoly padding) (lift 0)] ~])
  =|  f-pad=multi-poly
  |-
  ?:  ?=(~ k-vs)
    f-pad
  =/  padded  (init-bpoly (weld (bpoly-to-list p.i.k-vs) padding))
  $(k-vs t.k-vs, f-pad (~(put by f-pad) padded q.i.k-vs))
::
::  mpadd: multi-poly addition
++  mpadd
  ~/  %mpadd
  |=  [f=multi-poly g=multi-poly]
  ^-  multi-poly
  ~+
  ?>  ?&((valid-mp f) (valid-mp g))
  ?:  =(~ f)
    g
  ?:  =(~ g)
    f
  =/  m  (max (num-variables f) (num-variables g))
  =:  f  (pad f (sub m (num-variables f)))
      g  (pad g (sub m (num-variables g)))
    ==
  ::  map with keys from symmetric difference of f, g key sets
  =/  symm-diff     (~(uni by (~(dif by f) g)) (~(dif by g) f))
  ::  list of common keys
  =/  int-key-list  ~(tap in ~(key by (~(int by f) g)))
  =|  merger=multi-poly
  |-
  ?:  ?=(~ int-key-list)
    (~(uni by symm-diff) merger)
  =/  sum
    %+  fadd
      (~(got by f) i.int-key-list)
    (~(got by g) i.int-key-list)
  ::  unnecessary to record the sum if it's 0
  ?:  =(sum (lift 0))
    $(int-key-list t.int-key-list)
  %=  $
    int-key-list  t.int-key-list
  ::
      merger
    %+  ~(put by merger)
      i.int-key-list
    sum
  ==
::  mpsum: sum up a list of multi-polys
++  mpsum
  ~/  %mpsum
  |=  mpolys=(list multi-poly)
  ^-  multi-poly
  %+  roll  mpolys
  |=  [a=multi-poly b=_(mp-cb 0)]
  (mpadd a b)
::
::  mpscal: multiply a multi-poly by a scalar
++  mpscal
  ~/  %mpscal
  |=  [c=felt f=multi-poly]
  ^-  multi-poly
  ~+
  ?>  (fat c)
  ?:  =(c (lift 0))
    ~
  =/  kvs=(list (pair bpoly felt))  ~(tap by f)
  =|  res=multi-poly
  |-
  ?~  kvs
    res
  $(kvs t.kvs, res (~(gas by res) ~[[p.i.kvs (fmul c q.i.kvs)]]))
::
::  mpsub: multi-poly subtraction
++  mpsub
  ~/  %mpsub
  |=  [f=multi-poly g=multi-poly]
  ^-  multi-poly
  ~+
  (mpadd f (mpscal (lift (bneg 1)) g))
::
::  mpmul: multi-poly multiplication; naive multiplication of every pair of coefficients
++  mpmul
  ~/  %mpmul
  |=  [f=multi-poly g=multi-poly]
  ^-  multi-poly
  ~+
  ?>  ?&((valid-mp f) (valid-mp g))
  ?:  ?|(=(~ f) =(~ g))
    ~
  =/  m  (max (num-variables f) (num-variables g))
  =:  f  (pad f (sub m (num-variables f)))
      g  (pad g (sub m (num-variables g)))
    ==
  =|  prod=multi-poly
  =/  fkvs  ~(tap by f)
  =/  gkvs  ~(tap by g)
  |-
  ?~  fkvs
    prod
  =/  dup-gkvs  gkvs
  |-
  ?~  dup-gkvs
    ^$(fkvs t.fkvs)
  =/  new-term=(pair bpoly felt)
    %.  [i.fkvs i.dup-gkvs]
    |=  [[k1=bpoly v1=felt] k2=bpoly v2=felt]
    ^-  [bpoly felt]
    ?>  (fat v1)
    ?>  (fat v2)
    :_  (fmul v1 v2)
    %-  init-bpoly
    (zip (bpoly-to-list k1) (bpoly-to-list k2) add)
  %=  $
    dup-gkvs  t.dup-gkvs
    ::
      prod
    %+  ~(put by prod)  p.new-term
    ?.  (~(has by prod) p.new-term)
      q.new-term
    (fadd q.new-term (~(got by prod) p.new-term))
  ==
::
::  mppow: computes f^k with tail-recursive exponentiation by squaring
++  mppow
  ~/  %mppow
  |=  [f=multi-poly k=@]
  ^-  multi-poly
  ~+
  ?>  (valid-mp f)
  %.  [(mp-c (lift 1)) f k]
  |=  [g=multi-poly f=multi-poly k=@]
  ?:  =(k 0)
    g
  =/  flag  (end 0 k)
  ?:  =(flag 0)
    $(f (mpmul f f), k (rsh 0 k))
  $(g (mpmul g f), f (mpmul f f), k (rsh 0 k))
::
::  lift: takes p(x) = ∑ a_i x^i and makes f(x0, ... , xj) = ∑ a_i (x_j)^i
++  multi-poly-special-lift
  |=  [p=poly idx=@]
  ^-  multi-poly
  ~+
  =/  mono  (mp-c (lift 1))
  =/  xi  (make-variable idx)
  =|  res=multi-poly
  |-
  ?~  p
    res
  %=  $
    p     t.p
    mono  (mpmul xi mono)
    res   (mpadd res (mpscal i.p mono))
  ==
::
::  mpeval: evaluate p(x0, x1, ...) at ~[x0 x1 ...]
::
::    This is actually a bit subtle, since key length and args length don't have to match.
::    E.g. [~[0 0] 1] represents the constant multi-poly 1. We should get 1 for any input,
::    thus we should be able to give it the argument ~[1], which is shorter than ~[0 0].
::    However, we shouldn't be able to give ~[1] as an argument to [~[0 1] 1]. BUT we
::    should be able to give ~[1] as an argument to [~[0 1] 0] since this is just the
::    zero multi-poly in disguise!
::
::    We proceed by rolling over the eval of each term. If value=0, the eval is automatically
::    0. Otherwise, we make key and input lengths agree by welding 0's. If the key was shorter
::    originally, this just means some of the variable slots in our argument are unused, like
::    plugging (1,1) into x; basically, the welding interprets x as x^1 y^0. On the other hand,
::    if the key was longer originally, then we could be in a case like trying to eval [~[0 1] 1]
::    on ~[1], i.e. eval'ing y at x=1. We can interpret y as x^0 y^1 and plug in x=1, but what we
::    get mathematically is the polynomial y back. However, following the weld prescription above,
::    we plug (1,0) into y and get 0. This is incoherent. Basically we have to make sure that at
::    the 0's of the extension of the argument, we have a corresponding 0 in the exponent so that
::    the extra 0's don't affect the output (0^0 = 1 for us); said another way, the variables
::    in the input that are missing relative to the key have to be erasable from the term, e.g.
::    look like x^0.
::
::    NOTE: any multi-poly passed to +mpeval must have been pre-cleaned
++  mpeval
  ~/  %mpeval
  |=  [p=multi-poly fargs=fpoly]
  ^-  felt
  =/  tp  ~(tap by p)
  ?:  =(~ p)
    (lift 0)
  =/  args  ~(to-poly fop fargs)
  %-  roll
  :_  fadd
  %+  turn  tp
  |=  [key=bpoly value=felt]
  ^-  felt
  ?:  =(value (lift 0))
    value
  ::  TODO make zero-pad arms
  =:    key
      ?:  (gte len.key len.fargs)
        key
      =/  zeros  (reap (sub len.fargs len.key) 0)
      (init-bpoly (weld (bpoly-to-list key) zeros))
    ::
        fargs
      ?:  (gte len.fargs len.key)
        fargs
      =/  zeros
        (lift-to-fpoly (reap (sub len.key len.fargs) 0))
      (~(weld fop fargs) zeros)
    ==
  ~|  "mpeval: eval failed. check that your variable count and table width match"
  %+  fmul  value
  %^  zip-roll  (bpoly-to-list key)  args
  |=  [[k=@ a=felt] prod=_(lift 1)]
  (fmul prod (fpow a k))
::
::  mp-substitute: given ~[p0(t) p1(t) ... ] substitute pi(t) for xi
++  mp-substitute
  ~/  %mp-substitute
  |=  [p=multi-poly polys=(list fpoly)]
  ^-  fpoly
  |^
  %-  init-fpoly
  ?:  =(~ p)
    ~
  =/  kvs  ~(tap by p)
  %~  to-poly  fop
  %-  roll
  :_  fpadd
  %+  turn  kvs
  (curr kv-substitute polys)
  ::
  ++  kv-substitute
    |=  [[bkey=bpoly value=felt] polys=(list fpoly)]
    ^-  fpoly
    =/  key  (bpoly-to-list bkey)
    ?:  =(value (lift 0))
      zero-fpoly
    =/  prod  one-fpoly
    %+  fpscal  value
    ?:  (lte (lent key) (lent polys))
      |-
      ?~  key
        prod
      ?<  ?=(~ polys)
      $(key t.key, polys t.polys, prod (fpmul prod (fppow i.polys i.key)))
    |-
    ?~  polys
      ~|  "Too few arguments to produce an answer."
      ?>  =(key (reap (lent key) (lift 0)))
      prod
    ?<  ?=(~ key)
    $(key t.key, polys t.polys, prod (fpmul prod (fppow i.polys i.key)))
  --
::
::  substitution-bound: bound on degree when subbing polys in f w/ degrees bounded by max-degrees
++  substitution-degree-bound
  |=  [f=multi-poly max-degrees=(list @)]
  ^-  @
  ~+
  %-  roll
  :_  max
  %+  turn  ~(tap in ~(key by f))
  |=  bk=bpoly
  =/  k  (bpoly-to-list bk)
  =:    k
      ?:  (gte (lent k) (lent max-degrees))
        k
      (weld k (reap (sub (lent max-degrees) (lent k)) 0))
    ::
        max-degrees
      ?:  (gte (lent max-degrees) (lent k))
        max-degrees
      (weld max-degrees (reap (sub (lent k) (lent max-degrees)) (head max-degrees)))
    ==
  %^  zip-roll  k  max-degrees
  |=  [[exp=@ maxd=@] sum=@]
  %+  add  sum
  (mul exp maxd)
::
++  gen-random-felt
  |=  seed=@
  ^-  felt
  =|  base-randos=(list belt)
  %-  frep
  |-
  ?:  =(deg 0)
    base-randos
  %=  $
    deg          (dec deg)
    seed         (badd 1 (bmul seed seed))
    base-randos  [(mod (shax seed) p) base-randos]
  ==
::
::
++  gen-random-poly
  |=  [seed=@ length=@]
  ^-  poly
  =|  res=poly
  |-
  ?:  =(0 length)
    res
  %=  $
    seed    (mod (shax (fadd (lift 1) (fmul seed seed))) p)
    length  (dec length)
    res    [(gen-random-felt seed) res]
  ==
::
::
:: ++  fpdiv-test
::   |=  [p=poly q=poly]
::   ^-  ?
::   =(-:(fpdvr p q) (fpdiv p q))
:: ::
:: ++  fpdvr-test
::   |=  [a=poly b=poly]
::   ^-  ?
::   =/  [q=poly r=poly]  (fpdvr a b)
::   ?&  =(a (fpadd (fpmul-naive b q) r))
::       (lth (degree r) (degree b))
::   ==
::
++  turn-zip-fmul-mpeval
  ~/  %turn-zip-fmul-mpeval
  |=  [constraints=(list multi-poly) terms=fpoly points=(list fpoly)]
  ^-  (list fpoly)
  %+  turn  constraints
  |=  constraint=multi-poly
  %-  init-fpoly
  %^  zip  (range len.terms)  points
  |=  [i=@ point=fpoly]
  =/  term  (~(snag fop terms) i)
  %+  fmul  term
  (mpeval constraint point)
::
++  zipped-points-from-codewords
  ~/  %zipped-points-from-codewords
  |=  [domain=(list @) codewords=(list fpoly)]
  ^-  (list fpoly)
  %+  turn  (range (lent domain))
  |=  i=@
  %-  init-fpoly
  %+  turn  codewords
  |=  cw=fpoly
  (~(snag fop cw) i)
::
++  zipped-point-pairs-from-codewords
  ~/  %zipped-point-pairs-from-codewords
  |=  [domain=(list @) codewords=(list fpoly) unit-dist=@]
  ^-  (list fpoly)
  %+  turn  (range (lent domain))
  |=  i=@
  =/  point
    %-  init-fpoly
    %+  turn  codewords
    |=  cw=fpoly
    (~(snag fop cw) i)
  =/  next-point
    %-  init-fpoly
    %+  turn  codewords
    |=  cw=fpoly
    (~(snag fop cw) (mod (add i unit-dist) (lent domain)))
  (~(weld fop point) next-point)
--
