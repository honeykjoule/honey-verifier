/+  *merkle, *proof-stream, *goldilocks
::
~%  %top-fri  ..part  ~
:: This core is just to get hints working below. Without it I can't figure out how to
:: specify the parents correctly in the hints.
|%
++  placeholder
  |=  n=@ud
  !!
--
~%  %fri-core  ..placeholder  ~
=,  f
::
|%
::
+$  fri-input
  $:  offset=belt
      omega=belt
      init-domain-len=@
      expansion-fac=@
      num-colinearity-t=@
  ==
::
++  fri
  ~/  %fri-door
  |_  fri-input
  ++  eval-domain
    ~+
    ^-  (list felt)
    %+  turn  (range init-domain-len)
    |=  i=@
    (lift (bmul offset (bpow omega i)))
  ::
  ++  num-rounds
    ~+
    ^-  @
    =/  codeword-len  init-domain-len
    =/  num  0
    |-
    ?:  ?&  (gth codeword-len expansion-fac)
            (lth (mul 4 num-colinearity-t) codeword-len)
        ==
      $(codeword-len (div codeword-len 2), num +(num))
    ~|  "num-rounds must be greater than 1"
    ?>  (gth num 1)
    num
  ::
  ++  verify
    ~/  %verify
    |=  [stream=stream-state root=@uv]
    ^-  ?
    ::
    ::  extract roots and alphas values from commit phase
    =^  [roots=(list @uv) alphas=(list felt)]  stream
      =/  roots=(list @uv)  [root]~
      =-  [[(flop roots) (flop alphas)] str]
      %+  roll  (range num-rounds)
      |=  [i=@ str=_stream roots=_roots alphas=(list felt)]
      ?:  =(i 0)
        :+  str  roots
        :_  alphas
        (field:sample ~(verifier-fiat-shamir proof-stream str))
      =^  root  str
        =^(r str ~(pull proof-stream str) ?>(?=(%merk-root -.r) p.r^str))
      :+  str
        [root roots]
      :_  alphas
      (field:sample ~(verifier-fiat-shamir proof-stream str))
    ?>  =((lent roots) (lent alphas))
    ::
    ::  extract last codeword
    =^  last-codeword=fpoly  stream
      =^(c stream ~(pull proof-stream stream) ?>(?=(%codeword -.c) p.c^stream))
    ::
    ::  check if last codeword matches last merkle root
    =/  merk-codeword  q:(list-to-balanced-merk ~(to-poly fop last-codeword))
    ?.  =(h.merk-codeword (rear roots))
      ~&  "last codeword does not match last merkle root"
      %.n
    =*  len-code  len.last-codeword
    ::
    ::  assert that last omega has the right order
    =/  last=[omega=felt offset=felt]
      =/  num-sq  (pow 2 (dec num-rounds))
      [(lift (bpow omega num-sq)) (lift (bpow offset num-sq))]
    ?.  =((finv omega.last) (fpow omega.last (dec len-code)))
      ~&  "last omega does not have the right order"
      %.n
    ::
    ::  compute interpolant
    =/  poly=fpoly
      (intercosate offset.last len-code last-codeword)
    ?.  =((coseword poly offset.last len-code) last-codeword)
      ~&  "re-evaluated codeword does not match the original"
      %.n
    ::
    ::  check if it is low degree
    =/  degr
      (dec (div len-code expansion-fac))
    =/  calculated-degree  (fdegree ~(to-poly fop poly))
    ?:  (gth calculated-degree degr)
      ~&  "last codeword does not correspond to a low degree polynomial"
      ~&  [calculated-degree+calculated-degree desired-degree+degr]
      %.n
    ::
    ::  get indices
    =/  top-level-indices
      %-  indices:sample
      :^    ~(verifier-fiat-shamir proof-stream stream)
          (rsh [0 1] init-domain-len)
        (rsh [0 (dec num-rounds)] init-domain-len)
      num-colinearity-t
    =-  ::
        ::  all checks passed
        %.y
    ::
    ::  for every round, check consistency of subsequent layers
    %^  zip-roll  (range (dec num-rounds))  (zip (snip alphas) (snip roots) same)
    |=  $:  [round=@ alpha=felt root=@]
            [omega=_(lift omega) offset=_(lift offset) str=_stream]
        ==
    ::
    ::  fold c-indices
    =/  c-ind
      %+  mod-all  top-level-indices
      (rsh [0 +(round)] init-domain-len)
    ::
    ::  infer a and b-indices
    =/  a-ind  c-ind
    =/  b-ind
      %+  add-all  a-ind
      (rsh [0 +(round)] init-domain-len)
    :+  (fpow omega 2)
      (fpow offset 2)
    %^  zip-roll  (range num-colinearity-t)
      (zip a-ind (zip b-ind c-ind same) same)
    |=  [[co-test=@ a-i=@ b-i=@ c-i=@] str=_str]
    ::
    ::  read values and check colinearity
    =^  d  str
      =^(d str ~(pull proof-stream str) ?>(?=(%merk-paths -.d) d^str))
    =*  ay  leaf.a.d
    =*  by  leaf.b.d
    =*  cy  leaf.c.d
    ::
    ::  colinearity check
    =/  ax  (fmul offset (fpow omega a-i))
    =/  bx  (fmul offset (fpow omega b-i))
    =*  cx  alpha
    ~|  "colinearity check failure"
    ?>  (test-colinearity ~[[ax ay] [bx by] [cx cy]])
    ::
    ::  verify authentication paths
    =/  axis-a  (index-to-axis (xeb (rsh [0 round] init-domain-len)) a-i)
    ~|  "merkle authentication path failed for a"
    ?>  (verify-merk-proof (shax ay) axis-a root path.a.d)
    =/  axis-b  (index-to-axis (xeb (rsh [0 round] init-domain-len)) b-i)
    ~|  "merkle authentication path failed for b"
    ?>  (verify-merk-proof (shax by) axis-b root path.b.d)
    ?.  =(+(round) (dec num-rounds))
      =/  axis-c  (index-to-axis (xeb (rsh [0 +(round)] init-domain-len)) c-i)
      ~|  "merkle authentication path failed for c"
      ?>  (verify-merk-proof (shax cy) axis-c (snag +(round) roots) path.c.d)
      str
    ::  if we are in the last round, we do not check the merkle paths,
    ::  but we did receive the last codeword, so we should check the
    ::  leafs against that instead
    =/  c-leaf  (~(snag fop last-codeword) c-i)
    ~|  "leaf in last round does not match the last codeword"
    ?>  =(cy c-leaf)
    str
  ::
  ++  prove
    ~/  %prove
    |=  [codeword=fpoly stream=stream-state]
    ^-  [top-level-indices=(list @) stream=stream-state]
    =/  log-codeword-len  (dec (xeb len.codeword))
    ~|  "codeword must be of initial domain length"
    ?>  =(init-domain-len len.codeword)
    ~|  "omega is not nth root of unity"
    ?>  =((bpow omega (bex log-codeword-len)) 1)
    ~|  "omega is not primitive"
    ?>  !=((bpow omega (bex (dec log-codeword-len))) 1)
    ::
    ::  commit phase
    =^  codewords=(list fpoly)  stream
      (commit codeword stream)
    ?>  =((lent codewords) num-rounds)
    ::
    ::  get top-level indices
    =/  indices
      %-  indices:sample
      :^    ~(prover-fiat-shamir proof-stream stream)
          len:(head (tail codewords))
        len:(rear codewords)
      num-colinearity-t
    ::
    ::  query phase
    :-  indices
    =^  inner-indices  stream
      ?:  =((lent codewords) 2)
        [indices stream]
      %+  roll  (range (sub (lent codewords) 2))
      |=  [i=@ indices=_indices stream=_stream]
      =/  codeword       (snag i codewords)
      =/  next-codeword  (snag +(i) codewords)
      =.  indices  (mod-all indices (div len.codeword 2))
      :-  indices
      (query codeword next-codeword indices stream)
    =.  inner-indices
      (mod-all inner-indices len:(rear codewords))
    (query-last (rear (snip codewords)) (rear codewords) inner-indices stream)
  ::
  ++  commit
    ~/  %commit
    |=  [codeword=fpoly stream=stream-state]
    ^-  [codewords=(list fpoly) stream-state]
    =-  [codewords stream]
    %+  roll  (range +(num-rounds))
    |=  $:  round=@
            $:  [codewords=(list fpoly) stream=_stream codeword=_codeword]
                omega=_(lift omega)  offset=_(lift offset)
        ==  ==
    ~|  "error in commit: omega does not have the right order!"
    ~|  [(finv omega) (fpow omega (dec len.codeword))]
    ?>  =((finv omega) (fpow omega (dec len.codeword)))
    ?:  =(round num-rounds)
      :_  [omega offset]
      :+  (flop [codeword codewords])
        (~(push proof-stream stream) [%codeword codeword])
      codeword
    =/  =merk  +:(list-to-balanced-merk ~(to-poly fop codeword))
    ::
    ::  prover commits to f(x) by sending merkle root of codeword to verifier
    ::  but does not send merkle root in first round
    =?  stream  (gth round 0)
      (~(push proof-stream stream) [%merk-root h.merk])
    ?:  =(+(round) num-rounds)
      [[codewords stream codeword] omega offset]
    ::
    ::  verifier responds with random challenge alpha
    =/  alpha=felt  (field:sample ~(prover-fiat-shamir proof-stream stream))
    :_  [(fpow omega 2) (fpow offset 2)]
    :+  [codeword codewords]
      stream
    ::
    ::  split and fold
    %-  init-fpoly
    %+  turn  (range (div len.codeword 2))
    |=  i=@
    %-  fdiv
    :_  (lift 2)
    ::  alpha / (offset * omega^i)
    =+  (fdiv alpha (fmul offset (fpow omega i)))
    %+  fadd
      ::  (one + k) * codeword[i]
      (fmul (fadd (lift 1) -) (~(snag fop codeword) i))
    ::  (one - k) * codeword[len(codeword)/2 + i]
    %+  fmul  (fsub (lift 1) -)
    (~(snag fop codeword) (add (div len.codeword 2) i))
  ::
  ++  query
    ~/  %query
    |=  [curr=fpoly next=fpoly c-ind=(list @) stream=stream-state]
    ^-  stream-state
    ::
    ::  infer a and b indices
    =/  a-ind    c-ind
    =/  b-ind    (add-all c-ind (div len.curr 2))
    ::
    ::  merklize polynomials
    =+  [cur-h cur-t]=(list-to-balanced-merk ~(to-poly fop curr))
    =+  [nex-h nex-t]=(list-to-balanced-merk ~(to-poly fop next))
    ::
    ::  reveal leaf and authentication path
    =-  stream
    %^  zip-roll  a-ind  (zip b-ind c-ind same)
    |=  [[a-i=@ b-i=@ c-i=@] s=@ stream=_stream]
    :-  +(s)
    ?:  =(s num-colinearity-t)
      stream
    %-  ~(push proof-stream stream)
    :^    %merk-paths
        =/  a-axis  (index-to-axis cur-h a-i)
        =/  a-leaf  (~(snag fop curr) a-i)
        [a-leaf path:(build-merk-proof cur-t a-axis)]
      =/  b-axis  (index-to-axis cur-h b-i)
      =/  b-leaf  (~(snag fop curr) b-i)
      [b-leaf path:(build-merk-proof cur-t b-axis)]
    =/  c-axis  (index-to-axis nex-h c-i)
    =/  c-leaf  (~(snag fop next) c-i)
    [c-leaf path:(build-merk-proof nex-t c-axis)]
  ::
  ++  query-last
    ~/  %query-last
    |=  [curr=fpoly last=fpoly c-ind=(list @) stream=stream-state]
    ^-  stream-state
    ::
    ::  merklize second-to-last polynomial
    =+  [cur-h cur-t]=(list-to-balanced-merk ~(to-poly fop curr))
    ::
    ::  infer a and b indices
    =/  a-ind  c-ind
    =/  b-ind  (add-all c-ind (div len.curr 2))
    ::
    ::  reveal leaf and authentication path
    %^  zip-roll  a-ind  (zip b-ind c-ind same)
    |=  [[a-i=@ b-i=@ c-i=@] str=_stream]
    %-  ~(push proof-stream str)
    :^    %merk-paths
        =/  a-axis  (index-to-axis cur-h a-i)
        =/  a-leaf  (~(snag fop curr) a-i)
        [a-leaf path:(build-merk-proof cur-t a-axis)]
      =/  b-axis  (index-to-axis cur-h b-i)
      =/  b-leaf  (~(snag fop curr) b-i)
      [b-leaf path:(build-merk-proof cur-t b-axis)]
    [(~(snag fop last) c-i) ~]
  --
--
