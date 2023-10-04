/+  engine=stark-engine, *challenges
=>  engine
::
~%  %stark-verifier  ..get-verifier-funcs  ~
|%
::  copied from sur/verifier.hoon because of =>  engine
+$  verify-result  [valid=? code=[s=* f=*] prod=*]
++  verify
  ~/  %verify
  |=  [proof=stream-state heights=(list @)]
  ^-  verify-result
  ::
  ::
  ::=,  clc
  ::
  ::  get computation in raw noun form
  =^  comp  proof
    =^(c proof ~(pull proof-stream proof) ?>(?=(%computation -.c) c^proof))
  ::
  ::  get jets
  =^  jets  proof
    =^(j proof ~(pull proof-stream proof) ?>(?=(%jets -.j) p.j^proof))
  ::
  ::  Compute dynamic table widths using jets
  =.  table-base-widths
    %+  weld  table-base-widths-static:common
    ~[(base-width:jet-common jets)]
  =.  table-full-widths
    %+  weld  table-full-widths-static:common
    ~[(full-width:jet-common jets)]
  ::
  =/  clc  ~(. calc heights jets)
  ::=,  clc
  ::
  ::  get merkle root of base tables
  =^  base-root  proof
    =^(b proof ~(pull proof-stream proof) ?>(?=(%merk-root -.b) p.b^proof))
  ::
  ::  get coefficients for table extensions
  ::  challenges: a, b, c, alpha
  =/  challenges=(list felt)
    (weights:sample num-challenges ~(verifier-fiat-shamir proof-stream proof))
  ::
  ::  get root of table extensions
  =^  ext-root   proof
    =^(e proof ~(pull proof-stream proof) ?>(?=(%merk-root -.e) p.e^proof))
  ::
  ::  get terminals
  =^  terminals  proof
    =^(t proof ~(pull proof-stream proof) ?>(?=(%terminals -.t) p.t^proof))
  ::
  ::=,  clc
  ::=,  clc
  ::  calculate variables that depend on table heights
  ::=/  clc  ~(. calc heights ~)
  ::=,  clc
  ::  AT THIS POINT, claimed [s f] and randomness are available.
  ::  base and extension tables have been committed to
  ::  and terminals have been directly presented in stream.
  ::
  ::  Therefore, we now use the randomness to compute the expected fingerprints of the compute stack and product stack based on the given [s f] and product, respectively.
  ::  We then dynamically generate constraints that force the cs and ps to be equivalent to the expected fingerprints.
  ::  As long as the prover replicates this exact protocol, the opened indicies should match up.
  ::  The boundary constraint then ensures that the computation in cleartext is linked to the computation in the trace.
  ::
  =/  stack-table-idx  (i %stack table-names)
  =/  old-stack-fns=verifier-funcs
    (snag stack-table-idx all-verifier-funcs)
  =/  stack-fns-augmented=verifier-funcs
    (wrap-linking-constraints old-stack-fns [s f]:p.comp r.comp challenges)
  =/  new-verifier-funcs=(list verifier-funcs)
    (snap all-verifier-funcs stack-table-idx stack-fns-augmented)
  ::  Note: we stopped using (get-verifier-funcs i) because we modify state through shadowing which
  ::  doesn't propagate the changes up and so get-verifier-funcs will operate on stale data.
  =*  all-verifier-funcs  new-verifier-funcs
  ::
  ::  compute degree bounds
  =/  base-degree-bounds
    ~|  'error: table heights and table-base-widths may have mismatching lengths, check that the prover and verifier both have the same tables enabled'
    %^  zip-roll  heights  table-base-widths
    |=  [[h=@ w=@] acc=(list @)]
    %+  weld  acc
    %+  reap  w
    (static-interpolant-degree-bound h num-randomizers)
  =/  ext-degree-bounds
    ~|  'error: table heights and table-base-widths/full-widths may have mismatching lengths, check that the prover and verifier both have the same tables enabled'
    %^  zip-roll  heights  (zip-up table-base-widths table-full-widths)
    |=  [[h=@ bas=@ ful=@] acc=(list @)]
    %+  weld  acc
    %+  reap  (sub ful bas)
    (static-interpolant-degree-bound h num-randomizers)
  ::
  ::  get weights for nonlinear combination
  ::  - num-randomizer randomizers
  ::  - 2 for every other polynomial (base, extension, quotients, differences)
  =/  num-base-polys  (sum table-base-widths)
  =/  num-ext-polys   (sum (zip table-full-widths table-base-widths sub))
  =/  num-quotient-polys
    %-  sum
    %+  turn  (range (lent all-verifier-funcs))
    |=  i=@
    =/  funcs  (snag i all-verifier-funcs)
    =/  bw     (snag i table-base-widths)
    =/  fw     (snag i table-full-widths)
    %-  ~(num-quotients tab [[p bw fw num-randomizers] ~])
    [challenges terminals (snag i heights) funcs jets]
  =/  num-difference-quotients
    (lent permutation-args)
  =/  weights=(list felt)
    %+  weights:sample
      %+  add  num-randomizers
      %+  mul  2
      %-  sum
      :~  num-base-polys      num-ext-polys
          num-quotient-polys  num-difference-quotients
      ==
    ~(verifier-fiat-shamir proof-stream proof)
  ::
  ::  pull merkle root of combination codeword
  =^  combo-root  proof
    =^(c proof ~(pull proof-stream proof) ?>(?=(%merk-root -.c) p.c^proof))
  ::
  ::  get indices of leaves to verify nonlinear combination
  =/  indices
    %~  tap  in
    %-  silt
    %-  new-indices:sample
    :+  security-level
      ~(verifier-fiat-shamir proof-stream proof)
    fri-domain-len:clc
  ::
  ::  get unit distances
  =/  unit-distances=(list @)
    :-  0
    =-  ~(tap in (~(del in -) 0))
    %-  ~(gas in *(set @))
    (turn heights |=(h=@ (static-unit-distance fri-domain-len:clc h)))
  ::
  ::  get leaves at indicated positions
  =^  tuples=(map index=@ (list felt))  proof
    %+  roll  indices
    |=  [index=@ [tuples=(map index=@ (list felt)) str=_proof]]
    %+  roll  unit-distances
    |=  [distance=@ [tuples=_tuples str=_str]]
    =/  idx  (mod (add index distance) fri-domain-len:clc)
    =/  axis  (index-to-axis (xeb fri-domain-len:clc) idx)
    =^  bopening  str
      =^(mp str ~(pull proof-stream str) ?>(?=(%merk-path -.mp) p.mp^str))
    ?>  (verify-merk-proof (shax leaf.bopening) axis base-root path.bopening)
    =^  eopening  str
      =^(mp str ~(pull proof-stream str) ?>(?=(%merk-path -.mp) p.mp^str))
    ?>  (verify-merk-proof (shax leaf.eopening) axis ext-root path.eopening)
    =/  belems  ;;(fpoly (cue leaf.bopening))
    =/  eelems  ;;(fpoly (cue leaf.eopening))
    =/  res  ~(to-poly fop (~(weld fop belems) eelems))
    [(~(put by tuples) idx res) str]
  =*  fri-domain  eval-domain:fri:clc
  :_  [[s f]:p.comp r.comp]
  |-
  ?~  indices
    ::
    ::  verify low degree of combination polynomial using FRI
    ?.  (verify:fri:clc proof combo-root)
      %.n
    ::
    ::  TODO: verify result / external terminals
    ::
    %.y
  ::
  ::  verify nonlinear combination
  =*  index  i.indices
  =/  tuple=(list felt)  (~(got by tuples) index)
  ::
  ::  collect terms: randomizer
  =^  terms=(list felt)  tuple
    [(scag num-randomizers tuple) (slag num-randomizers tuple)]
  =*  ext-offset  num-base-polys
  =/  fri-at-index=felt  (snag index fri-domain)
  ::
  ::  collect terms: base + ext
  =.  terms
    %+  weld  terms
    ~|  "error: table-base-widths and table-full-widths may be incorrectly set"
    %^  zip-roll  (range (add num-base-polys num-ext-polys))  tuple
    |=  [[i=@ term=felt] acc=(list felt)]
    =/  shift
      %+  sub  max-degree:clc
      ?:  (lth i num-base-polys)
        ::
        ::  compute base shift
        (snag i base-degree-bounds)
      ::
      ::  compute ext shift
      (snag (sub i num-base-polys) ext-degree-bounds)
    %+  weld  acc
    :+  term
      %+  fmul  term
      (fpow fri-at-index shift)
    ~
  ?>  .=  (lent terms)
      +((mul 2 (add num-base-polys num-ext-polys)))
  ::
  ::  collect terms: quotients
  ::  quotients need to be computed
  =/  acc-index  0
  =^  points=(list fpoly)  acc-index
    =-  [(flop points) acc-index]
    %+  roll  table-base-widths
    |=  [w=@ [points=(list fpoly) acc-index=_acc-index]]
    :_  (add acc-index w)
    :_  points
    %-  init-fpoly
    (swag [acc-index w] tuple)
  ?>  =(acc-index num-base-polys)
  =.  points
    =-  ~|  [acc-index+acc-index tuple-len+(lent tuple)]
        ?>  =(acc-index (lent tuple))
        (flop points)
    %^  zip-roll  points  (zip table-full-widths table-base-widths sub)
    |=  $:  [pot=fpoly ext-w=@]
            [points=(list fpoly) acc-index=_acc-index]
        ==
    :_  (add acc-index ext-w)
    :_  points
    %-  ~(weld fop pot)
    (init-fpoly (swag [acc-index ext-w] tuple))
  ::
  ::  collect terms: difference-quotient / permutation arguments
  =/  difference-quotient-terms
    %+  roll  permutation-args
    |=  [[[lef-tab=@ lef-col=@] rig-tab=@ rig-col=@] acc=(list felt)]
    %+  weld  acc
    =/  quotient
      %-  fdiv
      :_  (fsub fri-at-index (lift 1))
      %-  evaluate-difference:permutation-arg
      :*  points
          lef-tab  lef-col
          rig-tab  rig-col
      ==
    ::  XX quotient-degree-bound on permutation-arg
    =/  degree-bound
      %-  dec
      %+  max
        (static-interpolant-degree-bound (snag lef-tab heights) num-randomizers)
      (static-interpolant-degree-bound (snag rig-tab heights) num-randomizers)
    =/  shift
      (sub max-degree:clc degree-bound)
    :+  quotient
      (fmul quotient (fpow fri-at-index shift))
    ~
  ::?>  =(0 (lent difference-quotient-terms))
  ::
  =.  terms
    %+  weld  terms
    %-  weld
    :_  difference-quotient-terms
    =-  ?>  =((sub baw num-randomizers) num-base-polys)
        ?>  =((sub eaw (add ext-offset num-randomizers)) num-ext-polys)
        acc
    %^  zip-roll  points  (range (lent table-base-widths))
    |=  $:  [point=fpoly t=@]
            [acc=(list felt) baw=_num-randomizers eaw=_(add ext-offset num-randomizers)]
        ==
    =/  bw      (snag t table-base-widths)
    =/  fw      (snag t table-full-widths)
    =/  h       (snag t heights)
    =/  funcs   (snag t all-verifier-funcs)
    =/  gam  (~(r rnd (make-shared-challenges challenges)) %gam)
    =/  next-index
      %+  mod
        (add index (static-unit-distance fri-domain-len:clc h))
      fri-domain-len:clc
    =/  next-point
      %-  init-fpoly
      =+  (~(got by tuples) next-index)
      %+  weld  (swag [baw bw] -)
      (swag [eaw (sub fw bw)] -)
    :_  [(add baw bw) (add eaw (sub fw bw))]
    %-  zing
    :~  acc
      ::
      ::  boundary
        =/  constraint
          (combine-constraints (boundary-constraints:funcs challenges) gam)
        =/  bound
          %-  ~(boundary-quotient-degree-bounds tab [[p bw fw num-randomizers] ~])
          [challenges terminals h funcs jets]
        ^-  (list @)
        =/  eval  (mpeval-graph constraint point)
        =/  quotient  (fdiv eval (fsub fri-at-index (lift 1)))
        =/  shift  (sub max-degree:clc bound)
        :+  quotient
          (fmul quotient (fpow fri-at-index shift))
        ~
      ::
      ::  transition
        =/  constraint
          %+  combine-constraints
            (turn ~(tap by (transition-constraints:funcs challenges jets)) tail)
          gam
        =/  bound
          %-  ~(transition-quotient-degree-bounds tab [[p bw fw num-randomizers] ~])
          [challenges terminals h funcs jets]
        ^-  (list @)
        =/  eval  (mpeval-graph constraint (~(weld fop point) next-point))
        ?<  =(h 0)
        =/  table-omicron  (lift (ordered-root h))
        =/  quotient
          %+  fmul  eval
          %+  fdiv
            (fsub fri-at-index (finv table-omicron))
          (fsub (fpow fri-at-index h) (lift 1))
        =/  shift  (sub max-degree:clc bound)
        :+  quotient
          (fmul quotient (fpow fri-at-index shift))
        ~
      ::
      ::  terminal
        =/  constraint
          (combine-constraints (terminal-constraints:funcs challenges terminals) gam)
        =/  bound
          %-  ~(terminal-quotient-degree-bounds tab [[p bw fw num-randomizers] ~])
          [challenges terminals h funcs jets]
        ^-  (list @)
        =/  eval  (mpeval-graph constraint point)
        =/  table-omicron
          (lift (ordered-root h))
        =/  quotient
          %+  fdiv  eval
          (fsub fri-at-index (finv table-omicron))
        =/  shift  (sub max-degree:clc bound)
        :+  quotient
          (fmul quotient (fpow fri-at-index shift))
        ~
    ==
  ::
  ::  compute inner product of weights and terms
  ::
  =/  inner-product
    ~|  "number of weights and terms must be equal"
    %^  zip-roll  weights  terms
    |=  [[w=felt t=felt] prod=_(lift 0)]
    (fadd (fmul w t) prod)
  ::  get value of the combination codeword to test the inner
  ::  product against
  =/  axis  (index-to-axis (xeb fri-domain-len:clc) index)
  =^  combo-merk-proof  proof
    =^(c proof ~(pull proof-stream proof) ?>(?=(%merk-path -.c) p.c^proof))
  =*  combo-leaf  leaf.combo-merk-proof
  =*  combo-path  path.combo-merk-proof
  ::
  ::  verify merkle authentication path
  ?>  (verify-merk-proof (shax combo-leaf) axis combo-root combo-path)
  ::
  ::  check equality
  ~|  leaf-inner-prod-mismatch+[`@ux`combo-leaf `@ux`inner-product]
  ?>  =(combo-leaf inner-product)
  $(indices t.indices)
--
