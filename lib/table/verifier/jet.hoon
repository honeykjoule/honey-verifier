/+  *goldilocks, *fock, *jet, *table, *table-util, common=table-jet
=,  f
|%
++  jet
  |%
  ::  change %col to %col-n
  ++  var-next-row
    |=  col=@tas
    ^-  @tas
   (crip (weld (trip col) "-n"))
  ::
  ++  funcs
    ^-  verifier-funcs
    |%
    ++  boundary-constraints
      |=  challenges=(list felt)
      ^-  (list multi-poly)
      ~
    ::
    ++  terminal-constraints
      |=  [challenges=(list felt) terminals=(map term (map term felt))]
      ^-  (list multi-poly)
      ~
    ::
    ++  transition-constraints
      |~  [challenges=(list felt:f) =jet-map]
      ^-  (map term multi-poly)
      ~+
      ::  name challenges
      =/  r   ~(r rnd (make-challenge-map challenges %stack))
      =/  alf  (r %alf)
      =/  bet  (r %bet)  :: multisets
      =/  a    (r %a)
      =/  b    (r %b)
      =/  c    (r %c)
      =/  p    (r %p)
      =/  q    (r %q)
      =/  r-chal    (r %r)
      =/  s    (r %s)
      =/  t    (r %t)
      =/  num-jets  (lent ~(tap by jet-map))
      =/  vars  (variables:common num-jets)
      =/  v  ~(v var vars)
      =/  noun-chals  [a b c alf]
      =/  nu  ~(. noun-poly-utils noun-chals vars)
      ::
      |^
      =/  jet-constraints  get-jet-constraints
      =/  selectors-binary
        %+  turn  (selector-column-names:common num-jets)
        |=  name=term
        ^-  [term multi-poly]
        :-  (crip (weld (trip name) "-binary"))
        (mpmul (v name) (mpsub one-poly (v name)))
      =/  one-selector
        :-  %one-selector-on
        %+  mpsub  one-poly
        %+  mpadd  (v %first-row)
        %+  roll  (selector-column-names:common num-jets)
        |:  [name=*@tas poly=(v %pad)]
        ^-  multi-poly
        (mpadd (v name) poly)
      =/  constraints=(list [term multi-poly])
        :~  ::  if padding=1 then %jet doesn't change
            :-  %pad-jet-unchanged
            (mpmul (v %pad-n) (mpsub (v %jet) (v %jet-n)))
        ::
            ::  if padding=1 then %mem doesn't change
            :-  %pad-mem-unchanged
            (mpmul (v %pad-n) (mpsub (v %mem) (v %mem-n)))
        ::
            :: multiply TUPLE(%jet-id, %sam, %prod) onto %jet multiset
            :-  %jet-multiset
            %+  mpmul  (mpsub one-poly (v %pad-n))
            %+  mpsub  (v %jet-n)
            %+  mpmul  (v %jet)
            %+  mpsub  (mp-c bet)
            ;:  mpadd
              (mpscal p (v %jet-id-n))
              (mpscal q (v %sam-n))
              (mpscal r-chal (v %prod-n))
            ==
        ==
      %-  ~(gas by *(map term multi-poly))
      ;:  weld
        jet-constraints
        selectors-binary
        ~[one-selector]
        constraints
      ==
      ::
      ++  get-jet-constraints
        ^-  (list [term multi-poly])
        =/  sel-columns  (selector-column-names:common num-jets)
        ::
        %-  zing
        %+  turn  ~(tap by jet-map)
        |=  [jet=@tas id=@]
        =/  jet-func  (~(got by jet-func-map) jet)
        %+  weld
          ::
          :: memset constraints
          %+  spun  atoms:jet-func
          |=  [=atom-data [prev-mem-set=(unit @tas) index=@ud]]
          ^-  (pair [@tas multi-poly] [(unit @tas) @ud])
          :_  interim-mem-set.atom-data^(add index 1)
          ?:  ?=(%1 axis.atom-data)
            :: if axis=1 don't multiply onto memset. just decode the sample.
            :-  `@tas`(crip :(weld "decode-sample-" (trip jet) "-" (scow %ud index)))
            %+  mpmul  (v (snag id sel-columns))
            %+  mpsub  (v %sam)
            (build-atom-reg.nu register.atom-data)
          ::
          :-  `@tas`(crip :(weld "memset-" (trip jet) "-" (scow %ud index)))
          ?~  prev-mem-set  :: first atom- use %mem and -n registers
            %+  mpmul  (v (var-next-row (snag id sel-columns)))
            %+  mpsub  (v (var-next-row (need interim-mem-set.atom-data)))
            %+  mpmul  (v %mem)
            %+  mpsub  (mp-c bet)
            ;:  mpadd
              (mpscal p (v %sam-n))
              (mpscal q (build-atom-literal.nu axis.atom-data))
              (mpscal r-chal (build-atom-reg.nu (var-next-row register.atom-data)))
              (mpscal s (v %sam-n))
              (mpscal t (build-atom-reg.nu (var-next-row register.atom-data)))
            ==
          ::  else copy form prev-mem-reg to interim-mem-set.atom-data in same row (no -n's)
          %+  mpmul  (v (snag id sel-columns))
          %+  mpsub  (v (fall interim-mem-set.atom-data %mem))
          %+  mpmul  (v (need prev-mem-set))
          %+  mpsub  (mp-c bet)
          ;:  mpadd
            (mpscal p (v %sam))
            (mpscal q (build-atom-literal.nu axis.atom-data))
            (mpscal r-chal (build-atom-reg.nu register.atom-data))
            (mpscal s (v %sam))
            (mpscal t (build-atom-reg.nu register.atom-data))
          ==
        ::
        ::  jet-specific transition constraints
        %+  turn
          %~  tap  by
          %+  transition-constraints:(~(got by jet-func-map) jet)
            vars
          challenges
        |=  [name=term poly=multi-poly]
        :-  name
        %+  mpmul  poly
        (v (snag (~(got by jet-map) jet) sel-columns))
      --
    --
  --
--
