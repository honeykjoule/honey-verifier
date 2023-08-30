/+  *table, *fock, common=table-exp, terminal
=,  f
::
|%
++  one  (mp-c (lift 1))
++  v  ~(v var variables:common)
::
++  exp
  |%
  ::
  ++  funcs
    ^-  verifier-funcs
    |%
    ++  boundary-constraints
      |=  challenges=(list felt)
      =/  r  ~(r rnd (make-challenge-map challenges %nockzs))
      =/  alf=felt  (r %alf)
      :~  (mpsub (v %pow) (mp-c (lift 2)))
          (mpsub (v %exp) (mp-c (fmul alf alf)))
          (mpsub (v %exp-mulset) one)
      ==
    ::
    ++  transition-constraints
      |=  challenges=(list felt)
      ^-  (map term multi-poly)
      %-  ~(gas by *(map term multi-poly))
      %+  turn  (unlabeled-transition-constraints challenges)
      |=  mp=multi-poly
      [%no-name mp]
    ::
    ++  unlabeled-transition-constraints
      |=  challenges=(list felt)
      =/  r  ~(r rnd (make-challenge-map challenges %nockzs))
      =/  [alf=felt bet=felt a=felt b=felt]
        [(r %alf) (r %bet) (r %a) (r %b)]
      :~  ::  mult/multi/multf constaint system
          %+  mpmul  (v %mult)
          (mpsub (v %multf) one)
        ::
          %+  mpmul  (v %multi)
          (mpsub (v %multf) one)
        ::
          %+  mpsub  (v %multf)
          (mpmul (v %mult) (v %multi))
        ::
        ::  evolution of pow
        ::
        ::    increments or doubles when mult=0, stays the same otherwise
        ::
        ::    multf•(pow'-pow) + (1-multf)(pow'-pow-1)(pow' - 2*pow)
          %+  mpadd  (mpmul (v %multf) (mpsub (v %pow-n) (v %pow)))
          ;:  mpmul
            (mpsub one (v %multf))
          ::
            (mpsub (v %pow-n) (mpadd (v %pow) one))
          ::
            (mpsub (v %pow-n) (mpscal (lift 2) (v %pow)))
          ==
        ::
        ::  evolution of mult
        ::
        ::    decrements as long as there's no underflow, in which case it's unconstrained
        ::
        ::    multf•(mult'-mult+1)
          %+  mpmul
            (v %multf)
          (mpadd (mpsub one (v %mult)) (v %mult-n))
        ::
        ::  evolution of exp
        ::
        ::    multiply by alf or square according to behavior of pow when mult=0, 
        ::    stay the same otherwise (ensures exp = alf^pow)
        ::
        ::    degree = 4
        ::
        ::    multf•(exp'-exp) + 
        ::      (1-multf)(exp'•(1-pow)-exp•[(pow' - 2*pow)alf + (1+pow-pow')•exp])
          %+  mpadd
            (mpmul (v %multf) (mpsub (v %exp-n) (v %exp)))
          %+  mpmul
            (mpsub one (v %multf))
          %+  mpsub
            (mpmul (v %exp-n) (mpsub one (v %pow)))
          %+  mpmul  (v %exp)
          %+  mpadd
            %+  mpmul  (mp-c alf)
            (mpsub (v %pow-n) (mpscal (lift 2) (v %pow)))
          %+  mpmul  (v %exp)
          (mpsub (mpadd (v %pow) one) (v %pow-n))
        ::
        ::  evolution of exp-mulset
        ::
        ::    Multiply bet-(a•pow+b•exp) into exp-mulset if multf=1.
        ::
        ::    exp-mulset' = exp-mulset•[(bet-(a•pow+b•exp))•multf + (1-multf)]
        ::
          %+  mpsub  (v %exp-mulset-n)
          %+  mpmul  (v %exp-mulset)
          %+  mpadd  (mpsub one (v %multf))
          %+  mpmul  (v %multf)
          %+  mpsub  (mp-c bet)
          %+  mpadd  (mpscal a (v %pow))
          (mpscal b (v %exp))
      ==
    ::
    ++  terminal-constraints
      |=  [challenges=(list @) terminals=(map term (map term felt))]
      :~  ::  mult/multi/multf constaint system
          (mpmul (v %mult) (mpsub (v %multf) one))
        ::
          (mpmul (v %multi) (mpsub (v %multf) one))
        ::
          (mpsub (v %multf) (mpmul (v %mult) (v %multi)))
      ==
    --
  --
--