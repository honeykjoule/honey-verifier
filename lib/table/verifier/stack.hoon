/+  *table, *fock, *table-util, common=table-stack, terminal, *jet
=,  f
|%
++  stack
  =,  mp-to-graph
  |%
  ++  one        (mp-c (lift 1))
  ++  zero       (mp-c (lift 0))
  ++  pop-mp     (mp-c (lift 1))
  ++  finish-mp  (mp-c (lift 0))
  ++  v  ~(v var variables:common)
  ++  sel
    |=  [nams=(list term) mp=mp-graph]
    ^-  mp-graph
    %+  roll  nams
    |:  [nam=`term`%$ poly=`mp-graph`mp]
    (mpmul (v nam) poly)
  ::
  ++  funcs
    ^-  verifier-funcs
    |%
    ++  boundary-constraints
      |=  challenges=(list felt)
      ^-  (list mp-graph)
      ~
    ::
    ++  terminal-constraints
      |=  [challenges=(list felt) terminals=(map term (map term felt))]
      ^-  (list mp-graph)
      =/  stack-terminals  (~(get by terminals) %stack)
      =/  terminal-consistency-checks=(list mp-graph)
        ?~  stack-terminals  ~
        (gen-consistency-checks:terminal u.stack-terminals column-names:common v)
      %+  weld  terminal-consistency-checks
      :~  zero
      ==
    ::
    ++  transition-constraints
      |=  [challenges=(list felt) =jet-map]
      ^-  (map term mp-graph)
      ~+
      ::  name challenges
      =/  r   ~(r rnd (make-challenge-map challenges %stack))
      =/  alf  (r %alf)  :: stacks
      =/  bet  (r %bet)  :: multisets
      =/  a    (r %a)    :: a-e for tuples
      =/  b    (r %b)
      =/  c    (r %c)
      =/  p    (r %p)
      =/  q    (r %q)
      =/  r-chal    (r %r)
      =/  s    (r %s)
      =/  t    (r %t)
      =/  u    (r %u)
      :: stacks
      =/  stack         [alf (finv alf) variables:common]
      =/  pop          ~(pop poly-stack stack)
      =/  pop-all      ~(pop-all poly-stack stack)
      =/  push         ~(push poly-stack stack)
      =/  push-all     ~(push-all poly-stack stack)
      =/  tupler       ~[p q r-chal s t]
      =/  make-noun    ~(compress poly-tupler ~[a b c])
      =/  memset        [bet (v %mem)]
      =/  mem-ld       ~(. poly-ld bet)
      ::=/  make-zero    ~(make-zero poly-nock-zero memset tupler)
     :: =/  make-zeroes  ~(make-zeroes poly-nock-zero memset tupler)
      =/  noun-chals    [a b c alf]
      =/  nu           ~(. noun-poly-utils noun-chals variables:common)
      =/  su           ~(. subtree-ld-utils tupler)
      =/  cs=mp-graph            (v %cs)
      =/  ps            (v %ps)
      =/  os            (v %os)
      ::
      ::  6 encoded as a tree-felt
      =/  poly-6  (mpadd (mp-c a) (mpscal c (mp-c (lift 6))))
      ::
      %-  ~(gas by *(map term mp-graph))
      :~  ::  mode flags must be binary
          ::  m1(1-m1)=0, ...
          ::
          ::
          =/  mp=mp-graph  (mpmul (v %popf) (mpsub one (v %popf)))
          [%popf-binary mp]
          :: opcode flags must be binary
          :: o0(1-o0)=0 ...
          [%o0 (mpmul (v %o0) (mpsub one (v %o0)))]
          [%o1 (mpmul (v %o1) (mpsub one (v %o1)))]
          [%o2 (mpmul (v %o2) (mpsub one (v %o2)))]
          [%o3 (mpmul (v %o3) (mpsub one (v %o3)))]
          [%o4 (mpmul (v %o4) (mpsub one (v %o4)))]
          [%o5 (mpmul (v %o5) (mpsub one (v %o5)))]
          [%o6 (mpmul (v %o6) (mpsub one (v %o6)))]
          [%o7 (mpmul (v %o7) (mpsub one (v %o7)))]
          [%o8 (mpmul (v %o8) (mpsub one (v %o8)))]
          [%o9 (mpmul (v %o9) (mpsub one (v %o9)))]
          [%o11 (mpmul (v %o10) (mpsub one (v %o10)))]
          [%o11 (mpmul (v %o11) (mpsub one (v %o11)))]
          [%o99 (mpmul (v %o99) (mpsub one (v %o99)))]
          :: only one opcode flag can be 1 so they must sum to 1
          :: o0 + o1 + o2 + o3 + o4 + o5 +o14 + o15 - 1 = 0
          :-  %opflags-add-to-one
          %+  mpsub  (mpsub one (v %osempty))
          ;:  mpadd
            (v %o0-n)  (v %o1-n)  (v %o2-n)  (v %o3-n)  (v %o4-n)
            (v %o5-n)  (v %o6-n)  (v %o7-n)  (v %o8-n)  (v %o9-n)
            (v %o10-n)  (v %o11-n)  (v %o99-n)
          ==
          :: opcode flags must correspond to opcode register o
          :: 0*o0 + 1*o1 + 2*o2 + ... + 11*o11 - o = 0
          :-  %opcodes-equal-op
          %+  mpmul  (v %popf)
          %+  mpsub  (v %op)
          ;:  mpadd
            (v %o1)
            (mpscal (lift 2) (v %o2))    (mpscal (lift 3) (v %o3))
            (mpscal (lift 4) (v %o4))    (mpscal (lift 5) (v %o5))
            (mpscal (lift 6) (v %o6))    (mpscal (lift 7) (v %o7))
            (mpscal (lift 8) (v %o8))    (mpscal (lift 9) (v %o9))
            (mpscal (lift 10) (v %o10))  (mpscal (lift 11) (v %o11))
            (mpscal (lift 99) (v %o99))
          ==
          :: CSEmpty is 1 if CS is empty (ie len=0), else 0 (used to check if we are finished)
          ::
          :: CSInv = CS-LEN^-1, 0^-1=0
          :: $CS-LEN(CS-LEN*CSInv-1)=0$
          :-  %os-inv-1
          (mpmul (v %os-len) (mpsub (mpmul (v %os-len) (v %osinv)) one))
          :: $CSInv(CS-LEN*CSInv-1)=0$
          :-  %os-inv-2
          (mpmul (v %osinv) (mpsub (mpmul (v %os-len) (v %osinv)) one))
          :: %csempty must be the flipped bit of %cs-inv*%cs-len
          :: $CS*CSInv+CSEmpty-1=0$
          :-  %os-inv-3
          (mpsub (mpadd (mpmul (v %os-len) (v %osinv)) (v %osempty)) one)
          ::
          ::
          :: Mode End
          ::
          :: We're finished with the computation and the product is in PS. Just repeat PS
          :: forever.
          :: $M_{end}(PS-PS')=0$
          :-  %end-ps-same
          (mpmul (v %osempty) (mpsub (v %ps) (v %ps-n)))
          :-  %end-ps-len-same
          (mpmul (v %osempty) (mpsub (v %ps-len) (v %ps-len-n)))
          :: remain in mode end forever
          :: $M_{end}(M_{end}-m_{end}')=0$
          :-  %end-os-forever
          (mpmul (v %osempty) (mpsub (v %os) (v %os-n)))
          ::
          :-  %end-os-len-forever
          (mpmul (v %osempty) (mpsub (v %os-len) (v %os-len-n)))
          ::
          ::
          :: Operand stack constraints
          ::
          ::
          ::  Evolution of OS len for pop
          ::
          ::  0,1,11: os-len - 1
          ::  2,5,6,7,9: os-len + 3
          ::  3,4: os-len + 2
          ::  8,10: os-len + 4
          ::
          ::  nock 0,1,11 - os-len minus 1
          :-  %os-len-pop-0-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o0-n) (v %o1-n) (v %o11-n))
          (mpsub (v %os-len-n) (mpsub (v %os-len) one))
          ::
          ::  nock 2,5,6,7,9 - os-len plus 3
          :-  %os-len-pop-0-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o2-n) (v %o5-n) (v %o6-n) (v %o7-n) (v %o9-n))
          (mpsub (v %os-len-n) (mpadd (v %os-len) (mp-c (lift 3))))
          ::
          ::  nock 3,4 - os-len plus 2
          :-  %os-len-pop-3-4
          %+  mpmul  (v %popf-n)
          %+  mpmul  (mpadd (v %o3-n) (v %o4-n))
          (mpsub (v %os-len-n) (mpadd (v %os-len) (mp-c (lift 2))))
          ::
          ::  nock 10 - os-len plus 4
          :-  %os-len-pop-8-10
          %+  mpmul  (v %popf-n)
          %+  mpmul  (mpadd (v %o10-n) (v %o8-n))
          (mpsub (v %os-len-n) (mpadd (v %os-len) (mp-c (lift 4))))
          ::
          ::
          ::  Evolution of OS for pop
          ::
          ::  nock 0, 1 and 11- pop %popf, %op off os
          :-  %os-pop-0-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o0-n) (v %o1-n) (v %o11-n))
          %+  mpsub  (pop os (v %popf-n))
          (v %os-n)
          ::
          ::
          ::  1 sfs- pop %popf, %op off os and push one pop and op on
          :-  %os-pop-1sf
          %+  mpmul  (v %popf-n)
          %+  mpmul  (mpadd (v %o3-n) (v %o4-n))
          %+  mpsub
            (push-all (pop os (v %popf-n)) ~[(v %op-n) finish-mp pop-mp])
          (v %os-n)
          ::
          :: 2 sfs- pop %popf, %op off os and push two pops and op on
          :-  %os-pop-2sf
          %+  mpmul  (v %popf-n)
          %+  mpmul  (mpadd (v %o2-n) (v %o5-n))
          %+  mpsub
            (push-all (pop os (v %popf-n)) ~[(v %op-n) finish-mp pop-mp pop-mp])
          (v %os-n)
          ::
          :: nock 6 - pop %popf, %op off os and push pop, op, and
          :: PAIR(s, tail2, tail3) on
          ::
          :: %r1 - subject
          :: %r3 - tail1
          :: %r4 - tail2
          :: %r5 - tail3
          :-  %os-pop-nock6
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o6-n)
          %+  mpsub
            %+  push-all  (pop os (v %popf-n))
            :~  ;:  mpadd
                  (mpscal p (v %r1-n))
                  (mpscal q (v %r4-n))
                  (mpscal r-chal (v %r5-n))
                ==
                (v %op-n)
                finish-mp
                pop-mp
            ==
          (v %os-n)
          ::
          :: nock 7 - pop %popf, %op off os and push pop, op, formula (%tail2)
          ::
          :: %r4 - tail2 (formula)
          :-  %os-pop-nock7
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o7-n)
          %+  mpsub  (v %os-n)
          (push-all (pop os (v %popf-n)) ~[(v %r4-n) (v %op-n) finish-mp pop-mp])
          ::
          :: nock 8 - pop %popf, %op off os and push pop, op, formula (%tail2), subject
          ::
          :: %r1 - subject
          :: %r4 - tail2 (formula)
          :-  %os-pop-nock8
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o8-n)
          %+  mpsub  (v %os-n)
          (push-all (pop os (v %popf-n)) ~[(v %r1-n) (v %r4-n) (v %op-n) finish-mp pop-mp])
          ::
          :: nock 9 - pop %popf, %op off os and push pop, op, axis (%tail1)
          ::
          :: %r3 - axis
          :-  %os-pop-nock9
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o9-n)
          %+  mpsub  (v %os-n)
          (push-all (pop os (v %popf-n)) ~[(v %r3-n) (v %op-n) finish-mp pop-mp])
          ::
          :: nock 10 - pop %popf, %op off os and push pop, pop, op, axis (%tail1)
          ::
          :: %r5 - axis
          :-  %os-pop-nock10
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o10-n)
          %+  mpsub  (v %os-n)
          (push-all (pop os (v %popf-n)) ~[(v %r5-n) (v %op-n) finish-mp pop-mp pop-mp])
          ::
          ::
          :: Evolution of CS
          ::
          ::
          :: %r1 - subject
          :: %r2 - formula
          :: %r3 - tail1
          :: %r4 - tail2  (if needed)
          :: %r5 - tail3  (if needed)
          ::
          :: Evolution of CS len for pop
          ::
          :: 3,4,6,7,8,9 - don't touch  (replace [S F] with new subformula)
          :: 0,1,11 - cs-len - 2 (just compute a product)
          :: 2,5,10 - cs-len + 2 (add 2 formulae to compute)
          :-  %cs-len-pop-nock0-1-11
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o0-n) (v %o1-n) (v %o11-n))
          (mpsub (v %cs-len) (mpadd (v %cs-len-n) (mp-c (lift 2))))
          ::
          :-  %cs-len-pop-nock-3-4-6-7-8-9
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o3-n) (v %o4-n) (v %o6-n) (v %o7-n) (v %o8-n) (v %o9-n))
          (mpsub (v %cs-len) (v %cs-len-n))
          ::
          :-  %cs-len-pop-nock-2-5-10
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o2-n) (v %o5-n) (v %o10-n))
          (mpsub (mpadd (v %cs-len) (mp-c (lift 2))) (v %cs-len-n))
          ::
          :-  %not-pop-preserve-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (mpsub :(mpadd (v %o2-n) (v %o6-n) (v %o7-n) (v %o8-n) (v %o9-n)) one)
          (mpsub (v %cs) (v %cs-n))
          ::
          :: Nock 0,1,11 - only pop S(%r1) and F(%r2) off CS
          ::
          :-  %nock-0-1-pop-2-off-cs
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o0-n) (v %o1-n) (v %o11-n))
          %+  mpsub  (v %cs-n)
          (pop-all cs ~[(v %r1-n) (v %r2-n)])
          ::
          :: Compute one subformula
          ::
          :: Nock 3, 4, 6, 7, 8
          ::
          :: %r1 - subject
          :: %r2 - formula
          :: %r3 - tail1 (SF)
          ::
          :: Pop {S, F} off CS and push {SF, S} onto CS.
          :-  %push-sf-to-cs
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o3-n) (v %o4-n) (v %o6-n) (v %o7-n) (v %o8-n))
          %+  mpsub  (v %cs-n)
          %+  push-all
            (pop-all cs ~[(v %r1-n) (v %r2-n)])
          ~[(v %r3-n) (v %r1-n)]
          ::
          :: Nock 9 needs to push tail2 instead of tail1
          ::
          :: %r1 - subject
          :: %r2 - formula
          :: %r4 - tail2 (compute core formula)
          ::
          :-  %push-sf-to-cs-nock-9
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o9-n)
          %+  mpsub  (v %cs-n)
          %+  push-all
            (pop-all cs ~[(v %r1-n) (v %r2-n)])
          ~[(v %r4-n) (v %r1-n)]
          ::
          ::  Compute two subformulae
          ::
          ::  Nock 2,5,10, cons
          ::
          :: %r1 - subject
          :: %r2 - formula
          :: %r3 - tail1 (SF)
          :: %r4 - tail2 (SF2)
          ::
          ::  Pop {S, F} and push {SF1, S, SF2, S} to CS
          :-  %push-two-sfs-to-cs
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o2-n) (v %o5-n) (v %o10-n) (v %o99-n))
          %+  mpsub  (v %cs-n)
          %+  push-all  (pop-all cs ~[(v %r1-n) (v %r2-n)])
          ~[(v %r3-n) (v %r1-n) (v %r4-n) (v %r1-n)]
          ::
          ::
          ::
          :: Formula decoding
          ::
          :: We decode in a pop by just multiplying nock 0's onto %mem. We do all those here
          :: except for nock 1 and 11 which have to use %mem themselves and so their decoding
          :: happens with their processing.
          ::
          ::
          :: Cons: tail1(%r3) = [f(%r2) 0 2]
          ::       tail2(%r4) = [f(%r2) 0 3]
          ::       tail3(%r5) = [f(%r2) 0 4] :: this is not used but it proves f is cons
          :-  %cons-pop-mem-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o99-n)
          %-  add.mem-ld
          :*  (v %mem)
              (v %mem-int1-n)
              (make-zero.su (v %r2-n) (build-atom-literal.nu 2) (v %r3-n))
              (mp-c (lift 1))
          ==
          ::
          :-  %cons-pop-mem-2
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o99)
          %-  add:mem-ld
          :*  (v %mem-int1)
              (v %mem-int2)
              (make-zero.su (v %r2) (build-atom-literal.nu 3) (v %r4))
              (mp-c (lift 1))
          ==
          ::
          :-  %cons-pop-mem-3
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o99)
          %-  add:mem-ld
          :*  (v %mem-int2)
              (v %mem)
              (make-zero.su (v %r2) (build-atom-literal.nu 4) (v %r5))
              (mp-c (lift 1))
          ==
          ::
          :: One subformula (nock 1,3,4)
          ::   %op      = [f(%r2) 0 2]
          ::   sf(%r3)  = [f(%r2) 0 3]
          :-  %one-sf-pop-mem-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o1-n) (v %o3-n) (v %o4-n))
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r2-n)
                  (build-atom-literal.nu 2)
                  (build-atom-reg.nu %op-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %one-sf-pop-mem-2
          %+  mpmul  (v %popf)
          %+  mpmul  :(mpadd (v %o1) (v %o3) (v %o4))
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 3)
                  (v %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :: Two subformulae (nock 2,5,7,8,9)
          ::   %op        = [f(%r2) 0 2]
          ::   tail1(%r3) = [f(%r2) 0 6]
          ::   tail2(%r4) = [f(%r2) 0 7]
          :-  %two-sf-pop-mem-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  :(mpadd (v %o2-n) (v %o5-n) (v %o7-n) (v %o8-n) (v %o9-n))
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r2-n)
                  (build-atom-literal.nu 2)
                  (build-atom-reg.nu %op-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %two-sf-pop-mem-2
          %+  mpmul  (v %popf)
          %+  mpmul  :(mpadd (v %o2) (v %o5) (v %o7) (v %o8) (v %o9))
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem-int2)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 6)
                  (v %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %two-sf-pop-mem-3
          %+  mpmul  (v %popf)
          %+  mpmul  :(mpadd (v %o2) (v %o5) (v %o7) (v %o8) (v %o9))
          %-  add:mem-ld
          :*  (v %mem-int2)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 7)
                  (v %r4)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :: Nock 6
          ::   %op        = [f(%r2) 0 2]
          ::   tail1(%r3) = [f(%r2) 0 6]
          ::   tail2(%r4) = [f(%r2) 0 14]
          ::   tail3(%r5) = [f(%r2) 0 15]
          :-  %nock-6-pop-mem-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o6-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r2-n)
                  (build-atom-literal.nu 2)
                  (build-atom-reg.nu %op-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-6-pop-mem-2
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o6)
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem-int2)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 6)
                  (v %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-6-pop-mem-3
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o6)
          %-  add:mem-ld
          :*  (v %mem-int2)
          ::
              (v %mem-int3)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 14)
                  (v %r4)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-6-pop-mem-4
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o6)
          %-  add:mem-ld
          :*  (v %mem-int3)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 15)
                  (v %r5)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :: Nock 10
          ::   %op        = [f(%r2) 0 2]
          ::   tail1(%r3) = [f(%r2) 0 13]
          ::   tail2(%r4) = [f(%r2) 0 7]
          ::   tail3(%r5) = [f(%r2) 0 12]
          :-  %nock-10-pop-mem-1
          %+  mpmul  (v %popf-n)
          %+  mpmul  (v %o10-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r2-n)
                  (build-atom-literal.nu 2)
                  (build-atom-reg.nu %op-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-10-pop-mem-2
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o10)
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem-int2)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 13)
                  (v %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-10-pop-mem-3
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o10)
          %-  add:mem-ld
          :*  (v %mem-int2)
          ::
              (v %mem-int3)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 7)
                  (v %r4)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-10-pop-mem-4
          %+  mpmul  (v %popf)
          %+  mpmul  (v %o10)
          %-  add:mem-ld
          :*  (v %mem-int3)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 12)
                  (v %r5)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          ::
          :: Mode n0 (nock 0)
          ::
          :: Decode:
          ::   %op         =  [f(%r2) 0 2]
          ::   axis(r3)    =  [f(%r2) 0 3]
          :: Run nock 0:
          ::   child(%r4)  =  [s(%r1) 0 axis(%r3)]
          :: %tr3 contains the axis. We multiply [%s %tail1 %i] onto the memory multiset
          :: and i will be the subtree.
          ::
          :-  %nock-0-axis-inv-1
          %+  mpmul  (v %o0)
          (mpmul (mpsub one (v %r3)) (mpsub (mpmul (mpsub one (v %r3)) (v %r5)) one))
          ::
          :-  %nock-0-axis-inv-2
          %+  mpmul  (v %o0)
          (mpmul (v %r5) (mpsub (mpmul (mpsub one (v %r3)) (v %r5)) one))
          ::
          :-  %nock-0-mem-multiset-1
          %+  mpmul  (v %o0-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r2-n)
                  (build-atom-literal.nu 2)
                  (build-atom-reg.nu %op-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-0-mem-multiset-2
          %+  mpmul  (v %o0)
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem-int2)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 3)
                  (build-atom-reg.nu %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          ::  Only prove a nock 0 if axis != 1.
          :-  %nock-0-mem-multiset-3
          %+  mpmul  (v %o0)
          %+  mpmul  (v %mem-int3)
          %-  add:mem-ld
          :*  (v %mem-int2)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r1)
                  (build-atom-reg.nu %r3)
                  (v %r4)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          ::  If axis=1 then just copy mem-int1 to mem since we're not putting the final
          ::  zero onto the multiset.
          :-  %nock-0-mem-multiset-4
          %+  mpmul  (v %o0)
          %+  mpmul  (mpsub one (v %mem-int3))
          (mpsub (v %mem-int2) (v %mem))
          ::
          ::  If axis=1 then set subtree(r4) to subject(r1) since that's the product.
          :-  %nock-0-axis-1-r4
          %+  mpmul  (v %o0)
          %+  mpmul  (mpsub one (v %mem-int3))
          (mpsub (v %r4) (v %r1))
          ::
          ::  Push child(%r4) onto product stack
          :-  %nock-0-ps
          %+  mpmul  (v %o0-n)
          (mpsub (mpadd (mpscal alf (v %ps)) (v %r4-n)) (v %ps-n))
          ::  Increment ps length
          ::  $M_1(PSLEN + 1 - PSLEN')=0$
          :-  %nock-0-ps-len
          %+  mpmul  (v %o0-n)
          (mpsub (mpadd (v %ps-len) one) (v %ps-len-n))
          :: Mode n1 (nock 1)
          ::
          :: tail(%r3) is the product. Just push it onto the product stack and return to mode 1.
          :-  %nock-1-push-ps
          %+  mpmul  (v %o1-n)
          %+  mpmul  (v %popf-n)
          (mpsub (mpadd (mpscal alf (v %ps)) (v %r3-n)) (v %ps-n))
          ::  Increment ps length
          ::  $M_1(PSLEN + 1 - PSLEN')=0$
          :-  %nock-1-push-ps-len
          %+  mpmul  (v %o1-n)
          %+  mpmul  (v %popf-n)
          (mpsub (mpadd (v %ps-len) one) (v %ps-len-n))
          ::
          :: Nock 11 - run jet
          ::
          :: id:     %r3
          :: sample: %r4
          :: prod:   %r5
          ::
          :: Decode:
          ::   %op          = [f(%r2) 0 2]
          ::   jet-id(%r3)  = [f(%r2) 0 6]  :: jet id
          :: Decode sample (axis 6 of subject):
          ::   same(%r4)    = [s(%r1) 0 6]
          ::
          :-  %nock-11-mem-1
          %+  mpmul  (v %o11-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r2-n)
                  (build-atom-literal.nu 2)
                  (build-atom-reg.nu %op-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-11-mem-2
          %+  mpmul  (v %o11)
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem-int2)
          ::
              %-  make-zero.su
              :*  (v %r2)
                  (build-atom-literal.nu 6)
                  (v %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-11-mem-3
          %+  mpmul  (v %o11)
          %-  add:mem-ld
          :*  (v %mem-int2)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r1)
                  (build-atom-literal.nu 6)
                  (v %r4)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :: Multiply TUPLE(id(%r3), sample(%r4), product(%r5)) onto jet multiset.
          :-  %nock-11-jet-multiset
          %+  mpmul  (v %o11-n)
          %+  mpsub  (v %jet-n)
          %+  mpmul  (v %jet)
          %+  mpsub  (mp-c bet)
          ;:  mpadd
            (mpscal p (v %r3-n))
            (mpscal q (v %r4-n))
            (mpscal r-chal (v %r5-n))
          ==
          ::
          :: Push product(%r5) onto PS
          :-  %nock-11-ps
          %+  mpmul  (v %o11-n)
          %+  mpsub  (v %ps-n)
          (push ps (v %r5-n))
          ::
          :: ps-len + 1
          :-  %nock-11-ps-len
          %+  mpmul  (v %o11-n)
          %+  mpsub  (v %ps-len-n)
          (mpadd (v %ps-len) one)
          ::
          :: Op 15 (finish opcode)
          ::
          :: We have evaluated the subformula(e) and the products are on the product stack.
          :: Now we switch off the opcode contained in %tail1 to go to a mode to finish the
          :: specific opcode. (0 and 1 are evaluated directly and never get here. 99 is cons.)
          ::
          :: update OS
          ::
          :: nock 2 - pop pop and op off os, push pop back on
          :-  %nock2-os
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o2-n)
          %+  mpsub  (v %os-n)
          (push (pop-all os ~[(v %popf-n) (v %op-n)]) pop-mp)
          ::
          :: os len - 1
          :-  %nock2-os-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o2-n)
          (mpsub (v %os-len-n) (mpsub (v %os-len) one))
          ::
          :: nock 3, 4, 5, cons - pop pop and op off OS
          :-  %nock3-5-os
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  :(mpadd (v %o3-n) (v %o4-n) (v %o5-n) (v %o99-n))
          %+  mpsub  (v %os-n)
          (pop-all os ~[(v %popf-n) (v %op-n)])
          ::
          ::  nock 3,4,5 -
          ::    os-len - 2
          :-  %nock3-5-os-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  :(mpadd (v %o3-n) (v %o4-n) (v %o5-n) (v %o99-n))
          (mpsub (v %os-len-n) (mpsub (v %os-len) (mp-c (lift 2))))
          ::
          :: Nock 6
          ::
          :: %r1 - old subject
          :: %r2 - condition result
          :: %r3 - yes formula
          :: %r4 - no formula
          :: %r5 - leaf of %r2
          ::
          :: pop %popf, %op and PAIR(sub(%r1), yes(%r3), no(%r4)) off os, push pop on
          :-  %nock6-os-process
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o6-n)
          %+  mpsub  (v %os-n)
          %+  push
            %+  pop-all  os
            :~  (v %popf-n)
                (v %op-n)
                ;:  mpadd
                  (mpscal p (v %r1-n))
                  (mpscal q (v %r3-n))
                  (mpscal r-chal (v %r4-n))
            ==  ==
          pop-mp
          ::
          :: nock 6-
          ::   os-len - 2
          :-  %nock6-os-len-process
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o6-n)
          (mpsub (v %os-len-n) (mpsub (v %os-len) (mp-c (lift 2))))
          ::
          :: Nock 7- Pop %popf, %op and formula off OS into %r2 and push pop on
          :: Nock 9- Pop %popf, %op, axis (%r2), push pop
          ::
          :: Can use same constraint for 7 & 9 because both use %r2
          :-  %nock7-9-process-os
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (mpadd (v %o7-n) (v %o9-n))
          %+  mpsub  (v %os-n)
          (push (pop-all os ~[(v %popf-n) (v %op-n) (v %r2-n)]) pop-mp)
          ::
          :: nock 7,9
          ::   os-len - 2
          :-  %nock7-9-os-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (mpadd (v %o7-n) (v %o9-n))
          %+  mpsub  (v %os-len-n)
          (mpsub (v %os-len) (mp-c (lift 2)))

          ::
          :: Nock 8- Pop %popf, %op, new formula (%r2) and old subject (%r3). Push pop.
          :-  %nock8-process-os
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o8-n)
          %+  mpsub  (v %os-n)
          (push (pop-all os ~[(v %popf-n) (v %op-n) (v %r2-n) (v %r3-n)]) pop-mp)
          ::
          :: nock 8
          ::  os-len - 3
          :-  %nock8-os-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o8-n)
          %+  mpsub  (v %os-len-n)
          (mpsub (v %os-len) (mp-c (lift 3)))
          ::
          :: nock 10 - pop %popf, %op and axis (%r3) off os
          :-  %nock10-os
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o10-n)
          %+  mpsub  (v %os-n)
          (pop-all os ~[(v %popf-n) (v %op-n) (v %r3-n)])
          ::
          :: nock 10 - os len minus 3
          :-  %nock10-os-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o10-n)
          %+  mpsub  (v %os-len-n)
          (mpsub (v %os-len) (mp-c (lift 3)))
          ::
          :: finish nock 2
          ::
          :: pop S and F off PS, push onto CS, return to mode start.
          ::
          :: %r1 - subject
          :: %r2 - formula
          ::
          :-  %nock2-pop-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o2-n)
          %+  mpsub  (v %ps-n)
          (pop-all ps ~[(v %r1-n) (v %r2-n)])
          ::  Decrement ps length by 2
          ::  $(PSLEN - 2 - PSLEN')=0$
          :-  %nock2-pop-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o2-n)
          (mpsub (mpsub (v %ps-len) (mp-c (lift 2))) (v %ps-len-n))
          :: Push i and i2 onto CS
          :-  %nock2-push-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o2-n)
          %+  mpsub  (v %cs-n)
          (push-all cs ~[(v %r2-n) (v %r1-n)])
          ::
          :: finish nock 3
          ::
          :: %r1 - len
          :: %r2 - dyck
          :: %r3 - leaf
          :: %r4 - len - 1
          :: %r5 - (len-n)^{-1}
          ::
          :: We want to pop the noun off the top of the product stack, decode it,
          :: compute 0 if it’s a cell and 1 if it’s a noun, then encode the result
          :: and push on the product stack.
          ::
          :: Pop the noun off the top of the PS and decode into %r1, %r2, %r3.
          :: If len==1 then we have an atom so push 1 onto PS else 0.
          ::
          :: First %r4 must len(%r1) - 1
          :-  %nock3-len-minus-1
          %+  mpmul  (mpsub one (v %popf))
          %+  mpmul  (v %o3)
          (mpsub (mpsub (v %r1) one) (v %r4))
          ::
          :: %r5 must be the inverse of %r4(which is len - 1)
          :: r4(r4*r5 - 1)=0
          :: r5(r4*r5 - 1)=0
          :-  %nock3-leninv-1
          %+  mpmul  (v %o3)
          %+  mpmul  (mpsub (v %r1) one)
          (mpsub (mpmul (mpsub (v %r1) one) (v %r5)) one)
          ::
          :-  %nock3-leninv-2
          %+  mpmul  (v %o3)
          %+  mpmul  (v %r5)
          (mpsub (mpmul (mpsub (v %r1) one) (v %r5)) one)
          ::
          :: Now %r4*%r5 is 0 of LEN=1 (ie an atom) and 1 if its a cell, which
          :: is the opposite of what we want. So encode 1-%r4*%r5 as an atom
          :: and push onto PS
          ::
          :: Pop the noun off PS and decode into %r1,%r2,%r3, then push
          :: 1-%r4*%r5 on.
          :-  %nock3-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o3-n)
          %+  mpsub  (v %ps-n)
          %+  push
            (pop ps (make-noun ~[(v %r1-n) (v %r2-n) (v %r3-n)]))
          (build-atom-poly.nu (mpsub one (mpmul (mpsub (v %r1-n) one) (v %r5-n))))
          ::
          ::  PSLEN is unchanged
          :-  %nock3-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o3-n)
          (mpsub (v %ps-len) (v %ps-len-n))
          ::
          :: finish nock 4
          ::
          :: %r1 - len
          :: %r2 - dyck
          :: %r3 - leaf
          ::
          :: Pop PS, decode into len, leaf, dyck, increment leaf,
          :: encode, and push onto PS.
          ::
          :-  %nock4-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o4-n)
          %+  mpsub  (v %ps-n)
          %+  push
            (pop ps (make-noun ~[(v %r1-n) (v %r2-n) (v %r3-n)]))
          (build-atom-poly.nu (mpadd one (v %r3-n)))
          ::  PSLEN is unchanged
          :-  %nock4-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o4-n)
          (mpsub (v %ps-len) (v %ps-len-n))
          ::
          :: finish nock 5
          ::
          :: %r1 - noun1
          :: %r2 - noun2
          :: %r5 - (%r1 - %r2)^{-1}
          ::
          :: Pop %r1 and %r2 off PS.
          :: We want to check if %r1=%r2. So we put (%r1-%r2)^{-1} into %r6 and
          :: push this to PS.
          ::
          :: (%r1-%2)((%r1-%r2)*%r5 - 1) = 0
          :: %r5((%r1-%r2)*%r5 - 1) = 0
          :-  %nock5-inverse-1
          %+  mpmul  (v %o5)
          %+  mpmul  (mpsub (v %r1) (v %r2))
          (mpsub (mpmul (mpsub (v %r1) (v %r2)) (v %r5)) one)
          ::
          :-  %nock5-inverse-2
          %+  mpmul  (v %o5)
          %+  mpmul  (v %r5)
          (mpsub (mpmul (mpsub (v %r1) (v %r2)) (v %r5)) one)
          ::
          :: Pop %r1 and %r2 off PS, encode %r5 and push onto PS.
          :-  %nock5-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o5-n)
          %+  mpsub  (v %ps-n)
          %+  push
            (pop-all ps ~[(v %r1-n) (v %r2-n)])
          (build-atom-poly.nu (mpmul (mpsub (v %r1-n) (v %r2-n)) (v %r5-n)))
          ::
          ::  Decrment ps length by 1
          ::  $(PSLEN - 1 - PSLEN')=0$
          :-  %nock5-push-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o5-n)
          (mpsub (mpsub (v %ps-len) one) (v %ps-len-n))
          ::
          ::
          :: finish nock 6
          ::
          :: %r1 - old subject
          :: %r2 - condition result
          :: %r3 - yes formula
          :: %r4 - no formula
          :: %r5 - leaf of %r2
          ::
          :: pop top of PS into %r2
          :-  %nock6-pop-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o6-n)
          (mpsub (pop ps (v %r2-n)) (v %ps-n))
          ::
          :: decode %r2 into a+c*%r5 (so r2 is an atom in %r5)
          :-  %nock5-decode-r2
          %+  mpmul  (mpsub one (v %popf))
          %+  mpmul  (v %o6)
          (mpsub (v %r2) (mpadd (mp-c a) (mpscal c (v %r5))))
          ::
          ::  result must be 0 or 1
          :-  %nock6-product-binary
          %+  mpmul  (mpsub one (v %popf))
          %+  mpmul  (v %o6)
          (mpmul (v %r5) (mpsub (v %r5) one))
          ::
          :: if r5=0 then push subject(%r1), yes(%r3) onto cs
          :-  %nock6-0-push-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o6-n)
          %+  mpmul  (mpsub (v %r5-n) one)
          %+  mpsub  (v %cs-n)
          (push-all cs ~[(v %r3-n) (v %r1-n)])
          ::
          :: eles if r=1 then push s, r3 onto cs
          :-  %nock6-1-push-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o6-n)
          %+  mpmul  (v %r5-n)
          %+  mpsub  (v %cs-n)
          (push-all cs ~[(v %r4-n) (v %r1-n)])
          ::
          ::
          :: Finish nock 7
          ::
          :: Pop subject (%r) off PS and push subject (%r) and formula (%r2) onto CS
          ::
          :: NOTE: 7,8, and 9 use the same PS constraints because they all pop one
          :: product into %r.
          :-  %nock-7-8-9-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  :(mpadd (v %o7-n) (v %o8-n) (v %o9-n))
          %+  mpsub  (v %ps-n)
          (pop ps (v %r1-n))
          ::
          :-  %nock-7-8-9-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  :(mpadd (v %o7-n) (v %o8-n) (v %o9-n))
          %+  mpsub  (v %ps-len-n)
          (mpsub (v %ps-len) one)
          ::
          :-  %nock-7-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o7-n)
          %+  mpsub  (v %cs-n)
          (push-all cs ~[(v %r2-n) (v %r1-n)])
          ::
          :-  %nock-7-cs-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o7-n)
          %+  mpsub  (v %cs-len-n)
          (mpadd (v %cs-len) (mp-c (lift 2)))
          ::
          :: Finish nock 8
          ::
          :: %r1 - head
          :: %r2 - formula
          :: %r3 - old subject
          :: %r4 - new subject
          ::
          :: Pop the new head off PS into %r. Pop the new formula off OS into %r2 and the old
          :: subject we stashed into %r3. Next pin %r2 to the head of %r3 by multiplying onto
          :: %mem TUPLE(new-subject=%r4, axis=2, head=%r, new-subject=%r4, head=%r) and
          :: TUPLE(new-subject=%r4, axis=3, old-subject=%r3, new-subject=%r4, old-subject=%r3).
          :: Finally push both onto CS and push pop onto OS.
          ::
          :: NOTE: nock 8 uses nock 7's PS constraints
          ::
          :: We are pinning the result in %r onto the subject in %r3 by nondeterministically
          :: computing the result %r4 and proving two CONS:
          ::    %r1 = [%r4 0 2]  :: head is head of new subject
          ::    %r3 = [%r4 0 3]  :: old subject is tail of new subject
          :-  %nock-8-mem-1
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o8-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r4-n)
                  (build-atom-literal.nu 2)
                  (v %r1-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %nock-8-mem-2
          %+  mpmul  (mpsub one (v %popf))
          %+  mpmul  (v %o8)
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r4)
                  (build-atom-literal.nu 3)
                  (v %r3)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :: Push formula (%r2) and new subject (%r4) onto CS
          :-  %nock-8-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o8-n)
          %+  mpsub  (v %cs-n)
          (push-all cs ~[(v %r2-n) (v %r4-n)])
          ::
          :-  %nock-8-cs-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o8-n)
          %+  mpsub  (v %cs-len-n)
          (mpadd (v %cs-len) (mp-c (lift 2)))
          ::
          ::
          :: Finish nock 9
          ::
          :: %r1 - core
          :: %r2 - axis
          :: %r3 - arm
          ::
          :: Pop the core off PS into %r1. Pop axis off OS into %r2.
          :: Nondeterministically store the new arm in %r3 and prove this
          :: by multiplying onto %mem:
          ::   TUPLE(core=%r1, axis=%r2, arm=%r3, core=%r1, arm=%r3)
          :: Then push core=%r2 and arm=%r2 onto CS and push pop onto OS.
          ::
          :: NOTE: nock 9 uses nock 7's PS constraints
          ::
          :: Prove that arm(%r3) is at axis(%r2) in core(%1r)
          :-  %nock-9-mem
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o9-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-n)
          ::
              (make-zero.su (v %r1-n) (v %r2-n) (v %r3-n))
          ::
              (mp-c (lift 1))
          ==
          ::
          :: Push arm(%r3) and core(%r2) onto CS
          :-  %nock-9-cs
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o9-n)
          %+  mpsub  (v %cs-n)
          (push-all cs ~[(v %r3-n) (v %r1-n)])
          ::
          :-  %nock-9-cs-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o9-n)
          %+  mpsub  (v %cs-len-n)
          (mpadd (v %cs-len) (mp-c (lift 2)))
          ::
          ::
          :: Finish nock 10
          ::
          :: %r1 - child
          :: %r2 - new-new
          :: %r3 - axis
          :: %r4 - target
          :: %r5 - value
          ::
          :: Pop top two nouns off PS (target=%r4 and value=%r5). Then multiply onto %mem
          :: TUPLE(target=%r4,axis=%r3,child=%r,new-noun=%r2,value=%r5).
          :: Finally push new-noun=%r2 onto PS.
          ::
          :: First pop off PS
          :-  %nock10-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o10-n)
          %+  mpsub  (v %ps-n)
          (push (pop-all ps ~[(v %r5-n) (v %r4-n)]) (v %r2-n))
          ::
          :: ps len minus 1
          :-  %nock10-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o10-n)
          %+  mpsub  (v %ps-len-n)
          (mpsub (v %ps-len) one)
          ::
          :: Multiply TUPLE(%r4,%r3,%r,%r2,%r5) onto %mem
          :-  %nock10-memset
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o10-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-n)
          ::
              %-  ~(compress poly-tupler tupler)
              ~[(v %r4-n) (v %r3-n) (v %r1-n) (v %r2-n) (v %r5-n)]
          ::
              (mp-c (lift 1))
          ==
          ::
          :: finish cons (op 99)
          ::
          :: %r1 - left
          :: %r2 - right
          :: %r3 - [left right]
          ::
          :: Pop top two nouns off PS, cons them, push onto PS.
          :: We cons them by nondeterministically writing the cons into a register
          :: and then proving it by doing two nock 0's:
          ::   LEFT=[0 2 CONS]
          ::   RIGHT=[0 3 CONS]
          ::
          :: Which we do by multiplying corresponding tuples onto the %mem multiset.
          :-  %cons-mem-1
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o99-n)
          %-  add:mem-ld
          :*  (v %mem)
          ::
              (v %mem-int1-n)
          ::
              %-  make-zero.su
              :*  (v %r3-n)
                  (build-atom-literal.nu 2)
                  (v %r1-n)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::
          :-  %cons-mem-2
          %+  mpmul  (mpsub one (v %popf))
          %+  mpmul  (v %o99)
          %-  add:mem-ld
          :*  (v %mem-int1)
          ::
              (v %mem)
          ::
              %-  make-zero.su
              :*  (v %r3)
                  (build-atom-literal.nu 3)
                  (v %r2)
              ==
          ::
              (mp-c (lift 1))
          ==
          ::  Pop left(%r) and right(%r2) off PS and push cons(%r3) on
          :-  %cons-ps
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o99-n)
          %+  mpsub  (v %ps-n)
          (push (pop-all ps ~[(v %r1-n) (v %r2-n)]) (v %r3-n))
          ::
          :: ps len minus 1
          :-  %cons-ps-len
          %+  mpmul  (mpsub one (v %popf-n))
          %+  mpmul  (v %o99-n)
          %+  mpsub  (v %ps-len-n)
          (mpsub (v %ps-len) one)
      ==
    --
  --
--
