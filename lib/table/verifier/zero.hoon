/+  *table, *fock, common=table-zero, terminal, jet
=,  f
::
|%
++  v  ~(v var variables:common)
++  one      (mp-c (lift 1))
::
++  nockzs
  |%
  ::
  ++  funcs
    ^-  verifier-funcs
    |%
    ++  boundary-constraints
      |=  [challenges=(list felt)]
      =/  r  ~(r rnd (make-challenge-map challenges %nockzs))
      =/  [a=felt b=felt c=felt p=felt q=felt r=felt s=felt t=felt alf=felt bet=felt]
        :*  (r %a)  (r %b)  (r %c)
            (r %p)  (r %q)  (r %r)  (r %s)  (r %t)
            (r %alf)  (r %bet)
        ==
      =/  mem-ld       ~(. poly-ld bet)
      =/  tupler       ~[p q r s t]
      =/  nu           ~(. noun-poly-utils [a b c alf] variables:common)
      ::
      ::  polynomials for tree felts
      =/  tree-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %tree-len))
          (mpscal b (v %tree-dyck))
          (mpscal c (v %tree-leaf))
        ==
      ::
      =/  left-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %left-len))
          (mpscal b (v %left-dyck))
          (mpscal c (v %left-leaf))
        ==
      ::
      =/  right-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %right-len))
          (mpscal b (v %right-dyck))
          (mpscal c (v %right-leaf))
        ==
      ::
      =/  new-tree-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %new-tree-len))
          (mpscal b (v %new-tree-dyck))
          (mpscal c (v %new-tree-leaf))
        ==
      ::
      =/  new-left-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %new-left-len))
          (mpscal b (v %new-left-dyck))
          (mpscal c (v %new-left-leaf))
        ==
      ::
      =/  new-right-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %new-right-len))
          (mpscal b (v %new-right-dyck))
          (mpscal c (v %new-right-leaf))
        ==
      ::
      ::  next row tree felts
      =/  tree-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %tree-len-n))
          (mpscal b (v %tree-dyck-n))
          (mpscal c (v %tree-leaf-n))
        ==
      ::
      =/  left-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %left-len-n))
          (mpscal b (v %left-dyck-n))
          (mpscal c (v %left-leaf-n))
        ==
      ::
      =/  right-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %right-len-n))
          (mpscal b (v %right-dyck-n))
          (mpscal c (v %right-leaf-n))
        ==
      ::
      =/  new-tree-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %new-tree-len-n))
          (mpscal b (v %new-tree-dyck-n))
          (mpscal c (v %new-tree-leaf-n))
        ==
      ::
      =/  new-left-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %new-left-len-n))
          (mpscal b (v %new-left-dyck-n))
          (mpscal c (v %new-left-leaf-n))
        ==
      ::
      =/  new-right-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %new-right-len-n))
          (mpscal b (v %new-right-dyck-n))
          (mpscal c (v %new-right-leaf-n))
        ==
      :~
        ::  axis starts at 1
          (mpsub (v %axis) one)
        ::
        ::  subj=tree-felt to start
          (mpsub (v %subj) tree-felt)
        ::  new-subject=new-tree-felt to start
          (mpsub (v %new-subj) new-tree-felt)
        ::
        ::  out may begin with first row info "pre-added"
        ::
        ::    The only way we can begin with output that needs to be recorded is if we start
        ::    with a [%0 1], which happens when yetf=0, and if `none` is false i.e. none=1.
        ::
        ::    out = yetf + (1-yetf)[(1-none) + none•(bet - (p*subj + q*(a + c) + r*tree-felt))]
        ::
          (mpmul (v %yetf) (mpsub (v %out) one))
        ::
        ::
          %+  mpmul  (mpsub one (v %yetf))
          %+  mpmul  (v %path)
          %-  add:mem-ld
          :*  one
          ::
              (v %out)
          ::
              %-  ~(compress poly-tupler tupler)
              :~  (v %subj)
                  (build-atom-reg.nu %tar)
                  right-felt
                  (v %new-subj)
                  new-right-felt
              ==
          ::
              (v %uses)
          ==
        ::
          %+  mpmul  (mpsub one (v %yetf))
          %+  mpmul  (mpsub one (v %path))
          %-  add:mem-ld
          :*  one
          ::
              (v %out)
          ::
              %-  ~(compress poly-tupler tupler)
              :~  (v %subj)
                  (build-atom-reg.nu %tar)
                  left-felt
                  (v %new-subj)
                  new-left-felt
              ==
          ::
              (v %uses)
          ==
        ::
        ::
        ::  noun-mulset may begin with first row info "pre-added"
        ::
        ::    If we start with a generic Nock 0 where the target axis is not 1, i.e. yetf
        ::    is 1 at the start, we have to add the left and right subtrees of the subject
        ::    initially. Otherwise, if none is true (=0), we don't want to preadd, while if
        ::    none is false (=1) it depends on whether uses starts with 0 or not. (If uses
        ::    starts with 0, this confusingly means we need to record this Nock 0 once,
        ::    because of how the table works in the generic case.)
        ::
        ::    NOTE: none•usesf = usesf since none=0 => usesf=0 which we use to optimize
        ::    the written constraint in the code below.
        ::
        ::  TODO: Hook up noun multiset. I'm leaving this commented out for now because
        ::  it's not yet degree 4 and so it will drastically slow down the prover.
        ::  And the noun table isn't even hooked up and I think we don't even need to use
        ::  it as much as we are.
        ::
        ::    noun-mulset = yetf•(bet - left-felt)(bet - right-felt)
        ::                    + (1-yetf)•[(1-none) + none•[usesf + (1-usesf)•(bet - tree-felt)]
          ::%+  mpsub  (v %noun-mulset)
          ::%+  mpadd
            ::;:  mpmul
              ::(v %yetf)
              ::(mpsub (mp-c bet) left-felt)
              ::(mpsub (mp-c bet) right-felt)
              ::(mpsub (mp-c bet) new-left-felt)
              ::(mpsub (mp-c bet) new-right-felt)
            ::==
          ::%+  mpmul  (mpsub one (v %yetf))
          ::;:    mpadd
              ::(mpsub one (v %none))
            ::::
              ::(v %usesf)
            ::::
              ::;:  mpmul
                ::(mpsub (v %none) (v %usesf))
                ::(mpsub (mp-c bet) tree-felt)
                ::(mpsub (mp-c bet) new-tree-felt)
              ::==
          ::==
      ==
    ::
    ::  transition constraints: constraints to apply to every pair of rows
    ::
    ::    Computation structure: subcomputations for each subject and axis target (=tar),
    ::    and within these subcomputations there are two phases: first phase where (virtual) yet
    ::    = tar - axis =! 0 and the second where yet=0. A subcomputation has a constant target.
    ::    The two phases are distinguished by yetf=1 and 0, respectively. (yet =! 0 and yet=0).
    ::    In the first phase, uses is constant, while in the second it decrements to 0; uses=0
    ::    is the trigger for target to change and to enter a new subcomputation.
    ::    In the first phase we verify a cons in each line and replace subject tree info by
    ::    left or right subtree info in the next line, according to path. In the second phase
    ::    the subject tree is the target subtree and stays constant, while the left and right
    ::    subtree info becomes irrelevant.
    ::    Padding is done by setting the prover setting target=0; a constraint forces path=0
    ::    in this section, and then axis evolves in such a way that it never hits the target.
    ::    Thus no additional output accumulation can occur in this section.
    ++  transition-constraints
      |=  [challenges=(list felt) =jet-map:jet]
      ^-  (map term multi-poly)
      =/  r  ~(r rnd (make-challenge-map challenges %nockzs))
      =/  [a=felt b=felt c=felt p=felt q=felt r=felt s=felt t=felt alf=felt bet=felt]
        :*  (r %a)  (r %b)  (r %c)
            (r %p)  (r %q)  (r %r)  (r %s)  (r %t)
            (r %alf)  (r %bet)
        ==
      =/  mem-ld       ~(. poly-ld bet)
      =/  tupler       ~[p q r s t]
      =/  nu           ~(. noun-poly-utils [a b c alf] variables:common)
      ::
      ::  polynomials for tree felts
      =/  tree-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %tree-len))
          (mpscal b (v %tree-dyck))
          (mpscal c (v %tree-leaf))
        ==
      =/  left-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %left-len))
          (mpscal b (v %left-dyck))
          (mpscal c (v %left-leaf))
        ==
      =/  right-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %right-len))
          (mpscal b (v %right-dyck))
          (mpscal c (v %right-leaf))
        ==
      =/  new-tree-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %new-tree-len))
          (mpscal b (v %new-tree-dyck))
          (mpscal c (v %new-tree-leaf))
        ==
      =/  new-left-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %new-left-len))
          (mpscal b (v %new-left-dyck))
          (mpscal c (v %new-left-leaf))
        ==
      =/  new-right-felt=multi-poly
        ;:  mpadd
          (mpscal a (v %new-right-len))
          (mpscal b (v %new-right-dyck))
          (mpscal c (v %new-right-leaf))
        ==
      ::  next row tree felts
      =/  tree-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %tree-len-n))
          (mpscal b (v %tree-dyck-n))
          (mpscal c (v %tree-leaf-n))
        ==
      =/  left-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %left-len-n))
          (mpscal b (v %left-dyck-n))
          (mpscal c (v %left-leaf-n))
        ==
      =/  right-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %right-len-n))
          (mpscal b (v %right-dyck-n))
          (mpscal c (v %right-leaf-n))
        ==
      =/  new-tree-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %new-tree-len-n))
          (mpscal b (v %new-tree-dyck-n))
          (mpscal c (v %new-tree-leaf-n))
        ==
      =/  new-left-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %new-left-len-n))
          (mpscal b (v %new-left-dyck-n))
          (mpscal c (v %new-left-leaf-n))
        ==
      =/  new-right-felt-n=multi-poly
        ;:  mpadd
          (mpscal a (v %new-right-len-n))
          (mpscal b (v %new-right-dyck-n))
          (mpscal c (v %new-right-leaf-n))
        ==
      %-  ~(gas by *(map term multi-poly))
      :~
        ::
        ::  path is binary
          :-  %path-is-binary
          %+  mpmul
            (v %path)
          (mpsub one (v %path))
        ::
        ::  tar/tari/tarf constaint system
          :-  %tar-tarf-tari-1
          %+  mpmul  (v %tar)
          (mpsub (v %tarf) one)
        ::
          :-  %tar-tarf-tari-2
          %+  mpmul  (v %tari)
          (mpsub (v %tarf) one)
        ::
          :-  %tar-tarf-tari-3
          %+  mpsub  (v %tarf)
          (mpmul (v %tar) (v %tari))
        ::
        ::  yet/yeti/yetf constaint system
          :-  %yet-yetf-yeti-1
          %+  mpmul  (v %yet)
          (mpsub (v %yetf) one)
        ::
          :-  %yet-yetf-yeti-2
          %+  mpmul  (v %yeti)
          (mpsub (v %yetf) one)
        ::
          :-  %yet-yetf-yeti-3
          %+  mpsub  (v %yetf)
          (mpmul (v %yet) (v %yeti))
        ::
        ::  cons relations
        ::
        ::    Only apply if yetf=1 (haven't hit the target subtree) and tarf=1 (non-padding
        ::    section).
        ::    TODO: Get rid of the tarf part and figure out how to pad to satisfy these
        ::    constraints everywhere.
        ::
        ::    yetf•tarf•(S-[L R])
          :-  %cons-len
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %tree-len)
          (mpadd (v %left-len) (v %right-len))
        ::
          :-  %cons-dyck
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %tree-dyck)
          ;:    mpadd
              (v %right-dyck)
            ::
              %+  mpscal  (finv (fmul alf alf))
              (mpmul (v %exp-r) (v %exp-r))
            ::
              %+  mpmul  (v %left-dyck)
              %+  mpscal  (finv alf)
              (mpmul (v %exp-r) (v %exp-r))
          ==
        ::
        ::
          :-  %cons-leaf
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %tree-leaf)
          %+  mpadd  (v %right-leaf)
          %+  mpmul  (v %left-leaf)
          (v %exp-r)
        ::
        ::  second walk
        ::
          :-  %cons-new-len
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %new-tree-len)
          %+  mpadd  (v %new-left-len)
          (v %new-right-len)
        ::
          :-  %cons-new-dyck
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %new-tree-dyck)
          ;:    mpadd
            (v %new-right-dyck)
            ::
              %+  mpscal  (finv (fmul alf alf))
              (mpmul (v %new-exp-r) (v %new-exp-r))
            ::
              %+  mpmul  (v %new-left-dyck)
              %+  mpscal  (finv alf)
              (mpmul (v %new-exp-r) (v %new-exp-r))
          ==
        ::
          :-  %cons-new-leaf
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %new-tree-leaf)
          %+  mpadd  (v %new-right-leaf)
          %+  mpmul  (v %new-left-leaf)
          (v %new-exp-r)
        ::
        ::
        ::  evolution of tree according to path
        ::
        ::    New subject tree is the left or right subtree according to path value,
        ::    as long as yetf=1. If yetf=0 then we're accruing multiple copies so
        ::    the tree stays constant until uses=0, where its next value could be anything.
        ::
        ::    (S'-[(1-path)L+path•R])yetf + (1-yetf)•usesf•(S'-S)
          :-  %tree-felt-evo
          %+  mpmul  (mpadd (mpscal (lift 2) (v %axis)) (v %path))
          %+  mpmul  (v %yetf)
          %+  mpsub  tree-felt-n
          %+  mpadd
            (mpmul (mpsub one (v %path)) left-felt)
          (mpmul (v %path) right-felt)
        ::
        :: 2nd tree walk
          :-  %new-tree-felt-evo
          %+  mpmul  (v %yetf)
          %+  mpsub  new-tree-felt-n
          %+  mpadd
            (mpmul (mpsub one (v %path)) new-left-felt)
          (mpmul (v %path) new-right-felt)
        ::
        ::  the unchosen siblings of both tree walks must be equal
        ::  path*(left-felt - new-left-felt) + (1-path)(right-felt - new-right-felt)
          :-  %siblings-equal
          %+  mpadd
            %+  mpmul  (v %path)
            (mpsub left-felt new-left-felt)
          %+  mpmul  (mpsub one (v %path))
          (mpsub right-felt new-right-felt)
        ::
        ::  evolution of axis
        ::
        ::    While yetf=1, axis evolves according to path. While yetf=0, axis remains the
        ::    same as long as uses =! 0, but if uses=0, the next value of axis=1 i.e. we're
        ::    starting over with the next Nock 0.
        ::
        ::    [axis'-(2axis + path)]•yetf + (1-yetf)•usesf•[axis'-axis] + (1-yetf)(1-usesf)(axis'-1)
        ::
        ::    but we can replace yetf•usesf with yetf and get
        ::    [axis'-(2axis + path)]•yetf + (usesf-yetf)•[axis'-axis] + (1-usesf)(axis'-1); deg=2
          :-  %axis-evo
          %+    mpadd
            %+  mpmul  (v %yetf)
            %+  mpsub  (v %axis-n)
            %+  mpadd  (v %path)
            (mpscal (lift 2) (v %axis))
          ::
          %+  mpmul  (mpsub one (v %yetf))
          (mpsub (v %axis-n) one)
        ::
        ::  tar evolution
        ::
        ::    tar stays constant until it's time to start a new Nock 0 i.e. when uses=0
        ::
        ::    usesf•(tar'-tar); deg=2
          :-  %tar-evo
          %+  mpmul  (v %yetf)
          (mpsub (v %tar-n) (v %tar))
        ::
        ::  evolution of subj
        ::
        ::    Same as tar, mutatis mutandis; stays constant as long as uses isn't exhausted.
        ::    When uses=0, the subsequent value is constrained; see next.
        ::
        ::    usesf•(subj' - subj)
          :-  %subj-evo
          %+  mpmul  (v %yetf)
          (mpsub (v %subj-n) (v %subj))
        ::
        ::  subj=tree-felt when we start a new subcomputation
        ::
        ::  (1-usesf)(subj'-tree-felt')
          :-  %subj-eq-tree-felt-at-start
          %+  mpmul  (mpsub one (v %yetf))
          (mpsub (v %subj-n) tree-felt-n)
        ::
        ::  If target is 0 (i.e. in padding section), path=0; this makes padding scheme work
        ::  by causing continuous multiplications by 2 in axis which never hit the target of 0
        ::
        ::    path•(1-tarf); deg=2
          :-  %target-0-path-0
          (mpmul (v %path) (mpsub one (v %tarf)))
        ::
        ::  evolution of out
        ::
        ::    (1-yetf')•(out'-out•(bet-(p*subj' + q*(a + c*tar') + r*(tree-felt'))))
          :-  %out-evo-right
          %+  mpmul  (mpsub one (v %yetf-n))
          %+  mpmul  (v %path-n)
          %-  add:mem-ld
          :*  (v %out)
          ::
              (v %out-n)
          ::
              %-  ~(compress poly-tupler tupler)
              :~  (v %subj-n)
                  (build-atom-reg.nu %tar-n)
                  right-felt-n
                  (v %new-subj-n)
                  new-right-felt-n
              ==
          ::
              (v %uses-n)
          ==
        ::
          :-  %out-evo-left
          %+  mpmul  (mpsub one (v %yetf-n))
          %+  mpmul  (mpsub one (v %path-n))
          %-  add:mem-ld
          :*  (v %out)
          ::
              (v %out-n)
          ::
              %-  ~(compress poly-tupler tupler)
              :~  (v %subj-n)
                  (build-atom-reg.nu %tar-n)
                  left-felt-n
                  (v %new-subj-n)
                  new-left-felt-n
              ==
          ::
              (v %uses-n)
          ==
        ::
        ::  evolution of noun-mulset
        ::
        ::    We only have to remove the left and right trees in cons rows for validation
        ::    since the cons constraint will imply the subject tree felt is valid.
        ::    Notice that in each row, the relevant info in the row has already been added
        ::    from the multiset, so there is a corresponding first-row constraint that
        ::    has to "pre-add" the first row info to the multiset.
        ::    Note we only record tree-felt when usesf'=0, which only happens once per
        ::    (subject, target) pair, to cut down on redundancy.
        ::
        :: TODO: This is commented out for reasons explained above. We will fix it up when we
        :: hook up the noun table.
        ::
        ::    noun-mulset'
        ::      = noun-mulset•[(1-tarf') + tarf'•[(usesf'-yetf') +
        ::            (1-usesf')(bet - tree-felt') + yetf'•(bet - left-felt')(bet - right-felt')]]
        ::
        ::    degree = 5  TODO: reduce
          :::-  %noun-mulset-evo
          ::%+  mpsub  (v %noun-mulset-n)
          ::%+  mpmul  (v %noun-mulset)
          ::%+  mpadd
            ::(mpsub one (v %tarf-n))
          ::%+  mpmul  (v %tarf-n)
          ::;:    mpadd
              ::(mpsub (v %usesf-n) (v %yetf-n))
            ::::
              ::;:  mpmul
                ::(mpsub one (v %usesf-n))
                ::(mpsub (mp-c bet) tree-felt-n)
                ::(mpsub (mp-c bet) new-tree-felt-n)
              ::==
            ::::
              ::;:  mpmul
                ::(v %yetf-n)
                ::(mpsub (mp-c bet) left-felt-n)
                ::(mpsub (mp-c bet) right-felt-n)
                ::(mpsub (mp-c bet) new-left-felt-n)
                ::(mpsub (mp-c bet) new-right-felt-n)
              ::==
          ::==
      ==
    ::
    ++  terminal-constraints
      |=  [challenges=(list @) terminals=(map term (map term felt))]
      =/  r  ~(r rnd (make-challenge-map challenges %nockzs))
      =/  [a=felt b=felt c=felt p=felt q=felt r=felt s=felt t=felt alf=felt bet=felt]
        :*  (r %a)  (r %b)  (r %c)
            (r %p)  (r %q)  (r %r)  (r %s)  (r %t)
            (r %alf)  (r %bet)
        ==
      ::=/  nockzs-terminals=(unit (map term felt))
      =/  nockzs-terminals  (~(get by terminals) %nockzs)
      =/  terminal-consistency-checks=(list multi-poly)
        ?~  nockzs-terminals  ~
        (gen-consistency-checks:terminal u.nockzs-terminals variable-labels:common v)
      %+  weld  terminal-consistency-checks
      :~
        ::
        ::  path is binary
          %+  mpmul
            (v %path)
          (mpsub one (v %path))
        ::
        ::  tar/tari/tarf constaint system
          %+  mpmul  (v %tar)
          (mpsub (v %tarf) one)
        ::
          %+  mpmul  (v %tari)
          (mpsub (v %tarf) one)
        ::
          %+  mpsub  (v %tarf)
          (mpmul (v %tar) (v %tari))
        ::
        ::  yet/yeti/yetf constaint system
          %+  mpmul  (v %yet)
          (mpsub (v %yetf) one)
        ::
          %+  mpmul  (v %yeti)
          (mpsub (v %yetf) one)
        ::
          %+  mpsub  (v %yetf)
          (mpmul (v %yet) (v %yeti))
        ::
        ::  cons relations
        ::
        ::    Only apply if yetf=1 (haven't hit the target subtree) and tarf=1 (non-padding
        ::    section).
        ::    TODO: Get rid of the tarf part and figure out how to pad to satisfy these
        ::    constraints everywhere.
        ::
        ::    yetf•tarf•(S-[L R])
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %tree-len)
          (mpadd (v %left-len) (v %right-len))
        ::
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %tree-dyck)
          ;:    mpadd
              (v %right-dyck)
            ::
              %+  mpscal
                (finv (fmul alf alf))
              (mpmul (v %exp-r) (v %exp-r))
            ::
              %+  mpmul
                (v %left-dyck)
              %+  mpscal  (finv alf)
              (mpmul (v %exp-r) (v %exp-r))
          ==
        ::
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %tree-leaf)
          %+  mpadd  (v %right-leaf)
          %+  mpmul  (v %left-leaf)
          (v %exp-r)
        ::
        :: cons relations for second tree walk
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %new-tree-len)
          (mpadd (v %new-left-len) (v %new-right-len))
        ::
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %new-tree-dyck)
          ;:    mpadd
              (v %new-right-dyck)
            ::
              %+  mpscal  (finv (fmul alf alf))
              (mpmul (v %new-exp-r) (v %new-exp-r))
            ::
              %+  mpmul  (v %new-left-dyck)
              %+  mpscal  (finv alf)
              (mpmul (v %new-exp-r) (v %new-exp-r))
          ==
        ::
          %+  mpmul  (v %tarf)
          %+  mpsub  (v %new-tree-leaf)
          %+  mpadd  (v %new-right-leaf)
          (mpmul (v %new-left-leaf) (v %new-exp-r))
      ==
    --
  --
--
