::  noun-table: implements a multiset of arbitrarily large nouns, encoded using
::  their leaf vector and dyck path
::
/+  *table, shape, fock, chal=challenges, util=table-util, jet
=,  chal
=,  util
::
=,  f
::
|%
++  test
  |=  sam=(list [[dyck=(list belt) leaf=(list belt)] @])
  =/  ret=return:fock
    :^  ~  ~  ~
    %-  ~(gas by *(map * @))
    %+  turn  sam
    |=  [[dyck=(list belt) leaf=(list belt)] mult=@]
    [(grow:shape dyck leaf) mult]
  =/  init-table  (build:noun ret)
  =/  padded
    (pad:funcs:noun p.init-table (bex (xeb (dec (lent p.init-table)))))
  =/  challenges
    (turn (turn (range 10) bex) gen-random-felt)
  =/  rows  p:(extend:funcs:noun [-:init-table padded] challenges ~ ret)
  %^  zip  (range 0 (lent rows))  rows
  |=  [i=@ row=fpoly]
  =/  list-row=(list @ux)  ~(to-poly fop row)
  [i (zip-up variable-labels list-row)]
::
++  test-input
  :~  [[~ ~[1]] 2]
      [[~[0 0 0 1 1 1] ~[1 2 3 4]] 1]
      [[~[0 1 0 0 1 1] ~[1 2 4 8]] 2]
      [[~[0 0 1 1 0 1] ~[2 3 5 7]] 3]
  ==
::
++  degrees
  ^-  @
  =/  challenges
    (turn (gulf 0 10) |=(n=@ (lift (mod (shax n) p))))
  =/  degs
    %+  turn  (unlabeled-transition-constraints:funcs:noun challenges)
    |=  mp=multi-poly
    ~&  >  "{<(mp-degree mp)>}"
    5
  5
++  num-randomizers  1
++  one  (mp-c (lift 1))
++  base-variables
  ^-  (list term)
  :~  %dyck  ::  dyck word characters
      %leaf  ::  (stretched) leaf vector
      %ct  ::  (weighted) count of dyck symbols
      %succit  ::  successor-of-count's inverse
      %rem  ::  characters remaining in dyck word, including one in current row
      %remi  ::  rem inverse
      %remf ::  rem flag
      %uses  ::  number of uses of current noun in computation as subject or formula
      %usesi  ::  uses inverse
      %usesf  ::  uses flag
      %triv  ::  flag; is the current noun trivial?
      %len  ::  computes the length of leaf
  ==
::
++  extension-variables
  ^-  (list term)
  :~  %dyck-stack
      %leaf-stack
      %mset
  ==
::
++  variable-labels
  ^-  (list term)
  (weld base-variables extension-variables)
::
++  variable-indices
  ^-  (map term @)
  %-  ~(gas by *(map term @))
  (zip-up variable-labels (range (lent variable-labels)))
::
++  variables
  ^-  (map term multi-poly:f)
  %-  make-vars
  variable-labels
::
++  v  ~(v var variables)
::
::  grab: alias for snagging from a row using the variable name instead of column index
++  grab
  |=  [label=term row=fpoly]
  %-  ~(snag fop row)
  (~(got by variable-indices) label)
::
++  roweld
    |=  [l=fpoly r=fpoly]
    (~(weld fop l) r)
::
::  stretch: stretches vec appropriately to have the same length as dyk
++  stretch
  |=  [dyk=(list belt) vec=(list belt)]
  ^-  (list belt)
  ?>  =((sub (mul 2 (lent vec)) 2) (lent dyk))
  =|  strch=(list belt)
  |-
  ?~  dyk
    (flop strch)
  ?<  ?=(~ vec)
  ?.  ?|(=(i.dyk 0) =(i.dyk 1))
    !!
  ?:  =(i.dyk 0)
    $(strch [i.vec strch], dyk t.dyk)
  ?<  ?=(~ t.vec)
  $(strch [i.t.vec strch], vec t.vec, dyk t.dyk)
::
::
++  dyck-stack-timeseries
  |=  [dyk=(list belt) rando=felt]
  ^-  (list felt)
  =-  ?<  ?=(~ series)
      (flop series)
  %+  roll  dyk
  |=  [w=belt [stack=_(lift 0) series=(list felt)]]
  =/  stamp  (fadd (fmul rando stack) (lift w))
  [stamp [stamp series]]
::
::
++  stretched-leaf-stack-timeseries
  |=  [lef=(list belt) rando=felt]
  ^-  (list felt)
  =|  series=(list felt)
  |-
  ?:  =((lent lef) 0)
    ?<  ?=(~ series)
    (flop series)
  =/  stack-state  ?~(series (lift 0) i.series)
  %_    $
      lef
    (slag 1 lef)
  ::
      series
    ?:  ?&  (gth (lent lef) 1)
            =((snag 0 lef) (snag 1 lef))
        ==
      [stack-state series]
    [(fadd (fmul rando stack-state) (lift (snag 0 lef))) series]
  ==
::
++  noun
  |%
  ++  build
    |=  =return:fock
    ^-  table
    :-  [p (lent base-variables) (lent variable-labels) num-randomizers]
    =/  noun-mult
      %~  tap  by
      %-  (~(uno by subjects.return) formulas.return)
      |=  [* mult-s=@ mult-f=@]
      (add mult-s mult-f)
    ::  for each noun we produce the list of rows in the table for it, then zing together
    %-  zing
    %+  turn  noun-mult
    |=  [noun=* mult=@]
    ^-  (list fpoly)
    ?@  noun
      %+  reap  mult
      %-  lift-to-fpoly
      ~[0 noun 0 1 0 0 0 0 0 0 1 (bdiv 3 2)]
    =/  dyk  (dyck:shape noun)
    =/  lef  (stretch dyk (leaf-sequence:shape noun))
    =/  len-dyk  (lent dyk)
    =-  %+  weld  (flop rows)
        %+  turn  (flop (range mult))
        |=  i=belt
        %-  lift-to-fpoly
        ~[0 0 0 1 0 0 0 i ?:(=(i 0) 0 (binv i)) ?:(=(i 0) 0 1) 0 len-dyk]
    %^  zip-roll  (flop (range 1 +(len-dyk)))  (zip-up dyk lef)
    |=  [[rem=belt d=belt l=belt] [ct=@ len=_1 rows=(list fpoly)]]
    =/  new-ct  (badd ct (bsub 1 (bmul 2 d)))
    =/  new-len  (badd len (binv 2))
    :+  new-ct
      new-len
    :_  rows
    %-  lift-to-fpoly
    :~  d  l
        new-ct  (binv (badd new-ct 1))
        rem  (binv rem)  1
        mult  (binv mult)  1
        0
        new-len
    ==
  ::
  ++  funcs
    ^-  table-funcs
    |%
    ++  terminal
      |=  =table
      ^-  felt
      ~(rear fop (rear p.table))
    ::
    ++  pad
      |=  [rows=(list fpoly) height=@]
      ^-  (list fpoly)
      =/  diff  (sub height (lent rows))
      ?:  =(diff 0)  rows
      %+  weld  rows
      %+  turn  (range diff)
      |=  i=@
      %-  lift-to-fpoly
      :~  0  0
          (badd i 1)  (binv (badd i 2))
          (bsub diff i)  (binv (bsub diff i))  1
          1  1  1
          0
          (badd 1 (bmul (binv 2) (badd i 1)))
      ==
    ::
    ++  extend
      ::  new columns: [row inn out]
      |=  [=table challenges=(list felt) initials=(list felt) =return:fock]
      ^-  ^table
      :-  [p (lent base-variables) (lent variable-labels) num-randomizers]
      =/  r   ~(r rnd (make-challenge-map challenges %noun))
      =/  [a=felt b=felt c=felt p=felt q=felt r=felt s=felt t=felt alf=felt bet=felt]
        :*  (r %a)  (r %b)  (r %c)
            (r %p)  (r %q)  (r %r)  (r %s)  (r %t)
            (r %alf)  (r %bet)
        ==
      =/  noun-mult
        %~  tap  by
        %-  (~(uno by subjects.return) formulas.return)
        |=  [* mult-s=@ mult-f=@]  (add mult-s mult-f)
      =/  mset=multiset  (init-multiset:util bet)
      =-  %-  zip
          :-  p.table
          :_  roweld
          %+  weld  rows
          %+  reap  (sub (lent p.table) (lent rows))
          %-  init-fpoly
          ~[(lift 0) (lift 0) dat.mset]
      %+  roll  noun-mult
      |=  [[noun=* mult=@] [mset=_mset rows=(list fpoly)]]
      ?@  noun
        =-  [mset (weld ^rows (flop rows))]
        %+  roll  (range mult)
        |=  [i=belt [mset=_mset rows=(list fpoly)]]
        =/  new-mset
          %-  ~(mult mset:util mset)
          (~(compress tuple ~[a b c]) ~[(lift 1) (lift 0) (lift noun)])
        :-  new-mset
        :_  rows
        %-  init-fpoly
        ~[(lift 0) (lift noun) dat.new-mset]
      =/  len  (num-of-leaves:shape noun)
      =/  ds-series  (dyck-stack-timeseries (dyck:shape noun) alf)
      =/  ls-series
      %-  stretched-leaf-stack-timeseries
      :_  alf
      (stretch (dyck:shape noun) (leaf-sequence:shape noun))
      =/  ds  (rear ds-series)
      =/  ls  (rear ls-series)
      =-  =/  new-mset
            %-  ~(mult mset:util mset)
            (~(compress tuple ~[a b c]) ~[(lift len) ds ls])
          :-  new-mset
          %-  zing
          :~  ^rows
            ::
              (flop rows)
            ::
              %+  reap  mult
              %-  init-fpoly
              ~[ds ls dat.new-mset]
          ==
      %+  roll  (zip ds-series ls-series same)
      |=  [[ds=felt ls=felt] [mset=_mset rows=(list fpoly)]]
      :-  mset
      :_  rows
      %-  init-fpoly
      ~[ds ls dat.mset]
    ::
    ++  boundary-constraints
      |=  challenges=(list felt)
      ^-  (list multi-poly)
      =/  r   ~(r rnd (make-challenge-map challenges %decoder))
      =/  [a=felt b=felt c=felt p=felt q=felt r=felt s=felt t=felt alf=felt bet=felt]
        :*  (r %a)  (r %b)  (r %c)
            (r %p)  (r %q)  (r %r)  (r %s)  (r %t)
            (r %alf)  (r %bet)
        ==
      :~  ::
            (v %dyck)
          ::
            (v %ct)
          ::
            (mpsub (mpadd (v %usesf) (v %triv)) one)
          ::
            (mpsub (mpadd (v %remf) (v %triv)) one)
          ::
            (mpsub (mpscal (lift 2) (v %len)) (mp-c (lift 3)))
          ::
            (v %dyck-stack)
          ::
            (v %leaf-stack)
          ::
          ::  mset may be pre-loaded
          ::
          ::    mset - [(1-triv) + triv•(bet-(a+c*leaf))]
            %+  mpsub  (v %mset)
            %+  mpadd  (mpsub one (v %triv))
            %+  mpmul  (v %triv)
            %+  mpsub  (mp-c bet)
            (mpadd (mp-c a) (mpscal c (v %leaf)))
      ==
    ::
    ++  transition-constraints
      |=  [challenges=(list felt) =jet-map:jet]
      ^-  (map term multi-poly)
      %-  ~(gas by *(map term multi-poly))
      %+  turn  (unlabeled-transition-constraints challenges return)
      |=  mp=multi-poly
      [%no-name mp]
    ::
    ++  unlabeled-transition-constraints
      |=  [challenges=(list felt) =jet-map:jet]
      ^-  (list multi-poly)
      =/  r   ~(r rnd (make-challenge-map challenges %decoder))
      =/  [a=felt b=felt c=felt p=felt q=felt r=felt s=felt t=felt alf=felt bet=felt]
        :*  (r %a)  (r %b)  (r %c)
            (r %p)  (r %q)  (r %r)  (r %s)  (r %t)
            (r %alf)  (r %bet)
        ==
      :~  ::  dyck is binary: dyck(1-dyck)
            (mpmul (v %dyck) (mpsub one (v %dyck)))
          ::
          ::  triv is binary
            (mpmul (v %triv) (mpsub one (v %triv)))
          ::
          ::  ct+1 and succit are inverse
          ::
          ::    This ensures that ct never hits 0.
          ::
          ::    (ct+1)•succit
            (mpmul (mpadd (v %ct) one) (v %succit))
          ::
          ::  ct=0 at the end of a dyck word
          ::
          ::    The end of a dyck word occurs when remf=1 and remf'=0.
          ::
          ::    remf•(1-remf')•ct
            :(mpmul (v %remf) (mpsub one (v %remf-n)) (v %ct))
          ::
          ::  if triv=1, then rem and uses =0
            (mpmul (v %triv) (v %rem))
          ::
            (mpmul (v %triv) (v %uses))
          ::
          ::  if there are characters remaining in a dyck word (remf=1), then uses =! 0;
          ::  contrapositively, uses=0 imples remf=0
            (mpmul (v %remf) (mpsub one (v %usesf)))
          ::
          ::  when we're out of dyck characters (remf=0), fill in the rest with 1;
          ::  not arbitrary, necessary for correct leaf accumulation
            (mpmul (mpsub one (v %remf)) (mpsub one (v %dyck)))
          ::
          ::  evolution of triv
          ::
          ::    While uses =! 0, triv stays constant.
          ::
          ::    usesf•(triv'-triv)
            (mpmul (v %usesf) (mpsub (v %triv-n) (v %triv)))
          ::
          ::  evolution of rem
          ::
          ::    Basically, rem decrements while it can and then stays constant
          ::    until uses finishes decrementing, then it can "jump" to a new start value.
          ::    If uses=0, the constraint is "off" since uses=0 => remf=0.
          ::    (Though see next constraint for qualification.)
          ::    If uses =! 0, then rem decrements or is 0 according to remf=1 or 0.
          ::
          ::    usesf•rem' - remf•(rem-1)
            %+  mpsub
              (mpmul (v %usesf) (v %rem-n))
            (mpmul (v %remf) (mpsub (v %rem) one))
          ::
          ::  rem starts =! 0 for nontrivial dyck words, = 0 for trivial ones
          ::
          ::    (1-usesf)•(remf' - (1 - triv'))
            %+  mpmul
              (mpsub one (v %usesf))
            %+  mpsub  (v %remf-n)
            (mpsub one (v %triv-n))
          ::
          ::  evolution of uses
          ::
          ::    Basically, uses stays constant while rem decrements, decrements for
          ::    the first time as rem decrements to 0, then decrements to 0, then can "jump".
          ::    If uses=0, the constraint is off, allowing a jump. Otherwise, depending on
          ::    whether the next value of rem is 0 or not, it decrements or stays constant.
          ::
          ::    usesf•[uses' - (remf'•uses + (1-remf')•(uses-1))]
            %+  mpmul  (v %usesf)
            %+  mpsub  (v %uses-n)
            %+  mpadd
              (mpmul (v %remf-n) (v %uses))
            (mpmul (mpsub one (v %remf-n)) (mpsub (v %uses) one))
          ::
          ::  uses starts =! 0 for nontrivial dyck words, = 0 for trivial ones
          ::
          ::    (1-usesf)•(usesf' - (1 - triv'))
            %+  mpmul
              (mpsub one (v %usesf))
            %+  mpsub  (v %usesf-n)
            (mpsub one (v %triv-n))
          ::
          ::  evolution of count
          ::
          ::    ct' - remf'•(ct + (1-2•dyck))
            %+  mpsub  (v %ct-n)
            %+  mpmul  (v %remf-n)
            (mpadd (v %ct) (mpsub one (mpscal (lift 2) (v %dyck))))
          ::
          ::  evolution of len
          ::
          ::    2*len' - [remf'•(2*len + 1) + (1-remf')[usesf•2*len + (1-usesf)•3]]
            %+  mpsub  (mpscal (lift 2) (v %len-n))
            %+  mpadd
              (mpmul (v %remf-n) (mpadd (mpscal (lift 2) (v %len)) one))
            %+  mpmul  (mpsub one (v %remf-n))
            %+  mpadd
              (mpmul (v %usesf) (mpscal (lift 2) (v %len)))
            (mpmul (mpsub one (v %usesf)) (mpscal (lift 3) one))
          ::
          ::  evolution of dyck-stack
          ::
          ::    dyck-stack' - [remf•(dyck-stack*alf + dyck)
          ::                  + (1-remf)[(1-usesf) + usesf•dyck-stack] ]
            %+  mpsub  (v %dyck-stack-n)
            %+  mpadd
              %+  mpmul  (v %remf)
              (mpadd (mpscal alf (v %dyck-stack)) (v %dyck))
            %+  mpmul  (mpsub one (v %remf))
            %+  mpadd  (mpsub one (v %usesf))
            (mpmul (v %usesf) (v %dyck-stack))
          ::
          ::  evolution of leaf-stack
          ::
          ::    leaf-stack' -
          ::      [(1-remf)•[(1-usesf) + usesf•leaf-stack] +
          ::       remf•[(1-dyck')•leaf-stack + dyck'(leaf-stack*alf + leaf)] ]
            %+  mpsub  (v %leaf-stack-n)
            %+  mpadd
              %+  mpmul  (mpsub one (v %remf))
              %+  mpadd  (mpsub one (v %usesf))
              (mpmul (v %usesf) (v %leaf-stack))
            %+  mpmul  (v %remf)
            %+  mpadd
              (mpmul (mpsub one (v %dyck-n)) (v %leaf-stack))
            (mpmul (v %dyck-n) (mpadd (mpscal alf (v %leaf-stack)) (v %leaf)))
          ::
          ::  evolution of mset
          ::
          ::    mset' -
          ::      triv'•[(bet-(a+c*leaf'))•mset]
          ::        + (1-triv')•[rem'•mset + (1-rem')(bet-(a*len'+b*dyck-stack'+c*leaf-stack'))•mset]
            %+  mpsub  (v %mset)
            %+  mpadd
              %+  mpmul  (v %triv-n)
              %+  mpmul  (v %mset)
              %+  mpsub  (mp-c bet)
              (mpadd (mp-c a) (mpscal c (v %leaf-n)))
            %+  mpmul  (mpsub one (v %triv-n))
            %+  mpadd  (mpmul (v %rem-n) (v %mset))
            ;:    mpmul
                (mpsub one (v %rem-n))
              ::
                (v %mset)
              ::
                %+  mpsub  (mp-c bet)
                ;:  mpadd
                  (mpscal a (v %len-n))
                  (mpscal b (v %dyck-stack-n))
                  (mpscal c (v %leaf-stack-n))
                ==
            ==
      ==
    ::
    ++  terminal-constraints
      |=  [challenges=(list felt) terminals=(list felt)]
      ^-  (list multi-poly)
      :~  ::  dyck is binary: dyck(1-dyck)
            (mpmul (v %dyck) (mpsub one (v %dyck)))
          ::
          ::  triv is binary
            (mpmul (v %triv) (mpsub one (v %triv)))
          ::
          ::  ct+1 and succit are inverse
          ::
          ::    This ensures that ct never hits 0.
          ::
          ::    (ct+1)•succit
            (mpmul (mpadd (v %ct) one) (v %succit))
          ::
          ::  if triv=1, then rem and uses =0
            (mpmul (v %triv) (v %rem))
          ::
            (mpmul (v %triv) (v %uses))
          ::
          ::  if there are characters remaining in a dyck word (remf=1), then uses =! 0;
          ::  contrapositively, uses=0 imples remf=0
            (mpmul (v %remf) (mpsub one (v %usesf)))
          ::
          ::  when we're out of dyck characters (remf=0), fill in the rest with 1;
          ::  not arbitrary, necessary for correct leaf accumulation
            (mpmul (mpsub one (v %remf)) (mpsub one (v %dyck)))
      ==
    --
  --
--
