/+  *list, *goldilocks, fock, jet, table-util, *challenges
~%  %table-top  ..part  ~
|%
::  TODO it may be more appropriate to completely split the constraints into verifier-funcs
::  and not include them in table-funcs at all to avoid duplication elsewhere.
::  prover-funcs : verifier-funcs :: table-funcs : constraint-funcs
::
++  table-funcs
  ::  TODO need to add arm for build=$-(return:fock table) below
  $+  table-funcs
  $_  ^|
  |%
  ::
  ::  pad: include extra rows until their number equals height (the next power of two)
  ::
  ++  pad
    |~  [rows=(list fpoly:f) height=@]
    *(list fpoly:f)
  ::
  ::  extend: augment the table with extra columns, using verifier provided randomness
  ::
  ++  extend
    |~  [=table challenges=(list felt:f) initials=(list felt:f) =return:fock]
    *^table
  ::
  ::  terminal: produce a map of felts sourced from the final row of the built and extended table
  ::
  ::            The output of this is made available to other tables in the terminal-constraints
  ::            arm, where tables can specify constraints to interrelate columns by
  ::            e.g. forcing terminal values of a multiset to be equal.
  ::
  ++  terminal
    |~  =table
    *(map term felt:f)
  ::
  ++  boundary-constraints    boundary-constraints:*verifier-funcs
  ++  transition-constraints  transition-constraints:*verifier-funcs
  ++  terminal-constraints    terminal-constraints:*verifier-funcs
  --
::
++  verifier-funcs
  ::  the verifier interface is a strict subset of the prover interface because verify:nock-verifier only uses constraints
  $+  verifier-funcs
  $_  ^|
  |%
  ++  boundary-constraints
    |~  challenges=(list felt:f)
    *(list mp-graph:f)
  ::
  ++  transition-constraints
    |~  [challenges=(list felt:f) =jet-map:jet]
    *(map term mp-graph:f)
  ::
  ++  terminal-constraints
    ::
    ::  challenges: list verifier provided randomness
    ::
    ::  terminals: double map of table-name and terminal-name to terminal-value.
    ::             this is the primary mechanism to interrelate tables
    ::             table-name -> terminal-name -> terminal-value
    ::  TODO use mip
    ::
    |~  [challenges=(list felt:f) terminals=(map term (map term felt:f))]
    *(list mp-graph:f)
  --
::  TODO make some of these functions a door
++  table-to-verifier-funcs
  ::  this arm is theoretically a temporary shim to assist the separation of the codebase
  ::  ideally this disappears after sufficient surgery but may be here to stay
  |=  fs=table-funcs
  ::~&  >>  "table-to-verifier-funcs was called; this should only be visible in prover-side code"
  ^-  verifier-funcs
  |%
  ++  boundary-constraints    boundary-constraints:fs
  ++  transition-constraints  transition-constraints:fs
  ++  terminal-constraints    terminal-constraints:fs
  --
++  wrap-verifier-funcs
  ::  Produces a new table-funcs that includes additional constraints;
  ::  useful for injecting dynamic constraints.
  |=  [old=verifier-funcs bound=(list mp-graph:f) term=(list mp-graph:f)]
  ^-  verifier-funcs
  ::
  ::  Note: it's not possible to construct cores inline somewhere else and have them be the same type,
  ::  because a core's type actually implicitly includes its subject/context. So typecasting will fail,
  ::  and ;;'ing an inline core spuriously succeeds but produces a "bunted" core which is plain wrong.
  ::  However, it can work if you construct and ^- the core right where the type-def is defined,
  ::  which is why this arm *must* be in this file since $table-funcs is defined here as well.
  ::
  ::  If this feels bad just close your eyes and pretend that `table-funcs` is a rust trait
  ::  and that this is the `new` method in an impl block lololol
  ::
  ::  Note: producing new cores inline is probably a terrible idea and likely defeats numerous attempts at performance
  ::        in the runtime. On the bright side, this is great fodder for testing how far ares can go.
  |%
  ++  boundary-constraints
    |=  challenges=(list felt:f)
    ^-  (list mp-graph:f)
    (weld bound (boundary-constraints:old challenges))
  ++  transition-constraints            transition-constraints:old
  ++  terminal-constraints
    |=  [challenges=(list felt:f) terminals=(map ^term (map ^term felt:f))]
    ^-  (list mp-graph:f)
    (weld term (terminal-constraints:old challenges terminals))
  --
++  replace-vrf-funcs
  |=  [old=table-funcs new-vrf=verifier-funcs]
  ^-  table-funcs
  |%
  ++  pad       pad:old
  ++  extend    extend:old
  ++  terminal  terminal:old
  ++  boundary-constraints    boundary-constraints:new-vrf
  ++  transition-constraints  transition-constraints:new-vrf
  ++  terminal-constraints    terminal-constraints:new-vrf
  --
::
::  Note: in our system, a row in a matrix is not a list of base elements
::  (representing the state of the computation at each step), but rather
::  a list of those base elements *lifted* into extension field elements.
::
::  Thus, fpoly is being used to represent a generic list of felts
::  not any specific polynomial with felt coefficients.
::
+$  matrix  (list fpoly:f)
::
+$  table  [[field=@ base-width=@ full-width=@ num-randomizers=@] p=matrix]
::
::
::  TODO the following 2 arms could go into the tab door and be renamed shorter
++  belt2d-to-matrix
  |=  btable=(list (list belt:f))
  ^-  matrix
  (turn btable lift-to-fpoly:f)
++  matrix-to-belt2d
  |=  mat=matrix
  ^-  (list (list))
  (turn mat row-to-belts)
::
++  row-to-belts
  |=  row=fpoly:f
  ^-  (list)
  (turn ~(to-poly fop:f row) drop:f)
::
::  var: helper door. allows for terse `(v %idx)` style variable accesses
::       after initializing with a variables map
++  var
  |_  variables=(map term mp-graph:f)
  ++  v
    |=  nam=term
    ^-  mp-graph:f
    ~+
    ~|  var-not-found+nam
    (~(got by variables) nam)
  --
::
::  make-vars: given a list of variable names (i.e., column names),
::             produce a map from variable names to corresponding mp-graph
++  make-vars
  |=  [var-names=(list term)]
  |^  ^-  (map term mp-graph:f)
  ::
  ::  Equivalent to:
  ::
  ::  %-  ~(gas by (map term mp-graph:f))
  ::  :~  [%idx (make-variable 0)]
  ::      [%a (make-variable 1)]
  ::      ...
  ::      [%a-n (make-variable 2*n)]
  ::  ==
  ::
  =/  num-succ  1
  ::  is the number of successors to generate
  ::  hardcoded to 1 because that is all the current stark impl supports
  ::  i.e., cannot have constraints of the form idx'' = idx' + 1
  ::
  =/  successor-names=(list term)
    ::  flat list of succesors ~[%idx-n %a-n %idx-n-n %a-n-n]
    %-  zing
    ^-  (list (list term))
    ::  list of ith successors idents for all i
    ::  e.g. ~[[%idx-n %a-n] ~[%idx-n-n %a-n-n]]
    %+  turn  (gulf 1 num-succ)
    |=  succ-num=@
    :: a list of all ith successor idents e.g. ~[%idx-n %a-n]
    (turn var-names |=(nam=term `@tas`(successor-name nam succ-num)))
  ::
  =/  vars-all  (weld var-names successor-names)
  ::  produce the final map of all var-names to mp-graphs
  %-  ~(gas by *(map term mp-graph:f))
  %^  zip  (range 0 (lent vars-all))  vars-all
  |=  [i=@ var=term]
  [var (make-variable:mp-to-graph:f i)]
  ::
  ++  successor-name
    |=  [nam=term n=@]
    ^-  term
    ::  example: when n=2, idx -> xdi -> -n-nxdi -> idx-n-n
    ::  idk why it works but it does lol
    (crip (flop (runt [n '-n'] (flop (trip nam)))))
  --
::
++  weighted-sum
  |=  [row=fpoly:f weights=fpoly:f]
  ^-  felt:f
  ?>  =(len.row len.weights)
  %+  roll
    ~(to-poly fop:f (~(zip fop:f row) weights fmul:f))
  fadd:f
::
++  static-interpolant-degree-bound
  |=  [height=@ num-randomizers=@]
  (dec (add height num-randomizers))
::
++  static-unit-distance
  |=  [domain-len=@ height=@]
  ^-  @
  ?:  =(height 0)
    0
  (div domain-len height)
::
++  tab
  =,  f
  |_  =table
  ++  typ     [field base-width full-width num-randomizers]:table
  ::
  ::  height: target padding height for given table
  ::          defined to be the next smallest power of 2
  ::          e.g. if (lent p.table) == 5, ~(height tab table) == 8
  ++  height
    ^-  @
    ~+
    =/  len  (lent p.table)
    ?:  =(len 0)  0
    (bex (xeb (dec len)))
  ::
  ++  omicron
    ::  TODO:  specialized for 2^64 - 2^32 + 1
    ~+((ordered-root height))
  ::
  ++  omicron-domain
    ^-  (list felt)
    ~+
    %+  turn  (range height)
    |=  i=@
    (lift (bpow omicron i))
  ::
  ++  interpolation-domain-length  (add height num-randomizers.table)
  ::
  ::  a more faithful name would be interpolant-degree-bound...
  ::  e.g. interpolating 3 points doesn't necessarily lead to a quadratic polynomial
  ++  interpolant-degree-bound     (dec interpolation-domain-length)
  ::
  ++  interpolate-columns
    |=  [omega=belt order=@ first-col=@ last-col=@ eny=@]
    ^-  (list fpoly)
    ?>  =(1 (bpow omega order))
    ?>  !=(1 (bpow omega (div order 2)))
    ?:  =(height 0)
      (reap (sub last-col first-col) zero-fpoly)
    =/  domain=fpoly
      (init-fpoly omicron-domain)
    (interpolate-table p.table height first-col last-col domain)
  ::
  ++  unit-distance
    |=  domain-len=@
    ^-  @
    ?:  =(height 0)
      0
    (div domain-len height)
  ::
  ++  lde-interpolate
    |=  [domain=fpoly omega=belt length=@ eny=@]
    ^-  (pair @ (list fpoly))
    :-  base-width.table
    (interpolate-columns omega length 0 (dec base-width.table) eny)
  ::
  ++  ldex-interpolate
    |=  [domain=fpoly omega=belt length=@ eny=@]
    ^-  (pair @ (list fpoly))
    :-  (sub full-width:table base-width:table)
    (interpolate-columns omega length base-width:table (dec full-width:table) eny)
  ::
  ++  all-quotients
    |=  $:  domain=(list @)
            codewords=(list fpoly)
            challenges=(list @)
            terminals=(map term (map term felt:f))
            funcs=verifier-funcs
            zerofiers=(unit [boundary=fpoly:f transition=fpoly:f terminal=fpoly:f])
            =jet-map:jet
        ==
    |^  ^-  (list fpoly)
    :~  boundary-quotients
        transition-quotients
        terminal-quotients
    ==
    ::
    ++  boundary-quotients
      ^-  fpoly
      =/  boundary-constraints  (boundary-constraints:funcs challenges)
      =/  boundary-zerofier-inverse
        ?^  zerofiers
          boundary.u.zerofiers
        %-  init-fpoly
        %-  mass-inversion
        %+  turn  domain
        |=(a=felt (fsub a (lift 1)))
      =/  gam  (~(r rnd (make-shared-challenges challenges)) %gam)
      =/  points=(list fpoly)
        (zipped-points-from-codewords domain codewords)
      (combine-constraints-and-eval boundary-constraints boundary-zerofier-inverse points gam)
    ::
    ++  transition-quotients
      ^-  fpoly
      ?<  =(height 0)
      =/  zerofier-inverse=fpoly
        ?^  zerofiers
          transition.u.zerofiers
        %-  init-fpoly
        %^    zip
            %+  turn  domain
            |=  d=felt
            (fsub d (finv (lift omicron)))
          %-  mass-inversion
          %+  turn  domain
          |=  d=felt
          (fsub (fpow d height) (lift 1))
        fmul
      =/  unit-dist  (unit-distance (lent domain))
      =/  transition-constraints
        (unlabel-constraints:table-util (transition-constraints:funcs challenges jet-map))
      =/  gam  (~(r rnd (make-shared-challenges challenges)) %gam)
      =/  points=(list fpoly)
        (zipped-point-pairs-from-codewords domain codewords unit-dist)
      (combine-constraints-and-eval transition-constraints zerofier-inverse points gam)
    ::
    ++  terminal-quotients
      ^-  fpoly
      =/  terminal-constraints
        (terminal-constraints:funcs challenges terminals)
      =/  zerofier-inverse
        ?^  zerofiers
          terminal.u.zerofiers
        %-  init-fpoly
        %-  mass-inversion
        %+  turn  domain
        |=  a=felt
        (fsub a (finv (lift omicron)))
      =/  points=(list fpoly)
        (zipped-points-from-codewords domain codewords)
      =/  gam  (~(r rnd (make-shared-challenges challenges)) %gam)
      (combine-constraints-and-eval terminal-constraints zerofier-inverse points gam)
    --
  ::
  ++  all-quotient-degree-bounds
    |=  $:  challenges=(list @)
            terminals=(map term (map term felt:f))
            height=@
            funcs=verifier-funcs
            =jet-map:jet
        ==
    ^-  (list @)
    :~  (boundary-quotient-degree-bounds +<)
        (transition-quotient-degree-bounds +<)
        (terminal-quotient-degree-bounds +<)
    ==
  ::
  ++  boundary-quotient-degree-bounds
    |=  $:  challenges=(list @)
            terminals=(map term (map term felt:f))
            height=@
            funcs=verifier-funcs
            =jet-map:jet
        ==
    ^-  @
    =/  boundary-constraints  (boundary-constraints:funcs challenges)
    =/  max-degrees=(list @)
      (reap full-width.table (static-interpolant-degree-bound height num-randomizers.table))
    %+  roll  boundary-constraints
    |=  [constraint=mp-graph acc=_1]
    %+  max  acc
    (dec (max (substitution-degree-bound constraint max-degrees) 1))
  ::
  ++  transition-quotient-degree-bounds
    |=  $:  challenges=(list @)
            terminals=(map term (map term felt:f))
            height=@
            funcs=verifier-funcs
            =jet-map:jet
        ==
    ^-  @
    =/  transition-constraints
      %-  unlabel-constraints:table-util
      (transition-constraints:funcs challenges jet-map)
    =/  max-degrees=(list @)
      (reap (mul 2 full-width.table) (static-interpolant-degree-bound height num-randomizers.table))
    %+  roll  transition-constraints
    |=  [constraint=mp-graph acc=_1]
    %+  max  acc
    .+((sub (substitution-degree-bound constraint max-degrees) height))
  ::
  ++  terminal-quotient-degree-bounds
    |=  $:  challenges=(list @)
            terminals=(map term (map term felt:f))
            height=@
            funcs=verifier-funcs
            =jet-map:jet
        ==
    ^-  @
    =/  terminal-constraints  (terminal-constraints:funcs challenges terminals)
    =/  max-degrees=(list @)
      (reap full-width.table (static-interpolant-degree-bound height num-randomizers.table))
    %+  roll  terminal-constraints
    |=  [constraint=mp-graph acc=_1]
    %+  max  acc
    (dec (max (substitution-degree-bound constraint max-degrees) 1))
  ::
  ++  num-quotients
    |=  $:  challenges=(list @)
            terminals=(map term (map term felt:f))
            height=@
            funcs=verifier-funcs
            =jet-map:jet
        ==
    ^-  @
    (lent (all-quotient-degree-bounds +<))
  ::
  ++  col
    |=  n=@
    ^-  fpoly
    %+  roll  p.table
    |:  [row=`fpoly`zero-fpoly vec=`fpoly`[0 0x1]]
    (~(snoc fop vec) (~(snag fop row) n))
  ::
  ++  compress
    |=  weights=fpoly
    ^-  ^table
    :-  [field.table 1 1 num-randomizers.table]
    %+  turn  p.table
    |=  row=fpoly
    ^-  fpoly
    1^(weighted-sum row weights)
  ::
  ++  test
    |=  $:  challenges=(list @)
            terminals=(map term (map term felt:f))
            funcs=verifier-funcs
            =jet-map:jet
        ==
    ::  TODO funcs is unused. we should handle extending and padding in here
    ::
    ::  TODO maybe add a should-fail flag that silences failed constraints or modifies printf
    ::       or change signature to surface error unit?
    |^  ^-  ?
    =/  boundary-constraints-labeled
      (labeled-constraints (boundary-constraints:funcs challenges) "boundary-")
    =/  bound-fail  (run-bounds boundary-constraints-labeled)
    ?.  ?=(~ bound-fail)
      ~&((need bound-fail) %.n)
    =/  terminal-constraints-labeled
      (labeled-constraints (terminal-constraints:funcs challenges terminals) "terminal-")
    =/  term-fail  (run-terms terminal-constraints-labeled)
    ?.  ?=(~ term-fail)
      ~&((need term-fail) %.n)
    ?:  =((lent p.table) 0)
      %.n
    ?:  =((lent p.table) 1)
      %.y  ::  1 row table automatically passes transition constraints
    =/  trans-fail  (run-trans (transition-constraints:funcs challenges jet-map))
    ?.  ?=(~ trans-fail)
      ~&((need trans-fail) %.n)
    %.y
    ::
    ++  run-bounds
      |=  boundary-constraints-labeled=(map @tas mp-graph)
      %+  mevy  ~(tap by boundary-constraints-labeled)
      |=  [name=@tas constraint=mp-graph]
      =/  point  (snag 0 p.table)
      =/  eval  (mpeval-graph constraint point)
      ?:  =((lift 0) eval)  ~
      %-  some
      :*  %constraint-failed
          name=name
          row=(row-to-belts point)
          result=(drop eval)
      ==
    ::
    ++  run-terms
      |=  terminal-constraints-labeled=(map @tas mp-graph)
      %+  mevy  ~(tap by terminal-constraints-labeled)
      |=  [name=@tas constraint=mp-graph]
      =/  point  (rear p.table)
      =/  eval  (mpeval-graph constraint point)
      ?:  =((lift 0) eval)  ~
      %-  some
      :*  %constraint-failed
          name=name
          row=(row-to-belts point)
          result=(drop eval)
      ==
    ::
    ++  run-trans
      |=  transition-constraints-labeled=(map @tas mp-graph)
      ::  produces ~ if all constraints pass on all points
      ::  and [~ err] on first error
      %+  mevy  ~(tap by transition-constraints-labeled)
      ::  following gate produces ~ if given constraint passes on all points
      ::  and [~ err] on first error
      |=  [name=@tas constraint=mp-graph]
      %+  mevy  (range (dec (lent p.table)))
      |=  i=@
      =/  point       (snag i p.table)
      =/  next-point  (snag +(i) p.table)
      =/  combo-point  (~(weld fop point) next-point)
      =/  eval  (mpeval-graph constraint combo-point)
      ?:  =((lift 0) eval)  ~
      %-  some
      :*  %constraint-failed
          name=name
          row-num=i
          row=(row-to-belts point)
          next-row=(row-to-belts next-point)
          result=(drop eval)
      ==
    ::
    ++  labeled-constraints
      |=  [constraints=(list mp-graph) prefix=tape]
      =/  len  (lent constraints)
      %-  ~(gas by *(map @tas mp-graph))
      (zip (make-labels prefix len) constraints same)
    ::
    ++  make-labels
      |=  [prefix=tape n=@]
      ^-  (list @t)
      ?:  =(n 0)  ~
      %+  turn  (range 1 (add 1 n))
      |=  i=@
      ^-  term
      (crip (welp prefix (scot %ud i)^~))
    --
  --
--
