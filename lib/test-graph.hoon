/+  *table, *goldilocks, common=table-stack, *table-util, terminal, *jet
::/+  *table, *fock, *table-util, common=table-stack, terminal, *jet
=,  f
=,  mp-to-graph
|%
++  v  ~(v var variables:common)
++  one  (mp-c (lift 1))
++  test
  |=  n=@
  =/  m=mp-graph  (mp-c (lift 4))
  =/  z=multi-poly  (^mp-c (lift 4))
  =/  d=mp-graph  (mpmul (v %hello) (mpsub one (v %blah)))
  n
--
