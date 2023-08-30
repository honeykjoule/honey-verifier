::  challenges.hoon
::
/+  goldilocks
=,  f:goldilocks
|%
++  shared-chal-names
  ^-  (set term)
  %-  silt
  ^-  (list term)
  :~  %a    ::  tuple packing, tree-data
      %b
      %c
      %p    ::  tuple packing, formula decoder
      %q
      %r
      %s
      %t
      %u
      %alf  ::  stack
      %bet  ::  multiset
  ==
::  no local randomness for now, but we are keeping the code
++  all-local-names
  ^-  (map term (set term))
  %-  molt
  ^-  (list [term (set term)])
  :~  [%subtree ~]
      [%nockzs ~]
      [%decoder ~]
      [%stack ~]
      [%noun ~]
      [%jet ~]
  ==
::  num-random-chals: the max of the num of local chals required across all tables
::
++  num-shared-chals  ~(wyt in shared-chal-names)
++  num-random-chals  (roll (turn ~(val by all-local-names) lent) max)
++  num-total-chals   (add num-shared-chals num-random-chals)
::
::
++  rnd
  |_  challenges=(map term felt)
  ++  r
    |=  nam=term
    ^-  felt
    ~+((~(got by challenges) nam))
  --
::
++  make-challenge-map
  |=  [raw-chals=(list felt) table-name=term]
  ^-  (map term felt)
  =/  local-names       (~(got by all-local-names) table-name)
  ~|  "make sure that you are passing in the right number of raw challenges, especially in your test arm"
  ?>  (gte (lent raw-chals) num-total-chals)  ::  ensure we have enough random values
  ~|  "and make sure that there are no conflicts between shared and local names"
  ?>  =(~ (~(int in shared-chal-names) local-names))  :: local names should not conflict with shared names
  ::
  =/  shared-raw-chals  (scag num-shared-chals raw-chals)
  =/  shared-chals      (make-shared-challenges raw-chals)
  ::  make local challenges map
  =/  local-raw-chals   (slag num-shared-chals raw-chals)
  =/  local-chals       (zip-chals local-names local-raw-chals)
  ::  combine local-challenges
  (~(uni by local-chals) shared-chals)
::
++  make-shared-challenges
  |=  raw-chals=(list felt)
  ::  even though shared challenges should only be computed once,
  ::  +make-challenges is called once per table in practice
  ::  and thus so is this. hopefully ~+ handles that
  ~+((zip-chals shared-chal-names raw-chals))
::
++  zip-chals
  |=  [names=(set term) raw-chals=(list felt)]
  (~(gas by *(map term felt)) (zip ~(tap in names) raw-chals same))
--
