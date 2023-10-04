/-  field
/+  *goldilocks
=,  f
=,  mp-to-graph
::
|%
++  gen-consistency-checks
  ::  the purpose of this arm is to assist with validating the terminals map in sample of terminal-constraints
  ::
  ::  the terminals map is out-of-band data, i.e., it is not constrained and is to be considered untrusted
  ::        thus, we need to manually ensure, per table, that all values in the inner map are correct.
  ::  we also need to assert that the list of column names (inner map's keys) are a (non-strict) subset
  ::  of the full column names of the table
  ::  we will generate equality constraints for each
  ::
  ::  extraneous-columns := terminal-columns - all-columns
  ::
  |=  [our-terminals=(map term felt) our-columns=(list term) v=$-(@tas mp-graph)]
  ^-  (list mp-graph)
  =/  terminal-columns    ~(key by our-terminals)
  =/  all-columns         (~(gas in *(set term)) our-columns)
  =/  extraneous-columns  (~(dif in terminal-columns) all-columns)
  ?>  =(~ extraneous-columns)
  %+  turn  ~(tap in terminal-columns)
  |=  col=@tas
  ^-  mp-graph
  =/  term-val  (~(got by our-terminals) col)
  ::  terminal constraint:
  ::
  ::  <col> = <terminal-val>,
  ::  <col> - <terminal-val> = 0
  ::    for all col in table columns names
  ::    for all terminal-val in claimed terminal values received OOB for this table
  ::
  (mpsub (v col) (mp-c term-val))
--
