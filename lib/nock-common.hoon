:: nock-common: common arms between nock-prover and nock-verifier
/+  table,
    zero-table=table-verifier-zero,
    stack-table=table-verifier-stack,
    jet-table=table-verifier-jet
    ::noun-table=table-verifier-noun
|%
::  all values in this table must generally be in the order of the tables
::  specified in the following arm.
++  static-table-names
  ^-  (list term)
  :~  %nockzs
      %stack
      :: %noun
  ==
::
++  dynamic-table-names
  ^-  (list term)
  ~[%jet]
::
++  table-names
  ^-  (list term)
  (weld static-table-names dynamic-table-names)
::
::  Widths of static tables. Dynamic tables (ie jet) need to be computed separately and passed
::  in specific data needed for each table.
++  table-base-widths-static
  ^-  (list @)
  :~  8   :: nockzs
      20   :: stack
  ==
::
++  table-full-widths-static
  ^-  (list @)
  :~  32  :: nockzs
      33  :: stack
  ==
::
++  all-verifier-funcs
  ^-  (list verifier-funcs:table)
  :~  funcs:nockzs:zero-table
      funcs:stack:stack-table
      funcs:jet:jet-table
      ::funcs:noun:noun-table
  ==
--
