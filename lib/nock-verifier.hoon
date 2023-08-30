/+  *table, *proof-stream, stark-verifier, stark=stark-engine, common=nock-common,
    shape, fock
::
::  Note: eny must be a field element.
::  For consistency, we tend to use (mod (shax 0) p:f:goldilocks) for testing
::  TODO: eny not sufficient
|_  [eny=@ cax=zerofier-cache:stark]
++  verifier
  =|  in=stark-input:stark
  %_    stark-verifier
      +>-
    %_  in
      all-verifier-funcs  all-verifier-funcs:common
      table-names         table-names:common
      cache               cax
    ==
  ==
::
++  verify  verify:verifier
--
