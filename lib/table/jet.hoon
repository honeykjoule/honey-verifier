/+  *goldilocks, *jet, table
=,  f
|%
::  %bn and %en columns are written by the individual jets themselves
++  basic-column-names
  ^-  (list term)
  :~  %b0
      %b1
      %b2
      %b3
      %b4
  ==
::
++  ext-column-names
  ^-  (list term)
  :~  %e0
      %e1
      %e2
      %e3
      %e4
      %e5
  ==
::
::  extra columns are written by the jet table and not by the individual jets
++  extra-basic-col-names
  ^-  (list term)
  :~  %pad        :: padding flag
      %first-row  :: is first row
      %jet-id     :: jet id
  ==
::
++  extra-ext-col-names
  ^-  (list term)
  :~  %sam   :: sample
      %prod  :: product
      %jet   :: mulitset shared with stack table
      %mem   :: memory multiset for nock 0s
  ==
::
::  selector columns are dynamic based on the actual jets used. they are written by the jet table
::  and not the individual jets.
++  selector-column-names
  |=  num-jets=@
  ^-  (list term)
  ~+
  %+  turn  (range num-jets)
  |=  i=@
  (crip (weld "sel" (scow %ud i)))
::
++  num-basic-cols
  |=  num-jets=@
  ^-  @
  ;:  add
    (lent basic-column-names)
    (lent extra-basic-col-names)
    (lent (selector-column-names num-jets))
  ==
::
++  num-ext-cols
  ^-  @
  (add (lent ext-column-names) (lent extra-ext-col-names))
::
++  num-total-cols
  |=  num-jets=@
  ^-  @
  (add (num-basic-cols num-jets) num-ext-cols)
::
++  base-width
  |=  =jet-map
  ^-  @
  (num-basic-cols (lent ~(tap by jet-map)))
::
++  full-width
  |=  =jet-map
  ^-  @
  (num-total-cols (lent ~(tap by jet-map)))
::
++  column-names
  |=  num-jets=@
  ^-  (list term)
  ~+
  ;:  weld
    extra-basic-col-names
    basic-column-names
    (selector-column-names num-jets)
    ext-column-names
    extra-ext-col-names
  ==
::
++  all-ext-column-names  (weld ext-column-names extra-ext-col-names)
::
++  all-basic-column-names
  |=  num-jets=@
  ^-  (list term)
  ;:  weld
    extra-basic-col-names
    basic-column-names
    (selector-column-names num-jets)
  ==
::
++  variables
  |=  num-jets=@
  ^-  (map term mp-graph)
  (make-vars:table (column-names num-jets))
--
