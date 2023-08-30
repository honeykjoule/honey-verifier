/+  *table, *fock
=,  f
|%
++  variables
  ^-  (map term multi-poly)
  %-  make-vars
  variable-labels
++  variable-labels
  ^-  (list term)
  :~  %pow         ::  the power in the exponent
      %mult        ::  multiplicity; how many times do you want to record this power
      %multi       ::  multiplicity inverse
      %multf       ::  multiplicity flag; 1 if mult =! 0, 0 otherwise
      %exp         ::  alf^pow
      %exp-mulset  ::  mass product of (bet - (a*pow + b*exp)) terms for each row where mult =! 0
  ==
--