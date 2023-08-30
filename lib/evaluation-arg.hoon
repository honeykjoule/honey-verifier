/+  *table
::
|_  [challenge-i=@ terminal-i=@ symbols=(list felt:f)]
++  select-terminal
  |=  terminals=(list @)
  (snag terminal-i terminals)
::
++  compute-terminal
  |=  challenges=(list @)
  ^-  felt:f
  =/  iota  (lift:f (snag challenge-i challenges))
  %+  roll  symbols
  |=  [s=felt:f acc=@]
  (fadd:f s (fmul:f iota acc))
--
