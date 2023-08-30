/+  *table
::
=,  f
::
|_  [lef=table lef-col=fpoly rig=table rig-col=fpoly]
++  quotient
  |=  domain=(list felt)
  ^-  fpoly
  =/  difference-codeword
    %~  to-poly  fop
    (fpsub lef-col rig-col)
  =/  zerofier
    (turn domain |=(d=@ (fsub d (lift 1))))
  %-  init-fpoly
  (zip difference-codeword zerofier fdiv)
::
++  quotient-degree-bound
  ^-  @
  %-  dec
  %+  max  ~(interpolant-degree-bound tab lef)
  ~(interpolant-degree-bound tab rig)
::
++  evaluate-difference
  |=  [points=(list fpoly) lef-tab=@ lef-col=@ rig-tab=@ rig-col=@]
  =/  lef  (~(snag fop (snag lef-tab points)) lef-col)
  =/  rig  (~(snag fop (snag rig-tab points)) rig-col)
  (fsub lef rig)
--
