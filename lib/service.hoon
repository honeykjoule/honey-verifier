::  library for proof server machinery: prover, proxy and get-proof thread
|%
++  default-proxy  ~misfed-podtel
++  prover-ver  2
::  @uv is a hash of (sham [requesting-ship [s=* f=*]])
::  so its map of request id to original s/f
++  make-request-id
  |=  [requester=ship sub=* fol=* n=*]
  ^-  @uv
  (sham requester sub fol n)
--