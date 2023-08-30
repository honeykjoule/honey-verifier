::  library for proof server machinery: prover, proxy and get-proof thread
|%
++  default-proxy  ~misfed-podtel
++  prover-ver  1
::  @uv is a hash of (sham [requesting-ship [s=* f=*]])
::  so its map of request id to original s/f
++  make-request-id
  |=  [requester=ship sub=* fol=* n=*]
  ^-  @uv
  (sham requester sub fol n)
::++  proxy-ack-path
::  |=  req-id=@uv
::  ^-  path
::  /proxy-ack/(scot %uv req-id)
--