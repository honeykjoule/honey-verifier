/-  *verifier-app
/-  spider
/+  *strandio
=,  strand=strand:spider
|%
++  max-retries  12
++  get-proof
  |=  [request-id=@uv byk=beak]
  =/  m  (strand ,(unit (unit verify-result)))  :: none when /has-proof false, unit when /has-proof true
  ^-  form:m
  ;<  =bowl:rand         bind:m  get-bowl
  ;<  has-proof=?        bind:m  (scry ? %gx %verifier /has-result/(scot %uv request-id)/noun)
  ~&  "waiting for proof to be processed"
  ?:  !has-proof  (pure:m ~)
  ;<  res=(unit verify-result)  bind:m  (scry (unit verify-result) %gx %verifier /proof-result/(scot %uv request-id)/noun)
  ~&  "proof has been processed"
  (pure:m (some res))
--
^-  thread:spider
|=  arg=vase
=/  m  (strand ,vase)
^-  form:m
=+  !<([~ s=* f=*] arg)
;<  =bowl:rand         bind:m  get-bowl
::  1
;<  ~      bind:m   (poke-our %verifier verifier-request-0+!>(`verifier-request`[%prove tid.bowl s f]))
~&  "pt 1"
::  2
;<  =vase  bind:m   (take-poke %verifier-update-0)
~&  "pt 2"
=/  upd  !<(verifier-update vase)
?>  ?=(%prove-info -.upd)
=/  rid=@uv  request-id.upd
~&  >  "prove-eden: request-id is {<rid>}"
::  3
;<  res=(unit verify-result)  bind:m  ((retry (unit verify-result)) `max-retries (get-proof rid byk.bowl))
(pure:m !>(res))