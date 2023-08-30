/-  *verifier-app
/-  spider
/+  *strandio
=,  strand=strand:spider
^-  thread:spider
|=  arg=vase
=/  m  (strand ,vase)
^-  form:m
::  accepts a path to a hoon file
::  containing a gate that will be evaluated with the provided argument in a vase
::  produces the final eden code that represents the computation
=+  !<([~ =path input=vase] arg)
;<  =bowl:rand  bind:m  get-bowl
;<  ~           bind:m  (poke-our %verifier verifier-request-0+!>(`verifier-request`[%build tid.bowl path input]))
;<  =vase       bind:m  (take-poke %verifier-update-0)
=/  upd  !<(verifier-update vase)
?>  ?=(%build-result -.upd)
(pure:m !>([s f]:upd))