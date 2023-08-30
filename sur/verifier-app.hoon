/-  *verifier
/-  *prover-app
|%
+$  verifier-request
  $%  [%prove tid=@tatid s=* f=*]
      [%build tid=@tatid =path input=vase]
  ==
::
+$  verifier-command
  $%  [%set-proxy new=ship]
      [%set-state new=versioned-state]
  ==
::
+$  verifier-update
  $%  [%state state=versioned-state]
      [%build-result s=* f=*]
      [%prove-info request-id=@uv]  :: request id for computation
  ==
::
+$  versioned-state
  $%  state-0
  ==
::
+$  state-0
  $+  state-0
  $:  %0
      proofs=(map @uv proof-update)                 ::  @uv = request-id
      verifications=(map @uv (unit verify-result))  ::  ~ means there was some kind of error, proof-result will have the details
      ids=(map [s=* f=*] @uv)
      prox=ship                                     ::  the ship hosting the server to request proofs from
  ==
--