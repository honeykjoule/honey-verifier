/-  *prover-app
/+  sv=service
|%
++  extract-proof
  ::  our-id: the id that we calculated and expect for this proof update
  |=  [upd=proof-update our-id=@uv]
  ^-  (unit proof)
  ?.  ?=(%proof -.response.upd)     ~
  ?.  =(request-id.upd our-id)      ~
  ?.  =(ver.upd prover-ver:sv)      ~
  (some proof.response.upd)
::
++  extract-proof-debug
  |=  [upd=proof-update our-id=@uv]
  ^-  (unit proof)
  ?:  ?=(%proof -.response.upd)
    ?:  !=(request-id.upd our-id)
      ~&  >>  "got proof for different id {<request-id.upd>} vs. {<our-id>}"
      ~
    ?:  !=(ver.upd prover-ver:sv)
      ~&  >>  "got proof that doesn't match our version our={<prover-ver:sv>} server={<ver.upd>}"
      ~
    (some proof.response.upd)
  ::  handle the error case
  ~&  >>  "the proof request returned an error"
  =/  err  err.response.upd
  ?-    -.err
      %crash
    ~&  >>  "prover crashed"
    ~&  "one reason may be that the compiled eden formula that was sent caused a crash at runtime"
    ~&  "stack trace:"
    %-  (slog trace.err)
    ~
  ::
      %too-big
    ~&  >>  "program was too large to be proven"
    ~&  upd
    ~
  ::
      %version-mismatch
    ~&  >>  "there was a version mismatch between our verifier codebase and the prover."
    ~&  >>  "you will need to upgrade the verifier before being able to request"
    ~&  upd
    ~
  ==
--