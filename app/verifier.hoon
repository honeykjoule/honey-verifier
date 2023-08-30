/-  *proxy
/-  *prover-app
/-  *verifier-app
/-  spider
/+  *service
/+  *verifier-app
/+  nv=nock-verifier
/+  default-agent, dbug, agentio
|%
::
+$  card  $+(card card:agent:gall)
--
::
%-  agent:dbug
=|  state-0
=*  state  -
^-  agent:gall
=<
|_  bol=bowl:gall
+*  this  .
    def   ~(. (default-agent this %.n) bol)
    io    ~(. agentio bol)
    hc    ~(. +> bol)
++  on-init
  ^-  (quip card _this)
  =.  prox  default-proxy:sv
  `this
::
++  on-save  !>(state)
++  on-load
  |=  old-vase=vase
  ^-  (quip card _this)
  [~ this(state !<(state-0 old-vase))]
::
++  on-poke
  |=  [=mark =vase]
  ^-  (quip card _this)
  =^  cards  state
  ?+    mark  (on-poke:def mark vase)
      %verifier-request-0
    ::  TODO make a compilation poke that takes a path and stores (or outputs to file) compiled nock
    =/  req         !<(verifier-request vase)
    ?-    -.req
        %build
      =/  base=path  /(scot %p our.bol)/[q.byk.bol]/(scot %da now.bol)
      =/  flib     (slap !>(~) (ream .^(@t %cx (weld base /lib/flib/hoon))))
      =/  program  (slap flib (ream .^(@t %cx path.req)))
      =/  program-built=[* *]
        (post:fock:nv ;;([* *] q:(flap:fock:nv program input.req)))
      :_  state
      :_  ~
      %+  ~(poke-our pass:io /build-result)  %spider
      :-  %spider-input
      =-  !>(`input:spider`[tid.req %verifier-update-0 -])
      !>(`verifier-update`[%build-result program-built])
    ::
        %prove
      =/  rid  (make-request-id our.bol s.req f.req eny.bol)
      =.  ids  (~(put by ids) [s f]:req rid)
      :_  state
      :~  %+  ~(poke pass:io /submit-comp)
            [prox %proxy]
          proxy-request-0+!>(`proxy-request`[%submit-to-proxy [s f]:req eny.bol prover-ver:sv])
        ::
          %+  ~(poke-our pass:io /proof-info)
            %spider
          :-  %spider-input
          =-  !>(`input:spider`[tid.req -])
          verifier-update-0+!>(`verifier-update`[%prove-info rid])
      ==
    ==
  ::
      %proof-update-0
    =/  upd     !<(proof-update vase)
    =.  proofs  (~(put by proofs) request-id.upd upd)
    ~&  "verifier: got proof update for {<request-id.upd>}"
    ?:  ?=(%proof -.response.upd)
      =/  ver=verify-result  (~(verify nv eny.bol ~) proof.response.upd)
      =.  verifications  (~(put by verifications) request-id.upd (some ver))
      `state
    =.  verifications  (~(put by verifications) request-id.upd ~)
    `state
  ::
      %verifier-command-0
    ::  commands are admin powers and can only be issued locally
    ?>  =(our.bol src.bol)
    =/  com  !<(verifier-command vase)
    ::?.  ?=(%set-proxy -.com)  ~|(%unknown-command !!)
    ~&  old+prox.state
    =.  prox  new.com
    ~&  new+prox.state
    `state
  ==
  [cards this]
::
++  on-agent  on-agent:def
++  on-watch  on-watch:def

++  on-leave
  |=  =path
  ^-  (quip card _this)
  `this
::
++  on-peek
  |=  =path
  ^-  (unit (unit cage))
  ?+    path  (on-peek:def path)
      [%x %all ~]  ``noun+!>(state)
      [%x %has-result @ ~]
    =/  rid=@uv  (slav %uv i.t.t.path)
    ``noun+!>(`?`(~(has by verifications) rid))
  ::
      [%x %proof-result @ ~]
    =/  rid=@uv  (slav %uv i.t.t.path)
    ?~  res=(~(get by verifications) rid)  ~
    ``noun+!>(`(unit verify-result)`u.res)
  ==
++  on-arvo  on-arvo:def
++  on-fail  on-fail:def
--
::
|_  bol=bowl:gall
++  is-allowed
  |=  =ship
  %.y
--
