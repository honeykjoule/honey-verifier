/-  *fock
/+  *goldilocks, shape, *challenges, util=table-util, *transpile, jet, bn=bignum
~%  %fock  ..part  ~
|%
++  indirect-to-bits
  ~/  %indirect-to-bits
  |=  axi=@
  ^-  (list ?)
  =|  lis=(list ?)
  |-
  ?:  =(1 axi)  lis
  =/  hav  (dvr axi 2)
  $(axi p.hav, lis [=(q.hav 0) lis])
--
::
~%  %inner-fock  ..indirect-to-bits  ~
=,  util
=,  f
|%
++  post
  ~/  %post
  |=  nok=^
  ^-  ^
  |^  [(process -.nok) (process +.nok)]
  ::
  ++  process
    |=  a=*
    ^-  *
    ?^  a
      ?:  ?=(%bignum -.a)
        ::  TODO investigate where [%bignum [0 0]] are coming from
        ::~&  bignom+a
        =>  .(a ;;(bignum:bn a))
        ?:  ?=(%| +<.a)  ::  all bignums must be literals from source
          (chunk:bn +>.a)
        ?:  (valid:bn a)
          a
        ~|(bignum-chunks-overu32/+.a !!)
      [$(a -.a) $(a +.a)]
    ?:  (based a)
      a
    ~&  not-based+a
    =/  pax  (indirect-to-bits a)
    |-
    =^  b  pax
      (take pax)
    ?~  pax  b
    [b $]
  ::
  ++  take
    |=  pax=(list ?)
    ^-  [@ (list ?)]
    =/  axi  1
    |-
    ?~  pax                     [axi ~]
    ?.  (based +((mul axi 2)))  [axi pax]
    =.  axi  (mul axi 2)
    $(pax t.pax, axi ?:(i.pax axi +(axi)))
  --
::
::  TODO make these arms a door over the randomness
::
::  a, b, c, and alf are random weights from the challenges
++  build-tree-data
  ~/  %build-tree-data
  |=  [t=* a=felt b=felt c=felt alf=felt]
  ^-  tree-data
  ~+
  =/  leaf=(list felt)  (turn (leaf-sequence:shape t) lift)
  =/  dyck=(list felt)  (turn (dyck:shape t) lift)
  =/  =leaf-felt
    dat:(~(push-all fstack (init-felt-stack alf)) leaf)
  =/  =dyck-felt
    dat:(~(push-all fstack (init-felt-stack alf)) dyck)
  =/  len  (lent leaf)
  :*  len
      (~(compress tuple ~[a b c]) ~[(lift len) dyck-felt leaf-felt])
      dyck       leaf
      dyck-felt  leaf-felt
      t
  ==
::
++  build-compute-stack
  ~/  %build-compute-stack
  |=  [lis=(list *) a=felt b=felt c=felt alf=felt]
  ^-  compute-stack
  %+  turn  lis
  |=  t=*
  (build-tree-data t a b c alf)
::
++  build-jet-list
  ~/  %build-jet-list
  |=  [lis=(list [@tas * *]) a=felt b=felt c=felt alf=felt]
  ^-  (list jet-data:jet)
  %+  turn  lis
  |=  [name=@tas sam=* prod=*]
  :+  name
    (build-tree-data sam a b c alf)
  (build-tree-data prod a b c alf)
::
+$  subtree-val  [count=@ =tree-felt len=@ =dyck-felt =leaf-felt]
::
+$  subtree-multiset
  $+  subtree-multiset
  (map subtree=* subtree-val)
::
++  get-powers
  ~/  %get-powers
  |=  ret=return
  ^-  pows=(map @ @)
  %+  roll  ~(tap by zeroes.ret)
  |=  [[subject=* rec=(map [axis=* new-subj=*] count=@)] pows=(map @ @)]
  %+  roll  ~(tap by rec)
  |=  [[[axis=* new-subj=*] count=@] pows=_pows]
  ::  TODO: support tuple axes
  ?>  ?=(@ axis)
  =/  bits  (indirect-to-bits axis)
  |-
  ?~  bits  pows
  =/  sib-subj
    ?:  =(0 i.bits)
      +.subject
    -.subject
  =/  pax-subj
    ?:  =(0 i.bits)
      -.subject
    +.subject
  =.  pows
    %+  ~(put by pows)  (lent (leaf-sequence:shape sib-subj))
    .+  (~(gut by pows) (lent (leaf-sequence:shape sib-subj)) 0)
  %=    $
    pows
    %+  ~(put by pows)  (lent (leaf-sequence:shape pax-subj))
    .+  (~(gut by pows) (lent (leaf-sequence:shape pax-subj)) 0)
  ::
    bits     t.bits
    subject  pax-subj
  ==
::
++  get-subtree-multiset
  ~/  %get-subtree-multiset
  |=  [ret=return challenges=(list felt)]
  ^-  subtree-multiset
  =/  r  ~(r rnd (make-challenge-map challenges %nockzs))
  =/  [a=felt b=felt c=felt alf=felt]  [(r %a) (r %b) (r %c) (r %alf)]
  %+  roll  ~(tap by zeroes.ret)
  |=  [[subject=* rec=(map [axis=* new-subj=*] count=@)] mult=subtree-multiset]
  =/  tre-stk
    %-  build-tree-data
    [subject a b c alf]
  %+  roll  ~(tap by rec)
  |=  [[[axis=* new-subj=*] count=@] mult=_mult]
  ::  TODO: support tuple axes
  ?>  ?=(@ axis)
  =/  bits  (indirect-to-bits axis)
  |^
  =/  new-tre-stk
    (build-tree-data new-subj a b c alf)
  =.  mult  (put-tree mult tre-stk 1)
  =.  mult  (put-tree mult new-tre-stk 1)
  ?~  bits  mult
  =/  sib-subj
    ?:  =(0 i.bits)
      +.subject
    -.subject
  =/  pax-subj
    ?:  =(0 i.bits)
      -.subject
    +.subject
  =/  sib-tre-stk
    %-  build-tree-data
    [sib-subj a b c alf]
  =/  pax-tre-stk
    %-  build-tree-data
    [pax-subj a b c alf]
  =/  new-pax-subj
    ?:  =(0 i.bits)
      -.new-subj
    +.new-subj
  =/  new-pax-tre-stk
    (build-tree-data [new-pax-subj a b c alf])
  =.  mult  (put-tree mult sib-tre-stk count)
  =.  mult  (put-tree mult new-pax-tre-stk count)
  =.  mult  (put-tree mult pax-tre-stk count)
  %=    $
    bits      t.bits
    subject   pax-subj
    new-subj  new-pax-subj
  ==
  ++  put-tree
    |=  [mult=subtree-multiset tree=tree-data inc=@ud]
    ^-  subtree-multiset
    =/  cot=subtree-val
      %+  fall  (~(get by mult) n.tree)
      [0 [tre len dyck-felt leaf-felt]:tree]
    %+  ~(put by mult)  n.tree
    cot(count (add count.cot inc))
  --
::
++  flap                                                ::  slam a gate
  ~/  %flap
  |=  [gat=vase sam=vase]  ^-  vase
  =+  :-  ^=  typ  ^-  type
          [%cell p.gat p.sam]
      ^=  gen  ^-  hoon
      [%cnsg [%$ ~] [%$ 2] [%$ 3] ~]
  =+  gun=(~(mint ut typ) %noun gen)
  [p.gun (flup q.gat q.sam)]
::
++  flup
  ~/  %flup
  |=  sub=[gat=* sam=*]
  [sub [%9 2 %10 [6 %0 3] %0 2]]
::
++  fink
  ~/  %fink
  |=  sam=^
  =*  subject  -.sam
  =*  formula  +.sam
  ::  TODO: this should not be run by fink, or if it is, it should be run by the user themselves
  ::  so that they can compare the compiled result with the nock returned from the proof
  ::  and have it be equivalent
  =.  sam      (post sam)
  =|  ret=return
  =.  ret  ret(s subject, f formula)
  |^  ^-  (pair * return)
  =.  stack.ret  [formula subject stack.ret]
  ::  XX duplicated code. should refactor out to a map-based multiset door or smtn
  =.  subjects.ret
    ?~  existing=(~(get by subjects.ret) subject)
      (~(put by subjects.ret) subject 1)
    (~(put by subjects.ret) subject +(u.existing))
  ::
  =?  formulas.ret  &(!=(%10 -.formula) !=(%11 -.formula))
    ?~  existing=(~(get by formulas.ret) formula)
      (~(put by formulas.ret) formula 1)
    (~(put by formulas.ret) formula +(u.existing))
  ?+    formula  ~&  formula  !!
      [^ *]
    =^  tail  ret  $(formula +.formula)
    =^  head  ret  $(formula -.formula)
    =.  stack.ret  [[head tail] tail head [15 99] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [[head tail] 2 [head tail]]
          [[head tail] 3 [head tail]]
          [formula 4 formula]
          [formula 2 formula]
          [formula 3 formula]
      ==
    :_  ret
    [head tail]
  ::
      [%0 axis=*]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 3 formula]
          [subject axis.formula subject]
      ==
    :-  (need (frag axis.formula subject))
    ret
  ::
      [%1 constant=*]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 3 formula]
      ==
    :_  ret
    constant.formula
  ::
      [%2 subject=* formula=*]
    =^  form  ret  $(formula formula.formula)
    =^  subj  ret  $(formula subject.formula)
    =.  stack.ret  [[15 2] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 6 formula]
          [formula 7 formula]
      ==
    %=  $
      subject  subj
      formula  form
    ==
  ::
      [%3 argument=*]
    =^  argument  ret  $(formula argument.formula)
    =.  stack.ret  [argument [15 3] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 3 formula]
      ==
    :_  ret
    .?(argument)
  ::
      [%4 argument=*]
    =^  argument  ret  $(formula argument.formula)
    =.  stack.ret  [[15 4] subject stack.ret]
    ?^  argument  !!
    =.  stack.ret  [argument stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 3 formula]
      ==
    :_  ret
    (mod .+(argument) p)
  ::
      [%5 a=* b=*]
    =^  b  ret  $(formula b.formula)
    =^  a  ret  $(formula a.formula)
    =.  stack.ret  [b a [15 5] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 6 formula]
          [formula 7 formula]
      ==
    :_  ret
    =(a b)
  ::
      [%6 test=* yes=* no=*]
    =^  result  ret  $(formula test.formula)
    =.  stack.ret
      [no.formula yes.formula result subject [15 6] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 6 formula]
          [formula 14 formula]
          [formula 15 formula]
      ==
    ?+  result  !!
      %&  $(formula yes.formula)
      %|  $(formula no.formula)
    ==
  ::
      [%7 subject=* next=*]
    =^  subj  ret  $(formula subject.formula)
    =.  stack.ret  [next.formula subj [15 7] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 6 formula]
          [formula 7 formula]
      ==
    %=  $
      subject  subj
      formula  next.formula
    ==
  ::
      [%8 head=* next=*]
    =^  head  ret  $(formula head.formula)
    =.  stack.ret
      [[head subject] subject next.formula head [15 8] subject stack.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [[head subject] 2 [head subject]]
          [[head subject] 3 [head subject]]
          [formula 2 formula]
          [formula 6 formula]
          [formula 7 formula]
      ==
    %=  $
      subject  [head subject]
      formula  next.formula
    ==
  ::
      [%9 axis=* core=*]
    =^  core  ret  $(formula core.formula)
    =/  arm  (need (frag axis.formula core))
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [core axis.formula core]
          [formula 2 formula]
          [formula 6 formula]
          [formula 7 formula]
      ==
    =.  stack.ret
      [arm axis.formula core [15 9] subject stack.ret]
    %=  $
      subject  core
      formula  arm
    ==
  ::
      [%10 [axis=@ value=*] target=*]
    ?:  =(0 axis.formula)  !!
    =^  target  ret  $(formula target.formula)
    =^  value   ret  $(formula value.formula)
    =/  mutant=(unit *)
      (edit axis.formula target value)
    ?~  mutant  !!
    =.  stack.ret
      :*  value
          target
          axis.formula
          u.mutant
          .*(target [0 axis.formula])
          [15 10]
          subject
          stack.ret
      ==
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      :~  [formula 2 formula]
          [formula 7 formula]
          [formula 13 formula]
          [formula 12 formula]
          [target axis.formula u.mutant]
      ==
    [u.mutant ret]
  ::
      [%11 tag=@ next=*]
    =.  zeroes.ret  (record zeroes.ret subject 6 subject)
    =/  sam
      ~|  sample-mismatch+sam
      (need (frag 6 subject))
    ::  TODO: handle an 11 that isn't a real jet
    =/  jet-name=@tas  `@tas`tag.formula
    =/  jf=jet-funcs:jet
      ~|  unknown-jet+jet-name
      (~(got by jet-func-map:jet) jet-name)
    =/  prod  (compute:jf sam)
    =.  jets.ret  [[jet-name sam prod] jets.ret]
    =.  zeroes.ret
      %+  record-all  zeroes.ret
      %+  welp
        (turn atoms:jf |=(ad=atom-data:jet [sam axis.ad sam]))
      :~  [formula 2 formula]
          [formula 6 formula]
      ==
    :_  ret
    prod
  ::
      [%11 [tag=@ clue=*] next=*]
    ~&  `@tas`tag.formula
    $(formula next.formula)
  ==
  ::
  ++  edit
    |=  [axis=@ target=* value=*]
    ^-  (unit)
    ?:  =(1 axis)  `value
    ?@  target  ~
    =/  pick  (cap axis)
    =/  mutant
      %=  $
        axis    (mas axis)
        target  ?-(pick %2 -.target, %3 +.target)
      ==
    ?~  mutant  ~
    ?-  pick
      %2  `[u.mutant +.target]
      %3  `[-.target u.mutant]
    ==
  ::
  ++  record-all
    |=  [zeroes=zero-map zs=(list [subject=* axis=* new-subject=*])]
    ^-  zero-map
    %+  roll  zs
    |=  [z=[subject=* axis=* new-subject=*] new-zeroes=_zeroes]
    (record new-zeroes z)
  ::
  ++  record
    |=  [zeroes=zero-map subject=* axis=* new-subject=*]
    ^-  zero-map
    ?~  rec=(~(get by zeroes) subject)
      %+  ~(put by zeroes)
        subject
      (~(put by *(map [* *] @)) [axis new-subject] 1)
    ?~  mem=(~(get by u.rec) [axis new-subject])
      %+  ~(put by zeroes)
        subject
      (~(put by u.rec) [axis new-subject] 1)
    %+  ~(put by zeroes)
      subject
    (~(put by u.rec) [axis new-subject] +(u.mem))
  --
  ::
  ++  frag
    |=  [axis=* noun=*]
    ^-  (unit)
    |^
    ?@  axis  (frag-atom axis noun)
    ~|(%axis-is-too-big !!)
    ::  TODO actually support the cell case
    ::?>  ?=(@ -.axis)
    ::$(axis +.axis, noun (need (frag-atom -.axis noun)))
    ::
    ++  frag-atom
      |=  [axis=@ noun=*]
      ^-  (unit)
      ?:  =(0 axis)  ~
      |-  ^-  (unit)
      ?:  =(1 axis)  `noun
      ?@  noun  ~
      =/  pick  (cap axis)
      %=  $
        axis  (mas axis)
        noun  ?-(pick %2 -.noun, %3 +.noun)
      ==
    --
--
