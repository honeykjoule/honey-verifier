|%
++  dec-nock
  ^-  nock
  ;;  nock
  [8 [1 0] [8 [1 [6 [5 [4 0 6] [0 7]] [0 6] [2 [[0 2] [4 0 6] [0 7]] [0 2]]]] [2 [0 1] [0 2]]]]
::
++  transpile
  |=  n=*
  ^-  *
  ::=/  nok=nock  ;;(nock n)
  =/  nok  n
  ?@  nok  n
  ?+    nok
    [$(n -.nok) $(n +.nok)]
  ::
      [%0 p=@]                                  ::  axis select
    nok
  ::
      [%1 p=*]                                  ::  constant
    :-  %1
    =/  inn=(unit nock)
      ((soft nock) p.nok)
    ?~  inn
      p.nok
    $(n p.nok)
  ::
      [%2 p=* q=*]                              ::  compose
    :+  %2
      $(n p.nok)
    $(n q.nok)
  ::
      [%3 p=*]                                  ::  cell test
    :-  %3
    $(n p.nok)
  ::
      [%4 p=*]                                  ::  increment
    :-  %4
    $(n p.nok)
  ::
      [%5 p=* q=*]                              ::  equality test
    :+  %5
      $(n p.nok)
    $(n q.nok)
  ::
      [%6 b=* c=* d=*]                          ::  if, then, else
    :^  %6
        $(n b.nok)
      $(n c.nok)
    $(n d.nok)
  ::
      [%7 b=* c=*]                        ::  serial compose
    =/  b  $(n +6:nok)
    =/  c  $(n +7:nok)
    =/  a  [%0 1]
    :+  %2
      [%2 a [%1 b]]
    [%1 c]
  ::
      [%8 b=* c=*]                        ::  push onto subject
    ::  *[[*[a b] a] c]
    =/  a  [%0 1]
    =/  b  $(n +6:nok)
    =/  c  $(n +7:nok)
    :+  %2
      [[%2 a [%1 b]] a]
    [%1 c]
  ::
      [%9 b=@ c=*]                           ::  select arm and fire
    ::  [7 c 2 [0 1] 0 b]
    =/  b  +6:nok
    =/  c  $(n +7:nok)
    %=    $
        n
      :+  %7
        c
      :+  %2
        [%0 1]
      [%0 b]
    ==
  ::
      [%10 p=[p=@ q=*] q=*]               ::  edit
    =/  b  $(n +12:nok)
    =/  c  $(n +13:nok)
    =/  d  $(n +7:nok)
    :+  %10
      [b c]
    d
  ::
      [%11 h=@ q=*]
    nok
    :::+  %11
      ::h.nok
    ::$(n q.nok)
::      [%11 p=$@(@ [p=@ q=nock]) q=nock]         ::  hint
::    !!
::  ::
::      [%12 p=nock q=nock]                       ::  grab data from sky
::    !!
  ==
::
--
