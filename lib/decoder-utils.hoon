/+  *table, fock, *table-util
::  TODO rename this file to something else
=,  f
|_  rand=[a=felt b=felt c=felt alf=felt]
++  f1   (lift 0x1)  :: one felt
++  f0  (lift 0x0)  :: zero felt
+$  decode-output
  $:  is-cons=felt
      opcode=felt
      tail1=tree-data:fock
      tail2=tree-data:fock
      tail3=tree-data:fock
      mem-int1=ld-mset
      mem-int2=ld-mset
      mem-int3=ld-mset
      mem=ld-mset
  ==
++  decoder
  |_  $:  noun-chals=[a=felt b=felt c=felt alf=felt]
          tuple-chals=[p=felt q=felt r=felt s=felt t=felt]
      ==
  ++  decode-formula
    |=  [f=tree-data:fock mem=ld-mset]
    ^-  decode-output
    =/  nu  ~(. noun-utils noun-chals tuple-chals)
    =/  t0  *tree-data:fock
    =/  m0  *ld-mset
    :+  ?:(?=(^ -.n.f) f1 f0)
      ?:(?=(^ -.n.f) (lift 99) (lift -.n.f))
    ?+  n.f  ~|(bad-formula+n.f !!)
    :: cons
        [^ *]
      :: We validate f is cons by proving that axis 4
      :: exists.
      =/  four  (build-tree-data:fock -<.n.f noun-chals)
      =/  sf1   (build-tree-data:fock -.n.f noun-chals)
      =/  sf2   (build-tree-data:fock +.n.f noun-chals)
      :^  sf1   sf2  four
      =-  [&1:- &2:- m0 &3:-]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 tre.sf1 1]
          [tre.f 3 tre.sf2 1]
          [tre.f 4 tre.four 1]
      ==
    ::
    :: Nock 0
      [op=%0 sf=*]
      =/  sf  (build-tree-data:fock sf.n.f noun-chals)
      :^  sf  t0  t0
      =-  [&1:- &2:- m0 m0]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 (build-atom.nu op.n.f) 1]
          [tre.f 3 tre.sf 1]
      ==
    ::
    :: One subformula
        [op=?(%0 %1 %3 %4) sf=*]
      =/  sf  (build-tree-data:fock sf.n.f noun-chals)
      :^  sf  t0  t0
      =-  [&1:- m0 m0 &2:-]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 (build-atom.nu op.n.f) 1]
          [tre.f 3 tre.sf 1]
      ==
    ::
    :: Two subformulae
        [op=?(%2 %5 %7 %8 %9) sf1=* sf2=*]
      =/  sf1  (build-tree-data:fock sf1.n.f noun-chals)
      =/  sf2  (build-tree-data:fock sf2.n.f noun-chals)
      :^  sf1  sf2  t0
      =-  [&1:- &2:- m0 &3:-]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 (build-atom.nu op.n.f) 1]
          [tre.f 6 tre.sf1 1]
          [tre.f 7 tre.sf2 1]
      ==
    ::
    :: Nock 6
        [op=%6 cond=* t=* f=*]
      =/  sf1  (build-tree-data:fock cond.n.f noun-chals)
      =/  sf2  (build-tree-data:fock t.n.f noun-chals)
      =/  sf3  (build-tree-data:fock f.n.f noun-chals)
      :^  sf1  sf2  sf3
      =-  [&1:- &2:- &3:- &4:-]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 (build-atom.nu op.n.f) 1]
          [tre.f 6 tre.sf1 1]
          [tre.f 14 tre.sf2 1]
          [tre.f 15 tre.sf3 1]
      ==
    ::
    :: Nock 10
    ::
    :: NOTE: for nock 10 we are returning the tails in the wrong order
    :: tail1=value, tail2=target, and tail3=axis. This is so 10 can be processed
    :: like all the other 2 subformulae formulas and we don't need separate constraints
    :: for it. But it's probably confusing so this should be cleaned up somehow maybe
    :: when we change how the registers work.
    :: Though if you squint you can see axis as just extra data and value is the real first
    :: subformula.
        [op=%10 [axis=* value=*] target=*]
      =/  sf1  (build-tree-data:fock value.n.f noun-chals)
      =/  sf2  (build-tree-data:fock target.n.f noun-chals)
      =/  sf3  (build-tree-data:fock axis.n.f noun-chals)
      :^  sf1  sf2  sf3
      =-  [&1:- &2:- &3:- &4:-]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 (build-atom.nu op.n.f) 1]
          [tre.f 13 tre.sf1 1]
          [tre.f 7 tre.sf2 1]
          [tre.f 12 tre.sf3 1]
      ==
    ::
    :: Nock 11
        [op=%11 tag=@ *]
      =/  sf  (build-tree-data:fock tag.n.f noun-chals)
      :^  sf  t0  t0
      =-  [&1:- &2:- m0 m0]
      %+  make-zeroes-ld.nu  mem
      :~  [tre.f 2 (build-atom.nu op.n.f) 1]
          [tre.f 6 tre.sf 1]
      ==
    ==
  --
--
