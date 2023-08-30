/+  *table, *fock, *table-util
=,  f
|%
++  basic-column-names
  ^-  (list term)
  ::  basic fields
  :~  %op      :: opcode
      %o0      :: opcode 0 flag
      %o1      :: opcode 1 flag
      %o2      :: opcode 2 flag
      %o3      :: opcode 3 flag
      %o4      :: opcode 4 flag
      %o5      :: opcode 5 flag
      %o6      :: opcode 6 flag
      %o7      :: opcode 7 flag
      %o8      :: opcode 8 flag
      %o9      :: opcode 9 flag
      %o10     :: opcode 10 flag
      %o11     :: opcode 11 flag
      %o99     :: opcode 99 flag
      %cs-len  :: len of compute stack
      %ps-len  :: len of product stack
      %os-len  :: len of operand stack
      %osinv   :: os-len^{-1}
      %osempty :: 1 if os is empty, else 0
      %popf    :: 1 if pop, 0 if not
  ==
++  ext-column-names
  ^-  (list term)
  :: extension fields
  :~  %r1       :: general purpose register
      %r2       :: general purpose register
      %r3       :: general purpose register
      %r4       :: general purpose register
      %r5       :: general purpose register
      %mem-int1 :: interim memory multiset 1
      %mem-int2 :: interim memory multiset 2
      %mem-int3 :: interim memory multiset 3
    :: state
      %cs      :: compute stack
      %ps      :: product stack
      %mem     :: memory multiset (nock 0)
      %os      :: op stack
      %jet     :: jet multiset
  ==
++  column-names
  ^-  (list term)
  ~+
  (weld basic-column-names ext-column-names)
++  variables
  ^-  (map term multi-poly)
  (make-vars column-names)
--
