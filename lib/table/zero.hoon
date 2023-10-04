/+  *table, *fock
=,  f
=,  mp-to-graph
::
|%
++  variables
  ^-  (map term mp-graph:f)
  =/  col-variables
    %-  make-vars
    variable-labels
  %-  ~(gas by col-variables)
  :~
    ::  %yet = %tar - (2*%axis + %path)
    :-  %yet
    %+  mpsub  (~(got by col-variables) %tar)
    %+  mpadd  (mpscal (lift 2) (~(got by col-variables) %axis))
    (~(got by col-variables) %path)
  ==
::  variable-labels: names for variables as terms
++  basic-labels
  ^-  (list term)
  :~
  ::
  ::  basic fields
  ::
    %path  ::  binary digit of target axis, excluding leading one, most sig to least
    %tar   ::  target axis
    %tari  ::  inverse of tar
    %tarf  ::  tar flag: 0 if tar=0, 1 otherwise
    %axis  ::  current axis in path traversal
    %yeti  ::  inverse of yet=(tar-axis) (as in, "are we there yet")
    %yetf  ::  yet flag; 0 if yet=0, 1 otherwise
    %uses  ::  how many times do we have to record this (subject, axis) pair
  ==
++  ext-labels
  ^-  (list term)
  :~
  ::
  ::  extension fields
  ::
    %subj  ::  current subject on which Nock 0 is being performed
    %tree-len  ::  length of the leaf vector of the tree
    %tree-dyck  ::  dyck word of tree as a polynomial in alf
    %tree-leaf  ::  leaf vector of tree as a polynomial in alf
    %left-len  ::  length of the leaf vector of tree's left subtree
    %left-dyck  ::  dyck word of left subtree as a polynomial in alf
    %left-leaf  ::  leaf vector of left subtree as a polynomial in alf
    %right-len  ::  length of the leaf vector of tree's right subtree
    %right-dyck  ::  dyck word of right subtree as a polynomial in alf
    %right-leaf  ::  leaf vector of right subtree as a polynomial in alf
  ::
  :: second tree walk (for nock 10)
  ::
    %new-subj       :: edited subject
    %new-tree-len
    %new-tree-dyck
    %new-tree-leaf
    %new-left-len
    %new-left-dyck
    %new-left-leaf
    %new-right-len
    %new-right-dyck
    %new-right-leaf
  ::
  ::  exponents and multisets
  ::
    %exp-r  ::  alf^{right-len}
    %new-exp-r  ::  alf^{new-right-len}
    %out  ::  output multiset
    %noun-mulset  ::  multiset for ensuring tree felts have been validated
  ==
++  variable-labels  (weld basic-labels ext-labels)
--
