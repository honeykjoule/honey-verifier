/+  *goldilocks
=,  f
|%
::
:: Nock 10 edits the noun so it has subject for the original noun and new-subject for the
:: new edited noun. Nock 0 is proved exactly like a nock 10 but with new-subject=subject.
:: So when recording a nock 0 you want to just pass subject in for new-subject.
:: Basically a nock 0 is a special case of nock 10 where the edited tree is the original tree.
+$  zero-map  (map subject=* (map [axis=* new-subject=*] count=@))
+$  return
  $+  return
  $:  stack=(list *)
      zeroes=zero-map
      formulas=(map formula=* count=@)
      subjects=(map subject=* count=@)
      [s=* f=*]
      jets=(list [@tas sam=* prod=*])
      recur-depth=@
  ==
::
::  dyck-stack: horner accumulated stack of dyck path
+$  dyck-stack  (list felt)
::
::  dyck-felt: felt representing dyck-stack
+$  dyck-felt  felt
::
::  leaf-stack: horner accumulated stack of leaves
+$  leaf-stack  (list felt)
::
::  leaf-felt: felt representing leaf-stack
+$  leaf-felt  felt
::
::  tree-felt: felt representing weighted sum: a*len + b*dyck-felt + c*leaf-felt
+$  tree-felt  felt
::
::  tree-data: len: length of the leaf stack
+$  tree-data
  $:  len=@        tre=tree-felt
      =dyck-stack  =leaf-stack
      =dyck-felt   =leaf-felt
      n=*
  ==
::
::  compute-stack: horner accumulated stack of packed-tree-felts
+$  compute-stack  (list tree-data)
::
::  compute-felt: felt representing compute-stack
+$  compute-felt   felt
--
