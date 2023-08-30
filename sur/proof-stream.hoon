/-  *field
|%
+$  proof-path  [leaf=@ux path=(list @uv)]
::
+$  proof-data
  $%  [%merk-root p=@uv]
      [%computation p=[s=* f=*] r=*]
      [%codeword p=fpoly]
      [%terminals p=$+(proof-data-terminals (map term (map term felt)))]
      [%merk-paths a=proof-path b=proof-path c=proof-path]
      [%merk-path p=proof-path]
      [%jets p=(map @tas @)]
  ==
::
+$  stream-state
  $:  objects=(list proof-data)
      read-index=@
  ==
--
