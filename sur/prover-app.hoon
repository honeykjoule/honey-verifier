/-  *prover
|%
+$  error
  $%  [%too-big heights=(list @)]  ::  table heights
      [%crash trace=tang]  :: stack trace
      [%version-mismatch current=@ requested=@]
  ==
+$  proof-request
  $%  [%submit-computation [s=* f=*] request-id=@uv src=ship ver=@]
  ==
+$  proof-command
  $%  [%set-queen queen=ship]
  ==
::
::
+$  proof-update
  $:  request-id=@uv
      ver=@
      $=  response
      $%  [%proof product=* =proof]
          [%error err=error]
      ==
  ==
--
