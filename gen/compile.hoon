::  compile some hoon file (against flib) (need to prefix /+  flib  =>  flib)
::  then, post process using post processer in fock
::  then, run thru transpiler
/+  *transpile, fock
/*  flib-txt  %hoon  /lib/flib/hoon
:-  %say
|=  $:  [now=@da eny=@uvJ bec=beak]
        [[pax=path ~] =desk ~]
    ==
~&  >  "compiling"
:-  %noun
::  assumes that the library has flib in its subject
=/  library    (ream .^(@t %cx pax))
=/  flib       (slap !>(~) (ream flib-txt))
=/  compiled   (slap flib library)
::(transpile (post:fock q.compiled))
compiled
