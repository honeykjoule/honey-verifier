|_  own=@t
::
++  grow                                                ::  convert to
  |%
  ++  mime  `^mime`[/text/x-hick (as-octs:mimes:html own)]
  ++  txt
    (to-wain:format own)
  --
++  grab
  |%                                            ::  convert from
  ++  mime  |=([p=mite q=octs] q.q)
  ++  noun  @t
  ++  txt   of-wain:format
  --
++  grad  %txt
--
