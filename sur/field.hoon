|%
::
::  belt: base field element
::
::    An integer in the interval [0, p).
::    Due to a well chosen p, almost all numbers representable with 64 bits
::    are present in the interval.
::
::    In other words, a belt under our choice of p will always fit in 64 bits.
::
+$  belt  @
::
::  felt: extension field element
::    A list of base field elements encoded as a byte array in a single atom.
::    Note that a high bit is set to force allocation of the whole memory region.
::
::    The length is assumed by field math door defined later on,
::    based on degree provided to it.
::
::    If G is a degree 3 extension field over field F, then G's elements
::    are 4-tuples of the form F^4 = (F, F, F, F). E.g., if F = {0, 1},
::    an element of F would be 1, while an example element of G is (0, 1, 1, 0).
::
::    The felt type represents exactly such elements of our extension field G.
::
::    Since the extension field over the base field "happens to be" a polynomial ring,
::    the felt (1, 2, 3) can be thought of as a polynomial (1 + 2x + 3x^2).
::    However, it is recommended by the elders to avoid thinking of felts
::    as polynomials, and to maintain a more abstract conception of them as tuples.
::
+$  felt  @ux
::
::  melt: Montgomery space element
::
::    `Montgomery space` is obtained from the base field (Z_p, +, •) by replacing ordinary
::    modular multiplication • with Montgomery multiplication *: a*b = abr^{-1} mod p, where
::    r = 2^64. The map a --> r•a is a field isomorphism, so in particular
::    (r•a)*(r•b) = r•(a*b). Note that (r mod p) is the mult. identity in Montgomery space.
+$  melt  @
::
::  bpoly: a polynomial of explicit length with base field coefficients.
::
::    A pair of a length (must fit within 32 bits) and dat, which is
::    a list of base field coefficients, encoded as a byte array.
::    Note that a high bit is set to force allocation of the whole memory region.
::
::    Critically, a bpoly is isomorphic to a felt (at least when its lte is lower than degree).
::
::    In other words, a polynomial defined as a list of base element coefficients
::    is equivalent to a single element of the extension field.
::
::    N.B: Sometimes, bpoly is used to represent a list of belt values
::         of length greater than degree that are not meant to be interpreted
::         as extension field elements (!).
::
::    TODO: would be nice to have a separate typedef for the arb. len. list case
::
+$  bpoly  [len=@ dat=@ux]
::
::  fpoly: a polynomial of explicit length with *extension field* coefficients.
::
::    A pair of a length (must fit inside 32 bits) and dat, a big atom
::    made up of (D * len) base field coefficients, where D is the extension degree.
::    Note that a high bit is set to force allocation of the whole memory region.
::
::    Put another way, an fpoly is a polynomial whose coefficients are felts
::    (i.e. tuple of belts) instead of numbers (belts).
::
::    N.B: Sometimes, fpoly is used to represent a list of felt values
::         that aren't meant to be interpreted interpreted as polynomials
::         with felt coefficients (!).
::
+$  fpoly  [len=@ dat=@ux]
::
::  poly: list of coefficients [a_0 a_1 a_2 ... ] representing a_0 + a_1*x + a_2*x^2 + ...
::
::    Note any polynomial has an infinite set of list representatives by adding 0's
::    arbitrarily to the end of the list.
::    Note also that ~ represents the zero polynomial.
::
::    Somewhat surprisingly, this type can reprsent both polynomials
::    whose coefficients are belts (aka felts), and polynomials whose
::    coefficients are themselves felts, aka fpolys. This works because felts
::    are encoded as a single atom, the same form factor as belts.
::
+$  poly  (list @)
::
::  multi-poly: multivariable polynomial
::
::    A multivariable polynomial is a finite expression composed of (possibly empty) sums
::    of products of constants and powers of variables from the ordered set x0, x1, x2, ...
::
::    Each summand can be represented by a [key value] pair [~[i0 i1 ... ] a_{i0i1...}]
::    where a_{i0i1...} is the coefficient of (x0^i0)(x1^i1)... .
::
::    Then, a key is a list of exponents of each indeterminate, and a value is a coefficient.
::    Keep in mind that the coefficients are extension field elements (felts),
::    and not simple base field elements (belts).
::
::    This representation should not be confused with the thing-in-itself. For example,
::    the zero polynomial can be represented by the empty map ~, a map with empty key
::    [~ 0], or by maps with any number of keys ~[i0 i1 ... ] as long as the values are
::    0.
::
::    Some conventions: The zero polynomial can be represented by ~. A constant c can
::    be represented by a map with a null key and value c, i.e. ~ --> c.
::
::    NOTE: A multi-poly which is constructed with k variables can be considered a multi-poly
::    with k+l variables for any atom l, by just considering those variables as being unused
::    by the polynomial.
::    This allows the user to input what may look like contradictory multi-polys such as, say,
::    {~[1] --> 1, ~[1 0] --> 2} which one could argue is just x0 + 2*x0 = 3*x0.
::    However, this would create annoyances, so in order to use multi-poly arithmetic below,
::    one must specify a fixed number of variables explicitly, i.e. all keys must have the same
::    length. See +valid-mp below. These explicit variables may not all be necessary, e.g. if
::    a variable appears with exponent 0 in every monomial summand.
+$  multi-poly  $+(multi-poly (map bpoly felt))
::
::  A multi-poly stored as an expression graph to preserve semantic information.
+$  mp-graph
  $~  [%con 0x1.0000.0000.0000.0000.0000.0000.0000.0000.0000.0000.0000.0000]
  $%  [%con a=felt]    :: felt constant
      [%var col=@]     :: variable. col is 0-based column index.
      [%add a=mp-graph b=mp-graph]
      [%sub a=mp-graph b=mp-graph]
      [%mul a=mp-graph b=mp-graph]
      [%pow a=mp-graph n=@]
      [%scal c=felt a=mp-graph]
  ==
--
