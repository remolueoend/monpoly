  $ echo 'P(x) AND x MATCHES r"ab"' > matches_1.mfotl
  $ monpoly -sig matches.sig -formula matches_1.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND x MATCHES r"ab"
  The sequence of free variables is: (x)
  At time point 0:
  @0 (time point 0): (("ab"))
  At time point 1:
  @1 (time point 1): (("aabc"))
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): (("zab"))
  At time point 4:
  @4 (time point 4): (("zzzab"))

  $ echo 'P(x) AND x MATCHES r"\(a\)*b"' > matches_2.mfotl
  $ monpoly -sig matches.sig -formula matches_2.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND x MATCHES r"\(a\)*b"
  The sequence of free variables is: (x)
  At time point 0:
  @0 (time point 0): (("ab"))
  At time point 1:
  @1 (time point 1): (("aabc"))
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): (("zab"))
  At time point 4:
  @4 (time point 4): (("zzzab"))

  $ echo 'P(x) AND x MATCHES r"\(z\)*ab" (_)' > matches_3.mfotl
  $ monpoly -sig matches.sig -formula matches_3.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND x MATCHES r"\(z\)*ab" (_)
  The sequence of free variables is: (x)
  At time point 0:
  @0 (time point 0): (("ab"))
  At time point 1:
  @1 (time point 1): (("aabc"))
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): (("zab"))
  At time point 4:
  @4 (time point 4): (("zzzab"))

  $ echo 'P(x) AND x MATCHES r"\(z\)*ab" (y)' > matches_4.mfotl
  $ monpoly -sig matches.sig -formula matches_4.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND x MATCHES r"\(z\)*ab" (y)
  The sequence of free variables is: (x,y)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ()
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): (("zab","z"))
  At time point 4:
  @4 (time point 4): (("zzzab","z"))

  $ echo 'P(x) AND Q(y) AND x MATCHES r"\(z*\)ab" (y)' > matches_5.mfotl
  $ monpoly -sig matches.sig -formula matches_5.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    (P(x) AND Q(y)) AND x MATCHES r"\(z*\)ab" (y)
  The sequence of free variables is: (x,y)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ()
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): ()
  At time point 4:
  @4 (time point 4): (("zzzab","zzz"))

  $ echo 'P(x) AND x MATCHES r"\(z\)*\(a+\)b" (y, z)' > matches_6.mfotl
  $ monpoly -sig matches.sig -formula matches_6.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND x MATCHES r"\(z\)*\(a+\)b" (y, z)
  The sequence of free variables is: (x,y,z)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ()
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): (("zab","z","a"))
  At time point 4:
  @4 (time point 4): (("zzzab","z","a"))

  $ echo 'P(x) AND Q(y) AND x MATCHES r"\(z*\)\(a+\)b" (y, z)' > matches_7.mfotl
  $ monpoly -sig matches.sig -formula matches_7.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    (P(x) AND Q(y)) AND x MATCHES r"\(z*\)\(a+\)b" (y, z)
  The sequence of free variables is: (x,y,z)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ()
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): ()
  At time point 4:
  @4 (time point 4): (("zzzab","zzz","a"))

  $ echo 'P(x) AND x MATCHES r"\(a\)\(a*\)b" (y, y)' > matches_8.mfotl
  $ monpoly -sig matches.sig -formula matches_8.mfotl -log matches.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND x MATCHES r"\(a\)\(a*\)b" (y, y)
  The sequence of free variables is: (x,y)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): (("aabc","a"))
  At time point 2:
  @2 (time point 2): ()
  At time point 3:
  @3 (time point 3): ()
  At time point 4:
  @4 (time point 4): ()
