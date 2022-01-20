  $ echo 'S(a,b,c) AND (NOT ((b = 0)))' > test2_1.mfotl
  $ monpoly -sig test2.sig -formula test2_1.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND (NOT b = 0)
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3,5,1))
  At time point 2:
  @120 (time point 2): ((3,5,5))
  At time point 3:
  @130 (time point 3): ((1,2,3),(3,5,6))

  $ echo 'S(a,b,c) AND (NOT (b = c))' > test2_2.mfotl
  $ monpoly -sig test2.sig -formula test2_2.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND (NOT b = c)
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3,5,1),(5,0,2))
  At time point 2:
  @120 (time point 2): ((5,0,5))
  At time point 3:
  @130 (time point 3): ((1,2,3),(3,5,6),(5,0,5))

  $ echo 'S(a,b,c) AND (b = c)' > test2_3.mfotl
  $ monpoly -sig test2.sig -formula test2_3.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND b = c
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((0,0,0))
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ((3,5,5))
  At time point 3:
  @130 (time point 3): ()

  $ echo 'S(a,b,c) AND (b = 0)' > test2_4.mfotl
  $ monpoly -sig test2.sig -formula test2_4.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND b = 0
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((0,0,0))
  At time point 1:
  @110 (time point 1): ((5,0,2))
  At time point 2:
  @120 (time point 2): ((5,0,5))
  At time point 3:
  @130 (time point 3): ((5,0,5))

  $ echo 'S(a,b,c) AND (0 = b)' > test2_5.mfotl
  $ monpoly -sig test2.sig -formula test2_5.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND 0 = b
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((0,0,0))
  At time point 1:
  @110 (time point 1): ((5,0,2))
  At time point 2:
  @120 (time point 2): ((5,0,5))
  At time point 3:
  @130 (time point 3): ((5,0,5))

  $ echo 'S(a,b,c) AND (1 = 0)' > test2_6.mfotl
  $ monpoly -sig test2.sig -formula test2_6.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND 1 = 0
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ()
  At time point 3:
  @130 (time point 3): ()

  $ echo 'S(a,b,c) AND (0 = 0)' > test2_7.mfotl
  $ monpoly -sig test2.sig -formula test2_7.mfotl -log test2.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND 0 = 0
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((0,0,0))
  At time point 1:
  @110 (time point 1): ((3,5,1),(5,0,2))
  At time point 2:
  @120 (time point 2): ((3,5,5),(5,0,5))
  At time point 3:
  @130 (time point 3): ((1,2,3),(3,5,6),(5,0,5))
