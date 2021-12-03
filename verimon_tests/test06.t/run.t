  $ echo '0 = 0 UNTIL[0,10] p(x)' > test6_1.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_1.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 UNTIL[0,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @11 (time point 0): ((0),(1),(2),(3))
  @11 (time point 1): ((1),(2),(3))
  @14 (time point 2): ((2),(3))
  @14 (time point 3): ((3))

  $ echo '0 = 0 UNTIL[1,10] p(x)' > test6_2.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_2.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 UNTIL[1,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @11 (time point 0): ((2),(3))
  @11 (time point 1): ((2),(3))
  @14 (time point 2): ()
  @14 (time point 3): ()

  $ echo '0 = 0 UNTIL[0,2] p(x)' > test6_3.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_3.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 UNTIL[0,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @11 (time point 0): ((0),(1))
  @11 (time point 1): ((1))
  At time point 3:
  At time point 4:
  @14 (time point 2): ((2),(3))
  @14 (time point 3): ((3))

  $ echo '0 = 0 UNTIL[1,2] p(x)' > test6_4.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_4.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 UNTIL[1,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @11 (time point 0): ()
  @11 (time point 1): ()
  At time point 3:
  At time point 4:
  @14 (time point 2): ()
  @14 (time point 3): ()

  $ echo '(NOT 0 = 1) UNTIL[0,10] p(x)' > test6_5.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_5.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) UNTIL[0,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @11 (time point 0): ((0),(1),(2),(3))
  @11 (time point 1): ((1),(2),(3))
  @14 (time point 2): ((2),(3))
  @14 (time point 3): ((3))

  $ echo '(NOT 0 = 1) UNTIL[1,10] p(x)' > test6_6.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_6.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) UNTIL[1,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @11 (time point 0): ((2),(3))
  @11 (time point 1): ((2),(3))
  @14 (time point 2): ()
  @14 (time point 3): ()

  $ echo '(NOT 0 = 1) UNTIL[0,2] p(x)' > test6_7.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_7.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) UNTIL[0,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @11 (time point 0): ((0),(1))
  @11 (time point 1): ((1))
  At time point 3:
  At time point 4:
  @14 (time point 2): ((2),(3))
  @14 (time point 3): ((3))

  $ echo '(NOT 0 = 1) UNTIL[1,2] p(x)' > test6_8.mfotl
  $ monpoly -verified -sig test6.sig -formula test6_8.mfotl -log test6.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) UNTIL[1,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @11 (time point 0): ()
  @11 (time point 1): ()
  At time point 3:
  At time point 4:
  @14 (time point 2): ()
  @14 (time point 3): ()
