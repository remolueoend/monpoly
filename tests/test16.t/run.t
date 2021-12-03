  $ echo '0 = 0 SINCE[0,10] p(x)' > test16_1.mfotl
  $ monpoly -sig test16.sig -formula test16_1.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 SINCE[0,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ((0))
  At time point 1:
  @11 (time point 1): ((0),(1))
  At time point 2:
  @14 (time point 2): ((0),(1),(2))
  At time point 3:
  @14 (time point 3): ((0),(1),(2),(3))
  At time point 4:
  @33 (time point 4): ()

  $ echo '0 = 0 SINCE[1,10] p(x)' > test16_2.mfotl
  $ monpoly -sig test16.sig -formula test16_2.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 SINCE[1,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ()
  At time point 1:
  @11 (time point 1): ()
  At time point 2:
  @14 (time point 2): ((0),(1))
  At time point 3:
  @14 (time point 3): ((0),(1))
  At time point 4:
  @33 (time point 4): ()

  $ echo '0 = 0 SINCE[0,2] p(x)' > test16_3.mfotl
  $ monpoly -sig test16.sig -formula test16_3.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 SINCE[0,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ((0))
  At time point 1:
  @11 (time point 1): ((0),(1))
  At time point 2:
  @14 (time point 2): ((2))
  At time point 3:
  @14 (time point 3): ((2),(3))
  At time point 4:
  @33 (time point 4): ()

  $ echo '0 = 0 SINCE[1,2] p(x)' > test16_4.mfotl
  $ monpoly -sig test16.sig -formula test16_4.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 SINCE[1,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ()
  At time point 1:
  @11 (time point 1): ()
  At time point 2:
  @14 (time point 2): ()
  At time point 3:
  @14 (time point 3): ()
  At time point 4:
  @33 (time point 4): ()

  $ echo '(NOT 0 = 1) SINCE[0,10] p(x)' > test16_5.mfotl
  $ monpoly -sig test16.sig -formula test16_5.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) SINCE[0,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ((0))
  At time point 1:
  @11 (time point 1): ((0),(1))
  At time point 2:
  @14 (time point 2): ((0),(1),(2))
  At time point 3:
  @14 (time point 3): ((0),(1),(2),(3))
  At time point 4:
  @33 (time point 4): ()

  $ echo '(NOT 0 = 1) SINCE[1,10] p(x)' > test16_6.mfotl
  $ monpoly -sig test16.sig -formula test16_6.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) SINCE[1,10] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ()
  At time point 1:
  @11 (time point 1): ()
  At time point 2:
  @14 (time point 2): ((0),(1))
  At time point 3:
  @14 (time point 3): ((0),(1))
  At time point 4:
  @33 (time point 4): ()

  $ echo '(NOT 0 = 1) SINCE[0,2] p(x)' > test16_7.mfotl
  $ monpoly -sig test16.sig -formula test16_7.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) SINCE[0,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ((0))
  At time point 1:
  @11 (time point 1): ((0),(1))
  At time point 2:
  @14 (time point 2): ((2))
  At time point 3:
  @14 (time point 3): ((2),(3))
  At time point 4:
  @33 (time point 4): ()

  $ echo '(NOT 0 = 1) SINCE[1,2] p(x)' > test16_8.mfotl
  $ monpoly -sig test16.sig -formula test16_8.mfotl -log test16.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 1) SINCE[1,2] p(x)
  The sequence of free variables is: (x)
  At time point 0:
  @11 (time point 0): ()
  At time point 1:
  @11 (time point 1): ()
  At time point 2:
  @14 (time point 2): ()
  At time point 3:
  @14 (time point 3): ()
  At time point 4:
  @33 (time point 4): ()
