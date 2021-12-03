  $ echo 'ONCE[0,10] p(x)' > test17_1.mfotl
  $ monpoly -sig test17.sig -formula test17_1.mfotl -log test17.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[0,10] p(x)
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

  $ echo 'ONCE[1,10] p(x)' > test17_2.mfotl
  $ monpoly -sig test17.sig -formula test17_2.mfotl -log test17.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[1,10] p(x)
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

  $ echo 'ONCE[0,2] p(x)' > test17_3.mfotl
  $ monpoly -sig test17.sig -formula test17_3.mfotl -log test17.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[0,2] p(x)
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

  $ echo 'ONCE[1,2] p(x)' > test17_4.mfotl
  $ monpoly -sig test17.sig -formula test17_4.mfotl -log test17.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[1,2] p(x)
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
