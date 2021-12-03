  $ echo 't <- MIN x S(x,y,z)' > test19_1.mfotl
  $ monpoly -sig test19.sig -formula test19_1.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MIN x S(x,y,z)
  The sequence of free variables is: (t)
  At time point 0:
  @0 (time point 0): ((1))

  $ echo 't <- MIN x;x S(x,y,z)' > test19_2.mfotl
  $ monpoly -sig test19.sig -formula test19_2.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MIN x; x S(x,y,z)
  The sequence of free variables is: (t,x)
  At time point 0:
  @0 (time point 0): ((1,1),(2,2),(4,4))

  $ echo 't <- MIN x;y S(x,y,z)' > test19_3.mfotl
  $ monpoly -sig test19.sig -formula test19_3.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MIN x; y S(x,y,z)
  The sequence of free variables is: (t,y)
  At time point 0:
  @0 (time point 0): ((1,10),(4,11))

  $ echo 't <- MIN x;y,z S(x,y,z)' > test19_4.mfotl
  $ monpoly -sig test19.sig -formula test19_4.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MIN x; y,z S(x,y,z)
  The sequence of free variables is: (t,y,z)
  At time point 0:
  @0 (time point 0): ((1,10,11),(1,10,12),(4,11,12))

  $ echo 't <- MIN x;x,y,z S(x,y,z)' > test19_5.mfotl
  $ monpoly -sig test19.sig -formula test19_5.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MIN x; x,y,z S(x,y,z)
  The sequence of free variables is: (t,x,y,z)
  At time point 0:
  @0 (time point 0): ((1,1,10,11),(1,1,10,12),(2,2,10,11),(4,4,11,12))

  $ echo 't <- MAX x S(x,y,z)' > test19_6.mfotl
  $ monpoly -sig test19.sig -formula test19_6.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MAX x S(x,y,z)
  The sequence of free variables is: (t)
  At time point 0:
  @0 (time point 0): ((4))

  $ echo 't <- MAX x;x S(x,y,z)' > test19_7.mfotl
  $ monpoly -sig test19.sig -formula test19_7.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MAX x; x S(x,y,z)
  The sequence of free variables is: (t,x)
  At time point 0:
  @0 (time point 0): ((1,1),(2,2),(4,4))

  $ echo 't <- MAX x;y S(x,y,z)' > test19_8.mfotl
  $ monpoly -sig test19.sig -formula test19_8.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MAX x; y S(x,y,z)
  The sequence of free variables is: (t,y)
  At time point 0:
  @0 (time point 0): ((2,10),(4,11))

  $ echo 't <- MAX x;y,z S(x,y,z)' > test19_9.mfotl
  $ monpoly -sig test19.sig -formula test19_9.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MAX x; y,z S(x,y,z)
  The sequence of free variables is: (t,y,z)
  At time point 0:
  @0 (time point 0): ((1,10,12),(2,10,11),(4,11,12))

  $ echo 't <- MAX x;x,y,z S(x,y,z)' > test19_10.mfotl
  $ monpoly -sig test19.sig -formula test19_10.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- MAX x; x,y,z S(x,y,z)
  The sequence of free variables is: (t,x,y,z)
  At time point 0:
  @0 (time point 0): ((1,1,10,11),(1,1,10,12),(2,2,10,11),(4,4,11,12))

  $ echo 't <- CNT x S(x,y,z)' > test19_11.mfotl
  $ monpoly -sig test19.sig -formula test19_11.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- CNT x S(x,y,z)
  The sequence of free variables is: (t)
  At time point 0:
  @0 (time point 0): ((4))

  $ echo 't <- CNT x;x S(x,y,z)' > test19_12.mfotl
  $ monpoly -sig test19.sig -formula test19_12.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- CNT x; x S(x,y,z)
  The sequence of free variables is: (t,x)
  At time point 0:
  @0 (time point 0): ((1,2),(1,4),(2,1))

  $ echo 't <- CNT x;y S(x,y,z)' > test19_13.mfotl
  $ monpoly -sig test19.sig -formula test19_13.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- CNT x; y S(x,y,z)
  The sequence of free variables is: (t,y)
  At time point 0:
  @0 (time point 0): ((1,11),(3,10))

  $ echo 't <- CNT x;y,z S(x,y,z)' > test19_14.mfotl
  $ monpoly -sig test19.sig -formula test19_14.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- CNT x; y,z S(x,y,z)
  The sequence of free variables is: (t,y,z)
  At time point 0:
  @0 (time point 0): ((1,10,12),(1,11,12),(2,10,11))

  $ echo 't <- CNT x;x,y,z S(x,y,z)' > test19_15.mfotl
  $ monpoly -sig test19.sig -formula test19_15.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- CNT x; x,y,z S(x,y,z)
  The sequence of free variables is: (t,x,y,z)
  At time point 0:
  @0 (time point 0): ((1,1,10,11),(1,1,10,12),(1,2,10,11),(1,4,11,12))

  $ echo 't <- SUM x S(x,y,z)' > test19_16.mfotl
  $ monpoly -sig test19.sig -formula test19_16.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- SUM x S(x,y,z)
  The sequence of free variables is: (t)
  At time point 0:
  @0 (time point 0): ((8))

  $ echo 't <- SUM x;x S(x,y,z)' > test19_17.mfotl
  $ monpoly -sig test19.sig -formula test19_17.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- SUM x; x S(x,y,z)
  The sequence of free variables is: (t,x)
  At time point 0:
  @0 (time point 0): ((2,1),(2,2),(4,4))

  $ echo 't <- SUM x;y S(x,y,z)' > test19_18.mfotl
  $ monpoly -sig test19.sig -formula test19_18.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- SUM x; y S(x,y,z)
  The sequence of free variables is: (t,y)
  At time point 0:
  @0 (time point 0): ((4,10),(4,11))

  $ echo 't <- SUM x;y,z S(x,y,z)' > test19_19.mfotl
  $ monpoly -sig test19.sig -formula test19_19.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- SUM x; y,z S(x,y,z)
  The sequence of free variables is: (t,y,z)
  At time point 0:
  @0 (time point 0): ((1,10,12),(3,10,11),(4,11,12))

  $ echo 't <- SUM x;x,y,z S(x,y,z)' > test19_20.mfotl
  $ monpoly -sig test19.sig -formula test19_20.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- SUM x; x,y,z S(x,y,z)
  The sequence of free variables is: (t,x,y,z)
  At time point 0:
  @0 (time point 0): ((1,1,10,11),(1,1,10,12),(2,2,10,11),(4,4,11,12))

  $ echo 't <- AVG x S(x,y,z)' > test19_21.mfotl
  $ monpoly -sig test19.sig -formula test19_21.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- AVG x S(x,y,z)
  The sequence of free variables is: (t)
  At time point 0:
  @0 (time point 0): ((2))

  $ echo 't <- AVG x;x S(x,y,z)' > test19_22.mfotl
  $ monpoly -sig test19.sig -formula test19_22.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- AVG x; x S(x,y,z)
  The sequence of free variables is: (t,x)
  At time point 0:
  @0 (time point 0): ((1,1),(2,2),(4,4))

  $ echo 't <- AVG x;y S(x,y,z)' > test19_23.mfotl
  $ monpoly -sig test19.sig -formula test19_23.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- AVG x; y S(x,y,z)
  The sequence of free variables is: (t,y)
  At time point 0:
  @0 (time point 0): ((1.33333,10),(4,11))

  $ echo 't <- AVG x;y,z S(x,y,z)' > test19_24.mfotl
  $ monpoly -sig test19.sig -formula test19_24.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- AVG x; y,z S(x,y,z)
  The sequence of free variables is: (t,y,z)
  At time point 0:
  @0 (time point 0): ((1,10,12),(1.5,10,11),(4,11,12))

  $ echo 't <- AVG x;x,y,z S(x,y,z)' > test19_25.mfotl
  $ monpoly -sig test19.sig -formula test19_25.mfotl -log test19.log -verbose -nonewlastts
  The analyzed formula is:
    t <- AVG x; x,y,z S(x,y,z)
  The sequence of free variables is: (t,x,y,z)
  At time point 0:
  @0 (time point 0): ((1,1,10,11),(1,1,10,12),(2,2,10,11),(4,4,11,12))
