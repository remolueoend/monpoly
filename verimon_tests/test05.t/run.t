  $ echo 'R(x,y) AND ( 0 =  0)' > test5_1.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_1.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND 0 = 0
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND ( 0 =  3)' > test5_2.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_2.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND 0 = 3
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND (x =  0)' > test5_3.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_3.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x = 0
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4))

  $ echo 'R(x,y) AND ( 0 = x)' > test5_4.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_4.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND 0 = x
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4))

  $ echo 'R(x,y) AND (x = x)' > test5_5.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_5.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x = x
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND (x = y)' > test5_6.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_6.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x = y
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(4,4))

  $ echo 'R(x,y) AND ( 0 <  0)' > test5_7.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_7.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND 0 < 0
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND ( 0 <  3)' > test5_8.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_8.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND 0 < 3
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND (x <  0)' > test5_9.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_9.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x < 0
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND (x <  3)' > test5_10.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_10.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x < 3
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4))

  $ echo 'R(x,y) AND ( 0 < x)' > test5_11.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_11.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND 0 < x
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((4,0),(4,4))

  $ echo 'R(x,y) AND (x < x)' > test5_12.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_12.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x < x
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND (x < y)' > test5_13.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_13.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND x < y
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,4))

  $ echo 'R(y,x) AND (x =  0)' > test5_14.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_14.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x = 0
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(4,0))

  $ echo 'R(y,x) AND ( 0 = x)' > test5_15.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_15.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND 0 = x
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(4,0))

  $ echo 'R(y,x) AND (x = x)' > test5_16.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_16.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x = x
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(y,x) AND (x = y)' > test5_17.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_17.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x = y
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(4,4))

  $ echo 'R(y,x) AND (x <  0)' > test5_18.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_18.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x < 0
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(y,x) AND (x <  3)' > test5_19.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_19.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x < 3
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(4,0))

  $ echo 'R(y,x) AND ( 0 < x)' > test5_20.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_20.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND 0 < x
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,4),(4,4))

  $ echo 'R(y,x) AND (x < x)' > test5_21.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_21.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x < x
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(y,x) AND (x < y)' > test5_22.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_22.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND x < y
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((4,0))

  $ echo 'R(x,y) AND NOT ( 0 =  0)' > test5_23.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_23.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT 0 = 0)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND NOT ( 0 =  3)' > test5_24.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_24.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT 0 = 3)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND NOT (x =  0)' > test5_25.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_25.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x = 0)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((4,0),(4,4))

  $ echo 'R(x,y) AND NOT ( 0 = x)' > test5_26.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_26.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT 0 = x)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((4,0),(4,4))

  $ echo 'R(x,y) AND NOT (x = x)' > test5_27.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_27.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x = x)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND NOT (x = y)' > test5_28.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_28.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x = y)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,4),(4,0))

  $ echo 'R(x,y) AND NOT ( 0 <  0)' > test5_29.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_29.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT 0 < 0)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND NOT ( 0 <  3)' > test5_30.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_30.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT 0 < 3)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(x,y) AND NOT (x <  0)' > test5_31.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_31.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x < 0)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND NOT (x <  3)' > test5_32.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_32.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x < 3)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((4,0),(4,4))

  $ echo 'R(x,y) AND NOT ( 0 < x)' > test5_33.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_33.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT 0 < x)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4))

  $ echo 'R(x,y) AND NOT (x < x)' > test5_34.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_34.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x < x)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(x,y) AND NOT (x < y)' > test5_35.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_35.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(x,y) AND (NOT x < y)
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0),(4,0),(4,4))

  $ echo 'R(y,x) AND NOT (x =  0)' > test5_36.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_36.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x = 0)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,4),(4,4))

  $ echo 'R(y,x) AND NOT ( 0 = x)' > test5_37.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_37.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT 0 = x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,4),(4,4))

  $ echo 'R(y,x) AND NOT (x = x)' > test5_38.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_38.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x = x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ()

  $ echo 'R(y,x) AND NOT (x = y)' > test5_39.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_39.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x = y)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,4),(4,0))

  $ echo 'R(y,x) AND NOT (x <  0)' > test5_40.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_40.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x < 0)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(y,x) AND NOT (x <  3)' > test5_41.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_41.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x < 3)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,4),(4,4))

  $ echo 'R(y,x) AND NOT ( 0 < x)' > test5_42.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_42.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT 0 < x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(4,0))

  $ echo 'R(y,x) AND NOT (x < x)' > test5_43.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_43.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x < x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,0),(4,4))

  $ echo 'R(y,x) AND NOT (x < y)' > test5_44.mfotl
  $ monpoly -verified -sig test5.sig -formula test5_44.mfotl -log test5.log -verbose -nonewlastts
  The analyzed formula is:
    R(y,x) AND (NOT x < y)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ((0,0),(0,4),(4,4))
