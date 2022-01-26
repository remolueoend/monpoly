  $ echo 'S(a,b,c) AND (a = b + 2)' > test18_1.mfotl
  $ monpoly -sig test18.sig -formula test18_1.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND a = b + 2
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,8,0))
  At time point 1:
  @200 (time point 1): ()

  $ echo 'S(a,b,c) AND (a = 1 + b + 2)' > test18_2.mfotl
  $ monpoly -sig test18.sig -formula test18_2.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND a = (1 + b) + 2
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,7,0))
  At time point 1:
  @200 (time point 1): ()

  $ echo 'S(a,b,c) AND (a + 1 = 1 + b)' > test18_3.mfotl
  $ monpoly -sig test18.sig -formula test18_3.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND a + 1 = 1 + b
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,10,1))
  At time point 1:
  @200 (time point 1): ()

  $ echo 'S(a,b,c) AND (a = b + c)' > test18_4.mfotl
  $ monpoly -sig test18.sig -formula test18_4.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND a = b + c
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,4,6))
  At time point 1:
  @200 (time point 1): ()

  $ echo 'S(a,b,c) AND (a + c = b + a)' > test18_5.mfotl
  $ monpoly -sig test18.sig -formula test18_5.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND a + c = b + a
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,3,3))
  At time point 1:
  @200 (time point 1): ()

  $ echo 'S(a,b,c) AND (x = 1 + b + c)' > test18_6.mfotl
  $ monpoly -sig test18.sig -formula test18_6.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND x = (1 + b) + c
  The sequence of free variables is: (a,b,c,x)
  At time point 0:
  @100 (time point 0): ((10,1,2,4),(10,3,3,7),(10,4,6,11),(10,7,0,8),(10,8,0,9),(10,10,1,12))
  At time point 1:
  @200 (time point 1): ((10,0,1,2))

  $ echo 'S(a,b,c) AND (x = a + b + c)' > test18_7.mfotl
  $ monpoly -sig test18.sig -formula test18_7.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND x = (a + b) + c
  The sequence of free variables is: (a,b,c,x)
  At time point 0:
  @100 (time point 0): ((10,1,2,13),(10,3,3,16),(10,4,6,20),(10,7,0,17),(10,8,0,18),(10,10,1,21))
  At time point 1:
  @200 (time point 1): ((10,0,1,11))

  $ echo 'S(a,b,c) AND (x + 1 = b + c)' > test18_8.mfotl
  $ monpoly -sig test18.sig -formula test18_8.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND x + 1 = b + c
  The sequence of free variables is: (a,b,c,x)
  The analyzed formula is NOT monitorable, because of the subformula:
    S(a,b,c) AND x + 1 = b + c
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

  $ echo 'S(a,b,c) AND (x = a * a - 2 * b + c)' > test18_9.mfotl
  $ monpoly -sig test18.sig -formula test18_9.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND x = ((a * a) - (2 * b)) + c
  The sequence of free variables is: (a,b,c,x)
  At time point 0:
  @100 (time point 0): ((10,1,2,100),(10,3,3,97),(10,4,6,98),(10,7,0,86),(10,8,0,84),(10,10,1,81))
  At time point 1:
  @200 (time point 1): ((10,0,1,101))

  $ echo 'S(a,b,c) AND (x = a / b)' > test18_10.mfotl
  $ monpoly -sig test18.sig -formula test18_10.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND x = a / b
  The sequence of free variables is: (a,b,c,x)
  At time point 0:
  @100 (time point 0): ((10,1,2,10),(10,3,3,3),(10,4,6,2),(10,7,0,1),(10,8,0,1),(10,10,1,1))
  At time point 1:
  Fatal error: exception Division_by_zero
  [2]

  $ echo 'S(a,b,c) AND NOT (a = b + 2)' > test18_11.mfotl
  $ monpoly -sig test18.sig -formula test18_11.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    S(a,b,c) AND (NOT a = b + 2)
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,1,2),(10,3,3),(10,4,6),(10,7,0),(10,10,1))
  At time point 1:
  @200 (time point 1): ((10,0,1))

  $ echo 'S(a,b,c) AND NOT b = 0 AND a / b - c = 8' > test18_12.mfotl
  $ monpoly -sig test18.sig -formula test18_12.mfotl -log test18.log -verbose -nonewlastts
  The analyzed formula is:
    (S(a,b,c) AND (NOT b = 0)) AND (a / b) - c = 8
  The sequence of free variables is: (a,b,c)
  At time point 0:
  @100 (time point 0): ((10,1,2))
  At time point 1:
  @200 (time point 1): ()
