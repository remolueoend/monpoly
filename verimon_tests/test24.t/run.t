  $ echo 'TRUE UNTIL[0,0] r()' > test24_1.mfotl
  $ monpoly -verified -sig test24.sig -formula test24_1.mfotl -log test24.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 UNTIL[0,0] r()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  @0 (time point 0): true
  At time point 2:
  At time point 3:
  @2 (time point 1): false
  @2 (time point 2): false

  $ echo 'NOT TRUE UNTIL[0,0] r()' > test24_2.mfotl
  $ monpoly -verified -sig test24.sig -formula test24_2.mfotl -log test24.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT 0 = 0) UNTIL[0,0] r()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  @0 (time point 0): true
  At time point 2:
  At time point 3:
  @2 (time point 1): false
  @2 (time point 2): false

  $ echo '(NEXT NEXT s()) UNTIL[0,0] r()' > test24_3.mfotl
  $ monpoly -verified -sig test24.sig -formula test24_3.mfotl -log test24.log -verbose -nonewlastts
  The analyzed formula is:
    (NEXT[0,*) NEXT[0,*) s()) UNTIL[0,0] r()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  At time point 2:
  @0 (time point 0): true
  At time point 3:

  $ echo 'NOT (NEXT[0,0] NEXT[0,0] s()) UNTIL[0,0] r()' > test24_4.mfotl
  $ monpoly -verified -sig test24.sig -formula test24_4.mfotl -log test24.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT NEXT[0,0] NEXT[0,0] s()) UNTIL[0,0] r()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  At time point 2:
  @0 (time point 0): true
  At time point 3:

  $ echo 'NOT (NEXT[0,0] s() OR NEXT[0,0] r()) UNTIL[0,0] r()' > test24_5.mfotl
  $ monpoly -verified -sig test24.sig -formula test24_5.mfotl -log test24.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT NEXT[0,0] (s() OR NEXT[0,0] r())) UNTIL[0,0] r()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  At time point 2:
  @0 (time point 0): true
  At time point 3:

  $ echo 'NOT ((NEXT[0,0] r()) OR NEXT[0,0] s()) UNTIL[0,0] r()' > test24_6.mfotl
  $ monpoly -verified -sig test24.sig -formula test24_6.mfotl -log test24.log -verbose -nonewlastts
  The input formula is:
    (NOT ((NEXT[0,0] r()) OR NEXT[0,0] s())) UNTIL[0,0] r()
  The analyzed formula is:
    ((NOT NEXT[0,0] r()) AND (NOT NEXT[0,0] s())) UNTIL[0,0] r()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  @0 (time point 0): true
  At time point 2:
  At time point 3:
  @2 (time point 1): false
  @2 (time point 2): false
