  $ echo 'PREVIOUS T()' > test23_1.mfotl
  $ monpoly -verified -sig test23.sig -formula test23_1.mfotl -log test23.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,*) T()
  The sequence of free variables is: ()
  At time point 0:
  @0 (time point 0): false
  At time point 1:
  @1 (time point 1): true
  At time point 2:
  @2 (time point 2): true

  $ echo 'NEXT T()' > test23_2.mfotl
  $ monpoly -verified -sig test23.sig -formula test23_2.mfotl -log test23.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,*) T()
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  @0 (time point 0): true
  At time point 2:
  @1 (time point 1): false

  $ echo 'PREVIOUS TRUE' > test23_3.mfotl
  $ monpoly -verified -sig test23.sig -formula test23_3.mfotl -log test23.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,*) 0 = 0
  The sequence of free variables is: ()
  At time point 0:
  @0 (time point 0): false
  At time point 1:
  @1 (time point 1): true
  At time point 2:
  @2 (time point 2): true

  $ echo 'NEXT TRUE' > test23_4.mfotl
  $ monpoly -verified -sig test23.sig -formula test23_4.mfotl -log test23.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,*) 0 = 0
  The sequence of free variables is: ()
  At time point 0:
  At time point 1:
  @0 (time point 0): true
  At time point 2:
  @1 (time point 1): true
