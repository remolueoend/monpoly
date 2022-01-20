  $ echo '(Q(a) AND (0 = 0 UNTIL[0,50] P(b)))' > test8_1.mfotl
  $ monpoly -verified -sig test8.sig -formula test8_1.mfotl -log test8.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    Q(a) AND (0 = 0 UNTIL[0,50] P(b))
  The sequence of free variables is: (a,b)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @10 (time point 0): ()
  @20 (time point 1): ()
  @30 (time point 2): ((3,4))
  @40 (time point 3): ()

  $ echo '(Q(a) AND (EVENTUALLY[0,50] P(b)))' > test8_2.mfotl
  $ monpoly -verified -sig test8.sig -formula test8_2.mfotl -log test8.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    Q(a) AND (EVENTUALLY[0,50] P(b))
  The sequence of free variables is: (a,b)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  @10 (time point 0): ()
  @20 (time point 1): ()
  @30 (time point 2): ((3,4))
  @40 (time point 3): ()
