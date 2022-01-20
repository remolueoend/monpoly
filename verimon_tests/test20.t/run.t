  $ echo 'trans(c,t,a) AND 2000 < a AND NOT (NOT (EXISTS t2, a2. trans(c,t2,a2) AND NOT EVENTUALLY[0,3] report(t2)) UNTIL[0,301] unflag(c))' > test20_1.mfotl
  $ monpoly -verified -sig test20.sig -formula test20_1.mfotl -log test20.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    (trans(c,t,a) AND 2000 < a) AND (NOT ((NOT EXISTS t2, a2. (trans(c,t2,a2) AND (NOT EVENTUALLY[0,3] report(t2)))) UNTIL[0,301] unflag(c)))
  The sequence of free variables is: (c,t,a)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  At time point 4:
  At time point 5:
  @41 (time point 0): ((2,4,2003))
  @42 (time point 1): ()
  @43 (time point 2): ()
  @44 (time point 3): ()
  @47 (time point 4): ()
