  $ echo 'A(x) UNTIL[1,10] (B(x) UNTIL[1,1] C(x))' > test37_1.mfotl
  $ monpoly -sig test37.sig -formula test37_1.mfotl -log test37.log
  @0 (time point 0): (1)
  @1 (time point 1): (1)
  @2 (time point 2): (1)

  $ echo 'A(x) UNTIL[1,10] B(x)' > test37_2.mfotl
  $ monpoly -sig test37.sig -formula test37_2.mfotl -log test37.log
  @0 (time point 0): (1)
  @1 (time point 1): (1)
  @2 (time point 2): (1)
