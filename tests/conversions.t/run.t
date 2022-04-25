  $ echo 'EXISTS x. Int(x) AND y = i2s(x)' > conversions_1.mfotl
  $ monpoly -sig conversions.sig -formula conversions_1.mfotl -log conversions.log -verbose -nonewlastts
  The analyzed formula is:
    EXISTS x. (Int(x) AND y = i2s(x))
  The sequence of free variables is: (y)
  At time point 0:
  @0 (time point 0): (("-42"),("0"),("1"),("987654321"))

  $ echo 'EXISTS x. Str(x) AND y = s2i(x)' > conversions_2.mfotl
  $ monpoly -sig conversions.sig -formula conversions_2.mfotl -log conversions.log -verbose -nonewlastts
  The analyzed formula is:
    EXISTS x. (Str(x) AND y = s2i(x))
  The sequence of free variables is: (y)
  At time point 1:
  @1 (time point 1): ((-42),(0),(1),(98754321))
  At time point 3:
  @3 (time point 3): ((-42),(0))

  $ echo 'EXISTS x. Float(x) AND y = f2s(x)' > conversions_3.mfotl
  $ monpoly -sig conversions.sig -formula conversions_3.mfotl -log conversions.log -verbose -nonewlastts
  The analyzed formula is:
    EXISTS x. (Float(x) AND y = f2s(x))
  The sequence of free variables is: (y)
  At time point 2:
  @2 (time point 2): (("-42."),("0.5"),("1.1"),("9.87654321e+30"))

  $ echo 'EXISTS x. Str(x) AND y = s2f(x)' > conversions_4.mfotl
  $ monpoly -sig conversions.sig -formula conversions_4.mfotl -log conversions.log -verbose -nonewlastts
  The analyzed formula is:
    EXISTS x. (Str(x) AND y = s2f(x))
  The sequence of free variables is: (y)
  At time point 1:
  @1 (time point 1): ((-42),(0),(1),(9.87543e+07))
  At time point 3:
  @3 (time point 3): ((-42),(0.5),(1.1),(9.87654e+30))

