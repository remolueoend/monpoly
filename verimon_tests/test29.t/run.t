  $ echo '(r <- AVG x (I(x))) AND t = f2i(r)' > test29_1.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_1.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- AVG x I(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((7.5,7))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- SUM x (I(x))) AND t = i2f(r)' > test29_2.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_2.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- SUM x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((15,15))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- CNT x (I(x))) AND t = i2f(r)' > test29_3.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_3.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((2,2))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- MIN x (I(x))) AND t = i2f(r)' > test29_4.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_4.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MIN x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((7,7))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- MAX x (I(x))) AND t = i2f(r)' > test29_5.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_5.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MAX x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((8,8))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- MED x (I(x))) AND t = f2i(r)' > test29_6.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_6.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MED x I(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((7.5,7))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- AVG x (F(x))) AND t = f2i(r)' > test29_7.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_7.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- AVG x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((0,0))
  At time point 1:
  @0 (time point 1): ((7.5,7))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- SUM x (F(x))) AND t = f2i(r)' > test29_8.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_8.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- SUM x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((0,0))
  At time point 1:
  @0 (time point 1): ((15,15))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- CNT x (F(x))) AND t = i2f(r)' > test29_9.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_9.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x F(x)) AND t = i2f(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((0,0))
  At time point 1:
  @0 (time point 1): ((2,2))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- MIN x (F(x))) AND t = f2i(r)' > test29_10.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_10.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MIN x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  Fatal error: exception Z.Overflow
  [2]

  $ echo '(r <- MAX x (F(x))) AND t = f2i(r)' > test29_11.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_11.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MAX x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  Fatal error: exception Z.Overflow
  [2]

  $ echo '(r <- MED x (F(x))) AND t = f2i(r)' > test29_12.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_12.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MED x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((0,0))
  At time point 1:
  @0 (time point 1): ((7.5,7))
  At time point 2:
  @0 (time point 2): ((0,0))

  $ echo '(r <- AVG x (W(x)))' > test29_13.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_13.mfotl -log test29.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term x: expected type String, actual type (Num t3) =>  t3")
  [2]

  $ echo '(r <- SUM x (W(x)))' > test29_14.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_14.mfotl -log test29.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term x: expected type String, actual type (Num t3) =>  t3")
  [2]

  $ echo '(r <- CNT x (W(x))) AND t = i2f(r)' > test29_15.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_15.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x W(x)) AND t = i2f(r)
  The sequence of free variables is: (r,t)
  At time point 0:
  @0 (time point 0): ((0,0))
  At time point 1:
  @0 (time point 1): ((0,0))
  At time point 2:
  @0 (time point 2): ((2,2))

  $ echo '(r <- MIN x (W(x)))' > test29_16.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_16.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    r <- MIN x W(x)
  The sequence of free variables is: (r)
  At time point 0:
  @0 (time point 0): ((""))
  At time point 1:
  @0 (time point 1): ((""))
  At time point 2:
  @0 (time point 2): (("no"))

  $ echo '(r <- MAX x (W(x)))' > test29_17.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_17.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    r <- MAX x W(x)
  The sequence of free variables is: (r)
  At time point 0:
  @0 (time point 0): ((""))
  At time point 1:
  @0 (time point 1): ((""))
  At time point 2:
  @0 (time point 2): (("yes"))

  $ echo '(r <- MED x (W(x)))' > test29_18.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_18.mfotl -log test29.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term x: expected type String, actual type (Num t3) =>  t3")
  [2]

  $ echo '(r <- AVG x ; x (I(x))) AND t = f2i(r)' > test29_19.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_19.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- AVG x; x I(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ((7,7,7),(8,8,8))
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- SUM x ; x (I(x))) AND t = i2f(r)' > test29_20.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_20.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- SUM x; x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ((7,7,7),(8,8,8))
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- CNT x ; x (I(x))) AND t = i2f(r)' > test29_21.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_21.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x; x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ((1,7,1),(1,8,1))
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- MIN x ; x (I(x))) AND t = i2f(r)' > test29_22.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_22.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MIN x; x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ((7,7,7),(8,8,8))
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- MAX x ; x (I(x))) AND t = i2f(r)' > test29_23.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_23.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MAX x; x I(x)) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ((7,7,7),(8,8,8))
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- MED x ; x (I(x))) AND t = f2i(r)' > test29_24.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_24.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MED x; x I(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ((7,7,7),(8,8,8))
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- AVG x ; x (F(x))) AND t = f2i(r)' > test29_25.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_25.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- AVG x; x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ((7,7,7),(8,8,8))
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- SUM x ; x (F(x))) AND t = f2i(r)' > test29_26.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_26.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- SUM x; x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ((7,7,7),(8,8,8))
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- CNT x ; x (F(x))) AND t = i2f(r)' > test29_27.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_27.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x; x F(x)) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ((1,7,1),(1,8,1))
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- MIN x ; x (F(x))) AND t = f2i(r)' > test29_28.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_28.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MIN x; x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ((7,7,7),(8,8,8))
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- MAX x ; x (F(x))) AND t = f2i(r)' > test29_29.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_29.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MAX x; x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ((7,7,7),(8,8,8))
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- MED x ; x (F(x))) AND t = f2i(r)' > test29_30.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_30.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- MED x; x F(x)) AND t = f2i(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ((7,7,7),(8,8,8))
  At time point 2:
  @0 (time point 2): ()

  $ echo '(r <- AVG x ; x (W(x)))' > test29_31.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_31.mfotl -log test29.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term x: expected type String, actual type (Num t3) =>  t3")
  [2]

  $ echo '(r <- SUM x ; x (W(x)))' > test29_32.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_32.mfotl -log test29.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term x: expected type String, actual type (Num t3) =>  t3")
  [2]

  $ echo '(r <- CNT x ; x (W(x))) AND t = i2f(r)' > test29_33.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_33.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    (r <- CNT x; x W(x)) AND t = i2f(r)
  The sequence of free variables is: (r,x,t)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): ((1,"no",1),(1,"yes",1))

  $ echo '(r <- MIN x ; x (W(x)))' > test29_34.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_34.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    r <- MIN x; x W(x)
  The sequence of free variables is: (r,x)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): (("no","no"),("yes","yes"))

  $ echo '(r <- MAX x ; x (W(x)))' > test29_35.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_35.mfotl -log test29.log -verbose -nonewlastts
  The analyzed formula is:
    r <- MAX x; x W(x)
  The sequence of free variables is: (r,x)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @0 (time point 1): ()
  At time point 2:
  @0 (time point 2): (("no","no"),("yes","yes"))

  $ echo '(r <- MED x ; x (W(x)))' > test29_36.mfotl
  $ monpoly -verified -sig test29.sig -formula test29_36.mfotl -log test29.log -verbose -nonewlastts
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term x: expected type String, actual type (Num t3) =>  t3")
  [2]
