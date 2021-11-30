  $ echo 'P(x) AND Q(x)' > test1_1.mfotl
  $ monpoly -sig test1.sig -formula test1_1.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) AND Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((3),(4))
  At time point 1:
  @110 (time point 1): ((4))
  At time point 2:
  @120 (time point 2): ((5))
  At time point 3:
  @130 (time point 3): ()

  $ echo 'P(x) OR Q(x)' > test1_2.mfotl
  $ monpoly -sig test1.sig -formula test1_2.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) OR Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4),(6))
  At time point 1:
  @110 (time point 1): ((2),(3),(4),(6),(7))
  At time point 2:
  @120 (time point 2): ((2),(3),(5),(6),(8))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(9),(12),(14),(16))

A domain-dependent formula:
  $ echo 'P(x) OR Q(y)' > test1_3.mfotl
  $ monpoly -sig test1.sig -formula test1_3.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) OR Q(y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(x) OR Q(y)
  In subformulas of the form phi OR psi, phi and psi should have the same set of free variables.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

  $ echo '(EXISTS b. R(a,b)) AND P(a)' > test1_4.mfotl
  $ monpoly -sig test1.sig -formula test1_4.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    (EXISTS b. R(a,b)) AND P(a)
  The sequence of free variables is: (a)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3))
  At time point 2:
  @120 (time point 2): ((3),(5))
  At time point 3:
  @130 (time point 3): ((3),(5))

  $ echo '(EXISTS x. ((x=0) AND EXISTS x.P(x))) AND P(x)' > test1_5.mfotl
  $ monpoly -sig test1.sig -formula test1_5.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    (EXISTS x. (x = 0 AND (EXISTS x. P(x)))) AND P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4))
  At time point 1:
  @110 (time point 1): ((3),(4),(7))
  At time point 2:
  @120 (time point 2): ((3),(5),(8))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(9))

  $ echo 'T()' > test1_6.mfotl
  $ monpoly -sig test1.sig -formula test1_6.mfotl -log test1.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T()
  The sequence of free variables is: ()
  At time point 0:
  @100 (time point 0): true
  At time point 1:
  @110 (time point 1): false
  At time point 2:
  @120 (time point 2): false
  At time point 3:
  @130 (time point 3): false

  $ echo 'R(y,x)' > test1_7.mfotl
  $ monpoly -sig test1.sig -formula test1_7.mfotl -log test1.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    R(y,x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3,5),(5,0))
  At time point 2:
  @120 (time point 2): ((3,5),(5,0))
  At time point 3:
  @130 (time point 3): ((3,5),(5,0))

  $ echo 'P(x)' > test1_8.mfotl
  $ monpoly -sig test1.sig -formula test1_8.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4))
  At time point 1:
  @110 (time point 1): ((3),(4),(7))
  At time point 2:
  @120 (time point 2): ((3),(5),(8))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(9))

  $ echo 'NEXT[0,30] P(x)' > test1_9.mfotl
  $ monpoly -sig test1.sig -formula test1_9.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((3),(4),(7))
  At time point 2:
  @110 (time point 1): ((3),(5),(8))
  At time point 3:
  @120 (time point 2): ((3),(5),(6),(9))

  $ echo 'PREVIOUS[0,30] P(x)' > test1_10.mfotl
  $ monpoly -sig test1.sig -formula test1_10.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((2),(3),(4))
  At time point 2:
  @120 (time point 2): ((3),(4),(7))
  At time point 3:
  @130 (time point 3): ((3),(5),(8))

  $ echo 'NEXT[0,30] NEXT[0,30] P(x)' > test1_11.mfotl
  $ monpoly -sig test1.sig -formula test1_11.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((3),(5),(8))
  At time point 3:
  @110 (time point 1): ((3),(5),(6),(9))

  $ echo 'NEXT[0,30] PREVIOUS[0,30] P(x)' > test1_12.mfotl
  $ monpoly -sig test1.sig -formula test1_12.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((2),(3),(4))
  At time point 2:
  @110 (time point 1): ((3),(4),(7))
  At time point 3:
  @120 (time point 2): ((3),(5),(8))

  $ echo 'PREVIOUS[0,30] PREVIOUS[0,30] P(x)' > test1_13.mfotl
  $ monpoly -sig test1.sig -formula test1_13.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ((2),(3),(4))
  At time point 3:
  @130 (time point 3): ((3),(4),(7))

  $ echo 'PREVIOUS[0,30] NEXT[0,30] P(x)' > test1_14.mfotl
  $ monpoly -sig test1.sig -formula test1_14.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3),(4),(7))
  At time point 2:
  @120 (time point 2): ((3),(5),(8))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(9))

  $ echo 'NEXT[0,30] NEXT[0,30] NEXT[0,30] P(x)' > test1_15.mfotl
  $ monpoly -sig test1.sig -formula test1_15.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] NEXT[0,30] NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  @100 (time point 0): ((3),(5),(6),(9))

  $ echo 'NEXT[0,30] NEXT[0,30] PREVIOUS[0,30] P(x)' > test1_16.mfotl
  $ monpoly -sig test1.sig -formula test1_16.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] NEXT[0,30] PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((3),(4),(7))
  At time point 3:
  @110 (time point 1): ((3),(5),(8))

  $ echo 'NEXT[0,30] PREVIOUS[0,30] NEXT[0,30] P(x)' > test1_17.mfotl
  $ monpoly -sig test1.sig -formula test1_17.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] PREVIOUS[0,30] NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((3),(4),(7))
  At time point 2:
  @110 (time point 1): ((3),(5),(8))
  At time point 3:
  @120 (time point 2): ((3),(5),(6),(9))

  $ echo 'NEXT[0,30] PREVIOUS[0,30] PREVIOUS[0,30] P(x)' > test1_18.mfotl
  $ monpoly -sig test1.sig -formula test1_18.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] PREVIOUS[0,30] PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ()
  At time point 2:
  @110 (time point 1): ((2),(3),(4))
  At time point 3:
  @120 (time point 2): ((3),(4),(7))

  $ echo 'PREVIOUS[0,30] NEXT[0,30] NEXT[0,30] P(x)' > test1_19.mfotl
  $ monpoly -sig test1.sig -formula test1_19.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] NEXT[0,30] NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  At time point 2:
  @110 (time point 1): ((3),(5),(8))
  At time point 3:
  @120 (time point 2): ((3),(5),(6),(9))

  $ echo 'PREVIOUS[0,30] NEXT[0,30] PREVIOUS[0,30] P(x)' > test1_20.mfotl
  $ monpoly -sig test1.sig -formula test1_20.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] NEXT[0,30] PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((2),(3),(4))
  At time point 2:
  @120 (time point 2): ((3),(4),(7))
  At time point 3:
  @130 (time point 3): ((3),(5),(8))

  $ echo 'PREVIOUS[0,30] PREVIOUS[0,30] NEXT[0,30] P(x)' > test1_21.mfotl
  $ monpoly -sig test1.sig -formula test1_21.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] PREVIOUS[0,30] NEXT[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ((3),(4),(7))
  At time point 3:
  @130 (time point 3): ((3),(5),(8))

  $ echo 'PREVIOUS[0,30] PREVIOUS[0,30] PREVIOUS[0,30] P(x)' > test1_22.mfotl
  $ monpoly -sig test1.sig -formula test1_22.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] PREVIOUS[0,30] PREVIOUS[0,30] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ()
  At time point 3:
  @130 (time point 3): ((2),(3),(4))

  $ echo 'P(x) SINCE[0,30] Q(x)' > test1_23.mfotl
  $ monpoly -sig test1.sig -formula test1_23.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) SINCE[0,30] Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((3),(4),(6))
  At time point 1:
  @110 (time point 1): ((2),(3),(4),(6))
  At time point 2:
  @120 (time point 2): ((2),(3),(5),(6))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(12),(14),(16))

  $ echo 'P(x) SINCE[1,10] R(y,x)' > test1_24.mfotl
  $ monpoly -sig test1.sig -formula test1_24.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) SINCE[1,10] R(y,x)
  The sequence of free variables is: (y,x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ((3,5))
  At time point 3:
  @130 (time point 3): ((3,5))

  $ echo '(0=0) SINCE[0,*] P(x)' > test1_25.mfotl
  $ monpoly -sig test1.sig -formula test1_25.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 SINCE[0,*) P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4))
  At time point 1:
  @110 (time point 1): ((2),(3),(4),(7))
  At time point 2:
  @120 (time point 2): ((2),(3),(4),(5),(7),(8))
  At time point 3:
  @130 (time point 3): ((2),(3),(4),(5),(6),(7),(8),(9))

  $ echo 'ONCE[0,0] P(x)' > test1_26.mfotl
  $ monpoly -sig test1.sig -formula test1_26.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[0,0] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4))
  At time point 1:
  @110 (time point 1): ((3),(4),(7))
  At time point 2:
  @120 (time point 2): ((3),(5),(8))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(9))

  $ echo 'ONCE[0,10] P(x)' > test1_27.mfotl
  $ monpoly -sig test1.sig -formula test1_27.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[0,10] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4))
  At time point 1:
  @110 (time point 1): ((2),(3),(4),(7))
  At time point 2:
  @120 (time point 2): ((3),(4),(5),(7),(8))
  At time point 3:
  @130 (time point 3): ((3),(5),(6),(8),(9))

  $ echo 'ONCE[0,*] P(x)' > test1_28.mfotl
  $ monpoly -sig test1.sig -formula test1_28.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[0,*) P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((2),(3),(4))
  At time point 1:
  @110 (time point 1): ((2),(3),(4),(7))
  At time point 2:
  @120 (time point 2): ((2),(3),(4),(5),(7),(8))
  At time point 3:
  @130 (time point 3): ((2),(3),(4),(5),(6),(7),(8),(9))

  $ echo 'ONCE[1,10] P(x)' > test1_29.mfotl
  $ monpoly -sig test1.sig -formula test1_29.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[1,10] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((2),(3),(4))
  At time point 2:
  @120 (time point 2): ((3),(4),(7))
  At time point 3:
  @130 (time point 3): ((3),(5),(8))

  $ echo 'ONCE[1,9] P(x)' > test1_30.mfotl
  $ monpoly -sig test1.sig -formula test1_30.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    ONCE[1,9] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ()
  At time point 3:
  @130 (time point 3): ()

  $ echo 'NEXT[0,30] (P(x) SINCE[0,30] Q(x))' > test1_31.mfotl
  $ monpoly -sig test1.sig -formula test1_31.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] (P(x) SINCE[0,30] Q(x))
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((2),(3),(4),(6))
  At time point 2:
  @110 (time point 1): ((2),(3),(5),(6))
  At time point 3:
  @120 (time point 2): ((3),(5),(6),(12),(14),(16))

  $ echo 'PREVIOUS[0,30] (P(x) SINCE[0,30] Q(x))' > test1_32.mfotl
  $ monpoly -sig test1.sig -formula test1_32.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] (P(x) SINCE[0,30] Q(x))
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3),(4),(6))
  At time point 2:
  @120 (time point 2): ((2),(3),(4),(6))
  At time point 3:
  @130 (time point 3): ((2),(3),(5),(6))

  $ echo 'P(x) SINCE[0,30] NEXT[0,30] Q(x)' > test1_33.mfotl
  $ monpoly -sig test1.sig -formula test1_33.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) SINCE[0,30] NEXT[0,30] Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((2),(4),(6))
  At time point 2:
  @110 (time point 1): ((2),(4),(5),(6))
  At time point 3:
  @120 (time point 2): ((5),(12),(14),(16))

  $ echo 'P(x) SINCE[0,30] PREVIOUS[0,30] Q(x)' > test1_34.mfotl
  $ monpoly -sig test1.sig -formula test1_34.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) SINCE[0,30] PREVIOUS[0,30] Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ((3),(4),(6))
  At time point 2:
  @120 (time point 2): ((2),(3),(4),(6))
  At time point 3:
  @130 (time point 3): ((2),(3),(5),(6))

  $ echo 'PREVIOUS[0,30] PREVIOUS[0,30] (P(x) SINCE[0,30] Q(x))' > test1_35.mfotl
  $ monpoly -sig test1.sig -formula test1_35.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    PREVIOUS[0,30] PREVIOUS[0,30] (P(x) SINCE[0,30] Q(x))
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @110 (time point 1): ()
  At time point 2:
  @120 (time point 2): ((3),(4),(6))
  At time point 3:
  @130 (time point 3): ((2),(3),(4),(6))

  $ echo 'P(x) UNTIL[0,10] Q(x)' > test1_36.mfotl
  $ monpoly -sig test1.sig -formula test1_36.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) UNTIL[0,10] Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((2),(3),(4),(6))
  At time point 3:
  @110 (time point 1): ((2),(4),(6))

  $ echo 'P(x) UNTIL[1,10] R(x,y)' > test1_37.mfotl
  $ monpoly -sig test1.sig -formula test1_37.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) UNTIL[1,10] R(x,y)
  The sequence of free variables is: (x,y)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((3,5))
  At time point 3:
  @110 (time point 1): ((3,5))

  $ echo 'NEXT[0,30] (P(x) UNTIL[0,10] Q(x))' > test1_38.mfotl
  $ monpoly -sig test1.sig -formula test1_38.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] (P(x) UNTIL[0,10] Q(x))
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:
  @100 (time point 0): ((2),(4),(6))

  $ echo 'NEXT[0,30] NEXT[0,30] (P(x) UNTIL[0,10] Q(x))' > test1_39.mfotl
  $ monpoly -sig test1.sig -formula test1_39.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    NEXT[0,30] NEXT[0,30] (P(x) UNTIL[0,10] Q(x))
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  At time point 3:

  $ echo 'P(x) UNTIL[1,9] Q(x)' > test1_40.mfotl
  $ monpoly -sig test1.sig -formula test1_40.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    P(x) UNTIL[1,9] Q(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ()
  At time point 2:
  @110 (time point 1): ()
  At time point 3:
  @120 (time point 2): ()

  $ echo '(NOT P(x)) UNTIL[0,10] R(x,y)' > test1_41.mfotl
  $ monpoly -sig test1.sig -formula test1_41.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT P(x)) UNTIL[0,10] R(x,y)
  The sequence of free variables is: (x,y)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((5,0))
  At time point 3:
  @110 (time point 1): ((3,5),(5,0))

  $ echo '(NOT P(x)) UNTIL[1,10] R(x,y)' > test1_42.mfotl
  $ monpoly -sig test1.sig -formula test1_42.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT P(x)) UNTIL[1,10] R(x,y)
  The sequence of free variables is: (x,y)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((5,0))
  At time point 3:
  @110 (time point 1): ((5,0))

  $ echo '(NOT P(x)) UNTIL[0,9] R(x,y)' > test1_43.mfotl
  $ monpoly -sig test1.sig -formula test1_43.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT P(x)) UNTIL[0,9] R(x,y)
  The sequence of free variables is: (x,y)
  At time point 0:
  At time point 1:
  @100 (time point 0): ()
  At time point 2:
  @110 (time point 1): ((3,5),(5,0))
  At time point 3:
  @120 (time point 2): ((3,5),(5,0))

  $ echo '(NOT P(x)) UNTIL[1,9] R(x,y)' > test1_44.mfotl
  $ monpoly -sig test1.sig -formula test1_44.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    (NOT P(x)) UNTIL[1,9] R(x,y)
  The sequence of free variables is: (x,y)
  At time point 0:
  At time point 1:
  @100 (time point 0): ()
  At time point 2:
  @110 (time point 1): ()
  At time point 3:
  @120 (time point 2): ()

  $ echo '0 = 0 UNTIL[0,0] P(x)' > test1_45.mfotl
  $ monpoly -sig test1.sig -formula test1_45.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    0 = 0 UNTIL[0,0] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((2),(3),(4))
  At time point 2:
  @110 (time point 1): ((3),(4),(7))
  At time point 3:
  @120 (time point 2): ((3),(5),(8))

  $ echo 'EVENTUALLY[0,0] P(x)' > test1_46.mfotl
  $ monpoly -sig test1.sig -formula test1_46.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[0,0] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ((2),(3),(4))
  At time point 2:
  @110 (time point 1): ((3),(4),(7))
  At time point 3:
  @120 (time point 2): ((3),(5),(8))

  $ echo 'EVENTUALLY[0,10] P(x)' > test1_47.mfotl
  $ monpoly -sig test1.sig -formula test1_47.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[0,10] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((2),(3),(4),(7))
  At time point 3:
  @110 (time point 1): ((3),(4),(5),(7),(8))

  $ echo 'EVENTUALLY[1,10] P(x)' > test1_48.mfotl
  $ monpoly -sig test1.sig -formula test1_48.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[1,10] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((3),(4),(7))
  At time point 3:
  @110 (time point 1): ((3),(5),(8))

  $ echo 'EVENTUALLY[1,9] P(x)' > test1_49.mfotl
  $ monpoly -sig test1.sig -formula test1_49.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[1,9] P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  @100 (time point 0): ()
  At time point 2:
  @110 (time point 1): ()
  At time point 3:
  @120 (time point 2): ()

  $ echo 'EVENTUALLY[1,10] NEXT P(x)' > test1_50.mfotl
  $ monpoly -sig test1.sig -formula test1_50.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[1,10] NEXT[0,*) P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((3),(5),(8))
  At time point 3:
  @110 (time point 1): ((3),(5),(6),(9))

  $ echo 'EVENTUALLY[1,10] PREVIOUS P(x)' > test1_51.mfotl
  $ monpoly -sig test1.sig -formula test1_51.mfotl -log test1.log -verbose -nonewlastts
  The analyzed formula is:
    EVENTUALLY[1,10] PREVIOUS[0,*) P(x)
  The sequence of free variables is: (x)
  At time point 0:
  At time point 1:
  At time point 2:
  @100 (time point 0): ((2),(3),(4))
  At time point 3:
  @110 (time point 1): ((3),(4),(7))
