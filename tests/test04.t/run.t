Safe-range:
  $ echo 'P(x) AND ( 0 =  0)' > test4_1.mfotl
  $ monpoly -sig test4.sig -formula test4_1.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND 0 = 0
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 =  1)' > test4_2.mfotl
  $ monpoly -sig test4.sig -formula test4_2.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND 0 = 1
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x =  0)' > test4_3.mfotl
  $ monpoly -sig test4.sig -formula test4_3.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x = 0
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 = x)' > test4_4.mfotl
  $ monpoly -sig test4.sig -formula test4_4.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND 0 = x
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x = x)' > test4_5.mfotl
  $ monpoly -sig test4.sig -formula test4_5.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x = x
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Domain independent but not safe-range:
  $ echo 'P(x) AND (x = y)' > test4_6.mfotl
  $ monpoly -sig test4.sig -formula test4_6.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x = y
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 <  0)' > test4_7.mfotl
  $ monpoly -sig test4.sig -formula test4_7.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND 0 < 0
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 <  1)' > test4_8.mfotl
  $ monpoly -sig test4.sig -formula test4_8.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND 0 < 1
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x <  0)' > test4_9.mfotl
  $ monpoly -sig test4.sig -formula test4_9.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x < 0
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x <  1)' > test4_10.mfotl
  $ monpoly -sig test4.sig -formula test4_10.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x < 1
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND ( 0 < x)' > test4_11.mfotl
  $ monpoly -sig test4.sig -formula test4_11.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND 0 < x
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND (x < x)' > test4_12.mfotl
  $ monpoly -sig test4.sig -formula test4_12.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x < x
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Domain dependent:
  $ echo 'P(x) AND (x < y)' > test4_13.mfotl
  $ monpoly -sig test4.sig -formula test4_13.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND x < y
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(x) AND x < y
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'P(y) AND (x =  0)' > test4_14.mfotl
  $ monpoly -sig test4.sig -formula test4_14.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND x = 0
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,0))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(y) AND ( 0 = x)' > test4_15.mfotl
  $ monpoly -sig test4.sig -formula test4_15.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND 0 = x
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,0))
  At time point 2:
  @300 (time point 2): ()

TODO zumstegr: CMFOTL typechecker throws because some free variables are not resovled to a concrete type:
Domain dependent:
$ echo 'P(y) AND (x = x)' > test4_16.mfotl
$ monpoly -sig test4.sig -formula test4_16.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
The analyzed formula is:
P(y) AND x = x
The sequence of free variables is: (x,y)
The analyzed formula is NOT monitorable, because of the subformula:
P(y) AND x = x
In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
The analyzed formula is neither safe-range.
By the way, the analyzed formula is not TSF safe-range.

Domain independent but not safe-range:
  $ echo 'P(y) AND (x = y)' > test4_17.mfotl
  $ monpoly -sig test4.sig -formula test4_17.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND x = y
  The sequence of free variables is: (x,y)
  At time point 0:
  @100 (time point 0): ((0,0))
  At time point 1:
  @200 (time point 1): ((1,1))
  At time point 2:
  @300 (time point 2): ()

Domain dependent (integers):
  $ echo 'P(y) AND (x <  0)' > test4_18.mfotl
  $ monpoly -sig test4.sig -formula test4_18.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND x < 0
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND x < 0
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent (integers):
  $ echo 'P(y) AND (x <  1)' > test4_19.mfotl
  $ monpoly -sig test4.sig -formula test4_19.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND x < 1
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND x < 1
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND ( 0 < x)' > test4_20.mfotl
  $ monpoly -sig test4.sig -formula test4_20.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND 0 < x
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND 0 < x
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

TODO zumstegr: CMFOTL typechecker throws because some free variables are not resovled to a concrete type:
Safe-range:
$ echo 'P(y) AND (x < x)' > test4_21.mfotl
$ monpoly -sig test4.sig -formula test4_21.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
The analyzed formula is:
P(y) AND x < x
The sequence of free variables is: (x,y)
The analyzed formula is NOT monitorable, because of the subformula:
P(y) AND x < x
In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
However, the input (and also the analyzed) formula is safe-range, 
hence one should be able to rewrite it into a monitorable formula.
By the way, the analyzed formula is TSF safe-range.

Domain dependent (integers):
  $ echo 'P(y) AND (x < y)' > test4_22.mfotl
  $ monpoly -sig test4.sig -formula test4_22.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND x < y
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND x < y
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Safe-range:
  $ echo 'P(x) AND NOT ( 0 =  0)' > test4_23.mfotl
  $ monpoly -sig test4.sig -formula test4_23.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT 0 = 0)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 =  1)' > test4_24.mfotl
  $ monpoly -sig test4.sig -formula test4_24.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT 0 = 1)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x =  0)' > test4_25.mfotl
  $ monpoly -sig test4.sig -formula test4_25.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x = 0)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 = x)' > test4_26.mfotl
  $ monpoly -sig test4.sig -formula test4_26.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT 0 = x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x = x)' > test4_27.mfotl
  $ monpoly -sig test4.sig -formula test4_27.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x = x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Domain dependent:
  $ echo 'P(x) AND NOT (x = y)' > test4_28.mfotl
  $ monpoly -sig test4.sig -formula test4_28.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x = y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(x) AND (NOT x = y)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'P(x) AND NOT ( 0 <  0)' > test4_29.mfotl
  $ monpoly -sig test4.sig -formula test4_29.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT 0 < 0)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 <  1)' > test4_30.mfotl
  $ monpoly -sig test4.sig -formula test4_30.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT 0 < 1)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x <  0)' > test4_31.mfotl
  $ monpoly -sig test4.sig -formula test4_31.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x < 0)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x <  1)' > test4_32.mfotl
  $ monpoly -sig test4.sig -formula test4_32.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x < 1)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ()
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT ( 0 < x)' > test4_33.mfotl
  $ monpoly -sig test4.sig -formula test4_33.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT 0 < x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ()
  At time point 2:
  @300 (time point 2): ()

Safe-range:
  $ echo 'P(x) AND NOT (x < x)' > test4_34.mfotl
  $ monpoly -sig test4.sig -formula test4_34.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x < x)
  The sequence of free variables is: (x)
  At time point 0:
  @100 (time point 0): ((0))
  At time point 1:
  @200 (time point 1): ((1))
  At time point 2:
  @300 (time point 2): ()

Domain dependent (integers):
  $ echo 'P(x) AND NOT (x < y)' > test4_35.mfotl
  $ monpoly -sig test4.sig -formula test4_35.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(x) AND (NOT x < y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(x) AND (NOT x < y)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND NOT (x =  0)' > test4_36.mfotl
  $ monpoly -sig test4.sig -formula test4_36.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND (NOT x = 0)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT x = 0)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND NOT ( 0 = x)' > test4_37.mfotl
  $ monpoly -sig test4.sig -formula test4_37.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND (NOT 0 = x)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT 0 = x)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

TODO zumstegr: CMFOTL typechecker throws because some free variables are not resovled to a concrete type:
Safe-range:
$ echo 'P(y) AND NOT (x = x)' > test4_38.mfotl
$ monpoly -sig test4.sig -formula test4_38.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
The analyzed formula is:
P(y) AND (NOT x = x)
The sequence of free variables is: (x,y)
The analyzed formula is NOT monitorable, because of the subformula:
P(y) AND (NOT x = x)
In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
However, the input (and also the analyzed) formula is safe-range, 
hence one should be able to rewrite it into a monitorable formula.
By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND NOT (x = y)' > test4_39.mfotl
  $ monpoly -sig test4.sig -formula test4_39.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND (NOT x = y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT x = y)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND NOT (x <  0)' > test4_40.mfotl
  $ monpoly -sig test4.sig -formula test4_40.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND (NOT x < 0)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT x < 0)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND NOT (x <  1)' > test4_41.mfotl
  $ monpoly -sig test4.sig -formula test4_41.mfotl -log test4.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    P(y) AND (NOT x < 1)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT x < 1)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent (integers):
  $ echo 'P(y) AND NOT ( 0 < x)' > test4_42.mfotl
  $ monpoly -sig test4.sig -formula test4_42.mfotl -log test4.log -verbose -nonewlastts
  The analyzed formula is:
    P(y) AND (NOT 0 < x)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT 0 < x)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

TODO zumstegr: CMFOTL typechecker throws because some free variables are not resovled to a concrete type:
Domain dependent:
$ echo 'P(y) AND NOT (x < x)' > test4_43.mfotl
$ monpoly -sig test4.sig -formula test4_43.mfotl -log test4.log -verbose -nonewlastts
The analyzed formula is:
P(y) AND (NOT x < x)
The sequence of free variables is: (x,y)
The analyzed formula is NOT monitorable, because of the subformula:
P(y) AND (NOT x < x)
In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
The analyzed formula is neither safe-range.
By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'P(y) AND NOT (x < y)' > test4_44.mfotl
  $ monpoly -sig test4.sig -formula test4_44.mfotl -log test4.log -verbose -nonewlastts
  The analyzed formula is:
    P(y) AND (NOT x < y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(y) AND (NOT x < y)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.
