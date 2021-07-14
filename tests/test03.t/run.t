Safe-range:
  $ echo '( 0 =  0)' > test3_1.mfotl
  $ monpoly -sig test3.sig -formula test3_1.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    0 = 0
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): true
  At time point 1:
  @200. (time point 1): true

Safe-range:
  $ echo '( 0 =  1)' > test3_2.mfotl
  $ monpoly -sig test3.sig -formula test3_2.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    0 = 1
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): false
  At time point 1:
  @200. (time point 1): false

Safe-range:
  $ echo '(x =  0)' > test3_3.mfotl
  $ monpoly -sig test3.sig -formula test3_3.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    x = 0
  The sequence of free variables is: (x)
  At time point 0:
  @100. (time point 0): ((0))
  At time point 1:
  @200. (time point 1): ((0))

Safe-range:
  $ echo '( 0 = x)' > test3_4.mfotl
  $ monpoly -sig test3.sig -formula test3_4.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    0 = x
  The sequence of free variables is: (x)
  At time point 0:
  @100. (time point 0): ((0))
  At time point 1:
  @200. (time point 1): ((0))

Domain dependent:
  $ echo '(x = x)' > test3_5.mfotl
  $ monpoly -sig test3.sig -formula test3_5.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    x = x
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    x = x
  In input formulas psi of the form t1 = t2 the terms t1 and t2 should be variables or constants and at least one should be a constant.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo '(x = y)' > test3_6.mfotl
  $ monpoly -sig test3.sig -formula test3_6.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    x = y
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    x = y
  In input formulas psi of the form t1 = t2 the terms t1 and t2 should be variables or constants and at least one should be a constant.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo '( 0 <  0)' > test3_7.mfotl
  $ monpoly -sig test3.sig -formula test3_7.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    0 < 0
  The sequence of free variables is: ()
  The analyzed formula is NOT monitorable, because of the subformula:
    0 < 0
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Safe-range:
  $ echo '( 0 <  1)' > test3_8.mfotl
  $ monpoly -sig test3.sig -formula test3_8.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    0 < 1
  The sequence of free variables is: ()
  The analyzed formula is NOT monitorable, because of the subformula:
    0 < 1
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent (integers):
  $ echo '(x <  0)' > test3_9.mfotl
  $ monpoly -sig test3.sig -formula test3_9.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    x < 0
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    x < 0
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent (integers):
  $ echo '(x <  5)' > test3_10.mfotl
  $ monpoly -sig test3.sig -formula test3_10.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    x < 5
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    x < 5
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo '( 0 < x)' > test3_11.mfotl
  $ monpoly -sig test3.sig -formula test3_11.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    0 < x
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    0 < x
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo '(x < x)' > test3_12.mfotl
  $ monpoly -sig test3.sig -formula test3_12.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp -nofilteremptytp
  The analyzed formula is:
    x < x
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    x < x
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo '(x < y)' > test3_13.mfotl
  $ monpoly -sig test3.sig -formula test3_13.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    x < y
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    x < y
  Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES t2 are currently considered not monitorable.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'T() AND ( 0 =  0)' > test3_14.mfotl
  $ monpoly -sig test3.sig -formula test3_14.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND 0 = 0
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): true
  At time point 1:
  @200. (time point 1): false

Safe-range:
  $ echo 'T() AND ( 0 =  1)' > test3_15.mfotl
  $ monpoly -sig test3.sig -formula test3_15.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND 0 = 1
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): false
  At time point 1:
  @200. (time point 1): false

Safe-range:
  $ echo 'T() AND (x =  0)' > test3_16.mfotl
  $ monpoly -sig test3.sig -formula test3_16.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x = 0
  The sequence of free variables is: (x)
  At time point 0:
  @100. (time point 0): ((0))
  At time point 1:
  @200. (time point 1): ()

Safe-range:
  $ echo 'T() AND ( 0 = x)' > test3_17.mfotl
  $ monpoly -sig test3.sig -formula test3_17.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND 0 = x
  The sequence of free variables is: (x)
  At time point 0:
  @100. (time point 0): ((0))
  At time point 1:
  @200. (time point 1): ()

Domain dependent:
  $ echo 'T() AND (x = x)' > test3_18.mfotl
  $ monpoly -sig test3.sig -formula test3_18.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x = x
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND x = x
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'T() AND (x = y)' > test3_19.mfotl
  $ monpoly -sig test3.sig -formula test3_19.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x = y
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND x = y
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'T() AND ( 0 <  0)' > test3_20.mfotl
  $ monpoly -sig test3.sig -formula test3_20.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND 0 < 0
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): false
  At time point 1:
  @200. (time point 1): false

Safe-range:
  $ echo 'T() AND ( 0 <  1)' > test3_21.mfotl
  $ monpoly -sig test3.sig -formula test3_21.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND 0 < 1
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): true
  At time point 1:
  @200. (time point 1): false

Domain dependent (integers):
  $ echo 'T() AND (x <  0)' > test3_22.mfotl
  $ monpoly -sig test3.sig -formula test3_22.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x < 0
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND x < 0
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent (integers):
  $ echo 'T() AND (x <  1)' > test3_23.mfotl
  $ monpoly -sig test3.sig -formula test3_23.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x < 1
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND x < 1
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'T() AND ( 0 < x)' > test3_24.mfotl
  $ monpoly -sig test3.sig -formula test3_24.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND 0 < x
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND 0 < x
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'T() AND (x < x) ' > test3_25.mfotl
  $ monpoly -sig test3.sig -formula test3_25.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x < x
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND x < x
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'T() AND (x < y)' > test3_26.mfotl
  $ monpoly -sig test3.sig -formula test3_26.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND x < y
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND x < y
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'T() AND NOT ( 0 =  0)' > test3_27.mfotl
  $ monpoly -sig test3.sig -formula test3_27.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT 0 = 0)
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): false
  At time point 1:
  @200. (time point 1): false

Safe-range:
  $ echo 'T() AND NOT ( 0 =  1)' > test3_28.mfotl
  $ monpoly -sig test3.sig -formula test3_28.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT 0 = 1)
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): true
  At time point 1:
  @200. (time point 1): false

Domain dependent:
  $ echo 'T() AND NOT (x =  0)' > test3_29.mfotl
  $ monpoly -sig test3.sig -formula test3_29.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x = 0)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x = 0)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'T() AND NOT ( 0 = x)' > test3_30.mfotl
  $ monpoly -sig test3.sig -formula test3_30.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT 0 = x)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT 0 = x)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'T() AND NOT (x = x) ' > test3_31.mfotl
  $ monpoly -sig test3.sig -formula test3_31.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x = x)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x = x)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'T() AND NOT (x = y)' > test3_32.mfotl
  $ monpoly -sig test3.sig -formula test3_32.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x = y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x = y)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Safe-range:
  $ echo 'T() AND NOT ( 0 <  0)' > test3_33.mfotl
  $ monpoly -sig test3.sig -formula test3_33.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT 0 < 0)
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): true
  At time point 1:
  @200. (time point 1): false

Safe-range:
  $ echo 'T() AND NOT ( 0 <  1)' > test3_34.mfotl
  $ monpoly -sig test3.sig -formula test3_34.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT 0 < 1)
  The sequence of free variables is: ()
  At time point 0:
  @100. (time point 0): false
  At time point 1:
  @200. (time point 1): false

Domain dependent:
  $ echo 'T() AND NOT (x <  0)' > test3_35.mfotl
  $ monpoly -sig test3.sig -formula test3_35.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x < 0)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x < 0)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'T() AND NOT (x <  1)' > test3_36.mfotl
  $ monpoly -sig test3.sig -formula test3_36.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x < 1)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x < 1)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent (integers):
  $ echo 'T() AND NOT ( 5 < x)' > test3_37.mfotl
  $ monpoly -sig test3.sig -formula test3_37.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT 5 < x)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT 5 < x)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  However, the input (and also the analyzed) formula is safe-range, 
  hence one should be able to rewrite it into a monitorable formula.
  By the way, the analyzed formula is TSF safe-range.

Domain dependent:
  $ echo 'T() AND NOT (x < x)' > test3_38.mfotl
  $ monpoly -sig test3.sig -formula test3_38.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x < x)
  The sequence of free variables is: (x)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x < x)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

Domain dependent:
  $ echo 'T() AND NOT (x < y)' > test3_39.mfotl
  $ monpoly -sig test3.sig -formula test3_39.mfotl -log test3.log -verbose -nonewlastts -nofilteremptytp
  The analyzed formula is:
    T() AND (NOT x < y)
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    T() AND (NOT x < y)
  In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with op among =, <, <=, either the variables of the terms t1 and t2 are among the free variables of psi or the formula is of the form psi AND x = t or psi AND x = t, and the variables of the term t are among the free variables of psi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.
