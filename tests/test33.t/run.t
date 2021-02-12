Propagation of guarding conjunctions below quantifiers must not capture bound variables.

  $ echo 'P(x, y) AND EXISTS x. NOT Q(x, y)' > test33_1.mfotl
  $ monpoly -sig test33.sig -formula test33_1.mfotl -log test33.log -verbose -nonewlastts
  The input formula is:
    P(x,y) AND (EXISTS x. NOT Q(x,y))
  The analyzed formula is:
    P(x,y) AND (EXISTS _x1. (P(x,y) AND (NOT Q(_x1,y))))
  The sequence of free variables is: (x,y)
  The analyzed formula is NOT monitorable, because of the subformula:
    P(x,y) AND (NOT Q(_x1,y))
  In subformulas of the form phi AND NOT psi, psi SINCE_I phi, and psi UNTIL_I phi, the free variables of psi should be among the free variables of phi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.

In capture-avoiding substitution, the fresh variables must also avoid variables introduced by the substitution.
(This test is brittle because _x1 must be one of the automatically generated variable names.)

  $ echo 'R(x,y,z) AND (EXISTS x, y. NOT EXISTS _x1. EXISTS _x1. S(x,y,_x1))' > test33_2.mfotl
  $ monpoly -sig test33.sig -formula test33_2.mfotl -check
  The input formula is:
    R(x,y,z) AND (EXISTS x, y. NOT EXISTS _x1. EXISTS _x1. EXISTS _x1. S(x,y,_x1))
  The analyzed formula is:
    R(x,y,z) AND (EXISTS _x1, _x2. (R(x,y,z) AND (NOT EXISTS _x3. S(_x1,_x2,_x3))))
  The sequence of free variables is: (x,y,z)
  The analyzed formula is NOT monitorable, because of the subformula:
    R(x,y,z) AND (NOT EXISTS _x3. S(_x1,_x2,_x3))
  In subformulas of the form phi AND NOT psi, psi SINCE_I phi, and psi UNTIL_I phi, the free variables of psi should be among the free variables of phi.
  The analyzed formula is neither safe-range.
  By the way, the analyzed formula is not TSF safe-range.
