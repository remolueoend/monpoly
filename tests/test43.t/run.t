When rewriting, negations must not be propagated if that would 
make the formula non-monitorable
  $ echo '(NOT (A(x) AND B(x))) SINCE B(x)' > test43.mfotl
  $ monpoly -sig test43.sig -formula test43.mfotl -check -no_rw
  The input formula is:
    (NOT (A(x) AND B(x))) SINCE[0,*) B(x)
  The sequence of free variables is: (x)
  The formula is monitorable.
  $ monpoly -sig test43.sig -formula test43.mfotl -check
  The analyzed formula is:
    (NOT (A(x) AND B(x))) SINCE[0,*) B(x)
  The sequence of free variables is: (x)
  The analyzed formula is monitorable.

Removing syntactic sugar is ok unconditionally
  $ echo '((EXISTS x . A(x)) IMPLIES (EXISTS x . B(x))) SINCE B(x)' > test43.mfotl
  $ monpoly -sig test43.sig -formula test43.mfotl -check 
  The input formula is:
    ((EXISTS x. A(x)) IMPLIES EXISTS x. B(x)) SINCE[0,*) B(x)
  The analyzed formula is:
    ((NOT EXISTS x. A(x)) OR EXISTS x. B(x)) SINCE[0,*) B(x)
  The sequence of free variables is: (x)
  The analyzed formula is monitorable.

Pushing negation should be done when it leads to a monitorable formula
  $ echo '(NOT (A(x) IMPLIES B(x))) SINCE B(x)' > test43.mfotl
  $ monpoly -sig test43.sig -formula test43.mfotl -check 
  The input formula is:
    (NOT (A(x) IMPLIES B(x))) SINCE[0,*) B(x)
  The analyzed formula is:
    (A(x) AND (NOT B(x))) SINCE[0,*) B(x)
  The sequence of free variables is: (x)
  The analyzed formula is monitorable.
