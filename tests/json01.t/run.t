correctly resolved types in nested scopes
  $ monpoly -check -sig json01.sig -formula json01.mfotl -log json01.log 2>&1 | grep "free"
  The sequence of free variables is: (r1,r2)
