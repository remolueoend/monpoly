Type check LET formulas correctly

  $ echo 'LET g(x,y) = (NOT (x = x)) AND x = y IN (z <- MAX v1; ((NOT v1 = v1) AND v1 = v2)) AND g(b,1) AND z = ""' > type05_1.mfotl
  $ monpoly -verified -sig type05.sig -formula type05_1.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep -A 1 "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); b:Int, z:String) ⊢ LET g(x,y) = ((NOT x = x) AND x = y)
  IN (((z <- MAX v1 ((NOT v1 = v1) AND v1 = v2)) AND g(b,1)) AND z = "")
 
  $ echo 'LET g(x,y) = (NOT (x = x)) AND x = y IN a = 1 AND g(a,b) AND b = ""' > type05_2.mfotl
  $ monpoly -verified -sig type05.sig -formula type05_2.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "Type check error"
  Fatal error: exception Failure("[Rewriting.type_check_term] Type check error on term \"\": expected type Int, actual type String")
 
