Type check atomic formulas correctly

  $ echo '0=0' > type01_1.mfotl
  $ monpoly -sig type01.sig -formula type01_1.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 0 = 0

  $ echo 'TRUE' > type01_2.mfotl
  $ monpoly -sig type01.sig -formula type01_2.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 0 = 0

  $ echo 'FALSE' > type01_3.mfotl
  $ monpoly -sig type01.sig -formula type01_3.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 0 = 1

  $ echo 'x=x' > type01_4.mfotl
  $ monpoly -sig type01.sig -formula type01_4.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:t1) ⊢ x = x

  $ echo 'x=y' > type01_5.mfotl
  $ monpoly -sig type01.sig -formula type01_5.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:t1, x:t1) ⊢ x = y

  $ echo 'x<x' > type01_6.mfotl
  $ monpoly -sig type01.sig -formula type01_6.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:t1) ⊢ x < x

  $ echo 'x<y' > type01_7.mfotl
  $ monpoly -sig type01.sig -formula type01_7.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:t1, x:t1) ⊢ x < y

  $ echo 'x=0' > type01_8.mfotl
  $ monpoly -sig type01.sig -formula type01_8.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = 0

  $ echo 'x=0.1' > type01_9.mfotl
  $ monpoly -sig type01.sig -formula type01_9.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x = 0.1

  $ echo 'x="a"' > type01_10.mfotl
  $ monpoly -sig type01.sig -formula type01_10.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x = "a"

  $ echo '"a" SUBSTRING "ab"' > type01_11.mfotl
  $ monpoly -sig type01.sig -formula type01_11.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ "a" SUBSTRING "ab"

  $ echo 'x SUBSTRING "ab"' > type01_12.mfotl
  $ monpoly -sig type01.sig -formula type01_12.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x SUBSTRING "ab"

  $ echo '"a" SUBSTRING x' > type01_13.mfotl
  $ monpoly -sig type01.sig -formula type01_13.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ "a" SUBSTRING x

  $ echo 'x SUBSTRING y' > type01_14.mfotl
  $ monpoly -sig type01.sig -formula type01_14.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:String, x:String) ⊢ x SUBSTRING y

  $ echo '"a" MATCHES r"ab"' > type01_15.mfotl
  $ monpoly -sig type01.sig -formula type01_15.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ "a" MATCHES r"ab"

  $ echo 'x MATCHES r"ab"' > type01_16.mfotl
  $ monpoly -sig type01.sig -formula type01_16.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x MATCHES r"ab"

  $ echo '"a" MATCHES x' > type01_17.mfotl
  $ monpoly -sig type01.sig -formula type01_17.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Regexp) ⊢ "a" MATCHES x

  $ echo 'x MATCHES y' > type01_18.mfotl
  $ monpoly -sig type01.sig -formula type01_18.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Regexp, x:String) ⊢ x MATCHES y
