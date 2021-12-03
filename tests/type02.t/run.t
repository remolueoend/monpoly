Type check terms correctly

  $ echo '0=0+1' > type02_1.mfotl
  $ monpoly -sig type02.sig -formula type02_1.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 0 = 0 + 1

  $ echo 'x=y+1' > type02_2.mfotl
  $ monpoly -sig type02.sig -formula type02_2.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Int) ⊢ x = y + 1

  $ echo 'x=y+z' > type02_3.mfotl
  $ monpoly -sig type02.sig -formula type02_3.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); z:(Num t4) =>  t4, y:(Num t4) =>  t4, x:(Num t4) =>  t4) ⊢ x = y + z

  $ echo 'x=y+z+w' > type02_4.mfotl
  $ monpoly -sig type02.sig -formula type02_4.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); w:(Num t5) =>  t5, z:(Num t5) =>  t5, y:(Num t5) =>  t5, x:(Num t5) =>  t5) ⊢ x = (y + z) + w

  $ echo 'x+y=z+w' > type02_5.mfotl
  $ monpoly -sig type02.sig -formula type02_5.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); w:(Num t5) =>  t5, z:(Num t5) =>  t5, y:(Num t5) =>  t5, x:(Num t5) =>  t5) ⊢ x + y = z + w

  $ echo '1=5 MOD 4' > type02_6.mfotl
  $ monpoly -sig type02.sig -formula type02_6.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 1 = 5 mod 4

  $ echo 'x=5 MOD 4' > type02_7.mfotl
  $ monpoly -sig type02.sig -formula type02_7.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = 5 mod 4

  $ echo 'x=y MOD 4' > type02_8.mfotl
  $ monpoly -sig type02.sig -formula type02_8.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Int) ⊢ x = y mod 4

  $ echo 'x=y MOD z' > type02_9.mfotl
  $ monpoly -sig type02.sig -formula type02_9.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); z:Int, y:Int, x:Int) ⊢ x = y mod z

  $ echo 'x=w+(y MOD z)' > type02_10.mfotl
  $ monpoly -sig type02.sig -formula type02_10.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); z:Int, y:Int, w:Int, x:Int) ⊢ x = w + (y mod z)

  $ echo 'x=(w+y) MOD z' > type02_11.mfotl
  $ monpoly -sig type02.sig -formula type02_11.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); z:Int, y:Int, w:Int, x:Int) ⊢ x = (w + y) mod z

  $ echo '0=-1' > type02_12.mfotl
  $ monpoly -sig type02.sig -formula type02_12.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 0 = -1

  $ echo 'x=-1' > type02_13.mfotl
  $ monpoly -sig type02.sig -formula type02_13.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = -1

  $ echo '0=-x' > type02_14.mfotl
  $ monpoly -sig type02.sig -formula type02_14.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ 0 = -x

  $ echo 'y=-x' > type02_15.mfotl
  $ monpoly -sig type02.sig -formula type02_15.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:(Num t3) =>  t3, y:(Num t3) =>  t3) ⊢ y = -x

  $ echo 'y=-(x MOD z)' > type02_16.mfotl
  $ monpoly -sig type02.sig -formula type02_16.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); z:Int, x:Int, y:Int) ⊢ y = -(x mod z)

  $ echo '1=f2i(0.1)' > type02_17.mfotl
  $ monpoly -sig type02.sig -formula type02_17.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 1 = f2i(0.1)

  $ echo 'x=f2i(0.1)' > type02_18.mfotl
  $ monpoly -sig type02.sig -formula type02_18.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = f2i(0.1)

  $ echo 'x=f2i(y)' > type02_19.mfotl
  $ monpoly -sig type02.sig -formula type02_19.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Int) ⊢ x = f2i(y)

  $ echo '0.1=i2f(1)' > type02_20.mfotl
  $ monpoly -sig type02.sig -formula type02_20.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 0.1 = i2f(1)

  $ echo 'x=i2f(1)' > type02_21.mfotl
  $ monpoly -sig type02.sig -formula type02_21.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x = i2f(1)

  $ echo 'x=i2f(y)' > type02_22.mfotl
  $ monpoly -sig type02.sig -formula type02_22.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Float) ⊢ x = i2f(y)

  $ echo 'x+y=i2f(f2i(y)+1)' > type02_23.mfotl
  $ monpoly -sig type02.sig -formula type02_23.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Float) ⊢ x + y = i2f((f2i(y)) + 1)

  $ echo 'x+y=f2i(i2f(y)+0.1)' > type02_24.mfotl
  $ monpoly -sig type02.sig -formula type02_24.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Int) ⊢ x + y = f2i((i2f(y)) + 0.1)

  $ echo '"a"=r2s(r"a")' > type02_25.mfotl
  $ monpoly -sig type02.sig -formula type02_25.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ "a" = r2s(r"a")

  $ echo 'x=r2s(r"a")' > type02_26.mfotl
  $ monpoly -sig type02.sig -formula type02_26.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x = r2s(r"a")

  $ echo 'x=r2s(y)' > type02_27.mfotl
  $ monpoly -sig type02.sig -formula type02_27.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Regexp, x:String) ⊢ x = r2s(y)

  $ echo 'r"a"=s2r("a")' > type02_28.mfotl
  $ monpoly -sig type02.sig -formula type02_28.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ r"a" = s2r("a")

  $ echo 'x=s2r("a")' > type02_29.mfotl
  $ monpoly -sig type02.sig -formula type02_29.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Regexp) ⊢ x = s2r("a")

  $ echo 'x=s2r(y)' > type02_30.mfotl
  $ monpoly -sig type02.sig -formula type02_30.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:String, x:Regexp) ⊢ x = s2r(y)

  $ echo 'x=r2s(s2r(x))' > type02_31.mfotl
  $ monpoly -sig type02.sig -formula type02_31.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x = r2s(s2r(x))

  $ echo 'x=s2r(r2s(x))' > type02_32.mfotl
  $ monpoly -sig type02.sig -formula type02_32.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Regexp) ⊢ x = s2r(r2s(x))

  $ echo 'x=s2r(r2s(r"a"))' > type02_33.mfotl
  $ monpoly -sig type02.sig -formula type02_33.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Regexp) ⊢ x = s2r(r2s(r"a"))

  $ echo '"a"=FORMAT_DATE(0.1)' > type02_34.mfotl
  $ monpoly -sig type02.sig -formula type02_34.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ "a" = FORMAT_DATE(0.1)

  $ echo 'x=FORMAT_DATE(0.1)' > type02_35.mfotl
  $ monpoly -sig type02.sig -formula type02_35.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x = FORMAT_DATE(0.1)

  $ echo 'x=FORMAT_DATE(y)' > type02_36.mfotl
  $ monpoly -sig type02.sig -formula type02_36.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:String) ⊢ x = FORMAT_DATE(y)

  $ echo '1=YEAR(0.1)' > type02_37.mfotl
  $ monpoly -sig type02.sig -formula type02_37.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 1 = YEAR(0.1)

  $ echo 'x=YEAR(0.1)' > type02_38.mfotl
  $ monpoly -sig type02.sig -formula type02_38.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = YEAR(0.1)

  $ echo 'x=YEAR(y)' > type02_39.mfotl
  $ monpoly -sig type02.sig -formula type02_39.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Int) ⊢ x = YEAR(y)

  $ echo '1=MONTH(0.1)' > type02_40.mfotl
  $ monpoly -sig type02.sig -formula type02_40.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 1 = MONTH(0.1)

  $ echo 'x=MONTH(0.1)' > type02_41.mfotl
  $ monpoly -sig type02.sig -formula type02_41.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = MONTH(0.1)

  $ echo 'x=MONTH(y)' > type02_42.mfotl
  $ monpoly -sig type02.sig -formula type02_42.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Int) ⊢ x = MONTH(y)

  $ echo '1=DAY_OF_MONTH(0.1)' > type02_43.mfotl
  $ monpoly -sig type02.sig -formula type02_43.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ 1 = DAY_OF_MONTH(0.1)

  $ echo 'x=DAY_OF_MONTH(0.1)' > type02_44.mfotl
  $ monpoly -sig type02.sig -formula type02_44.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x = DAY_OF_MONTH(0.1)

  $ echo 'x=DAY_OF_MONTH(y)' > type02_45.mfotl
  $ monpoly -sig type02.sig -formula type02_45.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Int) ⊢ x = DAY_OF_MONTH(y)

  $ echo 'x=DAY_OF_MONTH(y) AND i2f(x)=i2f(MONTH(y)) AND y=i2f(YEAR(y))' > type02_46.mfotl
  $ monpoly -sig type02.sig -formula type02_46.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Int) ⊢ (x = DAY_OF_MONTH(y) AND i2f(x) = i2f(MONTH(y))) AND y = i2f(YEAR(y))
