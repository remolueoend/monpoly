Type check aggregation formulas correctly

No groups, no result shadowing

  $ echo 'x <- CNT y I(y)' > type04_1.mfotl
  $ monpoly -sig type04.sig -formula type04_1.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y I(y)
 
  $ echo 'x <- CNT y F(y)' > type04_2.mfotl
  $ monpoly -sig type04.sig -formula type04_2.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y F(y)
 
  $ echo 'x <- CNT y W(y)' > type04_3.mfotl
  $ monpoly -sig type04.sig -formula type04_3.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y W(y)
 
  $ echo 'x <- SUM y I(y)' > type04_4.mfotl
  $ monpoly -sig type04.sig -formula type04_4.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- SUM y I(y)
 
  $ echo 'x <- SUM y F(y)' > type04_5.mfotl
  $ monpoly -sig type04.sig -formula type04_5.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- SUM y F(y)
 
  $ echo 'x <- AVG y I(y)' > type04_6.mfotl
  $ monpoly -sig type04.sig -formula type04_6.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- AVG y I(y)
 
  $ echo 'x <- AVG y F(y)' > type04_7.mfotl
  $ monpoly -sig type04.sig -formula type04_7.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- AVG y F(y)
 
  $ echo 'x <- MED y I(y)' > type04_8.mfotl
  $ monpoly -sig type04.sig -formula type04_8.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- MED y I(y)
 
  $ echo 'x <- MED y F(y)' > type04_9.mfotl
  $ monpoly -sig type04.sig -formula type04_9.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- MED y F(y)
 
  $ echo 'x <- MIN y I(y)' > type04_10.mfotl
  $ monpoly -sig type04.sig -formula type04_10.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- MIN y I(y)
 
  $ echo 'x <- MIN y F(y)' > type04_11.mfotl
  $ monpoly -sig type04.sig -formula type04_11.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- MIN y F(y)
 
  $ echo 'x <- MIN y W(y)' > type04_12.mfotl
  $ monpoly -sig type04.sig -formula type04_12.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x <- MIN y W(y)
 
  $ echo 'x <- MAX y I(y)' > type04_13.mfotl
  $ monpoly -sig type04.sig -formula type04_13.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- MAX y I(y)
 
  $ echo 'x <- MAX y F(y)' > type04_14.mfotl
  $ monpoly -sig type04.sig -formula type04_14.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- MAX y F(y)
 
  $ echo 'x <- MAX y W(y)' > type04_15.mfotl
  $ monpoly -sig type04.sig -formula type04_15.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ x <- MAX y W(y)
 
No groups, result shadowing

  $ echo 'x <- CNT y R(x,y)' > type04_16.mfotl
  $ monpoly -sig type04.sig -formula type04_16.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y R(x,y)
 
  $ echo 'x <- CNT y EXISTS x . R(x,y) AND z = i2f(x)' > type04_17.mfotl
  $ monpoly -sig type04.sig -formula type04_17.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y EXISTS x. (R(x,y) AND z = i2f(x))
 
  $ echo 'x <- CNT y EXISTS z . (EXISTS x . R(x,y) AND z = i2f(x)) AND z = x' > type04_18.mfotl
  $ monpoly -sig type04.sig -formula type04_18.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y EXISTS z. ((EXISTS x. (R(x,y) AND z = i2f(x))) AND z = x)
 
  $ echo 'x <- CNT y I(y) AND W(x)' > type04_19.mfotl
  $ monpoly -sig type04.sig -formula type04_19.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- CNT y (I(y) AND W(x))
 
  $ echo 'x <- SUM y R(x,y)' > type04_20.mfotl
  $ monpoly -sig type04.sig -formula type04_20.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- SUM y R(x,y)
 
  $ echo 'x <- SUM y EXISTS x . R(x,y) AND z = i2f(x)' > type04_21.mfotl
  $ monpoly -sig type04.sig -formula type04_21.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- SUM y EXISTS x. (R(x,y) AND z = i2f(x))
 
  $ echo 'x <- SUM y EXISTS z . (EXISTS x . R(x,y) AND z = i2f(x)) AND z = x' > type04_22.mfotl
  $ monpoly -sig type04.sig -formula type04_22.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- SUM y EXISTS z. ((EXISTS x. (R(x,y) AND z = i2f(x))) AND z = x)
 
  $ echo 'x <- SUM y I(y) AND W(x)' > type04_23.mfotl
  $ monpoly -sig type04.sig -formula type04_23.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- SUM y (I(y) AND W(x))
 
  $ echo 'x <- AVG y R(x,y)' > type04_24.mfotl
  $ monpoly -sig type04.sig -formula type04_24.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- AVG y R(x,y)
 
  $ echo 'x <- AVG y EXISTS x . R(x,y) AND z = i2f(x)' > type04_25.mfotl
  $ monpoly -sig type04.sig -formula type04_25.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- AVG y EXISTS x. (R(x,y) AND z = i2f(x))
 
  $ echo 'x <- AVG y EXISTS z . (EXISTS x . R(x,y) AND z = i2f(x)) AND z = x' > type04_26.mfotl
  $ monpoly -sig type04.sig -formula type04_26.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- AVG y EXISTS z. ((EXISTS x. (R(x,y) AND z = i2f(x))) AND z = x)
 
  $ echo 'x <- AVG y I(y) AND W(x)' > type04_27.mfotl
  $ monpoly -sig type04.sig -formula type04_27.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ x <- AVG y (I(y) AND W(x))
 
  $ echo 'x <- MIN y R(x,y)' > type04_28.mfotl
  $ monpoly -sig type04.sig -formula type04_28.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- MIN y R(x,y)
 
  $ echo 'x <- MIN y EXISTS x . R(x,y) AND z = i2f(x)' > type04_29.mfotl
  $ monpoly -sig type04.sig -formula type04_29.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- MIN y EXISTS x. (R(x,y) AND z = i2f(x))
 
  $ echo 'x <- MIN y EXISTS z . (EXISTS x . R(x,y) AND z = i2f(x)) AND z = x' > type04_30.mfotl
  $ monpoly -sig type04.sig -formula type04_30.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- MIN y EXISTS z. ((EXISTS x. (R(x,y) AND z = i2f(x))) AND z = x)
 
  $ echo 'x <- MIN y I(y) AND W(x)' > type04_31.mfotl
  $ monpoly -sig type04.sig -formula type04_31.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ x <- MIN y (I(y) AND W(x))
 
Groups, result shadowing

  $ echo 'r <- CNT y;x R(x,y) AND W(r)' > type04_32.mfotl
  $ monpoly -sig type04.sig -formula type04_32.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Int, x:Int) ⊢ r <- CNT y; x (R(x,y) AND W(r))

  $ echo 'r <- SUM z;x R(x,y) AND F(z) AND W(r)' > type04_33.mfotl
  $ monpoly -sig type04.sig -formula type04_33.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, x:Int) ⊢ r <- SUM z; x ((R(x,y) AND F(z)) AND W(r))

  $ echo 'r <- AVG z;x R(x,y) AND F(z) AND W(r)' > type04_34.mfotl
  $ monpoly -sig type04.sig -formula type04_34.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, x:Int) ⊢ r <- AVG z; x ((R(x,y) AND F(z)) AND W(r))

  $ echo 'r <- MIN z;x R(x,y) AND F(z) AND W(r)' > type04_35.mfotl
  $ monpoly -sig type04.sig -formula type04_35.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, x:Int) ⊢ r <- MIN z; x ((R(x,y) AND F(z)) AND W(r))

Groups, general shadowing

  $ echo 'I(z) AND r <- CNT y;x R(x,y) AND F(z) AND W(r)' > type04_36.mfotl
  $ monpoly -sig type04.sig -formula type04_36.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Int, z:Int, x:Int) ⊢ I(z) AND (r <- CNT y; x ((R(x,y) AND F(z)) AND W(r)))

  $ echo 'I(z) AND r <- SUM z;x R(x,y) AND F(z) AND W(r)' > type04_37.mfotl
  $ monpoly -sig type04.sig -formula type04_37.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, z:Int, x:Int) ⊢ I(z) AND (r <- SUM z; x ((R(x,y) AND F(z)) AND W(r)))

  $ echo 'I(z) AND r <- AVG z;x R(x,y) AND F(z) AND W(r)' > type04_38.mfotl
  $ monpoly -sig type04.sig -formula type04_38.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, z:Int, x:Int) ⊢ I(z) AND (r <- AVG z; x ((R(x,y) AND F(z)) AND W(r)))

  $ echo 'I(z) AND r <- MIN z;x R(x,y) AND F(z) AND W(r)' > type04_39.mfotl
  $ monpoly -sig type04.sig -formula type04_39.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, z:Int, x:Int) ⊢ I(z) AND (r <- MIN z; x ((R(x,y) AND F(z)) AND W(r)))

Group by aggregation variable

  $ echo 'I(y) AND r <- CNT z;x,z R(x,r) AND F(z) AND W(y)' > type04_40.mfotl
  $ monpoly -sig type04.sig -formula type04_40.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Int, y:Int, z:Float, x:Int) ⊢ I(y) AND (r <- CNT z; x,z ((R(x,r) AND F(z)) AND W(y)))

  $ echo 'I(y) AND r <- SUM z;x,z R(x,r) AND F(z) AND W(y)' > type04_41.mfotl
  $ monpoly -sig type04.sig -formula type04_41.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, y:Int, z:Float, x:Int) ⊢ I(y) AND (r <- SUM z; x,z ((R(x,r) AND F(z)) AND W(y)))

  $ echo 'I(y) AND r <- AVG z;x,z R(x,r) AND F(z) AND W(y)' > type04_42.mfotl
  $ monpoly -sig type04.sig -formula type04_42.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, y:Int, z:Float, x:Int) ⊢ I(y) AND (r <- AVG z; x,z ((R(x,r) AND F(z)) AND W(y)))

  $ echo 'I(y) AND r <- MIN z;x,z R(x,r) AND F(z) AND W(y)' > type04_43.mfotl
  $ monpoly -sig type04.sig -formula type04_43.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement" 
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); r:Float, y:Int, z:Float, x:Int) ⊢ I(y) AND (r <- MIN z; x,z ((R(x,r) AND F(z)) AND W(y)))
