Type check formulas correctly

  $ echo 'P()' > type03_1.mfotl
  $ monpoly -sig type03.sig -formula type03_1.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ P()

  $ echo 'Q(1)' > type03_2.mfotl
  $ monpoly -sig type03.sig -formula type03_2.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ Q(1)

  $ echo 'Q(x)' > type03_3.mfotl
  $ monpoly -sig type03.sig -formula type03_3.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ Q(x)

  $ echo 'R(1,1)' > type03_4.mfotl
  $ monpoly -sig type03.sig -formula type03_4.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ R(1,1)

  $ echo 'R(x,1)' > type03_5.mfotl
  $ monpoly -sig type03.sig -formula type03_5.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ R(x,1)

  $ echo 'R(1,y)' > type03_6.mfotl
  $ monpoly -sig type03.sig -formula type03_6.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); y:Int) ⊢ R(1,y)

  $ echo 'R(x,y)' > type03_7.mfotl
  $ monpoly -sig type03.sig -formula type03_7.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Int) ⊢ R(x,y)

  $ echo 'I(1)' > type03_8.mfotl
  $ monpoly -sig type03.sig -formula type03_8.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ I(1)

  $ echo 'F(0.1)' > type03_9.mfotl
  $ monpoly -sig type03.sig -formula type03_9.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ F(0.1)

  $ echo 'W("a")' > type03_10.mfotl
  $ monpoly -sig type03.sig -formula type03_10.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ W("a")

  $ echo 'I(x)' > type03_11.mfotl
  $ monpoly -sig type03.sig -formula type03_11.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ I(x)

  $ echo 'F(x)' > type03_12.mfotl
  $ monpoly -sig type03.sig -formula type03_12.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ F(x)

  $ echo 'W(x)' > type03_13.mfotl
  $ monpoly -sig type03.sig -formula type03_13.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:String) ⊢ W(x)

  $ echo 'I(x) AND F(y)' > type03_14.mfotl
  $ monpoly -sig type03.sig -formula type03_14.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); y:Float, x:Int) ⊢ I(x) AND F(y)

  $ echo 'I(x) AND F(y) AND W(z)' > type03_15.mfotl
  $ monpoly -sig type03.sig -formula type03_15.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); z:String, y:Float, x:Int) ⊢ (I(x) AND F(y)) AND W(z)

  $ echo 'I(x) OR Q(x)' > type03_16.mfotl
  $ monpoly -sig type03.sig -formula type03_16.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ I(x) OR Q(x)

  $ echo 'I(x) OR P()' > type03_17.mfotl
  $ monpoly -sig type03.sig -formula type03_17.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ I(x) OR P()

  $ echo 'I(x) OR (I(x) AND F(y) AND W(z))' > type03_18.mfotl
  $ monpoly -sig type03.sig -formula type03_18.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); z:String, y:Float, x:Int) ⊢ I(x) OR ((I(x) AND F(y)) AND W(z))

  $ echo '(I(x) OR P()) AND (F(y) OR W(z))' > type03_19.mfotl
  $ monpoly -sig type03.sig -formula type03_19.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); z:String, y:Float, x:Int) ⊢ (I(x) OR P()) AND (F(y) OR W(z))

  $ echo '(I(x) OR tp(x)) AND (Q(y) OR ts(y)) AND tpts(x,y)' > type03_20.mfotl
  $ monpoly -sig type03.sig -formula type03_20.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Int) ⊢ ((I(x) OR tp(x)) AND (Q(y) OR ts(y))) AND tpts(x,y)

  $ echo 'NOT P()' > type03_21.mfotl
  $ monpoly -sig type03.sig -formula type03_21.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ NOT P()

  $ echo 'NOT Q(x)' > type03_22.mfotl
  $ monpoly -sig type03.sig -formula type03_22.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ NOT Q(x)

  $ echo 'PREVIOUS Q(x)' > type03_23.mfotl
  $ monpoly -sig type03.sig -formula type03_23.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ PREVIOUS[0,*) Q(x)

  $ echo 'NEXT Q(x)' > type03_24.mfotl
  $ monpoly -sig type03.sig -formula type03_24.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ NEXT[0,*) Q(x)

  $ echo 'ONCE Q(x)' > type03_25.mfotl
  $ monpoly -sig type03.sig -formula type03_25.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ ONCE[0,*) Q(x)

  $ echo 'EVENTUALLY[0,0] Q(x)' > type03_26.mfotl
  $ monpoly -sig type03.sig -formula type03_26.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ EVENTUALLY[0,0] Q(x)

  $ echo 'EXISTS x. Q(x)' > type03_27.mfotl
  $ monpoly -sig type03.sig -formula type03_27.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); _) ⊢ EXISTS x. Q(x)

  $ echo 'EXISTS x. Q(x) AND R(x,y)' > type03_28.mfotl
  $ monpoly -sig type03.sig -formula type03_28.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); y:Int) ⊢ EXISTS x. (Q(x) AND R(x,y))

  $ echo '(EXISTS x. Q(x)) AND R(x,y)' > type03_29.mfotl
  $ monpoly -sig type03.sig -formula type03_29.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); y:Int, x:Int) ⊢ (EXISTS x. Q(x)) AND R(x,y)

  $ echo '(EXISTS x. Q(x)) AND F(x)' > type03_30.mfotl
  $ monpoly -sig type03.sig -formula type03_30.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Float) ⊢ (EXISTS x. Q(x)) AND F(x)

  $ echo 'F(x) AND (EXISTS x. Q(x) AND W(y) AND I(z)) AND x = i2f(z)' > type03_31.mfotl
  $ monpoly -sig type03.sig -formula type03_31.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); z:Int, y:String, x:Float) ⊢ (F(x) AND (EXISTS x. ((Q(x) AND W(y)) AND I(z)))) AND x = i2f(z)

  $ echo '(EXISTS x. I(x) AND EXISTS x. F(x) AND EXISTS x. W(x)) AND Q(x) ' > type03_32.mfotl
  $ monpoly -sig type03.sig -formula type03_32.mfotl -verbose -check -no_rw -debug typing 2>&1 | grep "final type judgement"
  [Rewriting.type_check] The final type judgement is (W:(String), F:(Float), I:(Int), S:(Int, Int, Int), R:(Int, Int), Q:(Int), P:(()), tp:(Int), ts:(Int), tpts:(Int, Int); x:Int) ⊢ (EXISTS x. (I(x) AND (EXISTS x. (F(x) AND (EXISTS x. W(x)))))) AND Q(x)
