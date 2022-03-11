(*  Copyright 2021 Dawit Legesse Tirore, Dmitriy Traytel, Martin Raszyk
    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
    *)
theory Rewriting
  imports Formula Regex
begin

datatype (discs_sels) 'a tformula =
    TPred Formula.name "Formula.trm list"
  | TLet Formula.name "'a tformula" "'a tformula"
  | TLetPast Formula.name "'a tformula" "'a tformula"
  | TEq Formula.trm Formula.trm
  | TLess Formula.trm Formula.trm
  | TLessEq Formula.trm Formula.trm
  | TNeg "'a tformula"
  | TOr "'a tformula" "'a tformula"
  | TAnd "'a tformula" "'a tformula"
  | TAnds "'a tformula list"
  | TExists 'a "'a tformula"
  | TAgg nat "'a Formula.agg_op" "'a list" Formula.trm "'a tformula"
  | TPrev \<I> "'a tformula"
  | TNext \<I> "'a tformula"
  | TSince "'a tformula" \<I> "'a tformula"
  | TUntil "'a tformula" \<I> "'a tformula"
  | TDiamondB \<I> "'a tformula"
  | TSquareB \<I> "'a tformula"
  | TDiamondW \<I> "'a tformula"
  | TSquareW \<I> "'a tformula"
  | TMatchF \<I> "'a tformula Regex.regex"
  | TMatchP \<I> "'a tformula Regex.regex"
  | TTP Formula.trm
  | TTS Formula.trm

datatype (discs_sels) 'a rformula = 
    RPred Formula.name "Formula.trm list"
  | RLet Formula.name "'a rformula" "'a rformula"
  | RLetPast Formula.name "'a rformula" "'a rformula"
  | REq Formula.trm Formula.trm | RLess Formula.trm Formula.trm | RLessEq Formula.trm Formula.trm
  | RNeg "'a rformula" 
  | ROr "'a rformula" "'a rformula" 
  | RAnd "'a rformula" "'a rformula" 
  | RAnds "'a rformula list"
  | RExists 'a "'a rformula"
  | RAgg nat "'a Formula.agg_op" "'a list" Formula.trm "'a rformula"
  | RPrev \<I> "'a rformula" 
  | RNext \<I> "'a rformula"
  | RSince "'a rformula" \<I> "'a rformula" 
  | RUntil "'a rformula" \<I> "'a rformula"
  | RRelease "'a rformula" \<I> "'a rformula" 
  | RTrigger "'a rformula" \<I> "'a rformula"
  | RDiamondB \<I> "'a rformula" 
  | RSquareB \<I> "'a rformula"
  | RDiamondW \<I> "'a rformula" 
  | RSquareW \<I> "'a rformula"
  | RMatchF \<I> "'a rformula Regex.regex" 
  | RMatchP \<I> "'a rformula Regex.regex"
  | RTP Formula.trm
  | RTS Formula.trm

fun embed1 :: "'a Formula.formula \<Rightarrow> 'a tformula" where
 "embed1 (Formula.Ands \<phi>s) = TAnds (map embed1 \<phi>s)"
| "embed1 (Formula.MatchF I r) = TMatchF I (regex.map_regex embed1 r)"
| "embed1 (Formula.MatchP I r) = TMatchP I (regex.map_regex embed1 r)"
|  "embed1 (Formula.Pred r ts) = TPred r ts"
| "embed1 (Formula.Let p \<phi> \<psi>) = TLet p (embed1 \<phi>) (embed1 \<psi>)"
| "embed1 (Formula.LetPast p \<phi> \<psi>) = TLetPast p (embed1 \<phi>) (embed1 \<psi>)"
| "embed1 (Formula.Eq t1 t2) = TEq t1 t2"
| "embed1 (Formula.Less t1 t2) = TLess t1 t2"
| "embed1 (Formula.LessEq t1 t2) = TLessEq t1 t2"
| "embed1 (Formula.Neg (Formula.Since \<phi> I (Formula.Neg \<psi>))) = (if \<phi> = Formula.TT then
    TSquareB I (embed1 \<psi>) else TNeg (TSince (embed1 \<phi>) I (TNeg (embed1 \<psi>))))"
| "embed1 (Formula.Neg (Formula.Until \<phi> I (Formula.Neg \<psi>))) =  (if \<phi> = Formula.TT then
    TSquareW I (embed1 \<psi>) else TNeg (TUntil (embed1 \<phi>) I (TNeg (embed1 \<psi>))))"
| "embed1 (Formula.Neg \<phi>) = TNeg (embed1 \<phi>)"
| "embed1 (Formula.Or \<phi> \<psi>) = TOr (embed1 \<phi>) (embed1 \<psi>)"
| "embed1 (Formula.And \<phi> \<psi>) = TAnd (embed1 \<phi>) (embed1 \<psi>)"
| "embed1 (Formula.Exists t \<phi>) = TExists t (embed1 \<phi>)"
| "embed1 (Formula.Agg y \<omega> b' f \<phi>) = TAgg y \<omega> b' f (embed1 \<phi>)"
| "embed1 (Formula.Prev I \<phi>) = TPrev I (embed1 \<phi>)"
| "embed1 (Formula.Next I \<phi>) = TNext I (embed1 \<phi>)"
| "embed1 (Formula.Since \<phi> I \<psi>) = (if \<phi> = Formula.TT then TDiamondB I (embed1 \<psi>)
                                             else TSince (embed1 \<phi>) I (embed1 \<psi>))"
| "embed1 (Formula.Until \<phi> I \<psi>) = (if \<phi> = Formula.TT then TDiamondW I (embed1 \<psi>)
                                             else TUntil (embed1 \<phi>) I (embed1 \<psi>))"
| "embed1 (Formula.TP t) = TTP t"
| "embed1 (Formula.TS t) = TTS t"


fun embed2 where
  "embed2 (TAnds \<phi>s) = RAnds (map embed2 \<phi>s)"
| "embed2 (TMatchF I r) = RMatchF I (regex.map_regex embed2 r)"
| "embed2 (TMatchP I r) = RMatchP I (regex.map_regex embed2 r)"
| "embed2 (TNeg (TSince (TNeg \<phi>) I (TNeg \<psi>))) =  RTrigger (embed2 \<phi>) I (embed2  \<psi>)"
| "embed2 (TNeg (TUntil (TNeg \<phi>) I (TNeg \<psi>))) =   RRelease (embed2 \<phi>) I (embed2 \<psi>)"
| "embed2 (TPred r ts) = RPred r ts"
| "embed2 (TLet p \<phi> \<psi>) = RLet p (embed2 \<phi>) (embed2 \<psi>)"
| "embed2 (TLetPast p \<phi> \<psi>) = RLetPast p (embed2 \<phi>) (embed2 \<psi>)"
| "embed2 (TEq t1 t2) = REq t1 t2"
| "embed2 (TLess t1 t2) = RLess t1 t2"
| "embed2 (TLessEq t1 t2) = RLessEq t1 t2"
| "embed2 (TNeg \<phi>) = RNeg (embed2 \<phi>)"
| "embed2 (TOr \<phi> \<psi>) = ROr (embed2 \<phi>) (embed2 \<psi>)"
| "embed2 (TAnd \<phi> \<psi>) = RAnd (embed2 \<phi>) (embed2 \<psi>)"
| "embed2 (TExists t \<phi>) = RExists t (embed2 \<phi>)"
| "embed2 (TAgg y \<omega> b' f \<phi>) = RAgg y \<omega> b' f (embed2 \<phi>)"
| "embed2 (TPrev I \<phi>) = RPrev I (embed2 \<phi>)"
| "embed2 (TNext I \<phi>) = RNext I (embed2 \<phi>)"
| "embed2 (TSince \<phi> I \<psi>) = RSince (embed2 \<phi>) I (embed2 \<psi>)"
| "embed2 (TUntil \<phi> I \<psi>) =  RUntil (embed2 \<phi>) I (embed2 \<psi>)"
| "embed2 (TDiamondW I a) = RDiamondW I (embed2 a) "
| "embed2 (TDiamondB I a) = RDiamondB I (embed2 a) "
| "embed2 (TSquareW I a) = RSquareW I (embed2 a) "
| "embed2 (TSquareB I a) = RSquareB I (embed2 a) "
| "embed2 (TTP t) = RTP t"
| "embed2 (TTS t) = RTS t"

fun project2 where
 "project2  (RTrigger \<phi> I \<psi>) =  TNeg (TSince (TNeg (project2 \<phi>)) I (TNeg (project2 \<psi>)))"
| "project2 (RRelease  \<phi> I \<psi>) =  TNeg (TUntil (TNeg (project2 \<phi>)) I (TNeg (project2 \<psi>)))  "
|  "project2 (RPred r ts) = TPred r ts"
| "project2 (RLet p \<phi> \<psi>) = TLet p (project2 \<phi>) (project2 \<psi>)"
| "project2 (RLetPast p \<phi> \<psi>) = TLetPast p (project2 \<phi>) (project2 \<psi>)"
| "project2 (REq t1 t2) = TEq t1 t2"
| "project2 (RLess t1 t2) = TLess t1 t2"
| "project2 (RLessEq t1 t2) = TLessEq t1 t2"
| "project2 (RNeg \<phi>) = TNeg (project2 \<phi>)"
| "project2 (ROr \<phi> \<psi>) = TOr (project2 \<phi>) (project2 \<psi>)"
| "project2 (RAnd \<phi> \<psi>) = TAnd (project2 \<phi>) (project2 \<psi>)"
| "project2 (RAnds \<phi>s) = TAnds (map project2 \<phi>s)"
| "project2 (RExists t \<phi>) = TExists t (project2 \<phi>)"
| "project2 (RAgg y \<omega> b' f \<phi>) = TAgg y \<omega> b' f (project2 \<phi>)"
| "project2 (RPrev I \<phi>) = TPrev I (project2 \<phi>)"
| "project2 (RNext I \<phi>) = TNext I (project2 \<phi>)"
| "project2 (RSince \<phi> I \<psi>) = TSince (project2 \<phi>) I (project2 \<psi>)"
| "project2 (RUntil \<phi> I \<psi>) =  TUntil (project2 \<phi>) I (project2 \<psi>)"
| "project2 (RMatchF I r) = TMatchF I (regex.map_regex project2 r)"
| "project2 (RMatchP I r) = TMatchP I (regex.map_regex project2 r)"
| "project2 (RDiamondW I a) = TDiamondW I (project2 a) "
| "project2 (RDiamondB I a) = TDiamondB I (project2 a) "
| "project2 (RSquareW I a) = TSquareW I (project2 a) "
| "project2 (RSquareB I a) = TSquareB I (project2 a) "
| "project2 (RTP t) = TTP t"
| "project2 (RTS t) = TTS t"

fun project1 :: "'a tformula \<Rightarrow> 'a Formula.formula" where
  "project1 (TPred r ts)  = Formula.Pred r ts"
| "project1 (TLet p \<phi> \<psi>) =  Formula.Let p (project1 \<phi>) (project1 \<psi>)"
| "project1 (TLetPast p \<phi> \<psi>) =  Formula.LetPast p (project1 \<phi>) (project1 \<psi>)"
| "project1 (TEq t1 t2) =Formula.Eq t1 t2"
| "project1 (TLess t1 t2) =Formula.Less t1 t2"
| "project1 (TLessEq t1 t2) =Formula.LessEq t1 t2"
| "project1 (TSquareB I \<psi>) = Formula.Neg (Formula.Since Formula.TT I (Formula.Neg (project1 \<psi>)))"
| "project1 (TSquareW I \<psi>) = Formula.Neg (Formula.Until Formula.TT I (Formula.Neg (project1 \<psi>)))"
| "project1 (TNeg \<phi>) = Formula.Neg (project1 \<phi>)"
| "project1 (TOr \<phi> \<psi>) = Formula.Or (project1 \<phi>) (project1 \<psi>)"
| "project1 (TAnd \<phi> \<psi>) = Formula.And (project1 \<phi>) (project1 \<psi>)"
| "project1 (TAnds \<phi>s) = Formula.Ands (map project1 \<phi>s)"
| "project1 (TExists t \<phi>) = Formula.Exists t (project1 \<phi>)"
| "project1 (TAgg y \<omega> b' f \<phi>) = Formula.Agg y \<omega> b' f (project1 \<phi>)"
| "project1 (TPrev I \<phi>) = Formula.Prev I (project1 \<phi>)"
| "project1 (TNext I \<phi>) = Formula.Next I (project1 \<phi>)"
| "project1 (TDiamondB I \<phi>) = Formula.Since Formula.TT I (project1 \<phi>)"
| "project1 (TSince \<phi> I \<psi>) = Formula.Since (project1 \<phi>) I (project1 \<psi>)"
| "project1 (TDiamondW I \<phi>) = Formula.Until Formula.TT I (project1 \<phi>)"
| "project1 (TUntil \<phi> I \<psi>) = Formula.Until (project1 \<phi>) I (project1 \<psi>)"
| "project1 (TMatchF I r) = Formula.MatchF I (regex.map_regex project1 r)"
| "project1 (TMatchP I r) = Formula.MatchP I (regex.map_regex project1 r)"
| "project1 (TTP t) = Formula.TP t"
| "project1 (TTS t) = Formula.TS t"

lemma project_embed1: "project1 (embed1 f) = f"
proof(induction f rule:embed1.induct)
  case (1 \<phi>s)
  then have "map (project1 \<circ> embed1) \<phi>s = map id \<phi>s" using map_cong[OF refl, of \<phi>s "project1 \<circ> embed1" id ] by simp (*reduce function argument to identity*)
  then show ?case by simp
next
  case (2 I r)
  then show ?case by (induction r;auto)
next
  case (3 I r)
  then show ?case by (induction r;auto)
qed auto

abbreviation embed where
 "embed f \<equiv> embed2 (embed1 f)"

abbreviation project where
 "project f \<equiv> project1 (project2 f)"

lemma project_embed2: "project2 (embed2 r) = r"
proof(induction r rule:embed2.induct)
  case (1 \<phi>s)
  then have "map (project2 \<circ> embed2) \<phi>s = map id \<phi>s" using map_cong[OF refl, of \<phi>s "project2 \<circ> embed2" id ] by simp (*reduce function argument to identity*)
  then show ?case by simp
next
  case (2 I r)
  then show ?case by (induction r;auto)
next
  case (3 I r)
  then show ?case by (induction r;auto)
qed auto


lemma project_embed[simp]: "project (embed f) = f"
  using project_embed1 project_embed2 by metis


definition   "rsat \<sigma> V v i \<phi> \<equiv> Formula.sat \<sigma> V v i (project \<phi>)"
abbreviation diamond_b where "diamond_b I \<alpha> \<equiv> Formula.Since Formula.TT I \<alpha>"
abbreviation square_b where "square_b I \<alpha> \<equiv> Formula.Neg (diamond_b I (Formula.Neg \<alpha>))"
abbreviation diamond_w where "diamond_w I \<alpha> \<equiv> Formula.Until Formula.TT I \<alpha>"
abbreviation square_w where "square_w I \<alpha> \<equiv> Formula.Neg (diamond_w I (Formula.Neg \<alpha>))"
abbreviation excl_zero where "excl_zero I \<equiv> \<not> (mem I 0)"

primrec rr_regex where
  "rr_regex rr (Regex.Skip n) = {}"
| "rr_regex rr (Regex.Test \<phi>) = rr \<phi>"
| "rr_regex rr (Regex.Plus r s) = rr_regex rr r \<inter> rr_regex rr s"
| "rr_regex rr (Regex.Times r s) = rr_regex rr r \<union> rr_regex rr s"
| "rr_regex rr (Regex.Star r) = {}"

primrec tvars where
 "tvars (Formula.Var v) = [v]"
|"tvars (Formula.Const c) = []"
|"tvars (Formula.F2i t) = tvars t"
|"tvars (Formula.I2f t) = tvars t"
|"tvars (Formula.UMinus t) = tvars t"
|"tvars (Formula.Plus t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Minus t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Mult t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Div t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Mod t1 t2) =  (tvars t1)@ (tvars t2)"

primrec rr :: "nat \<Rightarrow> 'a rformula \<Rightarrow> nat set" where
  "rr b (RPred r ts) = (\<Union>t\<in>set ts. Formula.fvi_trm b t)"
| "rr b (RLet p \<phi> \<psi>) = rr b \<psi>"
| "rr b (RLetPast p \<phi> \<psi>) = rr b \<psi>"
| "rr  b(REq t1 t2) = (case (t1,t2) of
                             (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                            |(Formula.Const _,Formula.Var x) \<Rightarrow> {x-b}
                            | _ \<Rightarrow> {})"

| "rr b (RLess t1 t2) = (case (t1,t2) of
                        (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                        |_ \<Rightarrow> {})"
| "rr b (RLessEq t1 t2) = (case (t1,t2) of
                                              (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                                             |_ \<Rightarrow> {})"
| "rr b (ROr \<phi> \<psi>) =  (rr b \<phi>) \<inter> (rr b \<psi>)"
| "rr b (RAnd \<phi> \<psi>) = rr b \<psi> \<union> (rr b \<phi>)"
| "rr b (RAnds \<phi>s) = (let xs = map (rr b) \<phi>s in \<Union>x\<in>set xs. x)"
| "rr b (RExists t \<phi>) = (if (0 \<in> (rr 0 \<phi>)) then rr (Suc b) \<phi>
                                            else {})"
| "rr b (RAgg y \<omega> b' f \<phi>) = (if {0..<length b'} \<subseteq> rr 0 \<phi> then {y} \<union> rr (b + length b') \<phi>
                                                   else {})" (*How?*)
| "rr b (RPrev I \<phi>) = rr b \<phi>"
| "rr b (RNext I \<phi>) = rr b \<phi>"
| "rr b (RSince \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RUntil \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RRelease \<phi> I \<psi>) = (if excl_zero I then {} else rr b \<psi>)"
| "rr b (RTrigger \<phi> I \<psi>) = (if excl_zero I then {} else rr b \<psi>)"
| "rr b (RMatchF I r) = {}" (*rr_regex should have been used here*)
| "rr b (RMatchP I r) = {}" (*and here*)
| "rr b (RNeg \<alpha>) = {}"
| "rr b (RDiamondW I \<alpha>) = rr b \<alpha>"
| "rr b (RDiamondB I \<alpha>) = rr b \<alpha>"
| "rr b (RSquareW I \<alpha>) = (if excl_zero I then {} else rr b \<alpha>)"
| "rr b (RSquareB I \<alpha>) = (if excl_zero I then {} else rr b \<alpha>)"
| "rr b (RTP t) = Formula.fvi_trm b t"
| "rr b (RTS t) = Formula.fvi_trm b t"

abbreviation fvi_r where
      "fvi_r b r \<equiv> Formula.fvi b (project r)"

definition prop_cond :: "'a rformula \<Rightarrow> 'a rformula \<Rightarrow> bool"where
 "prop_cond f1 f2 =
       (let rr1 = rr 0 f1;
            rr2 = rr 0 f2;
            fv2 = fvi_r 0 f2
        in (rr1 \<inter> (fv2-rr2))\<noteq> {})"

(*Section 2 of Normalization*)
lemma sat_2_1: "(\<forall>x. Formula.sat \<sigma> V (x#v) i \<alpha>) = Formula.sat \<sigma> V v i (Formula.Neg (Formula.Exists t (Formula.Neg \<alpha>)))" by simp
lemma sat_2_2: "(Formula.sat \<sigma> V v i \<alpha> \<longrightarrow> Formula.sat \<sigma> V v i \<beta>) = (Formula.sat \<sigma> V v i (Formula.Or (Formula.Neg \<alpha>) \<beta>))" by simp
lemma sat_2_3: "(Formula.sat \<sigma> V v i \<alpha> \<longleftrightarrow> Formula.sat \<sigma> V v i \<beta>) =
                (Formula.sat \<sigma> V v i (Formula.And (Formula.Or (Formula.Neg \<alpha>) \<beta>)(Formula.Or (Formula.Neg \<beta>) \<alpha>)))" by auto

(*------------setup and lemmas about shifting valuation list----------------------------*)

fun shiftTI :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
 "shiftTI k (Formula.Var i) = (if i < k then Formula.Var i
                                               else Formula.Var (i + 1))"
| "shiftTI k (Formula.Plus t u) = Formula.Plus (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Minus t u) = Formula.Minus (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.UMinus t) = Formula.UMinus (shiftTI k t)"
| "shiftTI k (Formula.Mult t u) = Formula.Mult (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Div t u) = Formula.Div (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Mod t u) = Formula.Mod (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.F2i t) = Formula.F2i (shiftTI k t)"
| "shiftTI k (Formula.I2f t) = Formula.I2f (shiftTI k t)"
| "shiftTI k (Formula.Const n) = (Formula.Const n)"

lemma eval_trm_shiftTI: "length xs = b \<Longrightarrow>
  Formula.eval_trm (xs @ z # v) (shiftTI b t) = Formula.eval_trm (xs @ v) t"
  by (induct b t rule: shiftTI.induct) (auto simp: nth_append split: trm.splits)

lemma shift_fv_in_t: "x+1 \<in> Formula.fvi_trm b (shiftTI b t) \<longleftrightarrow> x  \<in> Formula.fvi_trm b t"
   by (induction t;auto)

primrec shiftI :: "nat \<Rightarrow> 'a Formula.formula \<Rightarrow> 'a Formula.formula" where
  "shiftI k (Formula.Pred r ts) = Formula.Pred r (map (shiftTI k) ts)"
| "shiftI k (Formula.Exists t a) = Formula.Exists t (shiftI (Suc k) a)"
| "shiftI k (Formula.Let nm a b) = Formula.Let nm a (shiftI k b)" (*fixed error, a is not shifted*)
| "shiftI k (Formula.LetPast nm a b) = Formula.LetPast nm a (shiftI k b)"
| "shiftI k (Formula.Eq t1 t2) = Formula.Eq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.Less t1 t2) =  Formula.Less (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.LessEq t1 t2) = Formula.LessEq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.Neg a) = Formula.Neg (shiftI k a)"
| "shiftI k (Formula.Or a b) = Formula.Or (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.And a b) = Formula.And (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.Ands as) = Formula.Ands (map (shiftI k) as)"
| "shiftI k (Formula.Agg y op b t a) = Formula.Agg (if y < k then y else y + 1)
                                            op b (shiftTI (k + length b) t) (shiftI (k + length b) a)"
| "shiftI k (Formula.Prev \<I> a) = Formula.Prev \<I> (shiftI k a)"
| "shiftI k (Formula.Next \<I> a) = Formula.Next \<I> (shiftI k a)"
| "shiftI k (Formula.Since a1 \<I> a2) = Formula.Since (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (Formula.Until a1 \<I> a2) = Formula.Until (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (Formula.MatchF \<I> r) = Formula.MatchF \<I> (Regex.map_regex (shiftI k) r)"
| "shiftI k (Formula.MatchP \<I> r) = Formula.MatchP \<I> (Regex.map_regex (shiftI k) r)"
| "shiftI k (Formula.TP t) = Formula.TP (shiftTI k t)"
| "shiftI k (Formula.TS t) = Formula.TS (shiftTI k t)"

abbreviation shift where "shift \<equiv> shiftI 0"

primrec shiftI_r :: "nat \<Rightarrow> 'a rformula \<Rightarrow> 'a rformula" where
  "shiftI_r k (RPred r ts) = RPred r (map (shiftTI k) ts)"
| "shiftI_r k (RExists t a) = RExists t (shiftI_r (Suc k) a)"
| "shiftI_r k (RLet nm a b) = RLet nm a (shiftI_r k b)" (*fixed error, a is not shifted*)
| "shiftI_r k (RLetPast nm a b) = RLetPast nm a (shiftI_r k b)"
| "shiftI_r k (REq t1 t2) = REq (shiftTI k t1) (shiftTI k t2)"
| "shiftI_r k (RLess t1 t2) =  RLess (shiftTI k t1) (shiftTI k t2)"
| "shiftI_r k (RLessEq t1 t2) = RLessEq (shiftTI k t1) (shiftTI k t2)"
| "shiftI_r k (RNeg a) = RNeg (shiftI_r k a)"
| "shiftI_r k (ROr a b) = ROr (shiftI_r k a) (shiftI_r k b)"
| "shiftI_r k (RAnd a b) = RAnd (shiftI_r k a) (shiftI_r k b)"
| "shiftI_r k (RAnds as) = RAnds (map (shiftI_r k) as)"
| "shiftI_r k (RAgg y op b t a) = RAgg (if y < k then y else y + 1)
                                            op b (shiftTI (k + length b) t) (shiftI_r (k + length b) a)"
| "shiftI_r k (RPrev \<I> a) = RPrev \<I> (shiftI_r k a)"
| "shiftI_r k (RNext \<I> a) = RNext \<I> (shiftI_r k a)"
| "shiftI_r k (RSince a1 \<I> a2) = RSince (shiftI_r k a1) \<I> (shiftI_r k a2)"
| "shiftI_r k (RUntil a1 \<I> a2) = RUntil (shiftI_r k a1) \<I> (shiftI_r k a2)"
| "shiftI_r k (RRelease a1 \<I> a2) = RRelease (shiftI_r k a1) \<I> (shiftI_r k a2)"
| "shiftI_r k (RTrigger a1 \<I> a2) = RTrigger (shiftI_r k a1) \<I> (shiftI_r k a2)"
| "shiftI_r k (RDiamondW \<I> a2) = RDiamondW \<I> (shiftI_r k a2)"
| "shiftI_r k (RDiamondB \<I> a2) = RDiamondB \<I> (shiftI_r k a2)"
| "shiftI_r k (RSquareB \<I> a2) = RSquareB \<I> (shiftI_r k a2)"
| "shiftI_r k (RSquareW \<I> a2) = RSquareW \<I> (shiftI_r k a2)"
| "shiftI_r k (RMatchF \<I> r) = RMatchF \<I> (Regex.map_regex (shiftI_r k) r)"
| "shiftI_r k (RMatchP \<I> r) = RMatchP \<I> (Regex.map_regex (shiftI_r k) r)"
| "shiftI_r k (RTP t) = RTP (shiftTI k t)"
| "shiftI_r k (RTS t) = RTS (shiftTI k t)"


lemma project_shift: "project (shiftI_r b \<alpha>) = shiftI b (project \<alpha>)"
proof(induct \<alpha> arbitrary: b)
next
  case (RMatchF I r)
  then show ?case by (induction r;auto)
next
  case (RMatchP I r)
  then show ?case by (induction r;auto)
qed (auto simp: Formula.TT_def)

lemma shift_fv_in_f: "(x+1) \<in> (Formula.fvi b (shiftI b \<phi>)) \<longleftrightarrow> x \<in> (Formula.fvi b \<phi>)"
using shift_fv_in_t proof (induction b \<phi> rule: fvi.induct)
  case (17 b I r)
  then show ?case by (induct r;auto)
next
  case (18 b I r)
  then show ?case by (induct r;auto)
qed (auto)


lemma no_shift_t:  "b' \<le> x3 \<Longrightarrow> Formula.fvi_trm b' (shiftTI (b + x3) t) \<subseteq> {0..<x3-b'} \<longleftrightarrow> Formula.fvi_trm b' t \<subseteq> {0..<x3-b'}"
  by (induction t; auto)

lemma no_shift:  "b' \<le> x3 \<Longrightarrow> Formula.fvi b' (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3-b'} \<longleftrightarrow> Formula.fvi b' \<phi> \<subseteq> {0..<x3-b'}" (*MEETING: Do we want if on the top-lemma level?*)
proof(induction \<phi> arbitrary: b' x3)
  case (Ands x)
  then show ?case
    by fastforce (*MEETING: why do I have to instansiate b'? A: To obtain a faster proof by auto *)
next
  case (Pred r ts)
  thm no_shift_t[OF Pred(1)]
  then have helper: "((\<Union>a\<in>set ts. Formula.fvi_trm b' (shiftTI (b + x3) a)) \<subseteq> {0..<x3 - b'}) =
                     (\<Union> (Formula.fvi_trm b' ` set ts) \<subseteq> {0..<x3 - b'})" using no_shift_t[OF Pred(1)] by (auto;simp)
  from Pred helper show ?case by auto
next
  case (Exists \<phi>)
  from Exists(2) have suc_lemma: "Suc b' \<le> Suc x3" by simp
  from Exists(1)[OF suc_lemma] show ?case by simp
next
  case (Agg xy op bb' t \<phi>)
  define bb where [simp]: "bb = length bb'"
  from Agg(2) have plusbb: "b' + bb \<le> x3+bb" by simp
  from Agg(1)[OF plusbb] have helper1: "(Formula.fvi (b' + bb) (shiftI (b + (x3 + bb)) \<phi>)) \<subseteq> {0..<x3 - b'} =
                 ((Formula.fvi (b' + bb) \<phi>)  \<subseteq> {0..<x3 - b'})" by simp


  from no_shift_t[OF plusbb] have helper2: "(Formula.fvi_trm (b' + bb) (shiftTI (b + (x3 + bb)) t) \<subseteq> {0..<x3 - b'}) =
                                            (Formula.fvi_trm (b' + bb) t \<subseteq> {0..<x3 - b'}) " by simp

  from plusbb have helper3: "((if b' \<le> (if xy < b + x3 then xy else xy + 1) then {(if xy < b + x3 then xy else xy + 1) - b'} else {}) \<subseteq> {0..<x3 - b'}) =
                 ((if b' \<le> xy then {xy - b'} else {}) \<subseteq> {0..<x3 - b'})" by auto

  have helper: "(Formula.fvi (b' + bb) (shiftI (b + (x3 + bb)) \<phi>) \<union>
                Formula.fvi_trm (b' + bb) (shiftTI (b + (x3 + bb)) t) \<union>
                (if b' \<le> (if xy < b + x3 then xy else xy + 1) then {(if xy < b + x3 then xy else xy + 1) - b'} else {}) \<subseteq> {0..<x3 - b'}) =
                (Formula.fvi (b' + bb) \<phi> \<union>
                Formula.fvi_trm (b' + bb) t \<union>
                (if b' \<le> xy then {xy - b'} else {}) \<subseteq> {0..<x3 - b'})" 
    by (simp add: helper1 helper2 helper3 del:bb_def)
  have assoc: "b + x3 + bb = b + (x3 + bb)" by simp
  show ?case by (simp only: shiftI.simps fvi.simps helper assoc flip:bb_def) (*'simp only' because we aim for the helper-lemma as the last goal*)
next
  case (MatchF I r)
  then show ?case by (induction r;auto)
next
  case (MatchP I r)
  then show ?case by (induction r;auto)
qed (auto simp: no_shift_t)

lemma match_map_regex: "(\<And>k a. a \<in> Regex.atms r \<Longrightarrow> sat k (f a) \<longleftrightarrow> sat' k a) \<Longrightarrow>
  Regex.match sat (regex.map_regex f r) = Regex.match sat' r"
  by (induction r) simp_all

lemma sat_shift: "length xs = b \<Longrightarrow> Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (xs@v) i \<phi>"
proof(induction \<phi> arbitrary: V i xs b)
  case pred: (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ z # v) \<circ> shiftTI (length xs)) ts
             = map (Formula.eval_trm (xs @ v)) ts" by (auto simp:eval_trm_shiftTI)
  from pred show ?case by (auto split:option.splits simp:map_lemma)
  case (Exists \<phi>)
  then show ?case using Exists.IH[where xs= "_ # xs" and b="Suc b"] by (auto)
next
  case (Agg x1 x2 x3' x4 \<phi>)
  define x3 where [simp]:"x3 = length x3'"
  have rw11: "Formula.sat \<sigma> V (zs @ xs @ z # v) i (shiftI (b + x3) \<phi>) \<longleftrightarrow>
    Formula.sat \<sigma> V (zs @ xs @ v) i \<phi>" if "length zs = x3" for zs
    using Agg(1)[of "zs @ xs"] Agg(2) that
    by simp
  have rw12:
    "Formula.eval_trm (zs @ xs @ z # v) (shiftTI (b + x3) x4) =
    Formula.eval_trm (zs @ xs @ v) x4" if "length zs = x3" for zs
    using eval_trm_shiftTI[of "zs @ xs"] Agg(2) that
    by simp
  have rw1: "\<And>x. {zs. length zs = x3 \<and>
      Formula.sat \<sigma> V (zs @ xs @ z # v) i (shiftI (b + x3) \<phi>) \<and>
      Formula.eval_trm (zs @ xs @ z # v) (shiftTI (b + x3) x4) = x} =
    {zs. length zs = x3 \<and>
      Formula.sat \<sigma> V (zs @ xs @ v) i \<phi> \<and> Formula.eval_trm (zs @ xs @ v) x4 = x}"
    using rw11 rw12 by auto
  have rw2: "fv (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3} \<longleftrightarrow> fv \<phi> \<subseteq> {0..<x3}" 
    using no_shift[where b'=0]
    apply (auto simp del:x3_def) using atLeastLessThan_iff by blast
  show ?case
    using Agg(2)
    by (auto simp add: rw1 rw2 nth_append simp flip:x3_def)
next
  case (Prev x1 \<phi>)
  then show ?case by (auto split:nat.splits)
next
  case (MatchF I r)
  have rw: "Regex.match (Formula.sat \<sigma> V (xs @ z # v)) (regex.map_regex (shiftI b) r) =
    Regex.match (Formula.sat \<sigma> V (xs @ v)) r"
    apply (rule match_map_regex)
    using MatchF
    by auto
  show ?case
    using MatchF
    by (simp add: rw)
next
  case (MatchP I r)
  have rw: "\<And>j. Regex.match (Formula.sat \<sigma> V (xs @ z # v)) (regex.map_regex (shiftI b) r) =
    Regex.match (Formula.sat \<sigma> V (xs @ v)) r"
    apply (rule match_map_regex)
    using MatchP
    by auto
  show ?case
    by (simp add: rw)
qed (auto simp: eval_trm_shiftTI)





(*Section 3 of Normalization chapter p. 79*)
lemma sat_3_a: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Neg \<alpha>)) = Formula.sat \<sigma> V v i \<alpha>" by auto
lemma sat_3_b: "Formula.sat \<sigma> V v i (Formula.Exists t (shiftI 0 \<alpha>)) = Formula.sat \<sigma> V v i \<alpha>" using sat_shift[of "[]"] by auto (*Uses lemma proved in previous section*)
lemma sat_3_c1: "Formula.sat \<sigma> V v i (Formula.Neg(Formula.Or \<alpha> \<beta>)) = Formula.sat \<sigma> V v i (Formula.And (Formula.Neg \<alpha>) (Formula.Neg \<beta>)) " by auto
lemma sat_3_c2: "Formula.sat \<sigma> V v i (Formula.Neg(Formula.And \<alpha> \<beta>)) = Formula.sat \<sigma> V v i (Formula.Or (Formula.Neg \<alpha>) (Formula.Neg \<beta>)) " by auto

lemma sat_3_d: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Next I \<alpha>)) =
  Formula.sat \<sigma> V v i (Formula.Or (Formula.Neg (Formula.Next I Formula.TT))
                                  (Formula.Next I (Formula.Neg \<alpha>)))"  (*MEETING: So we are bloating up the formula because we want
                                                                        to push a negation closer to \<alpha>?*)
  by auto

(*Abbreviations corresponding to syntactic sugar presented in the phd-thesis*)
(*lemma FF_simp: "FF = Formula.FF" by (simp add: Formula.FF_def)
lemma TT_simp: "TT = Formula.TT" by (simp add: Formula.TT_def FF_simp)*)



(*Maybe interesting lemma for intution*)
lemma strict_until: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until \<phi> I \<psi>) =
                                    (\<exists>j>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i..< j}. Formula.sat \<sigma> V v k \<phi>))"  using le_eq_less_or_eq by auto

(*duplications of sat_3_f*  not needed*)
(*
lemma sat_3_e1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (diamond_w I \<alpha>)) = Formula.sat \<sigma> V v i (square_w I (Formula.Neg \<alpha>))"
  by simp

lemma sat_3_e2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (square_w I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_w I (Formula.Neg \<alpha>))"
  by auto

lemma sat_3_e3: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (diamond_b I \<alpha>)) = Formula.sat \<sigma> V v i (square_b I (Formula.Neg \<alpha>))"
  by auto

lemma sat_3_e4: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (square_b I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_b I (Formula.Neg \<alpha>))"
  by auto*)

lemma sat_3_f1: "Formula.sat \<sigma> V v i (Formula.Neg (diamond_w I \<alpha>)) = Formula.sat \<sigma> V v i (square_w I (Formula.Neg \<alpha>))"
  by simp

lemma sat_3_f2: "Formula.sat \<sigma> V v i (Formula.Neg (square_w I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_w I (Formula.Neg \<alpha>))"
  by auto

lemma sat_3_f3: "Formula.sat \<sigma> V v i (Formula.Neg (diamond_b I \<alpha>)) = Formula.sat \<sigma> V v i (square_b I (Formula.Neg \<alpha>))"
  by auto

lemma sat_3_f4: "Formula.sat \<sigma> V v i (Formula.Neg (square_b I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_b I (Formula.Neg \<alpha>))"
  by auto

abbreviation (input) release where "release \<beta> I \<gamma> \<equiv> Formula.Neg (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) )"
abbreviation trigger where "trigger \<beta> I \<gamma> \<equiv> Formula.Neg (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) )"

abbreviation release2 where "release2 \<beta> I \<gamma> \<equiv> Formula.And (Formula.Neg (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) ))
                                                          (diamond_w I Formula.TT)"


lemma sat_release2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (release2 \<beta> I \<gamma>) \<Longrightarrow>
                     (\<exists>j>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> ( Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)))" by fastforce

(*Duplication again*)
(*
lemma sat_3_g1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (Formula.Since \<beta> I \<gamma>)) =
                                 Formula.sat \<sigma> V v i (trigger (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by simp

lemma sat_3_g2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (Formula.Until \<beta> I \<gamma>)) =
                                 Formula.sat \<sigma> V v i (release (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by simp

lemma sat_3_h1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (trigger \<beta> I \<gamma>)) =
                                 Formula.sat \<sigma> V v i (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_h2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (release \<beta> I \<gamma>)) =
                                 Formula.sat \<sigma> V v i (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto*)

lemma sat_3_i1: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Since \<beta> I \<gamma>)) =
                 Formula.sat \<sigma> V v i (trigger (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_i2: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Until \<beta> I \<gamma>)) =
                 Formula.sat \<sigma> V v i (release (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by force

lemma sat_3_j1: "Formula.sat \<sigma> V v i (Formula.Neg (trigger \<beta> I \<gamma>)) =
                 Formula.sat \<sigma> V v i (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_j2: "Formula.sat \<sigma> V v i (Formula.Neg (release \<beta> I \<gamma>)) =
                 Formula.sat \<sigma> V v i (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto


(*Reasoning about intervals including 0*)
lift_definition init_int :: "\<I> \<Rightarrow> \<I>" is "\<lambda>(_,r,n). ((\<lambda>k. True),r,n)" 
  using zero_enat_def upclosed_def by auto

lemma left_init_int[simp]: "memL (init_int I) 0"  by (transfer; auto)+
lemma right_init_int[simp]: "memR (init_int I) = memR I"  by (transfer; auto)+

lemma interval_imp: "mem I i \<Longrightarrow> mem (init_int I) i" apply auto 
  using left_init_int memL_mono by blast


lemma nat_less_than_range: "\<And>i j:: nat. k \<in> {i..j} \<and> k' \<in>{i..j} \<Longrightarrow> (k-k') \<le> (j-i)"
proof -
  fix i j :: nat assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}"
  show "(k-k') \<le> (j-i)"
  proof(cases "i\<le>j")
  case True
  then show ?thesis using A diff_le_mono2 by auto
next
  case False
  then show ?thesis using A by auto
qed
qed

lemma mem_of_init: "mem I j \<Longrightarrow>  \<forall>k\<le>j. mem (init_int I) k"
proof(induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then show ?case 
  by (metis left_init_int memL_mono memR_antimono right_init_int zero_le)
qed

(*Main lemma used multiple times*)
lemma nat_less_mem_of_init: "\<And>i j:: nat. k \<in> {i..j} \<and> k' \<in>{i..j} \<Longrightarrow> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow>  mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> k')"
proof -
  fix i j :: nat assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  then have "(\<tau> \<sigma> k - \<tau> \<sigma> k') \<le> (\<tau> \<sigma> j - \<tau> \<sigma> i)" using nat_less_than_range by auto
  then show " mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> k')" using A(2) mem_of_init by blast
qed


(*Equivalences*)

(*excl_zero I assumption needed to ensure alpha is satisfiable in some range*)
lemma equiv_1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until \<alpha> I \<beta>) = Formula.sat \<sigma> V v i (Formula.Until \<alpha> I (Formula.And (diamond_b I \<alpha>) \<beta>))" by fastforce

lemma equiv_2: "Formula.sat \<sigma> V v i (Formula.Until \<alpha> I \<beta>) = Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> (diamond_w (init_int I) \<beta>) ) I \<beta>)"
(is "?L = ?R")
proof(rule iffI)
  assume ass:?L
  then obtain j where j: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<beta>" "(\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<alpha>)" by auto
  then have "\<forall>k\<in>{i..<j}.j\<ge>k " by auto
  moreover have "\<forall>k\<in>{i..<j}. mem (init_int I) (\<tau> \<sigma> j - \<tau> \<sigma> k)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v j \<beta>" using j(3) by auto
  ultimately have "\<forall>k\<in>{i..<j}. (\<exists>j\<ge>k. mem (init_int I) (\<tau> \<sigma> j - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v j \<beta>)" by fast
  then show ?R using j by auto
qed auto

lemma equiv_3: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Since \<alpha> I \<beta>) = Formula.sat \<sigma> V v i (Formula.Since \<alpha> I (Formula.And (diamond_w I \<alpha>) \<beta>))" by fastforce

lemma equiv_4: " Formula.sat \<sigma> V v i (Formula.Since \<alpha> I \<beta>)  = Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> (diamond_b (init_int I) \<beta>) ) I \<beta>)"
(is "?L = ?R")
proof(rule iffI)
  assume ass:?L
  then obtain j where j: "j\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<beta>" "(\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<alpha>)" by auto
  then have "\<forall>k\<in>{j<..i}.j\<le>k " by auto
  moreover have "\<forall>k\<in>{j<..i}. mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> j)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v j \<beta>" using j(3) by auto
  ultimately have "\<forall>k\<in>{j<..i}. (\<exists>j\<le>k. mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<beta>)" by fast
  then show ?R using j by auto
qed auto
(*rules 5-8 is covered by next sections rewriteC rules 10-13*)


lemma   sat_main_1:
  "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) =
   Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<alpha> \<beta>) (Formula.And \<alpha> \<gamma>))"
  by auto

lemma sat_main_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists t \<beta>)) =
                    Formula.sat \<sigma> V v i (Formula.Exists t (Formula.And (shift \<alpha>) \<beta> ))"
  using sat_shift[of "[]"] by auto

lemma sat_main_5: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Neg \<beta>))  =
                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Neg (Formula.And \<alpha> \<beta>)))"
  by auto

lemma sat_main_6: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_w I \<alpha>) \<beta>))" by fastforce

lemma sat_main_7: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_b I \<alpha>) \<beta>))" by fastforce


lemma sat_main_12: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I (Formula.And (diamond_w I \<alpha>)\<beta>)))" by auto

lemma sat_main_13: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I (Formula.And (diamond_b I \<alpha>)\<beta>)))" by auto


(*Duplications *)
(*lemma sat_main_14: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_main_15: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_main_16: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_main_17: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto*)

lemma sat_main_18: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_main_19: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_main_20: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_main_21: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_main_22: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Prev I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Prev I (Formula.And (Formula.Next I \<alpha>) \<beta>)))"  by (auto split: nat.splits)

lemma sat_main_23: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Next I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Next I (Formula.And (Formula.Prev I \<alpha>) \<beta>)))" by auto

(*Non-trivial rewriteCs gathered together*)

lemma sat_main_2: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (release \<beta> I \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (release (Formula.And \<beta> (diamond_b (init_int I) \<alpha>)) I (Formula.And \<gamma> (diamond_b I \<alpha>))))"
(is "?L = ?R" )
proof(rule iffI)
  assume ass: "?L"
  then have split_A: "Formula.sat \<sigma> V v i \<alpha>"
                   "(\<And>j. j\<ge>i \<Longrightarrow> \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>))"
    by auto

  then have "(\<And>j. j\<ge>i \<Longrightarrow> \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or>
               (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<le>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ja))) \<or>
              (\<exists>k\<in>{i..<j}.
                  (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<le>k. mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<alpha> ))))"
  proof -
  fix j assume le:"j\<ge>i"
  then have " \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)" using ass by auto
  then consider (a) "\<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" |
                (b) "(Formula.sat \<sigma> V v j \<gamma>) \<and>  mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" |
                (c) "(\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)"  "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" by auto
  then show "(\<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or>
               (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<le>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ja))) \<or>
              (\<exists>k\<in>{i..<j}.
                  (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<le>k. mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<alpha> ))))"
  proof(cases)
    case a
    then show ?thesis by auto
  next
    case b
    then show ?thesis using le by auto
  next
    case c
    then show ?thesis using split_A(1) nat_less_mem_of_init[OF _ c(2)] by auto
  qed
qed
  then show ?R using split_A(1)  by auto
qed auto

lemma sat_main_3: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger (Formula.And \<beta> (diamond_w (init_int I) \<alpha>)) I (Formula.And \<gamma> (diamond_w I \<alpha>))))"
(is "?L = ?R" )
proof(rule iffI)
  assume ass: "?L"
  then have split_A: "Formula.sat \<sigma> V v i \<alpha>"
                     "(\<And>j. i\<ge>j \<Longrightarrow> \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>))" by auto
  then have "(\<And>j. i\<ge>j \<Longrightarrow> \<not>mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or>
              (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<ge>j. mem I (\<tau> \<sigma> ja - \<tau> \<sigma> j))) \<or>
              (\<exists>k\<in>{j<..i}. (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<ge>k. mem (init_int I) (\<tau> \<sigma> j - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v j \<alpha>))))"
  proof -
    fix j assume le:"i\<ge>j"
    then have " \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>)" using ass by auto
    then consider (a) "\<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" |
                  (b) "Formula.sat \<sigma> V v j \<gamma> \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" |
                  (c) "(\<exists>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>)" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" by auto
    then show "\<not>mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or>
              (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<ge>j. mem I (\<tau> \<sigma> ja - \<tau> \<sigma> j))) \<or>
              (\<exists>k\<in>{j<..i}. (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<ge>k. mem (init_int I) (\<tau> \<sigma> j - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v j \<alpha>)))"
  proof(cases)
    case a
    then show ?thesis by blast
  next
    case b
    then show ?thesis using le by auto
  next
    case c
    then show ?thesis using split_A(1) nat_less_mem_of_init[OF _ c(2)] by auto
  qed
qed
then show ?R using split_A(1) by auto
qed auto


lemma sat_main_8: "Formula.sat \<sigma> V v i (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>) ) =
                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_4 L] by fastforce
qed auto

lemma sat_main_9: "Formula.sat \<sigma> V v i (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_2 L] by fastforce
qed auto



lemma sat_main_10: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =
                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v i \<alpha> \<and> Formula.sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{j<..i}. mem (init_int I) (\<tau> \<sigma> i - \<tau> \<sigma> k)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto


lemma sat_main_11: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{i..<j}.  Formula.sat \<sigma> V v i \<alpha> \<and> Formula.sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{i..<j}. mem (init_int I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto

datatype argpos = Same | Swapped

fun size_argpos :: "argpos \<Rightarrow> nat"where
"size_argpos Same = 1"
| "size_argpos Swapped = 0"


primrec my_size_regex :: "('a \<Rightarrow> nat) \<Rightarrow> 'a Regex.regex \<Rightarrow> nat" where
  "my_size_regex fun (Regex.Skip n) = 0"
| "my_size_regex fun (Regex.Test \<phi>) = fun \<phi>"
| "my_size_regex fun (Regex.Plus r s) = my_size_regex fun r + my_size_regex fun s"
| "my_size_regex fun (Regex.Times r s) = my_size_regex fun r + my_size_regex fun s"
| "my_size_regex fun (Regex.Star r) = my_size_regex fun r"

lemma my_size_regex_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>z. z \<in> Regex.atms r \<Longrightarrow> fun z = fun' z) \<Longrightarrow> my_size_regex fun r = my_size_regex fun' r'"
  by (induct r arbitrary: r') auto

fun my_size_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
 "my_size_list fun (f#fs) = fun f + my_size_list fun fs"
| "my_size_list fun [] = 0"

lemma my_size_list_cong[fundef_cong]:
  "fs = fs' \<Longrightarrow> (\<And>z. z \<in> set fs \<Longrightarrow> fun z = fun' z) \<Longrightarrow> my_size_list fun fs = my_size_list fun' fs'"
  by (induct fs arbitrary: fs') auto


(*define custom size function because it ignores everything but layers of formula constructors*)
fun my_size :: "'a rformula \<Rightarrow> nat" where
  "my_size (RPred r ts) = 1"
| "my_size (RLet p \<phi> \<psi>) = 1"
| "my_size (RLetPast p \<phi> \<psi>) = 1"
| "my_size  (REq t1 t2) = 1"
| "my_size (RLess t1 t2) = 1"
| "my_size (RLessEq t1 t2) = 1"
| "my_size (ROr \<phi> \<psi>) =  1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RAnd \<phi> \<psi>) = 1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RAnds \<phi>s) = 1+ my_size_list my_size \<phi>s"
| "my_size (RExists t \<phi>) = 1 + my_size \<phi>"
| "my_size (RAgg y \<omega> b' f \<phi>) = 1 + (my_size \<phi>)"
| "my_size (RPrev I \<phi>) = 1+ my_size \<phi>"
| "my_size (RNext I \<phi>) = 1+ my_size \<phi>"
| "my_size (RSince \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RUntil \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RRelease \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RTrigger \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RMatchF I r) = 1 + (my_size_regex my_size r)"
| "my_size (RMatchP I r) = 1 + (my_size_regex my_size r)"
| "my_size (RNeg \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RDiamondW I \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RDiamondB I \<alpha>) =1 + my_size \<alpha>"
| "my_size (RSquareW I \<alpha>) =1 + my_size \<alpha>"
| "my_size (RSquareB I \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RTP t) = 1"
| "my_size (RTS t) = 1"


lemma ands_size: "my_size (RAnds rs) > my_size_list my_size rs " by simp
lemma my_size_neg_sub: "my_size a = my_size b \<Longrightarrow> my_size (RNeg a) = my_size (RNeg b)" by simp

lemma shift_size: "my_size (shiftI_r b \<alpha>) = my_size \<alpha>"
proof(induction \<alpha> arbitrary: b)
next
  case (RAnds x)
  then show ?case by (induction x;auto)
next
  case (RMatchF I r)
then show ?case by (induction r;auto)
next
  case (RMatchP I r)
  then show ?case by (induction r;auto)
qed auto

lemma not_zero: "my_size \<alpha> > 0" by (induction \<alpha>;auto)

fun fix_r where
 "fix_r (RSince l I r) Swapped = RSince r I l"
| "fix_r (RUntil l I r) Swapped = RUntil r I l"
| "fix_r r _ = r "

lemma not_swapped: "t \<noteq> Swapped \<Longrightarrow> t = Same" by (induction t;auto)


lemma fix_r_same: "fix_r r Same = r" by auto

declare regex.map_cong[fundef_cong]

lemma my_size_list_estimation[termination_simp]: "x \<in> set xs \<Longrightarrow> y < f x \<Longrightarrow> y < my_size_list f xs"
  by (induct xs) auto

lemma my_size_list_estimation'[termination_simp]: "x \<in> set xs \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> my_size_list f xs"
  by (induct xs) auto

lemma my_size_regex_estimation[termination_simp]: "x \<in> regex.atms r \<Longrightarrow> y < f x \<Longrightarrow> y < my_size_regex f r"
  by (induct r) auto

lemma my_size_regex_estimation'[termination_simp]: "x \<in> regex.atms r \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> my_size_regex f r"
  by (induct r) auto


function (sequential) rewrite :: "'a rformula \<Rightarrow> argpos \<Rightarrow> 'a rformula" where
(*1*)  "rewrite (RAnd \<alpha> (ROr \<beta> \<gamma>)) t =
       (if prop_cond \<alpha> \<beta> \<or> prop_cond \<alpha> \<gamma>
       then ROr (rewrite (RAnd \<alpha> \<beta>) Same) (rewrite (RAnd \<alpha> \<gamma>) Same)
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in RAnd \<alpha>' (ROr \<beta>' \<gamma>'))" (*added prop_cond gamma because the rewrite shouldn't be position dependent*)

(*2*) | "rewrite (RAnd \<alpha> (RRelease \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> Same) (RRelease (rewrite (RAnd \<beta> (RDiamondB (init_int I) \<alpha>)) Same) I (rewrite (RAnd \<gamma> (RDiamondB I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (RAnd \<alpha>' (RRelease \<beta>' I \<gamma>')))"

(*3*) | "rewrite (RAnd \<alpha> (RTrigger \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> Same) (RTrigger (rewrite (RAnd \<beta> (RDiamondW (init_int I) \<alpha>)) Same) I (rewrite (RAnd \<gamma> (RDiamondW I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (RAnd \<alpha>' (RTrigger \<beta>' I \<gamma>')))"

(*4*) | "rewrite (RAnd \<alpha> (RExists k \<beta>)) t =
       (if prop_cond \<alpha> \<beta>
        then RExists k (rewrite (RAnd (shiftI_r 0 \<alpha>) \<beta>) Same)
        else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RExists k \<beta>'))"

(*5*) | "rewrite (RAnd \<alpha> (RNeg \<beta>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> Same) ((RNeg (rewrite (RAnd \<alpha> \<beta>) Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RNeg \<beta>'))"

(*10,12*) | "rewrite (RAnd \<alpha> (RSince \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I) then RAnd (rewrite \<alpha> Same) (RSince (rewrite (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (bounded I) then RAnd (rewrite \<alpha> Same) (RSince (rewrite \<beta> Same) I (rewrite (RAnd (RDiamondW I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in RAnd \<alpha>' (RSince \<beta>' I \<gamma>'))"

(*11,13*) | "rewrite (RAnd \<alpha> (RUntil \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I) then RAnd (rewrite \<alpha> Same) (RUntil (rewrite (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (bounded I) then RAnd (rewrite \<alpha> Same) (RUntil (rewrite \<beta> Same) I (rewrite (RAnd (RDiamondB I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in RAnd \<alpha>' (RUntil \<beta>' I \<gamma>'))"

(*18*) | "rewrite (RAnd \<alpha> (RDiamondB I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I)
       then RAnd (rewrite \<alpha> Same) (RDiamondB I (RAnd (RDiamondW I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RDiamondB I \<beta>'))"

(*19*) | "rewrite (RAnd \<alpha> (RDiamondW I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RDiamondW I (RAnd (RDiamondB I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RDiamondW I \<beta>'))"

 (*20*) | "rewrite (RAnd \<alpha> (RSquareB I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I)
       then RAnd (rewrite \<alpha> Same) (RSquareB I (RAnd (RDiamondW I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RSquareB I \<beta>'))" (*some of these rules don't rewrite the conjunction, of diamond/square, because it doesn't increase rr of the conjunction more than recursing the leaves*)

 (*21*) | "rewrite (RAnd \<alpha> (RSquareW I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RSquareW I (RAnd (RDiamondB I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RSquareW I \<beta>'))"

 (*22*) | "rewrite (RAnd \<alpha> (RPrev I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RPrev I (RAnd (RNext I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RPrev I \<beta>'))"

(*23*) | "rewrite (RAnd \<alpha> (RNext I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RNext I (RAnd (RPrev I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in (RAnd \<alpha>' (RNext I \<beta>')))"

(*6 first, then 8*)
| "rewrite (RSince (RAnd \<alpha> \<gamma>) I \<beta>) t =
             (let l = rewrite (RAnd \<alpha> \<gamma>) Same;
                  r =      if t=Same \<and> excl_zero I \<and> prop_cond \<alpha> \<beta> then rewrite (RAnd (RDiamondW I \<alpha>) \<beta>) Same
                      else if t=Same \<and> excl_zero I \<and> prop_cond \<gamma> \<beta> then rewrite (RAnd (RDiamondW I \<gamma>) \<beta>) Same
                      else if t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta> then rewrite (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>) Same
                      else if t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta> then rewrite (RAnd (RDiamondB (init_int I) \<gamma>) \<beta>) Same
                      else rewrite \<beta> Same
              in fix_r (RSince l I r) t)"

(*7 first, else 9*) (*don't check bounded for 9 because rewrite doesn't alter monitorability for future unbounded temporal operators*)
| "rewrite (RUntil (RAnd \<alpha> \<gamma>) I \<beta>) t =
             (let l = rewrite (RAnd \<alpha> \<gamma>) Same;
                  r =      if t=Same \<and> excl_zero I \<and> prop_cond \<alpha> \<beta> then rewrite (RAnd (RDiamondB I \<alpha>) \<beta>) Same
                      else if t=Same \<and> excl_zero I \<and> prop_cond \<gamma> \<beta> then rewrite (RAnd (RDiamondB I \<gamma>) \<beta>) Same
                      else if t=Swapped \<and> prop_cond \<alpha> \<beta> then rewrite (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>) Same
                      else if t=Swapped \<and> prop_cond \<gamma> \<beta> then rewrite (RAnd (RDiamondW (init_int I) \<gamma>) \<beta>) Same
                      else rewrite \<beta> Same
              in fix_r (RUntil l I r) t)"

| "rewrite (RSince l I r) Same = rewrite (RSince r I l) Swapped"
| "rewrite (RUntil l I r) Same = rewrite (RUntil r I l) Swapped"
| "rewrite (RAnd l r) Same = rewrite (RAnd r l) Swapped"

| "rewrite (RSince l I r) Swapped = RSince (rewrite r Same) I (rewrite l Same)" (*swap back before recursing on subformulas*)
| "rewrite (RUntil l I r) Swapped =  RUntil (rewrite r Same) I (rewrite l Same)"
| "rewrite (RAnd l r) Swapped =  RAnd (rewrite r Same) (rewrite l Same)"

| "rewrite (ROr \<phi> \<psi>) t =  ROr (rewrite \<phi> Same) (rewrite \<psi> Same)"

| "rewrite (RExists k \<phi>) t = RExists k (rewrite \<phi> Same)"
| "rewrite (RAgg y \<omega> b' f \<phi>) t = RAgg y \<omega> b' f (rewrite \<phi> Same)"
| "rewrite (RPrev I \<phi>) t = RPrev I (rewrite \<phi> Same)"
| "rewrite (RNext I \<phi>) t = RNext I (rewrite \<phi> Same)"

| "rewrite (RRelease \<phi> I \<psi>) t = RRelease (rewrite \<phi> Same) I (rewrite \<psi> Same)"
| "rewrite (RTrigger \<phi> I \<psi>) t =  RTrigger (rewrite \<phi> Same) I (rewrite \<psi> Same)"

| "rewrite (RNeg \<alpha>) t = RNeg (rewrite \<alpha> Same)"
| "rewrite (RDiamondW I \<alpha>) t = RDiamondW I (rewrite \<alpha> Same)"
| "rewrite (RDiamondB I \<alpha>) t = RDiamondB I (rewrite \<alpha> Same)"
| "rewrite (RSquareW I \<alpha>) t = RSquareW I (rewrite \<alpha> Same)"
| "rewrite (RSquareB I \<alpha>) t = RSquareB I (rewrite \<alpha> Same)"

| "rewrite (RMatchF I r) t = RMatchF I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (RMatchP I r) t = RMatchP I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (RAnds \<phi>s) t = RAnds (map (\<lambda>r. rewrite r Same) \<phi>s)"

| "rewrite f t =  f"

  by pat_completeness auto
termination

 apply(relation "measures [(\<lambda>(f,t). my_size f),(\<lambda>(f,t). size_argpos t)]")
 apply (auto simp add:  shift_size not_zero ands_size map_cong termination_simp) (*not_zero important because size of constructor then depends on its' number of arguments*)
 done




inductive f_con where
f_con_1_t: "f_con (\<lambda>f1. Formula.Exists t f1)"|
f_con_2_t: "f_con (\<lambda>f1. Formula.Neg f1)" |
f_con_3_t: "f_con (\<lambda>f1. Formula.Until TT I f1)"|
f_con_4_t: "f_con (\<lambda>f1. Formula.Since TT I f1)" |
f_con_5_t: "f_con (\<lambda>f1. Formula.Next I f1)"|
f_con_6_t: "f_con (\<lambda>f1. Formula.Prev I f1)"


lemma sub_1: "f_con P \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>)) \<Longrightarrow> Formula.sat \<sigma> V v i (P (project \<alpha>)) = Formula.sat \<sigma> V v i (P (project \<beta>))"
proof(induction P arbitrary: v rule:f_con.induct)
case f_con_1_t
  then show ?case by simp
next
  case (f_con_6_t I)
  then show ?case by (simp split:nat.splits)
qed simp_all


inductive f_con2 where
f_con2_1_t: "f_con2 (\<lambda>f1 f2. Formula.Or f1 f2)" |
f_con2_2_t: "f_con2 (\<lambda>f1 f2. Formula.And f1 f2)" |
f_con2_3_t: "f_con2 (\<lambda>f1 f2. Formula.Neg (Formula.Until (Formula.Neg f1) I (Formula.Neg f2)))"|
f_con2_4_t: "f_con2 (\<lambda>f1 f2. Formula.Neg (Formula.Since (Formula.Neg f1) I (Formula.Neg f2)))" |
f_con2_5_t: "f_con2 (\<lambda>f1 f2. Formula.Since f1 I f2)"|
f_con2_6_t: "f_con2 (\<lambda>f1 f2. Formula.Until f1 I f2)"


lemma sub_2: "f_con2 P \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project a1) = Formula.sat \<sigma> V v i (project b1)) \<Longrightarrow>
                           (\<And>v i. Formula.sat \<sigma> V v i (project a2) = Formula.sat \<sigma> V v i (project b2)) \<Longrightarrow>
                                 Formula.sat \<sigma> V v i (P (project a1) (project a2)) = Formula.sat \<sigma> V v i (P (project b1) (project b2))"
  by(induction P rule:f_con2.induct;auto)

inductive f_con_agg where
f_con_agg_1_t: "f_con_agg (\<lambda>f1. Formula.Agg n1 op n2 t f1)"

lemma sub_agg: "f_con_agg P \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>)) \<Longrightarrow> fv (project \<alpha>) = fv (project \<beta>)
                          \<Longrightarrow> Formula.sat \<sigma> V v i (P (project \<alpha>)) = Formula.sat \<sigma> V v i (P (project \<beta>))"
proof(induction P rule: f_con_agg.induct)
  case (f_con_agg_1_t n1 op n2 t)
  then show ?case by simp
qed


lemma fvi_trm_shift: "b'\<le>b \<Longrightarrow> Formula.fvi_trm b t = Formula.fvi_trm (Suc b) (Rewriting.shiftTI b' t)"  by (induction t;auto)

lemma fvi_shift: "b' \<le> b \<Longrightarrow> Formula.fvi b \<phi> = Formula.fvi (Suc b) (Rewriting.shiftI b' \<phi>)"
proof(induction \<phi> arbitrary: b b')
  case (Agg x1 x2 x3 x4 \<phi>)
  then have le:"b' + length x3 \<le> b + length x3" by simp
  from Agg show ?case by(simp add:Agg(1)[OF le] fvi_trm_shift[OF le])
next
  case (MatchF I r)
  then show ?case by (induction r;auto)
next
  case (MatchP I r)
  then show ?case by (induction r;auto)
qed  (auto simp add: fvi_trm_shift)

lemma [simp]: "Formula.fvi b Formula.TT = {}"
  by (auto simp:Formula.TT_def)

lemma rewrite_fv: "Formula.fvi b (project \<alpha>) = Formula.fvi b (project (rewrite \<alpha> t))"
proof(induction \<alpha> t arbitrary:b rule:rewrite.induct)
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta> ")
    case True
    then show ?thesis using 2 by fastforce
  next
    case False
    then show ?thesis using 2 by auto
  qed
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta>")
    case T1:True
    then show ?thesis
    proof(cases "prop_cond \<beta> \<alpha>")
      case T2:True
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        thm 3(1)
        case True
        then show ?thesis using 3[where ?b=b] T1 T2 by auto
      next
        case False
        then show ?thesis using 3[where ?b=b] T1 T2 by auto
      qed
    next
      case F1:False
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        case True
        then show ?thesis using 3[where ?b=b] T1 F1 by auto
      next
        case False
        then show ?thesis using 3[where ?b=b] T1 F1 by auto
      qed
    qed
  next
    case F1:False
    then show ?thesis
      proof(cases "prop_cond \<beta> \<alpha>")
      case T2:True
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        case True
        then show ?thesis using 3 F1 T2 by auto
      next
        case False
        then show ?thesis using 3 F1 T2 by auto
      qed
    next
      case F1:False
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        case True
        then show ?thesis using 3[where ?b=b] F1 F1 by auto
      next
        case False
        then show ?thesis using 3[where ?b=b] F1 F1 by auto
      qed
    qed
  qed
next
  case (4 \<alpha> t \<beta>)
  then show ?case
    proof(cases "prop_cond \<alpha> \<beta>")
      case True
      have helper:"fvi_r b \<alpha>  = Formula.fvi (Suc b) (Rewriting.shift (project \<alpha>))" 
        using fvi_shift by auto
      from True show ?thesis using 4 helper
        apply(simp only:rewrite.simps if_True)
        apply(simp only:project1.simps project2.simps)
        apply(simp only:fvi.simps)
        apply(simp only: 4(1)[OF True,of "Suc b",symmetric])
        apply(simp only:project1.simps project2.simps)
        apply(simp only: project_shift)
        apply(simp only:fvi.simps)
        done
    next
      case False
      then show ?thesis using 4 by auto
    qed
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case
      apply(simp add: 6(1)[symmetric])
    by fastforce
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case
      apply(simp add: 7(1)[symmetric])
      by fastforce

next
  case (14 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> excl_zero I \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> excl_zero I \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a(*TODO use simplifier for these proofs, also prove shift_fv2*)
    then show ?thesis using 14
      apply(simp add: 14(1)[symmetric])
      by auto
  next
    case b
    then show ?thesis
    proof(cases "prop_cond \<alpha> \<beta>")
      case True
      then show ?thesis using b 14 by blast
    next
      case False
      then show ?thesis using b 14 by fastforce
    qed
  next
    case c
    then show ?thesis using 14
      apply(simp add: 14(1)[symmetric])
      by blast
  next
    case d
    then show ?thesis using 14
      apply(simp add: 14(1)[symmetric])
      by blast
  next
    case e
    then show ?thesis
      proof(cases "t=Swapped")
        case True
        then show ?thesis using e 14
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project1.simps project2.simps)
          by auto
      next
        case False
        then show ?thesis using e 14 not_swapped[OF False]
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project1.simps project2.simps)
          by auto
      qed
  qed
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> excl_zero I \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> excl_zero I \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a(*TODO use simplifier for these proofs, also prove shift_fv2*)
    then show ?thesis using 15
      apply(simp add: 15(1)[symmetric])
      by auto
  next
    case b
    then show ?thesis
    proof(cases "prop_cond \<alpha> \<beta>")
      case True
      then show ?thesis using b 15 by blast
    next
      case False
      then show ?thesis using b 15 by fastforce
    qed
  next
    case c
    then show ?thesis using 15
      apply(simp add: 15(1)[symmetric])
      by blast
  next
    case d
    then show ?thesis using 15
      apply(simp add: 15(1)[symmetric])
      by blast
  next
    case e
    then show ?thesis
      proof(cases "t=Swapped")
        case True
        then show ?thesis using e 15
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project1.simps project2.simps)
          by auto
      next
        case False
        then show ?thesis using e 15 not_swapped[OF False]
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project1.simps project2.simps)
          by auto
      qed
    qed
next
  case ("16_11" v va vb vc vd I r)
  then show ?case by fastforce
next
  case ("17_11" v va vb vc vd I r)
  then show ?case by fastforce
next

  case ("18_9" l v va vb vc vd)
  then show ?case by fastforce
next
  case (23 \<phi> t)
  then show ?case by simp
next
  case (24 y \<omega> b' f \<phi> t)
  then show ?case by simp
next
case (34 I r t)
  then show ?case by (induction r;auto)
next
  case (35 I r t)
  then show ?case by (induction r;auto)
qed auto



inductive f_conr where
f_conr_1_t: "f_conr (\<lambda>f1. RExists t f1)"|
f_conr_2_t: "f_conr (\<lambda>f1. RNeg f1)" |
f_conr_3_t: "f_conr (\<lambda>f1. RDiamondW I f1)"|
f_conr_4_t: "f_conr (\<lambda>f1. RDiamondB I f1)" |
f_conr_5_t: "f_conr (\<lambda>f1. RNext I f1)"|
f_conr_6_t: "f_conr (\<lambda>f1. RPrev I f1)"


inductive trans where
trans1: "trans (\<lambda>f1. RExists t f1) (\<lambda>f1. Formula.Exists t f1)" |
trans2: "trans (\<lambda>f1. RNeg f1) (\<lambda>f1. Formula.Neg f1)" |
trans3: "trans (\<lambda>f1. RDiamondW I f1) (\<lambda>f1. Formula.Until Formula.TT I f1)"|
trans4: "trans (\<lambda>f1. RDiamondB I f1)  (\<lambda>f1. Formula.Since Formula.TT I f1)" |
trans5: "trans (\<lambda>f1. RNext I f1) (\<lambda>f1. Formula.Next I f1)"|
trans6: "trans (\<lambda>f1. RPrev I f1) (\<lambda>f1. Formula.Prev I f1)"


lemma trans1: "trans P P' \<Longrightarrow> f_conr P \<and> f_con P' "
proof(induction P P' rule: trans.induct)
  case trans1
  then show ?case using f_conr_1_t f_con_1_t by auto
next
  case trans2
  then show ?case using f_conr_2_t f_con_2_t by auto
next
  case (trans3 I)
  then show ?case using f_conr_3_t f_con_3_t by auto
next
case (trans4 I)
  then show ?case using f_conr_4_t f_con_4_t by auto
next
  case (trans5 I)
  then show ?case using f_conr_5_t f_con_5_t by auto
next
  case (trans6 I)
  then show ?case using f_conr_6_t f_con_6_t by auto
qed

lemma trans2: "trans P P' \<Longrightarrow> project (P r) = P' (project r)"
  by(induction P P' rule:trans.induct;simp)

lemma trans3: "f_conr P \<Longrightarrow> \<exists>P'. trans P P'"
  using f_conr.simps trans.trans1 trans.trans2 trans3 trans4 trans5 trans6  by metis


lemma rsub_1: "f_conr P \<Longrightarrow> (\<And>v i. rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<beta>) \<Longrightarrow> rsat \<sigma> V v i (P \<alpha>) = rsat \<sigma> V v i (P \<beta>)"
proof -
  assume A: "f_conr P" "(\<And>v i. rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<beta>)"
  then obtain P2 where P2: "trans P P2" using trans3[OF A(1)] by auto
  moreover have L1: "f_con P2" using trans1[OF P2] by auto
  moreover have L2:"(\<And>v i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>))" using A(2) by (simp add:rsat_def)
  ultimately show ?thesis
    using Rewriting.trans2  sub_1 rsat_def by (smt (verit, best))
qed




inductive f_conr2 where
f_conr2_1_t: "f_conr2 (\<lambda>f1 f2. ROr f1 f2)" |
f_conr2_2_t: "f_conr2 (\<lambda>f1 f2. RAnd f1 f2)" |
f_conr2_3_t: "f_conr2 (\<lambda>f1 f2. RRelease f1 I f2)"|
f_conr2_4_t: "f_conr2 (\<lambda>f1 f2. RTrigger f1 I f2)" |
f_conr2_5_t: "f_conr2 (\<lambda>f1 f2. RSince f1 I f2)"|
f_conr2_6_t: "f_conr2 (\<lambda>f1 f2. RUntil f1 I f2)"

inductive trans2 where
trans2_1: "trans2 (\<lambda>f1 f2. ROr f1 f2)  (\<lambda>f1 f2. Formula.Or f1 f2)" |
trans2_2: "trans2 (\<lambda>f1 f2. RAnd f1 f2) (\<lambda>f1 f2. Formula.And f1 f2)" |
trans2_3: "trans2 (\<lambda>f1 f2. RRelease f1 I f2) (\<lambda>f1 f2. Formula.Neg (Formula.Until (Formula.Neg f1) I (Formula.Neg f2)))"|
trans2_4: "trans2 (\<lambda>f1 f2. RTrigger f1 I f2) (\<lambda>f1 f2. Formula.Neg (Formula.Since (Formula.Neg f1) I (Formula.Neg f2)))" |
trans2_5: "trans2 (\<lambda>f1 f2. RSince f1 I f2) (\<lambda>f1 f2. Formula.Since f1 I f2)"|
trans2_6: "trans2 (\<lambda>f1 f2. RUntil f1 I f2) (\<lambda>f1 f2. Formula.Until f1 I f2)"

lemma trans2_1: "trans2 P P' \<Longrightarrow> f_conr2 P \<and> f_con2 P' "
  unfolding f_con2.simps f_conr2.simps trans2.simps by auto

lemma trans2_2: "trans2 P P' \<Longrightarrow> project (P r r2) = P' (project r) (project r2)"
  by (induction P P' rule:trans2.induct;simp)

lemma trans2_3: "f_conr2 P \<Longrightarrow> \<exists>P'. trans2 P P'"
  apply(induction P rule:f_conr2.induct)
  using trans2.trans2_1 trans2.trans2_2 trans2.trans2_3 trans2.trans2_4 trans2.trans2_5 trans2.trans2_6 apply blast+
  done


lemma rsub_2: "f_conr2 P \<Longrightarrow> (\<And>v i. rsat \<sigma> V v i a1 = rsat \<sigma> V v i b1) \<Longrightarrow> (\<And>v i. rsat \<sigma> V v i a2 = rsat \<sigma> V v i b2) \<Longrightarrow> rsat \<sigma> V v i (P a1 a2) = rsat \<sigma> V v i (P b1 b2)"
proof -
  assume A: "f_conr2 P" "(\<And>v i. rsat \<sigma> V v i a1 = rsat \<sigma> V v i b1)" "(\<And>v i. rsat \<sigma> V v i a2 = rsat \<sigma> V v i b2)"
  then obtain P2 :: "('t Formula.formula \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula)"
    where P2: "trans2 P P2" using trans2_3[OF A(1)] by auto
  moreover have L1: "f_con2 P2" using trans2_1[OF P2] by auto
  moreover have L2:"(\<And>v i. Formula.sat \<sigma> V v i (project a1) = Formula.sat \<sigma> V v i (project b1))" using A(2) by (simp add:rsat_def)
  moreover have L3:"(\<And>v i. Formula.sat \<sigma> V v i (project a2) = Formula.sat \<sigma> V v i (project b2))" using A(3) by (simp add:rsat_def)
  ultimately show ?thesis
    using Rewriting.trans2_2 sub_2 rsat_def by (smt (verit, ccfv_SIG) Rewriting.trans2_1 \<open>\<And>thesis. (\<And>P2. trans2 P P2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
qed

inductive f_conr_agg where
f_conr_agg_t: "f_conr_agg (\<lambda>f1. RAgg n1 op n2 t f1)"

inductive trans_agg where
trans_agg_1: "trans_agg (\<lambda>f1. RAgg n1 op n2 t f1) (\<lambda>f1. Formula.Agg n1 op n2 t f1)"

lemma trans_agg_1: "trans_agg P P' \<Longrightarrow> f_conr_agg P \<and> f_con_agg P' "
  using f_con_agg.simps f_conr_agg.simps trans_agg.simps by blast

lemma trans_agg_2: "trans_agg P P' \<Longrightarrow> project (P r) = P' (project r)"
  by (induction P P' rule:trans_agg.induct;simp)

lemma trans_agg_3: "f_conr_agg P \<Longrightarrow> \<exists>P'. trans_agg P P'"
  apply(induction P rule:f_conr_agg.induct)
  using trans_agg.trans_agg_1 apply blast
  done

lemma rsub_agg: "f_conr_agg P \<Longrightarrow> (\<And>v i. rsat \<sigma> V v i a = rsat \<sigma> V v i b) \<Longrightarrow> fv (project a) = fv (project b)   \<Longrightarrow> rsat \<sigma> V v i (P a) = rsat \<sigma> V v i (P b)"
proof -
  assume A: "f_conr_agg P" "(\<And>v i. rsat \<sigma> V v i a = rsat \<sigma> V v i b)" "fv (project a) = fv (project b) "
  then obtain P2 where P2: "trans_agg P P2" using trans_agg_3[OF A(1)] by auto
  moreover have L1: "f_con_agg P2" using trans_agg_1[OF P2] by auto
  moreover have L2:"(\<And>v i. Formula.sat \<sigma> V v i (project a) = Formula.sat \<sigma> V v i (project b))" using A(2) by (simp add:rsat_def)
  ultimately show ?thesis
    using Rewriting.trans_agg_2 sub_agg[OF L1 L2 A(3)] rsat_def
    by fastforce
qed



abbreviation "rewrite_f a \<equiv> project (rewrite (embed a) Same)"




lemma rewrite_sat: "rsat \<sigma> V v i (rewrite r t) = rsat \<sigma> V v i (fix_r r t)"
proof(induction r t arbitrary: v i rule: rewrite.induct)
  case (1 \<alpha> \<beta> \<gamma> t)
  thm rsub_2[OF f_conr2_1_t 1(1-2)]
  then show ?case using sat_main_1 by (simp add:rsat_def)
next
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case using sat_main_2 by (simp add:rsat_def)
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case using sat_main_3 by (simp add:rsat_def)
next
  case (4 \<alpha> t \<beta>)

  then show ?case
  proof(cases "prop_cond \<alpha> \<beta>")
    case True
    moreover have "project (shiftI_r 0 \<alpha>) = shiftI 0 (project \<alpha>)" by (rule project_shift[of 0])
    ultimately show ?thesis using
       sat_main_4
      apply (simp only: fix_r.simps rewrite.simps if_True)
      apply(simp only: rsub_1[OF f_conr_1_t 4(1)[OF True] ] fix_r.simps)
      apply(simp only: rsat_def project1.simps  fix_r.simps project2.simps)(*remove embedding*)
      done
  next
    case False
    then show ?thesis
      apply(simp only: fix_r.simps rewrite.simps if_False Let_def)
      apply(simp only: rsub_2[OF f_conr2_2_t 4(2)[OF False] rsub_1[OF f_conr_1_t 4(3)[OF False refl]]] fix_r.simps)
      done
  qed
next
  case (5 \<alpha> \<beta> t)
  then show ?case
    using
             sat_main_5
    by (simp add:rsat_def)
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases"(prop_cond \<alpha> \<beta>) \<and> (bounded I)")
    case True
  then show ?thesis
    apply(simp only:rewrite.simps rsub_2[OF f_conr2_2_t 6(1)[OF True] rsub_2[OF f_conr2_5_t 6(2,3)[OF True]]] split:if_splits)
    apply(simp only: rsat_def project1.simps  fix_r.simps project2.simps)(*remove embedding*)
    apply(simp only: sat_main_10[symmetric]) (*rewrite lemma*)
    apply(simp)
    done
next
  case F1:False
  then show ?thesis
  proof(cases "(prop_cond \<alpha> \<gamma>) \<and> (bounded I)")
    case True
    then show ?thesis using F1
      apply(simp only: rewrite.simps rsub_2[OF f_conr2_2_t 6(4)[OF F1 True] rsub_2[OF f_conr2_5_t 6(5,6)[OF F1 True]]] split:if_splits)
      apply(simp only: rsat_def project1.simps  fix_r.simps project2.simps)(*remove embedding*)
    apply(simp only: sat_main_12[symmetric]) (*rewrite lemma*)
    apply(simp)
      done
next
  case False
  then show ?thesis using F1 6
    apply(simp only:rewrite.simps Let_def  split:if_splits)
    apply(simp only: rsub_2[OF f_conr2_2_t 6(7)[OF F1 False] rsub_2[OF f_conr2_5_t 6(8)[OF F1 False refl] 6(9)[OF F1 False refl refl]]])
    apply(simp)
      done
qed
qed

next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases"(prop_cond \<alpha> \<beta>) \<and> (bounded I)")
    case True
  then show ?thesis
    apply(simp only:rewrite.simps rsub_2[OF f_conr2_2_t 7(1)[OF True] rsub_2[OF f_conr2_6_t 7(2,3)[OF True]]] split:if_splits)
    apply(simp only: rsat_def project1.simps  fix_r.simps project2.simps)(*remove embedding*)
    apply(simp only: sat_main_11[symmetric]) (*rewrite lemma*)
    apply(simp)
    done
next
  case F1:False
  then show ?thesis
  proof(cases "(prop_cond \<alpha> \<gamma>) \<and> (bounded I)")
    case True
    then show ?thesis using F1
      apply(simp only: rewrite.simps rsub_2[OF f_conr2_2_t 7(4)[OF F1 True] rsub_2[OF f_conr2_6_t 7(5,6)[OF F1 True]]] split:if_splits)
      apply(simp only: rsat_def project1.simps  fix_r.simps project2.simps)(*remove embedding*)
    apply(simp only: sat_main_13[symmetric]) (*rewrite lemma*)
    apply(simp)
      done
next
  case False
  then show ?thesis using F1
    apply(simp only:rewrite.simps Let_def  split:if_splits)
    apply(simp only: rsub_2[OF f_conr2_2_t 7(7)[OF F1 False] rsub_2[OF f_conr2_6_t 7(8)[OF F1 False refl] 7(9)[OF F1 False refl refl]]])
    apply(simp)
      done
  qed
  qed
next
  case (8 \<alpha> I \<beta> t)
  then show ?case by (auto simp add:rsat_def)
next
  case (9 \<alpha> I \<beta> t)
  then show ?case  by (auto simp add:rsat_def)
next
case (10 \<alpha> I \<beta> t)
  then show ?case  by (auto simp add:rsat_def)
next
  case (11 \<alpha> I \<beta> t)
  then show ?case by (auto simp add:rsat_def)
next
  case (12 \<alpha> I \<beta> t)
  then show ?case
proof(cases "prop_cond \<alpha> \<beta> ")
  case True
  then show ?thesis using rsub_2[OF f_conr2_2_t 12(1)[OF True] rsub_1[OF f_conr_6_t rsub_2[OF f_conr2_2_t rsub_1[OF f_conr_5_t 12(1)[OF True]] 12(3)[OF True]]]] sat_main_22[symmetric]
    apply(simp only: rewrite.simps fix_r.simps  split:if_splits)
    apply(simp only: project1.simps project2.simps rsat_def)
    by simp
next
  case False
  then show ?thesis using rsub_2[OF f_conr2_2_t 12(4)[OF False] rsub_1[OF f_conr_6_t 12(5)[OF False refl]]] by simp
qed
next
  case (13 \<alpha> I \<beta> t)
  then show ?case by (auto simp add: rsat_def)
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> excl_zero I \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> excl_zero I \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a
    then have ex:"excl_zero I" by auto
    from a show ?thesis
          apply(simp del: sat.simps add: rsub_2[OF f_conr2_5_t 14(1) 14(2)[OF refl a ]]  split:if_splits )
        apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
          apply(simp only:sat_main_6[OF ex, symmetric])(*apply rewrite lemma*)
      done
  next
    case b
    then have ex:"excl_zero I" by auto
    have swap: "rsat \<sigma> V v i (RSince (RAnd \<alpha> \<gamma>) I (RAnd (RDiamondW I \<gamma>) \<beta>)) = rsat \<sigma> V v i (RSince (RAnd \<alpha> \<gamma>) I \<beta>) \<longleftrightarrow>
                rsat \<sigma> V v i (RSince (RAnd \<gamma> \<alpha>) I (RAnd (RDiamondW I \<gamma>) \<beta>)) = rsat \<sigma> V v i (RSince (RAnd \<gamma> \<alpha>) I \<beta>)" by(simp add: rsat_def;fast)
    from b show ?thesis using swap
      apply(simp only:rewrite.simps)
        apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(1) 14(3)[OF refl b]]  split:if_splits) (*remove recursion*)
      apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
        apply(rule sat_main_6[OF ex, symmetric])(*apply rewrite lemma*)
      done
next
  case c
  then show ?thesis
    apply(simp only:rewrite.simps)
        apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(4)[OF refl c] 14(1)]  split:if_splits) (*remove recursion*)
      apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
    apply(rule sat_main_8[symmetric])
    done
next
  case d
  have swap:"rsat \<sigma> V v i (RSince (RAnd (RDiamondB (init_int I) \<gamma>) \<beta>) I (RAnd \<alpha> \<gamma>)) =
             rsat \<sigma> V v i (RSince (RAnd (RDiamondB (init_int I) \<gamma>) \<beta>) I (RAnd \<gamma> \<alpha>))"
            "rsat \<sigma> V v i (RSince \<beta> I (RAnd \<alpha> \<gamma>)) = rsat \<sigma> V v i (RSince \<beta> I (RAnd \<gamma> \<alpha>))" using rsat_def by auto
  from d show ?thesis
    apply(simp only:rewrite.simps)
    apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(5)[OF refl d] 14(1)]  split:if_splits) (*remove recursion*)
    apply(simp only: swap)
    apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
    apply(rule sat_main_8[symmetric])
    done
next
  case e
  then show ?thesis
  proof(cases "t=Swapped")
    case True
    then show ?thesis using e
      apply(simp only:rewrite.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(6)[OF refl e]] 14(1)  split:if_splits) (*remove recursion*)
      done
  next
    case False
    then show ?thesis using e not_swapped[OF False]
      apply(simp only:rewrite.simps fix_r.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(1) 14(6)[OF refl e]]  split:if_splits) (*remove recursion*)
      done
  qed
qed
next
case (15 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> excl_zero I \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> excl_zero I \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a
    then have ex:"excl_zero I" by auto
    from a show ?thesis
          apply(simp del: sat.simps add: rsub_2[OF f_conr2_6_t 15(1) 15(2)[OF refl a ]]  split:if_splits )
        apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
          apply(simp only:sat_main_7[OF ex, symmetric])(*apply rewrite lemma*)
      done
  next
    case b
    then have ex:"excl_zero I" by auto
    have swap: "rsat \<sigma> V v i (RUntil (RAnd \<alpha> \<gamma>) I (RAnd (RDiamondB I \<gamma>) \<beta>)) = rsat \<sigma> V v i (RUntil (RAnd \<gamma> \<alpha>) I (RAnd (RDiamondB I \<gamma>) \<beta>))"
               "rsat \<sigma> V v i (RSince (RAnd \<alpha> \<gamma>) I \<beta>) = rsat \<sigma> V v i (RSince (RAnd \<gamma> \<alpha>) I \<beta>)" using rsat_def by auto
    from b show ?thesis
      apply(simp only:rewrite.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(1) 15(3)[OF refl b]]  split:if_splits) (*remove recursion*)
      apply(simp only: swap)
      apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
      apply(simp only: sat_main_7[OF ex, symmetric])(*apply rewrite lemma*)
      apply(auto)
      done
next
  case c
  thm 15(1)
  thm 15(4)[OF refl ]
  thm rsub_2[OF f_conr2_5_t  ]
  thm sat_main_8[symmetric]
  then show ?thesis
    apply(simp only:rewrite.simps)
        apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(4)[OF refl c] 15(1)]  split:if_splits) (*remove recursion*)
      apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
    apply(rule sat_main_9[symmetric])
    done
next
  case d
  have swap:"rsat \<sigma> V v i (RUntil (RAnd (RDiamondW (init_int I) \<gamma>) \<beta>) I (RAnd \<alpha> \<gamma>)) =
             rsat \<sigma> V v i (RUntil (RAnd (RDiamondW (init_int I) \<gamma>) \<beta>) I (RAnd \<gamma> \<alpha>))"
            "rsat \<sigma> V v i (RUntil \<beta> I (RAnd \<alpha> \<gamma>)) = rsat \<sigma> V v i (RUntil \<beta> I (RAnd \<gamma> \<alpha>))" using rsat_def by auto
  from d show ?thesis using swap
    apply(simp only:rewrite.simps)
    apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(5)[OF refl d] 15(1)]  split:if_splits) (*remove recursion*)
    apply(simp only: swap)
    apply(simp only: rsat_def project1.simps  project2.simps)(*remove embedding*)
    apply(rule sat_main_9[symmetric])
    done
next
  case e
  then show ?thesis
  proof(cases "t=Swapped")
    case True
    then show ?thesis using e
      apply(simp only:rewrite.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(6)[OF refl e]] 15(1)  split:if_splits) (*remove recursion*)
      done
  next
    case False
    then show ?thesis using e not_swapped[OF False]
      apply(simp only:rewrite.simps fix_r.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(1) 15(6)[OF refl e]]  split:if_splits) (*remove recursion*)
      done
  qed
qed
next
  case (24 y \<omega> b' f \<phi> t)
  then show ?case
    apply(simp only:rewrite.simps fix_r.simps rsub_agg[OF f_conr_agg_t 24[symmetric],simplified fix_r.simps, OF rewrite_fv])
    done
next
  case (25 I \<phi> t)
  then show ?case
    apply(simp only:rewrite.simps fix_r.simps rsub_1[OF f_conr_6_t 25])
    done
next
  case (34 I r t)
  then show ?case by (simp add: rsat_def regex.map_comp o_def match_map_regex cong: regex.map_cong)
next
  case (35 I r t)
  then show ?case by (simp add: rsat_def regex.map_comp o_def match_map_regex cong: regex.map_cong)
qed (simp only:rewrite.simps fix_r.simps rsat_def;auto)+

lemma final_sat: "Formula.sat \<sigma> V v i (rewrite_f f) = Formula.sat \<sigma> V v i f"
  using rewrite_sat rsat_def by auto

definition st where
  "st t = (if Formula.fv_trm t = {} then Formula.Const (Formula.eval_trm [] t) else t)"

lemma eval_st:
  "Formula.eval_trm v (st t) = Formula.eval_trm v t"
  unfolding st_def by (induction t) auto

fun simplify_terms where
  "simplify_terms (Formula.Pred r ts) = Formula.Pred r (map st ts)"
| "simplify_terms (Formula.Let p \<phi> \<psi>) = Formula.Let p (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.Eq t1 t2) = Formula.Eq (st t1) (st t2)"
| "simplify_terms (Formula.Less t1 t2) = Formula.Less (st t1) (st t2)"
| "simplify_terms (Formula.LessEq t1 t2) = Formula.LessEq (st t1) (st t2)"
| "simplify_terms (Formula.Neg \<phi>) = Formula.Neg (simplify_terms \<phi>)"
| "simplify_terms (Formula.Or \<phi> \<psi>) = Formula.Or (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.And \<phi> \<psi>) = Formula.And (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.Ands l) = Formula.Ands (map simplify_terms l)"
| "simplify_terms (Formula.Exists t \<phi>) = Formula.Exists t (simplify_terms \<phi>)"
| "simplify_terms (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (simplify_terms \<phi>)"
| "simplify_terms (Formula.Prev I \<phi>) = Formula.Prev I (simplify_terms \<phi>)"
| "simplify_terms (Formula.Next I \<phi>) = Formula.Next I (simplify_terms \<phi>)"
| "simplify_terms (Formula.Since \<phi> I \<psi>) = Formula.Since (simplify_terms \<phi>) I (simplify_terms \<psi>)"
| "simplify_terms (Formula.Until \<phi> I \<psi>) = Formula.Until (simplify_terms \<phi>) I (simplify_terms \<psi>)"
| "simplify_terms (Formula.MatchP I r) = Formula.MatchP I (regex.map_regex simplify_terms r)"
| "simplify_terms (Formula.MatchF I r) = Formula.MatchF I (regex.map_regex simplify_terms r)"
| "simplify_terms (Formula.TP t) = Formula.TP (st t)"
| "simplify_terms (Formula.TS t) = Formula.TS (st t)"

lemma st_fvi:
  "Formula.fvi_trm b (st a) = Formula.fvi_trm b a"
  unfolding st_def
  by(induction a) auto

lemma simplify_terms_fvi:
  "Formula.fvi b (simplify_terms \<phi>) = Formula.fvi b \<phi>"
  by(induction \<phi> arbitrary: b rule:simplify_terms.induct) (auto simp:st_fvi fv_regex_alt regex.set_map)

lemma simplify_terms_nfv:
  "Formula.nfv (simplify_terms \<phi>) = Formula.nfv \<phi>" 
    unfolding Formula.nfv_def simplify_terms_fvi by auto

lemma simplify_terms_sat:
  "Formula.sat \<sigma> V v i (simplify_terms f) = Formula.sat \<sigma> V v i f"
proof(induction f arbitrary: V v i rule:simplify_terms.induct)
  case (1 r ts)
  then show ?case by(auto simp: comp_def eval_st split:option.splits)
next
  case (2 p \<phi> \<psi>)
  then show ?case unfolding simplify_terms.simps Formula.sat.simps 2 simplify_terms_nfv by auto
next
  case (3 p \<phi> \<psi>)
  then show ?case unfolding simplify_terms.simps Formula.sat.simps 3 simplify_terms_nfv by auto
next
qed (auto simp:eval_st Rewriting.match_map_regex simplify_terms_fvi split:nat.splits)

fun push_negation where
  "push_negation (Formula.Neg (Formula.And \<phi> \<psi>)) = Formula.Or (push_negation (Formula.Neg \<phi>)) (push_negation (Formula.Neg \<psi>))"
| "push_negation (Formula.Neg (Formula.Or \<phi> \<psi>)) = Formula.And (push_negation (Formula.Neg \<phi>)) (push_negation (Formula.Neg \<psi>))"
| "push_negation (Formula.Let p \<phi> \<psi>) = Formula.Let p (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.Neg \<phi>) = Formula.Neg (push_negation \<phi>)"
| "push_negation (Formula.Or \<phi> \<psi>) = Formula.Or (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.And \<phi> \<psi>) = Formula.And (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.Ands l) = Formula.Ands (map push_negation l)"
| "push_negation (Formula.Exists t \<phi>) = Formula.Exists t (push_negation \<phi>)"
| "push_negation (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (push_negation \<phi>)"
| "push_negation (Formula.Prev I \<phi>) = Formula.Prev I (push_negation \<phi>)"
| "push_negation (Formula.Next I \<phi>) = Formula.Next I (push_negation \<phi>)"
| "push_negation (Formula.Since \<phi> I \<psi>) = Formula.Since (push_negation \<phi>) I (push_negation \<psi>)"
| "push_negation (Formula.Until \<phi> I \<psi>) = Formula.Until (push_negation \<phi>) I (push_negation \<psi>)"
| "push_negation (Formula.MatchP I r) = Formula.MatchP I (regex.map_regex push_negation r)"
| "push_negation (Formula.MatchF I r) = Formula.MatchF I (regex.map_regex push_negation r)"
| "push_negation \<phi> = \<phi>"

lemma push_negation_fvi:
  "Formula.fvi b (push_negation \<phi>) = Formula.fvi b \<phi>"
  by(induction \<phi> arbitrary: b rule:push_negation.induct) (auto simp: fv_regex_alt regex.set_map)

lemma push_negation_nfv:
  "Formula.nfv (push_negation \<phi>) = Formula.nfv \<phi>" 
  unfolding Formula.nfv_def push_negation_fvi by auto

lemma push_negation_sat:
  "Formula.sat \<sigma> V v i (push_negation f) = Formula.sat \<sigma> V v i f"
proof(induction f arbitrary: V v i rule:push_negation.induct)
  case (3 p \<phi> \<psi>)
  then show ?case unfolding push_negation.simps Formula.sat.simps 3 push_negation_nfv by auto
next
  case (4 p \<phi> \<psi>)
  then show ?case unfolding push_negation.simps Formula.sat.simps 4 push_negation_nfv by auto
next
qed (auto simp: Rewriting.match_map_regex push_negation_fvi split:nat.splits)

fun elim_double_negation where
  "elim_double_negation (Formula.Neg (Formula.Neg \<phi>)) = elim_double_negation \<phi>"
| "elim_double_negation (Formula.Let p \<phi> \<psi>) = Formula.Let p (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.Neg \<phi>) = Formula.Neg (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Or \<phi> \<psi>) = Formula.Or (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.And \<phi> \<psi>) = Formula.And (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.Ands l) = Formula.Ands (map elim_double_negation l)"
| "elim_double_negation (Formula.Exists t \<phi>) = Formula.Exists t (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Prev I \<phi>) = Formula.Prev I (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Next I \<phi>) = Formula.Next I (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Since \<phi> I \<psi>) = Formula.Since (elim_double_negation \<phi>) I (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.Until \<phi> I \<psi>) = Formula.Until (elim_double_negation \<phi>) I (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.MatchP I r) = Formula.MatchP I (regex.map_regex elim_double_negation r)"
| "elim_double_negation (Formula.MatchF I r) = Formula.MatchF I (regex.map_regex elim_double_negation r)"
| "elim_double_negation \<phi> = \<phi>"

lemma elim_double_negation_fvi:
  "Formula.fvi b (elim_double_negation \<phi>) = Formula.fvi b \<phi>"
  by(induction \<phi> arbitrary: b rule:elim_double_negation.induct) (auto simp: fv_regex_alt regex.set_map)

lemma elim_double_negation_nfv:
  "Formula.nfv (elim_double_negation \<phi>) = Formula.nfv \<phi>" 
  unfolding Formula.nfv_def elim_double_negation_fvi by auto

lemma elim_double_negation_sat:
  "Formula.sat \<sigma> V v i (elim_double_negation f) = Formula.sat \<sigma> V v i f"
proof(induction f arbitrary: V v i rule:elim_double_negation.induct)
  case (2 p \<phi> \<psi>)
  then show ?case unfolding elim_double_negation.simps Formula.sat.simps 2 elim_double_negation_nfv by auto
next
  case (3 p \<phi> \<psi>)
  then show ?case unfolding elim_double_negation.simps Formula.sat.simps 3 elim_double_negation_nfv by auto
next
qed (auto simp: Rewriting.match_map_regex elim_double_negation_fvi split:nat.splits)

definition normalize where
  "normalize = elim_double_negation \<circ> push_negation \<circ> simplify_terms"

lemma normalize_sat:
  "Formula.sat \<sigma> V v i (normalize f) = Formula.sat \<sigma> V v i f"
  unfolding normalize_def comp_apply using simplify_terms_sat push_negation_sat elim_double_negation_sat by auto
end
