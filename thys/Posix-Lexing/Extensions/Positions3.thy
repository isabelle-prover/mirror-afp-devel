   
theory Positions3
  imports Lexer3 LexicalVals3
begin

section \<open>An alternative definition for POSIX values by Okui \& Suzuki\<close>

section \<open>Positions in Values\<close>

fun 
  at :: "'a val \<Rightarrow> nat list \<Rightarrow> 'a val"
where
  "at v [] = v"
| "at (Left v) (0#ps)= at v ps"
| "at (Right v) (Suc 0#ps)= at v ps"
| "at (Seq v1 v2) (0#ps)= at v1 ps"
| "at (Seq v1 v2) (Suc 0#ps)= at v2 ps"
| "at (Stars vs) (n#ps) = at (nth vs n) ps"
| "at (Recv l v) ps = at v ps" 



fun Pos :: "'a val \<Rightarrow> (nat list) set"
where
  "Pos (Void) = {[]}"
| "Pos (Atm c) = {[]}"
| "Pos (Left v) = {[]} \<union> {0#ps | ps. ps \<in> Pos v}"
| "Pos (Right v) = {[]} \<union> {1#ps | ps. ps \<in> Pos v}"
| "Pos (Seq v1 v2) = {[]} \<union> {0#ps | ps. ps \<in> Pos v1} \<union> {1#ps | ps. ps \<in> Pos v2}" 
| "Pos (Stars []) = {[]}"
| "Pos (Stars (v#vs)) = {[]} \<union> {0#ps | ps. ps \<in> Pos v} \<union> {Suc n#ps | n ps. n#ps \<in> Pos (Stars vs)}"
| "Pos (Recv l v) = {[]} \<union> {ps . ps \<in> Pos v}"

lemma Pos_stars:
  "Pos (Stars vs) = {[]} \<union> (\<Union>n < length vs. {n#ps | ps. ps \<in> Pos (vs ! n)})"
apply(induct vs)
apply(auto simp add: insert_ident less_Suc_eq_0_disj)
done

lemma Pos_empty:
  shows "[] \<in> Pos v"
by (induct v rule: Pos.induct)(auto)


abbreviation
  "intlen vs \<equiv> int (length vs)"


definition pflat_len :: "'a val \<Rightarrow> nat list => int"
where
  "pflat_len v p \<equiv> (if p \<in> Pos v then intlen (flat (at v p)) else -1)"

lemma pflat_len_simps:
  shows "pflat_len (Seq v1 v2) (0#p) = pflat_len v1 p"
  and   "pflat_len (Seq v1 v2) (Suc 0#p) = pflat_len v2 p"
  and   "pflat_len (Left v) (0#p) = pflat_len v p"
  and   "pflat_len (Left v) (Suc 0#p) = -1"
  and   "pflat_len (Right v) (Suc 0#p) = pflat_len v p"
  and   "pflat_len (Right v) (0#p) = -1"
  and   "pflat_len (Stars (v#vs)) (Suc n#p) = pflat_len (Stars vs) (n#p)"
  and   "pflat_len (Stars (v#vs)) (0#p) = pflat_len v p"
  and   "pflat_len (Recv l v) p = pflat_len v p"
  and   "pflat_len v [] = intlen (flat v)"
  apply (auto simp add: pflat_len_def Pos_empty)
  by (metis at.simps(7) neq_Nil_conv)
  

lemma pflat_len_Stars_simps:
  assumes "n < length vs"
  shows "pflat_len (Stars vs) (n#p) = pflat_len (vs!n) p"
using assms
apply(induct vs arbitrary: n p)
apply(auto simp add: less_Suc_eq_0_disj pflat_len_simps)
done

lemma pflat_len_outside:
  assumes "p \<notin> Pos v1"
  shows "pflat_len v1 p = -1 "
using assms by (simp add: pflat_len_def)



section \<open>Orderings\<close>


definition prefix_list:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<sqsubseteq>pre _" [60,59] 60)
where
  "ps1 \<sqsubseteq>pre ps2 \<equiv> \<exists>ps'. ps1 @ps' = ps2"

definition sprefix_list:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<sqsubset>spre _" [60,59] 60)
where
  "ps1 \<sqsubset>spre ps2 \<equiv> ps1 \<sqsubseteq>pre ps2 \<and> ps1 \<noteq> ps2"

inductive lex_list :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" ("_ \<sqsubset>lex _" [60,59] 60)
where
  "[] \<sqsubset>lex (p#ps)"
| "ps1 \<sqsubset>lex ps2 \<Longrightarrow> (p#ps1) \<sqsubset>lex (p#ps2)"
| "p1 < p2 \<Longrightarrow> (p1#ps1) \<sqsubset>lex (p2#ps2)"

lemma lex_irrfl:
  fixes ps1 ps2 :: "nat list"
  assumes "ps1 \<sqsubset>lex ps2"
  shows "ps1 \<noteq> ps2"
using assms
by(induct rule: lex_list.induct)(auto)

lemma lex_simps [simp]:
  fixes xs ys :: "nat list"
  shows "[] \<sqsubset>lex ys \<longleftrightarrow> ys \<noteq> []"
  and   "xs \<sqsubset>lex [] \<longleftrightarrow> False"
  and   "(x # xs) \<sqsubset>lex (y # ys) \<longleftrightarrow> (x < y \<or> (x = y \<and> xs \<sqsubset>lex ys))"
by (auto simp add: neq_Nil_conv elim: lex_list.cases intro: lex_list.intros)

lemma lex_trans:
  fixes ps1 ps2 ps3 :: "nat list"
  assumes "ps1 \<sqsubset>lex ps2" "ps2 \<sqsubset>lex ps3"
  shows "ps1 \<sqsubset>lex ps3"
using assms
by (induct arbitrary: ps3 rule: lex_list.induct)
   (auto elim: lex_list.cases)


lemma lex_trichotomous:
  fixes p q :: "nat list"
  shows "p = q \<or> p \<sqsubset>lex q \<or> q \<sqsubset>lex p"
apply(induct p arbitrary: q)
apply(auto elim: lex_list.cases)
apply(case_tac q)
apply(auto)
done




section \<open>POSIX Ordering of Values According to Okui \& Suzuki\<close>


definition PosOrd:: "'a val \<Rightarrow> nat list \<Rightarrow> 'a val \<Rightarrow> bool" ("_ \<sqsubset>val _ _" [60, 60, 59] 60)
where
  "v1 \<sqsubset>val p v2 \<equiv> pflat_len v1 p > pflat_len v2 p \<and>
                   (\<forall>q \<in> Pos v1 \<union> Pos v2. q \<sqsubset>lex p \<longrightarrow> pflat_len v1 q = pflat_len v2 q)"

lemma PosOrd_def2:
  shows "v1 \<sqsubset>val p v2 \<longleftrightarrow> 
         pflat_len v1 p > pflat_len v2 p \<and>
         (\<forall>q \<in> Pos v1. q \<sqsubset>lex p \<longrightarrow> pflat_len v1 q = pflat_len v2 q) \<and>
         (\<forall>q \<in> Pos v2. q \<sqsubset>lex p \<longrightarrow> pflat_len v1 q = pflat_len v2 q)"
unfolding PosOrd_def
apply(auto)
done


definition PosOrd_ex:: "'a val \<Rightarrow> 'a val \<Rightarrow> bool" ("_ :\<sqsubset>val _" [60, 59] 60)
where
  "v1 :\<sqsubset>val v2 \<equiv> \<exists>p. v1 \<sqsubset>val p v2"

definition PosOrd_ex_eq:: "'a val \<Rightarrow> 'a val \<Rightarrow> bool" ("_ :\<sqsubseteq>val _" [60, 59] 60)
where
  "v1 :\<sqsubseteq>val v2 \<equiv> v1 :\<sqsubset>val v2 \<or> v1 = v2"


lemma PosOrd_trans:
  assumes "v1 :\<sqsubset>val v2" "v2 :\<sqsubset>val v3"
  shows "v1 :\<sqsubset>val v3"
proof -
  from assms obtain p p'
    where as: "v1 \<sqsubset>val p v2" "v2 \<sqsubset>val p' v3" unfolding PosOrd_ex_def by blast
  then have pos: "p \<in> Pos v1" "p' \<in> Pos v2" unfolding PosOrd_def pflat_len_def
    by (smt not_int_zless_negative)+
  have "p = p' \<or> p \<sqsubset>lex p' \<or> p' \<sqsubset>lex p"
    by (rule lex_trichotomous)
  moreover
    { assume "p = p'"
      with as have "v1 \<sqsubset>val p v3" unfolding PosOrd_def pflat_len_def
      by (smt Un_iff)
      then have " v1 :\<sqsubset>val v3" unfolding PosOrd_ex_def by blast
    }   
  moreover
    { assume "p \<sqsubset>lex p'"
      with as have "v1 \<sqsubset>val p v3" unfolding PosOrd_def pflat_len_def
      by (smt Un_iff lex_trans)
      then have " v1 :\<sqsubset>val v3" unfolding PosOrd_ex_def by blast
    }
  moreover
    { assume "p' \<sqsubset>lex p"
      with as have "v1 \<sqsubset>val p' v3" unfolding PosOrd_def
      by (smt Un_iff lex_trans pflat_len_def)
      then have "v1 :\<sqsubset>val v3" unfolding PosOrd_ex_def by blast
    }
  ultimately show "v1 :\<sqsubset>val v3" by blast
qed

lemma PosOrd_irrefl:
  assumes "v :\<sqsubset>val v"
  shows "False"
using assms unfolding PosOrd_ex_def PosOrd_def
by auto

lemma PosOrd_assym:
  assumes "v1 :\<sqsubset>val v2" 
  shows "\<not>(v2 :\<sqsubset>val v1)"
using assms
using PosOrd_irrefl PosOrd_trans by blast 

(*
  :\<sqsubseteq>val and :\<sqsubset>val are partial orders.
*)

lemma PosOrd_ordering:
  shows "ordering (\<lambda>v1 v2. v1 :\<sqsubseteq>val v2) (\<lambda> v1 v2. v1 :\<sqsubset>val v2)"
unfolding ordering_def PosOrd_ex_eq_def
apply(auto)
using PosOrd_trans partial_preordering_def apply blast
using PosOrd_assym ordering_axioms_def by blast

lemma PosOrd_order:
  shows "class.order (\<lambda>v1 v2. v1 :\<sqsubseteq>val v2) (\<lambda> v1 v2. v1 :\<sqsubset>val v2)"
  using PosOrd_ordering
  apply(simp add: class.order_def class.preorder_def class.order_axioms_def)
  by (smt (verit) PosOrd_ex_eq_def PosOrd_irrefl PosOrd_trans)


lemma PosOrd_ex_eq2:
  shows "v1 :\<sqsubset>val v2 \<longleftrightarrow> (v1 :\<sqsubseteq>val v2 \<and> v1 \<noteq> v2)"
  using PosOrd_ordering
  using PosOrd_ex_eq_def PosOrd_irrefl by blast 

lemma PosOrdeq_trans:
  assumes "v1 :\<sqsubseteq>val v2" "v2 :\<sqsubseteq>val v3"
  shows "v1 :\<sqsubseteq>val v3"
using assms PosOrd_ordering 
  unfolding ordering_def
  by (metis partial_preordering.trans)

lemma PosOrdeq_antisym:
  assumes "v1 :\<sqsubseteq>val v2" "v2 :\<sqsubseteq>val v1"
  shows "v1 = v2"
using assms PosOrd_ordering 
  by (metis ordering.eq_iff)

lemma PosOrdeq_refl:
  shows "v :\<sqsubseteq>val v" 
unfolding PosOrd_ex_eq_def
by auto


lemma PosOrd_shorterE:
  assumes "v1 :\<sqsubset>val v2" 
  shows "length (flat v2) \<le> length (flat v1)"
using assms unfolding PosOrd_ex_def PosOrd_def
apply(auto)
apply(case_tac p)
apply(simp add: pflat_len_simps)
apply(drule_tac x="[]" in bspec)
apply(simp add: Pos_empty)
apply(simp add: pflat_len_simps)
done

lemma PosOrd_shorterI:
  assumes "length (flat v2) < length (flat v1)"
  shows "v1 :\<sqsubset>val v2"
unfolding PosOrd_ex_def PosOrd_def pflat_len_def 
using assms Pos_empty by force

lemma PosOrd_spreI:
  assumes "flat v' \<sqsubset>spre flat v"
  shows "v :\<sqsubset>val v'" 
using assms
apply(rule_tac PosOrd_shorterI)
unfolding prefix_list_def sprefix_list_def
by (metis append_Nil2 append_eq_conv_conj drop_all le_less_linear)

lemma pflat_len_inside:
  assumes "pflat_len v2 p < pflat_len v1 p"
  shows "p \<in> Pos v1"
using assms 
unfolding pflat_len_def
by (auto split: if_splits)

lemma PosOrd_Rec_eq:
  assumes "flat v1 = flat v2"
  shows "Recv l v1 :\<sqsubset>val Recv l v2 \<longleftrightarrow> v1 :\<sqsubset>val v2" 
unfolding PosOrd_ex_def PosOrd_def2
  using assms
  apply(auto)
  apply (simp add: pflat_len_simps(10))
  apply (metis pflat_len_simps(9))
  by (metis pflat_len_simps(10) pflat_len_simps(9))

lemma PosOrd_Left_Right:
  assumes "flat v1 = flat v2"
  shows "Left v1 :\<sqsubset>val Right v2" 
unfolding PosOrd_ex_def
apply(rule_tac x="[0]" in exI)
apply(auto simp add: PosOrd_def pflat_len_simps assms)
done

lemma PosOrd_LeftE:
  assumes "Left v1 :\<sqsubset>val Left v2" "flat v1 = flat v2"
  shows "v1 :\<sqsubset>val v2"
using assms
unfolding PosOrd_ex_def PosOrd_def2
apply(auto simp add: pflat_len_simps)
apply(frule pflat_len_inside)
apply(auto simp add: pflat_len_simps)
by (metis lex_simps(3) pflat_len_simps(3))

lemma PosOrd_LeftI:
  assumes "v1 :\<sqsubset>val v2" "flat v1 = flat v2"
  shows  "Left v1 :\<sqsubset>val Left v2"
using assms
unfolding PosOrd_ex_def PosOrd_def2
apply(auto simp add: pflat_len_simps)
by (metis less_numeral_extra(3) lex_simps(3) pflat_len_simps(3))

lemma PosOrd_Left_eq:
  assumes "flat v1 = flat v2"
  shows "Left v1 :\<sqsubset>val Left v2 \<longleftrightarrow> v1 :\<sqsubset>val v2" 
using assms PosOrd_LeftE PosOrd_LeftI
by blast


lemma PosOrd_RightE:
  assumes "Right v1 :\<sqsubset>val Right v2" "flat v1 = flat v2"
  shows "v1 :\<sqsubset>val v2"
using assms
unfolding PosOrd_ex_def PosOrd_def2
apply(auto simp add: pflat_len_simps)
apply(frule pflat_len_inside)
apply(auto simp add: pflat_len_simps)
by (metis lex_simps(3) pflat_len_simps(5))

lemma PosOrd_RightI:
  assumes "v1 :\<sqsubset>val v2" "flat v1 = flat v2"
  shows  "Right v1 :\<sqsubset>val Right v2"
using assms
unfolding PosOrd_ex_def PosOrd_def2
apply(auto simp add: pflat_len_simps)
by (metis lex_simps(3) nat_neq_iff pflat_len_simps(5))


lemma PosOrd_Right_eq:
  assumes "flat v1 = flat v2"
  shows "Right v1 :\<sqsubset>val Right v2 \<longleftrightarrow> v1 :\<sqsubset>val v2" 
using assms PosOrd_RightE PosOrd_RightI
by blast


lemma PosOrd_SeqI1:
  assumes "v1 :\<sqsubset>val w1" "flat (Seq v1 v2) = flat (Seq w1 w2)"
  shows "Seq v1 v2 :\<sqsubset>val Seq w1 w2" 
using assms(1)
apply(subst (asm) PosOrd_ex_def)
apply(subst (asm) PosOrd_def)
apply(clarify)
apply(subst PosOrd_ex_def)
apply(rule_tac x="0#p" in exI)
apply(subst PosOrd_def)
apply(rule conjI)
apply(simp add: pflat_len_simps)
apply(rule ballI)
apply(rule impI)
apply(simp only: Pos.simps)
apply(auto)[1]
apply(simp add: pflat_len_simps)
apply(auto simp add: pflat_len_simps)
using assms(2)
apply(simp)
apply(metis length_append of_nat_add)
done

lemma PosOrd_SeqI2:
  assumes "v2 :\<sqsubset>val w2" "flat v2 = flat w2"
  shows "Seq v v2 :\<sqsubset>val Seq v w2" 
using assms(1)
apply(subst (asm) PosOrd_ex_def)
apply(subst (asm) PosOrd_def)
apply(clarify)
apply(subst PosOrd_ex_def)
apply(rule_tac x="Suc 0#p" in exI)
apply(subst PosOrd_def)
apply(rule conjI)
apply(simp add: pflat_len_simps)
apply(rule ballI)
apply(rule impI)
apply(simp only: Pos.simps)
apply(auto)[1]
apply(simp add: pflat_len_simps)
using assms(2)
apply(simp)
apply(auto simp add: pflat_len_simps)
done

lemma PosOrd_Seq_eq:
  assumes "flat v2 = flat w2"
  shows "(Seq v v2) :\<sqsubset>val (Seq v w2) \<longleftrightarrow> v2 :\<sqsubset>val w2"
using assms 
apply(auto)
prefer 2
apply(simp add: PosOrd_SeqI2)
apply(simp add: PosOrd_ex_def)
apply(auto)
apply(case_tac p)
apply(simp add: PosOrd_def pflat_len_simps)
apply(case_tac a)
apply(simp add: PosOrd_def pflat_len_simps)
apply(clarify)
apply(case_tac nat)
prefer 2
apply(simp add: PosOrd_def pflat_len_simps pflat_len_outside)
apply(rule_tac x="list" in exI)
apply(auto simp add: PosOrd_def2 pflat_len_simps)
apply(smt Collect_disj_eq lex_list.intros(2) mem_Collect_eq pflat_len_simps(2))
apply(smt Collect_disj_eq lex_list.intros(2) mem_Collect_eq pflat_len_simps(2))
done



lemma PosOrd_StarsI:
  assumes "v1 :\<sqsubset>val v2" "flats (v1#vs1) = flats (v2#vs2)"
  shows "Stars (v1#vs1) :\<sqsubset>val Stars (v2#vs2)" 
using assms(1)
apply(subst (asm) PosOrd_ex_def)
apply(subst (asm) PosOrd_def)
apply(clarify)
apply(subst PosOrd_ex_def)
apply(subst PosOrd_def)
apply(rule_tac x="0#p" in exI)
apply(simp add: pflat_len_Stars_simps pflat_len_simps)
using assms(2)
apply(simp add: pflat_len_simps)
apply(auto simp add: pflat_len_Stars_simps pflat_len_simps)
by (metis length_append of_nat_add)

lemma PosOrd_StarsI2:
  assumes "Stars vs1 :\<sqsubset>val Stars vs2" "flats vs1 = flats vs2"
  shows "Stars (v#vs1) :\<sqsubset>val Stars (v#vs2)" 
using assms(1)
apply(subst (asm) PosOrd_ex_def)
apply(subst (asm) PosOrd_def)
apply(clarify)
apply(subst PosOrd_ex_def)
apply(subst PosOrd_def)
apply(case_tac p)
apply(simp add: pflat_len_simps)
apply(rule_tac x="Suc a#list" in exI)
apply(auto simp add: pflat_len_Stars_simps pflat_len_simps assms(2))
done

lemma PosOrd_Stars_appendI:
  assumes "Stars vs1 :\<sqsubset>val Stars vs2" "flat (Stars vs1) = flat (Stars vs2)"
  shows "Stars (vs @ vs1) :\<sqsubset>val Stars (vs @ vs2)"
using assms
apply(induct vs)
apply(simp)
apply(simp add: PosOrd_StarsI2)
done

lemma PosOrd_StarsE2:
  assumes "Stars (v # vs1) :\<sqsubset>val Stars (v # vs2)"
  shows "Stars vs1 :\<sqsubset>val Stars vs2"
using assms
apply(subst (asm) PosOrd_ex_def)
apply(erule exE)
apply(case_tac p)
apply(simp)
apply(simp add: PosOrd_def pflat_len_simps)
apply(subst PosOrd_ex_def)
apply(rule_tac x="[]" in exI)
apply(simp add: PosOrd_def pflat_len_simps Pos_empty)
apply(simp)
apply(case_tac a)
apply(clarify)
apply(auto simp add: pflat_len_simps PosOrd_def pflat_len_def split: if_splits)[1]
apply(clarify)
apply(simp add: PosOrd_ex_def)
apply(rule_tac x="nat#list" in exI)
apply(auto simp add: PosOrd_def pflat_len_simps)[1]
apply(case_tac q)
apply(simp add: PosOrd_def pflat_len_simps)
apply(clarify)
apply(drule_tac x="Suc a # lista" in bspec)
apply(simp)
apply(auto simp add: PosOrd_def pflat_len_simps)[1]
apply(case_tac q)
apply(simp add: PosOrd_def pflat_len_simps)
apply(clarify)
apply(drule_tac x="Suc a # lista" in bspec)
apply(simp)
apply(auto simp add: PosOrd_def pflat_len_simps)[1]
done

lemma PosOrd_Stars_appendE:
  assumes "Stars (vs @ vs1) :\<sqsubset>val Stars (vs @ vs2)"
  shows "Stars vs1 :\<sqsubset>val Stars vs2"
using assms
apply(induct vs)
apply(simp)
apply(simp add: PosOrd_StarsE2)
done

lemma PosOrd_Stars_append_eq:
  assumes "flats vs1 = flats vs2"
  shows "Stars (vs @ vs1) :\<sqsubset>val Stars (vs @ vs2) \<longleftrightarrow> Stars vs1 :\<sqsubset>val Stars vs2"
using assms
apply(rule_tac iffI)
apply(erule PosOrd_Stars_appendE)
apply(rule PosOrd_Stars_appendI)
apply(auto)
  done  

lemma PosOrd_Stars_equalsI:
  assumes "flats vs1 = flats vs2" "length vs1 = length vs2"
  and     "list_all2 (\<lambda>v1 v2. v1 :\<sqsubseteq>val v2) vs1 vs2"
  shows "Stars vs1 :\<sqsubseteq>val Stars vs2"
  using assms(3) assms(2,1)
  apply(induct rule: list_all2_induct)
  apply (simp add: PosOrdeq_refl)
  apply(case_tac "Stars (x # xs) = Stars (y # ys)")
  apply (simp add: PosOrdeq_refl)
  apply(case_tac "x = y")
   apply(subgoal_tac "Stars xs :\<sqsubset>val Stars ys")
  apply (simp add: PosOrd_StarsI2 PosOrd_ex_eq_def)
  apply (simp add: PosOrd_ex_eq2)
  by (meson PosOrd_StarsI PosOrd_ex_eq_def)

lemma PosOrd_almost_trichotomous:
  shows "v1 :\<sqsubset>val v2 \<or> v2 :\<sqsubset>val v1 \<or> (length (flat v1) = length (flat v2))"
apply(auto simp add: PosOrd_ex_def)
apply(auto simp add: PosOrd_def)
apply(rule_tac x="[]" in exI)
apply(auto simp add: Pos_empty pflat_len_simps)
apply(drule_tac x="[]" in spec)
apply(auto simp add: Pos_empty pflat_len_simps)
done


section \<open>The Posix Value is smaller than any other lexical value\<close>


lemma Posix_PosOrd:
  assumes "s \<in> r \<rightarrow> v1" "v2 \<in> LV r s" 
  shows "v1 :\<sqsubseteq>val v2"
using assms
proof (induct arbitrary: v2 rule: Posix.induct)
  case (Posix_One v)
  have "v \<in> LV One []" by fact
  then have "v = Void"
    by (simp add: LV_simps)
  then show "Void :\<sqsubseteq>val v"
    by (simp add: PosOrd_ex_eq_def)
next
  case (Posix_Atom c v)
  have "v \<in> LV (Atom c) [c]" by fact
  then have "v = Atm c"
    by (simp add: LV_simps)
  then show "Atm c :\<sqsubseteq>val v"
    by (simp add: PosOrd_ex_eq_def)
next
  case (Posix_Plus1 s r1 v r2 v2)
  have as1: "s \<in> r1 \<rightarrow> v" by fact
  have IH: "\<And>v2. v2 \<in> LV r1 s \<Longrightarrow> v :\<sqsubseteq>val v2" by fact
  have "v2 \<in> LV (Plus r1 r2) s" by fact
  then have "\<turnstile> v2 : Plus r1 r2" "flat v2 = s"
    by(auto simp add: LV_def prefix_list_def)
  then consider
    (Left) v3 where "v2 = Left v3" "\<turnstile> v3 : r1" "flat v3 = s" 
  | (Right) v3 where "v2 = Right v3" "\<turnstile> v3 : r2" "flat v3 = s"
  by (auto elim: Prf.cases)
  then show "Left v :\<sqsubseteq>val v2"
  proof(cases)
     case (Left v3)
     have "v3 \<in> LV r1 s" using Left(2,3) 
       by (auto simp add: LV_def prefix_list_def)
     with IH have "v :\<sqsubseteq>val v3" by simp
     moreover
     have "flat v3 = flat v" using as1 Left(3)
       by (simp add: Posix1(2)) 
     ultimately have "Left v :\<sqsubseteq>val Left v3"
       by (simp add: PosOrd_ex_eq_def PosOrd_Left_eq)
     then show "Left v :\<sqsubseteq>val v2" unfolding Left .
  next
     case (Right v3)
     have "flat v3 = flat v" using as1 Right(3)
       by (simp add: Posix1(2)) 
     then have "Left v :\<sqsubseteq>val Right v3" 
       unfolding PosOrd_ex_eq_def
       by (simp add: PosOrd_Left_Right)
     then show "Left v :\<sqsubseteq>val v2" unfolding Right .
  qed
next
  case (Posix_Plus2 s r2 v r1 v2)
  have as1: "s \<in> r2 \<rightarrow> v" by fact
  have as2: "s \<notin> lang r1" by fact
  have IH: "\<And>v2. v2 \<in> LV r2 s \<Longrightarrow> v :\<sqsubseteq>val v2" by fact
  have "v2 \<in> LV (Plus r1 r2) s" by fact
  then have "\<turnstile> v2 : Plus r1 r2" "flat v2 = s"
    by(auto simp add: LV_def prefix_list_def)
  then consider
    (Left) v3 where "v2 = Left v3" "\<turnstile> v3 : r1" "flat v3 = s" 
  | (Right) v3 where "v2 = Right v3" "\<turnstile> v3 : r2" "flat v3 = s"
  by (auto elim: Prf.cases)
  then show "Right v :\<sqsubseteq>val v2"
  proof (cases)
    case (Right v3)
     have "v3 \<in> LV r2 s" using Right(2,3) 
       by (auto simp add: LV_def prefix_list_def)
     with IH have "v :\<sqsubseteq>val v3" by simp
     moreover
     have "flat v3 = flat v" using as1 Right(3)
       by (simp add: Posix1(2)) 
     ultimately have "Right v :\<sqsubseteq>val Right v3" 
        by (auto simp add: PosOrd_ex_eq_def PosOrd_RightI)
     then show "Right v :\<sqsubseteq>val v2" unfolding Right .
  next
     case (Left v3)
     have "v3 \<in> LV r1 s" using Left(2,3) as2  
       by (auto simp add: LV_def prefix_list_def)
     then have "flat v3 = flat v \<and> \<turnstile> v3 : r1" using as1 Left(3)
       by (simp add: Posix1(2) LV_def) 
     then have "False" using as1 as2 Left
       using Prf_flat_lang by blast
     then show "Right v :\<sqsubseteq>val v2" by simp
  qed
next 
  case (Posix_Times s1 r1 v1 s2 r2 v2 v3)
  have "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" by fact+
  then have as1: "s1 = flat v1" "s2 = flat v2" by (simp_all add: Posix1(2))
  have IH1: "\<And>v3. v3 \<in> LV r1 s1 \<Longrightarrow> v1 :\<sqsubseteq>val v3" by fact
  have IH2: "\<And>v3. v3 \<in> LV r2 s2 \<Longrightarrow> v2 :\<sqsubseteq>val v3" by fact
  have cond: "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r1 \<and> s\<^sub>4 \<in> lang r2)" by fact
  have "v3 \<in> LV (Times r1 r2) (s1 @ s2)" by fact
  then obtain v3a v3b where eqs:
    "v3 = Seq v3a v3b" "\<turnstile> v3a : r1" "\<turnstile> v3b : r2"
    "flat v3a @ flat v3b = s1 @ s2" 
    by (force simp add: prefix_list_def LV_def elim: Prf.cases)
  with cond have "flat v3a \<sqsubseteq>pre s1" unfolding prefix_list_def
    by (smt Prf_flat_lang append_eq_append_conv2 append_self_conv)
  then have "flat v3a \<sqsubset>spre s1 \<or> (flat v3a = s1 \<and> flat v3b = s2)" using eqs
    by (simp add: sprefix_list_def append_eq_conv_conj)
  then have q2: "v1 :\<sqsubset>val v3a \<or> (flat v3a = s1 \<and> flat v3b = s2)" 
    using PosOrd_spreI as1(1) eqs by blast
  then have "v1 :\<sqsubset>val v3a \<or> (v3a \<in> LV r1 s1 \<and> v3b \<in> LV r2 s2)" using eqs(2,3)
    by (auto simp add: LV_def)
  then have "v1 :\<sqsubset>val v3a \<or> (v1 :\<sqsubseteq>val v3a \<and> v2 :\<sqsubseteq>val v3b)" using IH1 IH2 by blast         
  then have "Seq v1 v2 :\<sqsubseteq>val Seq v3a v3b" using eqs q2 as1
    unfolding  PosOrd_ex_eq_def by (auto simp add: PosOrd_SeqI1 PosOrd_Seq_eq) 
  then show "Seq v1 v2 :\<sqsubseteq>val v3" unfolding eqs by blast
next 
  case (Posix_Star1 s1 r v s2 vs v3) 
  have "s1 \<in> r \<rightarrow> v" "s2 \<in> Star r \<rightarrow> Stars vs" by fact+
  then have as1: "s1 = flat v" "s2 = flat (Stars vs)" by (auto dest: Posix1(2))
  have IH1: "\<And>v3. v3 \<in> LV r s1 \<Longrightarrow> v :\<sqsubseteq>val v3" by fact
  have IH2: "\<And>v3. v3 \<in> LV (Star r) s2 \<Longrightarrow> Stars vs :\<sqsubseteq>val v3" by fact
  have cond: "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" by fact
  have cond2: "flat v \<noteq> []" by fact
  have "v3 \<in> LV (Star r) (s1 @ s2)" by fact
  then consider 
    (NonEmpty) v3a vs3 where "v3 = Stars (v3a # vs3)" 
    "\<turnstile> v3a : r" "\<turnstile> Stars vs3 : Star r"
    "flat (Stars (v3a # vs3)) = s1 @ s2"
  | (Empty) "v3 = Stars []"
  unfolding LV_def  
  apply(auto)
  apply(erule Prf_elims)
  by (metis NonEmpty Prf.intros(6) list.set_intros(1) list.set_intros(2) neq_Nil_conv)
  then show "Stars (v # vs) :\<sqsubseteq>val v3" 
    proof (cases)
      case (NonEmpty v3a vs3)
      have "flat (Stars (v3a # vs3)) = s1 @ s2" using NonEmpty(4) . 
      with cond have "flat v3a \<sqsubseteq>pre s1" using NonEmpty(2,3)
        unfolding prefix_list_def
        by (smt Prf_flat_lang append_Nil2 append_eq_append_conv2 flat.simps(7)) 
      then have "flat v3a \<sqsubset>spre s1 \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" using NonEmpty(4)
        by (simp add: sprefix_list_def append_eq_conv_conj)
      then have q2: "v :\<sqsubset>val v3a \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" 
        using PosOrd_spreI as1(1) NonEmpty(4) by blast
      then have "v :\<sqsubset>val v3a \<or> (v3a \<in> LV r s1 \<and> Stars vs3 \<in> LV (Star r) s2)" 
        using NonEmpty(2,3) by (auto simp add: LV_def)
      then have "v :\<sqsubset>val v3a \<or> (v :\<sqsubseteq>val v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" using IH1 IH2 by blast
      then have "v :\<sqsubset>val v3a \<or> (v = v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" 
         unfolding PosOrd_ex_eq_def by auto     
      then have "Stars (v # vs) :\<sqsubseteq>val Stars (v3a # vs3)" using NonEmpty(4) q2 as1
        unfolding  PosOrd_ex_eq_def
        using PosOrd_StarsI PosOrd_StarsI2
        by (metis flat.simps(7) flat_Stars val.inject(5)) 
      then show "Stars (v # vs) :\<sqsubseteq>val v3" unfolding NonEmpty by blast
    next 
      case Empty
      have "v3 = Stars []" by fact
      then show "Stars (v # vs) :\<sqsubseteq>val v3"
      unfolding PosOrd_ex_eq_def using cond2
      by (simp add: PosOrd_shorterI)
    qed    
next
  case (Posix_Star2 r v2)
  have "v2 \<in> LV (Star r) []" by fact
  then have "v2 = Stars []" 
    unfolding LV_def by (auto elim: Prf.cases) 
  then show "Stars [] :\<sqsubseteq>val v2"
    by (simp add: PosOrd_ex_eq_def)
next
  case (Posix_NTimes2 vs r n v2)
  have IH: "\<forall>v\<in>set vs. [] \<in> r \<rightarrow> v \<and> (\<forall>x. x \<in> LV r [] \<longrightarrow> v :\<sqsubseteq>val x)" by fact
  then have "flats vs = []"
    by (metis Posix.Posix_NTimes2 Posix1(2) flat_Stars) 
  have "v2 \<in> LV (NTimes r n) []" by fact
    then obtain vs' where eq: "v2 = Stars vs'" and "length vs' = n" and as: "\<forall>v \<in> set vs'. v \<in> LV r [] \<and> flat v = []" 
      unfolding LV_def by (auto elim!: Prf_elims)
  then have "Stars vs :\<sqsubseteq>val Stars vs'"
    apply(rule_tac PosOrd_Stars_equalsI)
    apply (simp add: \<open>flats vs = []\<close>)
    using Posix_NTimes2.hyps(2) apply blast
    using IH apply(simp add: list_all2_iff)
    apply(auto)
    using Posix_NTimes2.hyps(2) apply blast
    by (meson in_set_zipE)
  then show "Stars vs :\<sqsubseteq>val v2" using eq by simp 
next
  case (Posix_NTimes1 s1 r v s2 n vs)
  have "s1 \<in> r \<rightarrow> v" "s2 \<in> NTimes r n \<rightarrow> Stars vs" by fact+
  then have as1: "s1 = flat v" "s2 = flat (Stars vs)" by (auto dest: Posix1(2))
  have IH1: "\<And>v3. v3 \<in> LV r s1 \<Longrightarrow> v :\<sqsubseteq>val v3" by fact
  have IH2: "\<And>v3. v3 \<in> LV (NTimes r n) s2 \<Longrightarrow> Stars vs :\<sqsubseteq>val v3" by fact
  have cond: "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (NTimes r n))" by fact
  have cond2: "flat v \<noteq> []" by fact
  have "v2 \<in> LV (NTimes r (n + 1)) (s1 @ s2)" by fact
  then consider 
    (NonEmpty) v3a vs3 where "v2 = Stars (v3a # vs3)" 
    "\<turnstile> v3a : r" "\<turnstile> Stars vs3 : NTimes r n"
    "flat (Stars (v3a # vs3)) = s1 @ s2"
  | (Empty) "v2 = Stars []"
  unfolding LV_def  
  apply(auto)
  apply(erule Prf_elims)
  apply(case_tac vs1)
  apply(simp add: as1(1) cond2 flats_empty)
   apply(simp)
  using Prf.simps apply fastforce
  done
  then show "Stars (v # vs) :\<sqsubseteq>val v2" 
    proof (cases)
      case (NonEmpty v3a vs3)
      have "flat (Stars (v3a # vs3)) = s1 @ s2" using NonEmpty(4) . 
      with cond have "flat v3a \<sqsubseteq>pre s1" using NonEmpty(2,3)
        unfolding prefix_list_def
        by (smt Prf_flat_lang append_Nil2 append_eq_append_conv2 flat.simps(7)) 
      then have "flat v3a \<sqsubset>spre s1 \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" using NonEmpty(4)
        by (simp add: sprefix_list_def append_eq_conv_conj)
      then have q2: "v :\<sqsubset>val v3a \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" 
        using PosOrd_spreI as1(1) NonEmpty(4) by blast
      then have "v :\<sqsubset>val v3a \<or> (v3a \<in> LV r s1 \<and> Stars vs3 \<in> LV (NTimes r n) s2)" 
        using NonEmpty(2,3) by (auto simp add: LV_def)
      then have "v :\<sqsubset>val v3a \<or> (v :\<sqsubseteq>val v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" using IH1 IH2 by blast
      then have "v :\<sqsubset>val v3a \<or> (v = v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" 
         unfolding PosOrd_ex_eq_def by auto     
      then have "Stars (v # vs) :\<sqsubseteq>val Stars (v3a # vs3)" using NonEmpty(4) q2 as1
        unfolding  PosOrd_ex_eq_def
        using PosOrd_StarsI PosOrd_StarsI2
        by (metis flat.simps(7) flat_Stars val.inject(5)) 
      then show "Stars (v # vs) :\<sqsubseteq>val v2" unfolding NonEmpty by blast
    next 
      case Empty
      have "v2 = Stars []" by fact
      then show "Stars (v # vs) :\<sqsubseteq>val v2"
      unfolding PosOrd_ex_eq_def using cond2
      by (simp add: PosOrd_shorterI)
  qed  
next
  case (Posix_Upto1 s1 r v s2 n vs v3)
    have "s1 \<in> r \<rightarrow> v" "s2 \<in> Upto r n \<rightarrow> Stars vs" by fact+
  then have as1: "s1 = flat v" "s2 = flat (Stars vs)" by (auto dest: Posix1(2))
  have IH1: "\<And>v3. v3 \<in> LV r s1 \<Longrightarrow> v :\<sqsubseteq>val v3" by fact
  have IH2: "\<And>v3. v3 \<in> LV (Upto r n) s2 \<Longrightarrow> Stars vs :\<sqsubseteq>val v3" by fact
  have cond: "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Upto r n))" by fact
  have cond2: "flat v \<noteq> []" by fact
  have "v3 \<in> LV (Upto r (n + 1)) (s1 @ s2)" by fact
  then consider 
    (NonEmpty) v3a vs3 where "v3 = Stars (v3a # vs3)" 
    "\<turnstile> v3a : r" "\<turnstile> Stars vs3 : Upto r n"
    "flat (Stars (v3a # vs3)) = s1 @ s2"
  | (Empty) "v3 = Stars []"
  unfolding LV_def  
  apply(auto)
  apply(erule Prf_elims)
  apply(case_tac vs)
   apply(auto)
  by (simp add: Prf.intros(8))
  then show "Stars (v # vs) :\<sqsubseteq>val v3" 
    proof (cases)
      case (NonEmpty v3a vs3)
      have "flat (Stars (v3a # vs3)) = s1 @ s2" using NonEmpty(4) . 
      with cond have "flat v3a \<sqsubseteq>pre s1" using NonEmpty(2,3)
        unfolding prefix_list_def
        by (smt Prf_flat_lang append_Nil2 append_eq_append_conv2 flat.simps(7)) 
      then have "flat v3a \<sqsubset>spre s1 \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" using NonEmpty(4)
        by (simp add: sprefix_list_def append_eq_conv_conj)
      then have q2: "v :\<sqsubset>val v3a \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" 
        using PosOrd_spreI as1(1) NonEmpty(4) by blast
      then have "v :\<sqsubset>val v3a \<or> (v3a \<in> LV r s1 \<and> Stars vs3 \<in> LV (Upto r n) s2)" 
        using NonEmpty(2,3) 
        by (auto simp add: LV_def)
      then have "v :\<sqsubset>val v3a \<or> (v :\<sqsubseteq>val v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" using IH1 IH2 by blast
      then have "v :\<sqsubset>val v3a \<or> (v = v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" 
         unfolding PosOrd_ex_eq_def by auto     
      then have "Stars (v # vs) :\<sqsubseteq>val Stars (v3a # vs3)" using NonEmpty(4) q2 as1
        unfolding  PosOrd_ex_eq_def
        using PosOrd_StarsI PosOrd_StarsI2
        by (metis flat.simps(7) flat_Stars val.inject(5)) 
      then show "Stars (v # vs) :\<sqsubseteq>val v3" unfolding NonEmpty by blast
    next 
      case Empty
      have "v3 = Stars []" by fact
      then show "Stars (v # vs) :\<sqsubseteq>val v3"
      unfolding PosOrd_ex_eq_def using cond2
      by (simp add: PosOrd_shorterI)
    qed    
next
  case (Posix_Upto2 r n v2) 
    have "v2 \<in> LV (Upto r n) []" by fact
  then have "v2 = Stars []" 
    unfolding LV_def by (auto elim: Prf.cases) 
  then show "Stars [] :\<sqsubseteq>val v2"
    by (simp add: PosOrd_ex_eq_def)
next
  case (Posix_From2 vs r n)
  then show "Stars vs :\<sqsubseteq>val v2"
    apply(simp add: LV_def)
      apply(auto)  
    apply(erule Prf_elims)
     apply(auto)
    apply(rule PosOrd_Stars_equalsI)
    apply (metis Posix1(2) flats_empty) 
      apply(simp)
    apply(auto simp add: list_all2_iff)
    apply (meson set_zip_leftD set_zip_rightD)
    done
next
  case (Posix_From1 s1 r v s2 n vs v3)
  have "s1 \<in> r \<rightarrow> v" "s2 \<in> From r (n - 1) \<rightarrow> Stars vs" by fact+
  then have as1: "s1 = flat v" "s2 = flats vs" by (auto dest: Posix1(2))
  have IH1: "\<And>v3. v3 \<in> LV r s1 \<Longrightarrow> v :\<sqsubseteq>val v3" by fact
  have IH2: "\<And>v3. v3 \<in> LV (From r (n - 1)) s2 \<Longrightarrow> Stars vs :\<sqsubseteq>val v3" by fact
  have cond: "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (From r (n - 1)))" by fact
  have cond2: "flat v \<noteq> []" by fact
  have "v3 \<in> LV (From r n) (s1 @ s2)" by fact
  then consider 
    (NonEmpty) v3a vs3 where "v3 = Stars (v3a # vs3)" 
    "\<turnstile> v3a : r" "\<turnstile> Stars vs3 : From r (n - 1)"
    "flats (v3a # vs3) = s1 @ s2"
  | (Empty) "v3 = Stars []" 
  unfolding LV_def  
  apply(auto)
  apply(erule Prf.cases)
             apply(auto)  
  apply(case_tac vs1)
   apply(auto intro: Prf.intros)
   apply(case_tac vs2)
    apply(auto intro: Prf.intros)
    apply (simp add: as1(1) cond2 flats_empty)
  apply (simp add: Prf.intros)
  apply(case_tac vs)
   apply(auto)
  by (metis Posix_From1.hyps(6) Prf.intros(10) Suc_le_eq Suc_pred less_Suc_eq_le)
  then show "Stars (v # vs) :\<sqsubseteq>val v3" 
    proof (cases)
      case (NonEmpty v3a vs3)
      have "flats (v3a # vs3) = s1 @ s2" using NonEmpty(4) . 
      with cond have "flat v3a \<sqsubseteq>pre s1" using NonEmpty(2,3)
        unfolding prefix_list_def
        by (smt (z3) Prf_flat_lang append.right_neutral append_eq_append_conv2 flat.simps(7) flat_Stars)
      then have "flat v3a \<sqsubset>spre s1 \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" using NonEmpty(4)
        by (simp add: sprefix_list_def append_eq_conv_conj)
      then have q2: "v :\<sqsubset>val v3a \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" 
        using PosOrd_spreI as1(1) NonEmpty(4) by blast
      then have "v :\<sqsubset>val v3a \<or> (v3a \<in> LV r s1 \<and> Stars vs3 \<in> LV (From r (n - 1)) s2)" 
        using NonEmpty(2,3) by (auto simp add: LV_def)
      then have "v :\<sqsubset>val v3a \<or> (v :\<sqsubseteq>val v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" using IH1 IH2 by blast
      then have "v :\<sqsubset>val v3a \<or> (v = v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" 
         unfolding PosOrd_ex_eq_def by auto     
      then have "Stars (v # vs) :\<sqsubseteq>val Stars (v3a # vs3)" using NonEmpty(4) q2 as1
        unfolding  PosOrd_ex_eq_def
        by (metis PosOrd_StarsI PosOrd_StarsI2 flat.simps(7) flat_Stars val.inject(5))
      then show "Stars (v # vs) :\<sqsubseteq>val v3" unfolding NonEmpty by blast
    next 
      case Empty
      have "v3 = Stars []" by fact
      then show "Stars (v # vs) :\<sqsubseteq>val v3"
      unfolding PosOrd_ex_eq_def using cond2
      by (simp add: PosOrd_shorterI)
  qed       
next
  case (Posix_From3 s1 r v s2 vs v3)
    have "s1 \<in> r \<rightarrow> v" "s2 \<in> Star r \<rightarrow> Stars vs" by fact+
  then have as1: "s1 = flat v" "s2 = flat (Stars vs)" by (auto dest: Posix1(2))
  have IH1: "\<And>v3. v3 \<in> LV r s1 \<Longrightarrow> v :\<sqsubseteq>val v3" by fact
  have IH2: "\<And>v3. v3 \<in> LV (Star r) s2 \<Longrightarrow> Stars vs :\<sqsubseteq>val v3" by fact
  have cond: "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> lang r \<and> s\<^sub>4 \<in> lang (Star r))" by fact
  have cond2: "flat v \<noteq> []" by fact
  have "v3 \<in> LV (From r 0) (s1 @ s2)" by fact
  then consider 
    (NonEmpty) v3a vs3 where "v3 = Stars (v3a # vs3)" 
    "\<turnstile> v3a : r" "\<turnstile> Stars vs3 : Star r"
    "flat (Stars (v3a # vs3)) = s1 @ s2"
  | (Empty) "v3 = Stars []" 
  unfolding LV_def  
  apply(auto)
  apply(erule Prf.cases)
  apply(auto)
  apply(case_tac vs)
  apply(auto intro: Prf.intros)
  done
  then show "Stars (v # vs) :\<sqsubseteq>val v3" 
    proof (cases)
      case (NonEmpty v3a vs3)
      have "flat (Stars (v3a # vs3)) = s1 @ s2" using NonEmpty(4) . 
      with cond have "flat v3a \<sqsubseteq>pre s1" using NonEmpty(2,3)
        unfolding prefix_list_def
        by (smt (z3) Prf_flat_lang append.right_neutral append_eq_append_conv2 flat.simps(7))
      then have "flat v3a \<sqsubset>spre s1 \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" using NonEmpty(4)
        by (simp add: sprefix_list_def append_eq_conv_conj)
      then have q2: "v :\<sqsubset>val v3a \<or> (flat v3a = s1 \<and> flat (Stars vs3) = s2)" 
        using PosOrd_spreI as1(1) NonEmpty(4) by blast
      then have "v :\<sqsubset>val v3a \<or> (v3a \<in> LV r s1 \<and> Stars vs3 \<in> LV (Star r) s2)" 
        using NonEmpty(2,3) by (auto simp add: LV_def)
      then have "v :\<sqsubset>val v3a \<or> (v :\<sqsubseteq>val v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" using IH1 IH2 by blast
      then have "v :\<sqsubset>val v3a \<or> (v = v3a \<and> Stars vs :\<sqsubseteq>val Stars vs3)" 
         unfolding PosOrd_ex_eq_def by auto     
      then have "Stars (v # vs) :\<sqsubseteq>val Stars (v3a # vs3)" using NonEmpty(4) q2 as1
        unfolding  PosOrd_ex_eq_def
        by (metis PosOrd_StarsI PosOrd_StarsI2 flat.simps(7) flat_Stars val.inject(5))
      then show "Stars (v # vs) :\<sqsubseteq>val v3" unfolding NonEmpty by blast
    next 
      case Empty
      have "v3 = Stars []" by fact
      then show "Stars (v # vs) :\<sqsubseteq>val v3"
      unfolding PosOrd_ex_eq_def using cond2
      by (simp add: PosOrd_shorterI)
  qed      
next
  case (Posix_Rec s r v l v2)
  then show "Recv l v :\<sqsubseteq>val v2"
    by (smt (verit, del_insts) LV_def LV_simps(6) PosOrd_Rec_eq PosOrd_ex_eq_def Posix1(2) mem_Collect_eq) 
next
  case (Posix_Cset c cs v)
  have "v \<in> LV (Charset cs) [c]" by fact
  then have "v = Atm c \<or> False"
    apply(case_tac "c \<in> cs")
    by(auto simp add: LV_simps)
  then show "Atm c :\<sqsubseteq>val v"
    by (simp add: PosOrd_ex_eq_def)
qed


lemma Posix_PosOrd_reverse:
  assumes "s \<in> r \<rightarrow> v1" 
  shows "\<not>(\<exists>v2 \<in> LV r s. v2 :\<sqsubset>val v1)"
using assms
by (metis Posix_PosOrd less_irrefl PosOrd_def 
    PosOrd_ex_eq_def PosOrd_ex_def PosOrd_trans)

lemma PosOrd_Posix:
  assumes "v1 \<in> LV r s" "\<forall>v\<^sub>2 \<in> LV r s. \<not> v\<^sub>2 :\<sqsubset>val v1"
  shows "s \<in> r \<rightarrow> v1" 
proof -
  have "s \<in> lang r" using assms(1) unfolding LV_def
    using Prf_flat_lang by blast
  then obtain vposix where vp: "s \<in> r \<rightarrow> vposix"
    using lexer_correct_Some by blast 
  with assms(1) have "vposix :\<sqsubseteq>val v1" by (simp add: Posix_PosOrd) 
  then have "vposix = v1 \<or> vposix :\<sqsubset>val v1" unfolding PosOrd_ex_eq2 by auto
  moreover
    { assume "vposix :\<sqsubset>val v1"
      moreover
      have "vposix \<in> LV r s" using vp 
         using Posix_LV by blast 
      ultimately have "False" using assms(2) by blast
    }
  ultimately show "s \<in> r \<rightarrow> v1" using vp by blast
qed

lemma Least_existence:
  assumes "LV r s \<noteq> {}"
  shows " \<exists>vmin \<in> LV r s. \<forall>v \<in> LV r s. vmin :\<sqsubseteq>val v"
proof -
  from assms
  obtain vposix where "s \<in> r \<rightarrow> vposix"
  unfolding LV_def 
  using Prf_flat_lang lexer_correct_Some by blast
  then have "\<forall>v \<in> LV r s. vposix :\<sqsubseteq>val v"
    by (simp add: Posix_PosOrd)
  then show "\<exists>vmin \<in> LV r s. \<forall>v \<in> LV r s. vmin :\<sqsubseteq>val v"
    using Posix_LV \<open>s \<in> r \<rightarrow> vposix\<close> by blast
qed 

lemma Least_existence1:
  assumes "LV r s \<noteq> {}"
  shows " \<exists>! v\<^sub>m\<^sub>i\<^sub>n \<in> LV r s. \<forall>v \<in> LV r s. v\<^sub>m\<^sub>i\<^sub>n :\<sqsubseteq>val v"
using Least_existence[OF assms] assms
using PosOrdeq_antisym by blast

lemma Least_existence2:
  assumes "LV r s \<noteq> {}"
  shows " \<exists>!vmin \<in> LV r s. lexer r s = Some vmin \<and> (\<forall>v \<in> LV r s. vmin :\<sqsubseteq>val v)"
using Least_existence[OF assms] assms
using PosOrdeq_antisym 
using PosOrd_Posix PosOrd_ex_eq2 lexer_correctness(1)
  by (metis (mono_tags, lifting)) 


lemma Least_existence1_pre:
  assumes "LV r s \<noteq> {}"
  shows " \<exists>!vmin \<in> LV r s. \<forall>v \<in> (LV r s \<union> {v'. flat v' \<sqsubset>spre s}). vmin :\<sqsubseteq>val v"
using Least_existence[OF assms] assms
apply -
apply(erule bexE)
apply(rule_tac a="vmin" in ex1I)
apply(auto)[1]
apply (metis PosOrd_Posix PosOrd_ex_eq2 PosOrd_spreI PosOrdeq_antisym Posix1(2))
apply(auto)[1]
apply(simp add: PosOrdeq_antisym)
done

lemma PosOrd_partial:
  shows "partial_order_on UNIV {(v1, v2). v1 :\<sqsubseteq>val v2}"
apply(simp add: partial_order_on_def)
apply(simp add: preorder_on_def refl_on_def)
apply(simp add: PosOrdeq_refl)
apply(auto)
apply(rule transI)
apply(auto intro: PosOrdeq_trans)[1]
apply(rule antisymI)
apply(simp add: PosOrdeq_antisym)
done
  
lemma PosOrd_wf:
  shows "wf {(v1, v2). v1 :\<sqsubset>val v2 \<and> v1 \<in> LV r s \<and> v2 \<in> LV r s}"
proof -
  have "finite {(v1, v2). v1 \<in> LV r s \<and> v2 \<in> LV r s}"
    by (simp add: LV_finite)
  moreover
  have "{(v1, v2). v1 :\<sqsubset>val v2 \<and> v1 \<in> LV r s \<and> v2 \<in> LV r s} \<subseteq> {(v1, v2). v1 \<in> LV r s \<and> v2 \<in> LV r s}"
    by auto
  ultimately have "finite {(v1, v2). v1 :\<sqsubset>val v2 \<and> v1 \<in> LV r s \<and> v2 \<in> LV r s}" 
    using finite_subset by blast 
  moreover
  have "acyclicP (\<lambda>v1 v2. v1 :\<sqsubset>val v2 \<and> v1 \<in> LV r s \<and> v2 \<in> LV r s)" 
    unfolding acyclic_def
    by (smt (verit, ccfv_threshold) PosOrd_irrefl PosOrd_trans tranclp_trans_induct tranclp_unfold)    
  ultimately show "wf {(v1, v2). v1 :\<sqsubset>val v2 \<and> v1 \<in> LV r s \<and> v2 \<in> LV r s}"
    using finite_acyclic_wf by blast
qed  

unused_thms

end