(*  Title:       The List Update Problem
    Author:      Tobias Nipkow
                 Max Haslbeck
*)

theory List_Update_Problem
imports Complex_Main
Inversion
Competitive_Analysis
begin 


section "The List Update Problem Formalized"
 
declare Let_def[simp]

subsection "Function @{text mtf}"

definition "mtf x xs =
  (if x \<in> set xs then x # (take (index xs x) xs) @ drop (index xs x + 1) xs
   else xs)"

lemma mtf_id[simp]: "x \<notin> set xs \<Longrightarrow> mtf x xs = xs"
by(simp add: mtf_def)

lemma mtf0[simp]: "x \<in> set xs \<Longrightarrow> mtf x xs ! 0 = x"
by(auto simp: mtf_def)

lemma before_in_mtf: assumes "z \<in> set xs"
shows "x < y in mtf z xs  \<longleftrightarrow>
      (y \<noteq> z \<and> (if x=z then y \<in> set xs else x < y in xs))"
proof-
  have 0: "index xs z < size xs" by (metis assms index_less_size_conv)
  let ?xs = "take (index xs z) xs @ xs ! index xs z # drop (Suc (index xs z)) xs"
  have "x < y in mtf z xs = (y \<noteq> z \<and> (if x=z then y \<in> set ?xs else x < y in ?xs))"
    using assms
    by(auto simp add: mtf_def before_in_def index_append)
      (metis add_lessD1 index_less_size_conv length_take less_Suc_eq not_less_eq)
  with id_take_nth_drop[OF 0, symmetric] show ?thesis by(simp)
qed

lemma Inv_mtf: "set xs = set ys \<Longrightarrow> z : set ys \<Longrightarrow> Inv xs (mtf z ys) =
 Inv xs ys \<union> {(x,z)|x. x < z in xs \<and> x < z in ys}
 - {(z,x)|x. z < x in xs \<and> x < z in ys}"
by(auto simp add: Inv_def before_in_mtf not_before_in dest: before_in_setD1)

lemma set_mtf[simp]: "set(mtf x xs) = set xs"
by(simp add: mtf_def)
  (metis append_take_drop_id Cons_nth_drop_Suc index_less le_refl Un_insert_right nth_index set_append set_simps(2))

lemma length_mtf[simp]: "size (mtf x xs) = size xs"
by (auto simp add: mtf_def min_def) (metis index_less_size_conv leD)

lemma distinct_mtf[simp]: "distinct (mtf x xs) = distinct xs"
by (metis length_mtf set_mtf card_distinct distinct_card)


subsection "Function @{text swapSuc}"

definition "swapSuc n xs =
  (if Suc n < size xs then xs[n := xs!Suc n, Suc n := xs!n] else xs)"

lemma length_swapSuc[simp]: "length(swapSuc i xs) = length xs"
by(simp add: swapSuc_def)

lemma swapSuc_id[simp]: "Suc n \<ge> size xs \<Longrightarrow> swapSuc n xs = xs"
by(simp add: swapSuc_def)

lemma distinct_swapSuc[simp]:
  "distinct(swapSuc i xs) = distinct xs"
by(simp add: swapSuc_def)

lemma swapSuc_Suc[simp]: "swapSuc (Suc n) (a # xs) = a # swapSuc n xs"
by(induction xs) (auto simp: swapSuc_def)

lemma index_swapSuc_distinct:
  "distinct xs \<Longrightarrow> Suc n < length xs \<Longrightarrow>
  index (swapSuc n xs) x =
  (if x = xs!n then Suc n else if x = xs!Suc n then n else index xs x)"
by(auto simp add: swapSuc_def index_swap_if_distinct)

lemma set_swapSuc[simp]: "set(swapSuc n xs) = set xs"
by(auto simp add: swapSuc_def set_conv_nth nth_list_update) metis

lemma nth_swapSuc_id[simp]: "Suc i < length xs \<Longrightarrow> swapSuc i xs ! i = xs!(i+1)"
by(simp add: swapSuc_def)

lemma before_in_swapSuc:
 "dist_perm xs ys \<Longrightarrow> Suc n < size xs \<Longrightarrow>
  x < y in (swapSuc n xs) \<longleftrightarrow>
  x < y in xs \<and> \<not> (x = xs!n \<and> y = xs!Suc n) \<or> x = xs!Suc n \<and> y = xs!n"
by(simp add:before_in_def index_swapSuc_distinct)
  (metis Suc_lessD Suc_lessI index_less_size_conv index_nth_id less_Suc_eq n_not_Suc_n nth_index)

lemma Inv_swap: assumes "dist_perm xs ys"
shows "Inv xs (swapSuc n ys) = 
  (if Suc n < size xs
   then if ys!n < ys!Suc n in xs
        then Inv xs ys \<union> {(ys!n, ys!Suc n)}
        else Inv xs ys - {(ys!Suc n, ys!n)}
   else Inv xs ys)"
proof-
  have "length xs = length ys" using assms by (metis distinct_card)
  with assms show ?thesis
    by(simp add: Inv_def set_eq_iff)
      (metis before_in_def not_before_in before_in_swapSuc)
qed


abbreviation swapSucs where "swapSucs == foldr swapSuc"

lemma swapSucs_inv[simp]:
  "set (swapSucs sws xs) = set xs \<and>
  size(swapSucs sws xs) = size xs \<and>
  distinct(swapSucs sws xs) = distinct xs"
by (induct sws arbitrary: xs) (simp_all add: swapSuc_def)

lemma swapSucs_eq_Nil_iff[simp]: "swapSucs acts xs = [] \<longleftrightarrow> xs = []"
by(induction acts)(auto simp: swapSuc_def)

lemma swapSucs_map_Suc[simp]:
  "swapSucs (map Suc sws) (a # xs) = a # swapSucs sws xs"
by(induction sws arbitrary: xs) auto

lemma card_Inv_swapSucs_le:
  "distinct xs \<Longrightarrow> card (Inv xs (swapSucs sws xs)) \<le> length sws"
by(induction sws) (auto simp: Inv_swap card_insert_if card_Diff_singleton_if)

lemma nth_swapSucs: "\<forall>i\<in>set is. j < i \<Longrightarrow> swapSucs is xs ! j = xs ! j"
by(induction "is")(simp_all add: swapSuc_def)

lemma not_before0[simp]: "~ x < xs ! 0 in xs"
apply(cases "xs = []")
by(auto simp: before_in_def neq_Nil_conv)

lemma before_id[simp]: "\<lbrakk> distinct xs; i < size xs; j < size xs \<rbrakk> \<Longrightarrow>
  xs ! i < xs ! j in xs \<longleftrightarrow> i < j"
by(simp add: before_in_def index_nth_id)

lemma before_swapSucs:
  "\<lbrakk> distinct is; \<forall>i\<in>set is. Suc i < size xs; distinct xs; i \<notin> set is; i < j; j < size xs \<rbrakk> \<Longrightarrow>
  swapSucs is xs ! i < swapSucs is xs ! j in xs"
apply(induction "is" arbitrary: i j)
 apply simp
apply(auto simp: swapSuc_def nth_list_update)
done

lemma card_Inv_swapSucs:
  "\<lbrakk> distinct is; \<forall>i\<in>set is. Suc i < size xs; distinct xs \<rbrakk> \<Longrightarrow>
  card(Inv xs (swapSucs is xs)) = length is"
apply(induction "is")
 apply simp
apply(simp add: Inv_swap before_swapSucs card_insert_if)
apply(simp add: Inv_def)
done

subsection "Function @{text mtf2}"

(* alternative definition von mtf, befördert das element x um n stellen nach vorne *)
definition mtf2 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"mtf2 n x xs = (if x : set xs then swapSucs [index xs x - n..<index xs x] xs else xs)"

lemma length_mtf2[simp]: "length (mtf2 n x xs) = length xs"
by (auto simp: mtf2_def index_less_size_conv[symmetric]
  simp del:index_conv_size_if_notin)

lemma set_mtf2[simp]: "set(mtf2 n x xs) = set xs"
by (auto simp: mtf2_def index_less_size_conv[symmetric]
  simp del:index_conv_size_if_notin)

lemma distinct_mtf2[simp]: "distinct (mtf2 n x xs) = distinct xs"
by (metis length_mtf2 set_mtf2 card_distinct distinct_card)


lemma card_Inv_mtf2: "xs!j = ys!0 \<Longrightarrow> j < length xs \<Longrightarrow> dist_perm xs ys \<Longrightarrow>
   card (Inv (swapSucs [i..<j] xs) ys) = card (Inv xs ys) - int(j-i)"
proof(induction j arbitrary: xs)
  case (Suc j)
  show ?case
  proof cases
    assume "i > j" thus ?thesis by simp
  next
    assume [arith]: "\<not> i > j"
    have 0: "Suc j < length ys" by (metis Suc.prems(2,3) distinct_card)
    have 1: "(ys ! 0, xs ! j) : Inv ys xs"
    proof (auto simp: Inv_def)
      show "ys ! 0 < xs ! j in ys" using Suc.prems
        by (metis Suc_lessD n_not_Suc_n not_before0 not_before_in nth_eq_iff_index_eq nth_mem)
      show "xs ! j < ys ! 0 in xs" using Suc.prems
        by (metis Suc_lessD before_id lessI)
    qed
    have 2: "card(Inv ys xs) \<noteq> 0" using 1 by auto
    have "int(card (Inv (swapSucs [i..<Suc j] xs) ys)) =
          card (Inv (swapSuc j xs) ys) - int (j-i)" using Suc by simp
    also have "\<dots> = card (Inv ys (swapSuc j xs)) - int (j-i)"
      by(simp add: card_Inv_sym)
    also have "\<dots> = card (Inv ys xs - {(ys ! 0, xs ! j)}) - int (j - i)"
      using Suc.prems 0 by(simp add: Inv_swap)
    also have "\<dots> = int(card (Inv ys xs) - 1) - (j - i)"
      using 1 by(simp add: card_Diff_singleton)
    also have "\<dots> = card (Inv ys xs) - int (Suc j - i)" using 2 by arith
    also have "\<dots> = card (Inv xs ys) - int (Suc j - i)" by(simp add: card_Inv_sym)
    finally show ?thesis .
  qed
qed simp


subsection "Function @{text mtf1}"

definition "mtf1 x xs = mtf2 (length xs) x xs"

lemma swapSucs_eq_nth_take_drop: "i < length xs \<Longrightarrow>
    swapSucs [0..<i] xs = xs!i # take i xs @ drop (Suc i) xs"
apply(induction i arbitrary: xs)
apply (auto simp add: neq_Nil_conv swapSuc_def drop_update_swap
  take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])
done

lemma mtf1_eq_mtf: "mtf1 x xs = mtf x xs"
by(auto simp: mtf1_def mtf_def mtf2_def swapSucs_eq_nth_take_drop index_le_size)




lemma mtf20[simp]: "mtf2 0 x xs = xs"
by(auto simp add: mtf2_def)

type_synonym 'a state = "'a list"
type_synonym 'a action = "nat * nat list"

(* sws sind paid exchanges, dann wird ein element q um k nach vorne free exchanged *)
definition step :: "'a state \<Rightarrow> 'a \<Rightarrow> 'a action \<Rightarrow> 'a state" where
"step s q a =
  (let (k,sws) = a in mtf2 k q (swapSucs sws s))"

definition t :: "'a state \<Rightarrow> 'a \<Rightarrow> 'a action \<Rightarrow> nat" where
"t s q a = (let (mf,sws) = a in index (swapSucs sws s) q + 1 + size sws)"


lemma length_step[simp]: "length (step s q as) = length s"
by(simp add: step_def split_def)

lemma step_Nil_iff[simp]: "step xs q act = [] \<longleftrightarrow> xs = []"
by(auto simp add: step_def mtf2_def split: prod.splits)


lemma set_step2: "set(step s q (mf,sws)) = set s"
by(auto simp add: step_def) 

lemma set_step: "set(step s q act) = set s"
by(cases act)(simp add: set_step2)

lemma distinct_step: "distinct(step s q as) = distinct s" (* earlier there was 's \<noteq> []' added as assumption, not needed! *)
by (auto simp: step_def split_def)


(* The core idea with upper bounds: *)
lemma potential:
fixes t :: "nat \<Rightarrow> 'a::linordered_ab_group_add" and p :: "nat \<Rightarrow> 'a"
assumes p0: "p 0 = 0" and ppos: "\<And>n. p n \<ge> 0"
and ub: "\<And>n. t n + p(n+1) - p n \<le> u n"
shows "(\<Sum>i<n. t i) \<le> (\<Sum>i<n. u i)"
proof-
  let ?a = "\<lambda>n. t n + p(n+1) - p n"
  have 1: "(\<Sum>i<n. t i) = (\<Sum>i<n. ?a i) - p(n)"
    by(induction n) (simp_all add: p0)
  thus ?thesis
    by (metis (erased, lifting) add.commute diff_add_cancel le_add_same_cancel2 order.trans ppos setsum_mono ub)
qed


(* The core idea with upper bounds: *)
lemma potential2:
fixes t :: "nat \<Rightarrow> 'a::linordered_ab_group_add" and p :: "nat \<Rightarrow> 'a"
assumes p0: "p 0 = 0" and ppos: "\<And>n. p n \<ge> 0"
and ub: "\<And>m. m<n \<Longrightarrow> t m + p(m+1) - p m \<le> u m"
shows "(\<Sum>i<n. t i) \<le> (\<Sum>i<n. u i)"
proof-
  let ?a = "\<lambda>n. t n + p(n+1) - p n"
  have "(\<Sum>i<n. t i) = (\<Sum>i<n. ?a i) - p(n)" by(induction n) (simp_all add: p0)
  also have      "\<dots> \<le> (\<Sum>i<n. ?a i)" using ppos by auto
  also have      "\<dots> \<le> (\<Sum>i<n. u i)" apply(rule setsum_mono) apply(rule ub) by auto
  finally show ?thesis .
qed

abbreviation "before x xs \<equiv> {y. y < x in xs}"
abbreviation "after x xs \<equiv> {y. x < y in xs}"

lemma finite_before[simp]: "finite (before x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD1)
done

lemma finite_after[simp]: "finite (after x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD2)
done

lemma before_conv_take:
  "x : set xs \<Longrightarrow> before x xs = set(take (index xs x) xs)"
by (auto simp add: before_in_def set_take_if_index index_le_size) (metis index_take leI)

lemma card_before: "distinct xs \<Longrightarrow> x : set xs \<Longrightarrow> card (before x xs) = index xs x"
using  index_le_size[of xs x]
by(simp add: before_conv_take distinct_card[OF distinct_take] min_def)

lemma before_Un: "set xs = set ys \<Longrightarrow> x : set xs \<Longrightarrow>
  before x ys = before x xs \<inter> before x ys Un after x xs \<inter> before x ys"
by(auto)(metis before_in_setD1 not_before_in)

lemma not_before_Cons[simp]: "\<not> x < y in y # xs"
by (simp add: before_in_def)

lemma before_Cons[simp]:
  "q \<in> set xs \<Longrightarrow> q \<noteq> x \<Longrightarrow> before q (x#xs) = insert x (before q xs)"
by(auto simp: before_in_def)

lemma card_before_le_index: "card (before q xs) \<le> index xs q"
apply(cases "q \<in> set xs")
 prefer 2 apply (simp add: before_in_def)
apply(induction xs)
 apply (simp add: before_in_def)
apply (auto simp: card_insert_if)
done




subsection "partial cost model"

definition t\<^sub>p :: "'a state \<Rightarrow> 'a \<Rightarrow> 'a action \<Rightarrow> nat" where
"t\<^sub>p s q a = (let (mf,sws) = a in index (swapSucs sws s) q + size sws)"

notation (latex) t\<^sub>p ("\<^raw:$t^{*}$>")

lemma t\<^sub>pt: "t\<^sub>p s q a + 1 = t s q a" unfolding t\<^sub>p_def t_def by(simp add: split_def)

term "T"


interpretation full: On_Off step t. 
 
abbreviation "config == full.config"
abbreviation "config' == full.config'"
abbreviation "T == full.T"
abbreviation "T_opt == full.T_opt"      
abbreviation "T_on == full.T_on"      
abbreviation "T_on_rand == full.T_on_rand"   
abbreviation "T_on_n == full.T_on_n" 
abbreviation "T_off == full.T_off" 
abbreviation "compet == full.compet"

notation (latex) T_opt ("\<^raw:$T_{opt}$>")
notation (latex) T_on ("\<^raw:$T_{on}$>")
notation (latex) T_off ("\<^raw:$T_{off}$>") 




lemmas config_induct = full.config'_induct

lemma T_ge_len: "length as = length qs \<Longrightarrow> T s qs as \<ge> length qs"
by(induction arbitrary: s rule: list_induct2)
  (auto simp: t_def trans_le_add2)

lemma T_off_neq0: "(\<And>qs s0. size(alg s0 qs) = length qs) \<Longrightarrow>
  qs \<noteq> [] \<Longrightarrow> T_off alg s0 qs \<noteq> 0"
apply(erule_tac x=qs in meta_allE)
apply(erule_tac x=s0 in meta_allE)
apply (auto simp: neq_Nil_conv length_Suc_conv t_def)
done
 



lemma config_config_length: "\<forall>x\<in>set_pmf (config  A init qs). length (fst x) = length init"
apply (induct rule: config_induct) by (simp_all)

lemma config_config_distinct: 
  shows "\<forall>x \<in> (config  A init qs). distinct (fst x) = distinct init" 
apply (induct rule: config_induct) by (simp_all add: distinct_step)

lemma config_config_set: 
  shows " \<forall>x \<in> (config   A init qs). set (fst x) = set init"
apply(induct rule: config_induct) by(simp_all add: set_step)

lemma config_config:
  "\<forall>x \<in> (config   A  init qs). set (fst x) = set init
        \<and> distinct (fst x) = distinct init \<and> length (fst x) = length init"
using config_config_distinct config_config_set config_config_length by metis

lemma config_dist_perm:
  "distinct init \<Longrightarrow> \<forall>x \<in> (config A init qs). dist_perm (fst x) init"
using config_config_distinct config_config_set config_config_length by metis
 
end 
