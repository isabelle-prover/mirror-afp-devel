(* Author: Bernhard Stöckl *)

theory IKKBZ_Optimality
  imports Complex_Main "CostFunctions" "QueryGraph" "IKKBZ" "HOL-Library.Sublist"
begin

section \<open>Optimality of IKKBZ\<close>

context directed_tree
begin
fun forward_arcs :: "'a list \<Rightarrow> bool" where
  "forward_arcs [] = True"
| "forward_arcs [x] = True"
| "forward_arcs (x#xs) = ((\<exists>y \<in> set xs. y \<rightarrow>\<^bsub>T\<^esub> x) \<and> forward_arcs xs)"

fun no_back_arcs :: "'a list \<Rightarrow> bool" where
  "no_back_arcs [] = True"
| "no_back_arcs (x#xs) = ((\<nexists>y. y \<in> set xs \<and> y \<rightarrow>\<^bsub>T\<^esub> x) \<and> no_back_arcs xs)"

definition forward :: "'a list \<Rightarrow> bool" where
  "forward xs = (\<forall>i \<in> {1..(length xs - 1)}. \<exists>j < i. xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i)"

definition no_back :: "'a list \<Rightarrow> bool" where
  "no_back xs = (\<nexists>i j. i < j \<and> j < length xs \<and> xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i)"

definition seq_conform :: "'a list \<Rightarrow> bool" where
  "seq_conform xs \<equiv> forward_arcs (rev xs) \<and> no_back_arcs xs"

definition before :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "before s1 s2 \<equiv> seq_conform s1 \<and> seq_conform s2 \<and> set s1 \<inter> set s2 = {}
    \<and> (\<exists>x \<in> set s1. \<exists>y \<in> set s2. x \<rightarrow>\<^bsub>T\<^esub> y)"

definition before2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "before2 s1 s2 \<equiv> seq_conform s1 \<and> seq_conform s2 \<and> set s1 \<inter> set s2 = {}
    \<and> (\<exists>x \<in> set s1. \<exists>y \<in> set s2. x \<rightarrow>\<^bsub>T\<^esub> y)
    \<and> (\<forall>x \<in> set s1. \<forall>v \<in> verts T - set s1 - set s2. \<not> x \<rightarrow>\<^bsub>T\<^esub> v)"

lemma before_alt1:
  "(\<exists>i < length s1. \<exists>j < length s2. s1!i \<rightarrow>\<^bsub>T\<^esub> s2!j) \<longleftrightarrow> (\<exists>x \<in> set s1. \<exists>y \<in> set s2. x \<rightarrow>\<^bsub>T\<^esub> y)"
  using in_set_conv_nth by metis

lemma before_alt2:
  "(\<forall>i < length s1. \<forall>v \<in> verts T - set s1 - set s2. \<not> s1!i \<rightarrow>\<^bsub>T\<^esub> v)
    \<longleftrightarrow> (\<forall>x \<in> set s1. \<forall>v \<in> verts T  - set s1 - set s2. \<not> x \<rightarrow>\<^bsub>T\<^esub> v)"
  using in_set_conv_nth by metis

lemma no_back_alt_aux: "(\<forall>i j. i \<ge> j \<or> j \<ge> length xs \<or> \<not>(xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i)) \<Longrightarrow> no_back xs"
  using less_le_not_le no_back_def by auto

lemma no_back_alt: "(\<forall>i j. i \<ge> j \<or> j \<ge> length xs \<or> \<not>(xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i)) \<longleftrightarrow> no_back xs"
  using no_back_alt_aux by (auto simp: no_back_def)

lemma no_back_arcs_alt_aux1: "\<lbrakk>no_back_arcs xs; i < j; j < length xs\<rbrakk> \<Longrightarrow> \<not>(xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i)"
proof(induction xs arbitrary: i j)
  case (Cons x xs)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then show ?thesis using Cons by auto
  qed
qed(simp)

lemma no_back_insert_aux:
  "(\<forall>i j. i \<ge> j \<or> j \<ge> length (x#xs) \<or> \<not>((x#xs)!j \<rightarrow>\<^bsub>T\<^esub> (x#xs)!i))
    \<Longrightarrow> (\<forall>i j. i \<ge> j \<or> j \<ge> length xs \<or> \<not>(xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i))"
  by force

lemma no_back_insert: "no_back (x#xs) \<Longrightarrow> no_back xs"
  using no_back_alt no_back_insert_aux by blast

lemma no_arc_fst_if_no_back:
  assumes "no_back (x#xs)" and "y \<in> set xs"
  shows "\<not> y \<rightarrow>\<^bsub>T\<^esub> x"
proof -
  have 0: "(x#xs)!0 = x" by simp
  obtain j where "xs!j = y" "j < length xs" using assms(2) by (auto simp: in_set_conv_nth)
  then have "(x#xs)!(Suc j) = y \<and> Suc j < length (x#xs)" by simp
  then show ?thesis using assms(1) 0 by (metis no_back_def zero_less_Suc)
qed

lemma no_back_arcs_alt_aux2: "no_back xs \<Longrightarrow> no_back_arcs xs"
  by(induction xs) (auto simp: no_back_insert no_arc_fst_if_no_back)

lemma no_back_arcs_alt: "no_back xs \<longleftrightarrow> no_back_arcs xs"
  using no_back_arcs_alt_aux1 no_back_arcs_alt_aux2 no_back_alt by fastforce

lemma forward_arcs_alt_aux1:
  "\<lbrakk>forward_arcs xs; i \<in> {1..(length (rev xs) - 1)}\<rbrakk> \<Longrightarrow> \<exists>j < i. (rev xs)!j \<rightarrow>\<^bsub>T\<^esub> (rev xs)!i"
proof(induction xs rule: forward_arcs.induct)
  case (3 x x' xs)
  then show ?case
  proof(cases "i = length (rev (x#x'#xs)) - 1")
    case True
    then have i: "(rev (x#x'#xs))!i = x" by (simp add: nth_append)
    then obtain y where y_def: "y\<in>set (x'#xs)" "y \<rightarrow>\<^bsub>T\<^esub> x" using "3.prems" by auto
    then obtain j where j_def: "rev (x'#xs)!j = y" "j < length (rev (x'#xs))"
      using in_set_conv_nth[of y] by fastforce
    then have "rev (x#x'#xs)!j = y" by (auto simp: nth_append)
    then show ?thesis using y_def(2) i j_def(2) True by auto
  next
    case False
    then obtain j where j_def: "j < i" "rev (x' # xs)!j \<rightarrow>\<^bsub>T\<^esub> rev (x' # xs)!i" using 3 by auto
    then have "rev (x#x'#xs)!j = rev (x'#xs)!j" using "3.prems"(2) by (auto simp: nth_append)
    moreover have "rev (x#x'#xs)!i = rev (x'#xs)!i"
      using "3.prems"(2) False by (auto simp: nth_append)
    ultimately show ?thesis using j_def by auto
  qed
qed(auto)

lemma forward_split_aux:
  assumes "forward (xs@ys)" and "i\<in>{1..length xs - 1}"
  shows "\<exists>j<i. xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i"
proof -
  obtain j where "j < i \<and> (xs@ys)!j \<rightarrow>\<^bsub>T\<^esub> (xs@ys)!i" using assms forward_def by force
  moreover have "i < length xs" using assms(2) by auto
  ultimately show ?thesis by (auto simp: nth_append)
qed

lemma forward_split: "forward (xs@ys) \<Longrightarrow> forward xs"
  using forward_split_aux forward_def by blast

lemma forward_cons:
  "forward (rev (x#xs)) \<Longrightarrow> forward (rev xs)"
  using forward_split by simp

lemma arc_to_lst_if_forward:
  assumes "forward (rev (x#xs))" and "xs = y#ys"
  shows "\<exists>y \<in> set xs. y \<rightarrow>\<^bsub>T\<^esub> x"
proof -
  have "(x#xs)!0 = x" by simp
  have "(rev xs@[x])!(length xs) = (xs@[x])!(length xs)" by (metis length_rev nth_append_length)
  then have i: "rev (x#xs)!(length xs) = x" by simp
  have "length xs \<in> {1..(length (rev (x#xs)) - 1)}" using assms(2) by simp
  then obtain j where j_def: "j < length xs \<and> (rev (x#xs))!j \<rightarrow>\<^bsub>T\<^esub> (rev (x#xs))!length xs"
    using assms(1) forward_def[of "rev (x#xs)"] by blast
  then have "rev xs!j \<in> set xs" using length_rev nth_mem set_rev by metis
  then have "rev (x#xs)!j \<in> set xs" by (auto simp: j_def nth_append)
  then show ?thesis using i j_def by auto
qed

lemma forward_arcs_alt_aux2: "forward (rev xs) \<Longrightarrow> forward_arcs xs"
proof(induction xs rule: forward_arcs.induct)
  case (3 x y xs)
  then have "forward_arcs (y # xs)" using forward_cons by blast
  then show ?case using arc_to_lst_if_forward "3.prems" by simp
qed(auto)

lemma forward_arcs_alt: "forward xs \<longleftrightarrow> forward_arcs (rev xs)"
  using forward_arcs_alt_aux1 forward_arcs_alt_aux2 forward_def by fastforce

corollary forward_arcs_alt': "forward (rev xs) \<longleftrightarrow> forward_arcs xs"
  using forward_arcs_alt by simp

corollary forward_arcs_split: "forward_arcs (ys@xs) \<Longrightarrow> forward_arcs xs"
  using forward_split[of "rev xs" "rev ys"] forward_arcs_alt by simp

lemma seq_conform_alt: "seq_conform xs \<longleftrightarrow> forward xs \<and> no_back xs"
  using forward_arcs_alt no_back_arcs_alt seq_conform_def by simp

lemma forward_app_aux:
  assumes "forward s1" "forward s2" "\<exists>x\<in>set s1. x \<rightarrow>\<^bsub>T\<^esub> hd s2" "i\<in>{1..length (s1@s2) - 1}"
  shows "\<exists>j<i. (s1@s2)!j \<rightarrow>\<^bsub>T\<^esub> (s1@s2)!i"
proof -
  consider "i\<in>{1..length s1 - 1}" | "i = length s1" | "i\<in>{length s1 + 1..length s1 + length s2 - 1}"
    using assms(4) by fastforce
  then show ?thesis
  proof(cases)
    case 1
    then obtain j where j_def: "j < i" "s1!j \<rightarrow>\<^bsub>T\<^esub> s1!i" using assms(1) forward_def by blast
    moreover have "(s1@s2)!i = s1!i" using 1 by (auto simp: nth_append)
    moreover have "(s1@s2)!j = s1!j" using 1 j_def(1) by (auto simp: nth_append)
    ultimately show ?thesis by auto
  next
    case 2
    then have "s2 \<noteq> []" using assms(4) by force
    then have "(s1@s2)!i = hd s2" using 2 assms(4) by (simp add: hd_conv_nth nth_append)
    then obtain x where x_def: "x\<in>set s1" "x \<rightarrow>\<^bsub>T\<^esub> (s1@s2)!i" using assms(3) by force
    then obtain j where "s1!j = x" "j < length s1" by (auto simp: in_set_conv_nth)
    then show ?thesis using x_def(2) 2 by (auto simp: nth_append)
  next
    case 3
    then have "i-length s1 \<in> {1..length s2 - 1}" by fastforce
    then obtain j where j_def: "j < (i-length s1)" "s2!j \<rightarrow>\<^bsub>T\<^esub> s2!(i-length s1)"
      using assms(2) forward_def by blast
    moreover have "(s1@s2)!i = s2!(i-length s1)" using 3 by (auto simp: nth_append)
    moreover have "(s1@s2)!(j+length s1) = s2!j" using 3 j_def(1) by (auto simp: nth_append)
    ultimately have "(j+length s1) < i \<and> (s1@s2)!(j+length s1) \<rightarrow>\<^bsub>T\<^esub> (s1@s2)!i" by force
    then show ?thesis by blast
  qed
qed

lemma forward_app: "\<lbrakk>forward s1; forward s2; \<exists>x\<in>set s1. x \<rightarrow>\<^bsub>T\<^esub> hd s2\<rbrakk> \<Longrightarrow> forward (s1@s2)"
  by (simp add: forward_def forward_app_aux)

lemma before_conform1I: "before s1 s2 \<Longrightarrow> seq_conform s1"
  unfolding before_def by blast

lemma before_forward1I: "before s1 s2 \<Longrightarrow> forward s1"
  unfolding before_def seq_conform_alt by blast

lemma before_no_back1I: "before s1 s2 \<Longrightarrow> no_back s1"
  unfolding before_def seq_conform_alt by blast

lemma before_ArcI: "before s1 s2 \<Longrightarrow> \<exists>x \<in> set s1. \<exists>y \<in> set s2. x \<rightarrow>\<^bsub>T\<^esub> y"
  unfolding before_def by blast

lemma before_conform2I: "before s1 s2 \<Longrightarrow> seq_conform s2"
  unfolding before_def by blast

lemma before_forward2I: "before s1 s2 \<Longrightarrow> forward s2"
  unfolding before_def seq_conform_alt by blast

lemma before_no_back2I: "before s1 s2 \<Longrightarrow> no_back s2"
  unfolding before_def seq_conform_alt by blast

lemma hd_reach_all_forward_arcs:
  "\<lbrakk>hd (rev xs) \<in> verts T; forward_arcs xs; x \<in> set xs\<rbrakk> \<Longrightarrow> hd (rev xs) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
proof(induction xs arbitrary: x rule: forward_arcs.induct)
  case (3 z y ys)
  then have 0: "(\<exists>y \<in> set (y#ys). y \<rightarrow>\<^bsub>T\<^esub> z)" "forward_arcs (y#ys)" by auto
  have hd_eq: "hd (rev (z # y # ys)) = hd (rev (y # ys))"
    using hd_rev[of "y#ys"] by (auto simp: last_ConsR)
  then show ?case
  proof(cases "x = z")
    case True
    then obtain x' where x'_def: "x' \<in> set (y#ys)" "x' \<rightarrow>\<^bsub>T\<^esub> x" using "3.prems"(2) by auto
    then have "hd (rev (z # y # ys)) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x'" using 3 hd_eq by simp
    then show ?thesis using x'_def(2) reachable_adj_trans by blast
  next
    case False
    then show ?thesis using 3 hd_eq by simp
  qed
qed(auto)

lemma hd_reach_all_forward:
  "\<lbrakk>hd xs \<in> verts T; forward xs; x \<in> set xs\<rbrakk> \<Longrightarrow> hd xs \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
  using hd_reach_all_forward_arcs[of "rev xs"] by (simp add: forward_arcs_alt)

lemma hd_in_verts_if_forward: "forward (x#y#xs) \<Longrightarrow> hd (x#y#xs) \<in> verts T"
  unfolding forward_def by fastforce

lemma two_elems_if_length_gt1: "length xs > 1 \<Longrightarrow> \<exists>x y ys. x#y#ys=xs"
  by (metis create_ldeep_rev.cases list.size(3) One_nat_def length_Cons less_asym zero_less_Suc)

lemma hd_in_verts_if_forward': "\<lbrakk>length xs > 1; forward xs\<rbrakk> \<Longrightarrow> hd xs \<in> verts T"
  using two_elems_if_length_gt1 hd_in_verts_if_forward by blast

lemma hd_reach_all_forward':
  "\<lbrakk>length xs > 1; forward xs; x \<in> set xs\<rbrakk> \<Longrightarrow> hd xs \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x"
  by (simp add: hd_in_verts_if_forward' hd_reach_all_forward)

lemma hd_reach_all_forward'':
  "\<lbrakk>forward (x#y#xs); z \<in> set (x#y#xs)\<rbrakk> \<Longrightarrow> hd (x#y#xs) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> z"
  using hd_in_verts_if_forward hd_reach_all_forward by blast

lemma no_back_if_distinct_forward: "\<lbrakk>forward xs; distinct xs\<rbrakk> \<Longrightarrow> no_back xs"
unfolding no_back_def proof
  assume "\<exists>i j. i < j \<and> j < length xs \<and> xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i" and assms: "forward xs" "distinct xs"
  then obtain i j where i_def: "i < j" "j < length xs" "xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i" by blast
  show False
  proof(cases "i=0")
    case True
    then have "xs!i = hd xs" using i_def(1,2) hd_conv_nth[of xs] by fastforce
    then have "xs!i \<rightarrow>\<^sup>*\<^bsub>T\<^esub> xs!j" using i_def(1,2) assms(1) hd_reach_all_forward' by simp
    then have "xs!i \<rightarrow>\<^sup>+\<^bsub>T\<^esub> xs!j" using reachable_neq_reachable1 i_def(3) by force
    then show ?thesis using i_def(3) reachable1_not_reverse by blast
  next
    case False
    then have "i \<in> {1 .. length xs - 1}" using i_def(1,2) by simp
    then obtain j' where j'_def: "j' < i" "xs!j' \<rightarrow>\<^bsub>T\<^esub> xs!i"
      using assms(1) unfolding forward_def by blast
    have "xs!j' = xs!j" using i_def(3) j'_def(2) two_in_arcs_contr by fastforce
    moreover have "xs!j' \<noteq> xs!j"
      using j'_def(1) i_def(1,2) assms(2) nth_eq_iff_index_eq by fastforce
    ultimately show ?thesis by blast
  qed
qed

corollary seq_conform_if_dstnct_fwd: "\<lbrakk>forward xs; distinct xs\<rbrakk> \<Longrightarrow> seq_conform xs"
  using no_back_if_distinct_forward seq_conform_def forward_arcs_alt no_back_arcs_alt by blast

lemma forward_arcs_single: "forward_arcs [x]"
  by simp

lemma forward_single: "forward [x]"
  unfolding forward_def by simp

lemma no_back_arcs_single: "no_back_arcs [x]"
  by simp

lemma no_back_single: "no_back [x]"
  unfolding no_back_def by simp

lemma seq_conform_single: "seq_conform [x]"
  unfolding seq_conform_def by simp

lemma forward_arc_to_head':
  assumes "forward ys" and "x \<notin> set ys" and "y \<in> set ys" and "x \<rightarrow>\<^bsub>T\<^esub> y"
  shows "y = hd ys"
proof (rule ccontr)
  assume asm: "y \<noteq> hd ys"
  obtain i where i_def: "i < length ys" "ys!i = y" using assms(3) by (auto simp: in_set_conv_nth)
  then have "i \<noteq> 0" using asm by (metis drop0 hd_drop_conv_nth)
  then have "i \<in> {1..(length ys - 1)}" using i_def(1) by simp
  then obtain j where j_def: "j < i" "ys!j \<rightarrow>\<^bsub>T\<^esub> ys!i"
    using assms(1) forward_def by blast
  then show False using assms(4,2) j_def(2) i_def two_in_arcs_contr by fastforce
qed

corollary forward_arc_to_head:
  "\<lbrakk>forward ys; set xs \<inter> set ys = {}; x \<in> set xs; y \<in> set ys; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> y = hd ys"
  using forward_arc_to_head' by blast

lemma forward_app':
  "\<lbrakk>forward s1; forward s2; set s1 \<inter> set s2 = {}; \<exists>x\<in>set s1. \<exists>y\<in>set s2. x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> forward (s1@s2)"
  using forward_app[of s1 s2] forward_arc_to_head by blast

lemma reachable1_from_outside_dom:
  "\<lbrakk>x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; x \<notin> set ys; y \<in> set ys\<rbrakk> \<Longrightarrow> \<exists>x'. \<exists>y' \<in> set ys. x' \<notin> set ys \<and> x' \<rightarrow>\<^bsub>T\<^esub> y'"
  by (induction x y rule: trancl.induct) auto

lemma hd_reachable1_from_outside':
  "\<lbrakk>x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; forward ys; x \<notin> set ys; y \<in> set ys\<rbrakk> \<Longrightarrow> \<exists>y' \<in> set ys. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> hd ys"
  apply(induction x y rule: trancl.induct)
  using forward_arc_to_head' by force+

lemma hd_reachable1_from_outside:
  "\<lbrakk>x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; forward ys; set xs \<inter> set ys = {}; x \<in> set xs; y \<in> set ys\<rbrakk>
    \<Longrightarrow> \<exists>y' \<in> set ys. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> hd ys"
  using hd_reachable1_from_outside' by blast

lemma reachable1_append_old_if_arc:
  assumes "\<exists>x\<in>set xs. \<exists>y\<in>set ys. x \<rightarrow>\<^bsub>T\<^esub> y"
      and "z \<notin> set xs"
      and "forward xs"
      and "y\<in>set (xs @ ys)"
      and "z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
  shows "\<exists>y\<in>set ys. z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof(cases "y \<in> set ys")
  case True
  then show ?thesis using assms(5) by blast
next
  case False
  then have "y \<in> set xs" using assms(4) by simp
  then have 0: "z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> hd xs" using hd_reachable1_from_outside'[OF assms(5,3,2)] by blast
  then have 1: "hd xs \<in> verts T" using reachable1_in_verts(2) by auto
  obtain x y where x_def: "x\<in>set xs" "y\<in>set ys" "x \<rightarrow>\<^bsub>T\<^esub> y" using assms(1) by blast
  then have "hd xs \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" using hd_reach_all_forward[OF 1 assms(3)] by simp
  then have "hd xs \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y" using x_def(3) by force
  then show ?thesis using reachable1_reachable_trans[OF 0] x_def(2) by blast
qed

lemma reachable1_append_old_if_arcU:
   "\<lbrakk>\<exists>x\<in>set xs. \<exists>y\<in>set ys. x \<rightarrow>\<^bsub>T\<^esub> y; set U \<inter> set xs = {}; z \<in> set U;
      forward xs; y\<in>set (xs @ ys); z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> \<exists>y\<in>set ys. z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
  using reachable1_append_old_if_arc[of xs ys] by auto

lemma before_arc_to_hd: "before xs ys \<Longrightarrow> \<exists>x \<in> set xs. x \<rightarrow>\<^bsub>T\<^esub> hd ys"
  using forward_arc_to_head before_def seq_conform_alt by auto

lemma no_back_backarc_app1:
  "\<lbrakk>j < length (xs@ys); j \<ge> length xs; i < j; no_back ys; (xs@ys)!j \<rightarrow>\<^bsub>T\<^esub> (xs@ys)!i\<rbrakk>
    \<Longrightarrow> i < length xs"
  by (rule ccontr) (auto simp add: no_back_def nth_append)

lemma no_back_backarc_app2: "\<lbrakk>no_back xs; i < j; (xs@ys)!j \<rightarrow>\<^bsub>T\<^esub> (xs@ys)!i\<rbrakk> \<Longrightarrow> j \<ge> length xs"
  by (rule ccontr) (auto simp add: no_back_def nth_append)

lemma no_back_backarc_i_in_xs:
  "\<lbrakk>no_back ys; j < length (xs@ys); i < j; (xs@ys)!j \<rightarrow>\<^bsub>T\<^esub> (xs@ys)!i\<rbrakk>
    \<Longrightarrow> xs!i \<in> set xs \<and> (xs@ys)!i = xs!i"
  by (auto simp add: no_back_def nth_append)

lemma no_back_backarc_j_in_ys:
  "\<lbrakk>no_back xs; j < length (xs@ys); i < j; (xs@ys)!j \<rightarrow>\<^bsub>T\<^esub> (xs@ys)!i\<rbrakk>
    \<Longrightarrow> ys!(j-length xs) \<in> set ys \<and> (xs@ys)!j = ys!(j-length xs)"
  by (auto simp add: no_back_def nth_append)

lemma no_back_backarc_difsets:
  assumes "no_back xs" and "no_back ys"
      and "i < j" and "j < length (xs @ ys)" and "(xs @ ys) ! j \<rightarrow>\<^bsub>T\<^esub> (xs @ ys) ! i"
    shows "\<exists>x \<in> set xs. \<exists>y \<in> set ys. y \<rightarrow>\<^bsub>T\<^esub> x"
  using no_back_backarc_i_in_xs[OF assms(2,4,3)] no_back_backarc_j_in_ys[OF assms(1,4,3)] assms(5)
  by auto

lemma no_back_backarc_difsets':
  "\<lbrakk>no_back xs; no_back ys; \<exists>i j. i < j \<and> j < length (xs@ys) \<and> (xs@ys)!j \<rightarrow>\<^bsub>T\<^esub> (xs@ys)!i\<rbrakk>
    \<Longrightarrow> \<exists>x \<in> set xs. \<exists>y \<in> set ys. y \<rightarrow>\<^bsub>T\<^esub> x"
  using no_back_backarc_difsets by blast

lemma no_back_before_aux:
  assumes "seq_conform xs" and "seq_conform ys"
      and "set xs \<inter> set ys = {}" and "(\<exists>x\<in>set xs. \<exists>y\<in>set ys. x \<rightarrow>\<^bsub>T\<^esub> y)"
    shows "no_back (xs @ ys)"
  unfolding no_back_def by (metis assms adj_in_verts(2) forward_arc_to_head hd_reach_all_forward
    inf_commute reachable1_not_reverse reachable_rtranclI rtrancl_into_trancl1 seq_conform_alt
    no_back_backarc_difsets')

lemma no_back_before: "before xs ys \<Longrightarrow> no_back (xs@ys)"
  using before_def no_back_before_aux by simp

lemma seq_conform_if_before: "before xs ys \<Longrightarrow> seq_conform (xs@ys)"
  using no_back_before before_def seq_conform_alt forward_app before_arc_to_hd by simp

lemma no_back_arc_if_fwd_dstct:
  assumes "forward (as@bs)" and "distinct (as@bs)"
  shows "\<not>(\<exists>x\<in>set bs. \<exists>y\<in>set as. x \<rightarrow>\<^bsub>T\<^esub> y)"
proof
  assume "\<exists>x\<in>set bs. \<exists>y\<in>set as. x \<rightarrow>\<^bsub>T\<^esub> y"
  then obtain x y where x_def: "x\<in>set bs" "y\<in>set as" "x \<rightarrow>\<^bsub>T\<^esub> y" by blast
  then obtain i where i_def: "as!i = y" "i < length as" by (auto simp: in_set_conv_nth)
  obtain j where j_def: "bs!j = x" "j < length bs" using x_def(1) by (auto simp: in_set_conv_nth)
  then have "(as@bs)!(j+length as) = x" by (simp add: nth_append)
  moreover have "(as@bs)!i = y" using i_def by (simp add: nth_append)
  moreover have "i < (j+length as)" using i_def(2) by simp
  moreover have "(j+length as) < length (as @ bs)" using j_def by simp
  ultimately show False
    using no_back_if_distinct_forward[OF assms] x_def(3) unfolding no_back_def by blast
qed

lemma no_back_reach1_if_fwd_dstct:
  assumes "forward (as@bs)" and "distinct (as@bs)"
  shows "\<not>(\<exists>x\<in>set bs. \<exists>y\<in>set as. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
proof
  assume "\<exists>x\<in>set bs. \<exists>y\<in>set as. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
  then obtain x y where x_def: "x\<in>set bs" "y\<in>set as" "x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y" by blast
  have fwd_as: "forward as" using forward_split[OF assms(1)] by blast
  have x_as: "x \<notin> set as" using x_def(1) assms(2) by auto
  show False
  using assms(1) x_def append.assoc list.distinct(1) Nil_is_append_conv append_Nil2[of "as@bs"]
      append_eq_append_conv2[of "as@bs" "as@bs" bs as] forward_arc_to_head' hd_append2
      hd_reach_all_forward hd_reachable1_from_outside'[OF x_def(3) fwd_as x_as x_def(2)]
      in_set_conv_decomp_first[of y as] in_set_conv_decomp_last reachable1_from_outside_dom
      reachable1_in_verts(2) reachable1_not_reverse reachable1_reachable_trans
  by metis
qed

lemma split_length_i: "i \<le> length bs \<Longrightarrow> \<exists>xs ys. xs@ys = bs \<and> length xs = i"
  using length_take append_take_drop_id min_absorb2 by metis

lemma split_length_i_prefix:
  assumes "length as \<le> i" "i < length (as@bs)"
  shows "\<exists>xs ys. xs@ys = bs \<and> length (as@xs) = i"
proof -
  obtain n where n_def: "n + length as = i"
    using assms(1) ab_semigroup_add_class.add.commute le_Suc_ex by blast
  then have "n \<le> length bs" using assms(2) by simp
  then show ?thesis using split_length_i n_def by fastforce
qed

lemma forward_alt_aux1:
  assumes "i \<in> {1..length xs - 1}" and "j<i" and "xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i"
  shows "\<exists>as bs. as@bs = xs \<and> length as = i \<and> (\<exists>x \<in> set as. x \<rightarrow>\<^bsub>T\<^esub> xs!i)"
proof -
  obtain as bs where "as@bs = xs \<and> length as = i"
    using assms(1) atLeastAtMost_iff diff_le_self le_trans split_length_i[of i xs] by metis
  then show ?thesis using assms(2,3) nth_append[of as bs j] by force
qed

lemma forward_alt_aux1':
  "forward xs
    \<Longrightarrow> \<forall>i \<in> {1..length xs - 1}. \<exists>as bs. as@bs = xs \<and> length as = i \<and> (\<exists>x \<in> set as. x \<rightarrow>\<^bsub>T\<^esub> xs!i)"
  using forward_alt_aux1 unfolding forward_def by fastforce

lemma forward_alt_aux2:
  "\<lbrakk>as@bs = xs; length as = i; \<exists>x \<in> set as. x \<rightarrow>\<^bsub>T\<^esub> xs!i\<rbrakk> \<Longrightarrow> \<exists>j<i. xs!j \<rightarrow>\<^bsub>T\<^esub> xs!i"
  by (auto simp add: nth_append in_set_conv_nth)

lemma forward_alt_aux2':
  "\<forall>i \<in> {1..length xs - 1}. \<exists>as bs. as@bs = xs \<and> length as = i \<and> (\<exists>x \<in> set as. x \<rightarrow>\<^bsub>T\<^esub> xs!i)
    \<Longrightarrow> forward xs"
  using forward_alt_aux2 unfolding forward_def by blast

corollary forward_alt:
  "\<forall>i \<in> {1..length xs - 1}. \<exists>as bs. as@bs = xs \<and> length as = i \<and> (\<exists>x \<in> set as. x \<rightarrow>\<^bsub>T\<^esub> xs!i)
    \<longleftrightarrow> forward xs"
  using forward_alt_aux1'[of xs] forward_alt_aux2' by blast

lemma move_mid_forward_if_noarc_aux:
  assumes "as \<noteq> []"
      and "\<not>(\<exists>x \<in> set U. \<exists>y \<in> set bs. x \<rightarrow>\<^bsub>T\<^esub> y)"
      and "forward (as@U@bs@cs)"
      and "i \<in> {1..length (as@bs@U@cs) - 1}"
    shows "\<exists>j<i. (as@bs@U@cs) ! j \<rightarrow>\<^bsub>T\<^esub> (as@bs@U@cs) ! i"
proof -
  have 0: "i \<in> {1..length (as@U@bs@cs) - 1}" using assms(4) by auto
  consider "i < length as" | "i \<in> {length as..length (as@bs) - 1}"
    | "i \<in> {length (as@bs)..length (as@bs@U) - 1}"
    | "i \<ge> length (as@bs@U)"
    by fastforce
  then show ?thesis
  proof(cases)
    case 1
    then have "(as@U@bs@cs)!i = (as@bs@U@cs)!i" by (simp add: nth_append)
    then obtain j where j_def: "j<i" "(as@U@bs@cs)!j \<rightarrow>\<^bsub>T\<^esub> ((as@bs)@U@cs)!i"
      using assms(3) 0 unfolding forward_def by fastforce
    then have "(as@U@bs@cs)!j = ((as@bs)@U@cs)!j" using 1 by (simp add: nth_append)
    then show ?thesis using j_def by auto
  next
    case 2
    have "((as@bs)@U@cs)!i = bs!(i - length as)"
      using 2 assms(4) nth_append root_in_T directed_tree_axioms in_degree_root_zero
      by (metis directed_tree.in_deg_one_imp_not_root atLeastAtMost_iff diff_diff_cancel
          diff_is_0_eq diff_le_self diff_less_mono neq0_conv zero_less_diff)
    then have i_in_bs: "((as@bs)@U@cs)!i \<in> set bs" using assms(4) 2 by auto
    have "(i - length as) < length bs" using 2 assms(4) by force
    then have "((as@bs)@U@cs)!i = (as@U@bs@cs)!(i + length U)"
      using 2 by (auto simp: nth_append)
    moreover have "(i + length U) \<in> {1.. length (as@U@bs@cs) - 1}" using 2 0 by force
    ultimately obtain j where j_def:
        "j < (i + length U)" "(as@U@bs@cs)!j \<rightarrow>\<^bsub>T\<^esub> ((as@bs)@U@cs)!i"
      using assms(3) unfolding forward_def by fastforce
    have "i < length (as@bs)" using \<open>i - length as < length bs\<close> by force
    moreover have "length as \<le> i" using 2 by simp
    ultimately obtain xs ys where xs_def: "bs = xs@ys" "length (as@xs) = i"
      using split_length_i_prefix by blast
    then have "j < (length (as@U@xs))" using 2 j_def(1) by simp
    then have "(as@U@bs@cs)!j \<in> set (as@U@xs)" by (auto simp: xs_def(1) nth_append)
    then have "(as@U@bs@cs)!j \<in> set (as@xs)" using assms(2) j_def(2) i_in_bs by auto
    then obtain j' where j'_def: "j' < length (as@xs)" "(as@xs)!j' = (as@U@bs@cs)!j"
      using in_set_conv_nth[of "(as@U@bs@cs)!j"] nth_append by blast
    then have "((as@bs)@U@cs)!j' = (as@U@bs@cs)!j"
      using nth_append[of "as@xs"] xs_def(1) by simp
    then show ?thesis using j_def(2) j'_def(1) xs_def(2) by force
  next
    case 3
    then have i_len_U: "i - length (as@bs) < length U" using assms(4) by fastforce
    have i_len_asU: "i - length bs < length (as@U)" using 3 assms(4) by force
    have "((as@bs)@U@cs)!i = (U@cs)!(i - length (as@bs))"
      using 3 by (auto simp: nth_append)
    also have "\<dots> = (as@U)!(i - length bs)"
      using 3 i_len_U by (auto simp: ab_semigroup_add_class.add.commute nth_append)
    also have "\<dots> = (as@U@bs@cs)!(i - length bs)"
      using i_len_asU nth_append[of "as@U"] by simp
    finally have 1: "((as@bs)@U@cs)!i = (as@U@bs@cs)!(i - length bs)" .
    have "(i - length bs) \<ge> length as" using 3 by auto
    then have "(i - length bs) \<ge> 1" using assms(1) length_0_conv[of as] by force
    then have "(i - length bs) \<in> {1.. length (as@U@bs@cs) - 1}" using 0 by auto
    then obtain j where j_def: "j < (i - length bs)" "(as@U@bs@cs)!j \<rightarrow>\<^bsub>T\<^esub> ((as@bs)@U@cs)!i"
      using assms(3) 1 unfolding forward_def by fastforce
    have "length as \<le> (i - length bs)" using 3 by auto
    then obtain xs ys where xs_def: "U = xs@ys" "length (as@xs) = (i - length bs)"
      using split_length_i_prefix[of as] i_len_asU by blast
    then have "j < (length (as@xs))" using 3 j_def(1) by simp
    then have "(as@U@bs@cs)!j \<in> set (as@bs@xs)" by (auto simp: xs_def(1) nth_append)
    then obtain j' where j'_def: "j' < length (as@bs@xs)" "(as@bs@xs)!j' = (as@U@bs@cs)!j"
      using in_set_conv_nth[of "(as@U@bs@cs)!j"] by blast
    then have "((as@bs)@U@cs)!j' = (as@U@bs@cs)!j"
      using nth_append[of "as@bs@xs"] xs_def(1) by simp
    moreover have "j' < i" using j'_def(1) xs_def(2) 3 by auto
    ultimately show ?thesis using j_def(2) by force
  next
    case 4
    have len_eq: "length (as@U@bs) = length (as@bs@U)" by simp
    have "((as@bs)@U@cs)!i = cs!(i - length (as@bs@U))"
      using 4 nth_append[of "as@bs@U"] by simp
    also have "\<dots> = cs!(i - length (as@U@bs))" using len_eq by argo
    finally have "((as@bs)@U@cs)!i = ((as@U@bs)@cs)!i" using 4 nth_append[of "as@U@bs"] by simp
    then obtain j where j_def: "j < i" "(as@U@bs@cs)!j \<rightarrow>\<^bsub>T\<^esub> ((as@bs)@U@cs)!i"
      using assms(3) 0 unfolding forward_def by fastforce
    have "length (as@U@bs) \<le> i" using 4 by auto
    moreover have "i < length ((as@U@bs)@cs)" using 0 by auto
    ultimately obtain xs ys where xs_def: "xs@ys = cs" "length ((as@U@bs) @ xs) = i"
      using split_length_i_prefix[of "as@U@bs" i] by blast
    then have "j < (length (as@U@bs@xs))" using 4 j_def(1) by simp
    then have "(as@U@bs@cs)!j \<in> set (as@bs@U@xs)" by (auto simp: xs_def(1)[symmetric] nth_append)
    then obtain j' where j'_def: "j' < length (as@bs@U@xs)" "(as@bs@U@xs)!j' = (as@U@bs@cs)!j"
      using in_set_conv_nth[of "(as@U@bs@cs)!j"] by blast
    then have "((as@bs)@U@cs)!j' = (as@U@bs@cs)!j"
      using nth_append[of "as@bs@U@xs"] xs_def(1)[symmetric] by simp
    moreover have "j' < i" using j'_def(1) xs_def(2) 4 by auto
    ultimately show ?thesis using j_def(2) by auto
  qed
qed

lemma move_mid_forward_if_noarc:
  "\<lbrakk>as \<noteq> []; \<not>(\<exists>x \<in> set U. \<exists>y \<in> set bs. x \<rightarrow>\<^bsub>T\<^esub> y); forward (as@U@bs@cs)\<rbrakk>
    \<Longrightarrow> forward (as@bs@U@cs)"
  using move_mid_forward_if_noarc_aux unfolding forward_def by blast

lemma move_mid_backward_if_noarc_aux:
  assumes "\<exists>x\<in>set U. x \<rightarrow>\<^bsub>T\<^esub> hd V"
      and "forward V"
      and "forward (as@U@bs@V@cs)"
      and "i \<in> {1..length (as@U@V@bs@cs) - 1}"
    shows "\<exists>j<i. (as@U@V@bs@cs) ! j \<rightarrow>\<^bsub>T\<^esub> (as@U@V@bs@cs) ! i"
proof -
  have 0: "i \<in> {1..length (as@U@bs@V@cs) - 1}" using assms(4) by auto
  consider "i < length (as@U)" | "i = length (as@U)" "i \<le> length (as@U@V) - 1"
    | "i \<in> {length (as@U) + 1..length (as@U@V) - 1}"
    | "i \<in> {length (as@U@V)..length (as@U@V@bs) - 1}"
    | "i \<ge> length (as@U@V@bs)"
    by fastforce
  then show ?thesis
  proof(cases)
    case 1
    then have "(as@U@bs@V@cs)!i = (as@U@V@bs@cs)!i" by (simp add: nth_append)
    then obtain j where j_def: "j<i" "(as@U@bs@V@cs)!j \<rightarrow>\<^bsub>T\<^esub> (as@U@V@bs@cs)!i"
      using assms(3) 0 unfolding forward_def by fastforce
    then have "(as@U@V@bs@cs)!j = (as@U@bs@V@cs)!j" using 1 by (simp add: nth_append)
    then show ?thesis using j_def by auto
  next
    case 2
    have "(as@U@V@bs@cs)!i = (V@bs@cs)!0" using 2(1) by (auto simp: nth_append)
    then have "(as@U@V@bs@cs)!i = hd V"
      using 2 assms(4) hd_append hd_conv_nth Suc_n_not_le_n atLeastAtMost_iff le_diff_conv2
      by (metis ab_semigroup_add_class.add.commute append.right_neutral Suc_eq_plus1_left)
    then obtain x where x_def: "x \<in> set U" "x \<rightarrow>\<^bsub>T\<^esub> (as@U@V@bs@cs)!i" using assms(1) by auto
    then obtain j where j_def: "(as@U)!j = x" "j < i" using in_set_conv_nth[of x] 2 by fastforce
    then have "(as@U@V@bs@cs)!j = x" using 2(1) by (auto simp: nth_append)
    then show ?thesis using j_def(2) x_def(2) by blast
  next
    case 3
    have "i - length (as@U) \<in> {1 .. length V - 1}" using 3 by force
    then obtain j where j_def: "j < (i - length (as@U))" "V!j \<rightarrow>\<^bsub>T\<^esub> V!(i - length (as@U))"
      using assms(2) unfolding forward_def by blast
    then have "(as@U@V@bs@cs)!(j+length (as@U)) = V!j"
      using 3 nth_append[of "as@U"] nth_append[of V] by auto
    moreover have "(as@U@V@bs@cs)!i = V!(i - length (as@U))"
      using 3 nth_append[of "as@U"] nth_append[of V] by auto
    moreover have "j+length (as@U) < i" using j_def(1) by simp
    ultimately show ?thesis using j_def(2) by auto
  next
    case 4
    have "(as@U@V@bs@cs)!i = (bs@cs)!(i - length (as@U@V))" using 4 nth_append[of "as@U@V"] by simp
    also have "\<dots> = bs!(i - length (as@U@V))" using 4 assms(4) by (auto simp: nth_append)
    also have "\<dots> = (as@U@bs)!(i - length (as@U@V) + length (as@U))" by (simp add: nth_append)
    also have "\<dots> = (as@U@bs)!(i - length V)" using 4 by simp
    finally have 1: "(as@U@V@bs@cs)!i = (as@U@bs@V@cs)!(i - length V)"
      using 4 assms(4) nth_append[of "as@U@bs"] by auto
    have "(i - length V) \<ge> length (as@U)" using 4 by auto
    then have "(i - length V) \<ge> 1" using assms(1) length_0_conv by fastforce
    then have "(i - length V) \<in> {1.. length (as@U@bs@V@cs) - 1}" using 0 by auto
    then obtain j where j_def: "j < i - length V" "(as@U@bs@V@cs)!j \<rightarrow>\<^bsub>T\<^esub> (as@U@V@bs@cs)!i"
      using assms(3) 1 unfolding forward_def by fastforce
    have "length (as@U) \<le> (i - length V)" using 4 by fastforce
    moreover have "(i - length V) < length ((as@U)@bs)" using 4 assms(4) by auto
    ultimately obtain xs ys where xs_def: "xs@ys = bs" "length ((as@U)@ xs) = i - length V"
      using split_length_i_prefix[of "as@U"] by blast
    then have "j < (length (as@U@xs))" using 4 j_def(1) by simp
    then have "(as@U@bs@V@cs)!j \<in> set (as@U@V@xs)" by (auto simp: xs_def(1)[symmetric] nth_append)
    then obtain j' where j'_def: "j' < length (as@U@V@xs)" "(as@U@V@xs)!j' = (as@U@bs@V@cs)!j"
      using in_set_conv_nth[of "(as@U@bs@V@cs)!j"] by blast
    then have "(as@U@V@bs@cs)!j' = (as@U@bs@V@cs)!j"
      using nth_append[of "as@U@V@xs"] xs_def(1) by auto
    moreover have "j' < i" using j'_def(1) xs_def(2) 4 by auto
    ultimately show ?thesis using j_def(2) by auto
  next
    case 5
    have len_eq: "length (as@U@bs@V) = length (as@U@V@bs)" by simp
    have "(as@U@V@bs@cs)!i = cs!(i - length (as@U@V@bs))"
      using 5 nth_append[of "as@U@V@bs"] by auto
    also have "\<dots> = cs!(i - length (as@U@bs@V))" using len_eq by argo
    finally have "(as@U@V@bs@cs)!i = ((as@U@bs@V)@cs)!i"
      using 5 nth_append[of "as@U@bs@V"] by simp
    then obtain j where j_def: "j < i" "(as@U@bs@V@cs)!j \<rightarrow>\<^bsub>T\<^esub> (as@U@V@bs@cs)!i"
      using assms(3) 0 unfolding forward_def by fastforce
    have "length (as@U@bs@V) \<le> i" using 5 by auto
    moreover have "i < length ((as@U@bs@V)@cs)" using 0 by auto
    ultimately obtain xs ys where xs_def: "xs@ys = cs" "length ((as@U@bs@V) @ xs) = i"
      using split_length_i_prefix[of "as@U@bs@V" i] by blast
    then have "j < (length (as@U@bs@V@xs))" using 5 j_def(1) by simp
    then have "(as@U@bs@V@cs)!j \<in> set (as@U@V@bs@xs)"
      by (auto simp: xs_def(1)[symmetric] nth_append)
    then obtain j' where j'_def: "j' < length (as@U@V@bs@xs)" "(as@U@V@bs@xs)!j' = (as@U@bs@V@cs)!j"
      using in_set_conv_nth[of "(as@U@bs@V@cs)!j"] by blast
    then have "(as@U@V@bs@cs)!j' = (as@U@bs@V@cs)!j"
      using nth_append[of "as@U@V@bs@xs"] xs_def(1) by force
    moreover have "j' < i" using j'_def(1) xs_def(2) 5 by auto
    ultimately show ?thesis using j_def(2) by auto
  qed
qed

lemma move_mid_backward_if_noarc:
  "\<lbrakk>before U V; forward (as@U@bs@V@cs)\<rbrakk> \<Longrightarrow> forward (as@U@V@bs@cs)"
  using before_forward2I
  by (simp add: forward_def before_arc_to_hd move_mid_backward_if_noarc_aux)

lemma move_mid_backward_if_noarc':
  "\<lbrakk>\<exists>x\<in>set U. \<exists>y\<in>set V. x \<rightarrow>\<^bsub>T\<^esub> y; forward V; set U \<inter> set V = {}; forward (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> forward (as@U@V@bs@cs)"
  using move_mid_backward_if_noarc_aux[of U V as bs cs] forward_arc_to_head[of V U] forward_def
  by blast

end

subsection \<open>Sublist Additions\<close>

lemma fst_sublist_if_not_snd_sublist:
  "\<lbrakk>xs@ys=A@B; \<not> sublist B ys\<rbrakk> \<Longrightarrow> \<exists>as bs. as @ bs = xs \<and> bs @ ys = B"
  by (metis suffix_append suffix_def suffix_imp_sublist)

lemma sublist_before_if_mid:
  assumes "sublist U (A@V)" and "A @ V @ B = xs" and "set U \<inter> set V = {}" and "U\<noteq>[]"
  shows "\<exists>as bs cs. as @ U @ bs @ V @ cs = xs"
proof -
  obtain C D where C_def: "(C @ U) @ D = A @ V" using assms(1) by (auto simp: sublist_def)
  have "sublist V D"
    using assms(3,4) fst_sublist_if_not_snd_sublist[OF C_def] disjoint_iff_not_equal last_appendR
    by (metis Int_iff Un_Int_eq(1) append_Nil2 append_self_conv2 set_append last_in_set sublist_def)
  then show ?thesis using assms(2) C_def sublist_def append.assoc by metis
qed

lemma list_empty_if_subset_dsjnt: "\<lbrakk>set xs \<subseteq> set ys; set xs \<inter> set ys = {}\<rbrakk> \<Longrightarrow> xs = []"
  using semilattice_inf_class.inf.orderE by fastforce

lemma empty_if_sublist_dsjnt: "\<lbrakk>sublist xs ys; set xs \<inter> set ys = {}\<rbrakk> \<Longrightarrow> xs = []"
  using set_mono_sublist list_empty_if_subset_dsjnt by fast

lemma sublist_snd_if_fst_dsjnt:
  assumes "sublist U (V@B)" and "set U \<inter> set V = {}"
  shows "sublist U B"
proof -
  consider "sublist U V" | "sublist U B" | "(\<exists>xs1 xs2. U = xs1@xs2 \<and> suffix xs1 V \<and> prefix xs2 B)"
    using assms(1) sublist_append by blast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using assms(2) empty_if_sublist_dsjnt by blast
  next
    case 2
    then show ?thesis by simp
  next
    case 3
    then obtain xs ys where xs_def: "U = xs@ys" "suffix xs V" "prefix ys B" by blast
    then have "set xs \<subseteq> set V" by (simp add: set_mono_suffix)
    then have "xs = []" using xs_def(1) assms(2) list_empty_if_subset_dsjnt by fastforce
    then show ?thesis using xs_def(1,3) by simp
  qed
qed

lemma sublist_fst_if_snd_dsjnt:
  assumes "sublist U (B@V)" and "set U \<inter> set V = {}"
  shows "sublist U B"
proof -
  consider "sublist U V" | "sublist U B" | "(\<exists>xs1 xs2. U = xs1@xs2 \<and> suffix xs1 B \<and> prefix xs2 V)"
    using assms(1) sublist_append by blast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using assms(2) empty_if_sublist_dsjnt by blast
  next
    case 2
    then show ?thesis by simp
  next
    case 3
    then obtain xs ys where xs_def: "U = xs@ys" "suffix xs B" "prefix ys V" by blast
    then have "set ys \<subseteq> set V" by (simp add: set_mono_prefix)
    then have "ys = []" using xs_def(1) assms(2) list_empty_if_subset_dsjnt by fastforce
    then show ?thesis using xs_def(1,2) by simp
  qed
qed

lemma sublist_app: "sublist (A @ B) C \<Longrightarrow> sublist A C \<and> sublist B C"
  using sublist_order.dual_order.trans by blast

lemma sublist_Cons: "sublist (A # B) C \<Longrightarrow> sublist [A] C \<and> sublist B C"
  using sublist_app[of "[A]"] by simp

lemma sublist_set_elem: "\<lbrakk>sublist xs (A@B); x \<in> set xs\<rbrakk> \<Longrightarrow> x \<in> set A \<or> x \<in> set B"
  using set_mono_sublist by fastforce

lemma subset_snd_if_hd_notin_fst:
  assumes "sublist ys (V @ B)" and "hd ys \<notin> set V" and "ys \<noteq> []"
  shows "set ys \<subseteq> set B"
proof -
  have "\<not> sublist ys V" using assms(2,3) by(auto simp: sublist_def)
  then consider "sublist ys B" | "(\<exists>xs1 xs2. ys = xs1@xs2 \<and> suffix xs1 V \<and> prefix xs2 B)"
    using assms(1) sublist_append by blast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using set_mono_sublist by blast
  next
    case 2
    then obtain xs zs where xs_def: "ys = xs@zs" "suffix xs V" "prefix zs B" by blast
    then have "set xs \<subseteq> set V" by (simp add: set_mono_suffix)
    then have "xs = []" using xs_def(1) assms(2,3) hd_append hd_in_set subsetD by fastforce
    then show ?thesis using xs_def(1,3) by (simp add: set_mono_prefix)
  qed
qed

lemma suffix_ndjsnt_snd_if_nempty: "\<lbrakk>suffix xs (A@V); V \<noteq> []; xs \<noteq> []\<rbrakk> \<Longrightarrow> set xs \<inter> set V \<noteq> {}"
  using empty_if_sublist_dsjnt disjoint_iff
  by (metis sublist_append_leftI suffix_append suffix_imp_sublist)

lemma sublist_not_mid:
  assumes "sublist U ((A @ V) @ B)" and "set U \<inter> set V = {}" and "V \<noteq> []"
  shows "sublist U A \<or> sublist U B"
proof -
  consider "sublist U A" | "sublist U V" | "(\<exists>xs1 xs2. U = xs1@xs2 \<and> suffix xs1 A \<and> prefix xs2 V)"
     | "sublist U B" | "(\<exists>xs1 xs2. U = xs1@xs2 \<and> suffix xs1 (A@V) \<and> prefix xs2 B)"
    using assms(1) sublist_append by metis
  then show ?thesis
  proof(cases)
    case 2
    then show ?thesis using assms(2) empty_if_sublist_dsjnt by blast
  next
    case 3
    then show ?thesis using assms(2) sublist_append sublist_fst_if_snd_dsjnt by blast
  next
    case 5
    then obtain xs ys where xs_def: "U = xs@ys" "suffix xs (A@V)" "prefix ys B" by blast
    then have "set xs \<inter> set V \<noteq> {} \<or> xs = []" using suffix_ndjsnt_snd_if_nempty assms(3) by blast
    then have "xs = []" using xs_def(1) assms(2) by auto
    then show ?thesis using xs_def(1,3) by simp
  qed(auto)
qed

lemma sublist_Y_cases_UV:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "U \<in> Y"
      and "V \<in> Y"
      and "U \<noteq> []"
      and "V \<noteq> []"
      and "(\<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs))"
      and "xs \<in> Y"
    shows "sublist xs as \<or> sublist xs bs \<or> sublist xs cs \<or> U = xs \<or> V = xs"
  using assms append_assoc sublist_not_mid by metis

lemma sublist_behind_if_nbefore:
  assumes "sublist U xs" "sublist V xs" "\<nexists>as bs cs. as @ U @ bs @ V @ cs = xs" "set U \<inter> set V = {}"
  shows "\<exists>as bs cs. as @ V @ bs @ U @ cs = xs"
proof -
  have "V \<noteq> []" using assms(1,3) unfolding sublist_def by blast
  obtain A B where A_def: "A @ V @ B = xs" using assms(2) by (auto simp: sublist_def)
  then have "\<not>sublist U A" unfolding sublist_def using assms(3) by fastforce
  moreover have "sublist U ((A @ V) @ B)" using assms(1) A_def by simp
  ultimately have "sublist U B" using assms(4) sublist_not_mid \<open>V\<noteq>[]\<close> by blast
  then show ?thesis unfolding sublist_def using A_def by blast
qed

lemma sublists_preserv_move_U:
  "\<lbrakk>set xs \<inter> set U = {}; set xs \<inter> set V = {}; V\<noteq>[]; sublist xs (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> sublist xs (as@bs@U@V@cs)"
  using append_assoc self_append_conv2 sublist_def sublist_not_mid by metis

lemma sublists_preserv_move_UY:
  "\<lbrakk>\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}; xs \<in> Y; U \<in> Y; V \<in> Y;
    V \<noteq> []; sublist xs (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> sublist xs (as@bs@U@V@cs)"
  using sublists_preserv_move_U append_assoc sublist_appendI by metis

lemma sublists_preserv_move_UY_all:
  "\<lbrakk>\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}; U \<in> Y; V \<in> Y;
    V \<noteq> []; \<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> \<forall>xs \<in> Y. sublist xs (as@bs@U@V@cs)"
  using sublists_preserv_move_UY[of Y] by simp

lemma sublists_preserv_move_V:
  "\<lbrakk>set xs \<inter> set U = {}; set xs \<inter> set V = {}; U\<noteq>[]; sublist xs (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> sublist xs (as@U@V@bs@cs)"
  using append_assoc self_append_conv2 sublist_def sublist_not_mid by metis

lemma sublists_preserv_move_VY:
  "\<lbrakk>\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}; xs \<in> Y; U \<in> Y; V \<in> Y;
    U \<noteq> []; sublist xs (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> sublist xs (as@U@V@bs@cs)"
  using sublists_preserv_move_V append_assoc sublist_appendI by metis

lemma sublists_preserv_move_VY_all:
  "\<lbrakk>\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}; U \<in> Y; V \<in> Y;
    U \<noteq> []; \<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs)\<rbrakk>
    \<Longrightarrow> \<forall>xs \<in> Y. sublist xs (as@U@V@bs@cs)"
  using sublists_preserv_move_VY[of Y] by simp

lemma distinct_sublist_first:
  "\<lbrakk>sublist as (x#xs); distinct (x#xs); x \<in> set as\<rbrakk> \<Longrightarrow> take (length as) (x#xs) = as"
  unfolding sublist_def using distinct_app_trans_l distinct_ys_not_xs hd_in_set
  by (metis list.sel(1) append_assoc append_eq_conv_conj append_self_conv2 hd_append2)

lemma distinct_sublist_first_remainder:
  "\<lbrakk>sublist as (x#xs); distinct (x#xs); x \<in> set as\<rbrakk> \<Longrightarrow> as @ drop (length as) (x#xs) = x#xs"
  using distinct_sublist_first append_take_drop_id[of "length as" "x#xs"] by fastforce

lemma distinct_set_diff: "distinct (xs@ys) \<Longrightarrow> set ys = set (xs@ys) - set xs"
  by auto

lemma list_of_sublist_concat_eq:
  assumes "\<forall>as \<in> Y. \<forall>bs \<in> Y. as = bs \<or> set as \<inter> set bs = {}"
      and "\<forall>as \<in> Y. sublist as xs"
      and "distinct xs"
      and "set xs = \<Union>(set ` Y)"
      and "finite Y"
    shows "\<exists>ys. set ys = Y \<and> concat ys = xs \<and> distinct ys"
using assms proof(induction "Finite_Set.card Y" arbitrary: Y xs)
  case (Suc n)
  show ?case
  proof(cases xs)
    case Nil
    then have "Y = {[]} \<or> Y = {}" using Suc.prems(4) by auto
    then have "set [[]] = Y \<and> concat [[]] = xs \<and> distinct [[]]" using Nil Suc.hyps(2) by auto
    then show ?thesis by blast
  next
    case (Cons x xs')
    then obtain as where as_def: "x \<in> set as" "as \<in> Y" using Suc.prems(4) by auto
    then have 0: "as @ (drop (length as) xs) = xs"
      using Suc.prems(2,3) distinct_sublist_first_remainder Cons by fast
    then have "\<forall>bs \<in> (Y - {as}). sublist bs (drop (length as) xs)"
      using Suc.prems(1,2) as_def(2) by (metis DiffE insertI1 sublist_snd_if_fst_dsjnt)
    moreover have "\<forall>cs \<in> (Y - {as}). \<forall>bs \<in> (Y - {as}). cs = bs \<or> set cs \<inter> set bs = {}"
      using Suc.prems(1) by simp
    moreover have "distinct (drop (length as) xs)" using Suc.prems(3) by simp
    moreover have "set (drop (length as) xs) = \<Union> (set ` (Y-{as}))"
      using Suc.prems(1,3,4) distinct_set_diff[of as "drop (length as) xs"] as_def(2) 0 by auto
    moreover have "n = Finite_Set.card (Y-{as})" using Suc.hyps(2) as_def(2) Suc.prems(5) by simp
    ultimately obtain ys where ys_def:
        "set ys = (Y-{as})" "concat ys = drop (length as) xs" "distinct ys"
      using Suc.hyps(1) Suc.prems(5) by blast
    then have "set (as#ys) = Y \<and> concat (as#ys) = xs \<and> distinct (as#ys)" using 0 as_def(2) by auto
    then show ?thesis by blast
  qed
qed(auto)

lemma extract_length_decr[termination_simp]:
  "List.extract P xs = Some (as,x,bs) \<Longrightarrow> length bs < length xs"
  by (simp add: extract_Some_iff)

fun separate_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "separate_P P acc xs = (case List.extract P xs of
      None \<Rightarrow> (acc,xs)
    | Some (as,x,bs) \<Rightarrow> (case separate_P P (x#acc) bs of (acc',xs') \<Rightarrow> (acc', as@xs')))"

lemma separate_not_P_snd: "separate_P P acc xs = (as,bs) \<Longrightarrow> \<forall>x \<in> set bs. \<not>P x"
proof(induction P acc xs arbitrary: as bs rule: separate_P.induct)
  case (1 P acc xs)
  then show ?case
  proof(cases "List.extract P xs")
    case None
    then have "bs = xs" using "1.prems" by simp
    then show ?thesis using None by (simp add: extract_None_iff)
  next
    case (Some a)
    then obtain cs x ds where x_def[simp]: "a = (cs,x,ds)" by(cases a) auto
    then obtain acc' xs' where acc'_def: "separate_P P (x#acc) ds = (acc',xs')" by fastforce
    then have "(acc', cs@xs') = (as,bs)" using "1.prems" Some by simp
    moreover have "\<forall>x \<in> set xs'. \<not>P x" using "1.IH" acc'_def Some x_def by blast
    ultimately show ?thesis using Some by (auto simp: extract_Some_iff)
  qed
qed

lemma separate_input_impl_none: "separate_P P acc xs = (acc,xs) \<Longrightarrow> List.extract P xs = None"
  using extract_None_iff separate_not_P_snd by fast

lemma separate_input_iff_none: "List.extract P xs = None \<longleftrightarrow> separate_P P acc xs = (acc,xs)"
  using separate_input_impl_none by auto

lemma separate_P_fst_acc:
  "separate_P P acc xs = (as,bs) \<Longrightarrow> \<exists>as'. as = as'@acc \<and> (\<forall>x \<in> set as'. P x)"
proof(induction P acc xs arbitrary: as bs rule: separate_P.induct)
  case (1 P acc xs)
  then show ?case
  proof(cases "List.extract P xs")
    case None
    then show ?thesis using "1.prems" by simp
  next
    case (Some a)
    then obtain cs x ds where x_def[simp]: "a = (cs,x,ds)" by(cases a) auto
    then obtain acc' xs' where acc'_def: "separate_P P (x#acc) ds = (acc',xs')" by fastforce
    then have "(acc', cs@xs') = (as,bs)" using "1.prems" Some by simp
    then have "\<exists>as'. as = as'@(x#acc) \<and> (\<forall>x \<in> set as'. P x)"
      using "1.IH" acc'_def Some x_def by blast
    then show ?thesis using Some by (auto simp: extract_Some_iff)
  qed
qed

lemma separate_P_fst: "separate_P P [] xs = (as,bs) \<Longrightarrow> \<forall>x \<in> set as. P x"
  using separate_P_fst_acc by fastforce

subsection \<open>Optimal Solution for Lists of Fixed Sets\<close>

lemma distinct_seteq_set_length_eq:
  "x \<in> {ys. set ys = xs \<and> distinct ys} \<Longrightarrow> length x = Finite_Set.card xs"
  using distinct_card by fastforce

lemma distinct_seteq_set_Cons:
  "\<lbrakk>Finite_Set.card xs = Suc n; x \<in> {ys. set ys = xs \<and> distinct ys}\<rbrakk>
    \<Longrightarrow> \<exists>y ys. y # ys = x \<and> length ys = n \<and> distinct ys \<and> finite (set ys)"
  using distinct_seteq_set_length_eq[of x] Suc_length_conv[of n x] by force

lemma distinct_seteq_set_Cons':
  "\<lbrakk>Finite_Set.card xs = Suc n; x \<in> {ys. set ys = xs \<and> distinct ys}\<rbrakk>
    \<Longrightarrow> \<exists>y ys zs. y # ys = x \<and> Finite_Set.card zs = n \<and> distinct ys \<and> set ys = zs"
  using distinct_seteq_set_length_eq[of x] Suc_length_conv[of n x] by force

lemma distinct_seteq_set_Cons'':
  "\<lbrakk>Finite_Set.card xs = Suc n; x \<in> {ys. set ys = xs \<and> distinct ys}\<rbrakk>
    \<Longrightarrow> \<exists>y ys zs. y # ys = x \<and> y \<in> xs
        \<and> set ys = zs \<and> Finite_Set.card zs = n \<and> distinct ys \<and> finite zs"
  using distinct_seteq_set_Cons by fastforce

lemma distinct_seteq_set_Cons_in_set:
  "\<lbrakk>Finite_Set.card xs = Suc n; x \<in> {ys. set ys = xs \<and> distinct ys}\<rbrakk>
    \<Longrightarrow> \<exists>y ys zs. y#ys = x \<and> y \<in> xs \<and> Finite_Set.card zs = n \<and> ys\<in>{ys. set ys = zs \<and> distinct ys}"
  using distinct_seteq_set_Cons'' by auto

lemma distinct_seteq_set_Cons_in_set':
  "\<lbrakk>Finite_Set.card xs = Suc n; x \<in> {ys. set ys = xs \<and> distinct ys}\<rbrakk>
    \<Longrightarrow> \<exists>y ys. x = y#ys \<and> y \<in> xs \<and> ys\<in>{ys. set ys = (xs - {y}) \<and> distinct ys}"
  using distinct_seteq_set_Cons'' by fastforce

lemma distinct_seteq_eq_set_union:
  "Finite_Set.card xs = Suc n
    \<Longrightarrow> {ys. set ys = xs \<and> distinct ys}
      = {y # ys |y ys. y \<in> xs \<and> ys \<in> {as. set as = (xs - {y}) \<and> distinct as}}"
  using distinct_seteq_set_Cons_in_set' by force

lemma distinct_seteq_sub_set_union:
  "Finite_Set.card xs = Suc n
    \<Longrightarrow> {ys. set ys = xs \<and> distinct ys}
      \<subseteq> {y # ys |y ys. y \<in> xs \<and> ys \<in> {as. \<exists>a \<in> xs. set as = (xs - {a}) \<and> distinct as}}"
  using distinct_seteq_set_Cons_in_set' by fast

lemma finite_set_union: "\<lbrakk>finite ys; \<forall>y \<in> ys. finite y\<rbrakk> \<Longrightarrow> finite (\<Union>y \<in> ys. y)"
  by simp

lemma Cons_set_eq_union_set:
  "{x # y | x y y'. x \<in> xs \<and> y \<in> y' \<and> y' \<in> ys} = {x # y | x y. x \<in> xs \<and> y \<in> (\<Union>y \<in> ys. y)}"
  by blast

lemma finite_set_Cons_union_finite:
  "\<lbrakk>finite xs; finite ys; \<forall>y \<in> ys. finite y\<rbrakk>
    \<Longrightarrow> finite {x # y | x y. x \<in> xs \<and> y \<in> (\<Union>y \<in> ys. y)}"
  by (simp add: finite_image_set2)

lemma finite_set_Cons_finite:
  "\<lbrakk>finite xs; finite ys; \<forall>y \<in> ys. finite y\<rbrakk>
    \<Longrightarrow> finite {x # y | x y y'. x \<in> xs \<and> y \<in> y' \<and> y' \<in> ys}"
  using Cons_set_eq_union_set[of xs] by (simp add: finite_image_set2)

lemma finite_set_Cons_finite':
  "\<lbrakk>finite xs; finite ys\<rbrakk> \<Longrightarrow> finite {x # y |x y. x \<in> xs \<and> y \<in> ys}"
  by (auto simp add: finite_image_set2)

lemma Cons_set_alt: "{x # y |x y. x \<in> xs \<and> y \<in> ys} = {zs. \<exists>x y. x # y = zs \<and> x \<in> xs \<and> y \<in> ys}"
  by blast

lemma Cons_set_sub:
  assumes "Finite_Set.card xs = Suc n"
  shows "{ys. set ys = xs \<and> distinct ys}
    \<subseteq> {x # y |x y. x \<in> xs \<and> y \<in> (\<Union>y \<in> xs. {as. set as = xs - {y} \<and> distinct as})}"
  using distinct_seteq_eq_set_union[OF assms] by auto

lemma distinct_seteq_finite: "finite xs \<Longrightarrow> finite {ys. set ys = xs \<and> distinct ys}"
proof(induction "Finite_Set.card xs" arbitrary: xs)
  case (Suc n)
  have "finite (\<Union>y \<in> xs. {as. set as = xs - {y} \<and> distinct as})" using Suc by simp
  then have "finite {x # y |x y. x \<in> xs \<and> y \<in> (\<Union>y \<in> xs. {as. set as = xs - {y} \<and> distinct as})}"
    using finite_set_Cons_finite'[OF Suc.prems] by blast
  then show ?case using finite_subset[OF Cons_set_sub] Suc.hyps(2)[symmetric] by blast
qed(simp)

lemma distinct_setsub_split:
  "{ys. set ys \<subseteq> xs \<and> distinct ys}
  = {ys. set ys = xs \<and> distinct ys} \<union> (\<Union>y \<in> xs. {ys. set ys \<subseteq> (xs-{y}) \<and> distinct ys})"
  by blast

lemma distinct_setsub_finite: "finite xs \<Longrightarrow> finite {ys. set ys \<subseteq> xs \<and> distinct ys}"
proof(induction "Finite_Set.card xs" arbitrary: xs)
  case (Suc x)
  then show ?case using distinct_seteq_finite distinct_setsub_split[of xs] by auto
qed(simp)

lemma valid_UV_lists_finite:
  "finite xs \<Longrightarrow> finite {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x}"
  using distinct_seteq_finite by force

lemma valid_UV_lists_r_subset:
  "{x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]}
  \<subseteq> {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x}"
  by blast

lemma valid_UV_lists_r_finite:
  "finite xs \<Longrightarrow> finite {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]}"
  using valid_UV_lists_finite finite_subset[OF valid_UV_lists_r_subset] by fast

lemma valid_UV_lists_arg_min_ex_aux:
  "\<lbrakk>finite ys; ys \<noteq> {}; ys = {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using arg_min_if_finite(1)[of ys f] arg_min_least[of ys, where ?f = f] by auto

lemma valid_UV_lists_arg_min_ex:
  "\<lbrakk>finite xs; ys \<noteq> {}; ys = {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using valid_UV_lists_finite valid_UV_lists_arg_min_ex_aux[of ys] by blast

lemma valid_UV_lists_arg_min_r_ex_aux:
  "\<lbrakk>finite ys; ys \<noteq> {};
    ys = {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using arg_min_if_finite(1)[of ys f] arg_min_least[of ys, where ?f = f] by auto

lemma valid_UV_lists_arg_min_r_ex:
  "\<lbrakk>finite xs; ys \<noteq> {};
    ys = {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using valid_UV_lists_r_finite[of xs] valid_UV_lists_arg_min_r_ex_aux[of ys] by blast

lemma valid_UV_lists_nemtpy:
  assumes "finite xs" "set (U@V) \<subseteq> xs" "distinct (U@V)"
  shows "{x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x} \<noteq> {}"
proof -
  obtain cs where "set cs = xs - set (U@V) \<and> distinct cs"
    using assms(1) finite_distinct_list[of "xs - set (U@V)"] by blast
  then have "[]@U@[]@V@cs = U@V@cs" "set (U@V@cs) = xs" "distinct (U@V@cs)" using assms by auto
  then show ?thesis by blast
qed

lemma valid_UV_lists_nemtpy':
  "\<lbrakk>finite xs; set U \<inter> set V = {}; set U \<subseteq> xs; set V \<subseteq> xs; distinct U; distinct V\<rbrakk>
    \<Longrightarrow> {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x} \<noteq> {}"
  using valid_UV_lists_nemtpy[of xs] by simp

lemma valid_UV_lists_nemtpy_r:
  assumes "finite xs" and "set (U@V) \<subseteq> xs" and "distinct (U@V)"
      and "take 1 U = [r] \<or> r \<notin> set U \<union> set V" and "r \<in> xs"
  shows "{x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]} \<noteq> {}"
proof(cases "take 1 U = [r]")
  case True
  obtain cs where "set cs = xs - set (U@V) \<and> distinct cs"
    using assms(1) finite_distinct_list by auto
  then have "[]@U@[]@V@cs = U@V@cs" "set (U@V@cs) = xs" "distinct (U@V@cs)" using assms by auto
  then show ?thesis using True take1_singleton_app by fast
next
  case False
  obtain cs where cs_def: "set cs = xs - ({r} \<union> set (U@V)) \<and> distinct cs"
    using assms(1) finite_distinct_list by auto
  then have "[r]@U@[]@V@cs = [r]@U@V@cs" "set ([r]@U@V@cs) = xs" "distinct ([r]@U@V@cs)"
      "take 1 ([r]@U@V@cs) = [r]"
    using assms False by auto
  then show ?thesis by (smt (verit, del_insts) empty_Collect_eq)
qed

lemma valid_UV_lists_nemtpy_r':
  "\<lbrakk>finite xs; set U \<inter> set V = {}; set U \<subseteq> xs; set V \<subseteq> xs; distinct U; distinct V;
    take 1 U = [r] \<or> r \<notin> set U \<union> set V; r \<in> xs\<rbrakk>
    \<Longrightarrow> {x. \<exists>as bs cs. as@U@bs@V@cs = x \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]} \<noteq> {}"
  using valid_UV_lists_nemtpy_r[of xs] by simp

lemma valid_UV_lists_arg_min_ex':
  "\<lbrakk>finite xs; set U \<inter> set V = {}; set U \<subseteq> xs; set V \<subseteq> xs; distinct U; distinct V;
    ys = {x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using valid_UV_lists_arg_min_ex[of xs] valid_UV_lists_nemtpy'[of xs] by simp

lemma valid_UV_lists_arg_min_r_ex':
  "\<lbrakk>finite xs; set U \<inter> set V = {}; set U \<subseteq> xs; set V \<subseteq> xs; distinct U; distinct V;
    take 1 U = [r] \<or> r \<notin> set U \<union> set V; r \<in> xs;
    ys = {x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x \<and> take 1 x = [r]}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using valid_UV_lists_arg_min_r_ex[of xs] valid_UV_lists_nemtpy_r'[of xs] by simp

lemma valid_UV_lists_alt:
  assumes "P = (\<lambda>x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x)"
  shows "{x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x} = {ys. P ys}"
  using assms by simp

lemma valid_UV_lists_argmin_ex:
  fixes cost :: "'a list \<Rightarrow> real"
  assumes "P = (\<lambda>x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x)"
      and "finite xs"
      and "set U \<inter> set V = {}"
      and "set U \<subseteq> xs"
      and "set V \<subseteq> xs"
      and "distinct U"
      and "distinct V"
    shows "\<exists>as' bs' cs'. P (as'@U@bs'@V@cs') \<and>
      (\<forall>as bs cs. P (as@U@bs@V@cs) \<longrightarrow> cost (as'@U@bs'@V@cs') \<le> cost (as@U@bs@V@cs))"
proof -
  obtain y where "y \<in> {ys. P ys} \<and> (\<forall>z \<in> {ys. P ys}. cost y \<le> cost z)"
    using valid_UV_lists_arg_min_ex'[OF assms(2-7)] assms(1) by fastforce
  then show ?thesis using assms(1) by blast
qed

lemma valid_UV_lists_argmin_ex_noP:
  fixes cost :: "'a list \<Rightarrow> real"
  assumes "finite xs"
      and "set U \<inter> set V = {}"
      and "set U \<subseteq> xs"
      and "set V \<subseteq> xs"
      and "distinct U"
      and "distinct V"
    shows "\<exists>as' bs' cs'. set (as' @ U @ bs' @ V @ cs') = xs \<and> distinct (as' @ U @ bs' @ V @ cs')
    \<and> (\<forall>as bs cs. set (as @ U @ bs @ V @ cs) = xs \<and> distinct (as @ U @ bs @ V @ cs)
        \<longrightarrow> cost (as' @ U @ bs' @ V @ cs') \<le> cost (as @ U @ bs @ V @ cs))"
    using valid_UV_lists_argmin_ex[OF refl assms] by metis

lemma valid_UV_lists_argmin_r_ex:
  fixes cost :: "'a list \<Rightarrow> real"
  assumes "P = (\<lambda>x. (\<exists>as bs cs. as@U@bs@V@cs = x) \<and> set x = xs \<and> distinct x \<and> take 1 x = [r])"
      and "finite xs"
      and "set U \<inter> set V = {}"
      and "set U \<subseteq> xs"
      and "set V \<subseteq> xs"
      and "distinct U"
      and "distinct V"
      and "take 1 U = [r] \<or> r \<notin> set U \<union> set V"
      and "r \<in> xs"
    shows "\<exists>as' bs' cs'. P (as'@U@bs'@V@cs') \<and>
      (\<forall>as bs cs. P (as@U@bs@V@cs) \<longrightarrow> cost (as'@U@bs'@V@cs') \<le> cost (as@U@bs@V@cs))"
proof -
  obtain y where "y \<in> {ys. P ys} \<and> (\<forall>z \<in> {ys. P ys}. cost y \<le> cost z)"
    using valid_UV_lists_arg_min_r_ex'[OF assms(2-9)] assms(1) by fastforce
  then show ?thesis using assms(1) by blast
qed

lemma valid_UV_lists_argmin_r_ex_noP:
  fixes cost :: "'a list \<Rightarrow> real"
  assumes "finite xs"
      and "set U \<inter> set V = {}"
      and "set U \<subseteq> xs"
      and "set V \<subseteq> xs"
      and "distinct U"
      and "distinct V"
      and "take 1 U = [r] \<or> r \<notin> set U \<union> set V"
      and "r \<in> xs"
    shows "\<exists>as' bs' cs'. set (as' @ U @ bs' @ V @ cs') = xs
    \<and> distinct (as' @ U @ bs' @ V @ cs') \<and> take 1 (as' @ U @ bs' @ V @ cs') = [r]
    \<and> (\<forall>as bs cs. set (as @ U @ bs @ V @ cs) = xs
      \<and> distinct (as @ U @ bs @ V @ cs) \<and> take 1 (as @ U @ bs @ V @ cs) = [r]
        \<longrightarrow> cost (as' @ U @ bs' @ V @ cs') \<le> cost (as @ U @ bs @ V @ cs))"
  using valid_UV_lists_argmin_r_ex[OF refl assms] by metis

lemma valid_UV_lists_argmin_r_ex_noP':
  fixes cost :: "'a list \<Rightarrow> real"
  assumes "finite xs"
      and "set U \<inter> set V = {}"
      and "set U \<subseteq> xs"
      and "set V \<subseteq> xs"
      and "distinct U"
      and "distinct V"
      and "take 1 U = [r] \<or> r \<notin> set U \<union> set V"
      and "r \<in> xs"
    shows "\<exists>as' bs' cs'. set (as' @ U @ bs' @ V @ cs') = xs
    \<and> distinct (as' @ U @ bs' @ V @ cs') \<and> take 1 (as' @ U @ bs' @ V @ cs') = [r]
    \<and> (\<forall>as bs cs. set (as @ U @ bs @ V @ cs) = xs
      \<and> distinct (as @ U @ bs @ V @ cs) \<and> take 1 (as @ U @ bs @ V @ cs) = [r]
        \<longrightarrow> cost (rev (as' @ U @ bs' @ V @ cs')) \<le> cost (rev (as @ U @ bs @ V @ cs)))"
  using valid_UV_lists_argmin_r_ex_noP[OF assms] by meson

lemma take1_split_nempty: "ys \<noteq> [] \<Longrightarrow> take 1 (xs@ys@zs) = take 1 (xs@ys)"
  by (metis append.assoc append_Nil2 gr_zeroI length_0_conv less_one same_append_eq
      take_append take_eq_Nil zero_less_diff)

lemma take1_elem: "\<lbrakk>take 1 (xs@ys) = [r]; r \<in> set xs\<rbrakk> \<Longrightarrow> take 1 xs = [r]"
  using in_set_conv_decomp_last[of r xs] by auto

lemma take1_nelem: "\<lbrakk>take 1 (xs@ys) = [r]; r \<notin> set ys\<rbrakk> \<Longrightarrow> take 1 xs = [r]"
  using take1_elem[of xs ys r] append_self_conv2[of xs] hd_in_set[of ys]
  by (fastforce dest: hd_eq_take1)

lemma take1_split_nelem_nempty: "\<lbrakk>take 1 (xs@ys@zs) = [r]; ys \<noteq> []; r \<notin> set ys\<rbrakk> \<Longrightarrow> take 1 xs = [r]"
  using take1_split_nempty take1_nelem by fastforce

lemma take1_empty_if_nelem: "\<lbrakk>take 1 (as@bs@cs) = [r]; r \<notin> set as\<rbrakk> \<Longrightarrow> as = []"
  using take1_split_nelem_nempty[of "[]" as "bs@cs"] by auto

lemma take1_empty_if_mid: "\<lbrakk>take 1 (as@bs@cs) = [r]; r \<in> set bs; distinct (as@bs@cs)\<rbrakk> \<Longrightarrow> as = []"
  using take1_empty_if_nelem by fastforce

lemma take1_mid_if_elem:
  "\<lbrakk>take 1 (as@bs@cs) = [r]; r \<in> set bs; distinct (as@bs@cs)\<rbrakk> \<Longrightarrow> take 1 bs = [r]"
  using take1_empty_if_mid[of as bs cs] by (fastforce intro: take1_elem)

lemma contr_optimal_nogap_no_r:
  assumes "asi rank r cost"
      and "rank (rev V) \<le> rank (rev U)"
      and "finite xs"
      and "set U \<inter> set V = {}"
      and "set U \<subseteq> xs"
      and "set V \<subseteq> xs"
      and "distinct U"
      and "distinct V"
      and "r \<notin> set U \<union> set V"
      and "r \<in> xs"
    shows "\<exists>as' cs'. distinct (as' @ U @ V @ cs') \<and> take 1 (as' @ U @ V @ cs') = [r]
      \<and> set (as' @ U @ V @ cs') = xs \<and> (\<forall>as bs cs. set (as @ U @ bs @ V @ cs) = xs
        \<and> distinct (as @ U @ bs @ V @ cs) \<and> take 1 (as @ U @ bs @ V @ cs) = [r]
          \<longrightarrow> cost (rev (as' @ U @ V @ cs')) \<le> cost (rev (as @ U @ bs @ V @ cs)))"
proof -
  define P where "P ys \<equiv> set ys = xs \<and> distinct ys \<and> take 1 ys = [r]" for ys
  obtain as' bs' cs' where bs'_def:
    "set (as'@U@bs'@V@cs') = xs" "distinct (as'@U@bs'@V@cs')" "take 1 (as'@U@bs'@V@cs') = [r]"
    "\<forall>as bs cs. P (as @ U @ bs @ V @ cs) \<longrightarrow>
         cost (rev (as' @ U @ bs' @ V @ cs')) \<le> cost (rev (as @ U @ bs @ V @ cs))"
    using valid_UV_lists_argmin_r_ex_noP'[OF assms(3-8)] assms(9,10) unfolding P_def by blast
  then consider "U = []" | "V = [] \<or> bs' = []"
    | "rank (rev bs') \<le> rank (rev U)" "U \<noteq> []" "bs' \<noteq> []"
    | "rank (rev U) \<le> rank (rev bs')" "U \<noteq> []" "V \<noteq> []" "bs' \<noteq> []"
    by fastforce
  then show ?thesis
  proof(cases)
    case 1
    then have "\<forall>as bs cs. P (as @ U @ bs @ V @ cs) \<longrightarrow>
         cost (rev ((as'@bs')@U@V@cs')) \<le> cost (rev (as @ U @ bs @ V @ cs))"
      using bs'_def(4) by simp
    moreover have "set ((as'@bs')@U@V@cs') = xs" using bs'_def(1) by auto
    moreover have "distinct ((as'@bs')@U@V@cs')" using bs'_def(2) by auto
    moreover have "take 1 ((as'@bs')@U@V@cs') = [r]" using bs'_def(3) 1 by auto
    ultimately show ?thesis unfolding P_def by blast
  next
    case 2
    then have "\<forall>as bs cs. P (as @ U @ bs @ V @ cs) \<longrightarrow>
         cost (rev (as'@U@V@bs'@cs')) \<le> cost (rev (as @ U @ bs @ V @ cs))" using bs'_def(4) by auto
    moreover have "set (as'@U@V@bs'@cs') = xs" using bs'_def(1) by auto
    moreover have "distinct (as'@U@V@bs'@cs')" using bs'_def(2) by auto
    moreover have "take 1 (as'@U@V@bs'@cs') = [r]" using bs'_def(3) 2 by auto
    ultimately show ?thesis unfolding P_def by blast
  next
    case 3
    have 0: "distinct (as'@bs'@U@V@cs')" using bs'_def(2) by auto
    have 1: "take 1 (as'@bs'@U@V@cs') = [r]"
      using bs'_def(3) assms(9) 3(2) take1_split_nelem_nempty[of as' U "bs'@V@cs'"] by simp
    then have "cost (rev (as'@bs'@U@V@cs')) \<le> cost (rev (as'@U@bs'@V@cs'))"
      using asi_le_rfst[OF assms(1) 3(1,3,2) 0] bs'_def(3) by blast
    then have "\<forall>as bs cs. P (as @ U @ bs @ V @ cs) \<longrightarrow>
         cost (rev ((as'@bs')@U@V@cs')) \<le> cost (rev (as @ U @ bs @ V @ cs))"
      using bs'_def(4) by fastforce
    moreover have "set ((as'@bs')@U@V@cs') = xs" using bs'_def(1) by auto
    moreover have "distinct ((as'@bs')@U@V@cs')" using 0 by simp
    moreover have "take 1 ((as'@bs')@U@V@cs') = [r]" using 1 by simp
    ultimately show ?thesis using P_def by blast
  next
    case 4
    then have 3: "rank (rev V) \<le> rank (rev bs')" using assms(2) by simp
    have 0: "distinct ((as'@U)@V@bs'@cs')" using bs'_def(2) by auto
    have 1: "take 1 (as'@U@V@bs'@cs') = [r]"
      using bs'_def(3) assms(9) 4(2) take1_split_nelem_nempty[of as' U "bs'@V@cs'"] by simp
    then have "cost (rev (as'@U@V@bs'@cs')) \<le> cost (rev ((as'@U)@bs'@V@cs'))"
      using asi_le_rfst[OF assms(1) 3 4(3,4) 0] bs'_def(3) by simp
    then have "\<forall>as bs cs. P (as @ U @ bs @ V @ cs) \<longrightarrow>
         cost (rev (as'@U@V@bs'@cs')) \<le> cost (rev (as @ U @ bs @ V @ cs))"
      using bs'_def(4) by fastforce
    moreover have "set (as'@U@V@bs'@cs') = xs" using bs'_def(1) by auto
    moreover have "distinct (as'@U@V@bs'@cs')" using 0 by simp
    ultimately show ?thesis using P_def 1 by blast
  qed
qed

fun combine_lists_P :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "combine_lists_P _ y [] = [y]"
| "combine_lists_P P y (x#xs) = (if P (x@y) then combine_lists_P P (x@y) xs else (x@y)#xs)"

fun make_list_P :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "make_list_P P acc xs = (case List.extract P xs of
      None \<Rightarrow> rev acc @ xs
    | Some (as,y,bs) \<Rightarrow> make_list_P P (combine_lists_P P y (rev as @ acc)) bs)"

lemma combine_lists_concat_rev_eq: "concat (rev (combine_lists_P P y xs)) = concat (rev xs) @ y"
  by (induction P y xs rule: combine_lists_P.induct) auto

lemma make_list_concat_rev_eq: "concat (make_list_P P acc xs) = concat (rev acc) @ concat xs"
proof(induction P acc xs rule: make_list_P.induct)
  case (1 P acc xs)
  then show ?case
  proof(cases "List.extract P xs")
    case (Some a)
    then obtain as x bs where x_def[simp]: "a = (as,x,bs)" by(cases a) auto
    then have "concat (make_list_P P acc xs)
      = concat (rev (combine_lists_P P x (rev as @ acc))) @ concat bs"
      using 1 Some by simp
    also have "\<dots> = concat (rev acc) @ concat (as@x#bs)"
      using combine_lists_concat_rev_eq[of P] by simp
    finally show ?thesis using Some extract_SomeE by force
  qed(simp)
qed

lemma combine_lists_sublists:
  "\<exists>x \<in> {y} \<union> set xs. sublist as x \<Longrightarrow> \<exists>x \<in> set (combine_lists_P P y xs). sublist as x"
proof (induction P y xs rule: combine_lists_P.induct)
  case (2 P y x xs)
  then show ?case
  proof(cases "sublist as x \<or> sublist as y")
    case True
    then have "sublist as (x@y)" using sublist_order.dual_order.trans by blast
    then show ?thesis using 2 by force
  next
    case False
    then show ?thesis using 2 by simp
  qed
qed(simp)

lemma make_list_sublists:
  "\<exists>x \<in> set acc \<union> set xs. sublist cs x \<Longrightarrow> \<exists>x \<in> set (make_list_P P acc xs). sublist cs x"
proof(induction P acc xs rule: make_list_P.induct)
  case (1 P acc xs)
  then show ?case
  proof(cases "List.extract P xs")
    case (Some a)
    then obtain as x bs where x_def[simp]: "a = (as,x,bs)" by(cases a) auto
    then have "make_list_P P acc xs = make_list_P P (combine_lists_P P x (rev as @ acc)) bs"
      using Some by simp
    then have "\<exists>a \<in> set (combine_lists_P P x (rev as @ acc)) \<union> set bs. sublist cs a"
      using Some combine_lists_sublists[of x "rev as @ acc" cs] "1.prems"
      by (auto simp: extract_Some_iff)
    then show ?thesis using 1 Some by simp
  qed(simp)
qed

lemma combine_lists_nempty: "\<lbrakk>[] \<notin> set xs; y \<noteq> []\<rbrakk> \<Longrightarrow> [] \<notin> set (combine_lists_P P y xs)"
  by (induction P y xs rule: combine_lists_P.induct) auto

lemma make_list_nempty:
  "\<lbrakk>[] \<notin> set acc; [] \<notin> set xs\<rbrakk> \<Longrightarrow> [] \<notin> set (make_list_P P acc xs)"
proof (induction P acc xs rule: make_list_P.induct)
  case (1 P acc xs)
  show ?case
  proof(cases "List.extract P xs")
    case None
    then show ?thesis using 1 by simp
  next
    case (Some a)
    then show ?thesis using 1 by (auto simp: extract_Some_iff combine_lists_nempty)
  qed
qed

lemma combine_lists_notP:
  "\<forall>x\<in>set xs. \<not>P x \<Longrightarrow> (\<exists>x. combine_lists_P P y xs = [x]) \<or> (\<forall>x\<in>set (combine_lists_P P y xs). \<not>P x)"
  by (induction P y xs rule: combine_lists_P.induct) auto

lemma combine_lists_single: "xs = [x] \<Longrightarrow> combine_lists_P P y xs = [x@y]"
  by auto

lemma combine_lists_lastP:
  "P (last xs) \<Longrightarrow> (\<exists>x. combine_lists_P P y xs = [x]) \<or> (P (last (combine_lists_P P y xs)))"
  by (induction P y xs rule: combine_lists_P.induct) auto

lemma make_list_notP:
  "\<lbrakk>(\<forall>x \<in> set acc. \<not>P x) \<or> P (last acc)\<rbrakk>
    \<Longrightarrow> (\<forall>x\<in>set (make_list_P P acc xs). \<not>P x) \<or> (\<exists>y ys. make_list_P P acc xs = y # ys \<and> P y)"
proof(induction P acc xs rule: make_list_P.induct)
  case (1 P acc xs)
  then show ?case
  proof(cases "List.extract P xs")
    case None
    then show ?thesis
    proof(cases "\<forall>x \<in> set acc. \<not>P x")
      case True
      from None have "\<forall>x \<in> set xs. \<not> P x" by (simp add: extract_None_iff)
      then show ?thesis using True "1.prems" None by auto
    next
      case False
      then have "acc \<noteq> []" by auto
      then have "make_list_P P acc xs = last acc # rev (butlast acc) @ xs" using None by simp
      then show ?thesis using False "1.prems" by blast
    qed
  next
    case (Some a)
    then obtain as x bs where x_def[simp]: "a = (as,x,bs)" by(cases a) auto
    show ?thesis
    proof(cases "\<forall>x \<in> set acc. \<not>P x")
      case True
      then have "\<forall>x \<in> set (rev as @ acc). \<not>P x" using Some by (auto simp: extract_Some_iff)
      then have "(\<forall>x\<in>set (combine_lists_P P x (rev as @ acc)). \<not> P x)
                \<or> P (last (combine_lists_P P x (rev as @ acc)))"
        using combine_lists_notP[of "rev as @ acc" P] by force
      then show ?thesis using "1.IH" Some by simp
    next
      case False
      then have "P (last acc) \<and> acc \<noteq> []" using "1.prems" by auto
      then have "P (last (rev as @ acc))" using "1.prems" by simp
      then have "(\<forall>x\<in>set (combine_lists_P P x (rev as @ acc)). \<not> P x)
                \<or> P (last (combine_lists_P P x (rev as @ acc)))"
        using combine_lists_lastP[of P] by force
      then show ?thesis using "1.IH" Some by simp
    qed
  qed
qed

corollary make_list_notP_empty_acc:
  "(\<forall>x\<in>set (make_list_P P [] xs). \<not>P x) \<or> (\<exists>y ys. make_list_P P [] xs = y # ys \<and> P y)"
  using make_list_notP[of "[]"] by auto

definition unique_set_r :: "'a \<Rightarrow> 'a list set \<Rightarrow> 'a list \<Rightarrow> bool" where
 "unique_set_r r Y ys \<longleftrightarrow> set ys = \<Union>(set ` Y) \<and> distinct ys \<and> take 1 ys = [r]"

context directed_tree
begin

definition fwd_sub :: "'a \<Rightarrow> 'a list set \<Rightarrow> 'a list \<Rightarrow> bool" where
 "fwd_sub r Y ys \<longleftrightarrow> unique_set_r r Y ys \<and> forward ys \<and> (\<forall>xs \<in> Y. sublist xs ys)"

lemma distinct_mid_unique1: "\<lbrakk>distinct (xs@U@ys); U\<noteq>[]; xs@U@ys = as@U@bs\<rbrakk> \<Longrightarrow> as = xs"
  using distinct_app_trans_r distinct_ys_not_xs[of xs "U@ys"] hd_append2[of U] append_is_Nil_conv[of U]
  by (metis append_Cons_eq_iff distinct.simps(2) list.exhaust_sel list.set_sel(1))

lemma distinct_mid_unique2: "\<lbrakk>distinct (xs@U@ys); U\<noteq>[]; xs@U@ys = as@U@bs\<rbrakk> \<Longrightarrow> ys = bs"
  using distinct_mid_unique1 by blast

lemma concat_all_sublist: "\<forall>x \<in> set xs. sublist x (concat xs)"
  using split_list by force

lemma concat_all_sublist_rev: "\<forall>x \<in> set xs. sublist x (concat (rev xs))"
  using split_list by force

lemma concat_all_sublist1:
  assumes "distinct (as@U@bs)"
      and "concat cs @ U @ concat ds = as@U@bs"
      and "U \<noteq> []"
      and "set (cs@U#ds) = Y"
    shows "\<exists>X. X \<subseteq> Y \<and> set as = \<Union>(set ` X) \<and> (\<forall>xs \<in> X. sublist xs as)"
proof -
  have eq: "concat cs = as"
    using distinct_mid_unique1[of "concat cs" U "concat ds"] assms(1-3) by simp
  then have "\<forall>xs \<in> set cs. sublist xs as" using concat_all_sublist by blast
  then show ?thesis using eq assms(4) by fastforce
qed

lemma concat_all_sublist2:
  assumes "distinct (as@U@bs)"
      and "concat cs @ U @ concat ds = as@U@bs"
      and "U \<noteq> []"
      and "set (cs@U#ds) = Y"
    shows "\<exists>X. X \<subseteq> Y \<and> set bs = \<Union>(set ` X) \<and> (\<forall>xs \<in> X. sublist xs bs)"
proof -
  have eq: "concat ds = bs"
    using distinct_mid_unique1[of "concat cs" U "concat ds"] assms(1-3) by simp
  then have "\<forall>xs \<in> set ds. sublist xs bs" using concat_all_sublist by blast
  then show ?thesis using eq assms(4) by fastforce
qed

lemma concat_split_mid:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "finite Y"
      and "U \<in> Y"
      and "distinct (as@U@bs)"
      and "set (as@U@bs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs)"
      and "U \<noteq> []"
    shows "\<exists>cs ds. concat cs = as \<and> concat ds = bs \<and> set (cs@U#ds) = Y \<and> distinct (cs@U#ds)"
proof -
  obtain ys where ys_def: "set ys = Y" "concat ys = as@U@bs" "distinct ys"
    using list_of_sublist_concat_eq[OF assms(1,6,4,5,2)] by blast
  then obtain cs ds where cs_def: "cs@U#ds = ys"
    using assms(3) in_set_conv_decomp_first[of U ys] by blast
  then have "List.extract ((=) U) ys = Some (cs,U,ds)"
    using extract_Some_iff[of "(=) U"] ys_def(3) by auto
  then have "concat cs @ U @ concat ds = as@U@bs" using ys_def(2) cs_def by auto
  then have "concat cs = as \<and> concat ds = bs"
    using distinct_mid_unique1[of "concat cs" U] assms(4,7) by auto
  then show ?thesis using ys_def(1,3) cs_def by blast
qed

lemma mid_all_sublists_set1:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "finite Y"
      and "U \<in> Y"
      and "distinct (as@U@bs)"
      and "set (as@U@bs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs)"
      and "U \<noteq> []"
    shows "\<exists>X. X \<subseteq> Y \<and> set as = \<Union>(set ` X) \<and> (\<forall>xs \<in> X. sublist xs as)"
proof -
  obtain ys where ys_def: "set ys = Y" "concat ys = as@U@bs" "distinct ys"
    using list_of_sublist_concat_eq[OF assms(1,6,4,5,2)] by blast
  then obtain cs ds where cs_def: "cs@U#ds = ys"
    using assms(3) in_set_conv_decomp_first[of U ys] by blast
  then have "List.extract ((=) U) ys = Some (cs,U,ds)"
    using extract_Some_iff[of "(=) U"] ys_def(3) by auto
  then have "concat cs @ U @ concat ds = as@U@bs" using ys_def(2) cs_def by auto
  then show ?thesis using cs_def ys_def(1) concat_all_sublist1[OF assms(4)] assms(7) by force
qed

lemma mid_all_sublists_set2:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "finite Y"
      and "U \<in> Y"
      and "distinct (as@U@bs)"
      and "set (as@U@bs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs)"
      and "U \<noteq> []"
    shows "\<exists>X. X \<subseteq> Y \<and> set bs = \<Union>(set ` X) \<and> (\<forall>xs \<in> X. sublist xs bs)"
proof -
  obtain ys where ys_def: "set ys = Y" "concat ys = as@U@bs" "distinct ys"
    using list_of_sublist_concat_eq[OF assms(1,6,4,5,2)] by blast
  then obtain cs ds where cs_def: "cs@U#ds = ys"
    using assms(3) in_set_conv_decomp_first[of U ys] by blast
  then have "List.extract ((=) U) ys = Some (cs,U,ds)"
    using extract_Some_iff[of "(=) U"] ys_def(3) by auto
  then have "concat cs @ U @ concat ds = as@U@bs" using ys_def(2) cs_def by auto
  then show ?thesis using cs_def ys_def(1) concat_all_sublist2[OF assms(4)] assms(7) by force
qed

lemma nonempty_notin_distinct_prefix:
  assumes "distinct (as@bs@V@cs)" and "concat as' = as" and "V \<noteq> []"
  shows "V \<notin> set as'"
proof
  assume "V \<in> set as'"
  then have "set V \<subseteq> set as" using assms(2) by auto
  then have "set as \<inter> set V \<noteq> {}" using assms(3) by (simp add: Int_absorb1)
  then show False using assms(1) by auto
qed

lemma concat_split_UV:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "finite Y"
      and "U \<in> Y"
      and "V \<in> Y"
      and "distinct (as@U@bs@V@cs)"
      and "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs)"
      and "U \<noteq> []"
      and "V \<noteq> []"
    shows "\<exists>as' bs' cs'. concat as' = as \<and> concat bs' = bs \<and> concat cs' = cs
          \<and> set (as'@U#bs'@V#cs') = Y \<and> distinct (as'@U#bs'@V#cs')"
proof -
  obtain as' ds where as'_def:
      "concat as' = as" "concat ds = bs@V@cs" "set (as'@U#ds) = Y" "distinct (as'@U#ds)"
    using concat_split_mid[OF assms(1-3,5-8)] by auto
  have 0: "distinct (bs@V@cs)" using assms(5) by simp
  have "V \<notin> set as'"
    using assms(5,9) as'_def(1) nonempty_notin_distinct_prefix[of as "U@bs"] by auto
  moreover have "V \<noteq> U" using assms(5,8,9) empty_if_sublist_dsjnt[of U] by auto
  ultimately have "V \<in> set ds" using as'_def(3) assms(4) by auto
  then show ?thesis
    using as'_def 0 assms(9) concat_append distinct_mid_unique1
    by (metis concat.simps(2) distinct_mid_unique2 split_list)
qed

lemma cost_decr_if_noarc_lessrank:
  assumes "asi rank r cost"
      and "b \<noteq> []"
      and "r \<notin> set U"
      and "U \<noteq> []"
      and "set (as@U@bs@cs) = \<Union>(set ` Y)"
      and "distinct (as@U@bs@cs)"
      and "take 1 (as@U@bs@cs) = [r]"
      and "forward (as@U@bs@cs)"
      and "concat (b#bs') = bs"
      and "(\<forall>xs \<in> Y. sublist xs as \<or> sublist xs U
            \<or> (\<exists>x \<in> set (b#bs'). sublist xs x) \<or> sublist xs cs)"
      and "\<not>(\<exists>x \<in> set U. \<exists>y \<in> set b. x \<rightarrow>\<^bsub>T\<^esub> y)"
      and "rank (rev b) < rank (rev U)"
    shows "fwd_sub r Y (as@b@U@concat bs'@cs)
          \<and> cost (rev (as@b@U@concat bs'@cs)) < cost (rev (as@U@bs@cs))"
proof -
  have rank_yU: "rank (rev b) < rank (rev U)" using assms(12) by simp
  have 0: "take 1 (as@b@U@concat bs'@cs) = [r]"
    using take1_singleton_app take1_split_nelem_nempty[OF assms(7,4,3)] by fast
  have 1: "distinct (as@b@U@ concat bs'@cs)" using assms(6,9) by force
  have "take 1 (as@U@b@concat bs'@cs) = [r]" using assms(7,9) by force
  then have cost_lt: "cost (rev (as@b@U@concat bs'@cs)) < cost (rev (as@U@bs@cs))"
    using asi_lt_rfst[OF assms(1) rank_yU assms(2,4) 1 0] assms(9) by fastforce
  have P: "set (as@b@U@concat bs'@cs) = \<Union>(set ` Y)" using assms(5,9) by fastforce
  then have P: "unique_set_r r Y (as@b@U@concat bs'@cs)"
    using 0 1 unfolding unique_set_r_def by blast
  have "(\<forall>xs \<in> Y. sublist xs as \<or> sublist xs U \<or> sublist xs b
          \<or> sublist xs (concat bs') \<or> sublist xs cs)"
    using assms(10) concat_all_sublist[of bs']
      sublist_order.dual_order.trans[where a = "concat bs'"] by auto
  then have all_sub: "\<forall>xs \<in> Y. sublist xs (as@b@U@concat bs'@cs)"
    by (metis sublist_order.order.trans sublist_append_leftI sublist_append_rightI)
  have "as \<noteq> []" using take1_split_nelem_nempty[OF assms(7,4,3)] by force
  then have "forward (as@b@U@concat bs'@cs)"
    using move_mid_forward_if_noarc assms(8,9,11) by auto
  then show ?thesis using assms(12) P all_sub cost_lt fwd_sub_def by blast
qed

lemma cost_decr_if_noarc_lessrank':
  assumes "asi rank r cost"
      and "b \<noteq> []"
      and "r \<notin> set U"
      and "U \<noteq> []"
      and "set (as@U@bs@cs) = \<Union>(set ` Y)"
      and "distinct (as@U@bs@cs)"
      and "take 1 (as@U@bs@cs) = [r]"
      and "forward (as@U@bs@cs)"
      and "concat (b#bs') = bs"
      and "(\<forall>xs \<in> Y. sublist xs as \<or> sublist xs U
            \<or> (\<exists>x \<in> set (b#bs'). sublist xs x) \<or> sublist xs cs)"
      and "\<not>(\<exists>x \<in> set U. \<exists>y \<in> set b. x \<rightarrow>\<^bsub>T\<^esub> y)"
      and "rank (rev b) < rank (rev V)"
      and "rank (rev V) \<le> rank (rev U)"
    shows "fwd_sub r Y (as@b@U@concat bs'@cs)
          \<and> cost (rev (as@b@U@concat bs'@cs)) < cost (rev (as@U@bs@cs))"
  using cost_decr_if_noarc_lessrank[OF assms(1-11)] assms(12,13) by simp

lemma sublist_exists_append:
  "\<exists>a\<in>set ((x # xs) @ [b]). sublist ys a \<Longrightarrow> \<exists>a\<in>set(xs @ [x@b]). sublist ys a"
  using sublist_order.dual_order.trans by auto

lemma sublist_set_concat_cases:
  "\<exists>a\<in>set ((x # xs) @ [b]). sublist ys a \<Longrightarrow> sublist ys (concat (rev xs)) \<or> sublist ys x \<or> sublist ys b"
  using sublist_order.dual_order.trans concat_all_sublist_rev[of xs] by auto

lemma sublist_set_concat_or_cases_aux1:
  "sublist ys as \<or> sublist ys U \<or> sublist ys cs
    \<Longrightarrow> sublist ys (as @ U @ concat (rev xs)) \<or> sublist ys cs"
  using sublist_order.dual_order.trans by blast

lemma sublist_set_concat_or_cases_aux2:
  "\<exists>a\<in>set ((x # xs) @ [b]). sublist ys a
    \<Longrightarrow> sublist ys (as @ U @ concat (rev xs)) \<or> sublist ys x \<or> sublist ys b"
  using sublist_set_concat_cases[of x xs b ys] sublist_order.dual_order.trans by blast

lemma sublist_set_concat_or_cases:
  "sublist ys as \<or> sublist ys U \<or> (\<exists>a\<in>set ((x#xs) @ [b]). sublist ys a) \<or> sublist ys cs \<Longrightarrow>
    sublist ys (as@U@ concat (rev xs)) \<or> sublist ys x \<or> (\<exists>a\<in>set [b]. sublist ys a) \<or> sublist ys cs"
  using sublist_set_concat_or_cases_aux1[of ys as U cs] sublist_set_concat_or_cases_aux2[of x xs b ys]
  by auto

corollary not_reachable1_append_if_not_old:
  "\<lbrakk>\<not> (\<exists>z\<in>set U. \<exists>y\<in>set b. z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); set U \<inter> set x = {}; forward x;
    \<exists>z\<in>set x. \<exists>y\<in>set b. z \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> \<not> (\<exists>z\<in>set U. \<exists>y\<in>set (x@b). z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
  using reachable1_append_old_if_arcU[of x b U] by auto

lemma combine_lists_notP:
  assumes "asi rank r cost"
      and "b \<noteq> []"
      and "r \<notin> set U"
      and "U \<noteq> []"
      and "set (as@U@bs@cs) = \<Union>(set ` Y)"
      and "distinct (as@U@bs@cs)"
      and "take 1 (as@U@bs@cs) = [r]"
      and "forward (as@U@bs@cs)"
      and "concat (rev ys @ [b]) = bs"
      and "(\<forall>xs \<in> Y. sublist xs as \<or> sublist xs U
            \<or> (\<exists>x \<in> set (ys @ [b]). sublist xs x) \<or> sublist xs cs)"
      and "rank (rev V) \<le> rank (rev U)"
      and "\<not>(\<exists>x \<in> set U. \<exists>y \<in> set b. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
      and "rank (rev b) < rank (rev V)"
      and "P = (\<lambda>x. rank (rev x) < rank (rev V))"
      and "\<forall>x\<in>set ys. \<not>P x"
      and "\<forall>xs. fwd_sub r Y xs \<longrightarrow> cost (rev (as@U@bs@cs)) \<le> cost (rev xs)"
      and "\<forall>x \<in> set ys. x \<noteq> []"
      and "\<forall>x \<in> set ys. forward x"
      and "forward b"
    shows "\<forall>x\<in>set (combine_lists_P P b ys). \<not>P x \<and> forward x"
using assms proof(induction P b ys rule: combine_lists_P.induct)
  case (1 P b)
  have 0: "concat (b#[]) = bs" using "1.prems"(9) by simp
  have 2: "(\<forall>xs \<in> Y. sublist xs as \<or> sublist xs U
        \<or> (\<exists>x \<in> set ([b]). sublist xs x) \<or> sublist xs cs)" using "1.prems"(10) by simp
  have 3: "\<not> (\<exists>x\<in>set U. \<exists>y\<in>set b. x \<rightarrow>\<^bsub>T\<^esub> y)" using "1.prems"(12) by blast
  show ?case
    using cost_decr_if_noarc_lessrank'[OF 1(1-8) 0 2 3 1(13,11)] 1(16) by auto
next
  case (2 P b x xs)
  have "take 1 as = [r]" using "2.prems"(3,4,7) take1_split_nelem_nempty by fast
  then have "r \<in> set as" using in_set_takeD[of r 1] by simp
  then have "r \<notin> set x" using "2.prems"(6,9) by force
  then have "x \<noteq> []" using "2.prems"(17) by simp
  text \<open>Arc between x and b otherwise not optimal.\<close>
  have 4: "as@U@bs@cs = (as@U@concat (rev xs)) @ x @ b @ cs" using "2.prems"(9) by simp
  have set: "set ((as@U@concat (rev xs)) @ x @ b @ cs) = \<Union> (set ` Y)"
    using "2.prems"(5) 4 by simp
  have dst: "distinct ((as@U@concat (rev xs)) @ x @ b @ cs)" using "2.prems"(6) 4 by simp
  have tk1: "take 1 ((as@U@concat (rev xs)) @ x @ b @ cs) = [r]" using "2.prems"(7) 4 by simp
  have fwd: "forward ((as@U@concat (rev xs)) @ x @ b @ cs)" using "2.prems"(8) 4 by simp
  have cnct: "concat (b # []) = b" by simp
  have sblst: "\<forall>xs' \<in> Y. sublist xs' (as @ U @ concat (rev xs)) \<or> sublist xs' x
          \<or> (\<exists>a\<in>set [b]. sublist xs' a) \<or> sublist xs' cs"
    using "2.prems"(10) sublist_set_concat_or_cases[where as = as] by simp
  have "rank (rev b) < rank (rev x)" using "2.prems"(13-15) by simp
  then have arc_xb: "\<exists>z\<in>set x. \<exists>y\<in>set b. z \<rightarrow>\<^bsub>T\<^esub> y"
    using "2.prems"(16) 4
      cost_decr_if_noarc_lessrank[OF 2(2,3) \<open>r\<notin>set x\<close> \<open>x\<noteq>[]\<close> set dst tk1 fwd cnct sblst]
    by fastforce
  have "set x \<inter> set b = {}" using dst by auto
  then have fwd: "forward (x@b)" using forward_app' arc_xb "2.prems"(18,19) by simp
  show ?case
  proof(cases "P (x @ b)")
    case True
    have 0: "x @ b \<noteq> []" using "2.prems"(2) by blast
    have 1: "concat (rev xs @ [x @ b]) = bs" using "2.prems"(9) by simp
    have 3: "\<forall>xs' \<in> Y. sublist xs' as \<or> sublist xs' U
            \<or> (\<exists>a\<in>set (xs @ [x @ b]). sublist xs' a) \<or> sublist xs' cs"
      using "2.prems"(10) sublist_exists_append by fast
    have "set U \<inter> set x = {}" using 4 "2.prems"(6) by force
    then have 4: "\<not> (\<exists>z\<in>set U. \<exists>y\<in>set (x @ b). z \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
      using not_reachable1_append_if_not_old[OF "2.prems"(12)] "2.prems"(18) arc_xb by simp
    have 5: "rank (rev (x @ b)) < rank (rev V)" using True "2.prems"(14) by simp
    show ?thesis
      using "2.IH"[OF True 2(2) 0 2(4-9) 1 3 2(12) 4 5 2(15)] 2(16-19) fwd by auto
  next
    case False
    then show ?thesis using "2.prems"(15,18) fwd by simp
  qed
qed

lemma sublist_app_l: "sublist ys cs \<Longrightarrow> sublist ys (xs @ cs)"
  using sublist_order.dual_order.trans by blast

lemma sublist_split_concat:
  assumes "a \<in> set (acc @ (as@x#bs))" and "sublist ys a"
  shows "(\<exists>a\<in>set (rev acc @ as @ [x]). sublist ys a) \<or> sublist ys (concat bs @ cs)"
proof(cases "a \<in> set (rev acc @ as @ [x])")
  case True
  then show ?thesis using assms(2) by blast
next
  case False
  then have "a \<in> set bs" using assms(1) by simp
  then show ?thesis
    using assms(2) concat_all_sublist[of bs]
      sublist_order.dual_order.trans[where c = ys, where b = "concat bs"]
    by fastforce
qed

lemma sublist_split_concat':
  "\<exists>a \<in> set (acc @ (as@x#bs)). sublist ys a \<or> sublist ys cs
    \<Longrightarrow> (\<exists>a\<in>set (rev acc @ as @ [x]). sublist ys a) \<or> sublist ys (concat bs @ cs)"
  using sublist_split_concat sublist_app_l[of ys cs] by blast

lemma make_list_notP:
  assumes "asi rank r cost"
      and "r \<notin> set U"
      and "U \<noteq> []"
      and "set (as@U@bs@cs) = \<Union>(set ` Y)"
      and "distinct (as@U@bs@cs)"
      and "take 1 (as@U@bs@cs) = [r]"
      and "forward (as@U@bs@cs)"
      and "concat (rev acc @ ys) = bs"
      and "(\<forall>xs \<in> Y. sublist xs as \<or> sublist xs U
            \<or> (\<exists>x \<in> set (acc @ ys). sublist xs x) \<or> sublist xs cs)"
      and "rank (rev V) \<le> rank (rev U)"
      and "\<And>xs. \<lbrakk>xs \<in> set ys; \<exists>x \<in> set U. \<exists>y \<in> set xs. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
      and "P = (\<lambda>x. rank (rev x) < rank (rev V))"
      and "\<forall>xs. fwd_sub r Y xs \<longrightarrow> cost (rev (as@U@bs@cs)) \<le> cost (rev xs)"
      and "\<forall>x \<in> set ys. x \<noteq> []"
      and "\<forall>x \<in> set ys. forward x"
      and "\<forall>x \<in> set acc. x \<noteq> []"
      and "\<forall>x \<in> set acc. forward x"
      and "\<forall>x \<in> set acc. \<not>P x"
    shows "\<forall>x\<in>set (make_list_P P acc ys). \<not>P x"
using assms proof(induction P acc ys rule: make_list_P.induct)
  case (1 P acc xs)
  then show ?case
  proof(cases "List.extract P xs")
    case None
    then have "\<forall>x \<in> set xs. \<not> P x" by (simp add: extract_None_iff)
    then show ?thesis using "1.prems"(18) None by auto
  next
    case (Some a)
    then obtain as' x bs' where x_def[simp]: "a = (as',x,bs')" by(cases a) auto
    then have x: "\<forall>x \<in> set (rev as' @ acc). \<not>P x" "xs = as'@x#bs'" "rank (rev x) < rank (rev V)"
      using Some "1.prems"(12,18) by (auto simp: extract_Some_iff)
    have "x \<noteq> []" using "1.prems"(14) Some by (simp add: extract_Some_iff)
    have eq: "as@U@bs@cs = as@U@(concat (rev acc @ as' @ [x])) @ (concat bs' @ cs)"
      using "1.prems"(8) Some by (simp add: extract_Some_iff)
    then have 0: "set (as@U@(concat (rev acc @ as' @ [x])) @ (concat bs' @ cs)) = \<Union> (set ` Y)"
      using "1.prems"(4) by argo
    have 2: "distinct (as@U@(concat (rev acc @ as' @ [x])) @ (concat bs' @ cs))"
      using "1.prems"(5) eq by argo
    have 3: "take 1 (as@U@(concat (rev acc @ as' @ [x])) @ (concat bs' @ cs)) = [r]"
      using "1.prems"(6) eq by argo
    have 4: "forward (as@U@(concat (rev acc @ as' @ [x])) @ (concat bs' @ cs))"
      using "1.prems"(7) eq by argo
    have 5: "concat (rev (rev as' @ acc) @ [x]) = concat (rev acc @ as' @ [x])" by simp
    have 6: "\<forall>xs\<in>Y. sublist xs as \<or> sublist xs U
          \<or> (\<exists>x\<in>set ((rev as' @ acc) @ [x]). sublist xs x) \<or> sublist xs (concat bs' @ cs)"
      using "1.prems"(9) x(2) sublist_split_concat'[of acc as' x bs', where cs = cs]
      by auto
    have 7: "\<not> (\<exists>x'\<in>set U. \<exists>y\<in>set x. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)" using "1.prems"(11) x(2,3) by fastforce
    have 8: "\<forall>xs. fwd_sub r Y xs
            \<longrightarrow> cost (rev (as@U@concat(rev acc@as'@[x])@concat bs'@cs)) \<le> cost (rev xs)"
      using "1.prems"(13) eq by simp
    have notP: "\<forall>x\<in>set (combine_lists_P P x (rev as' @ acc)). \<not> P x \<and> forward x"
      using "1.prems"(14-17) x(2)
        combine_lists_notP[OF 1(2) \<open>x\<noteq>[]\<close> 1(3,4) 0 2 3 4 5 6 1(11) 7 x(3) 1(13) x(1) 8]
      by auto
    have cnct: "concat (rev (combine_lists_P P x (rev as' @ acc)) @ bs') = bs"
      using "1.prems"(8) combine_lists_concat_rev_eq[of P] x(2) by simp
    have sblst: "\<forall>xs\<in>Y. sublist xs as \<or> sublist xs U
        \<or> (\<exists>a\<in>set (combine_lists_P P x (rev as' @ acc) @ bs'). sublist xs a) \<or> sublist xs cs"
      using "1.prems"(9) x(2) combine_lists_sublists[of x "rev as'@acc", where P=P] by auto
    have "\<forall>x\<in>set (combine_lists_P P x (rev as' @ acc)). x \<noteq> []"
      using combine_lists_nempty[of "rev as' @ acc"] "1.prems"(14,16) x(2) by auto
    then have "\<forall>x\<in>set (make_list_P P (combine_lists_P P x (rev as' @ acc)) bs'). \<not> P x"
      using "1.IH"[OF Some x_def[symmetric] refl 1(2-8) cnct sblst 1(11-14)] notP x(2) 1(15,16)
      by simp
    then show ?thesis using Some by simp
  qed
qed

lemma no_back_reach1_if_fwd_dstct_bs:
  "\<lbrakk>forward (as@concat bs@V@cs); distinct (as@concat bs@V@cs); xs \<in> set bs\<rbrakk>
    \<Longrightarrow> \<not>(\<exists>x'\<in>set V. \<exists>y\<in>set xs. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
    using no_back_reach1_if_fwd_dstct[of "as@concat bs" "V@cs"] by auto

lemma mid_ranks_ge_if_reach1:
  assumes "[] \<notin> Y"
      and "U \<in> Y"
      and "distinct (as@U@bs@V@cs)"
      and "forward (as@U@bs@V@cs)"
      and "concat bs' = bs"
      and "concat cs' = cs"
      and "set (as'@U#bs'@V#cs') = Y"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    shows "\<forall>xs \<in> set bs'. (\<exists>x\<in>set U. \<exists>y\<in>set xs. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<longrightarrow> rank (rev V) \<le> rank (rev xs)"
proof -
  have "\<forall>xs \<in> set bs'. \<forall>y\<in>set xs. \<not>(\<exists>x\<in>set V.  x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
    using assms(3-6) no_back_reach1_if_fwd_dstct_bs[of "as@U"] by fastforce
  then have 0: "\<forall>xs \<in> set bs'. (\<exists>y\<in>set xs. \<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)
    \<longrightarrow> (\<exists>y\<in>set xs. \<exists>x\<in>set U. \<not> (\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
    by blast
  have "\<forall>xs \<in> set bs'. xs \<noteq> U"
    using assms(1-3,5) concat_all_sublist empty_if_sublist_dsjnt[of U U] by fastforce
  then have "\<And>xs. \<lbrakk>xs \<in> set bs'; \<exists>y\<in>set xs. \<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> xs \<noteq> U \<and> (\<exists>y\<in>set xs. \<exists>x\<in>set U. \<not> (\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> xs \<in> Y"
    using 0 assms(7) by auto
  then show ?thesis using assms(8) by blast
qed

lemma bs_ranks_only_ge:
  assumes "asi rank r cost"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "r \<notin> set U"
      and "U \<in> Y"
      and "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
      and "distinct (as@U@bs@V@cs)"
      and "take 1 (as@U@bs@V@cs) = [r]"
      and "forward (as@U@bs@V@cs)"
      and "concat as' = as"
      and "concat bs' = bs"
      and "concat cs' = cs"
      and "set (as'@U#bs'@V#cs') = Y"
      and "rank (rev V) \<le> rank (rev U)"
      and "\<forall>zs. fwd_sub r Y zs \<longrightarrow> cost (rev (as@U@bs@V@cs)) \<le> cost (rev zs)"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    shows "\<exists>zs. concat zs = bs \<and> (\<forall>z \<in> set zs. rank (rev V) \<le> rank (rev z)) \<and> [] \<notin> set zs"
proof -
  let ?P = "\<lambda>x. rank (rev x) < rank (rev V)"
  have "U \<noteq> []" using assms(3,5) by blast
  have cnct: "concat (rev [] @ bs') = bs" using assms(11) by simp
  have "\<forall>xs\<in>Y. sublist xs as \<or> xs = U \<or> xs = V
        \<or> (\<exists>x\<in>set ([] @ bs'). sublist xs x) \<or> sublist xs cs"
    using assms(10,12,13) concat_all_sublist by auto
  then have sblst:
      "\<forall>xs\<in>Y. sublist xs as \<or> sublist xs U \<or> (\<exists>x\<in>set ([] @ bs'). sublist xs x) \<or> sublist xs (V@cs)"
    using sublist_app_l by fast
  have 0: "\<And>xs. \<lbrakk>xs \<in> set bs'; \<exists>x\<in>set U. \<exists>y\<in>set xs. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    using mid_ranks_ge_if_reach1[OF assms(3,5,7,9,11-13)] assms(16) by blast
  have "\<forall>x\<in>set bs'. x \<noteq> []" using assms(3,13) by auto
  moreover have 2: "\<forall>x\<in>set bs'. forward x" using assms(2,13) by auto
  ultimately have "(\<forall>x\<in>set (make_list_P ?P [] bs'). rank (rev V) \<le> rank (rev x))"
    using assms(15)
      make_list_notP[OF assms(1,4) \<open>U\<noteq>[]\<close> assms(6-9) cnct sblst assms(14) 0 refl]
    by fastforce
  then show ?thesis
    using assms(3,11,13) make_list_concat_rev_eq[of ?P "[]"] make_list_nempty[of "[]" bs'] by auto
qed

lemma cost_ge_if_all_bs_ge:
  assumes "asi rank r cost"
      and "V \<noteq> []"
      and "distinct (as@ds@concat bs@V@cs)"
      and "take 1 as = [r]"
      and "forward V"
      and "\<forall>z\<in>set bs. rank (rev V) \<le> rank (rev z)"
      and "[] \<notin> set bs"
    shows "cost (rev (as@ds@V@concat bs@cs)) \<le> cost (rev (as@ds@concat bs@V@cs))"
using assms proof(induction bs arbitrary: ds)
  case (Cons b bs)
  have 0: "distinct (as@(ds@b)@concat bs@V@cs)" using Cons.prems(3) by simp
  have r_b: "rank (rev V) \<le> rank (rev b)" using Cons.prems(6) by simp
  have "b \<noteq> []" using Cons.prems(7) by auto
  have dst: "distinct ((as@ds)@V@b@concat bs@cs)" using Cons.prems(3) by auto
  have "take 1 ((as@ds)@V@b@concat bs@cs) = [r]"
    using Cons.prems(4) take1_singleton_app by metis
  moreover have "take 1 ((as@ds)@b@V@concat bs@cs) = [r]"
    using Cons.prems(4) take1_singleton_app by metis
  ultimately have "cost (rev (as@ds@V@b@concat bs@cs)) \<le> cost (rev (as@ds@b@V@concat bs@cs))"
    using asi_le_rfst[OF Cons.prems(1) r_b Cons.prems(2) \<open>b\<noteq>[]\<close> dst] by simp
  then show ?case using Cons.IH[OF Cons.prems(1,2) 0] Cons.prems(4-7) by simp
qed(simp)

lemma bs_ge_if_all_ge:
  assumes "asi rank r cost"
      and "V \<noteq> []"
      and "distinct (as@bs@V@cs)"
      and "take 1 as = [r]"
      and "forward V"
      and "concat bs' = bs"
      and "\<forall>z\<in>set bs'. rank (rev V) \<le> rank (rev z)"
      and "[] \<notin> set bs'"
      and "bs \<noteq> []"
    shows "rank (rev V) \<le> rank (rev bs)"
proof -
  have dst: "distinct (as@[]@concat bs'@V@cs)" using assms(3,6) by simp
  then have cost_le: "cost (rev (as@V@bs@cs)) \<le> cost (rev (as@bs@V@cs))"
    using cost_ge_if_all_bs_ge[OF assms(1,2) dst] assms(3-9) by simp
  have tk1: "take 1 ((as)@bs@V@cs) = [r]" using assms(4) take1_singleton_app by metis
  have tk1': "take 1 ((as)@V@bs@cs) = [r]" using assms(4) take1_singleton_app by metis
  have dst: "distinct ((as)@V@bs@cs)" using assms(3) by auto
  show ?thesis using asi_le_iff_rfst[OF assms(1,2,9) tk1' tk1 dst] cost_le by simp
qed

lemma bs_ge_if_optimal:
  assumes "asi rank r cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "r \<notin> set U"
      and "U \<in> Y"
      and "V \<in> Y"
      and "distinct (as@U@bs@V@cs)"
      and "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs)"
      and "take 1 (as@U@bs@V@cs) = [r]"
      and "forward (as@U@bs@V@cs)"
      and "bs \<noteq> []"
      and "rank (rev V) \<le> rank (rev U)"
      and "\<forall>zs. fwd_sub r Y zs \<longrightarrow> cost (rev (as@U@bs@V@cs)) \<le> cost (rev zs)"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    shows "rank (rev V) \<le> rank (rev bs)"
proof -
  obtain as' bs' cs' where bs'_def: "concat as' = as" "concat bs' = bs" "concat cs' = cs"
      "set (as'@U#bs'@V#cs') = Y"
    using concat_split_UV[OF assms(2,5,7-11)] assms(4,7,8) by blast
  obtain bs2 where bs2_def:
      "concat bs2 = bs" "(\<forall>z\<in>set bs2. rank (rev V) \<le> rank (rev z))" "[] \<notin> set bs2"
    using bs_ranks_only_ge[OF assms(1,3,4,6,7,10,9,12,13) bs'_def assms(15-17)] by blast
  have "V \<noteq> []" using assms(4,8) by blast
  have "take 1 as = [r]" using take1_split_nelem_nempty[OF assms(12)] assms(4,6,7) by blast
  then have "take 1 (as@U) = [r]" using take1_singleton_app by fast
  then show ?thesis
    using bs_ge_if_all_ge[OF assms(1) \<open>V\<noteq>[]\<close>, of "as@U"] bs2_def assms(3,8,9,14) by auto
qed

lemma bs_ranks_only_ge_r:
  assumes "[] \<notin> Y"
      and "distinct (as@U@bs@V@cs)"
      and "forward (as@U@bs@V@cs)"
      and "as = []"
      and "concat bs' = bs"
      and "concat cs' = cs"
      and "set (U#bs'@V#cs') = Y"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    shows "\<forall>z \<in> set bs'. rank (rev V) \<le> rank (rev z)"
proof -
  have "U \<in> Y" using assms(7) by auto
  then have "U \<noteq> []" using assms(1) by blast
  have "V \<noteq> []" using assms(1,7) by auto
  have 0: "\<And>xs. \<lbrakk>xs \<in> set bs'; \<exists>x\<in>set U. \<exists>y\<in>set xs. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    using mid_ranks_ge_if_reach1[OF assms(1) \<open>U\<in>Y\<close> assms(2,3,5,6), of "[]"] assms(7,8) by auto
  have "\<exists>x y ys. x#y#ys= as@U@bs@V@cs"
    using \<open>U\<noteq>[]\<close> \<open>V\<noteq>[]\<close> append_Cons append.left_neutral list.exhaust by metis
  then have hd_T: "hd (as@U@bs@V@cs) \<in> verts T" using hd_in_verts_if_forward assms(3) by metis
  moreover have "\<forall>x\<in>set bs'. \<forall>y\<in>set x. y \<in> set (as@U@bs@V@cs)" using assms(5) by auto
  ultimately have "\<forall>x\<in>set bs'. \<forall>y\<in>set x. hd (U@bs@V@cs) \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
    using hd_reach_all_forward assms(3,4) by auto
  then have 1: "\<forall>x\<in>set bs'. \<forall>y\<in>set x. hd U \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y" using assms(1,7) by auto
  have "\<forall>x\<in>set bs'. \<forall>y\<in>set x. y \<notin> set U" using assms(2,5) by auto
  then have "\<forall>x\<in>set bs'. \<forall>y\<in>set x. y \<noteq> hd U" using assms(1,7) by fastforce
  then have "\<forall>x\<in>set bs'. \<forall>y\<in>set x. hd U \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y" using 1 by blast
  then have "\<forall>x\<in>set bs'. \<exists>y\<in>set x. hd U \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y" using assms(1,7) by auto
  then show ?thesis using 0 \<open>U \<noteq> []\<close> hd_in_set by blast
qed

lemma bs_ge_if_rU:
  assumes "asi rank r cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "r \<in> set U"
      and "U \<in> Y"
      and "V \<in> Y"
      and "distinct (as@U@bs@V@cs)"
      and "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs)"
      and "take 1 (as@U@bs@V@cs) = [r]"
      and "forward (as@U@bs@V@cs)"
      and "bs \<noteq> []"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    shows "rank (rev V) \<le> rank (rev bs)"
proof -
  obtain as' bs' cs' where bs'_def: "concat as' = as" "concat bs' = bs" "concat cs' = cs"
      "set (as'@U#bs'@V#cs') = Y"
    using concat_split_UV[OF assms(2,5,7-11)] assms(4,7,8) by blast
  have "take 1 U = [r]" using take1_mid_if_elem[OF assms(12,6,9)] .
  moreover have "as = []" using take1_empty_if_mid[OF assms(12,6,9)] .
  ultimately have tk1: "take 1 (as@U) = [r]" by simp
  then have "set (U#bs'@V#cs') = Y" using bs'_def(1,4) assms(4) \<open>as=[]\<close> by auto
  then have 0: "(\<forall>z\<in>set bs'. rank (rev V) \<le> rank (rev z))"
    using bs_ranks_only_ge_r[OF assms(4,9,13) \<open>as=[]\<close> bs'_def(2,3)] assms(15) by blast
  have "V \<noteq> []" using assms(4,8) by blast
  have "[] \<notin> set bs'" using assms(4) bs'_def(2,4) by auto
  then show ?thesis
    using bs_ge_if_all_ge[OF assms(1) \<open>V\<noteq>[]\<close>, of "as@U"] 0 bs'_def(2) tk1 assms(3,8,9,14) by auto
qed

lemma sublist_before_if_before:
  assumes "hd xs = root" and "forward xs" and "distinct xs"
      and "sublist U xs" and "sublist V xs" and "before U V"
    shows "\<exists>as bs cs. as @ U @ bs @ V @ cs = xs"
proof (rule ccontr)
  assume "\<nexists>as bs cs. as @ U @ bs @ V @ cs = xs"
  then obtain as bs cs where V_bf_U: "xs = as @ V @ bs @ U @ cs"
    using sublist_behind_if_nbefore[OF assms(4,5)] assms(6) before_def by blast
  obtain x y where x_def: "x \<in> set U" "y \<in> set V" "x \<rightarrow>\<^bsub>T\<^esub> y"
    using assms(6) before_def by auto
  then obtain i where i_def: "V!i = y" "i < length V" by (auto simp: in_set_conv_nth)
  then have i_xs: "(as@V@bs@U@cs)!(i + length as) = y" by (simp add: nth_append)
  have "root \<noteq> y" using x_def(3) dominated_not_root by auto
  then have "i + length as > 0" using i_def(2) i_xs assms(1,5) V_bf_U hd_conv_nth[of xs] by force
  then have "i + length as \<ge> 1" by linarith
  then have "i + length as \<in> {1..length (as@V@bs@U@cs) - 1}" using i_def(2) by simp
  then obtain j where j_def: "j < i + length as" "(as@V@bs@U@cs)!j \<rightarrow>\<^bsub>T\<^esub> y"
    using assms(2) V_bf_U i_xs unfolding forward_def by blast
  then have "(as@V@bs@U@cs)!j = (as@V)!j" using i_def(2) by (auto simp: nth_append)
  then have "(as@V@bs@U@cs)!j \<in> set (as@V)" using i_def(2) j_def(1) nth_mem[of "j" "as@V"] by simp
  then have "(as@V@bs@U@cs)!j \<noteq> x" using assms(3) V_bf_U x_def(1) by auto
  then show False using j_def(2) x_def(3) two_in_arcs_contr by fastforce
qed

lemma forward_UV_lists_subset:
  "{x. set x = X \<and> distinct x \<and> take 1 x = [r] \<and> forward x \<and> (\<forall>xs \<in> Y. sublist xs x)}
  \<subseteq> {x. set x = X \<and> distinct x}"
  by blast

lemma forward_UV_lists_finite:
  "finite xs
    \<Longrightarrow> finite {x. set x = xs \<and> distinct x \<and> take 1 x = [r] \<and> forward x \<and> (\<forall>xs \<in> Y. sublist xs x)}"
  using distinct_seteq_finite finite_subset[OF forward_UV_lists_subset] by auto

lemma forward_UV_lists_arg_min_ex_aux:
  "\<lbrakk>finite ys; ys \<noteq> {};
    ys = {x. set x = xs \<and> distinct x \<and> take 1 x = [r] \<and> forward x \<and> (\<forall>xs \<in> Y. sublist xs x)}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using arg_min_if_finite(1)[of ys f] arg_min_least[of ys, where ?f = f] by auto

lemma forward_UV_lists_arg_min_ex:
  "\<lbrakk>finite xs; ys \<noteq> {};
    ys = {x. set x = xs \<and> distinct x \<and> take 1 x = [r] \<and> forward x \<and> (\<forall>xs \<in> Y. sublist xs x)}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using forward_UV_lists_finite forward_UV_lists_arg_min_ex_aux by auto

lemma forward_UV_lists_argmin_ex':
  fixes f :: "'a list \<Rightarrow> real"
  assumes "P = (\<lambda>x. set x = X \<and> distinct x \<and> take 1 x = [r])"
      and "Q = (\<lambda>ys. P ys \<and> forward ys \<and> (\<forall>xs \<in> Y. sublist xs ys))"
      and "\<exists>x. Q x"
    shows "\<exists>zs. Q zs \<and> (\<forall>as. Q as \<longrightarrow> f zs \<le> f as)"
  using forward_UV_lists_arg_min_ex[of X "{x. Q x}"] using assms by fastforce

lemma forward_UV_lists_argmin_ex:
  fixes f :: "'a list \<Rightarrow> real"
  assumes "\<exists>x. fwd_sub r Y x"
  shows "\<exists>zs. fwd_sub r Y zs \<and> (\<forall>as. fwd_sub r Y as \<longrightarrow> f zs \<le> f as)"
  using forward_UV_lists_argmin_ex' assms unfolding fwd_sub_def unique_set_r_def by simp

lemma no_gap_if_contr_seq_fwd:
  assumes "asi rank root cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "U \<in> Y"
      and "V \<in> Y"
      and "before U V"
      and "rank (rev V) \<le> rank (rev U)"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
            \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
      and "\<exists>x. fwd_sub root Y x"
    shows "\<exists>zs. fwd_sub root Y zs \<and> sublist (U@V) zs
          \<and> (\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
proof -
  obtain zs where zs_def:
      "set zs = \<Union>(set ` Y)" "distinct zs" "take 1 zs = [root]" "forward zs"
      "(\<forall>xs \<in> Y. sublist xs zs)" "(\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using forward_UV_lists_argmin_ex[OF assms(11), of "\<lambda>xs. cost (rev xs)"]
    unfolding unique_set_r_def fwd_sub_def by blast
  then have "hd zs = root" using hd_eq_take1 by fast
  then obtain as bs cs where bs_def: "as @ U @ bs @ V @ cs = zs"
    using sublist_before_if_before zs_def(2,4,5) assms(6-8) by blast
  then have bs_prems: "distinct (as@U@bs@V@cs)" "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
    "\<forall>xs\<in>Y. sublist xs (as@U@bs@V@cs)" "take 1 (as@U@bs@V@cs) = [root]" "forward (as@U@bs@V@cs)"
    using zs_def(1-5) by auto
  show ?thesis
  proof(cases "bs = []")
    case True
    then have "sublist (U@V) zs" using bs_def sublist_def by force
    then show ?thesis using zs_def unfolding unique_set_r_def fwd_sub_def by blast
  next
    case bs_nempty: False
    then have rank_le: "rank (rev V) \<le> rank (rev bs)"
    proof(cases "root \<in> set U")
      case True
      then show ?thesis
        using bs_ge_if_rU[OF assms(1-5) True assms(6,7) bs_prems bs_nempty assms(10)]
        by blast
    next
      case False
      have "\<forall>zs. fwd_sub root Y zs \<longrightarrow> cost (rev (as@U@bs@V@cs)) \<le> cost (rev zs)"
        using zs_def(6) bs_def by blast
      then show ?thesis
        using bs_ge_if_optimal[OF assms(1-5)] bs_nempty bs_prems False assms(6,7,9,10)
        by blast
    qed
    have 0: "distinct ((as@U)@V@bs@cs)" using bs_def zs_def(2) by auto
    have "take 1 (as@U) = [root]"
      using bs_def assms(4,6) take1_split_nempty[of U as] zs_def(3) by fastforce
    then have 1: "take 1 (as@U@V@bs@cs) = [root]"
      using take1_singleton_app[of "as@U" root "V@bs@cs"] by simp
    have 2: "\<forall>xs\<in>Y. sublist xs (as@U@V@bs@cs)"
      using zs_def(5) bs_def sublists_preserv_move_VY_all[OF assms(2,6,7)] assms(4,6) by blast
    have "V \<noteq> []" using assms(4,7) by blast
    have "cost (rev (as@U@V@bs@cs)) \<le> cost (rev zs)"
      using asi_le_rfst[OF assms(1) rank_le \<open>V\<noteq>[]\<close> bs_nempty 0] 1 zs_def(3) bs_def by simp
    then have cost_le: "\<forall>ys. fwd_sub root Y ys \<longrightarrow> cost (rev (as@U@V@bs@cs)) \<le> cost (rev ys)"
      using zs_def(6) by fastforce
    have "forward (as@U@V@bs@cs)"
      using move_mid_backward_if_noarc assms(8) zs_def(4) bs_def by blast
    moreover have "set (as@U@V@bs@cs) = \<Union> (set ` Y)"
      unfolding zs_def(1)[symmetric] bs_def[symmetric] by force
    ultimately have "fwd_sub root Y (as@U@V@bs@cs)"
      unfolding unique_set_r_def fwd_sub_def using 0 1 2 by fastforce
    moreover have "sublist (U@V) (as@U@V@bs@cs)" unfolding sublist_def by fastforce
    ultimately show ?thesis using cost_le by blast
  qed
qed

lemma combine_union_sets_alt:
  fixes X Y
  defines "Z \<equiv> X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}"
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> X. \<forall>ys \<in> X. xs = ys \<or> set xs \<inter> set ys = {}"
    shows "Z = X \<union> (Y - {x. set x \<inter> \<Union>(set ` X) \<noteq> {}})"
  unfolding assms(1) using assms(2,3) by fast

lemma combine_union_sets_disjoint:
  fixes X Y
  defines "Z \<equiv> X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}"
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> X. \<forall>ys \<in> X. xs = ys \<or> set xs \<inter> set ys = {}"
    shows "\<forall>xs \<in> Z. \<forall>ys \<in> Z. xs = ys \<or> set xs \<inter> set ys = {}"
  unfolding Z_def using assms(2,3) by force

lemma combine_union_sets_set_sub1_aux:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>ys \<in> X. \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys"
      and "x \<in> \<Union>(set ` Y)"
  shows "x \<in> \<Union>(set ` (X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}))"
proof -
  let ?Z = "X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}"
  obtain ys where ys_def: "x \<in> set ys" "ys \<in> Y" using assms(3) by blast
  then show ?thesis
  proof(cases "ys \<in> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}")
    case True
    then show ?thesis using ys_def(1) by auto
  next
    case False
    then obtain U V where U_def: "U \<in> Y" "V \<in> Y" "U@V \<in> X" "set ys \<inter> set (U@V) \<noteq> {}"
      using ys_def(2) assms(2) by fast
    then consider "set ys \<inter> set U \<noteq> {}" | "set ys \<inter> set V \<noteq> {}" by fastforce
    then show ?thesis
    proof(cases)
      case 1
      then have "U = ys" using assms(1) U_def(1) ys_def(2) by blast
      then show ?thesis using ys_def(1) U_def(3) by fastforce
    next
      case 2
      then have "V = ys" using assms(1) U_def(2) ys_def(2) by blast
      then show ?thesis using ys_def(1) U_def(3) by fastforce
    qed
  qed
qed

lemma combine_union_sets_set_sub1:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>ys \<in> X. \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys"
    shows "\<Union>(set ` Y) \<subseteq> \<Union>(set ` (X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}))"
  using combine_union_sets_set_sub1_aux[OF assms] by blast

lemma combine_union_sets_set_sub2:
  assumes "\<forall>ys \<in> X. \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys"
  shows "\<Union>(set ` (X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}})) \<subseteq> \<Union>(set ` Y)"
  using assms by fastforce

lemma combine_union_sets_set_eq:
  assumes "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>ys \<in> X. \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys"
    shows "\<Union>(set ` (X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}})) = \<Union>(set ` Y)"
  using combine_union_sets_set_sub1[OF assms] combine_union_sets_set_sub2[OF assms(2)] by blast

lemma combine_union_sets_sublists:
  assumes "sublist x ys"
      and "\<forall>xs \<in> X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}. sublist xs ys"
      and "xs \<in> insert x X \<union> {xs. xs \<in> Y \<and> set xs \<inter> \<Union>(set ` (insert x X)) = {}}"
    shows "sublist xs ys"
  using assms by auto

lemma combine_union_sets_optimal_cost:
  assumes "asi rank root cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "\<exists>x. fwd_sub root Y x"
      and "\<forall>ys \<in> X. \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys \<and> before U V \<and> rank (rev V) \<le> rank (rev U)
          \<and> (\<forall>xs \<in> Y. (\<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> xs \<noteq> U)
            \<longrightarrow> rank (rev V) \<le> rank (rev xs))"
      and "\<forall>xs \<in> X. \<forall>ys \<in> X. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> X. \<forall>ys \<in> X. xs = ys \<or> \<not>(\<exists>x\<in>set xs. \<exists>y\<in>set ys. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
      and "finite X"
    shows "\<exists>zs. fwd_sub root (X \<union> {x. x \<in> Y \<and> set x \<inter> \<Union>(set ` X) = {}}) zs
            \<and> (\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
using assms(10,1-9) proof(induction X rule: finite_induct)
  case empty
  then show ?case using forward_UV_lists_argmin_ex by simp
next
  case (insert x X)
  let ?Y = "X \<union> {xs. xs \<in> Y \<and> set xs \<inter> \<Union>(set ` X) = {}}"
  let ?X = "insert x X \<union> {xs. xs \<in> Y \<and> set xs \<inter> \<Union>(set ` (insert x X)) = {}}"
  obtain zs where zs_def:
      "fwd_sub root ?Y zs" "(\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using insert.IH[OF insert(4-9)] insert.prems(7,8,9) by auto
  obtain U V where U_def: "U \<in> Y" "V \<in> Y" "U@V = x" "before U V" "rank (rev V) \<le> rank (rev U)"
    "\<forall>xs \<in> Y. (\<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> xs \<noteq> U)
      \<longrightarrow> rank (rev V) \<le> rank (rev xs)"
    using insert.prems(7) by auto
  then have U: "U \<in> ?Y" using insert.prems(2,8) insert.hyps(2) by fastforce
  have V: "V \<in> ?Y" using U_def(2,3) insert.prems(8) insert.hyps(2) by fastforce
  have disj: "\<forall>xs \<in> ?Y. \<forall>ys \<in> ?Y. xs = ys \<or> set xs \<inter> set ys = {}"
    using combine_union_sets_disjoint[of Y X] insert.prems(2,8) by blast
  have fwd: "\<forall>xs \<in> ?Y. forward xs"
    using insert.prems(3,7) seq_conform_alt seq_conform_if_before by fastforce
  have nempty: "[] \<notin> ?Y" using insert.prems(4,7) by blast
  have fin: "finite ?Y" using insert.prems(5) insert.hyps(1) by simp
  have 0: "\<And>xs. \<lbrakk>xs \<in> ?Y; \<exists>y\<in>set xs. \<not> (\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); xs \<noteq> U\<rbrakk>
         \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
    using U_def(3,6) insert.prems(9) insert.hyps(2) by auto
  then have "\<exists>zs. fwd_sub root ?Y zs \<and> sublist (U@V) zs
                \<and> (\<forall>as. fwd_sub root ?Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using no_gap_if_contr_seq_fwd[OF insert.prems(1) disj fwd nempty fin U V U_def(4,5)] zs_def(1)
    unfolding fwd_sub_def unique_set_r_def by blast
  then obtain xs where xs_def:
      "fwd_sub root ?Y xs" "sublist (U@V) xs"
      "(\<forall>as. fwd_sub root ?Y as \<longrightarrow> cost (rev xs) \<le> cost (rev as))"
    by blast
  then have cost: "(\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev xs) \<le> cost (rev as))"
    using zs_def by fastforce
  have 0: "\<forall>ys \<in> (insert x X). \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys" using insert.prems(7) by fastforce
  then have "\<forall>ys \<in> X. \<exists>U \<in> Y. \<exists>V \<in> Y. U@V = ys" by simp
  then have "\<Union>(set ` ?Y) = \<Union>(set ` Y)"
    using combine_union_sets_set_eq[OF insert.prems(2)] by simp
  then have "\<Union>(set ` ?X) = \<Union>(set ` ?Y)"
    using combine_union_sets_set_eq[OF insert.prems(2) 0] by simp
  then have P_eq: "unique_set_r root ?X = unique_set_r root ?Y" unfolding unique_set_r_def by simp
  have "\<And>ys. \<lbrakk>sublist (U@V) ys; (\<forall>xs \<in> ?Y. sublist xs ys)\<rbrakk> \<Longrightarrow> (\<forall>xs \<in> ?X. sublist xs ys)"
    using combine_union_sets_sublists[of x, where Y=Y and X=X] U_def(3) by blast
  then have "\<And>ys. \<lbrakk>sublist (U@V) ys; fwd_sub root ?Y ys\<rbrakk> \<Longrightarrow> fwd_sub root ?X ys"
    unfolding P_eq fwd_sub_def by blast
  then show ?case using xs_def(1,2) cost by blast
qed

lemma bs_ge_if_geV:
  assumes "asi rank r cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "U \<in> Y"
      and "V \<in> Y"
      and "distinct (as@U@bs@V@cs)"
      and "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
      and "\<forall>xs \<in> Y. sublist xs (as@U@bs@V@cs)"
      and "take 1 (as@U@bs@V@cs) = [r]"
      and "bs \<noteq> []"
      and "\<forall>xs \<in> Y. xs \<noteq> U \<longrightarrow> rank (rev V) \<le> rank (rev xs)"
    shows "rank (rev V) \<le> rank (rev bs)"
proof -
  obtain as' bs' cs' where bs'_def: "concat as' = as" "concat bs' = bs" "concat cs' = cs"
      "set (as'@U#bs'@V#cs') = Y"
    using concat_split_UV[OF assms(2,5-10)] assms(4,6,7) by blast
  have tk1: "take 1 (as@U) = [r]"
    using take1_split_nempty[of U as] assms(4,6,11) by force
  have "\<forall>z\<in>set bs'. z \<noteq> U"
    using bs'_def(2) assms(4,6,8) concat_all_sublist by (fastforce dest!: empty_if_sublist_dsjnt)
  then have 0: "\<forall>z\<in>set bs'. rank (rev V) \<le> rank (rev z)"
    using assms(13) bs'_def(4) by auto
  have "V \<noteq> []" using assms(4,7) by blast
  have "[] \<notin> set bs'" using assms(4) bs'_def(2,4) by auto
  then show ?thesis
    using bs_ge_if_all_ge[OF assms(1) \<open>V\<noteq>[]\<close>, of "as@U"] 0 bs'_def(2) tk1 assms(3,7,8,12) by auto
qed

lemma no_gap_if_geV:
  assumes "asi rank root cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "U \<in> Y"
      and "V \<in> Y"
      and "before U V"
      and "\<forall>xs \<in> Y. xs \<noteq> U \<longrightarrow> rank (rev V) \<le> rank (rev xs)"
      and "\<exists>x. fwd_sub root Y x"
    shows "\<exists>zs. fwd_sub root Y zs \<and> sublist (U@V) zs
          \<and> (\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
proof -
  obtain zs where zs_def:
      "set zs = \<Union>(set ` Y)" "distinct zs" "take 1 zs = [root]" "forward zs"
      "(\<forall>xs \<in> Y. sublist xs zs)" "(\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using forward_UV_lists_argmin_ex[OF assms(10), of "\<lambda>x. cost (rev x)"]
    unfolding fwd_sub_def unique_set_r_def by blast
  then have "hd zs = root" using hd_eq_take1 by fast
  then obtain as bs cs where bs_def: "as @ U @ bs @ V @ cs = zs"
    using sublist_before_if_before zs_def(2,4,5) assms(6-8) by blast
  then have bs_prems: "distinct (as@U@bs@V@cs)" "set (as@U@bs@V@cs) = \<Union>(set ` Y)"
    "\<forall>xs\<in>Y. sublist xs (as@U@bs@V@cs)" "take 1 (as@U@bs@V@cs) = [root]"
    using zs_def(1-5) by auto
  show ?thesis
  proof(cases "bs = []")
    case True
    then have "sublist (U@V) zs" using bs_def sublist_def by force
    then show ?thesis using zs_def unfolding fwd_sub_def unique_set_r_def by blast
  next
    case False
    then have rank_le: "rank (rev V) \<le> rank (rev bs)"
      using bs_ge_if_geV[OF assms(1-7) bs_prems False assms(9)] by blast
    have 0: "distinct ((as@U)@V@bs@cs)" using bs_def zs_def(2) by auto
    have "take 1 (as@U) = [root]"
      using bs_def assms(4,6) take1_split_nempty[of U as] zs_def(3) by fastforce
    then have 1: "take 1 (as@U@V@bs@cs) = [root]"
      using take1_singleton_app[of "as@U" root "V@bs@cs"] by simp
    have 2: "\<forall>xs\<in>Y. sublist xs (as@U@V@bs@cs)"
      using zs_def(5) bs_def sublists_preserv_move_VY_all[OF assms(2,6,7)] assms(4,6) by blast
    have "V \<noteq> []" using assms(4,7) by blast
    have "cost (rev (as@U@V@bs@cs)) \<le> cost (rev zs)"
      using asi_le_rfst[OF assms(1) rank_le \<open>V\<noteq>[]\<close> False 0] 1 zs_def(3) bs_def by simp
    then have cost_le: "\<forall>ys. fwd_sub root Y ys \<longrightarrow> cost (rev (as@U@V@bs@cs)) \<le> cost (rev ys)"
      using zs_def(6) by fastforce
    have "forward (as@U@V@bs@cs)"
      using move_mid_backward_if_noarc assms(8) zs_def(4) bs_def by blast
    moreover have "set (as@U@V@bs@cs) = \<Union>(set ` Y)" using bs_def zs_def(1) by fastforce
    ultimately have "fwd_sub root Y (as@U@V@bs@cs)"
      unfolding fwd_sub_def unique_set_r_def using 0 1 2 by auto
    moreover have "sublist (U@V) (as@U@V@bs@cs)" unfolding sublist_def by fastforce
    ultimately show ?thesis using cost_le by blast
  qed
qed

lemma app_UV_set_optimal_cost:
  assumes "asi rank root cost"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. forward xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "U \<in> Y"
      and "V \<in> Y"
      and "before U V"
      and "\<forall>xs \<in> Y. xs \<noteq> U \<longrightarrow> rank (rev V) \<le> rank (rev xs)"
      and "\<exists>x. fwd_sub root Y x"
    shows "\<exists>zs. fwd_sub root ({U@V} \<union> {x. x \<in> Y \<and> x \<noteq> U \<and> x \<noteq> V}) zs
            \<and> (\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
proof -
  have P_eq: "unique_set_r root Y = unique_set_r root ({U@V} \<union> {x. x \<in> Y \<and> x \<noteq> U \<and> x \<noteq> V})"
    unfolding unique_set_r_def using assms(6,7) by auto
  have "\<exists>zs. fwd_sub root Y zs \<and> sublist (U@V) zs
          \<and> (\<forall>as. fwd_sub root Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using no_gap_if_geV[OF assms(1-10)] by blast
  then show ?thesis unfolding P_eq fwd_sub_def by blast
qed

end

context tree_query_graph
begin

lemma no_cross_ldeep_rev_if_forward:
  assumes "xs \<noteq> []" and "r \<in> verts G" and "directed_tree.forward (dir_tree_r r) (rev xs)"
  shows "no_cross_products (create_ldeep_rev xs)"
using assms proof(induction xs rule: create_ldeep_rev.induct)
  case (3 x y ys)
  then interpret T: directed_tree "dir_tree_r r" r using directed_tree_r by blast
  have split: "create_ldeep_rev (x#y#ys) = Join (create_ldeep_rev (y#ys)) (Relation x)" by simp
  have "rev (x#y#ys) ! (length (y#ys)) = x" using nth_append_length[of "rev (y#ys)"] by simp
  moreover have "length (y#ys) \<in> {1..length (rev (x#y#ys)) - 1}" by simp
  ultimately obtain j where j_def: "j < (length (y#ys))" "rev (x#y#ys)!j \<rightarrow>\<^bsub>dir_tree_r r\<^esub> x"
    using "3.prems"(3) unfolding T.forward_def by fastforce
  then have "rev (x#y#ys)!j \<in> set (y#ys)"
    using nth_mem[of j "rev (y#ys)"] by (auto simp add: nth_append)
  then have "\<exists>x'\<in>relations (create_ldeep_rev (y#ys)). x' \<rightarrow>\<^bsub>dir_tree_r r\<^esub> x"
    using j_def(2) create_ldeep_rev_relations[of "y#ys"] by blast
  then have 1: "\<exists>x'\<in>relations (create_ldeep_rev (y#ys)). x' \<rightarrow>\<^bsub>G\<^esub>x"
    using assms(2) dir_tree_r_dom_in_G by blast
  have "T.forward (rev (y#ys))" using "3.prems"(3) T.forward_cons by blast
  then show ?case using 1 3 by simp
qed(auto)

lemma no_cross_ldeep_if_forward:
  "\<lbrakk>xs \<noteq> []; r \<in> verts G; directed_tree.forward (dir_tree_r r) xs\<rbrakk>
    \<Longrightarrow> no_cross_products (create_ldeep xs)"
  unfolding create_ldeep_def using no_cross_ldeep_rev_if_forward by simp

lemma no_cross_ldeep_if_forward':
  "\<lbrakk>set xs = verts G; r \<in> verts G; directed_tree.forward (dir_tree_r r) xs\<rbrakk>
    \<Longrightarrow> no_cross_products (create_ldeep xs)"
  using no_cross_ldeep_if_forward[of xs] by fastforce

lemma forward_if_ldeep_rev_no_cross:
  assumes "r \<in> verts G" and "no_cross_products (create_ldeep_rev xs)"
      and "hd (rev xs) = r" and "distinct xs"
    shows "directed_tree.forward_arcs (dir_tree_r r) xs"
using assms proof(induction xs rule: create_ldeep_rev.induct)
  case 1
  then show ?case using directed_tree_r directed_tree.forward_arcs.simps(1) by fast
next
  case (2 x)
  then show ?case using directed_tree_r directed_tree.forward_arcs.simps(2) by fast
next
  case (3 x y ys)
  then interpret T: directed_tree "dir_tree_r r" r using directed_tree_r by blast
  have "hd (rev (y # ys)) = r" using "3.prems"(3) hd_append2[of "rev (y#ys)" "[x]"] by simp
  then have ind: "T.forward_arcs (y#ys)" using 3 by fastforce
  have matching: "matching_rels (create_ldeep_rev (x#y#ys))"
    using matching_rels_if_no_cross "3.prems"(2) by simp
  have "r \<in> relations (create_ldeep_rev (x#y#ys))" using "3.prems"(3)
    using create_ldeep_rev_relations[of "x#y#ys"] hd_rev[of "x#y#ys"] by simp
  then obtain p' where p'_def:
      "awalk r p' x \<and> set (awalk_verts r p') \<subseteq> relations (create_ldeep_rev (x#y#ys))"
    using no_cross_awalk[OF matching "3.prems"(2)] by force
  then obtain p where p_def:
      "apath r p x" "set (awalk_verts r p) \<subseteq> relations (create_ldeep_rev (x#y#ys))"
    using apath_awalk_to_apath awalk_to_apath_verts_subset by blast
  then have "pre_digraph.apath (dir_tree_r r) r p x" using apath_in_dir_if_apath_G by blast
  moreover have "r \<noteq> x"
    using "3.prems"(3,4) T.no_back_arcs.cases[of "rev (x#y#ys)"] distinct_first_uneq_last[of x]
    by fastforce
  ultimately obtain u where u_def:
      "u \<rightarrow>\<^bsub>dir_tree_r r\<^esub> x" "u \<in> set (pre_digraph.awalk_verts (dir_tree_r r) r p)"
    using p_def(2) T.awalk_verts_dom_if_uneq T.awalkI_apath by blast
  then have "u \<in> relations (create_ldeep_rev (x#y#ys))"
    using awalk_verts_G_T "3.prems"(1) p_def(2) by auto
  then have "u \<in> set (x#y#ys)" by (simp add: create_ldeep_rev_relations)
  then show ?case using u_def(1) ind T.forward_arcs.simps(3) T.loopfree.adj_not_same by auto
qed

lemma forward_if_ldeep_no_cross:
  "\<lbrakk>r \<in> verts G; no_cross_products (create_ldeep xs); hd xs = r; distinct xs\<rbrakk>
    \<Longrightarrow> directed_tree.forward (dir_tree_r r) xs"
  using forward_if_ldeep_rev_no_cross directed_tree.forward_arcs_alt directed_tree_r
  by (fastforce simp: create_ldeep_def)

lemma no_cross_ldeep_iff_forward:
  "\<lbrakk>xs \<noteq> []; r \<in> verts G; hd xs = r; distinct xs\<rbrakk>
    \<Longrightarrow> no_cross_products (create_ldeep xs) \<longleftrightarrow> directed_tree.forward (dir_tree_r r) xs"
  using forward_if_ldeep_no_cross no_cross_ldeep_if_forward by blast

lemma no_cross_if_fwd_ldeep:
  "\<lbrakk>r \<in> verts G; left_deep t; directed_tree.forward (dir_tree_r r) (inorder t)\<rbrakk>
    \<Longrightarrow> no_cross_products t"
  using no_cross_ldeep_if_forward[OF inorder_nempty] by fastforce

lemma forward_if_ldeep_no_cross':
  "\<lbrakk>first_node t \<in> verts G; distinct_relations t; left_deep t; no_cross_products t\<rbrakk>
    \<Longrightarrow> directed_tree.forward (dir_tree_r (first_node t)) (inorder t)"
  using forward_if_ldeep_no_cross by (simp add: first_node_eq_hd distinct_relations_def)

lemma no_cross_iff_forward_ldeep:
  "\<lbrakk>first_node t \<in> verts G; distinct_relations t; left_deep t\<rbrakk>
    \<Longrightarrow> no_cross_products t \<longleftrightarrow> directed_tree.forward (dir_tree_r (first_node t)) (inorder t)"
  using no_cross_if_fwd_ldeep forward_if_ldeep_no_cross' by blast

lemma sublist_before_if_before:
  assumes "hd xs = r" and "no_cross_products (create_ldeep xs)" and "r \<in> verts G" and "distinct xs"
      and "sublist U xs" and "sublist V xs" and "directed_tree.before (dir_tree_r r) U V"
    shows "\<exists>as bs cs. as @ U @ bs @ V @ cs = xs"
  using directed_tree.sublist_before_if_before[OF directed_tree_r] forward_if_ldeep_no_cross assms
  by blast

lemma nocross_UV_lists_subset:
  "{x. set x = X \<and> distinct x \<and> take 1 x = [r]
     \<and> no_cross_products (create_ldeep x) \<and> (\<forall>xs \<in> Y. sublist xs x)}
  \<subseteq> {x. set x = X \<and> distinct x}"
  by blast

lemma nocross_UV_lists_finite:
  "finite xs
    \<Longrightarrow> finite {x. set x = xs \<and> distinct x \<and> take 1 x = [r]
      \<and> no_cross_products (create_ldeep x) \<and> (\<forall>xs \<in> Y. sublist xs x)}"
  using distinct_seteq_finite finite_subset[OF nocross_UV_lists_subset] by auto

lemma nocross_UV_lists_arg_min_ex_aux:
  "\<lbrakk>finite ys; ys \<noteq> {};
    ys = {x. set x = xs \<and> distinct x \<and> take 1 x = [r]
           \<and> no_cross_products (create_ldeep x) \<and> (\<forall>xs \<in> Y. sublist xs x)}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using arg_min_if_finite(1)[of ys f] arg_min_least[of ys, where ?f = f] by auto

lemma nocross_UV_lists_arg_min_ex:
  "\<lbrakk>finite xs; ys \<noteq> {};
    ys = {x. set x = xs \<and> distinct x \<and> take 1 x = [r]
           \<and> no_cross_products (create_ldeep x) \<and> (\<forall>xs \<in> Y. sublist xs x)}\<rbrakk>
    \<Longrightarrow> \<exists>y \<in> ys. \<forall>z \<in> ys. (f :: 'a list \<Rightarrow> real) y \<le> f z"
  using nocross_UV_lists_finite nocross_UV_lists_arg_min_ex_aux by auto

lemma nocross_UV_lists_argmin_ex:
  fixes f :: "'a list \<Rightarrow> real"
  assumes "P = (\<lambda>x. set x = X \<and> distinct x \<and> take 1 x = [r])"
      and "Q = (\<lambda>ys. P ys \<and> no_cross_products (create_ldeep ys) \<and> (\<forall>xs \<in> Y. sublist xs ys))"
      and "\<exists>x. Q x"
    shows "\<exists>zs. Q zs \<and> (\<forall>as. Q as \<longrightarrow> f zs \<le> f as)"
  using nocross_UV_lists_arg_min_ex[of X "{x. Q x}"] using assms by fastforce

lemma no_gap_if_contr_seq:
  fixes Y r
  defines "X \<equiv> \<Union>(set ` Y)"
  defines "P \<equiv> (\<lambda>ys. set ys = X \<and> distinct ys \<and> take 1 ys = [r])"
  defines "Q \<equiv> (\<lambda>ys. P ys \<and> no_cross_products (create_ldeep ys) \<and> (\<forall>xs \<in> Y. sublist xs ys))"
  assumes "asi rank r c"
      and "\<forall>xs \<in> Y. \<forall>ys \<in> Y. xs = ys \<or> set xs \<inter> set ys = {}"
      and "\<forall>xs \<in> Y. directed_tree.forward (dir_tree_r r) xs"
      and "[] \<notin> Y"
      and "finite Y"
      and "U \<in> Y"
      and "V \<in> Y"
      and "r \<in> verts G"
      and "directed_tree.before (dir_tree_r r) U V"
      and "rank (rev V) \<le> rank (rev U)"
      and "\<And>xs. \<lbrakk>xs \<in> Y; \<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>dir_tree_r r\<^esub> y)
            \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>dir_tree_r r\<^esub> y); xs \<noteq> U\<rbrakk>
              \<Longrightarrow> rank (rev V) \<le> rank (rev xs)"
      and "\<exists>x. Q x"
    shows "\<exists>zs. Q zs \<and> sublist (U@V) zs \<and> (\<forall>as. Q as \<longrightarrow> c (rev zs) \<le> c (rev as))"
proof -
  interpret T: directed_tree "dir_tree_r r" r using assms(11) directed_tree_r by auto
  let ?Q = "(\<lambda>ys. P ys \<and> T.forward ys \<and> (\<forall>xs \<in> Y. sublist xs ys))"
  have "?Q = Q"
    using no_cross_ldeep_iff_forward assms(11,2,3) hd_eq_take1 nempty_if_take1[where r=r] by fast
  then show ?thesis
    using T.no_gap_if_contr_seq_fwd[OF assms(4-10,12-14)] assms(15,1,2)
    unfolding T.fwd_sub_def unique_set_r_def by auto
qed

end

subsection "Arc Invariants"

function path_lverts :: "('a list,'b) dtree \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "path_lverts (Node r {|(t,e)|}) x = (if x \<in> set r then {} else set r \<union> path_lverts t x)"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> path_lverts (Node r xs) x = (if x \<in> set r then {} else set r)"
  by (metis darcs_mset.cases old.prod.exhaust) fast+
termination by lexicographic_order

definition path_lverts_list :: "('a list \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "path_lverts_list xs x = (\<Union>(t,e)\<in> set (takeWhile (\<lambda>(t,e). x \<notin> set t) xs). set t)"

definition dom_children :: "('a list,'b) dtree \<Rightarrow> ('a,'b) pre_digraph \<Rightarrow> bool" where
  "dom_children t1 T = (\<forall>t \<in> fst ` fset (sucs t1). \<forall>x \<in> dverts t.
      \<exists>r \<in> set (root t1) \<union> path_lverts t (hd x). r \<rightarrow>\<^bsub>T\<^esub> hd x)"

abbreviation children_deg1 :: "(('a,'b) dtree \<times> 'b) fset \<Rightarrow> (('a,'b) dtree \<times> 'b) set" where
  "children_deg1 xs \<equiv> {(t,e). (t,e) \<in> fset xs \<and> max_deg t \<le> 1}"

lemma path_lverts_subset_dlverts: "path_lverts t x \<subseteq> dlverts t"
  by(induction t x rule: path_lverts.induct) auto

lemma path_lverts_to_list_eq:
  "path_lverts t x = path_lverts_list (dtree_to_list (Node r0 {|(t,e)|})) x"
   by (induction t rule: dtree_to_list.induct) (auto simp: path_lverts_list_def)

lemma path_lverts_from_list_eq:
  "path_lverts (dtree_from_list r0 ys) x = path_lverts_list ((r0,e0)#ys) x"
  unfolding path_lverts_list_def using path_lverts.simps(2)[of "{||}"]
  by (induction ys rule: dtree_from_list.induct) (force, cases "x \<in> set r0", auto)

lemma path_lverts_child_union_root_sub:
  assumes "t2 \<in> fst ` fset (sucs t1)"
  shows "path_lverts t1 x \<subseteq> set (root t1) \<union> path_lverts t2 x"
proof(cases "\<forall>x. sucs t1 \<noteq> {|x|}")
  case True
  then show ?thesis using path_lverts.simps(2)[of "sucs t1" "root t1"] by simp
next
  case False
  then obtain e2 where "sucs t1 = {|(t2,e2)|}" using assms by fastforce
  then show ?thesis
    using path_lverts.simps(1)[of "root t1" t2 e2] dtree.collapse[of t1]
    by(cases "x \<in> set (root t1)") fastforce+
qed

lemma path_lverts_simps1_sucs:
  "\<lbrakk>x \<notin> set (root t1); sucs t1 = {|(t2,e2)|}\<rbrakk>
    \<Longrightarrow> set (root t1) \<union> path_lverts t2 x = path_lverts t1 x"
  using path_lverts.simps(1)[of "root t1" t2 e2 x] dtree.exhaust_sel[of t1] by argo

lemma subtree_path_lverts_sub:
  "\<lbrakk>wf_dlverts t1; max_deg t1 \<le> 1; is_subtree (Node r xs) t1; t2 \<in> fst ` fset xs; x\<in>set (root t2)\<rbrakk>
    \<Longrightarrow> set r \<subseteq> path_lverts t1 x"
proof(induction t1)
  case (Node r1 xs1)
  then have "xs1 \<noteq> {||}" by force
  then have "max_deg (Node r1 xs1) = 1"
    using Node.prems(2) empty_if_mdeg_0[of r1 xs1] by fastforce
  then obtain t e where t_def: "xs1 = {|(t,e)|}" using mdeg_1_singleton by fastforce
  have x_t2: "x \<in> dlverts t2" using Node.prems(5) lverts_if_in_verts dtree.set_sel(1) by fast
  show ?case
  proof(cases "Node r1 xs1 = Node r xs")
    case True
    then show ?thesis using Node.prems(1,4) x_t2 t_def by force
  next
    case False
    then have 0: "is_subtree (Node r xs) t" using t_def Node.prems(3) by force
    moreover have "max_deg t \<le> 1" using t_def Node.prems(2) mdeg_ge_child[of t e xs1] by simp
    moreover have "x \<notin> set r1" using t_def x_t2 Node.prems(1,4) 0 subtree_in_dlverts by force
    ultimately show ?thesis using Node.IH t_def Node.prems(1,4,5) by auto
  qed
qed

lemma path_lverts_empty_if_roothd:
  assumes "root t \<noteq> []"
  shows "path_lverts t (hd (root t)) = {}"
proof(cases "\<forall>x. sucs t \<noteq> {|x|}")
  case True
  then show ?thesis using path_lverts.simps(2)[of "sucs t" "root t"] by force
next
  case False
  then obtain t1 e1 where t1_def: "sucs t = {|(t1, e1)|}" by auto
  then have "path_lverts t (hd (root t)) =
    (if hd (root t) \<in> set (root t) then {} else set (root t) \<union> path_lverts t1 (hd (root t)))"
    using path_lverts.simps(1) dtree.collapse by metis
  then show ?thesis using assms by simp
qed

lemma path_lverts_subset_root_if_childhd:
  assumes "t1 \<in> fst ` fset (sucs t)" and "root t1 \<noteq> []"
  shows "path_lverts t (hd (root t1)) \<subseteq> set (root t)"
proof(cases "\<forall>x. sucs t \<noteq> {|x|}")
  case True
  then show ?thesis using path_lverts.simps(2)[of "sucs t" "root t"] by simp
next
  case False
  then obtain e1 where "sucs t = {|(t1, e1)|}" using assms(1) by fastforce
  then have "path_lverts t (hd (root t1)) =
    (if hd (root t1) \<in> set (root t) then {} else set (root t) \<union> path_lverts t1 (hd (root t1)))"
    using path_lverts.simps(1) dtree.collapse by metis
  then show ?thesis using path_lverts_empty_if_roothd[OF assms(2)] by auto
qed

lemma path_lverts_list_merge_supset_xs_notin:
  "\<forall>v \<in> fst ` set ys. a \<notin> set v
    \<Longrightarrow> path_lverts_list xs a \<subseteq> path_lverts_list (Sorting_Algorithms.merge cmp xs ys) a"
proof(induction xs ys taking: cmp rule: Sorting_Algorithms.merge.induct)
  case (3 x xs y ys)
  obtain v1 e1 where v1_def[simp]: "x = (v1,e1)" by force
  obtain v2 e2 where "y = (v2,e2)" by force
  then show ?case using 3 by (auto simp: path_lverts_list_def)
qed (auto simp: path_lverts_list_def)

lemma path_lverts_list_merge_supset_ys_notin:
  "\<forall>v \<in> fst ` set xs. a \<notin> set v
    \<Longrightarrow> path_lverts_list ys a \<subseteq> path_lverts_list (Sorting_Algorithms.merge cmp xs ys) a"
proof(induction xs ys taking: cmp rule: Sorting_Algorithms.merge.induct)
  case (3 x xs y ys)
  obtain v1 e1 where v1_def[simp]: "x = (v1,e1)" by force
  obtain v2 e2 where "y = (v2,e2)" by force
  then show ?case using 3 by (auto simp: path_lverts_list_def)
qed (auto simp: path_lverts_list_def)

lemma path_lverts_list_merge_supset_xs:
  "\<lbrakk>\<exists>v \<in> fst ` set xs. a \<in> set v; \<forall>v1 \<in> fst ` set xs. \<forall>v2 \<in> fst ` set ys. set v1 \<inter> set v2 = {}\<rbrakk>
    \<Longrightarrow> path_lverts_list xs a \<subseteq> path_lverts_list (Sorting_Algorithms.merge cmp xs ys) a"
  using path_lverts_list_merge_supset_xs_notin by fast

lemma path_lverts_list_merge_supset_ys:
  "\<lbrakk>\<exists>v \<in> fst ` set ys. a \<in> set v; \<forall>v1 \<in> fst ` set xs. \<forall>v2 \<in> fst ` set ys. set v1 \<inter> set v2 = {}\<rbrakk>
    \<Longrightarrow> path_lverts_list ys a \<subseteq> path_lverts_list (Sorting_Algorithms.merge cmp xs ys) a"
  using path_lverts_list_merge_supset_ys_notin by fast

lemma dom_children_if_all_singletons:
  "\<forall>(t1,e1) \<in> fset xs. dom_children (Node r {|(t1, e1)|}) T \<Longrightarrow> dom_children (Node r xs) T"
  by (auto simp: dom_children_def)

lemma dom_children_all_singletons:
  "\<lbrakk>dom_children (Node r xs) T; (t1,e1) \<in> fset xs\<rbrakk> \<Longrightarrow> dom_children (Node r {|(t1, e1)|}) T"
  by (auto simp: dom_children_def)

lemma dom_children_all_singletons':
  "\<lbrakk>dom_children (Node r xs) T; t1\<in> fst ` fset xs\<rbrakk> \<Longrightarrow> dom_children (Node r {|(t1, e1)|}) T"
  by (auto simp: dom_children_def)

lemma root_arc_if_dom_root_child_nempty:
  "\<lbrakk>dom_children (Node r xs) T; t1 \<in> fst ` fset xs; root t1 \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>set r. \<exists>y\<in>set (root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
  unfolding dom_children_def using dtree.set_sel(1)  path_lverts_empty_if_roothd[of t1]
  by fastforce

lemma root_arc_if_dom_root_child_wfdlverts:
  "\<lbrakk>dom_children (Node r xs) T; t1 \<in> fst ` fset xs; wf_dlverts t1\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>set r. \<exists>y\<in>set (root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
  using root_arc_if_dom_root_child_nempty dtree.set_sel(1)[of t1] empty_notin_wf_dlverts
  by fastforce

lemma root_arc_if_dom_wfdlverts:
  "\<lbrakk>dom_children (Node r xs) T; t1 \<in> fst ` fset xs; wf_dlverts (Node r xs)\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>set r. \<exists>y\<in>set (root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
  using root_arc_if_dom_root_child_wfdlverts[of r xs T t1] by fastforce

lemma children_deg1_sub_xs: "{(t,e). (t,e) \<in> fset xs \<and> max_deg t \<le> 1} \<subseteq> (fset xs)"
  by blast

lemma finite_children_deg1: "finite {(t,e). (t,e) \<in> fset xs \<and> max_deg t \<le> 1}"
  using children_deg1_sub_xs[of xs] by (simp add: finite_subset)

lemma finite_children_deg1': "{(t,e). (t,e) \<in> fset xs \<and> max_deg t \<le> 1} \<in> {A. finite A}"
  using finite_children_deg1 by blast

lemma children_deg1_fset_id[simp]: "fset (Abs_fset (children_deg1 xs)) = children_deg1 xs"
  using Abs_fset_inverse[OF finite_children_deg1'] by auto

lemma xs_sub_children_deg1: "\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1 \<Longrightarrow> (fset xs) \<subseteq> children_deg1 xs"
  by auto

lemma children_deg1_full:
  "\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1 \<Longrightarrow> (Abs_fset (children_deg1 xs)) = xs"
  using xs_sub_children_deg1[of xs] children_deg1_sub_xs[of xs] by (simp add: fset_inverse)

locale ranked_dtree_with_orig = ranked_dtree t rank cmp + directed_tree T root
  for t :: "('a list, 'b) dtree" and rank cost cmp and T :: "('a, 'b) pre_digraph" and root +
  assumes asi_rank: "asi rank root cost"
      and dom_mdeg_gt1:
    "\<lbrakk>is_subtree (Node r xs) t; t1 \<in> fst ` fset xs; max_deg (Node r xs) > 1\<rbrakk>
      \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
      and dom_sub_contr:
    "\<lbrakk>is_subtree (Node r xs) t; t1 \<in> fst ` fset xs;
      \<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) (Node r xs) \<and> rank (rev (Dtree.root t2)) < rank (rev v)\<rbrakk>
      \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
      and dom_contr:
    "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; rank (rev (Dtree.root t1)) < rank (rev r);
      max_deg (Node r {|(t1,e1)|}) = 1\<rbrakk>
      \<Longrightarrow> dom_children (Node r {|(t1,e1)|}) T"
      and dom_wedge:
    "\<lbrakk>is_subtree (Node r xs) t; fcard xs > 1\<rbrakk>
      \<Longrightarrow> dom_children (Node r (Abs_fset (children_deg1 xs))) T"
      and arc_in_dlverts:
    "\<lbrakk>is_subtree (Node r xs) t; x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts (Node r xs)"
      and verts_conform: "v \<in> dverts t \<Longrightarrow> seq_conform v"
      and verts_distinct: "v \<in> dverts t \<Longrightarrow> distinct v"
begin

lemma dom_contr':
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; rank (rev (Dtree.root t1)) < rank (rev r);
    max_deg (Node r {|(t1,e1)|}) \<le> 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r {|(t1,e1)|}) T"
  using dom_contr mdeg_ge_sub mdeg_singleton[of r t1] by (simp add: fcard_single_1)

lemma dom_self_contr:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; rank (rev (Dtree.root t1)) < rank (rev r)\<rbrakk>
    \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
  using dom_sub_contr by fastforce

lemma dom_wedge_full:
  "\<lbrakk>is_subtree (Node r xs) t; fcard xs > 1; \<forall>t \<in> fst ` fset xs. max_deg t \<le> 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r xs) T"
  using dom_wedge children_deg1_full by fastforce

lemma dom_wedge_singleton:
  "\<lbrakk>is_subtree (Node r xs) t; fcard xs > 1; t1 \<in> fst ` fset xs; max_deg t1 \<le> 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r {|(t1,e1)|}) T"
  using dom_children_all_singletons' dom_wedge children_deg1_fset_id by fastforce

lemma arc_to_dverts_in_subtree:
  "\<lbrakk>is_subtree (Node r xs) t; x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y; y \<in> set v; v \<in> dverts t\<rbrakk>
    \<Longrightarrow> v \<in> dverts (Node r xs)"
  using list_in_verts_if_lverts[OF arc_in_dlverts] dverts_same_if_set_wf[OF wf_lverts]
    dverts_subtree_subset by blast

lemma dlverts_arc_in_dlverts:
  "\<lbrakk>is_subtree t1 t; x \<rightarrow>\<^bsub>T\<^esub> y; x \<in> dlverts t1\<rbrakk> \<Longrightarrow> y \<in> dlverts t1"
proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "x \<in> set r")
    case True
    then show ?thesis using arc_in_dlverts Node.prems(1,2) by blast
  next
    case False
    then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "x \<in> dlverts t2"
      using Node.prems(3) by auto
    then have "is_subtree t2 (Node r xs)" using subtree_if_child
      by (metis image_iff prod.sel(1))
    then have "is_subtree t2 t" using Node.prems(1) subtree_trans by blast
    then show ?thesis using Node.IH Node.prems(2) t2_def by fastforce
  qed
qed

lemma dverts_arc_in_dlverts:
  "\<lbrakk>is_subtree t1 t; v1 \<in> dverts t1; x \<in> set v1; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts t1"
  using dlverts_arc_in_dlverts by (simp add: lverts_if_in_verts)

lemma dverts_arc_in_dverts:
  assumes "is_subtree t1 t"
      and "v1 \<in> dverts t1"
      and "x \<in> set v1"
      and "x \<rightarrow>\<^bsub>T\<^esub> y"
      and "y \<in> set v2"
      and "v2 \<in> dverts t"
    shows "v2 \<in> dverts t1"
proof -
  have "x \<in> dlverts t1" using assms(2,3) lverts_if_in_verts by fast
  then obtain v where v_def: "v\<in>dverts t1" "y \<in> set v"
    using list_in_verts_if_lverts[OF dlverts_arc_in_dlverts] assms(1-4) lverts_if_in_verts by blast
  then show ?thesis
    using dverts_same_if_set_wf[OF wf_lverts] assms(1,5,6) dverts_subtree_subset by blast
qed

lemma dlverts_reach1_in_dlverts:
  "\<lbrakk>x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; is_subtree t1 t; x \<in> dlverts t1\<rbrakk> \<Longrightarrow> y \<in> dlverts t1"
  by(induction x y rule: trancl.induct) (auto simp: dlverts_arc_in_dlverts)

lemma dlverts_reach_in_dlverts:
  "\<lbrakk>x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y; is_subtree t1 t; x \<in> dlverts t1\<rbrakk> \<Longrightarrow> y \<in> dlverts t1"
  using dlverts_reach1_in_dlverts by blast

lemma dverts_reach1_in_dlverts:
  "\<lbrakk>is_subtree t1 t; v1 \<in> dverts t1; x \<in> set v1; x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts t1"
  using dlverts_reach1_in_dlverts by (simp add: lverts_if_in_verts)

lemma dverts_reach_in_dlverts:
  "\<lbrakk>is_subtree t1 t; v1 \<in> dverts t1; x \<in> set v1; x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts t1"
  using list_in_verts_iff_lverts dverts_reach1_in_dlverts by (cases "x=y",fastforce,blast)

lemma dverts_reach1_in_dverts:
  "\<lbrakk>is_subtree t1 t; v1 \<in> dverts t1; x \<in> set v1; x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; y \<in> set v2; v2 \<in> dverts t\<rbrakk>
    \<Longrightarrow> v2 \<in> dverts t1"
  by (meson dverts_reach1_in_dlverts dverts_arc_in_dverts list_in_verts_if_lverts tranclE)

lemma dverts_same_if_set_subtree:
  "\<lbrakk>is_subtree t1 t; v1 \<in> dverts t1; x \<in> set v1; x \<in> set v2; v2 \<in> dverts t\<rbrakk> \<Longrightarrow> v1 = v2"
  using dverts_same_if_set_wf[OF wf_lverts] dverts_subtree_subset by blast

lemma dverts_reach_in_dverts:
  "\<lbrakk>is_subtree t1 t; v1 \<in> dverts t1; x \<in> set v1; x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y; y \<in> set v2; v2 \<in> dverts t\<rbrakk>
    \<Longrightarrow> v2 \<in> dverts t1"
  using dverts_same_if_set_subtree dverts_reach1_in_dverts by blast

lemma dverts_reach1_in_dverts_root:
  "\<lbrakk>is_subtree t1 t; v \<in> dverts t; \<exists>x\<in>set (Dtree.root t1). \<exists>y\<in>set v. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> v \<in> dverts t1"
  using dverts_reach1_in_dverts dtree.set_sel(1) by blast

lemma dverts_reach1_in_dverts_r:
  "\<lbrakk>is_subtree (Node r xs) t; v \<in> dverts t; \<exists>x\<in>set r. \<exists>y\<in>set v. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> v \<in> dverts (Node r xs)"
  using dverts_reach1_in_dverts[of "Node r xs"] by (auto intro: dtree.set_intros(1))

lemma dom_mdeg_gt1_subtree:
  "\<lbrakk>is_subtree tn t; is_subtree (Node r xs) tn; t1 \<in> fst ` fset xs; max_deg (Node r xs) > 1\<rbrakk>
    \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
  using dom_mdeg_gt1 subtree_trans by blast

lemma dom_sub_contr_subtree:
  "\<lbrakk>is_subtree tn t; is_subtree (Node r xs) tn; t1 \<in> fst ` fset xs;
    \<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) (Node r xs) \<and> rank (rev (Dtree.root t2)) < rank (rev v)\<rbrakk>
    \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
  using dom_sub_contr subtree_trans by blast

lemma dom_contr_subtree:
  "\<lbrakk>is_subtree tn t; is_subtree (Node r {|(t1,e1)|}) tn; rank (rev (Dtree.root t1)) < rank (rev r);
    max_deg (Node r {|(t1,e1)|}) = 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r {|(t1,e1)|}) T"
  using dom_contr subtree_trans by blast

lemma dom_wedge_subtree:
  "\<lbrakk>is_subtree tn t; is_subtree (Node r xs) tn; fcard xs > 1\<rbrakk>
      \<Longrightarrow> dom_children (Node r (Abs_fset (children_deg1 xs))) T"
  using dom_wedge subtree_trans by blast

corollary dom_wedge_subtree':
  "is_subtree tn t \<Longrightarrow>\<forall>r xs. is_subtree (Node r xs) tn \<longrightarrow> fcard xs > 1
    \<longrightarrow> dom_children (Node r (Abs_fset {(t, e). (t, e) \<in> fset xs \<and> max_deg t \<le> Suc 0})) T"
  by (auto simp only: dom_wedge_subtree One_nat_def[symmetric])

lemma dom_wedge_full_subtree:
  "\<lbrakk>is_subtree tn t; is_subtree (Node r xs) tn; fcard xs > 1; \<forall>t \<in> fst ` fset xs. max_deg t \<le> 1\<rbrakk>
      \<Longrightarrow> dom_children (Node r xs) T"
  using dom_wedge_full subtree_trans by fast

lemma arc_in_dlverts_subtree:
  "\<lbrakk>is_subtree tn t; is_subtree (Node r xs) tn; x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts (Node r xs)"
  using arc_in_dlverts subtree_trans by blast

corollary arc_in_dlverts_subtree':
  "is_subtree tn t \<Longrightarrow> \<forall>r xs. is_subtree (Node r xs) tn \<longrightarrow> (\<forall>x. x \<in> set r
    \<longrightarrow> (\<forall>y. x \<rightarrow>\<^bsub>T\<^esub> y \<longrightarrow> y \<in> set r \<or> (\<exists>c\<in>fset xs. y \<in> dlverts (fst c))))"
  using arc_in_dlverts_subtree by simp

lemma verts_conform_subtree: "\<lbrakk>is_subtree tn t; v \<in> dverts tn\<rbrakk> \<Longrightarrow> seq_conform v"
  using verts_conform dverts_subtree_subset by blast

lemma verts_distinct_subtree: "\<lbrakk>is_subtree tn t; v \<in> dverts tn\<rbrakk> \<Longrightarrow> distinct v"
  using verts_distinct dverts_subtree_subset by blast

lemma ranked_dtree_orig_subtree: "is_subtree x t \<Longrightarrow> ranked_dtree_with_orig x rank cost cmp T root"
  unfolding ranked_dtree_with_orig_def ranked_dtree_with_orig_axioms_def
  by (simp add: ranked_dtree_subtree directed_tree_axioms dom_mdeg_gt1_subtree dom_contr_subtree
      dom_sub_contr_subtree dom_wedge_subtree' arc_in_dlverts_subtree'
      verts_conform_subtree verts_distinct_subtree asi_rank)

corollary ranked_dtree_orig_rec:
  "\<lbrakk>Node r xs = t; (x,e) \<in> fset xs\<rbrakk> \<Longrightarrow> ranked_dtree_with_orig x rank cost cmp T root"
  using ranked_dtree_orig_subtree[of x] subtree_if_child[of x xs] by force

lemma child_disjoint_root:
  "\<lbrakk>is_subtree (Node r xs) t; t1 \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> set r \<inter> set (Dtree.root t1) = {}"
  using wf_dlverts_subtree[OF wf_lverts] dlverts_eq_dverts_union dtree.set_sel(1) by fastforce

lemma distint_verts_subtree:
  assumes "is_subtree (Node r xs) t" and "t1 \<in> fst ` fset xs"
  shows "distinct (r @ Dtree.root t1)"
proof -
  have "(Dtree.root t1) \<in> dverts t" using dtree.set_sel(1) assms dverts_subtree_subset by fastforce
  then show ?thesis
    using verts_distinct assms(1) dverts_subtree_subset child_disjoint_root[OF assms] by force
qed

corollary distint_verts_singleton_subtree:
  "is_subtree (Node r {|(t1,e1)|}) t \<Longrightarrow> distinct (r @ Dtree.root t1)"
  using distint_verts_subtree by simp

lemma dom_between_child_roots:
  assumes "is_subtree (Node r {|(t1,e1)|}) t" and "rank (rev (Dtree.root t1)) < rank (rev r)"
  shows "\<exists>x\<in>set r. \<exists>y\<in>set (Dtree.root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
  using dom_self_contr[OF assms] wf_dlverts_subtree[OF wf_lverts assms(1)]
    hd_in_set[of "Dtree.root t1"] dtree.set_sel(1)[of t1] empty_notin_wf_dlverts[of t1] by fastforce

lemma contr_before:
  assumes "is_subtree (Node r {|(t1,e1)|}) t" and "rank (rev (Dtree.root t1)) < rank (rev r)"
  shows "before r (Dtree.root t1)"
proof -
  have "(Dtree.root t1) \<in> dverts t" using dtree.set_sel(1) assms(1) dverts_subtree_subset by fastforce
  then have "seq_conform (Dtree.root t1)" using verts_conform by simp
  moreover have "seq_conform r" using verts_conform assms(1) dverts_subtree_subset by force
  ultimately show ?thesis
    using before_def dom_between_child_roots[OF assms] child_disjoint_root[OF assms(1)] by auto
qed

lemma contr_forward:
  assumes "is_subtree (Node r {|(t1,e1)|}) t" and "rank (rev (Dtree.root t1)) < rank (rev r)"
  shows "forward (r@Dtree.root t1)"
proof -
  have "(Dtree.root t1) \<in> dverts t" using dtree.set_sel(1) assms(1) dverts_subtree_subset by fastforce
  then have "seq_conform (Dtree.root t1)" using verts_conform by simp
  moreover have "seq_conform r" using verts_conform assms(1) dverts_subtree_subset by force
  ultimately show ?thesis
    using seq_conform_def forward_arcs_alt dom_self_contr assms forward_app by simp
qed

lemma contr_seq_conform:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; rank (rev (Dtree.root t1)) < rank (rev r)\<rbrakk>
    \<Longrightarrow> seq_conform (r @ Dtree.root t1)"
  using seq_conform_if_before contr_before by simp

lemma verts_forward: "\<forall>v \<in> dverts t. forward v"
  using seq_conform_alt verts_conform by simp

lemma dverts_reachable1_if_dom_children_aux_root:
  assumes "\<forall>v\<in>dverts (Node r xs). \<exists>x\<in>set r0 \<union> X \<union> path_lverts (Node r xs) (hd v). x \<rightarrow>\<^bsub>T\<^esub> hd v"
      and "\<forall>y\<in>X. \<exists>x\<in>set r0. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
      and "forward r"
    shows "\<forall>y\<in>set r. \<exists>x\<in>set r0. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof(cases "r = []")
  case False
  then have "path_lverts (Node r xs) (hd r) = {}"
    using path_lverts_empty_if_roothd[of "Node r xs"] by simp
  then obtain x where x_def: "x\<in>set r0 \<union> X" "x \<rightarrow>\<^bsub>T\<^esub> hd r" using assms(1) by auto
  then have "hd r \<in> verts T" using adj_in_verts(2) by auto
  then have "\<forall>y\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
    using hd_reach_all_forward x_def(2) assms(3) reachable1_reachable_trans by blast
  moreover obtain y where "y \<in> set r0" "y \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" using assms(2) x_def by auto
  ultimately show ?thesis using reachable_reachable1_trans by blast
qed(simp)

lemma dverts_reachable1_if_dom_children_aux:
  "\<lbrakk>\<forall>v\<in>dverts t1. \<exists>x\<in>set r0 \<union> X \<union> path_lverts t1 (hd v). x \<rightarrow>\<^bsub>T\<^esub> hd v;
     \<forall>y\<in>X. \<exists>x\<in>set r0. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; \<forall>v\<in>dverts t1. forward v; v\<in>dverts t1\<rbrakk>
    \<Longrightarrow> \<forall>y\<in>set v. \<exists>x\<in>set r0. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof(induction t1 arbitrary: X rule: dtree_to_list.induct)
  case (1 r t e)
  have r_reachable1: "\<forall>y\<in>set r. \<exists>x\<in>set r0. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
   using dverts_reachable1_if_dom_children_aux_root[OF "1.prems"(1,2)] "1.prems"(3) by simp
  then show ?case
  proof(cases "r = v")
    case True
    then show ?thesis using r_reachable1 by simp
  next
    case False
    have r_reach1: "\<forall>y\<in>set r \<union> X. \<exists>x\<in>set r0. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y" using "1.prems"(2) r_reachable1 by blast
    have "\<forall>x. path_lverts (Node r {|(t, e)|}) x \<subseteq> set r \<union> path_lverts t x"
      by simp
    then have 0: "\<forall>v\<in>dverts t. \<exists>x\<in>set r0 \<union> (set r \<union> X) \<union> (path_lverts t (hd v)). x \<rightarrow>\<^bsub>T\<^esub> hd v"
      using "1.prems"(1) by fastforce
    then show ?thesis using "1.IH"[OF 0 r_reach1] "1.prems"(3,4) False by simp
  qed
next
  case (2 xs r)
  then show ?case
  proof(cases "\<exists>x\<in>set r0 \<union> X. x \<rightarrow>\<^bsub>T\<^esub> hd v")
    case True
    then obtain x where x_def: "x\<in>set r0 \<union> X" "x \<rightarrow>\<^bsub>T\<^esub> hd v" using "2.prems"(1,4) by blast
    then have "hd v \<in> verts T" using x_def(2) adj_in_verts(2) by auto
    moreover have "forward v" using "2.prems"(3,4) by blast
    ultimately have v_reach1: "\<forall>y\<in>set v. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
      using hd_reach_all_forward x_def(2) reachable1_reachable_trans by blast
    then show ?thesis using "2.prems"(2) x_def(1) reachable_reachable1_trans by blast
  next
    case False
    then obtain x where x_def: "x \<in> path_lverts (Node r xs) (hd v)" "x \<rightarrow>\<^bsub>T\<^esub> hd v"
      using "2.prems"(1,4) by blast
    then have "x \<in> set r" using path_lverts.simps(2)[OF "2.hyps"] empty_iff by metis
    then obtain x' where x'_def: "x'\<in>set r0" "x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> x"
      using dverts_reachable1_if_dom_children_aux_root[OF "2.prems"(1,2)] "2.prems"(3) by auto
    then have x'_v: "x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> hd v" using x_def(2) by simp
    then have "hd v \<in> verts T" using x_def(2) adj_in_verts(2) by auto
    moreover have "forward v" using "2.prems"(3,4) by blast
    ultimately have v_reach1: "\<forall>y\<in>set v. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
      using hd_reach_all_forward x'_v reachable1_reachable_trans by blast
    then show ?thesis using x'_def(1) by blast
  qed
qed

lemma dlverts_reachable1_if_dom_children_aux:
  "\<lbrakk>\<forall>v\<in>dverts t1. \<exists>x\<in>set r \<union> X \<union> path_lverts t1 (hd v). x \<rightarrow>\<^bsub>T\<^esub> hd v;
     \<forall>y\<in>X. \<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; \<forall>v\<in>dverts t1. forward v; y\<in>dlverts t1\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
  using dverts_reachable1_if_dom_children_aux list_in_verts_iff_lverts[of y t1] by blast

lemma dverts_reachable1_if_dom_children:
  assumes "dom_children t1 T" and "v \<in> dverts t1" and "v \<noteq> Dtree.root t1" and "\<forall>v\<in>dverts t1. forward v"
  shows "\<forall>y\<in>set v. \<exists>x\<in>set (Dtree.root t1). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof -
  obtain t2 where t2_def: "t2 \<in> fst ` fset (sucs t1)" "v \<in> dverts t2"
    using assms(2,3) dverts_root_or_suc by force
  then have 0: "\<forall>v\<in>dverts t2. \<exists>x\<in>set (Dtree.root t1) \<union> {} \<union> path_lverts t2 (hd v). x \<rightarrow>\<^bsub>T\<^esub> hd v"
    using assms(1) unfolding dom_children_def by blast
  moreover have "\<forall>v\<in>dverts t2. forward v" using assms(4) t2_def(1) dverts_suc_subseteq by blast
  ultimately show ?thesis using dverts_reachable1_if_dom_children_aux t2_def(2) by blast
qed

lemma subtree_dverts_reachable1_if_mdeg_gt1:
  "\<lbrakk>is_subtree t1 t; max_deg t1 > 1; v \<in> dverts t1; v \<noteq> Dtree.root t1\<rbrakk>
    \<Longrightarrow> \<forall>y\<in>set v. \<exists>x\<in>set (Dtree.root t1). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof(induction t1)
  case (Node r xs)
  then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "v \<in> dverts t2" by auto
  then obtain x where x_def: "x\<in>set r" "x \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t2)"
    using dom_mdeg_gt1 Node.prems(1,2) by fastforce
  then have t2_T: "hd (Dtree.root t2) \<in> verts T" using adj_in_verts(2) by simp
  have "is_subtree t2 (Node r xs)" using subtree_if_child[of t2 xs r] t2_def(1) by force
  then have subt2: "is_subtree t2 t" using subtree_trans Node.prems(1) by blast
  have "Dtree.root t2 \<in> dverts t"
    using subt2 dverts_subtree_subset by (fastforce simp: dtree.set_sel(1))
  then have fwd_t2: "forward (Dtree.root t2)" by (simp add: verts_forward)
  then have t2_reach1: "\<forall>y\<in>set (Dtree.root t2). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
    using hd_reach_all_forward[OF t2_T fwd_t2] x_def(2) reachable1_reachable_trans by blast
  then consider "Dtree.root t2 = v" | "Dtree.root t2 \<noteq> v" "max_deg t2 > 1" | "Dtree.root t2 \<noteq> v" "max_deg t2 \<le> 1"
    by fastforce
  then show ?case
  proof(cases)
    case 1
    then show ?thesis using t2_reach1 x_def(1) by auto
  next
    case 2
    then have "\<forall>y\<in>set v. \<exists>x\<in>set (Dtree.root t2). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y" using Node.IH subt2 t2_def by simp
    then show ?thesis
      using t2_reach1 x_def(1) reachable1_reachable reachable1_reachable_trans
      unfolding dtree.sel(1) by blast
  next
    case 3
    then have "fcard xs > 1" using Node.prems(2) t2_def(1) fcard_gt1_if_mdeg_gt_child1 by fastforce
    then have dom: "dom_children (Node r {|(t2,e2)|}) T"
      using dom_wedge_singleton[OF Node.prems(1)] t2_def(1) 3(2) by fastforce
    have "\<forall>v \<in> dverts (Node r xs). forward v"
      using Node.prems(1) seq_conform_alt verts_conform_subtree by blast
    then have "\<forall>v \<in> dverts (Node r {|(t2, e2)|}). forward v" using t2_def(1) by simp
    then show ?thesis
      using dverts_reachable1_if_dom_children[OF dom] t2_def(2) Node.prems(4)
      unfolding dtree.sel(1) by simp
  qed
qed

lemma subtree_dverts_reachable1_if_mdeg_gt1_singleton:
  assumes "is_subtree (Node r {|(t1,e1)|}) t"
      and "max_deg (Node r {|(t1,e1)|}) > 1"
      and "v \<in> dverts t1"
      and "v \<noteq> Dtree.root t1"
    shows "\<forall>y\<in>set v. \<exists>x\<in>set (Dtree.root t1). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof -
  have "is_subtree t1 t" using subtree_trans[OF subtree_if_child assms(1)] by simp
  then show ?thesis
    using assms(2-4) mdeg_eq_child_if_singleton_gt1[OF assms(2)]
      subtree_dverts_reachable1_if_mdeg_gt1 by simp
qed

lemma subtree_dverts_reachable1_if_mdeg_le1_subcontr:
  "\<lbrakk>is_subtree t1 t; max_deg t1 \<le> 1; is_subtree (Node v2 {|(t2,e2)|}) t1;
    rank (rev (Dtree.root t2)) < rank (rev v2); v \<in> dverts t1; v \<noteq> Dtree.root t1\<rbrakk>
    \<Longrightarrow> \<forall>y\<in>set v. \<exists>x\<in>set (Dtree.root t1). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "Node v2 {|(t2,e2)|} = Node r xs")
    case True
    then have "dom_children (Node r xs) T" using dom_contr' Node.prems(1,2,4) by blast
    moreover have "\<forall>v \<in> dverts (Node r xs). forward v"
      using Node.prems(1) seq_conform_alt verts_conform_subtree by blast
    ultimately show ?thesis using dverts_reachable1_if_dom_children Node.prems(5,6) by blast
  next
    case False
    then obtain t3 e3 where t3_def: "(t3,e3) \<in> fset xs" "is_subtree (Node v2 {|(t2,e2)|}) t3"
      using Node.prems(3) by auto
    then have t3_xs: "xs = {|(t3,e3)|}"
      using Node.prems(2) by (simp add: singleton_if_mdeg_le1_elem)
    then have v_t3: "v \<in> dverts t3" using Node.prems(5,6) by simp
    then have t3_dom: "\<exists>x\<in>set r. x \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t3)"
      using dom_sub_contr Node.prems(1,3,4) t3_xs by fastforce
    then have t3_T: "hd (Dtree.root t3) \<in> verts T" using adj_in_verts(2) by blast
    have "is_subtree t3 (Node r xs)" using subtree_if_child[of t3 xs] t3_xs by simp
    then have sub_t3: "is_subtree t3 t" using subtree_trans Node.prems(1) by blast
    then have "Dtree.root t3 \<in> dverts t"
      using dverts_subtree_subset by (fastforce simp: dtree.set_sel(1))
    then have "forward (Dtree.root t3)" by (simp add: verts_forward)
    then have t3_reach1: "\<exists>x\<in>set r. \<forall>y\<in>set(Dtree.root t3). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
      using hd_reach_all_forward[OF t3_T] t3_dom reachable1_reachable_trans by blast
    show ?thesis
    proof(cases "v = Dtree.root t3")
      case True
      then show ?thesis using t3_reach1 by auto
    next
      case False
      moreover have "max_deg t3 \<le> 1" using Node.prems(2) t3_def(1) mdeg_ge_child by fastforce
      ultimately have "\<forall>y\<in>set v. \<exists>x\<in>set (Dtree.root t3). x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
        using Node.IH sub_t3 t3_def Node.prems(4) v_t3 by simp
      then show ?thesis
        using t3_reach1 reachable1_reachable_trans reachable1_reachable unfolding dtree.sel(1)
        by blast
    qed
  qed
qed

lemma subtree_y_reach_if_mdeg_gt1_notroot_reach:
  assumes "is_subtree (Node r {|(t1,e1)|}) t"
      and "max_deg (Node r {|(t1,e1)|}) > 1"
      and "v \<noteq> r"
      and "v \<in> dverts t"
      and "v \<noteq> Dtree.root t1"
      and "y \<in> set v"
      and "\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
    shows "\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof -
  have "v \<in> dverts (Node r {|(t1,e1)|})" using dverts_reach1_in_dverts_r assms(1,4,6,7) by blast
  then show ?thesis using subtree_dverts_reachable1_if_mdeg_gt1_singleton assms(1-3,5,6) by simp
qed

lemma subtree_eqroot_if_mdeg_gt1_reach:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; max_deg (Node r {|(t1,e1)|}) > 1; v \<in> dverts t;
    \<exists>y\<in>set v. \<not>(\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); v \<noteq> r\<rbrakk>
    \<Longrightarrow> Dtree.root t1 = v"
  using subtree_y_reach_if_mdeg_gt1_notroot_reach by blast

lemma subtree_rank_ge_if_mdeg_gt1_reach:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; max_deg (Node r {|(t1,e1)|}) > 1; v \<in> dverts t;
    \<exists>y\<in>set v. \<not>(\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y); v \<noteq> r\<rbrakk>
    \<Longrightarrow> rank (rev (Dtree.root t1)) \<le> rank (rev v)"
  using subtree_eqroot_if_mdeg_gt1_reach by blast

lemma subtree_y_reach_if_mdeg_le1_notroot_subcontr:
  assumes "is_subtree (Node r {|(t1,e1)|}) t"
      and "max_deg (Node r {|(t1,e1)|}) \<le> 1"
      and "is_subtree (Node v2 {|(t2,e2)|}) t1"
      and "rank (rev (Dtree.root t2)) < rank (rev v2)"
      and "v \<noteq> r"
      and "v \<in> dverts t"
      and "v \<noteq> Dtree.root t1"
      and "y \<in> set v"
      and "\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
    shows "\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
proof -
  have 0: "is_subtree t1 (Node r {|(t1,e1)|})" using subtree_if_child[of t1 "{|(t1,e1)|}"] by simp
  then have subt1: "is_subtree t1 t" using assms(1) subtree_trans by blast
  have "v \<in> dverts (Node r {|(t1,e1)|})"
    using dverts_reach1_in_dverts_r assms(1,6,8,9) by blast
  then have "v \<in> dverts t1" using assms(5) by simp
  moreover have "max_deg t1 \<le> 1" using assms(2) mdeg_ge_sub[OF 0] by simp
  ultimately show ?thesis
    using subtree_dverts_reachable1_if_mdeg_le1_subcontr[OF subt1] assms(3,4,7,8) by blast
qed

lemma rank_ge_if_mdeg_le1_dvert_nocontr:
  assumes "max_deg t1 \<le> 1"
      and "\<nexists>v2 t2 e2. is_subtree (Node v2 {|(t2,e2)|}) t1 \<and> rank (rev (Dtree.root t2)) < rank (rev v2)"
      and "v \<in> dverts t1"
    shows "rank (rev (Dtree.root t1)) \<le> rank (rev v)"
using assms proof(induction t1)
  case (Node r xs)
  then show ?case
  proof(cases "v = r")
    case False
    then obtain t2 e2 where t2_def: "xs = {|(t2,e2)|}" "v \<in> dverts t2"
      using Node.prems(1,3) singleton_if_mdeg_le1_elem by fastforce
    have "max_deg t2 \<le> 1" using Node.prems(1) mdeg_ge_child[of t2 e2 xs] t2_def(1) by simp
    then have "rank (rev (Dtree.root t2)) \<le> rank (rev v)"
      using Node.IH t2_def Node.prems(2) by fastforce
    then show ?thesis using Node.prems(2) t2_def(1) by fastforce
  qed(simp)
qed

lemma subtree_rank_ge_if_mdeg_le1_nocontr:
  assumes "is_subtree (Node r {|(t1,e1)|}) t"
      and "max_deg (Node r {|(t1,e1)|}) \<le> 1"
      and "\<nexists>v2 t2 e2. is_subtree (Node v2 {|(t2,e2)|}) t1 \<and> rank (rev (Dtree.root t2)) < rank (rev v2)"
      and "v \<noteq> r"
      and "v \<in> dverts t"
      and "y \<in> set v"
      and "\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y"
    shows "rank (rev (Dtree.root t1)) \<le> rank (rev v)"
proof -
  have 0: "is_subtree t1 (Node r {|(t1,e1)|})" using subtree_if_child[of t1 "{|(t1,e1)|}"] by simp
  then have 0: "max_deg t1 \<le> 1" using assms(2) mdeg_ge_sub[OF 0] by simp
  have "v \<in> dverts (Node r {|(t1,e1)|})" using dverts_reach1_in_dverts_r assms(1,5-7) by blast
  then have "v \<in> dverts t1" using assms(4) by simp
  then show ?thesis using rank_ge_if_mdeg_le1_dvert_nocontr 0 assms(3) by blast
qed

lemma subtree_rank_ge_if_mdeg_le1':
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; max_deg (Node r {|(t1,e1)|}) \<le> 1; v \<noteq> r;
    v \<in> dverts t; y \<in> set v; \<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y; \<not>(\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)\<rbrakk>
    \<Longrightarrow> rank (rev (Dtree.root t1)) \<le> rank (rev v)"
  using subtree_y_reach_if_mdeg_le1_notroot_subcontr subtree_rank_ge_if_mdeg_le1_nocontr
  apply(cases "\<exists>v2 t2 e2. is_subtree (Node v2 {|(t2,e2)|}) t1 \<and> rank (rev (Dtree.root t2))<rank (rev v2)")
  by blast+

lemma subtree_rank_ge_if_mdeg_le1:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; max_deg (Node r {|(t1,e1)|}) \<le> 1; v \<noteq> r;
    v \<in> dverts t; \<exists>y \<in> set v. \<not>(\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)\<rbrakk>
    \<Longrightarrow> rank (rev (Dtree.root t1)) \<le> rank (rev v)"
  using subtree_y_reach_if_mdeg_le1_notroot_subcontr subtree_rank_ge_if_mdeg_le1_nocontr
  apply(cases "\<exists>v2 t2 e2. is_subtree (Node v2 {|(t2,e2)|}) t1 \<and> rank (rev (Dtree.root t2))<rank (rev v2)")
  by blast+

lemma subtree_rank_ge_if_reach:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) t; v \<noteq> r; v \<in> dverts t;
    \<exists>y \<in> set v. \<not>(\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)\<rbrakk>
    \<Longrightarrow> rank (rev (Dtree.root t1)) \<le> rank (rev v)"
  using subtree_rank_ge_if_mdeg_le1 subtree_rank_ge_if_mdeg_gt1_reach
  by (cases "max_deg (Node r {|(t1,e1)|}) \<le> 1") (auto simp del: max_deg.simps)

lemma subtree_rank_ge_if_reach':
  "is_subtree (Node r {|(t1,e1)|}) t \<Longrightarrow> \<forall>v \<in> dverts t.
    (\<exists>y\<in>set v. \<not> (\<exists>x'\<in>set (Dtree.root t1). x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set r. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> v \<noteq> r)
      \<longrightarrow> rank (rev (Dtree.root t1)) \<le> rank (rev v)"
  using subtree_rank_ge_if_reach by blast

subsubsection \<open>Normalizing preserves Arc Invariants\<close>

lemma normalize1_mdeg_le: "max_deg (normalize1 t1) \<le> max_deg t1"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    then show ?thesis using mdeg_child_sucs_le by fastforce
  next
    case False
    then have "max_deg (normalize1 (Node r {|(t, e)|}))
            = max (max_deg (normalize1 t)) (fcard {|(normalize1 t, e)|})"
      using mdeg_singleton by force
    then show ?thesis using mdeg_singleton[of r t] 1 False by (simp add: fcard_single_1)
  qed
next
  case (2 xs r)
  then have 0: "\<forall>(t,e) \<in> fset xs. max_deg (normalize1 t) \<le> max_deg t" by fastforce
  have "max_deg (normalize1 (Node r xs)) = max_deg (Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs))"
    using "2.hyps" by simp
  then show ?case using mdeg_img_le'[OF 0] by simp
qed

lemma normalize1_mdeg_eq:
  "wf_darcs t1
    \<Longrightarrow> max_deg (normalize1 t1) = max_deg t1 \<or> (max_deg (normalize1 t1) = 0 \<and> max_deg t1 = 1)"
proof(induction t1 rule: normalize1.induct)
  case ind: (1 r t e)
  then have 0: "max_deg (Node r {|(t, e)|}) \<ge> 1"
    using mdeg_ge_fcard[of "{|(t, e)|}"] by (simp add: fcard_single_1)
  then consider "rank (rev (Dtree.root t)) < rank (rev r)"
    | "\<not>rank (rev (Dtree.root t)) < rank (rev r)" "max_deg (normalize1 t) \<le> 1"
    | "\<not>rank (rev (Dtree.root t)) < rank (rev r)" "max_deg (normalize1 t) > 1" by linarith
  then show ?case
  proof(cases)
    case 1
    then show ?thesis
      using mdeg_singleton mdeg_root fcard_single_1
      by (metis max_def nle_le dtree.exhaust_sel leI less_one normalize1.simps(1))
  next
    case 2
    then have "max_deg (normalize1 (Node r {|(t, e)|})) = 1"
      using mdeg_singleton[of r "normalize1 t"] by (auto simp: fcard_single_1)
    moreover have "max_deg (Node r {|(t, e)|}) = 1 "
      using mdeg_singleton[of r t] ind 2
      by (auto simp: fcard_single_1 wf_darcs_iff_darcs')
    ultimately show ?thesis by simp
  next
    case 3
    then show ?thesis
      using mdeg_singleton[of r t] mdeg_singleton[of r "normalize1 t"] ind
      by (auto simp: fcard_single_1)
  qed
next
  case ind: (2 xs r)
  then consider "max_deg (Node r xs) \<le> 1"
    | "max_deg (Node r xs) > 1" "max_deg (Node r xs) = fcard xs"
    | "max_deg (Node r xs) > 1" "fcard xs < max_deg (Node r xs)"
    using mdeg_ge_fcard[of xs] by fastforce
  then show ?case
  proof(cases)
    case 1
    then show ?thesis using normalize1_mdeg_le[of "Node r xs"] by fastforce
  next
    case 2
    then have "max_deg (Node r xs) \<le> max_deg (normalize1 (Node r xs))"
      using mdeg_ge_fcard[of "(\<lambda>(t, e). (normalize1 t, e)) |`| xs"] ind
      by (simp add: fcard_normalize_img_if_disjoint wf_darcs_iff_darcs')
    then show ?thesis using normalize1_mdeg_le[of "Node r xs"] by simp
  next
    case 3
    then obtain t e where t_def: "(t,e) \<in> fset xs" "max_deg (Node r xs) = max_deg t"
      using mdeg_child_if_gt_fcard by fastforce
    have "max_deg (normalize1 t) \<le> max_deg (Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs))"
      using mdeg_ge_child[of "normalize1 t" e "(\<lambda>(t,e). (normalize1 t,e)) |`| xs" r] t_def(1)
      by fastforce
    then have "max_deg (Node r xs) \<le> max_deg (normalize1 (Node r xs))"
      using ind.hyps ind.IH[OF t_def(1) refl] ind.prems 3(1) t_def
      by (fastforce simp: wf_darcs_iff_darcs')
    then show ?thesis using normalize1_mdeg_le[of "Node r xs"] by simp
  qed
qed

lemma normalize1_mdeg_eq':
  "wf_dlverts t1
    \<Longrightarrow> max_deg (normalize1 t1) = max_deg t1 \<or> (max_deg (normalize1 t1) = 0 \<and> max_deg t1 = 1)"
proof(induction t1 rule: normalize1.induct)
  case ind: (1 r t e)
  then have 0: "max_deg (Node r {|(t, e)|}) \<ge> 1"
    using mdeg_ge_fcard[of "{|(t, e)|}"] by (simp add: fcard_single_1)
  then consider "rank (rev (Dtree.root t)) < rank (rev r)"
    | "\<not>rank (rev (Dtree.root t)) < rank (rev r)" "max_deg (normalize1 t) \<le> 1"
    | "\<not>rank (rev (Dtree.root t)) < rank (rev r)" "max_deg (normalize1 t) > 1" by linarith
  then show ?case
  proof(cases)
    case 1
    then show ?thesis
      using mdeg_singleton[of r t] mdeg_root[of "Dtree.root t" "sucs t"]
      by (auto simp: fcard_single_1 simp del: max_deg.simps)
  next
    case 2
    then have "max_deg (normalize1 (Node r {|(t, e)|})) = 1"
      using mdeg_singleton[of r "normalize1 t"] by (auto simp: fcard_single_1)
    moreover have "max_deg (Node r {|(t, e)|}) = 1 "
      using mdeg_singleton[of r t] ind 2 by (auto simp: fcard_single_1)
    ultimately show ?thesis by simp
  next
    case 3
    then show ?thesis
      using mdeg_singleton[of r t] mdeg_singleton[of r "normalize1 t"] ind
      by (auto simp: fcard_single_1)
  qed
next
  case ind: (2 xs r)
   consider "max_deg (Node r xs) \<le> 1"
    | "max_deg (Node r xs) > 1" "max_deg (Node r xs) = fcard xs"
    | "max_deg (Node r xs) > 1" "fcard xs < max_deg (Node r xs)"
    using mdeg_ge_fcard[of xs] by fastforce
  then show ?case
  proof(cases)
    case 1
    then show ?thesis using normalize1_mdeg_le[of "Node r xs"] by (auto simp del: max_deg.simps)
  next
    case 2
    have 0: "\<forall>(t, e)\<in>fset xs. dlverts t \<noteq> {}" using dlverts_nempty_if_wf ind.prems by auto
    then have "max_deg (Node r xs) \<le> max_deg (normalize1 (Node r xs))"
      using mdeg_ge_fcard[of "(\<lambda>(t, e). (normalize1 t, e)) |`| xs"] ind 2
      by (simp add: fcard_normalize_img_if_disjoint_lverts)
    then show ?thesis using normalize1_mdeg_le[of "Node r xs"] by simp
  next
    case 3
    then obtain t e where t_def: "(t,e) \<in> fset xs" "max_deg (Node r xs) = max_deg t"
      using mdeg_child_if_gt_fcard by fastforce
    have "max_deg (normalize1 t) \<le> max_deg (Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs))"
      using mdeg_ge_child[of "normalize1 t" e "(\<lambda>(t,e). (normalize1 t,e)) |`| xs"] t_def(1)
      by (force simp del: max_deg.simps)
    then have "max_deg (Node r xs) \<le> max_deg (normalize1 (Node r xs))"
      using ind 3(1) t_def by (fastforce simp del: max_deg.simps)
    then show ?thesis using normalize1_mdeg_le[of "Node r xs"] by simp
  qed
qed

lemma normalize1_dom_mdeg_gt1:
  "\<lbrakk>is_subtree (Node r xs) (normalize1 t); t1 \<in> fst ` fset xs; max_deg (Node r xs) > 1\<rbrakk>
    \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case (1 r1 t e)
  then interpret R: ranked_dtree_with_orig "Node r1 {|(t,e)|}" by blast
  have sub_t: "is_subtree t (Node r1 {|(t,e)|})" using subtree_if_child[of t "{|(t,e)|}"] by simp
  show ?case
  proof(cases "Node r xs = normalize1 (Node r1 {|(t,e)|})")
    case eq: True
    then have 0: "max_deg (Node r1 {|(t,e)|}) > 1"
      by (metis normalize1_mdeg_le "1.prems"(3) less_le_trans)
    then have max_t: "max_deg t > 1" by (metis dtree.exhaust_sel mdeg_child_sucs_eq_if_gt1)
    then show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
      case True
      then have eq: "Node r xs = Node (r1@Dtree.root t) (sucs t)" using eq by simp
      then have "t1 \<in> fst ` fset (sucs t)" using "1.prems"(2) by simp
      then obtain v where "v \<in> set (Dtree.root t)" "v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
        using R.dom_mdeg_gt1[of "Dtree.root t" "sucs t"] sub_t max_t by auto
      then show ?thesis using eq by auto
    next
      case False
      obtain v where v_def: "v \<in> set r1" "v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t)"
        using max_t R.dom_mdeg_gt1[of r1 "{|(t, e)|}"] 0 by auto
      interpret T: ranked_dtree_with_orig t using R.ranked_dtree_orig_rec by simp
      have eq: "Node r xs = Node r1 {|(normalize1 t, e)|}" using False eq by simp
      then have "t1 = normalize1 t" using "1.prems"(2) by simp
      moreover have "Dtree.root t \<noteq> []"
        using empty_notin_wf_dlverts[OF T.wf_lverts] dtree.set_sel(1)[of t] by auto
      ultimately have "hd (Dtree.root t1) = hd (Dtree.root t)" using normalize1_hd_root_eq by blast
      then show ?thesis using v_def eq by auto
    qed
  next
    case uneq: False
    show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
      case True
      then have "normalize1 (Node r1 {|(t,e)|}) = Node (r1@Dtree.root t) (sucs t)" by simp
      then obtain t2 where t2_def: "t2 \<in> fst ` fset (sucs t)" "is_subtree (Node r xs) t2"
        using uneq "1.prems"(1) by fastforce
      then have "is_subtree t2 t" using subtree_if_suc by blast
      then have "is_subtree (Node r xs) (Node r1 {|(t,e)|})"
        using subtree_trans subtree_if_suc t2_def(2) by auto
      then show ?thesis using R.dom_mdeg_gt1 "1.prems" by blast
    next
      case False
      then have "normalize1 (Node r1 {|(t,e)|}) = Node r1 {|(normalize1 t, e)|}" by simp
      then have "is_subtree (Node r xs) (normalize1 t)" using uneq "1.prems"(1) by auto
      then show ?thesis using "1.IH" False "1.prems"(2,3) R.ranked_dtree_orig_rec by simp
    qed
  qed
next
  case (2 xs1 r1)
  then interpret R: ranked_dtree_with_orig "Node r1 xs1" by blast
  show ?case
  proof(cases "Node r xs = normalize1 (Node r1 xs1)")
    case True
    then have 0: "max_deg (Node r1 xs1) > 1"
      using normalize1_mdeg_le "2.prems"(3) less_le_trans by (fastforce simp del: max_deg.simps)
    then obtain t where t_def: "t \<in> fst ` fset xs1" "normalize1 t = t1"
      using "2.prems"(2) "2.hyps" True by fastforce
    then have sub_t: "is_subtree t (Node r1 xs1)" using subtree_if_child by fast
    then obtain v where v_def: "v \<in> set r1" "v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t)"
      using R.dom_mdeg_gt1[of r1] t_def(1) 0 by auto
    interpret T: ranked_dtree_with_orig t using R.ranked_dtree_orig_rec t_def(1) by force
    have "Dtree.root t \<noteq> []"
      using empty_notin_wf_dlverts[OF T.wf_lverts] dtree.set_sel(1)[of t] by auto
    then have "hd (Dtree.root t1) = hd (Dtree.root t)" using normalize1_hd_root_eq t_def(2) by blast
    then show ?thesis using v_def "2.hyps" True by auto
  next
    case False
    then show ?thesis using 2 R.ranked_dtree_orig_rec by auto
  qed
qed

lemma child_contr_if_new_contr:
  assumes "\<not>rank (rev (Dtree.root t1)) < rank (rev r)"
      and "rank (rev (Dtree.root (normalize1 t1))) < rank (rev r)"
    shows "\<exists>t2 e2. sucs t1 = {|(t2,e2)|} \<and> rank (rev (Dtree.root t2)) < rank (rev (Dtree.root t1))"
proof -
  obtain t2 e2 where t2_def: "sucs t1 = {|(t2,e2)|}"
    using root_normalize1_eq2[of "sucs t1" "Dtree.root t1"] assms by fastforce
  then show ?thesis
    using root_normalize1_eq1[of t2 "Dtree.root t1" e2] assms dtree.collapse[of t1] by fastforce
qed

lemma sub_contr_if_new_contr:
  assumes "\<not>rank (rev (Dtree.root t1)) < rank (rev r)"
      and "rank (rev (Dtree.root (normalize1 t1))) < rank (rev r)"
    shows "\<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) t1 \<and> rank (rev (Dtree.root t2)) < rank (rev v)"
proof -
  obtain t2 e2 where t2_def: "sucs t1 = {|(t2,e2)|}" "rank (rev (Dtree.root t2)) < rank (rev (Dtree.root t1))"
    using child_contr_if_new_contr[OF assms] by blast
  then have "is_subtree (Node (Dtree.root t1) {|(t2,e2)|}) t1"
    using is_subtree.simps[of "Node (Dtree.root t1) {|(t2,e2)|}" "Dtree.root t1" "sucs t1"] by fastforce
  then show ?thesis using t2_def(2) by blast
qed

lemma normalize1_subtree_same_hd:
  "\<lbrakk>is_subtree (Node v {|(t1,e1)|}) (normalize1 t)\<rbrakk>
    \<Longrightarrow> \<exists>t3 e3. (is_subtree (Node v {|(t3,e3)|}) t \<and> hd (Dtree.root t1) = hd (Dtree.root t3))
      \<or> (\<exists>v2. v = v2 @ Dtree.root t3 \<and> sucs t3 = {|(t1,e1)|}
        \<and> is_subtree (Node v2 {|(t3,e3)|}) t \<and> rank (rev (Dtree.root t3)) < rank (rev v2))"
using wf_lverts wf_arcs proof(induction t rule: normalize1.induct)
  case (1 r t e)
  show ?case
  proof(cases "Node v {|(t1,e1)|} = normalize1 (Node r {|(t,e)|})")
    case eq: True
    then show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
      case True
      then show ?thesis using 1 eq by auto
    next
      case False
      then have eq: "Node v {|(t1,e1)|} = Node r {|(normalize1 t,e)|}" using eq by simp
      then show ?thesis using normalize1_hd_root_eq' "1.prems"(2) by auto
    qed
  next
    case uneq: False
    then show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
      case True
      then obtain t2 e2 where "(t2,e2) \<in> fset (sucs t)" "is_subtree (Node v {|(t1,e1)|}) t2"
        using "1.prems"(1) uneq by auto
      then show ?thesis using is_subtree.simps[of "Node v {|(t1,e1)|}" "Dtree.root t" "sucs t"] by auto
    next
      case False
      then have "is_subtree (Node v {|(t1,e1)|}) (normalize1 t)" using "1.prems"(1) uneq by auto
      then show ?thesis
        using "1.IH" "1.prems"(2,3) False by (auto simp: wf_darcs_iff_darcs')
    qed
  qed
next
  case (2 xs r)
  then have "\<forall>x. ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) \<noteq> {|x|}"
    using singleton_normalize1 by (simp add: wf_darcs_iff_darcs')
  then have "Node v {|(t1,e1)|} \<noteq> Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)" by auto
  then obtain t2 e2 where "(t2,e2) \<in> fset xs \<and> is_subtree (Node v {|(t1,e1)|}) (normalize1 t2)"
    using "2.prems"(1) "2.hyps" by auto
  then show ?case using "2.IH" "2.prems"(2,3) by (fastforce simp: wf_darcs_iff_darcs')
qed

lemma normalize1_dom_sub_contr:
  "\<lbrakk>is_subtree (Node r xs) (normalize1 t); t1 \<in> fst ` fset xs;
    \<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) (Node r xs) \<and> rank (rev (Dtree.root t2)) < rank (rev v)\<rbrakk>
    \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case (1 r1 t e)
  then interpret R: ranked_dtree_with_orig "Node r1 {|(t,e)|}" by blast
  interpret T: ranked_dtree_with_orig t using R.ranked_dtree_orig_rec by simp
  have sub_t: "is_subtree (Node (Dtree.root t) (sucs t)) (Node r1 {|(t,e)|})"
    using subtree_if_child[of t "{|(t,e)|}"] by simp
  obtain v t2 e2 where v_def:
      "is_subtree (Node v {|(t2,e2)|}) (Node r xs)" "rank (rev (Dtree.root t2)) < rank (rev v)"
    using "1.prems"(3) by blast
  show ?case
  proof(cases "Node r xs = normalize1 (Node r1 {|(t,e)|})")
    case eq: True
    then show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
      case True
      then have eq: "Node r xs = Node (r1@Dtree.root t) (sucs t)" using eq by simp
      then consider "Node r xs = Node v {|(t2,e2)|}" "max_deg (Node r xs) \<le> 1"
        | "Node r xs \<noteq> Node v {|(t2,e2)|}" | "max_deg (Node r xs) > 1"
        by linarith
      then show ?thesis
      proof(cases)
        case 1
        then have "max_deg (Node (r1@Dtree.root t) (sucs t)) \<le> 1" using eq by blast
        then have "max_deg t \<le> 1" using mdeg_root[of "Dtree.root t" "sucs t"] by simp
        then have "max_deg (Node r1 {|(t,e)|}) = 1"
          using mdeg_singleton[of r1 t] by (simp add: fcard_single_1)
        then have dom: "dom_children (Node r1 {|(t, e)|}) T" using R.dom_contr True by auto
        have 0: "t1 \<in> fst ` fset (sucs t)" using eq "1.prems"(2) by blast
        then have "Dtree.root t1 \<in> dverts t"
          using dtree.set_sel(1) T.dverts_child_subset dtree.exhaust_sel psubsetD by metis
        then obtain r2 where r2_def:
            "r2 \<in> set r1 \<union> path_lverts t (hd (Dtree.root t1))" "r2 \<rightarrow>\<^bsub>T\<^esub> (hd (Dtree.root t1))"
          using dom unfolding dom_children_def by auto
        have "Dtree.root t1 \<noteq> []"
          using empty_notin_wf_dlverts T.wf_lverts 0 T.dverts_child_subset
          by (metis dtree.exhaust_sel dtree.set_sel(1) psubsetD)
        then have "r2 \<in> set r1 \<union> set (Dtree.root t)"
          using path_lverts_subset_root_if_childhd[OF 0] r2_def(1) by fast
        then show ?thesis using r2_def(2) eq by auto
      next
        case 2
        then obtain t3 e3 where t3_def:
            "(t3,e3) \<in> fset (sucs t)" "is_subtree (Node v {|(t2,e2)|}) t3"
          using eq v_def(1) by auto
        have "is_subtree t3 t" using t3_def(1) subtree_if_suc by fastforce
        then have "is_subtree (Node v {|(t2,e2)|}) (Node (Dtree.root t) (sucs t))"
          using t3_def(2) subtree_trans by auto
        moreover have "t1 \<in> fst ` fset (sucs t)" using eq "1.prems"(2) by blast
        ultimately obtain v where v_def: "v \<in> set (Dtree.root t) \<and> v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
          using R.dom_sub_contr[OF sub_t] v_def(2) eq by blast
        then show ?thesis using eq by auto
      next
        case 3
        then show ?thesis using R.normalize1_dom_mdeg_gt1 "1.prems"(1,2) by blast
      qed
    next
      case False
      then have eq: "Node r xs = Node r1 {|(normalize1 t, e)|}" using eq by simp
      have hd: "hd (Dtree.root (normalize1 t)) = hd (Dtree.root t)"
        using normalize1_hd_root_eq' T.wf_lverts by blast
      have "\<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) t \<and> rank (rev (Dtree.root t2)) < rank (rev v)"
        using contr_before_normalize1 eq v_def sub_contr_if_new_contr False by auto
      then show ?thesis using R.dom_sub_contr[of r1 "{|(t,e)|}"] eq "1.prems"(2) hd by auto
    qed
  next
    case uneq: False
    show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
      case True
      then have "normalize1 (Node r1 {|(t,e)|}) = Node (r1@Dtree.root t) (sucs t)" by simp
      then obtain t2 where t2_def: "t2 \<in> fst ` fset (sucs t)" "is_subtree (Node r xs) t2"
        using uneq "1.prems"(1) by fastforce
      then have "is_subtree t2 t" using subtree_if_suc by blast
      then have "is_subtree (Node r xs) (Node r1 {|(t,e)|})"
        using subtree_trans subtree_if_child t2_def(2) by auto
      then show ?thesis using R.dom_sub_contr "1.prems"(2,3) by fast
    next
      case False
      then have "normalize1 (Node r1 {|(t,e)|}) = Node r1 {|(normalize1 t, e)|}" by simp
      then have "is_subtree (Node r xs) (normalize1 t)" using uneq "1.prems"(1) by auto
      then show ?thesis using "1.IH" False "1.prems"(2,3) R.ranked_dtree_orig_rec by simp
    qed
  qed
next
  case (2 xs1 r1)
  then interpret R: ranked_dtree_with_orig "Node r1 xs1" by blast
  show ?case
  proof(cases "Node r xs = normalize1 (Node r1 xs1)")
    case True
    then have eq: "Node r xs = Node r1 ((\<lambda>(t,e). (normalize1 t,e)) |`| xs1)" using "2.hyps" by simp
    obtain v t2 e2 where v_def:
      "is_subtree (Node v {|(t2,e2)|}) (Node r xs)" "rank (rev (Dtree.root t2)) < rank (rev v)"
      using "2.prems"(3) by blast
    obtain t where t_def: "t \<in> fst ` fset xs1" "normalize1 t = t1" using "2.prems"(2) eq by force
    then interpret T: ranked_dtree_with_orig t using R.ranked_dtree_orig_rec by force
    have "\<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) (Node r1 xs1)
                \<and> rank (rev (Dtree.root t2)) < rank (rev v)"
      using True contr_before_normalize1 v_def by presburger
    moreover have "hd (Dtree.root t1) = hd (Dtree.root t)"
      using normalize1_hd_root_eq' T.wf_lverts t_def(2) by blast
    ultimately show ?thesis using R.dom_sub_contr[of r1 xs1] t_def(1) eq by auto
  next
    case False
    then obtain t e where "(t,e) \<in> fset xs1 \<and> is_subtree (Node r xs) (normalize1 t)"
      using "2.prems"(1) "2.hyps" by auto
    then show ?thesis using "2.IH" "2.prems"(2,3) R.ranked_dtree_orig_rec by fast
  qed
qed

lemma dom_children_combine_aux:
  assumes "dom_children (Node r {|(t1, e1)|}) T"
      and "t2 \<in> fst ` fset (sucs t1)"
      and "x \<in> dverts t2"
    shows "\<exists>v \<in> set (r @ Dtree.root t1) \<union> path_lverts t2 (hd x). v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
  using path_lverts_child_union_root_sub[OF assms(2)] assms dtree.set_sel(2)
  unfolding dom_children_def by fastforce

lemma dom_children_combine:
  "dom_children (Node r {|(t1, e1)|}) T \<Longrightarrow> dom_children (Node (r@Dtree.root t1) (sucs t1)) T"
  using dom_children_combine_aux by (simp add: dom_children_def)

lemma path_lverts_normalize1_sub:
  "\<lbrakk>wf_dlverts t1; x \<in> dverts (normalize1 t1); max_deg (normalize1 t1) \<le> 1\<rbrakk>
    \<Longrightarrow> path_lverts t1 (hd x) \<subseteq> path_lverts (normalize1 t1) (hd x)"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    then have eq: "normalize1 (Node r {|(t, e)|}) = Node (r@Dtree.root t) (sucs t)" by simp
    then show ?thesis
    proof(cases "x = r@Dtree.root t")
      case True
      then show ?thesis using 1 by auto
    next
      case False
      then obtain t1 e1 where t1_def: "(t1,e1) \<in> fset (sucs t)" "x \<in> dverts t1"
        using "1.prems"(2) eq by auto
      then have 0: "hd x \<in> dlverts t1"
        using hd_in_lverts_if_wf "1.prems"(1) wf_dlverts_sucs by force
      then have "hd x \<in> dlverts t" using t1_def(1) suc_in_dlverts by fast
      then have 2: "hd x \<notin> set r" using "1.prems"(1) by auto
      have "wf_dlverts t" using "1.prems"(1) by simp
      then have "hd x \<notin> set (Dtree.root t)" using 0 t1_def(1) wf_dlverts.simps[of "Dtree.root t"] by fastforce
      then have hd_nin: "hd x \<notin> set (r @ Dtree.root t)" using 2 by auto
      then obtain t2 e2 where "sucs t = {|(t2,e2)|}"
        using "1.prems"(3) \<open>hd x \<in> dlverts t\<close> \<open>hd x \<notin> set (Dtree.root t)\<close> mdeg_root eq
        by (metis dtree.collapse denormalize.simps(2) denormalize_set_eq_dlverts surj_pair)
      then show ?thesis using eq hd_nin path_lverts_simps1_sucs by fastforce
    qed
  next
    case uneq: False
    then have "normalize1 (Node r {|(t, e)|}) = Node r {|(normalize1 t, e)|}" by simp
    then have "max_deg (normalize1 t) \<le> 1"
      using "1.prems"(3) mdeg_singleton[of r "normalize1 t"] fcard_single_1 max_def by auto
    then show ?thesis using uneq 1 by auto
  qed
next
  case (2 xs r)
  then have "max_deg (normalize1 (Node r xs)) = max_deg (Node r xs) \<or> max_deg (Node r xs) = 1"
    using normalize1_mdeg_eq' by blast
  then have "max_deg (Node r xs) \<le> 1" using "2.prems"(3) by (auto simp del: max_deg.simps)
  then have "fcard xs = 0"
    using mdeg_ge_fcard[of xs r] fcard_single_1_iff[of xs] "2.hyps" by fastforce
  then show ?case using 2 by simp
qed

lemma dom_children_normalize1_aux_1:
  assumes "dom_children (Node r {|(t1, e1)|}) T"
      and "sucs t1 = {|(t2,e2)|}"
      and "wf_dlverts t1"
      and "normalize1 t1 = Node (Dtree.root t1 @ Dtree.root t2) (sucs t2)"
      and "max_deg t1 = 1"
      and "x \<in> dverts (normalize1 t1)"
    shows "\<exists>v \<in> set r \<union> path_lverts (normalize1 t1) (hd x). v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
proof(cases "x = Dtree.root t1 @ Dtree.root t2")
  case True
  then have 0: "hd x = hd (Dtree.root t1)" using assms(3,4) normalize1_hd_root_eq' by fastforce
  then obtain v where v_def: "v \<in> set r \<union> path_lverts t1 (hd x)" "v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
    using assms(1) dtree.set_sel(1) unfolding dom_children_def by auto
  have "Dtree.root t1 \<noteq> []" using assms(3) wf_dlverts.simps[of "Dtree.root t1" "sucs t1"] by simp
  then show ?thesis using v_def 0 path_lverts_empty_if_roothd by auto
next
  case False
  then obtain t3 e3 where t3_def: "(t3,e3) \<in> fset (sucs t2)" "x \<in> dverts t3"
    using assms(2,4,6) by auto
  then have "x \<in> dverts t2" using dtree.set(1)[of "Dtree.root t2" "sucs t2"] by fastforce
  then have "x \<in> dverts (Node (Dtree.root t1) {|(t2,e2)|})" by auto
  then have "x \<in> dverts t1" using assms(2) dtree.exhaust_sel by metis
  then obtain v where v_def: "v \<in> set r \<union> path_lverts t1 (hd x)" "v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
    using assms(1) dtree.set_sel(1) unfolding dom_children_def by auto
  have "path_lverts t1 (hd x) \<subseteq> path_lverts (Node (Dtree.root t1 @ Dtree.root t2) (sucs t2)) (hd x)"
    using assms(3-6) normalize1_mdeg_le path_lverts_normalize1_sub by metis
  then show ?thesis using v_def assms(4) by auto
qed

lemma dom_children_normalize1_1:
  "\<lbrakk>dom_children (Node r {|(t1, e1)|}) T; sucs t1 = {|(t2,e2)|}; wf_dlverts t1;
    normalize1 t1 = Node (Dtree.root t1 @ Dtree.root t2) (sucs t2); max_deg t1 = 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r {|(normalize1 t1, e1)|}) T"
  using dom_children_normalize1_aux_1 by (simp add: dom_children_def)

lemma dom_children_normalize1_aux:
  assumes "\<forall>x\<in>dverts t1. \<exists>v \<in> set r0 \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
      and "wf_dlverts t1"
      and "max_deg t1 \<le> 1"
      and "x \<in> dverts (normalize1 t1)"
    shows "\<exists>v \<in> set r0 \<union> path_lverts (normalize1 t1) (hd x). v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
using assms proof(induction t1 arbitrary: r0 rule: normalize1.induct)
  case (1 r t e)
  have deg1: "max_deg (Node r {|(t, e)|}) = 1"
    using "1.prems"(3) mdeg_ge_fcard[of "{|(t, e)|}"] by (simp add: fcard_single_1)
  then show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    have 0: "dom_children (Node r0 {|(Node r {|(t, e)|}, e)|}) T"
      using "1.prems"(1) unfolding dom_children_def by simp
    show ?thesis using dom_children_normalize1_aux_1[OF 0] "1.prems"(1,2,4) deg1 True by auto
  next
    case ncontr: False
    show ?thesis
    proof(cases "x = r")
      case True
      then show ?thesis using "1.prems"(1,2) by auto
    next
      case False
      have "wf_dlverts (normalize1 t)" using "1.prems"(2) wf_dlverts_normalize1 by auto
      then have "hd x \<in> dlverts (normalize1 t)"
        using hd_in_lverts_if_wf False ncontr "1.prems"(1,4) by fastforce
      then have hd: "hd x \<notin> set r" using "1.prems"(2) ncontr wf_dlverts_normalize1 by fastforce
      then have eq: "path_lverts (Node r {|(t, e)|}) (hd x) = set r \<union> path_lverts t (hd x)" by simp
      then have eq1: "path_lverts (Node r {|(normalize1 t, e)|}) (hd x)
                    = set r \<union> path_lverts (normalize1 t) (hd x)" by auto
      have "\<forall>x\<in>dverts t. path_lverts (Node r {|(t, e)|}) (hd x) \<subseteq> set r \<union> path_lverts t (hd x)"
        using path_lverts_child_union_root_sub by simp
      then have 2: "\<forall>x\<in>dverts t. \<exists>v\<in>set (r0@r) \<union> path_lverts t (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
        using "1.prems"(1) by fastforce
      have "max_deg t \<le> 1" using "1.prems"(3) mdeg_ge_child[of t e "{|(t, e)|}"] by simp
      then show ?thesis using "1.IH"[OF ncontr 2] "1.prems"(2,4) ncontr hd by auto
    qed
  qed
next
  case (2 xs r)
  then have "fcard xs \<le> 1" using mdeg_ge_fcard[of xs] by simp
  then have "fcard xs = 0" using "2.hyps" fcard_single_1_iff[of xs] by fastforce
  then show ?case using 2 by auto
qed

lemma dom_children_normalize1:
  "\<lbrakk>dom_children (Node r0 {|(t1,e1)|}) T; wf_dlverts t1; max_deg t1 \<le> 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r0 {|(normalize1 t1,e1)|}) T"
  using dom_children_normalize1_aux by (simp add: dom_children_def)

lemma dom_children_child_self_aux:
  assumes "dom_children t1 T"
      and "sucs t1 = {|(t2, e2)|}"
      and "rank (rev (Dtree.root t2)) < rank (rev (Dtree.root t1))"
      and "t = Node r {|(t1, e1)|}"
      and "x \<in> dverts t1"
    shows "\<exists>v \<in> set r \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
proof(cases "x = Dtree.root t1")
  case True
  have "is_subtree (Node (Dtree.root t1) {|(t2, e2)|}) (Node r {|(t1, e1)|})"
    using subtree_if_child[of "t1" "{|(t1, e1)|}"] assms(2) dtree.collapse[of t1] by simp
  then show ?thesis using dom_sub_contr[of r "{|(t1, e1)|}"] assms(3,4) True by auto
next
  case False
  then have "x \<in> (\<Union>y\<in>fset (sucs t1). \<Union> (dverts ` Basic_BNFs.fsts y))"
    using assms(5) dtree.set(1)[of "Dtree.root t1" "sucs t1"] by auto
  then have "x \<in> dverts t2" using assms(2) by auto
  then obtain v where v_def: "v \<in> set (Dtree.root t1) \<union> path_lverts t2 (hd x)" "v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
    using assms(1,2) dtree.set_sel(1) unfolding dom_children_def by auto
  interpret T1: list_dtree t1 using list_dtree_rec assms(4) by simp
  interpret T2: list_dtree t2 using T1.list_dtree_rec_suc assms(2) by simp
  have "hd x \<in> dlverts t2" using \<open>x \<in> dverts t2\<close> by (simp add: hd_in_lverts_if_wf T2.wf_lverts)
  then have "hd x \<notin> set (Dtree.root t1)"
    using T1.wf_lverts wf_dlverts.simps[of "Dtree.root t1" "sucs t1"] assms(2) by fastforce
  then have "path_lverts t1 (hd x) = set (Dtree.root t1) \<union> path_lverts t2 (hd x)"
    using assms(2) by (simp add: path_lverts_simps1_sucs)
  then show ?thesis using v_def by auto
qed

lemma dom_children_child_self:
  assumes "dom_children t1 T"
      and "sucs t1 = {|(t2, e2)|}"
      and "rank (rev (Dtree.root t2)) < rank (rev (Dtree.root t1))"
      and "t = Node r {|(t1, e1)|}"
    shows "dom_children (Node r {|(t1, e1)|}) T"
  using dom_children_child_self_aux[OF assms] by (simp add: dom_children_def)

lemma normalize1_dom_contr:
  "\<lbrakk>is_subtree (Node r {|(t1,e1)|}) (normalize1 t); rank (rev (Dtree.root t1)) < rank (rev r);
    max_deg (Node r {|(t1,e1)|}) = 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r {|(t1,e1)|}) T"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case (1 r1 t e)
  then interpret R: ranked_dtree_with_orig "Node r1 {|(t,e)|}" by blast
  interpret T: ranked_dtree_with_orig t using R.ranked_dtree_orig_rec by simp
  have sub_t: "is_subtree (Node (Dtree.root t) (sucs t)) (Node r1 {|(t,e)|})"
    using subtree_if_child[of t "{|(t,e)|}"] by simp
  show ?case
  proof(cases "Node r {|(t1,e1)|} = normalize1 (Node r1 {|(t,e)|})")
    case eq: True
    then show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
      case True
      then have eq: "Node r {|(t1,e1)|}  = Node (r1@Dtree.root t) (sucs t)" using eq by simp
      then have "max_deg t = 1" using mdeg_root[of "Dtree.root t" "sucs t"] 1 by simp
      then have "max_deg (Node r1 {|(t,e)|}) = 1"
        using mdeg_singleton[of r1 t] by (simp add: fcard_single_1)
      then have "dom_children (Node r1 {|(t, e)|}) T" using R.dom_contr[of r1 t e] True by simp
      then show ?thesis using dom_children_combine eq by simp
    next
      case False
      then have eq: "Node r {|(t1,e1)|} = Node r1 {|(normalize1 t, e)|}" using eq by simp
      then obtain t2 e2 where t2_def:
          "sucs t = {|(t2, e2)|}" "rank (rev (Dtree.root t2)) < rank (rev (Dtree.root t))"
        using child_contr_if_new_contr False "1.prems"(2) by blast
      then have "is_subtree (Node (Dtree.root t) {|(t2, e2)|}) (Node r1 {|(t, e)|})" using sub_t by simp
      have "max_deg t = 1"
        using "1.prems"(3) eq mdeg_singleton mdeg_root t2_def
        by (metis dtree.collapse fcard_single_1 normalize1.simps(1))
      then have "max_deg (Node (Dtree.root t) {|(t2, e2)|}) = 1"
        using t2_def(1) dtree.collapse[of t] by simp
      then have "dom_children (Node (Dtree.root t) (sucs t)) T"
        using R.dom_contr sub_t t2_def "1.prems"(3) by simp
      then have "dom_children t T" using dtree.exhaust_sel by simp
      then have "dom_children (Node r1 {|(t,e)|}) T"
        using R.dom_children_child_self t2_def by simp
      then show ?thesis using dom_children_normalize1 \<open>max_deg t = 1\<close> T.wf_lverts eq by auto
    qed
  next
    case uneq: False
    show ?thesis
    proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
      case True
      then have "normalize1 (Node r1 {|(t,e)|}) = Node (r1@Dtree.root t) (sucs t)" by simp
      then obtain t2 where t2_def: "t2 \<in> fst ` fset (sucs t)" "is_subtree (Node r {|(t1,e1)|}) t2"
        using uneq "1.prems"(1) by fastforce
      then have "is_subtree t2 t" using subtree_if_suc by blast
      then have "is_subtree (Node r {|(t1,e1)|}) (Node r1 {|(t,e)|})"
        using subtree_trans subtree_if_child t2_def(2) by auto
      then show ?thesis using R.dom_contr "1.prems"(2,3) by blast
    next
      case False
      then have "normalize1 (Node r1 {|(t,e)|}) = Node r1 {|(normalize1 t, e)|}" by simp
      then have "is_subtree (Node r {|(t1,e1)|}) (normalize1 t)" using uneq "1.prems"(1) by auto
      then show ?thesis using "1.IH" False "1.prems"(2,3) R.ranked_dtree_orig_rec by simp
    qed
  qed
next
  case (2 xs r1)
  then have eq: "normalize1 (Node r1 xs) = Node r1 ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
    using "2.hyps" by simp
  interpret R: ranked_dtree_with_orig "Node r1 xs" using "2.prems"(4) by blast
  have "\<forall>x. ((\<lambda>(t,e). (normalize1 t,e)) |`| xs) \<noteq> {|x|}"
    using singleton_normalize1 "2.hyps" disjoint_darcs_if_wf_xs[OF R.wf_arcs] by auto
  then have "Node r {|(t1,e1)|} \<noteq> Node r1 ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)" by auto
  then obtain t3 e3 where t3_def:
      "(t3,e3) \<in> fset xs" "is_subtree (Node r {|(t1, e1)|}) (normalize1 t3)"
    using "2.prems"(1) eq by auto
  then show ?case using "2.IH" "2.prems"(2,3) R.ranked_dtree_orig_rec by simp
qed

lemma dom_children_normalize1_img_full:
  assumes "dom_children (Node r xs) T"
      and "\<forall>(t1,e1) \<in> fset xs. wf_dlverts t1"
      and "\<forall>(t1,e1) \<in> fset xs. max_deg t1 \<le> 1"
    shows "dom_children (Node r ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)) T"
proof -
  have "\<forall>(t1, e1) \<in> fset xs. dom_children (Node r {|(t1, e1)|}) T"
    using dom_children_all_singletons[OF assms(1)] by blast
  then have "\<forall>(t1, e1) \<in> fset xs. dom_children (Node r {|(normalize1 t1, e1)|}) T"
    using dom_children_normalize1 assms(2,3) by fast
  then show ?thesis
    using dom_children_if_all_singletons[of "(\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs"] by fastforce
qed

lemma children_deg1_normalize1_sub:
  "(\<lambda>(t1,e1). (normalize1 t1,e1)) ` children_deg1 xs
  \<subseteq> children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)"
  using normalize1_mdeg_le order_trans by auto

lemma normalize1_children_deg1_sub_if_wfarcs:
  "\<forall>(t1,e1)\<in>fset xs. wf_darcs t1
    \<Longrightarrow> children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)
      \<subseteq> (\<lambda>(t1,e1). (normalize1 t1,e1)) ` children_deg1 xs"
  using normalize1_mdeg_eq by fastforce

lemma normalize1_children_deg1_eq_if_wfarcs:
  "\<forall>(t1,e1)\<in>fset xs. wf_darcs t1
    \<Longrightarrow> (\<lambda>(t1,e1). (normalize1 t1,e1)) ` children_deg1 xs
      = children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)"
  using children_deg1_normalize1_sub normalize1_children_deg1_sub_if_wfarcs
  by (meson subset_antisym)

lemma normalize1_children_deg1_sub_if_wflverts:
  "\<forall>(t1,e1)\<in>fset xs. wf_dlverts t1
    \<Longrightarrow> children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)
      \<subseteq> (\<lambda>(t1,e1). (normalize1 t1,e1)) ` children_deg1 xs"
  using normalize1_mdeg_eq' by fastforce

lemma normalize1_children_deg1_eq_if_wflverts:
  "\<forall>(t1,e1)\<in>fset xs. wf_dlverts t1
    \<Longrightarrow> (\<lambda>(t1,e1). (normalize1 t1,e1)) ` children_deg1 xs
      = children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)"
  using children_deg1_normalize1_sub normalize1_children_deg1_sub_if_wflverts
  by (meson subset_antisym)

lemma dom_children_normalize1_img:
  assumes "dom_children (Node r (Abs_fset (children_deg1 xs))) T"
      and "\<forall>(t1,e1) \<in> fset xs. wf_dlverts t1"
    shows "dom_children (Node r (Abs_fset (children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs)))) T"
proof -
  have "\<forall>(t1, e1) \<in> children_deg1 xs. dom_children (Node r {|(t1, e1)|}) T"
    using dom_children_all_singletons[OF assms(1)] children_deg1_fset_id by blast
  then have "\<forall>(t2, e2) \<in> (\<lambda>(t1,e1). (normalize1 t1,e1)) ` children_deg1 xs.
              dom_children (Node r {|(t2, e2)|}) T"
    using dom_children_normalize1 assms(2) by fast
  then have "\<forall>(t2, e2) \<in> children_deg1 ((\<lambda>(t1,e1). (normalize1 t1,e1)) |`| xs).
              dom_children (Node r {|(t2, e2)|}) T"
    using normalize1_children_deg1_eq_if_wflverts[of xs] assms(2) by blast
  then show ?thesis using dom_children_if_all_singletons children_deg1_fset_id
  proof -
    have "\<forall>f as p. \<exists>pa. (dom_children (Node (as::'a list) f) p \<or> pa |\<in>| f) \<and> (\<not> (case pa of (d, b::'b) \<Rightarrow> dom_children (Node as {|(d, b)|}) p) \<or> dom_children (Node as f) p)"
      using dom_children_if_all_singletons by blast
    then obtain pp :: "(('a list, 'b) Dtree.dtree \<times> 'b) fset \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) pre_digraph \<Rightarrow> ('a list, 'b) Dtree.dtree \<times> 'b" where
      f1: "\<And>as f p. (dom_children (Node as f) p \<or> pp f as p |\<in>| f) \<and> (\<not> (case pp f as p of (d, b) \<Rightarrow> dom_children (Node as {|(d, b)|}) p) \<or> dom_children (Node as f) p)"
      by metis
    moreover
    { assume "\<not> (case pp (Abs_fset (children_deg1 ((\<lambda>(d, y). (normalize1 d, y)) |`| xs))) r T of (d, b) \<Rightarrow> dom_children (Node r {|(d, b)|}) T)"
      then have "pp (Abs_fset (children_deg1 ((\<lambda>(d, y). (normalize1 d, y)) |`| xs))) r T \<notin> children_deg1 ((\<lambda>(d, y). (normalize1 d, y)) |`| xs)"
        by (smt (z3) \<open>\<forall>(t2, e2) \<in>children_deg1 ((\<lambda>(t1, e1). (normalize1 t1, e1)) |`| xs). dom_children (Node r {|(t2, e2)|}) T\<close>)
      then have "pp (Abs_fset (children_deg1 ((\<lambda>(d, y). (normalize1 d, y)) |`| xs))) r T |\<notin>| Abs_fset (children_deg1 ((\<lambda>(d, y). (normalize1 d, y)) |`| xs))"
        by (metis (no_types) children_deg1_fset_id)
      then have ?thesis
        using f1 by blast }
    ultimately show ?thesis
      by meson
  qed
qed

lemma normalize1_dom_wedge:
  "\<lbrakk>is_subtree (Node r xs) (normalize1 t); fcard xs > 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r (Abs_fset (children_deg1 xs))) T"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case (1 r1 t e)
  then interpret R: ranked_dtree_with_orig "Node r1 {|(t,e)|}" by blast
  have sub_t: "is_subtree (Node (Dtree.root t) (sucs t)) (Node r1 {|(t,e)|})"
    using subtree_if_child[of t "{|(t,e)|}"] by simp
  show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r1)")
    case True
    then have eq: "normalize1 (Node r1 {|(t,e)|}) = Node (r1@Dtree.root t) (sucs t)" by simp
    then show ?thesis
    proof(cases "Node r xs = normalize1 (Node r1 {|(t,e)|})")
      case True
      then have "Node r xs = Node (r1@Dtree.root t) (sucs t)" using eq by simp
      then show ?thesis using R.dom_wedge[OF sub_t] "1.prems"(2) unfolding dom_children_def by auto
    next
      case False
      then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset (sucs t)" "is_subtree (Node r xs) t2"
        using "1.prems"(1) eq by auto
      then have "is_subtree (Node r xs) t" using subtree_if_suc subtree_trans by fastforce
      then show ?thesis using R.dom_wedge sub_t "1.prems"(2) by simp
    qed
  next
    case False
    then show ?thesis using 1 R.ranked_dtree_orig_rec by (auto simp: fcard_single_1)
  qed
next
  case (2 xs1 r1)
  then have eq: "normalize1 (Node r1 xs1) = Node r1 ((\<lambda>(t,e). (normalize1 t,e)) |`| xs1)"
    using "2.hyps" by simp
  interpret R: ranked_dtree_with_orig "Node r1 xs1" using "2.prems"(3) by blast
  have "\<forall>x. ((\<lambda>(t,e). (normalize1 t,e)) |`| xs1) \<noteq> {|x|}"
    using singleton_normalize1 "2.hyps" disjoint_darcs_if_wf_xs[OF R.wf_arcs] by auto
  then show ?case
  proof(cases "Node r xs = normalize1 (Node r1 xs1)")
    case True
    then have "1 < fcard xs1" using eq "2.prems"(2) fcard_image_le less_le_trans by fastforce
    then have "dom_children (Node r1 (Abs_fset (children_deg1 xs1))) T" using R.dom_wedge by simp
    then show ?thesis using dom_children_normalize1_img eq R.wf_lverts True by fastforce
  next
    case False
    then show ?thesis using 2 R.ranked_dtree_orig_rec by fastforce
  qed
qed

corollary normalize1_dom_wedge':
  "\<forall>r xs. is_subtree (Node r xs) (normalize1 t) \<longrightarrow> fcard xs > 1
    \<longrightarrow> dom_children (Node r (Abs_fset {(t, e). (t, e) \<in> fset xs \<and> max_deg t \<le> Suc 0})) T"
  by (auto simp only: normalize1_dom_wedge One_nat_def[symmetric])

lemma normalize1_verts_conform: "v \<in> dverts (normalize1 t) \<Longrightarrow> seq_conform v"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case ind: (1 r t e)
  then interpret R: ranked_dtree_with_orig "Node r {|(t, e)|}" by blast
  consider "rank (rev (Dtree.root t)) < rank (rev r)" "v = r@Dtree.root t"
    | "rank (rev (Dtree.root t)) < rank (rev r)" "v \<noteq> r@Dtree.root t"
    | "\<not>rank (rev (Dtree.root t)) < rank (rev r)"
    by blast
  then show ?case
  proof(cases)
    case 1
    then show ?thesis using R.contr_seq_conform by auto
  next
    case 2
    then have "v \<in> dverts (Node r {|(t, e)|})" using dverts_suc_subseteq ind.prems by fastforce
    then show ?thesis using R.verts_conform by blast
  next
    case 3
    then show ?thesis using R.verts_conform ind R.ranked_dtree_orig_rec by auto
  qed
next
  case (2 xs r)
  then interpret R: ranked_dtree_with_orig "Node r xs" by blast
  show ?case using R.verts_conform 2 R.ranked_dtree_orig_rec by auto
qed

corollary normalize1_verts_distinct: "v \<in> dverts (normalize1 t) \<Longrightarrow> distinct v"
  using distinct_normalize1 verts_distinct by auto

lemma dom_mdeg_le1_aux:
  assumes "max_deg t \<le> 1"
      and "is_subtree (Node v {|(t2, e2)|}) t"
      and "rank (rev (Dtree.root t2)) < rank (rev v)"
      and "t1 \<in> fst ` fset (sucs t)"
      and "x \<in> dverts t1"
    shows "\<exists>r\<in>set (Dtree.root t) \<union> path_lverts t1 (hd x). r \<rightarrow>\<^bsub>T\<^esub> hd x"
using assms ranked_dtree_with_orig_axioms proof(induction t arbitrary: t1)
  case (Node r xs)
  then interpret R: ranked_dtree_with_orig "Node r xs" by blast
  interpret T1: ranked_dtree_with_orig t1 using Node.prems(4) R.ranked_dtree_orig_rec by force
  have "fcard xs > 0" using Node.prems(4) fcard_seteq by fastforce
  then have "fcard xs = 1" using mdeg_ge_fcard[of xs] Node.prems(1) by simp
  then obtain e1 where e1_def: "xs = {|(t1,e1)|}"
    using Node.prems(4) fcard_single_1_iff[of xs] by auto
  have mdeg1: "max_deg (Node r xs) = 1"
    using Node.prems(1) mdeg_ge_fcard[of xs] \<open>fcard xs = 1\<close> by simp
  show ?case
  proof(cases "Node v {|(t2, e2)|} = Node r xs")
    case True
    then have "dom_children (Node r xs) T"
      using mdeg1 Node.prems(2,3) R.dom_contr_subtree by blast
    then show ?thesis unfolding dom_children_def using e1_def Node.prems(5) by simp
  next
    case False
    then have sub_t1: "is_subtree (Node v {|(t2, e2)|}) t1"
      using Node.prems(2) e1_def is_subtree.simps[of "Node v {|(t2, e2)|}"] by force
    show ?thesis
    proof(cases "x = Dtree.root t1")
      case True
      then show ?thesis using R.dom_sub_contr[OF self_subtree] Node.prems(3) e1_def sub_t1 by auto
    next
      case False
      then obtain t3 where t3_def: "t3 \<in> fst ` fset (sucs t1)" "x \<in> dverts t3"
        using Node.prems(5) dverts_root_or_child[of x "Dtree.root t1" "sucs t1"] by fastforce
      have mdeg_t1: "max_deg t1 \<le> 1" using mdeg_ge_child[of t1 e1 xs] e1_def mdeg1 by simp
      moreover have "fcard (sucs t1) > 0" using t3_def fcard_seteq by fastforce
      ultimately have "fcard (sucs t1) = 1" using mdeg_ge_fcard[of "sucs t1" "Dtree.root t1"] by simp
      then obtain e3 where e3_def: "sucs t1 = {|(t3, e3)|}"
        using t3_def fcard_single_1_iff[of "sucs t1"] by fastforce
      have ind: "\<exists>r\<in>set (Dtree.root t1) \<union> path_lverts t3 (hd x). r \<rightarrow>\<^bsub>T\<^esub> hd x"
        using Node.IH mdeg_t1 e1_def sub_t1 Node.prems(3) t3_def T1.ranked_dtree_with_orig_axioms
        by auto
      have "hd x \<in> dlverts t3" using t3_def hd_in_lverts_if_wf T1.wf_lverts wf_dlverts_suc by blast
      then have "hd x \<notin> set (Dtree.root t1)"
        using t3_def dlverts_notin_root_sucs[OF T1.wf_lverts] by blast
      then have "path_lverts t1 (hd x) = set (Dtree.root t1) \<union> path_lverts t3 (hd x)"
        using path_lverts_simps1_sucs e3_def by fastforce
      then show ?thesis using ind by blast
    qed
  qed
qed

lemma dom_mdeg_le1:
  assumes "max_deg t \<le> 1"
      and "is_subtree (Node v {|(t2, e2)|}) t"
      and "rank (rev (Dtree.root t2)) < rank (rev v)"
    shows "dom_children t T"
  using dom_mdeg_le1_aux[OF assms] unfolding dom_children_def by blast

lemma dom_children_normalize1_preserv:
  assumes "max_deg (normalize1 t1) \<le> 1" and "dom_children t1 T" and "wf_dlverts t1"
  shows "dom_children (normalize1 t1) T"
using assms proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    then show ?thesis using 1 dom_children_combine by force
  next
    case False
    then have "max_deg (normalize1 t) \<le> 1"
      using "1.prems"(1) mdeg_ge_child[of "normalize1 t" e "{|(normalize1 t,e)|}"] by simp
    then have "max_deg t \<le> 1" using normalize1_mdeg_eq' "1.prems"(3) by fastforce
    then show ?thesis using dom_children_normalize1 False "1.prems"(2,3) by simp
  qed
next
  case (2 xs r)
  have "max_deg (Node r xs) \<le> 1"
    using normalize1_mdeg_eq'[OF "2.prems"(3)] "2.prems"(1) by fastforce
  then have "fcard xs \<le> 1" using mdeg_ge_fcard[of xs] by simp
  then have "fcard xs = 0" using fcard_single_1_iff[of xs] "2.hyps" by fastforce
  then have "normalize1 (Node r xs) = Node r xs" using "2.hyps" by simp
  then show ?case using "2.prems"(2) by simp
qed

lemma dom_mdeg_le1_normalize1:
  assumes "max_deg (normalize1 t) \<le> 1" and "normalize1 t \<noteq> t"
  shows "dom_children (normalize1 t) T"
proof -
  obtain v t2 e2 where "is_subtree (Node v {|(t2, e2)|}) t" "rank (rev (Dtree.root t2)) < rank (rev v)"
    using contr_if_normalize1_uneq assms(2) by blast
  moreover have "max_deg t \<le> 1" using assms(1) normalize1_mdeg_eq wf_arcs by fastforce
  ultimately show ?thesis
    using dom_mdeg_le1 dom_children_normalize1_preserv assms(1) wf_lverts by blast
qed

lemma normalize_mdeg_eq:
  "wf_darcs t1
    \<Longrightarrow> max_deg (normalize t1) = max_deg t1 \<or> (max_deg (normalize t1) = 0 \<and> max_deg t1 = 1)"
  apply (induction t1 rule: normalize.induct)
  by (smt (verit, ccfv_threshold) normalize1_mdeg_eq wf_darcs_normalize1 normalize.simps)

lemma normalize_mdeg_eq':
  "wf_dlverts t1
    \<Longrightarrow> max_deg (normalize t1) = max_deg t1 \<or> (max_deg (normalize t1) = 0 \<and> max_deg t1 = 1)"
  apply (induction t1 rule: normalize.induct)
  by (smt (verit, ccfv_threshold) normalize1_mdeg_eq' wf_dlverts_normalize1 normalize.simps)

corollary mdeg_le1_normalize:
  "\<lbrakk>max_deg (normalize t1) \<le> 1; wf_dlverts t1\<rbrakk> \<Longrightarrow> max_deg t1 \<le> 1"
  using normalize_mdeg_eq' by fastforce

lemma dom_children_normalize_preserv:
  assumes "max_deg (normalize t1) \<le> 1" and "dom_children t1 T" and "wf_dlverts t1"
  shows "dom_children (normalize t1) T"
using assms proof(induction t1 rule: normalize.induct)
  case (1 t1)
  then show ?case
  proof(cases "t1 = normalize1 t1")
    case True
    then show ?thesis using "1.prems" dom_children_normalize1_preserv by simp
  next
    case False
    have "max_deg t1 \<le> 1" using mdeg_le1_normalize "1.prems"(1,3) by blast
    then have "max_deg (normalize1 t1) \<le> 1"
      using normalize1_mdeg_eq' "1.prems"(3) by fastforce
    then have "dom_children (normalize1 t1) T"
      using dom_children_normalize1_preserv "1.prems"(2,3) by blast
    then show ?thesis using 1 False by (simp add: Let_def wf_dlverts_normalize1)
  qed
qed

lemma dom_mdeg_le1_normalize:
  assumes "max_deg (normalize t) \<le> 1" and "normalize t \<noteq> t"
  shows "dom_children (normalize t) T"
using assms ranked_dtree_with_orig_axioms proof(induction t rule: normalize.induct)
  case (1 t)
  then interpret T: ranked_dtree_with_orig t by blast
  show ?case
    using 1 T.dom_mdeg_le1_normalize1 T.wf_lverts wf_dlverts_normalize1
    by (smt (verit) dom_children_normalize_preserv normalize.elims mdeg_le1_normalize)
qed

lemma normalize1_arc_in_dlverts:
  "\<lbrakk>is_subtree (Node v ys) (normalize1 t); x \<in> set v; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts (Node v ys)"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case ind: (1 r t e)
  then interpret R: ranked_dtree_with_orig "Node r {|(t, e)|}" by blast
  show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    then have eq: "normalize1 (Node r {|(t, e)|}) = Node (r@Dtree.root t) (sucs t)" by simp
    then show ?thesis
    proof(cases "Node v ys = Node (r@Dtree.root t) (sucs t)")
      case True
      then consider "x \<in> set r" | "x \<in> set (Dtree.root t)" using ind.prems(2) by auto
      then show ?thesis
      proof(cases)
        case 1
        then have "y \<in> dlverts (Node r {|(t, e)|})"
          using R.arc_in_dlverts ind.prems(3) by fastforce
        then show ?thesis using eq normalize1_dlverts_eq[of "Node r {|(t, e)|}"] True by simp
      next
        case 2
        then have "y \<in> dlverts t"
          using R.arc_in_dlverts[of "Dtree.root t" "sucs t"] ind.prems(3)
            subtree_if_child[of t "{|(t, e)|}"] by simp
        then show ?thesis using eq normalize1_dlverts_eq[of "Node r {|(t, e)|}"] True by simp
      qed
    next
      case False
      then obtain t2 where t2_def: "t2 \<in> fst ` fset (sucs t)" "is_subtree (Node v ys) t2"
        using ind.prems(1) eq by force
      then have "is_subtree (Node v ys) (Node r {|(t, e)|})"
        using subtree_trans[OF t2_def(2)] subtree_if_suc by auto
      then show ?thesis using R.arc_in_dlverts ind.prems(2,3) by blast
    qed
  next
    case nocontr: False
    then show ?thesis
    proof(cases "Node v ys = Node r {|(normalize1 t, e)|}")
      case True
      then have "y \<in> dlverts (Node r {|(t, e)|})"
        using R.arc_in_dlverts ind.prems(2,3) by fastforce
      then show ?thesis using nocontr True by simp
    next
      case False
      then have "is_subtree (Node v ys) (normalize1 t)" using ind.prems(1) nocontr by auto
      then show ?thesis using ind.IH[OF nocontr] ind.prems(2,3) R.ranked_dtree_orig_rec by simp
    qed
  qed
next
  case (2 xs r)
  then interpret R: ranked_dtree_with_orig "Node r xs" by blast
  have eq: "normalize1 (Node r xs) = Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
    using "2.hyps" by simp
  show ?case
  proof(cases "Node v ys = normalize1 (Node r xs)")
    case True
    then have "y \<in> dlverts (Node r xs)" using R.arc_in_dlverts "2.hyps" "2.prems"(2,3) by simp
    then show ?thesis using True by simp
  next
    case False
    then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "is_subtree (Node v ys) (normalize1 t2)"
      using "2.hyps" "2.prems"(1) by auto
    then show ?thesis using "2.IH" "2.prems"(2,3) R.ranked_dtree_orig_rec by simp
  qed
qed

lemma normalize1_arc_in_dlverts':
  "\<forall>r xs. is_subtree (Node r xs) (normalize1 t) \<longrightarrow> (\<forall>x. x \<in> set r
    \<longrightarrow> (\<forall>y. x \<rightarrow>\<^bsub>T\<^esub> y \<longrightarrow> y \<in> set r \<or> (\<exists>x\<in>fset xs. y \<in> dlverts (fst x))))"
  using normalize1_arc_in_dlverts by simp

theorem ranked_dtree_orig_normalize1: "ranked_dtree_with_orig (normalize1 t) rank cost cmp T root"
  by (simp add: ranked_dtree_with_orig_def ranked_dtree_with_orig_axioms_def asi_rank
      normalize1_dom_contr normalize1_dom_mdeg_gt1 normalize1_dom_sub_contr
      normalize1_dom_wedge' directed_tree_axioms normalize1_arc_in_dlverts'
      ranked_dtree_normalize1 normalize1_verts_conform normalize1_verts_distinct)

theorem ranked_dtree_orig_normalize: "ranked_dtree_with_orig (normalize t) rank cost cmp T root"
using ranked_dtree_with_orig_axioms proof(induction t rule: normalize.induct)
  case (1 t)
  then interpret T: ranked_dtree_with_orig t by blast
  show ?case using "1.IH" T.ranked_dtree_orig_normalize1 by(auto simp: Let_def)
qed

subsubsection \<open>Merging preserves Arc Invariants\<close>

interpretation Comm: comp_fun_commute "merge_f r xs" by (rule merge_commute)

lemma path_lverts_supset_z:
  "\<lbrakk>list_dtree (Node r xs); \<forall>t1 \<in> fst ` fset xs. a \<notin> dlverts t1\<rbrakk>
    \<Longrightarrow> path_lverts_list z a \<subseteq> path_lverts_list (ffold (merge_f r xs) z xs) a"
proof(induction xs)
  case (insert x xs)
  interpret Comm: comp_fun_commute "merge_f r (finsert x xs)" by (rule merge_commute)
  define f where "f = merge_f r (finsert x xs)"
  define f' where "f' = merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge cmp'"
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  show ?case
  proof(cases "ffold f z (finsert x xs) = ffold f' z xs")
    case True
    then show ?thesis using insert.IH 0 insert.prems(2) f_def f'_def by auto
  next
    case False
    obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
    have 1: "\<forall>v\<in>fst ` set (dtree_to_list (Node r {|(t2, e2)|})). a \<notin> set v"
      using insert.prems(2) dtree_to_list_x_in_dlverts by auto
    have "xs |\<subseteq>| finsert x xs" by blast
    then have f_xs: "ffold f z xs = ffold f' z xs"
      using merge_ffold_supset insert.prems(1) f_def f'_def by presburger
    have "ffold f z (finsert x xs) = f x (ffold f z xs)"
      using Comm.ffold_finsert[OF insert.hyps] f_def by blast
    then have 2: "ffold f z (finsert x xs) = f x (ffold f' z xs)" using f_xs by argo
    then have "f x (ffold f' z xs) \<noteq> ffold f' z xs" using False f_def f'_def by argo
    then have "f (t2,e2) (ffold f' z xs)
              = ?merge (dtree_to_list (Node r {|(t2,e2)|})) (ffold f' z xs)"
      using merge_f_merge_if_not_snd t2_def f_def by blast
    then have "ffold f z (finsert x xs)
              = ?merge (dtree_to_list (Node r {|(t2,e2)|})) (ffold f' z xs)"
      using 2 t2_def by argo
    then have "path_lverts_list (ffold f' z xs) a \<subseteq> path_lverts_list (ffold f z (finsert x xs)) a"
      using path_lverts_list_merge_supset_ys_notin[OF 1] by presburger
    then show ?thesis using insert.IH 0 insert.prems(2) f_def f'_def by auto
  qed
qed (simp add: ffold.rep_eq)

lemma path_lverts_merge_ffold_sup:
  "\<lbrakk>list_dtree (Node r xs); t1 \<in> fst ` fset xs; a \<in> dlverts t1\<rbrakk>
    \<Longrightarrow> path_lverts t1 a \<subseteq> path_lverts_list (ffold (merge_f r xs) [] xs) a"
proof(induction xs)
  case (insert x xs)
  interpret Comm: comp_fun_commute "merge_f r (finsert x xs)" by (rule merge_commute)
  define f where "f = merge_f r (finsert x xs)"
  define f' where "f' = merge_f r xs"
  let ?merge = "Sorting_Algorithms.merge cmp'"
  have 0: "list_dtree (Node r xs)" using list_dtree_subset insert.prems(1) by blast
  obtain t2 e2 where t2_def[simp]: "x = (t2,e2)" by fastforce
  have "(t2, e2) \<in> fset (finsert x xs)" by simp
  moreover have "(t2, e2) \<notin> fset xs" using insert.hyps by fastforce
  ultimately have xs_val:
    "(\<forall>(v,e) \<in> set (ffold f' [] xs). set v \<inter> dlverts t2 = {} \<and> v \<noteq> [] \<and> e \<notin> darcs t2 \<union> {e2})"
    using merge_ffold_empty_inter_preserv'[OF insert.prems(1) empty_list_valid_merge] f'_def
    by blast
  have "ffold f [] (finsert x xs) = f x (ffold f [] xs)"
    using Comm.ffold_finsert[OF insert.hyps] f_def by blast
  also have "\<dots> = f x (ffold f' [] xs)"
    using merge_ffold_supset[of xs "finsert x xs" r "[]"] insert.prems(1) f_def f'_def by fastforce
  finally have "ffold f [] (finsert x xs) = ?merge (dtree_to_list (Node r {|x|})) (ffold f' [] xs)"
    using merge_f_merge_if_conds xs_val insert.prems f_def by simp
  then have merge: "ffold f [] (finsert x xs)
              = ?merge (dtree_to_list (Node r {|(t2,e2)|})) (ffold f'[] xs)"
    using t2_def by blast
  show ?case
  proof(cases "t1 = t2")
    case True
    then have "\<forall>v\<in>fst ` set (ffold f' [] xs). a \<notin> set v"
      using insert.prems(3) xs_val by fastforce
    then have "path_lverts_list (dtree_to_list (Node r {|(t2,e2)|})) a
              \<subseteq> path_lverts_list (ffold f [] (finsert x xs)) a"
      using merge path_lverts_list_merge_supset_xs_notin by fastforce
    then show ?thesis using True f_def path_lverts_to_list_eq by force
  next
    case False
    then have "a \<notin> dlverts t2" using insert.prems list_dtree.wf_lverts by fastforce
    then have 1: "\<forall>v\<in>fst ` set (dtree_to_list (Node r {|(t2, e2)|})). a \<notin> set v"
      using dtree_to_list_x_in_dlverts by fast
    have "path_lverts t1 a \<subseteq> path_lverts_list (ffold f' [] xs) a"
      using insert.IH[OF 0] insert.prems(2,3) False f'_def by simp
    then show ?thesis using f_def merge path_lverts_list_merge_supset_ys_notin[OF 1] by auto
  qed
qed(simp)

lemma path_lverts_merge_sup_aux:
  assumes "list_dtree (Node r xs)" and "t1 \<in> fst ` fset xs" and "a \<in> dlverts t1"
      and "ffold (merge_f r xs) [] xs = (v1, e1) # ys"
  shows "path_lverts t1 a \<subseteq> path_lverts (dtree_from_list v1 ys) a"
proof -
  have "xs \<noteq> {||}" using assms(2) by auto
  have "path_lverts t1 a \<subseteq> path_lverts_list (ffold (merge_f r xs) [] xs) a"
    using path_lverts_merge_ffold_sup[OF assms(1-3)] .
  then show ?thesis using path_lverts_from_list_eq assms(4) by fastforce
qed

lemma path_lverts_merge_sup:
  assumes "list_dtree (Node r xs)" and "t1 \<in> fst ` fset xs" and "a \<in> dlverts t1"
  shows "\<exists>t2 e2. merge (Node r xs) = Node r {|(t2,e2)|}
          \<and> path_lverts t1 a \<subseteq> path_lverts t2 a"
proof -
  have "xs \<noteq> {||}" using assms(2) by auto
  then obtain t2 e2 where t2_def: "merge (Node r xs) = Node r {|(t2,e2)|}"
    using merge_singleton[OF assms(1)] by blast
  obtain y ys where y_def: "ffold (merge_f r xs) [] xs = y # ys"
    using merge_ffold_nempty[OF assms(1) \<open>xs \<noteq> {||}\<close>] list.exhaust_sel by blast
  obtain v1 e1 where "y = (v1,e1)" by fastforce
  then show ?thesis using merge_xs path_lverts_merge_sup_aux[OF assms] t2_def y_def by fastforce
qed

lemma path_lverts_merge_sup_sucs:
  assumes "list_dtree t0" and "t1 \<in> fst ` fset (sucs t0)" and "a \<in> dlverts t1"
  shows "\<exists>t2 e2. merge t0 = Node (Dtree.root t0) {|(t2,e2)|}
          \<and> path_lverts t1 a \<subseteq> path_lverts t2 a"
  using path_lverts_merge_sup[of "Dtree.root t0" "sucs t0"] assms by simp

lemma merge_dom_children_aux:
  assumes "list_dtree t0"
      and "\<forall>x\<in>dverts t1. \<exists>v \<in> set (Dtree.root t0) \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
      and "t1 \<in> fst ` fset (sucs t0)"
      and "wf_dlverts t1"
      and "x \<in> dverts t1"
    shows "\<exists>!t2 \<in> fst ` fset (sucs (merge t0)).
            \<exists>v \<in> set (Dtree.root (merge t0)) \<union> path_lverts t2 (hd x). v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
proof -
  have "hd x \<in> dlverts t1" using assms(4,5) by (simp add: hd_in_lverts_if_wf)
  then obtain t2 e2 where t2_def:
      "merge t0 = Node (Dtree.root t0) {|(t2,e2)|}" "path_lverts t1 (hd x) \<subseteq> path_lverts t2 (hd x)"
    using path_lverts_merge_sup_sucs[OF assms(1,3)] by blast
  then show ?thesis using assms(2,5) by force
qed

lemma merge_dom_children_aux':
  assumes "dom_children t0 T"
      and "\<forall>t1 \<in> fst ` fset (sucs t0). wf_dlverts t1"
      and "t2 \<in> fst ` fset (sucs (merge t0))"
      and "x \<in> dverts t2"
    shows "\<exists>v\<in>set (Dtree.root (merge t0)) \<union> path_lverts t2 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
proof -
  have disj: "list_dtree t0"
    using assms(3) merge_empty_if_nwf_sucs[of t0] by fastforce
  obtain t1 where t1_def: "t1 \<in> fst ` fset (sucs t0)" "x \<in> dverts t1"
    using verts_child_if_merge_child[OF assms(3,4)] by blast
  then have 0: "\<forall>x\<in>dverts t1. \<exists>v\<in>set (Dtree.root t0) \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
    using assms(1) unfolding dom_children_def by blast
  then have "wf_dlverts t1" using t1_def(1) assms(2) by blast
  then obtain t3 where t3_def: "t3 \<in> fst ` fset (sucs (merge t0))"
      "(\<exists>v\<in>set (Dtree.root (merge t0)) \<union> path_lverts t3 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x)"
    using merge_dom_children_aux[OF disj 0] t1_def by blast
  then have "t3 = t2" using assms(3) merge_single_root1_sucs by fastforce
  then show ?thesis using t3_def(2) by blast
qed

lemma merge_dom_children_sucs:
  assumes "dom_children t0 T" and "\<forall>t1 \<in> fst ` fset (sucs t0). wf_dlverts t1"
  shows "dom_children (merge t0) T"
  using merge_dom_children_aux'[OF assms] dom_children_def by fast

lemma merge_dom_children:
  "\<lbrakk>dom_children (Node r xs) T; \<forall>t1 \<in> fst ` fset xs. wf_dlverts t1\<rbrakk>
    \<Longrightarrow> dom_children (merge (Node r xs)) T"
  using merge_dom_children_sucs by auto

lemma merge_dom_children_if_ndisjoint:
  "\<not>list_dtree (Node r xs) \<Longrightarrow> dom_children (merge (Node r xs)) T"
  using merge_empty_if_nwf unfolding dom_children_def by simp

lemma merge_subtree_fcard_le1: "is_subtree (Node r xs) (merge t1) \<Longrightarrow> fcard xs \<le> 1"
  using merge_mdeg_le1_sub le_trans mdeg_ge_fcard by fast

lemma merge_dom_mdeg_gt1:
    "\<lbrakk>is_subtree (Node r xs) (merge t2); t1 \<in> fst ` fset xs; max_deg (Node r xs) > 1\<rbrakk>
      \<Longrightarrow> \<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
  using merge_mdeg_le1_sub by fastforce

lemma merge_root_if_contr:
  "\<lbrakk>\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t1 \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2));
    is_subtree (Node v {|(t2,e2)|}) (merge t1); rank (rev (Dtree.root t2)) < rank (rev v)\<rbrakk>
    \<Longrightarrow> Node v {|(t2,e2)|} = merge t1"
  using merge_strict_subtree_nocontr_sucs2[of t1 v] strict_subtree_def by fastforce

lemma merge_new_contr_fcard_gt1:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t1 \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "Node v {|(t2,e2)|} = (merge t1)"
      and "rank (rev (Dtree.root t2)) < rank (rev v)"
    shows "fcard (sucs t1) > 1"
proof -
  have t_v: "Dtree.root t1 = v" using assms(2) dtree.sel(1)[of v "{|(t2,e2)|}"] by simp
  have "\<forall>t2 e2. Node v {|(t2,e2)|} \<noteq> t1"
    using assms merge_root_child_eq self_subtree less_le_not_le by metis
  then have "\<forall>x. sucs t1 \<noteq> {|x|}" using t_v dtree.collapse[of t1] by force
  moreover have "sucs t1 \<noteq> {||}" using assms(2) merge_empty_sucs by force
  ultimately show ?thesis using fcard_single_1_iff[of "sucs t1"] fcard_0_eq[of "sucs t1"] by force
qed

lemma merge_dom_sub_contr_if_nocontr:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r xs) (merge t)"
      and "t1 \<in> fst ` fset xs"
      and "\<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) (Node r xs)
            \<and> rank (rev (Dtree.root t2)) < rank (rev v)"
    shows "\<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
proof -
  obtain v t2 e2 where t2_def:
      "is_subtree (Node v {|(t2,e2)|}) (Node r xs)" "rank (rev (Dtree.root t2)) < rank (rev v)"
    using assms(4) by blast
  then have "is_subtree (Node v {|(t2,e2)|}) (merge t)" using assms(2) subtree_trans by blast
  then have eq: "Node v {|(t2,e2)|} = merge t" using merge_root_if_contr assms(1) t2_def(2) by blast
  then have t_v: "Dtree.root t = v" using dtree.sel(1)[of v "{|(t2,e2)|}"] by simp
  have eq2: "Node v {|(t2,e2)|} = Node r xs"
    using eq assms(2) t2_def(1) subtree_antisym[of "Node v {|(t2, e2)|}"] by simp
  have "fcard (sucs t) > 1" using merge_new_contr_fcard_gt1[OF assms(1) eq t2_def(2)] by simp
  then have mdeg: "max_deg t > 1" using mdeg_ge_fcard[of "sucs t" "Dtree.root t"] by simp
  have sub: "is_subtree (Node (Dtree.root t) (sucs t)) t" using self_subtree[of t] by simp
  obtain e1 where e1_def: "(t1, e1)\<in>fset (sucs (merge t))"
    using assms(3) eq eq2 dtree.sel(2)[of r xs] by force
  then obtain t3 where t3_def: "(t3, e1)\<in>fset (sucs t)" "Dtree.root t3 = Dtree.root t1"
    using merge_child_in_orig[OF e1_def] by blast
  then have "\<exists>v\<in>set (Dtree.root t). v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)" using dom_mdeg_gt1 sub mdeg by fastforce
  then show ?thesis using t_v eq2 by blast
qed

lemma merge_dom_contr_if_nocontr_mdeg_le1:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r {|(t1,e1)|}) (merge t)"
      and "rank (rev (Dtree.root t1)) < rank (rev r)"
      and "\<forall>t \<in> fst ` fset (sucs t). max_deg t \<le> 1"
    shows "dom_children (Node r {|(t1,e1)|}) T"
proof -
  have eq: "Node r {|(t1,e1)|} = merge t" using merge_root_if_contr[OF assms(1-3)] .
  have 0: "\<forall>t1\<in>fst ` fset (sucs t). wf_dlverts t1" using wf_lverts wf_dlverts_suc by auto
  have "fcard (sucs t) > 1" using merge_new_contr_fcard_gt1[OF assms(1) eq assms(3)] by simp
  then have "dom_children t T" using dom_wedge_full[of "Dtree.root t"] assms(4) self_subtree by force
  then show ?thesis using merge_dom_children_sucs 0 eq by simp
qed

lemma merge_dom_wedge:
  "\<lbrakk>is_subtree (Node r xs) (merge t1); fcard xs > 1; \<forall>t \<in> fst ` fset xs. max_deg t \<le> 1\<rbrakk>
    \<Longrightarrow> dom_children (Node r xs) T"
  using merge_subtree_fcard_le1 by fastforce

subsubsection \<open>Merge1 preserves Arc Invariants\<close>

lemma merge1_dom_mdeg_gt1:
  assumes "is_subtree (Node r xs) (merge1 t)" and "t1 \<in> fst ` fset xs" and "max_deg (Node r xs) > 1"
  shows "\<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
proof -
  obtain ys where ys_def: "merge1 (Node r ys) = Node r xs" "is_subtree (Node r ys) t"
    using merge1_subtree_if_mdeg_gt1[OF assms(1,3)] by blast
  then obtain t3 where t3_def: "t3 \<in> fst ` fset ys" "Dtree.root t3 = Dtree.root t1"
    using assms(2) merge1_child_in_orig by fastforce
  have "max_deg (Node r ys) > 1" using merge1_mdeg_le[of "Node r ys"] ys_def(1) assms(3) by simp
  then show ?thesis using dom_mdeg_gt1[OF ys_def(2) t3_def(1)] t3_def by simp
qed

lemma max_deg1_gt_1_if_new_contr:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t0 \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r {|(t1,e1)|}) (merge1 t0)"
      and "rank (rev (Dtree.root t1)) < rank (rev r)"
    shows "max_deg t0 > 1"
  using assms merge1_mdeg_gt1_if_uneq by force

lemma merge1_subtree_if_new_contr:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t0 \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r xs) (merge1 t0)"
      and "is_subtree (Node v {|(t1,e1)|}) (Node r xs)"
      and "rank (rev (Dtree.root t1)) < rank (rev v)"
    shows "\<exists>ys. is_subtree (Node r ys) t0 \<and> merge1 (Node r ys) = Node r xs"
using assms proof(induction t0)
  case (Node r' ys)
  then consider "fcard ys > 1" "(\<forall>t \<in> fst ` fset ys. max_deg t \<le> 1)"
    | "\<not>(fcard ys > 1 \<and> (\<forall>t \<in> fst ` fset ys. max_deg t \<le> 1))" "Node r xs = merge1 (Node r' ys)"
    | "\<not>(fcard ys > 1 \<and> (\<forall>t \<in> fst ` fset ys. max_deg t \<le> 1))" "Node r xs \<noteq> merge1 (Node r' ys)"
    by blast
  then show ?case
  proof(cases)
    case 1
    then have "is_subtree (Node v {|(t1, e1)|}) (merge (Node r' ys))"
      using subtree_trans[OF Node.prems(3,2)] by force
    then have "Node v {|(t1, e1)|} = merge (Node r' ys)"
      using merge_root_if_contr Node.prems(1,4) by blast
    then have "Node r xs = merge1 (Node r' ys)"
      using Node.prems(2,3) 1 subtree_eq_if_trans_eq1 by fastforce
    then show ?thesis using 1 dtree.sel(1)[of r xs] by auto
  next
    case 2
    then have "r = r'" using dtree.sel(1)[of r xs] by force
    then show ?thesis using 2(2) by auto
  next
    case 3
    then have "merge1 (Node r' ys) = Node r' ((\<lambda>(t,e). (merge1 t,e)) |`| ys)" by auto
    then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset ys" "is_subtree (Node r xs) (merge1 t2)"
      using Node.prems(2) 3(2) by auto
    then have subt2: "is_subtree t2 (Node r' ys)" using subtree_if_child
      by (metis fstI image_eqI)
    then have "\<And>r1 t3 e3. is_subtree (Node r1 {|(t3, e3)|}) t2
                    \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t3))"
      using Node.prems(1) subtree_trans by blast
    then obtain ys' where ys_def: "is_subtree (Node r ys') t2" "merge1 (Node r ys') = Node r xs"
      using Node.IH[OF t2_def(1)] Node.prems(3,4) t2_def(2) by auto
    then show ?thesis using subtree_trans subt2 by blast
  qed
qed

lemma merge1_dom_sub_contr:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r xs) (merge1 t)"
      and "t1 \<in> fst ` fset xs"
      and "\<exists>v t2 e2. is_subtree (Node v {|(t2,e2)|}) (Node r xs)\<and>rank (rev (Dtree.root t2))<rank (rev v)"
    shows "\<exists>v \<in> set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"
proof -
  obtain ys where ys_def: "is_subtree (Node r ys) t" "merge1 (Node r ys) = Node r xs"
    using merge1_subtree_if_new_contr assms(1,2,4) by blast
  then interpret R: ranked_dtree_with_orig "Node r ys" using ranked_dtree_orig_subtree by blast
  obtain v t2 e2 where v_def:
      "is_subtree (Node v {|(t2,e2)|}) (Node r xs)" "rank (rev (Dtree.root t2)) < rank (rev v)"
    using assms(4) by blast
  then have "is_subtree (Node v {|(t2,e2)|}) (merge1 (Node r ys))" using ys_def by simp
  then have mdeg_gt1: "max_deg (Node r ys) > 1"
    using max_deg1_gt_1_if_new_contr assms(1) v_def(2) subtree_trans ys_def(1) by blast
  obtain t3 where t3_def: "t3 \<in> fst ` fset ys" "Dtree.root t3 = Dtree.root t1"
    using ys_def(2) assms(3) merge1_child_in_orig by fastforce
  then show ?thesis using R.dom_mdeg_gt1[OF self_subtree] mdeg_gt1 by fastforce
qed

lemma merge1_merge_point_if_new_contr:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t0 \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "wf_darcs t0"
      and "is_subtree (Node r {|(t1,e1)|}) (merge1 t0)"
      and "rank (rev (Dtree.root t1)) < rank (rev r)"
    shows "\<exists>ys. is_subtree (Node r ys) t0 \<and> fcard ys > 1 \<and> (\<forall>t\<in> fst ` fset ys. max_deg t \<le> 1)
            \<and> merge1 (Node r ys) = Node r {|(t1,e1)|}"
using assms proof(induction t0)
  case (Node v xs)
  then consider "fcard xs > 1" "(\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)"
    | "fcard xs \<le> 1" | "fcard xs > 1" "\<not>(\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)"
    by linarith
  then show ?case
  proof(cases)
    case 1
    then have "is_subtree (Node r {|(t1, e1)|}) (merge (Node v xs))" using Node.prems(3) by simp
    then have "Node r {|(t1, e1)|} = merge (Node v xs)"
      using merge_root_if_contr Node.prems(1,4) by blast
    then show ?thesis using 1 dtree.sel(1)[of r "{|(t1, e1)|}"] by auto
  next
    case 2
    then have "merge1 (Node v xs) = Node v ((\<lambda>(t,e). (merge1 t,e)) |`| xs)" by auto
    then have "xs \<noteq> {||}" using Node.prems(3) by force
    then have "fcard xs = 1" using 2 le_Suc_eq by auto
    then obtain t2 e2 where t2_def: "xs = {|(t2,e2)|}" using fcard_single_1_iff[of xs] by fast
    then have "Node r {|(t1, e1)|} \<noteq> merge1 (Node v {|(t2,e2)|})" using Node.prems(1,4) 2 by force
    then have "is_subtree (Node r {|(t1, e1)|}) (merge1 t2)" using Node.prems(3) t2_def 2 by auto
    moreover have "\<And>r1 t3 e3. is_subtree (Node r1 {|(t3, e3)|}) t2
                    \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t3))"
      using Node.prems(1) t2_def by fastforce
    ultimately show ?thesis using Node.IH[of "(t2,e2)"] Node.prems(2,4) t2_def by fastforce
  next
    case 3
    then have "fcard ((\<lambda>(t,e). (merge1 t,e)) |`| xs) > 1"
      using fcard_merge1_img_if_disjoint disjoint_darcs_if_wf_xs[OF Node.prems(2)] by simp
    then have "Node r {|(t1,e1)|} \<noteq> merge1 (Node v xs)"
      using fcard_single_1_iff[of "(\<lambda>(t,e). (merge1 t,e)) |`| xs"] 3(2) by auto
    moreover have "merge1 (Node v xs) = Node v ((\<lambda>(t,e). (merge1 t,e)) |`| xs)" using 3(2) by auto
    ultimately obtain t2 e2 where t2_def:
        "(t2,e2) \<in> fset xs" "is_subtree (Node r {|(t1, e1)|}) (merge1 t2)"
      using Node.prems(3) by auto
    then have "is_subtree t2 (Node v xs)" using subtree_if_child
      by (metis fst_conv image_eqI)
    then have "\<And>r1 t3 e3. is_subtree (Node r1 {|(t3, e3)|}) t2
                    \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t3))"
      using Node.prems(1) subtree_trans by blast
    then obtain ys where ys_def: "is_subtree (Node r ys) t2" "1 < fcard ys"
        "(\<forall>t\<in>fst ` fset ys. max_deg t \<le> 1)" "merge1 (Node r ys) = Node r {|(t1, e1)|}"
      using Node.IH[OF t2_def(1)] Node.prems(2,4) t2_def by fastforce
    then show ?thesis using t2_def(1) by auto
  qed
qed

lemma merge1_dom_contr:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r {|(t1,e1)|}) (merge1 t)"
      and "rank (rev (Dtree.root t1)) < rank (rev r)"
      and "max_deg (Node r {|(t1,e1)|}) = 1"
    shows "dom_children (Node r {|(t1,e1)|}) T"
proof -
  obtain ys where ys_def: "is_subtree (Node r ys) t" "fcard ys > 1"
      "\<forall>t\<in>fst ` fset ys. max_deg t \<le> 1" "merge1 (Node r ys) = Node r {|(t1,e1)|}"
    using merge1_merge_point_if_new_contr wf_arcs assms(1-3) by blast
  have "\<forall>t1\<in>fst ` fset ys. wf_dlverts t1"
    using ys_def(1) list_dtree.wf_lverts list_dtree_sub by fastforce
  then show ?thesis using merge_dom_children_sucs[OF dom_wedge_full] ys_def by fastforce
qed

lemma merge1_dom_children_merge_sub_aux:
  assumes "merge1 t = t2"
      and "is_subtree (Node r' xs') t"
      and "fcard xs' > 1"
      and "(\<forall>t\<in>fst ` fset xs'. max_deg t \<le> 1)"
      and "max_deg t2 \<le> 1"
      and "x \<in> dverts t2"
      and "x \<noteq> Dtree.root t2"
    shows "\<exists>v \<in> path_lverts t2 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
using assms ranked_dtree_with_orig_axioms proof(induction t arbitrary: t2)
  case (Node r xs)
  then interpret R: ranked_dtree_with_orig "Node r xs" by blast
  obtain t1 e1 where t1_def: "(t1,e1) \<in> fset (sucs t2)" "x \<in> dverts t1"
    by (metis Node.prems(6,7) fsts.simps dtree.sel dtree.set_cases(1) fst_conv surj_pair)
  then have t2_sucs: "sucs t2 = {|(t1,e1)|}"
    using Node.prems(5) empty_iff_mdeg_0[of "Dtree.root t2" "sucs t2"]
      mdeg_1_singleton[of "Dtree.root t2" "sucs t2"] by auto
  have wf_t2: "wf_dlverts t2" using Node.prems(1) R.wf_dlverts_merge1 by blast
  then have "wf_dlverts t1" using t1_def(1) wf_dlverts_suc by fastforce
  then have "hd x \<in> dlverts t1" using t1_def(2) hd_in_lverts_if_wf by blast
  then have "hd x \<notin> set (Dtree.root t2)" using dlverts_notin_root_sucs[OF wf_t2] t1_def(1) by fastforce
  then have path_t2: "path_lverts t2 (hd x) = set (Dtree.root t2) \<union> path_lverts t1 (hd x)"
    using path_lverts_simps1_sucs t2_sucs by fastforce
  show ?case
  proof(cases "Node r xs = Node r' xs'")
    case True
    then have "merge (Node r' xs') = t2" using Node.prems(1,3,4) by simp
    then have "dom_children t2 T"
      using R.dom_wedge_full[OF Node.prems(2-4)] merge_dom_children R.wf_lverts True by fastforce
    then have "\<exists>v\<in>set (Dtree.root t2) \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
      using t1_def unfolding dom_children_def by auto
    then show ?thesis using path_t2 by blast
  next
    case False
    then have "\<not>(fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1))"
      using Node.prems(3,4) child_mdeg_gt1_if_sub_fcard_gt1[OF Node.prems(2)] by force
    then have eq: "merge1 (Node r xs) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs)" by auto
    then obtain t3 e3 where t3_def: "(t3,e3) \<in> fset xs" "is_subtree (Node r' xs') t3"
      using Node.prems(2) False by auto
    have "fcard ((\<lambda>(t,e). (merge1 t,e)) |`| xs) = 1"
      using Node.prems(1) eq t2_sucs fcard_single_1 by fastforce
    then have "fcard xs = 1"
      using fcard_merge1_img_if_disjoint disjoint_darcs_if_wf_xs[OF R.wf_arcs] by simp
    then have "xs = {|(t3,e3)|}" using fcard_single_1_iff[of xs] t3_def(1) by auto
    then have t13: "merge1 t3 = t1" using t2_sucs eq Node.prems(1) by force
    then have mdegt3: "max_deg t1 \<le> 1"
      using Node.prems(5) mdeg_ge_child[of t1 e1 "sucs t2" "Dtree.root t2"] t2_sucs by fastforce
    have mdeg_gt1: "max_deg (Node r xs) > 1"
      using mdeg_ge_fcard[of xs' r'] Node.prems(2,3) mdeg_ge_sub[of "Node r' xs'" "Node r xs"]
      by simp
    show ?thesis
    proof(cases "x = Dtree.root t1")
      case True
      then have "\<exists>v\<in>set r. v \<rightarrow>\<^bsub>T\<^esub> hd x"
        using R.dom_mdeg_gt1[of r xs] t3_def(1) mdeg_gt1 t13 by fastforce
      then show ?thesis using path_t2 Node.prems(1) by auto
    next
      case False
      then have "\<exists>v\<in>path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
        using Node.IH t1_def(2) t3_def t13 assms(3,4) mdegt3 R.ranked_dtree_orig_rec by simp
      then show ?thesis using path_t2 by blast
    qed
  qed
qed

lemma merge1_dom_children_fcard_gt1_aux:
  assumes "dom_children (Node r (Abs_fset (children_deg1 ys))) T"
      and "is_subtree (Node r ys) t"
      and "merge1 (Node r ys) = Node r xs"
      and "fcard xs > 1"
      and "max_deg t2 \<le> 1"
      and "t2 \<in> fst ` fset xs"
      and "x \<in> dverts t2"
    shows "\<exists>v\<in>set r \<union> path_lverts t2 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
proof -
  obtain t1 where t1_def: "t1 \<in> fst ` fset ys" "merge1 t1 = t2"
    using merge1_elem_in_img_if_fcard_gt1[OF assms(3,4)] assms(6) by fastforce
  then have x_t: "x \<in> dverts t1" using merge1_dverts_sub assms(7) by blast
  show ?thesis
  proof(cases "max_deg t1 \<le> 1")
    case True
    then have "t1 \<in> fst ` fset (sucs (Node r (Abs_fset (children_deg1 ys))))"
      using t1_def(1) children_deg1_fset_id by force
    then have "\<exists>v\<in>set r \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> hd x"
      using assms(1) x_t unfolding dom_children_def by auto
    then show ?thesis using t1_def(2) merge1_mdeg_gt1_if_uneq[of t1] True by force
  next
    case False
    then obtain r' xs' where r'_def:
        "is_subtree (Node r' xs') t1" "1 < fcard xs'" "(\<forall>t\<in>fst ` fset xs'. max_deg t \<le> 1)"
      using merge1_wedge_if_uneq[of t1] assms(5) t1_def(2) by fastforce
    interpret R: ranked_dtree_with_orig "Node r ys" using ranked_dtree_orig_subtree assms(2) .
    interpret T: ranked_dtree_with_orig t1 using R.ranked_dtree_orig_rec t1_def(1) by force
    have "max_deg (Node r ys) > 1"
      using assms(3,4) merge1_fcard_le[of r ys] mdeg_ge_fcard[of ys] by simp
    show ?thesis
    proof (cases "x = Dtree.root t2")
      case True
      have "max_deg (Node r ys) > 1"
        using assms(3,4) merge1_fcard_le[of r ys] mdeg_ge_fcard[of ys] by simp
      then show ?thesis using dom_mdeg_gt1[OF assms(2) t1_def(1)] True t1_def(2) by auto
    next
      case False
      then show ?thesis
        using T.merge1_dom_children_merge_sub_aux[OF t1_def(2) r'_def assms(5,7)] by blast
    qed
  qed
qed

lemma merge1_dom_children_fcard_gt1:
  assumes "dom_children (Node r (Abs_fset (children_deg1 ys))) T"
      and "is_subtree (Node r ys) t"
      and "merge1 (Node r ys) = Node r xs"
      and "fcard xs > 1"
    shows "dom_children (Node r (Abs_fset (children_deg1 xs))) T"
  unfolding dom_children_def
  using merge1_dom_children_fcard_gt1_aux[OF assms] children_deg1_fset_id[of xs] by fastforce

lemma merge1_dom_wedge:
  assumes "is_subtree (Node r xs) (merge1 t)" and "fcard xs > 1"
  shows "dom_children (Node r (Abs_fset (children_deg1 xs))) T"
proof -
  obtain ys where ys_def:
      "merge1 (Node r ys) = Node r xs" "is_subtree (Node r ys) t" "fcard xs \<le> fcard ys"
    using merge1_subtree_if_fcard_gt1[OF assms] by blast
  have "dom_children (Node r (Abs_fset (children_deg1 ys))) T"
    using dom_wedge ys_def(2,3) assms(2) by simp
  then show ?thesis using merge1_dom_children_fcard_gt1 ys_def(2,1) assms(2) by blast
qed

corollary merge1_dom_wedge':
  "\<forall>r xs. is_subtree (Node r xs) (merge1 t) \<longrightarrow> fcard xs > 1
    \<longrightarrow> dom_children (Node r (Abs_fset {(t, e). (t, e) \<in> fset xs \<and> max_deg t \<le> Suc 0})) T"
  by (auto simp only: merge1_dom_wedge One_nat_def[symmetric])

corollary merge1_verts_conform: "v \<in> dverts (merge1 t) \<Longrightarrow> seq_conform v"
  by (simp add: verts_conform)

corollary merge1_verts_distinct: "\<lbrakk>v \<in> dverts (merge1 t)\<rbrakk> \<Longrightarrow> distinct v"
  using distinct_merge1 verts_distinct by auto

lemma merge1_mdeg_le1_wedge_if_fcard_gt1:
  assumes "max_deg (merge1 t1) \<le> 1"
      and "wf_darcs t1"
      and "is_subtree (Node v ys) t1"
      and "fcard ys > 1"
    shows "(\<forall>t \<in> fst ` fset ys. max_deg t \<le> 1)"
using assms proof(induction t1 rule: merge1.induct)
  case (1 r xs)
  then show ?case
  proof(cases "fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)")
    case True
    then have "Node v ys = Node r xs"
      using "1.prems"(3,4) mdeg_ge_sub mdeg_ge_fcard[of ys] by fastforce
    then show ?thesis using True by simp
  next
    case False
    then have eq: "merge1 (Node r xs) = Node r ((\<lambda>(t, e). (merge1 t, e)) |`| xs)" by auto
    have "fcard ((\<lambda>(t, e). (merge1 t, e)) |`| xs) = fcard xs"
      using fcard_merge1_img_if_disjoint disjoint_darcs_if_wf_xs[OF "1.prems"(2)] by simp
    then have "fcard xs \<le> 1"
      by (metis "1.prems"(1) False merge1.simps num_leaves_1_if_mdeg_1 num_leaves_ge_card)
    then have "Node v ys \<noteq> Node r xs" using "1.prems"(4) by auto
    then obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "is_subtree (Node v ys) t2"
      using "1.prems"(3) by auto
    then have "max_deg (merge1 t2) \<le> 1"
      using "1.prems"(1) False eq
        mdeg_ge_child[of "merge1 t2" e2 "(\<lambda>(t, e). (merge1 t, e)) |`| xs"]
      by fastforce
    then show ?thesis using "1.IH"[OF False t2_def(1) refl] t2_def "1.prems"(2,4) by fastforce
  qed
qed

lemma dom_mdeg_le1_merge1_aux:
  assumes "max_deg (merge1 t) \<le> 1"
      and "merge1 t \<noteq> t"
      and "t1 \<in> fst ` fset (sucs (merge1 t))"
      and "x \<in> dverts t1"
    shows "\<exists>r\<in>set (Dtree.root (merge1 t)) \<union> path_lverts t1 (hd x). r \<rightarrow>\<^bsub>T\<^esub> hd x"
using assms ranked_dtree_with_orig_axioms proof(induction t arbitrary: t1 rule: merge1.induct)
  case (1 r xs)
  then interpret R: ranked_dtree_with_orig "Node r xs" by blast
  show ?case
  proof(cases "fcard xs > 1")
    case True
    then have 0: "(\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1)"
      using merge1_mdeg_le1_wedge_if_fcard_gt1[OF "1.prems"(1) R.wf_arcs] by auto
    then have "dom_children (merge (Node r xs)) T"
      using True merge_dom_children_sucs R.dom_wedge_full R.wf_lverts self_subtree wf_dlverts_suc
      by fast
    then show ?thesis unfolding dom_children_def using "1.prems"(3,4) 0 True by auto
  next
    case False
    then have rec: "\<not>(fcard xs > 1 \<and> (\<forall>t \<in> fst ` fset xs. max_deg t \<le> 1))" by simp
    then have eq: "merge1 (Node r xs) = Node r ((\<lambda>(t,e). (merge1 t,e)) |`| xs)" by auto
    obtain t2 e2 where t2_def: "xs = {|(t2,e2)|}" "merge1 t2 = t1"
      using "1.prems"(3) False singleton_if_fcard_le1_elem[of xs] by fastforce
    show ?thesis
    proof(cases "x = Dtree.root t1")
      case True
      have "max_deg (Node r xs) > 1" using merge1_mdeg_gt1_if_uneq "1.prems"(2) by blast
      then show ?thesis using True R.dom_mdeg_gt1[OF self_subtree] t2_def by auto
    next
      case False
      then obtain t3 where t3_def: "t3 \<in> fst ` fset (sucs (merge1 t2))" "x \<in> dverts t3"
        using "1.prems"(4) t2_def(2) dverts_root_or_suc by fastforce
      have mdeg1: "max_deg (merge1 t2) \<le> 1"
        using "1.prems"(1) mdeg_ge_child[of t1 e2 "(\<lambda>(t,e). (merge1 t,e)) |`| xs"] eq t2_def
        by simp
      then have 0: "\<exists>r\<in>set (Dtree.root (merge1 t2)) \<union> path_lverts t3 (hd x). r \<rightarrow>\<^bsub>T\<^esub> hd x"
        using "1.IH" rec mdeg1 t3_def "1.prems"(2) eq t2_def R.ranked_dtree_orig_rec by auto
      obtain e3 where e3_def: "sucs t1 = {|(t3, e3)|}"
        using t3_def singleton_if_mdeg_le1_elem_suc mdeg1 t2_def(2) by fastforce
      have "wf_dlverts t1" using wf_dlverts_suc "1.prems"(3)  R.wf_dlverts_merge1 by blast
      then have "hd x \<in> dlverts t3"
        using t3_def(2) "1.prems"(4) list_in_verts_iff_lverts hd_in_set[of x] empty_notin_wf_dlverts
        by fast
      then have "hd x \<notin> set (Dtree.root t1)"
        using t3_def(1) dlverts_notin_root_sucs[OF \<open>wf_dlverts t1\<close>] t2_def(2) by blast
      then show ?thesis using 0 path_lverts_simps1_sucs[of "hd x" t1] e3_def t2_def(2) by blast
    qed
  qed
qed

lemma dom_mdeg_le1_merge1:
  "\<lbrakk>max_deg (merge1 t) \<le> 1; merge1 t \<noteq> t\<rbrakk> \<Longrightarrow> dom_children (merge1 t) T"
  unfolding dom_children_def using dom_mdeg_le1_merge1_aux by blast

lemma merge1_arc_in_dlverts:
  "\<lbrakk>is_subtree (Node r xs) (merge1 t); x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts (Node r xs)"
  using merge1_subtree_dlverts_supset arc_in_dlverts by blast

theorem merge1_ranked_dtree_orig:
  assumes "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
  shows "ranked_dtree_with_orig (merge1 t) rank cost cmp T root"
  using assms merge1_arc_in_dlverts
  unfolding ranked_dtree_with_orig_def ranked_dtree_with_orig_axioms_def
  by(simp add: directed_tree_axioms ranked_dtree_merge1 merge1_verts_distinct merge1_verts_conform
      merge1_dom_mdeg_gt1 merge1_dom_contr merge1_dom_sub_contr merge1_dom_wedge' asi_rank)

theorem merge1_normalize_ranked_dtree_orig:
  "ranked_dtree_with_orig (merge1 (normalize t)) rank cost cmp T root"
  using ranked_dtree_with_orig.merge1_ranked_dtree_orig[OF ranked_dtree_orig_normalize]
  by (simp add: normalize_sorted_ranks)

theorem ikkbz_sub_ranked_dtree_orig: "ranked_dtree_with_orig (ikkbz_sub t) rank cost cmp T root"
using ranked_dtree_with_orig_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  then show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis using "1.prems" by auto
  next
    case False
    then show ?thesis
      by (metis 1 ranked_dtree_with_orig.merge1_normalize_ranked_dtree_orig ikkbz_sub.simps)
  qed
qed

subsection \<open>Optimality of IKKBZ-Sub result constrained to Invariants\<close>

lemma dtree_size_skip_decr[termination_simp]: "size (Node r (sucs t1)) < size (Node v {|(t1,e1)|})"
  using dtree_size_eq_root[of "Dtree.root t1" "sucs t1"] by auto

lemma dtree_size_skip_decr1: "size (Node (r @ Dtree.root t1) (sucs t1)) < size (Node r {|(t1,e1)|})"
  using dtree_size_skip_decr by auto

function normalize_full :: "('a list,'b) dtree \<Rightarrow> ('a list,'b) dtree" where
  "normalize_full (Node r {|(t1,e1)|}) = normalize_full (Node (r@Dtree.root t1) (sucs t1))"
| "\<forall>x. xs \<noteq> {|x|} \<Longrightarrow> normalize_full (Node r xs) = Node r xs"
  using dtree_to_list.cases by blast+
termination using dtree_size_skip_decr "termination" in_measure wf_measure by metis

subsubsection \<open>Result fulfills the requirements\<close>

lemma ikkbz_sub_eq_if_mdeg_le1: "max_deg t1 \<le> 1 \<Longrightarrow> ikkbz_sub t1 = t1"
  by simp

lemma ikkbz_sub_eq_iff_mdeg_le1: "max_deg t1 \<le> 1 \<longleftrightarrow> ikkbz_sub t1 = t1"
  using ikkbz_sub_mdeg_le1[of t1] by fastforce

lemma dom_mdeg_le1_ikkbz_sub: "ikkbz_sub t \<noteq> t \<Longrightarrow> dom_children (ikkbz_sub t) T"
using ranked_dtree_with_orig_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  then interpret T: ranked_dtree_with_orig t by simp
  interpret NT: ranked_dtree_with_orig "normalize t"
    using T.ranked_dtree_orig_normalize by blast
  interpret MT: ranked_dtree_with_orig "merge1 (normalize t)"
    using T.merge1_normalize_ranked_dtree_orig by blast
  show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis using "1.prems" by auto
  next
    case False
    then show ?thesis
    proof(cases "max_deg (merge1 (normalize t)) \<le> 1")
      case True
      then show ?thesis
        using NT.dom_mdeg_le1_merge1 T.dom_mdeg_le1_normalize T.list_dtree_axioms False
        by force
    next
      case False
      then have "ikkbz_sub (merge1 (normalize t)) \<noteq> (merge1 (normalize t))"
        using ikkbz_sub_mdeg_le1[of "merge1 (normalize t)"] by force
      then show ?thesis using 1 MT.ranked_dtree_with_orig_axioms by auto
    qed
  qed
qed

lemma combine_denormalize_eq:
  "denormalize (Node r {|(t1,e1)|}) = denormalize (Node (r@Dtree.root t1) (sucs t1))"
  by (induction t1 rule: denormalize.induct) auto

lemma normalize1_denormalize_eq: "wf_dlverts t1 \<Longrightarrow> denormalize (normalize1 t1) = denormalize t1"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case using combine_denormalize_eq[of r t] by simp
next
  case (2 xs r)
  then show ?case
    using fcard_single_1_iff[of "(\<lambda>(t,e). (normalize1 t,e)) |`| xs"] fcard_single_1_iff[of xs]
    by (auto simp: fcard_normalize_img_if_wf_dlverts)
qed

lemma normalize1_denormalize_eq': "wf_darcs t1 \<Longrightarrow> denormalize (normalize1 t1) = denormalize t1"
proof(induction t1 rule: normalize1.induct)
  case (1 r t e)
  then show ?case using combine_denormalize_eq[of r t] by (auto simp: wf_darcs_iff_darcs')
next
  case (2 xs r)
  then show ?case
    using fcard_single_1_iff[of "(\<lambda>(t,e). (normalize1 t,e)) |`| xs"] fcard_single_1_iff[of xs]
    by (auto simp: fcard_normalize_img_if_disjoint wf_darcs_iff_darcs')
qed

lemma normalize_denormalize_eq: "wf_dlverts t1 \<Longrightarrow> denormalize (normalize t1) = denormalize t1"
  apply (induction t1 rule: normalize.induct)
  by (smt (verit) normalize1_denormalize_eq normalize.simps wf_dlverts_normalize1)

lemma normalize_denormalize_eq': "wf_darcs t1 \<Longrightarrow> denormalize (normalize t1) = denormalize t1"
  apply (induction t1 rule: normalize.induct)
  by (smt (verit) normalize1_denormalize_eq' normalize.simps wf_darcs_normalize1)

lemma normalize_full_denormalize_eq[simp]: "denormalize (normalize_full t1) = denormalize t1"
proof(induction t1 rule: normalize_full.induct)
  case (1 r t e)
  then show ?case using combine_denormalize_eq[of r t] by simp
qed(simp)

lemma combine_dlverts_eq: "dlverts (Node r {|(t1,e1)|}) = dlverts (Node (r@Dtree.root t1) (sucs t1))"
  using dlverts.simps[of "Dtree.root t1" "sucs t1"] by auto

lemma normalize_full_dlverts_eq[simp]: "dlverts (normalize_full t1) = dlverts t1"
  using combine_dlverts_eq by(induction t1 rule: normalize_full.induct) fastforce+

lemma combine_darcs_sub: "darcs (Node (r@Dtree.root t1) (sucs t1)) \<subseteq> darcs (Node r {|(t1,e1)|})"
  using dtree.set(2)[of "Dtree.root t1" "sucs t1"] by auto

lemma normalize_full_darcs_sub: "darcs (normalize_full t1) \<subseteq> darcs t1"
  using combine_darcs_sub by(induction t1 rule: normalize_full.induct) fastforce+

lemma combine_nempty_if_wf_dlverts: "wf_dlverts (Node r {|(t1,e1)|}) \<Longrightarrow> r @ Dtree.root t1 \<noteq> []"
  by simp

lemma combine_empty_inter_if_wf_dlverts:
  assumes "wf_dlverts (Node r {|(t1,e1)|})"
  shows "\<forall>(x, e1)\<in>fset (sucs t1). set (r @ Dtree.root t1) \<inter> dlverts x = {} \<and> wf_dlverts x"
proof -
  have "\<forall>(x, e1)\<in>fset (sucs t1). set r \<inter> dlverts x = {}" using suc_in_dlverts assms by fastforce
  then show ?thesis using wf_dlverts.simps[of "Dtree.root t1" "sucs t1"] assms by auto
qed

lemma combine_disjoint_if_wf_dlverts:
  "wf_dlverts (Node r {|(t1,e1)|}) \<Longrightarrow> disjoint_dlverts (sucs t1)"
  using wf_dlverts.simps[of "Dtree.root t1" "sucs t1"] by simp

lemma combine_wf_dlverts:
  "wf_dlverts (Node r {|(t1,e1)|}) \<Longrightarrow> wf_dlverts (Node (r@Dtree.root t1) (sucs t1))"
  using combine_empty_inter_if_wf_dlverts[of r t1] wf_dlverts.simps[of "Dtree.root t1" "sucs t1"]
  by force

lemma combine_distinct:
  assumes "\<forall>v \<in> dverts (Node r {|(t1,e1)|}). distinct v"
      and "wf_dlverts (Node r {|(t1,e1)|})"
      and "v \<in> dverts (Node (r@Dtree.root t1) (sucs t1))"
    shows "distinct v"
proof(cases "v = r @ Dtree.root t1")
  case True
  have "(Dtree.root t1) \<in> dverts t1" by (simp add: dtree.set_sel(1))
  moreover from this have "set r \<inter> set (Dtree.root t1) = {}"
    using assms(2) lverts_if_in_verts by fastforce
  ultimately show ?thesis using True assms(1) by simp
next
  case False
  then show ?thesis using assms(1,3) dverts_suc_subseteq by fastforce
qed

lemma normalize_full_wfdlverts: "wf_dlverts t1 \<Longrightarrow> wf_dlverts (normalize_full t1)"
proof(induction t1 rule: normalize_full.induct)
  case (1 r t1 e1)
  then show ?case using combine_wf_dlverts[of r t1] by simp
qed(simp)

corollary normalize_full_wfdverts: "wf_dlverts t1 \<Longrightarrow> wf_dverts (normalize_full t1)"
  using normalize_full_wfdlverts by (simp add: wf_dverts_if_wf_dlverts)

lemma combine_wf_arcs: "wf_darcs (Node r {|(t1,e1)|}) \<Longrightarrow> wf_darcs (Node (r@Dtree.root t1) (sucs t1))"
  using wf_darcs'.simps[of "Dtree.root t1" "sucs t1"] by (simp add: wf_darcs_iff_darcs')

lemma normalize_full_wfdarcs: "wf_darcs t1 \<Longrightarrow> wf_darcs (normalize_full t1)"
  using combine_wf_arcs by(induction t1 rule: normalize_full.induct) fastforce+

lemma normalize_full_dom_preserv: "dom_children t1 T \<Longrightarrow> dom_children (normalize_full t1) T"
  by (induction t1 rule: normalize_full.induct) (auto simp: dom_children_combine)

lemma combine_forward:
  assumes "dom_children (Node r {|(t1,e1)|}) T"
      and "\<forall>v \<in> dverts (Node r {|(t1,e1)|}). forward v"
      and "wf_dlverts (Node r {|(t1,e1)|})"
      and "v \<in> dverts (Node (r@Dtree.root t1) (sucs t1))"
    shows "forward v"
proof(cases "v = r @ Dtree.root t1")
  case True
  have 0: "(Dtree.root t1) \<in> dverts t1" by (simp add: dtree.set_sel(1))
  then have fwd_t1: "forward (Dtree.root t1)" using assms(2) by simp
  moreover have "set r \<inter> set (Dtree.root t1) = {}" using assms(3) 0 lverts_if_in_verts by fastforce
  moreover have "\<exists>x\<in>set r. \<exists>y\<in>set (Dtree.root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
    using assms(1,3) root_arc_if_dom_wfdlverts by fastforce
  ultimately have "\<exists>x\<in>set r. x \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t1)"  using forward_arc_to_head by blast
  moreover have fwd_r: "forward r" using assms(2) by simp
  ultimately show ?thesis using forward_app fwd_t1 True by simp
next
  case False
  then show ?thesis using assms(2,4) dverts_suc_subseteq by fastforce
qed

lemma normalize_full_forward:
  "\<lbrakk>dom_children t1 T; \<forall>v \<in> dverts t1. forward v; wf_dlverts t1\<rbrakk>
    \<Longrightarrow> \<forall>v \<in> dverts (normalize_full t1). forward v"
proof(induction t1 rule: normalize_full.induct)
  case (1 r t e)
  have "\<forall>v \<in> dverts (Node (r@Dtree.root t) (sucs t)). forward v"
    using combine_forward[OF "1.prems"(1,2,3)] by blast
  moreover have "dom_children (Node (r@Dtree.root t) (sucs t)) T"
    using dom_children_combine "1.prems"(1) by simp
  ultimately show ?case using "1.IH" "1.prems"(3) combine_wf_dlverts[of r t e] by fastforce
qed(auto)

lemma normalize_full_max_deg0: "max_deg t1 \<le> 1 \<Longrightarrow> max_deg (normalize_full t1) = 0"
proof(induction t1 rule: normalize_full.induct)
  case (1 r t e)
  then show ?case using mdeg_child_sucs_le by (fastforce dest: order_trans)
next
  case (2 xs r)
  then show ?case using empty_fset_if_mdeg_le1_not_single by auto
qed

lemma normalize_full_mdeg_eq: "max_deg t1 > 1 \<Longrightarrow> max_deg (normalize_full t1) = max_deg t1"
proof(induction t1 rule: normalize_full.induct)
  case (1 r t e)
  then show ?case using mdeg_child_sucs_eq_if_gt1 by force
qed(auto)

lemma normalize_full_empty_sucs: "max_deg t1 \<le> 1 \<Longrightarrow> \<exists>r. normalize_full t1 = Node r {||}"
proof(induction t1 rule: normalize_full.induct)
  case (1 r t e)
  then show ?case using mdeg_child_sucs_le by (fastforce dest: order_trans)
next
  case (2 xs r)
  then show ?case using empty_fset_if_mdeg_le1_not_single by auto
qed

lemma normalize_full_forward_singleton:
  "\<lbrakk>max_deg t1 \<le> 1; dom_children t1 T; \<forall>v \<in> dverts t1. forward v; wf_dlverts t1\<rbrakk>
    \<Longrightarrow> \<exists>r. normalize_full t1 = Node r {||} \<and> forward r"
  using normalize_full_empty_sucs normalize_full_forward by fastforce

lemma denormalize_empty_sucs_simp: "denormalize (Node r {||}) = r"
  using denormalize.simps(2) by blast

lemma normalize_full_dverts_eq_denormalize:
  assumes "max_deg t1 \<le> 1"
  shows "dverts (normalize_full t1) = {denormalize t1}"
proof -
  obtain r where r_def[simp]: "normalize_full t1 = Node r {||}"
    using assms normalize_full_empty_sucs by blast
  then have "denormalize (normalize_full t1) = r" by (simp add: denormalize_empty_sucs_simp)
  then have "r = denormalize t1" using normalize_full_denormalize_eq by blast
  then show ?thesis by simp
qed

lemma normalize_full_normalize_dverts_eq_denormalize:
  assumes "wf_dlverts t1" and "max_deg t1 \<le> 1"
  shows "dverts (normalize_full (normalize t1)) = {denormalize t1}"
proof -
  have "max_deg (normalize t1) \<le> 1" using assms normalize_mdeg_eq' by fastforce
  then show ?thesis
    using normalize_full_dverts_eq_denormalize normalize_denormalize_eq assms(1) by simp
qed

lemma normalize_full_normalize_dverts_eq_denormalize':
  assumes "wf_darcs t1" and "max_deg t1 \<le> 1"
  shows "dverts (normalize_full (normalize t1)) = {denormalize t1}"
proof -
  have "max_deg (normalize t1) \<le> 1" using assms normalize_mdeg_eq by fastforce
  then show ?thesis
    using normalize_full_dverts_eq_denormalize normalize_denormalize_eq' assms(1) by simp
qed

lemma denormalize_full_forward:
  "\<lbrakk>max_deg t1 \<le> 1; dom_children t1 T; \<forall>v \<in> dverts t1. forward v; wf_dlverts t1\<rbrakk>
    \<Longrightarrow> forward (denormalize (normalize_full t1))"
  by (metis denormalize_empty_sucs_simp normalize_full_forward_singleton)

lemma denormalize_forward:
  "\<lbrakk>max_deg t1 \<le> 1; dom_children t1 T; \<forall>v \<in> dverts t1. forward v; wf_dlverts t1\<rbrakk>
    \<Longrightarrow> forward (denormalize t1)"
  using denormalize_full_forward by simp

lemma ikkbz_sub_forward_if_uneq: "ikkbz_sub t \<noteq> t \<Longrightarrow> forward (denormalize (ikkbz_sub t))"
  using denormalize_forward ikkbz_sub_mdeg_le1 dom_mdeg_le1_ikkbz_sub ikkbz_sub_wf_dlverts
    ranked_dtree_with_orig.verts_forward ikkbz_sub_ranked_dtree_orig
  by fast

theorem ikkbz_sub_forward:
  "\<lbrakk>max_deg t \<le> 1 \<Longrightarrow> dom_children t T\<rbrakk> \<Longrightarrow> forward (denormalize (ikkbz_sub t))"
  using ikkbz_sub_forward_if_uneq ikkbz_sub_eq_iff_mdeg_le1[of t]
  by (fastforce simp: verts_forward wf_lverts denormalize_forward)

lemma root_arc_singleton:
  assumes "dom_children (Node r {|(t1,e1)|}) T" and "wf_dlverts (Node r {|(t1,e1)|})"
  shows "\<exists>x\<in>set r. \<exists>y\<in>set (Dtree.root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
  using root_arc_if_dom_wfdlverts assms by fastforce

lemma before_if_dom_children_wf_conform:
  assumes "dom_children (Node r {|(t1,e1)|}) T"
      and "\<forall>v \<in> dverts (Node r {|(t1,e1)|}). seq_conform v"
      and "wf_dlverts (Node r {|(t1,e1)|})"
    shows "before r (Dtree.root t1)"
proof -
  have "seq_conform (Dtree.root t1)" using  dtree.set_sel(1) assms(2) by auto
  moreover have "seq_conform r" using assms(2) by auto
  moreover have "set r \<inter> set (Dtree.root t1) = {}"
    using assms(3) dlverts_eq_dverts_union dtree.set_sel(1) by fastforce
  ultimately show ?thesis unfolding before_def using root_arc_singleton assms(1,3) by blast
qed

lemma root_arc_singleton':
  assumes "Node r {|(t1,e1)|} = t" and "dom_children t T"
  shows "\<exists>x\<in>set r. \<exists>y\<in>set (Dtree.root t1). x \<rightarrow>\<^bsub>T\<^esub> y"
  using assms root_arc_singleton wf_lverts by blast

lemma root_before_if_dom:
  assumes "Node r {|(t1,e1)|} = t" and "dom_children t T"
  shows "before r (Dtree.root t1)"
proof -
  have "(Dtree.root t1) \<in> dverts t" using dtree.set_sel(1) assms(1) by fastforce
  then have "seq_conform (Dtree.root t1)" using verts_conform by simp
  moreover have "seq_conform r" using verts_conform assms(1) by auto
  ultimately show ?thesis
    using before_def child_disjoint_root root_arc_singleton' assms by fastforce
qed

lemma combine_conform:
  "\<lbrakk>dom_children (Node r {|(t1,e1)|}) T; \<forall>v \<in> dverts (Node r {|(t1,e1)|}). seq_conform v;
    wf_dlverts (Node r {|(t1,e1)|}); v \<in> dverts (Node (r@Dtree.root t1) (sucs t1))\<rbrakk>
      \<Longrightarrow> seq_conform v"
  apply(cases "v = r@Dtree.root t1")
   using before_if_dom_children_wf_conform seq_conform_if_before apply fastforce
  using dverts_suc_subseteq by fastforce

lemma denormalize_full_set_eq_dlverts:
  "max_deg t1 \<le> 1 \<Longrightarrow> set (denormalize (normalize_full t1)) = dlverts t1"
  using denormalize_set_eq_dlverts by auto

lemma denormalize_full_set_eq_dverts_union:
  "max_deg t1 \<le> 1 \<Longrightarrow> set (denormalize (normalize_full t1)) = \<Union>(set ` dverts t1)"
  using denormalize_full_set_eq_dlverts dlverts_eq_dverts_union by fastforce

corollary hd_eq_denormalize_full:
  "wf_dlverts t1 \<Longrightarrow> hd (denormalize (normalize_full t1)) = hd (Dtree.root t1)"
  using denormalize_hd_root_wf by auto

corollary denormalize_full_nempty_if_wf:
  "wf_dlverts t1 \<Longrightarrow> denormalize (normalize_full t1) \<noteq> []"
  using denormalize_nempty_if_wf by auto

lemma take1_eq_denormalize_full:
  "wf_dlverts t1 \<Longrightarrow> take 1 (denormalize (normalize_full t1)) = [hd (Dtree.root t1)]"
  using hd_eq_denormalize_full take1_eq_hd denormalize_full_nempty_if_wf by fast

lemma P_denormalize_full:
  assumes "wf_dlverts t1"
      and "\<forall>v \<in> dverts t1. distinct v"
      and "hd (Dtree.root t1) = root"
      and "max_deg t1 \<le> 1"
    shows "unique_set_r root (dverts t1) (denormalize (normalize_full t1))"
  using assms unique_set_r_def denormalize_full_set_eq_dverts_union
    denormalize_distinct normalize_full_wfdlverts take1_eq_denormalize_full
  by fastforce

lemma P_denormalize:
  fixes t1 :: "('a list,'b) dtree"
  assumes "wf_dlverts t1"
      and "\<forall>v \<in> dverts t1. distinct v"
      and "hd (Dtree.root t1) = root"
      and "max_deg t1 \<le> 1"
    shows "unique_set_r root (dverts t1) (denormalize t1)"
  using assms P_denormalize_full by auto

lemma denormalize_full_fwd:
  assumes "wf_dlverts t1"
      and "max_deg t1 \<le> 1"
      and "\<forall>xs \<in> (dverts t1). seq_conform xs"
      and "dom_children t1 T"
    shows "forward (denormalize (normalize_full t1))"
  using assms denormalize_forward forward_arcs_alt seq_conform_def by auto

lemma normalize_full_verts_sublist:
  "v \<in> dverts t1 \<Longrightarrow> \<exists>v2 \<in> dverts (normalize_full t1). sublist v v2"
proof(induction t1 arbitrary: v rule: normalize_full.induct)
  case ind: (1 r t e)
  then consider "v = r \<or> v = Dtree.root t" | "\<exists>t1 \<in> fst ` fset (sucs t). v \<in> dverts t1"
    using dverts_root_or_suc by fastforce
  then show ?case
  proof(cases)
    case 1
    have "\<exists>a\<in>dverts (normalize_full (Node (r @ Dtree.root t) (sucs t))). sublist (r@Dtree.root t) a"
      using ind.IH by simp
    moreover have "sublist v (r@Dtree.root t)" using 1 by blast
    ultimately show ?thesis using sublist_order.dual_order.trans by auto
  next
    case 2
    then show ?thesis using ind.IH[of v] by fastforce
  qed
next
  case (2 xs r)
  then show ?case by fastforce
qed

lemma normalize_full_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts t1\<rbrakk> \<Longrightarrow> \<exists>v2 \<in> dverts (normalize_full t1). sublist xs v2"
  using normalize_full_verts_sublist sublist_order.dual_order.trans by fast

lemma denormalize_full_sublist_preserv:
  assumes "sublist xs v" and "v \<in> dverts t1" and "max_deg t1 \<le> 1"
  shows "sublist xs (denormalize (normalize_full t1))"
proof -
  obtain r where r_def[simp]: "normalize_full t1 = Node r {||}"
    using assms(3) normalize_full_empty_sucs by blast
  have "sublist xs r" using normalize_full_sublist_preserv[OF assms(1,2)] by simp
  then show ?thesis by (simp add: denormalize_empty_sucs_simp)
qed

corollary denormalize_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts (t1::('a list,'b) dtree); max_deg t1 \<le> 1\<rbrakk>
    \<Longrightarrow> sublist xs (denormalize t1)"
  using denormalize_full_sublist_preserv by simp

lemma Q_denormalize_full:
  assumes "wf_dlverts t1"
      and "\<forall>v \<in> dverts t1. distinct v"
      and "hd (Dtree.root t1) = root"
      and "max_deg t1 \<le> 1"
      and "\<forall>xs \<in> (dverts t1). seq_conform xs"
      and "dom_children t1 T"
    shows "fwd_sub root (dverts t1) (denormalize (normalize_full t1))"
  using P_denormalize_full[OF assms(1-4)] assms(1,4-6) denormalize_full_sublist_preserv
  by (auto dest: denormalize_full_fwd simp: fwd_sub_def)

corollary Q_denormalize:
  assumes "wf_dlverts t1"
      and "\<forall>v \<in> dverts t1. distinct v"
      and "hd (Dtree.root t1) = root"
      and "max_deg t1 \<le> 1"
      and "\<forall>xs \<in> (dverts t1). seq_conform xs"
      and "dom_children t1 T"
    shows "fwd_sub root (dverts t1) (denormalize t1)"
  using Q_denormalize_full assms by simp

corollary Q_denormalize_t:
  assumes "hd (Dtree.root t) = root"
      and "max_deg t \<le> 1"
      and "dom_children t T"
    shows "fwd_sub root (dverts t) (denormalize t)"
  using Q_denormalize wf_lverts assms verts_conform verts_distinct by blast

lemma P_denormalize_ikkbz_sub:
  assumes "hd (Dtree.root t) = root"
  shows "unique_set_r root (dverts t) (denormalize (ikkbz_sub t))"
proof -
  interpret T: ranked_dtree_with_orig "ikkbz_sub t" using ikkbz_sub_ranked_dtree_orig by auto
  have "\<forall>v\<in>dverts (ikkbz_sub t). distinct v" using T.verts_distinct by simp
  then show ?thesis
    using P_denormalize T.wf_lverts ikkbz_sub_mdeg_le1 assms ikkbz_sub_hd_root
    unfolding unique_set_r_def denormalize_ikkbz_eq_dlverts dlverts_eq_dverts_union
    by blast
qed

lemma merge1_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts t\<rbrakk> \<Longrightarrow> \<exists>v2 \<in> dverts (merge1 t). sublist xs v2"
  using sublist_order.dual_order.trans by auto

lemma normalize1_verts_sublist: "v \<in> dverts t1 \<Longrightarrow> \<exists>v2 \<in> dverts (normalize1 t1). sublist v v2"
proof(induction t1 arbitrary: v rule: normalize1.induct)
  case ind: (1 r t e)
  show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    consider "v = r \<or> v = Dtree.root t" | "\<exists>t1 \<in> fst ` fset (sucs t). v \<in> dverts t1"
      using dverts_root_or_suc using ind.prems by fastforce
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using True by auto
    next
      case 2
      then show ?thesis using True by fastforce
    qed
  next
    case False
    then show ?thesis using ind by auto
  qed
next
  case (2 xs r)
  then show ?case by fastforce
qed

lemma normalize1_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts t1\<rbrakk> \<Longrightarrow> \<exists>v2 \<in> dverts (normalize1 t1). sublist xs v2"
  using normalize1_verts_sublist sublist_order.dual_order.trans by fast

lemma normalize_verts_sublist: "v \<in> dverts t1 \<Longrightarrow> \<exists>v2 \<in> dverts (normalize t1). sublist v v2"
proof(induction t1 arbitrary: v rule: normalize.induct)
  case (1 t1)
  then show ?case
  proof(cases "t1 = normalize1 t1")
    case True
    then show ?thesis using "1.prems" by auto
  next
    case False
    then have eq: "normalize (normalize1 t1) = normalize t1" by (auto simp: Let_def)
    then obtain v2 where v2_def: "v2 \<in> dverts (normalize1 t1)" "sublist v v2"
      using normalize1_verts_sublist "1.prems" by blast
    then show ?thesis
      using "1.IH"[OF refl False v2_def(1)] eq sublist_order.dual_order.trans by auto
  qed
qed

lemma normalize_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts t1\<rbrakk> \<Longrightarrow> \<exists>v2 \<in> dverts (normalize t1). sublist xs v2"
  using normalize_verts_sublist sublist_order.dual_order.trans by fast

lemma ikkbz_sub_verts_sublist: "v \<in> dverts t \<Longrightarrow> \<exists>v2 \<in> dverts (ikkbz_sub t). sublist v v2"
using ranked_dtree_with_orig_axioms proof(induction t arbitrary: v rule: ikkbz_sub.induct)
  case (1 t)
  then interpret T: ranked_dtree_with_orig t by simp
  interpret NT: ranked_dtree_with_orig "normalize t"
    using T.ranked_dtree_orig_normalize by blast
  show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis using "1.prems"(1) by auto
  next
    case False
    then have 0: "\<not> (max_deg t \<le> 1 \<or> \<not> list_dtree t)" using T.list_dtree_axioms by auto
    obtain v1 where v1_def: "v1 \<in> dverts (normalize t)" "sublist v v1"
      using normalize_verts_sublist "1.prems"(1) by blast
    then have "v1 \<in> dverts (merge1 (normalize t))" using NT.merge1_dverts_eq by blast
    then obtain v2 where v2_def: "v2 \<in> dverts (ikkbz_sub t)" "sublist v1 v2"
      using 1 0 T.merge1_normalize_ranked_dtree_orig by force
    then show ?thesis using v1_def(2) sublist_order.dual_order.trans by blast
  qed
qed

lemma ikkbz_sub_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts t\<rbrakk> \<Longrightarrow> \<exists>v2 \<in> dverts (ikkbz_sub t). sublist xs v2"
  using ikkbz_sub_verts_sublist sublist_order.dual_order.trans by fast

lemma denormalize_ikkbz_sub_verts_sublist:
  "\<forall>xs \<in> (dverts t). sublist xs (denormalize (ikkbz_sub t))"
  using ikkbz_sub_verts_sublist denormalize_sublist_preserv ikkbz_sub_mdeg_le1 by blast

lemma denormalize_ikkbz_sub_sublist_preserv:
  "\<lbrakk>sublist xs v; v \<in> dverts t\<rbrakk> \<Longrightarrow> sublist xs (denormalize (ikkbz_sub t))"
  using denormalize_ikkbz_sub_verts_sublist sublist_order.dual_order.trans by blast

lemma Q_denormalize_ikkbz_sub:
  "\<lbrakk>hd (Dtree.root t) = root; max_deg t \<le> 1 \<Longrightarrow> dom_children t T\<rbrakk>
    \<Longrightarrow> fwd_sub root (dverts t) (denormalize (ikkbz_sub t))"
  using P_denormalize_ikkbz_sub ikkbz_sub_forward denormalize_ikkbz_sub_verts_sublist fwd_sub_def
  by blast

subsubsection \<open>Minimal Cost of the result\<close>

lemma normalize1_dverts_app_before_contr:
  "\<lbrakk>v \<in> dverts (normalize1 t); v \<notin> dverts t\<rbrakk>
    \<Longrightarrow> \<exists>v1\<in>dverts t. \<exists>v2\<in>dverts t. v1 @ v2 = v \<and> before v1 v2 \<and> rank (rev v2) < rank (rev v1)"
  by (fastforce dest: normalize1_dverts_contr_subtree
      simp: single_subtree_root_dverts single_subtree_child_root_dverts contr_before)

lemma normalize1_dverts_app_bfr_cntr_rnks:
  assumes "v \<in> dverts (normalize1 t)" and "v \<notin> dverts t"
  shows "\<exists>U\<in>dverts t. \<exists>V\<in>dverts t. U @ V = v \<and> before U V \<and> rank (rev V) < rank (rev U)
      \<and> (\<forall>xs \<in> dverts t. (\<exists>y\<in>set xs. \<not> (\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> xs \<noteq> U)
        \<longrightarrow> rank (rev V) \<le> rank (rev xs))"
  using normalize1_dverts_contr_subtree[OF assms] subtree_rank_ge_if_reach'
  by (fastforce simp: single_subtree_root_dverts single_subtree_child_root_dverts contr_before)

lemma normalize1_dverts_app_bfr_cntr_rnks':
  assumes "v \<in> dverts (normalize1 t)" and "v \<notin> dverts t"
  shows "\<exists>U\<in>dverts t. \<exists>V\<in>dverts t. U @ V = v \<and> before U V \<and> rank (rev V) \<le> rank (rev U)
      \<and> (\<forall>xs \<in> dverts t. (\<exists>y\<in>set xs. \<not> (\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> xs \<noteq> U)
        \<longrightarrow> rank (rev V) \<le> rank (rev xs))"
  using normalize1_dverts_contr_subtree[OF assms] subtree_rank_ge_if_reach'
  by (fastforce simp: single_subtree_root_dverts single_subtree_child_root_dverts contr_before)

lemma normalize1_dverts_split:
  "dverts (normalize1 t1)
  = {v \<in> dverts (normalize1 t1). v \<notin> dverts t1} \<union> {v \<in> dverts (normalize1 t1). v \<in> dverts t1}"
  by blast

lemma normalize1_dlverts_split:
  "dlverts (normalize1 t1)
  = \<Union>(set ` {v \<in> dverts (normalize1 t1). v \<notin> dverts t1})
    \<union> \<Union>(set ` {v \<in> dverts (normalize1 t1). v \<in> dverts t1})"
  using dlverts_eq_dverts_union by fastforce

lemma normalize1_dsjnt_in_dverts:
  assumes "wf_dlverts t1"
      and "v \<in> dverts t1"
      and "set v \<inter> \<Union>(set ` {v \<in> dverts (normalize1 t1). v \<notin> dverts t1}) = {}"
    shows "v \<in> dverts (normalize1 t1)"
proof -
  have "set v \<subseteq> dlverts (normalize1 t1)" using assms(2) lverts_if_in_verts by fastforce
  then have sub: "set v \<subseteq> \<Union>(set ` {v \<in> dverts (normalize1 t1). v \<in> dverts t1})"
    using normalize1_dlverts_split assms(3) by auto
  have "v \<noteq> []" using assms(1,2) empty_notin_wf_dlverts by auto
  then obtain x where x_def: "x \<in> set v" by fastforce
  then show ?thesis using dverts_same_if_set_wf[OF assms(1,2)] x_def sub by blast
qed

lemma normalize1_dsjnt_subset_split1:
  fixes t1
  defines "X \<equiv> {v \<in> dverts (normalize1 t1). v \<notin> dverts t1}"
  assumes "wf_dlverts t1"
  shows "{x. x\<in>dverts t1 \<and> set x \<inter> \<Union>(set ` X) = {}} \<subseteq> {v \<in> dverts (normalize1 t1). v \<in> dverts t1}"
  using assms normalize1_dsjnt_in_dverts by blast

lemma normalize1_dsjnt_subset_split2:
  fixes t1
  defines "X \<equiv> {v \<in> dverts (normalize1 t1). v \<notin> dverts t1}"
  assumes "wf_dlverts t1"
  shows "{v \<in> dverts (normalize1 t1). v \<in> dverts t1} \<subseteq> {x. x\<in>dverts t1 \<and> set x \<inter> \<Union>(set ` X) = {}}"
  using dverts_same_if_set_wf[OF wf_dlverts_normalize1] assms by blast

lemma normalize1_dsjnt_subset_eq_split:
  fixes t1
  defines "X \<equiv> {v \<in> dverts (normalize1 t1). v \<notin> dverts t1}"
  assumes "wf_dlverts t1"
  shows "{v \<in> dverts (normalize1 t1). v \<in> dverts t1} = {x. x\<in>dverts t1 \<and> set x \<inter> \<Union>(set ` X) = {}}"
  using normalize1_dsjnt_subset_split1 normalize1_dsjnt_subset_split2 assms
  by blast

lemma normalize1_dverts_split2:
  fixes t1
  defines "X \<equiv> {v \<in> dverts (normalize1 t1). v \<notin> dverts t1}"
  assumes "wf_dlverts t1"
  shows "X \<union> {x. x \<in> dverts t1 \<and> set x \<inter> \<Union>(set ` X) = {}} = dverts (normalize1 t1)"
  unfolding assms(1) using normalize1_dsjnt_subset_eq_split[OF assms(2)] by blast

lemma set_subset_if_normalize1_vert: "v1 \<in> dverts (normalize1 t1) \<Longrightarrow> set v1 \<subseteq> dlverts t1"
  using lverts_if_in_verts by fastforce

lemma normalize1_new_verts_not_reach1:
  assumes "v1 \<in> dverts (normalize1 t)" and "v1 \<notin> dverts t"
      and "v2 \<in> dverts (normalize1 t)" and "v2 \<notin> dverts t"
      and "v1 \<noteq> v2"
  shows "\<not>(\<exists>x\<in>set v1. \<exists>y\<in>set v2. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
using assms ranked_dtree_with_orig_axioms proof(induction t rule: normalize1.induct)
  case (1 r t e)
  then interpret R: ranked_dtree_with_orig "Node r {|(t, e)|}" by blast
  show ?case
  proof(cases "rank (rev (Dtree.root t)) < rank (rev r)")
    case True
    then have eq: "normalize1 (Node r {|(t, e)|}) = Node (r@Dtree.root t) (sucs t)" by simp
    have "v1 = r @ Dtree.root t"
      using "1.prems"(1,2) dverts_suc_subseteq unfolding eq by fastforce
    moreover have "v2 = r @ Dtree.root t"
      using "1.prems"(3,4) dverts_suc_subseteq unfolding eq by fastforce
    ultimately show ?thesis using "1.prems"(5) by simp
  next
    case False
    then show ?thesis using 1 R.ranked_dtree_orig_rec by simp
  qed
next
  case (2 xs r)
  then interpret R: ranked_dtree_with_orig "Node r xs" by blast
  have eq: "normalize1 (Node r xs) = Node r ((\<lambda>(t,e). (normalize1 t,e)) |`| xs)"
    using "2.hyps" by simp
  obtain t1 e1 where t1_def: "(t1,e1) \<in> fset xs" "v1 \<in> dverts (normalize1 t1)"
    using "2.hyps" "2.prems"(1,2) by auto
  obtain t2 e2 where t2_def: "(t2,e2) \<in> fset xs" "v2 \<in> dverts (normalize1 t2)"
    using "2.hyps" "2.prems"(3,4) by auto
  show ?case
  proof(cases "t1 = t2")
    case True
    have "v1 \<notin> dverts t1 \<and> v2 \<notin> dverts t2"
      using "2.hyps" "2.prems"(2,4) t1_def(1) t2_def(1) by simp
    then show ?thesis using "2.IH" t1_def t2_def True "2.prems"(5) R.ranked_dtree_orig_rec by simp
  next
    case False
    have sub: "is_subtree t1 (Node r xs)" using t1_def(1) subtree_if_child[of t1 xs r] by force
    have "set v1 \<subseteq> dlverts t1" using set_subset_if_normalize1_vert t1_def(2) by simp
    then have reach_t1: "\<forall>x \<in> set v1. \<forall>y. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y \<longrightarrow> y \<in> dlverts t1"
      using R.dlverts_reach1_in_dlverts sub by blast
    have "dlverts t1 \<inter> dlverts t2 = {}"
      using R.wf_lverts t2_def(1) t1_def(1) wf_dlverts.simps[of r] False by fast
    then have "set v2 \<inter> dlverts t1 = {}" using set_subset_if_normalize1_vert t2_def(2) by auto
    then show ?thesis using reach_t1 by blast
  qed
qed

lemma normalize1_dverts_split_optimal:
  defines "X \<equiv> {v \<in> dverts (normalize1 t). v \<notin> dverts t}"
  assumes "\<exists>x. fwd_sub root (dverts t) x"
  shows "\<exists>zs. fwd_sub root (X \<union> {x. x \<in> dverts t \<and> set x \<inter> \<Union>(set ` X) = {}}) zs
          \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
proof -
  let ?Y = "dverts t"
  have dsjt: "\<forall>xs \<in> ?Y. \<forall>ys \<in> ?Y. xs = ys \<or> set xs \<inter> set ys = {}"
    using dverts_same_if_set_wf[OF wf_lverts] by blast
  have fwd: "\<forall>xs \<in> ?Y. forward xs" by (simp add: verts_forward)
  have nempty: "[] \<notin> ?Y" by (simp add: empty_notin_wf_dlverts wf_lverts)
  have fin: "finite ?Y" by (simp add: finite_dverts)
  have "\<forall>ys \<in> X. \<exists>U \<in> ?Y. \<exists>V \<in> ?Y. U@V = ys \<and> before U V \<and> rank (rev V) \<le> rank (rev U)
        \<and> (\<forall>xs \<in> ?Y. (\<exists>y\<in>set xs. \<not>(\<exists>x'\<in>set V. x' \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> (\<exists>x\<in>set U. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y) \<and> xs \<noteq> U)
          \<longrightarrow> rank (rev V) \<le> rank (rev xs))"
    unfolding X_def using normalize1_dverts_app_bfr_cntr_rnks' by blast
  moreover have "\<forall>xs \<in> X. \<forall>ys \<in> X. xs = ys \<or> set xs \<inter> set ys = {}"
    unfolding X_def using dverts_same_if_set_wf[OF wf_dlverts_normalize1] wf_lverts by blast
  moreover have "\<forall>xs \<in> X. \<forall>ys \<in> X. xs = ys \<or> \<not>(\<exists>x\<in>set xs. \<exists>y\<in>set ys. x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y)"
    unfolding X_def using normalize1_new_verts_not_reach1 by blast
  moreover have "finite X" by (simp add: X_def finite_dverts)
  ultimately show ?thesis
    using combine_union_sets_optimal_cost[OF asi_rank dsjt fwd nempty fin assms(2)] by simp
qed

corollary normalize1_dverts_optimal:
  assumes "\<exists>x. fwd_sub root (dverts t) x"
  shows "\<exists>zs. fwd_sub root (dverts (normalize1 t)) zs
        \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
  using normalize1_dverts_split_optimal assms normalize1_dverts_split2[OF wf_lverts] by simp

lemma normalize_dverts_optimal:
  assumes "\<exists>x. fwd_sub root (dverts t) x"
  shows "\<exists>zs. fwd_sub root (dverts (normalize t)) zs
        \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
using assms ranked_dtree_with_orig_axioms proof(induction t rule: normalize.induct)
  case (1 t)
  then interpret T: ranked_dtree_with_orig t by blast
  obtain zs where zs_def:
      "fwd_sub root (dverts (normalize1 t)) zs"
      "\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as)"
    using "1.prems" T.normalize1_dverts_optimal by auto
  show ?case
  proof(cases "t = normalize1 t")
    case True
    then show ?thesis using zs_def by auto
  next
    case False
    then have eq: "normalize (normalize1 t) = normalize t" by (auto simp: Let_def)
    have "\<exists>zs. fwd_sub root (dverts (normalize (normalize1 t))) zs
          \<and> (\<forall>as. fwd_sub root (dverts (normalize1 t)) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
      using "1.IH" False zs_def(1) T.ranked_dtree_orig_normalize1 by blast
    then show ?thesis using zs_def eq by force
  qed
qed

lemma merge1_dverts_optimal:
  assumes "\<exists>x. fwd_sub root (dverts t) x"
  shows "\<exists>zs. fwd_sub root (dverts (merge1 t)) zs
        \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
  using assms forward_UV_lists_argmin_ex by simp

theorem ikkbz_sub_dverts_optimal:
  assumes "\<exists>x. fwd_sub root (dverts t) x"
  shows "\<exists>zs. fwd_sub root (dverts (ikkbz_sub t)) zs
        \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
using assms ranked_dtree_with_orig_axioms proof(induction t rule: ikkbz_sub.induct)
  case (1 t)
  then interpret T: ranked_dtree_with_orig t by simp
  interpret NT: ranked_dtree_with_orig "normalize t"
    using T.ranked_dtree_orig_normalize by blast
  show ?case
  proof(cases "max_deg t \<le> 1")
    case True
    then show ?thesis using "1.prems"(1) forward_UV_lists_argmin_ex by auto
  next
    case False
    then have 0: "\<not> (max_deg t \<le> 1 \<or> \<not> list_dtree t)" using T.list_dtree_axioms by auto
    obtain zs where zs_def: "fwd_sub root (dverts (merge1 (normalize t))) zs"
        "\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as)"
      using "1.prems" T.normalize_dverts_optimal NT.merge1_dverts_eq by auto
    have "\<exists>zs. fwd_sub root (dverts (ikkbz_sub (merge1 (normalize t)))) zs
          \<and> (\<forall>as. fwd_sub root (dverts (merge1 (normalize t))) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
      using "1.IH" 0 zs_def(1) T.merge1_normalize_ranked_dtree_orig by blast
    then show ?thesis using zs_def 0 by force
  qed
qed

lemma ikkbz_sub_dverts_optimal':
  assumes "hd (Dtree.root t) = root" and "max_deg t \<le> 1 \<Longrightarrow> dom_children t T"
  shows "\<exists>zs. fwd_sub root (dverts (ikkbz_sub t)) zs
        \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
  using ikkbz_sub_dverts_optimal Q_denormalize_ikkbz_sub assms by blast

lemma combine_strict_subtree_orig:
  assumes "strict_subtree (Node r1 {|(t2,e2)|}) (Node (r@Dtree.root t1) (sucs t1))"
    shows "is_subtree (Node r1 {|(t2,e2)|}) (Node r {|(t1,e1)|})"
proof -
  obtain t3 where t3_def: "t3 \<in> fst ` fset (sucs t1)" "is_subtree (Node r1 {|(t2,e2)|}) t3"
    using assms unfolding strict_subtree_def by force
  then show ?thesis using subtree_trans subtree_if_suc[OF t3_def(1)] by auto
qed

lemma combine_subtree_orig_uneq:
  assumes "is_subtree (Node r1 {|(t2,e2)|}) (Node (r@Dtree.root t1) (sucs t1))"
  shows "Node r1 {|(t2,e2)|} \<noteq> Node r {|(t1,e1)|}"
proof -
  have "size (Node r1 {|(t2,e2)|}) \<le> size (Node (r@Dtree.root t1) (sucs t1))"
    using assms(1) subtree_size_le by blast
  also have "size (Node (r@Dtree.root t1) (sucs t1)) < size (Node r {|(t1,e1)|})"
    using dtree_size_skip_decr1 by fast
  finally show ?thesis by blast
qed

lemma combine_strict_subtree_ranks_le:
  assumes "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) (Node r {|(t1,e1)|})
              \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "strict_subtree (Node r1 {|(t2,e2)|}) (Node (r@Dtree.root t1) (sucs t1))"
    shows "rank (rev r1) \<le> rank (rev (Dtree.root t2))"
  using combine_strict_subtree_orig assms unfolding strict_subtree_def
  by (fast intro!: combine_subtree_orig_uneq )

lemma subtree_child_uneq:
  "\<lbrakk>is_subtree t1 t2; t2 \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> t1 \<noteq> Node r xs"
  using child_uneq subtree_antisym subtree_if_child by fast

lemma subtree_singleton_child_uneq:
  "is_subtree t1 t2 \<Longrightarrow> t1 \<noteq> Node r {|(t2,e2)|}"
  using subtree_child_uneq[of t1] by simp

lemma child_subtree_ranks_le_if_strict_subtree:
  assumes "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) (Node r {|(t1,e1)|})
              \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "is_subtree (Node r1 {|(t2,e2)|}) t1"
    shows "rank (rev r1) \<le> rank (rev (Dtree.root t2))"
  using assms subtree_trans subtree_singleton_child_uneq unfolding strict_subtree_def by fastforce

lemma verts_ge_child_if_sorted:
  assumes "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) (Node r {|(t1,e1)|})
              \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "max_deg (Node r {|(t1,e1)|}) \<le> 1"
      and "v \<in> dverts t1"
    shows "rank (rev (Dtree.root t1)) \<le> rank (rev v)"
proof -
  have "\<And>r1 t2 e2. is_subtree (Node r1 {|(t2,e2)|}) t1 \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
    using child_subtree_ranks_le_if_strict_subtree[OF assms(1)] by simp
  moreover have "max_deg t1 \<le> 1" using mdeg_ge_child[of t1 e1 "{|(t1,e1)|}"] assms(2) by simp
  ultimately show ?thesis using rank_ge_if_mdeg_le1_dvert_nocontr assms(3) by fastforce
qed

lemma verts_ge_child_if_sorted':
  assumes "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) (Node r {|(t1,e1)|})
              \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "max_deg (Node r {|(t1,e1)|}) \<le> 1"
      and "v \<in> dverts (Node r {|(t1,e1)|})"
      and "v \<noteq> r"
    shows "rank (rev (Dtree.root t1)) \<le> rank (rev v)"
  using verts_ge_child_if_sorted[OF assms(1,2)] assms(3,4) by simp

lemma not_combined_sub_dverts_combine:
  "{r@Dtree.root t1} \<union> {x. x \<in> dverts (Node r {|(t1,e1)|}) \<and> x \<noteq> r \<and> x \<noteq> Dtree.root t1}
        \<subseteq> dverts (Node (r @ Dtree.root t1) (sucs t1))"
  using dverts_suc_subseteq dverts_root_or_suc by fastforce

lemma dverts_combine_orig_not_combined:
  assumes "wf_dlverts (Node r {|(t1,e1)|})" and "x \<in> dverts (Node (r @ Dtree.root t1) (sucs t1))" and "x \<noteq> r@Dtree.root t1"
  shows "x \<in> dverts (Node r {|(t1,e1)|}) \<and> x \<noteq> r \<and> x \<noteq> Dtree.root t1"
proof -
  obtain t2 where t2_def: "t2 \<in> fst ` fset (sucs t1)" "x \<in> dverts t2" using assms(2,3) by fastforce
  have "set r \<inter> dlverts t2 = {}" using assms(1) suc_in_dlverts'[OF t2_def(1)] by auto
  then have "x \<noteq> r" using assms(1) t2_def(2) nempty_inter_notin_dverts by auto
  have "Dtree.root t1 \<noteq> []"
    using assms(1) empty_notin_wf_dlverts single_subtree_child_root_dverts[OF self_subtree, of t1]
    by force
  moreover have "set (Dtree.root t1) \<inter> dlverts t2 = {}"
    using assms(1) t2_def(1) notin_dlverts_suc_if_wf_in_root by fastforce
  ultimately have "x \<noteq> Dtree.root t1" using nempty_inter_notin_dverts t2_def(2) by blast
  then show ?thesis using \<open>x \<noteq> r\<close> t2_def dverts_suc_subseteq by auto
qed

lemma dverts_combine_sub_not_combined:
  "wf_dlverts (Node r {|(t1,e1)|}) \<Longrightarrow> dverts (Node (r @ Dtree.root t1) (sucs t1))
  \<subseteq> {r@Dtree.root t1} \<union> {x. x \<in> dverts (Node r {|(t1,e1)|}) \<and> x \<noteq> r \<and> x \<noteq> Dtree.root t1}"
  using dverts_combine_orig_not_combined by fast

lemma dverts_combine_eq_not_combined:
  "wf_dlverts (Node r {|(t1,e1)|}) \<Longrightarrow> dverts (Node (r @ Dtree.root t1) (sucs t1))
  = {r@Dtree.root t1} \<union> {x. x \<in> dverts (Node r {|(t1,e1)|}) \<and> x \<noteq> r \<and> x \<noteq> Dtree.root t1}"
  using dverts_combine_sub_not_combined not_combined_sub_dverts_combine by fast

lemma normalize_full_dverts_optimal_if_sorted:
  assumes "asi rank root cost"
      and "wf_dlverts t1"
      and "\<forall>xs \<in> (dverts t1). distinct xs"
      and "\<forall>xs \<in> (dverts t1). seq_conform xs"
      and "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) t1
            \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      and "max_deg t1 \<le> 1"
      and "hd (Dtree.root t1) = root"
      and "dom_children t1 T"
    shows "\<exists>zs. fwd_sub root (dverts (normalize_full t1)) zs
          \<and> (\<forall>as. fwd_sub root (dverts t1) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
using assms proof(induction t1 rule: normalize_full.induct)
  case (1 r t e)
  let ?Y = "dverts (Node r {|(t,e)|})"
  have dsjt: "\<forall>xs \<in> ?Y. \<forall>ys \<in> ?Y. xs = ys \<or> set xs \<inter> set ys = {}"
    using dverts_same_if_set_wf[OF "1.prems"(2)] by blast
  have fwd: "\<forall>xs \<in> ?Y. forward xs" using "1.prems"(4) seq_conform_alt by blast
  have nempty: "[] \<notin> ?Y" using empty_notin_wf_dlverts "1.prems"(2) by blast
  have fin: "finite ?Y" by (simp add: finite_dverts)
  have U: "r \<in> dverts (Node r {|(t, e)|})" by simp
  have V: "Dtree.root t \<in> dverts (Node r {|(t, e)|})"
    using single_subtree_child_root_dverts self_subtree by fast
  have ge: "\<forall>xs\<in>dverts (Node r {|(t, e)|}). xs \<noteq> r \<longrightarrow> rank (rev (Dtree.root t)) \<le> rank (rev xs)"
    using verts_ge_child_if_sorted'[OF "1.prems"(5,6)] by fast
  moreover have bfr: "before r (Dtree.root t)"
    using before_if_dom_children_wf_conform[OF "1.prems"(8,4,2)].
  moreover have Ex: "\<exists>x. fwd_sub root ?Y x" using Q_denormalize_full "1.prems"(1-8) by blast
  ultimately obtain zs where zs_def:
      "fwd_sub root ({r@Dtree.root t} \<union> {x. x \<in> ?Y \<and> x \<noteq> r \<and> x \<noteq> Dtree.root t}) zs"
      "(\<forall>as. fwd_sub root ?Y as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using app_UV_set_optimal_cost[OF "1.prems"(1) dsjt fwd nempty fin U V] by blast
  have wf: "wf_dlverts (Node (r @ Dtree.root t) (sucs t))" using "1.prems"(2) combine_wf_dlverts by fast
  moreover have dst: "\<forall>v\<in>dverts (Node (r @ Dtree.root t) (sucs t)). distinct v"
    using "1.prems"(2,3) combine_distinct by fast
  moreover have seq: "\<forall>v\<in>dverts (Node (r @ Dtree.root t) (sucs t)). seq_conform v"
      using "1.prems"(2,4,8) combine_conform by blast
  moreover have rnk: "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) (Node (r @ Dtree.root t) (sucs t))
                  \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
      using combine_strict_subtree_ranks_le[OF "1.prems"(5)] by simp
  moreover have mdeg: "max_deg (Node (r @ Dtree.root t) (sucs t)) \<le> 1"
    using "1.prems"(6) mdeg_child_sucs_le
    by (fastforce dest: order_trans simp del: max_deg.simps)
  moreover have hd: "hd (Dtree.root (Node (r @ Dtree.root t) (sucs t))) = root"
      using "1.prems"(2,7) by simp
  moreover have dom: "dom_children (Node (r @ Dtree.root t) (sucs t)) T"
      using "1.prems"(8) dom_children_combine by auto
    ultimately obtain xs where xs_def:
      "fwd_sub root (dverts (normalize_full (Node (r @ Dtree.root t) (sucs t)))) xs"
      "(\<forall>as. fwd_sub root (dverts (Node (r @ Dtree.root t) (sucs t))) as
          \<longrightarrow> cost (rev xs) \<le> cost (rev as))"
    using "1.IH" "1.prems"(1) by blast
  then show ?case using dverts_combine_eq_not_combined[OF "1.prems"(2)] zs_def by force
next
  case (2 xs r)
  have Ex: "\<exists>x. fwd_sub root (dverts (Node r xs)) x"
    using Q_denormalize_full "2.prems"(1-8) by blast
  then show ?case using "2.hyps"(1) forward_UV_lists_argmin_ex by simp
qed

corollary normalize_full_dverts_optimal_if_sorted':
  assumes "max_deg t \<le> 1"
      and "hd (Dtree.root t) = root"
      and "dom_children t T"
      and "\<And>r1 t2 e2. strict_subtree (Node r1 {|(t2,e2)|}) t
            \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
    shows "\<exists>zs. fwd_sub root (dverts (normalize_full t)) zs
          \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
  using normalize_full_dverts_optimal_if_sorted asi_rank wf_lverts assms
  by (blast intro: verts_distinct verts_conform)

lemma normalize_full_normalize_dverts_optimal:
  assumes "max_deg t \<le> 1"
      and "hd (Dtree.root t) = root"
      and "dom_children t T"
    shows "\<exists>zs. fwd_sub root (dverts (normalize_full (normalize t))) zs
          \<and> (\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
proof -
  interpret NT: ranked_dtree_with_orig "normalize t"
    using ranked_dtree_orig_normalize by auto
  have mdeg: "max_deg (normalize t) \<le> 1" using assms(1) normalize_mdeg_eq wf_arcs by fastforce
  moreover from this have dom: "dom_children (normalize t) T"
    using assms(3) dom_mdeg_le1_normalize by fastforce
  moreover have hd: "hd (Dtree.root (normalize t)) = root"
    using assms(2) normalize_hd_root_eq' wf_lverts by blast
  moreover have "\<And>r1 t2 e2. \<lbrakk>is_subtree (Node r1 {|(t2,e2)|}) (normalize t)\<rbrakk>
          \<Longrightarrow> rank (rev r1) \<le> rank (rev (Dtree.root t2))"
    by (simp add: normalize_sorted_ranks)
  ultimately obtain xs where xs_def: "fwd_sub root (dverts (normalize_full (normalize t))) xs"
      "(\<forall>as. fwd_sub root (dverts (normalize t)) as \<longrightarrow> cost (rev xs) \<le> cost (rev as))"
    using NT.normalize_full_dverts_optimal_if_sorted' strict_subtree_def by blast
  obtain zs where zs_def: "fwd_sub root (dverts (normalize t)) zs"
      "(\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using normalize_dverts_optimal Q_denormalize_t assms by blast
  then show ?thesis using xs_def by force
qed

lemma single_set_distinct_sublist: "\<lbrakk>set ys = set x; distinct ys; sublist x ys\<rbrakk> \<Longrightarrow> x = ys"
  unfolding sublist_def
  by (metis DiffD2 append.assoc append.left_neutral append.right_neutral list.set_intros(1)
      append_Cons distinct_set_diff neq_Nil_conv distinct_app_trans_l)

lemma denormalize_optimal_if_mdeg_le1:
  assumes "max_deg t \<le> 1" and "hd (Dtree.root t) = root" and "dom_children t T"
  shows "\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev (denormalize t)) \<le> cost (rev as)"
proof -
  obtain zs where zs_def: "fwd_sub root (dverts (normalize_full (normalize t))) zs"
      "(\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as))"
    using normalize_full_normalize_dverts_optimal assms by blast
  have "dverts (normalize_full (normalize t)) = {denormalize t}"
    using normalize_full_normalize_dverts_eq_denormalize wf_lverts assms(1) by blast
  then show ?thesis
    using zs_def single_set_distinct_sublist by (auto simp: fwd_sub_def unique_set_r_def)
qed

theorem denormalize_ikkbz_sub_optimal:
  assumes "hd (Dtree.root t) = root" and "max_deg t \<le> 1 \<Longrightarrow> dom_children t T"
  shows "(\<forall>as. fwd_sub root (dverts t) as
          \<longrightarrow> cost (rev (denormalize (ikkbz_sub t))) \<le> cost (rev as))"
proof -
  obtain zs where zs_def: "fwd_sub root (dverts (ikkbz_sub t)) zs"
      "\<forall>as. fwd_sub root (dverts t) as \<longrightarrow> cost (rev zs) \<le> cost (rev as)"
    using ikkbz_sub_dverts_optimal' assms by blast
  interpret T: ranked_dtree_with_orig "ikkbz_sub t" using ikkbz_sub_ranked_dtree_orig by simp
  have "max_deg (ikkbz_sub t) \<le> 1" using ikkbz_sub_mdeg_le1 by auto
  have "hd (Dtree.root (ikkbz_sub t)) = root" using assms(1) ikkbz_sub_hd_root by auto
  moreover have "dom_children (ikkbz_sub t) T"
    using assms(2) dom_mdeg_le1_ikkbz_sub ikkbz_sub_eq_iff_mdeg_le1 by auto
  ultimately have "\<forall>as. fwd_sub root (dverts (ikkbz_sub t)) as
              \<longrightarrow> cost (rev (denormalize (ikkbz_sub t))) \<le> cost (rev as)"
    using T.denormalize_optimal_if_mdeg_le1[OF ikkbz_sub_mdeg_le1] by blast
  then show ?thesis using zs_def order_trans by blast
qed

end

subsection \<open>Arc Invariants hold for Conversion to Dtree\<close>

context precedence_graph
begin

interpretation t: ranked_dtree to_list_dtree by (rule to_list_dtree_ranked_dtree)

lemma subtree_to_list_dtree_tree_dom:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; t \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> r \<rightarrow>\<^bsub>to_list_tree\<^esub> Dtree.root t"
  unfolding to_list_dtree_def
  using finite_directed_tree.subtree_child_dom to_list_tree_finite_directed_tree by fastforce

lemma subtree_to_list_dtree_dom:
  assumes "is_subtree (Node r xs) to_list_dtree" and "t \<in> fst ` fset xs"
  shows "hd r \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t)"
proof -
  interpret T: directed_tree to_list_tree "[root]" by (rule to_list_tree_directed_tree)
  have 0: "r \<rightarrow>\<^bsub>to_list_tree\<^esub> Dtree.root t" using subtree_to_list_dtree_tree_dom assms by blast
  then obtain x where x_def: "r = [x] \<and> x \<in> verts T" using to_list_tree_single by force
  obtain y where "Dtree.root t = [y]" using 0 to_list_tree_single T.adj_in_verts(2) by blast
  then show ?thesis using 0 to_list_tree_def x_def(1) in_arcs_imp_in_arcs_ends by force
qed

lemma to_list_dtree_nempty_root: "is_subtree (Node r xs) to_list_dtree \<Longrightarrow> r \<noteq> []"
  using list_dtree.list_dtree_sub list_dtree.wf_lverts to_list_dtree_list_dtree by force

lemma dom_children_aux:
  assumes "is_subtree (Node r xs) to_list_dtree"
      and "max_deg t1 \<le> 1"
      and "(t1,e1) \<in> fset xs"
      and "x \<in> dlverts t1"
    shows "\<exists>v \<in> set r \<union> path_lverts t1 x. v \<rightarrow>\<^bsub>T\<^esub> x"
proof(cases "x \<in> set (Dtree.root t1)")
  case True
  have "Dtree.root t1 \<in> dverts to_list_dtree"
    using assms(1,3) dverts_subtree_subset dtree.set_sel(1) by fastforce
  then have "Dtree.root t1 = [x]" using to_list_dtree_single True by fastforce
  then have 0: "hd r \<rightarrow>\<^bsub>T\<^esub> x" using subtree_to_list_dtree_dom assms(1,3) by fastforce
  have "r \<in> dverts to_list_dtree" using assms(1) dverts_subtree_subset by force
  then have "r = [hd r]" using to_list_dtree_single True by fastforce
  then have "hd r \<in> set r" using hd_in_set[of r] by blast
  then show ?thesis using 0 by blast
next
  case False
  obtain t2 where t2_def: "is_subtree t2 t1" "x \<in> set (Dtree.root t2)"
    using assms(4) subtree_root_if_dlverts by fastforce
  then obtain r1 xs1 where r1_def: "is_subtree (Node r1 xs1) t1" "t2 \<in> fst ` fset xs1"
    using subtree_child_if_strict_subtree t2_def False unfolding strict_subtree_def by blast
  have "is_subtree (Node r1 xs1) (Node r xs)" using r1_def(1) assms(3) by auto
  then have sub_r1: "is_subtree (Node r1 xs1) to_list_dtree" using assms(1) subtree_trans by blast
  have sub_t1_r: "is_subtree t1 (Node r xs)"
    using subtree_if_child[of t1 xs] assms(3) by force
  then have "is_subtree t2 to_list_dtree" using assms(1) subtree_trans t2_def(1) by blast
  then have "Dtree.root t2 \<in> dverts to_list_dtree"
    using assms(1) dverts_subtree_subset dtree.set_sel(1) by fastforce
  then have "Dtree.root t2 = [x]" using to_list_dtree_single t2_def(2) by force
  then have 0: "hd r1 \<rightarrow>\<^bsub>T\<^esub> x" using subtree_to_list_dtree_dom[OF sub_r1] r1_def(2) by fastforce
  have sub_t1_to: "is_subtree t1 to_list_dtree" using sub_t1_r assms(1) subtree_trans by blast
  then have "wf_dlverts t1" using t.wf_lverts list_dtree_def t.list_dtree_sub by blast
  moreover have "max_deg t1 \<le> 1" using assms(2) sub_t1_r le_trans mdeg_ge_sub by blast
  ultimately have "set r1 \<subseteq> path_lverts t1 x"
    using subtree_path_lverts_sub r1_def t2_def(2) by fast
  then show ?thesis
    using 0 sub_r1 dverts_subtree_subset hd_in_set[of r1] to_list_dtree_single by force
qed

lemma hd_dverts_in_dlverts:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; (t1,e1) \<in> fset xs; x \<in> dverts t1\<rbrakk> \<Longrightarrow> hd x \<in> dlverts t1"
  using list_dtree.list_dtree_rec list_dtree.wf_lverts hd_in_lverts_if_wf t.list_dtree_sub
  by fastforce

lemma dom_children_aux2:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; max_deg t1 \<le> 1; (t1,e1) \<in> fset xs; x \<in> dverts t1\<rbrakk>
    \<Longrightarrow> \<exists>v \<in> set r \<union> path_lverts t1 (hd x). v \<rightarrow>\<^bsub>T\<^esub> (hd x)"
  using dom_children_aux hd_dverts_in_dlverts by blast

lemma dom_children_full:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; \<forall>t \<in> fst ` fset xs. max_deg t \<le> 1\<rbrakk>
     \<Longrightarrow> dom_children (Node r xs) T"
  unfolding dom_children_def using dom_children_aux2 by auto

lemma dom_children':
  assumes "is_subtree (Node r xs) to_list_dtree"
  shows "dom_children (Node r (Abs_fset (children_deg1 xs))) T"
  unfolding dom_children_def dtree.sel children_deg1_fset_id
  using dom_children_aux2[OF assms(1)] by fastforce

lemma dom_children_maxdeg_1:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; max_deg (Node r xs) \<le> 1\<rbrakk>
     \<Longrightarrow> dom_children (Node r xs) T"
proof (elim dom_children_full)
  show "max_deg (Node r xs) \<le> 1 \<Longrightarrow> \<forall>t\<in>fst ` fset xs. max_deg t \<le> 1"
    using mdeg_ge_child by fastforce
qed

lemma dom_child_subtree:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; t \<in> fst ` fset xs\<rbrakk> \<Longrightarrow> \<exists>v\<in>set r. v \<rightarrow>\<^bsub>T\<^esub> hd (Dtree.root t)"
  using subtree_to_list_dtree_dom hd_in_set to_list_dtree_nempty_root by blast

lemma dom_children_maxdeg_1_self:
  "max_deg to_list_dtree \<le> 1 \<Longrightarrow> dom_children to_list_dtree T"
  using dom_children_maxdeg_1[of "Dtree.root to_list_dtree" "sucs to_list_dtree"] self_subtree by auto

lemma seq_conform_list_tree: "\<forall>v\<in>verts to_list_tree. seq_conform v"
  by (simp add: to_list_tree_def seq_conform_single)

lemma conform_list_dtree: "\<forall>v\<in>dverts to_list_dtree. seq_conform v"
  using seq_conform_list_tree dverts_eq_verts_to_list_tree by blast

lemma to_list_dtree_vert_single: "\<lbrakk>v \<in> dverts to_list_dtree; x \<in> set v\<rbrakk> \<Longrightarrow> v = [x] \<and> x \<in> verts T"
  using to_list_dtree_single by fastforce

lemma to_list_dtree_vert_single_sub:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; x \<in> set r\<rbrakk> \<Longrightarrow> r = [x] \<and> x \<in> verts T"
  using to_list_dtree_vert_single dverts_subtree_subset by fastforce

lemma to_list_dtree_child_if_to_list_tree_arc:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; r \<rightarrow>\<^bsub>to_list_tree\<^esub> v\<rbrakk> \<Longrightarrow> \<exists>ys. (Node v ys) \<in> fst ` fset xs"
  using finite_directed_tree.child_if_dominated_to_dtree'[OF to_list_tree_finite_directed_tree]
  unfolding to_list_dtree_def by simp

lemma to_list_dtree_child_if_arc:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk>
    \<Longrightarrow> \<exists>ys. Node [y] ys \<in> fst ` fset xs"
  using to_list_dtree_child_if_to_list_tree_arc to_list_tree_dom_iff to_list_dtree_vert_single_sub
  by auto

lemma to_list_dtree_dverts_if_arc:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> [y] \<in> dverts (Node r xs)"
  using to_list_dtree_child_if_arc[of r xs x y] by fastforce

lemma to_list_dtree_dlverts_if_arc:
  "\<lbrakk>is_subtree (Node r xs) to_list_dtree; x \<in> set r; x \<rightarrow>\<^bsub>T\<^esub> y\<rbrakk> \<Longrightarrow> y \<in> dlverts (Node r xs)"
  using to_list_dtree_child_if_arc[of r xs x y] by fastforce

theorem to_list_dtree_ranked_orig: "ranked_dtree_with_orig to_list_dtree rank cost cmp T root"
  using dom_children' to_list_dtree_dlverts_if_arc asi_rank apply(unfold_locales)
  by (auto simp: dom_children_maxdeg_1 dom_child_subtree distinct_to_list_dtree conform_list_dtree)

interpretation t: ranked_dtree_with_orig to_list_dtree by (rule to_list_dtree_ranked_orig)

lemma forward_ikkbz_sub: "forward ikkbz_sub"
  using ikkbz_sub_def dom_children_maxdeg_1_self t.ikkbz_sub_forward by simp

subsection \<open>Optimality of IKKBZ-Sub\<close>

lemma ikkbz_sub_optimal_Q:
  "(\<forall>as. fwd_sub root (verts to_list_tree) as \<longrightarrow> cost (rev ikkbz_sub) \<le> cost (rev as))"
  using t.denormalize_ikkbz_sub_optimal to_list_dtree_hd_root_eq_root dom_children_maxdeg_1_self
  unfolding dverts_eq_verts_to_list_tree ikkbz_sub_def by blast

lemma to_list_tree_sublist_if_set_eq:
  assumes "set ys = \<Union>(set ` verts to_list_tree)" and "xs \<in> verts to_list_tree"
  shows "sublist xs ys"
proof -
  obtain x where x_def: "xs = [x]" "x \<in> verts T" using to_list_tree_single assms(2) by blast
  then have "x \<in> set ys" using assms(1) to_list_tree_def by simp
  then show ?thesis using x_def(1) split_list[of x ys] sublist_Cons sublist_append_leftI by fast
qed

lemma hd_eq_tk1_if_set_eq_verts: "set xs = verts T \<Longrightarrow> hd xs = root \<longleftrightarrow> take 1 xs = [root]"
  using hd_eq_take1 take1_eq_hd[of xs] non_empty by fastforce

lemma ikkbz_sub_optimal:
  "\<lbrakk>set xs = verts T; distinct xs; forward xs; hd xs = root\<rbrakk>
    \<Longrightarrow> cost (rev ikkbz_sub) \<le> cost (rev xs)"
  using ikkbz_sub_optimal_Q to_list_tree_sublist_if_set_eq
  by (simp add: hd_eq_tk1_if_set_eq_verts to_list_tree_union_verts_eq fwd_sub_def unique_set_r_def)

end

subsection \<open>Optimality of IKKBZ\<close>

context ikkbz_query_graph
begin

text \<open>
Optimality only with respect to valid solutions (i.e. contain every relation exactly once).
Furthermore, only join trees without cross products are considered.
\<close>

lemma ikkbz_sub_optimal_cost_r:
  "\<lbrakk>set xs = verts G; distinct xs; no_cross_products (create_ldeep xs); hd xs = r; r \<in> verts G\<rbrakk>
    \<Longrightarrow> cost_r r (rev (ikkbz_sub r)) \<le> cost_r r (rev xs)"
  using precedence_graph.ikkbz_sub_optimal verts_dir_tree_r_eq
  by (fast intro: forward_if_ldeep_no_cross precedence_graph_r)

lemma ikkbz_sub_no_cross: "r \<in> verts G \<Longrightarrow> no_cross_products (create_ldeep (ikkbz_sub r))"
  using precedence_graph.forward_ikkbz_sub ikkbz_sub_verts_eq
  by (fastforce intro: no_cross_ldeep_if_forward' precedence_graph_r)

lemma ikkbz_sub_cost_r_eq_cost:
  "r \<in> verts G \<Longrightarrow> cost_r r (rev (ikkbz_sub r)) = cost_l (ikkbz_sub r)"
  using ikkbz_sub_verts_eq ikkbz_sub_distinct ikkbz_sub_no_cross ikkbz_sub_hd_eq_root
  by (fastforce dest: cost_correct')

corollary ikkbz_sub_optimal:
  "\<lbrakk>set xs = verts G; distinct xs; no_cross_products (create_ldeep xs); hd xs = r; r \<in> verts G\<rbrakk>
    \<Longrightarrow> cost_l (ikkbz_sub r) \<le> cost_l xs"
  using ikkbz_sub_optimal_cost_r cost_correct' ikkbz_sub_cost_r_eq_cost by fastforce

lemma ikkbz_no_cross: "no_cross_products (create_ldeep ikkbz)"
  using ikkbz_eq_ikkbz_sub ikkbz_sub_no_cross by force

lemma hd_in_verts_if_set_eq: "set xs = verts G \<Longrightarrow> hd xs \<in> verts G"
  using verts_nempty set_empty2[of xs] by force

lemma ikkbz_optimal:
  "\<lbrakk>set xs = verts G; distinct xs; no_cross_products (create_ldeep xs)\<rbrakk>
    \<Longrightarrow> cost_l ikkbz \<le> cost_l xs"
  using ikkbz_min_ikkbz_sub ikkbz_sub_optimal by (fastforce intro: hd_in_verts_if_set_eq)

theorem ikkbz_optimal_tree:
  "\<lbrakk>valid_tree t; no_cross_products t; left_deep t\<rbrakk> \<Longrightarrow> cost (create_ldeep ikkbz) \<le> cost t"
  using ikkbz_optimal inorder_eq_set by (fastforce simp: distinct_relations_def valid_tree_def)

end

end