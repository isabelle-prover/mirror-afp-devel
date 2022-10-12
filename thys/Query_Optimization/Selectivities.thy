(* Author: Bernhard Stöckl *)

theory Selectivities
  imports Complex_Main "HOL-Library.Multiset"
begin

section \<open>Selectivities\<close>

type_synonym 'a selectivity = "'a \<Rightarrow> 'a \<Rightarrow> real"

definition sel_symm :: "'a selectivity \<Rightarrow> bool" where
  "sel_symm sel = (\<forall>x y. sel x y = sel y x)"

definition sel_reasonable :: "'a selectivity \<Rightarrow> bool" where
  "sel_reasonable sel = (\<forall>x y. sel x y \<le> 1 \<and> sel x y > 0)"

subsection \<open>Selectivity Functions\<close>

fun list_sel_aux :: "'a selectivity \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> real" where
  "list_sel_aux sel x [] = 1"
| "list_sel_aux sel x (y#ys) = sel x y * list_sel_aux sel x ys"

fun list_sel :: "'a selectivity \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> real" where
  "list_sel sel [] y = 1"
| "list_sel sel (x#xs) y = list_sel_aux sel x y * list_sel sel xs y"

fun list_sel_aux' :: "'a selectivity \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> real" where
  "list_sel_aux' sel [] y = 1"
| "list_sel_aux' sel (x#xs) y = sel x y * list_sel_aux' sel xs y"

fun list_sel':: "'a selectivity \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> real" where
  "list_sel' sel x [] = 1"
| "list_sel' sel x (y#ys) = list_sel_aux' sel x y * list_sel' sel x ys"

definition set_sel_aux :: "'a selectivity \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> real" where
  "set_sel_aux sel x Y = (\<Prod>y \<in> Y. sel x y)"

definition set_sel :: "'a selectivity \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "set_sel sel X Y = (\<Prod>x \<in> X. set_sel_aux sel x Y)"

definition set_sel_aux' :: "'a selectivity \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "set_sel_aux' sel X y = (\<Prod>x \<in> X. sel x y)"

definition set_sel' :: "'a selectivity \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "set_sel' sel X Y = (\<Prod>y \<in> Y. set_sel_aux' sel X y)"

fun ldeep_s :: "'a selectivity \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> real" where
  "ldeep_s f [] = (\<lambda>_. 1)"
| "ldeep_s f (x#xs) = (\<lambda>a. if a=x then list_sel_aux' f xs a else ldeep_s f xs a)"

subsection \<open>Proofs\<close>

lemma distinct_alt: "(\<forall>x\<in># mset xs. count (mset xs) x = 1) \<longleftrightarrow> distinct xs"
  by(induction xs) auto

lemma mset_y_eq_list_sel_aux_eq: "mset y = mset z \<Longrightarrow> list_sel_aux f x y = list_sel_aux f x z"
proof(induction "length y" arbitrary: y z)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "length y > 0" by auto
  then obtain y' ys where y_def[simp]: "y=y'#ys" using list.exhaust_sel by blast
  have "length z > 0" using Suc by auto
  then obtain z' zs where z_def[simp]: "z=z'#zs" using list.exhaust_sel by blast
  then have "length zs = n" using Suc by (metis length_Cons mset_eq_length nat.inject)
  then show ?case
  proof(cases "y'=z'")
    case True
    then show ?thesis using Suc by simp
  next
    case False
    have "y' \<in># mset y" by simp
    moreover have "z' \<in># mset y" using Suc by simp
    ultimately have "\<exists>c. mset y = mset (y'#z'#c)"
      using False ex_mset in_set_member multi_member_split set_mset_mset
      by (metis (mono_tags, opaque_lifting) member_rec(1) mset.simps(2))
    then obtain c where c_def[simp]: "mset y = mset (y'#z'#c)" by blast
    then have 0: "mset ys = mset (z'#c)" by simp
    then have 1: "mset zs = mset (y'#c)" using Suc.prems by simp
    have "list_sel_aux f x y = list_sel_aux f x (y' # ys)" by simp
    also have "\<dots> = f x y' * list_sel_aux f x ys" by simp
    also have "\<dots> = f x y' * list_sel_aux f x (z'#c)" using Suc.hyps 0 by fastforce
    also have "\<dots> = f x z' * list_sel_aux f x (y'#c)" by simp
    also have "\<dots> = f x z' * list_sel_aux f x zs"
      using 1 Suc.hyps(1) \<open>length zs = n\<close> by presburger
    finally show ?thesis by simp
  qed
qed

lemma mset_y_eq_list_sel_eq: "mset y = mset y' \<Longrightarrow> list_sel f x y = list_sel f x y'"
  apply(induction x)
   apply(auto)[2]
  using mset_y_eq_list_sel_aux_eq by fast

lemma mset_x_eq_list_sel_eq: "mset x = mset z \<Longrightarrow> list_sel f x y = list_sel f z y"
proof(induction "length x" arbitrary: x z)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "length x > 0" by auto
  then obtain x' xs where y_def[simp]: "x=x'#xs" using list.exhaust_sel by blast
  have "length z > 0" using Suc by auto
  then obtain z' zs where z_def[simp]: "z=z'#zs" using list.exhaust_sel by blast
  then have "length zs = n" using Suc by (metis length_Cons mset_eq_length nat.inject)
  then show ?case
  proof(cases "x'=z'")
    case True
    then show ?thesis using Suc by simp
  next
    case False
    have "x' \<in># mset x" by simp
    moreover have "z' \<in># mset x" using Suc by simp
    ultimately have "\<exists>c. mset x = mset (x'#z'#c)"
      using False ex_mset in_set_member multi_member_split set_mset_mset
      by (metis (mono_tags, opaque_lifting) member_rec(1) mset.simps(2))
    then obtain c where c_def[simp]: "mset x = mset (x'#z'#c)" by blast
    then have 0: "mset xs = mset (z'#c)" by simp
    then have 1: "mset zs = mset (x'#c)" using Suc.prems by simp
    have "list_sel f x y = list_sel f (x'#xs) y" by simp
    also have "\<dots> = list_sel_aux f x' y * list_sel f xs y" by simp
    also have "\<dots> = list_sel_aux f x' y * list_sel f (z'#c) y" using Suc.hyps 0 by fastforce
    also have "\<dots> = list_sel_aux f z' y * list_sel f (x'#c) y" by simp
    also have "\<dots> = list_sel_aux f z' y * list_sel f zs y"
      using 1 Suc.hyps(1) \<open>length zs = n\<close> by presburger
    finally show ?thesis by simp
  qed
qed

lemma list_sel_empty: "list_sel f x [] = 1"
  by(induction x) auto

lemma list_sel'_empty: "list_sel' f [] y = 1"
  by(induction y) auto

lemma list_sel_symm_app:
    "sel_symm f \<Longrightarrow> list_sel_aux f x y * list_sel f y xs = list_sel f y (x # xs)"
  by(induction y) (auto simp: sel_symm_def)

lemma list_sel_symm: "sel_symm f \<Longrightarrow> list_sel f x y = list_sel f y x"
  by(induction x) (auto simp: sel_symm_def list_sel_empty list_sel_symm_app)

lemma list_sel_symm_aux_eq': "sel_symm f \<Longrightarrow> list_sel_aux f x y = list_sel_aux' f y x"
  by(induction y) (auto simp: sel_symm_def)

lemma list_sel_sing_aux': "list_sel f x [y] = list_sel_aux' f x y"
  by(induction x) auto

lemma list_sel_sing_aux: "list_sel f [x] y = list_sel_aux f x y"
  by(induction y) auto

lemma list_sel'_sing_aux': "list_sel' f x [y] = list_sel_aux' f x y"
  by(induction x) auto

lemma list_sel'_sing_aux: "list_sel' f [x] y = list_sel_aux f x y"
  by(induction y) auto

lemma list_sel'_split_aux: "list_sel' f (x#xs) y = list_sel_aux f x y * list_sel' f xs y"
  by(induction y) auto

lemma list_sel_eq': "list_sel f x y = list_sel' f x y"
  by(induction x) (auto simp: list_sel'_empty list_sel'_split_aux)

lemma mset_x_eq_list_sel_aux'_eq: "mset x = mset z \<Longrightarrow> list_sel_aux' f x y = list_sel_aux' f z y"
  using list_sel_sing_aux' mset_x_eq_list_sel_eq by metis

lemma foldl_acc_extr: "foldl (\<lambda>a b. a * f x b) z y = z * foldl (\<lambda>a b. a * f x b) (1::real) y"
proof(induction y arbitrary: z)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  have "foldl (\<lambda>a b. a * f x b) z (y # ys) = foldl (\<lambda>a b. a * f x b) (z * f x y) ys" by simp
  also have "\<dots> =  (z * f x y) * foldl (\<lambda>a b. a * f x b) 1 ys" using Cons by blast
  also have "\<dots> = z * foldl (\<lambda>a b. a * f x b) 1 (y#ys)"
    by (smt (verit, ccfv_SIG) Cons.IH foldl_Cons mult.assoc mult.left_commute)
  finally show ?case .
qed

lemma list_sel_aux_eq_foldl: "list_sel_aux f x y = foldl (\<lambda>a b. a * f x b) 1 y"
  apply(induction y)
   apply(auto)[2]
  using foldl_acc_extr by metis

lemma list_sel_eq_foldl: "list_sel f x y = foldl (\<lambda>a b. a * list_sel_aux f b y) 1 x"
  apply(induction x)
   apply(auto)[2]
  using foldl_acc_extr by metis

corollary list_sel_eq_foldl2: "list_sel f x y = foldl (\<lambda>a x. a * foldl (\<lambda>a b. a * f x b) 1 y) 1 x"
  by (simp add: list_sel_aux_eq_foldl list_sel_eq_foldl)

lemma list_sel_aux_eq_foldr: "list_sel_aux f x y = foldr (\<lambda>b a. a * f x b) y 1"
  by(induction y) auto

lemma sel_foldl_eq_foldr:
  "foldl (\<lambda>a b. a * f x b) 1 y = foldr (\<lambda>b a. a * (f::'a selectivity) x b) y 1"
  using list_sel_aux_eq_foldl list_sel_aux_eq_foldr by metis

lemma list_sel_eq_foldr: "list_sel f x y = foldr (\<lambda>b a. a * list_sel_aux f b y) x 1"
  by(induction x) auto

lemma list_sel_eq_foldr2: "list_sel f x y = foldr (\<lambda>x a. a * foldr (\<lambda>b a. a * f x b) y 1) x 1"
  by (simp add: list_sel_aux_eq_foldr list_sel_eq_foldr)

lemma list_sel_aux_reasonable:
    "sel_reasonable f \<Longrightarrow> list_sel_aux f x y \<le> 1 \<and> list_sel_aux f x y > 0"
  by(induction y) (auto simp: sel_reasonable_def mult_le_one)

lemma list_sel_aux'_reasonable:
    "sel_reasonable f \<Longrightarrow> list_sel_aux' f x y \<le> 1 \<and> list_sel_aux' f x y > 0"
  by(induction x) (auto simp: sel_reasonable_def mult_le_one)

lemma list_sel_reasonable: "sel_reasonable f \<Longrightarrow> list_sel f x y \<le> 1 \<and> list_sel f x y > 0"
  by(induction x) (auto simp: sel_reasonable_def mult_le_one list_sel_aux_reasonable)

lemma list_sel'_reasonable: "sel_reasonable f \<Longrightarrow> list_sel' f x y \<le> 1 \<and> list_sel' f x y > 0"
  using list_sel_eq' list_sel_reasonable by metis

lemma list_sel_aux_eq_set_sel_aux:
  "distinct ys \<Longrightarrow> list_sel_aux f x ys = set_sel_aux f x (set ys)"
  by(induction ys) (auto simp: set_sel_aux_def)

lemma list_sel_eq_set_sel:
  "\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow> list_sel f xs ys = set_sel f (set xs) (set ys)"
  by(induction xs) (auto simp: set_sel_def list_sel_aux_eq_set_sel_aux list_sel_empty)

lemma list_sel'_eq_set_sel:
  "\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow> list_sel' f xs ys = set_sel f (set xs) (set ys)"
  by (auto simp add: list_sel_eq' dest: list_sel_eq_set_sel)

lemma set_sel_symm_if_finite: "\<lbrakk>finite X; finite Y; sel_symm f\<rbrakk> \<Longrightarrow> set_sel f X Y = set_sel f Y X"
  using finite_distinct_list list_sel_symm list_sel_eq_set_sel by metis

lemma set_sel_aux_1_if_notfin: "\<not>finite Y \<Longrightarrow> set_sel_aux f x Y = 1"
  unfolding set_sel_aux_def by simp

lemma set_sel_1_if_notfin1: "\<not>finite X \<Longrightarrow> set_sel f X Y = 1"
  unfolding set_sel_def set_sel_aux_def by simp

lemma set_sel_1_if_notfin2: "\<not>finite Y \<Longrightarrow> set_sel f X Y = 1"
  unfolding set_sel_def set_sel_aux_def by simp

lemma set_sel_symm: "sel_symm f \<Longrightarrow> set_sel f X Y = set_sel f Y X"
  using set_sel_symm_if_finite[of X Y]
  by (fastforce simp: set_sel_1_if_notfin1 set_sel_1_if_notfin2)

lemma list_sel_aux'_eq_set_sel_aux':
  "distinct xs \<Longrightarrow> list_sel_aux' f xs x = set_sel_aux' f (set xs) x"
  by(induction xs) (auto simp: set_sel_aux'_def)

lemma list_sel'_eq_set_sel':
  "\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow> list_sel' f xs ys = set_sel' f (set xs) (set ys)"
  by(induction ys) (auto simp: set_sel'_def list_sel_aux'_eq_set_sel_aux' list_sel_empty)

lemma list_sel_eq_set_sel':
  "\<lbrakk>distinct xs; distinct ys\<rbrakk> \<Longrightarrow> list_sel f xs ys = set_sel' f (set xs) (set ys)"
  by (simp add: list_sel'_eq_set_sel' list_sel_eq')

lemma set_sel'_symm_if_finite: "\<lbrakk>finite X; finite Y; sel_symm f\<rbrakk> \<Longrightarrow> set_sel' f X Y = set_sel' f Y X"
  using finite_distinct_list list_sel_symm list_sel_eq_set_sel' by metis

lemma set_sel_aux'_1_if_notfin: "\<not>finite X \<Longrightarrow> set_sel_aux' f X y = 1"
  unfolding set_sel_aux'_def by simp

lemma set_sel'_1_if_notfin1: "\<not>finite X \<Longrightarrow> set_sel' f X Y = 1"
  unfolding set_sel'_def set_sel_aux'_def by simp

lemma set_sel'_1_if_notfin2: "\<not>finite Y \<Longrightarrow> set_sel' f X Y = 1"
  unfolding set_sel'_def set_sel_aux'_def by simp

lemma set_sel'_symm: "sel_symm f \<Longrightarrow> set_sel' f X Y = set_sel' f Y X"
  using set_sel'_symm_if_finite[of X Y]
  by (fastforce simp: set_sel'_1_if_notfin1 set_sel'_1_if_notfin2)

lemma set_sel'_eq_set_sel: "set_sel' f X Y = set_sel f X Y"
  unfolding set_sel_def set_sel_aux_def set_sel'_def set_sel_aux'_def using prod.swap by fast

lemma set_sel_aux_reasonable_fin:
  "\<lbrakk>finite y; sel_reasonable f\<rbrakk> \<Longrightarrow> set_sel_aux f x y \<le> 1 \<and> set_sel_aux f x y > 0"
  unfolding set_sel_aux_def
  by(induction y rule: finite_induct) (auto simp: sel_reasonable_def mult_le_one)

lemma set_sel_aux_reasonable:
  "sel_reasonable f \<Longrightarrow> set_sel_aux f x y \<le> 1 \<and> set_sel_aux f x y > 0"
  by(cases "finite y") (auto simp: set_sel_aux_reasonable_fin set_sel_aux_1_if_notfin)

lemma set_sel_aux'_reasonable_fin:
  "\<lbrakk>finite x; sel_reasonable f\<rbrakk> \<Longrightarrow> set_sel_aux' f x y \<le> 1 \<and> set_sel_aux' f x y > 0"
  unfolding set_sel_aux'_def
  by(induction x rule: finite_induct) (auto simp: sel_reasonable_def mult_le_one)

lemma set_sel_aux'_reasonable:
  "sel_reasonable f \<Longrightarrow> set_sel_aux' f x y \<le> 1 \<and> set_sel_aux' f x y > 0"
  by(cases "finite x") (auto simp: set_sel_aux'_reasonable_fin set_sel_aux'_1_if_notfin)

lemma set_sel_reasonable_fin:
  "\<lbrakk>finite x; sel_reasonable f\<rbrakk> \<Longrightarrow> set_sel f x y \<le> 1 \<and> set_sel f x y > 0"
  unfolding set_sel_def
  apply(induction x rule: finite_induct)
   using set_sel_aux'_reasonable_fin apply(simp)
  by (smt (verit) prod_le_1 prod_pos set_sel_aux_reasonable)

lemma set_sel_reasonable: "sel_reasonable f \<Longrightarrow> set_sel f x y \<le> 1 \<and> set_sel f x y > 0"
  by(cases "finite x") (auto simp: set_sel_reasonable_fin set_sel_1_if_notfin1)

lemma set_sel'_reasonable_fin:
  "\<lbrakk>finite y; sel_reasonable f\<rbrakk> \<Longrightarrow> set_sel' f x y \<le> 1 \<and> set_sel' f x y > 0"
  unfolding set_sel'_def
  apply(induction y rule: finite_induct)
   using set_sel_aux'_reasonable_fin apply(simp)
  by (smt (verit) prod_le_1 prod_pos set_sel_aux'_reasonable)

lemma set_sel'_reasonable: "sel_reasonable f \<Longrightarrow> set_sel' f x y \<le> 1 \<and> set_sel' f x y > 0"
  by (cases "finite y") (auto simp: set_sel'_reasonable_fin set_sel'_1_if_notfin2)

lemma ldeep_s_pos: "sel_reasonable f \<Longrightarrow> ldeep_s f xs x > 0"
  by (induction xs) (auto simp: list_sel_aux'_reasonable)

lemma distinct_app_trans_r: "distinct (ys@xs) \<Longrightarrow> distinct xs"
  by simp

lemma distinct_app_trans_l: "distinct (ys@xs) \<Longrightarrow> distinct ys"
  by simp

lemma ldeep_s_reasonable: "sel_reasonable f \<Longrightarrow> ldeep_s f xs y \<le> 1 \<and> ldeep_s f xs y > 0"
  by (induction xs) (auto simp: list_sel_aux'_reasonable)

lemma ldeep_s_eq_list_sel_aux'_split:
  "y \<in> set xs \<Longrightarrow> \<exists>as bs. as @ y # bs = xs \<and> ldeep_s sel xs y = list_sel_aux' sel bs y"
proof(induction xs)
  case (Cons x xs)
  then show ?case
  proof(cases "x = y")
    case False
    then obtain as bs where as_def: "as @ y # bs = xs" "ldeep_s sel xs y = list_sel_aux' sel bs y"
      using Cons by auto
    then have "(x#as) @ y # bs = x#xs" by simp
    then show ?thesis using False as_def(2) by fastforce
  qed(auto)
qed(simp)

lemma distinct_ldeep_s_eq_aux:
  "distinct xs \<Longrightarrow> \<exists>xs'. xs'@y#ys=xs \<Longrightarrow> ldeep_s f xs y = list_sel_aux' f ys y"
proof(induction xs arbitrary: ys)
  case (Cons x xs)
  then show ?case
  proof(cases "x=y \<and> ys=xs")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then have "\<exists>xs'. xs'@y#ys=x#xs \<and> xs' \<noteq> []" using Cons.prems by auto
    then have 0: "\<exists>xs''. x#xs''@y#ys=x#xs" by (metis list.sel(3) tl_append2)
    have 1: "distinct xs" using Cons.prems(1) by fastforce
    then show ?thesis
    proof(cases "x=y")
      case True
      then have "count (mset (x#xs)) x \<ge> 2" using 0 by auto
      then show ?thesis using Cons.prems by simp
    next
      case False
      then have "ldeep_s f (x # xs) y
              = (\<lambda>a. if a=x then list_sel_aux' f xs a else ldeep_s f xs a) y" by simp
      also have "\<dots> =  ldeep_s f xs y" using False by simp
      finally show ?thesis using Cons.IH 0 1 by simp
    qed
  qed
qed(simp)

lemma distinct_ldeep_s_eq_aux':
  "\<lbrakk>distinct xs; as @ y # bs = xs\<rbrakk> \<Longrightarrow> ldeep_s sel xs y = list_sel_aux' sel bs y"
  using distinct_ldeep_s_eq_aux by fast

lemma ldeep_s_last1_if_distinct: "distinct xs \<Longrightarrow> ldeep_s sel xs (last xs) = 1"
  by (induction xs) auto

lemma ldeep_s_revhd1_if_distinct: "distinct xs \<Longrightarrow> ldeep_s sel (rev xs) (hd xs) = 1"
  using ldeep_s_last1_if_distinct[of "rev xs"] by (simp add: last_rev)

lemma ldeep_s_1_if_nelem: "x \<notin> set xs \<Longrightarrow> ldeep_s sel xs x = 1"
  by (induction xs) auto

lemma distinct_xs_not_ys: "distinct (xs@ys) \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<notin> set ys"
  by auto

lemma distinct_ys_not_xs: "distinct (xs@ys) \<Longrightarrow> x \<in> set ys \<Longrightarrow> x \<notin> set xs"
  by auto

lemma distinct_change_order_first_eq_nempty:
  assumes "distinct (xs@ys@zs@rs)"
      and "ys \<noteq> []"
      and "zs \<noteq> []"
      and "take 1 (xs@ys@zs@rs) = take 1 (xs@zs@ys@rs)"
    shows "xs \<noteq> []"
proof
  assume "xs = []"
  then have "take 1 (ys@zs@rs) = take 1 (zs@ys@rs)" using assms(4) by simp
  then have "\<exists>r rs1 rs2. ys@zs@rs = r#rs1 \<and> zs@ys@rs = r#rs2"
    by (metis append_Cons append_take_drop_id assms(3) neq_Nil_conv take_eq_Nil zero_neq_one)
  then obtain r rs1 rs2 where r_def: "ys@zs@rs = r#rs1 \<and> zs@ys@rs = r#rs2" by blast
  then have 0: "r \<in> set ys \<and> r \<in> set zs"
    using assms(2,3) by (metis Cons_eq_append_conv list.set_intros(1))
  then show False using 0 assms(1) by auto
qed

lemma distinct_change_order_first_elem:
  "\<lbrakk>distinct (xs@ys@zs@rs); ys \<noteq> []; zs \<noteq> []; take 1 (xs@ys@zs@rs) = take 1 (xs@zs@ys@rs)\<rbrakk>
    \<Longrightarrow> take 1 (xs@ys@zs@rs) = take 1  xs"
  by (cases xs) (fastforce dest!: distinct_change_order_first_eq_nempty)+

lemma take1_singleton_app: "take 1 xs = [r] \<Longrightarrow> take 1 (xs@ys) = [r]"
  by (induction xs) (auto)

lemma hd_eq_take1: "take 1 xs = [r] \<Longrightarrow> hd xs = r"
  using hd_take[of 1 xs] by simp

lemma take1_eq_hd: "\<lbrakk>xs \<noteq> []; hd xs = r\<rbrakk> \<Longrightarrow> take 1 xs = [r]"
  by (simp add: take_Suc)

lemma nempty_if_take1: "take 1 xs = [r] \<Longrightarrow> xs \<noteq> []"
  by force

end