theory Valid_List
  imports Main "../util/List_Util"
begin

section \<open>Valid List\<close>

definition 
  valid_list :: "('a :: {linorder, order_bot}) list \<Rightarrow> bool"
where
  "valid_list s = (length s > 0 \<and> (\<forall>i < length s - 1. s ! i \<noteq> bot) \<and> last s = bot)"

lemma valid_list_ex_def:
  fixes s ::"('a :: {linorder, order_bot}) list"
  shows "(valid_list s) = 
           (\<exists>xs. s = xs @ [bot] \<and> 
                 (\<forall>i < length xs. xs ! i \<noteq> bot))"
unfolding valid_list_def
proof safe
  assume 
    "s \<noteq> []" 
    "\<forall>i<length s - 1. s ! i \<noteq> bot" 
    "last s = bot"
  then 
  show "\<exists>xs. s = xs @ [bot] \<and> 
             (\<forall>i<length xs. xs ! i \<noteq> bot)"
    by (metis append_butlast_last_id length_butlast nth_butlast)
qed (simp add: nth_append)+

lemma valid_list_iff_butlast_app_last:
  fixes s :: "('a :: {linorder, order_bot}) list"
  shows "valid_list s \<longleftrightarrow> 
            s \<noteq> [] \<and> 
            (\<forall>x \<in> set (butlast s). x \<noteq> bot) \<and> 
            last s = bot"
  by (metis append_butlast_last_id butlast_snoc in_set_conv_nth 
            valid_list_def valid_list_ex_def length_greater_0_conv)

lemma valid_list_consI:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes a :: 'a
  assumes "valid_list s"
  and "a \<noteq> bot" 
  shows "valid_list (a # s)"
  using assms 
  by (simp add: valid_list_iff_butlast_app_last)

lemma valid_list_consD:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes a :: 'a
  assumes "valid_list (a # s)"
  assumes "s \<noteq> []"
  shows "valid_list s"
  using assms
  by (simp add: valid_list_iff_butlast_app_last)

lemma Min_valid_list:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "Min (set s) = bot"
  by (metis assms List.finite_set Min.in_idem last_in_set min_bot valid_list_iff_butlast_app_last)

lemma valid_list_length:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "length s > 0"
  using assms
  by (clarsimp simp: valid_list_ex_def)

lemma valid_list_length_ex:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "\<exists>n. length s = Suc n"
  using assms
  by (clarsimp simp: valid_list_ex_def)

lemma valid_list_not_nil:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "s \<noteq> []"
  using assms by (simp add: valid_list_def)

lemma valid_list_Suc_mapping:
  fixes f :: "'a \<Rightarrow> nat"
  fixes s :: "'a list"
  shows "valid_list ((map (\<lambda>x. Suc (f x)) s) @ [bot])"
proof (induct s)
  case (Cons a s)
  note IH = this
  have "map (\<lambda>x. Suc (f x)) (a # s) = (Suc (f a)) # map (\<lambda>x. Suc (f x)) s"
    by simp
  moreover
  have "Suc (f a) \<noteq> bot"
    by (simp add: bot_nat_def)
  hence "valid_list ((Suc (f a)) # (map (\<lambda>x. Suc (f x)) s) @ [bot])"
    by (simp add: IH valid_list_consI)
  ultimately 
  show ?case
    by simp
qed (simp add: valid_list_ex_def)

lemma valid_list_app:
  assumes "valid_list (xs @ y # ys)"
  shows "valid_list (y # ys)"
  using assms
  by (induct xs) (simp add: valid_list_consD)+

lemma not_valid_list_app:
  assumes "valid_list (xs @ y # ys)"
  shows "\<not>valid_list xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case
    using valid_list_not_nil by auto
next
  case (Cons a xs)
  then show ?case
    by (metis Groups.add_ac(2) Nil_is_append_conv One_nat_def add_diff_cancel_left' append_Cons
              last_ConsL list.discI list.size(4) nth_Cons_0 valid_list_consD valid_list_def)
qed

lemma valid_list_neqE:
  assumes "valid_list xs" "valid_list ys" "xs \<noteq> ys"
  shows "\<exists>x y as bs cs. xs = as @ x # bs \<and> ys = as @ y # cs \<and> x \<noteq> y"
proof -
  note cases = list_neq_fc[OF assms(3)]
  moreover
  have "\<not>(\<exists>z zs. xs = ys @ z # zs)"
    using assms(1) assms(2) not_valid_list_app by blast
  moreover
  have "\<not>(\<exists>z zs. ys = xs @ z # zs)"
    using assms(1) assms(2) not_valid_list_app by blast
  ultimately show ?thesis
    by blast
qed

end