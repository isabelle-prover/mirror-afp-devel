theory Abs_Extract_LMS_Verification
  imports "../abs-def/Abs_SAIS" Abs_Induce_Verification
begin

section "Extract LMS types Proofs"

lemma abs_extract_lms_correct:
  "xs <~~> [0..<length T] \<Longrightarrow>
   distinct (abs_extract_lms T xs) \<and> set (abs_extract_lms T xs) = {i. abs_is_lms T i}"
  by (metis comp_apply distinct_filter distinct_upt filter_set get_lms_correct
            get_lms_set_n_gre_length order.refl perm_distinct_iff perm_set_eq set_rev)

(*
lemma abs_extract_lms_length:
  "xs <~~> [0..<length T] \<Longrightarrow> length (abs_extract_lms T xs) = card {i. abs_is_lms T i}"
  by (metis distinct_card abs_extract_lms_all_lms abs_extract_lms_distinct)

lemma length_lms_remdups_filter:
  "T \<noteq> [] \<Longrightarrow> length (remdups (filter (\<lambda>i. abs_is_lms T i) SA)) < length T"
proof -
  assume "T \<noteq> []"

  have "set (filter (abs_is_lms T) SA) \<subseteq> {i. abs_is_lms T i}"
    by clarsimp

  have "card {i. abs_is_lms T i} < length T"
    by (simp add: \<open>T \<noteq> []\<close> card_abs_is_lms_bound)
  with card_mono[OF _ `set (filter (abs_is_lms T) SA) \<subseteq> {i. abs_is_lms T i}`]
  have "card (set (filter (abs_is_lms T) SA)) < length T"
    using dual_order.strict_trans2 lms_finite by blast
  with List.card_set[of "filter (\<lambda>i. abs_is_lms T i) SA"]
  show "length (remdups (filter (abs_is_lms T) SA)) < length T"
    by simp
qed
*)

lemma set_abs_extract_lms_eq_all_lms:
  "set (abs_extract_lms T [0..<length T]) = {i. abs_is_lms T i}"
  using abs_extract_lms_correct by blast

lemma distinct_abs_extract_lms:
  "distinct (abs_extract_lms T [0..<length T])"
  using abs_extract_lms_correct by blast

(*
lemma distinct_length_abs_extract_lms:
  "\<lbrakk>distinct xs; T \<noteq> []\<rbrakk> \<Longrightarrow> length (abs_extract_lms T xs) < length T"
  by (metis card_set comp_apply distinct_card distinct_filter length_lms_remdups_filter)
*)

(*
lemma filter_perm_set_eq:
  "xs <~~> ys \<Longrightarrow> set (filter P xs) = set (filter P ys)"
  by (metis filter_set perm_set_eq)
*)

lemma filter_abs_sa_induce_eq_all_lms:
  "\<lbrakk>set LMS = {i. abs_is_lms T i}; distinct LMS; valid_list T; strict_mono \<alpha>; \<alpha> bot = 0;
    Suc 0 < length T\<rbrakk> \<Longrightarrow>
   set (abs_extract_lms T (abs_sa_induce \<alpha> T LMS)) = {i. abs_is_lms T i}"
  using abs_extract_lms_correct abs_sa_induce_permutation by blast

lemma distinct_filter_abs_sa_induce:
  "\<lbrakk>set LMS = {i. abs_is_lms T i}; distinct LMS; valid_list T; strict_mono \<alpha>; \<alpha> bot = 0; 
    Suc 0 < length T\<rbrakk> \<Longrightarrow>
   distinct (abs_extract_lms T (abs_sa_induce \<alpha> T LMS))"
  using abs_extract_lms_correct abs_sa_induce_permutation by blast

end