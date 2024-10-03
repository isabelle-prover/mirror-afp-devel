theory List_Type
  imports
    "../../util/Nat_Util"
    "../../util/Set_Util"
    "../../util/Fun_Util"     
    "../../util/List_Util"
    "../../order/Suffix_Util"
    "../../order/Valid_List_Util"
    "../../spec/Suffix_Array_Properties"
begin

text \<open>This theory file contains the background theory 
      for the SAIS algorithm (Nong et al., DCC 2009),
      which is essentially an optimisation of the 
      KA algorithm (Ko et al, JDA 2005).\<close>

section \<open>Small and Large List Types\<close>

datatype SL_types = S_type | L_type



text \<open>This section contains a generalisation of the suffix types to sequences of any type and
      any element comparison function that satisfies certain properties given the theorem.
      Typical constraints involve either one or a combination of @{const totalp_on},
      @{const irreflp_on}, @{const transp_on} and @{const asymp_on}.\<close>

definition 
  list_type :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> SL_types"
where
  "list_type cmp xs = 
    (if nslexordp cmp xs (suffix xs (Suc 0)) 
     then S_type 
     else L_type)"

lemma list_type_cons_same:
  "\<lbrakk>irreflp_on A cmp; x \<in> A\<rbrakk> \<Longrightarrow> list_type cmp (x # x # xs) = list_type cmp (x # xs)"
  by (clarsimp simp: list_type_def irreflp_onD)

lemma list_type_nil:
  "list_type cmp [] = L_type"
  by (clarsimp simp: list_type_def nslexordp_def)

lemma list_type_singleton:
  "list_type cmp [x] = S_type"
  by (simp add: nslexordp_def list_type_def)

lemma list_type_s_type_eq:
  "list_type cmp xs = S_type \<longleftrightarrow> nslexordp cmp xs (suffix xs (Suc 0))"
  by (simp add: list_type_def)

lemma list_type_l_type_eq:
  "list_type cmp xs = L_type \<longleftrightarrow> \<not>nslexordp cmp xs (suffix xs (Suc 0))"
  by (simp add: list_type_def)

lemma list_type_cons_diff1:
  "cmp x y \<Longrightarrow> list_type cmp (x # y # xs) = S_type"
  by (simp add: list_type_s_type_eq)

lemma list_type_cons_diff2:
  "\<lbrakk>\<not>cmp x y; x \<noteq> y\<rbrakk> \<Longrightarrow> list_type cmp (x # y # xs) = L_type"
  by (clarsimp simp add: list_type_l_type_eq)

lemma list_type_s_neq_nil:
  "list_type cmp xs = S_type \<Longrightarrow> xs \<noteq> []"
  by (metis SL_types.simps(2) list_type_nil)

lemma list_type_s_hd_cmp:
  "list_type cmp (x # y # xs) = S_type \<Longrightarrow> cmp x y \<or> x = y"
  by (metis SL_types.simps(2) list_type_cons_diff2)

lemma list_type_l_hd_cmp:
  "list_type cmp (x # y # xs) = L_type \<Longrightarrow> \<not>cmp x y \<or> x = y"
  by (metis SL_types.simps(2) list_type_cons_diff1)

lemma list_type_repl:
  "\<lbrakk>irreflp_on A cmp; x \<in> A; set xs = {x}\<rbrakk> \<Longrightarrow> list_type cmp (x # xs) = S_type"
  apply (induct xs; simp add: list_type_cons_same)
  using list_type_singleton subset_singletonD by fastforce

lemma list_type_s_ex:
  assumes "list_type cmp (x # xs) = S_type"
  shows "(\<forall>a \<in> set xs. a = x) \<or> (\<exists>b as bs. x # xs = as @ x # b # bs \<and> cmp x b \<and> (\<forall>k \<in> set as. k = x))"
proof -
  from list_type_s_type_eq[THEN iffD1, OF assms(1)]
  have "nslexordp cmp (x # xs) xs"
    by simp
  with nslexordp_cons2_exE[of cmp x xs]
  show ?thesis
    by blast
qed

lemma list_type_l_type_ex:
  assumes "list_type cmp (x # xs) = L_type"
  and     "totalp_on A cmp"
  and     "x \<in> A"
  and     "set xs \<subseteq> A"
  shows "\<exists>b as bs. x # xs = as @ x # b # bs \<and> cmp b x \<and> (\<forall>k \<in> set as. k = x)"
proof -
  from list_type_l_type_eq[THEN iffD1, OF assms(1)]
  have "\<not> nslexordp cmp (x # xs) xs"
    by simp
  moreover
  have "x # xs \<noteq> xs"
    by fastforce
  ultimately have "nslexordp cmp xs (x # xs)"
    using totalp_onD[OF nslexordp_totalp_on[OF assms(2)]]
    by (metis assms(3,4) insert_subset list.simps(15) mem_Collect_eq)
  with nslexordp_cons1_exE[of cmp xs x]
  show ?thesis
    by blast
qed

theorem l_less_than_s_type_list_type:
  assumes "list_type cmp (a # s1) = S_type"
  and     "list_type cmp (a # s2) = L_type"
  and     "totalp_on A cmp"
  and     "transp_on A cmp"
  and     "a \<in> A"
  and     "set s1 \<subseteq> A"
  and     "set s2 \<subseteq> A"
shows "nslexordp cmp (a # s2) (a # s1)"
proof -
  from list_type_l_type_ex[OF assms(2,3,5,7)]
  obtain b as bs where
    "a # s2 = as @ a # b # bs"
    "cmp b a"
    "\<forall>k\<in>set as. k = a"
    by blast
  hence S2: "a # s2 = replicate (length as) a @ a # b # bs"
    by (simp add: replicate_length_same)

  let ?c1 = "\<forall>x \<in> set s1. x = a"
  and ?c2 = "\<exists>d cs ds. a # s1 = cs @ a # d # ds \<and> cmp a d \<and> (\<forall>k\<in>set cs. k = a)"

  from list_type_s_ex[OF assms(1)]
  have "?c1 \<or> ?c2"
    by blast
  moreover
  have "?c1 \<Longrightarrow> ?thesis"
proof -
    assume ?c1

    have "length s1 \<le> length as \<Longrightarrow> ?thesis"
    proof -
      assume "length s1 \<le> length as"
      have "a # s1 = replicate (length s1) a @ [a]"
        by (metis \<open>?c1\<close> replicate_append_same replicate_length_same)
      hence "\<exists>es. replicate (length as) a  @ [a] = a # s1 @ es"
        by (metis \<open>length s1 \<le> length as\<close> le_add_diff_inverse list.simps(1) replicate_add
                  replicate_append_same)
      then show ?thesis
        by (metis S2 SL_types.simps(2) append.assoc append.right_neutral assms(1) assms(2)
                  list.sel(3) neq_Nil_conv nslexordpI2 nslexordp_cons_cons replicate_app_Cons_same)
    qed
    moreover
    have "length s1 > length as \<Longrightarrow> ?thesis"
    proof -
      assume "length s1 > length as"
      hence "\<exists>es. s1 = replicate (length as) a @ a # es"
        by (metis \<open>?c1\<close> add_Suc_right less_iff_Suc_add replicate_Suc replicate_add
                  replicate_length_same)
      then obtain es where
        "s1 = replicate (length as) a @ a # es"
        by blast
      hence S1: "a # s1 = replicate (length as) a @ a # a # es"
        by (simp add: replicate_app_Cons_same)
      then show ?thesis
        by (metis S2 \<open>cmp b a\<close> nslexordpI1 nslexordp_cons_cons replicate_app_Cons_same)
    qed
    ultimately show ?thesis
      by linarith
  qed
  moreover
  have "?c2 \<Longrightarrow> ?thesis"
  proof -
    assume ?c2
    then obtain d cs ds where
      "a # s1 = cs @ a # d # ds"
      "cmp a d"
      "\<forall>k\<in>set cs. k = a"
      by blast
    hence S1: "a # s1 = replicate (length cs) a @ a # d # ds"
      by (simp add: replicate_length_same)

    from transp_onD[OF assms(4) _ assms(5) _ \<open>cmp b a\<close> \<open>cmp a d\<close>]
    have "cmp b d"
      by (metis S1 S2 add_diff_cancel_left' assms(6,7) length_Cons length_append less_Suc_eq_le
                list.simps(1) nth_append_length nth_mem replicate_app_Cons_same subsetD zero_le
                zero_less_diff)
    hence "length cs = length as \<Longrightarrow> ?thesis"
      by (metis S1 S2 nslexordpI1 nslexordp_cons_cons replicate_app_Cons_same)
    moreover
    have "length as < length cs \<Longrightarrow> ?thesis"
    proof -
      assume "length as < length cs"
      hence "\<exists>es. replicate (length cs) a = replicate (length as) a @ a # es \<and>
                  (\<forall>k \<in> set es. k = a)"
        by (metis (no_types, lifting) Cons_nth_drop_Suc S1 \<open>a # s1 = cs @ a # d # ds\<close> add_Suc_right
                                      add_diff_cancel_left' append_same_eq drop_replicate
                                      in_set_replicate less_iff_Suc_add nth_mem replicate_add)
      then obtain es where
        "replicate (length cs) a = replicate (length as) a @ a # es"
        "\<forall>k \<in> set es. k = a"
        by blast
      then show ?thesis
        by (metis S1 S2 \<open>cmp b a\<close> append.assoc append_Cons nslexordpI1 replicate_app_Cons_same)
    qed
    moreover
    have "length cs < length as \<Longrightarrow> ?thesis"
    proof -
      assume "length cs < length as"
      hence "\<exists>es. replicate (length as) a = replicate (length cs) a @ a # es \<and>
                  (\<forall>k \<in> set es. k = a)"
        by (metis (no_types, lifting) Cons_nth_drop_Suc S2 \<open>a # s2 = as @ a # b # bs\<close> add_Suc_right
                                      add_diff_cancel_left' append_same_eq drop_replicate
                                      in_set_replicate less_iff_Suc_add nth_mem replicate_add)
      then obtain es where
        "replicate (length as) a = replicate (length cs) a @ a # es"
        "\<forall>k \<in> set es. k = a"
        by blast
      then show ?thesis
        by (metis S1 S2 \<open>cmp a d\<close> append.assoc append_Cons nslexordpI1 replicate_app_Cons_same)
    qed
    ultimately show ?thesis
      by linarith
  qed
  ultimately show ?thesis
    by blast
qed

lemma list_type_cons_diff_type1:
  "\<lbrakk>list_type cmp (a # b # xs) = S_type; list_type cmp (b # xs) = L_type\<rbrakk> \<Longrightarrow>
    cmp a b"
  by (simp add: list_type_l_type_eq list_type_s_type_eq)

lemma list_type_cons_diff_type2:
  "\<lbrakk>list_type cmp (a # b # xs) = L_type; list_type cmp (b # xs) = S_type\<rbrakk> \<Longrightarrow>
    \<not>cmp a b \<and> a \<noteq> b"
  by (simp add: list_type_l_type_eq list_type_s_type_eq)

section \<open>Suffix Type\<close>

text \<open>This section contains the suffix type definition.\<close>

definition suffix_type :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> SL_types"
  where
"suffix_type s i \<equiv>
  (if list_less_ns (suffix s i) (suffix s (Suc i)) then S_type
   else L_type)"

lemma suffix_type_list_type_eq:
  "suffix_type xs i = list_type (<) (suffix xs i)"
  by (clarsimp simp: suffix_type_def list_type_def nslexordp_eq_list_less_ns)

text \<open>There are two types of suffixes (@{typ SL_types}): @{term S_type} and @{term L_type}.
      An S-type suffix is a suffix that is strictly less than the suffix that occurs immediately
      after it, and an L-type suffix is a suffix that is strictly greater than the suffix that
      occurs immediately after it.
      The definition of less than used here is @{term list_less_ns}.
      Note that this definition of less than differs from lexicographical order(@{term list_less},
      i.e. dictionary order,
      but it is equivalent when the both lists are valid (@{term valid_list}) as shown in
      @{thm valid_list_list_less_equiv_list_less_ns}.
      There are three reasons for using the @{term list_less_ns} definition,
      and we explain in order of importance.

      The first reason is that the original suffix types definition required a special case for the
      singleton suffix that only contains the sentinel symbol.
      While this special case makes sense in regards to the algorithms,
      i.e. it is necessary for the correctness of the algorithms,
      it does not naturally follow from the intuition of suffix types.
      In fact, it contradicts the intuitive definition that follows from the lexicographical order
      @{term list_less}.
      That is, a list that only consists of one element is always strictly greater than the
      empty list.
      With the alternate definition of less than @{term list_less_ns},
      a proper prefix is always strictly greater, and so,
      a singleton list will always be strictly less than the empty list.
      Therefore, there is no need to have a special case for the singleton suffix that only
      contains the sentinel.

      The second reason is that the SAIS algorithm uses a sublist order that depends on the
      suffix type definition (see Section \"SAIS Sublist Order\").
      This definition is perfectly valid for the algorithm,
      since the ordering is only used for sublist of the same list.
      However, the ordering is not easily understandable when applied to arbitrary list,
      even though it is equivalent to @{term list_less_ns}, which we prove in a later section.
      As an ordering, @{term list_less_ns} is much easier to understand.
      It is also used within the definition of @{term suffix_type}.
      Therefore, it makes more sense to reuse @{term list_less_ns},
      rather than having multiple definitions of the same thing.

      The third reason is that the original suffix types definition does not handle the case
      where the suffix is not terminated by sentinel symbol.
      The reason for this is that it is assumed that all lists are terminated by the sentinel.
      This assumption is very important to the SAIS algorithm as it is central to its correctness
      argument.
      That being said, in terms of elegance and consistency,
      using @{term list_less_ns} requires the least amount of special cases.\<close>

subsection \<open>General Suffix Type Simplifications\<close>

text \<open>This section contains theorems that simplify the use of the definition @{term suffix_type}.\<close>

lemma suffix_type_cons_suc:
  "suffix_type (a # s) (Suc i) = suffix_type s i"
  by (simp add: suffix_type_def)

lemma suffix_type_cons_same:
  "suffix_type (x # x # xs) 0 = suffix_type (x # xs) 0"
  by (simp add: list_less_ns_cons_same suffix_type_def)

lemma suffix_type_suffix:
  "suffix_type s i = suffix_type (suffix s i) 0"
  by (simp add: suffix_type_list_type_eq)

lemma suffix_type_suffix_gen:
  "suffix_type (suffix s n) i = suffix_type s (i + n)"
  by (simp add: suffix_type_list_type_eq)

lemma suffix_type_eq_Suc:
  "suffix_type xs n = suffix_type xs (Suc n) \<Longrightarrow>
   suffix_type xs n = S_type \<or> suffix_type xs (Suc n) = L_type"
  using SL_types.exhaust by auto

subsection \<open>S-Type Simplifications\<close>

text \<open>This subsection contains theorems about facts that can be derived S-type suffixes and vice versa.\<close>

lemma suffix_is_bot:
  "suffix s i = [bot] \<Longrightarrow> suffix_type s i = S_type"
  by (simp add: list_type_singleton suffix_type_list_type_eq)

lemma suffix_is_singleton:
  "suffix s i = [x] \<Longrightarrow> suffix_type s i = S_type"
  by (simp add: list_type_singleton suffix_type_list_type_eq)

lemma suffix_type_last:
  "length xs = Suc n \<Longrightarrow> suffix_type xs n = S_type"
  by (simp add: list_less_ns_nil suffix_type_def)

lemma s_type_list_less_ns:
  "suffix_type s i = S_type \<longleftrightarrow> list_less_ns (suffix s i) (suffix s (Suc i))"
  by (metis SL_types.simps(2) suffix_type_def)

lemma nth_less_imp_s_type:
  "\<lbrakk>Suc i < length s; s ! i < s ! Suc i\<rbrakk> \<Longrightarrow> suffix_type s i = S_type"
  by (metis Cons_nth_drop_Suc Suc_lessD less_imp_le list_less_ns_cons neq_iff s_type_list_less_ns)

lemma sl_type_hd_less:
  "\<lbrakk>Suc i < length s; hd (suffix s i) < hd (suffix s (Suc i))\<rbrakk> \<Longrightarrow>
   suffix_type s i = S_type"
  by (simp add: hd_drop_conv_nth nth_less_imp_s_type)

lemma suffix_type_cons_less:
  "x < y \<Longrightarrow>  suffix_type (x # y # xs) 0 = S_type"
  by (clarsimp simp: suffix_type_def list_less_ns_cons_diff)

lemma suffix_type_s_bound:
  "suffix_type s i = S_type \<Longrightarrow> i < length s"
  using ordlistns.less_asym s_type_list_less_ns by fastforce

lemma s_type_letter_le_Suc:
  "\<lbrakk>Suc i < length T; suffix_type T i = S_type\<rbrakk> \<Longrightarrow>
    T ! i \<le> T ! (Suc i)"
  by (metis Cons_nth_drop_Suc Suc_lessD leI list_less_ns_cons_diff ordlistns.less_asym
        s_type_list_less_ns)

lemma s_type_ex:
  assumes "suffix_type (x # xs) 0 = S_type"
  shows "(\<forall>a \<in> set xs. a = x) \<or> (\<exists>b as bs. x # xs = as @ x # b # bs \<and> x < b \<and> (\<forall>k \<in> set as. k = x))"
  by (metis assms drop0 list_type_s_ex suffix_type_list_type_eq)

subsection \<open>L-Type Simplifications\<close>

text \<open>This subsection contains theorems about facts that can be derived from L-type suffixes and vice
versa.\<close>

lemma suffix_is_nil:
  "suffix s i = [] \<Longrightarrow> suffix_type s i = L_type"
  by (clarsimp simp: suffix_type_def split: if_splits)

lemma l_type_list_less_ns:
  "suffix_type s i = L_type \<longleftrightarrow> list_less_ns (suffix s (Suc i)) (suffix s i) \<or> suffix s i = []"
  by (metis Cons_nth_drop_Suc SL_types.distinct(1) drop_Nil drop_eq_Nil linorder_le_less_linear
            not_Cons_self2 ordlistns.less_imp_not_less ordlistns.neqE suffix_type_def
            suffix_type_suffix)

lemma nth_gr_imp_l_type:
  "\<lbrakk>Suc i < length s; s ! i > s ! Suc i\<rbrakk> \<Longrightarrow> suffix_type s i = L_type"
  by (metis Cons_nth_drop_Suc Suc_lessD list_less_ns_cons_diff ordlistns.less_asym suffix_type_def)

lemma sl_type_hd_greater:
  "\<lbrakk>Suc i < length s; hd (suffix s i) > hd (suffix s (Suc i))\<rbrakk> \<Longrightarrow>
   suffix_type s i = L_type"
  by (simp add: hd_drop_conv_nth nth_gr_imp_l_type)

lemma suffix_type_cons_greater:
  "x > y \<Longrightarrow>  suffix_type (x # y # xs) 0 = L_type"
  by (simp add: list_type_cons_diff2 suffix_type_list_type_eq)

lemma l_type_letter_gre_Suc:
  "\<lbrakk>i < length T; suffix_type T i = L_type\<rbrakk> \<Longrightarrow>
    T ! (Suc i) \<le> T ! i"
  by (metis SL_types.distinct(1) Suc_lessI not_less nth_less_imp_s_type suffix_type_last)

lemma l_type_ex:
  assumes "suffix_type (x # xs) 0 = L_type"
  shows "\<exists>b as bs. x # xs = as @ x # b # bs \<and> x > b \<and> (\<forall>k \<in> set as. k = x)"
  by (metis assms drop0 drop_Suc_Cons l_type_list_less_ns list.discI list_less_ns_cons1_exE)

text \<open>An overlooked property, but one that is crucial for completeness of the SAIS algorithm\<close>

lemma suffix_max_hd_is_l_type:
  assumes "valid_list s"
  and     "i < length s"
  and     "length s > Suc 0"
  and     "hd (suffix s i) = Max (set s)"
shows "suffix_type s i = L_type"
  using assms
proof (induct s arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a s i)
  note IH = this
  show ?case
  proof (cases s)
    case Nil
    then show ?thesis
      using IH(4) by auto
  next
    case (Cons b xs)
    assume "s = b # xs"
    show ?thesis
    proof (cases xs)
      case Nil
      hence "s = [b]"
        by (simp add: local.Cons)
      moreover
      have "b = bot"
        by (metis IH(2) last.simps local.Cons local.Nil not_Cons_self
                  valid_list_iff_butlast_app_last)
      moreover
      have "a > b"
        by (metis IH(2,4) One_nat_def antisym_conv3 bot.extremum_strict nth_Cons_0 valid_list_def
                  zero_less_diff calculation(2))
      ultimately show ?thesis
        by (metis IH(2,3,5) Max_greD add_diff_cancel_left' last_suffix_index length_Cons less_Suc0
                  linorder_not_less list.size(3) not_less_eq not_less_iff_gr_or_eq nth_Cons_0
                  plus_1_eq_Suc suffix_type_cons_greater)
    next
      case (Cons c ys)
      hence "s = b # c # ys"
        by (simp add: \<open>s = b # xs\<close>)
      show ?thesis
      proof (cases i)
        case 0
        hence "a \<ge> b"
          by (metis IH(4,5) List.finite_set Max_ge \<open>s = b # xs\<close> drop0 list.sel(1) nth_Cons_0
                    nth_Cons_Suc nth_mem)
        hence "a > b \<or> a = b"
          using antisym_conv1 by blast
        then show ?thesis
        proof 
          assume "b < a"
          then show ?thesis
            by (simp add: "0" \<open>s = b # xs\<close> suffix_type_cons_greater)
        next
          assume "a = b"
          hence "Max (set s) = b"
            using "0" IH(5) \<open>s = b # xs\<close> by auto
          with IH(1)[of 0]
          have "suffix_type s 0 = L_type"
            by (metis IH(2) Suc_less_eq2 \<open>s = b # xs\<close> drop0 drop_Suc_Cons length_Cons list.sel(1)
                      local.Cons valid_suffix zero_less_Suc)
          then show ?thesis
            by (simp add: "0" \<open>a = b\<close> \<open>s = b # xs\<close> suffix_type_cons_same)
        qed
      next
        case (Suc n)
        assume "i = Suc n"
        have "valid_list s"
          using IH(2) \<open>s = b # xs\<close> valid_list_consD by blast
        moreover
        have "n < length s"
          using IH(3) Suc by auto
        moreover
        have "Suc 0 < length s"
          by (simp add: \<open>s = b # xs\<close> local.Cons)
        moreover
        {
          have "hd (suffix s n) = hd (suffix (a # s) i)"
            using Suc by fastforce
          moreover
          have "hd (suffix s n) \<in> set s"
            by (simp add: \<open>n < length s\<close> hd_drop_conv_nth)
          with IH(5)
          have "Max (set (a # s)) \<in> set s"
            using calculation by argo
          hence "Max (set (a # s)) = Max (set s)"
            using IH(5) max.cobounded1[of a "Max (set s)"]
            by (metis List.finite_set Max_greD Max_insert Suc_lessD \<open>Suc 0 < length s\<close>
                      \<open>n < length s\<close> calculation hd_drop_conv_nth length_greater_0_conv list.set(2)
                      max_def set_empty)
          ultimately have "hd (suffix s n) = Max (set s)"
            using IH(5) by presburger
        }
        ultimately have "suffix_type s n = L_type"
          using Cons.hyps by blast
        then show ?thesis
          by (simp add: Suc suffix_type_cons_suc)
      qed
    qed
  qed
qed

subsection \<open>General Suffix Type Theories\<close>

text \<open>This subsection contains the background theory needed to prove that computing the suffix types
      of a list can be achieved in linear time by starting from the end of the list
      (lemma 1, Ko et al., JDA 2005).

      The main intuition is that the suffix type of the (i+1)th suffix is known and the ith suffix
      starts with same symbol of the (i+1)th suffix, then the ith suffix will have the same type.\<close>

theorem sl_type_hd_equal:
  "\<lbrakk>Suc i < length s; hd (suffix s i) = hd (suffix s (Suc i))\<rbrakk> \<Longrightarrow>
   suffix_type s i = suffix_type s (Suc i)"
  by (metis Cons_nth_drop_Suc Suc_lessD hd_drop_conv_nth l_type_letter_gre_Suc list_less_ns_cons
            suffix_type_def)

corollary sl_type_prefix_equal:
  "\<lbrakk>i + n \<le> length s; \<forall>j < n. hd (suffix s (i + j)) = hd (suffix s i)\<rbrakk> \<Longrightarrow>
   \<forall>j < n. suffix_type s (i + j) = suffix_type s i"
proof (induct n)
  case 0
  then show ?case
    by blast
next
  case (Suc n)
  note IH = this
  hence "\<forall>j<n. suffix_type s (i + j) = suffix_type s i"
    by (metis add_Suc_right less_Suc_eq linorder_not_less)
  show ?case
  proof safe
    fix j
    assume "j < Suc n"
    then show "suffix_type s (i + j) = suffix_type s i"
    proof (cases "j < n")
      assume "j < n"
      then show ?thesis
        by (simp add: \<open>\<forall>j<n. suffix_type s (i + j) = suffix_type s i\<close>)
    next
      assume "\<not> j < n"
      hence "j = n"
        using \<open>j < Suc n\<close> by auto
      show ?thesis
      proof (cases j)
        case 0
        then show ?thesis
          by simp
      next
        case (Suc m)
        then show ?thesis
          by (metis Suc.prems(1,2) Suc_lessD Suc_less_SucD \<open>j < Suc n\<close> \<open>j = n\<close> add_Suc_right
                    \<open>\<forall>j<n. suffix_type s (i + j) = suffix_type s i\<close> le_imp_less_Suc
                    sl_type_hd_equal)
      qed
    qed
  qed
qed

corollary sl_type_prefix_equal_nth:
  "\<lbrakk>i + n \<le> length s; \<forall>j < n. (suffix s i) ! j = (suffix s i) ! 0\<rbrakk> \<Longrightarrow>
   \<forall>j < n. suffix_type s (i + j) = suffix_type s i"
  by (rule sl_type_prefix_equal, assumption, clarsimp simp: hd_conv_nth)

corollary sl_type_prefix_replicate:
  "\<forall>i < n. suffix_type (replicate n a @ as) i = suffix_type (replicate n a @ as) 0"
  by (rule sl_type_prefix_equal_nth[where i = 0, simplified]; clarsimp simp: nth_append)

lemma suffix_type_neq:
  "\<lbrakk>suffix_type T j \<noteq> suffix_type T (Suc j); Suc j < length T\<rbrakk> \<Longrightarrow> T ! j \<noteq> T ! Suc j"
  by (metis Cons_nth_drop_Suc Suc_lessD l_type_letter_gre_Suc list_less_ns_cons suffix_type_def)


subsection \<open>S/L-Type Ordering\<close>

text \<open>This section contains the crucial theorem that L-type suffixes are always less than S-type
      suffixes if they start with the same symbol (lemma 2, Ko et al., JDA 2005).\<close>

theorem  l_less_than_s_type_general:
  assumes "suffix_type (a # s1) 0 = S_type"
  and     "suffix_type (a # s2) 0 = L_type"
shows "list_less_ns (a # s2) (a # s1)"
proof -
  from suffix_type_list_type_eq[of "a # s1" 0]
  have "suffix_type (a # s1) 0 = list_type (<) (a # s1)"
    by simp
  hence "list_type (<) (a # s1) = S_type"
    using assms(1) by auto
  moreover
  from suffix_type_list_type_eq[of "a # s2" 0]
  have "suffix_type (a # s2) 0 = list_type (<) (a # s2)"
    by simp
  hence "list_type (<) (a # s2) = L_type"
    using assms(2) by auto
  ultimately show ?thesis
    using l_less_than_s_type_list_type[of "(<)" a s1 s2]
    by (meson UNIV_I nslexordp_eq_list_less_ns_app top_greatest totalp_on_less transp_on_less)
qed

corollary l_less_than_s_type_suffix:
  assumes "i < length s"
  and     "j < length s"
  and     "s ! i = s ! j"
  and     "suffix_type s i = S_type"
  and     "suffix_type s j = L_type"
shows "list_less_ns (suffix s j) (suffix s i)"
  by (metis Cons_nth_drop_Suc assms l_less_than_s_type_general suffix_type_suffix)

theorem l_less_than_s_type:
  assumes "valid_list s"
  and     "i < length s"
  and     "j < length s"
  and     "hd (suffix s i) = hd (suffix s j)"
  and     "suffix_type s i = S_type"
  and     "suffix_type s j = L_type"
shows "list_less_ns (suffix s j) (suffix s i)"
  by (metis hd_drop_conv_nth assms(2-) l_less_than_s_type_suffix)

corollary (in Suffix_Array_General) same_hd_s_after_l:
  assumes valid_list: "valid_list s"
  and     i_less_len_s: "i < length s"
  and     j_less_len_s: "j < length s"
  and     i_neq_j:      "i \<noteq> j"
  and     suf_i_type:   "suffix_type s ((sa s)! i) = L_type"
  and     suf_j_type:   "suffix_type s ((sa s)! j) = S_type"
  and     hd_eq:        "hd (suffix s ((sa s) ! i)) = hd (suffix s ((sa s) ! j))"
shows "i < j"
proof -
  have A: "(sa s) ! i < length s"
    using i_less_len_s sa_nth_ex by auto

  from sa_set_upt[where s = s] sa_length[where s = s] j_less_len_s
  have B: "(sa s) ! j < length s"
    by (metis atLeast0LessThan lessThan_iff nth_mem)

  from l_less_than_s_type[OF valid_list B A hd_eq[symmetric] suf_j_type suf_i_type]
  have suf_i_less_suf_j: "list_less_ns (suffix s ((sa s)! i)) (suffix s ((sa s)! j))"
    by simp

  from sorted_nth_less_mono[OF strict_sorted_imp_sorted[OF sa_g_sorted],
                                    simplified length_map sa_length,
                                    OF i_less_len_s j_less_len_s i_neq_j]
       nth_map[where f = "suffix s" and xs = "sa s", simplified sa_length, OF i_less_len_s]
       nth_map[where f = "suffix s" and xs = "sa s", simplified sa_length, OF j_less_len_s]
       valid_list_list_less_equiv_list_less_ns[OF valid_suffix,
                                                 OF valid_list A valid_suffix,
                                                 OF valid_list B,
                                                 THEN iffD2,
                                                 OF suf_i_less_suf_j]
  show ?thesis by simp
qed

subsection \<open>Implementation of Suffix Type Computation\<close>

text \<open>This subsection contain a shallow embedding of a function that would compute the suffix types
      for a list.\<close>

fun abs_get_suffix_types :: "('a :: {linorder, order_bot}) list \<Rightarrow> SL_types list"
  where
"abs_get_suffix_types [] = []" |
"abs_get_suffix_types ([_]) = [S_type]" |
"abs_get_suffix_types (a # b # xs) =
  (let ys = abs_get_suffix_types (b # xs)
   in
     (if a < b then S_type # ys
      else if a > b then L_type # ys
      else hd (ys) # ys))"

lemma length_abs_get_suffix_types:
  "length (abs_get_suffix_types s) = length s"
  by (induct s rule: abs_get_suffix_types.induct; clarsimp simp: Let_def)

lemma abs_get_suffix_types_correct_nth:
  "i < length s \<Longrightarrow> abs_get_suffix_types s ! i = suffix_type s i"
proof (induct s arbitrary: i rule: abs_get_suffix_types.induct)
  case 1
  then show ?case
    by simp
next
  case (2 uu i)
  then show ?case
    by (simp add: suffix_is_singleton)
next
  case (3 a b xs i)
  note IH = this

  have "i \<noteq> 0 \<Longrightarrow> ?case"
  proof -
    assume "i \<noteq> 0"
    hence "\<exists>n. i = Suc n"
      using not0_implies_Suc by blast
    then obtain n where
      "i = Suc n"
      by blast
    hence "abs_get_suffix_types (a # b # xs) ! i = abs_get_suffix_types (b # xs) ! n"
      by (clarsimp simp: Let_def)
    moreover
    have "suffix_type (a # b # xs) i = suffix_type (b # xs) n"
      by (simp add: \<open>i = Suc n\<close> suffix_type_cons_suc)
    moreover
    from IH(1)[of n] IH(2) \<open>i = Suc n\<close>
    have "abs_get_suffix_types (b # xs) ! n = suffix_type (b # xs) n"
      by simp
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "i = 0 \<Longrightarrow> ?case"
  proof -
    assume "i = 0"

    have "a < b \<or> b < a \<or> a = b"
      by fastforce
    then show ?case
    proof (elim disjE)
      assume "a < b"
      then show ?case
        by (simp add: \<open>i = 0\<close> suffix_type_cons_less)
    next
      assume "b < a"
      then show ?case
        using \<open>i = 0\<close> order_less_imp_triv suffix_type_cons_greater by fastforce
    next
      assume "a = b"

      have "abs_get_suffix_types (b # xs) \<noteq> []"
        by (metis Zero_neq_Suc length_Cons length_abs_get_suffix_types list.size(3))
      hence "abs_get_suffix_types (a # b # xs) ! i = abs_get_suffix_types (b # xs) ! 0"
        unfolding abs_get_suffix_types.simps(3)[of a b xs, simplified Let_def]
        by (simp add: \<open>a = b\<close> \<open>i = 0\<close> hd_conv_nth)
      moreover
      have "suffix_type (a # b # xs) i = suffix_type (b # xs) 0"
        by (simp add: \<open>a = b\<close> \<open>i = 0\<close> suffix_type_cons_same)
      ultimately show ?case
        using IH(1)[of 0, simplified] by presburger
    qed
  qed
  ultimately show ?case
    by blast
qed

lemma get_suffix_types_correct:
  "\<forall>i < length s. (abs_get_suffix_types s) ! i = suffix_type s i"
  by (simp add: abs_get_suffix_types_correct_nth)

section \<open>SAIS Sublist Order\<close>

text \<open>This section contains the sublist ordering used in SAIS
      (definition 2.3, Nong et al., DCC 2009).
      Note that this generalised so that it is not a ternary relation but a binary relation.\<close>

fun ss_order_less :: "('a :: {linorder, order_bot}) list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"ss_order_less [] _ = False" |
"ss_order_less _ [] = True" |
"ss_order_less (a # as) (b # bs) =
  (if a < b then True
   else if a > b then False
   else if suffix_type (a # as) 0 = suffix_type (b # bs) 0 then ss_order_less as bs
   else if suffix_type (a # as) 0 = L_type then True
   else False)"

text \<open>As described in section "Suffix Type", the SAIS sublist ordering (@{term ss_order_less}) is
      equivalent to @{term list_less_ns}.\<close>

lemma ss_order_less_equiv_list_less_ns:
  "ss_order_less s1 s2 = list_less_ns s1 s2"
proof (induct rule: ss_order_less.induct)
  case (1 uu)
  then show ?case
    by simp
next
  case (2 v va)
  then show ?case
    by (simp add: list_less_ns_nil)
next
  case (3 a as b bs)
  then show ?case
    by (metis antisym_conv3 l_less_than_s_type_general list_less_ns_cons_diff list_less_ns_cons_same
              ordlistns.less_asym ss_order_less.simps(3) suffix_type_def)
qed

section \<open>Sorting\<close>

lemma sorted_letters_s_types:
  assumes "\<forall>k\<ge>i. k < j \<longrightarrow> suffix_type T k = S_type"
  and     "j \<le> length T"
  shows "sorted (list_slice T i j)"
proof (intro sorted_iff_nth_mono[THEN iffD2] allI impI)
  fix x y
  assume "x \<le> y" "y < length (list_slice T i j)"

  have "list_slice T i j ! x = T ! (i + x)"
    by (meson \<open>x \<le> y\<close> \<open>y < length (list_slice T i j)\<close> dual_order.strict_trans2 nth_list_slice)
  moreover
  have "list_slice T i j ! y = T ! (i + y)"
    using \<open>y < length (list_slice T i j)\<close> nth_list_slice 
    by blast
  moreover
  have "i + y < j"
    using \<open>y < length (list_slice T i j)\<close> 
    by (simp add: assms(2))
  have "i + x \<le> i + y"
    by (simp add: \<open>x \<le> y\<close>)
  with \<open>i + y < j\<close>
  have "T ! (i + x) \<le> T ! (i + y)"
  proof (induct "y - x" arbitrary: x y)
    case 0
    then show ?case by simp
  next
    case (Suc z)
    note IH = this
    from IH(2)
    have "\<exists>y'. y = Suc y'"
      by presburger
    then obtain y' where
      "y = Suc y'"
      by blast
    hence "z = y' - x"
      using IH(2) by linarith
    moreover
    have "i + y' < j"
      using Suc.prems(1) \<open>y = Suc y'\<close> by linarith
    moreover
    have "i + x \<le> i + y'"
      using Suc.hyps(2) \<open>y = Suc y'\<close> by linarith
    ultimately have "T ! (i + x) \<le> T ! (i + y')"
      using Suc.hyps(1) by blast
    moreover
    from assms(1)
    have "suffix_type T (i + y') = S_type"
      by (simp add: \<open>i + y' < j\<close>)
    hence "T ! (i + y') \<le> T ! (i + y)"
      using Suc.prems(1) \<open>y = Suc y'\<close> assms(2) less_le_trans s_type_letter_le_Suc by fastforce
    ultimately  show ?case
      using order.trans by blast
  qed
  ultimately show "list_slice T i j ! x \<le> list_slice T i j ! y"
    by simp
qed

lemma sorted_letters_l_types:
  assumes "\<forall>k\<ge>i. k < j \<longrightarrow> suffix_type T k = L_type"
  and     "j \<le> length T"
shows "sorted ((rev (list_slice T i j)))"
proof (intro sorted_rev_iff_nth_mono[THEN iffD2] allI impI)
  fix x y
  assume "x \<le> y" "y < length (list_slice T i j)"

  have "length (list_slice T i j) = j - i"
    by (simp add: assms(2))

  have "i + y < j"
    using \<open>length (list_slice T i j) = j - i\<close> \<open>y < length (list_slice T i j)\<close> by linarith
  with \<open>x \<le> y\<close>
  have "T ! (i + y) \<le> T ! (i + x)"
  proof (induct "y - x" arbitrary: x y)
    case 0
    then show ?case by simp
  next
    case (Suc z x y)
    note IH = this
    have "\<exists>y'. y = Suc y' \<and> x \<le> y' \<and> z = y' - x"
      by (metis Suc.hyps(2) Suc.prems(1) add_Suc_right add_diff_cancel_left' add_diff_cancel_right'
                diff_le_self ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    then obtain y' where
      "y = Suc y'" "x \<le> y'" "z = y' - x"
      by blast
    with IH(1) IH(4)
    have "T ! (i + x) \<ge> T ! (i + y')"
      by simp
    moreover
    from assms(1)
    have "suffix_type T (i + y') = L_type"
      using Suc.prems(2) \<open>y = Suc y'\<close> by auto
    hence "T ! (i + y') \<ge> T ! (i + y)"
      using Suc.prems(2) \<open>y = Suc y'\<close> assms(2) nth_less_imp_s_type order_less_le_trans by fastforce
    ultimately show ?case
      by auto
  qed
  moreover
  have "list_slice T i j ! x =  T ! (i + x)"
    by (metis \<open>x \<le> y\<close> \<open>y < length (list_slice T i j)\<close> nth_list_slice order_le_less_trans)
  moreover
  have "list_slice T i j ! y = T ! (i + y)"
    using \<open>y < length (list_slice T i j)\<close> nth_list_slice by blast
  ultimately show "list_slice T i j ! y \<le> list_slice T i j ! x"
    by presburger
qed

section \<open>LMS-Types\<close>

text \<open>This section contains the definition of an LMS-type;
      standing for large, middle and small.
      It also contains lemmas pertaining to these types.\<close>

definition 
  abs_is_lms :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> bool"
where
  "abs_is_lms s i \<equiv> 
    (suffix_type s i = S_type) \<and> 
    (\<exists>j. i = Suc j \<and> 
         suffix_type s j = L_type)"

text \<open>LMS-types are subtypes of @{term S_type}.
     This is because these are @{term S_type}, but they are also immediately succeed @{term L_type}.\<close>

subsection \<open>LMS-Type Simplifications\<close>

text \<open>This subsection contains theorems about facts that can be derived from the @{term abs_is_lms}
      definition and vice versa.\<close>

lemma lms_type_list_less_ns:
  "abs_is_lms s i = (\<exists>j. i = Suc j \<and> list_less_ns (suffix s i) (suffix s j) \<and>
                     list_less_ns (suffix s i) (suffix s (Suc i)))"
  by (metis SL_types.simps(2) abs_is_lms_def l_type_list_less_ns ordlistns.antisym_conv3 
            s_type_list_less_ns)

lemma abs_is_lms_0:
  "\<not>abs_is_lms s 0"
  apply (clarsimp simp: abs_is_lms_def)
  done

lemma abs_is_lms_cons_suc:
  "i > 0 \<Longrightarrow> abs_is_lms (a # s) (Suc i) = abs_is_lms s i"
  apply (drule gr0_implies_Suc; clarsimp)
  apply (clarsimp simp: abs_is_lms_def suffix_type_cons_suc)
  done

lemma i_s_type_imp_Suc_i_not_lms:
  "suffix_type s i = S_type \<Longrightarrow> \<not>abs_is_lms s (Suc i)"
  by (simp add: abs_is_lms_def)

lemma suffix_type_same_imp_not_lms:
  "suffix_type s i = suffix_type s (Suc i) \<Longrightarrow> \<not>abs_is_lms s (Suc i)"
  by (simp add: abs_is_lms_def)

lemma abs_is_lms_consec:
  "abs_is_lms xs i \<Longrightarrow> \<not>abs_is_lms xs (Suc i)"
  "abs_is_lms xs (Suc i) \<Longrightarrow> \<not>abs_is_lms xs i"
  by (clarsimp simp: abs_is_lms_def)+

lemma abs_is_lms_gre_length:
  "n \<ge> length xs \<Longrightarrow> \<not>abs_is_lms xs n"
  by (metis SL_types.distinct(1) drop_eq_Nil abs_is_lms_def l_type_list_less_ns)

lemma abs_is_lms_suffix:
  "abs_is_lms (suffix s n) i \<Longrightarrow> abs_is_lms s (i + n)"
  by (clarsimp simp: abs_is_lms_def suffix_type_suffix_gen)

lemma abs_is_lms_i_gr_0:
  "i > 0 \<Longrightarrow> abs_is_lms (suffix s n) i = abs_is_lms s (i + n)"
  apply safe
   apply (erule abs_is_lms_suffix)
  apply (clarsimp simp: abs_is_lms_def)
  apply (rule conjI)
   apply (subst suffix_type_suffix_gen; simp)
  by (metis (no_types, opaque_lifting) add.commute add_Suc_right add_right_cancel less_Suc_eq_le
        less_iff_Suc_add ordered_cancel_comm_monoid_diff_class.diff_add suffix_type_suffix_gen)

lemma set_abs_is_lms_suffix:
  "{i. abs_is_lms (suffix s n) (i - n)} = {i. abs_is_lms s i \<and> i > n}"
  apply safe
    apply (metis abs_is_lms_0 abs_is_lms_suffix le_less_linear nat_diff_split
            ordered_cancel_comm_monoid_diff_class.diff_add)
   apply (metis bot_nat_0.not_eq_extremum abs_is_lms_0 zero_less_diff)
  apply (cases n)
   apply clarsimp
  by (metis (no_types, lifting) Suc_diff_le abs_is_lms_def less_Suc_eq_le less_or_eq_imp_le
        ordered_cancel_comm_monoid_diff_class.diff_add suffix_type_suffix_gen)

lemma abs_is_lms_set_less_length:
  "n \<ge> length xs \<Longrightarrow> {i. abs_is_lms xs i \<and> i < n} = {i. abs_is_lms xs i}"
  by (meson dual_order.trans abs_is_lms_gre_length le_less_linear)

lemma abs_is_lms_suffix_Suc:
  "abs_is_lms (suffix s n) (Suc i) = abs_is_lms s (Suc (i + n))"
  apply safe
   apply (drule abs_is_lms_suffix; simp)
  apply (clarsimp simp: abs_is_lms_def)
  apply (subst suffix_type_suffix_gen)+
  apply simp
  done

subsection \<open>LMS-Type Sets and Subsets\<close>

text \<open>This subsection contains lemmas about sets and subsets of LMS-types.\<close>

lemma set_lms_gr_0:
  "{i. abs_is_lms xs i \<and> 0 < i} = {i. abs_is_lms xs i}"
  using bot_nat_0.not_eq_extremum abs_is_lms_0 by blast

lemma set_lms_n_subset:
  "{i. abs_is_lms xs i \<and> i > n} \<subseteq> {i. abs_is_lms xs i}"
  by blast

lemma set_lms_Suc_subset:
  "{i. abs_is_lms xs i \<and> i > Suc n} \<subseteq> {i. abs_is_lms xs i \<and> i > n}"
  by (simp add: Collect_mono)

lemma set_lms_Suc_insert:
  "abs_is_lms xs (Suc n) \<Longrightarrow> {i. abs_is_lms xs i \<and> i > n} = insert (Suc n) {i. abs_is_lms xs i \<and> i > Suc n}"
  using Collect_cong by auto

lemma lms_finite:
  "finite {i. abs_is_lms xs i}"
  by (metis finite_nat_set_iff_bounded abs_is_lms_def mem_Collect_eq suffix_type_s_bound)

lemma lms_set_empty:
  "\<lbrakk>length xs = Suc n; m \<ge> n\<rbrakk> \<Longrightarrow> {i. abs_is_lms xs i \<and> i > m } = {}"
  by (metis (no_types, lifting) Collect_empty_eq Suc_leI diff_diff_cancel abs_is_lms_gre_length
                                less_imp_diff_less)

subsection \<open>Implementation of LMS-Types Computation\<close>

text \<open>This section contains a shallow embedding of a function that would compute all
      the LMS-types of an ordered list.\<close>

fun get_lms :: "('a :: {linorder, order_bot}) list \<Rightarrow> nat \<Rightarrow> nat list"
  where
"get_lms xs 0 = []" |
"get_lms xs (Suc n) = (if abs_is_lms xs n then n # get_lms xs n else get_lms xs n)"

lemma get_lms_correct:
  "get_lms xs n = rev (filter (abs_is_lms xs) [0..<n])"
  apply (induct n)
   apply simp
  apply clarsimp
  done

subsubsection \<open>Properties\<close>

text \<open>This subsection contains miscellaneous lemmas about facts that can be derived from the shallow
      embedding and vice versa.\<close>

lemma get_lms_element_bound:
  "x \<in> set (get_lms xs n) \<Longrightarrow> x < n \<and> x > 0"
  apply (induct n; simp)
  apply (clarsimp split: if_splits)
  apply (erule disjE; clarsimp)
  apply (cases x; clarsimp simp: abs_is_lms_0)
  done

lemma distinct_get_lms:
  "distinct (get_lms xs n)"
  apply (induct n; clarsimp)
  apply (drule get_lms_element_bound)
  by blast

lemma get_lms_abs_is_lms:
  "x \<in> set (get_lms xs n) \<longleftrightarrow> abs_is_lms xs x \<and> x < n"
  apply (subst get_lms_correct)
  apply clarsimp
  by blast

lemma lms_le_length:
  "x \<in> set (get_lms xs n) \<Longrightarrow> x < length xs"
  by (simp add: get_lms_abs_is_lms abs_is_lms_def suffix_type_s_bound)

lemma get_lms_set:
  "set (get_lms xs n) = {i. abs_is_lms xs i \<and> i < n}"
  apply (induct n)
   apply simp
  apply safe
  using get_lms_abs_is_lms by blast+

lemma get_lms_set_n_gre_length:
  "n \<ge> length xs \<Longrightarrow> set (get_lms xs n) = {i. abs_is_lms xs i}"
  apply (simp add: get_lms_set)
  by (meson dual_order.trans abs_is_lms_gre_length not_less)

subsection \<open>Cardinality LMS-Types\<close>

text \<open>This section contains lemmas about how many LMS-types exist
      (lemma 2.1, Nonge et al., DCC2009).
      These lemmas are particularly important when proving that the SAIS is O(n) in space (bytes)
      and time complexity (lemma 3.1, Nong et al., DCC 2009).\<close>

lemma num_lms_bound_1:
  "length (get_lms xs n) \<le> n div 2"
proof -
  have "card (set (get_lms xs n)) \<le> n div 2"
  proof (intro ballI subset_upt_no_Suc[of "set (get_lms xs n)" n])
    show "set (get_lms xs n) \<subseteq> {1..<n}"
      by (simp add: Suc_leI get_lms_element_bound subset_code(1))
  next
    fix x
    assume "x \<in> set (get_lms xs n)"
    hence "abs_is_lms xs x"
      by (simp add: get_lms_abs_is_lms)
    then show "Suc x \<notin> set (get_lms xs n)"
      using get_lms_abs_is_lms abs_is_lms_consec(2) by blast
  qed
  with distinct_card[OF distinct_get_lms[of xs n]]
  show ?thesis
    by presburger
qed

lemma num_lms_bound_2:
  "length (get_lms xs n) \<le> length xs div 2"
proof -
  have "card (set (get_lms xs n)) \<le> length xs div 2"
  proof (intro ballI subset_upt_no_Suc[of "set (get_lms xs n)" "length xs"])
    show "set (get_lms xs n) \<subseteq> {1..<length xs}"
      by (metis One_nat_def Suc_leI atLeastLessThan_iff get_lms_element_bound lms_le_length subsetI)
  next
    fix x
    assume "x \<in> set (get_lms xs n)"
    hence "abs_is_lms xs x"
      by (simp add: get_lms_abs_is_lms)
    then show "Suc x \<notin> set (get_lms xs n)"
      using get_lms_abs_is_lms abs_is_lms_consec(2) by blast
  qed
  with distinct_card[OF distinct_get_lms[of xs n]]
  show ?thesis
    by simp
qed

lemma card_abs_is_lms_bound:
  "xs \<noteq> [] \<Longrightarrow> card {i. abs_is_lms xs i} < length xs"
  by (metis (no_types, opaque_lifting) One_nat_def distinct_card distinct_get_lms div_less_dividend
        get_lms_set_n_gre_length le_less_linear le_less_trans length_greater_0_conv lessI
        num_lms_bound_2 numeral_2_eq_2)

lemma card_abs_is_lms_bound_length_div_2:
  "card {i. abs_is_lms xs i} \<le> length xs div 2"
  by (metis distinct_card distinct_get_lms get_lms_set_n_gre_length linear num_lms_bound_2)

lemma length_filter_lms:
  "T \<noteq> [] \<Longrightarrow> length (filter (abs_is_lms T) [0..<length T]) < length T"
  by (metis diff_zero abs_is_lms_0 length_filter_less length_greater_0_conv length_upt nth_Cons_0
        nth_mem upt_rec)

subsection \<open>General Properties about LMS-types\<close>

lemma abs_is_lms_imp_le_nth:
  "\<lbrakk>abs_is_lms T i; Suc i < length T\<rbrakk> \<Longrightarrow> T ! i \<le> T ! Suc i"
  by (metis SL_types.simps(2) abs_is_lms_def not_less nth_gr_imp_l_type)

lemma abs_is_lms_neq:
  "abs_is_lms T (Suc i) \<Longrightarrow> T ! Suc i < T ! i"
  unfolding abs_is_lms_def
proof(safe)
  assume "suffix_type T (Suc i) = S_type" "suffix_type T i = L_type"

  from \<open>suffix_type T (Suc i) = S_type\<close>
  have "Suc i < length T"
    by (simp add: suffix_type_s_bound)
  with suffix_type_neq \<open>suffix_type T (Suc i) = S_type\<close> \<open>suffix_type T i = L_type\<close>
  show ?thesis
    by (metis SL_types.simps(2) not_less_iff_gr_or_eq nth_less_imp_s_type)
qed

lemma abs_is_lms_last:
  "\<lbrakk>valid_list T; length T = Suc (Suc n)\<rbrakk> \<Longrightarrow> abs_is_lms T (Suc n)"
proof (induct n arbitrary: T)
  case 0
  note IH = this

  have "T ! Suc 0 = bot"
    by (metis IH Zero_neq_Suc diff_Suc_1 last_conv_nth list.size(3) valid_list_def)
  with IH(1)[simplified valid_list_ex_def]
  have "T ! 0 > T ! Suc 0"
    by (metis IH(2) One_nat_def bot.not_eq_extremum butlast_snoc diff_Suc_1' le_less_Suc_eq
              length_butlast less_or_eq_imp_le nth_butlast)
  with suffix_type_last[OF IH(2)]
  show ?case
    using abs_is_lms_def nth_gr_imp_l_type suffix_type_s_bound by blast
next
  case (Suc n)
  note IH = this
  show ?case
  proof (cases T)
    case Nil
    then show ?thesis
      by (simp add: Suc.prems(1) valid_list_not_nil)
  next
    case (Cons a T')
    with IH valid_list_consD[of a T']
    have "abs_is_lms T' (Suc n)"
      by fastforce
    then show ?thesis
      by (simp add: abs_is_lms_def local.Cons suffix_type_cons_suc)
  qed
qed

lemma abs_is_lms_imp_less_length:
  "abs_is_lms T i \<Longrightarrow> i < length T"
  using abs_is_lms_gre_length le_less_linear by blast

lemma s_type_and_not_lms_Suc:
  "\<lbrakk>\<not>abs_is_lms T (Suc i); suffix_type T (Suc i) = S_type\<rbrakk> \<Longrightarrow> suffix_type T i = S_type"
  by (meson abs_is_lms_def suffix_type_def)

lemma no_lms_imp_all_s_type:
  assumes "j < length T"
  and     "i \<le> j"
  and     "\<forall>k>i. k \<le> j \<longrightarrow> \<not>abs_is_lms T k"
  and     "suffix_type T j = S_type"
  and     "i \<le> k"
  and     "k \<le> j"
shows "suffix_type T k = S_type"
  using assms
proof (induct "j - k" arbitrary: j)
  case 0
  then show ?case
    by auto
next
  case (Suc x)
  note IH = this

  have "\<exists>j'. j = Suc j'"
    using Suc.hyps(2) by presburger
  then obtain j' where
    "j = Suc j'"
    by blast
  hence "x = j' - k"
    using Suc.hyps(2) by linarith
  moreover
  have "j' < length T"
    using Suc.prems(1) Suc_lessD \<open>j = Suc j'\<close> by blast
  moreover
  have "i \<le> j'"
    using Suc.hyps(2) \<open>j = Suc j'\<close> assms(5) by linarith
  moreover
  have "\<forall>k>i. k \<le> j' \<longrightarrow> \<not> abs_is_lms T k"
    by (simp add: Suc.prems(3) \<open>j = Suc j'\<close>)
  moreover
  from IH(5)
  have "\<not>abs_is_lms T (Suc j')"
    by (simp add: \<open>j = Suc j'\<close> calculation(3) le_imp_less_Suc)
  with IH(6) \<open>j = Suc j'\<close> s_type_and_not_lms_Suc[of T j']
  have "suffix_type T j' = S_type"
    by blast
  moreover
  have "k \<le> j'"
    using Suc.hyps(2) \<open>j = Suc j'\<close> by linarith
  ultimately show ?case
    using IH(1)[of j'] assms(5) by blast
qed

lemma first_l_type_after_s_type:
  assumes "j < length T"
  and     "i \<le> j"
  and     "\<forall>k>i. k \<le> j \<longrightarrow> \<not>abs_is_lms T k"
  and     "suffix_type T j = L_type"
  and     "suffix_type T i = S_type"
shows "\<exists>l\<ge>i. l \<le> j \<and> (\<forall>k<l. i \<le> k \<longrightarrow> suffix_type T k = S_type) \<and> suffix_type T l = L_type"
  using assms
proof (induct "j - i" arbitrary: j)
  case 0
  then show ?case
    by auto
next
  case (Suc x)
  note IH = this

  have "\<exists>j'. j = Suc j'"
    by (metis SL_types.distinct(1) Suc.prems(2) Suc.prems(4) assms(5) diff_is_0_eq diff_zero
              less_imp_Suc_add neq0_conv)
  then obtain j' where
    "j = Suc j'"
    by blast
  hence "x = j' - i"
    using Suc.hyps(2) \<open>j = Suc j'\<close> by linarith

  have "j' < length T"
    using Suc.prems(1) Suc_lessD \<open>j = Suc j'\<close> by blast

  have "i \<le> j'"
    using Suc.hyps(2) \<open>j = Suc j'\<close> by linarith

  have P: "\<forall>k>i. k \<le> j' \<longrightarrow> \<not> abs_is_lms T k"
    by (simp add: Suc.prems(3) \<open>j = Suc j'\<close>)

  have "suffix_type T j' = S_type \<or> suffix_type T j' = L_type"
    using SL_types.exhaust by blast
  moreover
  have "suffix_type T j' = S_type \<Longrightarrow> ?case"
  proof -
    assume "suffix_type T j' = S_type"
    hence "\<forall>k<j. i \<le> k \<longrightarrow> suffix_type T k = S_type"
      using P \<open>j' < length T\<close> no_lms_imp_all_s_type  \<open>j = Suc j'\<close> less_Suc_eq_le by auto
    then show ?thesis
      using Suc.prems(2) Suc.prems(4) by blast
  qed
  moreover
  have "suffix_type T j' = L_type \<Longrightarrow> ?case"
  proof -
    assume "suffix_type T j' = L_type"
    with IH(1)[OF \<open>x = _\<close> \<open>j' < _\<close> \<open>i \<le> j'\<close> P _ assms(5)]
    have "\<exists>l\<ge>i. l \<le> j' \<and> (\<forall>k<l. i \<le> k \<longrightarrow> suffix_type T k = S_type) \<and> suffix_type T l = L_type" .
    then show ?thesis
      using \<open>j = Suc j'\<close> by auto
  qed
  ultimately show ?case
    by blast
qed

lemma no_lms_imp_and_s_imp_all_s_below:
  assumes "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> \<not>abs_is_lms T k"
  and     "suffix_type T k = S_type"
  and     "i \<le> k"
  and     "k < j"
shows "\<lbrakk>i \<le> k'; k' \<le> k\<rbrakk> \<Longrightarrow> suffix_type T k' = S_type"
proof (induct "k - k'" arbitrary: k')
  case 0
  with assms
  show ?case
    by auto
next
  case (Suc x)
  note IH = this

  from IH(2)
  have "x = k - Suc k'"
    by linarith

  from IH(3)
  have "i \<le> Suc k'"
    by simp

  from IH(2)
  have "Suc k' \<le> k"
    by linarith

  from IH(1)[OF \<open>x = k - Suc k'\<close> \<open>i \<le> Suc k'\<close> \<open>Suc k' \<le> k\<close>]
  have "suffix_type T (Suc k') = S_type"
    by assumption
  with assms(1) \<open>i \<le> k'\<close> \<open>k' \<le> k\<close> \<open>Suc k' \<le> k\<close> \<open>i \<le> Suc k'\<close> assms(4)
  show ?case
    by (meson SL_types.exhaust abs_is_lms_def order.strict_trans1)
qed

lemma no_lms_imp_and_l_imp_all_l_above:
  assumes "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> \<not>abs_is_lms T k"
  and     "suffix_type T k = L_type"
  and     "i \<le> k"
  and     "k < j"
shows "\<lbrakk>k \<le> k'; k' < j\<rbrakk> \<Longrightarrow> suffix_type T k' = L_type"
proof (induct "k' - k" arbitrary: k')
  case 0
  with assms
  show ?case
    by auto
next
  case (Suc x)
  note IH = this
  from IH(2)
  have "\<exists>n. k' = Suc n"
    by (metis less_Suc_eq less_Suc_eq_0_disj zero_diff)
  then obtain n where
    "k' = Suc n"
    by blast
  with IH(2)
  have "x = n - k"
    by linarith

  from IH(2) \<open>k' = Suc n\<close>
  have "k \<le> n"
    by linarith

  from IH(4) \<open>k' = Suc n\<close>
  have "n < j"
    by linarith

  from IH(1)[OF \<open>x = n - k\<close> \<open>k \<le> n\<close> \<open>n < j\<close>]
  have "suffix_type T n = L_type"
    by assumption
  with assms(1) \<open>k' = Suc n\<close> \<open>k' < j\<close> \<open>k \<le> k'\<close> assms(3)
  show ?case
    by (meson SL_types.exhaust abs_is_lms_def le_trans)
qed

lemma lms_sublist_helper:
  assumes "\<forall>k. suffix_type T k = S_type \<longrightarrow> Suc k < n \<longrightarrow> i \<le> k \<longrightarrow> suffix_type T (Suc k) \<noteq> L_type"
  and     "suffix_type T i = S_type"
shows "\<lbrakk>i \<le> k; k < n\<rbrakk> \<Longrightarrow> suffix_type T k = S_type"
proof (induct "k - i" arbitrary: k)
  case 0
  then show ?case
    using assms(2) by auto
next
  case (Suc x)
  note IH = this
  from IH(2)
  have "\<exists>k'. k = Suc k'"
    by presburger
  then obtain k' where
    "k = Suc k'"
    by blast
  with IH(2)
  have "x = k' - i"
    by linarith

  from IH(2) \<open>k = Suc k'\<close>
  have "i \<le> k'"
    by linarith

  from IH(4) \<open>k = Suc k'\<close>
  have "k' < n"
    by linarith

  from IH(1)[OF \<open>x = k' - i\<close> \<open>i \<le> k'\<close> \<open>k' < n\<close>] assms(1) IH(4) \<open>k = Suc k'\<close> \<open>i \<le> k'\<close>
  show ?case
    using SL_types.exhaust by blast
qed

end