theory Utils
  imports Regular_Tree_Relations.Term_Context
    Regular_Tree_Relations.FSet_Utils
begin

subsection \<open>Misc\<close>

definition "funas_trs \<R> = \<Union> ((\<lambda> (s, t). funas_term s \<union> funas_term t) ` \<R>)"

fun linear_term :: "('f, 'v) term \<Rightarrow> bool" where
  "linear_term (Var _) = True" |
  "linear_term (Fun _ ts) = (is_partition (map vars_term ts) \<and> (\<forall>t\<in>set ts. linear_term t))"

fun vars_term_list :: "('f, 'v) term \<Rightarrow> 'v list" where
  "vars_term_list (Var x) = [x]" |
  "vars_term_list (Fun _ ts) = concat (map vars_term_list ts)"

fun varposs :: "('f, 'v) term \<Rightarrow> pos set" where
  "varposs (Var x) = {[]}" |
  "varposs (Fun f ts) = (\<Union>i<length ts. {i # p | p. p \<in> varposs (ts ! i)})"

abbreviation "poss_args f ts \<equiv> map2 (\<lambda> i t. map ((#) i) (f t)) ([0 ..< length ts]) ts"

fun varposs_list :: "('f, 'v) term \<Rightarrow> pos list" where
  "varposs_list (Var x) = [[]]" |
  "varposs_list (Fun f ts) = concat (poss_args varposs_list ts)"

fun concat_index_split where
  "concat_index_split (o_idx, i_idx) (x # xs) =
     (if i_idx < length x
      then (o_idx, i_idx)
      else concat_index_split (Suc o_idx, i_idx - length x) xs)"

inductive_set trancl_list for \<R> where
  base[intro, Pure.intro] : "length xs = length ys \<Longrightarrow>
      (\<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R>) \<Longrightarrow> (xs, ys) \<in> trancl_list \<R>"
| list_trancl [Pure.intro]: "(xs, ys) \<in> trancl_list \<R> \<Longrightarrow> i < length ys \<Longrightarrow> (ys ! i, z) \<in> \<R> \<Longrightarrow>
    (xs, ys[i := z]) \<in> trancl_list \<R>"


lemma sorted_append_bigger:
  "sorted xs \<Longrightarrow>  \<forall>x \<in> set xs. x \<le> y \<Longrightarrow> sorted (xs @ [y])"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have s: "sorted xs" by (cases xs) simp_all
  from Cons have a: "\<forall>x\<in>set xs. x \<le> y" by simp
  from Cons(1)[OF s a] Cons(2-) show ?case by (cases xs) simp_all
qed

lemma find_SomeD:
  "List.find P xs = Some x \<Longrightarrow> P x"
  "List.find P xs = Some x \<Longrightarrow> x\<in>set xs"
  by (auto simp add: find_Some_iff)

lemma sum_list_replicate_length' [simp]:
  "sum_list (replicate n (Suc 0)) = n"
  by (induct n) simp_all

lemma arg_subteq [simp]:
  assumes "t \<in> set ts" shows "Fun f ts \<unrhd> t"
  using assms by auto

lemma finite_funas_term: "finite (funas_term s)"
  by (induct s) auto

lemma finite_funas_trs:
  "finite \<R> \<Longrightarrow> finite (funas_trs \<R>)"
  by (induct rule: finite.induct) (auto simp: finite_funas_term funas_trs_def)

fun subterms where
  "subterms (Var x) = {Var x}"|
  "subterms (Fun f ts) = {Fun f ts} \<union> (\<Union> (subterms ` set ts))"

lemma finite_subterms_fun: "finite (subterms s)"
  by (induct s) auto

lemma subterms_supteq_conv: "t \<in> subterms s \<longleftrightarrow> s \<unrhd> t"
  by (induct s) (auto elim: supteq.cases)

lemma set_all_subteq_subterms:
  "subterms s = {t. s \<unrhd> t}"
  using subterms_supteq_conv by auto

lemma finite_subterms: "finite {t. s \<unrhd> t}"
  unfolding set_all_subteq_subterms[symmetric]
  by (simp add: finite_subterms_fun)

lemma finite_strict_subterms: "finite {t. s \<rhd> t}"
  by (intro finite_subset[OF _ finite_subterms]) auto

lemma finite_UN_I2:
  "finite A \<Longrightarrow> (\<forall> B \<in> A. finite B) \<Longrightarrow> finite (\<Union> A)"
  by blast

lemma root_substerms_funas_term:
  "the ` (root ` (subterms s) - {None}) = funas_term s" (is "?Ls = ?Rs")
proof -
  thm subterms.induct
  {fix x assume "x \<in> ?Ls" then have "x \<in> ?Rs"
    proof (induct s arbitrary: x)
      case (Fun f ts)
      then show ?case
        by auto (metis DiffI Fun.hyps imageI option.distinct(1) singletonD) 
    qed auto}
  moreover
  {fix g assume "g \<in> ?Rs" then have "g \<in> ?Ls"
    proof (induct s arbitrary: g)
      case (Fun f ts)
      from Fun(2) consider "g = (f, length ts)" | "\<exists> t \<in> set ts. g \<in> funas_term t"
        by (force simp: in_set_conv_nth)
      then show ?case
      proof cases
        case 1 then show ?thesis
          by (auto simp: image_iff intro: bexI[of _ "Some (f, length ts)"])
      next
        case 2
        then obtain t where wit: "t \<in> set ts" "g \<in> funas_term t" by blast
        have "g \<in> the ` (root ` subterms t - {None})" using Fun(1)[OF wit] .
        then show ?thesis using wit(1)
          by (auto simp: image_iff)
      qed
    qed auto}
  ultimately show ?thesis by auto
qed

lemma root_substerms_funas_term_set:
  "the ` (root ` \<Union> (subterms ` R) - {None}) = \<Union> (funas_term ` R)"
  using root_substerms_funas_term
  by auto (smt DiffE DiffI UN_I image_iff)


lemma subst_merge:
  assumes part: "is_partition (map vars_term ts)"
  shows "\<exists>\<sigma>. \<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i). \<sigma> x = \<tau> i x"
proof -
  let ?\<tau> = "map \<tau> [0 ..< length ts]"
  let ?\<sigma> = "fun_merge ?\<tau> (map vars_term ts)"
  show ?thesis
    by (rule exI[of _ ?\<sigma>], intro allI impI ballI,
      insert fun_merge_part[OF part, of _ _ ?\<tau>], auto)
qed


lemma rel_comp_empty_trancl_simp: "R O R = {} \<Longrightarrow> R\<^sup>+ = R"
  by (metis O_assoc relcomp_empty2 sup_bot_right trancl_unfold trancl_unfold_right)

lemma choice_nat:
  assumes "\<forall>i<n. \<exists>x. P x i"
  shows "\<exists>f. \<forall>x<n. P (f x) x" using assms 
proof -
  from assms have "\<forall> i. \<exists> x. i < n \<longrightarrow> P x i" by simp
  from choice[OF this] show ?thesis by auto
qed


lemma subseteq_set_conv_nth:
  "(\<forall> i < length ss. ss ! i \<in> T) \<longleftrightarrow> set ss \<subseteq> T"
  by (metis in_set_conv_nth subset_code(1))

lemma singelton_trancl [simp]: "{a}\<^sup>+ = {a}"
  using tranclD tranclD2 by fastforce 

context
includes fset.lifting
begin
lemmas frelcomp_empty_ftrancl_simp = rel_comp_empty_trancl_simp [Transfer.transferred]
lemmas in_fset_idx = in_set_idx [Transfer.transferred]
lemmas fsubseteq_fset_conv_nth = subseteq_set_conv_nth [Transfer.transferred]
lemmas singelton_ftrancl [simp] = singelton_trancl [Transfer.transferred]
end

lemma set_take_nth:
  assumes "x \<in> set (take i xs)"
  shows "\<exists> j < length xs. j < i \<and> xs ! j = x" using assms
  by (metis in_set_conv_nth length_take min_less_iff_conj nth_take)

lemma nth_sum_listI:
  assumes "length xs = length ys"
    and "\<forall> i < length xs. xs ! i = ys ! i"
  shows "sum_list xs = sum_list ys"
  using assms nth_equalityI by blast

lemma concat_nth_length:
  "i < length uss \<Longrightarrow> j < length (uss ! i) \<Longrightarrow>
    sum_list (map length (take i uss)) + j < length (concat uss)"
by (induct uss arbitrary: i j) (simp, case_tac i, auto)

lemma sum_list_1_E [elim]:
  assumes "sum_list xs = Suc 0"
  obtains i where "i < length xs" "xs ! i = Suc 0" "\<forall> j < length xs. j \<noteq> i \<longrightarrow> xs ! j = 0"
proof -
  have "\<exists> i < length xs. xs ! i = Suc 0 \<and> (\<forall> j < length xs. j \<noteq> i \<longrightarrow> xs ! j = 0)" using assms
  proof (induct xs)
    case (Cons a xs) show ?case
    proof (cases a)
      case [simp]: 0
      obtain i where "i < length xs" "xs ! i = Suc 0" "(\<forall> j < length xs. j \<noteq> i \<longrightarrow> xs ! j = 0)"
        using Cons by auto
      then show ?thesis using less_Suc_eq_0_disj
        by (intro exI[of _ "Suc i"]) auto
    next
      case (Suc nat) then show ?thesis using Cons by auto
    qed
  qed auto
  then show " (\<And>i. i < length xs \<Longrightarrow> xs ! i = Suc 0 \<Longrightarrow> \<forall>j<length xs. j \<noteq> i \<longrightarrow> xs ! j = 0 \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by blast
qed


lemma nth_equalityE:
  "xs = ys \<Longrightarrow> (length xs = length ys \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> xs ! i = ys ! i) \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma map_cons_presv_distinct:
  "distinct t \<Longrightarrow> distinct (map ((#) i) t)"
  by (simp add: distinct_conv_nth)

lemma concat_nth_nthI:
  assumes "length ss = length ts" "\<forall> i < length ts. length (ss ! i) = length (ts ! i)"
    and "\<forall> i < length ts. \<forall> j < length (ts ! i). P (ss ! i ! j) (ts ! i ! j)"
  shows "\<forall> i < length (concat ts). P (concat ss ! i) (concat ts ! i)"
  using assms by (metis nth_concat_two_lists)


lemma last_nthI:
  assumes "i < length ts" "\<not> i < length ts - Suc 0"
  shows "ts ! i = last ts" using assms
  by (induct ts arbitrary: i)
    (auto, metis last_conv_nth length_0_conv less_antisym nth_Cons')

(* induction scheme for transitive closures of lists *)
lemma trancl_list_appendI [simp, intro]:
  "(xs, ys) \<in> trancl_list \<R> \<Longrightarrow> (x, y) \<in> \<R> \<Longrightarrow> (x # xs, y # ys) \<in> trancl_list \<R>"
proof (induct rule: trancl_list.induct)
  case (base xs ys)
  then show ?case using less_Suc_eq_0_disj
    by (intro trancl_list.base) auto
next
  case (list_trancl xs ys i z)
  from list_trancl(3) have *: "y # ys[i := z] = (y # ys)[Suc i := z]" by auto
  show ?case using list_trancl unfolding *
    by (intro trancl_list.list_trancl) auto
qed

lemma trancl_list_append_tranclI [intro]:
  "(x, y) \<in> \<R>\<^sup>+ \<Longrightarrow> (xs, ys) \<in> trancl_list \<R> \<Longrightarrow> (x # xs, y # ys) \<in> trancl_list \<R>"
proof (induct rule: trancl.induct)
  case (trancl_into_trancl a b c)
  then have "(a # xs, b # ys) \<in> trancl_list \<R>" by auto
  from trancl_list.list_trancl[OF this, of 0 c]
  show ?case using trancl_into_trancl(3)
    by auto
qed auto

lemma trancl_list_conv:
  "(xs, ys) \<in> trancl_list \<R> \<longleftrightarrow> length xs = length ys \<and> (\<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R>\<^sup>+)" (is "?Ls \<longleftrightarrow> ?Rs")
proof
  assume "?Ls" then show ?Rs
  proof (induct)
    case (list_trancl xs ys i z)
    then show ?case
      by auto (metis nth_list_update trancl.trancl_into_trancl)
  qed auto
next
  assume ?Rs then show ?Ls
  proof (induct ys arbitrary: xs)
    case Nil
    then show ?case by (cases xs) auto
  next
    case (Cons y ys)
    from Cons(2) obtain x xs' where *: "xs = x # xs'" and
      inv: "(x, y) \<in> \<R>\<^sup>+"
      by (cases xs) auto
    show ?case using Cons(1)[of "tl xs"] Cons(2) unfolding *
      by (intro trancl_list_append_tranclI[OF inv]) force
  qed
qed

lemma trancl_list_induct [consumes 2, case_names base step]:
  assumes "length ss = length ts" "\<forall> i < length ts. (ss ! i, ts ! i) \<in> \<R>\<^sup>+"
   and "\<And>xs ys. length xs = length ys \<Longrightarrow> \<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R> \<Longrightarrow> P xs ys"
   and "\<And>xs ys i z. length xs = length ys \<Longrightarrow> \<forall> i < length ys. (xs ! i, ys ! i) \<in> \<R>\<^sup>+ \<Longrightarrow> P xs ys
      \<Longrightarrow> i < length ys \<Longrightarrow> (ys ! i, z) \<in> \<R> \<Longrightarrow> P xs (ys[i := z])"
 shows "P ss ts" using assms
  by (intro trancl_list.induct[of ss ts \<R> P]) (auto simp: trancl_list_conv)


lemma swap_trancl:
  "(prod.swap ` R)\<^sup>+ = prod.swap ` (R\<^sup>+)"
proof -
  have [simp]: "prod.swap ` X = X\<inverse>" for X by auto
  show ?thesis by (simp add: trancl_converse)
qed

lemma swap_rtrancl:
  "(prod.swap ` R)\<^sup>* = prod.swap ` (R\<^sup>*)"
proof -
  have [simp]: "prod.swap ` X = X\<inverse>" for X by auto
  show ?thesis by (simp add: rtrancl_converse)
qed

lemma Restr_simps:
  "R \<subseteq> X \<times> X \<Longrightarrow> Restr (R\<^sup>+) X = R\<^sup>+"
  "R \<subseteq> X \<times> X \<Longrightarrow> Restr Id X O R = R"
  "R \<subseteq> X \<times> X \<Longrightarrow> R O Restr Id X = R"
  "R \<subseteq> X \<times> X \<Longrightarrow> S \<subseteq> X \<times> X \<Longrightarrow> Restr (R O S) X = R O S"
  "R \<subseteq> X \<times> X \<Longrightarrow> R\<^sup>+ \<subseteq> X \<times> X"
  subgoal using trancl_mono_set[of R "X \<times> X"] by (auto simp: trancl_full_on)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using trancl_subset_Sigma .
  done

lemma Restr_tracl_comp_simps:
  "\<R> \<subseteq> X \<times> X \<Longrightarrow> \<L> \<subseteq> X \<times> X \<Longrightarrow> \<L>\<^sup>+ O \<R> \<subseteq> X \<times> X"
  "\<R> \<subseteq> X \<times> X \<Longrightarrow> \<L> \<subseteq> X \<times> X \<Longrightarrow> \<L> O \<R>\<^sup>+ \<subseteq> X \<times> X"
  "\<R> \<subseteq> X \<times> X \<Longrightarrow> \<L> \<subseteq> X \<times> X \<Longrightarrow> \<L>\<^sup>+ O \<R> O \<L>\<^sup>+ \<subseteq> X \<times> X"
  by (auto dest: subsetD[OF Restr_simps(5)[of \<L>]] subsetD[OF Restr_simps(5)[of \<R>]])


text \<open>Conversions of the Nth function between lists and a spliting of the list into lists of lists\<close>

lemma concat_index_split_mono_first_arg:
  "i < length (concat xs) \<Longrightarrow> o_idx \<le> fst (concat_index_split (o_idx, i) xs)"
  by (induct xs arbitrary: o_idx i) (auto, metis Suc_leD add_diff_inverse_nat nat_add_left_cancel_less)

lemma concat_index_split_sound_fst_arg_aux:
  "i < length (concat xs) \<Longrightarrow> fst (concat_index_split (o_idx, i) xs) < length xs + o_idx"
  by (induct xs arbitrary: o_idx i) (auto, metis add_Suc_right add_diff_inverse_nat nat_add_left_cancel_less)

lemma concat_index_split_sound_fst_arg:
  "i < length (concat xs) \<Longrightarrow> fst (concat_index_split (0, i) xs) < length xs"
  using concat_index_split_sound_fst_arg_aux[of i xs 0] by auto

lemma concat_index_split_sound_snd_arg_aux:
  assumes "i < length (concat xs)"
  shows "snd (concat_index_split (n, i) xs) < length (xs ! (fst (concat_index_split (n, i) xs) - n))" using assms
proof (induct xs arbitrary: i n)
  case (Cons x xs)
  show ?case proof (cases "i < length x")
    case False then have size: "i - length x < length (concat xs)"
      using Cons(2) False by auto
    obtain k j where [simp]: "concat_index_split (Suc n, i - length x) xs = (k, j)"
      using old.prod.exhaust by blast
    show ?thesis using False Cons(1)[OF size, of "Suc n"] concat_index_split_mono_first_arg[OF size, of "Suc n"]
      by (auto simp: nth_append)
  qed (auto simp add: nth_append) 
qed auto

lemma concat_index_split_sound_snd_arg:
  assumes "i < length (concat xs)"
  shows "snd (concat_index_split (0, i) xs) < length (xs ! fst (concat_index_split (0, i) xs))"
  using concat_index_split_sound_snd_arg_aux[OF assms, of 0] by auto

lemma reconstr_1d_concat_index_split:
  assumes "i < length (concat xs)"
  shows "i = (\<lambda> (m, j). sum_list (map length (take (m - n) xs)) + j) (concat_index_split (n, i) xs)" using assms
proof (induct xs arbitrary: i n)
  case (Cons x xs) show ?case
  proof (cases "i < length x")
    case False
    obtain m k where res: "concat_index_split (Suc n, i - length x) xs = (m, k)"
      using prod_decode_aux.cases by blast
    then have unf_ind: "concat_index_split (n, i) (x # xs) = concat_index_split (Suc n, i - length x) xs" and
      size: "i - length x < length (concat xs)" using Cons(2) False by auto
    have "Suc n \<le> m" using concat_index_split_mono_first_arg[OF size, of "Suc n"] by (auto simp: res)
    then have [simp]: "sum_list (map length (take (m - n) (x # xs))) = sum_list (map length (take (m - Suc n) xs)) + length x"
      by (simp add: take_Cons')
    show ?thesis using Cons(1)[OF size, of "Suc n"] False unfolding unf_ind res by auto
  qed auto
qed auto

lemma concat_index_split_larger_lists [simp]:
  assumes "i < length (concat xs)"
  shows "concat_index_split (n, i) (xs @ ys) = concat_index_split (n, i) xs" using assms
  by (induct xs arbitrary: ys n i) auto

lemma concat_index_split_split_sound_aux:
  assumes "i < length (concat xs)"
  shows "concat xs ! i = (\<lambda> (k, j). xs ! (k - n) ! j) (concat_index_split (n, i) xs)" using assms
proof (induct xs arbitrary: i n)
  case (Cons x xs)
  show ?case proof (cases "i < length x")
    case False then have size: "i - length x < length (concat xs)"
      using Cons(2) False by auto
    obtain k j where [simp]: "concat_index_split (Suc n, i - length x) xs = (k, j)"
      using prod_decode_aux.cases by blast
    show ?thesis using False Cons(1)[OF size, of "Suc n"]
      using concat_index_split_mono_first_arg[OF size, of "Suc n"]
      by (auto simp: nth_append)
  qed (auto simp add: nth_append) 
qed auto

lemma concat_index_split_sound:
  assumes "i < length (concat xs)"
  shows "concat xs ! i = (\<lambda> (k, j). xs ! k ! j) (concat_index_split (0, i) xs)"
  using concat_index_split_split_sound_aux[OF assms, of 0] by auto

lemma concat_index_split_sound_bounds:
  assumes "i < length (concat xs)" and "concat_index_split (0, i) xs = (m, n)"
  shows "m < length xs" "n < length (xs ! m)"
  using concat_index_split_sound_fst_arg[OF assms(1)] concat_index_split_sound_snd_arg[OF assms(1)]
  by (auto simp: assms(2))

lemma concat_index_split_less_length_concat:
  assumes "i < length (concat xs)" and "concat_index_split (0, i) xs = (m, n)"
  shows "i = sum_list (map length (take m xs)) + n" "m < length xs" "n < length (xs ! m)"
    "concat xs ! i = xs ! m ! n"
  using concat_index_split_sound[OF assms(1)] reconstr_1d_concat_index_split[OF assms(1), of 0]
  using concat_index_split_sound_fst_arg[OF assms(1)] concat_index_split_sound_snd_arg[OF assms(1)] assms(2)
  by auto

lemma nth_concat_split':
  assumes "i < length (concat xs)"
  obtains j k where "j < length xs" "k < length (xs ! j)" "concat xs ! i = xs ! j ! k" "i = sum_list (map length (take j xs)) + k"
  using concat_index_split_less_length_concat[OF assms]
  by (meson old.prod.exhaust)

lemma sum_list_split [dest!, consumes 1]:
  assumes "sum_list (map length (take i xs)) + j = sum_list (map length (take k xs)) + l"
   and "i < length xs" "k < length xs"
   and "j < length (xs ! i)" "l < length (xs ! k)"
 shows "i = k \<and> j = l" using assms
proof (induct xs rule: rev_induct)
  case (snoc x xs)
  then show ?case
    by (auto simp: nth_append split: if_splits)
       (metis concat_nth_length length_concat not_add_less1)+
qed auto

lemma concat_index_split_unique:
  assumes "i < length (concat xs)" and "length xs = length ys"
    and "\<forall> i < length xs. length (xs ! i) = length (ys ! i)"
  shows "concat_index_split (n, i) xs = concat_index_split (n, i) ys" using assms
proof (induct xs arbitrary: ys n i)
  case (Cons x xs) note IH = this show ?case
  proof (cases ys)
    case Nil then show ?thesis using Cons(3) by auto
  next
    case [simp]: (Cons y ys')
    have [simp]: "length y = length x" using IH(4) by force
    have [simp]: "\<not> i < length x \<Longrightarrow> i - length x < length (concat xs)" using IH(2) by auto
    have [simp]: "i < length ys' \<Longrightarrow> length (xs ! i) = length (ys' ! i)" for i using IH(3, 4)
      by (auto simp: All_less_Suc) (metis IH(4) Suc_less_eq length_Cons Cons nth_Cons_Suc)
    show ?thesis using IH(2-) IH(1)[of "i - length x" ys' "Suc n"] by auto
  qed
qed auto

lemma set_vars_term_list [simp]:
  "set (vars_term_list t) = vars_term t"
  by (induct t) simp_all

lemma vars_term_list_empty_ground [simp]:
  "vars_term_list t = [] \<longleftrightarrow> ground t"
  by (induct t) auto

lemma varposs_imp_poss:
  assumes "p \<in> varposs t"
  shows "p \<in> poss t"
  using assms by (induct t arbitrary: p) auto

lemma vaposs_list_fun:
  assumes "p \<in> set (varposs_list (Fun f ts))"
  obtains i ps where "i < length ts" "p = i # ps"
  using assms set_zip_leftD by fastforce

lemma varposs_list_distinct:
  "distinct (varposs_list t)"
proof (induct t)
  case (Fun f ts)
  then show ?case proof (induct ts rule: rev_induct)
    case (snoc x xs)
    then have "distinct (varposs_list (Fun f xs))" "distinct (varposs_list x)" by auto
    then show ?case using snoc by (auto simp add: map_cons_presv_distinct dest: set_zip_leftD)
  qed auto
qed auto

lemma varposs_append:
  "varposs (Fun f (ts @ [t])) = varposs (Fun f ts) \<union> ((#) (length ts)) ` varposs t"
  by (auto simp: nth_append split: if_splits)

lemma varposs_eq_varposs_list:
  "set (varposs_list t) = varposs t"
proof (induct t)
  case (Fun f ts)
  then show ?case proof (induct ts rule: rev_induct)
    case (snoc x xs)
    then have "varposs (Fun f xs) = set (varposs_list (Fun f xs))"
      "varposs x = set (varposs_list x)" by auto
    then show ?case using snoc unfolding varposs_append
      by auto
  qed auto
qed auto

lemma varposs_list_var_terms_length:
  "length (varposs_list t) = length (vars_term_list t)"
  by (induct t) (auto simp: vars_term_list.simps intro: eq_length_concat_nth)

lemma vars_term_list_nth:
  assumes "i < length (vars_term_list (Fun f ts))"
    and "concat_index_split (0, i) (map vars_term_list ts) = (k, j)"
  shows "k < length ts \<and> j < length (vars_term_list (ts ! k)) \<and>
    vars_term_list (Fun f ts) ! i = map vars_term_list ts ! k ! j \<and>
    i = sum_list (map length (map vars_term_list (take k ts))) + j"
  using assms concat_index_split_less_length_concat[of i "map vars_term_list ts" k j]
  by (auto simp: vars_term_list.simps comp_def take_map) 

lemma varposs_list_nth:
  assumes "i < length (varposs_list (Fun f ts))"
     and "concat_index_split (0, i) (poss_args varposs_list ts) = (k, j)"
  shows "k < length ts \<and> j < length (varposs_list (ts ! k)) \<and>
    varposs_list (Fun f ts) ! i = k # (map varposs_list ts) ! k ! j \<and>
    i = sum_list (map length (map varposs_list (take k ts))) + j"
  using assms concat_index_split_less_length_concat[of i "poss_args varposs_list ts" k j]
  by (auto simp: comp_def take_map intro: nth_sum_listI)

lemma varposs_list_to_var_term_list:
  assumes "i < length (varposs_list t)"
  shows "the_Var (t |_ (varposs_list t ! i)) = (vars_term_list t) ! i" using assms
proof (induct t arbitrary: i)
  case (Fun f ts)
  have "concat_index_split (0, i) (poss_args varposs_list ts) = concat_index_split (0, i) (map vars_term_list ts)"
    using Fun(2) concat_index_split_unique[of i "poss_args varposs_list ts" "map vars_term_list ts" 0]
    using varposs_list_var_terms_length[of "ts ! i" for i]
    by (auto simp: vars_term_list.simps)
  then obtain k j where "concat_index_split (0, i) (poss_args varposs_list ts) = (k, j)"
    "concat_index_split (0, i) (map vars_term_list ts) = (k, j)" by fastforce
  from varposs_list_nth[OF Fun(2) this(1)] vars_term_list_nth[OF _ this(2)]
  show ?case using Fun(2) Fun(1)[OF nth_mem] varposs_list_var_terms_length[of "Fun f ts"] by auto
qed (auto simp: vars_term_list.simps)

end