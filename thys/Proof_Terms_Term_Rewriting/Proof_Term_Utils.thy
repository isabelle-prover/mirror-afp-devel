section\<open>Preliminaries\<close>

theory Proof_Term_Utils
imports 
  First_Order_Terms.Matching
  First_Order_Rewriting.Term_Impl
begin

subsection\<open>Utilities for Lists\<close>

lemma obtain_list_with_property:
  assumes "\<forall>x \<in> set xs. \<exists>a. P a x"
  shows "\<exists>as. length as = length xs \<and> (\<forall>i < length xs. P (as!i) (xs!i))"
  using assms proof(induct xs)
  case (Cons a xs)
  then show ?case
    by (metis length_map nth_map nth_mem)
qed simp

lemma card_Union_Sum:
  assumes "is_partition (map f [0..<length xs])" 
    and "\<forall>i < length xs. finite (f i)"
  shows "card (\<Union>i<length xs. f i) = (\<Sum>i<length xs. card (f i))"
proof-
  from assms(1) have disj:"pairwise (\<lambda>s t. disjnt (f s) (f t)) {..<length xs}" 
    unfolding pairwise_def is_partition_alt is_partition_alt_def disjnt_def by simp
  then have "pairwise disjnt (f ` {..<length xs})" 
    by (metis (mono_tags, lifting) pairwiseD pairwise_imageI) 
  then have "card (\<Union>i<length xs. f i) = sum card (f ` {..<length xs})" 
    using assms(2) card_Union_disjoint by (metis (mono_tags, lifting) imageE lessThan_iff) 
  with disj show ?thesis 
    using sum_card_image by (metis finite_lessThan)
qed

lemma sum_sum_concat: "(\<Sum>i<length xs. \<Sum>x\<leftarrow>f (xs!i). g x) = (\<Sum>x\<leftarrow>concat (map f xs). g x)"
proof(induct xs)
  case (Cons a xs)
  then show ?case unfolding list.map concat.simps map_append sum_list_append
    by (metis (mono_tags, lifting) length_nth_simps(2) nth_Cons_0 nth_Cons_Suc sum.cong sum.lessThan_Suc_shift)
qed simp

lemma concat_map2_zip:
  assumes "length xs = length ys" 
    and "\<forall>i < length xs. length (xs!i) = length (ys!i)"
  shows "concat (map2 zip xs ys) = zip (concat xs) (concat ys)"
  using assms proof(induct xs arbitrary:ys rule:rev_induct)
  case (snoc x xs)
  from snoc(2) obtain y ys' where y:"ys = ys'@[y]"
    by (metis append_is_Nil_conv length_0_conv neq_Nil_conv rev_exhaust) 
  moreover with snoc(2) have l:"length xs = length ys'" by simp
  moreover with snoc(3) have l':"\<forall>i < length xs. length (xs!i) = length (ys'!i)"
    unfolding y by (metis (no_types, lifting) Ex_less_Suc add_Suc_right append.right_neutral append_Cons_nth_left length_Cons length_append order_less_trans) 
  ultimately have IH:"concat (map2 zip xs ys') = zip (concat xs) (concat ys')"
    using snoc(1) by presburger
  have *:"concat (map2 zip (xs @ [x]) ys) = concat (map2 zip xs ys') @ (zip x y)" 
    unfolding y zip_append[OF l] by simp
  have "length (concat xs) = length (concat ys')" 
    using l l' eq_length_concat_nth by blast 
  then show ?case 
    unfolding * IH unfolding y concat_append using zip_append by simp   
qed simp

lemma sum_list_less:
  assumes less:"i < j" 
    and i'j':"i' < length xs" "j' < length xs" 
    and j'':"j'' < length (xs!j')" 
    and sums:"i = sum_list (map length (take i' xs)) + i''" "j = sum_list (map length (take j' xs)) + j''"
  shows "i' \<le> j'" 
proof(rule ccontr)
  assume *:"\<not> i' \<le> j'" 
  then have subsums:"sum_list (map length (take i' xs)) = sum_list (map length (take j' xs)) + sum_list (map length (take (i'-j') (drop j' xs)))"
    by (metis le_add_diff_inverse map_append nat_le_linear sum_list_append take_add) 
  from * have "take (i' - j') (drop j' xs) = xs!j' # (take (i' - (Suc j')) (drop (Suc j') xs))"  
    using i'j' by (metis Cons_nth_drop_Suc Suc_diff_Suc linorder_le_less_linear take_Suc_Cons) 
  with j'' have "j'' < sum_list (map length (take (i'-j') (drop j' xs)))" by simp
  then show False
    using sums subsums less by linarith
qed

lemma zip_symm: "(x, y) \<in> set (zip xs ys) \<Longrightarrow> (y, x) \<in> set (zip ys xs)"
  by (induct xs ys rule:list_induct2') auto

lemma sum_list_elem:
  "(\<Sum>x\<leftarrow>[y]. f x) = f y"
  by simp

lemma sum_list_zero:
  assumes "\<forall>i < length xs. f (xs!i) = 0"
  shows "(\<Sum>x\<leftarrow>xs. f x) = 0"
  by (metis assms map_eq_conv' monoid_add_class.sum_list_0)

lemma distinct_is_partition:
  assumes "distinct (concat ts)"
  shows "is_partition (map set ts)" 
  using assms proof(induct ts)
  case Nil
  then show ?case
    using is_partition_Nil by auto
next
  case (Cons t ts)
  {fix i j assume j:"j < length (t#ts)" and ij:"i < j" 
    have "(map set (t#ts))!i \<inter> (map set (t#ts))!j = {}" proof(cases i)
      case 0
      show ?thesis using Cons(2) unfolding 0
        using ij j by force
    next
      case (Suc n)
      from Cons have "is_partition (map set ts)" by simp
      then show ?thesis 
        unfolding Suc is_partition_def using j ij using Suc Suc_less_eq2 by fastforce
    qed
  }
  then show ?case unfolding is_partition_def by simp
qed

lemma filter_ex_index:
  assumes "x = filter f xs ! i" "i < length (filter f xs)" 
  shows "\<exists>j. j < length xs \<and> x = xs!j"
  using assms proof(induct "xs" arbitrary:i)
  case (Cons y ys)
  show ?case proof(cases "f y")
    case True
    then have filter:"filter f (y#ys) = y#(filter f ys)" by simp 
    show ?thesis proof(cases i)
      case 0
      from Cons(2) show ?thesis unfolding filter 0 by auto
    next
      case (Suc n)
      from Cons(2) have "x = filter f ys ! n" 
        unfolding Suc filter by simp
      moreover from Cons(3) have "n < length (filter f ys)" 
        unfolding Suc filter by simp
      ultimately obtain j where "j<length ys" and "x = ys ! j" 
        using Cons(1) by blast
      then show ?thesis by auto 
    qed
  next
    case False
    then have filter:"filter f (y#ys) = filter f ys" by simp
    from Cons obtain j where "j<length ys" and "x = ys ! j" 
      unfolding filter by blast 
    then show ?thesis by auto
  qed
qed simp

lemma filter_index_neq':
  assumes "i < j" "j < length (filter f xs)"
  shows "\<exists> i' j'. i' < length xs \<and> j' < length xs \<and> i' < j' \<and> xs ! i' = (filter f xs) ! i \<and> xs ! j' = (filter f xs) ! j" 
  using assms proof(induct xs arbitrary: i j)
  case (Cons x xs)
  then show ?case proof(cases "f x")
    case True
    show ?thesis proof(cases i)
      case 0
      then have i0:"filter f (x#xs) ! i = (x#xs) ! 0" 
        using \<open>f x\<close> by simp 
      from Cons(2) obtain j' where "j = Suc j'" 
        unfolding 0 using gr0_implies_Suc by blast
      with Cons(3) have "j' < length (filter f xs)" 
        unfolding filter.simps using \<open>f x\<close> by simp  
      then obtain j'' where j'':"j'' < length xs" "filter f xs ! j' = xs ! j''"
        by (meson filter_ex_index) 
      then have "filter f (x#xs) ! j = (x#xs) ! (Suc j'')" 
        using \<open>f x\<close> \<open>j = Suc j'\<close> by simp
      with i0 j''(1) show ?thesis
        by (metis length_nth_simps(2) not_less_eq zero_less_Suc)
    next
      case (Suc i')
      from Cons(2) obtain j' where j:"j = Suc j'" 
        unfolding Suc using Suc_lessE by auto 
      from Cons(1)[of i' j'] Cons(2,3) obtain i'' j'' where "i'' < length xs" "j'' < length xs" "i'' < j''" "xs ! i'' = filter f xs ! i'" "xs ! j'' = filter f xs ! j'"
        using Suc True j by auto 
      then show ?thesis
        by (smt (verit) Suc Suc_less_eq True filter.simps(2) j length_nth_simps(2) nth_Cons_Suc)
    qed
  next
    case False
    then have "filter f (x#xs) = filter f xs" by simp
    with Cons show ?thesis
      by (metis Suc_less_eq length_nth_simps(2) nth_Cons_Suc)
  qed
qed simp

lemma filter_index_neq:
  assumes "i \<noteq> j" "i < length (filter f xs)" "j < length (filter f xs)"
  shows "\<exists> i' j'. i' < length xs \<and> j' < length xs \<and> i' \<noteq> j' \<and> xs ! i' = (filter f xs) ! i \<and> xs ! j' = (filter f xs) ! j"
using assms filter_index_neq' proof(cases "i < j")
  case False
  then have *:"j < i" using assms(1) by simp
  then show ?thesis using filter_index_neq'[OF * assms(2)] by blast
qed blast

lemma nth_drop_equal: 
  assumes "length xs = length ys"
    and "\<forall>j < length xs. j \<ge> i \<longrightarrow> xs!j = ys!j"
  shows "drop i xs = drop i ys"
using assms proof (induct i arbitrary: xs ys)
  case 0
  then show ?case
    using nth_equalityI by blast
next
  case (Suc i)
  then show ?case proof(cases "Suc i < length xs")
    case True
    then obtain x xs' where x:"xs = x # xs'"
      by (metis Suc_length_conv Suc_lessE) 
    with Suc(2) obtain y ys' where y:"ys = y # ys'"
      by (metis length_greater_0_conv nth_drop_0)
    from Suc(1)[of xs' ys'] have "drop i xs' = drop i ys'"
      using Suc(2,3) unfolding x y
      by (metis Suc_le_mono length_nth_simps(2) linorder_not_le nat.inject nth_Cons_Suc)
    then show ?thesis unfolding x y by simp
  qed simp
qed

lemma union_take_drop_list:
  assumes "i < length xs"
  shows "(set (take i xs)) \<union> (set (drop (Suc i) xs)) = {xs!j | j. j < length xs \<and> j \<noteq> i}"
proof-
  from assms have i:"i \<le> length xs" by simp
  have set1:"set (take i xs) = {xs ! j |j. j < i}" 
    using nth_image[OF i] unfolding image_def by fastforce
  from assms have i:"Suc i \<le> length xs" by simp
  have set2:"set (drop (Suc i) xs) = {xs !j |j. i < j \<and> j < length xs}" proof
    {fix x assume "x \<in> set (drop (Suc i) xs)" 
      then have "x \<in> {xs !j |j. i < j \<and> j < length xs}" 
        unfolding set_conv_nth nth_drop[OF i] length_drop by auto 
    }
    then show "set (drop (Suc i) xs) \<subseteq> {xs ! j |j. i < j \<and> j < length xs}" by auto
    {fix x assume "x \<in> {xs !j |j. i < j \<and> j < length xs}" 
      then have "x \<in> set (drop (Suc i) xs)" 
        unfolding set_conv_nth nth_drop[OF i] length_drop
        by (smt (verit, best) Suc_leI add_diff_inverse_nat i mem_Collect_eq nat_add_left_cancel_less not_less_eq_eq)
    }
    then show "{xs ! j |j. i < j \<and> j < length xs} \<subseteq> set (drop (Suc i) xs)" by auto
  qed
  {fix x assume "x \<in> set (take i xs) \<union> set (drop (Suc i) xs)"
    then consider "x \<in> set (take i xs)" | "x \<in> set (drop (Suc i) xs)" by blast
    then have "x \<in> {xs ! j |j. j < length xs \<and> j \<noteq> i}" proof(cases)
      case 1
      with set1 show ?thesis using in_set_idx by fastforce
    next
      case 2
      with set2 show ?thesis using in_set_idx by fastforce
    qed
  }moreover
  {fix x assume "x \<in> {xs ! j |j. j < length xs \<and> j \<noteq> i}"
    then obtain j where "x = xs!j" and j:"j < length xs" "j \<noteq> i"
      by blast
    then have "x \<in> set (take i xs) \<union> set (drop (Suc i) xs)" 
      using set1 set2 using nat_neq_iff by auto
  }
  ultimately show ?thesis by auto
qed

lemma list_tl_eq:
  assumes "length xs = length ys" "xs \<noteq> []"
    and "\<forall>i < length xs. i > 0 \<longrightarrow> xs!i = ys!i"
  shows "tl xs = tl ys"
  by (metis Suc_le_lessD assms(1) assms(3) length_greater_0_conv list.sel(3) nth_drop_0 nth_drop_equal) 

subsubsection\<open>Lists of @{type option}\<close>

lemma length_those:
  assumes "those xs = Some ys"
  shows "length xs = length ys"
  using assms proof(induction xs arbitrary:ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons(2) obtain ys' where ys':"those xs = Some ys'"
    by (smt not_None_eq option.case_eq_if option.simps(8) those.simps(2)) 
  from Cons(2) obtain y where y:"Some y = a"
    by (metis option.case_eq_if option.exhaust_sel option.simps(3) those.simps(2)) 
  from y ys' have "those (Cons a xs) = Some (Cons y ys')"
    by auto
  then show ?case using Cons ys'
    by auto
qed

lemma those_not_none_x: "those xs = Some ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<noteq> None"
proof (induction xs arbitrary: x ys)
  case (Cons a xs)
  from Cons(2) have "a \<noteq> None" using option.simps(4) by fastforce 
  from this Cons(2) have "those xs \<noteq> None" by auto
  then show ?case using Cons(1,3) \<open>a \<noteq> None\<close> by auto
qed (simp)

lemma those_not_none_xs: "list_all (\<lambda>x. x \<noteq> None) xs \<Longrightarrow> those xs \<noteq> None"
  by (induction xs) auto

lemma those_some:
  assumes "length xs = length ys" "\<forall>i < length xs. xs!i = Some (ys!i)" 
  shows "those xs = Some ys"
  using assms by (induct rule:list_induct2) (simp, force)

lemma those_some2:
  assumes "those xs = Some ys"
  shows "\<forall>i < length xs. xs!i = Some (ys!i)"
proof-
  from assms have "length xs = length ys" by (simp add: length_those)
  then show ?thesis using assms proof(induction xs ys rule:list_induct2)
    case (Cons x xs y ys)
    from Cons(3) have "x \<noteq> None" by (metis list.set_intros(1) those_not_none_x)
    with Cons(3) have *:"x = Some y" by force
    with Cons(3) have "those xs = Some ys" by force
    with * Cons(2) show ?case by (simp add: nth_Cons') 
  qed simp
qed

lemma exists_some_list:
  assumes "\<forall>i < length xs. (\<exists>y. xs!i = Some y)"
  shows "\<exists> ys. (\<forall>i < length xs. xs!i = Some (ys!i)) \<and> length ys = length xs"
  by (metis assms length_map nth_map option.sel)

subsection\<open>Results About Linear Terms\<close>

lemma linear_term_var_vars_term_list:
  assumes "linear_term t"
  shows "vars_term_list t = vars_distinct t"
  using assms linear_term_distinct_vars
  by (metis comp_apply distinct_rev remdups_id_iff_distinct rev_rev_ident)

lemma linear_term_unique_vars:
  assumes "linear_term s"
    and "p \<in> poss s" and "s|_p = Var x"
    and "q \<in> poss s" and "s|_q = Var x"
  shows "p = q"
proof(rule ccontr)
  assume "p \<noteq> q"
  with assms(2-) obtain i j where ij:"i < length (var_poss_list s)" "j < length (var_poss_list s)" "i \<noteq> j" 
    "var_poss_list s ! i = p" "var_poss_list s ! j = q"
    by (metis in_set_idx var_poss_iff var_poss_list_sound) 
  with assms(3,5) have "vars_term_list s ! i = vars_term_list s ! j"
    by (metis length_var_poss_list term.inject(1) vars_term_list_var_poss_list) 
  moreover from assms(1) have "distinct (vars_term_list s)"
    by (metis distinct_remdups distinct_rev linear_term_var_vars_term_list o_apply) 
  ultimately show False using ij(1,2,3)
    by (metis distinct_Ex1 length_var_poss_list nth_mem) 
qed

lemma linear_term_ctxt:
  assumes "linear_term t"
    and "p \<in> poss t"
  shows "vars_ctxt (ctxt_of_pos_term p t) \<inter> vars_term (t|_p) = {}"
  using assms proof(induct p arbitrary:t)
  case (Cons i p)
  from Cons(3) obtain f ts where t:"t = Fun f ts" "i < length ts" "p \<in> poss (ts!i)"
    using args_poss by blast 
  with Cons(1,2) have IH:"vars_ctxt (ctxt_of_pos_term p (ts!i)) \<inter> vars_term ((ts!i) |_ p) = {}"
    by simp 
  {fix j assume j:"j < length ts" "j \<noteq> i"
    with Cons(2) have "vars_term (ts!j) \<inter> vars_term (ts!i |_p) = {}"
      unfolding t using var_in_linear_args t(2,3) by (metis (no_types, opaque_lifting) Int_Un_distrib disjoint_iff sup_bot.neutr_eq_iff vars_ctxt_pos_term) 
  }
  then have "\<Union> {vars_term (ts ! j) |j. j < length ts \<and> j \<noteq> i} \<inter> vars_term (ts!i |_p) = {}"
    by blast 
  moreover have "(\<Union> (vars_term ` set (take i ts)) \<union> \<Union> (vars_term ` set (drop (Suc i) ts))) = 
                \<Union> {vars_term (ts ! j) |j. j < length ts \<and> j \<noteq> i}" 
    unfolding set_map[symmetric] take_map[symmetric] drop_map[symmetric] Union_Un_distrib[symmetric]
    using union_take_drop_list[where xs="(map vars_term ts)"] unfolding length_map using t(2) by auto
  ultimately show ?case unfolding t ctxt_of_pos_term.simps subt_at.simps using IH
    by (metis (no_types, lifting) bot_eq_sup_iff inf_sup_distrib2 vars_ctxt.simps(2))      
qed simp

lemma linear_term_obtain_subst:
  assumes "linear_term (Fun f ts)" and l:"length ts = length ss"
    and substs: "\<forall>i< length ts. (\<exists>\<sigma>. ts!i \<cdot> \<sigma> = ss!i)" 
  shows "\<exists>\<sigma>. Fun f ts \<cdot> \<sigma> = Fun f ss" 
  using assms proof(induct ts arbitrary: ss)
  case (Cons t ts)
  from Cons(3) obtain s ss' where ss:"ss = s#ss'"
    by (metis length_Suc_conv)
  from Cons(2) have lin:"linear_term (Fun f ts)" 
    unfolding linear_term.simps by (simp add: is_partition_Cons) 
  from Cons(4) have "\<forall>i<length ts. \<exists>\<sigma>. ts ! i \<cdot> \<sigma> = ss' ! i"
    unfolding ss by (metis length_nth_simps(2) not_less_eq nth_Cons_Suc) 
  then obtain \<sigma> where \<sigma>:"Fun f ts \<cdot> \<sigma> = Fun f ss'" 
    using Cons(1)[OF lin, of ss'] using Cons.prems(2) ss by auto 
  from Cons(4) obtain \<sigma>1 where \<sigma>1:"t \<cdot> \<sigma>1 = s"
    using ss by auto 
  let ?\<sigma>="\<lambda>x. if x \<in> vars_term t then \<sigma>1 x else \<sigma> x" 
  have t:"t \<cdot> ?\<sigma> = s"
    by (simp add: \<sigma>1 term_subst_eq) 
  {fix i assume "i < length ts" 
    then have "ts!i \<cdot> ?\<sigma> = ss'!i"
      by (smt (verit, ccfv_SIG) Cons.prems(1) Cons.prems(2) Suc_inject Suc_leI \<sigma> \<sigma>1 eval_term.simps(2) le_imp_less_Suc length_nth_simps(2) map_nth_eq_conv nth_Cons_0 nth_Cons_Suc ss term.sel(4) term_subst_eq var_in_linear_args zero_less_Suc)
  }
  with t have "Fun f (t#ts) \<cdot> ?\<sigma> = Fun f ss"
    using Cons.prems(2) map_nth_eq_conv ss by auto 
  then show ?case by blast
qed simp

lemma linear_ctxt_of_pos_term:
  assumes "linear_term t" and lin_s:"linear_term s" and p:"p \<in> poss t"
    and "vars_term t \<inter> vars_term s = {}" 
  shows "linear_term (replace_at t p s)" 
using assms proof(induct t arbitrary:p)
  case (Var x)
  with p have "p = []" by simp
  with lin_s show ?case by simp
next
  case (Fun f ts)
  from lin_s show ?case proof(cases p)
    case (Cons i p')
    with Fun(4) have i:"i < length ts" by simp
    with Fun(4) have p':"p' \<in> poss (ts!i)" unfolding Cons by simp
    {fix n assume n:"n < length ts" "n \<noteq> i"
      with Fun(2) have "vars_term (ts!n) \<inter> vars_term (ts!i) = {}"
        by (metis disjoint_iff i var_in_linear_args) 
      then have "vars_term (ts!n) \<inter> vars_ctxt (ctxt_of_pos_term p' (ts!i)) = {}"
        using p' vars_ctxt_pos_term by fastforce 
      moreover from n Fun(5) have "vars_term (ts!n) \<inter> vars_term s = {}"
        by (meson disjoint_iff nth_mem term.set_intros(4))
      ultimately have "vars_term (ts!n) \<inter> vars_term ((ctxt_of_pos_term p' (ts ! i))\<langle>s\<rangle>) = {}"
        unfolding vars_term_ctxt_apply by blast
    }
    with Fun(2) have "is_partition (map vars_term (take i ts @ (ctxt_of_pos_term p' (ts ! i))\<langle>s\<rangle> # drop (Suc i) ts))"
      unfolding linear_term.simps is_partition_def by (smt (z3) Int_commute append_Cons_nth_not_middle i id_take_nth_drop 
          length_append length_map length_nth_simps(2) linorder_neq_iff nth_append_take nth_map order.strict_implies_order order.strict_trans) 
    moreover have "linear_term ((ctxt_of_pos_term p' (ts ! i))\<langle>s\<rangle>)" 
      using Fun p' by (meson disjoint_iff i linear_term.simps(2) nth_mem term.set_intros(4)) 
    ultimately show ?thesis 
      using Fun(2) unfolding Cons ctxt_of_pos_term.simps intp_actxt.simps linear_term.simps
      by (metis Un_iff in_set_dropD in_set_takeD set_ConsD set_append)
  qed simp
qed

lemma distinct_vars:
  assumes "\<And>p q x y. p \<noteq> q \<Longrightarrow> p \<in> poss t \<Longrightarrow> q \<in> poss t \<Longrightarrow> t|_p = Var x \<Longrightarrow> t|_q = Var y \<Longrightarrow> x \<noteq> y"
  shows "distinct (vars_term_list t)" 
proof-
  {fix i j assume ij:"i \<noteq> j" and i:"i < length (vars_term_list t)" and j:"j < length (vars_term_list t)" 
    let ?p="var_poss_list t ! i" and ?q="var_poss_list t ! j" 
    let ?x="vars_term_list t ! i" and ?y="vars_term_list t ! j" 
    from ij i j have pq:"?p \<noteq> ?q"
      by (simp add: distinct_var_poss_list length_var_poss_list nth_eq_iff_index_eq) 
    have p:"?p \<in> poss t"
      by (metis i length_var_poss_list nth_mem var_poss_imp_poss var_poss_list_sound) 
    have q:"?q \<in> poss t"
      by (metis j length_var_poss_list nth_mem var_poss_imp_poss var_poss_list_sound) 
    have "?x \<noteq> ?y" 
      using assms[OF pq p q] i j by (simp add: vars_term_list_var_poss_list) 
  }
  then show ?thesis by (meson distinct_conv_nth) 
qed

lemma distinct_vars_linear_term:
  assumes "distinct (vars_term_list t)"
  shows "linear_term t" 
  using assms proof(induct t)
  case (Fun f ts)
  {fix t assume t:"t \<in> set ts" 
    with Fun(2) have "distinct (vars_term_list t)" 
      unfolding vars_term_list.simps by (simp add: distinct_concat_iff) 
    with t Fun(1) have "linear_term t"
      by auto
  }
  moreover have "is_partition (map vars_term ts)" 
    using Fun(2) unfolding vars_term_list.simps using distinct_is_partition set_vars_term_list
    by (metis (mono_tags, lifting) length_map map_nth_eq_conv)
  ultimately show ?case by simp
qed simp

lemma distinct_vars_eq_linear: "linear_term t = distinct (vars_term_list t)"
  using distinct_vars_linear_term linear_term_distinct_vars by blast 

subsection\<open>Results About Substitutions and Contexts\<close>

lemma ctxt_apply_term_subst:
  assumes "linear_term t" and "i < length (vars_term_list t)"
    and "p = (var_poss_list t)!i"
  shows "(ctxt_of_pos_term p (t \<cdot> \<sigma>))\<langle>s\<rangle> = t \<cdot> \<sigma>((vars_term_list t)!i := s)"
proof-
  from assms(2,3) have "t|_p = Var ((vars_term_list t)!i)"
    by (metis vars_term_list_var_poss_list)
  with assms show ?thesis
    by (smt (verit, ccfv_threshold) filter_cong fun_upd_other fun_upd_same length_var_poss_list linear_term_replace_in_subst nth_mem var_poss_imp_poss var_poss_list_sound)
qed

lemma ctxt_subst_apply:
  assumes "p \<in> poss t" and "t|_p = Var x"
    and "linear_term t"
  shows "((ctxt_of_pos_term p t) \<cdot>\<^sub>c \<sigma>)\<langle>s\<rangle> = t \<cdot> \<sigma>(x := s)"
  unfolding ctxt_of_pos_term_subst[symmetric, OF assms(1)]
  using assms 
  by (smt (verit) fun_upd_apply linear_term_replace_in_subst)

lemma ctxt_of_pos_term_hole_subst:
  assumes "linear_term t" 
    and "i < length (var_poss_list t)" and "p = var_poss_list t ! i"
    and "\<forall>x \<in> vars_term t. x \<noteq> vars_term_list t !i \<longrightarrow> \<sigma> x = \<tau> x"
  shows "ctxt_of_pos_term p (t \<cdot> \<sigma>) = ctxt_of_pos_term p (t \<cdot> \<tau>)"
  using assms proof(induct p arbitrary: t i)
  case (Cons j p)
  from Cons(3,4) have "j#p \<in> var_poss t"
    using nth_mem by force 
  then obtain f ts where ts:"j < length ts" "t = Fun f ts" "p \<in> var_poss (ts!j)"
    by (metis args_poss subt_at.simps(2) var_poss_iff) 
  then obtain i' where i':"i' < length (var_poss_list (ts!j))" "p = var_poss_list (ts!j)!i'"
    using var_poss_list_sound by (metis in_set_conv_nth)
  from Cons(3,4) have "Var (vars_term_list t ! i) = t|_(j#p)"
    by (metis length_var_poss_list vars_term_list_var_poss_list) 
  also have "... = (ts!j)|_p" 
    unfolding ts(2) by simp
  also have "... = Var (vars_term_list (ts!j) ! i')" 
    using i' by (simp add: length_var_poss_list vars_term_list_var_poss_list) 
  finally have *:"vars_term_list t ! i = vars_term_list (ts ! j) ! i'" by simp
  with Cons(5) have "\<forall>x\<in>vars_term (ts!j). x \<noteq> vars_term_list (ts!j) ! i' \<longrightarrow> \<sigma> x = \<tau> x" 
    unfolding ts(2) using ts(1) by auto 
  with Cons(2) i' ts have IH:"ctxt_of_pos_term p ((ts!j) \<cdot> \<sigma>) = ctxt_of_pos_term p ((ts!j) \<cdot> \<tau>)"  
    using Cons(1)[of "ts!j" i'] by (meson linear_term.simps(2) nth_mem) 
  {fix j' assume j':"j' < length ts" "j' \<noteq> j"
    with Cons(2) have "vars_term (ts ! j') \<inter> vars_term (ts!j) = {}" 
      unfolding ts(2) by (metis disjoint_iff ts(1) var_in_linear_args)
    then have "\<forall>x \<in> vars_term (ts!j'). \<sigma> x = \<tau> x" 
      using Cons(5) j' * by (metis disjoint_iff i'(1) length_var_poss_list nth_mem set_vars_term_list term.set_intros(4) ts(2)) 
    then have "(ts!j') \<cdot> \<sigma> = (ts!j') \<cdot> \<tau>"
       by (meson term_subst_eq)
   } note t'=this
  with ts(1) have "take j (map (\<lambda>t. t \<cdot> \<sigma>) ts) = take j (map (\<lambda>t. t \<cdot> \<tau>) ts)" 
    using nth_take_lemma[of j "(map (\<lambda>t. t \<cdot> \<sigma>) ts)" "(map (\<lambda>t. t \<cdot> \<tau>) ts)"] by simp
  moreover from t' ts(1) have "(drop (Suc j) (map (\<lambda>t. t \<cdot> \<sigma>) ts)) = (drop (Suc j) (map (\<lambda>t. t \<cdot> \<tau>) ts))"
    using nth_drop_equal[of "(map (\<lambda>t. t \<cdot> \<sigma>) ts)" "(map (\<lambda>t. t \<cdot> \<tau>) ts)" "Suc j"] by auto
  ultimately show ?case 
    unfolding ts(2) eval_term.simps ctxt_of_pos_term.simps using IH by (simp add: ts(1)) 
qed simp

lemma ctxt_apply_ctxt_apply:
  assumes "p \<in> poss t"
  shows "(ctxt_of_pos_term (p@q) ((ctxt_of_pos_term p t) \<langle>s\<rangle>)) \<langle>u\<rangle> = (ctxt_of_pos_term p t)\<langle>(ctxt_of_pos_term q s) \<langle>u\<rangle>\<rangle>"
  by (metis assms ctxt_ctxt ctxt_of_pos_term_append hole_pos_ctxt_of_pos_term hole_pos_id_ctxt hole_pos_poss replace_at_subt_at)

lemma replace_at_append_subst:
  assumes "linear_term t"
    and "p \<in> poss t" "t|_p = Var x"
  shows "(ctxt_of_pos_term (p@q) (t \<cdot> \<sigma>)) \<langle>s\<rangle> = t \<cdot> \<sigma>(x := (ctxt_of_pos_term q (\<sigma> x)) \<langle>s\<rangle>)"
  using assms proof(induct p arbitrary:t)
  case (Cons i p)
  then obtain f ts where t:"t = Fun f ts" and i:"i < length ts" and p:"p \<in> poss (ts!i)"
    by (meson args_poss)
  from Cons(4) have x:"(ts!i)|_p = Var x" 
    unfolding t by simp
  from Cons(2) have lin:"linear_term (ts!i)"
    using i t by simp
  have IH:"(ctxt_of_pos_term (p@q) ((ts!i) \<cdot> \<sigma>)) \<langle>s\<rangle> = (ts!i) \<cdot> \<sigma>(x := (ctxt_of_pos_term q (\<sigma> x)) \<langle>s\<rangle>)"
    using Cons(1)[OF lin p x] .
  let ?\<sigma>="\<sigma>(x := (ctxt_of_pos_term q (\<sigma> x)) \<langle>s\<rangle>)"
  {fix j assume j:"j < length ts" "j \<noteq> i"
    from x have "x \<in> vars_term (ts!i)"
      by (metis p subsetD term.set_intros(3) vars_term_subt_at)
    then have "x \<notin> vars_term (ts!j)" 
      using j Cons(2) unfolding t by (meson i var_in_linear_args) 
    then have "(ts!j) \<cdot> \<sigma> = (ts!j) \<cdot> ?\<sigma>"
      by (simp add: term_subst_eq_conv)
  } note sigma=this
  then have "take i (map (\<lambda>t. t \<cdot> \<sigma>) ts) = take i (map (\<lambda>t. t \<cdot> ?\<sigma>) ts)"
    using nth_take_lemma[of i "(map (\<lambda>t. t \<cdot> \<sigma>) ts)" "(map (\<lambda>t. t \<cdot> ?\<sigma>) ts)"] i by simp 
  moreover from sigma have "drop (Suc i) (map (\<lambda>t. t \<cdot> \<sigma>) ts) = drop (Suc i) (map (\<lambda>t. t \<cdot> ?\<sigma>) ts)"
     using nth_drop_equal[of "(map (\<lambda>t. t \<cdot> \<sigma>) ts)" "(map (\<lambda>t. t \<cdot> ?\<sigma>) ts)"] i by simp 
  ultimately show ?case 
    unfolding t append_Cons eval_term.simps ctxt_of_pos_term.simps intp_actxt.simps nth_map[OF i] IH
    by (metis i id_take_nth_drop length_map nth_map)
qed simp

lemma replace_at_fun_poss_not_below:
  assumes "\<not> p \<le>\<^sub>p q"
    and "p \<in> poss t" and "q \<in> fun_poss (replace_at t p s)"
  shows "q \<in> fun_poss t"
  using assms by (metis ctxt_supt_id fun_poss_ctxt_apply_term hole_pos_ctxt_of_pos_term less_eq_pos_def) 

lemma substitution_subterm_at:
  assumes "\<forall>j < length (vars_term_list l). \<sigma> (vars_term_list l ! j) = s |_ (var_poss_list l ! j)"
    and "\<exists>\<tau>. l \<cdot> \<tau> = s"
  shows "l \<cdot> \<sigma> = s"
  using assms proof(induct l arbitrary:s)
  case (Var x)
  then show ?case 
    unfolding vars_term_list.simps poss_list.simps var_poss.simps eval_term.simps by simp 
next
  case (Fun f ts)
  from Fun(3) obtain ss where s:"s = Fun f ss" and l:"length ts = length ss"
    by fastforce 
  {fix i assume i:"i < length ts"
    {fix j assume j:"j<length (vars_term_list (ts!i))" 
      let ?p="var_poss_list (ts!i) ! j"
      let ?x="vars_term_list (ts!i) ! j"
      let ?k="sum_list (map (length \<circ> vars_term_list) (take i ts)) + j"
      from i j have x:"?x = vars_term_list (Fun f ts) ! ?k"
        unfolding vars_term_list.simps by (simp add: concat_nth take_map) 
      have p:"var_poss_list (Fun f ts) ! ?k = i # ?p" proof-
        from i have i':"i < length (map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts))" 
          by simp 
        from i j have "j < length ((map var_poss_list ts) ! i)" 
          using length_var_poss_list by (metis (mono_tags, lifting) nth_map) 
        with i have j':"j < length (map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts) ! i)"
          by simp
        {fix l assume "l < length ts"
          then have "(map length (map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts)))!l = (map (length \<circ> vars_term_list) ts) ! l" 
            using length_var_poss_list by simp
        }  
        then have "map length (map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts)) = map (length \<circ> vars_term_list) ts" 
          using nth_equalityI[where ys="map (length \<circ> vars_term_list) ts"] by simp
        with i have k:"sum_list (map length (take i (map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts)))) + j = ?k"
          by (metis take_map)
        then have "var_poss_list (Fun f ts) ! ?k = (map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts))!i !j" 
          unfolding var_poss_list.simps using concat_nth[OF i' j'] by presburger
        also have "... = (map ((#) i) (var_poss_list (ts!i)))!j" using i by simp
        also have "... = i # ?p" using nth_map j length_var_poss_list by metis
        ultimately show ?thesis by simp
      qed
      from i j have k:"?k < length (vars_term_list (Fun f ts))" 
        unfolding vars_term_list.simps by (metis concat_nth_length length_map map_map nth_map take_map) 
      from Fun(2) k have "\<sigma> ?x = (ss!i) |_ (var_poss_list (ts!i) ! j)" 
        unfolding x s using p by simp
    }
    then have "\<forall>j<length (vars_term_list (ts!i)).\<sigma> (vars_term_list (ts!i) ! j) = (ss!i) |_ var_poss_list (ts!i) ! j" 
      by simp
    moreover from Fun(3) have "\<exists>\<tau>. (ts!i) \<cdot> \<tau> = ss!i" 
      unfolding eval_term.simps s using i l by (metis nth_map term.inject(2))
    ultimately have "(ts!i) \<cdot> \<sigma> = ss!i " 
      using i Fun(1) nth_mem by blast  
  }
  then show ?case unfolding eval_term.simps s 
    using l by (simp add: map_nth_eq_conv)
qed

lemma vars_map_vars_term:
  "map f (vars_term_list t) = vars_term_list (map_vars_term f t)"
unfolding map_vars_term_eq proof(induct t)
  case (Fun g ts)
  then have "map (\<lambda>xs. map f xs)(map vars_term_list ts) = map vars_term_list (map (\<lambda>t. t \<cdot> (Var \<circ> f)) ts)"
    by fastforce
  then show ?case unfolding vars_term_list.simps eval_term.simps map_map map_concat
    by presburger
qed (simp add: vars_term_list.simps)

lemma ctxt_apply_subt_at:
  assumes "q \<in> poss s" 
  shows "(ctxt_of_pos_term p (s|_q)) \<langle>t\<rangle> = (ctxt_of_pos_term (q@p) s) \<langle>t\<rangle> |_ q"
using assms proof(induct q arbitrary: s)
  case (Cons i q)
  from Cons(2) obtain f ss where i:"i < length ss" and s:"s = Fun f ss"
    by (meson args_poss) 
  from i Cons show ?case unfolding s
    by (metis ctxt_apply_ctxt_apply ctxt_supt_id replace_at_subt_at) 
qed simp

subsubsection\<open>Utilities for @{const mk_subst}\<close>
text\<open>We consider the special case of applying @{const mk_subst} when the variables involved form a partition.\<close>

lemma mk_subst_same:
  assumes "length xs = length ts" "distinct xs"
  shows "map (mk_subst f (zip xs ts)) xs = ts"
  using assms by (simp add: mk_subst_distinct map_nth_eq_conv)

lemma map2_zip: "set (map fst (concat (map2 zip xs ys))) \<subseteq> set (concat xs)"
proof
  fix x assume x:"x \<in> set (map fst (concat (map2 zip xs ys)))"
  let ?l="min (length xs) (length ys)"
  from x obtain i where i:"i < ?l" "x \<in> set (map fst (zip (xs!i) (ys!i)))"
    by (smt (verit) case_prod_conv in_set_conv_nth length_map length_zip min.strict_boundedE nth_concat_split nth_map nth_zip) 
  then have "x \<in> set (xs!i)"
    by (metis in_set_takeD map_fst_zip_take) 
  then show "x \<in> set (concat xs)"
    using i(1) by (metis concat_nth concat_nth_length in_set_conv_nth min.strict_boundedE) 
qed

lemma mk_subst_partition: 
  fixes xs :: "'a list list"
  assumes l:"length xs = length ss"
    and part:"is_partition (map set xs)"
  shows "\<forall>i < length xs. \<forall>x \<in> set (xs!i). (mk_subst f (zip (xs!i) (ss!i))) x = (mk_subst f (concat (map2 zip xs ss))) x"
proof-
  {fix i assume i:"i < length xs" 
    {fix x assume x:"x \<in> set (xs!i)"
      have "concat (map2 zip xs ss) = concat (map2 zip (take i xs) (take i ss)) @ concat (map2 zip (drop i xs) (drop i ss))"
        by (metis append_take_drop_id concat_append drop_map drop_zip take_map take_zip)
      moreover have "concat (map2 zip (drop i xs) (drop i ss)) = concat (zip (xs!i) (ss!i) # (map2 zip (drop (Suc i) xs) (drop (Suc i) ss)))"
        using i l by (smt (verit, del_insts) Cons_nth_drop_Suc list.map(2) prod.simps(2) zip_Cons_Cons) 
      ultimately have cc:"concat (map2 zip xs ss) = concat (map2 zip (take i xs) (take i ss)) @ 
                concat (zip (xs!i) (ss!i) # (map2 zip (drop (Suc i) xs) (drop (Suc i) ss)))" by presburger
      {fix j assume "j < length xs" and "j \<noteq> i"
        with i x part have "x \<notin> set (xs!j)" 
          unfolding is_partition_alt is_partition_alt_def by auto
      } note part=this
      then have "x \<notin> set (concat (take i xs))"
        by (smt (verit) in_set_conv_nth length_take less_length_concat min.strict_boundedE nth_take order_less_irrefl)
      then have "x \<notin> set (map fst (concat (map2 zip (take i xs) (take i ss))))" 
        using map2_zip in_mono by fastforce 
      then have subst:"(mk_subst f (concat (map2 zip xs ss))) x = (mk_subst f (concat (zip (xs!i) (ss!i) # 
                                                                  (map2 zip (drop (Suc i) xs) (drop (Suc i) ss))))) x"
        unfolding cc using mk_subst_concat by metis
      have "mk_subst f (zip (xs ! i) (ss ! i)) x = (mk_subst f (concat (map2 zip xs ss))) x"
      proof(cases "x \<in> set (map fst (zip (xs!i) (ss!i)))")
        case True
        then show ?thesis 
          using mk_subst_concat_Cons subst by metis
      next
        case False
        {fix j assume j:"j < length (drop (Suc i) xs)"
          then have "(drop (Suc i) xs)!j = xs!(Suc i + j)"
              using Suc_leI i nth_drop by blast 
            moreover from i j have "Suc i + j < length xs"
              by (metis add.commute length_drop less_diff_conv) 
            ultimately have "x \<notin> set ((drop (Suc i) xs)!j)" 
              using part by (metis Suc_n_not_le_n le_add1) 
          }        
          then have "x \<notin> set (concat (drop (Suc i) xs))" 
            by (smt (verit) in_set_conv_nth length_map length_take less_not_refl2 min.strict_boundedE nth_concat_split nth_map nth_take) 
          then have "x \<notin> set (map fst (concat (map2 zip (drop (Suc i) xs) (drop (Suc i) ss))))" 
            using map2_zip in_mono by fastforce 
          with False have "x \<notin> set (map fst (concat (zip (xs!i) (ss!i) # (map2 zip (drop (Suc i) xs) (drop (Suc i) ss)))))" 
            unfolding concat.simps by (metis Un_iff map_append set_append)
          with False show ?thesis 
            unfolding subst using mk_subst_not_mem' by metis
        qed
      }                         
    }
  then show ?thesis by simp
qed

text\<open>The following lemma is used later to show that @{text "A = (to_pterm (lhs \<alpha>)) \<cdot> \<sigma>"} implies 
@{text "A = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>"} for some suitable @{text As}.\<close>
lemma subst_imp_mk_subst:
  assumes "s = t \<cdot> \<sigma>"
  shows "\<exists>ss. t \<cdot> \<sigma> = t \<cdot> (mk_subst Var (zip (vars_distinct t) ss)) \<and> length ss = length (vars_distinct t) \<and> (\<forall>i < length ss. \<sigma> (vars_distinct t!i) = ss!i)" 
proof-
  let ?ss="map \<sigma> (vars_distinct t)"
  let ?\<tau>="(mk_subst Var (zip (vars_distinct t) ?ss))"
  {fix x assume "x \<in> vars_term t"
    then have "\<sigma> x = ?\<tau> x" unfolding mk_subst_def
      by (simp add: map_of_zip_map) 
  }
  then have "t \<cdot> \<sigma> = t \<cdot> ?\<tau>"  
    using term_subst_eq by blast 
  then show ?thesis by auto
qed

lemma mk_subst_rename:
  assumes "length (vars_distinct t) = length xs" and "inj f"
  shows "t \<cdot> (mk_subst Var (zip (vars_distinct t) xs)) = (map_vars_term f t) \<cdot> (mk_subst Var (zip (vars_distinct (map_vars_term f t)) xs))" 
proof-
  {fix x assume "x \<in> vars_term t" 
    then obtain i where i:"x = (vars_distinct t)!i" "i < length (vars_distinct t)"
      by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct) 
    with assms have 1:"(mk_subst Var (zip (vars_distinct t) xs)) x = xs!i" 
      using mk_subst_distinct by (metis comp_apply distinct_remdups distinct_rev) 
    have "vars_distinct (map_vars_term f t) = map f (vars_distinct t)" 
      unfolding vars_map_vars_term[symmetric] comp_apply using assms(2)
      by (metis distinct_map distinct_remdups distinct_remdups_id inj_on_inverseI remdups_map_remdups rev_map the_inv_f_f)
    with assms i have 2:"(mk_subst Var (zip (vars_distinct (map_vars_term f t)) xs)) (f x) = xs!i"
      by (metis (mono_tags, lifting) comp_apply distinct_remdups distinct_rev length_map mk_subst_same nth_map) 
    from 1 2 have "(mk_subst Var (zip (vars_distinct t) xs)) x = (mk_subst Var (zip (vars_distinct (map_vars_term f t)) xs)) (f x)"
      by presburger
  }
  then show ?thesis
    by (simp add: apply_subst_map_vars_term term_subst_eq_conv) 
qed

subsection\<open>Matching Terms\<close>

text\<open>The goal is showing that @{term "match (t \<cdot> \<sigma>) t = Some \<sigma>"} whenever the domain of @{term \<sigma>} is a subset of the variables in @{term t}.
For that we need some helper lemmas.\<close>

lemma decompose_fst:
  assumes "decompose (Fun f ss) t = Some us"
  shows "map fst us = ss"
proof-
  from assms obtain ts where t:"t = Fun f ts" 
     by (metis (no_types, lifting) decompose_def option.distinct(1) decompose_Some is_FunE old.prod.case term.case_eq_if)
  with assms have "length ss = length ts"
    by blast 
  with assms(1) t show ?thesis
    by auto 
qed

lemma decompose_vars_term:
  assumes "decompose (Fun f ss) t = Some us"
  shows "vars_term (Fun f ss) = (\<Union>(a, b) \<in> set us. vars_term a)"
proof-
  have "vars_term (Fun f ss) = (\<Union> s \<in> set ss. vars_term s)"
    by (meson Term.term.simps(18))
  also have "... = (\<Union> s \<in> set (map fst us). vars_term s)"
    using assms decompose_fst by metis 
  finally show ?thesis
    using image_image by auto 
qed

lemma match_term_list_domain:
  assumes "match_term_list P \<sigma> = Some \<tau>"
  shows "\<forall>x. x \<notin> (\<Union> (a, b) \<in> set P. vars_term a) \<and> \<sigma> x = None  \<longrightarrow> \<tau> x = None"
  using assms proof(induct P \<sigma> rule:match_term_list.induct)
  case (2 x t P \<sigma>)
  then show ?case
    by (metis (mono_tags, lifting) Sup_insert Un_iff case_prod_conv fun_upd_idem_iff fun_upd_triv fun_upd_twist image_insert list.simps(15) match_term_list.simps(2) option.simps(3) term.set_intros(3))
next
  case (3 f ss g ts P \<sigma>)
  from 3(2) obtain us where us:"decompose (Fun f ss) (Fun g ts) = Some us"
    using  match_term_list.simps(3) option.distinct(1) option.simps(4) by fastforce
  with 3(2) have *:"match_term_list (us @ P) \<sigma> = Some \<tau>" 
    by auto
  from us have "(\<Union> (a, b) \<in> set ((Fun f ss, Fun g ts) # P). vars_term a) = (\<Union> s \<in> set ss. vars_term s) \<union> (\<Union> (a, b) \<in> set P. vars_term a)"
    by simp
  also have "... = (\<Union> (a, b) \<in> set (us@P). vars_term a)" 
    using us by (metis (mono_tags, lifting) Term.term.simps(18) UN_Un decompose_vars_term set_append)
  finally show ?case 
    using  3(1) us * by metis
qed simp_all

lemma match_subst_domain:
  assumes "match a b = Some \<sigma>"
  shows "subst_domain \<sigma> \<subseteq> vars_term b"
proof-
  from assms have "\<forall>x. x \<notin> vars_term b \<longrightarrow> \<sigma> x = Var x"
    unfolding match_def match_list_def subst_of_map_def using match_term_list_domain by fastforce
  then show ?thesis
    using subst_domain_def by fastforce 
qed

lemma match_trivial: 
  assumes "subst_domain \<sigma> \<subseteq> vars_term t"
  shows "match (t \<cdot> \<sigma>) t = Some \<sigma>"
proof-
  obtain \<tau> where tau:"match (t \<cdot> \<sigma>) t = Some \<tau>" and 1:"(\<forall>x\<in>vars_term t. \<sigma> x = \<tau> x)"
    by (meson match_complete') 
  from assms have 2:"\<forall>x. x \<notin> vars_term t \<longrightarrow> \<sigma> x = Var x"
    by (meson notin_subst_domain_imp_Var subset_eq)
  from tau have 3:"\<forall>x. x \<notin> vars_term t \<longrightarrow> \<tau> x = Var x" 
    using match_subst_domain notin_subst_domain_imp_Var by fastforce  
  from 1 2 3 show ?thesis
    by (metis subst_term_eqI tau term_subst_eq)
qed

end