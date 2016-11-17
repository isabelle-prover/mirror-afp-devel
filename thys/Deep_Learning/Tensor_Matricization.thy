(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor Matricization\<close>

theory Tensor_Matricization
imports Tensor_Plus
"../Jordan_Normal_Form/Matrix" DL_Missing_Sublist
begin

(*TODO extract the theory of digit encoding and/or sublist weaving*)
fun digit_decode :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
"digit_decode [] [] = 0" |
"digit_decode (d # ds) (i # is) = i + d * digit_decode ds is"

fun digit_encode :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"digit_encode [] a = []" |
"digit_encode (d # ds) a = a mod d # digit_encode ds (a div d)"

lemma digit_encode_decode[simp]:
assumes "is \<lhd> ds"
shows "digit_encode ds (digit_decode ds is) = is"
  using assms apply (induction rule:valid_index.induct)
  unfolding digit_decode.simps digit_encode.simps
  by simp_all

lemma digit_decode_encode[simp]:
shows "digit_decode ds (digit_encode ds a) = a mod (prod_list ds)"
by (induction ds arbitrary:a; simp add: Divides.mod_mult2_eq add.commute)

lemma digit_decode_encode_lt[simp]:
assumes "a < prod_list ds"
shows "digit_decode ds (digit_encode ds a) = a"
by (simp add: assms)

lemma digit_decode_lt:
assumes "is \<lhd> ds"
shows "digit_decode ds is < prod_list ds"
using assms proof (induction rule:valid_index.induct)
  case Nil
  then show ?case by simp
next
  case (Cons "is" ds i d)
  have "(i + d * digit_decode ds is) div (d * prod_list ds) = 0"
    using Cons.IH Cons.hyps(2) Divides.div_mult2_eq by force
  then show ?case unfolding digit_decode.simps prod_list.Cons 
    by (metis (no_types) Cons.IH Cons.hyps(2) div_eq_0_iff mult_eq_0_iff not_less0)
qed

lemma digit_encode_valid_index:
assumes "a < prod_list ds"
shows "digit_encode ds a \<lhd> ds"
using assms proof (induction ds arbitrary:a) 
  case Nil
  show ?case by (simp add: valid_index.Nil)
next
  case (Cons d ds a)
  then show ?case
    unfolding digit_encode.simps using Cons
    by (metis Divides.div_mult2_eq div_eq_0_iff gr_implies_not0 prod_list.Cons mod_div_trivial 
     mult_not_zero valid_index.Cons)
qed

lemma length_digit_encode:
shows "length (digit_encode ds a) = length ds"
  by (induction ds arbitrary:a; simp_all) 

lemma digit_encode_0:
"prod_list ds dvd a \<Longrightarrow> digit_encode ds a = replicate (length ds) 0"
proof (induction ds arbitrary:a)
  case Nil
  then show ?case by simp
next
  case (Cons d ds a)
  then have "prod_list ds dvd (a div d)" unfolding prod_list.Cons 
    by (metis dvd_0_right dvd_div_iff_mult dvd_mult_left mult.commute split_div)
  then show ?case unfolding digit_encode.simps length_Cons replicate_Suc prod_list.Cons using Cons 
    using dvd_imp_mod_0 dvd_mult_left prod_list.Cons by force
qed

definition weave :: "nat set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"weave A xs ys = map (\<lambda>i. if i\<in>A then xs!(card {a\<in>A. a<i}) else ys!(card {a\<in>-A. a<i})) [0..<length xs + length ys]"

lemma length_weave:
shows "length (weave A xs ys) = length xs + length ys"
unfolding weave_def length_map by simp

lemma nth_weave:
assumes "i < length (weave A xs ys)"
shows "weave A xs ys ! i = (if i\<in>A then xs!(card {a\<in>A. a<i}) else ys!(card {a\<in>-A. a<i}))"
proof -
  have "i < length xs + length ys" using length_weave using assms by metis
  then have "i < length [0..<length xs + length ys]" by auto
  then have "[0..<length xs + length ys] ! i = i" 
    by (metis \<open>i < length xs + length ys\<close> add.left_neutral nth_upt)
  then show ?thesis      
    unfolding weave_def nth_map[OF `i < length [0..<length xs + length ys]`] by presburger
qed

lemma weave_append1:
assumes "length xs + length ys \<in> A"
assumes "length xs = card {a\<in>A. a < length xs + length ys}"
shows "weave A (xs @ [x]) ys = weave A xs ys @ [x]"
proof (rule nth_equalityI)
  show "length (weave A (xs @ [x]) ys) = length (weave A xs ys @ [x])"
    unfolding weave_def length_map by simp
  show "\<forall>i<length (weave A (xs @ [x]) ys). weave A (xs @ [x]) ys ! i = (weave A xs ys @ [x]) ! i"
  proof (rule allI, rule impI)
    fix i assume "i < length (weave A (xs @ [x]) ys)"
    show "weave A (xs @ [x]) ys ! i = (weave A xs ys @ [x]) ! i"
    proof (cases "i = length xs + length ys")
      case True
      then have "(weave A xs ys @ [x]) ! i = x" using length_weave by (metis nth_append_length)
      have "card {a \<in> A. a < i} = length xs" using assms(2) True by auto
      then show ?thesis unfolding nth_weave[OF `i < length (weave A (xs @ [x]) ys)`] 
        `(weave A xs ys @ [x]) ! i = x` using True assms(1) by simp
    next
      case False
      have "i < length (weave A xs ys)" using \<open>i < length (weave A (xs @ [x]) ys)\<close> 
        \<open>length (weave A (xs @ [x]) ys) = length (weave A xs ys @ [x])\<close> length_append_singleton 
        length_weave less_antisym False by fastforce
      then have "(weave A xs ys @ [x]) ! i = (weave A xs ys) ! i" by (simp add: nth_append)
      {
        assume "i\<in>A" 
        have  "i<length xs + length ys" by (metis \<open>i < length (weave A xs ys)\<close> length_weave)
        then have "{a \<in> A. a < i} \<subset> {a\<in>A. a < length xs + length ys}" 
          using assms(1) `i<length xs + length ys` `i\<in>A` by auto
        then have "card {a \<in> A. a < i} < card {a\<in>A. a < length xs + length ys}"
          using psubset_card_mono[of "{a\<in>A. a < length xs + length ys}" "{a \<in> A. a < i}"]  by simp
        then have "(xs @ [x]) ! card {a \<in> A. a < i} = xs ! card {a \<in> A. a < i}" 
        by (metis (no_types, lifting)  assms(2) nth_append)
      }
      then show ?thesis unfolding nth_weave[OF `i < length (weave A (xs @ [x]) ys)`]
        `(weave A xs ys @ [x]) ! i = (weave A xs ys) ! i` nth_weave[OF `i < length (weave A xs ys)`] 
        by simp
    qed
  qed
qed

lemma weave_append2:
assumes "length xs + length ys \<notin> A"
assumes "length ys = card {a\<in>-A. a < length xs + length ys}"
shows "weave A xs (ys @ [y]) = weave A xs ys @ [y]"
proof (rule nth_equalityI)
  show "length (weave A xs (ys @ [y])) = length (weave A xs ys @ [y])"
    unfolding weave_def length_map by simp
  show "\<forall>i<length (weave A xs (ys @ [y])). weave A xs (ys @ [y]) ! i = (weave A xs ys @ [y]) ! i"
  proof (rule allI, rule impI)
    fix i assume "i < length (weave A xs (ys @ [y]))"
    show "weave A xs (ys @ [y]) ! i = (weave A xs ys @ [y]) ! i"
    proof (cases "i = length xs + length ys")
      case True
      then have "(weave A xs ys @ [y]) ! i = y" using length_weave by (metis nth_append_length)
      have "card {a \<in> -A. a < i} = length ys" using assms(2) True by auto
      then show ?thesis unfolding nth_weave[OF `i < length (weave A xs (ys @ [y]))`] 
        `(weave A xs ys @ [y]) ! i = y` using True assms(1) by simp
    next
      case False
      have "i < length (weave A xs ys)" using \<open>i < length (weave A xs (ys @ [y]))\<close> 
        \<open>length (weave A xs (ys @ [y])) = length (weave A xs ys @ [y])\<close> length_append_singleton 
        length_weave less_antisym False by fastforce
      then have "(weave A xs ys @ [y]) ! i = (weave A xs ys) ! i" by (simp add: nth_append)
      {
        assume "i\<notin>A" 
        have  "i<length xs + length ys" by (metis \<open>i < length (weave A xs ys)\<close> length_weave)
        then have "{a \<in> -A. a < i} \<subset> {a\<in>-A. a < length xs + length ys}" 
          using assms(1) `i<length xs + length ys` `i\<notin>A` by auto
        then have "card {a \<in> -A. a < i} < card {a\<in>-A. a < length xs + length ys}"
          using psubset_card_mono[of "{a\<in>-A. a < length xs + length ys}" "{a \<in> -A. a < i}"]  by simp
        then have "(ys @ [y]) ! card {a \<in> -A. a < i} = ys ! card {a \<in> -A. a < i}" 
        by (metis (no_types, lifting)  assms(2) nth_append)
      }
      then show ?thesis unfolding nth_weave[OF `i < length (weave A xs (ys @ [y]))`]
        `(weave A xs ys @ [y]) ! i = (weave A xs ys) ! i` nth_weave[OF `i < length (weave A xs ys)`] 
        by simp
    qed
  qed
qed

(* TODO: verschieben *)
lemma valid_index_list_all2_iff: "is \<lhd> ds \<longleftrightarrow> list_all2 (op <) is ds" 
by (metis list_all2_conv_all_nth list_all2_nthD valid_indexI valid_index_length valid_index_lt)

lemma sublist_nth: 
assumes "n\<in>A" "n<length xs"
shows "sublist xs A ! (card {i. i<n \<and> i\<in>A}) = xs ! n"
using assms proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
  proof (cases "n = length xs")
    case True
    then show ?thesis unfolding sublist_append[of xs "[x]" A] nth_append 
      using length_sublist[of xs A] sublist_singleton snoc.prems(1) by auto
  next
    case False
    then have "n < length xs" using snoc by auto
    then have 0:"sublist xs A ! card {i. i < n \<and> i \<in> A} = xs ! n" using snoc by auto
    
    have "{i. i < n \<and> i \<in> A} \<subset> {i. i < length xs \<and> i \<in> A}" using `n < length xs` snoc by force
    then have "card {i. i < n \<and> i \<in> A} < length (sublist xs A)" unfolding length_sublist 
      by (simp add: psubset_card_mono)
    then show ?thesis unfolding sublist_append[of xs "[x]" A] nth_append using 0 
      by (simp add: \<open>n < length xs\<close>)
  qed
qed

lemma list_all2_sublist:
assumes "list_all2 P (sublist xs A) (sublist ys A)"
and     "list_all2 P (sublist xs (-A)) (sublist ys (-A))"
shows "list_all2 P xs ys"
proof -
  have "length xs = length ys"
  proof (rule ccontr; cases "length xs < length ys")
    case True
    then show False
    proof (cases "length xs \<in> A")
      case False
      have "{i. i < length xs \<and> i \<in> - A} \<subset> {i. i < length ys \<and> i \<in> - A}" 
        using False `length xs < length ys` by force
      then have "length (sublist ys (-A)) > length (sublist xs (-A))" 
        unfolding length_sublist by (simp add: psubset_card_mono)
      then show False using assms(2) list_all2_lengthD not_less_iff_gr_or_eq by blast
    next
      case True
      have "{i. i < length xs \<and> i \<in> A} \<subset> {i. i < length ys \<and> i \<in> A}" 
        using True `length xs < length ys` by force
      then have "length (sublist ys A) > length (sublist xs A)" 
        unfolding length_sublist by (simp add: psubset_card_mono)
      then show False using assms(1) list_all2_lengthD not_less_iff_gr_or_eq by blast
    qed
  next
    assume "length xs \<noteq> length ys"
    case False
    then have "length xs > length ys" using `length xs \<noteq> length ys` by auto
    then show False
    proof (cases "length ys \<in> A")
      case False
      have "{i. i < length ys \<and> i \<in> -A} \<subset> {i. i < length xs \<and> i \<in> -A}" 
        using False `length xs > length ys`  by force
      then have "length (sublist xs (-A)) > length (sublist ys (-A))" 
        unfolding length_sublist by (simp add: psubset_card_mono)
      then show False using assms(2) list_all2_lengthD dual_order.strict_implies_not_eq by blast
    next
      case True
      have "{i. i < length ys \<and> i \<in> A} \<subset> {i. i < length xs \<and> i \<in> A}" 
        using True `length xs > length ys` by force
      then have "length (sublist xs A) > length (sublist ys A)" 
        unfolding length_sublist by (simp add: psubset_card_mono)
      then show False using assms(1) list_all2_lengthD dual_order.strict_implies_not_eq by blast
    qed
  qed

  have "\<And>n. n < length xs \<Longrightarrow> P (xs ! n) (ys ! n)"
  proof -
    fix n assume "n < length xs"
    then have "n < length ys" using `length xs = length ys` by auto
    then show "P (xs ! n) (ys ! n)"
    proof (cases "n\<in>A")
      case True
      have "{i. i < n \<and> i \<in> A} \<subset> {i. i < length xs \<and> i \<in> A}" using `n < length xs` `n\<in>A` by force
      then have "card {i. i < n \<and> i \<in> A} < length (sublist xs A)" unfolding length_sublist 
        by (simp add: psubset_card_mono)
      show ?thesis using sublist_nth[OF `n\<in>A` `n < length xs`] sublist_nth[OF `n\<in>A` `n < length ys`]
        list_all2_nthD[OF assms(1), of "card {i. i < n \<and> i \<in> A}"] length_sublist 
        by (simp add: \<open>card {i. i < n \<and> i \<in> A} < length (sublist xs A)\<close>)
    next
      case False then have "n\<in>-A" by auto
      have "{i. i < n \<and> i \<in> -A} \<subset> {i. i < length xs \<and> i \<in> -A}" using `n < length xs` `n\<in>-A` by force
      then have "card {i. i < n \<and> i \<in> -A} < length (sublist xs (-A))" unfolding length_sublist 
        by (simp add: psubset_card_mono)
      show ?thesis using sublist_nth[OF `n\<in>-A` `n < length xs`] sublist_nth[OF `n\<in>-A` `n < length ys`]
        list_all2_nthD[OF assms(2), of "card {i. i < n \<and> i \<in> -A}"] length_sublist 
        using \<open>card {i. i < n \<and> i \<in> - A} < length (sublist xs (- A))\<close> by auto   next
    qed
  qed
  then show ?thesis using \<open>length xs = length ys\<close> list_all2_all_nthI by blast
qed

 (* TODO: Is there a general induction principle for sublists? *)
 (* TODO: How to avoid the copy & paste above? *)


lemma sublist_weave: 
assumes "length xs = card {a\<in>A. a < length xs + length ys}"
assumes "length ys = card {a\<in>(-A). a < length xs + length ys}"
shows "sublist (weave A xs ys) A = xs \<and> sublist (weave A xs ys) (-A) = ys"
using assms proof (induction "length xs + length ys" arbitrary: xs ys)
  case 0
  then show ?case
    unfolding weave_def sublist_map by simp
next
  case (Suc l)
  then show ?case
  proof (cases "l\<in>A")
    case True
    then have "l\<in>{a \<in> A. a < length xs + length ys}" using Suc.hyps mem_Collect_eq zero_less_Suc by auto
    then have "length xs > 0" using Suc by fastforce
    then obtain xs' x where "xs = xs' @ [x]" by (metis append_butlast_last_id length_greater_0_conv)
    then have "l = length xs' + length ys" using Suc.hyps by simp
    have length_xs':"length xs' = card {a \<in> A. a < length xs' + length ys}"
    proof -
      have "{a \<in> A. a < length xs + length ys} = {a \<in> A. a < length xs' + length ys} \<union> {l}"
        using `xs = xs' @ [x]` `l\<in>{a \<in> A. a < length xs + length ys}` `l = length xs' + length ys` 
        by force 
      then have "card {a \<in> A. a < length xs + length ys} = card {a \<in> A. a < length xs' + length ys} + 1" 
        using `l = length xs' + length ys` by fastforce
      then show ?thesis by (metis One_nat_def Suc.prems(1) \<open>xs = xs' @ [x]\<close> add_right_imp_eq 
        length_Cons length_append list.size(3))
    qed
    have length_ys:"length ys = card {a \<in> - A. a < length xs' + length ys}"
    proof -
      have "l\<notin>{a \<in> - A. a < length xs + length ys}" using `l\<in>A` `l = length xs' + length ys` by blast
      have "{a \<in> -A. a < length xs + length ys} = {a \<in> -A. a < length xs' + length ys}"
        apply (rule subset_antisym)
        using  `l = length xs' + length ys` `Suc l = length xs + length ys` `l\<notin>{a \<in> - A. a < length xs + length ys}`
        apply (metis (no_types, lifting) Collect_mono less_Suc_eq mem_Collect_eq)
        using Collect_mono Suc.hyps(2) \<open>l = length xs' + length ys\<close> by auto
      then show ?thesis using Suc.prems(2) by auto
    qed
    have "length xs' + length ys \<in> A" using `l\<in>A` \<open>l = length xs' + length ys\<close> by blast

    then have "sublist (weave A xs ys) A = sublist (weave A xs' ys @ [x]) A" unfolding
       `xs = xs' @ [x]` using weave_append1[OF `length xs' + length ys \<in> A` length_xs'] by metis
    also have "... = sublist (weave A xs' ys) A @ sublist [x] {a. a + (length xs' + length ys) \<in> A}"
      using sublist_append length_weave by metis
    also have "... = sublist (weave A xs' ys) A @ [x]" 
      using sublist_singleton `length xs' + length ys \<in> A` by auto
    also have "... = xs" using Suc.hyps(1)[OF `l = length xs' + length ys` length_xs' length_ys]
     `xs = xs' @ [x]` by presburger
    finally have "sublist (weave A xs ys) A = xs" by metis

    have "sublist (weave A xs ys) (-A) = sublist (weave A xs' ys @ [x]) (-A)" unfolding
       `xs = xs' @ [x]` using weave_append1[OF `length xs' + length ys \<in> A` length_xs'] by metis
    also have "... = sublist (weave A xs' ys) (-A) @ sublist [x] {a. a + (length xs' + length ys) \<in> (-A)}"
      using sublist_append length_weave by metis
    also have "... = sublist (weave A xs' ys) (-A)" 
      using sublist_singleton `length xs' + length ys \<in> A` by auto
    also have "... = ys" 
      using Suc.hyps(1)[OF `l = length xs' + length ys` length_xs' length_ys] by presburger
    finally show ?thesis using `sublist (weave A xs ys) A = xs` by auto
  next
    case False
    then have "l\<notin>{a \<in> A. a < length xs + length ys}" using Suc.hyps mem_Collect_eq zero_less_Suc by auto
    then have "length ys > 0" using Suc by fastforce
    then obtain ys' y where "ys = ys' @ [y]" by (metis append_butlast_last_id length_greater_0_conv)
    then have "l = length xs + length ys'" using Suc.hyps by simp
    have length_ys':"length ys' = card {a \<in> -A. a < length xs + length ys'}"
    proof -
      have "{a \<in> -A. a < length xs + length ys} = {a \<in> -A. a < length xs + length ys'} \<union> {l}"
        using `ys = ys' @ [y]` `l\<notin>{a \<in> A. a < length xs + length ys}` `l = length xs + length ys'` 
        by force 
      then have "card {a \<in> -A. a < length xs + length ys} = card {a \<in> -A. a < length xs + length ys'} + 1" 
        using `l = length xs + length ys'` by fastforce
      then show ?thesis by (metis One_nat_def Suc.prems(2) \<open>ys = ys' @ [y]\<close> add_right_imp_eq 
        length_Cons length_append list.size(3))
    qed
    have length_xs:"length xs = card {a \<in> A. a < length xs + length ys'}"
    proof -
      have "l\<notin>{a \<in> A. a < length xs + length ys}" using `l\<notin>A` `l = length xs + length ys'` by blast
      have "{a \<in> A. a < length xs + length ys} = {a \<in> A. a < length xs + length ys'}"
        apply (rule subset_antisym)
        using  `l = length xs + length ys'` `Suc l = length xs + length ys` `l\<notin>{a \<in> A. a < length xs + length ys}`
        apply (metis (no_types, lifting) Collect_mono less_Suc_eq mem_Collect_eq)
        using Collect_mono Suc.hyps(2) \<open>l = length xs + length ys'\<close> by auto
      then show ?thesis using Suc.prems(1) by auto
    qed
    have "length xs + length ys' \<notin> A" using `l\<notin>A` \<open>l = length xs + length ys'\<close> by blast

    then have "sublist (weave A xs ys) A = sublist (weave A xs ys' @ [y]) A" unfolding
       `ys = ys' @ [y]` using weave_append2[OF `length xs + length ys' \<notin> A` length_ys'] by metis
    also have "... = sublist (weave A xs ys') A @ sublist [y] {a. a + (length xs + length ys') \<in> A}"
      using sublist_append length_weave by metis
    also have "... = sublist (weave A xs ys') A" 
      using sublist_singleton `length xs + length ys' \<notin> A` by auto
    also have "... = xs" 
      using Suc.hyps(1)[OF `l = length xs + length ys'` length_xs length_ys'] by auto
    finally have "sublist (weave A xs ys) A = xs" by auto

    have "sublist (weave A xs ys) (-A) = sublist (weave A xs ys' @ [y]) (-A)" unfolding
       `ys = ys' @ [y]` using weave_append2[OF `length xs + length ys' \<notin> A` length_ys'] by metis
    also have "... = sublist (weave A xs ys') (-A) @ sublist [y] {a. a + (length xs + length ys') \<in> (-A)}"
      using sublist_append length_weave by metis
    also have "... = sublist (weave A xs ys') (-A) @ [y]" 
      using sublist_singleton `length xs + length ys' \<notin> A` by auto
    also have "... = ys" 
      using Suc.hyps(1)[OF `l = length xs + length ys'` length_xs length_ys'] `ys = ys' @ [y]` by simp
    finally show ?thesis using `sublist (weave A xs ys) A = xs` by auto
  qed
qed

lemma set_weave:
assumes "length xs = card {a\<in>A. a < length xs + length ys}"
assumes "length ys = card {a\<in>-A. a < length xs + length ys}"
shows "set (weave A xs ys) = set xs \<union> set ys"
proof
  show "set (weave A xs ys) \<subseteq> set xs \<union> set ys"
  proof
    fix x assume "x\<in>set (weave A xs ys)"
    then obtain i where "weave A xs ys ! i = x" "i<length (weave A xs ys)" by (meson in_set_conv_nth)
    show "x \<in> set xs \<union> set ys" 
    proof (cases "i\<in>A")
      case True
      then have "i \<in> {a\<in>A. a < length xs + length ys}" unfolding length_weave 
        by (metis \<open>i < length (weave A xs ys)\<close> length_weave mem_Collect_eq)
      then have "{a \<in> A. a < i} \<subset> {a\<in>A. a < length xs + length ys}"
        using Collect_mono \<open>i < length (weave A xs ys)\<close>[unfolded length_weave] le_Suc_ex  less_imp_le_nat trans_less_add1
        le_neq_trans less_irrefl mem_Collect_eq by auto
      then have "card {a \<in> A. a < i} < card {a\<in>A. a < length xs + length ys}" by (simp add: psubset_card_mono)
      then show "x \<in> set xs \<union> set ys"
        unfolding nth_weave[OF `i<length (weave A xs ys)`, unfolded `weave A xs ys ! i = x`] using True
        using UnI1 assms(1) nth_mem by auto
    next
      case False
      have "i\<notin>A \<Longrightarrow> i \<in> {a\<in>-A. a < length xs + length ys}" unfolding length_weave
        by (metis ComplI \<open>i < length (weave A xs ys)\<close> length_weave mem_Collect_eq)
      then have "{a \<in> -A. a < i} \<subset> {a\<in>-A. a < length xs + length ys}"
        using Collect_mono \<open>i < length (weave A xs ys)\<close>[unfolded length_weave] le_Suc_ex  less_imp_le_nat trans_less_add1
        le_neq_trans less_irrefl mem_Collect_eq using False by auto
      then have "card {a \<in> -A. a < i} < card {a\<in>-A. a < length xs + length ys}" by (simp add: psubset_card_mono)
      then show "x \<in> set xs \<union> set ys"
        unfolding nth_weave[OF `i<length (weave A xs ys)`, unfolded `weave A xs ys ! i = x`] using False
        using UnI1 assms(2) nth_mem by auto
    qed
  qed
  show "set xs \<union> set ys \<subseteq> set (weave A xs ys)" 
    using sublist_weave[OF assms] by (metis Un_subset_iff set_sublist_subset)
qed


lemma weave_complementary_sublists[simp]:
 "weave A (sublist xs A) (sublist xs (-A)) = xs"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by (metis gen_length_def length_0_conv length_code length_weave sublist_nil)
next
  case (snoc x xs)
  have length_xs:"length xs = length (sublist xs A) + length (sublist xs (-A))" by (metis length_weave snoc.IH)
  show ?case
  proof (cases "(length xs)\<in>A")
    case True 
    have 0:"length (sublist xs A) + length (sublist xs (-A)) \<in> A" using length_xs True by metis
    have 1:"length (sublist xs A) = card {a \<in> A. a < length (sublist xs A) + length (sublist xs (-A))}" 
      using length_sublist[of xs A] by (metis (no_types, lifting) Collect_cong length_xs)
    have 2:"sublist (xs @ [x]) A = sublist xs A @ [x]"
      unfolding sublist_append[of xs "[x]" A] using sublist_singleton True by auto
    have 3:"sublist (xs @ [x]) (-A) = sublist xs (-A)"
      unfolding sublist_append[of xs "[x]" "-A"] using True by auto
    show ?thesis unfolding 2 3 weave_append1[OF 0 1] snoc.IH by metis
  next
    case False
    have 0:"length (sublist xs A) + length (sublist xs (-A)) \<notin> A" using length_xs False by metis
    have 1:"length (sublist xs (-A)) = card {a \<in> -A. a < length (sublist xs A) + length (sublist xs (-A))}" 
      using length_sublist[of xs "-A"] by (metis (no_types, lifting) Collect_cong length_xs)
    have 2:"sublist (xs @ [x]) A = sublist xs A"
      unfolding sublist_append[of xs "[x]" A] using sublist_singleton False by auto
    have 3:"sublist (xs @ [x]) (-A) = sublist xs (-A) @ [x]"
      unfolding sublist_append[of xs "[x]" "-A"] using False by auto
    show ?thesis unfolding 2 3 weave_append2[OF 0 1] snoc.IH by metis
  qed
qed

lemma length_sublist':
"length (sublist xs I) = card {i\<in>I. i < length xs}"
unfolding length_sublist by meson

lemma valid_index_weave:
assumes "is1 \<lhd> (sublist ds A)"
and     "is2 \<lhd> (sublist ds (-A))"
shows "weave A is1 is2 \<lhd> ds"
and "sublist (weave A is1 is2) A = is1"
and "sublist (weave A is1 is2) (-A) = is2"
proof -
  have length_ds: "length is1 + length is2 = length ds" 
    using valid_index_length[OF assms(1)] valid_index_length[OF assms(2)]
    length_weave  weave_complementary_sublists by metis
  have 1:"length is1 = card {i \<in> A. i < length is1 + length is2}" unfolding length_ds
    using length_sublist' assms(1) valid_index_length by auto
  have 2:"length is2 = card {i \<in> -A. i < length is1 + length is2}" unfolding length_ds
    using length_sublist'[of ds "-A"] assms(2) valid_index_length by auto
  show "sublist (weave A is1 is2) A = is1" "sublist (weave A is1 is2) (-A) = is2" using sublist_weave[OF 1 2] by blast+
  then have "sublist (weave A is1 is2) A \<lhd> (sublist ds A)"
       "sublist (weave A is1 is2) (-A) \<lhd> (sublist ds (-A))" using assms by auto
  then show "weave A is1 is2 \<lhd> ds" using list_all2_sublist valid_index_list_all2_iff by blast
qed

definition matricize :: "nat set \<Rightarrow> 'a tensor \<Rightarrow> 'a mat" where
"matricize rmodes T = mat
  (prod_list (sublist (Tensor.dims T) rmodes))
  (prod_list (sublist (Tensor.dims T) (-rmodes)))
  (\<lambda>(r, c). Tensor.lookup T (weave rmodes 
    (digit_encode (sublist (Tensor.dims T) rmodes) r) 
    (digit_encode (sublist (Tensor.dims T) (-rmodes)) c)
  ))
"

definition dematricize::"nat set \<Rightarrow> 'a mat \<Rightarrow> nat list \<Rightarrow> 'a tensor" where
"dematricize rmodes A ds  = tensor_from_lookup ds
  (\<lambda>is. A $$ (digit_decode (sublist ds rmodes) (sublist is rmodes),
              digit_decode (sublist ds (-rmodes)) (sublist is (-rmodes)))
 )
"

lemma dims_matricize: 
"dim\<^sub>r (matricize rmodes T) = prod_list (sublist (Tensor.dims T) rmodes)"
"dim\<^sub>c (matricize rmodes T) = prod_list (sublist (Tensor.dims T) (-rmodes))"
  unfolding matricize_def using mat_dim_row_mat by simp_all

lemma dims_dematricize: "Tensor.dims (dematricize rmodes A ds) = ds"
  by (simp add: dematricize_def dims_tensor_from_lookup)

lemma valid_index_sublist:
assumes "is \<lhd> ds"
shows "sublist is A \<lhd> sublist ds A"
using assms proof (induction arbitrary:A rule:valid_index.induct)
  case Nil
  then show ?case using sublist_nil valid_index.simps by blast
next
  case (Cons "is" ds i d)
  then have " sublist is {j. Suc j \<in> A} \<lhd> sublist ds {j. Suc j \<in> A}"
    by simp
  then show ?case unfolding sublist_Cons
    by (cases "0\<in>A"; simp_all add: Cons.hyps(2) valid_index.Cons)
qed

lemma dematricize_matricize:
shows "dematricize rmodes (matricize rmodes T) (Tensor.dims T) = T"
proof (rule tensor_lookup_eqI)
  show 1:"Tensor.dims (dematricize rmodes (matricize rmodes T) (Tensor.dims T)) = Tensor.dims T"
    by (simp add: dematricize_def dims_tensor_from_lookup)
  fix "is" assume "is \<lhd> Tensor.dims (dematricize rmodes (matricize rmodes T) (Tensor.dims T))"
  then have "is \<lhd> Tensor.dims T" using 1 by auto
  let ?rds = "(sublist (Tensor.dims T) rmodes)"
  let ?cds = "(sublist (Tensor.dims T) (-rmodes))"
  have decode_r: "digit_decode ?rds (sublist is rmodes) < prod_list ?rds" 
    by (simp add: \<open>is \<lhd> Tensor.dims T\<close> valid_index_sublist digit_decode_lt)
  have decode_c: "digit_decode ?cds (sublist is (-rmodes)) < prod_list ?cds" 
    by (simp add: \<open>is \<lhd> Tensor.dims T\<close> valid_index_sublist digit_decode_lt)
  have "(matricize rmodes T) $$
     (digit_decode ?rds (sublist is rmodes),
      digit_decode ?cds (sublist is (- rmodes))) =
    Tensor.lookup T is"
    unfolding matricize_def 
    by (simp add: decode_r decode_c \<open>is \<lhd> Tensor.dims T\<close> valid_index_sublist)
  then show "Tensor.lookup (dematricize rmodes (matricize rmodes T) (Tensor.dims T)) is = Tensor.lookup T is"
    by (simp add: dematricize_def dims_tensor_from_lookup lookup_tensor_from_lookup[OF `is \<lhd> Tensor.dims T`])
qed

lemma matricize_dematricize:
assumes " dim\<^sub>r A = prod_list (sublist ds rmodes)"
and " dim\<^sub>c A = prod_list (sublist ds (-rmodes))"
shows "matricize rmodes (dematricize rmodes A ds) = A"
proof (rule mat_eqI)
  show "dim\<^sub>r (matricize rmodes (dematricize rmodes A ds)) = dim\<^sub>r A" 
    unfolding assms(1) dematricize_def dims_tensor_from_lookup matricize_def mat_dim_row_mat by metis
  show "dim\<^sub>c (matricize rmodes (dematricize rmodes A ds)) = dim\<^sub>c A" 
    unfolding assms(2) dematricize_def dims_tensor_from_lookup matricize_def mat_dim_col_mat by metis
  fix r c assume "r < dim\<^sub>r A" "c < dim\<^sub>c A"
  have valid1:"digit_encode (sublist ds rmodes) r \<lhd> sublist ds rmodes" and
       valid2:"digit_encode (sublist ds (- rmodes)) c \<lhd> sublist ds (- rmodes)" 
    using \<open>r < dim\<^sub>r A\<close> assms(1) \<open>c < dim\<^sub>c A\<close> assms(2) digit_encode_valid_index by auto
  have 0:"Tensor.lookup (dematricize rmodes A ds)
     (weave rmodes 
       (digit_encode (sublist (Tensor.dims (dematricize rmodes A ds)) rmodes) r)
       (digit_encode (sublist (Tensor.dims (dematricize rmodes A ds)) (- rmodes)) c)
     ) =  A $$ (r, c)"
      unfolding dematricize_def unfolding dims_tensor_from_lookup
      unfolding lookup_tensor_from_lookup[OF valid_index_weave(1)[OF valid1 valid2]]
      using digit_decode_encode_lt[OF \<open>c < dim\<^sub>c A\<close>[unfolded assms(2)]] 
      digit_decode_encode_lt[OF \<open>r < dim\<^sub>r A\<close>[unfolded assms(1)]]  
      valid_index_weave(2)[OF valid1 valid2] valid_index_weave(3)[OF valid1 valid2]
      by presburger  
  from `r < dim\<^sub>r A` have r_le: "r < prod_list (sublist (Tensor.dims (dematricize rmodes A ds)) rmodes)" 
    by (metis \<open>dim\<^sub>r (matricize rmodes (dematricize rmodes A ds)) = dim\<^sub>r A\<close> matricize_def mat_dim_row_mat(1))
  from `c < dim\<^sub>c A `have c_le: "c < prod_list (sublist (Tensor.dims (dematricize rmodes A ds)) (- rmodes))"
    by (metis \<open>dim\<^sub>c (matricize rmodes (dematricize rmodes A ds)) = dim\<^sub>c A\<close> matricize_def mat_dim_col_mat(1))
  then show "(matricize rmodes (dematricize rmodes A ds)) $$ (r, c) = A $$ (r, c)"
    unfolding matricize_def using r_le c_le 0 by simp
qed

lemma matricize_add:
assumes "dims A = dims B"
shows "matricize I A \<oplus>\<^sub>m matricize I B = matricize I (A+B)"
proof (rule mat_eqI)
  show "dim\<^sub>r (matricize I A \<oplus>\<^sub>m matricize I B) = dim\<^sub>r (matricize I (A + B))" by (simp add: assms dims_matricize(1))
  show "dim\<^sub>c (matricize I A \<oplus>\<^sub>m matricize I B) = dim\<^sub>c (matricize I (A + B))" by (simp add: assms dims_matricize(2))
  fix i j assume ij_le1:"i < dim\<^sub>r (matricize I (A + B))" "j < dim\<^sub>c (matricize I (A + B))"
  then have 
    ij_le2:"i < prod_list (sublist (Tensor.dims A) I)"  "j < prod_list (sublist (Tensor.dims A) (-I))" and
    ij_le3:"i < prod_list (sublist (Tensor.dims B) I)"  "j < prod_list (sublist (Tensor.dims B) (-I))" and
    ij_le4:"i < prod_list (sublist (Tensor.dims (A + B)) I)"  "j < prod_list (sublist (Tensor.dims (A + B)) (-I))" 
    by (simp_all add: assms dims_matricize)
  then have ij_le5:"i < dim\<^sub>r (matricize I B)" "j < dim\<^sub>c (matricize I B)" 
    by (simp_all add: assms dims_matricize)
  show "(matricize I A \<oplus>\<^sub>m matricize I B) $$ (i, j) = matricize I (A + B) $$ (i, j)"
    unfolding mat_index_add(1)[OF ij_le5] unfolding matricize_def unfolding mat_index_mat[OF ij_le2] mat_index_mat[OF ij_le3] mat_index_mat[OF ij_le4]
    using assms digit_encode_valid_index ij_le2(1) ij_le2(2) valid_index_weave(1) by auto
qed

lemma matricize_0:
shows "matricize I (tensor0 ds) = \<zero>\<^sub>m (dim\<^sub>r (matricize I (tensor0 ds))) (dim\<^sub>c (matricize I (tensor0 ds)))"
proof (rule mat_eqI)
  show "dim\<^sub>r (matricize I (tensor0 ds)) = dim\<^sub>r (\<zero>\<^sub>m (dim\<^sub>r (matricize I (tensor0 ds))) (dim\<^sub>c (matricize I (tensor0 ds))))" 
    unfolding mat_zero_def mat_dim_row_mat by (simp add: dims_matricize(1))
  show "dim\<^sub>c (matricize I (tensor0 ds)) = dim\<^sub>c (\<zero>\<^sub>m (dim\<^sub>r (matricize I (tensor0 ds))) (dim\<^sub>c (matricize I (tensor0 ds))))" 
    unfolding mat_zero_def mat_dim_row_mat by (simp add: dims_matricize(2))
  fix i j assume ij_le1: "i < dim\<^sub>r (\<zero>\<^sub>m (dim\<^sub>r (matricize I (tensor0 ds))) (dim\<^sub>c (matricize I (tensor0 ds))))"
                 "j < dim\<^sub>c (\<zero>\<^sub>m (dim\<^sub>r (matricize I (tensor0 ds))) (dim\<^sub>c (matricize I (tensor0 ds))))"
  then have ij_le2:"i < dim\<^sub>r (matricize I (tensor0 ds))" "j < dim\<^sub>c (matricize I (tensor0 ds))"
    unfolding mat_zero_def mat_dim_row_mat by (simp_all add: dims_matricize)
  show "matricize I (tensor0 ds) $$ (i, j) = \<zero>\<^sub>m (dim\<^sub>r (matricize I (tensor0 ds))) (dim\<^sub>c (matricize I (tensor0 ds))) $$ (i, j)"
    unfolding mat_zero_def  mat_index_mat[OF ij_le2] unfolding matricize_def mat_index_mat[OF ij_le2[unfolded dims_matricize]] 
    by (simp, metis lookup_tensor0 digit_encode_valid_index dims_matricize(1) dims_matricize(2) dims_tensor0 
    ij_le2(1) ij_le2(2) valid_index_weave(1))
qed

end
