section \<open>Multiset extension of order pairs in the other direction\<close>

text \<open>Many term orders are formulated in the other direction, i.e., they use
  strong normalization of $>$ instead of well-foundedness of $<$. Here, we
  flip the direction of the multiset extension of two orders, connect it to existing interfaces,
  and prove some further properties of the multiset extension.\<close>

theory Multiset_Extension2
  imports
    List_Order
    Multiset_Extension_Pair
begin

subsection \<open>List based characterization of @{const multpw}\<close>

lemma multpw_listI:
  assumes "length xs = length ys" "X = mset xs" "Y = mset ys"
    "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns"
  shows "(X, Y) \<in> multpw ns"
  using assms
proof (induct xs arbitrary: ys X Y)
  case (Nil ys) then show ?case by (cases ys) (auto intro: multpw.intros)
next
  case Cons1: (Cons x xs ys' X Y) then show ?case
  proof (cases ys')
    case (Cons y ys)
    then have "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns" using Cons1(5) by fastforce
    then show ?thesis using Cons1(2,5) by (auto intro!: multpw.intros simp: Cons(1) Cons1)
  qed auto
qed

lemma multpw_listE:
  assumes "(X, Y) \<in> multpw ns"
  obtains xs ys where "length xs = length ys" "X = mset xs" "Y = mset ys"
    "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns"
  using assms
proof (induct X Y arbitrary: thesis rule: multpw.induct)
  case (add x y X Y)
  then obtain xs ys where "length xs = length ys" "X = mset xs"
    "Y = mset ys" "(\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns)" by blast
  then show ?case using add(1) by (intro add(4)[of "x # xs" "y # ys"]) (auto, case_tac i, auto)
qed auto

subsection\<open>Definition of the multiset extension of $>$-orders\<close>

text\<open>We define here the non-strict extension of the order pair $(\geqslant, >)$ --
  usually written as (ns, s) in the sources --
  by just flipping the directions twice.\<close>

definition ns_mul_ext :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel"
  where "ns_mul_ext ns s \<equiv> (mult2_alt_ns (ns\<inverse>) (s\<inverse>))\<inverse>"

lemma ns_mul_extI:
  assumes "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  shows "(A, B) \<in> ns_mul_ext ns s"
  using assms by (auto simp: ns_mul_ext_def multpw_converse intro!: mult2_alt_nsI)

lemma ns_mul_extE:
  assumes "(A, B) \<in> ns_mul_ext ns s"
  obtains A1 A2 B1 B2 where "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  using assms by (auto simp: ns_mul_ext_def multpw_converse elim!: mult2_alt_nsE)

lemmas ns_mul_extI_old = ns_mul_extI[OF _ _ multpw_listI[OF _ refl refl], rule_format]

text\<open>Same for the "greater than" order on multisets.\<close>

definition s_mul_ext :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel"
  where "s_mul_ext ns s \<equiv> (mult2_alt_s (ns\<inverse>) (s\<inverse>))\<inverse>"

lemma s_mul_extI:
  assumes "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "A2 \<noteq> {#}" and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  shows "(A, B) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def multpw_converse intro!: mult2_alt_sI)

lemma s_mul_extE:
  assumes "(A, B) \<in> s_mul_ext ns s"
  obtains A1 A2 B1 B2 where "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "A2 \<noteq> {#}" and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  using assms by (auto simp: s_mul_ext_def multpw_converse elim!: mult2_alt_sE)

lemmas s_mul_extI_old = s_mul_extI[OF _ _ multpw_listI[OF _ refl refl], rule_format]


subsection\<open>Basic properties\<close>

lemma s_mul_ext_mono:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "s_mul_ext ns s \<subseteq> s_mul_ext ns' s'"
  unfolding s_mul_ext_def using assms mono_mult2_alt[of "ns\<inverse>" "ns'\<inverse>" "s\<inverse>" "s'\<inverse>"] by simp

lemma ns_mul_ext_mono:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "ns_mul_ext ns s \<subseteq> ns_mul_ext ns' s'"
  unfolding ns_mul_ext_def using assms mono_mult2_alt[of "ns\<inverse>" "ns'\<inverse>" "s\<inverse>" "s'\<inverse>"] by simp

lemma s_mul_ext_local_mono:
  assumes sub: "(set_mset xs \<times> set_mset ys) \<inter> ns \<subseteq> ns'" "(set_mset xs \<times> set_mset ys) \<inter> s \<subseteq> s'"
    and rel: "(xs,ys) \<in> s_mul_ext ns s"
  shows "(xs,ys) \<in> s_mul_ext ns' s'"
  using rel s_mul_ext_mono[OF sub] mult2_alt_local[of ys xs False "ns\<inverse>" "s\<inverse>"]
  by (auto simp: s_mul_ext_def converse_Int ac_simps converse_Times)

lemma ns_mul_ext_local_mono:
  assumes sub: "(set_mset xs \<times> set_mset ys) \<inter> ns \<subseteq> ns'" "(set_mset xs \<times> set_mset ys) \<inter> s \<subseteq> s'"
    and rel: "(xs,ys) \<in> ns_mul_ext ns s"
  shows "(xs,ys) \<in> ns_mul_ext ns' s'"
  using rel ns_mul_ext_mono[OF sub] mult2_alt_local[of ys xs True "ns\<inverse>" "s\<inverse>"]
  by (auto simp: ns_mul_ext_def converse_Int ac_simps converse_Times)


text\<open>The empty multiset is the minimal element for these orders\<close>

lemma ns_mul_ext_bottom: "(A,{#}) \<in> ns_mul_ext ns s"
  by (auto intro!: ns_mul_extI)

lemma ns_mul_ext_bottom_uniqueness:
  assumes "({#},A) \<in> ns_mul_ext ns s"
  shows "A = {#}"
  using assms by (auto simp: ns_mul_ext_def mult2_alt_ns_def)

lemma ns_mul_ext_bottom2:
  assumes "(A,B) \<in> ns_mul_ext ns s"
    and "B \<noteq> {#}"
  shows "A \<noteq> {#}"
  using assms by (auto simp: ns_mul_ext_def mult2_alt_ns_def)

lemma s_mul_ext_bottom:
  assumes "A \<noteq> {#}"
  shows "(A,{#}) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def mult2_alt_s_def)

lemma s_mul_ext_bottom_strict:
  "({#},A) \<notin> s_mul_ext ns s"
  by (auto simp: s_mul_ext_def mult2_alt_s_def)

text\<open>Obvious introduction rules.\<close>

lemma all_ns_ns_mul_ext:
  assumes "length as = length bs"
    and "\<forall>i. i < length bs \<longrightarrow> (as ! i, bs ! i) \<in> ns"
  shows "(mset as, mset bs) \<in> ns_mul_ext ns s"
  using assms by (auto intro!: ns_mul_extI[of _ _ "{#}" _ _ "{#}"] multpw_listI)

lemma all_s_s_mul_ext:
  assumes "A \<noteq> {#}"
    and "\<forall>b. b \<in># B \<longrightarrow> (\<exists>a. a \<in># A \<and> (a,b) \<in> s)"
  shows "(A, B) \<in> s_mul_ext ns s"
  using assms by (auto intro!: s_mul_extI[of _ "{#}" _ _ "{#}"] multpw_listI)

text\<open>Being stricly lesser than implies being lesser than\<close>

lemma s_ns_mul_ext:
  assumes "(A, B) \<in> s_mul_ext ns s"
  shows "(A, B) \<in> ns_mul_ext ns s"
  using assms by (simp add: s_mul_ext_def ns_mul_ext_def mult2_alt_s_implies_mult2_alt_ns)

text\<open>The non-strict order is reflexive.\<close>

lemma multpw_refl':
  assumes "locally_refl ns A"
  shows "(A, A) \<in> multpw ns"
proof -
  have "Restr Id (set_mset A) \<subseteq> ns" using assms by (auto simp: locally_refl_def)
  from refl_multpw[of Id] multpw_local[of A A Id] mono_multpw[OF this]
  show ?thesis by (auto simp: refl_on_def)
qed

lemma ns_mul_ext_refl_local:
  assumes "locally_refl ns A"
  shows "(A, A) \<in> ns_mul_ext ns s"
  using assms by (auto intro!:  ns_mul_extI[of A A "{#}" A A "{#}" ns s] multpw_refl')

lemma ns_mul_ext_refl:
  assumes "refl ns"
  shows "(A, A) \<in> ns_mul_ext ns s"
  using assms ns_mul_ext_refl_local[of ns A s] unfolding refl_on_def locally_refl_def by auto

text\<open>The orders are union-compatible\<close>

lemma ns_s_mul_ext_union_multiset_l:
  assumes "(A, B) \<in> ns_mul_ext ns s"
    and "C \<noteq> {#}"
    and "\<forall>d. d \<in># D \<longrightarrow> (\<exists>c. c \<in># C \<and> (c,d) \<in> s)"
  shows "(A + C, B + D) \<in> s_mul_ext ns s"
  using assms unfolding ns_mul_ext_def s_mul_ext_def
  by (auto intro!: converseI mult2_alt_ns_s_add mult2_alt_sI[of _ "{#}" _ _ "{#}"])

lemma s_mul_ext_union_compat:
  assumes "(A, B) \<in> s_mul_ext ns s"
    and "locally_refl ns C"
  shows "(A + C, B + C) \<in> s_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(2)] unfolding ns_mul_ext_def s_mul_ext_def
  by (auto intro!: converseI mult2_alt_s_ns_add)

lemma ns_mul_ext_union_compat:
  assumes "(A, B) \<in> ns_mul_ext ns s"
    and "locally_refl ns C"
  shows "(A + C, B + C) \<in> ns_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(2)] unfolding ns_mul_ext_def s_mul_ext_def
  by (auto intro!: converseI mult2_alt_ns_ns_add)

context
  fixes NS :: "'a rel"
  assumes NS: "refl NS"
begin

lemma refl_imp_locally_refl: "locally_refl NS A" using NS unfolding refl_on_def locally_refl_def by auto

lemma supseteq_imp_ns_mul_ext:
  assumes "A \<supseteq># B"
  shows "(A, B) \<in> ns_mul_ext NS S"
  using assms
  by (auto intro!: ns_mul_extI[of A B "A - B" B B "{#}"] multpw_refl' refl_imp_locally_refl
      simp: subset_mset.add_diff_inverse)

lemma supset_imp_s_mul_ext:
  assumes "A \<supset># B"
  shows "(A, B) \<in> s_mul_ext NS S"
  using assms subset_mset.add_diff_inverse[of B A]
  by (auto intro!: s_mul_extI[of A B "A - B" B B "{#}"] multpw_refl' refl_imp_locally_refl
      simp: Diff_eq_empty_iff_mset)

end

definition mul_ext :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
  where "mul_ext f xs ys \<equiv> let s = {(x,y). fst (f x y)}; ns = {(x,y). snd (f x y)}
    in ((mset xs,mset ys) \<in> s_mul_ext ns s, (mset xs, mset ys) \<in> ns_mul_ext ns s)"

definition "smulextp f m n \<longleftrightarrow> (m, n) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
definition "nsmulextp f m n \<longleftrightarrow> (m, n) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"

lemma smulextp_cong[fundef_cong]:
  assumes "xs1 = ys1"
    and "xs2 = ys2"
    and "\<And> x x'. x \<in># ys1 \<Longrightarrow> x' \<in># ys2 \<Longrightarrow> f x x' = g x x'"
  shows "smulextp f xs1 xs2 = smulextp g ys1 ys2"
  unfolding smulextp_def
proof
  assume "(xs1, xs2) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
  from s_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (g x y)}" "{(x, y). fst (g x y)}"]
  show "(ys1, ys2) \<in> s_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
    using assms by force
next
  assume "(ys1, ys2) \<in> s_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
  from s_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (f x y)}" "{(x, y). fst (f x y)}"]
  show "(xs1, xs2) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
    using assms by force
qed

lemma nsmulextp_cong[fundef_cong]:
  assumes "xs1 = ys1"
    and "xs2 = ys2"
    and "\<And> x x'. x \<in># ys1 \<Longrightarrow> x' \<in># ys2 \<Longrightarrow> f x x' = g x x'"
  shows "nsmulextp f xs1 xs2 = nsmulextp g ys1 ys2"
  unfolding nsmulextp_def
proof
  assume "(xs1, xs2) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
  from ns_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (g x y)}" "{(x, y). fst (g x y)}"]
  show "(ys1, ys2) \<in> ns_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
    using assms by force
next
  assume "(ys1, ys2) \<in> ns_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
  from ns_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (f x y)}" "{(x, y). fst (f x y)}"]
  show "(xs1, xs2) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
    using assms by force
qed


definition "mulextp f m n = (smulextp f m n, nsmulextp f m n)"

lemma mulextp_cong[fundef_cong]:
  assumes "xs1 = ys1"
    and "xs2 = ys2"
    and "\<And> x x'. x \<in># ys1 \<Longrightarrow> x' \<in># ys2 \<Longrightarrow> f x x' = g x x'"
  shows "mulextp f xs1 xs2 = mulextp g ys1 ys2"
  unfolding mulextp_def using assms by (auto cong: nsmulextp_cong smulextp_cong)

lemma mset_s_mul_ext:
  "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y).fst (f x y)} \<longleftrightarrow>
    fst (mul_ext f xs ys)"
  by (auto simp: mul_ext_def Let_def)

lemma mset_ns_mul_ext:
  "(mset xs, mset ys) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y).fst (f x y)} \<longleftrightarrow>
    snd (mul_ext f xs ys)"
  by (auto simp: mul_ext_def Let_def)

lemma smulextp_mset_code:
  "smulextp f (mset xs) (mset ys) \<longleftrightarrow> fst (mul_ext f xs ys)"
  unfolding smulextp_def mset_s_mul_ext ..

lemma nsmulextp_mset_code:
  "nsmulextp f (mset xs) (mset ys) \<longleftrightarrow> snd (mul_ext f xs ys)"
  unfolding nsmulextp_def mset_ns_mul_ext ..

lemma nstri_mul_ext_map:
  assumes "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> fst (order' (f s) (f t))"
    and "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> snd (order' (f s) (f t))"
    and "snd (mul_ext order ss ts)"
  shows "snd (mul_ext order' (map f ss) (map f ts))"
  using assms mult2_alt_map[of "mset ts" "mset ss" "{(t, s). snd (order s t)}" f f
      "{(t, s). snd (order' s t)}" "{(t, s). fst (order s t)}" "{(t, s). fst (order' s t)}" True]
  by (auto simp: mul_ext_def ns_mul_ext_def converse_unfold)

lemma stri_mul_ext_map:
  assumes "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> fst (order' (f s) (f t))"
    and "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> snd (order' (f s) (f t))"
    and "fst (mul_ext order ss ts)"
  shows "fst (mul_ext order' (map f ss) (map f ts))"
  using assms mult2_alt_map[of "mset ts" "mset ss" "{(t,s). snd (order s t)}" f f
      "{(t, s). snd (order' s t)}" "{(t, s). fst (order s t)}" "{(t, s). fst (order' s t)}" False]
  by (auto simp: mul_ext_def s_mul_ext_def converse_unfold)


lemma mul_ext_arg_empty: "snd (mul_ext f [] xs) \<Longrightarrow> xs = []" 
  unfolding mul_ext_def Let_def by (auto simp: ns_mul_ext_def mult2_alt_def)


text \<open>The non-strict order is irreflexive\<close>
lemma s_mul_ext_irrefl: assumes irr: "irrefl_on (set_mset A) S" 
  and S_NS: "S \<subseteq> NS" 
  and compat: "S O NS \<subseteq> S" 
shows "(A,A) \<notin> s_mul_ext NS S" using irr
proof (induct A rule: wf_induct[OF wf_measure[of size]])
  case (1 A)
  show ?case
  proof
    assume "(A,A) \<in> s_mul_ext NS S" 
    from s_mul_extE[OF this]
    obtain A1 A2 B1 B2 where
      A: "A = A1 + A2" 
      and B: "A = B1 + B2"
      and AB1: "(A1, B1) \<in> multpw NS"
      and ne: "A2 \<noteq> {#}" 
      and S: "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> S" 
      by blast
    from multpw_listE[OF AB1] obtain as1 bs1 where
      l1: "length as1 = length bs1" 
      and A1: "A1 = mset as1" 
      and B1: "B1 = mset bs1" 
      and NS: "\<And> i. i<length bs1 \<Longrightarrow> (as1 ! i, bs1 ! i) \<in> NS" by blast
    (* store for later usage *)
    note NSS = NS
    note SS = S
   
    obtain as2 where A2: "A2 = mset as2" by (metis ex_mset)
    obtain bs2 where B2: "B2 = mset bs2" by (metis ex_mset)
    define as where "as = as1 @ as2" 
    define bs where "bs = bs1 @ bs2" 
    have as: "A = mset as" unfolding A A1 A2 as_def by simp
    have bs: "A = mset bs" unfolding B B1 B2 bs_def by simp
    from as bs have abs: "mset as = mset bs" by simp
    hence set_ab: "set as = set bs" by (rule mset_eq_setD)
    let ?n = "length bs" 
    have las: "length as = ?n" 
      using mset_eq_length abs by fastforce
    let ?m = "length bs1" 
    define decr where "decr j i \<equiv> 
       (as ! j, bs ! i) \<in> NS \<and> (i < ?m \<longrightarrow> j = i) \<and> (?m \<le> i \<longrightarrow> ?m \<le> j \<and> (as ! j, bs ! i) \<in> S)" for i j
    define step where "step i j k = 
       (i < ?n \<and> j < ?n \<and> k < ?n \<and> bs ! k = as ! j \<and> decr j i)" 
      for i j k
    {
      fix i
      assume i: "i < ?n" 
      let ?b = "bs ! i" 
      have "\<exists> j. j < ?n \<and> decr j i" 
      proof (cases "i < ?m")
        case False
        with i have "?b \<in> set bs2" unfolding bs_def 
          by (auto simp: nth_append)
        hence "?b \<in># B2" unfolding B2 by auto
        from S[OF this, unfolded A2] obtain a where a: "a \<in> set as2" and S: "(a, ?b) \<in> S" 
          by auto
        from a obtain k where a: "a = as2 ! k" and k: "k < length as2" unfolding set_conv_nth by auto
        have "a = as ! (?m + k)" unfolding a as_def l1[symmetric] by simp
        from S[unfolded this] S_NS False k
        show ?thesis unfolding decr_def
          by (intro exI[of _ "?m + k"], auto simp: las[symmetric] l1[symmetric] as_def)
      next
        case True
        from NS[OF this] i True show ?thesis unfolding decr_def
          by (auto simp: as_def bs_def l1 nth_append)
      qed (insert i NS)
      from this[unfolded set_conv_nth] las
      obtain j where j: "j < ?n" and decr: "decr j i" by auto
      let ?a = "as ! j" 
      from j las have "?a \<in> set as" by auto
      from this[unfolded set_ab, unfolded set_conv_nth] obtain k where
        k: "k < ?n" and id: "?a = bs ! k" by auto
      have "\<exists> j k. step i j k" 
        using j k decr id i unfolding step_def by metis
    }
    hence "\<forall> i. \<exists> j k. i < ?n \<longrightarrow> step i j k" by blast
    from choice[OF this] obtain J' where "\<forall> i. \<exists> k. i < ?n \<longrightarrow> step i (J' i) k" by blast
    from choice[OF this] obtain K' where 
      step: "\<And> i. i < ?n \<Longrightarrow> step i (J' i) (K' i)" by blast
    define I where "I i = (K'^^i) 0" for i 
    define J where "J i = J' (I i)" for i
    define K where "K i = K' (I i)" for i
    from ne have "A \<noteq> {#}" unfolding A by auto
    hence "set as \<noteq> {}" unfolding as by auto
    hence "length as \<noteq> 0" by simp
    hence n0: "0 < ?n" using las by auto
    {
      fix n
      have "step (I n) (J n) (K n)" 
      proof (induct n)
        case 0
        from step[OF n0] show ?case unfolding I_def J_def K_def by auto
      next
        case (Suc n)
        from Suc have "K n < ?n" unfolding step_def by auto
        from step[OF this] show ?case unfolding J_def K_def I_def by auto
      qed
    }
    note step = this
    have "I n \<in> {..<?n}" for n using step[of n] unfolding step_def by auto 
    hence "I ` UNIV \<subseteq> {..<?n}" by auto
    from finite_subset[OF this] have "finite (I ` UNIV)" by simp
    from pigeonhole_infinite[OF _ this] obtain m where 
      "infinite {i. I i = I m}" by auto
    hence "\<exists> m'. m' > m \<and> I m' = I m"
      by (simp add: infinite_nat_iff_unbounded)
    then obtain m' where *: "m < m'" "I m' = I m" by auto
    let ?P = "\<lambda> n. \<exists> m. n \<noteq> 0 \<and> I (n + m) = I m" 
    define n where "n = (LEAST n. ?P n)" 
    have "\<exists> n. ?P n" 
      by (rule exI[of _ "m' - m"], rule exI[of _ m], insert *, auto)
    from LeastI_ex[of ?P, OF this, folded n_def]
    obtain m where n: "n \<noteq> 0" and Im: "I (n + m) = I m" by auto
    let ?M = "{m..<m+n}" 
    {
      fix i j
      assume *: "m \<le> i" "i < j" "j < n + m" 
      define k where "k = j - i" 
      have k0: "k \<noteq> 0" and j: "j = k + i" and kn: "k < n" using * unfolding k_def by auto
      from not_less_Least[of _ ?P, folded n_def, OF kn] k0
      have "I i \<noteq> I j" unfolding j by metis
    } 
    hence inj: "inj_on I ?M" unfolding inj_on_def
      by (metis add.commute atLeastLessThan_iff linorder_neqE_nat)
    define b where "b i = bs ! I i" for i
    have bnm: "b (n + m) = b m" unfolding b_def Im ..
    {
      fix i
      from step[of i, unfolded step_def]
      have id: "bs ! K i = as ! J i" and decr: "decr (J i) (I i)" by auto
      from id decr[unfolded decr_def] have "(bs ! K i, bs ! I i) \<in> NS" by auto
      also have "K i = I (Suc i)" unfolding I_def K_def by auto
      finally have "(b (Suc i), b i) \<in> NS" unfolding b_def by auto
    } note NS = this
    {
      fix i j :: nat
      assume "i \<le> j" 
      then obtain k where j: "j = i + k" by (rule less_eqE)
      have "(b j, b i) \<in> NS^*" unfolding j
      proof (induct k)
        case (Suc k)
        thus ?case using NS[of "i + k"] by auto
      qed auto
    } note NSstar = this
    {
      assume "\<exists> i \<in> ?M. I i \<ge> ?m" 
      then obtain k where k: "k \<in> ?M" and I: "I k \<ge> ?m" by auto
      from step[of k, unfolded step_def]
      have id: "bs ! K k = as ! J k" and decr: "decr (J k) (I k)" by auto
      from id decr[unfolded decr_def] I have "(bs ! K k, bs ! I k) \<in> S" by auto
      also have "K k = I (Suc k)" unfolding I_def K_def by auto
      finally have S: "(b (Suc k), b k) \<in> S" unfolding b_def by auto
      from k have "m \<le> k" by auto
      from NSstar[OF this] have NS1: "(b k, b m) \<in> NS^*" .
      from k have "Suc k \<le> n + m" by auto
      from NSstar[OF this, unfolded bnm] have NS2: "(b m, b (Suc k)) \<in> NS^*" .
      from NS1 NS2 have "(b k, b (Suc k)) \<in> NS^*" by simp
      with S have "(b (Suc k), b (Suc k)) \<in> S O NS^*" by auto
      also have "\<dots> \<subseteq> S" using compat
        by (metis compat_tr_compat converse_inward(1) converse_mono converse_relcomp)
      finally have contradiction: "b (Suc k) \<notin> set_mset A" using 1 unfolding irrefl_on_def by auto
      have "b (Suc k) \<in> set bs" unfolding b_def using step[of "Suc k"] unfolding step_def
        by auto
      also have "set bs = set_mset A" unfolding bs by auto
      finally have False using contradiction by auto
    }
    hence only_NS: "i \<in> ?M \<Longrightarrow> I i < ?m" for i by force
    {
      fix i
      assume i: "i \<in> ?M" 
      from step[of i, unfolded step_def] have *: "I i < ?n" "K i < ?n" 
        and id: "bs ! K i = as ! J i" and decr: "decr (J i) (I i)" by auto
      from decr[unfolded decr_def] only_NS[OF i] have "J i = I i" by auto
      with id have id: "bs ! K i = as ! I i" by auto
      note only_NS[OF i] id
    } note pre_result = this
    {
      fix i
      assume i: "i \<in> ?M" 
      have *: "I i < ?m" "K i < ?m" 
      proof (rule pre_result[OF i])
        have "\<exists> j \<in> ?M. K i = I j" 
        proof (cases "Suc i \<in> ?M")
          case True
          show ?thesis by (rule bexI[OF _ True], auto simp: K_def I_def)
        next
          case False
          with i have id: "n + m = Suc i" by auto
          hence id: "K i = I m" by (subst Im[symmetric], unfold id, auto simp: K_def I_def) 
          with i show ?thesis by (intro bexI[of _ m], auto simp: K_def I_def)
        qed
        with pre_result show "K i < ?m" by auto
      qed
      from pre_result(2)[OF i] * l1 have "bs1 ! K i = as1 ! I i" "K i = I (Suc i)" 
        unfolding as_def bs_def by (auto simp: nth_append K_def I_def)
      with * have "bs1 ! I (Suc i) = as1 ! I i" "I i < ?m" "I (Suc i) < ?m" 
        by auto
    } note pre_identities = this
    define M where "M = ?M" 
    note inj = inj[folded M_def]
    define nxt where "nxt i = (if Suc i = n + m then m else Suc i)" for i
    define prv where "prv i = (if i = m then n + m - 1 else i - 1)" for i
    {
      fix i
      assume "i \<in> M" 
      hence i: "i \<in> ?M" unfolding M_def by auto
      from i n have inM: "nxt i \<in> M" "prv i \<in> M" "nxt (prv i) = i" "prv (nxt i) = i"
        unfolding nxt_def prv_def by (auto simp: M_def)
      from i pre_identities[OF i] pre_identities[of m] Im n
      have nxt: "bs1 ! I (nxt i) = as1 ! I i"  
        unfolding nxt_def prv_def by (auto simp: M_def)
      note nxt inM
    } note identities = this
  
  
    (* next up: remove elements indexed by I ` ?m from both as1 and bs1 
       and apply induction hypothesis *)
    note identities = identities[folded M_def]
    define Drop where "Drop = I ` M" 

    define rem_idx where "rem_idx = filter (\<lambda> i. i \<notin> Drop) [0..<?m]" 
    define drop_idx where "drop_idx = filter (\<lambda> i. i \<in> Drop) [0..<?m]" 
    define as1' where "as1' = map ((!) as1) rem_idx" 
    define bs1' where "bs1' = map ((!) bs1) rem_idx"
    define as1'' where "as1'' = map ((!) as1) drop_idx" 
    define bs1'' where "bs1'' = map ((!) bs1) drop_idx" 
    {
      fix as1 :: "'a list" and D :: "nat set" 
      define I where "I = [0..< length as1]" 
      have "mset as1 = mset (map ((!) as1) I)" unfolding I_def
        by (rule arg_cong[of _ _ mset], intro nth_equalityI, auto)
      also have "\<dots> = mset (map ((!) as1) (filter (\<lambda> i. i \<in> D) I))
          + mset (map ((!) as1) (filter (\<lambda> i. i \<notin> D) I))" 
        by (induct I, auto)
      also have "I = [0..< length as1]" by fact
      finally have "mset as1 = mset (map ((!) as1) (filter (\<lambda>i. i \<in> D) [0..<length as1])) + mset (map ((!) as1) (filter (\<lambda>i. i \<notin> D) [0..<length as1]))" .
    } note split = this
    from split[of bs1 Drop, folded rem_idx_def drop_idx_def, folded bs1'_def bs1''_def]
    have bs1: "mset bs1 = mset bs1'' + mset bs1'" .
    from split[of as1 Drop, unfolded l1, folded rem_idx_def drop_idx_def, folded as1'_def as1''_def]
    have as1: "mset as1 = mset as1'' + mset as1'" .

    (* showing that as1'' = bs1'' *)
    define I' where "I' = the_inv_into M I" 
    have bij: "bij_betw I M Drop" using inj unfolding Drop_def by (rule inj_on_imp_bij_betw)
    from the_inv_into_f_f[OF inj, folded I'_def] have I'I: "i \<in> M \<Longrightarrow> I' (I i) = i" for i by auto
    from bij I'I have II': "i \<in> Drop \<Longrightarrow> I (I' i) = i" for i
      by (simp add: I'_def f_the_inv_into_f_bij_betw)
    from II' I'I identities bij have Drop_M: "i \<in> Drop \<Longrightarrow> I' i \<in> M" for i
      using Drop_def by force
    have M_Drop: "i \<in> M \<Longrightarrow> I i \<in> Drop" for i unfolding Drop_def by auto
    {
      fix x
      assume "x \<in> Drop" 
      then obtain i where i: "i \<in> M" and x: "x = I i" unfolding Drop_def by auto
      have "x < ?m" unfolding x using i pre_identities[of i] unfolding M_def by auto
    } note Drop_m = this
    hence drop_idx: "set drop_idx = Drop" unfolding M_def drop_idx_def set_filter set_upt by auto
    have "mset as1'' = mset (map ((!) as1) drop_idx)" unfolding as1''_def mset_map by auto
    also have "drop_idx = map (I o I') drop_idx" using drop_idx by (intro nth_equalityI, auto intro!: II'[symmetric])
    also have "map ((!) as1) \<dots> = map (\<lambda> i. as1 ! I i) (map I' drop_idx)" by auto
    also have "\<dots> = map (\<lambda> i. bs1 ! I (nxt i)) (map I' drop_idx)" 
      by (rule map_cong[OF refl], rule identities(1)[symmetric], insert drop_idx Drop_M, auto)
    also have "\<dots> = map ((!) bs1) (map (I o nxt o I') drop_idx)" 
      by auto
    also have "mset \<dots> = image_mset ((!) bs1) (image_mset (I o nxt o I') (mset drop_idx))" unfolding mset_map ..
    also have "image_mset (I o nxt o I') (mset drop_idx) = image_mset I (image_mset nxt (image_mset I' (mset drop_idx)))" 
      by (metis multiset.map_comp)
    also have "image_mset nxt (image_mset I' (mset drop_idx)) = image_mset I' (mset drop_idx)" 
    proof -
      have dist: "distinct drop_idx" unfolding drop_idx_def by auto
      have injI': "inj_on I' Drop" using II' by (rule inj_on_inverseI)
      have "mset drop_idx = mset_set Drop" unfolding drop_idx[symmetric]
        by (rule mset_set_set[symmetric, OF dist])
      from image_mset_mset_set[OF injI', folded this]
      have "image_mset I' (mset drop_idx) = mset_set (I' ` Drop)" by auto
      also have "I' ` Drop = M" using II' I'I M_Drop Drop_M by force
      finally have id: "image_mset I' (mset drop_idx) = mset_set M" .
      have inj_nxt: "inj_on nxt M" using identities by (intro inj_on_inverseI)
      have nxt: "nxt ` M = M" using identities by force
      show ?thesis unfolding id image_mset_mset_set[OF inj_nxt] nxt ..
    qed
    also have "image_mset I \<dots> = mset drop_idx" unfolding multiset.map_comp using II' 
      by (intro multiset.map_ident_strong, auto simp: drop_idx)
    also have "image_mset ((!) bs1) \<dots> = mset bs1''" unfolding bs1''_def mset_map ..
    finally have bs1'': "mset bs1'' = mset as1''" ..

    (* showing the remaining identities *)
    let ?A = "mset as1' + mset as2" 
    let ?B = "mset bs1' + mset bs2" 
    from as1 bs1'' have as1: "mset as1 = mset bs1'' + mset as1'" by auto
    have A: "A = mset bs1'' + ?A" unfolding A A1 A2 as1 by auto
    have B: "A = mset bs1'' + ?B" unfolding B B1 B2 bs1 by auto
    from A[unfolded B] have AB: "?A = ?B" by simp
    
    have l1': "length as1' = length bs1'" unfolding as1'_def bs1'_def by auto
    have NS: "(mset as1', mset bs1') \<in> multpw NS" 
    proof (rule multpw_listI[OF l1' refl refl], intro allI impI)
      fix i
      assume i: "i < length bs1'"
      hence "rem_idx ! i \<in> set rem_idx" unfolding bs1'_def by (auto simp: nth_append)
      hence ri: "rem_idx ! i < ?m" unfolding rem_idx_def by auto
      from NSS[OF this] i
      show "(as1' ! i, bs1' ! i) \<in> NS" unfolding as1'_def bs1'_def by (auto simp: nth_append)
    qed
    have S: "(mset as1' + mset as2, ?B) \<in> s_mul_ext NS S"
      by (intro s_mul_extI[OF refl refl NS], unfold A2[symmetric] B2[symmetric], rule ne, rule S)
    have irr: "irrefl_on (set_mset ?B) S" using 1(2) B unfolding irrefl_on_def by simp
    have "M \<noteq> {}" unfolding M_def using n by auto
    hence "Drop \<noteq> {}" unfolding Drop_def by auto
    with drop_idx have "drop_idx \<noteq> []" by auto
    hence "bs1'' \<noteq> []" unfolding bs1''_def by auto
    hence "?B \<subset># A" unfolding B by (simp add: subset_mset.less_le)
    hence "size ?B < size A" by (rule mset_subset_size)
    thus False using 1(1) AB S irr by auto
  qed
qed
  
lemma mul_ext_irrefl: assumes "\<And> x. x \<in> set xs \<Longrightarrow> \<not> fst (rel x x)" 
  and "\<And> x y z. fst (rel x y) \<Longrightarrow> snd (rel y z) \<Longrightarrow> fst (rel x z)"
  and "\<And> x y. fst (rel x y) \<Longrightarrow> snd (rel x y)" 
shows "\<not> fst (mul_ext rel xs xs)" 
  unfolding mul_ext_def Let_def fst_conv
  by (rule s_mul_ext_irrefl, insert assms, auto simp: irrefl_on_def)

text \<open>The non-strict order is transitive.\<close>

lemma ns_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> ns_mul_ext ns s"
    and "(B, C) \<in> ns_mul_ext ns s"
  shows "(A, C) \<in> ns_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def ns_mul_ext_def
  using trans_mult2_ns[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_ns_eq_mult2_ns_alt converse_relcomp[symmetric]) (metis trans_def)

text\<open>The strict order is trans.\<close>

lemma s_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> s_mul_ext ns s"
    and "(B, C) \<in> s_mul_ext ns s"
  shows "(A, C) \<in> s_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def s_mul_ext_def
  using trans_mult2_s[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_s_eq_mult2_s_alt converse_relcomp[symmetric]) (metis trans_def)

text\<open>The strict order is compatible on the left with the non strict one\<close>

lemma s_ns_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> s_mul_ext ns s"
    and "(B, C) \<in> ns_mul_ext ns s"
  shows "(A, C) \<in> s_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def s_mul_ext_def ns_mul_ext_def
  using compat_mult2(1)[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_s_eq_mult2_s_alt mult2_ns_eq_mult2_ns_alt converse_relcomp[symmetric])


text\<open>The strict order is compatible on the right with the non-strict one.\<close>

lemma ns_s_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> ns_mul_ext ns s"
    and "(B, C) \<in> s_mul_ext ns s"
  shows "(A, C) \<in> s_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def s_mul_ext_def ns_mul_ext_def
  using compat_mult2(2)[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_s_eq_mult2_s_alt mult2_ns_eq_mult2_ns_alt converse_relcomp[symmetric])

text\<open>@{const s_mul_ext} is strongly normalizing\<close>

lemma SN_s_mul_ext_strong:
  assumes "order_pair s ns"
    and "\<forall>y. y \<in># M \<longrightarrow> SN_on s {y}"
  shows "SN_on (s_mul_ext ns s) {M}"
  using mult2_s_eq_mult2_s_alt[of "ns\<inverse>" "s\<inverse>"] assms wf_below_pointwise[of "s\<inverse>" "set_mset M"]
  unfolding SN_on_iff_wf_below s_mul_ext_def order_pair_def compat_pair_def pre_order_pair_def
  by (auto intro!: wf_below_mult2_s_local simp: converse_relcomp[symmetric])

lemma SN_s_mul_ext:
  assumes "order_pair s ns" "SN s"
  shows "SN (s_mul_ext ns s)"
  using SN_s_mul_ext_strong[OF assms(1)] assms(2)
  by (auto simp: SN_on_def)

lemma (in order_pair) mul_ext_order_pair:
  "order_pair (s_mul_ext NS S) (ns_mul_ext NS S)" (is "order_pair ?S ?NS")
proof
  from s_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "trans ?S" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from ns_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "trans ?NS" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from ns_s_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "?NS O ?S \<subseteq> ?S" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from s_ns_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "?S O ?NS \<subseteq> ?S" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from ns_mul_ext_refl[OF refl_NS, of _ S]
  show "refl ?NS" unfolding refl_on_def by fast
qed

lemma (in SN_order_pair) mul_ext_SN_order_pair: "SN_order_pair (s_mul_ext NS S) (ns_mul_ext NS S)"
  (is "SN_order_pair ?S ?NS")
proof -
  from mul_ext_order_pair
  interpret order_pair ?S ?NS .
  have "order_pair S NS" by unfold_locales
  then interpret SN_ars ?S using SN_s_mul_ext[of S NS] SN by unfold_locales
  show ?thesis by unfold_locales
qed

lemma mul_ext_compat:
  assumes compat: "\<And> s t u. \<lbrakk>s \<in> set ss; t \<in> set ts; u \<in> set us\<rbrakk> \<Longrightarrow>
    (snd (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u)) \<and>
    (fst (f s t) \<and> snd (f t u) \<longrightarrow> fst (f s u)) \<and>
    (snd (f s t) \<and> snd (f t u) \<longrightarrow> snd (f s u)) \<and>
    (fst (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u))"
  shows "
    (snd (mul_ext f ss ts) \<and> fst (mul_ext f ts us) \<longrightarrow> fst (mul_ext f ss us)) \<and>
    (fst (mul_ext f ss ts) \<and> snd (mul_ext f ts us) \<longrightarrow> fst (mul_ext f ss us)) \<and>
    (snd (mul_ext f ss ts) \<and> snd (mul_ext f ts us) \<longrightarrow> snd (mul_ext f ss us)) \<and>
    (fst (mul_ext f ss ts) \<and> fst (mul_ext f ts us) \<longrightarrow> fst (mul_ext f ss us)) "
proof -
  let ?s = "{(x, y). fst (f x y)}\<inverse>" and ?ns = "{(x, y). snd (f x y)}\<inverse>"
  have [dest]: "(mset ts, mset ss) \<in> mult2_alt b2 ?ns ?s \<Longrightarrow> (mset us, mset ts) \<in> mult2_alt b1 ?ns ?s \<Longrightarrow>
    (mset us, mset ss) \<in> mult2_alt (b1 \<and> b2) ?ns ?s" for b1 b2
    using assms by (auto intro!: trans_mult2_alt_local[of _ "mset ts"] simp: in_multiset_in_set)
  show ?thesis by (auto simp: mul_ext_def s_mul_ext_def ns_mul_ext_def Let_def)
qed

lemma mul_ext_cong[fundef_cong]:
  assumes "mset xs1 = mset ys1"
    and "mset xs2 = mset ys2"
    and "\<And> x x'. x \<in> set ys1 \<Longrightarrow> x' \<in> set ys2 \<Longrightarrow> f x x' = g x x'"
  shows "mul_ext f xs1 xs2 = mul_ext g ys1 ys2"
  using assms
    mult2_alt_map[of "mset xs2" "mset xs1" "{(x, y). snd (f x y)}\<inverse>" id id "{(x, y). snd (g x y)}\<inverse>"
      "{(x, y). fst (f x y)}\<inverse>" "{(x, y). fst (g x y)}\<inverse>"]
    mult2_alt_map[of "mset ys2" "mset ys1" "{(x, y). snd (g x y)}\<inverse>" id id "{(x, y). snd (f x y)}\<inverse>"
      "{(x, y). fst (g x y)}\<inverse>" "{(x, y). fst (f x y)}\<inverse>"]
  by (auto simp: mul_ext_def s_mul_ext_def ns_mul_ext_def Let_def in_multiset_in_set)

lemma all_nstri_imp_mul_nstri:
  assumes "\<forall>i<length ys. snd (f (xs ! i) (ys ! i))"
    and "length xs = length ys"
  shows "snd (mul_ext f xs ys)"
proof-
  from assms(1) have "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> {(x,y). snd (f x y)}" by simp
  from all_ns_ns_mul_ext[OF assms(2) this] show ?thesis by (simp add: mul_ext_def)
qed

lemma relation_inter:
  shows "{(x,y). P x y} \<inter> {(x,y). Q x y} = {(x,y). P x y \<and> Q x y}"
  by blast

lemma mul_ext_unfold:
  "(x,y) \<in> {(a,b). fst (mul_ext g a b)} \<longleftrightarrow> (mset x, mset y) \<in> (s_mul_ext {(a,b). snd (g a b)} {(a,b). fst (g a b)})"
  unfolding mul_ext_def by (simp add: Let_def)

text \<open>The next lemma is a local version of strong-normalization of
  the multiset extension, where the base-order only has to be strongly normalizing
  on elements of the multisets. This will be crucial for orders that are defined recursively
  on terms, such as RPO or WPO.\<close>
lemma mul_ext_SN:
  assumes "\<forall>x. snd (g x x)"
    and "\<forall>x y z. fst (g x y) \<longrightarrow> snd (g y z) \<longrightarrow> fst (g x z)"
    and "\<forall>x y z. snd (g x y) \<longrightarrow> fst (g y z) \<longrightarrow> fst (g x z)"
    and "\<forall>x y z. snd (g x y) \<longrightarrow> snd (g y z) \<longrightarrow> snd (g x z)"
    and "\<forall>x y z. fst (g x y) \<longrightarrow> fst (g y z) \<longrightarrow> fst (g x z)"
  shows "SN {(ys, xs).
  (\<forall>y\<in>set ys. SN_on {(s ,t). fst (g s t)} {y}) \<and>
  fst (mul_ext g ys xs)}"
proof -
  let ?R1 = "\<lambda>xs ys. \<forall>y\<in> set ys. SN_on {(s ,t). fst (g s t)} {y}"
  let ?R2 = "\<lambda>xs ys. fst (mul_ext g ys xs)"
  let ?s = "{(x,y). fst (g x y)}" and ?ns = "{(x,y). snd (g x y)}"
  have OP: "order_pair ?s ?ns" using assms(1-5)
    by unfold_locales ((unfold refl_on_def trans_def)?, blast)+
  let ?R = "{(ys, xs). ?R1 xs ys \<and> ?R2 xs ys}"
  let ?Sn = "SN_on ?R"
  {
    fix ys xs
    assume R_ys_xs: "(ys, xs) \<in> ?R"
    let ?mys = "mset ys"
    let ?mxs = "mset xs"
    from R_ys_xs have  HSN_ys: "\<forall>y. y \<in> set ys \<longrightarrow> SN_on ?s {y}" by simp
    with in_multiset_in_set[of ys] have "\<forall>y. y \<in># ?mys \<longrightarrow> SN_on ?s {y}" by simp
    from SN_s_mul_ext_strong[OF OP this] and mul_ext_unfold
    have "SN_on {(ys,xs). fst (mul_ext g ys xs)} {ys}" by fast
    from relation_inter[of ?R2 ?R1] and SN_on_weakening[OF this]
    have "SN_on ?R {ys}" by blast
  }
  then have Hyp: "\<forall>ys xs. (ys,xs) \<in> ?R \<longrightarrow> SN_on ?R {ys}" by auto
  {
    fix ys
    have "SN_on ?R {ys}"
    proof (cases "\<exists> xs. (ys, xs) \<in> ?R")
      case True with Hyp show ?thesis by simp
    next
      case False then show ?thesis by auto
    qed
  }
  then show ?thesis unfolding SN_on_def by simp
qed

lemma mul_ext_stri_imp_nstri:
  assumes "fst (mul_ext f as bs)"
  shows "snd (mul_ext f as bs)"
  using assms and s_ns_mul_ext unfolding mul_ext_def by (auto simp: Let_def)

lemma ns_ns_mul_ext_union_compat:
  assumes "(A,B) \<in> ns_mul_ext ns s"
    and "(C,D) \<in> ns_mul_ext ns s"
  shows "(A + C, B + D) \<in> ns_mul_ext ns s"
  using assms by (auto simp: ns_mul_ext_def intro: mult2_alt_ns_ns_add)

lemma s_ns_mul_ext_union_compat:
  assumes "(A,B) \<in> s_mul_ext ns s"
    and "(C,D) \<in> ns_mul_ext ns s"
  shows "(A + C, B + D) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def ns_mul_ext_def intro: mult2_alt_s_ns_add)

lemma ns_ns_mul_ext_union_compat_rtrancl: assumes refl: "refl ns"
  and AB: "(A, B) \<in> (ns_mul_ext ns s)\<^sup>*"
  and CD: "(C, D) \<in> (ns_mul_ext ns s)\<^sup>*"
shows "(A + C, B + D) \<in> (ns_mul_ext ns s)\<^sup>*"
proof -
  {
    fix A B C
    assume "(A, B) \<in> (ns_mul_ext ns s)\<^sup>*"
    then have "(A + C, B + C) \<in> (ns_mul_ext ns s)\<^sup>*"
    proof (induct rule: rtrancl_induct)
      case (step B D)
      have "(C, C) \<in> ns_mul_ext ns s"
        by (rule ns_mul_ext_refl, insert refl, auto simp: locally_refl_def refl_on_def)
      from ns_ns_mul_ext_union_compat[OF step(2) this] step(3)
      show ?case by auto
    qed auto
  }
  from this[OF AB, of C] this[OF CD, of B]
  show ?thesis by (auto simp: ac_simps)
qed

subsection \<open>Multisets as order on lists\<close>

interpretation mul_ext_list: list_order_extension
  "\<lambda>s ns. {(as, bs). (mset as, mset bs) \<in> s_mul_ext ns s}"
  "\<lambda>s ns. {(as, bs). (mset as, mset bs) \<in> ns_mul_ext ns s}"
proof -
  let ?m = "mset :: ('a list \<Rightarrow> 'a multiset)"
  let ?S = "\<lambda>s ns. {(as, bs). (?m as, ?m bs) \<in> s_mul_ext ns s}"
  let ?NS = "\<lambda>s ns. {(as, bs). (?m as, ?m bs) \<in> ns_mul_ext ns s}"
  show "list_order_extension ?S ?NS"
  proof (rule list_order_extension.intro)
    fix s ns
    let ?s = "?S s ns"
    let ?ns = "?NS s ns"
    assume "SN_order_pair s ns"
    then interpret SN_order_pair s ns .
    interpret SN_order_pair "(s_mul_ext ns s)" "(ns_mul_ext ns s)"
      by (rule mul_ext_SN_order_pair)
    show "SN_order_pair ?s ?ns"
    proof
      show "refl ?ns" using refl_NS unfolding refl_on_def by blast
      show "?ns O ?s \<subseteq> ?s" using compat_NS_S by blast
      show "?s O ?ns \<subseteq> ?s" using compat_S_NS by blast
      show "trans ?ns" using trans_NS unfolding trans_def by blast
      show "trans ?s" using trans_S unfolding trans_def by blast
      show "SN ?s" using SN_inv_image[OF SN, of ?m, unfolded inv_image_def] .
    qed
  next
    fix S f NS as bs
    assume "\<And>a b. (a, b) \<in> S \<Longrightarrow> (f a, f b) \<in> S"
      "\<And>a b. (a, b) \<in> NS \<Longrightarrow> (f a, f b) \<in> NS"
      "(as, bs) \<in> ?S S NS"
    then show "(map f as, map f bs) \<in> ?S S NS"
      using mult2_alt_map[of _ _ "NS\<inverse>" f f "NS\<inverse>" "S\<inverse>" "S\<inverse>"] by (auto simp: mset_map s_mul_ext_def)
  next
    fix S f NS as bs
    assume "\<And>a b. (a, b) \<in> S \<Longrightarrow> (f a, f b) \<in> S"
      "\<And>a b. (a, b) \<in> NS \<Longrightarrow> (f a, f b) \<in> NS"
      "(as, bs) \<in> ?NS S NS"
    then show "(map f as, map f bs) \<in> ?NS S NS"
      using mult2_alt_map[of _ _ "NS\<inverse>" f f "NS\<inverse>" "S\<inverse>" "S\<inverse>"] by (auto simp: mset_map ns_mul_ext_def)
  next
    fix as bs :: "'a list" and NS S :: "'a rel"
    assume ass: "length as = length bs"
      "\<And>i. i < length bs \<Longrightarrow> (as ! i, bs ! i) \<in> NS"
    show "(as, bs) \<in> ?NS S NS"
      by (rule, unfold split, rule all_ns_ns_mul_ext, insert ass, auto)
  qed
qed

lemma s_mul_ext_singleton [simp, intro]:
  assumes "(a, b) \<in> s"
  shows "({#a#}, {#b#}) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def mult2_alt_s_single)

lemma ns_mul_ext_singleton [simp, intro]:
  "(a, b) \<in> ns \<Longrightarrow> ({#a#}, {#b#}) \<in> ns_mul_ext ns s"
  by (auto simp: ns_mul_ext_def multpw_converse intro: multpw_implies_mult2_alt_ns multpw_single)

lemma ns_mul_ext_singleton2:
  "(a, b) \<in> s \<Longrightarrow> ({#a#}, {#b#}) \<in> ns_mul_ext ns s"
  by (intro s_ns_mul_ext s_mul_ext_singleton)

lemma s_mul_ext_self_extend_left:
  assumes "A \<noteq> {#}" and "locally_refl W B"
  shows "(A + B, B) \<in> s_mul_ext W S"
proof -
  have "(A + B, {#} + B) \<in> s_mul_ext W S"
    using assms by (intro s_mul_ext_union_compat) (auto dest: s_mul_ext_bottom)
  then show ?thesis by simp
qed

lemma s_mul_ext_ne_extend_left:
  assumes "A \<noteq> {#}" and "(B, C) \<in> ns_mul_ext W S"
  shows "(A + B, C) \<in> s_mul_ext W S"
  using assms
proof -
  have "(A + B, {#} + C) \<in> s_mul_ext W S"
    using assms by (intro s_ns_mul_ext_union_compat)
      (auto simp: s_mul_ext_bottom dest: s_ns_mul_ext)
  then show ?thesis by (simp add: ac_simps)
qed

lemma s_mul_ext_extend_left:
  assumes "(B, C) \<in> s_mul_ext W S"
  shows "(A + B, C) \<in> s_mul_ext W S"
  using assms
proof -
  have "(B + A, C + {#}) \<in> s_mul_ext W S"
    using assms by (intro s_ns_mul_ext_union_compat)
      (auto simp: ns_mul_ext_bottom dest: s_ns_mul_ext)
  then show ?thesis by (simp add: ac_simps)
qed

lemma mul_ext_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set ys; fst (P x y)\<rbrakk> \<Longrightarrow> fst (P' x y)"
    and   "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set ys; snd (P x y)\<rbrakk> \<Longrightarrow> snd (P' x y)"
  shows
    "fst (mul_ext P xs ys) \<Longrightarrow> fst (mul_ext P' xs ys)"
    "snd (mul_ext P xs ys) \<Longrightarrow> snd (mul_ext P' xs ys)"
  unfolding mul_ext_def Let_def fst_conv snd_conv
proof -
  assume mem: "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (P x y)} {(x, y). fst (P x y)}"
  show "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (P' x y)} {(x, y). fst (P' x y)}"
    by (rule s_mul_ext_local_mono[OF _ _ mem], insert assms, auto)
next
  assume mem: "(mset xs, mset ys) \<in> ns_mul_ext {(x, y). snd (P x y)} {(x, y). fst (P x y)}"
  show "(mset xs, mset ys) \<in> ns_mul_ext {(x, y). snd (P' x y)} {(x, y). fst (P' x y)}"
    by (rule ns_mul_ext_local_mono[OF _ _ mem], insert assms, auto)
qed



subsection \<open>Special case: non-strict order is equality\<close>

lemma ns_mul_ext_IdE:
  assumes "(M, N) \<in> ns_mul_ext Id R"
  obtains X and Y and Z where "M = X + Z" and "N = Y + Z"
    and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  using assms
  by (auto simp: ns_mul_ext_def elim!: mult2_alt_nsE) (insert union_commute, blast)

lemma ns_mul_ext_IdI:
  assumes "M = X + Z" and "N = Y + Z" and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  shows "(M, N) \<in> ns_mul_ext Id R"
  using assms mult2_alt_nsI[of N Z Y M Z X Id "R\<inverse>"]
  by (auto simp: ns_mul_ext_def)

lemma s_mul_ext_IdE:
  assumes "(M, N) \<in> s_mul_ext Id R"
  obtains X and Y and Z where "X \<noteq> {#}" and "M = X + Z" and "N = Y + Z"
    and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  using assms
  by (auto simp: s_mul_ext_def elim!: mult2_alt_sE) (metis union_commute)

lemma s_mul_ext_IdI:
  assumes "X \<noteq> {#}" and "M = X + Z" and "N = Y + Z"
    and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  shows "(M, N) \<in> s_mul_ext Id R"
  using assms mult2_alt_sI[of N Z Y M Z X Id "R\<inverse>"]
  by (auto simp: s_mul_ext_def ac_simps)

lemma mult_s_mul_ext_conv:
  assumes "trans R"
  shows "(mult (R\<inverse>))\<inverse> = s_mul_ext Id R"
  using mult2_s_eq_mult2_s_alt[of Id "R\<inverse>"] assms
  by (auto simp: s_mul_ext_def refl_Id mult2_s_def)

lemma ns_mul_ext_Id_eq:
  "ns_mul_ext Id R = (s_mul_ext Id R)\<^sup>="
  by (auto simp add: ns_mul_ext_def s_mul_ext_def mult2_alt_ns_conv)

lemma subseteq_mset_imp_ns_mul_ext_Id:
  assumes "A \<subseteq># B"
  shows "(B, A) \<in> ns_mul_ext Id R"
proof -
  obtain C where [simp]: "B = C + A" using assms by (auto simp: mset_subset_eq_exists_conv ac_simps)
  have "(C + A, {#} + A) \<in> ns_mul_ext Id R"
    by (intro ns_mul_ext_IdI [of _ C A _ "{#}"]) auto
  then show ?thesis by simp
qed

lemma subset_mset_imp_s_mul_ext_Id:
  assumes "A \<subset># B"
  shows "(B, A) \<in> s_mul_ext Id R"
  using assms by (intro supset_imp_s_mul_ext) (auto simp: refl_Id)


end
