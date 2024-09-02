theory Traces 
imports Main HOL.Lattices HOL.List 
begin

chapter \<open>Traces and Definitive Prefixes\<close>

section \<open>Traces\<close>

typedecl \<Sigma>
type_synonym 'a finite_trace = \<open>'a list\<close>
type_synonym 'a infinite_trace = \<open>nat \<Rightarrow> 'a\<close>
datatype 'a trace = Finite \<open>'a finite_trace\<close> | Infinite \<open>'a infinite_trace\<close>

fun thead :: \<open>'a trace \<Rightarrow> 'a\<close> where
  \<open>thead (Finite t) = t ! 0\<close>
| \<open>thead (Infinite t) = t 0\<close>

fun append :: \<open>'a trace \<Rightarrow> 'a trace \<Rightarrow> 'a trace\<close> (infixr \<open>\<frown>\<close> 80) where
  \<open>(Finite t)   \<frown> (Infinite \<omega>) = Infinite (\<lambda>n. if n < length t then t!n else \<omega> (n - length t))\<close>
| \<open>(Finite t)   \<frown> (Finite u)   = Finite (t @ u)\<close>
| \<open>(Infinite t) \<frown> u            = Infinite t\<close>

definition \<epsilon> :: \<open>'a trace\<close> where
  \<open>\<epsilon> = Finite []\<close>

definition singleton :: \<open>'a \<Rightarrow> 'a trace\<close> where
  \<open>singleton \<sigma> = Finite [\<sigma>]\<close>

interpretation trace: monoid_list \<open>(\<frown>)\<close> \<open>\<epsilon>\<close>
proof unfold_locales
  fix a :: \<open>'a trace\<close> show \<open>\<epsilon> \<frown> a = a\<close>
    by (cases \<open>a\<close>; simp add: \<epsilon>_def)
next
  fix a :: \<open>'a trace\<close> show \<open>a \<frown> \<epsilon> = a\<close> 
    by (cases \<open>a\<close>; simp add: \<epsilon>_def)
next
  fix a b c :: \<open>'a trace\<close> show \<open>(a \<frown> b) \<frown> c = a \<frown> (b \<frown> c)\<close>
    apply (cases \<open>a\<close>; simp)
    apply (cases \<open>b\<close>; simp)
    apply (cases \<open>c\<close>; simp)
    apply (rule ext; simp)
    by (smt (verit, ccfv_threshold) 
            add.commute add_diff_inverse_nat add_less_cancel_left 
            nth_append trans_less_add2)
qed

lemma finite_empty_suffix: 
  assumes \<open>Finite xs = Finite xs \<frown> t\<close>
  shows \<open>t = \<epsilon>\<close>
  using assms by (cases \<open>t\<close>) (simp_all add: \<epsilon>_def)

lemma finite_empty_prefix: 
  assumes \<open>Finite xs = t \<frown> Finite xs\<close>
  shows \<open>t = \<epsilon>\<close>
  using assms by (cases \<open>t\<close>) (simp_all add: \<epsilon>_def)

lemma finite_finite_suffix: 
  assumes \<open>Finite xs = Finite ys \<frown> t\<close>
  obtains zs where \<open>t = Finite zs\<close>
  using assms by (cases \<open>t\<close>) (simp_all)

lemma finite_finite_prefix:
  assumes \<open>Finite xs = t \<frown> Finite ys\<close>
  obtains zs where \<open>t = Finite zs\<close>
  using assms by (cases \<open>t\<close>) (simp_all)

lemma append_is_empty:
  assumes \<open>t \<frown> u = \<epsilon>\<close>
  shows   \<open>t = \<epsilon>\<close>
  and     \<open>u = \<epsilon>\<close>
  using assms by (simp add: \<epsilon>_def; cases \<open>t\<close>; cases \<open>u\<close>; simp)+

fun ttake :: \<open>nat \<Rightarrow> 'a trace \<Rightarrow> 'a finite_trace\<close> where
  \<open>ttake k (Finite xs) = take k xs\<close>
| \<open>ttake k (Infinite xs) = map xs [0..<k] \<close>


definition itdrop :: \<open>nat \<Rightarrow> 'a infinite_trace \<Rightarrow> 'a infinite_trace\<close> where
  \<open>itdrop k xs = (\<lambda>i. xs (i + k))\<close>

lemma itdrop_itdrop[simp]: \<open>itdrop i (itdrop j x) = itdrop (i + j) x\<close>
  by (simp add: itdrop_def add.commute add.left_commute)

lemma itdrop_zero[simp]: \<open>itdrop 0 x = x\<close>
  by (simp add: itdrop_def)


fun tdrop :: \<open>nat \<Rightarrow> 'a trace \<Rightarrow> 'a trace\<close> where
  \<open>tdrop k (Finite xs) = Finite (drop k xs)\<close>
| \<open>tdrop k (Infinite xs) = Infinite (itdrop k xs) \<close>

lemma ttake_simp[simp]: \<open>ttake (length xs) (Finite xs \<frown> t) = xs\<close>
  by (cases \<open>t\<close>, auto intro:  list_eq_iff_nth_eq[THEN iffD2])

lemma ttake_tdrop[simp]: \<open>Finite (ttake k t) \<frown> tdrop k t = t\<close>
  by (cases \<open>t\<close>, auto simp: itdrop_def)

definition prefixes :: \<open>'a trace \<Rightarrow> 'a trace set\<close> (\<open>\<down> _\<close> [80] 80) where
  \<open>\<down> t = { u | u v. t = u \<frown> v }\<close>

definition extensions :: \<open>'a trace \<Rightarrow> 'a trace set\<close> (\<open>\<up> _\<close> [80] 80) where
  \<open>\<up> t = { t \<frown> u | u. True }\<close>

lemma prefixes_extensions: \<open>t \<in> \<down> u \<longleftrightarrow> u \<in> \<up> t\<close>
  unfolding prefixes_def extensions_def by simp

interpretation prefixes: order \<open>\<lambda> t u. t \<in> \<down> u\<close> \<open>\<lambda> t u. t \<in> \<down> u \<and> t \<noteq> u\<close>
proof 
  (* Reflexivity *)
  fix x :: \<open>'a trace\<close> 
  show \<open>x \<in> \<down> x\<close>
    unfolding prefixes_def
    by (simp, metis trace.right_neutral)
next
  (* Strict Ordering *)
  fix x y :: \<open>'a trace\<close>
  show \<open>(x \<in> \<down> y \<and> x \<noteq> y) = (x \<in> \<down> y \<and> \<not> y \<in> \<down> x)\<close>
    unfolding prefixes_def
    by (simp, metis append.simps(3) append_is_empty(1) finite_empty_suffix 
                    trace.assoc trace.exhaust)
next
  (* Antisymmetry *)
  fix x y :: \<open>'a trace\<close>
  assume assms: \<open>x \<in> \<down> y\<close> \<open>y \<in> \<down> x\<close>
  show \<open>x = y\<close> 
  proof (cases \<open>y\<close>)
    case Finite note yfinite = this 
    show \<open>?thesis\<close>
    proof (cases \<open>x\<close>)
      case Finite
      with assms(2) obtain z where \<open>x = y \<frown> z\<close> 
        unfolding  prefixes_def
        by auto
      with assms(1) yfinite show \<open>?thesis\<close>
        unfolding  prefixes_def
        by (force simp: trace.assoc dest: finite_empty_suffix append_is_empty)
    qed (smt (verit, del_insts) CollectD append.simps(3) assms(1) prefixes_def)
  qed (smt (verit, del_insts) CollectD append.simps(3) assms(2) prefixes_def)
next
  (* Transitivity *)
  fix x y z :: \<open>'a trace\<close>
  assume \<open>x \<in> \<down> y\<close> \<open>y \<in> \<down> z\<close>
  then show \<open>x \<in> \<down> z\<close>
  unfolding  prefixes_def by (force simp: trace.assoc)
qed

lemma prefixes_empty_least : \<open>\<epsilon> \<in> \<down> t\<close>
  by (simp add: prefixes_def)
  
lemma prefixes_infinite_greatest : \<open>Infinite x \<in> \<down> t \<Longrightarrow> t = Infinite x\<close>
  by (simp add: prefixes_def)



lemma prefixes_finite : \<open>Finite xs \<in> \<down> Finite ys \<longleftrightarrow> (\<exists> zs. ys = xs @ zs)\<close>
proof (rule iffI)
  show \<open>Finite xs \<in> \<down> Finite ys \<Longrightarrow> \<exists>zs. ys = xs @ zs\<close>
    using finite_finite_suffix by (fastforce simp: prefixes_def)
next
  show \<open>\<exists>zs. ys = xs @ zs \<Longrightarrow> Finite xs \<in> \<down> Finite ys\<close>
    by (clarsimp simp: prefixes_def) (metis Traces.append.simps(2))
qed

lemma ttake_take : \<open>take n (ttake m t) = ttake (min n m) t\<close>
  by (cases \<open>t\<close>) (simp_all add: min_def take_map)

lemma tdrop_tdrop : \<open>tdrop n (tdrop m t) = tdrop (n + m) t\<close>
  by (cases \<open>t\<close>) (simp_all add: add.commute add.left_commute)


lemma tdrop_mono: \<open>t \<in> \<down> u \<Longrightarrow> tdrop k t \<in> \<down> tdrop k u\<close>
proof -
  { fix v assume A: \<open>u = t \<frown> v\<close> then have \<open>\<exists>va. tdrop k (t \<frown> v) = tdrop k t \<frown> va \<close>
  proof (cases \<open>t\<close>; cases \<open>v\<close>)
    fix x1 x2 assume \<open>t = Finite x1\<close> and \<open>v = Finite x2\<close> with A show \<open>?thesis\<close>
      by (simp, metis Traces.append.simps(2))
  next
    fix x1 x2 assume \<open>t = Finite x1\<close> and \<open>v = Infinite x2\<close> with A
     have \<open>tdrop k (t \<frown> v) = tdrop k t \<frown> Infinite (itdrop (k - length x1) x2) \<close>
      apply simp
      apply (rule ext)
      apply clarsimp
      apply (rule conjI)      
       apply (simp add: add.commute itdrop_def less_diff_conv)
      by (smt (z3) add.commute add_diff_cancel_left' add_diff_inverse_nat diff_is_0_eq' 
                   diff_right_commute itdrop_def linorder_not_less nat_less_le)
    then show \<open>\<exists>va. tdrop k (t \<frown> v) = tdrop k t \<frown> va\<close>
      by auto
  qed auto } note A = this
  assume \<open>t \<in> \<down> u\<close> with A show ?thesis unfolding prefixes_def by clarsimp
qed

lemma ttake_finite_prefixes : \<open>Finite xs \<in> \<down> t \<longleftrightarrow> xs = ttake (length xs) t\<close>
proof (rule iffI)
  show \<open>Finite xs \<in> \<down> t \<Longrightarrow> xs = ttake (length xs) t\<close>
    by (clarsimp simp: prefixes_def)
next
  show \<open>xs = ttake (length xs) t \<Longrightarrow> Finite xs \<in> \<down> t\<close>
    unfolding prefixes_def using ttake_tdrop
    by (metis (full_types) mem_Collect_eq)
qed

lemma ttake_prefixes : \<open>a \<le> b \<Longrightarrow> Finite (ttake a t) \<in> \<down> Finite (ttake b t)\<close>
  by (cases \<open>t\<close>; simp add: ttake_finite_prefixes min_def take_map)

lemma finite_directed:
assumes \<open> Finite xs \<in> \<down> t \<close> \<open> Finite ys \<in> \<down> t \<close>
shows \<open> \<exists>zs. (xs = ys @ zs) \<or> (ys = xs @ zs) \<close>
proof (cases \<open>length xs > length ys\<close>)
  case True
  with assms show \<open>?thesis\<close> 
    apply (simp add: ttake_finite_prefixes)
    using ttake_prefixes[simplified prefixes_finite]
    by (metis less_le_not_le) 
next
  case False
  from assms this[THEN leI] show \<open>?thesis\<close> 
    apply (simp add: ttake_finite_prefixes)
    using ttake_prefixes[simplified prefixes_finite]
    by (metis)
qed


lemma prefixes_directed: \<open>u \<in> \<down> t \<Longrightarrow> v \<in> \<down> t \<Longrightarrow> u \<in> \<down> v \<or> v \<in> \<down> u\<close>
proof (cases \<open>v\<close>; cases \<open>u\<close>)
  { fix a b assume \<open>Finite a \<in> \<down> t\<close> \<open>Finite b \<in> \<down> t\<close> 
  then have \<open>Finite a \<in> \<down> Finite b \<or> Finite b \<in> \<down> Finite a\<close>
    using finite_directed prefixes_finite by blast } note X = this
  fix a b show \<open>u \<in> \<down> t \<Longrightarrow> v \<in> \<down> t \<Longrightarrow> v = Finite a \<Longrightarrow> u = Finite b \<Longrightarrow> u \<in> \<down> v \<or> v \<in> \<down> u\<close> 
    using X by auto
qed (auto simp: prefixes_def dest: prefixes_infinite_greatest)

interpretation extensions: order \<open>\<lambda> t u. t \<in> \<up> u\<close> \<open>\<lambda> t u. t \<in> \<up> u \<and> t \<noteq> u\<close>
proof
qed (auto simp: prefixes_extensions[THEN sym] dest: prefixes.leD intro:prefixes.order.trans)

lemma extensions_infinite[simp]: \<open>\<up> Infinite xs = { Infinite xs }\<close>
  by (simp add: extensions_def)

lemma extensions_empty[simp]: \<open>\<up> \<epsilon> = UNIV\<close>
  by (simp add: extensions_def)

lemma prefixes_empty: \<open>\<down> \<epsilon> = {\<epsilon>}\<close>
  apply (clarsimp simp add: set_eq_iff \<epsilon>_def prefixes_def)
  apply (rule iffI)
  apply (metis \<epsilon>_def append_is_empty(1))
  by (metis \<epsilon>_def trace.left_neutral)


section \<open>Prefix Closure\<close>

definition prefix_closure :: \<open>'a trace set \<Rightarrow> 'a trace set\<close> (\<open>\<down>\<^sub>s _\<close> [80] 80) where
  \<open>\<down>\<^sub>s X = (\<Union> t \<in> X. prefixes t) \<close>

lemma prefix_closure_subset: \<open>X \<subseteq> \<down>\<^sub>s X\<close>
  unfolding prefix_closure_def
  by auto 

lemma prefix_closure_infinite: \<open>Infinite x \<in> \<down>\<^sub>s X \<longleftrightarrow> Infinite x \<in> X\<close>
proof
  assume \<open>Infinite x \<in> \<down>\<^sub>s X\<close> then show \<open>Infinite x \<in> X\<close>
    by (metis UN_E prefix_closure_def prefixes_infinite_greatest)
next
  assume \<open>Infinite x \<in> X\<close> then show \<open>Infinite x \<in> \<down>\<^sub>s X\<close>
    by (meson in_mono prefix_closure_subset)
qed

lemma prefix_closure_idem: \<open>\<down>\<^sub>s \<down>\<^sub>s X = \<down>\<^sub>s X\<close>
  unfolding prefix_closure_def
  using prefixes.order.trans by blast

lemma prefix_closure_mono: \<open>X \<subseteq> Y \<Longrightarrow> \<down>\<^sub>s X \<subseteq> \<down>\<^sub>s Y\<close>
  unfolding prefix_closure_def
  by blast

lemma prefix_closure_union_distrib: \<open>\<down>\<^sub>s (X \<union> Y) = \<down>\<^sub>s X \<union> \<down>\<^sub>s Y\<close>
  unfolding prefix_closure_def
  by simp

lemma prefix_closure_Union_distrib: \<open>\<down>\<^sub>s (\<Union> S) = \<Union> (prefix_closure ` S)\<close>
  unfolding prefix_closure_def
  by simp

lemma prefix_closure_Inter: \<open>\<down>\<^sub>s (\<Inter> (prefix_closure ` S)) = \<Inter> (prefix_closure ` S) \<close>
  unfolding prefix_closure_def
  using prefixes.dual_order.trans by fastforce

lemma prefix_closure_inter: \<open>\<down>\<^sub>s (\<down>\<^sub>s X \<inter> \<down>\<^sub>s Y) = \<down>\<^sub>s X \<inter> \<down>\<^sub>s Y\<close>
  by (rule prefix_closure_Inter[where S = \<open>{X,Y}\<close>, simplified])

lemma prefix_closure_UNIV: \<open>\<down>\<^sub>s UNIV = UNIV\<close>
  unfolding prefix_closure_def by blast

lemma prefix_closure_empty: \<open>\<down>\<^sub>s {} = {}\<close>
  unfolding prefix_closure_def by blast

lemma prefix_closure_extensions: \<open> \<down>\<^sub>s (\<up> t) = \<up> t \<union> \<down> t\<close>
  by (force intro: prefix_closure_subset dest: prefixes_directed
            simp: prefixes_extensions[THEN sym] prefix_closure_def)

lemma prefix_closure_prefixes: \<open>\<down>\<^sub>s (\<down> t) = \<down> t\<close>
  unfolding prefix_closure_def
  by (force intro: prefixes.dual_order.trans)

section \<open>Definitive Prefixes\<close>

definition dprefixes :: \<open>'a trace set \<Rightarrow> 'a trace set\<close>  (\<open>\<down>\<^sub>d _\<close> [80] 80) where
  \<open>\<down>\<^sub>d X = { t | t. \<up> t \<subseteq> \<down>\<^sub>s X }\<close>

lemma dprefixes_are_prefixes : \<open>\<down>\<^sub>d X \<subseteq> \<down>\<^sub>s X\<close>
  unfolding dprefixes_def
  using extensions.order.refl by blast

lemma prefix_closure_dprefixes : \<open>\<down>\<^sub>s (\<down>\<^sub>d X) \<subseteq> \<down>\<^sub>s X\<close>
  using dprefixes_are_prefixes prefix_closure_idem prefix_closure_mono 
  by blast

lemma dprefixes_idem: \<open>\<down>\<^sub>d \<down>\<^sub>d X = \<down>\<^sub>d X\<close>
proof
  show \<open>\<down>\<^sub>d \<down>\<^sub>d X \<subseteq> \<down>\<^sub>d X\<close>
    using prefix_closure_dprefixes 
    by (force simp: dprefixes_def)
next
  show \<open>\<down>\<^sub>d X \<subseteq> \<down>\<^sub>d \<down>\<^sub>d X\<close> 
    using extensions.order.trans prefix_closure_subset 
    by (force simp: dprefixes_def)
qed

lemma dprefixes_contains_extensions: \<open>t \<in> \<down>\<^sub>d X \<Longrightarrow> \<up> t \<subseteq> \<down>\<^sub>d X\<close>
  unfolding dprefixes_def
  using extensions.dual_order.trans by auto

lemma dprefixes_infinite: \<open>Infinite x \<in> \<down>\<^sub>d X \<longleftrightarrow> Infinite x \<in> X\<close>
proof
  show \<open>Infinite x \<in> X \<Longrightarrow> Infinite x \<in> \<down>\<^sub>d X\<close>
  unfolding dprefixes_def
  using prefix_closure_subset by fastforce
next
  show \<open>Infinite x \<in> \<down>\<^sub>d X \<Longrightarrow> Infinite x \<in> X\<close>
  unfolding dprefixes_def
  by (clarsimp simp: prefix_closure_infinite)
qed


lemma dprefixes_UNIV: \<open>\<down>\<^sub>d UNIV = UNIV\<close>
  unfolding dprefixes_def
  using prefix_closure_UNIV by force

lemma dprefixes_empty: \<open>\<down>\<^sub>d {} = {}\<close>
  unfolding dprefixes_def
  using prefix_closure_empty by blast

lemma dprefixes_Inter_distrib: \<open>\<down>\<^sub>d (\<Inter> S) \<subseteq> \<Inter> (dprefixes ` S)\<close>
  unfolding dprefixes_def prefix_closure_def
  by auto

lemma dprefixes_Inter: \<open>\<down>\<^sub>d (\<Inter> (dprefixes ` S)) = \<Inter> (dprefixes ` S)\<close>
proof
  show \<open>\<Inter> (dprefixes ` S) \<subseteq> \<down>\<^sub>d \<Inter> (dprefixes ` S)\<close>
    unfolding dprefixes_def prefix_closure_def
    using prefixes.order.refl extensions.dual_order.trans 
    by force
next
  show \<open>\<down>\<^sub>d \<Inter> (dprefixes ` S) \<subseteq> \<Inter> (dprefixes ` S)\<close>
    using dprefixes_idem  dprefixes_Inter_distrib 
    by blast
qed

lemma dprefixes_mono: 
  assumes \<open>X \<subseteq> Y\<close>
  shows \<open>\<down>\<^sub>d X \<subseteq> \<down>\<^sub>d Y\<close>
  using assms
  apply (simp add: dprefixes_def)
  apply (simp add: prefix_closure_def)
  apply (rule subsetI)
  using prefixes_extensions by blast


lemma dprefixes_inter: \<open>\<down>\<^sub>d (\<down>\<^sub>d X \<inter> \<down>\<^sub>d Y) = (\<down>\<^sub>d X \<inter> \<down>\<^sub>d Y)\<close>
  by (rule dprefixes_Inter[where S = \<open>{X,Y}\<close>, simplified])

lemma dprefixes_inter_distrib: \<open>\<down>\<^sub>d (X \<inter> Y) \<subseteq> \<down>\<^sub>d X \<inter> \<down>\<^sub>d Y\<close>
  using dprefixes_Inter_distrib[where S = \<open>{X,Y}\<close>] by auto

section \<open>Definitive Sets\<close>

definition definitive:: \<open>'a trace set \<Rightarrow> bool\<close> where
  \<open>definitive X \<longleftrightarrow> \<down>\<^sub>d X = X\<close>

lemma definitive_image: \<open>\<forall>X \<in> S. definitive X \<Longrightarrow> dprefixes ` S = S\<close>
  unfolding definitive_def by auto

lemma definitive_dprefixes: \<open>definitive (\<down>\<^sub>d X)\<close>
  unfolding definitive_def by (rule dprefixes_idem)

lemma definitive_contains_extensions: \<open>definitive X \<Longrightarrow> t \<in> X \<Longrightarrow> \<up> t \<subseteq> X\<close>
  unfolding definitive_def using dprefixes_contains_extensions by blast

lemma definitive_UNIV: \<open>definitive UNIV\<close>
  unfolding definitive_def by (rule dprefixes_UNIV)

lemma definitive_empty: \<open>definitive {}\<close>
  unfolding definitive_def by (rule dprefixes_empty)

lemma definitive_Inter: \<open>\<forall>X \<in> S. definitive X \<Longrightarrow> definitive (\<Inter> S)\<close>
  unfolding definitive_def using dprefixes_Inter definitive_image[simplified definitive_def]
  by metis

lemma definitive_inter: \<open>definitive X \<Longrightarrow> definitive Y \<Longrightarrow> definitive (X \<inter> Y)\<close>
  using definitive_Inter[where S = \<open>{X,Y}\<close>, simplified] by blast

lemma definitive_infinite_extension:
  assumes \<open>definitive X\<close> and \<open>t \<in> X\<close> 
  shows \<open>\<exists> f. Infinite f \<in> X \<and> t \<in> \<down> Infinite f\<close>
using assms proof (cases \<open>t\<close>)
  case (Finite xs) then show \<open>?thesis\<close>
    apply (intro exI[where x=\<open>\<lambda>n. if n < length xs then xs!n else undefined\<close>])
    by (force simp:   prefixes_extensions[THEN sym] prefixes_def 
              intro!: definitive_contains_extensions[THEN subsetD, OF assms] 
              intro:  exI[where x=\<open>Infinite (\<lambda>_. undefined)\<close>])
qed auto

lemma definitive_elemI:
  assumes \<open>definitive X\<close> \<open>\<up> t \<subseteq> \<down>\<^sub>s X\<close> 
  shows \<open>t \<in> X\<close>
  using assms
  by (auto simp add: definitive_def dprefixes_def)


definition dUnion :: \<open>'a trace set set \<Rightarrow> 'a trace set\<close> (\<open>\<Union>\<^sub>d\<close>) where
  \<open>\<Union>\<^sub>d X = \<down>\<^sub>d \<Union> X\<close>

abbreviation dunion :: \<open>'a trace set \<Rightarrow> 'a trace set \<Rightarrow> 'a trace set\<close>  (infixl \<open>\<union>\<^sub>d\<close> 65) where
  \<open>X \<union>\<^sub>d Y \<equiv> \<Union>\<^sub>d {X,Y}\<close>

lemma dprefixes_dUnion: \<open>\<down>\<^sub>d \<Union>\<^sub>d S = \<Union>\<^sub>d S\<close>
  by (simp add: dUnion_def dprefixes_idem)

lemma definitive_dUnion: \<open>definitive (\<Union>\<^sub>d S)\<close>
  by (simp add: dprefixes_dUnion definitive_def)

lemma dUnion_contains_dprefixes: \<open>t \<in> S \<Longrightarrow> \<down>\<^sub>d t \<subseteq> \<Union>\<^sub>d S\<close>
  by (auto simp: dUnion_def dprefixes_def prefix_closure_def)

lemma dUnion_contains_definitive: \<open>X \<in> S \<Longrightarrow> definitive X \<Longrightarrow> X \<subseteq> \<Union>\<^sub>d S\<close>
  unfolding definitive_def
  using dUnion_contains_dprefixes by blast

lemma dUnion_empty[simp]: \<open>\<Union>\<^sub>d {} = {}\<close>
  unfolding dUnion_def
  by (simp add: dprefixes_empty)

lemma dUnion_least_dprefixes: \<open>(\<And>X. X \<in> S \<Longrightarrow> X \<subseteq> \<down>\<^sub>d Z) \<Longrightarrow>  \<down>\<^sub>d (\<Union> (dprefixes ` S)) \<subseteq> \<down>\<^sub>d Z\<close>
  unfolding dprefixes_def prefix_closure_def
  by (simp add: subset_iff, meson extensions.order_refl prefixes.order.trans)

lemma dUnion_least_definitive: 
  assumes all_defn: \<open>\<forall>X \<in> S. definitive X\<close>
  shows \<open>(\<And>X. X \<in> S \<Longrightarrow> X \<subseteq> Z) \<Longrightarrow> definitive Z \<Longrightarrow> \<down>\<^sub>d \<Union> S \<subseteq> Z\<close>
  using  definitive_image[OF all_defn,THEN sym] dUnion_least_dprefixes definitive_def
  by metis

section \<open>A type for definitive sets\<close>

typedef 'a dset = \<open>{p :: 'a trace set. definitive p }\<close>
  using definitive_UNIV by blast

setup_lifting type_definition_dset

lift_definition Inter_dset :: \<open>'a dset set \<Rightarrow> 'a dset\<close> (\<open>\<Sqinter>\<close>) is \<open>\<lambda> ss. \<Inter> ss\<close>
  by (simp add: definitive_Inter)

abbreviation inter_dset :: \<open>'a dset \<Rightarrow> 'a dset \<Rightarrow> 'a dset\<close>  (infixl \<open>\<sqinter>\<close> 66)  where
  \<open>X \<sqinter> Y \<equiv> \<Sqinter> {X,Y}\<close>

lift_definition Union_cset :: \<open>'a dset set \<Rightarrow> 'a dset\<close> (\<open>\<Squnion>\<close>) is \<open>\<lambda> ss. \<Union>\<^sub>d ss\<close>
  by (rule definitive_dUnion)

abbreviation union_dset :: \<open>'a dset \<Rightarrow> 'a dset \<Rightarrow> 'a dset\<close>  (infixl \<open>\<squnion>\<close> 65)  where
  \<open>X \<squnion> Y \<equiv> \<Squnion> {X,Y}\<close>

lift_definition empty_dset :: \<open>'a dset\<close> (\<open>\<emptyset>\<close>) is \<open>{}\<close>
  by (rule definitive_empty)

lift_definition univ_dset :: \<open>'a dset\<close> (\<open>\<Sigma>\<infinity>\<close>) is \<open>UNIV\<close> 
  by (rule definitive_UNIV)

lift_definition subset_dset :: \<open>'a dset \<Rightarrow> 'a dset \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<close> 50) is \<open>(\<subseteq>)\<close> 
  done

lift_definition strict_subset_cset :: \<open>'a dset \<Rightarrow> 'a dset \<Rightarrow> bool\<close>  (infix \<open>\<sqsubset>\<close> 50) is \<open>(\<subset>)\<close> 
  done

lift_definition in_dset :: \<open>'a trace \<Rightarrow> 'a dset \<Rightarrow> bool\<close> is \<open>(\<in>)\<close>
  done

lift_definition notin_dset :: \<open>'a trace \<Rightarrow> 'a dset \<Rightarrow> bool\<close> is \<open>(\<notin>)\<close>
  done



lemma in_dset_\<epsilon>: \<open>in_dset \<epsilon> A \<Longrightarrow> A = \<Sigma>\<infinity>\<close>
  apply (transfer)
  using definitive_contains_extensions extensions_empty by blast

lemma in_dset_UNIV: \<open>in_dset x \<Sigma>\<infinity>\<close>
  by (transfer, simp)

lemma in_dset_subset: \<open>A \<sqsubseteq> B \<Longrightarrow> in_dset x A \<Longrightarrow> in_dset x B\<close>
  by (transfer, auto)

lemma in_dset_inter: \<open>in_dset x A \<Longrightarrow> in_dset x B \<Longrightarrow> in_dset x (A \<sqinter> B)\<close>
  by (transfer, simp)


interpretation dset: complete_lattice \<open>\<Sqinter>\<close> \<open>\<Squnion>\<close> \<open>(\<sqinter>)\<close> \<open>(\<sqsubseteq>)\<close> \<open>(\<sqsubset>)\<close> \<open>(\<squnion>)\<close> \<open>\<emptyset>\<close> \<open>\<Sigma>\<infinity>\<close>
proof (unfold_locales;transfer)
  fix X Y Z :: \<open>'a trace set\<close> assume \<open>definitive X\<close> \<open>definitive Y\<close> \<open>definitive Z\<close>
  then show \<open> Y \<subseteq> X \<Longrightarrow> Z \<subseteq> X \<Longrightarrow> (Y \<union>\<^sub>d Z) \<subseteq> X\<close>
    by (metis dUnion_def dUnion_least_definitive insert_iff singletonD)
next
  fix A :: \<open>'a trace set set\<close> and Z :: \<open>'a trace set\<close> 
  assume \<open>\<forall>X\<in>A. definitive X\<close> \<open>definitive Z\<close> \<open>(\<And>X. definitive X \<Longrightarrow> X \<in> A \<Longrightarrow> X \<subseteq> Z)\<close>
  then show \<open>\<Union>\<^sub>d A \<subseteq> Z\<close>
    by (simp add: dUnion_def dUnion_least_definitive)
qed (auto simp: dUnion_contains_definitive)

section \<open>Isomorphism of definitive sets and LTL properties\<close>

definition infinites :: \<open>'a trace set \<Rightarrow> 'a infinite_trace set\<close> where
  \<open>infinites X = (\<Union>x \<in> X. case x of Finite xs \<Rightarrow> {} | Infinite xs \<Rightarrow> {xs})\<close>

lemma infinites_alt: \<open>Infinite ` infinites A = A \<inter> range Infinite\<close>
unfolding set_eq_iff proof 
  fix x { assume \<open> (x \<in> Infinite ` infinites A)\<close> hence \<open> (x \<in> A \<inter> range Infinite) \<close>
    by (clarsimp simp: infinites_def split!: trace.split_asm)
  } moreover { assume \<open> (x \<in> A \<inter> range Infinite) \<close> hence \<open> (x \<in> Infinite ` infinites A) \<close>
      by (force simp: infinites_def split!: trace.split intro!: imageI)
  } ultimately show \<open> (x \<in> Infinite ` infinites A) = (x \<in> A \<inter> range Infinite)\<close>
    by blast
qed

lemma infinites_append_right: \<open>t \<frown> Infinite \<omega> \<in> range Infinite\<close>
  by (cases \<open>t\<close>; auto)

lemma infinites_prefix_closure:
  assumes \<open>definitive X\<close>
  shows \<open>\<down>\<^sub>s Infinite ` infinites X = \<down>\<^sub>s X\<close>
  unfolding prefix_closure_def infinites_def
  using definitive_infinite_extension[OF assms] prefixes.order.trans 
  by (force split: trace.split_asm)

lemma infinites_UNIV[simp]: \<open>infinites UNIV = UNIV\<close>
 by (auto simp: infinites_def split: trace.split)

lemma infinites_empty[simp]: \<open>infinites {} = {}\<close>
  by (auto simp: infinites_def)
 
lemma infinites_Inter: \<open>infinites (\<Inter> S) = \<Inter> (infinites ` S)\<close>
  unfolding infinites_def
  apply (rule set_eqI; rule iffI)
   apply (force)
   apply (simp split: trace.split trace.split_asm)
  by (metis InterI trace.distinct(1) trace.exhaust trace.inject(2))

lemma infinites_Union: \<open>infinites (\<Union> S) = \<Union> (infinites ` S)\<close>
  unfolding infinites_def
  by auto

lemma infinites_dprefixes: \<open>infinites (\<down>\<^sub>d X) = infinites X\<close>
  unfolding infinites_def
   by (force simp: dprefixes_infinite split: trace.split trace.split_asm)

lemma infinites_dprefixes_Infinite: \<open>infinites (\<down>\<^sub>d Infinite ` X) = X\<close>
proof
  show \<open>infinites (\<down>\<^sub>d Infinite ` X) \<subseteq> X\<close>
    unfolding infinites_def
    using prefixes_infinite_greatest
    by (force split: trace.split_asm simp: dprefixes_def prefix_closure_def)
next
  show \<open>X \<subseteq> infinites (\<down>\<^sub>d Infinite ` X)\<close>
    by (force simp: infinites_def dprefixes_def prefix_closure_def split: trace.split)
qed

lift_definition property :: \<open>'a dset \<Rightarrow> 'a infinite_trace set\<close> is \<open>infinites\<close>
  done

lift_definition definitives :: \<open>'a infinite_trace set \<Rightarrow> 'a dset\<close> is \<open>\<lambda>x. \<down>\<^sub>d (Infinite ` x)\<close>
  by (rule definitive_dprefixes)

lemma property_inverse: \<open>property (definitives X) = X\<close>
  by (transfer, simp add: infinites_dprefixes_Infinite)

lemma definitives_inverse: \<open>definitives (property X) = X\<close>
proof (rule dset.order_antisym)
  show \<open>definitives (property X) \<sqsubseteq> X\<close>
    by (transfer, force simp: dprefixes_def infinites_prefix_closure 
                        intro: definitive_elemI)
next
  show \<open>X \<sqsubseteq> definitives (property X)\<close>
    apply transfer
    using definitive_contains_extensions definitive_infinite_extension 
    by (force simp: dprefixes_def prefix_closure_def infinites_def)
qed

lemma definitives_mono: \<open>A \<subseteq> B \<Longrightarrow> definitives A \<sqsubseteq> definitives B\<close>
  by (transfer, metis dprefixes_inter_distrib image_mono inf.order_iff le_infE)

lemma property_mono: \<open>A \<sqsubseteq> B \<Longrightarrow> property A \<subseteq> property B\<close>
  by (transfer, auto simp: infinites_def)

lemma definitives_reflecting: \<open>definitives A \<sqsubseteq> definitives B \<Longrightarrow> A \<subseteq> B\<close>
  using property_inverse property_mono by metis

lemma completions_reflecting: \<open>property A \<subseteq> property B \<Longrightarrow> A \<sqsubseteq> B\<close>
  using definitives_inverse definitives_mono by metis

lemma property_Inter: \<open>property (\<Sqinter> S) = \<Inter> (property ` S)\<close>
  by (transfer, simp add: infinites_Inter)

lemma property_Union: \<open>property (\<Squnion> S) = \<Union> (property ` S)\<close>
  by (transfer, simp add: dUnion_def infinites_dprefixes infinites_Union)



interpretation dset: complete_distrib_lattice \<open>\<Sqinter>\<close> \<open>\<Squnion>\<close> \<open>(\<sqinter>)\<close> \<open>(\<sqsubseteq>)\<close> \<open>(\<sqsubset>)\<close> \<open>(\<squnion>)\<close> \<open>\<emptyset>\<close> \<open>\<Sigma>\<infinity>\<close>
  by (unfold_locales)
     (auto intro: completions_reflecting simp add: property_Inter property_Union INF_SUP_set)


definition iprepend :: \<open>'a infinite_trace set \<Rightarrow> 'a infinite_trace set\<close> where
  \<open>iprepend X = {t. itdrop 1 t \<in> X }\<close>

lemma iprepend_itdrop: \<open>itdrop k x \<in> iprepend B \<longleftrightarrow> itdrop (Suc k) x \<in> B\<close>
  by (simp add: iprepend_def)

lemmas iprepend_itdrop_0[simp] = iprepend_itdrop[where k = \<open>0\<close>,simplified]

definition prepend' :: \<open>'a trace set \<Rightarrow> 'a trace set\<close> where
  \<open>prepend' X = {t. tdrop 1 t \<in> X }\<close>

lemma trace_uncons_cases [case_names Cons Nil]: 
  assumes \<open>\<And>\<sigma> t. x = singleton \<sigma> \<frown> t \<Longrightarrow> P\<close> 
  and \<open>x = \<epsilon> \<Longrightarrow> P\<close> 
  shows \<open>P\<close>
proof (cases \<open>x\<close>)
  case (Finite xs)
  then show \<open>?thesis\<close> 
    by (cases \<open>xs\<close>; 
        force simp: assms(2)[simplified \<epsilon>_def] 
              intro: assms(1)[where t = \<open>Finite ts\<close> for ts,
                     simplified singleton_def append.simps List.append.simps])
next
  case (Infinite f) note A = this
  have \<open>f = (\<lambda>n. if n = 0 then [f 0] ! n else (f \<circ> Suc) (n - length [f 0]))\<close>
    by (rule ext, simp)
  with A show \<open>?thesis\<close> 
    using assms(1)[where \<sigma> = \<open>f 0\<close> and t = \<open>Infinite (f \<circ> Suc)\<close>,
                   simplified singleton_def append.simps, simplified]
    by simp
qed

lemma append_prefixes_left: \<open>a \<in> \<down> b \<Longrightarrow> c \<frown> a \<in> \<down> c \<frown> b\<close>
  by (simp add: prefixes_def) (metis trace.assoc)

lemma tdrop_singleton_append[simp]: \<open>tdrop (Suc n) (singleton \<sigma> \<frown> t) = tdrop n t\<close>
  by (cases \<open>t\<close>, simp_all add: singleton_def itdrop_def)
lemma tdrop_zero[simp]: \<open>tdrop 0 t = t\<close>
  by (cases \<open>t\<close>; simp)
lemma tdrop_\<epsilon>[simp]: \<open>tdrop k \<epsilon> = \<epsilon>\<close>
  by (simp add: \<epsilon>_def)

lemma prepend'_prefix_closure: \<open>\<down>\<^sub>s (prepend' X) \<subseteq> prepend' (\<down>\<^sub>s X)\<close>
proof (rule subsetI)
  fix x 
  assume A: \<open> x \<in> \<down>\<^sub>s prepend' X\<close> 
  show \<open>x \<in> prepend' (\<down>\<^sub>s X) \<close>
  proof (cases \<open>x\<close> rule: trace_uncons_cases)
    case (Cons \<sigma> t)
    with A show \<open>?thesis\<close> 
      unfolding prefix_closure_def prepend'_def prefixes_def 
      by (fastforce simp: trace.assoc)
  next
    case Nil
    with A show \<open>?thesis\<close> 
      unfolding prefix_closure_def prepend'_def
      by (force simp: prefixes_empty_least)
  qed
qed

lemma prepend'_dprefixes : 
assumes \<open>definitive X\<close>
shows \<open>\<down>\<^sub>d prepend' X = prepend' X\<close>
proof
  show \<open>\<down>\<^sub>d prepend' X \<subseteq> prepend' X\<close>
  proof (rule subsetI)
    fix x assume A: \<open>x \<in> \<down>\<^sub>d prepend' X\<close> show \<open>x \<in> prepend' X\<close>
    proof (cases \<open>x\<close> rule: trace_uncons_cases)
      case (Cons \<sigma> t)
      with A show \<open>?thesis\<close> 
        unfolding dprefixes_def
        apply (subst assms[simplified definitive_def, THEN sym])
        apply (clarsimp dest!: subset_trans[OF _ prepend'_prefix_closure])
        using append_prefixes_left 
        by (force simp: dprefixes_def prepend'_def prefix_closure_def subset_iff 
                        prefixes_extensions[THEN sym])
    next
      case Nil
      with A show \<open>?thesis\<close> 
        apply (subst assms[simplified definitive_def, THEN sym])
        apply (clarsimp simp: prefixes_empty_least prefixes_def dprefixes_def 
                              prepend'_def prefix_closure_def subset_iff
                              prefixes_extensions[THEN sym])
        by (metis tdrop_singleton_append tdrop_zero trace.assoc)
    qed
  qed
next
  show \<open>prepend' X \<subseteq> \<down>\<^sub>d prepend' X\<close>
  proof (rule subsetI)
    fix x assume A: \<open>x \<in> prepend' X\<close> show \<open>x \<in> \<down>\<^sub>d prepend' X\<close>
    proof (cases \<open>x\<close> rule: trace_uncons_cases)
      case (Cons \<sigma> t)
      with A show \<open>?thesis\<close>
        by (clarsimp simp: dprefixes_def prefixes_def prepend'_def 
                              prefix_closure_def prefixes_extensions[THEN sym])
           (metis (mono_tags, lifting) assms definitive_contains_extensions 
                  mem_Collect_eq prefixes_def prefixes_extensions subset_eq 
                  tdrop_singleton_append tdrop_zero trace.assoc)
    next
      case Nil
      with A show \<open>?thesis\<close>
        using assms definitive_contains_extensions 
        by (force simp: dprefixes_def prepend'_def prefix_closure_def)
    qed
  qed
qed

lemma prepend'_definitive : 
  assumes \<open>definitive X\<close> 
  shows \<open>definitive (prepend' X)\<close>
  unfolding definitive_def using assms
  by (rule prepend'_dprefixes)

lift_definition prepend :: \<open>'a dset \<Rightarrow> 'a dset\<close> is \<open>prepend'\<close>
  by (rule prepend'_definitive)

lemma prepend_Inter: \<open>\<Sqinter> (prepend ` S) = prepend (\<Sqinter> S)\<close>
  apply transfer
  by (auto simp add: prepend'_def)

lemma in_dset_prependD: \<open>in_dset (Finite [a] \<frown> x) (prepend A) \<Longrightarrow> in_dset x A\<close>
  by (transfer, metis One_nat_def Traces.singleton_def mem_Collect_eq prepend'_def 
                      tdrop_singleton_append tdrop_zero)

lemma in_dset_prependI: \<open>in_dset x A \<Longrightarrow> in_dset (Finite [a] \<frown> x) (prepend A)\<close>
  by (transfer, metis One_nat_def Traces.singleton_def mem_Collect_eq prepend'_def 
                      tdrop_singleton_append tdrop_zero)

lemma prepend'_mono: 
  assumes \<open>A \<subseteq> B\<close> 
  shows   \<open>prepend' A \<subseteq> prepend' B\<close>
  using assms unfolding prepend'_def
  by blast

lemma property_prepend: \<open>property (prepend X) = iprepend (property X)\<close>
  apply transfer
  by (clarsimp simp: definitive_def infinites_def prepend'_def 
               split!: trace.split_asm trace.split intro!: set_eqI; 
      blast)

lemma iprepend_Union: \<open>\<Union> (iprepend ` S) = iprepend (\<Union> S)\<close>
  by fastforce

lemma definitives_inverse_eqI: \<open>definitives (property X) = definitives (property Y) \<Longrightarrow> X = Y\<close>
  by (simp add: definitives_inverse)

lemma prepend_Union: \<open>\<Squnion> (prepend ` S) = prepend (\<Squnion> S)\<close>
  apply (rule definitives_inverse_eqI)
  apply (simp add: property_Union property_prepend)
  by (metis UN_extend_simps(10) iprepend_Union)

lemma non_empty_trace: \<open> x \<noteq> \<epsilon> \<longleftrightarrow> (\<exists>\<sigma> x'. x = Finite [\<sigma>] \<frown> x')\<close>
  apply (cases \<open>x\<close> rule: trace_uncons_cases; clarsimp)
   apply (metis Traces.singleton_def \<epsilon>_def append_is_empty(1) not_Cons_self2 trace.inject(1))
  by (metis \<epsilon>_def append_is_empty(1) list.discI trace.inject(1))

lemma thead_append: \<open>x \<noteq> \<epsilon> \<Longrightarrow> thead (x \<frown> y) = thead x\<close>
  by (cases \<open>x\<close>; cases \<open>y\<close>; simp add: \<epsilon>_def nth_append)

lemma thead_prefix: \<open> x \<in> \<down> y \<Longrightarrow> x \<noteq> \<epsilon> \<Longrightarrow> thead x = thead y\<close>
  apply (simp add: prefixes_def non_empty_trace)
  using thead_append [where x = \<open>Finite [_]\<close>, simplified \<epsilon>_def, simplified]
  by (metis append_is_empty(1) thead_append)

lemma compr'_inter_thead: 
    \<open>\<down>\<^sub>d {x. x \<noteq> \<epsilon> \<and> P (thead x)} \<inter> \<down>\<^sub>d {x.  x \<noteq> \<epsilon> \<and> Q (thead x)} 
   = \<down>\<^sub>d {x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> Q (thead x)}\<close>
proof (rule antisym)
{ fix x t
  assume \<open>\<forall>t. x \<in> \<down> t \<longrightarrow> (\<exists>x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> t \<in> \<down> x)\<close>
  and    \<open>\<forall>t. x \<in> \<down> t \<longrightarrow> (\<exists>x. x \<noteq> \<epsilon> \<and> Q (thead x) \<and> t \<in> \<down> x)\<close>
  and    \<open>x \<in> \<down> t\<close>
  then have \<open> \<exists>x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> Q (thead x) \<and> t \<in> \<down> x\<close>
    by (cases \<open>t = \<epsilon>\<close>; fastforce dest: thead_prefix simp: prefixes_empty prefixes_empty_least)
} then show \<open>\<down>\<^sub>d {x. x \<noteq> \<epsilon> \<and> P (thead x)} \<inter> \<down>\<^sub>d {x.  x \<noteq> \<epsilon> \<and> Q (thead x)} \<subseteq> \<down>\<^sub>d {x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> Q (thead x)}\<close> 
  by (clarsimp simp: set_eq_iff subset_iff dprefixes_def prefix_closure_def prefixes_extensions[THEN sym])
next
{ fix x
  assume \<open> \<forall>t. x \<in> \<down> t \<longrightarrow> (\<exists>x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> Q (thead x) \<and> t \<in> \<down> x)\<close>
  then have \<open>(\<forall>t. x \<in> \<down> t \<longrightarrow> (\<exists>x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> t \<in> \<down> x)) \<and>
             (\<forall>t. x \<in> \<down> t \<longrightarrow> (\<exists>x. x \<noteq> \<epsilon> \<and> Q (thead x) \<and> t \<in> \<down> x))\<close>
    by fastforce }
  then show \<open>\<down>\<^sub>d {x. x \<noteq> \<epsilon> \<and> P (thead x)} \<inter> \<down>\<^sub>d {x.  x \<noteq> \<epsilon> \<and> Q (thead x)} \<supseteq> \<down>\<^sub>d {x. x \<noteq> \<epsilon> \<and> P (thead x) \<and> Q (thead x)}\<close> 
  by (clarsimp simp: set_eq_iff subset_iff dprefixes_def prefix_closure_def prefixes_extensions[THEN sym])
qed

lift_definition compr :: \<open>('a trace \<Rightarrow> bool) \<Rightarrow> 'a dset\<close> is \<open>\<lambda>p. \<down>\<^sub>d {x. p x }\<close>
  by (rule definitive_dprefixes)


lift_definition complement :: \<open>'a dset \<Rightarrow> 'a dset\<close> is \<open>\<lambda>p. \<down>\<^sub>d (range Infinite - p)\<close>
  by (rule definitive_dprefixes)


lemma property_complement[simp]: \<open>property (complement X) = UNIV - property X\<close>
  by (transfer, force simp: infinites_dprefixes[simplified infinites_def] infinites_def 
                      split: trace.split_asm trace.split)

end
