section \<open>Library additions\<close>

theory Library_Additions
  imports "ZFC_in_HOL.Ordinal_Exp" "HOL-Library.Ramsey" "Nash_Williams.Nash_Williams"

begin

subsection \<open>Already in the development version\<close>

declare \<omega>_gt0 [simp]

lemma irrefl_less_than: "irrefl less_than"
  using irrefl_def by blast

lemma total_on_less_than [simp]: "total_on A less_than"
  using total_on_def by force+

lemma takeWhile_eq_Nil_iff: "takeWhile P xs = [] \<longleftrightarrow> xs = [] \<or> \<not>P (hd xs)"
by (cases xs) auto

lemma lenlex_append1:
  assumes len: "(us,xs) \<in> lenlex R" and eq: "length vs = length ys" 
  shows "(us @ vs, xs @ ys) \<in> lenlex R"
  using len
proof (induction us)
  case Nil
  then show ?case 
    by (simp add: lenlex_def eq)
next
  case (Cons u us)
  with lex_append_rightI show ?case
    by (fastforce simp add: lenlex_def eq)
qed

lemma lenlex_append2 [simp]:
  assumes "irrefl R"
  shows "(us @ xs, us @ ys) \<in> lenlex R \<longleftrightarrow> (xs, ys) \<in> lenlex R"
proof (induction us)
  case Nil
  then show ?case 
    by (simp add: lenlex_def)
next
  case (Cons u us)
  with assms show ?case
    by (auto simp: lenlex_def irrefl_def)
qed

lemma hd_concat: "\<lbrakk>xs \<noteq> []; hd xs \<noteq> []\<rbrakk> \<Longrightarrow> hd (concat xs) = hd (hd xs)"
  by (metis concat.simps(2) hd_Cons_tl hd_append2)

lemma sorted_list_of_set_lessThan_Suc [simp]: 
  "sorted_list_of_set {..<Suc k} = sorted_list_of_set {..<k} @ [k]"
proof -
  have "sorted_wrt (<) (sorted_list_of_set {..<k} @ [k])"
    unfolding sorted_wrt_append  by (auto simp flip: strict_sorted_sorted_wrt)
  then show ?thesis
    by (simp add: lessThan_atLeast0)
qed

lemma finite_enumerate_in_set: "\<lbrakk>finite S; n < card S\<rbrakk> \<Longrightarrow> enumerate S n \<in> S"
proof (induction n arbitrary: S)
  case 0
  then show ?case
    by (metis all_not_in_conv card_empty enumerate.simps(1) not_less0 wellorder_Least_lemma(1))
next
  case (Suc n)
  show ?case
    using Suc.prems Suc.IH [of "S - {LEAST n. n \<in> S}"]
    apply (simp add: enumerate.simps)
    by (metis Diff_empty Diff_insert0 Suc_lessD card.remove less_Suc_eq)
qed

lemma finite_enumerate_step: "\<lbrakk>finite S; Suc n < card S\<rbrakk> \<Longrightarrow> enumerate S n < enumerate S (Suc n)"
proof (induction n arbitrary: S)
  case 0
  then have "enumerate S 0 \<le> enumerate S (Suc 0)"
    by (simp add: Least_le enumerate.simps(1) finite_enumerate_in_set)
  moreover have "enumerate (S - {enumerate S 0}) 0 \<in> S - {enumerate S 0}"
    by (metis 0 Suc_lessD Suc_less_eq card_Suc_Diff1 enumerate_in_set finite_enumerate_in_set)
  then have "enumerate S 0 \<noteq> enumerate (S - {enumerate S 0}) 0"
    by auto
  ultimately show ?case
    by (simp add: enumerate_Suc')
next
  case (Suc n)
  then show ?case
    by (simp add: enumerate_Suc' finite_enumerate_in_set)
qed

lemma finite_enumerate_mono: "\<lbrakk>m < n; finite S; n < card S\<rbrakk> \<Longrightarrow> enumerate S m < enumerate S n"
  by (induct m n rule: less_Suc_induct) (auto intro: finite_enumerate_step)

lemma finite_enumerate_Suc'':
  fixes S :: "'a::wellorder set"
  assumes "finite S" "Suc n < card S"
  shows "enumerate S (Suc n) = (LEAST s. s \<in> S \<and> enumerate S n < s)"
  using assms
proof (induction n arbitrary: S)
  case 0
  then have "\<forall>s \<in> S. enumerate S 0 \<le> s"
    by (auto simp: enumerate.simps intro: Least_le)
  then show ?case
    unfolding enumerate_Suc' enumerate_0[of "S - {enumerate S 0}"]
    by (metis Diff_iff dual_order.strict_iff_order singletonD singletonI)
next
  case (Suc n S)
  then have "Suc n < card (S - {enumerate S 0})"
    using Suc.prems(2) finite_enumerate_in_set by force
  then show ?case
    apply (subst (1 2) enumerate_Suc')
    apply (simp add: Suc)
    apply (intro arg_cong[where f = Least] HOL.ext)
    using finite_enumerate_mono[OF zero_less_Suc \<open>finite S\<close>, of n] Suc.prems
    by (auto simp flip: enumerate_Suc')
qed

lemma finite_enumerate_initial_segment:
  fixes S :: "'a::wellorder set"
  assumes "finite S" and n: "n < card (S \<inter> {..<s})"
  shows "enumerate (S \<inter> {..<s}) n = enumerate S n"
  using n
proof (induction n)
  case 0
  have "(LEAST n. n \<in> S \<and> n < s) = (LEAST n. n \<in> S)"
  proof (rule Least_equality)
    have "\<exists>t. t \<in> S \<and> t < s"
      by (metis "0" card_gt_0_iff disjoint_iff_not_equal lessThan_iff)
    then show "(LEAST n. n \<in> S) \<in> S \<and> (LEAST n. n \<in> S) < s"
      by (meson LeastI Least_le le_less_trans)
  qed (simp add: Least_le)
  then show ?case
    by (auto simp: enumerate_0)
next
  case (Suc n)
  then have less_card: "Suc n < card S"
    by (meson assms(1) card_mono inf_sup_ord(1) leD le_less_linear order.trans)
  obtain T where T: "T \<in> {s \<in> S. enumerate S n < s}"
    by (metis Infinite_Set.enumerate_step enumerate_in_set finite_enumerate_in_set finite_enumerate_step less_card mem_Collect_eq)
  have "(LEAST x. x \<in> S \<and> x < s \<and> enumerate S n < x) = (LEAST x. x \<in> S \<and> enumerate S n < x)"
       (is "_ = ?r")
  proof (intro Least_equality conjI)
    show "?r \<in> S"
      by (metis (mono_tags, lifting) LeastI mem_Collect_eq T)
    have "\<not> s \<le> ?r"
      using not_less_Least [of _ "\<lambda>x. x \<in> S \<and> enumerate S n < x"] Suc assms
      by (metis (mono_tags, lifting) Int_Collect Suc_lessD finite_Int finite_enumerate_in_set finite_enumerate_step lessThan_def less_le_trans)
    then show "?r < s"
      by auto
    show "enumerate S n < ?r"
      by (metis (no_types, lifting) LeastI mem_Collect_eq T)
  qed (auto simp: Least_le)
  then show ?case
    using Suc assms by (simp add: finite_enumerate_Suc'' less_card)
qed

lemma finite_enumerate_Ex:
  fixes S :: "'a::wellorder set"
  assumes S: "finite S"
    and s: "s \<in> S"
  shows "\<exists>n<card S. enumerate S n = s"
  using s S
proof (induction s arbitrary: S rule: less_induct)
  case (less s)
  show ?case
  proof (cases "\<exists>y\<in>S. y < s")
    case True
    let ?T = "S \<inter> {..<s}"
    have "finite ?T"
      using less.prems(2) by blast
    have TS: "card ?T < card S"
      using less.prems by (blast intro: psubset_card_mono [OF \<open>finite S\<close>])
    from True have y: "\<And>x. Max ?T < x \<longleftrightarrow> (\<forall>s'\<in>S. s' < s \<longrightarrow> s' < x)"
      by (subst Max_less_iff) (auto simp: \<open>finite ?T\<close>)
    then have y_in: "Max ?T \<in> {s'\<in>S. s' < s}"
      using Max_in \<open>finite ?T\<close> by fastforce
    with less.IH[of "Max ?T" ?T] obtain n where n: "enumerate ?T n = Max ?T" "n < card ?T"
      using \<open>finite ?T\<close> by blast
    then have "Suc n < card S"
      using TS less_trans_Suc by blast
    with S n have "enumerate S (Suc n) = s"
      by (subst finite_enumerate_Suc'') (auto simp: y finite_enumerate_initial_segment less finite_enumerate_Suc'' intro!: Least_equality)
    then show ?thesis
      using \<open>Suc n < card S\<close> by blast
  next
    case False
    then have "\<forall>t\<in>S. s \<le> t" by auto
    moreover have "0 < card S"
      using card_0_eq less.prems by blast
    ultimately show ?thesis
      using \<open>s \<in> S\<close>
      by (auto intro!: exI[of _ 0] Least_equality simp: enumerate_0)
  qed
qed

lemma finite_bij_enumerate:
  fixes S :: "'a::wellorder set"
  assumes S: "finite S"
  shows "bij_betw (enumerate S) {..<card S} S"
proof -
  have "\<And>n m. \<lbrakk>n \<noteq> m; n < card S; m < card S\<rbrakk> \<Longrightarrow> enumerate S n \<noteq> enumerate S m"
    using finite_enumerate_mono[OF _ \<open>finite S\<close>] by (auto simp: neq_iff)
  then have "inj_on (enumerate S) {..<card S}"
    by (auto simp: inj_on_def)
  moreover have "\<forall>s \<in> S. \<exists>i<card S. enumerate S i = s"
    using finite_enumerate_Ex[OF S] by auto
  moreover note \<open>finite S\<close>
  ultimately show ?thesis
    unfolding bij_betw_def by (auto intro: finite_enumerate_in_set)
qed

lemma length_sorted_list_of_set [simp]: "length (sorted_list_of_set A) = card A"
proof (cases "finite A")
  case True
  then show ?thesis 
    by(metis distinct_card distinct_sorted_list_of_set set_sorted_list_of_set)
qed auto

lemmas sorted_list_of_set = set_sorted_list_of_set sorted_sorted_list_of_set distinct_sorted_list_of_set

lemma strict_sorted_equal:
  assumes "strict_sorted xs"
      and "strict_sorted ys"
      and "set ys = set xs"
    shows "ys = xs"
  using assms
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis
      using Cons.prems by auto 
  next
    case (Cons y ys')
    then have "xs = ys'"
      by (metis Cons.prems list.inject sorted_distinct_set_unique strict_sorted_iff)
    moreover have "x = y"
      using Cons.prems \<open>xs = ys'\<close> local.Cons by fastforce
    ultimately show ?thesis
      using local.Cons by blast
  qed
qed auto

lemma sorted_list_of_set_inject:
  assumes "sorted_list_of_set A = sorted_list_of_set B" "finite A" "finite B" 
  shows "A = B"
  using assms set_sorted_list_of_set by fastforce

lemma sorted_list_of_set_unique:
  assumes "finite A"
  shows "strict_sorted l \<and> set l = A \<and> length l = card A \<longleftrightarrow> sorted_list_of_set A = l"
  using assms strict_sorted_equal by force

lemma iso_iff2: "iso r r' f \<longleftrightarrow>
                 bij_betw f (Field r) (Field r') \<and> 
                 (\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a, b) \<in> r \<longleftrightarrow> (f a, f b) \<in> r')"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "bij_betw f (Field r) (Field r')" and emb: "embed r r' f"
    by (auto simp: bij_betw_def iso_def)
  then obtain g where g: "\<And>x. x \<in> Field r \<Longrightarrow> g (f x) = x"
    by (auto simp: bij_betw_iff_bijections)
  moreover
  have "(a, b) \<in> r" if "a \<in> Field r" "b \<in> Field r" "(f a, f b) \<in> r'" for a b 
    using that emb g g [OF FieldI1] \<comment>\<open>yes it's weird\<close>
    by (force simp: embed_def under_def bij_betw_iff_bijections)
  ultimately show ?rhs
    using L by (auto simp: compat_def iso_def dest: embed_compat)
next
  assume R: ?rhs
  then show ?lhs
    apply (clarsimp simp add: iso_def embed_def under_def bij_betw_iff_bijections)
    apply (rule_tac x=g in exI)
    apply (fastforce simp add: intro: FieldI1)+
    done
qed

lemma sorted_list_of_set_atMost_Suc [simp]:
  "sorted_list_of_set {..Suc k} = sorted_list_of_set {..k} @ [Suc k]"
  using lessThan_Suc_atMost sorted_list_of_set_lessThan_Suc by fastforce

lemma sorted_list_of_set_greaterThanLessThan:
  assumes "Suc i < j" 
    shows "sorted_list_of_set {i<..<j} = Suc i # sorted_list_of_set {Suc i<..<j}"
proof -
  have "{i<..<j} = insert (Suc i) {Suc i<..<j}"
    using assms by auto
  then show ?thesis
    by (metis assms atLeastSucLessThan_greaterThanLessThan sorted_list_of_set_range upt_conv_Cons)
qed

lemma sorted_list_of_set_greaterThanAtMost:
  assumes "Suc i \<le> j" 
    shows "sorted_list_of_set {i<..j} = Suc i # sorted_list_of_set {Suc i<..j}"
  using sorted_list_of_set_greaterThanLessThan [of i "Suc j"]
  by (metis assms greaterThanAtMost_def greaterThanLessThan_eq le_imp_less_Suc lessThan_Suc_atMost)

lemma nth_sorted_list_of_set_greaterThanLessThan: 
  "n < j - Suc i \<Longrightarrow> sorted_list_of_set {i<..<j} ! n = Suc (i+n)"
  by (induction n arbitrary: i) (auto simp: sorted_list_of_set_greaterThanLessThan)

lemma nth_sorted_list_of_set_greaterThanAtMost: 
  "n < j - i \<Longrightarrow> sorted_list_of_set {i<..j} ! n = Suc (i+n)"
  using nth_sorted_list_of_set_greaterThanLessThan [of n "Suc j" i]
  by (simp add: greaterThanAtMost_def greaterThanLessThan_eq lessThan_Suc_atMost)

lemma inv_into_ordermap: "\<alpha> \<in> elts (ordertype A r) \<Longrightarrow> inv_into A (ordermap A r) \<alpha> \<in> A"
  by (meson in_mono inv_into_into ordermap_surj)

lemma elts_multE:
  assumes "z \<in> elts (x * y)" 
  obtains u v where "u \<in> elts x" "v \<in> elts y" "z = x*v + u" 
  using mult [of x y] lift_def assms by auto

lemma Ord_add_mult_iff:
  assumes "\<beta> \<in> elts \<gamma>" "\<beta>' \<in> elts \<gamma>" "Ord \<alpha>" "Ord \<alpha>'" "Ord \<gamma>"
  shows "\<gamma> * \<alpha> + \<beta> \<in> elts (\<gamma> * \<alpha>' + \<beta>') \<longleftrightarrow> \<alpha> \<in> elts \<alpha>' \<or> \<alpha> = \<alpha>' \<and> \<beta> \<in> elts \<beta>'" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof (cases "\<alpha> \<in> elts \<alpha>'")
    case False
    with assms have "\<alpha> = \<alpha>'"
      by (meson L Ord_linear Ord_mult Ord_trans add_mult_less not_add_mem_right)
    then show ?thesis
      using L less_V_def by auto
  qed auto
next
  assume R: ?rhs
  then show ?lhs
  proof
    assume "\<alpha> \<in> elts \<alpha>'"
    then obtain \<delta> where "\<alpha>' = \<alpha>+\<delta>"
      by (metis OrdmemD assms(3) assms(4) le_Ord_diff less_V_def)
    show ?lhs 
      using assms
      by (meson \<open>\<alpha> \<in> elts \<alpha>'\<close> add_le_cancel_left0 add_mult_less vsubsetD)
  next
    assume "\<alpha> = \<alpha>' \<and> \<beta> \<in> elts \<beta>'"
    then show ?lhs
      using less_V_def by auto
  qed
qed

lemma small_Times [simp]:
  assumes "small A" "small B" 
  shows "small (A \<times> B)"
proof -
  obtain f a g b where "inj_on f A" "inj_on g B" and f: "f ` A = elts a" and g: "g ` B = elts b"
    using assms by (auto simp: small_def)
  define h where "h \<equiv> \<lambda>(x,y). \<langle>f x, g y\<rangle>"
  show ?thesis
    unfolding small_def
  proof (intro exI conjI)
    show "inj_on h (A \<times> B)"
      using \<open>inj_on f A\<close> \<open>inj_on g B\<close> by (simp add: h_def inj_on_def)
    have "h ` (A \<times> B) = elts (vtimes a b)"
      using f g by (fastforce simp: h_def image_iff split: prod.split)
    then show "h ` (A \<times> B) \<in> range elts"
      by blast
  qed
qed

lemma ordertype_Times:
  assumes "small A" "small B" and r: "wf r" "trans r" "total_on A r" and s: "wf s" "trans s" "total_on B s"
  shows "ordertype (A\<times>B) (r <*lex*> s) = ordertype B s * ordertype A r" (is "_ = ?\<beta> * ?\<alpha>")
proof (subst ordertype_eq_iff)
  show "Ord (?\<beta> * ?\<alpha>)"
    by (intro wf_Ord_ordertype Ord_mult r s; simp)
  define f where "f \<equiv> \<lambda>(x,y). ?\<beta> * ordermap A r x + (ordermap B s y)"
  show "\<exists>f. bij_betw f (A \<times> B) (elts (?\<beta> * ?\<alpha>)) \<and> (\<forall>x\<in>A \<times> B. \<forall>y\<in>A \<times> B. (f x < f y) = ((x, y) \<in> (r <*lex*> s)))"
    unfolding bij_betw_def
  proof (intro exI conjI strip)
    show "inj_on f (A \<times> B)"
    proof (clarsimp simp: f_def inj_on_def)
      fix x y x' y'
      assume "x \<in> A" "y \<in> B" "x' \<in> A" "y' \<in> B"
        and eq: "?\<beta> * ordermap A r x + ordermap B s y = ?\<beta> * ordermap A r x' + ordermap B s y'"
      have "ordermap A r x = ordermap A r x' \<and>
            ordermap B s y = ordermap B s y'"
      proof (rule mult_cancellation_lemma [OF eq])
        show "ordermap B s y \<sqsubset> ?\<beta>"
          using ordermap_in_ordertype [OF \<open>y \<in> B\<close>, of s] less_TC_iff \<open>small B\<close> by blast 
        show "ordermap B s y' \<sqsubset> ?\<beta>"
          using ordermap_in_ordertype [OF \<open>y' \<in> B\<close>, of s] less_TC_iff \<open>small B\<close> by blast 
      qed
      then show "x = x' \<and> y = y'"
        using \<open>x \<in> A\<close> \<open>x' \<in> A\<close> \<open>y \<in> B\<close> \<open>y' \<in> B\<close> r s \<open>small A\<close> \<open>small B\<close> by auto
    qed
    show "f ` (A \<times> B) = elts (?\<beta> * ?\<alpha>)" (is "?lhs = ?rhs")
    proof 
      show "f ` (A \<times> B) \<subseteq> elts (?\<beta> * ?\<alpha>)"
        apply (auto simp: f_def add_mult_less ordermap_in_ordertype wf_Ord_ordertype r s)
        by (simp add: add_mult_less assms ordermap_in_ordertype wf_Ord_ordertype)
      show "elts (?\<beta> * ?\<alpha>) \<subseteq> f ` (A \<times> B)"
      proof (clarsimp simp: f_def image_iff elim!: elts_multE split: prod.split)
        fix u v
        assume u: "u \<in> elts (?\<beta>)" and v: "v \<in> elts ?\<alpha>"
        have "inv_into B (ordermap B s) u \<in> B"
          by (simp add: inv_into_ordermap u)
        moreover have "inv_into A (ordermap A r) v \<in> A"
          by (simp add: inv_into_ordermap v)
        ultimately show "\<exists>x\<in>A. \<exists>y\<in>B. ?\<beta> * v + u = ?\<beta> * ordermap A r x + ordermap B s y"
          by (metis \<open>small A\<close> \<open>small B\<close> bij_betw_inv_into_right ordermap_bij r(1) r(3) s(1) s(3) u v)
      qed
    qed
  next
    fix p q
    assume "p \<in> A \<times> B" and "q \<in> A \<times> B"
    then obtain u v x y where \<section>: "p = (u,v)" "u \<in> A" "v \<in> B" "q = (x,y)" "x \<in> A" "y \<in> B"
      by blast
    show "((f p) < f q) = ((p, q) \<in> (r <*lex*> s))"
    proof
      assume "f p < f q"
      with \<section> assms have "(u, x) \<in> r \<or> u=x \<and> (v, y) \<in> s"
        apply (simp add: f_def)
        by (metis Ord_add Ord_add_mult_iff Ord_mem_iff_lt Ord_mult Ord_ordermap converse_ordermap_mono 
            ordermap_eq_iff ordermap_in_ordertype wf_Ord_ordertype)
      then show "(p,q) \<in> (r <*lex*> s)"
        by (simp add: \<section>)
    next
      assume "(p,q) \<in> (r <*lex*> s)"
      then have "(u, x) \<in> r \<or> u = x \<and> (v, y) \<in> s"
        by (simp add: \<section>)
      then show "f p < f q"
      proof
        assume ux: "(u, x) \<in> r"
        have oo: "\<And>x. Ord (ordermap A r x)" "\<And>y. Ord (ordermap B s y)" 
          by (simp_all add: r s)
        show "f p < f q"
        proof (clarsimp simp: f_def split: prod.split)
          fix a b a' b'
          assume "p = (a, b)" and "q = (a', b')"
          then have "?\<beta> * ordermap A r a + ordermap B s b < ?\<beta> * ordermap A r a'"
            using ux assms \<section>
            by (metis Ord_mult Ord_ordermap OrdmemD Pair_inject add_mult_less ordermap_in_ordertype ordermap_mono wf_Ord_ordertype)
          also have "\<dots> \<le> ?\<beta> * ordermap A r a' + ordermap B s b'"
            by simp
          finally show "?\<beta> * ordermap A r a + ordermap B s b < ?\<beta> * ordermap A r a' + ordermap B s b'" .
        qed
      next
        assume "u = x \<and> (v, y) \<in> s"
        then show "f p < f q"
          using \<section> assms by (fastforce simp: f_def split: prod.split intro: ordermap_mono_less)
      qed 
    qed
  qed 
qed (use assms small_Times in auto)

lemma ordertype_nat_\<omega>:
  assumes "infinite N" shows "ordertype N less_than = \<omega>"
proof -
  have "small N"
    by (meson inj_on_def ord_of_nat_inject small_def small_iff_range small_image_nat_V)
  have "ordertype (ord_of_nat ` N) VWF = \<omega>"
    by (force simp: assms finite_image_iff inj_on_def intro: ordertype_infinite_\<omega>)
  moreover have "ordertype (ord_of_nat ` N) VWF = ordertype N less_than"
    using total_on_def by (fastforce intro!: ordertype_inc_eq \<open>small N\<close>)
  ultimately show ?thesis
    by simp
qed
lemma infinite_infinite_partition:
  assumes "infinite A"
  obtains C :: "nat \<Rightarrow> 'a set" 
    where "pairwise (\<lambda>i j. disjnt (C i) (C j)) UNIV" "(\<Union>i. C i) \<subseteq> A" "\<And>i. infinite (C i)"
proof -
  obtain f :: "nat\<Rightarrow>'a" where "range f \<subseteq> A" "inj f"
    using assms infinite_countable_subset by blast
  let ?C = "\<lambda>i. range (\<lambda>j. f (prod_encode (i,j)))"
  show thesis
  proof
    show "pairwise (\<lambda>i j. disjnt (?C i) (?C j)) UNIV"
      by (auto simp: pairwise_def disjnt_def inj_on_eq_iff [OF \<open>inj f\<close>] inj_on_eq_iff [OF inj_prod_encode, of _ UNIV])
    show "(\<Union>i. ?C i) \<subseteq> A"
      using \<open>range f \<subseteq> A\<close> by blast
    have "infinite (range (\<lambda>j. f (prod_encode (i, j))))" for i
      by (rule range_inj_infinite) (meson Pair_inject \<open>inj f\<close> inj_def prod_encode_eq)
    then show "\<And>i. infinite (?C i)"
      using that by auto
  qed
qed

text \<open>This is already installed in the development AFP entry\<close>
lemma mult_cancellation_half:
  assumes "a*x + r \<le> a*y + s" "r \<sqsubset> a" "s \<sqsubset> a"
  shows "x \<le> y"
proof -
  have "x \<le> y" if "Ord \<alpha>" "x \<in> elts (Vset \<alpha>)" "y \<in> elts (Vset \<alpha>)" for \<alpha>
    using that assms
  proof (induction \<alpha> arbitrary: x y r s rule: Ord_induct3)
    case 0
    then show ?case
      by auto
  next
    case (succ k)
    show ?case
    proof
      fix u
      assume u: "u \<in> elts x"
      have u_k: "u \<in> elts (Vset k)"
        using Vset_succ succ.hyps succ.prems(1) u by auto
      obtain r' where "r' \<in> elts a" "r \<sqsubseteq> r'"
        using less_TC_iff succ.prems(4) by blast
      have "a*u + r' \<in> elts (lift (a*u) a)"
        by (simp add: \<open>r' \<in> elts a\<close> lift_def)
      also have "\<dots> \<le> elts (a*x)"
        using u by (force simp: mult [of _ x])
      also have "\<dots> \<le> elts (a*y + s)"
        using plus_eq_lift succ.prems(3) by auto
      also have "\<dots> = elts (a*y) \<union> elts (lift (a*y) s)"
        by (simp add: plus_eq_lift)
      finally have "a * u + r' \<in> elts (a * y) \<union> elts (lift (a * y) s)" .
      then show "u \<in> elts y"
      proof
        assume *: "a * u + r' \<in> elts (a * y)"
        show "u \<in> elts y"
        proof -
          obtain v e where v: "v \<in> elts y" "e \<in> elts a" "a * u + r' = a * v + e"
            using * by (auto simp: mult [of _ y] lift_def)
          then have v_k: "v \<in> elts (Vset k)"
            using Vset_succ_TC less_TC_iff succ.prems(2) by blast
          then show ?thesis
            by (metis \<open>r' \<in> elts a\<close> antisym le_TC_refl less_TC_iff order_refl succ.IH u_k v)
        qed
      next
        assume "a * u + r' \<in> elts (lift (a * y) s)"
        then obtain t where "t \<in> elts s" and t: "a * u + r' = a * y + t"
          using lift_def by auto
        have noteq: "a*y \<noteq> a*u"
        proof
          assume "a*y = a*u"
          then have "lift (a*y) a = lift (a*u) a"
            by metis
          also have "\<dots> \<le> a*x"
            unfolding mult [of _ x] using \<open>u \<in> elts x\<close> by (auto intro: cSUP_upper)
          also have "\<dots> \<le> a*y \<squnion> lift (a*y) s"
            using \<open>elts (a * x) \<subseteq> elts (a * y + s)\<close> plus_eq_lift by auto
          finally have "lift (a*y) a \<le> a*y \<squnion> lift (a*y) s" .
          then have "lift (a*y) a \<le> lift (a*y) s"
            using add_le_cancel_left less_TC_imp_not_le plus_eq_lift \<open>s \<sqsubset> a\<close> by auto
          then have "a \<le> s"
            by (simp add: le_iff_sup lift_eq_lift lift_sup_distrib)
          then show False
            using \<open>s \<sqsubset> a\<close> less_TC_imp_not_le by auto
        qed
        consider "a * u \<unlhd> a * y" | "a * y \<unlhd> a * u"
          using t comparable vle_comparable_def by blast
        then have "False"
        proof cases
          case 1
          then obtain c where "a*y = a*u + c"
            by (metis vle_def)
          then have "c+t = r'"
            by (metis add_right_cancel add.assoc t)
          then have "c \<sqsubset> a"
            using \<open>r' \<in> elts a\<close> less_TC_iff vle2 vle_def by force
          moreover have "c \<noteq> 0"
            using \<open>a * y = a * u + c\<close> noteq by auto
          ultimately show ?thesis
            using \<open>a * y = a * u + c\<close> mult_eq_imp_0 by blast
        next
          case 2
          then obtain c where "a*u = a*y + c"
            by (metis vle_def)
          then have "c+r' = t"
            by (metis add_right_cancel add.assoc t)
          then have "c \<sqsubset> a"
            by (metis \<open>t \<in> elts s\<close> less_TC_iff less_TC_trans \<open>s \<sqsubset> a\<close> vle2 vle_def)
          moreover have "c \<noteq> 0"
            using \<open>a * u = a * y + c\<close> noteq by auto
          ultimately show ?thesis
            using \<open>a * u = a * y + c\<close> mult_eq_imp_0 by blast
        qed
        then show "u \<in> elts y" ..
      qed
    qed
  next
    case (Limit k)
    obtain i j where k: "i \<in> elts k" "j \<in> elts k"
      and x: "x \<in> elts (Vset i)" and y: "y \<in> elts (Vset j)"
      using that Limit by (auto simp: Limit_Vfrom_eq)
    show ?case
    proof (rule Limit.IH [of "i \<squnion> j"])
      show "i \<squnion> j \<in> elts k"
        by (meson k x y Limit.hyps Limit_def Ord_in_Ord Ord_mem_iff_lt Ord_sup union_less_iff)
      show "x \<in> elts (Vset (i \<squnion> j))" "y \<in> elts (Vset (i \<squnion> j))"
        using x y by (auto simp: Vfrom_sup)
      show "a * x + r \<le> a * y + s"
        by (simp add: Limit.prems)
    qed (auto simp: Limit.prems)
  qed
  then show ?thesis
    by (metis two_in_Vset Ord_rank Ord_VsetI rank_lt)
qed

corollary mult_cancellation_less:
  assumes lt: "a*x + r < a*y + s" and "r \<sqsubset> a" "s \<sqsubset> a"
  obtains "x < y" | "x = y" "r < s"
proof -
  have "x \<le> y"
    by (meson assms dual_order.strict_implies_order mult_cancellation_half)
  then consider "x < y" | "x = y"
    using less_V_def by blast
  with lt that show ?thesis by blast
qed

subsection \<open>For HOL\<close>

lemma enumerate_mono_iff [simp]:
  "infinite S \<Longrightarrow> enumerate S m < enumerate S n \<longleftrightarrow> m < n"
  by (metis enumerate_mono less_asym less_linear)

lemma finite_enumerate_mono_iff [simp]:
  "\<lbrakk>finite S; m < card S; n < card S\<rbrakk> \<Longrightarrow> enumerate S m < enumerate S n \<longleftrightarrow> m < n"
  by (metis finite_enumerate_mono less_asym less_linear)

lemma finite_enumerate_Diff_singleton:
  fixes S :: "'a::wellorder set"
  assumes "finite S" and i: "i < card S" "enumerate S i < x"
  shows "enumerate (S - {x}) i = enumerate S i"
  using i
proof (induction i)
  case 0
  have "(LEAST i. i \<in> S \<and> i\<noteq>x) = (LEAST i. i \<in> S)"
  proof (rule Least_equality)
    have "\<exists>t. t \<in> S \<and> t\<noteq>x"
      using 0 \<open>finite S\<close> finite_enumerate_in_set by blast
    then show "(LEAST i. i \<in> S) \<in> S \<and> (LEAST i. i \<in> S) \<noteq> x"
      by (metis "0.prems"(2) LeastI enumerate_0 not_less_Least)
  qed (simp add: Least_le)
  then show ?case
    by (auto simp: enumerate_0)
next
  case (Suc i)
  then have x: "enumerate S i < x"
    by (meson enumerate_step finite_enumerate_step less_trans)
  have cardSx: "Suc i < card (S - {x})" and "i < card S"
    using Suc \<open>finite S\<close> card_Diff_singleton_if finite_enumerate_Ex by fastforce+
  have "(LEAST s. s \<in> S \<and> s\<noteq>x \<and> enumerate (S - {x}) i < s) = (LEAST s. s \<in> S \<and> enumerate S i < s)"
       (is "_ = ?r")
  proof (intro Least_equality conjI)
    show "?r \<in> S"
      by (metis (lifting) LeastI Suc.prems(1) assms(1) finite_enumerate_in_set finite_enumerate_step)
    show "?r \<noteq> x"
      using Suc.prems not_less_Least [of _ "\<lambda>t. t \<in> S \<and> enumerate S i < t"] 
       \<open>finite S\<close> finite_enumerate_in_set finite_enumerate_step by blast
    show "enumerate (S - {x}) i < ?r"
      by (metis (full_types) Suc.IH Suc.prems(1) \<open>i < card S\<close> enumerate_Suc'' enumerate_step finite_enumerate_Suc'' finite_enumerate_step x)
    show "\<And>y. y \<in> S \<and> y \<noteq> x \<and> enumerate (S - {x}) i < y \<Longrightarrow> ?r \<le> y"
      by (simp add: Least_le Suc.IH \<open>i < card S\<close> x)
  qed
  then show ?case
    using Suc assms by (simp add: finite_enumerate_Suc'' cardSx)
qed



lemma lexl_not_refl [simp]: "irrefl r \<Longrightarrow> (x,x) \<notin> lex r"
  by (meson irrefl_def lex_take_index)

lemma hd_lex: "\<lbrakk>hd ms < hd ns; length ms = length ns; ns \<noteq> []\<rbrakk> \<Longrightarrow> (ms, ns) \<in> lex less_than"
  by (metis hd_Cons_tl length_0_conv less_than_iff lexord_cons_cons lexord_lex)


lemma finite_enum_subset:
  assumes "\<And>i. i < card X \<Longrightarrow> enumerate X i = enumerate Y i" and "finite X" "finite Y" "card X \<le> card Y"
  shows "X \<subseteq> Y"
  by (metis assms finite_enumerate_Ex finite_enumerate_in_set less_le_trans subsetI)

lemma finite_enum_ext:
  assumes "\<And>i. i < card X \<Longrightarrow> enumerate X i = enumerate Y i" and "finite X" "finite Y" "card X = card Y"
  shows "X = Y"
  by (intro antisym finite_enum_subset) (auto simp: assms)

thm card_Un_disjoint
lemma card_Un_disjnt: "\<lbrakk>finite A; finite B; disjnt A B\<rbrakk> \<Longrightarrow> card (A \<union> B) = card A + card B"
  by (simp add: card_Un_disjoint disjnt_def)


lemma sorted_list_of_set_nonempty:
  assumes "finite I" "I \<noteq> {}"
  shows "sorted_list_of_set I = Min I # sorted_list_of_set (I - {Min I})"
  using assms by (auto simp: less_le simp flip: sorted_list_of_set_unique intro: Min_in)
lemma strict_sorted_imp_sorted: "strict_sorted xs \<Longrightarrow> sorted xs"
  by (auto simp: strict_sorted_iff)

lemma sorted_hd_le:
  assumes "sorted xs" "x \<in> list.set xs"
  shows "hd xs \<le> x"
  using assms by (induction xs) (auto simp: less_imp_le)

lemma sorted_le_last:
  assumes "sorted xs" "x \<in> list.set xs"
  shows "x \<le> last xs"
  using assms by (induction xs) (auto simp: less_imp_le)

lemma hd_list_of:
  assumes "finite A" "A \<noteq> {}"
  shows "hd (sorted_list_of_set A) = Min A" 
proof (rule antisym)
  have "Min A \<in> A"
    by (simp add: assms)
  then show "hd (sorted_list_of_set A) \<le> Min A"
    by (simp add: sorted_hd_le \<open>finite A\<close>)
next
  show "Min A \<le> hd (sorted_list_of_set A)"
    by (metis Min_le assms hd_in_set set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
qed

lemma sorted_hd_le_last:
  assumes "sorted xs" "xs \<noteq> []"
  shows "hd xs \<le> last xs"
  using assms by (simp add: sorted_hd_le)

lemma sorted_list_of_set_set_of [simp]: "strict_sorted l \<Longrightarrow> sorted_list_of_set (list.set l) = l"
  by (simp add: strict_sorted_equal)

lemma finite_Inf_in:
  fixes A :: "'a::complete_lattice set"
  assumes "finite A" "A\<noteq>{}" and inf: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> inf x y \<in> A"
  shows "Inf A \<in> A"
proof -
  have "Inf B \<in> A" if "B \<le> A" "B\<noteq>{}" for B
    using finite_subset [OF \<open>B \<subseteq> A\<close> \<open>finite A\<close>] that
  by (induction B) (use inf in \<open>force+\<close>)
  then show ?thesis
    by (simp add: assms)
qed

lemma finite_Sup_in:
  fixes A :: "'a::complete_lattice set"
  assumes "finite A" "A\<noteq>{}" and sup: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> sup x y \<in> A"
  shows "Sup A \<in> A"
proof -
  have "Sup B \<in> A" if "B \<le> A" "B\<noteq>{}" for B
    using finite_subset [OF \<open>B \<subseteq> A\<close> \<open>finite A\<close>] that
  by (induction B) (use sup in \<open>force+\<close>)
  then show ?thesis
    by (simp add: assms)
qed

lemma range_strict_mono_ext:
  fixes f::"nat \<Rightarrow> 'a::linorder"
  assumes eq: "range f = range g"
      and sm: "strict_mono f" "strict_mono g"
    shows "f = g"
proof
  fix n
  show "f n = g n"
  proof (induction n rule: less_induct)
    case (less n)
    obtain x y where xy: "f n = g y" "f x = g n"
      by (metis eq imageE rangeI)
    then have "n = y"
      by (metis (no_types) less.IH neq_iff sm strict_mono_less xy)
    then show ?case using xy by auto
  qed
qed

(*METIS NOT ALLOWED!*)

lemma iso_trans:
  assumes "trans r" "iso r r' f" shows "trans r'"
  using assms unfolding trans_def iso_iff2 bij_betw_iff_bijections 
  by (metis (full_types) FieldI1 FieldI2)

lemma iso_Total:
  assumes "Total r" "iso r r' f" shows "Total r'"
  using assms unfolding total_on_def iso_iff2 bij_betw_iff_bijections by metis

lemma iso_wf:
  assumes "wf r" "iso r r' f" shows "wf r'"
proof -
  have bij: "bij_betw f (Field r) (Field r')"
    and iff: "(\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a, b) \<in> r \<longleftrightarrow> (f a, f b) \<in> r')"
    using assms by (auto simp: iso_iff2)
  show ?thesis
  proof (rule wfI_min)
    fix x::'b and Q
    assume "x \<in> Q"
    let ?Q = "inv_into (Field r) f ` Q"
    obtain z where "z \<in> ?Q" "\<And>x y. \<lbrakk>(y, z) \<in> r; x \<in> Q\<rbrakk> \<Longrightarrow> y \<noteq> inv_into (Field r) f x"
      by (metis \<open>x \<in> Q\<close> \<open>wf r\<close> image_eqI wfE_min)
    with bij show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r' \<longrightarrow> y \<notin> Q"
      by (metis (no_types, lifting) FieldI2 bij_betw_imp_surj_on f_inv_into_f iff inv_into_into)
  qed
qed


subsection \<open>Also in the Nash-Williams development\<close>
text \<open>FIXME: these contain duplicates and need consolidation\<close>

lemma less_setsD: "\<lbrakk>less_sets A B; a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a < b"
  by (auto simp: less_sets_def)

lemma less_sets_irrefl [simp]: "less_sets A A \<longleftrightarrow> A = {}"
  by (auto simp: less_sets_def)

lemma less_sets_trans: "\<lbrakk>less_sets A B; less_sets B C; B \<noteq> {}\<rbrakk> \<Longrightarrow> less_sets A C"
  unfolding less_sets_def using less_trans by blast

lemma less_sets_weaken1: "\<lbrakk>less_sets A' B; A \<subseteq> A'\<rbrakk> \<Longrightarrow> less_sets A B"
  by (auto simp: less_sets_def)

lemma less_sets_weaken2: "\<lbrakk>less_sets A B'; B \<subseteq> B'\<rbrakk> \<Longrightarrow> less_sets A B"
  by (auto simp: less_sets_def)

lemma less_sets_imp_disjnt: "less_sets A B \<Longrightarrow> disjnt A B"
  by (auto simp: less_sets_def disjnt_def)

lemma less_sets_Un1: "less_sets (A \<union> A') B \<longleftrightarrow> less_sets A B \<and> less_sets A' B"
  by (auto simp: less_sets_def)

lemma less_sets_Un2: "less_sets A (B \<union> B') \<longleftrightarrow> less_sets A B \<and> less_sets A B'"
  by (auto simp: less_sets_def)

lemma less_sets_UN1: "less_sets (\<Union>\<A>) B \<longleftrightarrow> (\<forall>A\<in>\<A>. less_sets A B)"
  by (auto simp: less_sets_def)

lemma less_sets_UN2: "less_sets A (\<Union> \<B>) \<longleftrightarrow> (\<forall>B\<in>\<B>. less_sets A B)"
  by (auto simp: less_sets_def)

lemma strict_sorted_imp_less_sets:
  "strict_sorted (as @ bs) \<Longrightarrow> less_sets (list.set as) (list.set bs)"
  by (simp add: less_sets_def sorted_wrt_append strict_sorted_sorted_wrt)

subsection \<open>Other material\<close>

definition strict_mono_sets :: "['a::order set, 'a::order \<Rightarrow> 'b::order set] \<Rightarrow> bool" where
  "strict_mono_sets A f \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. x < y \<longrightarrow> less_sets (f x) (f y)"

lemma strict_mono_setsD:
  assumes "strict_mono_sets A f" "x < y" "x \<in> A" "y \<in> A"
  shows "less_sets (f x) (f y)"
  using assms by (auto simp: strict_mono_sets_def)

lemma strict_mono_on_o: "\<lbrakk>strict_mono_on r A; strict_mono_on s B; s ` B \<subseteq> A\<rbrakk> \<Longrightarrow> strict_mono_on (r \<circ> s) B"
  by (auto simp: image_subset_iff strict_mono_on_def)

lemma strict_mono_sets_imp_disjoint:
  fixes A :: "'a::linorder set"
  assumes "strict_mono_sets A f"
  shows "pairwise (\<lambda>x y. disjnt (f x) (f y)) A"
  using assms unfolding strict_mono_sets_def pairwise_def
  by (meson antisym_conv3 disjnt_sym less_sets_imp_disjnt)

lemma strict_mono_sets_subset:
  assumes "strict_mono_sets B f" "A \<subseteq> B"
  shows "strict_mono_sets A f"
  using assms by (auto simp: strict_mono_sets_def)

lemma strict_mono_less_sets_Min:
  assumes "strict_mono_sets I f" "finite I" "I \<noteq> {}"
  shows "less_sets (f (Min I)) (\<Union> (f ` (I - {Min I})))"
  using assms by (simp add: strict_mono_sets_def less_sets_UN2 dual_order.strict_iff_order)

lemma pair_less_iff1 [simp]: "((x,y), (x,z)) \<in> pair_less \<longleftrightarrow> y<z"
  by (simp add: pair_less_def)

lemma infinite_finite_Inter:
  assumes "finite \<A>" "\<A>\<noteq>{}" "\<And>A. A \<in> \<A> \<Longrightarrow> infinite A"
    and "\<And>A B. \<lbrakk>A \<in> \<A>; B \<in> \<A>\<rbrakk> \<Longrightarrow> A \<inter> B \<in> \<A>"
  shows "infinite (\<Inter>\<A>)"
  by (simp add: assms finite_Inf_in)

lemma atLeast_less_sets: "\<lbrakk>less_sets A {x}; B \<subseteq> {x..}\<rbrakk> \<Longrightarrow> less_sets A B"
  by (force simp: less_sets_def subset_iff)



subsection \<open>The list-of function\<close>

(*NOT THE FOLLOWING*)

lemma sorted_list_of_set_insert:
  assumes "finite A" "less_sets {a} A"
  shows "sorted_list_of_set (insert a A) = a # sorted_list_of_set A"
proof -
  have "strict_sorted (a # sorted_list_of_set A)"
    using assms less_setsD by auto
  moreover have "list.set (a # sorted_list_of_set A) = insert a A"
    using assms by force
  moreover have "length (a # sorted_list_of_set A) = card (insert a A)"
    using assms card_insert_if less_setsD by fastforce
  ultimately show ?thesis
    by (metis assms(1) finite_insert sorted_list_of_set_unique)
qed

lemma sorted_list_of_set_Un:
  assumes AB: "less_sets A B" and fin: "finite A" "finite B"
  shows "sorted_list_of_set (A \<union> B) = sorted_list_of_set A @ sorted_list_of_set B"
proof -
  have "strict_sorted (sorted_list_of_set A @ sorted_list_of_set B)"
    using AB unfolding less_sets_def
    by (metis fin set_sorted_list_of_set sorted_wrt_append strict_sorted_list_of_set strict_sorted_sorted_wrt)
  moreover have "card A + card B = card (A \<union> B)"
    using less_sets_imp_disjnt [OF AB]
    by (simp add: assms card_Un_disjoint disjnt_def)
  ultimately show ?thesis
    by (simp add: assms strict_sorted_equal)
qed

lemma sorted_list_of_set_UN_lessThan:
  fixes k::nat
  assumes sm: "strict_mono_sets {..<k} A" and "\<And>i. i < k \<Longrightarrow> finite (A i)"
  shows "sorted_list_of_set (\<Union>i<k. A i) = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..<k}))"
  using assms
proof (induction k)
  case 0
  then show ?case
    by auto
next
  case (Suc k)
  have ls: "less_sets (\<Union> (A ` {..<k})) (A k)"
    using sm Suc.prems(1) strict_mono_setsD by (force simp: less_sets_UN1)
  have "sorted_list_of_set (\<Union> (A ` {..<Suc k})) = sorted_list_of_set (\<Union> (A ` {..<k}) \<union> A k)"
    by (simp add: Un_commute lessThan_Suc)
  also have "\<dots> = sorted_list_of_set (\<Union> (A ` {..<k})) @ sorted_list_of_set (A k)"
    by (rule sorted_list_of_set_Un) (auto simp: Suc.prems ls)
  also have "\<dots> = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..<k})) @ sorted_list_of_set (A k)"
    using Suc strict_mono_sets_def by fastforce
  also have "\<dots> = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..<Suc k}))"
    using strict_mono_sets_def by fastforce
  finally show ?case .
qed

lemma sorted_list_of_set_UN_atMost:
  fixes k::nat
  assumes "strict_mono_sets {..k} A" and "\<And>i. i \<le> k \<Longrightarrow> finite (A i)"
  shows "sorted_list_of_set (\<Union>i\<le>k. A i) = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..k}))"
  by (metis assms lessThan_Suc_atMost less_Suc_eq_le sorted_list_of_set_UN_lessThan)



subsection \<open>Ramsey\<close>

lemma nsets_Pi_contra: "A' \<subseteq> A \<Longrightarrow> Pi ([A]\<^bsup>n\<^esup>) B \<subseteq> Pi ([A']\<^bsup>n\<^esup>) B"
  by (auto simp: nsets_def)

subsection \<open>Misc additions to the ZF libraries\<close>


lemma oexp_\<omega>_Limit: "Limit \<beta> \<Longrightarrow> \<omega>\<up>\<beta> = (SUP \<xi> \<in> elts \<beta>. \<omega>\<up>\<xi>)"
  by (simp add: oexp_Limit)


lemma oexp_mult_commute:
  fixes j::nat
  shows "Ord \<alpha> \<Longrightarrow> (\<alpha> \<up> j) * \<alpha> = \<alpha> * (\<alpha> \<up> j)"
  by (metis Ord_1 Ord_ord_of_nat oexp_1_right oexp_add oexp_succ one_V_def ord_of_nat_\<omega> succ_0_plus_eq)

lemma iso_imp_ordertype_eq_ordertype:
  assumes iso: "iso r r' f"
    and "wf r"
    and "Total r"
    and "trans r"
    and sm: "small (Field r)"
  shows "ordertype (Field r) r = ordertype (Field r') r'"
proof (subst ordertype_eq_ordertype)
  show "small (Field r')"
    by (metis iso sm iso_Field replacement)
  show "\<exists>f. bij_betw f (Field r) (Field r') \<and> (\<forall>x\<in>Field r. \<forall>y\<in>Field r. ((f x, f y) \<in> r') = ((x, y) \<in> r))"
    using assms(1) iso_iff2 by blast
qed (use assms iso_wf iso_Total iso_trans in auto)

proposition ordertype_eq_ordertype_iso:
  assumes r: "wf r" "total_on A r" "trans r" and "small A" and FA: "Field r = A"
  assumes s: "wf s" "total_on B s" "trans s" and "small B" and FB: "Field s = B"
  shows "ordertype A r = ordertype B s \<longleftrightarrow> (\<exists>f. iso r s f)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then obtain f where "bij_betw f A B" "\<forall>x \<in> A. \<forall>y \<in> A. (f x, f y) \<in> s \<longleftrightarrow> (x,y) \<in> r"
    using assms ordertype_eq_ordertype by blast
  then show ?rhs
    using FA FB iso_iff2 by blast
next
  assume ?rhs
  then show ?lhs
    using FA FB \<open>small A\<close> iso_imp_ordertype_eq_ordertype r by blast
qed

lemma total_on_imp_Total_Restr: "total_on A r \<Longrightarrow> Total (Restr r A)"
  by (auto simp: Field_def total_on_def)

lemma Limit_ordertype_imp_Field_Restr:
  assumes Lim: "Limit (ordertype A r)" and r: "wf r" "total_on A r" and "small A"
  shows "Field (Restr r A) = A"
proof -
  have "\<exists>y\<in>A. (x,y) \<in> r" if "x \<in> A" for x
  proof -
    let ?oy = "succ (ordermap A r x)"
    have \<section>: "?oy \<in> elts (ordertype A r)"
      by (simp add: Lim \<open>small A\<close> ordermap_in_ordertype succ_in_Limit_iff that)
    then have A: "inv_into A (ordermap A r) ?oy \<in> A"
      by (simp add: inv_into_ordermap)
    moreover have "(x, inv_into A (ordermap A r) ?oy) \<in> r"
    proof -
      have "ordermap A r x \<in> elts (ordermap A r (inv_into A (ordermap A r) ?oy))"
        by (metis "\<section>" elts_succ f_inv_into_f insert_iff ordermap_surj subsetD)
      then show ?thesis
        by (metis \<open>small A\<close> A converse_ordermap_mono r that)
    qed
    ultimately show ?thesis ..
  qed
  then have "A \<subseteq> Field (Restr r A)"
    by (auto simp: Field_def)
  then show ?thesis
    by (simp add: Field_Restr_subset subset_antisym)
qed

lemma ordertype_Field_Restr:
  assumes "wf r" "total_on A r" "trans r" "small A" "Field (Restr r A) = A"
  shows "ordertype (Field (Restr r A)) (Restr r A) = ordertype A r"
  using assms by (force simp: ordertype_eq_ordertype wf_Restr total_on_def trans_Restr)

proposition ordertype_eq_ordertype_iso_Restr:
  assumes r: "wf r" "total_on A r" "trans r" and "small A" and FA: "Field (Restr r A) = A"
  assumes s: "wf s" "total_on B s" "trans s" and "small B" and FB: "Field (Restr s B) = B"
  shows "ordertype A r = ordertype B s \<longleftrightarrow> (\<exists>f. iso (Restr r A) (Restr s B) f)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then obtain f where "bij_betw f A B" "\<forall>x \<in> A. \<forall>y \<in> A. (f x, f y) \<in> s \<longleftrightarrow> (x,y) \<in> r"
    using assms ordertype_eq_ordertype by blast
  then show ?rhs
    using FA FB bij_betwE unfolding iso_iff2 by fastforce
next
  assume ?rhs
  moreover
  have "ordertype (Field (Restr r A)) (Restr r A) = ordertype A r"
    using FA \<open>small A\<close> ordertype_Field_Restr r by blast
  moreover
  have "ordertype (Field (Restr s B)) (Restr s B) = ordertype B s"
    using FB \<open>small B\<close> ordertype_Field_Restr s by blast
  ultimately show ?lhs
    using iso_imp_ordertype_eq_ordertype FA FB \<open>small A\<close> r
    by (fastforce intro: total_on_imp_Total_Restr trans_Restr wf_Int1)
qed

subsection \<open>Monotonic enumeration of a countably infinite set\<close>

abbreviation "enum \<equiv> enumerate"

text \<open>Could be generalised to infinite countable sets of any type\<close>
lemma nat_infinite_iff:
  fixes N :: "nat set"
  shows "infinite N \<longleftrightarrow> (\<exists>f::nat\<Rightarrow>nat. N = range f \<and> strict_mono f)"
proof safe
  assume "infinite N"
  then show "\<exists>f. N = range (f::nat \<Rightarrow> nat) \<and> strict_mono f"
    by (metis bij_betw_imp_surj_on bij_enumerate enumerate_mono strict_mono_def)
next
  fix f :: "nat \<Rightarrow> nat"
  assume "strict_mono f" and "N = range f" and "finite (range f)"
  then show False
    using range_inj_infinite strict_mono_imp_inj_on by blast
qed

lemma enum_works:
  fixes N :: "nat set"
  assumes "infinite N"
  shows "N = range (enum N) \<and> strict_mono (enum N)"
  by (metis assms bij_betw_imp_surj_on bij_enumerate enumerate_mono strict_monoI)

lemma range_enum: "range (enum N) = N" and strict_mono_enum: "strict_mono (enum N)"
  if "infinite N" for N :: "nat set"
  using enum_works [OF that] by auto

lemma enum_0_eq_Inf:
  fixes N :: "nat set"
  assumes "infinite N"
  shows "enum N 0 = Inf N"
proof -
  have "enum N 0 \<in> N"
    using assms range_enum by auto
  moreover have "\<And>x. x \<in> N \<Longrightarrow> enum N 0 \<le> x"
    by (metis (mono_tags, hide_lams) assms imageE le0 less_mono_imp_le_mono range_enum strict_monoD strict_mono_enum)
  ultimately show ?thesis
    by (metis cInf_eq_minimum)
qed

lemma enum_works_finite:
  fixes N :: "nat set"
  assumes "finite N"
  shows "N = enum N ` {..<card N} \<and> strict_mono_on (enum N) {..<card N}"
  using assms
  by (metis bij_betw_imp_surj_on finite_bij_enumerate finite_enumerate_mono lessThan_iff strict_mono_onI)

lemma enum_obtain_index_finite:
  fixes N :: "nat set"
  assumes "x \<in> N" "finite N" 
  obtains i where "i < card N" "x = enum N i"
  by (metis \<open>x \<in> N\<close> \<open>finite N\<close> enum_works_finite imageE lessThan_iff)

lemma enum_0_eq_Inf_finite:
  fixes N :: "nat set"
  assumes "finite N" "N \<noteq> {}"
  shows "enum N 0 = Inf N"
proof -
  have "enum N 0 \<in> N"
    by (metis Nat.neq0_conv assms empty_is_image enum_works_finite image_eqI lessThan_empty_iff lessThan_iff)
  moreover have "enum N 0 \<le> x" if "x \<in> N" for x
  proof -
    obtain i where "i < card N" "x = enum N i"
      by (metis \<open>x \<in> N\<close> \<open>finite N\<close> enum_obtain_index_finite)
    with assms show ?thesis
      by (metis Nat.neq0_conv finite_enumerate_mono less_or_eq_imp_le)
  qed
  ultimately show ?thesis
    by (metis cInf_eq_minimum)
qed

lemma greaterThan_less_enum:
  fixes N :: "nat set"
  assumes "N \<subseteq> {x<..}" "infinite N"
  shows "x < enum N i"
  using assms range_enum by fastforce

lemma atLeast_le_enum:
  fixes N :: "nat set"
  assumes "N \<subseteq> {x..}" "infinite N"
  shows "x \<le> enum N i"
  using assms range_enum by fastforce

lemma less_sets_empty1 [simp]: "less_sets {} A" and less_sets_empty2 [simp]: "less_sets A {}"
  by (simp_all add: less_sets_def)

lemma less_sets_singleton1 [simp]: "less_sets {a} A \<longleftrightarrow> (\<forall>x\<in>A. a < x)" 
  and less_sets_singleton2 [simp]: "less_sets A {a} \<longleftrightarrow> (\<forall>x\<in>A. x < a)"
  by (simp_all add: less_sets_def)

lemma less_sets_atMost [simp]: "less_sets {..a} A \<longleftrightarrow> (\<forall>x\<in>A. a < x)" 
  and less_sets_alLeast [simp]: "less_sets A {a..} \<longleftrightarrow> (\<forall>x\<in>A. x < a)"
  by (auto simp: less_sets_def)

lemma less_sets_imp_strict_mono_sets:
  assumes "\<And>i. less_sets (A i) (A (Suc i))" "\<And>i. i>0 \<Longrightarrow> A i \<noteq> {}"
  shows "strict_mono_sets UNIV A"
proof (clarsimp simp: strict_mono_sets_def)
  fix i j::nat
  assume "i < j"
  then show "less_sets (A i) (A j)"
  proof (induction "j-i" arbitrary: i j)
    case (Suc x)
    then show ?case
      by (metis Suc_diff_Suc Suc_inject Suc_mono assms less_Suc_eq less_sets_trans zero_less_Suc)
  qed auto
qed

lemma less_sets_Suc_Max:  
  assumes "finite A"
  shows "less_sets A {Suc (Max A)..}"
proof (cases "A = {}")
  case False
  then show ?thesis
    by (simp add: assms less_Suc_eq_le)
qed auto

lemma infinite_nat_greaterThan:
  fixes m::nat
  assumes "infinite N"
  shows "infinite (N \<inter> {m<..})"
proof -
  have "N \<subseteq> -{m<..} \<union> (N \<inter> {m<..})"
    by blast
  moreover have "finite (-{m<..})"
    by simp
  ultimately show ?thesis
    using assms finite_subset by blast
qed

end

    

