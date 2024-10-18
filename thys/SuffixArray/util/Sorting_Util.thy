theory Sorting_Util
  imports Main
begin

section \<open>Lemmas about bijections\<close>

text \<open>A convenient definition of an inverses between two sets\<close>
definition 
  inverses_on :: 
  "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
where
  "inverses_on f g A B \<longleftrightarrow> 
     (\<forall>x \<in> A. g (f x) = x) \<and> 
     (\<forall>x \<in> B. f (g x) = x)"

lemmas inverses_onD1 = inverses_on_def[THEN iffD1, THEN conjunct1]
lemmas inverses_onD2 = inverses_on_def[THEN iffD1, THEN conjunct2]

text \<open>The inverses relation over maps\<close>

lemma inverses_on_mapD:
  assumes "inverses_on (map f) (map g) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
  shows "inverses_on f g A B"
proof -
  from inverses_onD1[OF assms, THEN bspec, of "[_]", simplified]
  have "\<forall>x \<in> A. g (f x) = x"
    by blast
  moreover
  from inverses_onD2[OF assms, THEN bspec, of "[_]", simplified]
  have "\<forall>x \<in> B. f (g x) = x"
    by blast
  ultimately show ?thesis
    by (simp add: inverses_on_def)
qed

lemma inverses_on_map:
  assumes "inverses_on f g A B"
  shows "inverses_on (map f) (map g) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
proof -
  have "\<forall>x \<in> {xs. set xs \<subseteq> A}. map g (map f x) = x"
    using list_eq_iff_nth_eq inverses_onD1 assms subsetD by fastforce
  moreover
  have "\<forall>x \<in> {xs. set xs \<subseteq> B}. map f (map g x) = x"
    using list_eq_iff_nth_eq inverses_onD2 assms subsetD by fastforce
  ultimately show ?thesis
    by (simp add: inverses_on_def)
qed

text \<open>Inverses are symmetric\<close>

lemma inverses_on_sym:
  "inverses_on f g A B = inverses_on g f B A"
  apply (simp add: inverses_on_def)
  apply (subst conj.commute)
  apply simp
  done

text \<open>Convenient theorem to obtain the inverse of a bijection between two sets\<close>

lemma bij_betw_inv_alt:
  assumes "bij_betw f A B"
  shows "\<exists>g. bij_betw g B A \<and> inverses_on f g A B"
  by (meson assms bij_betw_imp_inj_on bij_betw_inv_into inv_into_f_f
            bij_betw_inv_into_right inverses_on_def[THEN iffD2])

text \<open>Bijections over maps\<close>

lemma bij_betw_map:
  assumes "bij_betw f A B"
  shows "bij_betw (map f) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
proof (rule bij_betwI')
  fix x y
  assume "x \<in> {xs. set xs \<subseteq> A}" "y \<in> {xs. set xs \<subseteq> A}"
  hence P: "set x \<subseteq> A" "set y \<subseteq> A"
    by blast+
  note inj = inj_on_eq_iff[THEN iffD1, OF bij_betw_imp_inj_on[OF assms]]
  from list.inj_map_strong[OF inj, simplified]
  show "(map f x = map f y) = (x = y)"
    using P(1) P(2) by blast
next
  fix x
  assume "x \<in> {xs. set xs \<subseteq> A}"
  hence "set x \<subseteq> A"
    by blast
  then show "map f x \<in> {xs. set xs \<subseteq> B}"
    using assms bij_betw_imp_surj_on by fastforce
next
  fix y
  assume "y \<in> {xs. set xs \<subseteq> B}"
  hence "set y \<subseteq> B"
    by blast

  from bij_betw_inv_alt[OF assms, simplified inverses_on_def]
  obtain g where
    "bij_betw g B A"
    "\<forall>x\<in>A. g (f x) = x"
    "\<forall>x\<in>B. f (g x) = x"
    by blast

  have "set (map g y) \<subseteq> A"
    using \<open>bij_betw g B A\<close> \<open>set y \<subseteq> B\<close> bij_betw_imp_surj_on 
    by fastforce
  moreover
  have "y = map f (map g y)"
  proof -
    have "length y = length (map f (map g y))"
      by simp
    moreover
    have "\<forall>i < length y. y ! i = map f (map g y) ! i"
      using \<open>\<forall>x\<in>B. f (g x) = x\<close> \<open>set y \<subseteq> B\<close> subsetD by fastforce
    ultimately show ?thesis
      using list_eq_iff_nth_eq by blast
  qed
  ultimately have "\<exists>x. set x \<subseteq> A \<and> y = map f x"
    by blast
  then show "\<exists>x\<in>{xs. set xs \<subseteq> A}. y = map f x"
    by blast
qed

text \<open>Eliminating the map from a bijection relation\<close>

lemma bij_betw_mapD:
  assumes "bij_betw (map f) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
  shows "bij_betw f A B"
proof (intro bij_betwI' iffI)
  fix x y
  assume "x \<in> A" "y \<in> A" "f x = f y"
  with inj_onD[OF bij_betw_imp_inj_on[OF assms], of "[x]" "[y]", simplified]
  show "x = y"
    by blast
next
  fix x
  assume "x \<in> A"
  with bij_betwE[OF assms, THEN bspec, of "[x]", simplified]
  show "f x \<in> B"
    by blast
next
  fix y
  assume "y \<in> B"
  with bij_betw_imp_surj_on[OF assms, simplified]
  have "[y] \<in> map f ` {xs. set xs \<subseteq> A}"
    by auto
  with image_iff[THEN iffD1, of "[y]" "map f" "{xs. set xs \<subseteq> A}"]
  obtain x' where
    "x' \<in> {xs. set xs \<subseteq> A}"
    "[y] = map f x'"
    by meson
  then show "\<exists>x\<in>A. y = f x"
    by auto
next
qed(clarsimp)

text \<open>Obtaining the inverse over map\<close>

lemma bij_betw_inv_map:
  assumes "bij_betw f A B"
  shows "\<exists>g. bij_betw (map g) {xs. set xs \<subseteq> B} {xs. set xs \<subseteq> A} \<and>
             inverses_on (map f) (map g) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
proof -
  from bij_betw_inv_alt[OF assms, simplified inverses_on_def]
  obtain g where
    "bij_betw g B A"
    "\<forall>x\<in>A. g (f x) = x"
    "\<forall>x\<in>B. f (g x) = x"
    by blast

  note bij_betw_map[OF \<open>bij_betw g B A\<close>]
  moreover
  {
    have "\<forall>x. set x \<subseteq> A \<longrightarrow> map g (map f x) = x"
    proof safe
      fix x
      assume "set x \<subseteq> A"
      then show "map g (map f x) = x"
        by (clarsimp simp: list_eq_iff_nth_eq \<open>\<forall>x\<in>A. g (f x) = x\<close> subsetD)
    qed
    moreover
    have "\<forall>x. set x \<subseteq> B \<longrightarrow> map f (map g x) = x"
    proof safe
      fix x
      assume "set x \<subseteq> B"
      then show "map f (map g x) = x"
        by (clarsimp simp: list_eq_iff_nth_eq \<open>\<forall>x\<in>B. f (g x) = x\<close> subsetD)
    qed
    ultimately have 
      "inverses_on (map f) (map g) {xs. set xs \<subseteq> A} {xs. set xs \<subseteq> B}"
      by (simp add: inverses_on_def)
  }
  ultimately show ?thesis
    by blast
qed

section "Lemmas about monotone functions"

text \<open>Note that the base version of monotone is used as 
      the sorts cause some issues with the types\<close>

text \<open>Essentially a general version of @{thm strict_mono_less}\<close>

lemma monotone_on_iff:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on (f ` A) ordb"
  and     "totalp_on (f ` A) ordb"
  and     "x \<in> A"
  and     "y \<in> A"
shows "orda x y \<longleftrightarrow> ordb (f x) (f y)"
proof (safe)
  show "orda x y \<Longrightarrow> ordb (f x) (f y)"
    by (meson assms monotone_onD)
next
  show "ordb (f x) (f y) \<Longrightarrow> orda x y"
    by (metis (full_types) assms(1,3,4,6,7) 
          asymp_onD monotone_onD totalp_onD imageI)
qed

text \<open>The inverse of a monotonic function is also monotonic\<close>

lemma monotone_on_bij_betw_inv:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on B ordb"
  and     "totalp_on B ordb"
  and     "bij_betw f A B"
  and     "bij_betw g B A"
  and     "inverses_on f g A B"
shows "monotone_on B ordb orda g"
proof (rule monotone_onI)
  fix x y
  assume "x \<in> B" "y \<in> B" "ordb x y"
  moreover
  have "g x \<in> A"
    using \<open>bij_betw g B A\<close> bij_betwE calculation(1) by auto
  moreover
  have "f (g x) = x"
    using assms(8) calculation(1) inverses_onD2 by blast
  moreover
  have "g y \<in> A"
    using \<open>bij_betw g B A\<close> bij_betwE calculation(2) by auto
  moreover
  have "f (g y) = y"
    using assms(8) calculation(2) inverses_onD2 by blast
  ultimately show "orda (g x) (g y)"
    using assms bij_betw_imp_surj_on monotone_on_iff by fastforce
qed

lemma monotone_on_bij_betw:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on B ordb"
  and     "totalp_on B ordb"
  and     "bij_betw f A B"
shows "\<exists>g. bij_betw g B A \<and> inverses_on f g A B \<and> monotone_on B ordb orda g"
  using assms bij_betw_inv_alt monotone_on_bij_betw_inv by fastforce

section "Sorting"

subsection "General sorting"

text \<open>Intro for @{const sorted_wrt}\<close>

lemmas sorted_wrtI = sorted_wrt_iff_nth_less[THEN iffD2, OF allI, OF allI, OF impI, OF impI]

lemma sorted_wrt_mapI:
  "(\<And>i j. \<lbrakk>i < j; j < length xs\<rbrakk> \<Longrightarrow> P (f (xs ! i)) (f (xs ! j))) \<Longrightarrow>
    sorted_wrt P (map f xs)"
  by (metis (mono_tags, lifting) length_map nth_map order_less_trans sorted_wrtI)

lemma sorted_wrt_mapD:
  "(\<And>i j. \<lbrakk>sorted_wrt P (map f xs); i < j; j < length xs\<rbrakk> \<Longrightarrow> P (f (xs ! i)) (f (xs ! j)))"
  by (metis (mono_tags, lifting) length_map nth_map order_less_trans sorted_wrt_iff_nth_less)

lemma monotone_on_sorted_wrt_map:
  assumes "monotone_on A orda ordb f"
  and     "sorted_wrt orda xs"
  and     "set xs \<subseteq> A"
shows "sorted_wrt ordb (map f xs)"
proof (rule sorted_wrt_mapI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_nth_less[OF assms(2)]
  have "orda (xs ! i) (xs ! j)"
    by blast
  with monotone_onD[OF assms(1), of "xs ! i" "xs ! j"] assms(3)
  show "ordb (f (xs ! i)) (f (xs ! j))"
    by (meson \<open>i < j\<close> \<open>j < length xs\<close> nth_mem order_less_trans subsetD)
qed

lemma monotone_on_map_sorted_wrt:
  assumes "monotone_on A orda ordb f"
  and     "asymp_on A orda"
  and     "totalp_on A orda"
  and     "asymp_on (f ` A) ordb"
  and     "totalp_on (f ` A) ordb"
  and     "sorted_wrt ordb (map f xs)"
  and     "set xs \<subseteq> A"
shows "sorted_wrt orda xs"
proof (rule sorted_wrtI)
  fix i j
  assume "i < j" "j < length xs"
  with sorted_wrt_nth_less[OF assms(6)]
  have "ordb (f (xs ! i)) (f (xs ! j))"
    by force
  with monotone_on_iff[OF assms(1-3), of "xs ! i" "xs ! j"]
  show "orda (xs ! i) (xs ! j)"
    using \<open>i < j\<close> \<open>j < length xs\<close> assms(4,5,7) 
          nth_mem order_less_trans by blast
qed

subsection "Sorting on linear orders"

context linorder begin

abbreviation "strict_sorted xs \<equiv> sorted_wrt (<) xs"

lemma sorted_nth_less_mono:
  "\<lbrakk>sorted xs; i < length xs; j < length xs; i \<noteq> j; xs ! i < xs ! j\<rbrakk> \<Longrightarrow> i < j"
  by (meson linorder_neqE_nat not_less sorted_iff_nth_mono_less)

lemma strict_sorted_nth_less_mono:
  "\<lbrakk>strict_sorted xs; i < length xs; j < length xs; i \<noteq> j; xs ! i < xs ! j\<rbrakk> \<Longrightarrow> i < j"
  using strict_sorted_iff sorted_nth_less_mono by blast

lemma strict_sorted_Min:
  "\<lbrakk>strict_sorted xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> xs ! 0 = Min (set xs)"
  by (metis finite_set list.simps(15) Min_insert2 strict_sorted_imp_sorted
            nth_Cons_0 sorted_wrt.elims(2))

lemma strict_sorted_take:
  assumes "strict_sorted xs"
  and     "i < length xs"
  shows "set (take i xs) = {x. x \<in> set xs \<and> x < xs ! i}"
proof (safe)
  fix x
  assume "x \<in> set (take i xs)"
  then show "x \<in> set xs"
    by (meson in_set_takeD)
next
  fix x
  assume "x \<in> set (take i xs)"
  then show "x < xs ! i"
    by (metis assms id_take_nth_drop list.set_intros(1) sorted_wrt_append)
next
  fix x
  assume "x \<in> set xs" "x < xs ! i"
  hence "\<exists>j < length xs. xs ! j = x"
    by (simp add: in_set_conv_nth)
  then obtain j where
    "j < length xs" "xs ! j = x"
    by blast
  with strict_sorted_nth_less_mono[OF assms(1) _ assms(2), of j] \<open>x < xs ! i\<close>
  have "j < i"
    by blast
  then show "x \<in> set (take i xs)"
    using \<open>j < length xs\<close> \<open>xs ! j = x\<close> in_set_conv_nth by fastforce
qed

lemma strict_sorted_card_idx:
  "\<lbrakk>strict_sorted xs; i < length xs\<rbrakk> \<Longrightarrow> card {x. x \<in> set xs \<and> x < xs ! i} = i"
  by (metis (mono_tags, lifting) distinct_card distinct_take length_take strict_sorted_iff
                                 ord_class.min_def order_class.leD strict_sorted_take)

lemmas strict_sorted_distinct_set_unique =
  sorted_distinct_set_unique[OF strict_sorted_imp_sorted _ strict_sorted_imp_sorted]

lemma sorted_and_distinct_imp_strict_sorted:
  "\<lbrakk>sorted xs; distinct xs\<rbrakk> \<Longrightarrow> strict_sorted xs"
  using strict_sorted_iff
  by blast

lemma filter_sorted:
  "sorted xs \<Longrightarrow> sorted (filter P xs)"
  using sorted_wrt_filter by blast

lemma sorted_nth_eq:
  assumes "sorted xs"
  and     "j < length xs"
  and     "xs ! i = xs ! j"
  and     "i \<le> k"
  and     "k \<le> j"
shows "xs ! k = xs ! i"
  by (metis assms sorted_iff_nth_mono preorder_class.le_less_trans nle_le)

lemma sorted_find_Min:
  "sorted xs \<Longrightarrow> \<exists>x \<in> set xs. P x \<Longrightarrow> List.find P xs = Some (Min {x\<in>set xs. P x})"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) show ?case
  proof (cases "P x")
    case True
    with Cons show ?thesis by (auto intro: Min_eqI [symmetric])
  next
    case False then have "{y. (y = x \<or> y \<in> set xs) \<and> P y} = {y \<in> set xs. P y}"
      by auto
    with Cons False show ?thesis by (simp_all)
  qed
qed

lemma sorted_cons_nil:
  "xs = [] \<Longrightarrow> sorted (x # xs)"
  by simp

lemma sorted_consI:
  "\<lbrakk>xs \<noteq> []; sorted xs; x \<le> xs ! 0\<rbrakk> \<Longrightarrow> sorted (x # xs)"
  by (metis list.exhaust sorted2_simps(2) nth_Cons_0)

end (* of context *)

subsection "Sorting on orders"

context order begin

lemma strict_mono_strict_sorted_map_1:
  assumes "strict_mono \<alpha>"
  and     "strict_sorted xs"
shows "strict_sorted (map \<alpha> xs)"
  using assms(1) assms(2) monotone_on_sorted_wrt_map by blast

lemma strict_mono_sorted_map_2:
  assumes "strict_mono \<alpha>"
  and     "strict_sorted (map \<alpha> xs)"
shows "strict_sorted xs"
  using assms(1) assms(2) monotone_on_map_sorted_wrt by fastforce

end (* of context *)

section "Mapping elements to natural numbers"

text \<open>This section contains a mapping from elements to natural numbers that maintains ordering.\<close>

definition elm_rank :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> nat"
  where
"elm_rank ord A x = card {y. y \<in> A \<and> ord y x}"

lemma monotone_on_elm_rank:
  assumes "finite A"
  and     "transp_on A ord"
  and     "irreflp_on A ord"
  shows "monotone_on A ord (<) (elm_rank ord A)"
proof (rule monotone_onI)
  fix a b
  assume "a \<in> A" "b \<in> A" "ord a b"

  have "{y. y \<in> A \<and> ord y a} \<subseteq> {y. y \<in> A \<and> ord y b}"
  proof safe
    fix x
    assume "x \<in> A" "ord x a"
    then show "ord x b"
      by (meson \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>ord a b\<close> assms(2) transp_onD)
  qed
  moreover
  have "a \<in> {y. y \<in> A \<and> ord y b}"
    by (simp add: \<open>a \<in> A\<close> \<open>ord a b\<close>)
  moreover
  have "a \<notin> {y. y \<in> A \<and> ord y a}"
    using assms(3) irreflp_onD by fastforce
  ultimately have "{y. y \<in> A \<and> ord y a} \<subset> {y. y \<in> A \<and> ord y b}"
    by blast
  then show "elm_rank ord A a < elm_rank ord A b"
    by (simp add: elm_rank_def assms(1) psubset_card_mono)
qed

lemma elm_rank_insert_min:
  assumes "finite A"
  and     "x \<notin> A"
  and     "\<forall>y \<in> A. ord x y"
  and     "z \<in> A"
shows "elm_rank ord (insert x A) z = Suc (elm_rank ord A z)"
  unfolding elm_rank_def
proof -
  have "ord x z"
    by (simp add: assms(3,4))
  hence "{y \<in> insert x A. ord y z} = insert x {y \<in> A. ord y z}"
    by safe
  moreover
  have "x \<notin> {y \<in> A. ord y z}"
    using assms(2) by auto
  ultimately show "card {y \<in> insert x A. ord y z} = Suc (card {y \<in> A. ord y z})"
    by (simp add: assms(1))
qed

definition (in order) elem_rank :: "'a set \<Rightarrow> 'a \<Rightarrow> nat"
  where
"elem_rank = elm_rank (<)"

lemma (in order) strict_mono_on_elem_rank:
  assumes "finite A"
  shows "strict_mono_on A (elem_rank A)"
  by (simp add: assms elem_rank_def monotone_on_elm_rank)

lemma (in linorder) bij_betw_elem_rank_upt:
  assumes "finite A"
  shows "bij_betw (elem_rank A) A {0..<card A}"
proof -
  have "\<And>x. x \<in> A \<Longrightarrow> {y. y \<in> A \<and> y < x} \<subset> A"
    by blast
  hence "\<And>x. x \<in> A \<Longrightarrow> card {y. y \<in> A \<and> y < x} < card A"
    by (meson assms psubset_card_mono)
  hence "\<And>x. x \<in> A \<Longrightarrow> elem_rank A x \<in> {0..<card A}"
    by (simp add: elm_rank_def elem_rank_def)
  moreover
  have "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> (elem_rank A x = elem_rank A y) = (x = y)"
    by (metis assms less_irrefl_nat antisym_conv3 ord.strict_mono_onD strict_mono_on_elem_rank)
  moreover
  {
    let ?xs = "sorted_list_of_set A"
    have "strict_sorted ?xs"
      by simp
    moreover
    have "\<And>x. elem_rank A x = elem_rank (set ?xs) x"
      using assms by force
    moreover
    have "\<And>y. y < length ?xs \<Longrightarrow> y = elem_rank (set ?xs) (?xs ! y)"
      by (metis (no_types, lifting) Collect_cong calculation(1) elem_rank_def elm_rank_def
                                    strict_sorted_card_idx)
    ultimately have "\<And>y. y \<in> {0..<card A} \<Longrightarrow> \<exists>x\<in>A. y = elem_rank A x"
      by (metis assms length_sorted_list_of_set set_sorted_list_of_set nth_mem
                ord_class.atLeastLessThan_iff)
  }
  ultimately show ?thesis
    using bij_betwI' by blast
qed

lemma (in order) elem_rank_insert_min:
  "\<lbrakk>finite A; x \<notin> A; \<forall>y\<in>A. x < y; z \<in> A\<rbrakk> \<Longrightarrow> elem_rank (insert x A) z = Suc (elem_rank A z)"
  by (simp add: elm_rank_insert_min elem_rank_def)
end
