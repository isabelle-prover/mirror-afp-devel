(* Theory: PiE_Rel_Extras
   Author: Chelsea Edmonds *)

section\<open>Extensional function extras\<close>
text\<open>Counting lemmas (i.e. reasoning on cardinality) of sets on the extensional function relation \<close>

theory PiE_Rel_Extras imports Card_Partitions.Card_Partitions
begin

subsection \<open>Relations and Extensional Function sets \<close>
text \<open>A number of lemmas to convert between relations and functions for counting purposes. 
Note, ultimately not needed in this formalisation, but may be of use in the future \<close>

lemma Range_unfold: "Range r = {y. \<exists>x. (x, y) \<in> r}"
  by blast

definition fun_to_rel:: " 'a set \<Rightarrow> 'b set  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>('a \<times> 'b) set" where
"fun_to_rel A B f \<equiv> {(a, b) | a b . a \<in> A \<and> b \<in> B \<and> f a = b}"

definition rel_to_fun:: "('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> 'b)" where
"rel_to_fun R \<equiv> \<lambda> a . (if a \<in> Domain R then (THE b . (a, b) \<in> R) else undefined)"

lemma fun_to_relI: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> f a = b \<Longrightarrow> (a, b) \<in> fun_to_rel A B f"
  unfolding fun_to_rel_def by auto

lemma fun_to_rel_alt: "fun_to_rel A B f \<equiv> {(a, f a) | a b . a \<in> A \<and> f a \<in> B}"
  unfolding fun_to_rel_def by simp 

lemma fun_to_relI2: "a \<in> A \<Longrightarrow> f a \<in> B  \<Longrightarrow> (a, f a) \<in> fun_to_rel A B f"
  using fun_to_rel_alt by fast

lemma rel_to_fun_in[simp]: "a \<in> Domain R \<Longrightarrow> (rel_to_fun R) a = (THE b . (a, b) \<in> R)"
  unfolding rel_to_fun_def by simp

lemma rel_to_fun_undefined[simp]: "a \<notin> Domain R \<Longrightarrow> (rel_to_fun R) a = undefined"
  unfolding rel_to_fun_def by simp

lemma single_valued_unique_Dom_iff: "single_valued R \<longleftrightarrow> (\<forall> x \<in> Domain R. \<exists>! y . (x, y) \<in> R)"
  using single_valued_def by fastforce 

lemma rel_to_fun_range:
  assumes "single_valued R"
  assumes "a \<in> Domain R"
  shows "(THE b . (a, b) \<in> R) \<in> Range R"
  using single_valued_unique_Dom_iff
  by (metis Range_iff assms(1) assms(2) theI') 

lemma rel_to_fun_extensional: "single_valued R \<Longrightarrow> rel_to_fun R \<in> (Domain R \<rightarrow>\<^sub>E Range R)"
  by (intro PiE_I) (simp_all add: rel_to_fun_range)

lemma single_value_fun_to_rel:  "single_valued (fun_to_rel A B f)"
  unfolding single_valued_def fun_to_rel_def
  by simp

lemma fun_to_rel_domain: 
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "Domain (fun_to_rel A B f) = A"
  unfolding fun_to_rel_def using assms by (auto simp add: subset_antisym subsetI Domain_unfold)

lemma fun_to_rel_range: 
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "Range (fun_to_rel A B f) \<subseteq> B"
  unfolding fun_to_rel_def using assms by (auto simp add: subsetI Range_unfold)

lemma rel_to_fun_to_rel: 
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "rel_to_fun (fun_to_rel A B f) = f"
proof (intro ext allI)
  fix x
  show "rel_to_fun (fun_to_rel A B f) x = f x"
  proof (cases "x \<in> A")
    case True
    then have ind: "x \<in> Domain (fun_to_rel A B f)" using fun_to_rel_domain assms 
      by blast
    have "(x, f x) \<in> fun_to_rel A B f" using fun_to_rel_alt True single_value_fun_to_rel
      using assms by fastforce 
    moreover have "rel_to_fun (fun_to_rel A B f) x = (THE b. (x, b) \<in> (fun_to_rel A B f))" by (simp add: ind)
    ultimately show ?thesis using single_value_fun_to_rel single_valuedD the_equality
      by (metis (no_types, lifting)) 
  next
    case False
    then have "x \<notin> Domain (fun_to_rel A B f)" unfolding fun_to_rel_def
      by blast 
    then show ?thesis
      using False assms by auto 
  qed
qed

lemma fun_to_rel_to_fun: 
  assumes "single_valued R"
  shows "fun_to_rel (Domain R) (Range R) (rel_to_fun R) = R"
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> fun_to_rel (Domain R) (Range R) (rel_to_fun R)"
  then obtain a b where "x = (a, b)" and "a \<in> Domain R" and "b \<in> Range R" and "(rel_to_fun R a) = b"
    using fun_to_rel_def by (smt (verit) mem_Collect_eq) 
  then have "b = (THE b'. (a, b') \<in> R)" using rel_to_fun_in
    by simp 
  then show "x \<in> R"
    by (metis (no_types, lifting) \<open>a \<in> Domain R\<close> \<open>x = (a, b)\<close> assms single_valued_unique_Dom_iff the1_equality)
next
  fix x assume "x \<in> R"
  then obtain a b where "x = (a, b)" and "(a, b) \<in> R" and "\<forall> c . (a, c) \<in> R \<longrightarrow> b = c"
    using assms
    by (metis prod.collapse single_valued_def)
  then have "a \<in> Domain R" "b \<in> Range R" by blast+
  then have "b = (THE b' . (a, b') \<in> R)"
    by (metis \<open>\<forall>c. (a, c) \<in> R \<longrightarrow> b = c\<close> \<open>x = (a, b)\<close> \<open>x \<in> R\<close> the_equality) 
  then have "(a, b) \<in> fun_to_rel (Domain R) (Range R) (rel_to_fun R)"
    using \<open>a \<in> Domain R\<close> \<open>b \<in> Range R\<close> by (intro fun_to_relI) (simp_all)
  then show "x \<in> fun_to_rel (Domain R) (Range R) (rel_to_fun R)" using \<open>x = (a, b)\<close> by simp
qed

lemma bij_betw_fun_to_rel: 
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "bij_betw (\<lambda> a . (a, f a)) A (fun_to_rel A B f)"
proof (intro bij_betw_imageI inj_onI)
  show "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, f x) = (y, f y) \<Longrightarrow> x = y" by simp
next
  show "(\<lambda>a. (a, f a)) ` A = fun_to_rel A B f"
  proof (intro subset_antisym subsetI)
    fix x assume "x \<in> (\<lambda>a. (a, f a)) ` A"
    then obtain a where "a \<in> A" and "x = (a, f a)" by blast
    then show "x \<in> fun_to_rel A B f" using fun_to_rel_alt assms
      by fastforce 
  next
    fix x assume "x \<in> fun_to_rel A B f"
    then show "x \<in> (\<lambda>a. (a, f a)) ` A" using fun_to_rel_alt
      using image_iff by fastforce 
  qed
qed

lemma fun_to_rel_indiv_card: 
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "card (fun_to_rel A B f) = card A"
  using bij_betw_fun_to_rel assms bij_betw_same_card[of "(\<lambda> a . (a, f a))" A "(fun_to_rel A B f)"]
  by (metis)

lemma fun_to_rel_inj: 
  assumes "C \<subseteq> A \<rightarrow>\<^sub>E B"
  shows "inj_on (fun_to_rel A B) C"
proof (intro inj_onI ext allI)
  fix f g x  assume fin: "f \<in> C" and gin: "g \<in> C" and eq: "fun_to_rel A B f = fun_to_rel A B g"
  then show "f x = g x"
  proof (cases "x \<in> A")
    case True
    then have "(x, f x) \<in> fun_to_rel A B f" using fun_to_rel_alt
      by (smt (verit) PiE_mem assms fin fun_to_rel_def mem_Collect_eq subset_eq)
    moreover have "(x, g x) \<in> fun_to_rel A B g" using fun_to_rel_alt True
      by (smt (verit) PiE_mem assms fun_to_rel_def gin mem_Collect_eq subset_eq)
    ultimately show ?thesis  using eq single_value_fun_to_rel single_valued_def
      by metis 
  next
    case False
    then have "f x = undefined" "g x = undefined" using fin gin assms by auto 
    then show ?thesis by simp
  qed
qed

lemma fun_to_rel_ss: "fun_to_rel A B f \<subseteq> A \<times> B"
  unfolding fun_to_rel_def by auto

lemma card_fun_to_rel: "C \<subseteq> A \<rightarrow>\<^sub>E B \<Longrightarrow> card C = card ((\<lambda> f . fun_to_rel A B f ) ` C)"
  using card_image fun_to_rel_inj by metis 

subsection \<open>Cardinality Lemmas \<close>
text \<open>Lemmas to count variations of filtered sets over the extensional function set relation \<close>

lemma card_PiE_filter_range_set:
  assumes "\<And> a. a \<in> A' \<Longrightarrow> X a \<in> C"
  assumes "A' \<subseteq> A"
  assumes "finite A"
  shows "card {f \<in> A \<rightarrow>\<^sub>E C . \<forall> a \<in> A' . f a = X a} = (card C)^(card A - card A')"
proof -
  have finA: "finite A'" using assms(3) finite_subset assms(2) by auto 
  have c1: "card (A - A') = card A - card A'" using assms(2)
  using card_Diff_subset finA by blast 
  define g :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a  \<Rightarrow> 'b)" where "g \<equiv> \<lambda> f. (\<lambda> a' . if a' \<in> A' then undefined else f a')"
  have "bij_betw g {f \<in> A \<rightarrow>\<^sub>E C . \<forall> a \<in> A' . f a = X a} ((A - A') \<rightarrow>\<^sub>E C)"
  proof (intro bij_betw_imageI inj_onI)
    fix h h' assume h1in: "h \<in> {f \<in> A \<rightarrow>\<^sub>E C. \<forall> a \<in> A' . f a = X a}" and h2in: "h' \<in> {f \<in> A \<rightarrow>\<^sub>E C. \<forall> a \<in> A' . f a = X a}" "g h = g h'"
    then have eq: "(\<lambda> a' . if a' \<in> A' then undefined  else h a') = (\<lambda> a' .  if a' \<in> A' then undefined else h' a')"
      using g_def by simp
    show "h = h'"
    proof (intro ext allI)
      fix x
      show "h x = h' x" using h1in h2in eq by (cases "x \<in> A'", simp, meson)
    qed
  next
    show "g ` {f \<in> A \<rightarrow>\<^sub>E C. \<forall> a \<in> A' . f a = X a} = A - A' \<rightarrow>\<^sub>E C"
    proof (intro subset_antisym subsetI)
      fix g' assume "g' \<in> g ` {f \<in> A \<rightarrow>\<^sub>E C. \<forall> a \<in> A' . f a = X a}"
      then obtain f' where geq: "g' = g f'" and fin: "f' \<in> A \<rightarrow>\<^sub>E C" and "\<forall> a \<in> A' . f' a = X a"
        by blast
      show "g' \<in> A - A' \<rightarrow>\<^sub>E C"
        using g_def fin geq by (intro PiE_I)(auto)
    next
      fix g' assume gin: "g' \<in> A - A' \<rightarrow>\<^sub>E C"
      define f' where "f' = (\<lambda> a' . (if a' \<in> A' then X a' else g' a'))" 
      then have eqc: "\<forall> a' \<in> A' . f' a' = X a'" by auto
      have fin: "f' \<in> A \<rightarrow>\<^sub>E C"
      proof (intro PiE_I)
        fix x assume "x \<in> A"
        have "x \<notin> A' \<Longrightarrow> f' x = g' x" using f'_def by auto
        moreover have "x \<in> A' \<Longrightarrow> f' x = X x" using f'_def by (simp add: \<open>x \<in> A\<close>) 
        ultimately show "f' x \<in> C"
          using gin  PiE_E \<open>x \<in> A\<close> assms(1)[of x] by (metis Diff_iff) 
      next
        fix x assume "x \<notin> A"
        then show "f' x = undefined"
          using f'_def gin assms(2) by auto 
      qed
      have "g' = g f'" unfolding f'_def g_def 
        by (auto simp add: fun_eq_iff) (metis DiffE PiE_arb gin) 
      then show "g' \<in> g ` {f \<in> A \<rightarrow>\<^sub>E C. \<forall> a \<in> A' . f a = X a}" using fin eqc by blast
    qed
  qed
  then have "card {f \<in> A \<rightarrow>\<^sub>E C . \<forall> a \<in> A' . f a = X a} = card ((A - A') \<rightarrow>\<^sub>E C)"
    using bij_betw_same_card by blast
  also have "... = (card C)^card (A - A')" 
    using card_funcsetE assms(3) by (metis finite_Diff) 
  finally show ?thesis using c1 by auto
qed

lemma card_PiE_filter_range_indiv: "X a' \<in> C \<Longrightarrow> a' \<in> A \<Longrightarrow> finite A \<Longrightarrow>
    card {f \<in> A \<rightarrow>\<^sub>E C . f a' = X a'} = (card C)^(card A - 1)"
  using card_PiE_filter_range_set[of "{a'}" X C A ] by auto

lemma card_PiE_filter_range_set_const: "c \<in> C \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> finite A \<Longrightarrow> 
    card {f \<in> A \<rightarrow>\<^sub>E C . \<forall> a \<in> A' . f a = c} = (card C)^(card A - card A')"
  using card_PiE_filter_range_set[of A' "\<lambda> a . c"] by auto

lemma card_PiE_filter_range_set_nat: "c \<in> {0..<n} \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> finite A \<Longrightarrow>
    card {f \<in> A \<rightarrow>\<^sub>E {0..<n} . \<forall> a \<in> A' . f a = c} = n^(card A - card A')"
  using card_PiE_filter_range_set_const[of c "{0..<n}" A' A] by auto

end