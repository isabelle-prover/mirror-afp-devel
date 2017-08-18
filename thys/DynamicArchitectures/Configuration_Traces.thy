(*  Title:      Configuration_Traces.thy
    Author:     Diego Marmsoler
*)
section "A Theory of Dynamic Architectures"
text {*
  The following theory formalizes configuration traces~\cite{Marmsoler2016a,Marmsoler2016} as a model for dynamic architectures.
  Since configuration traces may be finite as well as infinite, the theory depends on Lochbihler's theory of co-inductive lists~\cite{Lochbihler2010}.
*}
theory Configuration_Traces
  imports Coinductive.Coinductive_List
begin
text {*
  In the following we first provide some preliminary results for extended natural numbers and lazy lists.
  Then, we formalize the notion of configuration traces and provide some basic properties thereof.
*}

subsection "Extended Natural Numbers"
text {*
  We provide one simple property for the \emph{strict} order over extended natural numbers.
*}
lemma enat_min:
  assumes "m \<ge> enat n'"
    and "enat n < m - enat n'"
  shows "enat n + enat n' < m" 
  using assms by (metis add.commute enat.simps(3) enat_add_mono enat_add_sub_same le_iff_add)
  
subsection "Lazy Lists"
text {*
  In the following we provide some additional notation and properties for lazy lists.
*}
notation LNil ("[]\<^sub>l")
notation LCons (infixl "#\<^sub>l" 60)
notation lappend (infixl "@\<^sub>l" 60)

lemma lnth_lappend[simp]:
  assumes "lfinite xs"
    and "\<not> lnull ys"
  shows "lnth (xs @\<^sub>l ys) (the_enat (llength xs)) = lhd ys"
proof -
  from assms have "\<exists>k. llength xs = enat k" using lfinite_conv_llength_enat by auto
  then obtain k where "llength xs = enat k" by blast
  hence "lnth (xs @\<^sub>l ys) (the_enat (llength xs)) = lnth ys 0"
    using lnth_lappend2[of xs k k ys] by simp
  with assms show ?thesis using lnth_0_conv_lhd by simp
qed

lemma lfilter_ltake:
  assumes "\<forall>(n::nat)\<le>llength xs. n\<ge>i \<longrightarrow> (\<not> P (lnth xs n))"
  shows "lfilter P xs = lfilter P (ltake i xs)"
proof -
  have "lfilter P xs = lfilter P ((ltake i xs) @\<^sub>l (ldrop i xs))"
    using lappend_ltake_ldrop[of "(enat i)" xs] by simp
  hence "lfilter P xs = (lfilter P ((ltake i) xs)) @\<^sub>l (lfilter P (ldrop i xs))" by simp
  show ?thesis
  proof cases
    assume "enat i \<le> llength xs"
  
    have "\<forall>x<llength (ldrop i xs). \<not> P (lnth (ldrop i xs) x)"
    proof (rule allI)
      fix x show "enat x < llength (ldrop (enat i) xs) \<longrightarrow> \<not> P (lnth (ldrop (enat i) xs) x)"
      proof
        assume "enat x < llength (ldrop (enat i) xs)"
        moreover have "llength (ldrop (enat i) xs) = llength xs - enat i"
          using llength_ldrop[of "enat i"] by simp
        ultimately have "enat x < llength xs - enat i" by simp
        with `enat i \<le> llength xs` have "enat x + enat i < llength xs"
          using enat_min[of i "llength xs" x] by simp
        moreover have "enat i + enat x = enat x + enat i" by simp
        ultimately have "enat i + enat x < llength xs" by arith
        hence "i + x < llength xs" by simp
        hence "lnth (ldrop i xs) x = lnth xs (x + the_enat i)" using lnth_ldrop[of "enat i" "x" xs] by simp
        moreover have "x + i \<ge> i" by simp
        with assms `i + x < llength xs` have "\<not> P (lnth xs (x + the_enat i))"
          by (simp add: assms(1) add.commute)
        ultimately show "\<not> P (lnth (ldrop i xs) x)" using assms by simp
      qed
    qed
    hence "lfilter P (ldrop i xs) = []\<^sub>l" by (metis diverge_lfilter_LNil in_lset_conv_lnth)
    with `lfilter P xs = (lfilter P ((ltake i) xs)) @\<^sub>l (lfilter P (ldrop i xs))`
      show "lfilter P xs = lfilter P (ltake i xs)" by simp
  next
    assume "\<not> enat i \<le> llength xs"
    hence "enat i > llength xs" by simp
    hence "ldrop i xs = []\<^sub>l" by simp
    hence "lfilter P (ldrop i xs) = []\<^sub>l" using lfilter_LNil[of P] by arith
    with `lfilter P xs = (lfilter P ((ltake i) xs)) @\<^sub>l (lfilter P (ldrop i xs))`
      show "lfilter P xs = lfilter P (ltake i xs)" by simp        
  qed
qed

lemma lfilter_lfinite[simp]:
  assumes "lfinite (lfilter P t)"
    and "\<not> lfinite t"
  shows "\<exists>n. \<forall>n'>n. \<not> P (lnth t n')"
proof -
  from assms have "finite {n. enat n < llength t \<and> P (lnth t n)}" using lfinite_lfilter by auto
  then obtain k
    where sset: "{n. enat n < llength t \<and> P (lnth t n)} \<subseteq> {n. n<k \<and> enat n < llength t \<and> P (lnth t n)}"
    using finite_nat_bounded[of "{n. enat n < llength t \<and> P (lnth t n)}"] by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not>(\<exists>n. \<forall>n'>n. \<not> P (lnth t n'))"
    hence "\<forall>n. \<exists>n'>n. P (lnth t n')" by simp
    then obtain n' where "n'>k" and "P (lnth t n')" by auto
    moreover from `\<not> lfinite t` have "n' < llength t" by (simp add: not_lfinite_llength)
    ultimately have "n' \<notin> {n. n<k \<and> enat n < llength t \<and> P (lnth t n)}" and
      "n'\<in>{n. enat n < llength t \<and> P (lnth t n)}" by auto
    with sset show False by auto
  qed
qed
  
subsection "A Model of Dynamic Architectures"
text {*
  In the following we formalize dynamic architectures in terms of configuration traces.
  Moreover, we formalize component behavior in terms of behavior traces.
*}

text {*
  In our model, each component has an abstract notion of state and is identified by means of an identifier.
*}
typedecl state
typedecl cid
text {*
  Note that @{type state} and @{type cid} act as parameters for our theory.
*}

record cmp =
  name :: cid
  state :: state

text {*
  A set of components is called healthy if each component is uniquely identified by its name.
*}
definition healthy :: "cmp set \<Rightarrow> bool"
  where "healthy C \<equiv> \<forall>c\<in>C.\<forall>d\<in>C. name c=name d \<longrightarrow> c=d"

text {*
  In the following we introduce a function to obtain a component from a set of components, based on its identifier.
*}
definition tCMP :: "cid \<Rightarrow> cmp set \<Rightarrow> cmp"
  where "tCMP i C \<equiv> (THE c. c\<in>C \<and> name(c)=i)"

text {*
  For healthy sets of components @{text C}, which contain a component with name @{text i}, @{term "tCMP i C"} is well-defined.
*}
lemma healtyCMP1:
  fixes C::"cmp set"
  assumes hC: "healthy C"
    and "c\<in>C"
    and "name c=i"
  shows "tCMP i C = c"
proof -
  have "tCMP i C = (THE c. c\<in>C \<and> name(c)=i)" unfolding tCMP_def ..
  moreover have "(THE c. c\<in>C \<and> name(c)=i) = c"
  proof (rule the_equality)
    from assms show "c \<in> C \<and> name c = i" by simp
    fix c' show "c' \<in> C \<and> name c' = i \<Longrightarrow> c' = c"
    proof -
      assume "c' \<in> C \<and> name c' = i"
      with `c \<in> C \<and> name c = i` show "c' = c" using hC healthy_def by simp
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma healtyCMP2:
  fixes C::"cmp set"
  assumes "healthy C"
    and "\<exists>c\<in>C. name c = i"
  shows "name (tCMP i C)=i"
    and "(tCMP i C)\<in>C" using assms healtyCMP1 by auto
  
text {*
  An architecture configuration is then modeled by a set of currently active components.
  Note that for the purpose of this theory, connections between components are not considered.
  A theory of a concrete architecture would model it as equalities between component ports.
*}
type_synonym conf = "cmp set"

subsubsection "Behavior Traces"
text {*
  A component's behavior is modeled in terms of behavior traces, i.e., a (finite or infinite) sequence of component states.
*}
type_synonym BTrace = "state llist"
type_synonym BTraceINF = "nat \<Rightarrow> state"

subsubsection "Configuration Traces"
text {*
  A dynamic architecture is then modeled in terms of configuration traces, i.e., a (finite or infinite) sequence of architecture configurations.
*}
type_synonym CTrace = "conf llist"
type_synonym CTraceINF = "nat \<Rightarrow> conf"

consts arch :: "CTrace set"
  
subsubsection "Active Components"
text {*
  In the following, we introduce a predicate to check whether a certain component is active in an architecture configuration.
*}
definition active :: "cid \<Rightarrow> conf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
  where "\<parallel>i\<parallel>\<^bsub>k\<^esub> \<equiv> {c\<in>k. name(c)=i} \<noteq> {}"

lemma lActive_least:
  assumes "\<exists>i\<ge>n. i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<exists>i\<ge>n. (i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub> \<and> (\<nexists>k. n\<le>k \<and> k<i \<and> k<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>))"
proof -
  let ?L = "LEAST i. (i\<ge>n \<and> i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
  from assms have "?L\<ge>n \<and> ?L < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t ?L\<^esub>"
    using LeastI[of "\<lambda>x::nat.(x\<ge>n \<and> x<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t x\<^esub>)"] by auto
  moreover have "\<nexists>k. n\<le>k \<and> k<llength t \<and> k<?L \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" using not_less_Least by auto
  ultimately show ?thesis by blast
qed
  
subsection "Projection"
text {*
  In the following we introduce an operator which extracts the behavior of a certain component out of a given configuration trace.
*}

definition proj:: "cid \<Rightarrow> CTrace \<Rightarrow> BTrace" ("\<pi>\<^bsub>_\<^esub>(_)" [0,110]60) 
  where "proj c = lmap (\<lambda>cnf. state (tCMP c cnf)) \<circ> (lfilter (active c))"
    
lemma proj_lnil [simp,intro]:
  "\<pi>\<^bsub>c\<^esub>([]\<^sub>l) = []\<^sub>l" using proj_def by simp

lemma proj_lnull [simp]:
  "\<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l \<longleftrightarrow> (\<forall>k \<in> lset t. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>)"
proof
  assume "\<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l"
  hence "lfilter (active c) t = []\<^sub>l" using proj_def lmap_eq_LNil by auto
  thus "\<forall>k \<in> lset t. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>" using lfilter_eq_LNil[of "active c"] by simp
next
  assume "\<forall>k\<in>lset t. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>"
  hence "lfilter (active c) t = []\<^sub>l" by simp
  thus "\<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l" using proj_def by simp
qed
  
lemma proj_LCons [simp]:
  "\<pi>\<^bsub>i\<^esub>(x #\<^sub>l xs) = (if \<parallel>i\<parallel>\<^bsub>x\<^esub> then (state (tCMP i x)) #\<^sub>l (\<pi>\<^bsub>i\<^esub>(xs)) else \<pi>\<^bsub>i\<^esub>(xs))"
  using proj_def by simp
    
lemma proj_llength[simp]:
  "llength (\<pi>\<^bsub>c\<^esub>(t)) \<le> llength t"
  using llength_lfilter_ile proj_def by simp
    
lemma proj_ltake:
  assumes "\<forall>(n'::nat)\<le>llength t. n'\<ge>n \<longrightarrow> (\<not> \<parallel>c\<parallel>\<^bsub>lnth t n'\<^esub>)"
  shows "\<pi>\<^bsub>c\<^esub>(t) = \<pi>\<^bsub>c\<^esub>(ltake n t)" using lfilter_ltake proj_def assms by (metis comp_apply)
    
lemma proj_finite_bound:
  assumes "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  shows "\<exists>n. \<forall>n'>n. \<not> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>"
  using assms lfilter_lfinite[of "active c" "inf_llist t"] proj_def by simp

subsubsection "Monotonicity and Continuity"

lemma proj_mcont:
  shows "mcont lSup lprefix lSup lprefix (proj c)"
proof -
  have "mcont lSup lprefix lSup lprefix (\<lambda>x. lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) x))"
    by simp
  moreover have "(\<lambda>x. lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) x)) =
    lmap (\<lambda>cnf. state (tCMP c cnf)) \<circ> lfilter (active c)" by auto
  ultimately show ?thesis using proj_def by simp
qed

lemma proj_mcont2mcont:
  assumes "mcont lub ord lSup lprefix f"
  shows "mcont lub ord lSup lprefix (\<lambda>x. \<pi>\<^bsub>c\<^esub>(f x))"
proof -
  have "mcont lSup lprefix lSup lprefix (proj c)" using proj_mcont by simp
  with assms show ?thesis using llist.mcont2mcont[of lSup lprefix "proj c"] by simp
qed
    
lemma proj_mono_prefix[simp]:
  assumes "lprefix t t'"
  shows "lprefix (\<pi>\<^bsub>c\<^esub>(t)) (\<pi>\<^bsub>c\<^esub>(t'))"
proof -
  from assms have "lprefix (lfilter (active c) t) (lfilter (active c) t')" using lprefix_lfilterI by simp
  hence "lprefix (lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) t))
    (lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) t'))" using lmap_lprefix by simp
  thus ?thesis using proj_def by simp
qed
 
subsubsection "Finiteness"
    
lemma proj_finite[simp]:
  assumes "lfinite t"
  shows "lfinite (\<pi>\<^bsub>c\<^esub>(t))"
  using assms proj_def by simp

lemma proj_finite2:
  assumes "\<forall>(n'::nat)\<le>llength t. n'\<ge>n \<longrightarrow> (\<not> \<parallel>c\<parallel>\<^bsub>lnth t n'\<^esub>)"
  shows "lfinite (\<pi>\<^bsub>c\<^esub>(t))" using assms proj_ltake proj_finite by simp

lemma proj_append_lfinite[simp]:
  fixes t t'
  assumes "lfinite t"
  shows "\<pi>\<^bsub>c\<^esub>(t @\<^sub>l t') = (\<pi>\<^bsub>c\<^esub>(t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(t'))" (is "?lhs=?rhs")
proof -
  have "?lhs = (lmap (\<lambda>cnf. state (tCMP c cnf)) \<circ> (lfilter (active c))) (t @\<^sub>l t')" using proj_def by simp
  also have "\<dots> = lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) (t @\<^sub>l t'))" by simp
  also from assms have "\<dots> = lmap (\<lambda>cnf. state (tCMP c cnf))
    ((lfilter (active c) t) @\<^sub>l (lfilter (active c) t'))" by simp
  also have "\<dots> = op @\<^sub>l (lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) t))
    (lmap (\<lambda>cnf. state (tCMP c cnf)) (lfilter (active c) t'))" using lmap_lappend_distrib by simp
  also have "\<dots> = ?rhs" using proj_def by simp
  finally show ?thesis .
qed
  
lemma proj_one:
  assumes "\<exists>i. i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "llength (\<pi>\<^bsub>c\<^esub>(t)) \<ge> 1"
proof -
  from assms have "\<exists>x\<in>lset t. \<parallel>c\<parallel>\<^bsub>x\<^esub>" using lset_conv_lnth by force
  hence "\<not> lfilter (\<lambda>k. \<parallel>c\<parallel>\<^bsub>k\<^esub>) t = []\<^sub>l" using lfilter_eq_LNil[of "(\<lambda>k. \<parallel>c\<parallel>\<^bsub>k\<^esub>)"] by blast
  hence "\<not> \<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l" using proj_def by fastforce
  thus ?thesis by (simp add: ileI1 lnull_def one_eSuc)
qed

subsubsection "Projection Not Active"
  
lemma proj_not_active[simp]:
  assumes "enat n < llength t"
    and "\<not> \<parallel>c\<parallel>\<^bsub>lnth t n\<^esub>"
  shows "\<pi>\<^bsub>c\<^esub>(ltake (Suc n) t) = \<pi>\<^bsub>c\<^esub>(ltake n t)" (is "?lhs = ?rhs")
proof -
  from assms have "ltake (enat (Suc n)) t = (ltake (enat n) t) @\<^sub>l ((lnth t n) #\<^sub>l []\<^sub>l)"
    using ltake_Suc_conv_snoc_lnth by blast
  hence "?lhs = \<pi>\<^bsub>c\<^esub>((ltake (enat n) t) @\<^sub>l ((lnth t n) #\<^sub>l []\<^sub>l))" by simp
  moreover have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>((lnth t n) #\<^sub>l []\<^sub>l))" by simp
  moreover from assms have "\<pi>\<^bsub>c\<^esub>((lnth t n) #\<^sub>l []\<^sub>l) = []\<^sub>l" by simp
  ultimately show ?thesis by simp
qed

lemma proj_not_active_same:
  assumes "enat n \<le> (n'::enat)"
      and "\<not> lfinite t \<or> n'-1 < llength t"
      and "\<nexists>k. k\<ge>n \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    shows "\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake n t)"
proof -
  have "\<pi>\<^bsub>c\<^esub>(ltake (n + (n' - n)) t) = \<pi>\<^bsub>c\<^esub>((ltake n t) @\<^sub>l (ltake (n'-n) (ldrop n t)))"
    by (simp add: ltake_plus_conv_lappend)
  hence "\<pi>\<^bsub>c\<^esub>(ltake (n + (n' - n)) t) =
    (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(ltake (n'-n) (ldrop n t)))" by simp
  moreover have "\<pi>\<^bsub>c\<^esub>(ltake (n'-n) (ldrop n t)) = []\<^sub>l"
  proof -
    have "\<forall>k\<in>{lnth (ltake (n' - enat n) (ldrop (enat n) t)) na |
      na. enat na < llength (ltake (n' - enat n) (ldrop (enat n) t))}. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>"
    proof
      fix k assume "k\<in>{lnth (ltake (n' - enat n) (ldrop (enat n) t)) na |
        na. enat na < llength (ltake (n' - enat n) (ldrop (enat n) t))}"
      then obtain k' where "enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))"
        and "k=lnth (ltake (n' - enat n) (ldrop (enat n) t)) k'" by auto
      have "enat (k' + n) < llength t"
      proof -
        from `enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))` have "enat k' < n'-n" by simp
        hence "enat k' + n < n'" using assms(1) enat_min by auto
        show ?thesis
        proof cases
          assume "lfinite t"
          with `\<not> lfinite t \<or> n'-1 < llength t` have "n'-1<llength t" by simp
          hence "n'< eSuc (llength t)" by (metis eSuc_minus_1 enat_minus_mono1 leD leI)
          hence "n'\<le> llength t" using eSuc_ile_mono ileI1 by blast
          with `enat k' + n < n'` show ?thesis by (simp add: add.commute)
        next
          assume "\<not> lfinite t"
          hence "llength t = \<infinity>" using not_lfinite_llength by auto
          thus ?thesis by simp
        qed
      qed
      moreover have "k = lnth t (k' + n)"
      proof -
        from \<open>enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))\<close>
          have "enat k'<n' - enat n" by auto
        hence "lnth (ltake (n' - enat n) (ldrop (enat n) t)) k' = lnth (ldrop (enat n) t) k'"
          using lnth_ltake[of k' "n' - enat n"] by simp
        with `enat (k' + n) < llength t` show ?thesis using lnth_ldrop[of n k' t ]
          using \<open>k = lnth (ltake (n' - enat n) (ldrop (enat n) t)) k'\<close> by (simp add: add.commute)
      qed
      moreover from `enat n \<le> (n'::enat)` have "k' + the_enat n\<ge>n" by auto
      moreover from `enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))` have "k' + n<n'"
        using assms(1) enat_min by auto
      ultimately show "\<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>" using `\<nexists>k. k\<ge>n \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>` by simp
    qed
    hence "\<forall>k\<in>lset (ltake (n'-n) (ldrop n t)). \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>"
      using lset_conv_lnth[of "(ltake (n' - enat n) (ldrop (enat n) t))"] by simp
    thus ?thesis using proj_lnull by auto
  qed
  moreover from assms have "n + (n' - n) = n'"
    by (meson enat.distinct(1) enat_add_sub_same enat_diff_cancel_left enat_le_plus_same(1) less_imp_le)
  ultimately show ?thesis by simp
qed
  
subsubsection "Projection Active"

lemma proj_active[simp]:
  assumes "enat i < llength t" "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) = (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" (is "?lhs = ?rhs")
proof -
  from assms have "ltake (enat (Suc i)) t = (ltake (enat i) t) @\<^sub>l ((lnth t i) #\<^sub>l []\<^sub>l)"
    using ltake_Suc_conv_snoc_lnth by blast
  hence "?lhs = \<pi>\<^bsub>c\<^esub>((ltake (enat i) t) @\<^sub>l ((lnth t i) #\<^sub>l []\<^sub>l))" by simp
  moreover have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake (enat i) t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>((lnth t i) #\<^sub>l []\<^sub>l))" by simp
  moreover from assms have "\<pi>\<^bsub>c\<^esub>((lnth t i) #\<^sub>l []\<^sub>l) = (state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l" by simp
  ultimately show ?thesis by simp
qed
  
lemma proj_active_append:
  assumes a1: "(n::nat) \<le> i"
      and a2: "enat i < (n'::enat)"
      and a3: "\<not> lfinite t \<or> n'-1 < llength t"
      and a4: "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
      and "\<forall>i'. (n \<le> i' \<and> enat i'<n' \<and> i' < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>) \<longrightarrow> (i' = i)"
    shows "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)"
  proof -
    from a2 have "Suc i \<le> n'" by (simp add: Suc_ile_eq)
    moreover from a3 have "\<not> lfinite t \<or> n'-1 < llength t" by simp
    moreover have "\<nexists>k. enat k\<ge>enat (Suc i) \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    proof
      assume "\<exists>k. enat k\<ge>enat (Suc i) \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
      then obtain k where "enat k\<ge>enat (Suc i)" and "k<n'" and "k < llength t" and "\<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" by blast
      moreover from `enat k\<ge>enat (Suc i)` have "enat k\<ge>n"
        using assms by (meson dual_order.trans enat_ord_simps(1) le_SucI)
      ultimately have "enat k=enat i" using assms using enat_ord_simps(1) by blast
      with `enat k\<ge>enat (Suc i)` show False by simp
    qed
    ultimately show ?thesis using proj_not_active_same[of "Suc i" n' t c] by simp
  qed
  also have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)"
  proof -
    have "i < llength t"
    proof cases
      assume "lfinite t"
      with a3 have "n'-1 < llength t" by simp
      hence "n' \<le> llength t" by (metis eSuc_minus_1 enat_minus_mono1 ileI1 not_le)
      with a2 show "enat i < llength t" by simp
    next
      assume "\<not> lfinite t"
      thus ?thesis by (metis enat_ord_code(4) llength_eq_infty_conv_lfinite)
    qed
    with a4 show ?thesis by simp
  qed
  also have "\<dots> = ?rhs"
  proof -
    from a1 have "enat n \<le> enat i" by simp
    moreover from a2 a3 have "\<not> lfinite t \<or> enat i-1 < llength t"
      using enat_minus_mono1 less_imp_le order.strict_trans1 by blast
    moreover have "\<nexists>k. k\<ge>n \<and> enat k<enat i \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    proof
      assume "\<exists>k. k\<ge>n \<and> enat k<enat i \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
      then obtain k where "k\<ge>n" and "enat k<enat i" and "enat k < llength t" and "\<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" by blast
      moreover from `enat k<enat i` have "enat k<n'" using assms dual_order.strict_trans by blast
      ultimately have "enat k=enat i" using assms by simp
      with `enat k<enat i` show False by simp
    qed
    ultimately show ?thesis using proj_not_active_same[of n i t c] by simp
  qed    
  finally show ?thesis by simp
qed
  

subsubsection "Same and Not Same"

lemma proj_same_not_active:
  assumes "n \<le> n'"
    and "enat (n'-1) < llength t"
    and "\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake n t)"
  shows "\<nexists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
proof
  assume "\<exists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
  then obtain i where "i\<ge>n" and "i<n'" and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>" by blast
  moreover from `enat (n'-1)<llength t` and `i<n'` have "i<llength t"
    by (metis diff_Suc_1 dual_order.strict_trans enat_ord_simps(2) lessE)
  ultimately have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) =
    (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" by simp
  moreover from `i<n'` have "Suc i \<le> n'" by simp
    hence "lprefix(\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) (\<pi>\<^bsub>c\<^esub>(ltake n' t))" by simp
    then obtain "tl" where "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) @\<^sub>l tl"
      using lprefix_conv_lappend by auto
  moreover from `n\<le>i` have "lprefix(\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
    hence "lprefix(\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
    then obtain "hd" where "\<pi>\<^bsub>c\<^esub>(ltake i t) = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd"
      using lprefix_conv_lappend by auto
  ultimately have "\<pi>\<^bsub>c\<^esub>(ltake n' t) =
    (((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)) @\<^sub>l tl" by simp
  also have "\<dots> = ((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l tl)"
    using lappend_snocL1_conv_LCons2[of "(\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd" "state (tCMP c (lnth t i))"] by simp
  also have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (hd @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l tl))"
    using lappend_assoc by auto
  also have "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake n' t)) @\<^sub>l []\<^sub>l" by simp
  finally have "(\<pi>\<^bsub>c\<^esub>(ltake n' t)) @\<^sub>l []\<^sub>l = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (hd @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l tl))" .
  moreover from assms(3) have "llength (\<pi>\<^bsub>c\<^esub>(ltake n' t)) = llength (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  ultimately have "lfinite (\<pi>\<^bsub>c\<^esub>(ltake n' t)) \<longrightarrow> []\<^sub>l = hd @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l tl)"
    using assms(3) lappend_eq_lappend_conv[of "\<pi>\<^bsub>c\<^esub>(ltake n' t)" "\<pi>\<^bsub>c\<^esub>(ltake n t)" "[]\<^sub>l"] by simp
  moreover have "lfinite (\<pi>\<^bsub>c\<^esub>(ltake n' t))" by simp
  ultimately have "[]\<^sub>l = hd @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l tl)" by simp
  hence "(state (tCMP c (lnth t i))) #\<^sub>l tl = []\<^sub>l" using LNil_eq_lappend_iff by auto
  thus False by simp
qed

lemma proj_not_same_active:
  assumes "enat n \<le> (n'::enat)"
    and "(\<not> lfinite t) \<or> n'-1 < llength t"
    and "\<not>(\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake n t))"
  shows "\<exists>k. k\<ge>n \<and> k<n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
proof (rule ccontr)
  assume "\<not>(\<exists>k. k\<ge>n \<and> k<n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>)"
  have "\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake (enat n) t)"
  proof cases
    assume "lfinite t"
    hence "llength t\<noteq>\<infinity>" by (simp add: lfinite_llength_enat) 
    hence "enat (the_enat (llength t)) = llength t" by auto
    with assms \<open>\<not> (\<exists>k\<ge>n. k < n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>)\<close>
      show ?thesis using proj_not_active_same[of n n' t c] by simp
  next
    assume "\<not> lfinite t"
    with assms \<open>\<not> (\<exists>k\<ge>n. k < n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>)\<close>
      show ?thesis using proj_not_active_same[of n n' t c] by simp
  qed
  with assms show False by simp
qed

subsection "Activations"
text {*
  Finally, we introduce an operator to obtain the number of activations of a certain component within a given configuration trace.
*}

definition nAct :: "cid \<Rightarrow> enat \<Rightarrow> CTrace \<Rightarrow> enat" ("\<langle>_ #\<^bsub>_\<^esub>_\<rangle>") where
"\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<equiv> llength (\<pi>\<^bsub>c\<^esub>(ltake n t))"

lemma nAct_0[simp]:
  "\<langle>c #\<^bsub>0\<^esub> t\<rangle> = 0" by (simp add: nAct_def)

lemma nAct_NIL[simp]:
  "\<langle>c #\<^bsub>n\<^esub> []\<^sub>l\<rangle> = 0" by (simp add: nAct_def)    

lemma nAct_Null:
  assumes "llength t \<ge> n"
      and "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = 0"
    shows "\<forall>i<n. \<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof -
  from assms have "lnull (\<pi>\<^bsub>c\<^esub>(ltake n t))" using nAct_def lnull_def by simp
  hence "\<pi>\<^bsub>c\<^esub>(ltake n t) = []\<^sub>l" using lnull_def by blast
  hence "(\<forall>k\<in>lset (ltake n t). \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>)" by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> (\<forall>i<n. \<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
    then obtain i where "i<n" and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>" by blast
    moreover have "enat i < llength (ltake n t)  \<and> lnth (ltake n t) i = (lnth t i)"
    proof
      from `llength t \<ge> n` have "n = min n (llength t)" using min.orderE by auto
      hence "llength (ltake n t) = n" by simp
      with `i<n` show "enat i < llength (ltake n t)" by auto
      from `i<n` show "lnth (ltake n t) i = (lnth t i)" using lnth_ltake by auto
    qed
    hence "(lnth t i \<in> lset (ltake n t))" using in_lset_conv_lnth[of "lnth t i" "ltake n t"] by blast
    ultimately show False using `(\<forall>k\<in>lset (ltake n t). \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>)` by simp
  qed
qed

lemma nAct_ge_one[simp]:
  assumes "llength t \<ge> n"
      and "i < n"
      and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
    shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<ge> enat 1"
proof (rule ccontr)
  assume "\<not> (\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<ge> enat 1)"
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < enat 1" by simp
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < 1" using enat_1 by simp
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = 0" using Suc_ile_eq \<open>\<not> enat 1 \<le> \<langle>c #\<^bsub>n\<^esub> t\<rangle>\<close> zero_enat_def by auto
  with `llength t \<ge> n` have "\<forall>i<n. \<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>" using nAct_Null by simp
  with assms show False by simp
qed
    
lemma nAct_finite[simp]:
  assumes "n \<noteq> \<infinity>"
  shows "\<exists>n'. \<langle>c #\<^bsub>n\<^esub> t\<rangle> = enat n'"
proof -
  from assms have "lfinite (ltake n t)" by simp
  hence "lfinite (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  hence "\<exists>n'. llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) = enat n'" using lfinite_llength_enat[of "\<pi>\<^bsub>c\<^esub>(ltake n t)"] by simp
  thus ?thesis using nAct_def by simp
qed

lemma nAct_enat_the_nat[simp]:
  assumes "n \<noteq> \<infinity>"
  shows "enat (the_enat (\<langle>c #\<^bsub>n\<^esub> t\<rangle>)) = \<langle>c #\<^bsub>n\<^esub> t\<rangle>"
proof -
  from assms have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<noteq> \<infinity>" by simp
  thus ?thesis using enat_the_enat by simp
qed
  
subsubsection "Monotonicity and Continuity"
  
lemma nAct_mcont:
  shows "mcont lSup lprefix Sup op \<le> (nAct c n)"
proof -
  have "mcont lSup lprefix lSup lprefix (ltake n)" by simp
  hence "mcont lSup lprefix lSup lprefix (\<lambda>t. \<pi>\<^bsub>c\<^esub>(ltake n t))"
    using proj_mcont2mcont[of lSup lprefix "(ltake n)"] by simp
  hence "mcont lSup lprefix Sup op \<le> (\<lambda>t. llength (\<pi>\<^bsub>c\<^esub>(ltake n t)))" by simp
  moreover have "nAct c n = (\<lambda>t. llength (\<pi>\<^bsub>c\<^esub>(ltake n t)))" using nAct_def by auto
  ultimately show ?thesis by simp
qed
  
lemma nAct_mono:
  assumes "n \<le> n'"
    shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
proof -
  from assms have "lprefix (ltake n t) (ltake n' t)" by simp
  hence "lprefix (\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(ltake n' t))" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) \<le> llength (\<pi>\<^bsub>c\<^esub>(ltake n' t))"
    using lprefix_llength_le[of "(\<pi>\<^bsub>c\<^esub>(ltake n t))"] by simp
  thus ?thesis using nAct_def by simp
qed
  
lemma nAct_mono_back:
  assumes "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
    shows "n < n'"
proof (rule ccontr)
  assume "\<not> n<n'"
  hence "n\<ge>n'" by simp
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<ge> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using nAct_mono by simp
  thus False using assms by simp
qed

subsubsection "Not Active"

lemma nAct_not_active[simp]:
  fixes n::nat
    and n'::nat
    and t::CTrace
    and c::cid
  assumes "enat i < llength t"
    and "\<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = \<langle>c #\<^bsub>i\<^esub> t\<rangle>"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) = \<pi>\<^bsub>c\<^esub>(ltake i t)" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(ltake (enat (Suc i)) t)) = llength (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(ltake i t)) \<noteq> \<infinity>"
    using llength_eq_infty_conv_lfinite[of "\<pi>\<^bsub>c\<^esub>(ltake (enat i) t)"] by simp
  ultimately have "llength (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) = llength (\<pi>\<^bsub>c\<^esub>(ltake i t))"
    using the_enat_eSuc by simp
  with nAct_def show ?thesis by simp
qed
  
lemma nAct_not_active_same:
  assumes "enat n \<le> (n'::enat)"
      and "n'-1 < llength t"
      and "\<nexists>k. enat k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    shows "\<langle>c #\<^bsub>n'\<^esub> t\<rangle> = \<langle>c #\<^bsub>n\<^esub> t\<rangle>"
  using assms proj_not_active_same nAct_def by simp
    
subsubsection "Active"
  
lemma nAct_active[simp]:
  fixes n::nat
    and n'::nat
    and t::CTrace
    and c::cid
  assumes "enat i < llength t"
    and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) =
    (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(ltake (enat (Suc i)) t)) = eSuc (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))"
    using plus_1_eSuc one_eSuc by simp
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(ltake i t)) \<noteq> \<infinity>"
    using llength_eq_infty_conv_lfinite[of "\<pi>\<^bsub>c\<^esub>(ltake (enat i) t)"] by simp
  ultimately have "llength (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) = eSuc (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))"
    using the_enat_eSuc by simp
  with nAct_def show ?thesis by simp
qed

lemma nAct_active_suc:
  fixes n::nat
    and n'::enat
    and t::CTrace
    and c::cid
  assumes "\<not> lfinite t \<or> n'-1 < llength t"
    and "n \<le> i"
    and "enat i < n'"
    and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
    and "\<forall>i'. (n \<le> i' \<and> enat i'<n' \<and> i' < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>) \<longrightarrow> (i' = i)"
  shows "\<langle>c #\<^bsub>n'\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>n\<^esub> t\<rangle>)"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)"
    using proj_active_append[of n i n' t c] by blast
  moreover have "llength ((\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)) =
    eSuc (llength (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)))" using one_eSuc eSuc_plus_1 by simp
  ultimately show ?thesis using nAct_def by simp
qed
  
lemma nAct_less:
  assumes "enat k < llength t"
    and "n \<le> k"
    and "k < (n'::enat)"
    and "\<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
  shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
proof -
  have "\<langle>c #\<^bsub>k\<^esub> t\<rangle> \<noteq> \<infinity>" by simp
  then obtain en where en_def: "\<langle>c #\<^bsub>k\<^esub> t\<rangle> = enat en" by blast  
  moreover have "eSuc (enat en) \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
  proof -
    from assms have "Suc k \<le> n'" using Suc_ile_eq by simp
    hence "\<langle>c #\<^bsub>Suc k\<^esub> t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using nAct_mono by simp
    moreover from assms have "\<langle>c #\<^bsub>Suc k\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>k\<^esub> t\<rangle>)" by simp
    ultimately have "eSuc (\<langle>c #\<^bsub>k\<^esub> t\<rangle>) \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" by simp
    thus ?thesis using en_def by simp
  qed
  moreover have "enat en < eSuc (enat en)" by simp
  ultimately have "enat en < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using less_le_trans[of "enat en" "eSuc (enat en)"] by simp
  moreover have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> enat en"
  proof -
    from assms have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> \<langle>c #\<^bsub>k\<^esub> t\<rangle>" using nAct_mono by simp
    thus ?thesis using en_def by simp
  qed
  ultimately show ?thesis using le_less_trans[of "\<langle>c #\<^bsub>n\<^esub> t\<rangle>"] by simp
qed
  
lemma nAct_less_active:
  assumes "n' - 1 < llength t"
      and "\<langle>c #\<^bsub>enat n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
  shows "\<exists>i\<ge>n. i<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof (rule ccontr)
  assume "\<not> (\<exists>i\<ge>n. i<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
  moreover have "enat n \<le> n'" using assms(2) less_imp_le nAct_mono_back by blast
  ultimately have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using `n' - 1 < llength t` nAct_not_active_same by simp
  thus False using assms by simp
qed

subsubsection "Same and Not Same"
  
lemma nAct_same_not_active:
  assumes "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  shows "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
proof (rule ccontr)
  assume "\<not>(\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  then obtain k where "k\<ge>n" and "k<n'" and "\<parallel>c\<parallel>\<^bsub>t k\<^esub>" by blast
  hence "\<langle>c #\<^bsub>Suc k\<^esub> inf_llist t\<rangle> = eSuc (\<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle>)" by simp
  moreover have "\<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
  ultimately have "\<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>Suc k\<^esub> inf_llist t\<rangle>" by fastforce
  moreover from `n\<le>k` have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle>" using nAct_mono by simp
  moreover from `k<n'` have "Suc k \<le> n'" by (simp add: Suc_ile_eq)
  hence "\<langle>c #\<^bsub>Suc k\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_mono by simp
  ultimately show False using assms by simp
qed
  
lemma nAct_not_same_active:
  assumes "\<langle>c #\<^bsub>enat n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
    and "\<not> lfinite t \<or> n' - 1 < llength t"
  shows "\<exists>(i::nat)\<ge>n. enat i< n' \<and> i<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof -
  from assms have "llength(\<pi>\<^bsub>c\<^esub>(ltake n t)) < llength (\<pi>\<^bsub>c\<^esub>(ltake n' t))" using nAct_def by simp
  hence "\<pi>\<^bsub>c\<^esub>(ltake n' t) \<noteq> \<pi>\<^bsub>c\<^esub>(ltake n t)" by auto
  moreover from assms have "enat n < n'" using nAct_mono_back[of c "enat n" t n'] by simp
  ultimately show ?thesis using proj_not_same_active[of n n' t c] assms by simp
qed
  
lemma nAct_less_llength_active:
  assumes "x < llength (\<pi>\<^bsub>c\<^esub>(t))"
    and "enat x = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>"
  shows "\<exists>(i::nat)\<ge>n'. i<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof -
  have "llength(\<pi>\<^bsub>c\<^esub>(ltake n' t)) < llength (\<pi>\<^bsub>c\<^esub>(t))" using assms(1) assms(2) nAct_def by auto
  hence "llength(\<pi>\<^bsub>c\<^esub>(ltake n' t)) < llength (\<pi>\<^bsub>c\<^esub>(ltake (llength t) t))" by (simp add: ltake_all)
  hence "\<langle>c #\<^bsub>enat n'\<^esub> t\<rangle> < \<langle>c #\<^bsub>llength t\<^esub> t\<rangle>" using nAct_def by simp
  moreover have "\<not> lfinite t \<or> llength t - 1 < llength t"
  proof (rule Meson.imp_to_disjD[OF impI])
    assume "lfinite t"
    hence "llength t \<noteq> \<infinity>" by (simp add: llength_eq_infty_conv_lfinite)
    moreover have "llength t>0"
    proof -
      from `x < llength (\<pi>\<^bsub>c\<^esub>(t))` have "llength (\<pi>\<^bsub>c\<^esub>(t))>0" by auto
      thus ?thesis using proj_llength Orderings.order_class.order.strict_trans2 by blast
    qed
    ultimately show "llength t - 1 < llength t" by (metis One_nat_def \<open>lfinite t\<close> diff_Suc_less
      enat_ord_simps(2) idiff_enat_enat lfinite_conv_llength_enat one_enat_def zero_enat_def)
  qed
  ultimately show ?thesis using nAct_not_same_active[of c n' t "llength t"] by simp
qed

lemma nAct_exists:
  assumes "x < llength (\<pi>\<^bsub>c\<^esub>(t))"
  shows "\<exists>(n'::nat). enat x = \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
proof -
  have "x < llength (\<pi>\<^bsub>c\<^esub>(t)) \<longrightarrow> (\<exists>(n'::nat). enat x = \<langle>c #\<^bsub>n'\<^esub> t\<rangle>)"
  proof (induction x)
    case 0
    thus ?case by (metis nAct_0 zero_enat_def)
  next
    case (Suc x)
    show ?case
    proof
      assume "Suc x < llength (\<pi>\<^bsub>c\<^esub>(t))"
      hence "x < llength (\<pi>\<^bsub>c\<^esub>(t))" using Suc_ile_eq less_imp_le by auto
      with Suc.IH obtain n' where "enat x = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>" by blast
      with `x < llength (\<pi>\<^bsub>c\<^esub>(t))` have "\<exists>i\<ge>n'. i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
        using nAct_less_llength_active[of x c t n'] by simp
      then obtain i where "i\<ge>n'" and "i<llength t" and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
        and "\<nexists>k. n'\<le>k \<and> k<i \<and> k<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" using lActive_least[of n' t c] by auto
      moreover from `i<llength t` have "\<not> lfinite t \<or> enat (Suc i) - 1 < llength t"
        by (simp add: one_enat_def)
      moreover have "enat i < enat (Suc i)" by simp
      moreover have "\<forall>i'. (n' \<le> i' \<and> enat i'<enat (Suc i) \<and> i'<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>) \<longrightarrow> (i' = i)"
      proof (rule impI[THEN allI])
        fix i' assume "n' \<le> i' \<and> enat i'<enat (Suc i) \<and> i'<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>"
        with `\<nexists>k. n'\<le>k \<and> k<i \<and> k<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>` show "i'=i" by fastforce
      qed
      ultimately have "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>n'\<^esub> t\<rangle>)" using nAct_active_suc[of t "Suc i" n' i c] by simp
      with `enat x = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>` have "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (enat x)" by simp
      thus "\<exists>n'. enat (Suc x) = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>" by (metis eSuc_enat)
    qed
  qed
  with assms show ?thesis by simp
qed
  
subsection "Projection and Activation"
text {*
  In the following we provide some properties about the relationship between the projection and activations operator.
*}
  
lemma nAct_le_proj:
  "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> llength (\<pi>\<^bsub>c\<^esub>(t))"
proof -
  from nAct_def have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) \<le> llength (\<pi>\<^bsub>c\<^esub>(t))"
  proof -
    have "lprefix (ltake n t) t" by simp
    hence "lprefix (\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(t))" by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) \<le> llength (\<pi>\<^bsub>c\<^esub>(t))" using lprefix_llength_le by blast
    thus ?thesis by auto
  qed
  thus ?thesis using nAct_def by simp
qed
  
lemma proj_nAct:
  assumes "(enat n < llength t)"
  shows "\<pi>\<^bsub>c\<^esub>(ltake n t) = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>(t))" (is "?lhs = ?rhs")
proof -
  have "?lhs = ltake (llength (\<pi>\<^bsub>c\<^esub>(ltake n t))) (\<pi>\<^bsub>c\<^esub>(ltake n t))"
    using ltake_all[of "\<pi>\<^bsub>c\<^esub>(ltake n t)" "llength (\<pi>\<^bsub>c\<^esub>(ltake n t))"] by simp
  also have "\<dots> = ltake (llength (\<pi>\<^bsub>c\<^esub>(ltake n t))) ((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(ldrop n t)))"
    using ltake_lappend1[of "llength (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t))" "\<pi>\<^bsub>c\<^esub>(ltake n t)" "(\<pi>\<^bsub>c\<^esub>(ldrop n t))"] by simp
  also have "\<dots> = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) ((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(ldrop n t)))" using nAct_def by simp      
  also have "\<dots> = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>((ltake (enat n) t) @\<^sub>l (ldrop n t)))" by simp
  also have "\<dots> = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>(t))" using lappend_ltake_ldrop[of n t] by simp
  finally show ?thesis by simp
qed

lemma proj_active_nth:
  assumes "enat (Suc i) < llength t" "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "lnth (\<pi>\<^bsub>c\<^esub>(t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)) = state (tCMP c (lnth t i))"
proof -
  from assms have "enat i < llength t" using Suc_ile_eq[of i "llength t"] by auto
  with assms have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) = (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" by simp
  moreover have "lnth ((\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l))
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))) = state (tCMP c (lnth t i))"
  proof -
    have "\<not> lnull ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" by simp
    moreover have "lfinite (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
    ultimately have "lnth ((\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l))
      (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))) = lhd ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l)" by simp
    also have "\<dots> = state (tCMP c (lnth t i))" by simp
    finally show "lnth ((\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((state (tCMP c (lnth t i))) #\<^sub>l []\<^sub>l))
      (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))) = state (tCMP c (lnth t i))" by simp
  qed
  ultimately have "state (tCMP c (lnth t i)) = lnth (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t))
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t))))" by simp
  also have "\<dots> = lnth (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))" using nAct_def by simp
  also have "\<dots> = lnth (ltake (\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>(t))) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))"
    using proj_nAct[of "Suc i" t c] assms by simp
  also have "\<dots> = lnth (\<pi>\<^bsub>c\<^esub>(t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))"
  proof -
    from assms have "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)" using `enat i < llength t` by simp
    moreover have "\<langle>c #\<^bsub>i\<^esub> t\<rangle> < eSuc (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)" using iless_Suc_eq[of "the_enat (\<langle>c #\<^bsub>enat i\<^esub> t\<rangle>)"] by simp
    ultimately have "\<langle>c #\<^bsub>i\<^esub> t\<rangle> < (\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle>)" by simp
    hence "enat (the_enat (\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle>)) > enat (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))" by simp
    thus ?thesis using lnth_ltake[of "the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)" "the_enat (\<langle>c #\<^bsub>enat (Suc i)\<^esub> t\<rangle>)" "\<pi>\<^bsub>c\<^esub>(t)"] by simp
  qed
  finally show ?thesis ..
qed

lemma nAct_eq_proj:
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
  shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(t))" (is "?lhs = ?rhs")
proof -
  from nAct_def have "?lhs = llength (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  moreover from assms have "\<forall>(n'::nat)\<le>llength t. n'\<ge>n \<longrightarrow> (\<not> \<parallel>c\<parallel>\<^bsub>lnth t n'\<^esub>)" by simp
  hence "\<pi>\<^bsub>c\<^esub>(t) = \<pi>\<^bsub>c\<^esub>(ltake n t)" using proj_ltake by simp
  ultimately show ?thesis by simp
qed

lemma nAct_llength_proj:
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<ge> eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
proof -
  from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` obtain i where "i\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<not> (\<exists>k\<ge>n. k < i \<and> k < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
    using lActive_least[of n "inf_llist t" c] by auto
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<ge> \<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>" using nAct_le_proj by simp
  moreover have "eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) = \<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>"
  proof -
    have "enat (Suc i) < llength (inf_llist t)" by simp
    moreover have "i < Suc i" by simp
    moreover from `\<not> (\<exists>k\<ge>n. k < i \<and> k < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)`
      have "\<forall>i'. n \<le> i' \<and> i' < Suc i \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i'\<^esub> \<longrightarrow> i' = i" by fastforce
    ultimately show ?thesis using nAct_active_suc `i\<ge>n` `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
  qed
  ultimately show ?thesis by simp
qed

end