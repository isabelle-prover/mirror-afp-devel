section \<open> Properties of MLTL \<close>
theory MLTL_Properties

imports MLTL_Encoding

begin

subsection \<open>Useful Functions\<close>

text \<open> We use the following function to assume that an MLTL formula is well-defined:
  i.e., that all intervals in the formula satisfy a is less than or equal to b \<close>
fun intervals_welldef:: "'a mltl \<Rightarrow> bool"
  where "intervals_welldef True\<^sub>m = True"
  | "intervals_welldef False\<^sub>m = True"
  | "intervals_welldef (Prop\<^sub>m (p)) = True"
  | "intervals_welldef (Not\<^sub>m \<phi>) = intervals_welldef \<phi>"
  | "intervals_welldef (\<phi> And\<^sub>m \<psi>) = (intervals_welldef \<phi> \<and> intervals_welldef \<psi>)"
  | "intervals_welldef (\<phi> Or\<^sub>m \<psi>) = (intervals_welldef \<phi> \<and> intervals_welldef \<psi>)"
  | "intervals_welldef (F\<^sub>m [a,b] \<phi>)  = (a \<le> b \<and> intervals_welldef \<phi>)"
  | "intervals_welldef (G\<^sub>m [a,b] \<phi>)  = (a \<le> b \<and> intervals_welldef \<phi>)"
  | "intervals_welldef (\<phi> U\<^sub>m [a,b] \<psi>) =
      (a \<le> b \<and> intervals_welldef \<phi> \<and> intervals_welldef \<psi>)"
  | "intervals_welldef (\<phi> R\<^sub>m [a,b] \<psi>) =
      (a \<le> b \<and> intervals_welldef \<phi> \<and> intervals_welldef \<psi>)"

subsection \<open>Semantic Equivalence\<close>
(* \<phi> and \<psi> are sematically equivalent iff for all traces \<pi>, \<pi> |= \<phi> \<longleftrightarrow> \<pi> |= \<psi>  *)
definition semantic_equiv:: "'a mltl \<Rightarrow> 'a mltl \<Rightarrow> bool" ("_ \<equiv>\<^sub>m _" [80, 80] 80)
  where "\<phi> \<equiv>\<^sub>m \<psi> \<equiv> (\<forall>\<pi>. \<pi> \<Turnstile>\<^sub>m \<phi> = \<pi> \<Turnstile>\<^sub>m \<psi>)"

fun depth_mltl:: "'a mltl \<Rightarrow> nat"
  where "depth_mltl True\<^sub>m = 0"
  | "depth_mltl False\<^sub>m = 0"
  | "depth_mltl Prop\<^sub>m (p) = 0"
  | "depth_mltl (Not\<^sub>m \<phi>) = 1 + depth_mltl \<phi>"
  | "depth_mltl (\<phi> And\<^sub>m \<psi>) = 1 + max (depth_mltl \<phi>) (depth_mltl \<psi>)"
  | "depth_mltl (\<phi> Or\<^sub>m \<psi>) = 1 + max (depth_mltl \<phi>) (depth_mltl \<psi>)"
  | "depth_mltl (G\<^sub>m [a,b] \<phi>) = 1 + depth_mltl \<phi>"
  | "depth_mltl (F\<^sub>m [a,b] \<phi>) = 1 + depth_mltl \<phi>"
  | "depth_mltl (\<phi> U\<^sub>m [a,b] \<psi>) = 1 + max (depth_mltl \<phi>) (depth_mltl \<psi>)"
  | "depth_mltl (\<phi> R\<^sub>m [a,b] \<psi>) = 1 + max (depth_mltl \<phi>) (depth_mltl \<psi>)"

fun subformulas:: "'a mltl \<Rightarrow> 'a mltl set"
  where "subformulas True\<^sub>m = {}"
  | "subformulas False\<^sub>m = {}"
  | "subformulas Prop\<^sub>m (p) = {}"
  | "subformulas (Not\<^sub>m \<phi>) = {\<phi>} \<union> subformulas \<phi>"
  | "subformulas (\<phi> And\<^sub>m \<psi>) = {\<phi>, \<psi>} \<union> subformulas \<phi> \<union> subformulas \<psi>"
  | "subformulas (\<phi> Or\<^sub>m \<psi>) = {\<phi>, \<psi>} \<union> subformulas \<phi> \<union> subformulas \<psi>"
  | "subformulas (G\<^sub>m [a,b] \<phi>) = {\<phi>} \<union> subformulas \<phi>"
  | "subformulas (F\<^sub>m [a,b] \<phi>) = {\<phi>} \<union> subformulas \<phi>"
  | "subformulas (\<phi> U\<^sub>m [a,b] \<psi>) = {\<phi>, \<psi>} \<union> subformulas \<phi> \<union> subformulas \<psi>"
  | "subformulas (\<phi> R\<^sub>m [a,b] \<psi>) = {\<phi>, \<psi>} \<union> subformulas \<phi> \<union> subformulas \<psi>"

subsection \<open>Basic Properties\<close>

lemma future_or_distribute:
  shows "F\<^sub>m [a,b] (\<phi>1 Or\<^sub>m \<phi>2) \<equiv>\<^sub>m (F\<^sub>m [a,b] \<phi>1) Or\<^sub>m (F\<^sub>m [a,b] \<phi>2)"
  unfolding semantic_equiv_def by auto

lemma global_and_distribute:
  shows "G\<^sub>m [a,b] (\<phi>1 And\<^sub>m \<phi>2) \<equiv>\<^sub>m (G\<^sub>m [a,b] \<phi>1) And\<^sub>m (G\<^sub>m [a,b] \<phi>2)"
  unfolding semantic_equiv_def
  unfolding semantics_mltl.simps by auto

lemma not_not_equiv:
  shows "\<phi> \<equiv>\<^sub>m (Not\<^sub>m (Not\<^sub>m \<phi>))"
  unfolding semantic_equiv_def by simp

lemma demorgan_and_or:
  shows "Not\<^sub>m (\<phi> And\<^sub>m \<psi>) \<equiv>\<^sub>m (Not\<^sub>m \<phi>) Or\<^sub>m (Not\<^sub>m \<psi>)"
  unfolding semantic_equiv_def by simp

lemma demorgan_or_and:
  shows "semantic_equiv (Not_mltl (\<phi> Or\<^sub>m \<psi>))
         (And_mltl (Not\<^sub>m \<phi>) (Not_mltl \<psi>))"
  unfolding semantic_equiv_def by simp

lemma future_as_until:
  fixes a b::"nat"
  assumes "a \<le> b"
  shows "(F\<^sub>m [a,b] \<phi>) \<equiv>\<^sub>m (True\<^sub>m U\<^sub>m [a,b] \<phi>)"
  unfolding semantic_equiv_def by auto

lemma globally_as_release:
  fixes a b::"nat"
  assumes "a \<le> b"
  shows "(G\<^sub>m [a,b] \<phi>) \<equiv>\<^sub>m (False\<^sub>m R\<^sub>m [a,b] \<phi>)"
  unfolding semantic_equiv_def by auto

lemma until_or_distribute:
  fixes a b ::"nat"
  assumes "a \<le> b"
  shows "\<phi> U\<^sub>m [a,b] (\<alpha> Or\<^sub>m \<beta>) \<equiv>\<^sub>m
         (\<phi> U\<^sub>m [a,b] \<alpha>) Or\<^sub>m (\<phi> U\<^sub>m [a,b] \<beta>)"
  using assms semantics_mltl.simps unfolding semantic_equiv_def
  by auto

lemma until_and_distribute:
  fixes a b ::"nat"
  assumes "a \<le> b"
  shows "(\<alpha> And\<^sub>m \<beta>) U\<^sub>m [a,b] \<phi> \<equiv>\<^sub>m
         (\<alpha> U\<^sub>m [a,b] \<phi>) And\<^sub>m (\<beta> U\<^sub>m [a,b] \<phi>)"
  using assms unfolding semantic_equiv_def semantics_mltl.simps
  by (smt (verit) linorder_less_linear order_less_trans)

lemma release_or_distribute:
  fixes a b ::"nat"
  assumes "a \<le> b"
  shows "(\<alpha> Or\<^sub>m \<beta>) R\<^sub>m [a,b] \<phi> \<equiv>\<^sub>m
         (\<alpha> R\<^sub>m [a,b] \<phi>) Or\<^sub>m (\<beta> R\<^sub>m [a,b] \<phi>)"
  using assms unfolding semantic_equiv_def semantics_mltl.simps
  by auto

lemma different_next_operators:
  shows "\<not>(G\<^sub>m [1,1] \<phi> \<equiv>\<^sub>m F\<^sub>m [1,1] \<phi>)"
  unfolding semantic_equiv_def semantics_mltl.simps
  by (metis le_numeral_extra(4) linordered_nonzero_semiring_class.zero_le_one list.size(3) not_one_less_zero)

subsection \<open>Duality Properties\<close>

lemma globally_future_dual:
  fixes a b::"nat"
  assumes "a \<le> b"
  shows "(G\<^sub>m [a,b] \<phi>) \<equiv>\<^sub>m Not\<^sub>m (F\<^sub>m [a,b] (Not\<^sub>m \<phi>))"
  using assms unfolding semantic_equiv_def by auto

lemma future_globally_dual:
  fixes a b::"nat"
  assumes "a \<le> b"
  shows "(F\<^sub>m [a,b] \<phi>) \<equiv>\<^sub>m Not\<^sub>m (G\<^sub>m [a,b] (Not\<^sub>m \<phi>))"
  using assms unfolding semantic_equiv_def by auto

text \<open> Proof altered from source material in the last case. \<close>
lemma release_until_dual1:
  fixes a b::"nat"
  assumes "\<pi> \<Turnstile>\<^sub>m (\<phi> R\<^sub>m [a,b] \<psi>)"
  shows "\<pi> \<Turnstile>\<^sub>m (Not\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not\<^sub>m \<psi>)))"
proof -
  have relase_unfold: "(a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> ((semantics_mltl (drop i \<pi>) \<psi>) \<or> (\<exists>j. j \<ge> a \<and> j \<le> b-1 \<and> semantics_mltl (drop j \<pi>) \<phi> \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) \<psi>))))))"
    using assms by auto
  {assume *: "length \<pi> \<le> a"
    then have ?thesis
      by (simp add: assms)
  } moreover {assume **: "(\<forall>i. (a \<le> i \<and> i \<le> b) \<longrightarrow> semantics_mltl (drop i \<pi>) \<psi>)"
    then have "length \<pi> \<le> a \<or> (\<forall>s. a \<le> s \<and> s \<le> b \<longrightarrow> (semantics_mltl (drop s \<pi>) \<psi> \<or> (\<exists>t. t\<ge> a \<and> t \<le> s-1 \<and> semantics_mltl (drop t \<pi>) \<phi>)))"
      by auto
    then have ?thesis using assms
      using "**" linorder_not_less by auto
  } moreover {assume *: "length \<pi> > a \<and> (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> \<not> (semantics_mltl (drop i \<pi>) \<psi>))"
    then obtain i where i_prop: "(a \<le> i \<and> i \<le> b)" "\<not> (semantics_mltl (drop i \<pi>) \<psi>)"
      by blast
    have "(\<forall>i. (a \<le> i \<and> i \<le> b) \<longrightarrow> (semantics_mltl (drop i \<pi>) \<psi>))
       \<longrightarrow> semantics_mltl (drop i \<pi>) \<psi>"
      using i_prop(1) by blast
    then have h1: "\<not> (\<forall>i. (a \<le> i \<and> i \<le> b) \<longrightarrow>
          semantics_mltl (drop i \<pi>) \<psi>)"
      using i_prop by blast
    have "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
          semantics_mltl (drop i \<pi>) \<psi>) \<or>
          (\<exists>j\<ge>a. j \<le> b - 1 \<and>
                  semantics_mltl (drop j \<pi>) \<phi> \<and>
                  (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                       semantics_mltl (drop k \<pi>) \<psi>))"
      using * relase_unfold by auto
    then have "(\<exists>j\<ge>a. j \<le> b - 1 \<and>
                  semantics_mltl (drop j \<pi>) \<phi> \<and>
                  (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>
                       semantics_mltl (drop k \<pi>) \<psi>))"
      using * h1 by blast
   (*Deviates from proof after this point*)
   then have "\<exists>j. a \<le> j \<and> j \<le> b-1 \<and> (semantics_mltl (drop j \<pi>) \<phi> \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow>  semantics_mltl (drop k \<pi>) \<psi>))"
     using relase_unfold
     by metis
  (* Sledgehammer finds this *)
   then have "\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
        (semantics_mltl (drop i \<pi>) \<psi> \<or>
        (\<exists>j. a \<le> j \<and> j < i \<and> semantics_mltl (drop j \<pi>) \<phi>))"
     by (metis linorder_not_less)
   then have "\<forall>i. (i \<ge> a \<and> i \<le> b) \<longrightarrow>  (semantics_mltl (drop i \<pi>) \<psi> \<or>
        \<not> (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> \<not> semantics_mltl (drop j \<pi>) \<phi>))"
     by blast
   then have "\<forall>i. (i \<ge> a \<and> i \<le> b) \<longrightarrow> \<not> (\<not> semantics_mltl (drop i \<pi>) \<psi> \<and>
        (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> \<not> semantics_mltl (drop j \<pi>) \<phi>))"
     by blast
   then have "\<not> ((\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (\<not> (semantics_mltl (drop i \<pi>) \<psi>) \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> \<not> (semantics_mltl (drop j \<pi> ) \<phi>)))))"
     by blast
   then have "\<not> (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (\<not> (semantics_mltl (drop i \<pi>) \<psi>) \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> \<not> (semantics_mltl (drop j \<pi> ) \<phi>)))))"
     using * by blast
   then have  ?thesis
     by auto
 }
  ultimately show ?thesis
    using linorder_not_less
    by (smt (verit) relase_unfold semantics_mltl.simps(4) semantics_mltl.simps(9))
qed

lemma release_until_dual2:
  fixes a b::"nat"
  assumes a_leq_b: "a \<le> b"
  assumes "\<pi> \<Turnstile>\<^sub>m (Not\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not\<^sub>m \<psi>)))"
  shows "semantics_mltl \<pi> (\<phi> R\<^sub>m [a,b] \<psi>)"
proof -
  have unfold_not_until_not: " \<not> (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (\<not> (semantics_mltl (drop i \<pi>) \<psi>) \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> \<not> (semantics_mltl (drop j \<pi> ) \<phi>)))))"
   using assms by auto
  have not_until_not_unfold: "(a \<le> b \<and> a < length \<pi>) \<longrightarrow> (\<pi> \<Turnstile>\<^sub>m (Not\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not\<^sub>m \<psi>))) \<longleftrightarrow>
    (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
        semantics_mltl (drop i \<pi>) \<psi> \<or>
        (\<exists>j. a \<le> j \<and> j < i \<and> semantics_mltl (drop j \<pi>) \<phi>)))"
    by auto
  {assume *: "length \<pi> \<le> a"
   then have ?thesis
     using assms semantics_mltl.simps(10)
     by blast
 } moreover {assume *: "\<forall>s. (a \<le> s \<and> s \<le> b) \<longrightarrow> semantics_mltl (drop s \<pi>) \<psi>"
   then have ?thesis
     by (simp add: assms(1))
 } moreover {assume *: "(a \<le> b \<and> a < length \<pi>) \<and> (\<exists>s. (a \<le> s \<and> s \<le> b) \<and> \<not> (semantics_mltl (drop s \<pi>) \<psi>))"
   then have not_until_not: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow>
        semantics_mltl (drop i \<pi>) \<psi> \<or>
        (\<exists>j. a \<le> j \<and> j < i \<and> semantics_mltl (drop j \<pi>) \<phi>))"
     using not_until_not_unfold assms
     by blast
   have least_prop: "(\<exists>s. (a \<le> s \<and> s \<le> b) \<and> f s \<pi> \<psi> \<and>
        (\<forall>k. a \<le> k \<and> k < s \<longrightarrow> \<not> (f k \<pi> \<psi>))
        )" if f_prop: "(\<exists>s. (a \<le> s \<and> s \<le> b) \<and> f s \<pi> \<psi>)" for f::"nat \<Rightarrow> 'a set list \<Rightarrow> 'a mltl \<Rightarrow> bool"
   proof -
     have "\<exists>q. q = (LEAST p. (a \<le> p \<and> p \<le> b) \<and> f p \<pi> \<psi>)"
       by simp
     then obtain q where q_prop: "q = (LEAST p. (a \<le> p \<and> p \<le> b) \<and> f p \<pi> \<psi>)"
       by auto
     then have least1: "(a \<le> q \<and> q \<le> b) \<and> f q \<pi> \<psi>"
       using f_prop
       by (smt (verit) LeastI)
     have least2: "(\<forall>k. a \<le> k \<and> k < q \<longrightarrow> \<not> (f k \<pi> \<psi>))"
       using q_prop
       using least1 not_less_Least by fastforce
     show ?thesis using least1 least2 by blast
   qed
   have "\<exists>i1. a \<le> i1 \<and> i1 \<le> b \<and> \<not> (semantics_mltl (drop i1 \<pi>) \<psi>) \<and> (\<forall>k. (a \<le> k \<and> k \<le> i1-1) \<longrightarrow> (semantics_mltl (drop k \<pi>) \<psi>))"
     using * least_prop[of "\<lambda> s \<pi> \<psi>. \<not> (semantics_mltl (drop s \<pi>) \<psi>)"]
     by (metis add_diff_inverse_nat gr_implies_not0 le_imp_less_Suc less_one plus_1_eq_Suc unfold_not_until_not)
   then obtain i1 where i1_prop: "a \<le> i1 \<and> i1 \<le> b \<and> \<not> (semantics_mltl (drop i1 \<pi>) \<psi>) \<and> (\<forall>k. (a \<le> k \<and> k \<le> i1-1) \<longrightarrow> (semantics_mltl (drop k \<pi>) \<psi>))"
     by auto

   have "semantics_mltl (drop i1 \<pi>) \<psi> \<or>
        (\<exists>j\<ge>a. j < i1 \<and> semantics_mltl (drop j \<pi>) \<phi>)"
     using not_until_not i1_prop by blast
   then have "(semantics_mltl (drop i1 \<pi>) \<psi>) \<or> (\<exists>t. a \<le> t \<and> t \<le> i1-1 \<and> (semantics_mltl (drop t \<pi>) \<phi>))"
     using * i1_prop
     using not_less_eq by fastforce
   then have "(\<exists>t. a \<le> t \<and> t \<le> i1-1 \<and> (semantics_mltl (drop t \<pi>) \<phi>))"
     by (smt (verit, ccfv_threshold) "*" i1_prop less_imp_le_nat nle_le not_until_not order_le_less_trans)
   then obtain t where t_prop: "a \<le> t \<and> t \<le> i1-1 \<and> semantics_mltl (drop t \<pi>) \<phi>"
     by auto
   have "\<forall>k. a \<le> k \<and> k \<le> i1-1 \<longrightarrow> (semantics_mltl (drop k \<pi>) \<psi> )"
     using i1_prop by blast
   then have "\<forall>k. a \<le> k \<and> k \<le> t \<longrightarrow> (semantics_mltl (drop k \<pi>) \<psi> )"
     using t_prop by auto
   then have "\<exists>j. a \<le> j \<and> j \<le> (b-1) \<and> (semantics_mltl (drop j \<pi>) \<phi>)
      \<and> (\<forall>k. a \<le> k \<and>k \<le> j \<longrightarrow> (semantics_mltl (drop k \<pi>) \<psi>))"
     by (meson diff_le_mono i1_prop le_trans t_prop)
   then have ?thesis
     using semantics_mltl.simps(10) a_leq_b
     by blast
 }
  ultimately show  ?thesis
    using assms(1) linorder_not_less by blast
qed

lemma release_until_dual:
  fixes a b::"nat"
  assumes a_leq_b: "a \<le> b"
  shows "(\<phi> R\<^sub>m [a,b] \<psi>) \<equiv>\<^sub>m (Not\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not\<^sub>m \<psi>)))"
  using release_until_dual1 release_until_dual2
  using assms unfolding semantic_equiv_def by metis

lemma until_release_dual:
  fixes a b::"nat"
  assumes a_leq_b: "a \<le> b"
  shows "(\<phi> U\<^sub>m [a,b] \<psi>) \<equiv>\<^sub>m (Not\<^sub>m ((Not\<^sub>m \<phi>) R\<^sub>m [a,b] (Not\<^sub>m \<psi>)))"
proof-
  have release_until_dual_alternate: "(Not\<^sub>m (\<phi> R\<^sub>m [a,b] \<psi>)) \<equiv>\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not\<^sub>m \<psi>))"
    using release_until_dual
    using assms semantics_mltl.simps(4) unfolding semantic_equiv_def by metis
  have not_not_until: "(\<phi> U\<^sub>m [a,b] \<psi>) \<equiv>\<^sub>m ((Not\<^sub>m (Not\<^sub>m \<phi>)) U\<^sub>m [a,b] (Not\<^sub>m (Not\<^sub>m \<psi>)))"
    using assms not_not_equiv using semantics_mltl.simps(9)
    by (simp add: semantic_equiv_def)
  have "(Not\<^sub>m ((Not\<^sub>m \<phi>) R\<^sub>m [a,b] (Not\<^sub>m \<psi>))) \<equiv>\<^sub>m ((Not\<^sub>m (Not\<^sub>m \<phi>)) U\<^sub>m [a,b] (Not\<^sub>m (Not\<^sub>m \<psi>)))"
    using assms release_until_dual semantics_mltl.simps(4) unfolding semantic_equiv_def by metis
  then show ?thesis using not_not_until
    unfolding semantic_equiv_def
    by blast
qed

subsection "Additional Basic Properties"
lemma release_and_distribute:
  fixes a b ::"nat"
  assumes "a \<le> b"
  shows "(\<phi> R\<^sub>m [a,b] (\<alpha> And\<^sub>m \<beta>)) \<equiv>\<^sub>m
         ((\<phi> R\<^sub>m [a,b] \<alpha>) And\<^sub>m (\<phi> R\<^sub>m [a,b] \<beta>))"
proof-
  let ?lhs = "(\<phi> R\<^sub>m [a,b] (\<alpha> And\<^sub>m \<beta>))"
  let ?rhs = "((\<phi> R\<^sub>m [a,b] \<alpha>) And\<^sub>m (\<phi> R\<^sub>m [a,b] \<beta>))"
  let ?neg = "Not\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not\<^sub>m (\<alpha> And\<^sub>m \<beta>)))"
  have eq_lhs: "semantic_equiv ?lhs ?neg"
    using until_release_dual release_until_dual until_or_distribute
    by (smt (verit) assms release_until_dual1 semantic_equiv_def)
  let ?neg1 = "Not\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] ((Not\<^sub>m \<alpha>) Or\<^sub>m (Not\<^sub>m \<beta>)))"
  have eq_neg1: "semantic_equiv ?neg ?neg1"
    unfolding semantic_equiv_def semantic_equiv_def by auto
  let ?neg2 = "Not\<^sub>m (((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not_mltl \<alpha>)) Or\<^sub>m ((Not\<^sub>m \<phi>) U\<^sub>m [a,b] (Not_mltl \<beta>)))"
  have eq_neg2: "semantic_equiv ?neg1 ?neg2"
    unfolding semantic_equiv_def by auto
  let ?neg3 = "((\<phi> R\<^sub>m [a,b] \<alpha>) And\<^sub>m (\<phi> R\<^sub>m [a,b] \<beta>))"
  have eq_neg3: "semantic_equiv ?neg2 ?neg3"
    unfolding semantic_equiv_def using assms
    by (metis release_until_dual1 release_until_dual2 semantics_mltl.simps(4) semantics_mltl.simps(5) semantics_mltl.simps(6))
  have eq_rhs: "semantic_equiv ?rhs ?neg"
    using eq_neg1 eq_neg2 eq_neg3
    by (meson semantic_equiv_def)
  show ?thesis using eq_rhs eq_lhs unfolding semantic_equiv_def by meson
qed

subsection \<open>NNF Transformation and Properties \<close>
fun convert_nnf:: "'a mltl \<Rightarrow> 'a mltl"
  where "convert_nnf True\<^sub>m = True\<^sub>m"
  | "convert_nnf False\<^sub>m = False\<^sub>m"
  | "convert_nnf Prop\<^sub>m (p) = Prop\<^sub>m (p)"
  | "convert_nnf (\<phi> And\<^sub>m \<psi>) = ((convert_nnf \<phi>) And\<^sub>m (convert_nnf \<psi>))"
  | "convert_nnf (\<phi> Or\<^sub>m \<psi>) = ((convert_nnf \<phi>) Or\<^sub>m (convert_nnf \<psi>))"
  | "convert_nnf (F\<^sub>m [a,b] \<phi>) = (F\<^sub>m [a,b] (convert_nnf \<phi>))"
  | "convert_nnf (G\<^sub>m [a,b] \<phi>) = (G\<^sub>m [a,b] (convert_nnf \<phi>))"
  | "convert_nnf (\<phi> U\<^sub>m [a,b] \<psi>) = ((convert_nnf \<phi>) U\<^sub>m [a,b] (convert_nnf \<psi>))"
  | "convert_nnf (\<phi> R\<^sub>m [a,b] \<psi>) = ((convert_nnf \<phi>) R\<^sub>m [a,b] (convert_nnf \<psi>))"
  (* Rewriting with logical duals *)
  | "convert_nnf (Not\<^sub>m True\<^sub>m) = False\<^sub>m"
  | "convert_nnf (Not\<^sub>m False\<^sub>m) = True\<^sub>m"
  | "convert_nnf (Not\<^sub>m Prop\<^sub>m (p)) = (Not\<^sub>m Prop\<^sub>m (p))"
  | "convert_nnf (Not\<^sub>m (Not\<^sub>m \<phi>)) = convert_nnf \<phi>"
  | "convert_nnf (Not\<^sub>m (\<phi> And\<^sub>m \<psi>)) = ((convert_nnf (Not\<^sub>m \<phi>)) Or\<^sub>m (convert_nnf (Not\<^sub>m \<psi>)))"
  | "convert_nnf (Not\<^sub>m (\<phi> Or\<^sub>m \<psi>)) = ((convert_nnf (Not\<^sub>m \<phi>)) And\<^sub>m (convert_nnf (Not\<^sub>m \<psi>)))"
  | "convert_nnf (Not\<^sub>m (F\<^sub>m [a,b] \<phi>)) = (G\<^sub>m [a,b] (convert_nnf (Not\<^sub>m \<phi>)))"
  | "convert_nnf (Not\<^sub>m (G\<^sub>m [a,b] \<phi>)) = (F\<^sub>m [a,b] (convert_nnf (Not\<^sub>m \<phi>)))"
  | "convert_nnf (Not\<^sub>m (\<phi> U\<^sub>m [a,b] \<psi>)) = ((convert_nnf (Not\<^sub>m \<phi>)) R\<^sub>m [a,b] (convert_nnf (Not\<^sub>m \<psi>)))"
  | "convert_nnf (Not\<^sub>m (\<phi> R\<^sub>m [a,b] \<psi>)) = ((convert_nnf (Not\<^sub>m \<phi>)) U\<^sub>m [a,b] (convert_nnf (Not\<^sub>m \<psi>)))"


lemma convert_nnf_preserves_semantics:
  assumes "intervals_welldef \<phi>"
  shows "(\<pi> \<Turnstile>\<^sub>m (convert_nnf \<phi>)) \<longleftrightarrow> (\<pi> \<Turnstile>\<^sub>m \<phi>)"
  using assms
proof (induct "depth_mltl \<phi>" arbitrary:\<phi> \<pi> rule:less_induct)
  case less
  then show ?case
  proof (cases \<phi>)
    case True_mltl
    then show ?thesis by simp
  next
    case False_mltl
    then show ?thesis by simp
  next
    case (Prop_mltl x)
    then show ?thesis by simp
  next
    case (Not_mltl \<phi>1)
    then have phi_is: "\<phi> = Not\<^sub>m \<phi>1"
      by auto
    then show ?thesis
    proof (cases \<phi>1)
      case True_mltl
      then show ?thesis using Not_mltl
        by simp
    next
      case False_mltl
      then show ?thesis using Not_mltl
        by simp
    next
      case (Prop_mltl p)
      then show ?thesis using Not_mltl
        by simp
    next
      case (Not_mltl \<phi>2)
      then show ?thesis using phi_is less
        by auto
    next
      case (And_mltl \<phi>2 \<phi>3)
      then show ?thesis using phi_is less
        by auto
    next
      case (Or_mltl \<phi>2 \<phi>3)
      then show ?thesis using phi_is less
        by auto
    next
      case (Future_mltl a b \<phi>2)
      then have *: "a \<le> b" using less(2)
        phi_is by simp
      have "semantics_mltl \<pi> (convert_nnf \<phi>) = semantics_mltl \<pi> (Global_mltl a b (convert_nnf (Not\<^sub>m \<phi>2)))"
        using Future_mltl phi_is by simp
      then have semantics_unfold: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>2)))))"
        by auto
      have "intervals_welldef (Not\<^sub>m \<phi>2)"
        using less(2) Future_mltl phi_is by simp
      then have "semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>2)) =  semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>2)" for i
        using less(1)[of "Not\<^sub>m \<phi>2" "(drop i \<pi>)"] phi_is Future_mltl
        by auto
      then have semantics_unfold1: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>2))))"
        using semantics_unfold by auto
      have "semantics_mltl \<pi> \<phi> = (\<not> (semantics_mltl \<pi> (Future_mltl a b \<phi>2)))"
        using phi_is Future_mltl by simp
      then show ?thesis using semantics_unfold1 *
        by auto
    next
      case (Global_mltl a b \<phi>2)
      then have *: "a \<le> b" using less(2)
        phi_is by simp
      have "semantics_mltl \<pi> (convert_nnf \<phi>) = semantics_mltl \<pi> (Future_mltl a b (convert_nnf (Not\<^sub>m \<phi>2)))"
        using Global_mltl phi_is by simp
      then have semantics_unfold: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>2))))"
        by auto
      have "intervals_welldef (Not\<^sub>m \<phi>2)"
        using less(2) Global_mltl phi_is by simp
      then have "semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>2)) =  semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>2)" for i
        using less(1)[of "Not\<^sub>m \<phi>2" "(drop i \<pi>)"] phi_is Global_mltl
        by auto
      then have semantics_unfold1: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>2)))"
        using semantics_unfold by auto
       have "semantics_mltl \<pi> \<phi> = (\<not> (semantics_mltl \<pi> (Global_mltl a b \<phi>2)))"
         using phi_is Global_mltl by simp
       then show ?thesis using semantics_unfold1 *
         by auto
    next
      case (Until_mltl \<phi>2 a b \<phi>3)
      then have *: "a \<le> b" using less(2)
        phi_is by simp
      have "semantics_mltl \<pi> (convert_nnf \<phi>) = semantics_mltl \<pi> (Release_mltl (convert_nnf (Not\<^sub>m \<phi>2)) a b (convert_nnf (Not\<^sub>m \<phi>3)))"
        using Until_mltl phi_is by simp
      then have semantics_unfold: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> ((semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>3))))) \<or> (\<exists>j. j \<ge> a \<and> j \<le> b-1 \<and> semantics_mltl (drop j \<pi>) (convert_nnf (Not\<^sub>m \<phi>2)) \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) (convert_nnf (Not\<^sub>m \<phi>3))))))"
        by auto
      have phi3_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>3)) = semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>3)" for i
        using less(1)[of "Not\<^sub>m \<phi>3" "(drop i \<pi>)"] phi_is Until_mltl
        using less.prems by force
      have phi2_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>2)) = semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>2)" for i
        using less(1)[of "Not\<^sub>m \<phi>2" "(drop i \<pi>)"] phi_is Until_mltl
        using less.prems by force
      have semantics_unfold1: "semantics_mltl \<pi> (convert_nnf \<phi>) = (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> ((semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>3)))) \<or> (\<exists>j. j \<ge> a \<and> j \<le> b-1 \<and> semantics_mltl (drop j \<pi>)  (Not\<^sub>m \<phi>2) \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) (Not\<^sub>m \<phi>3))))"
        using * phi3_ind_h phi2_ind_h semantics_unfold by auto
      have "semantics_mltl \<pi> \<phi> = semantics_mltl \<pi> (Release_mltl (Not\<^sub>m \<phi>2) a b (Not\<^sub>m \<phi>3))"
        using Until_mltl phi_is until_release_dual[OF *]
        using semantics_mltl.simps(4)
        using semantic_equiv_def by blast
       then show ?thesis using semantics_unfold1 *
          by auto
    next
      case (Release_mltl \<phi>2 a b \<phi>3)
       then have *: "a \<le> b" using less(2)
        phi_is by simp
      have "semantics_mltl \<pi> (convert_nnf \<phi>) = semantics_mltl \<pi> (Until_mltl (convert_nnf (Not\<^sub>m \<phi>2)) a b (convert_nnf (Not\<^sub>m \<phi>3)))"
        using Release_mltl phi_is by simp
      then have semantics_unfold: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (semantics_mltl (drop i \<pi>)  (convert_nnf (Not\<^sub>m \<phi>3)) \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> semantics_mltl (drop j \<pi> )  (convert_nnf (Not\<^sub>m \<phi>2))))))"
        by auto
      have phi3_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>3)) = semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>3)" for i
        using less(1)[of "Not\<^sub>m \<phi>3" "(drop i \<pi>)"] phi_is Release_mltl
        using less.prems by force
      have phi2_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf (Not\<^sub>m \<phi>2)) = semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>2)" for i
        using less(1)[of "Not\<^sub>m \<phi>2" "(drop i \<pi>)"] phi_is Release_mltl
        using less.prems by force
      have semantics_unfold1: "semantics_mltl \<pi> (convert_nnf \<phi>) = (length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (semantics_mltl (drop i \<pi>) (Not\<^sub>m \<phi>3) \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> semantics_mltl (drop j \<pi>) (Not\<^sub>m \<phi>2)))))"
        using * phi3_ind_h phi2_ind_h semantics_unfold by auto
      have "semantics_mltl \<pi> \<phi> = semantics_mltl \<pi> (Until_mltl (Not\<^sub>m \<phi>2) a b (Not\<^sub>m \<phi>3))"
        using Release_mltl phi_is release_until_dual[OF *]
        using semantics_mltl.simps(4) unfolding semantic_equiv_def by metis
       then show ?thesis using semantics_unfold1 *
          by auto
    qed
  next
    case (And_mltl \<phi>1 \<phi>2)
    then show ?thesis using less by simp
  next
    case (Or_mltl \<phi>1 \<phi>2)
    then show ?thesis using less by simp
  next
    case (Future_mltl a b \<phi>1)
    then have "intervals_welldef \<phi>1"
      using less(2) by simp
    then have ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf \<phi>1) = semantics_mltl (drop i \<pi>)  \<phi>1" for i
      using Future_mltl less(1)[of \<phi>1 "(drop i \<pi>)"]
      by auto
    have unfold_future: "semantics_mltl \<pi> (convert_nnf (Future_mltl a b \<phi>1)) = semantics_mltl \<pi> (Future_mltl a b (convert_nnf \<phi>1))"
      by simp
    moreover then have unfold_future_semantics: "... = (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) (convert_nnf \<phi>1)))"
      by simp
    moreover then have "... = (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) \<phi>1))"
      using ind_h
      by auto
    ultimately show ?thesis using Future_mltl
      by simp
  next
    case (Global_mltl a b \<phi>1)
    then have "intervals_welldef \<phi>1"
      using less(2) by simp
    then have ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf \<phi>1) = semantics_mltl (drop i \<pi>)  \<phi>1" for i
      using Global_mltl less(1)[of \<phi>1 "(drop i \<pi>)"]
      by auto
    have unfold_future: "semantics_mltl \<pi> (convert_nnf (Global_mltl a b \<phi>1)) = semantics_mltl \<pi> (Global_mltl a b (convert_nnf \<phi>1))"
      by simp
    moreover then have unfold_future_semantics: "... = (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> semantics_mltl (drop i \<pi>) (convert_nnf \<phi>1))))"
      by simp
    moreover then have "... = (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> semantics_mltl (drop i \<pi>) \<phi>1)))"
      using ind_h
      by auto
    ultimately show ?thesis using Global_mltl
      by simp
  next
    case (Until_mltl \<phi>1 a b \<phi>2)
    then have *: "a \<le> b" using less(2)
        Until_mltl by simp
    have semantics_unfold: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (semantics_mltl (drop i \<pi>) (convert_nnf \<phi>2) \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> semantics_mltl (drop j \<pi> ) (convert_nnf \<phi>1)))))"
        using Until_mltl by auto
      have phi3_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf \<phi>1) = semantics_mltl (drop i \<pi>) \<phi>1" for i
        using less(1)[of \<phi>1 "(drop i \<pi>)"] Until_mltl less.prems
        by force
      have phi2_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf \<phi>2) = semantics_mltl (drop i \<pi>) \<phi>2" for i
        using less(1)[of \<phi>2 "(drop i \<pi>)"] Until_mltl less.prems
        by force
      have semantics_unfold1: "semantics_mltl \<pi> (convert_nnf \<phi>) = (length \<pi> > a \<and> (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (semantics_mltl (drop i \<pi>) \<phi>2 \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> semantics_mltl (drop j \<pi> ) \<phi>1))))"
        using * phi3_ind_h phi2_ind_h semantics_unfold
        by auto
      then show ?thesis using semantics_unfold1 * Until_mltl
        by auto
  next
    case (Release_mltl \<phi>1 a b \<phi>2)
    then have *: "a \<le> b" using less(2)
       Release_mltl by simp
    have semantics_unfold: "semantics_mltl \<pi> (convert_nnf \<phi>) = (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> ((semantics_mltl (drop i \<pi>) (convert_nnf \<phi>2)))) \<or> (\<exists>j. j \<ge> a \<and> j \<le> b-1 \<and> semantics_mltl (drop j \<pi>) (convert_nnf \<phi>1) \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) (convert_nnf \<phi>2)))))"
       using Release_mltl by auto
    have phi3_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf \<phi>1) = semantics_mltl (drop i \<pi>) \<phi>1" for i
       using less(1)[of \<phi>1 "(drop i \<pi>)"] Release_mltl less.prems
       by force
    have phi2_ind_h: "semantics_mltl (drop i \<pi>) (convert_nnf \<phi>2) = semantics_mltl (drop i \<pi>) \<phi>2" for i
       using less(1)[of \<phi>2 "(drop i \<pi>)"] Release_mltl less.prems
       by force
    have semantics_unfold1: "semantics_mltl \<pi> (convert_nnf \<phi>) = (length \<pi> \<le> a \<or> (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> ((semantics_mltl (drop i \<pi>) \<phi>2))) \<or> (\<exists>j. j \<ge> a \<and> j \<le> b-1 \<and> semantics_mltl (drop j \<pi>) \<phi>1 \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) \<phi>2)))"
       using * phi3_ind_h phi2_ind_h semantics_unfold
       by auto
    then show ?thesis using semantics_unfold1 * Release_mltl
       by auto
  qed
qed

lemma convert_nnf_form_Not_Implies_Prop:
  assumes "Not\<^sub>m F = convert_nnf init_F"
  shows "\<exists>p. F = Prop\<^sub>m (p)"
  using assms
proof (induct "depth_mltl init_F" arbitrary: init_F rule: less_induct)
  case less
  then have ind_h1: "\<And>G. depth_mltl G < depth_mltl init_F \<Longrightarrow>
    Not_mltl F = convert_nnf G \<Longrightarrow> \<exists>p. F = Prop_mltl p"
    by auto
  have not: "Not_mltl F = convert_nnf init_F" using less
    by auto
  then show ?case proof (cases init_F)
    case True_mltl
    then show ?thesis using ind_h1 not by auto
  next
    case False_mltl
    then show ?thesis using ind_h1 not by auto
  next
    case (Prop_mltl p)
    then show ?thesis using ind_h1 not by auto
  next
    case (Not_mltl \<phi>)
    then have init_F_is: "init_F = Not\<^sub>m \<phi>"
      by auto
    then show ?thesis  proof (cases \<phi>)
      case True_mltl
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case False_mltl
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Prop_mltl p)
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Not_mltl \<phi>)
      then have not_convert: "Not_mltl F = convert_nnf \<phi>" using not init_F_is
        by auto
      have depth: "depth_mltl \<phi> < depth_mltl init_F"
        using Not_mltl init_F_is by auto
      then show ?thesis using ind_h1[OF depth not_convert] by auto
    next
      case (And_mltl \<phi> \<psi>)
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Or_mltl \<phi> \<psi>)
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Future_mltl a b \<phi>)
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Global_mltl a b \<phi>)
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Until_mltl \<phi> a b \<psi>)
      then show ?thesis using ind_h1 not init_F_is by auto
    next
      case (Release_mltl \<phi> a b \<psi>)
      then show ?thesis using ind_h1 not init_F_is by auto
    qed
  next
    case (And_mltl \<phi> \<psi>)
    then show ?thesis using ind_h1 not by auto
  next
    case (Or_mltl \<phi> \<psi>)
    then show ?thesis using ind_h1 not by auto
  next
    case (Future_mltl a b \<phi>)
    then show ?thesis using ind_h1 not by auto
  next
    case (Global_mltl a b \<phi>)
    then show ?thesis using ind_h1 not by auto
  next
    case (Until_mltl \<phi> a b \<psi>)
    then show ?thesis using ind_h1 not by auto
  next
    case (Release_mltl \<phi> a b \<psi>)
    then show ?thesis using ind_h1 not by auto
  qed
qed

lemma convert_nnf_convert_nnf:
  shows "convert_nnf (convert_nnf F) = convert_nnf F"
proof (induction "depth_mltl F" arbitrary: F rule: less_induct)
  case less
  have not_case: "(\<And>F. depth_mltl F < Suc (depth_mltl G) \<Longrightarrow>
               convert_nnf (convert_nnf F) = convert_nnf F) \<Longrightarrow>
          F = Not_mltl G \<Longrightarrow>
          convert_nnf (convert_nnf (Not_mltl G)) = convert_nnf (Not_mltl G)" for "G"
  proof -
    assume ind_h: "(\<And>F. depth_mltl F < Suc (depth_mltl G) \<Longrightarrow>
               convert_nnf (convert_nnf F) = convert_nnf F)"
    assume F_is: "F = Not_mltl G"
    show ?thesis using less F_is apply (cases G) by simp_all
  qed
  show ?case using less apply (cases F) apply simp_all using not_case
    by auto
qed

lemma nnf_subformulas:
  assumes "F = convert_nnf init_F"
  assumes "G \<in> subformulas F"
  shows "\<exists> init_G. G = convert_nnf init_G"
  using assms proof (induct "depth_mltl init_F" arbitrary: init_F F G rule: less_induct)
  case less
  then show ?case proof (cases init_F)
    case True_mltl
    then show ?thesis using less by simp
  next
    case False_mltl
    then show ?thesis using less by simp
  next
    case (Prop_mltl p)
    then show ?thesis using less by simp
  next
    case (Not_mltl \<phi>)
    then have init_is: "init_F = Not\<^sub>m \<phi>"
      by auto
    then show ?thesis proof (cases \<phi>)
      case True_mltl
      then show ?thesis using less init_is
        by auto
    next
      case False_mltl
      then show ?thesis using less init_is
        by auto
    next
      case (Prop_mltl p)
      then have "init_F = (Not_mltl Prop\<^sub>m (p))"
        using init_is by auto
      then have "G = Prop_mltl p"
        using less by simp
      then have "G = convert_nnf Prop\<^sub>m (p)"
        by auto
      then show ?thesis by blast
    next
      case (Not_mltl \<psi>)
      then have init_is2: "init_F = (Not_mltl (Not_mltl \<psi>))"
        using init_is by auto
      then have F_is: "F = convert_nnf \<psi>"
        using less by auto
      then show ?thesis using less.hyps[OF _ F_is] init_is2 less(3)
        by simp
    next
      case (And_mltl \<psi>1 \<psi>2)
        then have init_is2: "init_F = (Not_mltl (And_mltl \<psi>1 \<psi>2))"
        using init_is by auto
      then have F_is: "F = (Or_mltl (convert_nnf (Not_mltl \<psi>1)) (convert_nnf (Not_mltl \<psi>2)))"
        using less by auto
      have depth1: "depth_mltl (Not_mltl \<psi>1) < depth_mltl init_F"
        using init_is2
        by simp
      have depth2: "depth_mltl (Not_mltl \<psi>2) < depth_mltl init_F"
        using init_is2
        by simp
      have G_inset: "G \<in> {(convert_nnf (Not_mltl \<psi>1)), (convert_nnf (Not_mltl \<psi>2))}
        \<union> subformulas (convert_nnf (Not_mltl \<psi>1)) \<union> subformulas (convert_nnf (Not_mltl \<psi>2))"
        using F_is less(3) by auto
      then show ?thesis using less.hyps[OF depth1, of "convert_nnf (Not_mltl \<psi>1)"] less.hyps[OF depth2, of "convert_nnf (Not_mltl \<psi>2)"]
        G_inset by blast
    next
      case (Or_mltl \<psi>1 \<psi>2)
        then have init_is2: "init_F = (Not_mltl (Or_mltl \<psi>1 \<psi>2))"
        using init_is by auto
      then have F_is: "F = (And_mltl (convert_nnf (Not_mltl \<psi>1)) (convert_nnf (Not_mltl \<psi>2)))"
        using less by auto
      have depth1: "depth_mltl (Not_mltl \<psi>1) < depth_mltl init_F"
        using init_is2
        by simp
      have depth2: "depth_mltl (Not_mltl \<psi>2) < depth_mltl init_F"
        using init_is2
        by simp
      have G_inset: "G \<in> {(convert_nnf (Not_mltl \<psi>1)), (convert_nnf (Not_mltl \<psi>2))}
        \<union> subformulas (convert_nnf (Not_mltl \<psi>1)) \<union> subformulas (convert_nnf (Not_mltl \<psi>2))"
        using F_is less(3) by auto
      then show ?thesis using less.hyps[OF depth1, of "convert_nnf (Not_mltl \<psi>1)"] less.hyps[OF depth2, of "convert_nnf (Not_mltl \<psi>2)"]
        G_inset by blast
    next
      case (Future_mltl a b \<psi>)
      then have init_is2: "init_F = (Not_mltl (Future_mltl a b \<psi>))"
        using init_is by auto
      then have F_is: "F = (Global_mltl a b (convert_nnf (Not_mltl \<psi>)))"
        using less by auto
      have depth1: "depth_mltl (Not_mltl \<psi>) < depth_mltl init_F"
        using init_is2
        by simp
      have G_inset: "G \<in> {(convert_nnf (Not_mltl \<psi>))}
        \<union> subformulas (convert_nnf (Not_mltl \<psi>))"
        using F_is less(3) by auto
      then show ?thesis using less.hyps[OF depth1, of "convert_nnf (Not_mltl \<psi>)"]
        G_inset by blast
    next
      case (Global_mltl a b \<psi>)
      then have init_is2: "init_F = (Not_mltl (Global_mltl a b \<psi>))"
        using init_is by auto
      then have F_is: "F = (Future_mltl a b (convert_nnf (Not_mltl \<psi>)))"
        using less by auto
      have depth1: "depth_mltl (Not_mltl \<psi>) < depth_mltl init_F"
        using init_is2
        by simp
      have G_inset: "G \<in> {(convert_nnf (Not_mltl \<psi>))}
        \<union> subformulas (convert_nnf (Not_mltl \<psi>))"
        using F_is less(3) by auto
      then show ?thesis using less.hyps[OF depth1, of "convert_nnf (Not_mltl \<psi>)"]
        G_inset by blast
    next
      case (Until_mltl \<psi>1 a b \<psi>2)
     then have init_is2: "init_F = (Not_mltl (Until_mltl \<psi>1 a b \<psi>2))"
        using init_is by auto
      then have F_is: "F = (Release_mltl (convert_nnf (Not_mltl \<psi>1)) a b (convert_nnf (Not_mltl \<psi>2)))"
        using less by auto
      have depth1: "depth_mltl (Not_mltl \<psi>1) < depth_mltl init_F"
        using init_is2
        by simp
      have depth2: "depth_mltl (Not_mltl \<psi>2) < depth_mltl init_F"
        using init_is2
        by simp
      have G_inset: "G \<in> {(convert_nnf (Not_mltl \<psi>1)), (convert_nnf (Not_mltl \<psi>2))}
        \<union> subformulas (convert_nnf (Not_mltl \<psi>1)) \<union> subformulas (convert_nnf (Not_mltl \<psi>2))"
        using F_is less(3) by auto
      then show ?thesis using less.hyps[OF depth1, of "convert_nnf (Not_mltl \<psi>1)"] less.hyps[OF depth2, of "convert_nnf (Not_mltl \<psi>2)"]
        G_inset by blast
    next
      case (Release_mltl \<psi>1 a b \<psi>2)
     then have init_is2: "init_F = (Not_mltl (Release_mltl \<psi>1 a b \<psi>2))"
        using init_is by auto
      then have F_is: "F = (Until_mltl (convert_nnf (Not_mltl \<psi>1)) a b (convert_nnf (Not_mltl \<psi>2)))"
        using less by auto
      have depth1: "depth_mltl (Not_mltl \<psi>1) < depth_mltl init_F"
        using init_is2
        by simp
      have depth2: "depth_mltl (Not_mltl \<psi>2) < depth_mltl init_F"
        using init_is2
        by simp
      have G_inset: "G \<in> {(convert_nnf (Not_mltl \<psi>1)), (convert_nnf (Not_mltl \<psi>2))}
        \<union> subformulas (convert_nnf (Not_mltl \<psi>1)) \<union> subformulas (convert_nnf (Not_mltl \<psi>2))"
        using F_is less(3) by auto
      then show ?thesis using less.hyps[OF depth1, of "convert_nnf (Not_mltl \<psi>1)"] less.hyps[OF depth2, of "convert_nnf (Not_mltl \<psi>2)"]
        G_inset by blast
    qed
  next
    case (And_mltl \<phi>1 \<phi>2)
    then have F_is: "F = And_mltl (convert_nnf \<phi>1) (convert_nnf \<phi>2)"
      using less by auto
    then have G_inset: "G \<in> {(convert_nnf \<phi>1), (convert_nnf \<phi>2)} \<union> subformulas (convert_nnf \<phi>1) \<union>
      subformulas (convert_nnf \<phi>2)" using less(3) by simp
    have depth_phi1: "depth_mltl \<phi>1 < depth_mltl init_F"
      using less And_mltl by simp
    have depth_phi2: "depth_mltl \<phi>2 < depth_mltl init_F"
      using less And_mltl by simp
    then show ?thesis using less.hyps[OF depth_phi1, of "convert_nnf \<phi>1"] using less.hyps[OF depth_phi2, of "convert_nnf \<phi>2"]
        G_inset by blast
  next
    case (Or_mltl \<phi>1 \<phi>2)
    then have F_is: "F = Or_mltl (convert_nnf \<phi>1) (convert_nnf \<phi>2)"
      using less by auto
    then have G_inset: "G \<in> {(convert_nnf \<phi>1), (convert_nnf \<phi>2)} \<union> subformulas (convert_nnf \<phi>1) \<union>
      subformulas (convert_nnf \<phi>2)" using less(3) by simp
    have depth_phi1: "depth_mltl \<phi>1 < depth_mltl init_F"
      using less Or_mltl by simp
    have depth_phi2: "depth_mltl \<phi>2 < depth_mltl init_F"
      using less Or_mltl by simp
    then show ?thesis using less.hyps[OF depth_phi1, of "convert_nnf \<phi>1"] using less.hyps[OF depth_phi2, of "convert_nnf \<phi>2"]
        G_inset by blast
  next
    case (Future_mltl a b \<phi>)
    then have F_is: "F = Future_mltl a b (convert_nnf \<phi>)"
      using less by auto
    then have G_inset: "G \<in> {(convert_nnf \<phi>)} \<union> subformulas (convert_nnf \<phi>)"
      using less(3) by simp
    have depth_phi1: "depth_mltl \<phi> < depth_mltl init_F"
      using less Future_mltl by simp
    then show ?thesis using less.hyps[OF depth_phi1, of "convert_nnf \<phi>"]
        G_inset by blast
  next
    case (Global_mltl a b \<phi>)
    then have F_is: "F = Global_mltl a b (convert_nnf \<phi>)"
      using less by auto
    then have G_inset: "G \<in> {(convert_nnf \<phi>)} \<union> subformulas (convert_nnf \<phi>)"
      using less(3) by simp
    have depth_phi1: "depth_mltl \<phi> < depth_mltl init_F"
      using less Global_mltl by simp
    then show ?thesis using less.hyps[OF depth_phi1, of "convert_nnf \<phi>"]
        G_inset by blast
  next
    case (Until_mltl \<phi>1 a b \<phi>2)
    then have F_is: "F = Until_mltl (convert_nnf \<phi>1) a b (convert_nnf \<phi>2)"
      using less by auto
    then have G_inset: "G \<in> {(convert_nnf \<phi>1), (convert_nnf \<phi>2)} \<union> subformulas (convert_nnf \<phi>1) \<union>
      subformulas (convert_nnf \<phi>2)" using less(3) by simp
    have depth_phi1: "depth_mltl \<phi>1 < depth_mltl init_F"
      using less Until_mltl by simp
    have depth_phi2: "depth_mltl \<phi>2 < depth_mltl init_F"
      using less Until_mltl by simp
    then show ?thesis using less.hyps[OF depth_phi1, of "convert_nnf \<phi>1"] using less.hyps[OF depth_phi2, of "convert_nnf \<phi>2"]
        G_inset by blast
  next
    case (Release_mltl \<phi>1 a b \<phi>2)
     then have F_is: "F = Release_mltl (convert_nnf \<phi>1) a b (convert_nnf \<phi>2)"
      using less by auto
    then have G_inset: "G \<in> {(convert_nnf \<phi>1), (convert_nnf \<phi>2)} \<union> subformulas (convert_nnf \<phi>1) \<union>
      subformulas (convert_nnf \<phi>2)" using less(3) by simp
    have depth_phi1: "depth_mltl \<phi>1 < depth_mltl init_F"
      using less Release_mltl by simp
    have depth_phi2: "depth_mltl \<phi>2 < depth_mltl init_F"
      using less Release_mltl by simp
    then show ?thesis using less.hyps[OF depth_phi1, of "convert_nnf \<phi>1"] using less.hyps[OF depth_phi2, of "convert_nnf \<phi>2"]
        G_inset by blast
  qed
qed


subsection \<open>Computation Length and Properties\<close>

fun complen_mltl:: "'a mltl \<Rightarrow> nat"
  where "complen_mltl False\<^sub>m = 1"
  | "complen_mltl True\<^sub>m = 1"
  | "complen_mltl Prop\<^sub>m (p) = 1"
  | "complen_mltl (Not\<^sub>m \<phi>) = complen_mltl \<phi>"
  | "complen_mltl (\<phi> And\<^sub>m \<psi>) = max (complen_mltl \<phi>) (complen_mltl \<psi>)"
  | "complen_mltl (\<phi> Or\<^sub>m \<psi>) = max (complen_mltl \<phi>) (complen_mltl \<psi>)"
  | "complen_mltl (G\<^sub>m [a,b] \<phi>) = b + (complen_mltl \<phi>)"
  | "complen_mltl (F\<^sub>m [a,b] \<phi>) = b + (complen_mltl \<phi>)"
  | "complen_mltl (\<phi> R\<^sub>m [a,b] \<psi>) = b + (max ((complen_mltl \<phi>)-1) (complen_mltl \<psi>))"
  | "complen_mltl (\<phi> U\<^sub>m [a,b] \<psi>) = b + (max ((complen_mltl \<phi>)-1) (complen_mltl \<psi>))"

lemma complen_geq_one: "complen_mltl F \<ge> 1"
  apply (induct F) apply simp_all .

subsubsection \<open>Capture (not (a <= b)) in an MLTL formula\<close>
fun make_empty_trace:: "nat \<Rightarrow> 'a set list"
  where "make_empty_trace 0 = []"
  | "make_empty_trace n = [{}]@ make_empty_trace (n-1)"

lemma length_make_empty_trace:
  shows "length (make_empty_trace n) = n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by auto
qed


lemma semantics_of_not_a_lteq_b:
  shows "(make_empty_trace (a+1)) \<Turnstile>\<^sub>m (Global_mltl a b True\<^sub>m) = (a \<le> b)"
  using length_make_empty_trace
  by simp

lemma semantics_of_not_a_lteq_b2:
  shows "(make_empty_trace (a+1)) \<Turnstile>\<^sub>m (Not_mltl (Global_mltl a b True\<^sub>m)) = (\<not> (a \<le> b))"
  using semantics_of_not_a_lteq_b
  by simp

subsection \<open>Custom Induction Rules\<close>

text \<open> In some cases, it is sufficient to consider
 just a subset of MLTL operators when proving a property.
 We facilitate this with the following custom induction
 rules. \<close>

text \<open> In order to use the MLTL-induct rule,
  one must establish IntervalsWellDef, which
  states that the input formula is well-formed,
  and also prove PProp, which states that the
  property being established is not dependent on
  the syntax of the input formula but only on its
  semantics. \<close>
lemma MLTL_induct[case_names IntervalsWellDef PProp True False Prop Not And Until]:
  assumes IntervalsWellDef: "intervals_welldef F"
    and PProp: "(\<And> F G. ((\<forall>\<pi>. semantics_mltl \<pi> F = semantics_mltl \<pi> G) \<longrightarrow> P F = P G))"
    and True: "P True\<^sub>m"
    and False: "P False\<^sub>m"
    and Prop: "\<And> p. P Prop\<^sub>m (p)"
    and Not: "\<And> F G. \<lbrakk>F = Not\<^sub>m G; P G\<rbrakk> \<Longrightarrow> P F"
    and And: "\<And>F F1 F2.  \<lbrakk>F = F1 And\<^sub>m F2;
        P F1; P F2\<rbrakk> \<Longrightarrow> P F"
    and Until:"\<And>F F1 F2 a b.  \<lbrakk>F = F1 U\<^sub>m [a,b] F2;
        P F1; P F2\<rbrakk> \<Longrightarrow> P F"
  shows "P F" using IntervalsWellDef
proof (induction F)
  case True_mltl
  then show ?case using True by simp
next
  case False_mltl
  then show ?case using False by simp
next
  case (Prop_mltl x)
  then show ?case using Prop by simp
next
  case (Not_mltl F1)
  then show ?case using Not by auto
next
  case (And_mltl F1 F2)
  then show ?case using And by auto
next
  case (Or_mltl F1 F2)
  have "\<And> \<pi>. semantics_mltl \<pi> (Or_mltl (Not_mltl (Not_mltl F1)) (Not_mltl (Not_mltl F2))) =
     semantics_mltl \<pi> (Or_mltl F1 F2)"
    using not_not_equiv
    by auto
  then have P1: "P (Or_mltl F1 F2) = P (Or_mltl (Not_mltl (Not_mltl F1)) (Not_mltl (Not_mltl F2)))"
    using PProp by blast
  have "\<And> \<pi>. semantics_mltl \<pi> (Not_mltl (And_mltl (Not_mltl F1) (Not_mltl F2))) =
    semantics_mltl \<pi> (Or_mltl (Not_mltl (Not_mltl F1)) (Not_mltl (Not_mltl F2)))"
    using demorgan_and_or[of "(Not_mltl F1)" "(Not_mltl F2)"]
    unfolding semantic_equiv_def by simp
  then have P2: "P (Not_mltl (And_mltl (Not_mltl F1) (Not_mltl F2))) = P (Or_mltl (Not_mltl (Not_mltl F1)) (Not_mltl (Not_mltl F2)))"
    using PProp by blast
  show ?case using P1 P2
    using And Not PProp
    using Or_mltl.IH(1) Or_mltl.IH(2) Or_mltl.prems by force
next
  case (Future_mltl a b F)
  then show ?case
    using future_as_until PProp IntervalsWellDef Until True
    unfolding semantic_equiv_def
    by (metis True Until intervals_welldef.simps(7))
next
  case (Global_mltl a b F)
  then show ?case using globally_future_dual Not PProp True Until future_as_until
    unfolding semantic_equiv_def
    by (metis intervals_welldef.simps(8))
next
  case (Until_mltl F1 a b F2)
  then show ?case using Until using intervals_welldef.simps(9)[of F1 a b F2]
    by blast
next
  case (Release_mltl F1 a b F2)
  have a_lt_b: "a \<le> b" using Release_mltl(3) intervals_welldef.simps(10)[of F1 a b F2]
    by auto
  have PF: "P F1 \<and> P F2"
    using Release_mltl using intervals_welldef.simps(10)[of F1 a b F2]
    by blast
  have "P (Release_mltl F1 a b F2) \<longleftrightarrow> P (Not_mltl (Until_mltl (Not_mltl F1) a b (Not_mltl F2)))"
    using release_until_dual[OF a_lt_b, of F1 F2]  PProp
    unfolding semantic_equiv_def by metis
  then show ?case using Not
    using PF Until by force
qed

text \<open> In order to use the nnf-induct rule,
  one must establish that the input formula (i.e.
  the formula being inducted on) is in NNF format. \<close>
lemma nnf_induct[case_names nnf True False Prop And Or Final Global Until Release NotProp]:
  assumes nnf: "\<exists>init_F. F = convert_nnf init_F"
    and True: "P True\<^sub>m"
    and False: "P False\<^sub>m"
    and Prop: "\<And> p. P Prop\<^sub>m (p)"
    and And: "\<And>F F1 F2.  \<lbrakk>F = F1 And\<^sub>m F2;
        P F1; P F2\<rbrakk> \<Longrightarrow> P F"
    and Or: "\<And>F F1 F2.  \<lbrakk>F = F1 Or\<^sub>m F2;
        P F1; P F2\<rbrakk> \<Longrightarrow> P F"
    and Final: "\<And>F F1  a b.  \<lbrakk>F = F\<^sub>m [a,b] F1;
        P F1\<rbrakk> \<Longrightarrow> P F"
    and Global: "\<And>F F1  a b.  \<lbrakk>F = G\<^sub>m [a,b] F1;
        P F1\<rbrakk> \<Longrightarrow> P F"
    and Until: "\<And>F F1 F2  a b.  \<lbrakk>F = F1 U\<^sub>m [a,b] F2;
        P F1; P F2\<rbrakk> \<Longrightarrow> P F"
    and Release: "\<And>F F1 F2 a b.  \<lbrakk>F = F1 R\<^sub>m [a,b] F2;
        P F1; P F2\<rbrakk> \<Longrightarrow> P F"
    and Not_Prop: "\<And> F p. F = Not\<^sub>m Prop\<^sub>m (p) \<Longrightarrow> P F"
  shows "P F" using nnf proof (induct F)
  case True_mltl
  then show ?case using True by auto
next
  case False_mltl
  then show ?case using False by auto
next
  case (Prop_mltl x)
  then show ?case using Prop by auto
next
  case (Not_mltl F)
  then show ?case using convert_nnf_form_Not_Implies_Prop Not_Prop by blast
next
  case (And_mltl F1 F2)
  then obtain init_F where init_F: "And_mltl F1 F2 = convert_nnf init_F"
    by auto
  then have "(\<exists>init_F1. F1 = convert_nnf init_F1) \<and> (\<exists>init_F2. F2 = convert_nnf init_F2)"
    using nnf_subformulas[OF init_F] subformulas.simps(5) by blast
  then show ?case using And_mltl And by auto
next
  case (Or_mltl F1 F2)
  then obtain init_F where init_F: "Or_mltl F1 F2 = convert_nnf init_F"
    by auto
  then have "(\<exists>init_F1. F1 = convert_nnf init_F1) \<and> (\<exists>init_F2. F2 = convert_nnf init_F2)"
    using nnf_subformulas[OF init_F] subformulas.simps(6) by blast
  then show ?case using Or_mltl Or by auto
next
  case (Future_mltl a b F)
  then obtain init_F where init_F: "Future_mltl a b F = convert_nnf init_F"
    by auto
  then have "(\<exists>init_F1. F = convert_nnf init_F1)"
    using nnf_subformulas[OF init_F] subformulas.simps(8) by blast
  then show ?case using Future_mltl Final by auto
next
  case (Global_mltl a b F)
  then obtain init_F where init_F: "Global_mltl a b F = convert_nnf init_F"
    by auto
  then have "(\<exists>init_F1. F = convert_nnf init_F1)"
    using nnf_subformulas[OF init_F] subformulas.simps(7) by blast
  then show ?case using Global_mltl Global by auto
next
  case (Until_mltl F1 a b F2)
  then obtain init_F where init_F: "Until_mltl F1 a b F2 = convert_nnf init_F"
    by auto
  then have "(\<exists>init_F1. F1 = convert_nnf init_F1) \<and> (\<exists>init_F2. F2 = convert_nnf init_F2)"
    using nnf_subformulas[OF init_F] subformulas.simps(9) by blast
  then show ?case using Until_mltl Until by auto
next
  case (Release_mltl F1 a b F2)
  then obtain init_F where init_F: "Release_mltl F1 a b F2 = convert_nnf init_F"
    by auto
  then have "(\<exists>init_F1. F1 = convert_nnf init_F1) \<and> (\<exists>init_F2. F2 = convert_nnf init_F2)"
    using nnf_subformulas[OF init_F] subformulas.simps(10) by blast
  then show ?case using Release_mltl Release by auto
qed

end