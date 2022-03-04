section\<open>Various results missing from ZF.\<close>

theory ZF_Miscellanea
  imports
    ZF
    Nat_Miscellanea
begin

lemma function_subset:
  "function(f) \<Longrightarrow> g\<subseteq>f \<Longrightarrow> function(g)"
  unfolding function_def subset_def by auto

lemma converse_refl : "refl(A,r) \<Longrightarrow> refl(A,converse(r))"
  unfolding refl_def by simp

lemma Ord_lt_subset : "Ord(b) \<Longrightarrow> a<b \<Longrightarrow> a\<subseteq>b"
  by(intro subsetI,frule ltD,rule_tac Ord_trans,simp_all)

lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp_all add: apply_Pair)

lemma vimage_fun_sing:
  assumes "f\<in>A\<rightarrow>B" "b\<in>B"
  shows "{a\<in>A . f`a=b} = f-``{b}"
  using assms vimage_singleton_iff function_apply_equality Pi_iff funcI by auto

lemma image_fun_subset: "S\<in>A\<rightarrow>B \<Longrightarrow> C\<subseteq>A\<Longrightarrow> {S ` x . x\<in> C} = S``C"
  using image_function[symmetric,of S C] domain_of_fun Pi_iff by auto

lemma subset_Diff_Un: "X \<subseteq> A \<Longrightarrow> A = (A - X) \<union> X " by auto

lemma Diff_bij:
  assumes "\<forall>A\<in>F. X \<subseteq> A" shows "(\<lambda>A\<in>F. A-X) \<in> bij(F, {A-X. A\<in>F})"
  using assms unfolding bij_def inj_def surj_def
  by (auto intro:lam_type, subst subset_Diff_Un[of X]) auto

lemma function_space_nonempty:
  assumes "b\<in>B"
  shows "(\<lambda>x\<in>A. b) : A \<rightarrow> B"
  using assms lam_type by force

lemma vimage_lam: "(\<lambda>x\<in>A. f(x)) -`` B = { x\<in>A . f(x) \<in> B }"
  using lam_funtype[of A f, THEN [2] domain_type]
    lam_funtype[of A f, THEN [2] apply_equality] lamI[of _ A f]
  by auto blast

lemma range_fun_subset_codomain:
  assumes "h:B \<rightarrow> C"
  shows "range(h) \<subseteq> C"
  unfolding range_def domain_def converse_def using range_type[OF _ assms]  by auto

lemma Pi_rangeD:
  assumes "f\<in>Pi(A,B)" "b \<in> range(f)"
  shows "\<exists>a\<in>A. f`a = b"
  using assms apply_equality[OF _ assms(1), of _ b]
    domain_type[OF _ assms(1)] by auto

lemma Pi_range_eq: "f \<in> Pi(A,B) \<Longrightarrow> range(f) = {f ` x . x \<in> A}"
  using Pi_rangeD[of f A B] apply_rangeI[of f A B]
  by blast

lemma Pi_vimage_subset : "f \<in> Pi(A,B) \<Longrightarrow> f-``C \<subseteq> A"
  unfolding Pi_def by auto

definition
  minimum :: "i \<Rightarrow> i \<Rightarrow> i" where
  "minimum(r,B) \<equiv> THE b. first(b,B,r)"

lemma minimum_in: "\<lbrakk> well_ord(A,r); B\<subseteq>A; B\<noteq>0 \<rbrakk> \<Longrightarrow> minimum(r,B) \<in> B"
  using the_first_in unfolding minimum_def by simp

lemma well_ord_surj_imp_inj_inverse:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "(\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})) \<in> inj(B,A)"
proof -
  let ?f="\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})"
  have "minimum(r, {a \<in> A . h ` a = b}) \<in> {a\<in>A. h`a=b}" if "b\<in>B" for b
  proof -
    from \<open>h \<in> surj(A,B)\<close> that
    have "{a\<in>A. h`a=b} \<noteq> 0"
      unfolding surj_def by blast
    with \<open>well_ord(A,r)\<close>
    show "minimum(r,{a\<in>A. h`a=b}) \<in> {a\<in>A. h`a=b}"
      using minimum_in by blast
  qed
  moreover from this
  have "?f : B \<rightarrow> A"
    using lam_type[of B _ "\<lambda>_.A"] by simp
  moreover
  have "?f ` w = ?f ` x \<Longrightarrow> w = x" if "w\<in>B" "x\<in>B" for w x
  proof -
    from calculation that
    have "w = h ` minimum(r,{a\<in>A. h`a=w})"
      "x = h ` minimum(r,{a\<in>A. h`a=x})"
      by simp_all
    moreover
    assume "?f ` w = ?f ` x"
    moreover from this and that
    have "minimum(r, {a \<in> A . h ` a = w}) = minimum(r, {a \<in> A . h ` a = x})"
      unfolding minimum_def by simp_all
    moreover from calculation(1,2,4)
    show "w=x" by simp
  qed
  ultimately
  show ?thesis
    unfolding inj_def by blast
qed

lemma well_ord_surj_imp_lepoll:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "B\<lesssim>A"
  unfolding lepoll_def using well_ord_surj_imp_inj_inverse[OF assms]
  by blast

\<comment> \<open>New result\<close>
lemma surj_imp_well_ord:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "\<exists>s. well_ord(B,s)"
  using assms lepoll_well_ord[OF well_ord_surj_imp_lepoll]
  by force

lemma Pow_sing : "Pow({a}) = {0,{a}}"
proof(intro equalityI,simp_all)
  have "z \<in> {0,{a}}" if "z \<subseteq> {a}" for z
    using that by auto
  then
  show " Pow({a}) \<subseteq> {0, {a}}" by auto
qed

lemma Pow_cons:
  shows "Pow(cons(a,A)) = Pow(A) \<union> {{a} \<union> X . X: Pow(A)}"
  using Un_Pow_subset Pow_sing
proof(intro equalityI,auto simp add:Un_Pow_subset)
  {
    fix C D
    assume "\<And> B . B\<in>Pow(A) \<Longrightarrow> C \<noteq> {a} \<union> B" "C \<subseteq> {a} \<union> A" "D \<in> C"
    moreover from this
    have "\<forall>x\<in>C . x=a \<or> x\<in>A" by auto
    moreover from calculation
    consider (a) "D=a" | (b) "D\<in>A" by auto
    from this
    have "D\<in>A"
    proof(cases)
      case a
      with calculation show ?thesis by auto
    next
      case b
      then show ?thesis by simp
    qed
  }
  then show "\<And>x xa. (\<forall>xa\<in>Pow(A). x \<noteq> {a} \<union> xa) \<Longrightarrow> x \<subseteq> cons(a, A) \<Longrightarrow> xa \<in> x \<Longrightarrow> xa \<in> A"
    by auto
qed

lemma app_nm :
  assumes "n\<in>nat" "m\<in>nat" "f\<in>n\<rightarrow>m" "x \<in> nat"
  shows "f`x \<in> nat"
proof(cases "x\<in>n")
  case True
  then show ?thesis using assms in_n_in_nat apply_type by simp
next
  case False
  then show ?thesis using assms apply_0 domain_of_fun by simp
qed

lemma Upair_eq_cons: "Upair(a,b) = {a,b}"
  unfolding cons_def by auto

lemma converse_apply_eq : "converse(f) ` x = \<Union>(f -`` {x})"
  unfolding apply_def vimage_def by simp

lemmas app_fun = apply_iff[THEN iffD1]

lemma Finite_imp_lesspoll_nat:
  assumes "Finite(A)"
  shows "A \<prec> nat"
  using assms subset_imp_lepoll[OF naturals_subset_nat] eq_lepoll_trans
    n_lesspoll_nat eq_lesspoll_trans
  unfolding Finite_def lesspoll_def by auto

end