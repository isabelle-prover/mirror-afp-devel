section\<open>Cohen forcing notions\<close>

theory Partial_Functions_Relative
  imports
    Cardinal_Library_Relative
begin

text\<open>In this theory we introduce bounded partial functions and its relative
version; for historical reasons the relative version is based on a proper
definition of partial functions.

We note that finite partial functions are easier and are used to prove
some lemmas about finite sets in the theory
\<^theory>\<open>Transitive_Models.ZF_Library_Relative\<close>.\<close>

definition
  Fn :: "[i,i,i] \<Rightarrow> i" where
  "Fn(\<kappa>,I,J) \<equiv> \<Union>{y . d \<in> Pow(I), y=(d\<rightarrow>J) \<and> d\<prec>\<kappa>}"

lemma domain_function_lepoll :
  assumes "function(r)"
  shows "domain(r) \<lesssim> r"
proof -
  let ?f="\<lambda>x\<in>domain(r) . \<langle>x,r`x\<rangle>"
  have "\<langle>x, r ` x\<rangle> \<in> r" if "\<langle>x, y\<rangle> \<in> r" for x y
  proof -
    have "x\<in>domain(r)" using that by auto
    with assms
    show ?thesis using function_apply_Pair by auto
  qed
  then
  have "?f \<in> inj(domain(r), r)"
    by(rule_tac lam_injective,auto)
  then
  show ?thesis unfolding lepoll_def
    by force
qed

lemma function_lepoll:
  assumes "r:d\<rightarrow>J"
  shows "r \<lesssim> d"
proof -
  let ?f="\<lambda>x\<in>r . fst(x)"
  note assms Pi_iff[THEN iffD1,OF assms]
  moreover from calculation
  have "r`fst(x) = snd(x)" if "x\<in>r" for x
    using that apply_equality
    by auto
  ultimately
  have "?f\<in>inj(r,d)"
    by(rule_tac d= "\<lambda>u . \<langle>u, r`u\<rangle>" in lam_injective,auto)
  then
  show ?thesis
    unfolding lepoll_def
    by auto
qed

lemma function_eqpoll :
  assumes "r:d\<rightarrow>J"
  shows "r \<approx> d"
  using assms domain_of_fun domain_function_lepoll Pi_iff[THEN iffD1,OF assms]
    eqpollI[OF function_lepoll[OF assms]] subset_imp_lepoll
  by force

lemma Fn_char : "Fn(\<kappa>,I,J) = {f \<in> Pow(I\<times>J) . function(f) \<and> f \<prec> \<kappa>}" (is "?L=?R")
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> ?R"
  moreover from this
  have "domain(x) \<in> Pow(I)" "domain(x) \<lesssim> x" "x\<prec> \<kappa>"
    using domain_function_lepoll
    by auto
  ultimately
  show "x \<in> ?L"
    unfolding Fn_def
    using lesspoll_trans1 Pi_iff
    by (auto,rule_tac rev_bexI[of "domain(x) \<rightarrow> J"],auto)
next
  fix x
  assume "x \<in> ?L"
  then
  obtain d where "x:d\<rightarrow>J" "d \<in> Pow(I)" "d\<prec>\<kappa>"
    unfolding Fn_def
    by auto
  moreover from this
  have "x\<prec>\<kappa>"
    using function_lepoll[THEN lesspoll_trans1] by auto
  moreover from calculation
  have "x \<in> Pow(I\<times>J)" "function(x)"
    using Pi_iff by auto
  ultimately
  show "x \<in> ?R" by simp
qed

lemma zero_in_Fn:
  assumes "0 < \<kappa>"
  shows "0 \<in> Fn(\<kappa>, I, J)"
  using lt_Card_imp_lesspoll assms zero_lesspoll
  unfolding Fn_def
  by (simp,rule_tac x="0\<rightarrow>J" in bexI,simp)
    (rule ReplaceI[of _ 0],simp_all)

lemma Fn_nat_eq_FiniteFun: "Fn(nat,I,J) = I -||> J"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> I -||> J"
  then
  show "x \<in> Fn(nat,I,J)"
  proof (induct)
    case emptyI
    then
    show ?case
      using zero_in_Fn ltI
      by simp
  next
    case (consI a b h)
    then
    obtain d where "h:d\<rightarrow>J" "d\<prec>nat" "d\<subseteq>I"
      unfolding Fn_def by auto
    moreover from this
    have "Finite(d)"
      using lesspoll_nat_is_Finite by simp
    ultimately
    have "h : d -||> J"
      using fun_FiniteFunI Finite_into_Fin by blast
    note \<open>h:d\<rightarrow>J\<close>
    moreover from this
    have "domain(cons(\<langle>a, b\<rangle>, h)) = cons(a,d)" (is "domain(?h) = ?d")
      and "domain(h) = d"
      using domain_of_fun by simp_all
    moreover
    note consI
    moreover from calculation
    have "cons(\<langle>a, b\<rangle>, h) \<in> cons(a,d) \<rightarrow> J"
      using fun_extend3 by simp
    moreover from \<open>Finite(d)\<close>
    have "Finite(cons(a,d))" by simp
    moreover from this
    have "cons(a,d) \<prec> nat" using Finite_imp_lesspoll_nat by simp
    ultimately
    show ?case
      unfolding Fn_def
      by (simp,rule_tac x="?d\<rightarrow>J" in bexI)
        (force dest:app_fun)+
  qed
next
  fix x
  assume "x \<in> Fn(nat,I,J)"
  then
  obtain d where "x:d\<rightarrow>J" "d \<in> Pow(I)" "d\<prec>nat"
    unfolding Fn_def
    by auto
  moreover from this
  have "Finite(d)"
    using lesspoll_nat_is_Finite by simp
  moreover from calculation
  have "d \<in> Fin(I)"
    using Finite_into_Fin[of d] Fin_mono by auto
  ultimately
  show "x \<in> I -||> J" using fun_FiniteFunI FiniteFun_mono by blast
qed

lemma Fn_nat_subset_Pow: "Fn(\<kappa>,I,J) \<subseteq> Pow(I\<times>J)"
  using Fn_char by auto

lemma FnI:
  assumes "p : d \<rightarrow> J" "d \<subseteq> I" "d \<prec> \<kappa>"
  shows "p \<in> Fn(\<kappa>,I,J)"
  using assms
  unfolding Fn_def by auto

lemma FnD[dest]:
  assumes "p \<in> Fn(\<kappa>,I,J)"
  shows "\<exists>d. p : d \<rightarrow> J \<and> d \<subseteq> I \<and> d \<prec> \<kappa>"
  using assms
  unfolding Fn_def by auto

lemma Fn_is_function: "p \<in> Fn(\<kappa>,I,J) \<Longrightarrow> function(p)"
  unfolding Fn_def using fun_is_function by auto

lemma Fn_csucc:
  assumes "Ord(\<kappa>)"
  shows "Fn(csucc(\<kappa>),I,J) = \<Union>{y . d \<in> Pow(I), y=(d\<rightarrow>J) \<and> d\<lesssim>\<kappa>}"
  using assms
  unfolding Fn_def using lesspoll_csucc by (simp)

definition
  FnleR :: "i \<Rightarrow> i \<Rightarrow> o" (infixl \<open>\<supseteq>\<close> 50) where
  "f \<supseteq> g \<equiv> g \<subseteq> f"

lemma FnleR_iff_subset [iff]: "f \<supseteq> g \<longleftrightarrow> g \<subseteq> f"
  unfolding FnleR_def ..

definition
  Fnlerel :: "i \<Rightarrow> i" where
  "Fnlerel(A) \<equiv> Rrel(\<lambda>x y. x \<supseteq> y,A)"

definition
  Fnle :: "[i,i,i] \<Rightarrow> i" where
  "Fnle(\<kappa>,I,J) \<equiv> Fnlerel(Fn(\<kappa>,I,J))"

lemma FnleI[intro]:
  assumes "p \<in> Fn(\<kappa>,I,J)" "q \<in> Fn(\<kappa>,I,J)" "p \<supseteq> q"
  shows "\<langle>p,q\<rangle> \<in> Fnle(\<kappa>,I,J)"
  using assms unfolding Fnlerel_def Fnle_def FnleR_def Rrel_def
  by auto

lemma FnleD[dest]:
  assumes "\<langle>p,q\<rangle> \<in> Fnle(\<kappa>,I,J)"
  shows "p \<in> Fn(\<kappa>,I,J)" "q \<in> Fn(\<kappa>,I,J)" "p \<supseteq> q"
  using assms unfolding Fnlerel_def Fnle_def FnleR_def Rrel_def
  by auto

definition PFun_Space_Rel :: "[i,i\<Rightarrow>o, i] \<Rightarrow> i"  ("_\<rightharpoonup>\<^bsup>_\<^esup>_")
  where "A \<rightharpoonup>\<^bsup>M\<^esup> B \<equiv> {f \<in> Pow(A\<times>B) . M(f) \<and> function(f)}"

lemma (in M_library) PFun_Space_subset_Powrel :
  assumes "M(A)" "M(B)"
  shows "A \<rightharpoonup>\<^bsup>M\<^esup> B = {f \<in> Pow\<^bsup>M\<^esup>(A\<times>B) . function(f)}"
  using Pow_rel_char assms
  unfolding PFun_Space_Rel_def
  by auto

lemma (in M_library) PFun_Space_closed :
  assumes "M(A)" "M(B)"
  shows "M(A \<rightharpoonup>\<^bsup>M\<^esup> B)"
  using assms PFun_Space_subset_Powrel separation_is_function
  by auto

lemma pfun_is_function :
  "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B \<Longrightarrow> function(f)"
  unfolding PFun_Space_Rel_def by simp

lemma pfun_range :
  "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B \<Longrightarrow> range(f) \<subseteq> B"
  unfolding PFun_Space_Rel_def by auto

lemma pfun_domain :
  "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B \<Longrightarrow> domain(f) \<subseteq> A"
  unfolding PFun_Space_Rel_def by auto

lemma Un_filter_fun_space_closed:
  assumes "G \<subseteq> I \<rightarrow> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightarrow> J . d \<supseteq> f \<and> d \<supseteq> g"
  shows "\<Union>G \<in> Pow(I\<times>J)" "function(\<Union>G)"
proof -
  from assms
  show "\<Union>G \<in> Pow(I\<times>J)"
    using Union_Pow_iff
    unfolding Pi_def
    by auto
next
  show "function(\<Union>G)"
    unfolding function_def
  proof(auto)
    fix B B' x y y'
    assume "B \<in> G" "\<langle>x, y\<rangle> \<in> B" "B' \<in> G" "\<langle>x, y'\<rangle> \<in> B'"
    moreover from assms this
    have "B \<in> I \<rightarrow> J" "B' \<in> I \<rightarrow> J"
      by auto
    moreover from calculation assms(2)[of B B']
    obtain d where "d \<supseteq> B"  "d \<supseteq> B'" "d\<in>I \<rightarrow> J"  "\<langle>x, y\<rangle> \<in> d" "\<langle>x, y'\<rangle> \<in> d"
      using subsetD[OF \<open>G\<subseteq>_\<close>]
      by auto
    then
    show "y=y'"
      using fun_is_function[OF \<open>d\<in>_\<close>]
      unfolding function_def
      by force
  qed
qed

lemma Un_filter_is_fun :
  assumes "G \<subseteq> I \<rightarrow> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightarrow> J . d\<supseteq>f \<and> d\<supseteq>g" "G\<noteq>0"
  shows "\<Union>G \<in> I \<rightarrow> J"
  using assms Un_filter_fun_space_closed Pi_iff
proof(simp_all)
  show "I\<subseteq>domain(\<Union>G)"
  proof -
    from \<open>G\<noteq>0\<close>
    obtain f where "f\<subseteq>\<Union>G" "f\<in>G"
      by auto
    with \<open>G\<subseteq>_\<close>
    have "f\<in>I\<rightarrow>J" by auto
    then
    show ?thesis
      using subset_trans[OF _ domain_mono[OF \<open>f\<subseteq>\<Union>G\<close>],of I]
      unfolding Pi_def by auto
  qed
qed

context M_Pi
begin

lemma mem_function_space_relD:
  assumes "f \<in> function_space_rel(M,A,y)" "M(A)" "M(y)"
  shows "f \<in> A \<rightarrow> y" and "M(f)"
  using assms function_space_rel_char by simp_all

lemma pfunI :
  assumes "C\<subseteq>A" "f \<in> C \<rightarrow>\<^bsup>M\<^esup> B" "M(C)" "M(B)"
  shows "f\<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
proof -
  from assms
  have "f \<in> C\<rightarrow>B" "M(f)"
    using mem_function_space_relD
    by simp_all
  with assms
  show ?thesis
    using Pi_iff
    unfolding PFun_Space_Rel_def
    by auto
qed

lemma zero_in_PFun_rel:
  assumes "M(I)" "M(J)"
  shows "0 \<in> I \<rightharpoonup>\<^bsup>M\<^esup> J"
  using pfunI[of 0] nonempty mem_function_space_rel_abs assms
  by simp

lemma pfun_subsetI :
  assumes "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B" "g\<subseteq>f" "M(g)"
  shows "g\<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms function_subset
  unfolding PFun_Space_Rel_def
  by auto

lemma pfun_Un_filter_closed:
  assumes "G \<subseteq>I\<rightharpoonup>\<^bsup>M\<^esup> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightharpoonup>\<^bsup>M\<^esup> J . d\<supseteq>f \<and> d\<supseteq>g"
  shows "\<Union>G \<in> Pow(I\<times>J)" "function(\<Union>G)"
proof -
  from assms
  show "\<Union>G \<in> Pow(I\<times>J)"
    using Union_Pow_iff
    unfolding PFun_Space_Rel_def
    by auto
next
  show "function(\<Union>G)"
    unfolding function_def
  proof(auto)
    fix B B' x y y'
    assume "B \<in> G" "\<langle>x, y\<rangle> \<in> B" "B' \<in> G" "\<langle>x, y'\<rangle> \<in> B'"
    moreover from calculation assms
    obtain d where "d \<in> I \<rightharpoonup>\<^bsup>M\<^esup> J" "function(d)" "\<langle>x, y\<rangle> \<in> d"  "\<langle>x, y'\<rangle> \<in> d"
      using pfun_is_function
      by force
    ultimately
    show "y=y'"
      unfolding function_def
      by auto
  qed
qed

lemma pfun_Un_filter_closed'':
  assumes "G \<subseteq>I\<rightharpoonup>\<^bsup>M\<^esup> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>G . d\<supseteq>f \<and> d\<supseteq>g"
  shows "\<Union>G \<in> Pow(I\<times>J)" "function(\<Union>G)"
proof -
  from assms
  have "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightharpoonup>\<^bsup>M\<^esup> J . d\<supseteq>f \<and> d\<supseteq>g"
    using subsetD[OF assms(1),THEN [2] bexI]
    by force
  then
  show "\<Union>G \<in> Pow(I\<times>J)"  "function(\<Union>G)"
    using assms pfun_Un_filter_closed
    unfolding PFun_Space_Rel_def
    by auto
qed

lemma pfun_Un_filter_closed':
  assumes "G \<subseteq>I\<rightharpoonup>\<^bsup>M\<^esup> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>G . d\<supseteq>f \<and> d\<supseteq>g" "M(G)"
  shows "\<Union>G \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
  using assms pfun_Un_filter_closed''
  unfolding PFun_Space_Rel_def
  by auto

lemma pfunD :
  assumes "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  shows "\<exists>C[M]. C\<subseteq>A \<and> f \<in> C\<rightarrow>B"
proof -
  note assms
  moreover from this
  have "f\<in>Pow(A\<times>B)" "function(f)" "M(f)"
    unfolding PFun_Space_Rel_def
    by simp_all
  moreover from this
  have "domain(f) \<subseteq> A" "f \<in> domain(f) \<rightarrow> B" "M(domain(f))"
    using assms Pow_iff[of f "A\<times>B"] domain_subset Pi_iff
    by auto
  ultimately
  show ?thesis by auto
qed

lemma pfunD_closed :
  assumes "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  shows "M(f)"
  using assms
  unfolding PFun_Space_Rel_def by simp

lemma pfun_singletonI :
  assumes "x \<in> A" "b \<in> B" "M(A)" "M(B)"
  shows "{\<langle>x,b\<rangle>} \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms transM[of x A] transM[of b B]
  unfolding PFun_Space_Rel_def function_def
  by auto

lemma pfun_unionI :
  assumes "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B" "g \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B" "domain(f)\<inter>domain(g)=0"
  shows "f\<union>g \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms
  unfolding PFun_Space_Rel_def function_def
  by blast

lemma (in M_library) pfun_restrict_eq_imp_compat:
  assumes "f \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J" "g \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J" "M(J)"
    "restrict(f, domain(f) \<inter> domain(g)) = restrict(g, domain(f) \<inter> domain(g))"
  shows "f \<union> g \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
proof -
  note assms
  moreover from this
  obtain C D where "f : C \<rightarrow> J" "C \<subseteq> I" "D \<subseteq> I" "M(C)" "M(D)" "g : D \<rightarrow> J"
    using pfunD[of f] pfunD[of g] by force
  moreover from calculation
  have "f\<union>g \<in> C\<union>D \<rightarrow> J"
    using restrict_eq_imp_Un_into_Pi'[OF \<open>f\<in>C\<rightarrow>_\<close> \<open>g\<in>D\<rightarrow>_\<close>]
    by auto
  ultimately
  show ?thesis
    using pfunI[of "C\<union>D" _ "f\<union>g"] Un_subset_iff pfunD_closed function_space_rel_char
    by auto
qed

lemma FiniteFun_pfunI :
  assumes "f \<in> A-||> B" "M(A)" "M(B)"
  shows "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms(1)
proof(induct)
  case emptyI
  then
  show ?case
    using assms nonempty mem_function_space_rel_abs pfunI[OF empty_subsetI, of 0]
    by simp
next
  case (consI a b h)
  note consI
  moreover from this
  have "M(a)" "M(b)" "M(h)" "domain(h) \<subseteq> A"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>]
      FinD
      FiniteFun_domain_Fin
      pfunD_closed
    by simp_all
  moreover from calculation
  have "{a}\<union>domain(h)\<subseteq>A" "M({a}\<union>domain(h))" "M(cons(<a,b>,h))" "domain(cons(<a,b>,h)) = {a}\<union>domain(h)"
    by auto
  moreover from calculation
  have "cons(<a,b>,h) \<in> {a}\<union>domain(h) \<rightarrow> B"
    using FiniteFun_is_fun[OF FiniteFun.consI, of a A b B h]
    by auto
  ultimately
  show "cons(<a,b>,h) \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
    using assms  mem_function_space_rel_abs pfunI
    by simp_all
qed

lemma PFun_FiniteFunI :
  assumes "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B" "Finite(f)"
  shows  "f \<in> A-||> B"
proof -
  from assms
  have "f\<in>Fin(A\<times>B)" "function(f)"
    using Finite_Fin Pow_iff
    unfolding PFun_Space_Rel_def
    by auto
  then
  show ?thesis
    using FiniteFunI by simp
qed

end \<comment> \<open>\<^locale>\<open>M_Pi\<close>\<close>

(* Fn_rel should be the relativization *)
definition
  Fn_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>Fn\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fn_rel(M,\<kappa>,I,J) \<equiv> {f \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J . f \<prec>\<^bsup>M\<^esup> \<kappa>}"

context  M_library
begin

lemma Fn_rel_subset_PFun_rel : "Fn\<^bsup>M\<^esup>(\<kappa>,I,J) \<subseteq> I\<rightharpoonup>\<^bsup>M\<^esup> J"
  unfolding Fn_rel_def by auto

lemma Fn_relI[intro]:
  assumes "f : d \<rightarrow> J" "d \<subseteq> I" "f \<prec>\<^bsup>M\<^esup> \<kappa>" "M(d)" "M(J)" "M(f)"
  shows "f \<in> Fn_rel(M,\<kappa>,I,J)"
  using assms pfunI mem_function_space_rel_abs
  unfolding Fn_rel_def
  by auto

lemma Fn_relD[dest]:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)"
  shows "\<exists>C[M]. C\<subseteq>I \<and> p : C \<rightarrow> J \<and> p \<prec>\<^bsup>M\<^esup> \<kappa>"
  using assms pfunD
  unfolding Fn_rel_def
  by simp

lemma Fn_rel_is_function:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)"
  shows "function(p)" "M(p)" "p \<prec>\<^bsup>M\<^esup> \<kappa>" "p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
  using assms
  unfolding Fn_rel_def PFun_Space_Rel_def by simp_all

lemma Fn_rel_mono:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)" "\<kappa> \<prec>\<^bsup>M\<^esup> \<kappa>'" "M(\<kappa>)" "M(\<kappa>')"
  shows "p \<in> Fn_rel(M,\<kappa>',I,J)"
  using assms lesspoll_rel_trans[OF _ assms(2)] cardinal_rel_closed
    Fn_rel_is_function(2)[OF assms(1)]
  unfolding Fn_rel_def
  by simp

lemma Fn_rel_mono':
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)" "\<kappa> \<lesssim>\<^bsup>M\<^esup> \<kappa>'" "M(\<kappa>)" "M(\<kappa>')"
  shows "p \<in> Fn_rel(M,\<kappa>',I,J)"
proof -
  note assms
  then
  consider "\<kappa> \<prec>\<^bsup>M\<^esup> \<kappa>'"  | "\<kappa> \<approx>\<^bsup>M\<^esup> \<kappa>'"
    using lepoll_rel_iff_leqpoll_rel
    by auto
  then
  show ?thesis
  proof(cases)
    case 1
    with assms show ?thesis using Fn_rel_mono by simp
  next
    case 2
    then show ?thesis
      using assms cardinal_rel_closed Fn_rel_is_function[OF assms(1)]
        lesspoll_rel_eq_trans
      unfolding Fn_rel_def
      by simp
  qed
qed

lemma Fn_csucc:
  assumes "Ord(\<kappa>)" "M(\<kappa>)"
  shows "Fn_rel(M,(\<kappa>\<^sup>+)\<^bsup>M\<^esup>,I,J) = {p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J . p  \<lesssim>\<^bsup>M\<^esup> \<kappa>}"   (is "?L=?R")
  using assms
proof(intro equalityI)
  show "?L \<subseteq> ?R"
  proof(intro subsetI)
    fix p
    assume "p\<in>?L"
    then
    have "p \<prec>\<^bsup>M\<^esup> csucc_rel(M,\<kappa>)" "M(p)" "p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
      using Fn_rel_is_function by simp_all
    then
    show "p\<in>?R"
      using  assms lesspoll_rel_csucc_rel by simp
  qed
next
  show "?R\<subseteq>?L"
  proof(intro subsetI)
    fix p
    assume "p\<in>?R"
    then
    have  "p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J" "p \<lesssim>\<^bsup>M\<^esup> \<kappa>"
      using assms lesspoll_rel_csucc_rel by simp_all
    then
    show "p\<in>?L"
      using  assms lesspoll_rel_csucc_rel pfunD_closed
      unfolding Fn_rel_def
      by simp
  qed
qed

lemma Finite_imp_lesspoll_nat:
  assumes "Finite(A)"
  shows "A \<prec> nat"
  using assms subset_imp_lepoll[OF naturals_subset_nat] eq_lepoll_trans
    n_lesspoll_nat eq_lesspoll_trans
  unfolding Finite_def lesspoll_def by auto

lemma FinD_Finite :
  assumes "a\<in>Fin(A)"
  shows "Finite(a)"
  using assms
  by(induct,simp_all)

lemma Fn_rel_nat_eq_FiniteFun:
  assumes "M(I)" "M(J)"
  shows "I -||> J = Fn_rel(M,\<omega>,I,J)"
proof(intro equalityI subsetI)
  fix p
  assume "p\<in>I -||> J"
  with assms
  have "p\<in> I \<rightharpoonup>\<^bsup>M\<^esup> J" "Finite(p)"
    using FiniteFun_pfunI FinD_Finite[OF subsetD[OF FiniteFun.dom_subset,OF \<open>p\<in>_\<close>]]
    by auto
  moreover from this
  have "p \<prec>\<^bsup>M\<^esup> \<omega>"
    using Finite_lesspoll_rel_nat pfunD_closed[of p] n_lesspoll_rel_nat
    by simp
  ultimately
  show "p\<in> Fn_rel(M,\<omega>,I,J)"
    unfolding Fn_rel_def by simp
next
  fix p
  assume "p\<in> Fn_rel(M,\<omega>,I,J)"
  then
  have "p\<in> I \<rightharpoonup>\<^bsup>M\<^esup> J"  "p \<prec>\<^bsup>M\<^esup> \<omega>"
    unfolding Fn_rel_def by simp_all
  moreover from this
  have "Finite(p)"
    using Finite_cardinal_rel_Finite lesspoll_rel_nat_is_Finite_rel pfunD_closed
      cardinal_rel_closed[of p]  Finite_cardinal_rel_iff'[THEN iffD1]
    by simp
  ultimately
  show "p\<in>I -||> J"
    using PFun_FiniteFunI
    by simp
qed

lemma Fn_nat_abs:
  assumes "M(I)" "M(J)"
  shows "Fn(nat,I,J) = Fn_rel(M,\<omega>,I,J)"
  using assms Fn_rel_nat_eq_FiniteFun Fn_nat_eq_FiniteFun
  by simp

lemma Fn_rel_singletonI:
  assumes "x \<in> I" "j \<in> J" "1 \<prec>\<^bsup>M\<^esup> \<kappa>" "M(\<kappa>)" "M(I)" "M(J)"
  shows "{\<langle>x,j\<rangle>} \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
  using pfun_singletonI transM[of x] transM[of j] assms
    eq_lesspoll_rel_trans[OF singleton_eqpoll_rel_1]
  unfolding Fn_rel_def
  by auto

end \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

definition
  Fnle_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>Fnle\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fnle_rel(M,\<kappa>,I,J) \<equiv> Fnlerel(Fn\<^bsup>M\<^esup>(\<kappa>,I,J))"

abbreviation
  Fn_r_set ::  "[i,i,i,i] \<Rightarrow> i" (\<open>Fn\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fn_r_set(M) \<equiv> Fn_rel(##M)"

abbreviation
  Fnle_r_set ::  "[i,i,i,i] \<Rightarrow> i" (\<open>Fnle\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fnle_r_set(M) \<equiv> Fnle_rel(##M)"


context M_library
begin

lemma Fnle_relI[intro]:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)" "q \<in> Fn_rel(M,\<kappa>,I,J)" "p \<supseteq> q"
  shows "\<langle>p, q\<rangle> \<in> Fnle_rel(M,\<kappa>,I,J)"
  using assms unfolding Fnlerel_def Fnle_rel_def FnleR_def Rrel_def
  by auto

lemma Fnle_relD[dest]:
  assumes "\<langle>p, q\<rangle> \<in> Fnle_rel(M,\<kappa>,I,J)"
  shows "p \<in> Fn_rel(M,\<kappa>,I,J)" "q \<in> Fn_rel(M,\<kappa>,I,J)" "p \<supseteq> q"
  using assms unfolding Fnlerel_def Fnle_rel_def FnleR_def Rrel_def
  by auto

lemma Fn_rel_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fn\<^bsup>M\<^esup>(\<kappa>,I,J))"
  using assms separation_cardinal_rel_lesspoll_rel PFun_Space_closed
  unfolding Fn_rel_def
  by auto

lemma Fn_rel_subset_Pow:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "Fn\<^bsup>M\<^esup>(\<kappa>,I,J) \<subseteq> Pow(I\<times>J)"
  unfolding Fn_rel_def PFun_Space_Rel_def
  by auto

lemma Fnle_rel_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fnle\<^bsup>M\<^esup>(\<kappa>,I,J))"
  unfolding Fnle_rel_def Fnlerel_def Rrel_def FnleR_def
  using assms supset_separation Fn_rel_closed
  by auto

lemma zero_in_Fn_rel:
  assumes "0<\<kappa>" "M(\<kappa>)" "M(I)" "M(J)"
  shows "0 \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)"
  unfolding Fn_rel_def
  using zero_in_PFun_rel zero_lesspoll_rel assms
  by simp

lemma zero_top_Fn_rel:
  assumes "p\<in>Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "0<\<kappa>" "M(\<kappa>)" "M(I)" "M(J)"
  shows "\<langle>p, 0\<rangle> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>, I, J)"
  using assms zero_in_Fn_rel unfolding preorder_on_def refl_def trans_on_def
  by auto

lemma preorder_on_Fnle_rel:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "preorder_on(Fn\<^bsup>M\<^esup>(\<kappa>, I, J), Fnle\<^bsup>M\<^esup>(\<kappa>, I, J))"
  unfolding preorder_on_def refl_def trans_on_def
  by blast

end  \<comment> \<open>\<^locale>\<open>M_library\<close>\<close>

context M_cardinal_library
begin

lemma lesspoll_nat_imp_lesspoll_rel:
  assumes "A \<prec> \<omega>" "M(A)"
  shows "A \<prec>\<^bsup>M\<^esup> \<omega>"
proof -
  note assms
  moreover from this
  obtain f n where "f\<in>bij\<^bsup>M\<^esup>(A,n)" "n\<in>\<omega>" "A \<approx>\<^bsup>M\<^esup> n"
    using lesspoll_nat_is_Finite Finite_rel_def[of M A]
    by auto
  moreover from calculation
  have "A \<lesssim>\<^bsup>M\<^esup> \<omega>"
    using lesspoll_nat_is_Finite Infinite_imp_nats_lepoll_rel[of \<omega> n]
      nat_not_Finite eq_lepoll_rel_trans[of A n \<omega>]
    by auto
  moreover from calculation
  have "\<not> g \<in> bij\<^bsup>M\<^esup>(A,\<omega>)" for g
    using mem_bij_rel unfolding lesspoll_def by auto
  ultimately
  show ?thesis
    unfolding lesspoll_rel_def
    by auto
qed

lemma Finite_imp_lesspoll_rel_nat:
  assumes "Finite(A)" "M(A)"
  shows "A \<prec>\<^bsup>M\<^esup> \<omega>"
  using Finite_imp_lesspoll_nat assms lesspoll_nat_imp_lesspoll_rel
  by auto

end \<comment> \<open>\<^locale>\<open>M_cardinal_library\<close>\<close>

context M_cardinal_library_extra
begin

lemma InfCard_rel_lesspoll_rel_Un:
  includes Ord_dests
  assumes "InfCard_rel(M,\<kappa>)" "A \<prec>\<^bsup>M\<^esup> \<kappa>" "B \<prec>\<^bsup>M\<^esup> \<kappa>"
    and types: "M(\<kappa>)" "M(A)" "M(B)"
  shows "A \<union> B \<prec>\<^bsup>M\<^esup> \<kappa>"
proof -
  from assms
  have "|A|\<^bsup>M\<^esup> < \<kappa>" "|B|\<^bsup>M\<^esup> < \<kappa>"
    using lesspoll_rel_cardinal_rel_lt InfCard_rel_is_Card_rel
    by auto
  show ?thesis
  proof (cases "Finite(A) \<and> Finite(B)")
    case True
    with assms
    show ?thesis
      using lesspoll_rel_trans2[OF _ le_imp_lepoll_rel, of _ nat \<kappa>]
        Finite_imp_lesspoll_rel_nat[OF Finite_Un]
      unfolding InfCard_rel_def
      by simp
  next
    case False
    with types
    have "InfCard_rel(M,max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>))"
      using Infinite_InfCard_rel_cardinal_rel InfCard_rel_is_Card_rel
        le_trans[of nat] not_le_iff_lt[THEN iffD1, THEN leI, of "|A|\<^bsup>M\<^esup>" "|B|\<^bsup>M\<^esup>"]
      unfolding max_def InfCard_rel_def
      by auto
    with \<open>M(A)\<close> \<open>M(B)\<close>
    have "|A \<union> B|\<^bsup>M\<^esup> \<le> max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>)"
      using cardinal_rel_Un_le[of "max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>)" A B]
        not_le_iff_lt[THEN iffD1, THEN leI, of "|A|\<^bsup>M\<^esup>" "|B|\<^bsup>M\<^esup>" ]
      unfolding max_def
      by simp
    moreover from \<open>|A|\<^bsup>M\<^esup> < \<kappa>\<close> \<open>|B|\<^bsup>M\<^esup> < \<kappa>\<close>
    have "max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>) < \<kappa>"
      unfolding max_def
      by simp
    ultimately
    have "|A \<union> B|\<^bsup>M\<^esup> <  \<kappa>"
      using lt_trans1
      by blast
    moreover
    note \<open>InfCard_rel(M,\<kappa>)\<close>
    moreover from calculation types
    have "|A \<union> B|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>"
      using lt_Card_rel_imp_lesspoll_rel InfCard_rel_is_Card_rel
      by simp
    ultimately
    show ?thesis
      using cardinal_rel_eqpoll_rel eq_lesspoll_rel_trans[of "A \<union> B" "|A \<union> B|\<^bsup>M\<^esup>" \<kappa>]
        eqpoll_rel_sym types
      by simp
  qed
qed

lemma Fn_rel_unionI:
  assumes "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "q\<in>Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
    "M(\<kappa>)" "M(I)" "M(J)" "domain(p) \<inter> domain(q) = 0"
  shows "p\<union>q \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
proof -
  note assms
  moreover from calculation
  have "p \<prec>\<^bsup>M\<^esup> \<kappa>" "q \<prec>\<^bsup>M\<^esup> \<kappa>" "M(p)" "M(q)"
    using Fn_rel_is_function by simp_all
  moreover from calculation
  have "p\<union>q \<prec>\<^bsup>M\<^esup> \<kappa>"
    using eqpoll_rel_sym cardinal_rel_eqpoll_rel InfCard_rel_lesspoll_rel_Un
    by simp_all
  ultimately
  show ?thesis
    unfolding Fn_rel_def
    using pfun_unionI cardinal_rel_eqpoll_rel eq_lesspoll_rel_trans[OF _ \<open>p\<union>q \<prec>\<^bsup>M\<^esup> _\<close>]
    by auto
qed

lemma restrict_eq_imp_compat_rel:
  assumes "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "q \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "InfCard\<^bsup>M\<^esup>(\<kappa>)" "M(J)" "M(\<kappa>)"
    "restrict(p, domain(p) \<inter> domain(q)) = restrict(q, domain(p) \<inter> domain(q))"
  shows "p \<union> q \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)"
proof -
  note assms
  moreover from calculation
  have "p \<prec>\<^bsup>M\<^esup> \<kappa>" "q \<prec>\<^bsup>M\<^esup> \<kappa>" "M(p)" "M(q)"
    using Fn_rel_is_function by simp_all
  moreover from calculation
  have "p\<union>q \<prec>\<^bsup>M\<^esup> \<kappa>"
    using InfCard_rel_lesspoll_rel_Un cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym]
    by auto
  ultimately
  show ?thesis
    unfolding Fn_rel_def
    using pfun_restrict_eq_imp_compat cardinal_rel_eqpoll_rel
      eq_lesspoll_rel_trans[OF _ \<open>p\<union>q \<prec>\<^bsup>M\<^esup> _\<close>]
    by auto
qed

lemma InfCard_rel_imp_n_lesspoll_rel :
  assumes "InfCard\<^bsup>M\<^esup>(\<kappa>)" "M(\<kappa>)" "n\<in>\<omega>"
  shows "n \<prec>\<^bsup>M\<^esup> \<kappa>"
proof -
  note assms
  moreover from this
  have "n \<prec>\<^bsup>M\<^esup> \<omega>"
    using n_lesspoll_rel_nat by simp
  ultimately
  show ?thesis
    using lesspoll_rel_trans2 Infinite_iff_lepoll_rel_nat InfCard_rel_imp_Infinite nat_into_M
    by simp
qed

lemma cons_in_Fn_rel:
  assumes "x \<notin> domain(p)" "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "x \<in> I" "j \<in> J" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
    "M(\<kappa>)" "M(I)" "M(J)"
  shows "cons(\<langle>x,j\<rangle>, p) \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
  using assms cons_eq Fn_rel_unionI[OF Fn_rel_singletonI[of x I j J] \<open>p\<in>_\<close>]
    InfCard_rel_imp_n_lesspoll_rel
  by auto

lemma dense_dom_dense:
  assumes "x \<in> I" "InfCard\<^bsup>M\<^esup>(\<kappa>)" "M(I)" "M(J)" "z\<in>J" "M(\<kappa>)" "p\<in>Fn\<^bsup>M\<^esup>(\<kappa>, I, J)"
  shows "\<exists>d\<in>{ p \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J) . x \<in> domain(p) }. \<langle>d,p\<rangle> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>, I, J)"
proof (cases "x \<in> domain(p)")
  case True
  with \<open>x \<in> I\<close> \<open>p \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)\<close>
  show ?thesis by auto
next
  case False
  note \<open>p \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)\<close>
  moreover from this and False and assms
  have "cons(\<langle>x,z\<rangle>, p) \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "M(x)"
    using cons_in_Fn_rel by (auto dest:transM)
  ultimately
  show ?thesis using Fn_relD by blast
qed

lemma (in M_cardinal_library) domain_lepoll_rel :
  assumes "function(r)" "M(r)"
  shows "domain(r) \<lesssim>\<^bsup>M\<^esup> r"
proof -
  let ?f="\<lambda>x\<in>domain(r) . \<langle>x,r`x\<rangle>"
  have "\<langle>x, r ` x\<rangle> \<in> r" if "\<langle>x, y\<rangle> \<in> r" for x y
  proof -
    have "x\<in>domain(r)" using that by auto
    with assms
    show ?thesis using function_apply_Pair by auto
  qed
  then
  have "?f \<in> inj(domain(r), r)"
    by(rule_tac lam_injective,auto)
  moreover note assms
  moreover from calculation
  have "M(?f)"
    using lam_replacement_constant[of r] lam_replacement_identity assms
      lam_replacement_apply lam_replacement_Pair[THEN [5] lam_replacement_hcomp2]
    by(rule_tac lam_replacement_imp_lam_closed,auto dest:transM[of _ r])
  ultimately
  have "?f \<in> inj\<^bsup>M\<^esup>(domain(r),r)" using inj_rel_char
    by auto
  with \<open>M(?f)\<close>
  show ?thesis
    using lepoll_relI by simp
qed

lemma dense_surj_dense:
  assumes "x \<in> J" "InfCard\<^bsup>M\<^esup>(\<kappa>)" "M(I)" "M(J)" "M(\<kappa>)" "p\<in>Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "\<kappa> \<lesssim>\<^bsup>M\<^esup> I"
  shows "\<exists>d\<in>{ p \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J) . x \<in> range(p) }. \<langle>d,p\<rangle> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>, I, J)"
proof -
  from \<open>p \<in> _\<close> \<open>M(J)\<close> \<open>x\<in>_\<close> lesspoll_rel_def
  have "domain(p) \<subseteq> I" "M(p)" "p \<prec>\<^bsup>M\<^esup> \<kappa>" "M(x)" "function(p)"
    using pfun_domain[OF Fn_rel_is_function(4)] Fn_rel_is_function transM[of x J]
    by simp_all
  moreover from calculation assms
  have 1:"domain(p) \<prec>\<^bsup>M\<^esup> \<kappa>" "M(domain(p))" "domain(p) \<prec>\<^bsup>M\<^esup> I"
    using domain_lepoll_rel lesspoll_rel_trans1[of "domain(p)" p \<kappa>] lesspoll_rel_trans2
    by auto
  with calculation \<open>\<kappa> \<lesssim>\<^bsup>M\<^esup> I\<close> \<open>M(I)\<close> \<open>M(\<kappa>)\<close>
  have "domain(p) \<noteq> I"
  proof -
    {assume "domain(p) = I"
      with 1
      have "domain(p) \<prec>\<^bsup>M\<^esup> domain(p)"
        by auto
      with \<open>M(domain(p))\<close>
      have False
        using lesspoll_rel_irrefl[of "domain(p)"] by simp
    }
    then show ?thesis by auto
  qed
  ultimately
  obtain \<alpha> where "\<alpha> \<notin> domain(p)" "\<alpha>\<in>I"
    by force
  moreover note assms
  moreover from calculation
  have "cons(\<langle>\<alpha>,x\<rangle>, p) \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)"
    using InfCard_rel_Aleph_rel cons_in_Fn_rel[of \<alpha> p \<kappa> I J x]
    by auto
  ultimately
  show ?thesis
    using Fnle_relI by blast
qed

end \<comment> \<open>\<^locale>\<open>M_cardinal_library_extra\<close>\<close>

end
