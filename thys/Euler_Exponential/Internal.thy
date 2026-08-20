(*  Title:  Internal.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Internal sets and functions\<close>

theory Internal
imports "HOL-Nonstandard_Analysis.NatStar" HyperInt AuxiliaryNSA
begin                                         

definition
  n_star :: "'a star \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "n_star x = (SOME y. x = star_n y)"

definition
  n_starset :: "'a star set \<Rightarrow> (nat \<Rightarrow> 'a set)" ("*ns* _" [80] 80) where
  "*ns* A = (SOME As. A = Iset (star_n As))"

definition
  n_starfun :: "('a star \<Rightarrow> 'b star) \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow> 'b))" ("*nf* _" [80] 80) where
  "*nf* F = (SOME Fs. F = Ifun (star_n Fs))"

definition
  starfun2_n :: "(nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)) \<Rightarrow> ('a star \<Rightarrow> 'b star \<Rightarrow> 'c star)" ("*fn2* _" [80] 80) where
  "*fn2* F = (\<lambda>x. Ifun (star_n F \<star> x))"

definition
  n_starfun2 :: "('a star \<Rightarrow> 'b star \<Rightarrow> 'c star) \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c))" ("*nf2* _" [80] 80) where
  "*nf2* F = (SOME Gs. F = (\<lambda>x. Ifun (star_n Gs \<star> x)))"

definition
  InternalFuns2 :: "('a star \<Rightarrow> 'b star \<Rightarrow> 'c star) set" where
  "InternalFuns2 = {X. \<exists>F. X = *fn2* F}"

lemma n_star_def2: "n_star x = (SOME y. y \<in> Rep_star x)"
  by (case_tac x, auto simp add: n_star_def star_n_eq_iff)

lemma star_n_star [simp]: 
   "star_n (n_star x) = x"
  by (metis (full_types) n_star_def someI_ex star_cases)

lemma n_star_star_n_eq_ultra:
   "eventually (\<lambda>n. n_star (star_n X) n = X n) \<U>"
using star_n_eq_iff by fastforce

lemma n_star_star_of_eq_ultra:
  "eventually  (\<lambda>n. n_star (star_of X) n = X)  \<U>"
  using  star_of_def star_n_eq_iff by fastforce 

lemma n_starset_def2: "*ns* S = (SOME Sn. S = *sn* Sn)"
  by (simp add: n_starset_def starset_n_def)

lemma Iset_n_starset_eq [simp]:
  assumes "X \<in> InternalSets" 
  shows "Iset (star_n (*ns* X)) = X"
proof -
  have "\<exists>As. X = *sn* As" using assms
    using InternalSets_def by blast 
  then have "Iset (star_n (SOME As. X = Iset (star_n As))) = X"
    by (metis (mono_tags) someI_ex starset_n_def)
  then show ?thesis
    by (simp add: n_starset_def) 
qed

lemma Iset_n_starset_empty [simp]:
  "Iset(star_n (*ns* {})) = {}"
by simp

lemma n_starset_eq_ultra:
  "eventually (\<lambda>n. (*ns* (Iset (star_n X))) n = X n) \<U>"
proof (simp add: n_starset_def)
  have "\<forall>\<^sub>F n in \<U>. (SOME As. Iset (star_n X) = Iset (star_n As)) n = X n"
  proof  (rule someI2_ex [of "\<lambda>x. Iset (star_n X) = Iset (star_n x)"])
    show "\<exists>a. Iset (star_n X) = Iset (star_n a)"
      by force
    next fix x assume "Iset (star_n X) = Iset (star_n x)"
    then show "\<forall>\<^sub>F n in \<U>. x n = X n"
      using Iset_eq_cancel by blast
  qed
  then show "\<forall>\<^sub>F n in \<U>. (SOME As. Iset (star_n X) = Iset (star_n As)) n = X n" .  
qed

lemma n_starset_starset_n_eq_ultra:
  "eventually (\<lambda>n. (*ns* *sn* X) n = X n) \<U>"
  by (simp add: starset_n_def n_starset_eq_ultra)

lemma n_starset_starset_n_eq_ultra2:
  "eventually (\<lambda>n. X n = (*ns* *sn* X) n) \<U>"
by (metis n_starset_starset_n_eq_ultra star_n_eq_iff)

lemma n_starset_empty_ultra: 
      "eventually (\<lambda>n. (*ns* {}) n = {}) \<U>"
proof -
  have "\<forall>\<^sub>F n in \<U>. (*ns* *sn* (\<lambda>n. {})) n = {}"
    using n_starset_starset_n_eq_ultra by blast
  then show ?thesis 
    using starset_n_empty by simp
qed

lemma P_n_starset_starset_n_ultra_iff:
   "eventually (\<lambda>n. P ((*ns* *sn* X) n)) \<U> = (eventually (\<lambda>n. P (X n)) \<U>)"
by (metis n_starset_starset_n_eq_ultra2 starP_star_n star_n_eq_iff)

lemma InternalSets_starset_n_starset [simp]:
  assumes "A \<in> InternalSets" 
  shows "*sn* (*ns* A) = A"
proof -
  have "\<exists>a. A = Iset (star_n a)"
    using Iset_n_starset_eq assms by blast
  moreover {fix x
  assume "A = Iset (star_n x)" 
  then have "*sn* x = A"
    by (simp add: starset_n_def)} 
  ultimately have "*sn* (SOME As. A = Iset (star_n As)) = A"
    by (rule someI2_ex, simp)
  then show ?thesis
    by (simp add: n_starset_def) 
qed

lemma starset_n_star_n:
  "(star_n X \<in> *sn* As) =  (eventually (\<lambda>n. (X n) \<in> (As n)) \<U>)"
by (metis Iset_star_n starset_n_def)

lemma n_starfun_def2: "*nf* F = (SOME Fn. F = *fn* Fn)"
  by (simp add:  n_starfun_def starfun_n_def)

lemma InternalFuns_starfun_n_starfun [simp]:
  assumes "F \<in> InternalFuns" 
  shows "*fn* (*nf* F) = F"
proof -
  have "\<exists>a. F = Ifun (star_n a)"
    using  assms 
    by (simp add: InternalFuns_def starfun_n_def) 
  moreover {fix x
  assume "F = Ifun (star_n x)" 
  then have "*fn* x = F"
    by (simp add: starfun_n_def)}
  ultimately have "*fn* (SOME Fs. F = Ifun (star_n Fs)) = F"
    by (rule someI2_ex, simp)
  then show ?thesis
    by (simp add: n_starfun_def)
qed

lemma Ifun_eq_cancel:
  "(Ifun (star_n F) = Ifun (star_n G)) = (eventually (\<lambda>n. F n = G n) \<U>)"
by (auto intro!: transfer_fun_eq [THEN meta_eq_to_obj_eq] 
     simp add: Ifun_star_n star_n_eq_iff)

lemma starfun_n_eq_cancel:
  "(*fn* F = *fn* G) = (eventually (\<lambda>n. F n = G n) \<U>)"
by (simp add: starfun_n_def Ifun_eq_cancel)

lemma n_starfun_starfun_n_eq_ultra:
  "eventually (\<lambda>n. (*nf* (*fn* F)) n = F n) \<U>"
using InternalFuns_def InternalFuns_starfun_n_starfun starfun_n_eq_cancel by auto

lemma n_starfun_starfun_eq_ultra:
  "eventually (\<lambda>n. (*nf* (*f* f)) n = f) \<U>"
by (simp add: starfun_starfun_n_eq n_starfun_starfun_n_eq_ultra)

lemma P_n_starfun_starfun_n_ultra_iff:
   "eventually (\<lambda>n. P ((*nf* *fn* X) n)) \<U> = (eventually (\<lambda>n. P (X n)) \<U>)"
by (metis n_starfun_starfun_n_eq_ultra starP_star_n starP_star_n star_n_eq_iff)

lemma starfun2_eq_starfun2n: "*f2* f = *fn2* (\<lambda>n. f)"
by (simp add: starfun2_n_def starfun2_def star_of_def)

lemma starfun2_n_Ifun_starfun_n: "*fn2* f = (\<lambda>x. Ifun ((*fn* f) x))"
by (simp add: starfun2_n_def starfun_n_def)

lemma starfun2_n_Ifun_starfun_n2: "( *fn2* f) x y = ((*fn* f) x) \<star> y"
by (simp add: starfun2_n_Ifun_starfun_n)

text\<open>The definition of binary internal functions is as expected\<close>
lemma starfun2_n: "(*fn2* f) (star_n X) (star_n Y) = star_n (\<lambda>n. f n (X n) (Y n))"
by (simp add: starfun2_n_def Ifun_star_n)

lemma n_starfun2_starfun2_n_eq_ultra:
  "eventually (\<lambda>n. (*nf2* (*fn2* F)) n = F n) \<U>"
proof -
  {
    fix x 
    assume "(\<lambda>y. Ifun (star_n F \<star> y)) = (\<lambda>xa. Ifun (star_n x \<star> xa))"
    then have "\<forall>X Xa. \<forall>\<^sub>F n in \<U>. F n (X n) (Xa n) = x n (X n) (Xa n)"
      by (auto simp add: fun_eq_iff all_star_eq Ifun_star_n star_n_eq_iff)
    then have "\<And>X. \<forall>\<^sub>F n in \<U>. \<forall>xb. F n (X n) xb = x n (X n) xb"
      using transfer_all [THEN meta_eq_to_obj_eq, THEN iffD1, where  p2="\<lambda>x. True"]
      by fastforce
    then have "\<forall>\<^sub>F n in \<U>. \<forall> xa xb. F n xa xb = x n xa xb"
      using transfer_all [THEN meta_eq_to_obj_eq, THEN iffD1, 
                          where P2="\<lambda>n xa. \<forall>xb. F n xa xb = x n xa xb" and p2="\<lambda>x. True"]
      by force
    moreover have "\<forall>\<^sub>F n in \<U>. (\<forall>xa xb. F n xa xb = x n xa xb) \<longrightarrow> F n = x n"
      by (simp add: ext)
    ultimately have "\<forall>\<^sub>F n in \<U>. F n = x n"
      using not_eventually_impI 
      by force
  }
  then have ev_fn2:  \<open>\<And>x. (\<lambda>y. Ifun (star_n F \<star> y)) = (\<lambda>xa. Ifun (star_n x \<star> xa)) \<Longrightarrow> \<forall>\<^sub>F n in \<U>. F n = x n\<close> .
  
  show ?thesis
    unfolding n_starfun2_def starfun2_n_def
    using someI2 [of "\<lambda>Gs. (\<lambda>x. Ifun (star_n F \<star> x)) = (\<lambda>x. Ifun (star_n Gs \<star> x))", 
                  OF _ ev_fn2, where x1="\<lambda>x. x"]
    eventually_mono 
    by fastforce
qed

lemma n_starfun2_starfun2_eq_ultra: "eventually (\<lambda>n. (*nf2* (*f2* f)) n = f) \<U>"
by (simp add: starfun2_eq_starfun2n n_starfun2_starfun2_n_eq_ultra)

lemma InternalFuns2_starfun2_n_starfun2 [simp]:
  assumes "f \<in> InternalFuns2" 
  shows "*fn2* (*nf2* f) = f"
proof -
  have "\<exists>a. f = (\<lambda>x. Ifun (star_n a \<star> x))"
    using  assms
    by (simp add: InternalFuns2_def starfun2_n_def) 
  moreover {fix x
  assume "f = (\<lambda>xa. Ifun (star_n x \<star> xa))" 
  then have "*fn2* x = f"
    by (simp add: starfun2_n_def)}
  ultimately have "*fn2* (SOME Gs. f = (\<lambda>x. Ifun (star_n Gs \<star> x))) = f"
    by (rule someI2_ex, simp)
  then show ?thesis
    by (simp add: n_starfun2_def)
qed

lemma transfer_fun2_eq [transfer_intro]:
  "\<lbrakk> \<And>X Y. f (star_n X) (star_n Y) = g (star_n X) (star_n Y)
    \<equiv> eventually (\<lambda>n. F n (X n) (Y n) = G n (X n) (Y n)) \<U> \<rbrakk>
      \<Longrightarrow> f = g \<equiv> eventually (\<lambda>n. F n = G n) \<U>"
by (simp only: fun_eq_iff transfer_all)

lemma starfun2_n_eq_cancel:
  "(*fn2* F = *fn2* G) = (eventually (\<lambda>n. F n = G n) \<U>)"
by (auto intro!: transfer_fun2_eq [THEN meta_eq_to_obj_eq] simp add: starfun2_n_def Ifun_star_n star_n_eq_iff)

lemma n_starfun_starfun2_n_eq_ultra:
  "\<forall>\<^sub>F n in \<U>. (*nf* (*fn2* f) (star_n X)) n = f n (X n)"
proof -
  have "Ifun (star_n f \<star> star_n X) = Ifun (star_n (\<lambda>n. f n (X n)))"
    by (simp add: Ifun_star_n)
  then show ?thesis
    by (metis n_starfun_starfun_n_eq_ultra starfun2_n_def starfun_n_def)
qed

lemma starfun2_n_minus: "- (*fn2* f) x y = (*fn2* (\<lambda>i j x. - (f i j) x)) x y"
proof (cases x)
  case (star_n X)
  assume x_star: "x = star_n X"
  then show ?thesis 
  proof (cases y)
    case (star_n Y)
    then show ?thesis 
      using x_star by (simp add: starfun2_n star_n_minus star_n_diff)
  qed
qed

lemma starfun2_n_diff:
     "(*fn2* f) y z - (*fn2* g) y z = (*fn2* (\<lambda>i j x. f i j x - g i j x)) y z"
proof (cases y)
  case (star_n Y)
  assume y_star: "y = star_n Y"
  then show ?thesis 
  proof(cases z)
    case (star_n Z)
    then show ?thesis 
      using y_star by (simp add: starfun2_n star_n_minus star_n_diff)
  qed
qed

lemma starfun2_n_inverse: "inverse ((*fn2* f) x y) = (*fn2* (\<lambda>i j x. inverse ((f i j) x))) x y"
proof (cases x)
  case (star_n X)
  assume x_star: "x = star_n X"
  then show ?thesis 
  proof (cases y)
    case (star_n Y)
    then show ?thesis 
      using x_star by (auto simp add: starfun2_n star_n_inverse)
  qed
qed

lemma starfun2_n_mult:
     "(*fn2* f) y z * (*fn2* g) y z = (*fn2* (\<lambda>i j x. f i j x * g i j x)) y z"
proof (cases y)
  case (star_n Y)
  assume y_star: "y = star_n Y"
  then show ?thesis 
  proof(cases z)
    case (star_n Z)
    then show ?thesis 
      using y_star by (simp add: starfun2_n star_n_mult)
  qed
qed

lemma starfun2_n_divide:
     "((*fn2* f) y z ::'a::division_ring star)/ (*fn2* g) y z = 
      (*fn2* (\<lambda>i j x. f i j x / g i j x)) y z"
  by (simp add: divide_inverse starfun2_n_mult starfun2_n_inverse)

lemma starfun_n_starfun2_omega: "(*fn* F) z = (*f2* F) whn z"
by (cases z, auto simp add:  starfun2_star_n starfun_n star_n_eq_iff hypnat_omega_def)

lemma InternalFuns2_divide:
  "\<lbrakk> f \<in> InternalFuns2; g \<in> InternalFuns2 \<rbrakk> 
       \<Longrightarrow> (\<lambda>m n. (f m n ::'a::division_ring star)/g m n) \<in> InternalFuns2"
  by (auto simp add: InternalFuns2_def starfun2_n_divide )

lemma InternalFuns2_mult:
  "\<lbrakk> f \<in> InternalFuns2; g \<in> InternalFuns2 \<rbrakk> \<Longrightarrow> (\<lambda>m n. f m n * g m n) \<in> InternalFuns2"
by (auto simp add: InternalFuns2_def starfun2_n_mult)

lemma InternalFuns2_diff:
  "\<lbrakk> f \<in> InternalFuns2; g \<in> InternalFuns2 \<rbrakk> \<Longrightarrow> (\<lambda>m n. f m n - g m n) \<in> InternalFuns2"
by (auto simp add: InternalFuns2_def starfun2_n_diff)

lemma InternalFuns2_minus:
  "f \<in> InternalFuns2  \<Longrightarrow> (\<lambda>m n. - f m n) \<in> InternalFuns2"
by (auto simp add: InternalFuns2_def starfun2_n_minus)

lemma InternalFuns_starfun2_n [simp]: "*fn2* f \<in> InternalFuns2"
  using InternalFuns2_def by auto                    

lemma ext_obj: "(\<forall>x y. f x y = g x y) \<Longrightarrow> f = g"
  using ext by blast

(* Clumsy proof *)
lemma InternalFuns2_const_fun: "(\<lambda>n m. c) \<in> InternalFuns2"
proof (cases c, simp add: InternalFuns2_def)
  case (star_n X)
    show "\<exists>F. (\<lambda>n m. star_n X) = *fn2* F"
    proof (rule exI [of _ "\<lambda>n m p. X n"])
      show "(\<lambda>n m. star_n X) = *fn2* (\<lambda>n m p. X n)"
      proof (rule ext)+
        fix n::"'f star" and m::"'g star"
        show "star_n X = (*fn2* (\<lambda>n m p. X n)) n m"
          by (force intro: star_cases [of n] star_cases [of m] 
              simp add: starfun2_n star_n_eq_iff)
      qed
    qed
qed

lemma InternalFuns2_InternalFuns_iff:
  "((\<lambda>m n. f m) \<in> InternalFuns2) = (f \<in> InternalFuns)"
proof (auto simp add: InternalFuns_def InternalFuns2_def)
  fix F :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  assume fn2F: "(\<lambda>m n. f m) = *fn2* F" 
  show "\<exists>F. f = *fn* F"
  proof (rule exI [of _ "\<lambda>m n. F m n p"], rule ext)
    {fix x 
    have "f x = (*fn* (\<lambda>m n. F m n p)) x"
    proof -
      have fx: "f x = (*fn2* F) x (star_of p)" 
        using fn2F by metis 
      then show ?thesis 
      proof (cases x)
        case (star_n X)
        then show ?thesis 
          using fx by (simp add: starfun_n starfun2_n star_n_eq_iff star_of_def)
      qed
    qed}
  then show "\<And>x. f x = (*fn* (\<lambda>m n. F m n p)) x" 
    by blast
qed
next
  fix F
  assume "f = *fn* F" 
  show "\<exists>Fa. (\<lambda>m n. (*fn* F) m) = *fn2* Fa"
  proof (rule exI [of _ "\<lambda>n j k. F n j"],  (rule ext)+)
    {fix m::"'a star" and n::"'e star"
    have "(*fn* F) m = (*fn2* (\<lambda>n j k. F n j)) m n"
    proof (cases m)
      case (star_n X)
      assume m: "m = star_n X"
      then show ?thesis
      proof (cases n)
        case (star_n Y)
        then show ?thesis by (auto simp add: m starfun_n starfun2_n)
      qed
    qed}
    then show "\<And>m n. (*fn* F) m = (*fn2* (\<lambda>n j k. F n j)) m n"
      by blast
  qed
qed         

lemma InternalSets_hnorm_InternalFuns_gt [simp]:
  assumes "X \<in> InternalFuns" 
  shows "{n. hnorm (X n) > m} \<in> InternalSets"
proof (cases m)
  case (star_n Y)
  assume m_star: "m = star_n Y"
  obtain A where internal_X: "X = *fn* A" using assms
    by (metis InternalFuns_starfun_n_starfun) 
  have "{n. star_n Y < hnorm ((*fn* A) n)} = 
             {x. (*p2* (\<in>)) x (star_n (\<lambda>m. {n. Y m < norm (A m n)}))}"
  proof (safe)
    fix x
    assume less_hnorm: "star_n Y < hnorm ((*fn* A) x)" 
    then show "(*p2* (\<in>)) x (star_n (\<lambda>m. {n. Y m < norm (A m n)}))"
    proof(cases x)
      case (star_n X)
      then show ?thesis using less_hnorm 
        by (simp add: starP2_star_n hnorm_def starfun_n starfun star_less_def)
    qed                   
  next
    fix x
    assume set_mem: "(*p2* (\<in>)) x (star_n (\<lambda>m. {n. Y m < norm (A m n)}))"
    then show "star_n Y < hnorm ((*fn* A) x)"
    proof (cases x)
      case (star_n X)
      then show ?thesis using set_mem 
        by (simp add: starP2_star_n hnorm_def starfun_n starfun star_less_def)
    qed  
  qed
  then show ?thesis 
    using InternalSets_def Iset_def internal_X star_n starset_n_def by fastforce
qed

lemma InternalSets_hnorm_starfun_gt [simp]:
      "\<And>m. {n. hnorm((*f* X) n) > m} \<in> InternalSets"
by (metis InternalFuns_starfun InternalSets_hnorm_InternalFuns_gt)

subsection\<open>Overspill theorem\<close>

text\<open>Theorem 3.3.18, Nonstandard Analysis, A. Robinson\<close>

lemma InternalFuns_ub:
  assumes "X \<in> InternalFuns" 
  and "\<forall>n\<in>\<nat>. hnorm(X n) \<le> m" 
  shows "\<exists>v\<in>HNatInfinite. \<forall>n<v. hnorm(X n) \<le> m"
proof (cases "\<forall>n. hnorm(X n) \<le> m")
  case True
  then show ?thesis
    using HNatInfinite_whn by blast 
next
  case False
  have "{n. m < hnorm (X n)} \<in> InternalSets"
    using InternalSets_hnorm_InternalFuns_gt assms(1) by blast
  then have "\<exists>n\<in>{n. m < hnorm (X n)}. \<forall>m\<in>{n. m < hnorm (X n)}. n \<le> m"
    by (metis False empty_iff leI mem_Collect_eq nonempty_InternalNatSet_has_least)
  then obtain na where na_prop: "m < hnorm (X na)" "\<forall>m\<in>{n. m < hnorm (X n)}. na \<le> m" by blast
  have "na \<in> HNatInfinite" 
  proof (rule ccontr)
    assume "na \<notin> HNatInfinite" 
    then have "na \<in> \<nat>"
      using HNatInfinite_not_Nats_iff by blast 
    then show False 
      using na_prop(1) assms(2) not_less by blast 
  qed
  moreover have "\<forall>n<na. hnorm (X n) \<le> m" 
  proof (safe)
    fix n
    assume n_l_na: "n < na" 
    show "hnorm (X n) \<le> m" 
    proof (rule ccontr)
      assume "\<not> hnorm (X n) \<le> m" 
      then have "m < hnorm (X n)" by simp
      then have "na \<le> n" using na_prop(2)
        by blast
      then show False using n_l_na by simp
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma starfun_least:
   "\<forall>n\<in>Nats. hnorm((*f* X) n) \<le> m \<Longrightarrow> \<exists>v\<in>HNatInfinite. \<forall>n<v. hnorm( (*f* X) n) \<le> m"
by (metis InternalFuns_ub InternalFuns_starfun)

subsection\<open>The Sequential Theorem\<close>

text\<open>Theorem 3.3.20, Nonstandard Analysis, A. Robinson\<close>

lemma InternalFuns_Sequential_Theorem: 
  assumes Int_f: "f \<in> InternalFuns"
  and f_approx_zero: "\<forall>n\<in>Nats. f n \<approx> (0:: 'a::{real_normed_div_algebra, semiring_1_cancel} star)"
  shows "\<exists>N\<in>HNatInfinite.\<forall>n<N. f n \<approx> 0"
proof -
  have "\<forall>n\<in>Nats. hnorm(of_hypnat n * f n) \<le> 1"
  proof 
    fix n 
    assume "(n :: nat star) \<in> \<nat>"
    then have "f n * of_hypnat n \<in> Infinitesimal" 
       using f_approx_zero Infinitesimal_HFinite_mult mem_infmal_iff
       by (metis HFinite_star_of Nats_hypnat_of_nat_iff of_hypnat_def starfun_star_of)
    then show "hnorm (of_hypnat n * f n) \<le> 1"
      by (metis Infinitesimal_hnorm_iff hnorm_le_Infinitesimal hnorm_mult 
          hnorm_one le_cases mult.commute one_not_Infinitesimal)
  qed
  then obtain v where Inf_v : "v\<in>HNatInfinite" and hnorm_le_1: "\<forall>n<v. hnorm (of_hypnat n * f n) \<le> 1"
    using Int_f  InternalFuns_ub [OF InternalFuns_mult_of_hypnat] by blast
  show ?thesis
  proof (rule bexI [of _ "v"])
    show "v \<in> HNatInfinite"
      by (simp add: Inf_v) 
  next
    {fix n 
    assume n_less_v: "n < v"
    then have "f n \<approx> 0"
    proof (cases "n \<in> Nats")
      case True
      then show ?thesis
        using f_approx_zero by blast 
    next
      case False
      then have "hypreal_of_hypnat n \<noteq> 0"
        by force 
      then have "hnorm (f n) \<le> 1 / hypreal_of_hypnat n"
        using hnorm_le_1 n_less_v 
        by (force simp add: zero_less_HNatInfinite le_divide_eq hnorm_mult mult.commute)
      then show ?thesis
        by (metis False HNatInfinite_inverse_Infinitesimal HNatInfinite_not_Nats_iff 
            hnorm_le_Infinitesimal inverse_eq_divide mem_infmal_iff)
    qed}
    then show "\<forall>n<v. f n \<approx> 0"
      by blast
  qed
qed

lemma InternalFuns_Sequential_Theorem2: 
  assumes "f \<in> InternalFuns" "g \<in> InternalFuns"
          "\<forall>n\<in>Nats. f n \<approx> (g n :: 'a::{real_normed_div_algebra, semiring_1_cancel} star)"
  shows "\<exists>N\<in>HNatInfinite.\<forall>n<N. f n \<approx> g n"
proof -
  have "(\<lambda>n. f n - g n) \<in> InternalFuns" 
    using assms(1,2) by (force simp add: InternalFuns_def starfun_n_diff)
  moreover have "\<forall>n\<in>\<nat>. f n - g n \<approx> 0"
    using approx_minus_iff assms(3) by blast
  ultimately show ?thesis using InternalFuns_Sequential_Theorem
    by (metis (no_types, lifting) approx_minus_iff)
qed

lemma Sequential_Theorem: 
      "\<forall>n\<in>Nats. (*f* f) n \<approx> (0:: 'a::{real_normed_div_algebra, semiring_1_cancel} star) 
       \<Longrightarrow> \<exists>N\<in>HNatInfinite.\<forall>n<N. (*f* f) n \<approx> 0"
by (metis InternalFuns_Sequential_Theorem InternalFuns_starfun)

lemma Sequential_Theorem2: 
  "\<forall>n\<in>Nats. (*f* f) n \<approx> ((*f* g) n :: 'a::{real_normed_div_algebra, semiring_1_cancel} star)
   \<Longrightarrow> \<exists>N\<in>HNatInfinite.\<forall>n<N. (*f* f) n \<approx> (*f* g) n"
by (metis InternalFuns_Sequential_Theorem2 InternalFuns_starfun)

lemma hyperpower_starfun_n: 
  "(x::'a::power star) pow n = ( *fn* (\<lambda>n m. (n_star x) n ^ m)) n"
  by (metis hyperpow star_n_star starfun_n)

lemma InternalFuns2_hyperpower [simp]: "(\<lambda>m. (pow) x) \<in> InternalFuns2"
proof(cases x, simp add: InternalFuns2_def)
  case (star_n X)
   show "\<exists>F. (\<lambda>m. (pow) (star_n X)) = *fn2* F"
   proof(rule exI [where x="(\<lambda>m n. (^) (X m))"],(rule ext)+)
    fix m::"'c star" and x 
     show "star_n X pow x = (*fn2* (\<lambda>m n. (^) (X m))) m x"
     proof(cases m, cases x)
       fix Xa Xaa
       assume nx: "m = star_n Xa" "x = star_n Xaa"
       then show ?thesis 
         by (auto simp add: hyperpow starfun2_n)
     qed
   qed
qed

(* This follows from the Sequential Theorem  -- 
   it should probably be moved but then the ST would need to move too *)
lemma hyperpow_approx_one_ex:
  assumes "x \<approx> 1" 
  shows "\<exists>N\<in>HNatInfinite.\<forall>n<N. x pow n \<approx> (1::'a::real_normed_div_algebra star)"
proof -
  have "\<forall>n\<in>\<nat>. x pow n \<approx> 1"
    by (metis Nats_hypnat_of_nat_iff assms hrealpow_approx_one hyperpow_hypnat_of_nat)
  then show ?thesis 
    using  InternalFuns_hyperpow 
    by (force intro!: InternalFuns_Sequential_Theorem2)
qed

end