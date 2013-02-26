theory IteratedFixedPoint
imports Plain_HOLCF
begin


definition cfun_upd :: "('a::discrete_cpo \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'b \<rightarrow> ('a \<rightarrow> 'b)" where
 "cfun_upd = (\<Lambda> f a b x. if x=a then b else f\<cdot>x)"

abbreviation cfun_upd_syn :: "('a::discrete_cpo \<rightarrow> 'b) => 'a => 'b => ('a \<rightarrow> 'b)" where
 "cfun_upd_syn f a b == cfun_upd\<cdot>f\<cdot>a\<cdot>b"

nonterminal cupdbinds and cupdbind

syntax
  "_cupdbind" :: "['a, 'a] => cupdbind"               ("(2_ :\<cdot>=/ _)")
  ""         :: "cupdbind => cupdbinds"               ("_")
  "_cupdbinds":: "[cupdbind, cupdbinds] => cupdbinds" ("_,/ _")
  "_cUpdate"  :: "['a, cupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_cUpdate f (_cupdbinds b bs)" == "_cUpdate (_cUpdate f b) bs"
  "f(x:\<cdot>=y)" == "CONST cfun_upd_syn f x y"

lemma cfun_upd_apply[simp]: "(f(x :\<cdot>= v))\<cdot>y = (if y=x then v else f\<cdot>y)"
  unfolding cfun_upd_def by simp

(*
lemma cfun_upd_eqvt[eqvt]: "p \<bullet> (cfun_upd f (x::'a::{cont_pt,discrete_cpo}) y) = cfun_upd (p \<bullet> f) (p \<bullet> x) (p \<bullet> y)"
 by (auto simp add:permute_cfun_def cfun_eq_iff cfun_upd_def)
*)


lemma fun_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. fun_upd (f x) v (h x) :: 'a \<Rightarrow> 'b::cpo)"
proof (intro contI2  monofunI fun_belowI)
  fix x1 x2 :: 'c
  fix v'
  assume "x1 \<sqsubseteq> x2"
  thus "((f x1)(v := h x1)) v' \<sqsubseteq> ((f x2)(v := h x2)) v'"
    by (metis assms(1) assms(2) cont2monofunE fun_belowD fun_upd_apply)
next
  fix Y
  assume c1: "chain (Y :: nat \<Rightarrow> 'c)"
  assume c2: "chain (\<lambda>i. (f (Y i))(v := h (Y i)))"
  have "Y 0 \<sqsubseteq> Lub Y" by (metis is_ub_thelub[OF c1])
  hence "f (Y 0) \<sqsubseteq> f (Lub Y)" by (rule cont2monofunE[OF `cont f`])
  fix v'
  show "(((f (\<Squnion> i. Y i))(v := h (\<Squnion> i. Y i))) v') \<sqsubseteq> ((\<Squnion> i. (f (Y i))(v := h (Y i))) v') "
  proof(cases "v = v'")
    case True
    thus ?thesis
      using lub_fun[OF c2] cont2contlubE[OF `cont h` c1]
      by simp
  next
    case False
    thus ?thesis
      using lub_fun[OF c2] cont2contlubE[OF `cont f` c1]
            lub_fun[OF ch2ch_cont[OF `cont f` `chain Y`]]
      by simp
  qed
qed

lemma fun_upd_belowI:
  assumes "v \<sqsubseteq> g x"
  and "\<And> y. x \<noteq> y \<Longrightarrow> f y \<sqsubseteq> g y" 
  shows "f(x := v) \<sqsubseteq> g"
  using assms
  by (metis fun_belowI fun_upd_def)

lemma cfun_upd_belowI:
  assumes "v \<sqsubseteq> g\<cdot>x"
  and "\<And> y. x \<noteq> y \<Longrightarrow> f\<cdot>y \<sqsubseteq> g\<cdot>y" 
  shows "f(x :\<cdot>= v) \<sqsubseteq> g"
  using assms
  by -(rule cfun_belowI, simp)

lemma fun_upd2_belowI:
  assumes "v \<sqsubseteq> g x"
  assumes "v2 \<sqsubseteq> g y"
  and "\<And> z. z \<noteq> y \<Longrightarrow> z \<noteq> x \<Longrightarrow> f z \<sqsubseteq> g z"
  shows "f(x := v, y := v2) \<sqsubseteq> g"
  using assms
  by (metis fun_belowI fun_upd_def)

lemma cfun_upd2_belowI:
  assumes "v \<sqsubseteq> g\<cdot>x"
  assumes "v2 \<sqsubseteq> g\<cdot>y"
  and "\<And> z. z \<noteq> y \<Longrightarrow> z \<noteq> x \<Longrightarrow> f\<cdot>z \<sqsubseteq> g\<cdot>z"
  shows "f(x :\<cdot>= v, y :\<cdot>= v2) \<sqsubseteq> g"
  using assms
  by -(rule cfun_belowI, simp)

lemma
  fixes \<rho> :: "'a \<Rightarrow> 'b::pcpo"
   and e1 :: "('a \<Rightarrow> 'b) \<rightarrow> 'b"
   and e2 :: "('a \<Rightarrow> 'b) \<rightarrow> 'b"
   and x1 :: 'a and x2 :: 'a
  assumes ne:"x1 \<noteq> x2"
  shows "fix\<cdot>(\<Lambda> \<rho>'. \<rho> (x1 := e1\<cdot>\<rho>', x2 := e2\<cdot>\<rho>')) =
         fix\<cdot>(\<Lambda> \<rho>'. \<rho> (x1 := (fix\<cdot>(\<Lambda> \<rho>''. \<rho>' (x1 := e1\<cdot>\<rho>''))) x1, x2 := e2\<cdot>\<rho>'))" (is "fix_syn ?L = fix_syn ?R")
proof(rule below_antisym[OF fix_least_below fix_least_below])
  let ?H = "\<lambda> \<rho>' \<rho>''. \<rho>'(x1 := e1\<cdot>\<rho>'')"

  { fix y \<rho>
    assume "y \<noteq> x1"
    hence "fix_syn (?H \<rho>) y = \<rho> y"
    unfolding fix_def
    apply simp
    apply (subst lub_fun[OF chain_iterate])
    apply (subst lub_range_shift[symmetric, where j = 1, simplified, OF ch2ch_fun[OF chain_iterate]])
    apply simp
    done
  } note H_ignores_not_x1 = this
 

  { fix \<rho> \<rho>'
    assume "e1\<cdot>\<rho>' \<sqsubseteq> \<rho> x1"
    hence "?H \<rho> \<rho>' \<sqsubseteq> \<rho>"
      by (metis below_refl fun_upd_belowI)
  } note H_noop = this

  have [simp]: "cont ?R"
    apply (intro cont2cont)
    apply (rule cont2cont_fun) back
    apply (intro cont2cont)
    done

  note fix_eq_R = fix_eq[where F = "Abs_cfun ?R", unfolded beta_cfun[OF `cont ?R`]]

  have HR_is_R: "fix_syn (?H (fix_syn ?R)) = fix_syn ?R"
  proof
    case (goal1 x)
    show ?case
    proof(cases "x = x1")
    case True
      have "fix_syn (?H (fix_syn ?R)) x1 = fix_syn ?R x1"
        apply (subst (2) fix_eq_R)
        by (simp add: ne)
      with True
      show ?thesis by simp
    next
    case False
      thus ?thesis
        apply (subst fix_eq[where F = "Abs_cfun (?H (fix_syn ?R))"])
        by simp
    qed
  qed

  case goal2
  have "?R (fix_syn ?L) \<sqsubseteq> fix_syn ?L"
  proof(rule fun_upd2_belowI)  
    have "e1\<cdot>(fix_syn ?L) \<sqsubseteq> (fix_syn ?L) x1"
      by (subst fix_eq, simp add: ne)
    hence "?H (fix_syn ?L) (fix_syn ?L) \<sqsubseteq> (fix_syn ?L)"
      by (rule H_noop)
    hence "(fix_syn (?H (fix_syn ?L))) \<sqsubseteq> (fix_syn ?L)"
      by -(rule fix_least_below, simp)
    thus "(fix_syn (?H (fix_syn ?L))) x1 \<sqsubseteq> (fix_syn ?L) x1"
      by (rule fun_belowD)
    show "e2\<cdot>(fix_syn ?L) \<sqsubseteq> (fix_syn ?L) x2"
      by (subst (2) fix_eq, simp)
    case goal3 thus ?case
      by (subst fix_eq, simp)
  qed
  thus ?case by simp

  case goal1
  have "?L (fix_syn ?R) \<sqsubseteq> fix_syn ?R"
  proof(rule fun_upd2_belowI)
    have "e1\<cdot>(fix_syn ?R) \<sqsubseteq> e1\<cdot>(fix_syn (?H (fix_syn ?R)))"
      by (simp add: HR_is_R)
    hence "e1\<cdot>(fix_syn ?R) \<sqsubseteq> (fix_syn (?H (fix_syn ?R))) x1"
      apply (subst fix_eq[of "Abs_cfun (?H (fix_syn ?R))"])
      by simp
    thus "e1\<cdot>(fix_syn ?R) \<sqsubseteq> (fix_syn ?R) x1"
      apply (subst (3) fix_eq)
      by (simp add: ne)
    show "e2\<cdot>(fix_syn ?R) \<sqsubseteq> (fix_syn ?R) x2"
      apply (subst (3) fix_eq)
      by simp
    fix y
    assume "y \<noteq> x1" and "y \<noteq> x2"
    thus "\<rho> y \<sqsubseteq> (fix_syn ?R) y"
      by (subst fix_eq, simp)
  qed
  thus ?case by simp
qed

lemma
  fixes \<rho> :: "'a::discrete_cpo \<rightarrow> 'b::pcpo"
   and e1 :: "('a \<rightarrow> 'b) \<rightarrow> 'b"
   and e2 :: "('a \<rightarrow> 'b) \<rightarrow> 'b"
   and x1 :: 'a and x2 :: 'a
  assumes ne:"x1 \<noteq> x2"
  shows "fix\<cdot>(\<Lambda> \<rho>'. \<rho> (x1 :\<cdot>= e1\<cdot>\<rho>', x2 :\<cdot>= e2\<cdot>\<rho>')) =
         fix\<cdot>(\<Lambda> \<rho>'. \<rho> (x1 :\<cdot>= (fix\<cdot>(\<Lambda> \<rho>''. \<rho>'(x1 :\<cdot>= e1\<cdot>\<rho>'')))\<cdot>x1, x2 :\<cdot>= e2\<cdot>\<rho>'))" (is "fix_syn ?L = fix_syn ?R")
proof(rule below_antisym[OF fix_least_below fix_least_below])
  let ?H = "\<lambda> \<rho>' \<rho>''. \<rho>'(x1 :\<cdot>= e1\<cdot>\<rho>'')"

  { fix y \<rho>
    assume "y \<noteq> x1"
    hence "fix_syn (?H \<rho>)\<cdot>y = \<rho>\<cdot>y"
    unfolding fix_def
    apply simp
    apply (subst lub_cfun[OF chain_iterate])
    apply (subst lub_range_shift[symmetric, where j = 1, simplified, OF ch2ch_Rep_cfunL[OF chain_iterate]])
    apply simp
    done
  } note H_ignores_not_x1 = this

  { fix \<rho> \<rho>'
    assume "e1\<cdot>\<rho>' \<sqsubseteq> \<rho>\<cdot>x1"
    hence "?H \<rho> \<rho>' \<sqsubseteq> \<rho>"
      by (metis below_refl cfun_upd_belowI)
  } note H_noop = this

  note fix_eq_R = fix_eq[where F = "Abs_cfun ?R", simplified]

  have HR_is_R: "fix_syn (?H (fix_syn ?R)) = fix_syn ?R"
  proof(rule cfun_eqI)
    case (goal1 x)
    show ?case
    proof(cases "x = x1")
    case True
      have "fix_syn (?H (fix_syn ?R))\<cdot>x1 = fix_syn ?R\<cdot>x1"
        apply (subst (2) fix_eq_R)
        by (simp add: ne)
      with True
      show ?thesis by simp
    next
    case False
      thus ?thesis
        apply (subst fix_eq[where F = "Abs_cfun (?H (fix_syn ?R))"])
        by simp
    qed
  qed

  case goal2
  have "?R (fix_syn ?L) \<sqsubseteq> fix_syn ?L"
  proof(rule cfun_upd2_belowI)  
    have "e1\<cdot>(fix_syn ?L) \<sqsubseteq> (fix_syn ?L)\<cdot>x1"
      by (subst fix_eq, simp add: ne)
    hence "?H (fix_syn ?L) (fix_syn ?L) \<sqsubseteq> (fix_syn ?L)"
      by (rule H_noop)
    hence "(fix_syn (?H (fix_syn ?L))) \<sqsubseteq> (fix_syn ?L)"
      by -(rule fix_least_below, simp)
    thus "(fix_syn (?H (fix_syn ?L)))\<cdot>x1 \<sqsubseteq> (fix_syn ?L)\<cdot>x1"
      by (rule monofun_cfun_fun)
    show "e2\<cdot>(fix_syn ?L) \<sqsubseteq> (fix_syn ?L)\<cdot>x2"
      by (subst (2) fix_eq, simp)
    case goal3 thus ?case
      by (subst fix_eq, simp)
  qed
  thus ?case by simp

  case goal1
  have "?L (fix_syn ?R) \<sqsubseteq> fix_syn ?R"
  proof(rule cfun_upd2_belowI)
    have "e1\<cdot>(fix_syn ?R) \<sqsubseteq> e1\<cdot>(fix_syn (?H (fix_syn ?R)))"
      by (simp add: HR_is_R)
    hence "e1\<cdot>(fix_syn ?R) \<sqsubseteq> (fix_syn (?H (fix_syn ?R)))\<cdot>x1"
      apply (subst fix_eq[of "Abs_cfun (?H (fix_syn ?R))"])
      by simp
    thus "e1\<cdot>(fix_syn ?R) \<sqsubseteq> (fix_syn ?R)\<cdot>x1"
      apply (subst (3) fix_eq)
      by (simp add: ne)
    show "e2\<cdot>(fix_syn ?R) \<sqsubseteq> (fix_syn ?R)\<cdot>x2"
      apply (subst (3) fix_eq)
      by simp
    fix y
    assume "y \<noteq> x1" and "y \<noteq> x2"
    thus "\<rho>\<cdot>y \<sqsubseteq> (fix_syn ?R)\<cdot>y"
      by (subst fix_eq, simp)
  qed
  thus ?case by simp
qed

definition cfun_upd_on :: "('a::discrete_cpo \<rightarrow> 'b) \<rightarrow> 'a set discr \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)" where
 "cfun_upd_on = (\<Lambda> f S g x. if x \<in> undiscr S then g\<cdot>x else f\<cdot>x)"

abbreviation cfun_upd_on_syn :: "('a::discrete_cpo \<rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<rightarrow> 'b) \<Rightarrow> ('a \<rightarrow> 'b)" ("_ ++\<^bsub>_\<^esub> _" [60,60,60] 60)
  where "cfun_upd_on_syn f S g == cfun_upd_on\<cdot>f\<cdot>(Discr S)\<cdot>g"

lemma cfun_upd_on_apply[simp]: "(f ++\<^bsub>S\<^esub> g)\<cdot>x = (if x \<in> S then g\<cdot>x else f\<cdot>x)"
  unfolding cfun_upd_on_def by simp

lemma cfun_upd_on_belowI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> g\<cdot>x \<sqsubseteq> h\<cdot>x"
  assumes "\<And>x. x \<notin> S \<Longrightarrow> f\<cdot>x \<sqsubseteq> h\<cdot>x"
  shows "f ++\<^bsub>S\<^esub> g \<sqsubseteq> h"
  using assms
  by -(rule cfun_belowI, simp)

lemma
  fixes \<rho> :: "'a::discrete_cpo \<rightarrow> 'b::pcpo"
   and e1 :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b)"
   and e2 :: "('a \<rightarrow> 'b) \<rightarrow> 'b"
   and S :: "'a set" and x2 :: 'a
  assumes ne:"x2 \<notin> S"
  shows "fix\<cdot>(\<Lambda> \<rho>'. (\<rho> ++\<^bsub>S\<^esub> e1\<cdot>\<rho>')(x2 :\<cdot>= e2\<cdot>\<rho>')) =
         fix\<cdot>(\<Lambda> \<rho>'. (\<rho> ++\<^bsub>S\<^esub> (fix\<cdot>(\<Lambda> \<rho>''. \<rho>' ++\<^bsub>S\<^esub> e1\<cdot>\<rho>'')))(x2 :\<cdot>= e2\<cdot>\<rho>'))" (is "fix_syn ?L = fix_syn ?R")
proof(rule below_antisym[OF fix_least_below fix_least_below])
  let ?H = "\<lambda> \<rho>' \<rho>''. \<rho>' ++\<^bsub>S\<^esub> e1\<cdot>\<rho>''"

  { fix y \<rho>
    assume "y \<notin> S"
    hence "fix_syn (?H \<rho>)\<cdot>y = \<rho>\<cdot>y"
    unfolding fix_def
    apply simp
    apply (subst lub_cfun[OF chain_iterate])
    apply (subst lub_range_shift[symmetric, where j = 1, simplified, OF ch2ch_Rep_cfunL[OF chain_iterate]])
    apply simp
    done
  } note H_ignores_not_S = this

  { fix \<rho> \<rho>'
    assume "\<And> x. x \<in> S \<Longrightarrow> e1\<cdot>\<rho>'\<cdot>x \<sqsubseteq> \<rho>\<cdot>x"
    hence "?H \<rho> \<rho>' \<sqsubseteq> \<rho>"
      by (metis cfun_upd_on_belowI below_refl)
  } note H_noop = this

  note fix_eq_R = fix_eq[where F = "Abs_cfun ?R", simplified]
  note fix_eq_L = fix_eq[where F = "Abs_cfun ?L", simplified]
  note fix_eq_HR = fix_eq[where F = "Abs_cfun (?H (fix_syn ?R))", simplified]

  have HR_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> fix_syn (?H (fix_syn ?R))\<cdot>x = fix_syn ?R \<cdot> x"
     by (subst fix_eq_HR, simp)

  have HR_S[simp]: "\<And> x. x \<in> S \<Longrightarrow> fix_syn (?H (fix_syn ?R))\<cdot>x = e1\<cdot>(fix_syn (?H (fix_syn ?R)))\<cdot>x"
    apply (subgoal_tac "x \<noteq> x2")
    apply (subst fix_eq_HR)
    apply simp
    using ne by metis

  have L_S[simp]: "\<And> x. x \<in> S \<Longrightarrow> (fix_syn ?L)\<cdot>x = e1\<cdot>(fix_syn ?L)\<cdot>x"
    apply (subgoal_tac "x \<noteq> x2")
    apply (subst (1) fix_eq_L)
    apply simp
    using ne by metis

  have L_x2[simp]: "(fix_syn ?L)\<cdot>x2 = e2\<cdot>(fix_syn ?L)"
    by (subst (1) fix_eq_L, simp)

  have L_not_S_x2[simp]: "\<And> x. x \<notin> S \<Longrightarrow> x \<noteq> x2 \<Longrightarrow> (fix_syn ?L)\<cdot>x = \<rho>\<cdot>x"
    by (subst (1) fix_eq_L, simp)

  have R_S[simp]: "\<And> x. x \<in> S \<Longrightarrow> fix_syn ?R \<cdot> x = e1\<cdot>(fix_syn (?H (fix_syn ?R)))\<cdot>x"
    apply (subgoal_tac "x \<noteq> x2")
    apply (subst fix_eq_R)
    apply simp
    using ne by metis

  have R_x2[simp]: "fix_syn ?R \<cdot> x2 = e2\<cdot>(fix_syn ?R)"
    by (subst fix_eq_R, simp)

  have R_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> x \<noteq> x2 \<Longrightarrow> fix_syn ?R \<cdot> x = \<rho>\<cdot>x"
    by (subst fix_eq_R, simp)

  have HR_is_R[simp]: "fix_syn (?H (fix_syn ?R)) = fix_syn ?R"
    apply (rule cfun_eqI)
    apply (case_tac "x \<in> S")
    apply simp_all
    done

  have HLL_below_L: "?H (fix_syn ?L) (fix_syn ?L) \<sqsubseteq> (fix_syn ?L)"
    by (rule H_noop, simp)

  case goal2
  have "?R (fix_syn ?L) \<sqsubseteq> fix_syn ?L"
  proof(rule cfun_upd_belowI)
    show "e2\<cdot>(fix_syn ?L) \<sqsubseteq> (fix_syn ?L)\<cdot>x2"
      by simp
    fix x
    assume "x2 \<noteq> x"
    hence [simp]:"x \<noteq> x2" by metis
    show "(\<rho> ++\<^bsub>S\<^esub> (fix_syn (?H (fix_syn ?L))))\<cdot>x \<sqsubseteq> (fix_syn ?L)\<cdot>x"
    proof(cases "x \<in> S")
    case True[simp]
      from HLL_below_L
      have "(fix_syn (?H (fix_syn ?L))) \<sqsubseteq> (fix_syn ?L)"
        by -(rule fix_least_below, simp)
      hence "(fix_syn (?H (fix_syn ?L)))\<cdot>x \<sqsubseteq> (fix_syn ?L)\<cdot>x"
        by (rule monofun_cfun_fun)
      thus ?thesis
        by simp
    next
    case False
      thus ?thesis by simp
    qed
  qed
  thus ?case by simp

  case goal1
  have "?L (fix_syn ?R) \<sqsubseteq> fix_syn ?R"
    apply(rule cfun_upd_belowI)
    apply simp
    apply (case_tac "x \<notin> S")
    apply simp_all
    done
  thus ?case by simp
qed

end
