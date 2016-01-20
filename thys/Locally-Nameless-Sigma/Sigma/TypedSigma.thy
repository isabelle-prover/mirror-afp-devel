(*  Title:      Sigma/Typed_Sigma.thy
    Author:     Florian Kammuller and Henry Sudhof, 2006
*)

section {* First Order Types for Sigma terms *}

theory TypedSigma imports "../preliminary/Environments" Sigma begin

subsubsection {* Types and typing rules *}
text{* The inductive definition of the typing relation.*}

definition
  return :: "(type \<times> type) \<Rightarrow> type" where
  "return a = fst a"

definition
  param :: "(type \<times> type) \<Rightarrow> type" where
  "param a = snd a"

primrec
  do :: "type \<Rightarrow> (Label set)"  
where
 "do (Object l) = (dom l)"

primrec
  type_get :: "type \<Rightarrow> Label \<Rightarrow> (type \<times> type) option "  ("_^_" 1000)
where
 "(Object l)^n = (l n)"

  (* we need to restrict objects to ok environments, 
     as the empty object does not yield ok env otherwise *)
inductive 
  typing :: "(type environment) \<Rightarrow> sterm \<Rightarrow> type \<Rightarrow> bool"    
  ("_ \<turnstile> _ : _" [80, 0, 80] 230)
where 
  T_Var[intro!]:
    "\<lbrakk> ok env; x \<in> env_dom env; (the (env!x)) = T \<rbrakk> 
    \<Longrightarrow> env \<turnstile> (Fvar x) : T"
| T_Obj[intro!]:
    "\<lbrakk> ok env; dom b = do A;  finite F; 
       \<forall>l\<in>do A. \<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
        \<longrightarrow> env\<lparr>s:A\<rparr>\<lparr>p:param(the (A^l))\<rparr> 
            \<turnstile> (the (b l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the (A^l)) \<rbrakk> 
    \<Longrightarrow> env \<turnstile> (Obj b A) : A"
| T_Upd[intro!]:  
    "\<lbrakk> finite F; 
       \<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
        \<longrightarrow>  env\<lparr>s:A\<rparr>\<lparr>p:param(the (A^l))\<rparr>
             \<turnstile> (n\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the (A^l));
    env \<turnstile> a : A; l \<in> do A \<rbrakk> \<Longrightarrow> env \<turnstile> Upd a l n : A"
| T_Call[intro!]: 
    "\<lbrakk> env \<turnstile> a : A; env \<turnstile> b : param(the (A^l)); l \<in> do A \<rbrakk> 
    \<Longrightarrow> env \<turnstile> (Call a l b) : return(the (A^l))"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Obj b T : T"
  "e \<turnstile> Fvar x : T"
  "e \<turnstile> Call a l b : T"
  "e \<turnstile> Upd a l n : T"

subsubsection {*Basic lemmas *}
text{*Basic treats of the type system.*}
lemma not_bvar: "e \<turnstile> t : T \<Longrightarrow> \<forall>i. t \<noteq> Bvar i"
  by (erule typing.cases, simp_all)

lemma typing_regular': "e \<turnstile> t : T \<Longrightarrow> ok e" 
  by (induct rule:typing.induct, auto)

lemma typing_regular'': "e \<turnstile> t : T \<Longrightarrow> lc t" 
  by (induct rule:typing.induct, auto)

theorem typing_regular: "e \<turnstile> t : T \<Longrightarrow> ok e \<and> lc t" 
  by (simp add: typing_regular' typing_regular'')

lemma obj_inv: "e \<turnstile> Obj f U : A \<Longrightarrow> A = U"
  by (erule typing.cases, auto)

lemma obj_inv_elim: 
  "e \<turnstile> Obj f U : U 
  \<Longrightarrow> (dom f = do U) 
    \<and> (\<exists>F. finite F \<and> (\<forall>l\<in>do U. \<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
        \<longrightarrow> e\<lparr>s:U\<rparr>\<lparr>p:param(the U^l)\<rparr>
            \<turnstile> (the (f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the (U^l))))"
  by (erule typing.cases, simp_all, blast)

lemma typing_induct[consumes 1, case_names Fvar Call Upd Obj Bnd]:
  fixes 
  env :: "type environment" and t :: sterm and T :: type and 
  P1 :: "type environment \<Rightarrow> sterm \<Rightarrow> type \<Rightarrow> bool" and
  P2 :: "type environment \<Rightarrow> sterm \<Rightarrow> type \<Rightarrow> Label \<Rightarrow> bool"
  assumes
  "env \<turnstile> t : T" and
  "\<And>env T x. \<lbrakk> ok env; x \<in> env_dom env; the env!x = T \<rbrakk>
  \<Longrightarrow> P1 env (Fvar x) T" and
  "\<And>env T t l p. \<lbrakk> env \<turnstile> t : T; P1 env t T; env \<turnstile> p : param (the(T^l));
                    P1 env p (param (the(T^l))); l \<in> do T \<rbrakk>
  \<Longrightarrow> P1 env (Call t l p) (return (the(T^l)))" and
  "\<And>env T t l u. \<lbrakk> env \<turnstile> t : T; P1 env t T; l \<in> do T; P2 env u T l \<rbrakk>
  \<Longrightarrow> P1 env (Upd t l u) T" and
  "\<And>env T f. \<lbrakk> ok env; dom f = do T; \<forall>l\<in>dom f. P2 env (the(f l)) T l \<rbrakk>
  \<Longrightarrow> P1 env (Obj f T) T" and
  "\<And>env T l t L. \<lbrakk> ok env; finite L; 
                  \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                   \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param (the(T^l))\<rparr> 
                       \<turnstile> (t\<^bsup>[Fvar s, Fvar p]\<^esup>) : return (the(T^l))
                      \<and> P1 (env\<lparr>s:T\<rparr>\<lparr>p:param (the(T^l))\<rparr>) (t\<^bsup>[Fvar s, Fvar p]\<^esup>) 
                           (return (the(T^l))) \<rbrakk>
  \<Longrightarrow> P2 env t T l"
  shows
  "P1 env t T"
  using assms by (induct rule: typing.induct, auto simp: typing_regular')

(* TODO: delete after refactoring of disjunct_env *)
lemma ball_Tltsp:
  fixes 
  P1 :: "type \<Rightarrow> Label \<Rightarrow> sterm \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" and 
  P2 :: "type \<Rightarrow> Label \<Rightarrow> sterm \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
  assumes 
  "\<And>l t t'. \<lbrakk> \<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p \<longrightarrow> P1 T l t s p \<rbrakk> 
  \<Longrightarrow> \<forall>s p. s \<notin> F' \<and> p \<notin> F' \<and> s \<noteq> p \<longrightarrow> P2 T l t s p" and
  "\<forall>l\<in>do T. \<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p \<longrightarrow> P1 T l (the(f l)) s p"
  shows "\<forall>l\<in>do T. \<forall>s p. s \<notin> F' \<and> p \<notin> F' \<and> s \<noteq> p \<longrightarrow> P2 T l (the(f l)) s p"
proof
  fix l assume "l \<in> do T"
  with assms(2) 
  have "\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p \<longrightarrow> P1 T l (the(f l)) s p"
    by simp
  with assms(1) 
  show "\<forall>s p. s \<notin> F' \<and> p \<notin> F' \<and> s \<noteq> p \<longrightarrow> P2 T l (the(f l)) s p"
    by simp
qed

(* TODO: delete after refactoring of subject_reduction *)
lemma ball_ex_finite:
  fixes 
  S :: "'a set" and F :: "'b set" and x :: 'a and 
  P :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes 
  "finite S" and "finite F" and
  "\<forall>x\<in>S. (\<exists>F'. finite F'
              \<and> (\<forall>s p. s \<notin> F' \<union> F \<and> p \<notin> F' \<union> F \<and> s \<noteq> p
                  \<longrightarrow> P x s p))"
  shows 
  "\<exists>F'. finite F'
      \<and> (\<forall>x\<in>S. \<forall>s p. s \<notin> F' \<union> F \<and> p \<notin> F' \<union> F \<and> s \<noteq> p
                 \<longrightarrow> P x s p)"
proof -
  from assms show ?thesis 
  proof (induct S)
    case empty thus ?case by force
  next
    case (insert x S)
    from insert(5)
    have 
      "\<forall>y\<in>S. (\<exists>F'. finite F' 
                  \<and> (\<forall>s p. s \<notin> F' \<union> F \<and> p \<notin> F' \<union> F \<and> s \<noteq> p
                      \<longrightarrow> P y s p))"
      by simp
    from insert(3)[OF `finite F` this]
    obtain F1 where 
      "finite F1" and
      pred_S: "\<forall>y\<in>S. \<forall>s p. s \<notin> F1 \<union> F \<and> p \<notin> F1 \<union> F \<and> s \<noteq> p
                       \<longrightarrow> P y s p"
      by auto
    from insert(5)
    obtain F2 where 
      "finite F2" and
      "\<forall>s p. s \<notin> F2 \<union> F \<and> p \<notin> F2 \<union> F \<and> s \<noteq> p \<longrightarrow> P x s p"
      by auto
    with pred_S have 
      "\<forall>y\<in>insert x S. \<forall>s p. s \<notin> F1 \<union> F2 \<union> F \<and> p \<notin> F1 \<union> F2 \<union> F \<and> s \<noteq> p
                        \<longrightarrow> P y s p"
      by auto
    moreover
    from `finite F1` `finite F2` have "finite (F1 \<union> F2)" by simp
    ultimately
    show ?case by blast
  qed
qed

(* TODO: delete after refactoring of type_renaming' *)
lemma bnd_renaming_lem:
  assumes 
  "s \<notin> FV t'" and "p \<notin> FV t'" and "x \<notin> FV t'" and "y \<notin> FV t'" and
  "x \<notin> env_dom env'" and "y \<notin> env_dom env'" and "s \<noteq> p" and "x \<noteq> y" and
  "t = {Suc n \<rightarrow> [Fvar s, Fvar p]} t'" and "env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>" and
  pred_bnd:
  "\<forall>sa pa. sa \<notin> F \<and> pa \<notin> F \<and> sa \<noteq> pa 
    \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> \<turnstile> (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))
        \<and> (\<forall>env'' t'' s' p' x' y' A' B' n'. 
            s' \<notin> FV t'' \<longrightarrow> p' \<notin> FV t'' \<longrightarrow> x' \<notin> FV t'' \<longrightarrow> y' \<notin> FV t'' \<longrightarrow> 
            x' \<notin> env_dom env'' \<longrightarrow> y' \<notin> env_dom env'' \<longrightarrow> x' \<noteq> y' \<longrightarrow> s' \<noteq> p' 
            \<longrightarrow> (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) = {n' \<rightarrow> [Fvar s',Fvar p']} t'' 
            \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> = env''\<lparr>s':A'\<rparr>\<lparr>p':B'\<rparr> 
            \<longrightarrow> env''\<lparr>x':A'\<rparr>\<lparr>y':B'\<rparr> 
                \<turnstile> {n' \<rightarrow> [Fvar x',Fvar y']} t'' : return(the(T^l)))" and
  "FV t' \<subseteq> F'"
  shows
  "\<forall>sa pa. sa \<notin> F \<union> {s,p,x,y} \<union> F' \<union> env_dom env' 
         \<and> pa \<notin> F \<union> {s,p,x,y} \<union> F' \<union> env_dom env' 
         \<and> sa \<noteq> pa
    \<longrightarrow> env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
        \<turnstile> ({Suc n \<rightarrow> [Fvar x, Fvar y]} t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return (the(T^l))"
proof (intro strip, elim conjE)
  fix sa pa 
  assume 
    nin_sa: "sa \<notin> F \<union> {s,p,x,y} \<union> F' \<union> env_dom env'" and
    nin_pa: "pa \<notin> F \<union> {s,p,x,y} \<union> F' \<union> env_dom env'" and "sa \<noteq> pa"
  hence "sa \<notin> F \<and> pa \<notin> F \<and> sa \<noteq> pa" by auto
  moreover
  {
    fix a assume "a \<notin> FV t'" and "a \<in> {s,p,x,y}"
    with 
      `FV t' \<subseteq> F'` nin_sa nin_pa `sa \<noteq> pa` 
      sopen_FV[of 0 "Fvar sa" "Fvar pa" t']
    have "a \<notin> FV (t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>)" by (auto simp: openz_def)
  } note 
      this[OF `s \<notin> FV t'`] this[OF `p \<notin> FV t'`] 
      this[OF `x \<notin> FV t'`] this[OF `y \<notin> FV t'`]
  moreover
  from 
    not_in_env_bigger_2[OF `x \<notin> env_dom env'`] 
    not_in_env_bigger_2[OF `y \<notin> env_dom env'`]
    nin_sa nin_pa
  have 
    "x \<notin> env_dom (env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>) 
    \<and> y \<notin> env_dom (env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>)" by auto
  moreover
  from `t = {Suc n \<rightarrow> [Fvar s, Fvar p]} t'` sopen_commute[OF Suc_not_Zero] 
  have "(t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) = {Suc n \<rightarrow> [Fvar s,Fvar p]} (t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>)"
    by (auto simp: openz_def)
  moreover
  from 
    subst_add[of s sa env' A T] subst_add[of sa p "env'\<lparr>s:A\<rparr>" T B] 
    subst_add[of s pa "env'\<lparr>sa:T\<rparr>" A "param(the(T^l))"]
    subst_add[of p pa "env'\<lparr>sa:T\<rparr>\<lparr>s:A\<rparr>" B "param(the(T^l))"]
    `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` nin_sa nin_pa
  have "env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> = env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>"
    by auto
  ultimately
  have 
    "env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the T^l)\<rparr>\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>
     \<turnstile> {Suc n \<rightarrow> [Fvar x, Fvar y]} (t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))"
    using `s \<noteq> p` `x \<noteq> y` pred_bnd by auto
  moreover
  from 
    subst_add[of y sa "env'\<lparr>x:A\<rparr>" B T] subst_add[of x sa env' A T] 
    subst_add[of y pa "env'\<lparr>sa:T\<rparr>\<lparr>x:A\<rparr>" B "param(the(T^l))"]
    subst_add[of x pa "env'\<lparr>sa:T\<rparr>" A "param(the(T^l))"] 
    nin_sa nin_pa
  have 
    "env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
     = env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>"
    by auto
  ultimately 
  show 
    "env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
     \<turnstile> ({Suc n \<rightarrow> [Fvar x, Fvar y]} t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return (the(T^l))"
    using sopen_commute[OF not_sym[OF Suc_not_Zero]]
    by (simp add: openz_def)
qed

(* TODO: refactor to work with typing_induct *)
lemma type_renaming'[rule_format]:
  "e \<turnstile> t : C \<Longrightarrow>
  (\<And>env t' s p x y A B n. \<lbrakk> s \<notin> FV t'; p \<notin> FV t'; x \<notin> FV t'; y \<notin> FV t'; 
                             x \<notin> env_dom env; y \<notin> env_dom env; s \<noteq> p;  x \<noteq> y;
                             t = {n \<rightarrow> [Fvar s,Fvar p]} t'; e = env\<lparr>s:A\<rparr>\<lparr>p:B\<rparr> \<rbrakk>
    \<Longrightarrow> env\<lparr>x:A\<rparr>\<lparr>y:B\<rparr> \<turnstile> {n \<rightarrow> [Fvar x,Fvar y]} t' : C)"
proof (induct set:typing)
  case (T_Call env t1 T t2 l env' t' s p x y A B n)
  with sopen_eq_Call[OF sym[OF `Call t1 l t2 = {n \<rightarrow> [Fvar s,Fvar p]} t'`]]
  show ?case by auto
next
  case (T_Var env a T env' t' s p x y A B n)
  from `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` ok_add_2[of env' s A p B] 
  have "ok env'" by simp
  from 
    ok_add_ok[OF ok_add_ok[OF this `x \<notin> env_dom env'`]
                 not_in_env_bigger[OF `y \<notin> env_dom env'` not_sym[OF `x \<noteq> y`]]]
  have ok: "ok (env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>)" by assumption

  from sopen_eq_Fvar[OF sym[OF `Fvar a = {n \<rightarrow> [Fvar s,Fvar p]} t'`]] 
  show ?case
  proof (elim disjE conjE)
    assume "t' = Fvar a" with T_Var(4-7)
    obtain "a \<noteq> s" and "a \<noteq> p" and "a \<noteq> x" and "a \<noteq> y" by auto
    note in_env_smaller2[OF _ this(1-2)]
    from `a \<in> env_dom env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` this[of env' A B]
    have "a \<in> env_dom env'" by simp
    from env_bigger2[OF `x \<notin> env_dom env'` `y \<notin> env_dom env'` this `x \<noteq> y`]
    have inenv: "a \<in> env_dom (env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>)" by assumption
    note get_env_bigger2[OF _ `a \<noteq> s` `a \<noteq> p`]
    from 
      this[of env' A B] `a \<in> env_dom env` `the env!a = T` 
      `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` get_env_bigger2[OF inenv `a \<noteq> x` `a \<noteq> y`] 
    have "the (env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>!a) = T" by simp
    from typing.T_Var[OF ok inenv this] `t' = Fvar a` show ?case by simp
  next
    assume "a = s" and "t' = Bvar (Self n)"
    from 
      this(1) `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` `the env!a = T` 
      add_get2_1[of env' s A p B]
    have "T = A" by simp
    moreover
    from `t' = Bvar (Self n)` have "{n \<rightarrow> [Fvar x,Fvar y]} t' = Fvar x" by simp
    ultimately
    show ?case using in_add_2[OF ok] typing.T_Var[OF ok _ add_get2_1[OF ok]]
      by simp
  next
    note subst = subst_add[OF `x \<noteq> y`] 
    from subst[of env' A B] ok have ok': "ok (env'\<lparr>y:B\<rparr>\<lparr>x:A\<rparr>)" by simp
    assume "a = p" and "t' = Bvar (Param n)"
    from 
      this(1) `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` `the env!a = T`
      add_get2_2[of env' s A p B]
    have "T = B" by simp
    moreover
    from `t' = Bvar (Param n)` have "{n \<rightarrow> [Fvar x,Fvar y]} t' = Fvar y" by simp
    ultimately
    show ?case 
      using 
        subst[of env' A B] in_add_2[OF ok'] 
        typing.T_Var[OF ok' _ add_get2_1[OF ok']]
      by simp
  qed
next
  case (T_Upd F env T l t2 t1 env' t' s p x y A B n)
  from sopen_eq_Upd[OF sym[OF `Upd t1 l t2 = {n \<rightarrow> [Fvar s,Fvar p]} t'`]]
  obtain t1' t2' where 
    t1: "t1 = {n \<rightarrow> [Fvar s,Fvar p]} t1'" and
    t2: "t2 = {Suc n \<rightarrow> [Fvar s,Fvar p]} t2'" and
    t': "t' = Upd t1' l t2'" 
    by auto
  { fix a assume "a \<notin> FV t'" with t' have "a \<notin> FV t1'" by simp } 
  note 
    t1' = T_Upd(4)[OF this[OF `s \<notin> FV t'`] this[OF `p \<notin> FV t'`] 
                      this[OF `x \<notin> FV t'`] this[OF `y \<notin> FV t'`] 
                      `x \<notin> env_dom env'` `y \<notin> env_dom env'`
                      `s \<noteq> p` `x \<noteq> y` t1 `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>`]
  from ok_finite[of env'] ok_add_2[OF typing_regular'[OF this]]
  have findom: "finite (env_dom env')" by simp

  { fix a assume "a \<notin> FV t'" with t' have "a \<notin> FV t2'" by simp }
  note 
    bnd_renaming_lem[OF this[OF `s \<notin> FV t'`] this[OF `p \<notin> FV t'`] 
                        this[OF `x \<notin> FV t'`] this[OF `y \<notin> FV t'`] 
                        `x \<notin> env_dom env'` `y \<notin> env_dom env'`
                        `s \<noteq> p` `x \<noteq> y` t2 `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>`]
  from this[of F T l "FV t2'"] T_Upd(2)
  have 
    "\<forall>sa pa. sa \<notin> F \<union> {s, p, x, y} \<union> FV t2' \<union> env_dom env' 
           \<and> pa \<notin> F \<union> {s, p, x, y} \<union> FV t2' \<union> env_dom env' 
           \<and> sa \<noteq> pa 
      \<longrightarrow> env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
          \<turnstile> ({Suc n \<rightarrow> [Fvar x,Fvar y]} t2'\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))"
    by simp
  from 
    typing.T_Upd[OF _ this t1' `l \<in> do T`]
    `finite F` findom t' 
  show ?case by simp
next
  case (T_Obj env f T F env' t' s p x y A B n)
  from `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` ok_add_2[of env' s A p B] 
  have "ok env'" by simp
  from 
    ok_add_ok[OF ok_add_ok[OF this `x \<notin> env_dom env'`]
                 not_in_env_bigger[OF `y \<notin> env_dom env'` not_sym[OF `x \<noteq> y`]]]
  have ok: "ok (env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>)" by assumption
  from sopen_eq_Obj[OF sym[OF `Obj f T = {n \<rightarrow> [Fvar s,Fvar p]} t'`]] 
  obtain f' where 
    obj: "{n \<rightarrow> [Fvar s,Fvar p]} Obj f' T = Obj f T" and
    t': "t' = Obj f' T" by auto
  from 
    this(1) `dom f = do T`
    sym[OF dom_sopenoption_lem[of "Suc n" "Fvar s" "Fvar p" f']]
    dom_sopenoption_lem[of "Suc n" "Fvar x" "Fvar y" f']
  have dom: "dom (\<lambda>l. sopen_option (Suc n) (Fvar x) (Fvar y) (f' l)) = do T" 
    by simp
    
  from 
    `finite F` finite_FV[of "Obj f' T"] 
    ok_finite[of env'] ok_add_2[OF ok]
  have finF: "finite (F \<union> {s,p,x,y} \<union>  FV (Obj f' T) \<union> env_dom env')"
    by simp

  have 
    "\<forall>l\<in>do T. \<forall>sa pa. sa \<notin> F \<union> {s, p, x, y} \<union> FV (Obj f' T) \<union> env_dom env' 
                     \<and> pa \<notin> F \<union> {s, p, x, y} \<union> FV (Obj f' T) \<union> env_dom env' 
                     \<and> sa \<noteq> pa 
      \<longrightarrow> env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
          \<turnstile> (the(sopen_option (Suc n) (Fvar x) (Fvar y) (f' l))\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : 
          return(the(T^l))"
  proof 
    fix l assume "l \<in> do T" with T_Obj(4)
    have cof: 
      "\<forall>sa pa. sa \<notin> F \<and> pa \<notin> F \<and> sa \<noteq> pa
        \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
            \<turnstile> (the(f l)\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))
          \<and> (\<forall>env'' t'' s' p' x' y' A' B' n'.
               s' \<notin> FV t'' \<longrightarrow> p' \<notin> FV t'' \<longrightarrow> x' \<notin> FV t'' \<longrightarrow> y' \<notin> FV t'' 
               \<longrightarrow> x' \<notin> env_dom env'' \<longrightarrow> y' \<notin> env_dom env'' \<longrightarrow> x' \<noteq> y' 
               \<longrightarrow> s' \<noteq> p' 
               \<longrightarrow> (the(f l)\<^bsup>[Fvar sa,Fvar pa]\<^esup>) = {n' \<rightarrow> [Fvar s',Fvar p']} t'' 
               \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> = env''\<lparr>s':A'\<rparr>\<lparr>p':B'\<rparr> 
               \<longrightarrow> env''\<lparr>x':A'\<rparr>\<lparr>y':B'\<rparr>
                   \<turnstile> {n' \<rightarrow> [Fvar x',Fvar y']} t'' : return(the(T^l)))"
      by simp
    from 
      `l \<in> do T` `dom f = do T` `Obj f T = {n \<rightarrow> [Fvar s,Fvar p]} t'` obj t'
      dom_sopenoption_lem[of "Suc n" "Fvar s" "Fvar p" f']
    have indomf': "l \<in> dom f'" by auto
    hence 
      opened: "the (sopen_option (Suc n) (Fvar x) (Fvar y) (f' l)) 
               = {Suc n \<rightarrow> [Fvar x,Fvar y]} the(f' l)" 
      by force
    from indomf' have FVsubset: "FV (the(f' l)) \<subseteq> FV (Obj f' T)" by force
    with 
      `s \<notin> FV t'` `p \<notin> FV t'` `x \<notin> FV t'` `y \<notin> FV t'` obj t'
      indomf' FV_option_lem[of f']
    obtain 
      "s \<notin> FV (the(f' l))" and "p \<notin> FV (the(f' l))" and
      "x \<notin> FV (the(f' l))" and "y \<notin> FV (the(f' l))" and
      "the(f l) = {Suc n \<rightarrow> [Fvar s,Fvar p]} the(f' l)" by auto
    from 
      bnd_renaming_lem[OF this(1-4) `x \<notin> env_dom env'` `y \<notin> env_dom env'`
                          `s \<noteq> p` `x \<noteq> y` this(5) `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` 
                          cof FVsubset]
    show 
      "\<forall>sa pa. sa \<notin> F \<union> {s, p, x, y} \<union> FV (Obj f' T) \<union> env_dom env' 
             \<and> pa \<notin> F \<union> {s, p, x, y} \<union> FV (Obj f' T) \<union> env_dom env' 
             \<and> sa \<noteq> pa 
        \<longrightarrow> env'\<lparr>x:A\<rparr>\<lparr>y:B\<rparr>\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
            \<turnstile> (the(sopen_option (Suc n) (Fvar x) (Fvar y) (f' l))\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : 
              return(the(T^l))"
      by (subst opened, assumption)
  qed
  from typing.T_Obj[OF ok dom finF this] t' show ?case by simp
qed

lemma type_renaming: 
  "\<lbrakk> e\<lparr>s:A\<rparr>\<lparr>p:B\<rparr> \<turnstile> {n \<rightarrow> [Fvar s,Fvar p]} t : T; 
     s \<notin> FV t; p \<notin> FV t; x \<notin> FV t; y \<notin> FV t; 
     x \<notin> env_dom e; y \<notin> env_dom e; x \<noteq> y; s \<noteq> p\<rbrakk> 
  \<Longrightarrow> e\<lparr>x:A\<rparr>\<lparr>y:B\<rparr> \<turnstile> {n \<rightarrow> [Fvar x,Fvar y]} t : T"
  by (auto simp: type_renaming')
(* too weak, as we need specific s,p *)

lemma obj_inv_elim': 
  assumes 
  "e \<turnstile> Obj f U : U" and 
  nin_s: "s \<notin> FV (Obj f U) \<union> env_dom e" and
  nin_p: "p \<notin> FV (Obj f U) \<union> env_dom e" and "s \<noteq> p"
  shows 
  "(dom f = do U) \<and> (\<forall>l\<in>do U. e\<lparr>s:U\<rparr>\<lparr>p:param(the(U^l))\<rparr>
                               \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(U^l)))"
  using assms
proof (cases rule: typing.cases)
  case (T_Obj F)
(*  from `e = env` `Obj f U = Obj f' T` `dom f' = do T`
  have "dom f = do U" by simp*)
  thus ?thesis 
  proof (simp, intro strip)
    fix l assume "l \<in> do U"
    from `finite F` finite_FV[of "Obj f U"] have "finite (F \<union> FV (Obj f U) \<union> {s,p})"
      by simp
    from exFresh_s_p_cof[OF this]
    obtain sa pa where 
      "sa \<noteq> pa" and
      nin_sa: "sa \<notin> F \<union> FV (Obj f U)" and
      nin_pa: "pa \<notin> F \<union> FV (Obj f U)" by auto
    with `l \<in> do U` T_Obj(4)
    have 
      "e\<lparr>sa:U\<rparr>\<lparr>pa:param(the(U^l))\<rparr> 
       \<turnstile> (the(f l)\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(U^l))"
      by simp
    moreover
    from `l \<in> do U` `dom f = do U`  
    have "l \<in> dom f" by simp
    with nin_s nin_p nin_sa nin_pa FV_option_lem[of f]
    have 
      "sa \<notin> FV (the(f l)) \<and> pa \<notin> FV (the(f l)) 
       \<and> s \<notin> FV (the(f l)) \<and> p \<notin> FV (the(f l))
       \<and> s \<notin> env_dom e \<and> p \<notin> env_dom e" by auto
    ultimately
    show 
      "e\<lparr>s:U\<rparr>\<lparr>p:param(the(U^l))\<rparr> 
       \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(U^l))"
      using type_renaming[OF _ _ _ _ _ _ _ `s \<noteq> p` `sa \<noteq> pa`]
      by (simp add: openz_def)
  qed
qed

lemma dom_lem: "e \<turnstile> Obj f (Object fun) : Object fun \<Longrightarrow> dom f = dom fun"
  by (erule typing.cases, auto)

lemma abs_typeE: 
  assumes "e \<turnstile> Call (Obj f U) l b : T"
  shows 
  "(\<exists>F. finite F 
      \<and> (\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
          \<longrightarrow> e\<lparr>s:U\<rparr>\<lparr>p: param(the(U^l))\<rparr> \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : T) \<Longrightarrow> P) 
  \<Longrightarrow> P"
  using assms
proof (cases rule: typing.cases)
  case (T_Call A (*env t1 t2=b*))
  assume 
    cof: "\<exists>F. finite F 
            \<and> (\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
                \<longrightarrow> e\<lparr>s:U\<rparr>\<lparr>p: param(the(U^l))\<rparr> \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : T) 
          \<Longrightarrow> P"
  from 
    `T = return(the(A^l))`
    `e \<turnstile> Obj f U : A` `l \<in> do A` obj_inv[of e f U A]
  obtain "e \<turnstile> (Obj f U) : U" and "T = return(the(U^l))" and "l \<in> do U" 
    by simp
  from obj_inv_elim[OF this(1)] this(2-3) cof show ?thesis by blast
qed

subsubsection {* Substitution preserves Well-Typedness *}
lemma bigger_env_lemma[rule_format]: 
  assumes "e \<turnstile> t : T"
  shows "\<forall>x X. x \<notin> env_dom e \<longrightarrow> e\<lparr>x:X\<rparr> \<turnstile> t: T"
proof -
  def pred_cof \<equiv> "\<lambda>L env t T l. 
    \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
     \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param (the(T^l))\<rparr> \<turnstile> (t\<^bsup>[Fvar s,Fvar p]\<^esup>) : return (the(T^l))"
  from assms show ?thesis
  proof (induct
      taking: "\<lambda>env t T l. \<forall>x X. x \<notin> env_dom env 
                            \<longrightarrow> (\<exists>L. finite L \<and> pred_cof L (env\<lparr>x:X\<rparr>) t T l)"
      rule: typing_induct)
    case Call thus ?case by auto
  next
    case (Fvar env Ta xa) thus ?case
    proof (intro strip)
      fix x X assume "x \<notin> env_dom env"
      from 
        get_env_smaller[OF `xa \<in> env_dom env` this]
        T_Var[OF ok_add_ok[OF `ok env` this]
        env_bigger[OF this `xa \<in> env_dom env`]]
        `the env!xa = Ta`
      show "env\<lparr>x:X\<rparr> \<turnstile> Fvar xa : Ta" by simp
    qed
  next
    case (Obj env Ta f) note pred_o = this(3)
    def pred_cof' \<equiv> "\<lambda>x X b l. \<exists>L. finite L \<and> pred_cof L (env\<lparr>x:X\<rparr>) (the b) Ta l"
    from pred_o
    have pred: "\<forall>x X. x \<notin> env_dom env \<longrightarrow> (\<forall>l\<in>dom f. pred_cof' x X (f l) l)"
      by (intro fmap_ball_all2'[of f "\<lambda>x X. x \<notin> env_dom env" pred_cof'],
        unfold pred_cof_def pred_cof'_def, simp)
    show ?case
    proof (intro strip)
      fix x X 
      def pred_bnd \<equiv> "\<lambda>s p b l. env\<lparr>x:X\<rparr>\<lparr>s:Ta\<rparr>\<lparr>p:param (the(Ta^l))\<rparr> 
                                \<turnstile> (the b\<^bsup>[Fvar s,Fvar p]\<^esup>) : return (the(Ta^l))"
      assume "x \<notin> env_dom env"
      with pred fmap_ex_cof[of f pred_bnd] `dom f = do Ta`
      obtain L where
        "finite L" and "\<forall>l\<in>do Ta. pred_cof L (env\<lparr>x:X\<rparr>) (the(f l)) Ta l"
        unfolding pred_bnd_def pred_cof_def pred_cof'_def
        by auto
      from 
        T_Obj[OF ok_add_ok[OF `ok env` `x \<notin> env_dom env`] 
                 `dom f = do Ta` this(1)]
        this(2)
      show "env\<lparr>x:X\<rparr> \<turnstile> Obj f Ta : Ta"
        unfolding pred_cof_def
        by simp
    qed
  next
    case (Upd env Ta t l u) 
    note pred_t = this(2) and pred_u = this(4)
    show ?case
    proof (intro strip)
      fix x X assume "x \<notin> env_dom env" 
      with pred_u obtain L where
        "finite L" and "pred_cof L (env\<lparr>x:X\<rparr>) u Ta l" by auto
      with `l \<in> do Ta` `x \<notin> env_dom env` pred_t
      show "env\<lparr>x:X\<rparr> \<turnstile> Upd t l u : Ta" 
        unfolding pred_cof_def
        by auto
    qed
  next
    case (Bnd env Ta l t L) note pred = this(3)
    show ?case
    proof (intro strip)
      fix x X assume "x \<notin> env_dom env"
      thus "\<exists>L. finite L \<and> pred_cof L (env\<lparr>x:X\<rparr>) t Ta l"
      proof (rule_tac x = "L \<union> {x}" in exI, simp add: `finite L`, 
          unfold pred_cof_def, auto)
        fix s p
        assume 
          "s \<notin> L" and "p \<notin> L" and "s \<noteq> p" and
          "s \<noteq> x" and "p \<noteq> x"
        note 
          subst_add[OF not_sym[OF `s \<noteq> x`]]
          subst_add[OF not_sym[OF `p \<noteq> x`]]
        from 
          this(1)[of env X Ta] this(2)[of "env\<lparr>s:Ta\<rparr>" X "param (the(Ta^l))"]
          pred `s \<notin> L` `p \<notin> L` `s \<noteq> p`
          not_in_env_bigger_2[OF `x \<notin> env_dom env` 
                                 not_sym[OF `s \<noteq> x`] not_sym[OF `p \<noteq> x`]]
        show 
          "env\<lparr>x:X\<rparr>\<lparr>s:Ta\<rparr>\<lparr>p:param (the(Ta^l))\<rparr> 
          \<turnstile> (t\<^bsup>[Fvar s,Fvar p]\<^esup>) : return (the(Ta^l))"
          by auto
      qed
    qed
  qed
qed

lemma bnd_disj_env_lem: 
  assumes 
  "ok e1" and "env_dom e1 \<inter> env_dom e2 = {}" and "ok e2" and
  "\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
    \<longrightarrow> e1\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>
        \<turnstile> (t2\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l)) 
        \<and> (env_dom (e1\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>) \<inter> env_dom e2 = {} 
    \<longrightarrow> ok e2 
    \<longrightarrow> e1\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>+e2 
        \<turnstile> (t2\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l)))"
  shows 
  "\<forall>s p. s \<notin> F \<union> env_dom (e1+e2) \<and> p \<notin> F \<union> env_dom (e1+e2) \<and> s \<noteq> p
    \<longrightarrow> (e1+e2)\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> \<turnstile> (t2\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))"
proof (intro strip, elim conjE)
  fix s p assume 
    nin_s: "s \<notin> F \<union> env_dom (e1+e2)" and
    nin_p: "p \<notin> F \<union> env_dom (e1+e2)" and "s \<noteq> p"
  from 
    this(1-2) env_add_dom_2[OF assms(1) _ _ this(3)]
    assms(2) env_app_dom[OF assms(1-3)]
  have "env_dom (e1\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>) \<inter> env_dom e2 = {}" by simp
  with 
    env_app_add2[OF assms(1-3) _ _ _ _ `s \<noteq> p`]
    env_app_dom[OF assms(1-3)] `ok e2` assms(4) nin_s nin_p `s \<noteq> p`
  show "(e1+e2)\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> \<turnstile> (t2\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))"
    by auto
qed

(* TODO: refactor to work with typing_induct *)
lemma disjunct_env: 
  assumes "e \<turnstile> t : A" 
  shows "(env_dom e \<inter> env_dom e' = {} \<Longrightarrow> ok e' \<Longrightarrow> e + e' \<turnstile> t : A)"
  using assms
proof (induct rule: typing.induct)
  case T_Call thus ?case by auto
next
  case (T_Var env x T)
  from 
    env_app_dom[OF `ok env` `env_dom env \<inter> env_dom e' = {}` `ok e'`]
    `x \<in> env_dom env`
  have indom: "x \<in> env_dom (env+e')" by simp
  from 
    `ok env` `x \<in> env_dom env` `the env!x = T` `env_dom env \<inter> env_dom e' = {}`
    `ok e'` 
  have "the (env+e')!x = T" by simp
  from 
    typing.T_Var[OF env_app_ok[OF `ok env` `env_dom env \<inter> env_dom e' = {}` 
                                  `ok e'`] 
                    indom this] 
  show ?case by assumption
next
  case (T_Upd F env T l t2 t1)
  from 
    typing.T_Upd[OF _ bnd_disj_env_lem[OF typing_regular'[OF `env \<turnstile> t1 : T`] 
                                          `env_dom env \<inter> env_dom e' = {}` `ok e'` 
                                          T_Upd(2)] 
                    T_Upd(4)[OF `env_dom env \<inter> env_dom e' = {}` `ok e'`] 
                    `l \<in> do T`]
    `finite F` ok_finite[OF env_app_ok[OF typing_regular'[OF `env \<turnstile> t1 : T`] 
                                          `env_dom env \<inter> env_dom e' = {}` `ok e'`]]
  show ?case by simp
next
  case (T_Obj env f T F)
  from 
    ok_finite[OF env_app_ok[OF `ok env` `env_dom env \<inter> env_dom e' = {}` `ok e'`]]
    `finite F` 
  have finF: "finite (F \<union> env_dom (env+e'))" by simp
  note 
    ball_Tltsp[of F
    "\<lambda>T l t s p. env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> \<turnstile> (t\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))
               \<and> (env_dom (env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>) \<inter> env_dom e' = {} 
                  \<longrightarrow> ok e' 
                  \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>+e' 
                      \<turnstile> (t\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l)))"
    T "F \<union> env_dom (env+e')"
    "\<lambda>T l t s p. (env+e')\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> 
                 \<turnstile> (t\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))"]
  from 
    this[OF _ T_Obj(4)] 
    bnd_disj_env_lem[OF `ok env` `env_dom env \<inter> env_dom e' = {}` `ok e'`] 
    typing.T_Obj[OF env_app_ok[OF `ok env` 
                    `env_dom env \<inter> env_dom e' = {}` `ok e'`] 
                    `dom f = do T` finF]
  show ?case by simp
qed

text {* Typed in the Empty Environment implies typed in any Environment *}
lemma empty_env: 
  assumes "(Env empty) \<turnstile> t : A" and "ok env"
  shows "env \<turnstile> t : A"
proof -
  from `ok env` have "env = (Env empty)+env" by (cases env, auto)
  with disjunct_env[OF assms(1) _ assms(2)] show ?thesis by simp
qed

lemma bnd_open_lem:
  assumes
  pred_bnd:
  "\<forall>sa pa. sa \<notin> F \<and> pa \<notin> F \<and> sa \<noteq> pa 
    \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> 
        \<turnstile> (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l)) 
     \<and> (\<forall>env'' t'' s' p' x' y' A' B' n'. s' \<notin> FV t'' \<union> FV x' \<union> FV y' 
         \<longrightarrow> p' \<notin> FV t'' \<union> FV x' \<union> FV y' \<longrightarrow> s' \<noteq> p' 
         \<longrightarrow> env'' \<turnstile> x' : A' \<longrightarrow> env'' \<turnstile> y' : B' 
         \<longrightarrow> (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) = {n' \<rightarrow> [Fvar s',Fvar p']} t'' 
         \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> = env''\<lparr>s':A'\<rparr>\<lparr>p':B'\<rparr> 
         \<longrightarrow> env'' \<turnstile> {n' \<rightarrow> [x',y']} t'' : return(the(T^l)))" and
  "ok env" and "env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>" and 
  "s \<notin> FV t'' \<union> FV x \<union> FV y" and "p \<notin> FV t'' \<union> FV x \<union> FV y" and "s \<noteq> p" and 
  "env' \<turnstile> x : A" and "env' \<turnstile> y : B" and 
  "t = {Suc n \<rightarrow> [Fvar s,Fvar p]} t'" and "FV t' \<subseteq> FV t''"
  shows 
  "\<forall>sa pa. sa \<notin> F \<union> {s,p} \<union> env_dom env' 
         \<and> pa \<notin> F \<union> {s,p} \<union> env_dom env' \<and> sa \<noteq> pa
    \<longrightarrow> env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
        \<turnstile> ({Suc n \<rightarrow> [x,y]} t'\<^bsup>[Fvar sa, Fvar pa]\<^esup>) : return(the(T^l))"
proof (intro strip, elim conjE)
  fix sa pa assume 
    nin_sa: "sa \<notin> F \<union> {s,p} \<union> env_dom env'" and 
    nin_pa: "pa \<notin> F \<union> {s,p} \<union> env_dom env'" and "sa \<noteq> pa"
  hence "sa \<notin> F \<and> pa \<notin> F \<and> sa \<noteq> pa" by auto
  moreover
  {
    fix a assume "a \<notin> FV t'' \<union> FV x \<union> FV y" and "a \<in> {s,p}"
    with 
      `FV t' \<subseteq> FV t''` nin_sa nin_pa `sa \<noteq> pa` 
      sopen_FV[of 0 "Fvar sa" "Fvar pa" t']
    have "a \<notin> FV (t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>) \<union> FV x \<union> FV y" by (auto simp: openz_def)
  } note 
      this[OF `s \<notin> FV t'' \<union> FV x \<union> FV y`] 
      this[OF `p \<notin> FV t'' \<union> FV x \<union> FV y`]
  moreover
  {
    from `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` ok_add_2[of env' s A p B]
    have "ok env'" by simp
    from nin_sa nin_pa `sa \<noteq> pa` env_add_dom[OF this] 
    obtain "sa \<notin> env_dom env'" and "pa \<notin> env_dom (env'\<lparr>sa:T\<rparr>)" by auto
    note 
      bigger_env_lemma[OF bigger_env_lemma[OF `env' \<turnstile> x : A` this(1)] this(2)]
      bigger_env_lemma[OF bigger_env_lemma[OF `env' \<turnstile> y : B` this(1)] this(2)]
  }note 
      this(1)[of "param(the(T^l))"] 
      this(2)[of "param(the(T^l))"]
  moreover
  from `t = {Suc n \<rightarrow> [Fvar s,Fvar p]} t'` sopen_commute[of 0 "Suc n" sa pa s p t']
  have "(t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) = {Suc n \<rightarrow> [Fvar s,Fvar p]} (t'\<^bsup>[Fvar sa,Fvar pa]\<^esup>)"
    by (simp add: openz_def)
  moreover
  from 
    subst_add[of p sa "env'\<lparr>s:A\<rparr>" B T] subst_add[of s sa env' A T]
    subst_add[of p pa "env'\<lparr>sa:T\<rparr>\<lparr>s:A\<rparr>" B "param(the(T^l))"] 
    subst_add[of s pa "env'\<lparr>sa:T\<rparr>" A "param(the(T^l))"]
    `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` nin_sa nin_pa
  have "env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> = env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>"
    by auto
  ultimately
  show 
    "env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
     \<turnstile> ({Suc n \<rightarrow> [x,y]} t'\<^bsup>[Fvar sa, Fvar pa]\<^esup>) : return(the(T^l))"
    using 
      pred_bnd `s \<noteq> p`
      sopen_commute_gen[OF lc_Fvar[of sa] lc_Fvar[of pa] 
                           typing_regular''[OF `env' \<turnstile> x : A`] 
                           typing_regular''[OF `env' \<turnstile> y : B`]
                           not_sym[OF Suc_not_Zero]]
    by (auto simp: openz_def)
qed

(* A variation of the Type Renaming lemma above. This is stronger and could be extended to show type renaming, using that a term typed in one environment is typed in any bigger environment *)
(* TODO: refactor to work with typing_induct *)
lemma open_lemma':
  shows 
  "e \<turnstile> t : C 
  \<Longrightarrow> (\<And>env t' s p x y A B n. s \<notin> FV t' \<union> FV x \<union> FV y 
         \<Longrightarrow> p \<notin> FV t' \<union> FV x \<union> FV y \<Longrightarrow> s \<noteq> p
         \<Longrightarrow> env \<turnstile> x : A \<Longrightarrow> env \<turnstile> y : B 
         \<Longrightarrow> t = {n \<rightarrow> [Fvar s,Fvar p]} t'
         \<Longrightarrow> e = env\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>
         \<Longrightarrow> env \<turnstile> {n \<rightarrow> [x,y]} t' : C)"
proof (induct set:typing)
  case (T_Var env x T env' t' s p y z A B n)
  from sopen_eq_Fvar[OF sym[OF `Fvar x = {n \<rightarrow> [Fvar s,Fvar p]} t'`]] 
  show ?case
  proof (elim disjE conjE)
    assume "t' = Fvar x" 
    with `s \<notin> FV t' \<union> FV y \<union> FV z` `p \<notin> FV t' \<union> FV y \<union> FV z` 
    obtain "x \<noteq> s" and "x \<noteq> p" by auto
    from `x \<in> env_dom env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` in_env_smaller2[OF _ this]
    have indom: "x \<in> env_dom env'" by simp
    from 
      `ok env` `the env!x = T` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>`
      ok_add_2[of env' s A p B] get_env_smaller2[OF this _ _ `s \<noteq> p`]
    have "the env'!x = T" by simp
    from 
      `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` `t' = Fvar x`
      ok_add_2[of env' s A p B] typing.T_Var[OF _ indom this]
    show ?case by simp
  next
    assume "x = s"
    with 
      `ok env` `the env!x = T` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` 
      add_get2_1[of env' s A p B] 
    have "T = A" by simp
    moreover assume "t' = Bvar (Self n)"
    ultimately show ?thesis using `env' \<turnstile> y : A` by simp
  next
    assume "x = p" 
    with 
      `ok env` `the env!x = T` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` 
      add_get2_2[of env' s A p B] have "T = B" by simp
    moreover assume "t' = Bvar (Param n)"
    ultimately show ?thesis using `env' \<turnstile> z : B` by simp
  qed
next
  case (T_Upd F env T l t2 t1 env' t' s p x y A B n)
  from sopen_eq_Upd[OF sym[OF `Upd t1 l t2 = {n \<rightarrow> [Fvar s,Fvar p]} t'`]]
  obtain t1' t2' where 
    t1': "t1 = {n \<rightarrow> [Fvar s,Fvar p]} t1'" and
    t2': "t2 = {Suc n \<rightarrow> [Fvar s,Fvar p]} t2'" and
    t': "t' = Upd t1' l t2'" by auto
  hence "FV t2' \<subseteq> FV t'" by auto
  from 
    `s \<notin> FV t' \<union> FV x \<union> FV y` `p \<notin> FV t' \<union> FV x \<union> FV y`
    t' `finite F` ok_finite[OF typing_regular'[OF `env' \<turnstile> x : A`]]
    typing.T_Upd[OF _ bnd_open_lem[OF T_Upd(2) 
                    typing_regular'[OF `env \<turnstile> t1 : T`] 
                    `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` 
                    `s \<notin> FV t' \<union> FV x \<union> FV y` 
                    `p \<notin> FV t' \<union> FV x \<union> FV y` `s \<noteq> p`
                    `env' \<turnstile> x : A` `env' \<turnstile> y : B` t2' this]
    T_Upd(4)[OF _ _ `s \<noteq> p` `env' \<turnstile> x : A` `env' \<turnstile> y : B` 
                t1' `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>`] `l \<in> do T`]
  show ?case by simp
next
  case (T_Obj env f T F env' t' s p x y A B n)
  from sopen_eq_Obj[OF sym[OF `Obj f T = {n \<rightarrow> [Fvar s,Fvar p]} t'`]]
  obtain f' where 
    obj: "Obj f T = {n \<rightarrow> [Fvar s,Fvar p]} Obj f' T" and 
    t': "t' = Obj f' T" by auto
  from 
    sym[OF this(1)] `dom f = do T`
    sym[OF dom_sopenoption_lem[of "Suc n" "Fvar s" "Fvar p" f']]
    dom_sopenoption_lem[of "Suc n" x y f']
  have dom: "dom (\<lambda>l. sopen_option (Suc n) x y (f' l)) = do T" by simp

  from `finite F` ok_finite[OF typing_regular'[OF `env' \<turnstile> x : A`]] 
  have finF: "finite (F \<union> {s,p} \<union> env_dom env')"
    by simp

  have
    "\<forall>l\<in>do T. \<forall>sa pa. sa \<notin> F \<union> {s,p} \<union> env_dom env' 
                     \<and> pa \<notin> F \<union> {s,p} \<union> env_dom env' 
                     \<and> sa \<noteq> pa 
      \<longrightarrow> env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
          \<turnstile> (the(sopen_option (Suc n) x y (f' l))\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))"
  proof 
    fix l assume "l \<in> do T" with T_Obj(4)
    have 
      cof: 
      "\<forall>sa pa. sa \<notin> F \<and> pa \<notin> F \<and> sa \<noteq> pa
        \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> 
            \<turnstile> (the(f l)\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))
          \<and> (\<forall>env'' t'' s' p' x' y' A' B' n'.
               s' \<notin> FV t'' \<union> FV x' \<union> FV y' \<longrightarrow> p' \<notin> FV t'' \<union> FV x' \<union> FV y' 
               \<longrightarrow> s' \<noteq> p' \<longrightarrow> env'' \<turnstile> x' : A' \<longrightarrow> env'' \<turnstile> y' : B'
               \<longrightarrow> (the(f l)\<^bsup>[Fvar sa,Fvar pa]\<^esup>) = {n' \<rightarrow> [Fvar s',Fvar p']} t''
               \<longrightarrow> env\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr> = env''\<lparr>s':A'\<rparr>\<lparr>p':B'\<rparr> 
               \<longrightarrow> env'' \<turnstile> {n' \<rightarrow> [x',y']} t'' : return(the(T^l)))"
      by simp
    from 
      `l \<in> do T` `dom f = do T` `Obj f T = {n \<rightarrow> [Fvar s,Fvar p]} t'` obj t'
      dom_sopenoption_lem[of "Suc n" "Fvar s" "Fvar p" f']
    have indomf': "l \<in> dom f'" by auto
    with obj sopen_option_lem[of f' "Suc n" "Fvar s" "Fvar p"] FV_option_lem[of f'] t'
    obtain 
      "the(f l) = {Suc n \<rightarrow> [Fvar s,Fvar p]} the(f' l)" and
      "FV (the(f' l)) \<subseteq> FV t'" by auto
    from 
      bnd_open_lem[OF cof `ok env` `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>` 
                      `s \<notin> FV t' \<union> FV x \<union> FV y` `p \<notin> FV t' \<union> FV x \<union> FV y`
                      `s \<noteq> p` `env' \<turnstile> x : A` `env' \<turnstile> y : B` this]
      indomf' sopen_option_lem[of f' "Suc n" x y] T_Obj(4)
    show 
      "\<forall>sa pa. sa \<notin> F \<union> {s,p} \<union> env_dom env' 
             \<and> pa \<notin> F \<union> {s,p} \<union> env_dom env' \<and> sa \<noteq> pa 
        \<longrightarrow> env'\<lparr>sa:T\<rparr>\<lparr>pa:param(the(T^l))\<rparr>
            \<turnstile> (the(sopen_option (Suc n) x y (f' l))\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(T^l))"
      by simp
  qed
  from typing.T_Obj[OF typing_regular'[OF `env' \<turnstile> x : A`] dom finF this] t' 
  show ?case by simp
next
  case (T_Call env t1 T t2 l env' t' s p x y A B n)
  from sopen_eq_Call[OF sym[OF `Call t1 l t2 = {n \<rightarrow> [Fvar s,Fvar p]} t'`]]
  obtain t1' t2' where 
    t1: "t1 = {n \<rightarrow> [Fvar s,Fvar p]} t1'" and
    t2: "t2 = {n \<rightarrow> [Fvar s,Fvar p]} t2'" and
    t': "t' = Call t1' l t2'" by auto
  { fix a assume "a \<notin> FV t' \<union> FV x \<union> FV y" 
    with t' have "a \<notin> FV t1' \<union> FV x \<union> FV y" by simp
  }note 
      t1' = T_Call(2)[OF this[OF `s \<notin> FV t' \<union> FV x \<union> FV y`]
                        this[OF `p \<notin> FV t' \<union> FV x \<union> FV y`]
                        `s \<noteq> p` `env' \<turnstile> x : A` `env' \<turnstile> y : B`
                        t1 `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>`]
  { fix a assume "a \<notin> FV t' \<union> FV x \<union> FV y" 
    with t' have "a \<notin> FV t2' \<union> FV x \<union> FV y" by simp
  }
  from 
    typing.T_Call[OF t1' T_Call(4)[OF this[OF `s \<notin> FV t' \<union> FV x \<union> FV y`]
                                     this[OF `p \<notin> FV t' \<union> FV x \<union> FV y`]
                                     `s \<noteq> p` `env' \<turnstile> x : A` `env' \<turnstile> y : B`
                                     t2 `env = env'\<lparr>s:A\<rparr>\<lparr>p:B\<rparr>`] 
                     `l \<in> do T`]
    t'
  show ?case by simp
qed

lemma open_lemma: 
  "\<lbrakk> env\<lparr>s:A\<rparr>\<lparr>p:B\<rparr> \<turnstile> {n \<rightarrow> [Fvar s,Fvar p]} t : T; 
     s \<notin> FV t \<union> FV x \<union> FV y;  p \<notin> FV t \<union> FV x \<union> FV y; s \<noteq> p; 
     env \<turnstile> x : A; env \<turnstile> y : B \<rbrakk> 
  \<Longrightarrow> env \<turnstile> {n \<rightarrow> [x,y]} t : T"  
  by (simp add: open_lemma')

subsubsection {* Subject reduction *}
lemma type_dom[simp]: "env \<turnstile> (Obj a A) : A \<Longrightarrow> dom a = do A" 
  by (erule typing.cases, auto)

lemma select_preserve_type[simp]:
  assumes 
  "env \<turnstile> Obj f (Object t) : Object t" and "s \<notin> FV a" and "p \<notin> FV a" and
  "env\<lparr>s:(Object t)\<rparr>\<lparr>p:param(the(t l2))\<rparr> \<turnstile> (a\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(t l2))" and
  "l1 \<in> dom t" and "l2 \<in> dom t"
  shows 
  "\<exists>F. finite F 
     \<and> (\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p
         \<longrightarrow> env\<lparr>s:(Object t)\<rparr>\<lparr>p:param(the(t l1))\<rparr>
             \<turnstile> (the((f(l2 \<mapsto> a)) l1)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(t l1)))"
proof -
  from ok_finite[OF typing_regular'[OF `env \<turnstile> Obj f (Object t) : Object t`]]
  have finF: "finite ({s,p} \<union> env_dom env)" by simp

  { 
    note 
      ok_env = typing_regular'[OF `env \<turnstile> Obj f (Object t) : Object t`] and
      ok_env_sp = typing_regular'[OF assms(4)]
    fix sa pa assume 
      nin_sa: "sa \<notin> {s,p} \<union> env_dom env" and
      nin_pa: "pa \<notin> {s,p} \<union> env_dom env" and "sa \<noteq> pa"
    from this(1) ok_add_2[OF ok_env_sp] env_add_dom_2[OF ok_env]
    have "sa \<notin> env_dom (env\<lparr>s:Object t\<rparr>\<lparr>p:param(the(t l2))\<rparr>)" by simp
    from 
      nin_sa bigger_env_lemma[OF assms(4) this]
      subst_add[of sa p "env\<lparr>s:Object t\<rparr>" "Object t" "param(the(t l2))"]
      subst_add[of sa s env "Object t" "Object t"]
    have 
      aT_sa: "env\<lparr>sa:Object t\<rparr>\<lparr>s:Object t\<rparr>\<lparr>p:param(the(t l2))\<rparr>
              \<turnstile> (a\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(t l2))" by simp
    from 
      `sa \<noteq> pa` nin_sa nin_pa env_add_dom[OF ok_env] 
      ok_add_2[OF ok_env_sp]
    obtain 
      "s \<notin> env_dom (env\<lparr>sa:Object t\<rparr>)" and
      "p \<notin> env_dom (env\<lparr>sa:Object t\<rparr>)" and "s \<noteq> p" and 
      "sa \<notin> env_dom env" and "pa \<notin> env_dom (env\<lparr>sa:Object t\<rparr>)" 
      by auto
    with env_add_dom_2[OF ok_add_ok[OF ok_env this(4)] this(1-3)] nin_pa
    have "pa \<notin> env_dom (env\<lparr>sa:Object t\<rparr>\<lparr>s:Object t\<rparr>\<lparr>p:param(the(t l2))\<rparr>)"
      by simp
    from 
      nin_pa bigger_env_lemma[OF aT_sa this]
      subst_add[of pa p "env\<lparr>sa:Object t\<rparr>\<lparr>s:Object t\<rparr>" 
                   "param(the(t l2))" "param(the(t l2))"]
      subst_add[of pa s "env\<lparr>sa:Object t\<rparr>" "param(the(t l2))" "Object t"]
    have 
      aT_sapa: 
      "env\<lparr>sa:Object t\<rparr>\<lparr>pa:param(the(t l2))\<rparr>\<lparr>s:Object t\<rparr>\<lparr>p:param(the(t l2))\<rparr>
      \<turnstile> {0 \<rightarrow> [Fvar s, Fvar p]} a : return(the(t l2))" by (simp add: openz_def)
    from nin_sa nin_pa `s \<notin> FV a` `p \<notin> FV a` ok_add_2[OF ok_env_sp] 
    obtain 
      ninFV_s: "s \<notin> FV a \<union> FV (Fvar sa) \<union> FV (Fvar pa)" and
      ninFV_p: "p \<notin> FV a \<union> FV (Fvar sa) \<union> FV (Fvar pa)" and "s \<noteq> p"
      by auto
    from ok_add_2[OF typing_regular'[OF aT_sapa]]
    have ok_env_sapa: "ok (env\<lparr>sa:Object t\<rparr>\<lparr>pa:param(the(t l2))\<rparr>)"
      by simp
    with ok_add_reverse[OF this]
    have ok_env_pasa: "ok (env\<lparr>pa:param(the(t l2))\<rparr>\<lparr>sa:Object t\<rparr>)"
      by simp

    from 
      open_lemma[OF aT_sapa ninFV_s ninFV_p `s \<noteq> p` _
                    T_Var[OF ok_env_sapa in_add[OF ok_env_sapa] 
                             add_get2_2[OF ok_env_sapa]]]
      T_Var[OF ok_env_pasa in_add[OF ok_env_pasa] add_get2_2[OF ok_env_pasa]]
      ok_add_reverse[OF ok_env_sapa]
    have 
      "env\<lparr>sa:(Object t)\<rparr>\<lparr>pa:param(the(t l2))\<rparr> 
       \<turnstile> (a\<^bsup>[Fvar sa,Fvar pa]\<^esup>) : return(the(t l2))"
      by (simp add: openz_def)
  }note alem = this

(* case split *)
  show ?thesis
  proof (cases "l1 = l2")
    case True with assms obj_inv_elim'[OF assms(1)] show ?thesis
      by (simp (no_asm_simp), rule_tac x = "{s,p} \<union> env_dom env" in exI,
          auto simp: finF alem)
  next
    case False
    from obj_inv_elim[OF `env \<turnstile> Obj f (Object t) : Object t`]
    obtain F where 
      "finite F" and
      "\<forall>l\<in>dom t. 
        \<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p
         \<longrightarrow> env\<lparr>s:Object t\<rparr>\<lparr>p:param(the(Object t^l))\<rparr>
             \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(Object t^l))"
      by auto
    from this(2) `l1 \<in> dom t`
    have 
      "\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p
        \<longrightarrow> env\<lparr>s:Object t\<rparr>\<lparr>p:param(the(Object t^l1))\<rparr>
            \<turnstile> (the(f l1)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(Object t^l1))"
      by auto
    thus ?thesis using `finite F` `l1 \<noteq> l2` by (simp,blast)
  qed
qed

text {* Main Lemma *}
(* TODO: refactor to work with typing_induct *)
lemma subject_reduction: "e \<turnstile> t : T \<Longrightarrow> (\<And>t'. t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> e \<turnstile> t' : T)"
proof (induct set: typing)
  case (T_Var env x T t') 
  from Fvar_beta[OF `Fvar x \<rightarrow>\<^sub>\<beta> t'`] show ?case by simp 
next
  case (T_Upd F env T l t2 t1 t')
  from Upd_beta[OF `Upd t1 l t2 \<rightarrow>\<^sub>\<beta> t'`] show ?case
  proof (elim disjE exE conjE)
    fix t1' assume "t1 \<rightarrow>\<^sub>\<beta> t1'" and "t' = Upd t1' l t2"
    from 
      this(2) T_Upd(2) 
      typing.T_Upd[OF `finite F` _ T_Upd(4)[OF this(1)] `l \<in> do T`]
    show ?case by simp
  next
    fix t2' F' 
    assume 
      "finite F'" and
      pred_F': "\<forall>s p. s \<notin> F' \<and> p \<notin> F' \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>t''. t2\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> t2' = \<sigma>[s,p] t'')"  and
      t': "t' = Upd t1 l t2'"
    have 
      "\<forall>s p. s \<notin> F \<union> F' \<and> p \<notin> F \<union> F' \<and> s \<noteq> p
        \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> \<turnstile> (t2'\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))"
    proof (intro strip, elim conjE)
      fix s p assume 
        nin_s: "s \<notin> F \<union> F'" and
        nin_p: "p \<notin> F \<union> F'" and "s \<noteq> p"
      with pred_F' obtain t'' where "t2\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t''" and "t2' = \<sigma>[s,p] t''"
        by auto
      with beta_lc[OF this(1)] sopen_sclose_eq_t[of t'' 0 s p]
      have "t2\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> (t2'\<^bsup>[Fvar s,Fvar p]\<^esup>)" 
        by (simp add: openz_def closez_def)
      with nin_s nin_p `s \<noteq> p` T_Upd(2) 
      show "env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> \<turnstile> (t2'\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))"
        by auto
    qed
    from t' `finite F` `finite F'` typing.T_Upd[OF _ this `env \<turnstile> t1 : T` `l \<in> do T`]
    show ?case by simp
  next
    fix f U assume 
      "l \<in> dom f" and "Obj f U = t1" and 
      t': "t' = Obj (f(l \<mapsto> t2)) U"
    from this(1-2) `env \<turnstile> t1 : T` obj_inv[of env f U T]
    obtain t where 
      objT: "env \<turnstile> Obj f (Object t) : (Object t)" and 
      "Object t = T" and "T = U" 
      by (cases T, auto)
    from obj_inv_elim[OF objT] `Object t = T` `l \<in> dom f` 
    have domf': "dom (f(l \<mapsto> t2)) = do T" by auto
    have 
      exF: "\<forall>l'\<in>do T. 
             (\<exists>F'. finite F' 
                 \<and> (\<forall>s p. s \<notin> F' \<union> (F \<union> FV t2) \<and> p \<notin> F' \<union> (F \<union> FV t2) \<and> s \<noteq> p 
                     \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l'))\<rparr>
                         \<turnstile> (the ((f(l \<mapsto> t2)) l')\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l'))))"
    proof
      fix l' assume "l' \<in> do T"
      with dom_lem[OF objT] `l \<in> dom f` `Object t = T`
      obtain ll': "l' \<in> dom t" and "l \<in> dom t" by auto

      from `finite F` have "finite (F \<union> FV t2)" by simp
      from exFresh_s_p_cof[OF this]
      obtain s p where 
        nin_s: "s \<notin> F \<union> FV t2" and 
        nin_p: "p \<notin> F \<union> FV t2" and "s \<noteq> p"
        by auto
      with T_Upd(2) `Object t = T` 
      have 
        "env\<lparr>s:Object t\<rparr>\<lparr>p:param(the(t l))\<rparr> 
         \<turnstile> (t2\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(t l))"
        by auto
      from 
        select_preserve_type[OF objT _ _ this ll'] sym[OF `Object t = T`]
        nin_s nin_p `l \<in> dom t`
      obtain F' where 
        "finite F'" and
        "\<forall>s p. s \<notin> F' \<and> p \<notin> F' \<and> s \<noteq> p
          \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l'))\<rparr>
              \<turnstile> (the ((f(l \<mapsto> t2)) l')\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l'))"
        by auto
      thus 
        "\<exists>F'. finite F' 
            \<and> (\<forall>s p. s \<notin> F' \<union> (F \<union> FV t2) \<and> p \<notin> F' \<union> (F \<union> FV t2) \<and> s \<noteq> p
                \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l'))\<rparr>
                    \<turnstile> (the ((f(l \<mapsto> t2)) l')\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l')))"
        by blast
    qed
    { fix Ta from finite_dom_fmap have "finite (do Ta)" by (cases Ta, auto) }
    note fin_doT = this ball_ex_finite[of "do T" "F \<union> FV t2"]
    from this(2)[OF this(1)[of T] _ exF] `finite F`
    obtain F' where 
      "finite F'" and
      "\<forall>l'\<in>do T. \<forall>s p. s \<notin> F' \<union> (F \<union> FV t2) \<and> p \<notin> F' \<union> (F \<union> FV t2) \<and> s \<noteq> p
                   \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l'))\<rparr>
                       \<turnstile> (the ((f(l \<mapsto> t2)) l')\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l'))"
      by auto
    moreover
    from `finite F'` `finite F` have "finite (F' \<union> (F \<union> FV t2))" by simp
    note typing.T_Obj[OF typing_regular'[OF `env \<turnstile> t1 : T`] domf' this]
    ultimately show ?case using t' `T = U` by auto
  qed
next
  case (T_Obj env f T F t')
  from Obj_beta[OF `Obj f T \<rightarrow>\<^sub>\<beta> t'`] show ?case
  proof (elim exE conjE)
    fix l f' a a' F' assume 
      "dom f = dom f'" and "f = f'(l \<mapsto> a)" and "l \<in> dom f'" and
      t': "t' = Obj (f'(l \<mapsto> a')) T" and "finite F'" and
      red_sp: "\<forall>s p. s \<notin> F' \<and> p \<notin> F' \<and> s \<noteq> p 
                \<longrightarrow> (\<exists>t''. a\<^bsup>[Fvar s, Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> a' = \<sigma>[s,p] t'')"
    from this(2) `dom f = do T` have domf': "dom (f'(l \<mapsto> a')) = do T" by auto
    have 
      exF: "\<forall>l'\<in>do T. \<forall>s p. s \<notin> F \<union> F' \<and> p \<notin> F \<union> F' \<and> s \<noteq> p 
             \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l'))\<rparr>
                 \<turnstile> (the ((f'(l \<mapsto> a')) l')\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l'))"
    proof (intro strip, elim conjE)
      fix l' s p assume 
        "l' \<in> do T" and 
        nin_s: "s \<notin> F \<union> F'" and
        nin_p: "p \<notin> F \<union> F'" and "s \<noteq> p"
      with red_sp obtain t'' where "a\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t''" and "a' = \<sigma>[s,p] t''" 
        by auto
      with 
        beta_lc[OF this(1)] sopen_sclose_eq_t[of t'' 0 s p] 
        `f = f'(l \<mapsto> a)`
      have "the (f l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> (the((f'(l \<mapsto> a')) l)\<^bsup>[Fvar s,Fvar p]\<^esup>)" 
        by (simp add: openz_def closez_def)
      with T_Obj(4) nin_s nin_p `s \<noteq> p` `l' \<in> do T` `f = f'(l \<mapsto> a)`
      show 
        "env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l'))\<rparr>
         \<turnstile> (the((f'(l \<mapsto> a')) l')\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l'))"
        by auto
    qed
    from typing.T_Obj[OF `ok env` domf' _ this] `finite F` `finite F'` t'
    show ?case by (simp (no_asm_simp))
  qed
next
  case (T_Call env t1 T t2 l t')
  from Call_beta[OF `Call t1 l t2 \<rightarrow>\<^sub>\<beta> t'`] show ?case
  proof (elim disjE conjE exE)
    fix t1' assume "t1 \<rightarrow>\<^sub>\<beta> t1'" and "t' = Call t1' l t2"
    from 
      typing.T_Call[OF T_Call(2)[OF this(1)] 
                       `env \<turnstile> t2 : param(the(T^l))` `l \<in> do T`]
      this(2)
    show ?case by simp
  next
    fix t2' assume "t2 \<rightarrow>\<^sub>\<beta> t2'" and "t' = Call t1 l t2'"
    from 
      typing.T_Call[OF `env \<turnstile> t1 : T` T_Call(4)[OF this(1)] `l \<in> do T`]
      this(2) 
    show ?case by simp
  next
    fix f U assume "Obj f U = t1" and "l \<in> dom f" and t': "t' = (the(f l)\<^bsup>[Obj f U,t2]\<^esup>)"
    from 
      typing.T_Call[OF `env \<turnstile> t1 : T` `env \<turnstile> t2 : param(the(T^l))` `l \<in> do T`]
      sym[OF this(1)] `env \<turnstile> t1 : T` `env \<turnstile> t2 : param(the(T^l))` 
      obj_inv[of env f U T]
    obtain 
      objT: "env \<turnstile> (Obj f T) : T" and "T = U" and
      callT: "env \<turnstile> Call (Obj f T) l t2 : return(the(T^l))" 
      by auto
    have 
      "(\<exists>F. finite F 
          \<and> (\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p 
              \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> 
                  \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l)))
      \<Longrightarrow> env \<turnstile> (the (f l)\<^bsup>[Obj f T,t2]\<^esup>) : return (the(T^l)))"
    proof (elim exE conjE)
      fix F 
      assume 
        "finite F" and
        pred_F:
        "\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p
          \<longrightarrow> env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> 
              \<turnstile> (the(f l)\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))"
      from this(1) finite_FV[of "Obj f T"]
      have "finite (F \<union> FV (Obj f T) \<union> FV t2)" by simp
      from exFresh_s_p_cof[OF this]
      obtain s p where 
        nin_s: "s \<notin> F \<union> FV (Obj f T) \<union> FV t2" and
        nin_p: "p \<notin> F \<union> FV (Obj f T) \<union> FV t2" and "s \<noteq> p" 
        by auto
      with pred_F
      have 
        type_opened: "env\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr>
                      \<turnstile> {0 \<rightarrow> [Fvar s,Fvar p]} the(f l) : return(the(T^l))"
        by (auto simp: openz_def)
      from nin_s nin_p FV_option_lem[of f] objT `l \<in> do T`
      obtain 
        "s \<notin> FV (the(f l)) \<union> FV (Obj f T) \<union> FV t2" and
        "p \<notin> FV (the(f l)) \<union> FV (Obj f T) \<union> FV t2" by auto
      from 
        open_lemma[OF type_opened this `s \<noteq> p` 
        objT `env \<turnstile> t2 : param(the(T^l))`]
      show ?thesis by (simp add: openz_def)
    qed
    with abs_typeE[OF callT] t' `T = U` show ?case by auto
  qed
qed

theorem subject_reduction': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induct set: rtranclp) (iprover intro: subject_reduction)+

lemma type_members_equal: 
  fixes A :: type and B :: type
  assumes "do A = do B" and "\<forall>i. (A^i) = (B^i)"
  shows "A = B"
proof (cases A)
  case (Object ta) thus ?thesis
  proof (cases B)
    case (Object tb)
    from `\<forall>i. (A^i) = (B^i)` `A = Object ta` `B = Object tb` 
    have "\<And>i. ta i = tb i" by auto
    with `A = Object ta` `B = Object tb` show ?thesis by (simp add: ext)
  qed
qed

lemma not_var: "Env empty \<turnstile> a : A \<Longrightarrow> \<forall>x. a \<noteq> Fvar x"
  by (rule allI, case_tac x, auto)

lemma Call_label_range: "(Env empty) \<turnstile> Call (Obj c T) l b : A \<Longrightarrow> l \<in> dom c"
  by (erule typing_elims, erule typing.cases, simp_all)

lemma  Call_subterm_type: "Env empty \<turnstile> Call t l b: T 
  \<Longrightarrow> (\<exists>T'. Env empty \<turnstile> t : T') \<and>  (\<exists>T'. Env empty \<turnstile> b : T')"
  by (erule typing.cases) auto

lemma Upd_label_range: "Env empty \<turnstile> Upd (Obj c T) l x : A \<Longrightarrow> l \<in> dom c"
  by (erule typing_elims, erule typing.cases, simp_all)

lemma Upd_subterm_type: 
  "Env empty \<turnstile> Upd t l x : T \<Longrightarrow> \<exists>T'. Env empty \<turnstile> t : T'" 
  by (erule typing.cases) auto

lemma no_var: "\<exists>T. Env empty \<turnstile> Fvar x : T \<Longrightarrow> False"
  by (case_tac x, auto)

lemma no_bvar: "e \<turnstile> Bvar x : T \<Longrightarrow> False" 
  by (erule typing.cases, auto)

subsubsection{*Unique Type*}
theorem type_unique[rule_format]: 
  assumes "env \<turnstile> a: T"
  shows "\<forall>T'. env \<turnstile> a: T' \<longrightarrow> T = T'"
  using assms
proof (induct rule: typing.induct)
  case T_Var thus ?case by (auto simp: add_get_eq)
next
  case T_Obj show ?case by (auto simp: sym[OF obj_inv])
next
  case T_Call from this(2) show ?case by auto
next 
  case T_Upd from this(4) show ?case by auto
qed

subsubsection{*Progress*}
text {* Final Type Soundness Lemma *}
theorem progress: 
  assumes "Env empty \<turnstile> t : A" and "\<not>(\<exists>c A. t = Obj c A)"
  shows "\<exists>b. t \<rightarrow>\<^sub>\<beta> b"
proof -
  fix f
  have 
    "(\<forall>A. Env empty \<turnstile> t : A \<longrightarrow> \<not>(\<exists>c T. t = Obj c T) \<longrightarrow> (\<exists>b. t \<rightarrow>\<^sub>\<beta> b))
    &(\<forall>A. Env empty \<turnstile> Obj f A : A \<longrightarrow> \<not>(\<exists>c T. Obj f A = Obj c T) 
       \<longrightarrow> (\<exists>b. Obj f A \<rightarrow>\<^sub>\<beta> b))"
  proof (induct rule: sterm_induct)
    case (Bvar b) with no_bvar[of "Env empty" b] show ?case 
      by auto (* contradiction *)
  next
    case (Fvar x) with Fvar_beta[of x] show ?case
      by auto (* contradiction *)
  next
    case Obj show ?case by auto (* contradiction *)
  next
    case empty thus ?case by auto (* contradiction *)
  next
    case insert show ?case by auto (* contradiction *)
  next
    case (Call t1 l t2) show ?case
    proof (clarify)
      fix T assume 
        "Env empty \<turnstile> t1 : T" and "Env empty \<turnstile> t2 : param(the(T^l))" and "l \<in> do T"
      note lc = typing_regular''[OF this(1)] typing_regular''[OF this(2)]
      from 
        `Env empty \<turnstile> t1 : T` 
        `\<forall>A. Env empty \<turnstile> t1 : A \<longrightarrow> \<not> (\<exists>c T. t1 = Obj c T) \<longrightarrow> (\<exists>b. t1 \<rightarrow>\<^sub>\<beta> b)`
      have "(\<exists>c B. t1 = Obj c B) \<or> (\<exists>b. t1 \<rightarrow>\<^sub>\<beta> b)" by auto
      thus "\<exists>b. Call t1 l t2 \<rightarrow>\<^sub>\<beta> b"
      proof (elim disjE exE)
        fix c B assume "t1 = Obj c B" 
        with 
          `Env empty \<turnstile> t1 : T` obj_inv[of "Env empty" c B T] 
          `l \<in> do T` obj_inv_elim[of "Env empty" c B]
        have "l \<in> dom c" by auto
        with `t1 = Obj c B` lc beta.beta[of l c B t2]
        show ?thesis by auto
      next
        fix b assume "t1 \<rightarrow>\<^sub>\<beta> b"
        from beta.beta_CallL[OF this lc(2)] show ?thesis by auto
      qed
    qed
  next
    case (Upd t1 l t2) show ?case
    proof (clarify)
      fix T F
      assume 
        "finite F" and
        "\<forall>s p. s \<notin> F \<and> p \<notin> F \<and> s \<noteq> p
          \<longrightarrow> Env empty\<lparr>s:T\<rparr>\<lparr>p:param(the(T^l))\<rparr> 
              \<turnstile> (t2\<^bsup>[Fvar s,Fvar p]\<^esup>) : return(the(T^l))" and
        "Env empty \<turnstile> t1 : T" and
        "l \<in> do T"
      from typing_regular''[OF T_Upd[OF this]] lc_upd[of t1 l t2]
      obtain "lc t1" and "body t2" by auto
      from 
        `Env empty \<turnstile> t1 : T` 
        `\<forall>A. Env empty \<turnstile> t1 : A \<longrightarrow> \<not> (\<exists>c T. t1 = Obj c T) \<longrightarrow> (\<exists>b. t1 \<rightarrow>\<^sub>\<beta> b)`
      have "(\<exists>c B. t1 = Obj c B) \<or> (\<exists>b. t1 \<rightarrow>\<^sub>\<beta> b)" by auto
      thus "\<exists>b. Upd t1 l t2 \<rightarrow>\<^sub>\<beta> b"
      proof (elim disjE exE)
        fix c B assume "t1 = Obj c B" 
        with 
          `Env empty \<turnstile> t1 : T` obj_inv[of "Env empty" c B T] 
          `l \<in> do T` obj_inv_elim[of "Env empty" c B]
        have "l \<in> dom c" by auto
        with `t1 = Obj c B` `lc t1` `body t2` beta.beta_Upd[of l c B t2]
        show ?thesis by auto
      next
        fix b assume "t1 \<rightarrow>\<^sub>\<beta> b"
        from beta.beta_UpdL[OF this `body t2`] show ?thesis by auto
      qed
    qed
  qed
  with assms show ?thesis by auto
qed

end
