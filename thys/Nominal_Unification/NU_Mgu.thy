(*<*)
theory NU_Mgu
imports NU_Substs
begin
(*>*)

section \<open>Most General Unifiers\<close>

text \<open>
 Defines the notion of unification problems and reduction rules over sets of
 such problems; proves that every reduction leading to the empty set produces an mgu.
\<close>

syntax equ_prob :: "trm \<Rightarrow> trm \<Rightarrow> (trm \<times> trm)"  (infix "\<approx>?" 81)
  fresh_prob :: "string \<Rightarrow> trm \<Rightarrow> (string \<times> trm)" (infix "\<sharp>?" 81)
translations
 "t1 \<approx>? t2" \<rightharpoonup> "(t1, t2)"
 "a \<sharp>? t"  \<rightharpoonup> "(a,t)"

text \<open>
  All solutions for a unification problem.
\<close>

type_synonym problem_type = "((trm \<times> trm) list) \<times> ((string \<times> trm) list)"

type_synonym unifier_type = "fresh_envs \<times> substs"

definition U:: "problem_type \<Rightarrow> (unifier_type set)"
  where all_solutions_def: 
    "U P  \<equiv> {(nabla, s). 
             (\<forall> (t1,t2) \<in> set (fst P). nabla \<turnstile> subst s t1 \<approx> subst s t2) \<and> 
             (\<forall> (a,t) \<in> set (snd P). nabla \<turnstile> a \<sharp> subst s t)}"

text \<open>The set of variables in unification problems.\<close>

type_synonym eprobs = "((trm \<times> trm) list)"
type_synonym fprobs = "((string \<times> trm) list)"
type_synonym probs = "eprobs \<times> fprobs"

fun vars_fprobs:: "((string \<times> trm) list) \<Rightarrow> (string set)"
  where
  "vars_fprobs [] = {}" |
  "vars_fprobs (x#xs) = (vars_trm (snd x))\<union>(vars_fprobs xs)"

fun  vars_eprobs :: "((trm \<times> trm) list) \<Rightarrow> (string set)"
  where
   "vars_eprobs [] = {}" |
   "vars_eprobs (x#xs) = (vars_trm (snd x))\<union>(vars_trm (fst x))\<union>(vars_eprobs xs)"

definition vars_probs :: "problem_type \<Rightarrow> nat"
  where "vars_probs P \<equiv> card((vars_fprobs (snd P))\<union>(vars_eprobs (fst P)))"

text \<open>Most general unifier\<close>

definition mgu :: "problem_type \<Rightarrow> unifier_type \<Rightarrow> bool"
  where "mgu P unif \<equiv> 
   \<forall> (nabla,s1)\<in> U P. (\<exists> s2. (nabla \<Turnstile> (subst s2) (fst unif)) \<and> 
                              (nabla \<Turnstile> subst (s2 \<bullet>(snd unif)) \<approx> subst s1))"


text \<open>Idempotency of a unifier\<close>

definition idem :: "unifier_type \<Rightarrow> bool"
  where "idem unif \<equiv> (fst unif)\<Turnstile> subst ((snd unif)\<bullet>(snd unif)) \<approx> subst (snd unif)"

text \<open>Application of a substitution to a problem\<close>

definition apply_subst_eprobs :: "substs \<Rightarrow> eprobs \<Rightarrow> eprobs"
  where "apply_subst_eprobs s P \<equiv> map (\<lambda>(t1, t2). (subst s t1 \<approx>? subst s t2)) P"

definition apply_subst_fprobs :: "substs \<Rightarrow> fprobs \<Rightarrow> fprobs"
  where "apply_subst_fprobs s P \<equiv> map (\<lambda>(a, t). (a \<sharp>? subst s t)) P"

definition apply_subst :: "substs \<Rightarrow> problem_type \<Rightarrow> problem_type"
  where "apply_subst s P \<equiv> (map (\<lambda>(t1, t2). (subst s t1 \<approx>? subst s t2)) (fst P),
                      map (\<lambda>(a, t). (a \<sharp>? (subst s t))) (snd P))"

text \<open>Equality reductions\<close>

inductive s_red :: "problem_type \<Rightarrow> substs \<Rightarrow> problem_type \<Rightarrow> bool"  ("_ \<turnstile> _ \<leadsto> _ " [80,80,80] 80)
  where
  unit_sred[intro!]:    "((Unit \<approx>? Unit) # xs, ys) \<turnstile> [] \<leadsto> (xs, ys)" |
  paar_sred[intro!]:    "((Paar t1 t2 \<approx>? Paar s1 s2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?s1)#(t2\<approx>?s2)#xs,ys)" |
  func_sred[intro!]:    "((Func F t1 \<approx>? Func F t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?t2)#xs,ys)" |
  abst_aa_sred[intro!]: "((Abst a t1 \<approx>? Abst a t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?t2)#xs,ys)" |
  abst_ab_sred[intro!]: "a\<noteq>b \<Longrightarrow> 
                       ((Abst a t1\<approx>?Abst b t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?swap [(a,b)] t2)#xs,(a\<sharp>?t2)#ys)" |
  atom_sred[intro!]:    "((Atom a\<approx>?Atom a)#xs,ys) \<turnstile>[]\<leadsto> (xs,ys)" |
  susp_sred[intro!]:    "((Susp pi1 X\<approx>?Susp pi2 X)#xs,ys) 
                                \<turnstile>[]\<leadsto> (xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi1 pi2))@ys)" | 
  var_1_sred[intro!]:   "\<not>(occurs X t) \<Longrightarrow> ((Susp pi X\<approx>?t)#xs,ys) 
                               \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)" |
  var_2_sred[intro!]:   "\<not>(occurs X t) \<Longrightarrow> ((t\<approx>?Susp pi X)#xs,ys) 
                               \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"

inductive_cases s_red_elims:
"((Unit \<approx>? Unit) # xs, ys) \<turnstile>[] \<leadsto> (xs, ys)"
"((Paar t1 t2 \<approx>? Paar s1 s2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?s1)#(t2\<approx>?s2)#xs,ys)"
"((Func F t1 \<approx>? Func F t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?t2)#xs,ys)"
"((Abst a t1 \<approx>? Abst a t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?t2)#xs,ys)"
"((Abst a t1\<approx>?Abst b t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?swap [(a,b)] t2)#xs,(a\<sharp>?t2)#ys)"
"((Atom a\<approx>?Atom a)#xs,ys) \<turnstile>[]\<leadsto> (xs,ys)"
"((Susp pi1 X\<approx>?Susp pi2 X)#xs,ys) \<turnstile>[]\<leadsto> (xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi1 pi2))@ys)"
"((Susp pi X\<approx>?t)#xs,ys) \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"
"((t\<approx>?Susp pi X)#xs,ys) \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"


lemma sred_symm:
  assumes "((t1 \<approx>? t2) # xs, ys) \<turnstile> s \<leadsto> P2"
  shows "\<exists> P3. ((t2 \<approx>? t1) # xs, ys) \<turnstile> s \<leadsto> P3"
  using assms
proof(cases rule: s_red.cases)
  case (var_1_sred X pi)
  have "((t2, Susp pi X) # xs,
     ys) \<turnstile> [(X, swap (rev pi) t2)] \<leadsto> apply_subst [(X, swap (rev pi) t2)] (xs, ys)"
    using var_2_sred[OF \<open>\<not> occurs X t2\<close>] by simp
  then show ?thesis using var_1_sred by blast
next
  case (var_2_sred X pi)
  have "((Susp pi X, t1) # xs,
     ys) \<turnstile> [(X, swap (rev pi) t1)] \<leadsto> apply_subst [(X, swap (rev pi) t1)] (xs, ys)"
    using var_1_sred[OF \<open>\<not> occurs X t1\<close>] by simp
  then show ?thesis using var_2_sred by blast
qed (auto)

text \<open>Weakening of freshness\<close>

lemma solution_weak:
  assumes "(nabla1, s) \<in> U P"
  shows "(nabla1 \<union> nabla3, s) \<in> U P"
  using assms
  unfolding all_solutions_def using fresh_weak equ_weak by auto

lemma solution_comp_id: 
  shows "((nabla, s) \<in> U P) = ((nabla, s \<bullet> []) \<in> U P)" and 
    "((nabla, s) \<in> U P) = ((nabla, [] \<bullet> s) \<in> U P)"
  unfolding all_solutions_def by auto

lemma solutions_subst_assoc:
   "((nabla, s1 \<bullet> (s2 \<bullet> s3)) \<in> U P) = ((nabla, (s1 \<bullet> s2) \<bullet> s3) \<in> U P)"
  unfolding all_solutions_def using subst_assoc by simp

text \<open>Freshness reductions\<close>

inductive c_red :: "problem_type \<Rightarrow> fresh_envs \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _ " [80,80,80] 80)
  where
  unit_cred[intro!]:    "([],(a \<sharp>? Unit)#xs) \<turnstile>{}\<rightarrow> ([],xs)" |
  paar_cred[intro!]:    "([],(a \<sharp>? Paar t1 t2)#xs) \<turnstile>{}\<rightarrow> ([],(a\<sharp>?t1)#(a\<sharp>?t2)#xs)" |
  func_cred[intro!]:    "([],(a \<sharp>? Func F t)#xs) \<turnstile>{}\<rightarrow> ([],(a\<sharp>?t)#xs)" |
  abst_aa_cred[intro!]: "([],(a \<sharp>? Abst a t)#xs) \<turnstile>{}\<rightarrow> ([],xs)" |
  abst_ab_cred[intro!]: "a\<noteq>b \<Longrightarrow>([],(a \<sharp>? Abst b t)#xs) \<turnstile>{}\<rightarrow> ([],(a\<sharp>?t)#xs)" |
  atom_cred[intro!]:    "a\<noteq>b \<Longrightarrow>([],(a \<sharp>? Atom b)#xs) \<turnstile>{}\<rightarrow> ([],xs)" |
  susp_cred[intro!]:    "([],(a \<sharp>? Susp pi X)#xs) \<turnstile> {((swapas (rev pi) a),X)}\<rightarrow> ([],xs)"

text\<open>It only reduces the freshness part after the equations list is empty \<close>

lemma c_red_eqs_empty:
  assumes "P1 \<turnstile> s \<rightarrow> P2"
  shows "fst P1 = []"
  using assms by (auto elim: c_red.cases)

text \<open>Unification reduction sequences\<close>

inductive red_plus :: "problem_type \<Rightarrow> unifier_type \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<Turnstile> _ \<Rightarrow> _ " [80,80,80] 80)
  where
  sred_single[intro!]: "\<lbrakk>P1\<turnstile>s1 \<leadsto> P2\<rbrakk> \<Longrightarrow> P1\<Turnstile>({},s1)\<Rightarrow>P2" |
  cred_single[intro!]: "\<lbrakk>P1\<turnstile>nabla1\<rightarrow>P2\<rbrakk> \<Longrightarrow> P1 \<Turnstile> (nabla1,[]) \<Rightarrow> P2" |
  sred_step[intro!]:   "\<lbrakk>P1\<turnstile>s1\<leadsto>P2; P2\<Turnstile>(nabla2,s2)\<Rightarrow>P3\<rbrakk> \<Longrightarrow> P1\<Turnstile>(nabla2,(s2\<bullet>s1))\<Rightarrow>P3" |
  cred_step[intro!]:   "\<lbrakk>P1\<turnstile>nabla1\<rightarrow>P2; P2\<Turnstile>(nabla2,[])\<Rightarrow>P3\<rbrakk> \<Longrightarrow> P1\<Turnstile>(nabla2\<union>nabla1,[])\<Rightarrow>P3"

text\<open>Symmetry of the reduction\<close>

lemma red_plus_symm:
assumes"P1 = ((t1 \<approx>? t2) # xs, ys)"
  and "P1 \<Turnstile> (nabla, s) \<Rightarrow> P2"
shows "\<exists> nabla1 s1 P3. ((t2 \<approx>? t1) # xs, ys) \<Turnstile> (nabla1, s1) \<Rightarrow> P3"
  using assms
proof (induction arbitrary: nabla s rule: red_plus.induct[OF assms(2)])
  case (1 P1 s1 P)
  hence "(((t1, t2) # xs, ys)) \<turnstile> s1 \<leadsto> P" by simp
  hence "\<exists> P3. ((t2 \<approx>? t1) # xs, ys) \<turnstile> s1 \<leadsto> P3"
    using sred_symm by simp
  hence "\<exists> P3. ((t2 \<approx>? t1) # xs, ys) \<Turnstile> ({}, s1) \<Rightarrow> P3" 
    using sred_single by auto
  then show "\<exists>nabla1 s1 P3. ((t2, t1) # xs, ys) \<Turnstile> (nabla1, s1) \<Rightarrow> P3" by auto
next
  case (2 P1 nabla1 P2)
  hence "fst P1 \<noteq> []" by simp
  moreover from 2(1) have "fst P1 = []"
    using c_red_eqs_empty by simp
  ultimately have False by simp
  then show ?case by simp
next
  case (3 P1 s1 P' nabla2 s2 P3)
  hence "(((t1, t2) # xs, ys)) \<turnstile> s1 \<leadsto> P'" by simp
  hence "\<exists> P3. ((t2 \<approx>? t1) # xs, ys) \<turnstile> s1 \<leadsto> P3"
    using sred_symm by simp
  hence "\<exists> P3. ((t2 \<approx>? t1) # xs, ys) \<Turnstile> ({}, s1) \<Rightarrow> P3" 
    using sred_single by auto
  then show "\<exists>nabla1 s1 P3. ((t2, t1) # xs, ys) \<Turnstile> (nabla1, s1) \<Rightarrow> P3" by auto
next
  case (4 P1 nabla1 P' nabla2 P3)
  hence "fst P1 \<noteq> []" by simp
  moreover from 4(1) have "fst P1 = []"
    using c_red_eqs_empty by simp
  ultimately have False by simp
  then show ?case by simp
qed


lemma mgu_idem: 
  assumes "(nabla1,s1) \<in> U P"
    and "\<forall>(nabla2,s2) \<in> U P. nabla2 \<Turnstile>(subst s2) nabla1 \<and>  nabla2\<Turnstile>subst(s2 \<bullet> s1)\<approx>subst s2"
  shows "mgu P (nabla1,s1) \<and> idem (nabla1,s1)"
  using assms mgu_def idem_def by auto

lemma problem_subst_comm: 
  shows "((nabla,s2) \<in> U (apply_subst s1 P)) = ((nabla,(s2\<bullet>s1))\<in>U P)"
  using all_solutions_def apply_subst_def subst_comp_expand by auto

text \<open>Preservation of solutions\<close>

lemma P1_to_P2_sred:
  assumes "(nabla1,s1) \<in> U P1" and "P1 \<turnstile>s2 \<leadsto> P2"
  shows "(nabla1,s1) \<in> U P2  \<and> (nabla1\<Turnstile>subst (s1\<bullet>s2)\<approx>subst s1)"
  using assms
proof(induction arbitrary: nabla1 s1 rule: s_red.induct[OF \<open>P1 \<turnstile> s2 \<leadsto> P2\<close>])
  case (1 xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp
   from 1
   have eqs: "\<forall> (t1,t2) \<in> set xs. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2" 
     and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t" 
     using all_solutions_def by simp_all
   with subst show ?case
     using all_solutions_def by auto
 next
   case (2 t1 t2 t3 t4 xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1\<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp

   from 2
   have fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by simp

   from 2
   have i: "\<forall> (t1,t2) \<in> set ((Paar t1 t2, Paar t3 t4) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using all_solutions_def by simp
   hence "nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t3" 
    "nabla1 \<turnstile> subst s1 t2 \<approx> subst s1 t4"
    using Equ_elims(4)[of nabla1 \<open>(subst s1 t1)\<close>  \<open>(subst s1 t2)\<close>  \<open>(subst s1 t3)\<close>  \<open>(subst s1 t4)\<close>] 
      subst_paar[of s1] by auto+
    with i have eqs:
    "\<forall> (t1,t2) \<in> set ((t1,t3)#(t2, t4) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
      by auto

    from fresh eqs subst 
    show ?case using all_solutions_def by simp
 next
   case (3 F t1 t2 xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp

   from 3
   have fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by simp

   from 3
   have i: "\<forall> (t1,t2) \<in> set ((Func F t1, Func F t2) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using all_solutions_def by simp
   hence "nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2" 
     using Equ_elims(5)[of nabla1 F \<open>subst s1 t1\<close> \<open>subst s1 t2\<close>] 
      subst_func by auto
   with i have eqs: 
     "\<forall> (t1,t2) \<in> set ((t1, t2) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     by auto

   from subst fresh eqs
   show ?case using all_solutions_def by simp
 next
   case (4 a t1 t2 xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp

   from 4
   have fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by simp

   from 4
   have i: "\<forall> (t1,t2) \<in> set ((Abst a t1, Abst a t2) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using all_solutions_def by simp
   hence "nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2" 
     using Equ_elims(6)[of nabla1 a \<open>subst s1 t1\<close> \<open>subst s1 t2\<close>] 
      subst_abst by auto
   with i have eqs: 
     "\<forall> (t1,t2) \<in> set ((t1, t2) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     by auto

   from subst fresh eqs
   show ?case using all_solutions_def by simp
 next
   case (5 a b t1 t2 xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp

   from 5
   have eqsP1: "\<forall> (t1,t2) \<in> set ((Abst a t1, Abst b t2) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using all_solutions_def by simp
   hence i: "nabla1 \<turnstile> Abst a (subst s1 t1) \<approx> Abst b (subst s1 t2)"
     using subst_abst[of s1] by simp
   
   from 5
   have ii: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by auto
   from 5 i
   have "nabla1 \<turnstile> a \<sharp> subst s1 t2"
     using Equ_elims(7) by blast
   with ii 
   have fresh: "\<forall> (a,t) \<in> set ((a,t2) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
     by simp
   
   from i 5
   have "nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 (swap [(a, b)] t2)" 
     using 5 Equ_elims(7)[of nabla1 a \<open>subst s1 t1\<close> b \<open>subst s1 t2\<close>]  
       subst_swap_comm by simp
   with eqsP1 have eqs: 
     "\<forall> (t1,t2) \<in> set ((t1, swap [(a,b)] t2) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     by auto
    
   from subst fresh eqs 
   show ?case using all_solutions_def by simp
 next
   case (6 a xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp

   from 6
   have fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by auto

   from 6
   have eqs: "\<forall> (t1,t2) \<in> set xs. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using all_solutions_def by auto
  
   from subst fresh eqs
   show ?case using all_solutions_def by simp
 next
   case (7 pi1 X pi2 xs ys)
   then have subst: "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1" 
     using equ_refl subst_equ_def by simp

   from 7
   have i: "\<forall> (t1,t2) \<in> set ((Susp pi1 X, Susp pi2 X) # xs). nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by simp+


   from 7(1)
   have "nabla1 \<turnstile> swap pi1 (look_up X s1) \<approx> swap pi2 (look_up X s1)"
     using all_solutions_def subst_susp by simp
   hence "\<forall>a\<in>ds pi1 pi2.  nabla1 \<turnstile> a \<sharp> (look_up X s1)"
     using equ_pi1_pi2_dec by simp
   hence "\<forall>a\<in> set (ds_list pi1 pi2). nabla1 \<turnstile> a \<sharp> subst s1 (Susp [] X)"
     using subst_susp ds_list_equ_ds[of pi1 pi2] by simp
   hence "\<forall> (a,t) \<in> set (map (\<lambda>a. a \<sharp>? Susp [] X) (ds_list pi1 pi2)). nabla1 \<turnstile> a \<sharp> subst s1 t"
    by (auto split: prod.splits)
   with 7 i(2)
   have fresh: 
     "\<forall> (a,t) \<in> set (map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
    by auto

   from i(1)
   have eqs:  
    "\<forall> (t1,t2) \<in> set xs. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     by simp
  
   from subst fresh eqs
   show ?case using all_solutions_def by simp
 next
   case (8 X t' pi xs ys)
   hence "nabla1 \<turnstile> subst s1 (Susp pi X) \<approx> subst s1 t'"
     using all_solutions_def[of \<open>((Susp pi X, t') # xs, ys)\<close>] by auto
   hence subst: "nabla1 \<Turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) \<approx> subst s1"
     using unif_1 by simp

   from 8
   have eqs_old:
     "\<forall>(t1,t2)\<in>set xs. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     and fresh_old:
     "\<forall>(a,t)\<in>set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
     using all_solutions_def by auto

   from eqs_old 
   have eqs: "\<forall>(t1,t2)\<in>set xs. 
    nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t1 \<approx>  subst (s1 \<bullet> [(X, swap (rev pi) t')]) t2"
     using unif_2a[OF subst] by auto

   from fresh_old 
   have fresh: "\<forall>(a,t)\<in>set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t"
     using unif_2b[OF subst] by auto

   from eqs fresh
   have "(nabla1, (s1 \<bullet> [(X, swap (rev pi) t')])) \<in> U (xs, ys)"
     using all_solutions_def by simp
   hence U: "(nabla1, s1) \<in> U (apply_subst [(X, swap (rev pi) t')] (xs, ys))"
     using problem_subst_comm by simp
   
   from subst U
   show ?case by simp
 next
   case (9 X t' pi xs ys)
   hence "nabla1 \<turnstile>  subst s1 t' \<approx> subst s1 (Susp pi X)"
     using all_solutions_def[of \<open>((t', Susp pi X) # xs, ys)\<close>] by simp
   hence subst: "nabla1 \<Turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) \<approx> subst s1 "
     using unif_1[OF equ_symm] by blast

   from 9
   have eqs_old:
    "\<forall>(t1,t2)\<in>set xs. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     and fresh_old:
    "\<forall>(a,t)\<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t"
      using all_solutions_def by auto

   from eqs_old 
   have eqs: "\<forall>(t1,t2)\<in>set xs. 
    nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t1 \<approx>  subst (s1 \<bullet> [(X, swap (rev pi) t')]) t2"
    using unif_2a[OF subst] by auto

   from fresh_old 
   have fresh: "\<forall>(a,t)\<in>set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t"
     using unif_2b[OF subst] by auto

   from eqs fresh
   have "(nabla1, (s1 \<bullet> [(X, swap (rev pi) t')])) \<in> U (xs, ys)"
     using all_solutions_def by simp
   hence U: "(nabla1, s1) \<in> U (apply_subst [(X, swap (rev pi) t')] (xs, ys))"
     using problem_subst_comm by simp

   from subst U
  show ?case by simp
qed

text \<open>Auxiliary lemma for completeness\<close>

lemma P1_from_P2_sred: 
  assumes "(nabla1,s1)\<in> U P2" and "P1\<turnstile>s2\<leadsto>P2"
  shows "(nabla1,s1\<bullet>s2)\<in> U P1"
 using assms
proof(induction arbitrary: nabla1 s1 rule: s_red.induct[OF \<open>P1 \<turnstile> s2 \<leadsto> P2\<close>])
  case (1 xs ys)
  hence "\<forall> (t1,t2) \<in> set xs. nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
     and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    using all_solutions_def by simp_all
  hence eqs: 
    "\<forall> (t1,t2) \<in> set ((Unit, Unit) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
    using subst_unit[of \<open>(s1 \<bullet> [])\<close>] equ_refl[of nabla1 Unit] by auto
  from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (2 t1 t2 t3 t4 xs ys)
   hence eqs_old: "\<forall> (t1,t2) \<in> set ((t1, t3) # (t2, t4) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
     and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
     using all_solutions_def by simp_all
   hence "nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t3" 
     "nabla1 \<turnstile> subst (s1 \<bullet> []) t2 \<approx> subst (s1 \<bullet> []) t4" by simp_all
   hence "nabla1 \<turnstile> subst (s1 \<bullet> []) (Paar t1 t2) \<approx> subst (s1 \<bullet> []) (Paar t3 t4)"
     using equ_paar by simp
   with eqs_old have eqs:
     "\<forall> (t1,t2) \<in> set ((Paar t1 t2, Paar t3 t4) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
     by auto
   from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (3 f t1 t2 xs ys)
  hence eqs_old: "\<forall> (t1,t2) \<in> set ((t1, t2) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
     and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    using all_solutions_def by simp_all
  hence "nabla1 \<turnstile> subst (s1 \<bullet> []) (Func f t1) \<approx> subst (s1 \<bullet> []) (Func f t2)"
    using equ_func by simp
  with eqs_old have eqs:
     "\<forall> (t1,t2) \<in> set ((Func f t1, Func f t2) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
     by auto
  from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (4 a t1 t2 xs ys)
  hence eqs_old: "\<forall> (t1,t2) \<in> set ((t1, t2) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
     and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    using all_solutions_def by simp_all
  hence "nabla1 \<turnstile> subst (s1 \<bullet> []) (Abst a t1) \<approx> subst (s1 \<bullet> []) (Abst a t2)"
    using equ_abst_aa by simp
  with eqs_old have eqs:
     "\<forall> (t1,t2) \<in> set ((Abst a t1, Abst a t2) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
     by auto
  from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (5 a b t1 t2 xs ys)
  hence eqs_old: "\<forall> (t1,t2) \<in> set ((t1, swap [(a, b)] t2) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
    and fresh: "\<forall> (a,t) \<in> set ((a, t2) # ys). nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    using all_solutions_def by simp_all
  hence "nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> swap [(a, b)] (subst (s1 \<bullet> []) t2)"
      "nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t2" 
    using subst_swap_comm[of \<open>(s1 \<bullet> [])\<close> \<open>[(a, b)]\<close> t2] by simp_all
  hence "nabla1 \<turnstile> subst (s1 \<bullet> []) (Abst a t1) \<approx> subst (s1 \<bullet> []) (Abst b t2)"
    using equ_abst_ab[OF 5(1) \<open>nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t2\<close>] subst_abst by simp
  with eqs_old have eqs:
     "\<forall> (t1,t2) \<in> set ((Abst a t1, Abst b t2) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
     by auto
  from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (6 a xs ys)
  hence "\<forall> (t1,t2) \<in> set xs. nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
     and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    using all_solutions_def by simp_all
  hence eqs: 
    "\<forall> (t1,t2) \<in> set ((Atom a, Atom a) # xs). nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
    using subst_unit[of \<open>(s1 \<bullet> [])\<close>] equ_refl[of nabla1 Unit] by auto
  from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (7 pi1 X pi2 xs ys)
  hence eqs_old: "\<forall> (t1,t2) \<in> set xs. nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2" 
     and fresh_old: 
     "\<forall> (a,t) \<in> set (map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys). nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    using all_solutions_def by simp_all
  hence "\<forall>c\<in> set (ds_list pi1 pi2). nabla1 \<turnstile> c \<sharp> subst (s1 \<bullet> []) (Susp [] X)"
    by (auto split: prod.splits)
  hence "\<forall>c \<in> ds pi1 pi2. nabla1 \<turnstile> c \<sharp> subst (s1 \<bullet> []) (Susp [] X)"
    using ds_list_equ_ds by simp
  hence "\<forall>c \<in> ds pi1 pi2. nabla1 \<turnstile> c \<sharp> (look_up X (s1 \<bullet> []))"
    using subst_susp[of \<open>(s1 \<bullet> [])\<close> \<open>[]\<close> X] swap_id by simp
  hence "nabla1 \<turnstile> subst (s1 \<bullet> []) (Susp pi1 X) \<approx> subst (s1 \<bullet> []) (Susp pi2 X)"
    using  equ_equiv_pi subst_susp[of \<open>(s1 \<bullet> [])\<close> _ X] by auto
  with eqs_old fresh_old have
  eqs: "\<forall> (t1,t2) \<in> set ((Susp pi1 X, Susp pi2 X)#xs). 
    nabla1 \<turnstile> subst (s1 \<bullet> []) t1 \<approx> subst (s1 \<bullet> []) t2"
  and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> []) t"
    by simp_all
  then show ?case 
    using all_solutions_def by simp
next
  case (8 X t' pi xs ys)
  hence "(nabla1, s1 \<bullet> [(X, swap (rev pi) t')]) \<in> U (xs, ys)"
    using problem_subst_comm by simp
  hence eqs_old: 
    "\<forall> (t1,t2) \<in> set xs. 
    nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t1 \<approx> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t2"
  and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t"
    using all_solutions_def by simp_all

  have "subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X) = subst s1 (swap pi (swap (rev pi) t'))"
    using subst_susp subst_swap_comm subst_comp_expand eq_fst_iff look_up.simps(2) snd_eqD by metis
  also have "... = swap pi (swap (rev pi) (subst s1 t'))"
    using subst_swap_comm by simp
  hence "nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X) \<approx> subst s1 t'"
    using equ_refl calculation rev_pi_pi_equ[of nabla1 pi \<open>subst s1 t'\<close>]
      equ_trans[of nabla1 \<open>subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X)\<close> 
        \<open>swap (rev pi) (swap pi (subst s1 t'))\<close> \<open>subst s1 t'\<close>]
       swap_inv_side by auto

  with 8 eqs_old
  have eqs: "\<forall> (t1,t2) \<in> set ((Susp pi X, t')#xs). 
    nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t1 \<approx> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t2"
    using subst_comp_expand subst_not_occurs by simp

  from fresh eqs show ?case
    using all_solutions_def by simp
next
  case (9 X t' pi xs ys)
  hence "(nabla1, s1 \<bullet> [(X, swap (rev pi) t')]) \<in> U (xs, ys)"
    using problem_subst_comm by simp
  hence eqs_old: 
    "\<forall> (t1,t2) \<in> set xs. 
    nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t1 \<approx> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t2"
  and fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t"
    using all_solutions_def by simp_all

  have "subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X) = subst s1 (swap pi (swap (rev pi) t'))"
    using subst_susp subst_swap_comm subst_comp_expand eq_fst_iff look_up.simps(2) snd_eqD by metis
  also have "... = swap pi (swap (rev pi) (subst s1 t'))"
    using subst_swap_comm by simp
  hence "nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X) \<approx> subst s1 t'"
    using equ_refl calculation rev_pi_pi_equ[of nabla1 pi \<open>subst s1 t'\<close>]
      equ_trans[of nabla1 \<open>subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X)\<close> 
        \<open>swap (rev pi) (swap pi (subst s1 t'))\<close> \<open>subst s1 t'\<close>]
       swap_inv_side by auto
  hence "nabla1 \<turnstile> subst s1 t' \<approx> subst (s1 \<bullet> [(X, swap (rev pi) t')]) (Susp pi X)"
    using equ_symm by simp

  with 9 eqs_old
  have eqs: "\<forall> (t1,t2) \<in> set ((t', Susp pi X)#xs). 
    nabla1 \<turnstile> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t1 \<approx> subst (s1 \<bullet> [(X, swap (rev pi) t')]) t2"
    using subst_comp_expand subst_not_occurs by simp

  from fresh eqs show ?case
    using all_solutions_def by simp
qed

lemma P1_to_P2_cred: 
  assumes "(nabla1,s1)\<in> U P1"
  and "P1 \<turnstile>nabla2 \<rightarrow> P2"
shows "(nabla1,s1)\<in> U P2  \<and> (nabla1\<Turnstile>(subst s1) nabla2)"
  using assms
proof(induction arbitrary: nabla1 s1 rule: c_red.induct[OF \<open>P1 \<turnstile>nabla2\<rightarrow> P2\<close>])
  case (2 a t1 t2 ys)
  hence fresh_old: "\<forall> (a,t) \<in> set ((a, Paar t1 t2) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
    and eqs: "\<forall> (t1,t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by simp_all
  hence "nabla1 \<turnstile> a \<sharp> subst s1 (Paar t1 t2)" 
    by simp
  hence "nabla1 \<turnstile> a \<sharp> subst s1 t1" "nabla1 \<turnstile> a \<sharp> subst s1 t2"
    using Fresh_elims(5)[of nabla1 a \<open>subst s1 t1\<close>
        \<open>subst s1 t2\<close>] by auto
  with fresh_old have
   fresh: "\<forall> (a,t) \<in> set ((a, t1) # (a, t2) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
    by auto
  from fresh eqs
  show ?case
    using all_solutions_def ext_subst_def by simp
next
  case (3 a f t ys)
  hence fresh_old: "\<forall> (a,t) \<in> set ((a, Func f t) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
    and eqs: "\<forall> (t1,t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by simp_all
  hence "nabla1 \<turnstile> a \<sharp> subst s1 (Func f t)" 
    by simp
  hence "nabla1 \<turnstile> a \<sharp> subst s1 t" 
    using Fresh_elims(6) by auto
  with fresh_old have
   fresh: "\<forall> (a,t) \<in> set ((a, t) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
    by auto
  from fresh eqs
  show ?case
    using all_solutions_def ext_subst_def by simp
next
  case (5 a b t ys)
  hence fresh_old: "\<forall> (a,t') \<in> set ((a, Abst b t) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t'"
    and eqs: "\<forall> (t1,t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by simp_all
  hence "nabla1 \<turnstile> a \<sharp> subst s1 (Abst b t)"
    by simp
  hence "nabla1 \<turnstile> a \<sharp> subst s1 t"
    using 5 Fresh_elims(1)[of nabla1 a b \<open>subst s1 t\<close>] by auto
  with fresh_old have
  fresh: "\<forall> (a,t') \<in> set ((a, t) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t'"
    by auto
  from fresh eqs
  show ?case
    using all_solutions_def ext_subst_def by simp
next
  case (7 b pi X ys)
  hence fresh_old: "\<forall> (a,t) \<in> set ((b, Susp pi X) # ys). nabla1 \<turnstile> a \<sharp> subst s1 t"
    and eqs: "\<forall> (t1,t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by simp_all
  hence fresh: "\<forall> (a,t) \<in> set ys. nabla1 \<turnstile> a \<sharp> subst s1 t" by simp
  from fresh_old have
  "nabla1 \<turnstile> b \<sharp> subst s1 (Susp pi X)" by simp
  hence "nabla1 \<turnstile> swapas (rev pi) b \<sharp> subst s1 (Susp [] X)"
    using fresh_swap_left subst_susp by simp
  hence ext: "nabla1 \<Turnstile> (subst s1) {(swapas (rev pi) b, X)}"
    using ext_subst_def by simp
  from fresh eqs ext
    show ?case using all_solutions_def by simp
qed (auto simp add: all_solutions_def ext_subst_def)

lemma P1_from_P2_cred:
  assumes "(nabla1,s1)\<in>U P2"
    and "P1 \<turnstile>nabla2\<rightarrow> P2" and "nabla3\<Turnstile>(subst s1) nabla2"
  shows "(nabla1\<union>nabla3,s1)\<in> U P1" 
  using assms
proof(induction arbitrary: nabla1 s1 rule: c_red.induct[OF \<open>P1 \<turnstile>nabla2\<rightarrow> P2\<close>])
  case (2 a t1 t2 xs)
  hence fresh_old:
    "\<forall>(b,t)\<in>set ((a,t1)#(a,t2)#xs). nabla1 \<turnstile> b \<sharp> subst s1 t"
    and "\<forall> (t1, t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by auto
  hence weak1: "\<forall>(b,t)\<in>set xs. (nabla1 \<union> nabla3) \<turnstile> b \<sharp> subst s1 t"
        "\<forall> (t1, t2) \<in> set []. (nabla1 \<union> nabla3) \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using fresh_weak by auto
  from fresh_old have "nabla1 \<turnstile> a \<sharp> subst s1 t1" "nabla1 \<turnstile> a \<sharp> subst s1 t2"
    by simp+
  hence "nabla1 \<turnstile> a \<sharp> subst s1 (Paar t1 t2)"
    using fresh_paar subst_paar by auto
  hence "(nabla1 \<union> nabla3) \<turnstile> a \<sharp> subst s1 (Paar t1 t2)"
    using fresh_weak by auto
  with weak1
  have fresh: "\<forall>(b,t)\<in>set ((a,Paar t1 t2)#xs). (nabla1 \<union> nabla3) \<turnstile> b \<sharp> subst s1 t"
    by simp
  with weak1(2) show ?case 
    using all_solutions_def ext_subst_def by simp
next
  case (3 a f t' xs)
  hence fresh_old:
    "\<forall>(b,t)\<in>set ((a,t')#xs). nabla1 \<turnstile> b \<sharp> subst s1 t"
    and "\<forall> (t1, t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by auto
  hence weak1: "\<forall>(b,t)\<in>set xs. (nabla1 \<union> nabla3) \<turnstile> b \<sharp> subst s1 t"
        "\<forall> (t1, t2) \<in> set []. (nabla1 \<union> nabla3) \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using fresh_weak by auto
  from fresh_old have "nabla1 \<turnstile> a \<sharp> subst s1 t'" 
    by simp
  hence "nabla1 \<turnstile> a \<sharp> subst s1 (Func f t')"
    using fresh_paar subst_paar by auto
  hence "(nabla1 \<union> nabla3) \<turnstile> a \<sharp> subst s1 (Func f t')"
    using fresh_weak by auto
  with weak1
  have fresh: "\<forall>(b,t)\<in>set ((a, Func f t')#xs). (nabla1 \<union> nabla3) \<turnstile> b \<sharp> subst s1 t"
    by simp
  with weak1(2) show ?case 
    using all_solutions_def ext_subst_def by simp
next
  case (5 a b t' xs)
   hence fresh_old:
    "\<forall>(c,t)\<in>set ((a,t')#xs). nabla1 \<turnstile> c \<sharp> subst s1 t"
    and "\<forall> (t1, t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using all_solutions_def by auto
   hence weak1: "\<forall>(c,t)\<in>set xs. (nabla1 \<union> nabla3) \<turnstile> c \<sharp> subst s1 t"
      "\<forall> (t1, t2) \<in> set []. (nabla1 \<union> nabla3) \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using fresh_weak by auto
   from fresh_old have "nabla1 \<turnstile> a \<sharp> subst s1 t'" 
     by simp
   hence "nabla1 \<turnstile> a \<sharp> subst s1 (Abst b t')"
   using fresh_abst_ab[OF \<open>nabla1 \<turnstile> a \<sharp> subst s1 t'\<close> 5(1)] subst_abst by auto
   hence "(nabla1 \<union> nabla3) \<turnstile> a \<sharp> subst s1 (Abst b t')"
     using fresh_weak by auto
   with weak1
   have fresh: "\<forall>(b,t)\<in>set ((a, Abst b t')#xs). (nabla1 \<union> nabla3) \<turnstile> b \<sharp> subst s1 t"
     by simp
   with weak1(2) show ?case 
     using all_solutions_def ext_subst_def by simp
next
  case (7 b pi X xs)
  hence fresh_old: "\<forall> (a,t) \<in> set xs. nabla1 \<turnstile> a \<sharp> subst s1 t"
    and eqs: "\<forall> (t1,t2) \<in> set []. nabla1 \<turnstile> subst s1 t1 \<approx> subst s1 t2"
    using all_solutions_def by simp_all
  hence weak1: "\<forall>(a,t)\<in>set xs. (nabla1 \<union> nabla3) \<turnstile> a \<sharp> subst s1 t"
      "\<forall> (t1, t2) \<in> set []. (nabla1 \<union> nabla3) \<turnstile> subst s1 t1 \<approx> subst s1 t2"
     using fresh_weak by auto
  from 7 have "nabla3 \<turnstile> swapas (rev pi) b \<sharp> subst s1 (Susp [] X)"
    using ext_subst_def by auto
  hence "nabla3 \<turnstile> b \<sharp> subst s1 (Susp pi X)"
    using fresh_swap_right subst_susp by auto
  hence weak2: "(nabla1 \<union> nabla3) \<turnstile> b \<sharp> subst s1 (Susp pi X)"
    using fresh_weak[of nabla3 b _ nabla1] Un_commute[of nabla3 nabla1] by auto
  with weak1(1) 
  have "\<forall>(a,t)\<in>set ((b,Susp pi X)#xs). (nabla1 \<union> nabla3) \<turnstile> a \<sharp> subst s1 t"
    by simp
  with weak2 show ?case 
    using ext_subst_def all_solutions_def by simp
qed (auto simp add: ext_subst_def all_solutions_def fresh_weak)

lemma P1_to_P2_red_plus1: 
  assumes "P1 \<Turnstile> (nabla,s) \<Rightarrow> P2"
  and "(nabla1,s1) \<in> U P1"
  shows "(nabla1,s1) \<in> U P2"
  using assms
proof(induction P1\<equiv>"P1" nabla\<equiv>"(nabla, s)" P2\<equiv>"P2" arbitrary: s nabla1 nabla s1 P1 P2 rule: red_plus.induct)
  case (sred_single P1 s P2 nabla1 s1)
  have "P1 \<turnstile> s \<leadsto> P2" "(nabla1, s1) \<in> U P1" by fact+
  then show "(nabla1, s1) \<in> U P2"
    using P1_to_P2_sred by blast
next
  case (cred_single P1 nabla1 P2 nabla2 s1)
  have "P1 \<turnstile> nabla1 \<rightarrow>P2" "(nabla2, s1) \<in> U P1" by fact+
  then show "(nabla2, s1) \<in> U P2"
    using P1_to_P2_cred by blast
next
  case (sred_step P1 s P2 nabla2 s2 P3 nabla1 s1)
  have "P1 \<turnstile> s \<leadsto> P2" and "(nabla1, s1) \<in> U P1" by fact+
  then have "(nabla1, s1) \<in> U P2" using P1_to_P2_sred by blast 
  moreover 
  have IH: "(nabla1, s1) \<in> U P2 \<Longrightarrow> (nabla1, s1) \<in> U P3" by fact
  ultimately 
  show "(nabla1, s1) \<in> U P3" by simp 
next
  case (cred_step P1 nabla1 P2 nabla2 P3 nabla3 s1)
  have "P1 \<turnstile> nabla1 \<rightarrow> P2" and "(nabla3, s1) \<in> U P1" by fact+
  then have "(nabla3, s1) \<in> U P2" using P1_to_P2_cred by blast 
  moreover 
  have IH: "(nabla3, s1) \<in> U P2 \<Longrightarrow> (nabla3, s1) \<in> U P3" by fact
  ultimately show "(nabla3, s1) \<in> U P3" by simp
qed

lemma P1_to_P2_red_plus3: 
  assumes "P1 \<Turnstile> (nabla,s) \<Rightarrow> P2"
  and "(nabla1,s1)\<in> U P1"
  shows "nabla1\<Turnstile>(subst s1) nabla"
  using assms
proof(induction P1\<equiv>"P1" nabla\<equiv>"(nabla, s)" P2\<equiv>"P2" arbitrary: s nabla1 nabla s1 P1 P2 rule: red_plus.induct)
  case (sred_single P1 s P2 nabla1 s1)
  then show "nabla1 \<Turnstile> (subst s1) {}" by (simp add: ext_subst_def) 
next
  case (cred_single P1 nabla1 P2 nabla2 s1)
  have "P1  \<turnstile> nabla1 \<rightarrow> P2" "(nabla2, s1) \<in> U P1" by fact+
  then show "nabla2 \<Turnstile> (subst s1) nabla1" using P1_to_P2_cred by blast
next
  case (sred_step P1 s P2 nabla2 s2 P3 nabla1 s1)
  have "P1  \<turnstile> s \<leadsto> P2" "(nabla1, s1)\<in> U P1" by fact+ 
  then have "(nabla1, s1)\<in> U P2" using P1_to_P2_sred by blast 
  moreover have IH: "(nabla1, s1)\<in> U P2 \<Longrightarrow>  nabla1 \<Turnstile> (subst s1) nabla2" by fact 
  ultimately show "nabla1 \<Turnstile> (subst s1) nabla2" by simp 
next
  case (cred_step P1 nabla1 P2 nabla2 P3 nabla3 s1)
  have IH: "(nabla3, s1) \<in> U P2 \<Longrightarrow> nabla3 \<Turnstile> (subst s1) nabla2" by fact
  have as: "P1 \<turnstile> nabla1 \<rightarrow> P2" "(nabla3, s1) \<in> U P1" by fact+ 
  
  from as have "nabla3 \<Turnstile> (subst s1) nabla1" using P1_to_P2_cred by blast    
  moreover 
  from as have "(nabla3, s1) \<in> U P2" using P1_to_P2_cred by blast 
  then have "nabla3 \<Turnstile> (subst s1) nabla2" using IH by blast
  ultimately show "nabla3 \<Turnstile> (subst s1) (nabla2 \<union> nabla1)"
    by(auto simp add: ext_subst_def)
qed

lemma P1_to_P2_red_plus2:
  assumes "P1 \<Turnstile> (nabla, s) \<Rightarrow> P2"
  and "(nabla1, s1) \<in> U P1"
shows "nabla1 \<Turnstile> subst (s1 \<bullet> s) \<approx> subst s1"
  using assms
proof(induction P1\<equiv>"P1" nablas\<equiv>"(nabla, s)" P2\<equiv>"P2" arbitrary: s nabla1 nabla s1 P1 P2 rule: red_plus.induct)
  case (sred_single P1 s P2 nabla1 s1)
  have "P1 \<turnstile>s \<leadsto>P2" "(nabla1, s1) \<in> U P1" by fact+
  then show "nabla1 \<Turnstile> subst (s1 \<bullet> s) \<approx>subst s1"
    using P1_to_P2_sred by blast
next
  case (cred_single P1 nabla1 P2 nabla2 s1)
  show "nabla2 \<Turnstile> subst (s1 \<bullet> []) \<approx>subst s1"
    by (simp add: subst_equ_refl) 
next
  case (sred_step P1 s P2 nabla2 s2 P3 nabla1 s1)
  have IH: "(nabla1, s1) \<in> U P2 \<Longrightarrow>  nabla1 \<Turnstile> subst (s1 \<bullet> s2) \<approx>subst s1" by fact
  have as: "P1 \<turnstile>s \<leadsto>P2" "(nabla1, s1) \<in> U P1" by fact+

  from as have "(nabla1, s1) \<in> U P2" using P1_to_P2_sred by blast 
  with IH have "nabla1 \<Turnstile> subst (s1 \<bullet> s2) \<approx> subst s1" by blast
  then have "nabla1 \<Turnstile> subst ((s1 \<bullet> s2) \<bullet> s) \<approx> subst (s1 \<bullet> s)"
    by (simp add: subst_cancel_right)  
  moreover
  from as have "nabla1 \<Turnstile> subst (s1 \<bullet> s) \<approx>subst s1"
    using P1_to_P2_sred by blast 
  ultimately
  show "nabla1 \<Turnstile> subst (s1 \<bullet> (s2 \<bullet> s)) \<approx> subst s1"
    using subst_assoc subst_trans by metis
next
  case (cred_step P1 nabla1 P2 nabla2 P3)
  show "nabla1 \<Turnstile> subst (s1 \<bullet> []) \<approx> subst s1"
    by (simp add: subst_equ_refl)
qed

lemma P1_from_P2_red_plus:
  assumes "P1 \<Turnstile>(nabla,s)\<Rightarrow>P2"
    and "(nabla1,s1)\<in> U P2" and "nabla3\<Turnstile>(subst s1)(nabla)"
  shows "(nabla1\<union>nabla3,(s1 \<bullet> s))\<in> U P1"
  using assms
proof(induction P1 \<equiv> "P1" nablas\<equiv>"(nabla, s)" P2\<equiv>"P2" arbitrary: s nabla1 nabla nabla3 s1 P1 P2 rule: red_plus.induct)
  case (sred_single P1 s P2 nabla1 nabla3)
  have "P1 \<turnstile> s \<leadsto> P2" "(nabla1, s1) \<in> U P2" by fact+
  then have "(nabla1, s1 \<bullet> s) \<in> U P1"
    using P1_from_P2_sred by simp
  then show "(nabla1 \<union> nabla3, s1 \<bullet> s) \<in> U P1"
    using P1_from_P2_sred solution_weak by simp
next
  case (cred_single P1 nabla P2 nabla1 nabla3)
  have "P1 \<turnstile> nabla \<rightarrow> P2"
      "(nabla1, s1) \<in> U P2" 
      "nabla3 \<Turnstile> (subst s1) nabla" by fact+
  hence "(nabla1 \<union> nabla3, s1) \<in> U P1"
    using P1_from_P2_cred by simp
  then show "(nabla1 \<union> nabla3, s1 \<bullet> []) \<in> U P1"
    using solution_comp_id by auto
next
  case (sred_step P1 s P2 nabla2 s2 P3 nabla1 nabla3)
  have IH: "(nabla1, s1) \<in> U P3 \<Longrightarrow>
     nabla3 \<Turnstile> (subst s1) nabla2  \<Longrightarrow> (nabla1 \<union> nabla3, s1 \<bullet> s2) \<in> U P2" by fact+
  have as: "(nabla1, s1) \<in> U P3" 
    "nabla3 \<Turnstile> (subst s1) nabla2" 
    "P1 \<turnstile> s \<leadsto> P2" by fact+
  hence "(nabla1 \<union> nabla3, s1 \<bullet> s2) \<in> U P2"
    using IH by simp
  hence "(nabla1 \<union> nabla3, (s1 \<bullet> s2) \<bullet> s) \<in> U P1"
    using as(3)
    by (simp add: P1_from_P2_sred)
  then show "(nabla1 \<union> nabla3, s1 \<bullet> (s2 \<bullet> s)) \<in> U P1"
    using solutions_subst_assoc by simp
next
  case (cred_step P1 nabla P2 nabla2 P3)
  have IH: "(nabla1, s1) \<in> U P3 \<Longrightarrow>
     nabla3 \<Turnstile> (subst s1) nabla2  \<Longrightarrow> (nabla1 \<union> nabla3, s1 \<bullet> []) \<in> U P2" by fact
  have as: "P1 \<turnstile> nabla \<rightarrow> P2"
           "(nabla1, s1) \<in> U P3"
           "nabla3 \<Turnstile> (subst s1) (nabla2 \<union> nabla)" by fact+
  have ext_substs: "nabla3 \<Turnstile> (subst s1) (nabla2)" 
    "nabla3 \<Turnstile> (subst s1) nabla"
    using ext_subst_strong[OF as(3)] by simp+
  hence a: "(nabla1 \<union> nabla3, s1 \<bullet> []) \<in> U P2"
    using IH as(2) by simp
  hence "(nabla1 \<union> nabla3 \<union> nabla3, s1 \<bullet> []) \<in> U P1"
    using as(1) ext_substs(2) P1_from_P2_cred solution_comp_id by blast
  then show "(nabla1 \<union> nabla3, s1 \<bullet> []) \<in> U P1"
    unfolding all_solutions_def using Un_absorb by simp
qed

lemma mgu: 
  assumes "P \<Turnstile>(nabla,s)\<Rightarrow>([],[])"
  shows "mgu P (nabla,s) \<and> idem (nabla,s)"
proof(rule mgu_idem)
  have i: "({},[]) \<in> U ([],[])"
    unfolding all_solutions_def by simp
  then show "(nabla, s) \<in> U P"
    using P1_from_P2_red_plus[OF assms i] 
      ext_subst_id  solution_comp_id(2) by simp
                            
  show "\<forall>(nabla2, s2)\<in> U P.  nabla2 \<Turnstile> (subst s2) nabla \<and>  
                       nabla2 \<Turnstile> subst (s2 \<bullet> s) \<approx> subst s2"
  proof
    fix x
    assume "x \<in> U P"
    then show "case x of (nabla2, s2) \<Rightarrow> 
               nabla2 \<Turnstile> (subst s2) nabla \<and>  
                       nabla2 \<Turnstile> subst (s2 \<bullet> s) \<approx> subst s2"
    proof (cases x)
      case (Pair nabla2 s2)
      hence "(nabla2,s2) \<in> U P"
        using \<open>x \<in> U P\<close> by auto
      hence "nabla2 \<Turnstile> (subst s2) nabla \<and> nabla2 \<Turnstile> subst (s2 \<bullet> s) \<approx> subst s2"
        using assms P1_to_P2_red_plus2 P1_to_P2_red_plus3 by auto+
      with Pair show ?thesis by simp
    qed
  qed
qed



(*<*)
end
(*>*)