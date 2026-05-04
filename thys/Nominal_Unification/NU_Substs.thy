(*<*)
theory NU_Substs
imports NU_Equ
begin
(*>*)

section \<open>Substitutions\<close>

text \<open>
  Defines substitutions and composition of substitutions, and establishes some 
  facts of substitution and the equivalence relation.
\<close>

type_synonym substs = "(string \<times> trm) list"

fun look_up :: "string \<Rightarrow> substs \<Rightarrow> trm" where
  "look_up X []     = Susp [] X" |
  "look_up X (x#xs) = (if (X = fst x) then (snd x) else look_up X xs)"

fun subst :: "substs \<Rightarrow> trm \<Rightarrow> trm" where
  subst_unit: "subst s (Unit)          = Unit" |
  subst_susp: "subst s (Susp pi X)     = swap pi (look_up X s)" |
  subst_atom: "subst s (Atom a)        = Atom a" |
  subst_abst: "subst s (Abst a t)      = Abst a (subst s t)" |
  subst_paar: "subst s (Paar t1 t2)    = Paar (subst s t1) (subst s t2)" |
  subst_func: "subst s (Func F t)      = Func F (subst s t)"

declare subst_susp [simp del]

text \<open>
 The notion of composition of substitutions (adapted from Martin Coen's Classical 
 Computational Logic).
\<close>

fun alist_rec :: "substs \<Rightarrow> substs \<Rightarrow> (string\<Rightarrow>trm\<Rightarrow>substs\<Rightarrow>substs\<Rightarrow>substs) \<Rightarrow> substs" where
  "alist_rec [] c d = c" |
  "alist_rec (p # al) c d = d (fst p) (snd p) al (alist_rec al c d)"

definition comp ::  "substs \<Rightarrow> substs \<Rightarrow> substs" (infixl \<open>\<bullet>\<close> 81) where
 "s1 \<bullet> s2 \<equiv> alist_rec s2 s1 (\<lambda> x y xs g. (x,subst s1 y) # g)"

text \<open>
  The domain of substitutions.
\<close>

definition domn :: "(trm \<Rightarrow> trm) \<Rightarrow> string set" where
  "domn s \<equiv> {X. (s (Susp [] X)) \<noteq> (Susp [] X)}" 

text \<open>
  substitutions extend freshness environments.
\<close>

definition ext_subst :: "fresh_envs \<Rightarrow> (trm \<Rightarrow> trm) \<Rightarrow> fresh_envs \<Rightarrow> bool" (" _ \<Turnstile> _ _ " [80,80,80] 80) where
  "nabla1 \<Turnstile> s nabla2 \<equiv> (\<forall>(a,X)\<in>nabla2. nabla1\<turnstile>a\<sharp> s (Susp [] X))"

text \<open>
  Alpha-equality for substitutions 
\<close>

definition subst_equ :: "fresh_envs \<Rightarrow> (trm\<Rightarrow>trm) \<Rightarrow> (trm\<Rightarrow>trm) \<Rightarrow> bool" (" _ \<Turnstile> _ \<approx> _" [80,80,80] 80)
  where
  "nabla \<Turnstile> s1 \<approx> s2 \<equiv>  \<forall>X\<in>(domn s1\<union>domn s2). (nabla \<turnstile> s1 (Susp [] X) \<approx> s2 (Susp [] X))"

lemma subst_equ_symm: 
  assumes "nabla \<Turnstile> s1 \<approx> s2"
  shows "nabla \<Turnstile> s2 \<approx> s1"
  using assms equ_symm subst_equ_def[of nabla s1 s2]
    subst_equ_def[of nabla s2 s1] Un_commute[of \<open>domn s1\<close> \<open>domn s2\<close>] by blast

lemma subst_equ_refl:
  shows "nabla \<Turnstile> s \<approx> s"
  using equ_refl subst_equ_def Un_absorb by simp

lemma not_in_domn: 
  assumes "X \<notin> (domn s)"
  shows "s (Susp [] X) = (Susp [] X)"
  using assms domn_def by simp

lemma subst_swap_comm: 
  shows "subst s (swap pi t) = swap pi (subst s t)"
  using swap_append subst_susp by (induct t) auto

lemma subst_not_occurs: 
  assumes "\<not>(occurs X t)"
  shows "subst [(X,t2)] t = t"
proof-
  have i: "\<not>(occurs X t) \<longrightarrow> subst [(X,t2)] t = t"
    using subst_susp by (induct t) auto
  then show ?thesis using assms by simp
qed

lemma id_subst [simp]: 
  shows "subst [] t = t"
  using subst_susp by (induct t) auto

lemma subst_comp_id [simp]: 
  shows "subst (s \<bullet> []) = subst s"
  using comp_def by simp

lemma id_comp_subst [simp]: 
  shows "subst ([] \<bullet> s) = subst s"
proof(rule ext)
  fix t
  show "subst ([] \<bullet> s) t = subst s t"
  proof(induction t arbitrary: s)
    case (Susp pi X)
    then show ?case using comp_def subst_susp
    proof (induction s)
      case Nil
      then show ?case
        using comp_def subst_susp by simp
    next
      case (Cons a s)
      then show ?case 
        using comp_def subst_susp by simp
    qed
  qed (simp_all)
qed

lemma subst_comp_expand: 
  shows "subst (s1 \<bullet> s2) t = subst s1 (subst s2 t)"
proof(induct t)
  case (Susp x1 x2)
  then show ?case 
   proof(induct s2)
      case Nil
      then show ?case using comp_def subst_susp subst_swap_comm by simp
   next
    case (Cons a s2)
    then show ?case using comp_def subst_susp subst_swap_comm by simp
  qed
qed (simp_all)

lemma subst_assoc: 
  shows "subst (s1 \<bullet> (s2 \<bullet> s3)) = subst ((s1 \<bullet> s2) \<bullet> s3)"
proof(rule ext)
  fix t 
  show "subst (s1 \<bullet> (s2 \<bullet> s3)) t = subst (s1 \<bullet> s2 \<bullet> s3) t"
  proof(induct t)
    case (Susp pi X)
    then show ?case using subst_comp_expand by simp
  qed (simp_all)
qed

lemma fresh_subst:
  assumes "nabla1 \<turnstile> a \<sharp> t"
    and "nabla2 \<Turnstile> (subst s) nabla1"
  shows "nabla2 \<turnstile> a \<sharp> subst s t"
  using assms
proof(induction rule: fresh.induct)
  case (fresh_susp pi a X nabla)
  then show ?case 
    using ext_subst_def subst_susp fresh_swap_right 
    by auto
qed (auto)

lemma equ_subst:
  assumes "nabla1\<turnstile> t1 \<approx>t2"
    and "nabla2 \<Turnstile> (subst s) nabla1"
  shows "nabla2 \<turnstile>(subst s t1)\<approx>(subst s t2)"
  using assms
proof(induction rule: equ.induct)
  case (equ_abst_ab a b nabla t2 t1)
  then show ?case 
    using subst_swap_comm fresh_subst equ.equ_abst_ab by simp 
next
  case (equ_susp pi1 pi2 X nabla)
  then show ?case 
    using subst_susp equ_pi1_pi2_add ext_subst_def subst_susp
    by fastforce
qed (auto)

lemma unif_1: 
  assumes "nabla \<turnstile> subst s (Susp pi X) \<approx> subst s t"
  shows "nabla \<Turnstile> subst (s \<bullet> [(X, swap (rev pi) t)]) \<approx> subst s"
  using assms
  apply(simp only: subst_equ_def)
proof
  fix Xa
  assume hyps: "nabla \<turnstile> subst s (Susp pi X) \<approx> subst s t"
   "Xa \<in> domn (subst (s \<bullet> [(X, swap (rev pi) t)])) \<union> domn (subst s)"
  show "nabla \<turnstile> subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa) \<approx> subst s (Susp [] Xa)"
  proof-
    have one: 
      "nabla \<turnstile> subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp pi Xa) \<approx> 
       subst s (subst [(X, swap (rev pi) t)] (Susp pi Xa))"
      using subst_comp_expand equ_refl by simp
    have two: 
      "nabla \<turnstile> subst s (subst [(X, swap (rev pi) t)] (Susp pi Xa)) \<approx> 
      subst s (swap pi (look_up Xa [(X, swap (rev pi) t)]))"
      using equ_refl subst_susp[of \<open>[(X, swap (rev pi)t)]\<close> pi Xa] 
      by simp
    have "nabla \<turnstile> subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp pi Xa) \<approx> 
    subst s (swap pi (look_up Xa [(X, swap (rev pi) t)]))"
      using equ_trans[OF one two] by simp
    hence  "nabla \<turnstile> swap pi (look_up Xa (s \<bullet> [(X, swap (rev pi) t)])) \<approx> 
    subst s (swap pi (look_up Xa [(X, swap (rev pi) t)]))"
      using subst_susp[of \<open>(s \<bullet> [(X, swap (rev pi) t)])\<close>] by simp
    hence swap_pi_outside:  "nabla \<turnstile> swap pi (look_up Xa (s \<bullet> [(X, swap (rev pi) t)])) \<approx> 
    swap pi (subst s (look_up Xa [(X, swap (rev pi) t)]))"
      using subst_swap_comm by simp
    hence "nabla \<turnstile> (look_up Xa (s \<bullet> [(X, swap (rev pi) t)])) \<approx> 
    (subst s (look_up Xa [(X, swap (rev pi) t)]))"
      using equ_dec_pi[OF swap_pi_outside] by simp
    hence three: 
    "nabla \<turnstile> subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa) \<approx> 
    (subst s (look_up Xa [(X, swap (rev pi) t)]))" 
      using subst_susp by simp
    then show ?thesis
      proof(cases "Xa = X")
        case True
        hence "subst s (look_up Xa [(X, swap (rev pi) t)]) = subst s (swap (rev pi) t)"
          by simp
        with three have
          "nabla \<turnstile> subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa) \<approx> swap (rev pi) (subst s t)"
          using subst_swap_comm by auto
        hence i: "nabla \<turnstile> swap pi (subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa))
          \<approx> subst s t" using swap_inv_side by simp
        hence "nabla \<turnstile> swap pi (subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa))
          \<approx> subst s (Susp pi Xa)"
          using True equ_trans[OF i equ_symm[OF assms(1)]] by simp
        hence "nabla \<turnstile> swap pi (subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa))
          \<approx> swap pi (look_up Xa s)"
          using subst_susp by simp
        then show "nabla \<turnstile> (subst (s \<bullet> [(X, swap (rev pi) t)]) (Susp [] Xa))
          \<approx> subst s (Susp [] Xa)"
          using equ_dec_pi subst_susp by simp
      next
        case False
        hence "subst s (look_up Xa [(X, swap (rev pi) t)]) = subst s (Susp [] Xa)"
          by simp
        with three show ?thesis by auto
      qed
    qed
  qed

lemma subst_equ_a:
  assumes "nabla \<Turnstile> (subst s1) \<approx> (subst s2)"
    and "nabla \<turnstile> (subst s2 t1) \<approx> t2"
  shows "nabla \<turnstile> (subst s1 t1) \<approx> t2"
  using assms
proof(induct t1 arbitrary: t2)
  case (Abst a t1')
  then obtain t2' b 
    where t2: "t2 = Abst b t2'"
    by(auto elim: equ.cases)
  with Abst(3) have
    i: "nabla \<turnstile> Abst a (subst s2 t1') \<approx> Abst b t2'"
    using subst_abst by simp
  then show ?case 
  proof(cases "a=b")
    case True
    hence "nabla \<turnstile> (subst s2 t1') \<approx> t2'" 
      using Equ_elims(7)[OF i] by auto
    with Abst(1)[OF Abst(2), of t2']
    have "nabla \<turnstile> subst s1 t1' \<approx> t2'" 
      by simp
    hence "nabla \<turnstile> Abst a (subst s1 t1') \<approx> Abst b t2'"
      using True equ_abst_aa by simp
    with t2 show ?thesis
      using subst_abst[of s1 a t1'] by simp
  next
    case False
    hence "nabla \<turnstile> (subst s2 t1') \<approx> swap [(a,b)] t2'"
          and fresh: "nabla \<turnstile> a \<sharp> t2'"
      using Equ_elims(7)[OF i] by auto
     with Abst(1)[OF Abst(2), of \<open>swap [(a,b)] t2'\<close>]
    have "nabla \<turnstile> subst s1 t1' \<approx>  swap [(a,b)] t2'" 
      by simp
    hence "nabla \<turnstile> Abst a (subst s1 t1') \<approx> Abst b t2'"
      using equ_abst_ab[OF False fresh] by simp
    with t2 show ?thesis
      using subst_abst[of s1 a t1'] by simp
  qed
next
  case (Susp pi X)
  hence "nabla \<turnstile> swap pi (look_up X s2) \<approx> t2"
    using subst_susp by simp
  hence "nabla \<turnstile> (look_up X s2) \<approx> swap (rev pi) t2"
    using subst_susp swap_inv_side by simp
  hence i: "nabla \<turnstile> subst s2 (Susp [] X) \<approx> swap (rev pi) t2"
    using subst_susp[of s2 \<open>[]\<close>] by simp

  with Susp(1) subst_equ_def[of nabla \<open>subst s1\<close> \<open>subst s2\<close>]
  have "nabla \<turnstile> subst s1 (Susp [] X) \<approx> subst s2 (Susp [] X)"
    using UnCI equ_refl not_in_domn by metis

  with i have "nabla \<turnstile> subst s1 (Susp [] X) \<approx> swap (rev pi) t2"
    using equ_trans by blast
  hence "nabla \<turnstile> (look_up X s1) \<approx> swap (rev pi) t2"
    using subst_susp by simp
  hence "nabla \<turnstile> swap pi (look_up X s1) \<approx>  t2"
    using swap_inv_side by simp
    then show ?case 
      using subst_susp by simp
next
  case (Paar t11 t12)
  then obtain t21 t22
    where t2: "t2 = Paar t21 t22"
    by(auto elim: equ.cases)
  with Paar(4) 
  have paar_i: "nabla \<turnstile> subst s2 t11 \<approx> t21"
    and paar_ii: "nabla \<turnstile> subst s2 t12 \<approx> t22"
    by (auto elim: equ.cases)
  from t2 show ?case
    using equ_paar[OF Paar(1)[OF Paar(3) paar_i] Paar(2)[OF Paar(3) paar_ii]]
    subst_paar by simp
next
  case (Func f t1')
  then obtain t2' 
    where t2: "t2 = Func f t2'"
    by(auto elim: equ.cases)
   with Func(3) 
   have func: "nabla \<turnstile> subst s2 t1' \<approx> t2'"
   by (auto elim: equ.cases)
  from t2 show ?case
    using equ_func[OF Func(1)[OF Func(2) func], of f] by simp
qed (simp_all)

lemma unif_2a: 
  assumes "nabla\<Turnstile>subst s1\<approx>subst s2"
  and "(nabla\<turnstile>subst s2 t1 \<approx> subst s2 t2)"             
shows"(nabla\<turnstile>subst s1 t1 \<approx> subst s1 t2)"
proof-
  have i: "(nabla\<turnstile>subst s1 t1 \<approx> subst s2 t2)"
    using subst_equ_a[OF assms(1,2)] by simp
  show "(nabla\<turnstile>subst s1 t1 \<approx> subst s1 t2)"
    using subst_equ_a[OF assms(1) equ_symm[OF i]] equ_symm by auto
qed

lemma unif_2b:
  assumes "nabla \<Turnstile> subst s1 \<approx> subst s2" 
  and "nabla \<turnstile> a \<sharp> subst s2 t"
shows "nabla \<turnstile> a \<sharp> subst s1 t" 
  using assms
proof(induct t)
  case (Abst b t')
  then show ?case
  proof(cases "a=b")
    case True
    then show ?thesis 
      using fresh_abst_aa by simp 
  next
    case False
    with Abst show ?thesis 
      using Fresh_elims(1) subst_abst fresh_abst_ab
      by metis
  qed
next
  case (Susp pi X)
  then show ?case
    using equ_refl equ_symm l3_jud subst_equ_a by meson
next
  case (Paar t1 t2)
  then show ?case 
    using Fresh_elims(5) subst_paar fresh_paar 
    by metis
next
  case (Func f t')
  then show ?case
    using Fresh_elims(6) subst_func fresh_func
    by metis
qed (simp_all)

lemma subst_equ_to_trm: 
  assumes "nabla \<Turnstile> subst s1 \<approx> subst s2"
  shows "nabla\<turnstile>subst s1 t \<approx> subst s2 t"
  using assms equ_refl subst_equ_a by simp

lemma subst_cancel_right: 
  assumes "nabla\<Turnstile>(subst s1)\<approx>(subst s2)"
  shows "nabla\<Turnstile>(subst (s1\<bullet>s))\<approx>(subst (s2\<bullet>s))" 
  using assms subst_comp_expand subst_equ_def subst_equ_to_trm
  by simp

lemma subst_trans: 
  assumes "nabla\<Turnstile>subst s1 \<approx> subst s2" "nabla \<Turnstile> subst s2 \<approx> subst s3"
  shows "nabla\<Turnstile>subst s1\<approx>subst s3"
  using assms equ_trans subst_equ_def subst_equ_to_trm by meson

text \<open>
  If occurs holds, then one subterm is equal to (subst s (Susp pi X))
\<close>

lemma occurs_sub_trm_equ: 
  assumes "occurs X t1"
  shows "\<exists> t2 \<in> sub_trms (subst s t1). (\<exists>pi.(nabla\<turnstile>subst s (Susp pi1 X)\<approx>(swap pi t2)))" 
  using assms
proof(induct t1)
  case (Susp pi' X)
  then show ?case 
    using equ_pi_to_left equ_involutive_left 
      equ_refl subst_susp swap_append t_sub_trms_t
    occurs.simps(3) by metis
next
  case (Paar t11 t12)
  then show ?case 
    using subst_paar Un_iff occurs.simps(5) psub_sub_trms
        psub_trms.simps(4) by (metis)
qed(auto)

lemma ext_subst_strong:
  assumes "nabla1 \<Turnstile> (subst s) (nabla2 \<union> nabla3)"
  shows "nabla1 \<Turnstile> (subst s) nabla2" and "nabla1 \<Turnstile> (subst s) nabla3"
  using assms
  unfolding ext_subst_def by auto

lemma ext_subst_id:
  shows "nabla \<Turnstile> (subst []) nabla"
  unfolding ext_subst_def id_subst by auto


(*<*)
end
(*>*)