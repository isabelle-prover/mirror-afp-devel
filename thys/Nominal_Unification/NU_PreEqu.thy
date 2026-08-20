(*<*)
theory NU_PreEqu
imports NU_Fresh
begin
(*>*)

section \<open>Pre-Equality\<close>

text \<open>
  Defines the relation which captures the notion of alpha-equivalence (on open terms) 
  and proves this relation is an equivalence relation.
\<close>

inductive equ :: "fresh_envs \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<turnstile> _ \<approx> _" [80,80,80] 80) where
equ_abst_ab[intro!]: "\<lbrakk>a\<noteq>b;(nabla \<turnstile> a \<sharp> t2);(nabla \<turnstile> t1 \<approx> (swap [(a,b)] t2))\<rbrakk> 
                      \<Longrightarrow> (nabla \<turnstile> Abst a t1 \<approx> Abst b t2)" |
equ_abst_aa[intro!]: "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> Abst a t1 \<approx> Abst a t2)" |
equ_unit[intro!]:    "(nabla \<turnstile> Unit \<approx> Unit)" |
equ_atom[intro!]:    "a=b\<Longrightarrow>nabla \<turnstile> Atom a \<approx> Atom b" |
equ_susp[intro!]:    "(\<forall> c \<in> ds pi1 pi2. (c,X) \<in> nabla) \<Longrightarrow> (nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X)" |
equ_paar[intro!]:    "\<lbrakk>(nabla \<turnstile> t1\<approx>t2);(nabla \<turnstile> s1\<approx>s2)\<rbrakk> \<Longrightarrow> (nabla \<turnstile> Paar t1 s1 \<approx> Paar t2 s2)" |
equ_func[intro!]:    "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> Func F t1 \<approx> Func F t2)"

inductive_cases Equ_elims:
"nabla \<turnstile> Atom a \<approx> Atom b"
"nabla \<turnstile> Unit \<approx> Unit"
"nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X"
"nabla \<turnstile> Paar s1 t1 \<approx> Paar s2 t2"
"nabla \<turnstile> Func F t1 \<approx> Func F t2"
"nabla \<turnstile> Abst a t1 \<approx> Abst a t2"
"nabla \<turnstile> Abst a t1 \<approx> Abst b t2"

lemma equ_depth: 
  assumes "nabla \<turnstile> t1 \<approx> t2"
  shows "depth t1 = depth t2"
  using assms by (rule equ.induct, simp_all)

lemma rev_pi_pi_equ: 
  shows "(nabla \<turnstile> swap (rev pi) (swap pi t) \<approx> t)"
proof(induct t)
  case (Susp pi' X)
  then show ?case 
    using ds_cancel_pi_left[of _ \<open>rev pi @ pi\<close> _ \<open>[]\<close>]
    ds_rev_pi_pi elem_ds ds_rev_pi_id by auto
qed (auto)
  
lemma equ_pi_right: 
  assumes "\<forall>a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  shows "nabla \<turnstile> t \<approx> swap pi t"
  using assms
proof(induct t arbitrary: pi)
   case (Abst b t')
   have "swapas pi b = b \<or> swapas pi b \<noteq> b" by simp
  moreover 
  { assume eq: "swapas pi b = b"
    have "nabla \<turnstile> Abst b t' \<approx> Abst b (swap pi t')"
      by (metis Abst.hyps Abst.prems Fresh_elims(1) elem_ds eq equ_abst_aa)
    then have "nabla \<turnstile> Abst b t' \<approx> swap pi (Abst b t')" using eq by simp
  }
  moreover
  { assume neq: "b \<noteq> swapas pi b"  
    obtain c where c_def: "c = swapas pi b" by simp
    have "c \<in> ds [] pi"
      by (metis append.right_neutral c_def ds_cancel_pi_front ds_cancel_pi_left ds_elem neq)
    then have one: "nabla \<turnstile> c \<sharp> Abst b t'" using assms Abst.prems by auto
    have two: "b \<noteq> c" using neq c_def by blast
    have "nabla \<turnstile> c \<sharp> t'" using one two by cases auto
    have "nabla \<turnstile> Abst b t' \<approx> Abst c (swap pi t')" 
    proof(rule equ_abst_ab)
      show "b \<noteq> c" using neq c_def by blast
      have b_is_swap: "b = swapas (rev pi) c" using c_def by simp
      show "nabla \<turnstile> b \<sharp> swap pi t'" 
        using Abst.prems Fresh_elims(1) ds_elem fresh_swap_right neq swapas_rev_pi_a by metis
      show "nabla \<turnstile> t' \<approx> swap [(b, c)] (swap pi t')"
      proof -
         have fresh_ext:
          "\<forall>a \<in> ds [] ((b,c) # pi). nabla \<turnstile> a \<sharp> t'"
        proof (rule ballI)
          fix a assume A: "a \<in> ds [] ((b,c)#pi)"
          then have "a = c \<or> a \<in> ds [] pi"
            using c_def ds_7 neq by auto  
          then show "nabla \<turnstile> a \<sharp> t'"
          proof
            assume "a = c"
            with \<open>nabla \<turnstile> c \<sharp> t'\<close> show ?thesis by simp
          next
            assume "a \<in> ds [] pi"
            show ?thesis 
            proof(rule Fresh_elims(1)[of nabla a b t'], goal_cases)
              case 1
              then show ?case
                using Abst.prems \<open>a \<in> ds [] pi\<close>
              by simp
            next
              case 2
              then show ?case by simp
            next
              case 3
              have "a \<noteq> swapas ((b, c) # pi) a" 
                using A elem_ds
                by blast
              hence "a \<noteq> b" using c_def A 
                by (auto simp add: if_split)
              hence False using 3 by simp
              then show ?case by simp
          qed
        qed
      qed
        from Abst.hyps[OF fresh_ext]
        have "nabla \<turnstile> t' \<approx> swap ([(b,c)]@pi) t'"
          by simp
        moreover have "swap ([(b,c)]@pi) t' = swap [(b,c)] (swap pi t')"
          using swap_append by blast
        ultimately show ?thesis by simp
      qed
    qed
   then have "nabla \<turnstile> Abst b t' \<approx> swap pi (Abst b t')" using neq c_def by force
 }
  ultimately show ?case by argo
next
  case (Susp pi' X)
  have "\<forall>a\<in>ds [] pi. nabla \<turnstile> a \<sharp> Susp pi' X" by fact
  then have "nabla \<turnstile> Susp pi' X \<approx> Susp (pi @ pi') X"
   using Fresh_elims(4) equ_susp ds_def ds_cancel_pi_left
   by (metis (lifting) append_self_conv2 swapas_rev_pi_a)
  then show ?case by simp
next
  case Unit
  then show ?case 
    using equ_unit swap.simps(2) by force
next
  case (Atom b)
    then show ?case
      apply simp
    apply (rule equ_atom)
    using Fresh_elims(3) ds_elem_cp
    by metis
next
  case (Paar t1 t2)
  then have hypsp1: "(\<forall>a\<in>ds [] pi.  nabla \<turnstile> a \<sharp> t1)"
    and hypsp2: "(\<forall>a\<in>ds [] pi.  nabla \<turnstile> a \<sharp> t2)"
    using Paar.prems Fresh_elims(5) by meson+
  have "nabla \<turnstile> Paar t1 t2 \<approx> Paar (swap pi t1) (swap pi t2)"
    using Paar.hyps(1,2) hypsp1 hypsp2 by blast
  then show ?case by simp
next
  case (Func f t')
  then have hypsf: "\<forall>a\<in>ds [] pi. nabla \<turnstile> a \<sharp> t'" using fresh_func
    by (metis Fresh_elims(6))
  have "nabla \<turnstile> Func f t' \<approx> Func f (swap pi t')"
    using Func.hyps hypsf by blast
  then show ?case
    by simp
qed

lemma pi_comm: 
  shows "nabla \<turnstile> (swap (pi @ [(a,b)]) t) \<approx> (swap ([(swapas pi a, swapas pi b)] @ pi) t)"
proof(induct t)
  case (Abst c t)
  then show ?case using swapas_comm by force
next
  case (Susp \<pi>' X)
  have rew1:
    "swap (pi @ [(a,b)]) (Susp \<pi>' X) = Susp (pi @ [(a,b)] @ \<pi>') X"
    by simp
  have rew2:
    "swap ([(swapas pi a, swapas pi b)] @ pi) (Susp \<pi>' X) 
    = Susp ([(swapas pi a, swapas pi b)] @ pi @ \<pi>') X"
    by simp
  have fresh:
  "\<forall>c \<in> ds (pi @ [(a,b)] @ \<pi>') ([(swapas pi a, swapas pi b)] @ pi @ \<pi>'). (c, X) \<in> nabla"
    using swapas_append swapas_comm ds_def by simp
  from rew1 rew2 fresh
  show ?case
    using equ_susp by simp
next
  case Unit
  then show ?case by force
next
  case (Atom c)
  then show ?case 
    using equ_atom swapas_comm by auto
next
  case (Paar t1 t2)
  then show ?case by force
next
  case (Func f t)
  then show ?case by force
qed

lemma l3_jud: 
  assumes "(nabla \<turnstile> t1 \<approx> t2)"
  shows "(nabla \<turnstile> a \<sharp> t1) \<longrightarrow> (nabla \<turnstile> a \<sharp> t2)"
  using assms
proof(induction rule: equ.induct)
  case (equ_abst_ab b c nabla t2 t1)
  then show ?case 
    using fresh_swap_left Fresh_elims(1) fresh_abst_aa fresh_abst_ab rev_singleton_conv swapa.simps swapas.simps(1,2)
    by metis
next
  case (equ_abst_aa nabla t1 t2 b)
  then show ?case 
    using fresh_swap_left Fresh_elims(1) fresh_abst_aa fresh_abst_ab 
    by metis
next
  case (equ_unit nabla)
  then show ?case
    by blast
next
  case (equ_atom b c nabla)
  then show ?case 
    by simp
next
  case (equ_susp pi1 pi2 X nabla)
  then show ?case 
    using Fresh_elims(4) ds_elem_cp ds_rev fresh_susp swapas_append swapas_rev_pi_a
    by metis
next
  case (equ_paar nabla t1 t2 s1 s2)
  then show ?case
    using Fresh_elims(5) by blast
next
  case (equ_func nabla t1 t2 f)
  then show ?case 
    using Fresh_elims(6) by blast
qed

lemma ds_empty_equiv_1:
  assumes "ds pi1 pi2 = {}"
  shows "nabla \<turnstile> swap pi1 t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> swap pi2 t1 \<approx> t2"
  using assms
proof(induction t1 arbitrary: t2)
  case (Abst a t1')
  then obtain b t2'
    where t2: "t2 = Abst b t2'"
    by(auto elim: equ.cases)
  with Abst have i: "nabla \<turnstile> Abst (swapas pi1 a) (swap pi1 t1') \<approx> Abst b t2'"
    using swap.simps(4) by simp
  then show ?case
  proof(cases \<open>swapas pi1 a = b\<close>)
    case True
    then have "nabla \<turnstile> swap pi1 t1' \<approx> t2'" 
      using Abst i Equ_elims(6) by blast
    then have ii: "nabla \<turnstile> swap pi2 t1' \<approx> t2'"
      using Abst by simp
    then have "nabla \<turnstile> Abst (swapas pi2 a) (swap pi2 t1') \<approx> Abst b t2'"
      using True ds_swapas_eq[OF Abst(3), of a] equ_abst_aa[OF ii, of \<open>swapas pi2 a\<close>] 
      by simp
    then show ?thesis 
      using t2 by simp
  next
    case False
    then have equ_ab_pi1: "nabla \<turnstile> swap pi1 t1' \<approx> swap [(swapas pi1 a, b)] t2'" 
      and fresh_ab_pi1: "nabla \<turnstile> swapas pi1 a \<sharp> t2'"
      using i Equ_elims(7)[of nabla \<open>swapas pi1 a\<close> \<open>swap pi1 t1'\<close> b t2'] 
      by blast+
    have equ_ab_pi2: "nabla \<turnstile> swap pi2 t1' \<approx> swap [(swapas pi2 a, b)] t2'"
      using equ_ab_pi1 ds_swapas_eq[OF Abst(3), of a] 
        Abst(3) Abst(1)[of \<open>swap [(swapas pi1 a, b)] t2'\<close>] by auto
    have fresh_ab_pi2: "nabla \<turnstile> swapas pi2 a \<sharp> t2'"
      using fresh_ab_pi1 ds_swapas_eq[OF Abst(3), of a] by simp
    with equ_ab_pi2 have "nabla \<turnstile> Abst (swapas pi2 a) (swap pi2 t1') \<approx> Abst b t2'"
      using equ_abst_ab[OF False, of nabla t2'] ds_swapas_eq[OF Abst(3), of a] by simp
    then show ?thesis using t2 by simp
  qed
next
  case (Susp pi X)
  then obtain pi'
    where t2: "t2 = Susp pi' X"
    by (auto elim:equ.cases)
  with Susp have i: "nabla \<turnstile> Susp (pi1 @ pi) X \<approx> Susp pi' X" 
    by simp
  then have "\<forall> c \<in> ds (pi1@pi) pi'. (c,X) \<in> nabla"
    using Equ_elims(3)[OF i] by auto
  with Susp have "\<forall> c \<in> ds (pi2@pi) pi'. (c,X) \<in> nabla"
    using ds_cancel_pi_left ds_sym ds_trans
    by blast
  then have "nabla \<turnstile> Susp (pi2 @ pi) X \<approx> Susp pi' X"
    using equ_susp by simp
  then show ?case using t2 swap.simps(3) by simp
next
  case (Atom a)
  then show ?case
    using ds_swapas_eq[OF Atom(2), of a]
    by (auto elim: equ.cases)
qed (auto elim: equ.cases)

lemma ds_empty_equiv_2:
  assumes "ds pi1 pi2 = {}"
  shows "nabla \<turnstile> t1 \<approx> swap pi1 t2 \<Longrightarrow> nabla \<turnstile> t1 \<approx> swap pi2 t2"
using assms
proof(induction t2 arbitrary: pi1 pi2 t1)
  case (Abst b t2')
  then obtain a t1'
    where t1: "t1 = Abst a t1'"
    by(auto elim: equ.cases)
  with Abst have i: "nabla \<turnstile> Abst a t1' \<approx> Abst (swapas pi1 b) (swap pi1 t2')"
    using swap.simps(4) by simp
  then show ?case
  proof(cases \<open>swapas pi1 b = a\<close>)
    case True
    then have "nabla \<turnstile> t1' \<approx> swap pi1 t2'" 
      using Abst i Equ_elims(6) by blast
    then have ii: "nabla \<turnstile> t1' \<approx> swap pi2 t2'"
      using Abst by simp
    then have "nabla \<turnstile> Abst a t1' \<approx> Abst (swapas pi2 b) (swap pi2 t2')"
      using True ds_swapas_eq[OF Abst(3), of b] equ_abst_aa[OF ii, of \<open>swapas pi2 b\<close>] 
      by simp
    then show ?thesis 
      using t1 by simp
  next
    case False
    then have equ_ab: "nabla \<turnstile> t1' \<approx> swap [(a, swapas pi1 b)] (swap pi1 t2')" 
      and fresh_ab_pi1: "nabla \<turnstile> a \<sharp> swap pi1 t2'"
      using i Equ_elims(7) by blast+

    then have equ_ab_pi1: "nabla \<turnstile> t1' \<approx> swap ([(a, swapas pi1 b)]@ pi1) t2'"
      using swap_append[of \<open>[(a, swapas pi1 b)]\<close> pi1 t2'] by simp

    have ds_empty: "ds ([(a, swapas pi1 b)] @ pi1) ([(a, swapas pi2 b)] @ pi2) = {}"
      using Abst(3) ds_swapas_eq[OF Abst(3), of b] 
        ds_cancel_pi_front[of \<open>[(a, swapas pi1 b)]\<close> pi1 pi2] by simp
    
    hence "nabla \<turnstile> t1' \<approx> swap ([(a, swapas pi2 b)]@ pi2) t2'"
      using Abst(1)[OF equ_ab_pi1 ds_empty] by simp
    hence equ_ab_pi2: "nabla \<turnstile> t1' \<approx> swap [(a, swapas pi2 b)] (swap pi2 t2')"
      using swap_append[of \<open>[(a, swapas pi2 b)]\<close> pi2 t2'] by simp

    have fresh_ab_pi2: "nabla \<turnstile> a \<sharp> swap pi2 t2'"
      using ds_empty_fresh_2 Abst(3) fresh_ab_pi1 by auto
    with equ_ab_pi2 have "nabla \<turnstile> Abst a t1' \<approx> Abst (swapas pi2 b) (swap pi2 t2')"
      using equ_abst_ab ds_swapas_eq False assms Abst(3) by auto
    then show ?thesis using t1 by simp
  qed
next
  case (Susp pi' X)
  then obtain pi
    where t1: "t1 = Susp pi X"
    by (auto elim:equ.cases)
  with Susp have i: "nabla \<turnstile> Susp pi X \<approx> Susp (pi1 @ pi') X" 
    by simp
  then have "\<forall> c \<in> ds pi (pi1 @ pi'). (c,X) \<in> nabla"
    using Equ_elims(3)[OF i] by auto
  with Susp have "\<forall> c \<in> ds pi (pi2 @ pi'). (c,X) \<in> nabla"
    using ds_cancel_pi_left ds_sym ds_trans
    by blast
  then have "nabla \<turnstile> Susp pi X \<approx> Susp (pi2 @ pi') X"
    using equ_susp by simp
  then show ?case using t1 swap.simps(3) by simp
next
  case (Atom a)
  then show ?case
    using ds_swapas_eq by (auto elim: equ.cases)
qed (auto elim: equ.cases)

lemma equ_equivariance:
  assumes "nabla \<turnstile> t1 \<approx> t2"
  shows "nabla \<turnstile> swap pi t1 \<approx> swap pi t2"
  using assms
proof(induct rule: equ.induct)
  case (equ_abst_ab a b nabla t2' t1')
  have i: "nabla \<turnstile> swapas pi a \<sharp> swap pi t2'"
    using fresh_swap_eqvt[OF equ_abst_ab(2), of pi] by simp

  have "nabla \<turnstile> swap pi t1' \<approx> swap (pi @ [(a,b)]) t2'"
    using equ_abst_ab(4) swap_append[of pi \<open>[(a,b)]\<close> t2'] by simp
  then have "nabla \<turnstile> swap pi t1' \<approx> swap ([(swapas pi a, swapas pi b)] @ pi) t2'"
    using ds_empty_equiv_2[OF ds_comm[of pi a b]] by auto
  then have ii: "nabla \<turnstile> swap pi t1' \<approx> swap [(swapas pi a, swapas pi b)] (swap pi t2')"
    using ds_empty_equiv_2[OF ds_comm[of pi a b]] 
      swap_append[of \<open>[(swapas pi a, swapas pi b)]\<close> pi t2'] by simp

  have iii: "swapas pi a \<noteq> swapas pi b" 
    using equ_abst_ab.hyps(1) swapas_rev_pi_a by blast
  
  with i ii
  have "nabla \<turnstile> Abst (swapas pi a) (swap pi t1') \<approx> Abst (swapas pi b) (swap pi t2')"
    using equ.equ_abst_ab by auto
  hence "nabla \<turnstile> swap pi (Abst a t1') \<approx> swap pi (Abst b t2')"
    using swap.simps(4) by simp
  then show ?case by simp
next
  case (equ_abst_aa nabla t1' t2' a)
  then show ?case
    using equ.equ_abst_aa by simp
next
  case (equ_susp pi1 pi2 X nabla)
  then show ?case using ds_cancel_pi_front
    by auto
qed (auto)

lemma swap_inv_side: 
  shows "nabla \<turnstile> swap pi t1 \<approx> t2 = nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
proof
  
  {assume assm1: "nabla \<turnstile> swap pi t1 \<approx> t2"
  from equ_equivariance[OF assm1, of \<open>rev pi\<close>]
  have "nabla \<turnstile> swap (rev pi @ pi) t1  \<approx> swap (rev pi) t2"
    using swap_append[of \<open>rev pi\<close> pi t1] by simp
  then show "nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
    using ds_empty_equiv_1[OF ds_rev_pi_id[of pi], of nabla t1 \<open>swap (rev pi) t2\<close>] 
      swap_id[of t1] by simp}

  {assume assm2: "nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
  from equ_equivariance[OF assm2, of pi]
  have "nabla \<turnstile> swap pi t1 \<approx> swap (pi @ rev pi) t2"
    using swap_append[of pi \<open>rev pi\<close> t2] by simp
  then show "nabla \<turnstile> swap pi t1 \<approx> t2"
    using ds_empty_equiv_2[OF ds_pi_rev_id[of pi], of nabla \<open>swap pi t1\<close> t2] 
      swap_id[of t2] by simp}
qed

lemma equ_swap_abba:
  assumes "n = depth t1"
  shows "nabla \<turnstile> swap [(a,b)] t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> t1 \<approx> swap [(b,a)] t2"
proof-
  assume "nabla \<turnstile> swap [(a,b)] t1 \<approx> t2"
  with ds_baab[of b a] 
  have "nabla \<turnstile> swap [(b,a)] t1 \<approx> t2"
    using ds_empty_equiv_1 by blast
    then show ?thesis
    using swap_inv_side[of nabla \<open>[(b,a)]\<close>] by simp
qed

lemma equ_equiv_pi: 
  assumes "\<forall>a \<in> ds pi1 pi2. nabla \<turnstile> a \<sharp> t"
  shows "nabla \<turnstile> swap pi1 t \<approx> swap pi2 t"
  using assms equ_pi_right[of \<open>rev pi1 @ pi2\<close> nabla t]
    swap_inv_side[of nabla pi1 t \<open>swap pi2 t\<close>] ds_rev swap_append by simp

lemma equ_symm:
  shows "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> t2 \<approx> t1)"
proof(induction rule: equ.induct)
  case (equ_abst_ab a b nabla t2' t1')
  have i: "nabla \<turnstile> b \<sharp> swap [(a, b)] t2'" 
    using fresh_swap_eqvt[of nabla a t2' "[(a,b)]"] equ_abst_ab(2) by auto
  with equ_abst_ab(4) 
  have b_fresh: "nabla \<turnstile> b \<sharp> t1'"
    using l3_jud by blast
  from equ_abst_ab(4) 
  have ii: "nabla \<turnstile> t2' \<approx> swap [(b, a)] t1'"
    using equ_swap_abba by simp
  show ?case 
    using equ.equ_abst_ab[OF equ_abst_ab(1)[symmetric] b_fresh ii] by simp
next
  case (equ_abst_aa nabla t1' t2' a)
  then show ?case 
    using equ.equ_abst_aa[OF equ_abst_aa(2), of a] by simp
next
  case (equ_unit nabla)
  then show ?case by auto
next
  case (equ_atom a b nabla)
  then show ?case by auto
next
  case (equ_susp pi1 pi2 X nabla)
  then show ?case 
    using ds_sym by auto
next
  case (equ_paar nabla t1' t2' s1' s2')
  then show ?case by auto
next
  case (equ_func nabla t1' t2' f)
  then show ?case 
    using equ.equ_func[OF equ_func(2), of f] by simp
qed

lemma equ_trans:
  assumes "nabla \<turnstile> t1 \<approx> t2" "nabla \<turnstile> t2 \<approx> t3"
  shows "nabla \<turnstile> t1 \<approx> t3"
  using assms
proof(induction \<open>depth t1\<close> arbitrary: t1 t2 t3 rule: nat_less_induct)
  case 1
  note IH = this
  have IH_usable: 
    "depth t1' < depth t1 \<Longrightarrow> nabla \<turnstile> t1' \<approx> t2' \<Longrightarrow>  nabla \<turnstile> t2' \<approx> t3' \<Longrightarrow> nabla \<turnstile> t1' \<approx> t3'"
    for t1' t2' t3' using IH by blast
  have "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> t2 \<approx> t3 \<Longrightarrow>  nabla \<turnstile> t1 \<approx> t3"
  proof-
    assume t12: "nabla \<turnstile> t1 \<approx> t2" and t23: "nabla \<turnstile> t2 \<approx> t3"
    show ?thesis
     proof(cases rule: equ.cases[OF \<open>nabla \<turnstile> t1 \<approx> t2\<close>])
       case (1 a b nabla t2' t1')
       from 1(2) have deptht1: "depth t1' < depth t1"
         using depth.simps(4) by auto
       from t23 show ?thesis
       proof(cases rule: equ.cases)
         case (equ_abst_ab b c t3' t2')
         then show ?thesis 
         proof(cases "a = c")
           case True
           have i: "nabla \<turnstile> swap [(c,b)] t2' \<approx> swap ([(c,b)]@[(b,c)]) t3'"
             using equ_equivariance[OF equ_abst_ab(5), of \<open>[(c,b)]\<close>] 1(1)
               swap_append[of \<open>[(c,b)]\<close> \<open>[(b,c)]\<close> t3'] by simp
           have ii: "nabla \<turnstile> swap [(c,b)] t2' \<approx> t3'"
             using ds_empty_equiv_2[OF ds_baab_id[OF equ_abst_ab(3)] i] by simp
           with equ_abst_ab 1 True
           have iii: "nabla \<turnstile> t1' \<approx> swap [(c, b)] t2'" by blast
           with ii have "nabla \<turnstile> t1' \<approx> t3'"
             using IH_usable[OF deptht1, of \<open>swap [(c, b)] t2'\<close> t3'] 1(1)
             by simp
           then show ?thesis using True equ_abst_ab(2) 1(1,2) by auto
         next
           case False

           have deptht2: "depth (swap [(a,b)] t2') < depth t1"
              using depth.simps(4) equ_depth[OF 1(6)] swap_depth 1(3) deptht1
              equ_abst_ab(1) by simp

            from equ_abst_ab(1,4,5) 1(1,3,5)
              have ii: "nabla \<turnstile> a \<sharp> swap [(b,c)] t3'"
                using l3_jud by simp

            then have a_fresh_t3: "nabla \<turnstile> a \<sharp> t3'"
              using fresh_swap_left[OF ii] False equ_abst_ab 1 by simp
            have b_fresh_t3: "nabla \<turnstile> b \<sharp> t3'" 
              using equ_abst_ab(4) 1(1) by simp

            from 1(1) equ_abst_ab(5)
            have "nabla \<turnstile> swap [(a,b)] t2' \<approx> swap ([(a,b)]@[(b,c)]) t3'"
              using equ_equivariance[OF equ_abst_ab(5)]
             swap_append[of \<open>[(a, b)]\<close> \<open>[(b,c)]\<close> t3'] by simp
            then have iii: "nabla \<turnstile> swap [(a,b)] t2' \<approx> swap ([(a,b),(b,c)]) t3'"
              by simp
            
            have "ds [(a,b), (b,c)] [(a,c)] = {a,b}" 
              using ds_acabbc equ_abst_ab 1 False by simp
            with a_fresh_t3 b_fresh_t3 
            have iv: "nabla \<turnstile> swap [(a,b),(b,c)] t3' \<approx> swap [(a,c)] t3'"
              using equ_equiv_pi by simp

            with 1(1) iii have "nabla \<turnstile> swap [(a,b)] t2' \<approx> swap [(a,c)] t3'"
              using IH_usable[OF deptht2, of \<open>swap ([(a,b),(b,c)]) t3'\<close> \<open>swap [(a,c)] t3'\<close>]
              by simp

            with 1(1,3,6) have "nabla \<turnstile> t1' \<approx> swap [(a,c)] t3'"
              using IH_usable[OF deptht1, of \<open>swap [(a, b)] t2'\<close> \<open>swap [(a,c)] t3'\<close>]
              equ_abst_ab(1) by simp
            
            with 1(1,2) equ_abst_ab(2) 
            show ?thesis using equ.equ_abst_ab[OF False a_fresh_t3] by simp
         qed
       next
         case (equ_abst_aa t2' t3' b)
         from this(3) 1(1)
         have i: "nabla \<turnstile> swap [(a,b)] t2' \<approx> swap [(a,b)] t3'"
           using equ_equivariance[of nabla t2' t3' \<open>[(a,b)]\<close>] by simp

         have "nabla \<turnstile> b \<sharp> swap [(a,b)] t2'" 
           using 1(1,3,4,5) equ_abst_aa(1) fresh_swap_eqvt[of nabla a t2' \<open>[(a,b)]\<close>]
           by auto
         then have ii: "nabla \<turnstile> b \<sharp> swap [(a,b)] t3'"
           using l3_jud[OF i, of b] by simp
         have "nabla \<turnstile> swapas [(a,b)] b \<sharp> t3'"
           using fresh_swap_left[OF ii] by simp
         then have a_fresh_t3: "nabla \<turnstile> a \<sharp> t3'"
           using 1(3,4) equ_abst_aa(1) by simp

         have is_equ: "nabla \<turnstile> t1' \<approx> swap [(a,b)] t3'"
           using 1 i IH_usable[OF deptht1, of \<open>swap [(a,b)] t2'\<close> \<open>swap [(a,b)] t3'\<close>]
           equ_abst_aa(1) by auto
          
         from a_fresh_t3 is_equ show ?thesis
           using 1 equ_abst_aa(1,2) equ.equ_abst_ab by simp
       qed (auto simp add: 1 t12)
     next
       case (2 nabla t1' t2' a)
       have deptht1: "depth t1' < depth t1"
         using depth.simps(4) 2(2) by simp
         from t23 show ?thesis 
         proof(cases rule: equ.cases)
           case (equ_abst_ab a c t3' t2')
           have "nabla \<turnstile> t1' \<approx> swap [(a,c)] t3'"
             using 2(1,2,3,4) IH_usable[OF deptht1, of \<open>t2'\<close> \<open>swap [(a,c)] t3'\<close>] 
            equ_abst_ab(1,4,5) by simp
           then show ?thesis
             using equ.equ_abst_ab[OF equ_abst_ab(3)]
               2(1,2,3) equ_abst_ab(1,2,4) by auto
         next
           case (equ_abst_aa t2' t3' a)
           then show ?thesis 
             using 1 2(1,2,3,4) by auto
         qed (auto simp add: 2)
     next
       case (3 nabla)
        from t23 show ?thesis
        proof(cases rule: equ.cases)
          case equ_unit
          then show ?thesis using t12 by auto
        qed (auto simp add: 3)
     next
       case (4 a b nabla)
        from t23 show ?thesis 
        proof(cases rule: equ.cases)
          case (equ_atom a b)
          then show ?thesis
            using t12 by auto
        qed (auto simp add: 4)
     next
       case (5 pi1 pi2 X nabla)
        from t23 show ?thesis 
        proof(cases rule: equ.cases)
          case (equ_susp pi1 pi2 X)
          then show ?thesis 
            using ds_trans 5 by blast
        qed (auto simp add: 5)
     next
       case (6 nabla t1' t2' s1' s2')
        from t23 show ?thesis 
        proof(cases rule: equ.cases)
          case (equ_paar t2' t3' s2' s3')
          have deptht1: "depth t1' < depth t1" 
            using 6(2) by simp
         have depths1: "depth s1' < depth t1" 
           using 6(2) by simp
         have a: "nabla \<turnstile> t1' \<approx> t2'" 
           using "6"(3,4) equ_paar by auto
         have b: "nabla \<turnstile> s1' \<approx> s2'" 
           using "6" equ_paar by auto
         from a have t1_equal_t3: "nabla \<turnstile> t1' \<approx> t3'" 
           using IH_usable[of t1' t2' t3'] equ_paar(3) 6(1) deptht1
           by simp
         from b have s1_equal_s3: "nabla \<turnstile> s1' \<approx> s3'" 
           using IH_usable[of s1' s2' s3'] equ_paar(4) 6(1) depths1
           by simp
         from t1_equal_t3 s1_equal_s3 show ?thesis 
           using equ.equ_paar[of nabla t1' t3' s1' s3'] 6(1,2) equ_paar(2)
           by simp
        qed (auto simp add: 6)
     next
       case (7 nabla t1 t2 F)
        from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_func t1 t2 F)
         then show ?thesis 
           using 1 7(1,2,3,4) by auto
       qed (auto simp add: 7)
     qed
   qed
   then show ?case 
     using IH(2,3) by blast
 qed

lemma pi_right_equ_help:
  assumes "(n = depth t)"
  shows "nabla \<turnstile> t \<approx> swap pi t \<Longrightarrow> \<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  using assms 
proof(induction n arbitrary: t pi rule: nat_less_induct)
  case (1 n)
  note IH = this
  then show ?case 
    proof(cases rule: equ.cases[OF \<open>nabla \<turnstile> t \<approx> swap pi t\<close>])
      case (1 b c nabla t2 t1)
        have deptht1: "depth t1 < n"
          using 1 depth.simps(4) IH by simp
        have swap_pi_t1_is_t2: "swap pi t1 = t2"
          using 1(2,3) by auto
        have swap_pi_b_is_c: "swapas pi b = c"
          using 1(2,3) by auto
        with swap_pi_t1_is_t2 have "nabla \<turnstile> t1 \<approx> swap [(b, swapas pi b)] (swap pi t1)"
          using 1(1,6) by simp
        then have "nabla \<turnstile> t1 \<approx> swap ([(b, swapas pi b)] @ pi) t1"
          using swap_append[of \<open>[(b, swapas pi b)]\<close> pi t1] by simp
        with deptht1 have "\<forall> a \<in> ds [] ((b, swapas pi b)#pi). nabla \<turnstile> a \<sharp> t1"
          using "1.IH" 1 by auto
        then have ds_minus_bc: "\<forall> a \<in> ds [] pi - {b, c}. nabla \<turnstile> a \<sharp> t1"
          using ds_equality swap_pi_b_is_c by auto
        have c_fresh_t1: "nabla \<turnstile> c \<sharp> t1"
          using 1 equ_symm l3_jud fresh_swap_eqvt Equ_elims equ_abst_ab by meson
        with ds_minus_bc have "\<forall> a \<in> ds [] pi - {b}. nabla \<turnstile> a \<sharp> t1"
          by auto
        then have ds_minus_b: "\<forall> a \<in> ds [] pi - {b}. nabla \<turnstile> a \<sharp> Abst b t1"
          using fresh_abst_ab by blast
        have b_fresh_abst_t1: "nabla \<turnstile> b \<sharp> Abst b t1"
          using fresh_abst_aa by simp
        have "\<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> Abst b t1"
        proof(rule, goal_cases)
          case (1 a)
          then show ?case
            using b_fresh_abst_t1 ds_minus_b
            by (cases "a=b", auto)
        qed
        with 1 show ?thesis
          by auto
    next
      case (2 nabla t1 t2 b)
      have deptht1: "depth t1 < n"
        using 2 depth.simps(4) IH by simp
      have swap_pi_t1_is_t2: "swap pi t1 = t2"
        using 2(2,3) by auto
      from swap_pi_t1_is_t2 deptht1 
      have "\<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t1"
        using "1.IH" 2(1,4) by auto
      then show ?thesis 
        using 2(1,2,3) elem_ds by fastforce
    next
      case (3 nabla)
      then show ?thesis 
        by blast
    next
      case (4 a b nabla)
      then show ?thesis
        using elem_ds by force
    next
      case (5 pi1 pi2 X nabla)
      have "swap pi t = Susp (pi@pi1) X" 
        using "5"(2) by auto
      also have "... = Susp pi2 X"
        using 5(3) calculation by simp
      then have "pi@pi1 = pi2" by simp
      hence "\<forall>c\<in>ds pi1 (pi@pi1). (c, X) \<in> nabla"
        using 5(4) by simp
      then show ?thesis 
        using "5"(1,2) fresh_susp ds_cancel_pi_right[of _ _ "[]" _]
        by simp
    next
      case (6 nabla t1 t2 s1 s2)
      have deptht1: "depth t1 < n"
        using 6 depth.simps(5) IH
        by simp
      have depths1: "depth s1 < n"
        using 6 depth.simps(5) IH
        by simp
      from deptht1 depths1 show ?thesis 
        using "1.IH" 6 by auto
    next
      case (7 nabla t1 t2 f)
      have deptht1: "depth t1 < n"
        using 7(2) depth.simps(5) IH 
        by auto
      have "nabla \<turnstile> t1 \<approx> swap pi t1"
        using 7 by simp
      then have "\<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t1"
        using 7(1) IH deptht1 by simp
      then show ?thesis 
        using 7(1,2) fresh_func[of nabla _ t1 f] 
        by simp
    qed
  qed

(*<*)
end 
(*>*)