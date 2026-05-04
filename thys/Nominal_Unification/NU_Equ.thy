(*<*)
theory NU_Equ
imports NU_PreEqu
begin
(*>*)

section \<open>Equality\<close>

text \<open>
  Proves various facts about the equivalence relation.
\<close>

lemma equ_refl: 
  shows "nabla \<turnstile> t \<approx> t"
  by(induct t, auto simp add: ds_def)


lemma equ_dec_pi:
  assumes "nabla \<turnstile> swap pi t1 \<approx> swap pi t2"
  shows "nabla \<turnstile> t1 \<approx> t2"
proof-
  have i: "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t1"
    "nabla \<turnstile> swap (rev pi) (swap pi t2) \<approx> t2"
    using rev_pi_pi_equ by auto
  then have "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> swap (rev pi) (swap pi t2)"
    using equ_equivariance assms by simp
  then show ?thesis using i equ_symm equ_trans by meson 
qed

lemma equ_involutive_left: 
  shows "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t2 = nabla \<turnstile> t1 \<approx> t2"
proof(auto)
  have i: "nabla \<turnstile> t1 \<approx> swap (rev pi) (swap pi t1)"
    using rev_pi_pi_equ equ_symm by blast
  show "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t2 \<Longrightarrow> nabla \<turnstile> t1 \<approx> t2"
    using i equ_trans by blast
  show "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t2"
    using i equ_trans equ_symm by blast
qed

lemma equ_pi_to_left: 
  shows "nabla \<turnstile> swap (rev pi) t1 \<approx> t2 = nabla \<turnstile> t1 \<approx> swap pi t2"
proof

  {assume i: "nabla \<turnstile> swap (rev pi) t1 \<approx> t2"
  have "nabla \<turnstile> swap pi (swap (rev pi) t1) \<approx> swap pi t2"
    using equ_equivariance[OF i, of pi] by simp
  then show "nabla \<turnstile> t1 \<approx> swap pi t2"
    using equ_involutive_left[of nabla \<open>rev pi\<close> t1 \<open>swap pi t2\<close>] rev_rev_ident[of pi]
    by simp}

  {assume i: "nabla \<turnstile> t1 \<approx> swap pi t2"
  have ii: "nabla \<turnstile> swap (rev pi) t1 \<approx> swap (rev pi) (swap pi t2)"
    using equ_equivariance[OF i, of \<open>rev pi\<close>] by simp
  then have iii: "nabla \<turnstile> swap (rev pi) (swap pi t2) \<approx> swap (rev pi) t1"
    using equ_symm[OF ii] by simp
  then have iv: "nabla \<turnstile> t2 \<approx> swap (rev pi) t1"
    using equ_involutive_left[of nabla pi t2 \<open>swap (rev pi) t1\<close>] by simp
  then show "nabla \<turnstile> swap (rev pi) t1 \<approx> t2"
    using equ_symm[OF iv] by simp}

qed
    
lemma equ_pi_to_right: 
  shows "nabla\<turnstile>t1 \<approx> swap (rev pi) t2 = nabla\<turnstile>swap pi t1\<approx>t2"
proof
  {assume i: "nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
    then show "nabla \<turnstile> swap pi t1 \<approx>  t2"
      using equ_involutive_left equ_dec_pi by blast}
  {assume ii: "nabla \<turnstile> swap pi t1 \<approx> t2"
    then show "nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
      using equ_involutive_left equ_equivariance by blast}
qed

lemma equ_involutive_right: 
  shows "nabla \<turnstile> t1 \<approx> swap (rev pi) (swap pi t2) = nabla \<turnstile> t1 \<approx> t2"
  using equ_dec_pi[of nabla pi t1 t2] equ_equivariance[of nabla t1 t2 pi] 
    equ_pi_to_right[of nabla t1 pi \<open>swap pi t2\<close>]
  by auto

lemma equ_pi1_pi2_add: 
  assumes "\<forall>a\<in> ds pi1 pi2. nabla\<turnstile>a\<sharp>t"
  shows "nabla\<turnstile>swap pi1 t \<approx> swap pi2 t"
proof-
  have "nabla \<turnstile> t \<approx> swap (rev pi1 @ pi2) t" 
    using assms ds_rev equ_pi_right by simp
  hence "nabla \<turnstile> t \<approx> swap (rev pi1) (swap pi2 t)"
    using swap_append by auto
  then show "nabla\<turnstile>swap pi1 t \<approx> swap pi2 t"
    using equ_pi_to_right by simp
qed

lemma pi_right_equ: 
  assumes "nabla \<turnstile> t \<approx> swap pi t"
  shows "\<forall>a\<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  using assms pi_right_equ_help by blast

lemma equ_pi1_pi2_dec:  
  assumes "nabla \<turnstile> swap pi1 t \<approx> swap pi2 t"
  shows "\<forall> a \<in> ds pi1 pi2. nabla\<turnstile>a \<sharp> t"
proof-
  have "nabla \<turnstile> t \<approx> swap ((rev pi1) @ pi2) t"
    using assms equ_pi_to_right swap_append by simp
  then show "\<forall> a \<in> ds pi1 pi2. nabla\<turnstile>a \<sharp> t"
    using pi_right_equ ds_rev[of pi1 pi2] by simp
qed

lemma equ_weak: 
  assumes "nabla1 \<turnstile> t1 \<approx> t2"
  shows "(nabla1 \<union> nabla2) \<turnstile> t1 \<approx> t2"
  using assms by (erule_tac equ.induct) (auto simp add: fresh_weak)

text \<open>
  No term can be equal to one of its proper subterm.
\<close>

lemma psub_trm_not_equ: 
  shows "\<forall> t2 \<in> psub_trms t1. (\<not>(\<exists> pi. (nabla \<turnstile> t1 \<approx> swap pi t2)))"
proof
  fix t2
  assume i: "t2 \<in> psub_trms t1"
  show "\<not> (\<exists>pi. nabla \<turnstile> t1 \<approx> swap pi t2)"
  proof
    assume "\<exists>pi. nabla \<turnstile> t1 \<approx> swap pi t2"
    then obtain pi where H:
      "nabla \<turnstile> t1 \<approx> swap pi t2" by blast

    from equ_depth[OF H]
    have "depth t1 = depth (swap pi t2)"
      by simp
    hence "depth t1 = depth t2" 
      by simp
    moreover have "depth t2 < depth t1"
      using i depth_psub_trms 
      by simp

    ultimately show False by auto
  qed
qed


(*<*)
end 
(*>*)
