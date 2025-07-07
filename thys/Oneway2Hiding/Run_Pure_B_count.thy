theory Run_Pure_B_count

imports Definition_Pure_O2H

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax


context pure_o2h
begin
section \<open>Defining and Representing the Adversary $B$ with Counting\<close>
text \<open>For the proof of the O2H, we need an intermediate operator \<open>U_S'\<close>.
The operator \<open>U_S'\<close> counts, how many oracle queries were made so far in a separate register 
(modelled by \<open>nat\<close>).\<close>

text \<open>Given the initial state \<open>init \<otimes>\<^sub>s ket 0 :: 'mem \<times> nat\<close>, 
we run the adversary with counting by adding $+1$ in \<open>{0..<d+1}\<close>. 
\<open>run_B_count_upto n\<close> is the function that allows the adversary \<open>n\<close> calls to the query oracle.
\<open>run_B_count\<close> allows exactly \<open>d\<close> query calls (ie.\ queries up to the full query depth $d$).
The final state called $\Psi_{count}$ in the paper is represented by \<open>run_B_count\<close>.\<close>
  (* representation of adversarial run:
  init \<Rightarrow> UA \<Rightarrow> Uquery H \<Rightarrow> U_S' \<Rightarrow> UA \<Rightarrow> Uquery H \<Rightarrow> U_S' \<Rightarrow> \<dots> \<Rightarrow> Uquery H \<Rightarrow> UA *)
  (* Notation: \<Psi>_count == run_B_count *)

definition \<open>run_B_count_upto n = 
  run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H\<close>

definition \<open>run_B_count = run_pure_adv d (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H\<close>

lemma run_B_count_altdef: "run_B_count = run_B_count_upto d"
  unfolding run_B_count_def run_B_count_upto_def by auto

lemma run_B_count_upto_I:
  "run_B_count_upto (Suc n) = (UA (Suc n) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (X_for_C;Y_for_C) (Uquery H) *\<^sub>V
    U_S' S *\<^sub>V run_B_count_upto n"
  unfolding run_B_count_upto_def by auto

text \<open>This version of the O2H is only for pure states. 
Therefore, the norm of states is always $1$.\<close>
lemma norm_run_B_count_upto:
  assumes "n<d+1"
  shows "norm (run_B_count_upto n) \<le> 1"
  using assms proof (induct n)
  case 0
  then show ?case unfolding run_B_count_upto_def init_B_count_def using norm_UA_0_init 
    by (auto simp add: tensor_op_ell2 norm_tensor_ell2 norm_init)
next
  case (Suc n)
  have "norm (run_B_count_upto (Suc n)) \<le> norm ((UA (Suc n) \<otimes>\<^sub>o (id_cblinfun::nat update))) * 
    norm ((X_for_C;Y_for_C) (Uquery H) *\<^sub>V U_S' S *\<^sub>V
    run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)"
    unfolding run_B_count_upto_def run_pure_adv.simps using norm_cblinfun by blast
  also have "\<dots> \<le> norm ((UA (Suc n) \<otimes>\<^sub>o (id_cblinfun::nat update))) * 
    norm (run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)" 
    by (simp add: iso_H_C iso_U_S' isometry_preserves_norm norm_isometry)
  also have "\<dots> \<le> 1" using norm_UA Suc by (simp add: mult_le_one run_B_count_upto_def tensor_op_norm)
  finally show ?case by linarith
qed

lemma norm_run_B_count:
  "norm run_B_count \<le> 1"
  unfolding run_B_count_altdef using norm_run_B_count_upto by auto

subsection \<open>Representing the run of Adversary $B$ with counting as a finite sum\<close>

text \<open>Preparation for representation of \<open>run_B_count\<close>\<close>

lemma tensor_proj_UqueryH_commute:
  "(id_cblinfun \<otimes>\<^sub>o proj_classical_set A) o\<^sub>C\<^sub>L (X_for_C;Y_for_C) (Uquery H) = 
    (X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o proj_classical_set A)"
  by (subst UqueryH_tensor_id_cblinfunC)+ (auto intro!: tensor_ell2_extensionality simp add: tensor_op_ell2)

text \<open>How the counting unitary \<open>Uc\<close> behaves with respect to projections on the counting register.\<close>
lemma proj_Uc:
  assumes "m>0"
  shows "proj_classical_set {m} o\<^sub>C\<^sub>L Uc = Uc o\<^sub>C\<^sub>L 
  (if m<d+1 then proj_classical_set {m-1} else proj_classical_set {m})"
proof (intro equal_ket, goal_cases)
  case (1 x)
  consider (less) "x<d" | (eq) "x=d" | (greater) "x>d" by linarith
  then show ?case
  proof (cases)
    case less
    have "proj_classical_set {m} *\<^sub>V ket (Suc x) = ket (Suc x)" if "m=x+1" using that
        proj_classical_set_elem by force
    moreover have "proj_classical_set {m} *\<^sub>V ket (Suc x) = 0" if "m\<noteq>x+1" using that
      by (simp add: proj_classical_set_not_elem) 
    moreover have "(Uc o\<^sub>C\<^sub>L(if m < d + 1 then proj_classical_set {m - 1} else proj_classical_set {m}))
       *\<^sub>V ket x = ket (Suc x)" if "m=x+1"
      by (simp add: Uc_ket_less less proj_classical_set_elem that)
    moreover have "(Uc o\<^sub>C\<^sub>L(if m < d + 1 then proj_classical_set {m - 1} else proj_classical_set {m}))
       *\<^sub>V ket x = 0" if "m\<noteq>x+1"
      using assms less proj_classical_set_not_elem that
      by (smt (verit) Suc_eq_plus1 Suc_pred' basic_trans_rules(20) cblinfun.real.zero_right 
          cblinfun_apply_cblinfun_compose not_less_eq singletonD)
    ultimately show ?thesis using Uc_ket_less[OF less] less by force
  next
    case eq
    then show ?thesis using Uc_ket_d assms proj_classical_set_not_elem 
      by (smt (verit, best) One_nat_def Set.ball_empty Suc_pred ab_semigroup_add_class.add_ac(1) 
          cblinfun.real.zero_right insertE less_add_eq_less less_add_same_cancel2 less_numeral_extra(1)
          nat_less_le plus_1_eq_Suc simp_a_oCL_b')
  next
    case greater
    show ?thesis using Uc_ket_greater[OF greater] greater proj_classical_set_elem 
      by (smt (verit, ccfv_SIG) Suc_eq_plus1 basic_trans_rules(20) cblinfun.real.zero_right 
          less_diff_conv not_less_eq proj_classical_set_not_elem simp_a_oCL_b' singleton_iff)
  qed
qed


lemma proj_classical_set_over_Uc:
  "proj_classical_set {Suc n..} o\<^sub>C\<^sub>L Uc = Uc o\<^sub>C\<^sub>L proj_classical_set 
(if n>d then {Suc n..} else {n..}-{d})"
proof (intro equal_ket, goal_cases)
  case (1 x)
  consider (less) "x<d" | (eq) "x=d" | (greater) "x>d" by linarith
  then show ?case
  proof (cases)
    case less
    have "proj_classical_set {Suc n..} *\<^sub>V ket (Suc x) = 0" if "x<n"
      by (simp add: proj_classical_set_upto that)
    moreover have "Uc *\<^sub>V proj_classical_set ({n..} - {d}) *\<^sub>V ket x = 0" if "x<n"
      by (subst proj_classical_set_not_elem) (use that in \<open>auto\<close>)
    moreover have "proj_classical_set {Suc n..} *\<^sub>V ket (Suc x) = ket (Suc x)" if "x\<ge>n"
      by (simp add: Proj_fixes_image ccspan_superset' proj_classical_set_def that)
    moreover have  "Uc *\<^sub>V proj_classical_set ({n..} - {d}) *\<^sub>V ket x = ket (Suc x)" if "x\<ge>n" 
      by (subst proj_classical_set_elem) (use that less Uc_ket_less[OF less] in \<open>auto\<close>)
    ultimately show ?thesis using Uc_ket_less[OF less] less proj_classical_set_upto by force
  next
    case eq
    have "(proj_classical_set {Suc n..} o\<^sub>C\<^sub>L Uc) *\<^sub>V ket x = 0" 
      using Uc_ket_d proj_classical_set_not_elem eq by (simp add: proj_classical_set_upto)
    moreover have 
      "(Uc o\<^sub>C\<^sub>L proj_classical_set (if d < n then {Suc n..} else {n..} - {d})) *\<^sub>V ket x = 0"
      using proj_classical_set_not_elem eq 
      by (metis (full_types) Diff_not_in cblinfun.real.zero_right cblinfun_apply_cblinfun_compose
          less_SucI proj_classical_set_upto)
    ultimately show ?thesis by force
  next
    case greater
    have "proj_classical_set {Suc n..} *\<^sub>V ket x = Uc *\<^sub>V proj_classical_set {Suc n..} *\<^sub>V ket x" 
      if "d<n" by (cases "x<n+1")(auto simp add: proj_classical_set_not_elem Uc_ket_greater 
          greater proj_classical_set_elem)
    then show ?thesis using Uc_ket_greater[OF greater] greater proj_classical_set_elem 
      by (smt (verit, ccfv_SIG) atLeast_iff basic_trans_rules(19) cblinfun_apply_cblinfun_compose 
          diff_Suc_1 insertCI insertE insert_Diff_single le_simps(2) lessI less_natE linorder_neqE_nat 
          linorder_not_less zero_less_Suc)
  qed
qed

text \<open>How the state after the $n$-th query behaves with respect to projections.\<close>

lemma run_B_count_proj_gr:
  assumes "m>n"
  shows "Proj_ket_set {m} *\<^sub>V run_B_count_upto n = 0"
  using assms proof (induction n arbitrary: m)
  case 0
  have "proj_classical_set {m} *\<^sub>V ket 0 = 0"
    by (simp add: "0.prems" proj_classical_set_not_elem)
  then show ?case unfolding run_B_count_upto_def init_B_count_def Proj_ket_set_def
    by (auto simp add: tensor_op_ell2)
next
  case (Suc n)
  have 1: "Proj_ket_set {m} *\<^sub>V run_B_count_upto (Suc n) = 
    (UA (Suc n) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (X_for_C;Y_for_C) (Uquery H) *\<^sub>V
    Proj_ket_set {m} *\<^sub>V U_S' S *\<^sub>V run_B_count_upto n" 
    unfolding Proj_ket_set_def
    by (subst run_B_count_upto_I)(smt (verit, best) UqueryH_tensor_id_cblinfunC 
        cblinfun_compose_id_left cblinfun_compose_id_right comp_tensor_op lift_cblinfun_comp(4))
  have "m>0" using Suc(2) by linarith
  then have 2: "Proj_ket_set {m} *\<^sub>V U_S' S *\<^sub>V run_B_count_upto n =
    (S_embed S \<otimes>\<^sub>o (Uc o\<^sub>C\<^sub>L (if m<d+1 then proj_classical_set {m-1} else proj_classical_set {m}))) 
    *\<^sub>V run_B_count_upto n + (not_S_embed S \<otimes>\<^sub>o proj_classical_set {m}) *\<^sub>V run_B_count_upto n"
    unfolding U_S'_def Proj_ket_set_def by (subst proj_Uc[symmetric])
      (auto simp add: cblinfun.add_left cblinfun.add_right comp_tensor_op
        cblinfun_apply_cblinfun_compose[symmetric] simp del: cblinfun_apply_cblinfun_compose)
  have 3: "(S_embed S \<otimes>\<^sub>o (Uc o\<^sub>C\<^sub>L (if m<d+1 then proj_classical_set {m-1} else proj_classical_set {m}))) 
    *\<^sub>V run_B_count_upto n = 0"
  proof (cases "m<d+1")
    case True
    have *: "(S_embed S \<otimes>\<^sub>o (Uc o\<^sub>C\<^sub>L proj_classical_set {m-1})) *\<^sub>V run_B_count_upto n = 
      (S_embed S \<otimes>\<^sub>o Uc) *\<^sub>V Proj_ket_set {m-1} *\<^sub>V run_B_count_upto n" 
      by (simp add: Proj_ket_set_def comp_tensor_op lift_cblinfun_comp(4))
    have "(S_embed S \<otimes>\<^sub>o Uc) *\<^sub>V Proj_ket_set {m-1} *\<^sub>V run_B_count_upto n = 0"
      by (simp add: Suc(1) Suc(2) less_diff_conv)
    then show ?thesis using True * by auto  
  next
    case False
    have "n<m" using Suc(2) by auto
    have "(S_embed S \<otimes>\<^sub>o (Uc o\<^sub>C\<^sub>L proj_classical_set {m})) *\<^sub>V run_B_count_upto n = 0" 
      using Suc(1)[OF \<open>n<m\<close>] unfolding Proj_ket_set_def
      by (metis (no_types, opaque_lifting) cblinfun.zero_right 
          cblinfun_apply_cblinfun_compose cblinfun_compose_id_right comp_tensor_op)
    then show ?thesis using False by auto
  qed 
  have *: "(not_S_embed S \<otimes>\<^sub>o proj_classical_set {m}) *\<^sub>V run_B_count_upto n =
    (not_S_embed S \<otimes>\<^sub>o id_cblinfun) *\<^sub>V Proj_ket_set {m} *\<^sub>V run_B_count_upto n"
    unfolding Proj_ket_set_def by (metis cblinfun_apply_cblinfun_compose cblinfun_compose_id_left 
        cblinfun_compose_id_right comp_tensor_op)
  have 4: "(not_S_embed S \<otimes>\<^sub>o proj_classical_set {m}) *\<^sub>V run_B_count_upto n = 0" 
    unfolding * by (simp add: Suc(1) Suc.prems Suc_lessD)
  show ?case by (subst 1, subst 2, subst 3, subst 4) auto
qed


lemma run_B_count_upto_proj_over:
  "Proj_ket_set {n+1..} *\<^sub>V run_B_count_upto n = 0"
proof (induction n)
  case 0
  then show ?case unfolding run_B_count_upto_def init_B_count_def Proj_ket_set_def
    using proj_classical_set_upto[of 0] by (auto simp add: tensor_op_ell2)
next
  case (Suc n)
  have 1: "Proj_ket_set {Suc n + 1..} *\<^sub>V run_B_count_upto (Suc n) = 
    (UA (Suc n) \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (X_for_C;Y_for_C) (Uquery H) *\<^sub>V
    Proj_ket_set {Suc n + 1..} *\<^sub>V U_S' S *\<^sub>V run_B_count_upto n" 
    unfolding Proj_ket_set_def
    by (subst run_B_count_upto_I) (metis (no_types, lifting) 
        cblinfun_apply_cblinfun_compose tensor_proj_UA_tensor_commute tensor_proj_UqueryH_commute)
  have 2: "Proj_ket_set {Suc n + 1..} *\<^sub>V U_S' S *\<^sub>V run_B_count_upto n =
    (S_embed S \<otimes>\<^sub>o Uc) *\<^sub>V Proj_ket_set (if Suc n>d then {Suc (Suc n)..} else {Suc n..}-{d}) *\<^sub>V 
    run_B_count_upto n + 
    (not_S_embed S \<otimes>\<^sub>o id_cblinfun) *\<^sub>V Proj_ket_set {Suc n +1..} *\<^sub>V run_B_count_upto n "
    using proj_classical_set_over_Uc[symmetric] unfolding U_S'_def Proj_ket_set_def
    by (auto simp add: cblinfun.add_left cblinfun.add_right comp_tensor_op
        cblinfun_apply_cblinfun_compose[symmetric] simp del: cblinfun_apply_cblinfun_compose)
  have "Proj_ket_set {Suc n} *\<^sub>V run_B_count_upto n + 
        Proj_ket_set {Suc (Suc n)..} *\<^sub>V run_B_count_upto n = 0"
    using proj_classical_set_split_Suc[of "Suc n"] Suc unfolding Proj_ket_set_def 
    by (simp add: cblinfun.add_left tensor_op_right_add proj_classical_set_def)
  then have Suc_Suc: "Proj_ket_set  {Suc (Suc n)..} *\<^sub>V run_B_count_upto n = 0"
    using run_B_count_proj_gr[of "n" "Suc n"] by auto
  have 3: "(S_embed S \<otimes>\<^sub>o Uc) *\<^sub>V Proj_ket_set (if Suc n>d then {Suc (Suc n)..} else {Suc n..}-{d})
     *\<^sub>V run_B_count_upto n = 0"
  proof (cases "Suc n > d")
    case True
    show ?thesis using Suc_Suc True by auto
  next
    case False
    have ket: "ket ` {Suc n..} = insert (ket d) (ket ` ({Suc n..} - {d}))" using False by auto
    have "proj_classical_set {Suc n..} = proj (ket d) + proj_classical_set ({Suc n..} - {d})"
      unfolding proj_classical_set_def ket by (intro Proj_orthog_ccspan_insert) auto
    then have "Proj_ket_set {d} *\<^sub>V run_B_count_upto n +
      Proj_ket_set ({Suc n..} - {d}) *\<^sub>V run_B_count_upto n = 0"
      by (metis (no_types, opaque_lifting) One_nat_def Proj_ket_set_def Suc add_Suc_right 
          cblinfun.add_left image_empty image_insert nat_arith.rule0 proj_classical_set_def 
          tensor_op_right_add)
    then have "Proj_ket_set ({Suc n..} - {d}) *\<^sub>V run_B_count_upto n = 0" 
      using False run_B_count_proj_gr by auto
    then show ?thesis using False by auto
  qed 
  have 4: "(not_S_embed S \<otimes>\<^sub>o id_cblinfun) *\<^sub>V Proj_ket_set {Suc (Suc n)..} *\<^sub>V run_B_count_upto n = 0"
    using Suc_Suc by auto
  show ?case by (subst 1, subst 2) (auto simp add: 3 4)
qed


text \<open>How \<open>\<Psi>s\<close> relate to \<open>run_B_count\<close>. We can write \<open>run_B_count\<close> as a sum counting over all 
valid ket states in the counting register.\<close>

lemma run_B_count_upto_split:
  "run_B_count_upto n = (\<Sum>i<n+1. \<Psi>s i (run_B_count_upto n) \<otimes>\<^sub>s ket i)"
proof -
  have "run_B_count_upto n = 
    (\<Sum>i<n+1. (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)) *\<^sub>V run_B_count_upto n + 
    Proj_ket_set {n+1..} *\<^sub>V run_B_count_upto n" 
    using id_cblinfun_tensor_split_finite 
    by (smt (verit) Compl_lessThan cblinfun.add_left cblinfun_id_cblinfun_apply finite_lessThan)
  also have "\<dots> = (\<Sum>i<n+1. (tensor_ell2_right (ket i)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)*)) 
    *\<^sub>V run_B_count_upto n" using run_B_count_upto_proj_over by auto
  finally have *: "run_B_count_upto n = 
    (\<Sum>i<n+1. (tensor_ell2_right (ket i)* *\<^sub>V run_B_count_upto n) \<otimes>\<^sub>s ket i)"
    by (smt (verit, ccfv_SIG) cblinfun.sum_left cblinfun_apply_cblinfun_compose sum.cong 
        tensor_ell2_right.rep_eq)
  show ?thesis unfolding \<Psi>s_def by (subst *)(use lessThan_Suc_atMost in \<open>auto\<close>)
qed

lemma run_B_count_split:
  "run_B_count = (\<Sum>i<d+1. \<Psi>s i run_B_count \<otimes>\<^sub>s ket i)"
  unfolding run_B_count_altdef by (rule run_B_count_upto_split)


lemma run_B_count_projection:
  "Proj_ket_set {..<n+1} *\<^sub>V (run_B_count_upto n) = (run_B_count_upto n)"
proof -
  have v: "run_B_count_upto n = (\<Sum>i<n+1. \<Psi>s i (run_B_count_upto n) \<otimes>\<^sub>s ket i)"
    using run_B_count_upto_split by auto 
  show ?thesis by (subst v, subst (2) v, subst cblinfun.sum_right) 
      (intro sum.cong, auto intro!: Proj_ket_set_vec)
qed




end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end