theory Pure_O2H


imports Run_Pure_B
  Run_Pure_B_count

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax

context pure_o2h
begin


text \<open>The probability that the find event occurs. That is the event that the adversary $B$ notices
that a query in $S$ was made.\<close>
definition \<open>Pfind' = (norm (Snd (id_cblinfun - selfbutter (ket empty)) *\<^sub>V run_B))\<^sup>2\<close>


text \<open>What happens only to the first part of the memory when executing \<open>B\<close> or \<open>B_count\<close> is the same.
  This is recorded in \<open>\<Phi>\<close>. The second registers only serve as counting registers.\<close>
definition \<Phi>s where
  "\<Phi>s n = run_pure_adv n (\<lambda>i. UA i) (\<lambda>_. not_S_embed S) init X Y H"


text \<open>We ensure that the $\Phi s$ is the same as the left part of $\Psi_{count}$ 
(ie.\ \<open>run_B_count\<close>) with right part $\mid 0 \rangle$.\<close>

lemma \<Psi>s_run_B_count_upto_eq_\<Phi>s:
  assumes "i<d+1"
  shows "\<Psi>s 0 (run_B_count_upto i) = \<Phi>s i"
  using le0 proof (induction i rule: Nat.dec_induct)
  case base
  then show ?case unfolding run_B_count_upto_def init_B_count_def \<Phi>s_def 
    by (auto simp add: tensor_op_ell2 tensor_ell2_ket \<Psi>s_def)
next
  case (step n)
  then have "n<d" using assms by auto
  have "\<Psi>s 0 (run_B_count_upto (Suc n)) = UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V
    \<Psi>s 0 (U_S' S *\<^sub>V Proj_ket_set {..<n+1} *\<^sub>V
    run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)"
    using run_B_count_projection 
    by (auto simp add: \<Psi>s_id_cblinfun UqueryH_tensor_id_cblinfunC  run_B_count_upto_def)
  also have "\<dots> = UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V
    (not_S_embed S *\<^sub>V tensor_ell2_right (ket 0)* *\<^sub>V
    run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)"
    using \<Psi>s_U_S'_Proj_ket_upto[OF \<open>n<d\<close>]
    by (metis (no_types, lifting) \<Psi>s_def cblinfun_apply_cblinfun_compose)
  also have "\<dots> = UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V 
    not_S_embed S *\<^sub>V run_pure_adv n UA (\<lambda>_. not_S_embed S) init X Y H"
    using step by (simp add: \<Phi>s_def \<Psi>s_def run_B_count_upto_def)
  finally show ?case unfolding \<Phi>s_def by auto
qed

text \<open>Analogously, $\Phi s$ is the same as the left part of $\Psi_{right}$ (ie.\ \<open>run_B\<close>) with
right part $\mid embed\ 0\rangle$.\<close>

lemma \<Psi>s_run_B_upto_eq_\<Phi>s:
  assumes "i\<le>d"
  shows "\<Psi>s empty (run_B_upto i) = \<Phi>s i"
  using le0 proof (induction i rule: Nat.dec_induct)
  case base
  then show ?case unfolding run_B_upto_def init_B_def \<Phi>s_def 
    by (auto simp add: tensor_op_ell2 tensor_ell2_ket \<Psi>s_def)
next
  case (step n)
  then have "n<d" using assms by auto
  have "\<Psi>s empty (run_B_upto (Suc n)) = UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V
    \<Psi>s empty ((US S n) *\<^sub>V Proj_ket_upto (has_bits_upto n) *\<^sub>V run_B_upto n)"
    by (subst run_B_upto_I, subst run_B_projection[OF \<open>n<d\<close>])
      (auto simp add: \<Psi>s_id_cblinfun UqueryH_tensor_id_cblinfunB)
  also have "\<dots> = UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V
    (not_S_embed S *\<^sub>V tensor_ell2_right (ket empty)* *\<^sub>V run_B_upto n)"
    using \<Psi>s_US_Proj_ket_upto[OF \<open>n<d\<close>]
    by (metis (no_types, lifting) \<Psi>s_def cblinfun_apply_cblinfun_compose)
  also have "\<dots> = UA (Suc n) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V 
    not_S_embed S *\<^sub>V run_pure_adv n UA (\<lambda>_. not_S_embed S) init X Y H"
    using step by (simp add: \<Phi>s_def \<Psi>s_def run_B_upto_def init_B_count_def init_B_def)
  finally show ?case unfolding \<Phi>s_def by auto
qed

text \<open>For the version of o2h with \<open>norm UA \<le> 1\<close>, we need to introduce the following error term:
when an adversary does not terminate, we get an additional term in the Pfind.\<close>
definition "P_nonterm = (norm run_B_count)\<^sup>2 - (norm run_B)\<^sup>2"

text \<open>The One-Way-to-Hiding Lemma for pure states.
Intuition: The difference of two games where we may change queries on a set $S$ in game $B$ can 
be bounded by the fining event \<open>Pfind'\<close>.
Proof idea: We introduce an intermediate game $B_{count}$ and show first equivalence between
$A$ and the left part of $B_{count}$ in $\mid 0\rangle$ and then equivalence of $B_{count}$ and $B$
in $\mid 0\rangle$.\<close>
lemma pure_o2h: \<open>(norm ((run_A \<otimes>\<^sub>s ket empty) - run_B))\<^sup>2 \<le> (d+1) * Pfind' + d * P_nonterm\<close>
proof -
  define \<Psi>s' where "\<Psi>s' = (\<lambda>i::nat. \<Psi>s i run_B_count)"
  have eq16: "run_B_count = (\<Sum>i<d+1. \<Psi>s' i \<otimes>\<^sub>s (ket i))"
    using run_B_count_split \<Psi>s'_def by auto
      \<comment>\<open>Equation (16)\<close>

\<comment> \<open>The operation $N'$ connects the results of the game $A$ and the counting game $B_{count}$.\<close>

  define N':: "('mem \<times> nat) update" where 
    "N' = (id_cblinfun \<otimes>\<^sub>o (\<Sum>i<d+1. butterfly (ket 0) (ket i))) o\<^sub>C\<^sub>L Proj_ket_set {..<d+1}"

  have *: "sum (Rep_ell2 (ket c)) {..<d + 1} *\<^sub>C ket 0 = ket 0" if "c<d+1" for c
    by (metis lessThan_iff proj_classical_set_elem sum_butterfly_ket0 sum_butterfly_ket0' that)
  have N'_ket: "N' (ket (x,c)) = ket (x,0)" if "c<d+1" for x c
    unfolding N'_def Proj_ket_set_def 
    apply (subst tensor_ell2_ket[symmetric], subst comp_tensor_op, subst tensor_op_ell2)
    apply (subst (2) cblinfun_apply_cblinfun_compose, subst sum_butterfly_ket0')
    apply (subst *[OF that])
    by (auto simp add: tensor_ell2_ket[symmetric])
  have N'_tensor_ket: "N' *\<^sub>V y \<otimes>\<^sub>s ket c = y \<otimes>\<^sub>s ket 0" if "c<d+1" for c y unfolding N'_def
  proof (subst cblinfun_apply_cblinfun_compose, subst Proj_ket_set_vec)
    show "c \<in> {..<d + 1}" using that by auto
    then show "(id_cblinfun \<otimes>\<^sub>o (\<Sum>i<d + 1. butterfly (ket 0) (ket i))) *\<^sub>V y \<otimes>\<^sub>s ket c = y \<otimes>\<^sub>s ket 0" 
      by (subst tensor_op_ell2, subst sum_butterfly_ket0) auto
  qed

  have N'_UA: "N' o\<^sub>C\<^sub>L (UA i \<otimes>\<^sub>o id_cblinfun) = (UA i \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L N'" for i
    unfolding N'_def by (simp add: Proj_ket_set_def comp_tensor_op)
      \<comment>\<open>\<open>N'\<close> commutes with \<open>UA\<close>\<close>

  have N'_UqueryH: "N' o\<^sub>C\<^sub>L (X_for_C;Y_for_C) (Uquery H) = (X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L N'"
    unfolding UqueryH_tensor_id_cblinfunC by (simp add: N'_def Proj_ket_set_def comp_tensor_op)
      \<comment>\<open>\<open>N'\<close> commutes with the oracle queries\<close>

  have N'_B_count: "N' o\<^sub>C\<^sub>L U_S' S = N'" 
  proof (unfold N'_def, intro equal_ket, safe, goal_cases)
    case (1 a b)
    show ?case proof (cases "b<d+1")
      case True
      obtain y where y: "Uc *\<^sub>V ket b = ket y" "y<d+1"
        using True Uc_ket_range_valid by auto
      have proj_y:"proj_classical_set {..<Suc d} *\<^sub>V ket y = ket y" using \<open>y<d+1\<close>
        by (metis Suc_eq_plus1 lessThan_iff proj_classical_set_elem)
      have proj_b:"proj_classical_set {..<Suc d} *\<^sub>V ket b = ket b" using True 
        by (metis Suc_eq_plus1 lessThan_iff proj_classical_set_elem)
      have butter_y: "(\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket y = ket 0" 
        using sum_butterfly_ket0 y(2) by blast
      have butter_b: "(\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket b = ket 0" 
        using sum_butterfly_ket0 True by blast
      have "(S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s (\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket y +
        (not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s (\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket b =
        ket a \<otimes>\<^sub>s (\<Sum>i<d+1. butterfly (ket 0) (ket i)) *\<^sub>V ket b"
        unfolding butter_y butter_b by (metis S_embed_not_S_embed_add tensor_ell2_add1)
      then show ?thesis using y proj_y proj_b
        by(auto simp add: tensor_op_ell2 tensor_op_ket cblinfun.add_right
            U_S'_ket_split sum_butterfly_ket0 tensor_ell2_add1[symmetric] Proj_ket_set_def)
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) S_embed_not_S_embed_add U_S'_ket_split Uc_ket_greater 
            lift_cblinfun_comp(4) not_less_eq semiring_norm(174) tensor_ell2_add1 tensor_ell2_ket) 
    qed 

  qed  
    \<comment>\<open>\<open>N' U_S' = N'\<close>\<close>

  have "0<d+1" using d_gr_0 by auto
  have N'_init_B_count: "N' *\<^sub>V init_B_count = init_B_count" 
    unfolding init_B_count_def using N'_def N'_tensor_ket[OF \<open>0<d+1\<close>] by blast
      \<comment>\<open>the initial state of \<open>B_count\<close> is invariant under \<open>N'\<close>\<close>

  have N'_run_B_count_upto_N'_run_A: "N' *\<^sub>V run_B_count_upto n = 
    N' *\<^sub>V (run_pure_adv n UA (\<lambda>_. id_cblinfun) init X Y H \<otimes>\<^sub>s ket (0))" for n
    unfolding run_B_count_upto_def run_A_def
  proof (induction n)
    case 0
    have "N' *\<^sub>V U_S' S *\<^sub>V (UA 0 \<otimes>\<^sub>o id_cblinfun) *\<^sub>V init_B_count = 
      (UA 0 \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L N') *\<^sub>V init_B_count" 
      by (auto simp add: cblinfun_apply_cblinfun_compose[symmetric] N'_B_count 
          N'_init_B_count N'_UA cblinfun_compose_assoc[symmetric]
          simp del: cblinfun_apply_cblinfun_compose)
    also have "\<dots> = (UA 0 \<otimes>\<^sub>o id_cblinfun) *\<^sub>V init_B_count" using N'_init_B_count by auto
    finally show ?case by (auto simp add: N'_UA N'_tensor_ket tensor_op_ell2 init_B_count_def)
  next
    case (Suc n)
    let ?run_pure_adv_B_count_d = 
      "run_pure_adv n (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H"
    let ?run_pure_adv_A_d = "run_pure_adv n UA (\<lambda>_. id_cblinfun) init X Y H"
    have "N' *\<^sub>V run_pure_adv (n+1) (\<lambda>i. UA i \<otimes>\<^sub>o id_cblinfun) (\<lambda>_. U_S' S) 
      init_B_count X_for_C Y_for_C H =
      (UA (Suc n) \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L (X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L N') *\<^sub>V ?run_pure_adv_B_count_d" 
      using N'_B_count N'_UA N'_UqueryH
      by (auto simp add: cblinfun_apply_cblinfun_compose[symmetric]
          cblinfun_compose_assoc[symmetric] simp del: cblinfun_apply_cblinfun_compose)
        (auto simp add: cblinfun_compose_assoc)
    also have "\<dots> = (UA (Suc n) \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L (X_for_C;Y_for_C) (Uquery H)) *\<^sub>V
      N' *\<^sub>V ?run_pure_adv_A_d \<otimes>\<^sub>s ket 0"
      by (simp add: Suc.IH)
    also have "\<dots> = (N' o\<^sub>C\<^sub>L UA (Suc n) \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L (X_for_C;Y_for_C) (Uquery H)) *\<^sub>V
      ?run_pure_adv_A_d \<otimes>\<^sub>s ket 0"
      using N'_B_count N'_UA N'_UqueryH
      by (auto simp add: cblinfun_apply_cblinfun_compose[symmetric]
          cblinfun_compose_assoc[symmetric] simp del: cblinfun_apply_cblinfun_compose)
        (auto simp add: cblinfun_compose_assoc)
    finally show ?case 
      by (auto simp add: UqueryH_tensor_id_cblinfunC tensor_op_ell2 nth_append)
  qed

  have N'_run_B_count_N'_run_A: "N' *\<^sub>V run_B_count = N' *\<^sub>V (run_A \<otimes>\<^sub>s ket (0))"
    unfolding run_B_count_altdef by (subst N'_run_B_count_upto_N'_run_A)
      (auto simp add: run_A_def)
      \<comment>\<open>\<open>N'\<close> does not touch the second part of the memory and \<open>run_B_count\<close> and \<open>run_A\<close> 
      do the same on \<open>'mem\<close>\<close>

  then have N'_run_B_count_run_A: "N' *\<^sub>V run_B_count = run_A \<otimes>\<^sub>s ket 0"
    by (simp add: N'_tensor_ket)
      \<comment> \<open>Relation between $A$ and $B_{count}$\<close>


  have "(\<Sum>i<d+1. \<Psi>s' i \<otimes>\<^sub>s ket (0::nat)) = N' *\<^sub>V run_B_count" unfolding eq16 
    by (subst cblinfun.sum_right, intro sum.cong) (auto simp add: N'_tensor_ket)
  moreover have "N' *\<^sub>V run_B_count = run_A \<otimes>\<^sub>s ket (0::nat)" 
    unfolding N'_run_B_count_N'_run_A by (auto simp add: N'_tensor_ket)
  ultimately have \<Psi>s'_run_A:
    "(\<Sum>i<d+1. \<Psi>s' i \<otimes>\<^sub>s ket (0::nat)) = run_A \<otimes>\<^sub>s ket (0)" by auto

  have eq17: "run_A = (\<Sum>i<d+1. \<Psi>s' i)" 
  proof -
    have "run_A = (tensor_ell2_right (ket 0))* *\<^sub>V (run_A \<otimes>\<^sub>s ket (0::nat))" by auto
    also have "\<dots> = (\<Sum>i<d+1. \<Psi>s' i)"
      unfolding \<Psi>s'_run_A[symmetric] 
      by (subst tensor_ell2_sum_left[symmetric], subst tensor_ell2_right_adj_apply, auto) 
    finally show ?thesis by blast
  qed
    \<comment>\<open>Equation (17)\<close>
    \<comment> \<open>Representation of $A$ in terms of parts of states in $B_{count}$\<close>

  define \<Psi>sB where "\<Psi>sB = (\<lambda>i::bool list. \<Psi>s (list_to_l i) run_B)"
  have eq18: "run_B = (\<Sum>l\<in>len_d_lists. \<Psi>sB l \<otimes>\<^sub>s ket (list_to_l l))"
    by (subst run_B_split, unfold \<Psi>sB_def) auto
      \<comment>\<open>Equation (18)\<close>


  have \<Psi>sB_\<Phi>s: "\<Psi>sB empty_list = \<Phi>s d" by (simp add: \<Psi>sB_def \<Psi>s_run_B_upto_eq_\<Phi>s run_B_altdef)

  have eq19: "\<Psi>s' 0 = \<Psi>sB empty_list"
  proof -
    have "\<Psi>s' 0 = \<Psi>s 0 (run_B_count_upto d)" unfolding \<Psi>s'_def run_B_count_altdef by auto
    also have "\<dots> = \<Phi>s d" by (simp add: \<Psi>s_run_B_count_upto_eq_\<Phi>s)
    also have "\<dots> = \<Psi>sB empty_list" unfolding \<Psi>sB_\<Phi>s by auto
    finally show ?thesis by blast
  qed
    \<comment>\<open>Equation (19)\<close>
    \<comment> \<open>Relating the games $B$ and $B_{count}$.\<close>

\<comment> \<open>Now, we argue about the probabilits of the find event and the outcome states.\<close>

  have eq20:"norm (\<Psi>sB empty_list)^2 = (norm run_B)^2 - Pfind'"
  proof -
    have "norm (\<Psi>sB empty_list)^2 = (norm (\<Phi>s d))^2" unfolding \<Psi>sB_def run_B_altdef
      by (auto simp add: \<Psi>s_run_B_upto_eq_\<Phi>s)
    also have "\<dots> = (norm run_B)^2 - (norm (run_B - \<Phi>s d \<otimes>\<^sub>s ket empty))\<^sup>2"
    proof -
      have norm_B: "Re (run_B \<bullet>\<^sub>C run_B) = (norm run_B)^2" 
        unfolding power2_norm_eq_cinner[symmetric] norm_run_B by auto
      have cinner_B_\<Psi>: "(run_B) \<bullet>\<^sub>C (\<Phi>s d \<otimes>\<^sub>s ket empty) = (\<Phi>s d) \<bullet>\<^sub>C (\<Phi>s d)"
      proof -
        have "list_to_l x = empty \<Longrightarrow> x\<in>len_d_lists \<Longrightarrow> x=empty_list" for x
          using inj_list_to_l inj_onD by fastforce
        then have **: "\<Psi>sB empty_list \<bullet>\<^sub>C \<Psi>sB empty_list = sum ((\<lambda>l. \<Psi>sB l \<bullet>\<^sub>C \<Psi>sB empty_list * 
          (ket (list_to_l l) \<bullet>\<^sub>C ket empty))) len_d_lists" 
          by (subst sum.remove[OF finite_len_d_lists empty_list_len_d]) (auto intro!: sum.neutral)
        show ?thesis unfolding eq18 \<Psi>sB_\<Phi>s[symmetric] unfolding ** 
          by (auto simp add: cinner_sum_left)
      qed
      have "(norm (\<Phi>s d))^2 + (norm (run_B - \<Phi>s d \<otimes>\<^sub>s ket empty))^2 = 
        Re (\<Phi>s d \<bullet>\<^sub>C \<Phi>s d + (run_B - \<Phi>s d \<otimes>\<^sub>s ket empty) \<bullet>\<^sub>C (run_B - \<Phi>s d \<otimes>\<^sub>s ket empty))"
        unfolding power2_norm_eq_cinner' by auto
      also have "\<dots> = Re (2 * (\<Phi>s d \<bullet>\<^sub>C \<Phi>s d) + run_B \<bullet>\<^sub>C run_B - (run_B) \<bullet>\<^sub>C (\<Phi>s d \<otimes>\<^sub>s ket empty) - 
        (\<Phi>s d \<otimes>\<^sub>s ket empty) \<bullet>\<^sub>C (run_B))"
        by (auto simp add: algebra_simps norm_B)
      also have "\<dots> = (norm run_B)^2" by (subst (3)cinner_commute, unfold cinner_B_\<Psi>) 
          (auto simp add: norm_B)
      finally have "(norm (\<Phi>s d))^2 + (norm (run_B - \<Phi>s d \<otimes>\<^sub>s ket empty))^2 = (norm run_B)^2" by auto
      then show ?thesis by auto
    qed
    also have "\<dots> = (norm run_B)^2 - (norm (run_B - (tensor_ell2_right (ket empty)* *\<^sub>V run_B) 
      \<otimes>\<^sub>s ket empty))\<^sup>2"  unfolding run_B_def 
      by (subst \<Psi>s_run_B_upto_eq_\<Phi>s[symmetric])(auto simp add: \<Psi>s_def run_B_upto_def)
    also have "\<dots> = (norm run_B)^2 - Pfind'" unfolding Pfind'_def 
      by (auto simp add: Snd_def tensor_op_right_minus cblinfun.diff_left 
          id_cblinfun_selfbutter_tensor_ell2_right)
    finally show ?thesis by auto
  qed
    \<comment>\<open>Equation (20)\<close>

  have eq20':"norm (\<Psi>s' 0)^2 = norm (run_B)^2 - Pfind'" unfolding eq19 using eq20 by auto
      \<comment>\<open>Analog to Equation (20)\<close>

  have sum_to_1': "(\<Sum>i<d+1. norm (\<Psi>s' i)^2) = (norm run_B_count)^2"
  proof -
    have "(\<Sum>i<d+1. norm (\<Psi>s' i)^2) = 
      (\<Sum>i<d+1. norm ((\<Psi>s' i) \<otimes>\<^sub>s ket (i::nat))^2)"
      by (intro sum.cong, auto simp add: norm_tensor_ell2)
    also have "\<dots> = norm (\<Sum>i<d+1. (\<Psi>s' i) \<otimes>\<^sub>s ket (i::nat))^2"
      by (rule pythagorean_theorem_sum[symmetric], auto)
    also have "\<dots> = norm (run_B_count)^2" unfolding eq16 by auto
    finally show ?thesis by auto
  qed
  then have eq21': "(\<Sum>i=1..<d+1. norm (\<Psi>s' i)^2) = Pfind' + P_nonterm"
  proof -
    have "(\<Sum>i<d+1. norm (\<Psi>s' i)^2) =  
      norm (\<Psi>s' 0)^2 + (\<Sum>i=1..<d+1. norm (\<Psi>s' i)^2)"
      unfolding atLeast0AtMost  lessThan_atLeast0
      by (subst sum.atLeast_Suc_lessThan[OF \<open>0<d+1\<close>]) auto
    then show ?thesis using eq20' sum_to_1' unfolding P_nonterm_def by linarith 
  qed
    \<comment>\<open>Part of Equation (21)\<close>

  have sum_to_1:"(\<Sum>l\<in>len_d_lists. norm (\<Psi>sB l)^2) = (norm run_B)^2"
  proof -
    have "(\<Sum>l\<in>len_d_lists. norm (\<Psi>sB l)^2) = 
      (\<Sum>l\<in>len_d_lists. norm ((\<Psi>sB l) \<otimes>\<^sub>s ket (list_to_l l))^2)"
      by (intro sum.cong, auto simp add: norm_tensor_ell2)
    also have "\<dots> = norm (\<Sum>l\<in>len_d_lists. \<Psi>sB l \<otimes>\<^sub>s ket (list_to_l l))^2"
    proof -
      have "a \<noteq> a' \<Longrightarrow> a\<in>len_d_lists \<Longrightarrow> a'\<in>len_d_lists \<Longrightarrow> list_to_l a \<noteq> (list_to_l a')" 
        for a a' by (meson inj_list_to_l inj_onD)
      then show ?thesis by (subst pythagorean_theorem_sum) auto
    qed
    also have "\<dots> = norm (run_B)^2" unfolding eq18  by auto
    finally show ?thesis by auto
  qed
  then have eq21: "(\<Sum>l\<in>has_bits {0..<d}. norm (\<Psi>sB l)^2) = Pfind'"
  proof -
    have "(\<Sum>l\<in>len_d_lists. norm (\<Psi>sB l)^2) =  
      norm (\<Psi>sB empty_list)^2 + (\<Sum>l\<in>has_bits {0..<d}. norm (\<Psi>sB l)^2)" 
      by (subst sum.remove[of _ empty_list], unfold len_d_empty_has_bits) auto
    then show ?thesis using eq20 sum_to_1 unfolding P_nonterm_def by auto 
  qed
    \<comment>\<open>Part of Equation (21)\<close>

\<comment> \<open>Finally, we can subsume all our findings and prove the O2H Lemma.\<close>

  show ?thesis 
  proof -
    have "(norm (run_A \<otimes>\<^sub>s ket empty - run_B))\<^sup>2 = 
          (norm (run_B - run_A \<otimes>\<^sub>s ket empty))\<^sup>2" 
      by (subst norm_minus_cancel[symmetric], auto)
    also have "\<dots> = (norm ((\<Psi>sB empty_list - run_A) \<otimes>\<^sub>s ket empty + 
      (\<Sum>l\<in>has_bits {0..<d}. \<Psi>sB l \<otimes>\<^sub>s ket (list_to_l l))))\<^sup>2"
    proof -
      have *: "(\<Psi>sB empty_list - run_A) \<otimes>\<^sub>s ket empty = 
        \<Psi>sB empty_list \<otimes>\<^sub>s ket empty - run_A \<otimes>\<^sub>s ket empty"
        using tensor_ell2_diff1 by blast
      show ?thesis unfolding eq18 
        by (subst sum.remove[of _ empty_list], unfold * len_d_empty_has_bits) 
          (auto simp add: algebra_simps)
    qed
    also have "\<dots> = (norm ((\<Psi>sB empty_list - run_A) \<otimes>\<^sub>s ket (empty)))\<^sup>2 + 
      (norm (\<Sum>l\<in>has_bits {0..<d}. \<Psi>sB l \<otimes>\<^sub>s ket (list_to_l l)))\<^sup>2"
    proof -
      have l: "(if empty = list_to_l l then 1 else 0) = 0" if "l \<in> has_bits {0..<d}" for l
        using that by (metis DiffE empty_iff has_bits_empty len_d_empty_has_bits has_bits_not_empty) 
      then have *: "(\<Sum>l\<in>has_bits {0..<d}.
        (\<Psi>sB empty_list - run_A) \<bullet>\<^sub>C \<Psi>sB l * (if empty = list_to_l l then 1 else 0)) = 0"
        by (smt (verit, best) class_semiring.add.finprod_all1 semiring_norm(64))
      have "(\<Sum>l\<in>has_bits {0..<d} \<inter> {l. empty = list_to_l l}. 
        (\<Psi>sB empty_list - run_A) \<bullet>\<^sub>C \<Psi>sB l) = 0" by (subst sum.inter_restrict, simp)
      (subst (2) *[symmetric], intro sum.cong, auto)  
      then have "is_orthogonal ((\<Psi>sB empty_list - run_A) \<otimes>\<^sub>s ket empty)
        (\<Sum>l\<in>has_bits {0..<d}. \<Psi>sB l \<otimes>\<^sub>s ket (list_to_l l))" 
        by (auto simp add: cinner_sum_right cinner_ket) 
      then show ?thesis by (rule pythagorean_theorem)
    qed
    also have "\<dots> = (norm ((\<Psi>sB empty_list - run_A) \<otimes>\<^sub>s ket empty))\<^sup>2 + 
      (\<Sum>l\<in>has_bits {0..<d}. norm (\<Psi>sB l)^2)"
    proof -
      have "a \<noteq> a' \<Longrightarrow> a\<in>has_bits {0..<d} \<Longrightarrow> a'\<in>has_bits {0..<d} \<Longrightarrow>
        list_to_l a \<noteq> list_to_l a'" for a a'
        by (metis DiffE inj_list_to_l inj_onD len_d_empty_has_bits) 
      then show ?thesis
        by (subst pythagorean_theorem_sum) (auto simp add: norm_tensor_ell2)
    qed
    also have "\<dots> = (norm ((\<Psi>sB empty_list - run_A) \<otimes>\<^sub>s ket empty))\<^sup>2 + Pfind'" 
      using eq21 by auto
    also have "\<dots> = norm (\<Sum>i=1..<d+1. \<Psi>s' i)^2 + Pfind'"
    proof -
      have *: "\<Psi>s' 0 - (\<Sum>i<d+1. \<Psi>s' i) = - (\<Sum>i=1..<d+1. \<Psi>s' i)"
        unfolding lessThan_atLeast0
        by (subst sum.atLeast_Suc_lessThan[OF \<open>0<d+1\<close>]) auto
      have **: "norm ((\<Psi>s'  0 - (\<Sum>i<d+1. \<Psi>s' i)) \<otimes>\<^sub>s ket empty) = 
        norm (\<Sum>i = 1..<d+1. \<Psi>s' i)"
        unfolding * by (simp add: norm_tensor_ell2)
      show ?thesis unfolding eq17 eq19[symmetric] ** by auto
    qed
    also have "\<dots> \<le> (\<Sum>i=1..<d+1. norm (\<Psi>s' i))^2 + Pfind'"
      using eq20 eq21'
      by (smt (verit) power_mono[OF norm_sum norm_ge_zero] sum.cong)
    also have "\<dots> \<le> d * (\<Sum>i=1..<d+1. norm (\<Psi>s' i)^2) + Pfind'" 
      by (subst add_le_cancel_right)
        (use arith_quad_mean_ineq[of "{1..<d+1}" "(\<lambda>i. norm (\<Psi>s' i))"] in \<open>auto\<close>)
    also have "\<dots> = (d+1) * Pfind' + d * P_nonterm"
      unfolding eq21' by (simp add: algebra_simps)
    finally show ?thesis by linarith
  qed
qed

lemma pure_o2h_sqrt: \<open>norm ((run_A \<otimes>\<^sub>s ket empty) - run_B) \<le> sqrt ((d+1) * Pfind' + d * P_nonterm)\<close>
  using pure_o2h real_le_rsqrt by blast

lemma error_term_pos:
  "(d+1) * Pfind' + d * P_nonterm \<ge> 0"
  using pure_o2h by (smt (verit, best) power2_diff sum_squares_bound)

end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end
