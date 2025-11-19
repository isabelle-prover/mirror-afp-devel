theory Run_Adversary

imports Definition_O2H 
  More_Kraus_Maps
  Unitary_S 
  Unitary_S_prime

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax

section \<open>Running the Adversary\<close>

text \<open>Modelling the adversary, some type synonyms.\<close>
type_synonym 'a tc_op = "('a ell2,'a ell2) trace_class"
type_synonym 'a kraus_adv = "nat \<Rightarrow> ('a ell2,'a ell2,unit) kraus_family"
type_synonym 'a pure_adv = "nat \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> 'a ell2" 
  (* types: depth \<Rightarrow> unitaries \<Rightarrow> init *)
type_synonym 'a mixed_adv = "nat \<Rightarrow> 'a kraus_adv \<Rightarrow> 'a update" 
  (* types: depth \<Rightarrow> Kraus maps \<Rightarrow> final Projection *)



text \<open>We define the run of the quantum algorithm of our adversaries.
Each adversary can make quantum calculations (in form of unitaries) before and after each query 
to the oracle \<open>Uquery H\<close>. Since the oracle function $H:X\longrightarrow Y$ works on (classical) 
registers, we need to embed the domain and target registers \<open>X\<close> and \<open>Y\<close> as well. 
(\<open>(X;Y) (Uquery H)\<close> is the notation for the query to \<open>H\<close> applied to the registers \<open>X\<close> and \<open>Y\<close>.)
\<open>init\<close> is the initial quantum state which may also be manipulated by the adversary in
the first step.\<close>

(* representation of adversarial run: 
  init \<Rightarrow> UA 0 \<Rightarrow> UB 0 \<Rightarrow> Uquery H (on X,Y) \<Rightarrow> UA 1 \<Rightarrow> UB 1 \<Rightarrow> Uquery H \<Rightarrow> \<dots> \<Rightarrow> 
  UB (q-1) \<Rightarrow> Uquery H \<Rightarrow> UA q *)


text \<open>Running the adversary with Uquerys\<close>

text \<open>Definitions for pure adversaries\<close>

fun run_pure_adv :: "nat \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> 'a ell2 \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a ell2"  where 
  "run_pure_adv 0 UAs UB init X Y H = (UAs 0) *\<^sub>V init"
| "run_pure_adv (Suc n) UAs UB init X Y H = 
    (UAs (Suc n)) *\<^sub>V (X;Y) (Uquery H) *\<^sub>V (UB n) *\<^sub>V (run_pure_adv n UAs UB init X Y H)"

fun run_pure_adv_update :: "nat \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> 'a ell2 \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a update"  where 
  "run_pure_adv_update 0 UAs UB init X Y H = sandwich (UAs 0) *\<^sub>V (selfbutter init)"
| "run_pure_adv_update (Suc n) UAs UB init X Y H = 
    sandwich (UAs (Suc n) o\<^sub>C\<^sub>L (X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n) *\<^sub>V (run_pure_adv_update n UAs UB init X Y H)"

fun run_pure_adv_tc :: "nat \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> 'a ell2 \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a tc_op"  where 
  "run_pure_adv_tc 0 UAs UB init X Y H = sandwich_tc (UAs 0) (tc_selfbutter init)"
| "run_pure_adv_tc (Suc n) UAs UB init X Y H = 
    sandwich_tc (UAs (Suc n) o\<^sub>C\<^sub>L (X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n) (run_pure_adv_tc n UAs UB init X Y H)"



lemma run_pure_adv_tc_pos:
  "run_pure_adv_tc n UAs UB init X Y H \<ge> 0"
  by (induct n) (auto simp add: Abs_trace_class_geq0I sandwich_tc_pos tc_selfbutter_def)

text \<open>How a pure run is mapped from ell2 to trace class.\<close>
lemma run_pure_adv_ell2_update:
  "run_pure_adv_update n UAs UB init X Y H = selfbutter (run_pure_adv n UAs UB init X Y H)"
  by (induct n) (auto simp add: butterfly_comp_cblinfun cblinfun_comp_butterfly sandwich_apply)

lemma run_pure_adv_update_tc':
  "from_trace_class (run_pure_adv_tc n UAs UB init X Y H) = run_pure_adv_update n UAs UB init X Y H"
  by (induct n) (auto simp add: Abs_trace_class_inverse from_trace_class_sandwich_tc 
      tc_butterfly.abs_eq tc_selfbutter_def)

lemma run_pure_adv_update_tc:
  "run_pure_adv_tc n UAs UB init X Y H = Abs_trace_class (run_pure_adv_update n UAs UB init X Y H)"
  using Abs_trace_class_inverse unfolding run_pure_adv_update_tc'[symmetric] from_trace_class_inverse 
  by auto

text \<open>Definitions for mixed adversaries\<close>

fun run_mixed_adv :: 
  "nat \<Rightarrow> 'a kraus_adv \<Rightarrow> (nat \<Rightarrow> 'a update) \<Rightarrow> 'a ell2 \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'a tc_op"  where 
  "run_mixed_adv 0 Es UB init X Y H = (kf_apply (Es 0)) (tc_selfbutter init)"
| "run_mixed_adv (Suc n) Es UB init X Y H = (kf_apply (Es (Suc n))) 
    (sandwich_tc ((X;Y) (Uquery H) o\<^sub>C\<^sub>L UB n) (run_mixed_adv n Es UB init X Y H))"


lemma run_mixed_adv_pos:
  "run_mixed_adv n Es UB init X Y H \<ge> 0"
  by (induct n) (auto simp add: Abs_trace_class_geq0I sandwich_tc_pos kf_apply_pos tc_selfbutter_def)


lemma (in o2h_setting) norm_run_mixed_adv:
  assumes Es_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (Es i) \<le> id_cblinfun"
    and n: "n < d+1"
    and normUB: "\<And>i. i < d+1 \<Longrightarrow> norm (UB i) \<le> 1" 
    and register: "register (X';Y')"
    and norm_init': "norm init' = 1"
  fixes H :: "'x \<Rightarrow> 'y"
  shows "norm (run_mixed_adv n Es UB init' X' Y' H) \<le> 1"
  using n proof (induct n)
  case 0
  have norm1:"norm (tc_selfbutter init') = 1" using norm_init'
    by (simp add: norm_tc_butterfly tc_selfbutter_def)
  have init0: "0 \<le> tc_selfbutter init'" by (simp add: tc_selfbutter_def)
  have "norm (run_mixed_adv 0 Es UB init' X' Y' H) \<le> kf_norm (Es 0)" 
    using kf_apply_bounded_pos[OF init0] norm1 by auto
  also have "\<dots> \<le> 1" unfolding kf_norm_def using Es_norm_id[of 0]
    by (metis "0.prems" Kraus_Families.kf_bound_pos norm_cblinfun_id norm_cblinfun_mono)
  finally show ?case by auto
next
  case (Suc n)
  have uniH: "unitary ((X';Y') (Uquery H))" by (intro register_unitary[OF register unitary_H])
  let ?sand = "sandwich_tc ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB n)"
  have pos: "?sand (run_mixed_adv n Es UB init' X' Y' H) \<ge> 0"
    using sandwich_tc_pos[OF run_mixed_adv_pos] by blast
  have "norm (kf_apply (Es (Suc n)) (?sand (run_mixed_adv n Es UB init' X' Y' H))) \<le>
    kf_norm (Es (Suc n)) *  norm (?sand (run_mixed_adv n Es UB init' X' Y' H))"
    using kf_apply_bounded_pos[OF pos] by auto
  also have "\<dots> \<le> norm (?sand (run_mixed_adv n Es UB init' X' Y' H))"
    unfolding kf_norm_def using Es_norm_id[OF Suc(2)]
    by (metis Kraus_Families.kf_bound_pos mult_left_le_one_le norm_cblinfun_id norm_cblinfun_mono norm_ge_zero)
  also have "\<dots> \<le> (norm ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB n))^2" 
    using norm_sandwich_tc Suc by (smt (verit, best) Suc_lessD mult_less_cancel_left1 zero_le_power2)
  also have "\<dots> \<le> (norm ((X';Y') (Uquery H)))^2 * (norm (UB n))^2"
    by (metis norm_cblinfun_compose norm_ge_zero power_mono power_mult_distrib)
  also have "\<dots> \<le> (norm (UB n))^2" by (simp add: norm_isometry uniH)
  also have "\<dots> \<le> 1" using Suc(2) normUB[of n] by (auto simp add: power_le_one)
  finally show ?case by auto 
qed


text \<open>Trace preserving Kraus maps/adversaries preserve the norm.\<close>

lemma km_trace_preserving_kf_apply:
  assumes "km_trace_preserving (kf_apply F)" "\<rho> \<ge> 0"
  shows "norm (kf_apply F \<rho>) = norm \<rho>"
  by (metis assms(1,2) kf_apply_pos km_trace_preserving_iff norm_tc_pos_Re)


lemma (in o2h_setting) trace_preserving_norm_run_mixed_adv:
  assumes trace_pres: "\<And>i. i < d+1 \<Longrightarrow> km_trace_preserving (kf_apply (Es i))"
    and n: "n < d+1"
    and iso_UB: "\<And>i. i < d+1 \<Longrightarrow> isometry (UB i)" 
    and register: "register (X';Y')"
    and norm_init': "norm init' = 1"
  fixes H :: "'x \<Rightarrow> 'y"
  shows "norm (run_mixed_adv n Es UB init' X' Y' H) = 1"
  using n proof (induct n)
  case 0
  have "norm (kf_apply (Es 0) (tc_selfbutter init')) = norm (tc_selfbutter init')" 
    using assms(1)
    by (auto intro!: km_trace_preserving_kf_apply simp add: tc_selfbutter_def)
  then show ?case using assms by auto 
next
  case (Suc n)
  have "n<d+1" using Suc by auto
  have "norm (kf_apply (Es (Suc n))
       (sandwich_tc ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB n) (run_mixed_adv n Es UB init' X' Y' H))) =
    norm (sandwich_tc ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB n) (run_mixed_adv n Es UB init' X' Y' H))"
    using assms(1)[OF Suc(2)]
    by (auto intro!: km_trace_preserving_kf_apply simp add: tc_selfbutter_def  run_mixed_adv_pos sandwich_tc_pos)
  also have "\<dots> =  norm (run_mixed_adv n Es UB init' X' Y' H)" 
    by (intro norm_sandwich_tc_unitary) (use iso_UB[OF \<open>n<d+1\<close>] 
        unitary_isometry[OF register_unitary[OF register unitary_H]]
        in \<open>auto simp add: run_mixed_adv_pos intro!: isometry_cblinfun_compose\<close>)
  finally show ?case using Suc by auto
qed




context o2h_setting
begin



text \<open>The run of the adversaries A and B (= A with counting in register 'l) for mixed states.\<close>

text \<open>For pure adversaries\<close>
definition run_pure_A_ell2 where
  "run_pure_A_ell2 UA H = run_pure_adv d UA (\<lambda>_. id_cblinfun) init X Y H"

definition run_pure_A_update :: "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'mem update" where
  "run_pure_A_update UA H = run_pure_adv_update d UA (\<lambda>_. id_cblinfun) init X Y H"

definition run_pure_A_tc :: "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'mem tc_op" where
  "run_pure_A_tc UA H = run_pure_adv_tc d UA (\<lambda>_. id_cblinfun) init X Y H"

lemma run_pure_A_ell2_update:
  "run_pure_A_update UA H = selfbutter (run_pure_A_ell2 UA H)"
  unfolding run_pure_A_update_def run_pure_A_ell2_def by (rule run_pure_adv_ell2_update)

lemma run_pure_A_update_tc:
  "run_pure_A_tc UA H = Abs_trace_class (run_pure_A_update UA H)"
  unfolding run_pure_A_update_def run_pure_A_tc_def by (rule run_pure_adv_update_tc)

lemma run_pure_A_tc_pos: "0 \<le> run_pure_A_tc UA H"
  unfolding run_pure_A_tc_def by (rule run_pure_adv_tc_pos)


text \<open>For mixed adversaries\<close>
definition run_mixed_A :: "'mem kraus_adv \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'mem tc_op" where
  "run_mixed_A kraus_A H = run_mixed_adv d kraus_A (\<lambda>_. id_cblinfun) init X Y H"

lemma run_mixed_A_pos:
  "0 \<le> run_mixed_A kraus_A H"
  unfolding run_mixed_A_def by (rule run_mixed_adv_pos)

lemma norm_run_mixed_A:
  assumes F_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (F i) \<le> id_cblinfun"
  shows "norm (run_mixed_A F H) \<le> 1"
  unfolding run_mixed_A_def  
  by (intro norm_run_mixed_adv) (auto simp add: norm_init assms)






text \<open>Embeddings of \<open>X\<close> and \<open>Y\<close> in the counting register of \<open>B\<close>\<close>
definition X_for_B :: \<open>'x update \<Rightarrow> ('mem \<times> 'l) update\<close> where
  \<open>X_for_B = Fst o X\<close>

definition Y_for_B :: \<open>'y update \<Rightarrow> ('mem \<times> 'l) update\<close> where
  \<open>Y_for_B = Fst o Y\<close>

lemma [register]: \<open>register X_for_B\<close>
  by (simp add: X_for_B_def)

lemma [register]: \<open>register Y_for_B\<close>
  by (simp add: Y_for_B_def)

lemma register_XY_for_B: 
  "register (X_for_B;Y_for_B)" by (simp add: X_for_B_def Y_for_B_def)



text \<open>Alternative representation of \<open>Uquery H\<close> on \<open>'l\<close>\<close>
lemma UqueryH_tensor_id_cblinfunB: 
  "(X_for_B;Y_for_B) (Uquery H) = (X;Y) (Uquery H) \<otimes>\<^sub>o id_cblinfun"
  unfolding X_for_B_def Y_for_B_def
  by (metis Fst_def comp_eq_dest_lhs compat register_Fst register_comp_pair)

text \<open>The oracle query on the extended register stays unitary.\<close>

lemma unitary_H_B: "unitary ((X_for_B;Y_for_B) (Uquery H))" 
  by (intro register_unitary[OF register_XY_for_B]) (auto simp add: unitary_H)

lemma iso_H_B: "isometry ((X_for_B;Y_for_B) (Uquery H))" 
  by (simp add: unitary_H_B)

text \<open>The initial register state \<open>init\<close> is extended by zeros in the register \<open>'l\<close>.
Here, we need the embedding of the counter into the type \<open>'l\<close> by \<open>list_to_l\<close>.\<close>

definition \<open>init_B = init \<otimes>\<^sub>s ket empty\<close>

lemma norm_init_B: "norm init_B = 1" 
  unfolding init_B_def using norm_init by (simp add: norm_tensor_ell2)



text \<open>Definition of adversary B\<close>

text \<open>For pure adversaries\<close>
definition run_pure_B_ell2 where
  "run_pure_B_ell2 UB H S = 
  run_pure_adv d (Fst o UB) (US S) init_B X_for_B Y_for_B H"

definition run_pure_B_update :: 
  "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> ('mem \<times> 'l) update" where
  "run_pure_B_update UB H S = run_pure_adv_update d (Fst o UB) (US S) init_B X_for_B Y_for_B H"

definition run_pure_B_tc :: 
  "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> ('mem\<times>'l) tc_op" where
  "run_pure_B_tc UB H S = run_pure_adv_tc d(Fst o UB) (US S) init_B X_for_B Y_for_B H"


lemma run_pure_B_ell2_update:
  "run_pure_B_update UB H S = selfbutter (run_pure_B_ell2 UB H S)"
  unfolding run_pure_B_update_def run_pure_B_ell2_def by (rule run_pure_adv_ell2_update)

lemma run_pure_B_update_tc:
  "run_pure_B_tc UB H S = Abs_trace_class (run_pure_B_update UB H S)"
  unfolding run_pure_B_update_def run_pure_B_tc_def by (rule run_pure_adv_update_tc)

lemma run_pure_B_update_tc':
  "run_pure_B_update UB H S = from_trace_class (run_pure_B_tc UB H S)"
  by (simp add: run_pure_B_tc_def run_pure_B_update_def run_pure_adv_update_tc')

lemma run_pure_B_tc_pos: "0 \<le> run_pure_B_tc UB H S"
  unfolding run_pure_B_tc_def by (rule run_pure_adv_tc_pos)

text \<open>For mixed adversaries\<close>
definition run_mixed_B  ::
  "'mem kraus_adv \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> ('mem \<times> 'l) tc_op"where
  "run_mixed_B kraus_B H S = run_mixed_adv d (\<lambda>n. kf_Fst (kraus_B n)) 
  (US S) init_B X_for_B Y_for_B H"


lemma run_mixed_B_pos:
  "0 \<le> run_mixed_B kraus_B H S"
  unfolding run_mixed_B_def by (rule run_mixed_adv_pos)

lemma norm_run_mixed_B:
  assumes F_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (F i) \<le> id_cblinfun"
  shows "norm (run_mixed_B F H S) \<le> 1"
  unfolding run_mixed_B_def  proof (intro norm_run_mixed_adv, goal_cases)
  case (1 i)
  have "kf_bound (kf_Fst (F i)) \<le> kf_bound (F i) \<otimes>\<^sub>o id_cblinfun"
    using kf_bound_kf_Fst by auto
  also have "\<dots> \<le> id_cblinfun \<otimes>\<^sub>o id_cblinfun" 
    by (intro tensor_op_mono_left[OF assms[OF 1]], auto)
  finally show ?case by auto
qed (auto simp add: register_XY_for_B norm_init_B norm_US assms)

lemma trace_preserving_norm_run_mixed_B:
  assumes "\<And>i. i < d+1 \<Longrightarrow> km_trace_preserving (kf_apply 
  (kf_Fst (F i)::(('mem \<times> 'l) ell2, ('mem \<times> 'l) ell2, unit) kraus_family))"
  shows "norm (run_mixed_B F H S) = 1"
  unfolding run_mixed_B_def
  by (auto intro!: trace_preserving_norm_run_mixed_adv
      simp add: assms isometry_US register_XY_for_B norm_init_B
      simp del: km_trace_preserving_apply)


section \<open>Definition of \<^term>\<open>B_count\<close>\<close>


subsection \<open>Defining the run of adversary $B$\<close>

text \<open>Embeddings of \<open>X\<close> and \<open>Y\<close> in the counting register for $B_{count}$\<close>
definition X_for_C :: \<open>'x update \<Rightarrow> ('mem \<times> nat) update\<close> where
  \<open>X_for_C = Fst o X\<close>

definition Y_for_C :: \<open>'y update \<Rightarrow> ('mem \<times> nat) update\<close> where
  \<open>Y_for_C = Fst o Y\<close>

lemma [register]: \<open>register X_for_C\<close>
  by (simp add: X_for_C_def)

lemma [register]: \<open>register Y_for_C\<close>
  by (simp add: Y_for_C_def)

lemma register_XY_for_C: 
  "register (X_for_C;Y_for_C)" by (simp add: X_for_C_def Y_for_C_def)

text \<open>The oracle query on the extended register stays unitary.\<close>

lemma unitary_H_C: "unitary ((X_for_C;Y_for_C) (Uquery H))" 
  by (intro register_unitary[OF register_XY_for_C]) (auto simp add: unitary_H)

lemma iso_H_C: "isometry ((X_for_C;Y_for_C) (Uquery H))" 
  by (simp add: unitary_H_C)

text \<open>Alternative representation of \<open>Uquery H\<close>.\<close>
lemma UqueryH_tensor_id_cblinfunC: 
  "(X_for_C;Y_for_C) (Uquery H) = (X;Y) (Uquery H) \<otimes>\<^sub>o id_cblinfun"
  unfolding X_for_C_def Y_for_C_def
  by (metis Fst_def comp_eq_dest_lhs compat register_Fst register_comp_pair)


text \<open>The initial register for the adversary $B$ with counting is the initial state and starting 
with $0$ in the counting register.\<close>
definition init_B_count :: "('mem \<times> nat) ell2" where 
  \<open>init_B_count = init \<otimes>\<^sub>s ket 0\<close>

lemma norm_init_B_count:
  "norm (init_B_count) = 1"
  unfolding init_B_count_def by (simp add: norm_init norm_tensor_ell2)

text \<open>Definition of adversary B with counting\<close>

text \<open>For pure adversaries\<close>
definition run_pure_B_count_ell2 where
  "run_pure_B_count_ell2 UB H S = run_pure_adv d (Fst o UB) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H"

definition run_pure_B_count_update :: 
  "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> ('mem \<times> nat) update" where
  "run_pure_B_count_update UB H S = run_pure_adv_update d (Fst o UB) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H"

definition run_pure_B_count_tc :: 
  "(nat \<Rightarrow> 'mem update) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> ('mem\<times>nat) tc_op" where
  "run_pure_B_count_tc UB H S = run_pure_adv_tc d (Fst o UB) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H"


lemma run_pure_B_count_ell2_update:
  "run_pure_B_count_update UB H S = selfbutter (run_pure_B_count_ell2 UB H S)"
  unfolding run_pure_B_count_update_def run_pure_B_count_ell2_def by (rule run_pure_adv_ell2_update)

lemma run_pure_B_count_update_tc:
  "run_pure_B_count_tc UB H S = Abs_trace_class (run_pure_B_count_update UB H S)"
  unfolding run_pure_B_count_update_def run_pure_B_count_tc_def by (rule run_pure_adv_update_tc)

lemma run_pure_B_count_update_tc':
  "run_pure_B_count_update UB H S = from_trace_class (run_pure_B_count_tc UB H S)"
  by (simp add: run_pure_B_count_tc_def run_pure_B_count_update_def run_pure_adv_update_tc')


lemma run_pure_B_count_tc_pos: "0 \<le> run_pure_B_count_tc UB H S"
  unfolding run_pure_B_count_tc_def by (rule run_pure_adv_tc_pos)

text \<open>For mixed adversaries\<close>
definition run_mixed_B_count  ::
  "'mem kraus_adv \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> bool) \<Rightarrow> ('mem \<times> nat) tc_op" where
  "run_mixed_B_count kraus_B H S = run_mixed_adv d (\<lambda>n. kf_Fst (kraus_B n)) 
  (\<lambda>n. U_S' S) init_B_count X_for_C Y_for_C H"


lemma run_mixed_B_count_pos:
  "0 \<le> run_mixed_B_count kraus_B H S"
  unfolding run_mixed_B_count_def by (rule run_mixed_adv_pos)

lemma norm_run_mixed_B_count:
  assumes F_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (F i) \<le> id_cblinfun"
  shows "norm (run_mixed_B_count F H S) \<le> 1"
  unfolding run_mixed_B_count_def  proof (intro norm_run_mixed_adv, goal_cases)
  case (1 i)
  have "kf_bound (kf_Fst (F i)) \<le> kf_bound (F i) \<otimes>\<^sub>o id_cblinfun"
    using kf_bound_kf_Fst by auto
  also have "\<dots> \<le> id_cblinfun \<otimes>\<^sub>o id_cblinfun" 
    by (intro tensor_op_mono_left[OF assms[OF 1]], auto)
  finally show ?case by auto
qed (auto simp add: register_XY_for_C norm_init_B_count norm_U_S' assms)

lemma trace_preserving_norm_run_mixed_B_count:
  assumes "\<And>i. i < d+1 \<Longrightarrow> km_trace_preserving (kf_apply 
  (kf_Fst (F i)::(('mem \<times> nat) ell2, ('mem \<times> nat) ell2, unit) kraus_family))"
  shows "norm (run_mixed_B_count F H S) = 1"
  by (auto intro!: trace_preserving_norm_run_mixed_adv
      simp add: assms iso_U_S' register_XY_for_C norm_init_B_count run_mixed_B_count_def
      simp del: km_trace_preserving_apply)


end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end