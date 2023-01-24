section \<open>Composing functions\label{s:tm-composing}\<close>

theory Composing
  imports Elementary
begin

text \<open>
For a Turing machine $M_1$ computing $f_1$ in time $T_1$ and a TM $M_2$
computing $f_2$ in time $T_2$ there is a TM $M$ computing $f_2 \circ f_1$ in
time $O(T_1(n) + \max_{m \le T_1(n)} T_2(m))$. If $T_1$ is monotone
the time bound is $O(T_1 + T_2 \circ T_1)$; if $T_1$ and $T_2$ are
polynomially bounded the running-time of $M$ is polynomially bounded, too.

The Turing machines $M_1$ and $M_2$ can have both a different alphabet and
number of tapes, so generally they cannot be composed by the $;;$ operator. To
get around this we enlarge the alphabet and prepend and append tapes, so $M$ has
as many tapes as $M_1$ and $M_2$ combined. The following function returns the
combined Turing machine $M$.

\null
\<close>

definition "compose_machines k1 G1 M1 k2 G2 M2 \<equiv>
  enlarged G1 (append_tapes k1 (k1 + k2) M1) ;;
  tm_start 1 ;;
  tm_cp_until 1 k1 {\<box>} ;;
  tm_erase_cr 1 ;;
  tm_start k1 ;;
  prepend_tapes k1 (enlarged G2 M2) ;;
  tm_cr (k1 + 1) ;;
  tm_cp_until (k1 + 1) 1 {\<box>}"

locale compose =
  fixes k1 k2 G1 G2 :: nat
    and M1 M2 :: machine
    and T1 T2 :: "nat \<Rightarrow> nat"
    and f1 f2 :: "string \<Rightarrow> string"
  assumes tm_M1: "turing_machine k1 G1 M1"
    and tm_M2: "turing_machine k2 G2 M2"
    and computes1: "computes_in_time k1 M1 f1 T1"
    and computes2: "computes_in_time k2 M2 f2 T2"
begin

definition "tm1 \<equiv> enlarged G1 (append_tapes k1 (k1 + k2) M1)"
definition "tm2 \<equiv> tm1 ;; tm_start 1"
definition "tm3 \<equiv> tm2 ;; tm_cp_until 1 k1 {\<box>}"
definition "tm4 \<equiv> tm3 ;; tm_erase_cr 1"
definition "tm5 \<equiv> tm4 ;; tm_start k1"
definition "tm56 \<equiv> prepend_tapes k1 (enlarged G2 M2)"
definition "tm6 \<equiv> tm5 ;; tm56"
definition "tm7 \<equiv> tm6 ;; tm_cr (k1 + 1)"
definition "tm8 \<equiv> tm7 ;; tm_cp_until (k1 + 1) 1 {\<box>}"

definition G :: nat where
  "G \<equiv> max G1 G2"

lemma G1: "G1 \<le> G" and G2: "G2 \<le> G"
  using G_def by simp_all

lemma k_ge: "k1 \<ge> 2" "k2 \<ge> 2"
  using tm_M1 tm_M2 turing_machine_def by simp_all

lemma tm1_tm: "turing_machine (k1 + k2) G tm1"
  unfolding tm1_def using turing_machine_enlarged append_tapes_tm tm_M1 G1 by simp

lemma tm2_tm: "turing_machine (k1 + k2) G tm2"
  unfolding tm2_def using tm1_tm tm_start_tm turing_machine_def by blast

lemma tm3_tm: "turing_machine (k1 + k2) G tm3"
  unfolding tm3_def
  using tm2_tm tm_cp_until_tm turing_machine_def k_ge turing_machine_sequential_turing_machine
  by (metis add_leD1 less_add_same_cancel1 less_le_trans less_numeral_extra(1) nat_1_add_1)

lemma tm4_tm: "turing_machine (k1 + k2) G tm4"
  unfolding tm4_def
  using tm3_tm tm_erase_cr_tm turing_machine_def turing_machine_sequential_turing_machine
  by (metis Suc_1 Suc_le_lessD tm_erase_cr_tm zero_less_one)

lemma tm5_tm: "turing_machine (k1 + k2) G tm5"
  unfolding tm5_def
  using tm4_tm tm_start_tm turing_machine_def turing_machine_sequential_turing_machine
  by auto

lemma tm6_tm: "turing_machine (k1 + k2) G tm6"
  unfolding tm6_def
  using tm5_tm tm56_def turing_machine_enlarged prepend_tapes_tm tm_M2 G2
  by simp

lemma tm7_tm: "turing_machine (k1 + k2) G tm7"
  unfolding tm7_def using tm6_tm tm_cr_tm turing_machine_def by blast

lemma tm8_tm: "turing_machine (k1 + k2) G tm8"
  unfolding tm8_def
  using tm7_tm tm_cp_until_tm turing_machine_def turing_machine_sequential_turing_machine k_ge(2)
  by (metis add.commute add_less_cancel_right add_strict_increasing nat_1_add_1
    verit_comp_simplify1(3) zero_less_one)

context
  fixes x :: string
begin

definition "zs \<equiv> string_to_symbols x"

lemma bit_symbols_zs: "bit_symbols zs"
  using zs_def by simp

abbreviation "n \<equiv> length x"

lemma length_zs [simp]: "length zs = n"
  using zs_def by simp

definition "tps0 \<equiv> snd (start_config (k1 + k2) zs)"

definition tps1a :: "tape list" where
  "tps1a \<equiv> SOME tps. tps ::: 1 = string_to_contents (f1 x) \<and>
       transforms M1 (snd (start_config k1 (string_to_symbols x))) (T1 n) tps"

lemma tps1a_aux:
  "tps1a ::: 1 = string_to_contents (f1 x)"
  "transforms M1 (snd (start_config k1 (string_to_symbols x))) (T1 n) tps1a"
  using tps1a_def someI_ex[OF computes_in_timeD[OF computes1, of x]]
  by simp_all

lemma tps1a:
  "tps1a ::: 1 = string_to_contents (f1 x)"
  "transforms M1 (snd (start_config k1 zs)) (T1 n) tps1a"
  using tps1a_aux zs_def by simp_all

lemma length_tps1a [simp]: "length tps1a = k1"
  using tps1a(2) tm_M1 start_config_length execute_num_tapes transforms_def transits_def turing_machine_def
  by (smt (verit, del_insts) Suc_1 add_pos_pos less_le_trans less_numeral_extra(1) plus_1_eq_Suc snd_conv)

definition tps1b :: "tape list" where
  "tps1b \<equiv> replicate k2 (\<lfloor>[]\<rfloor>, 0)"

definition tps1 :: "tape list" where
  "tps1 \<equiv> tps1a @ tps1b"

lemma tps1_at_1: "tps1 ! 1 = tps1a ! 1"
  using tps1_def length_tps1a k_ge by (metis Suc_1 Suc_le_lessD nth_append)

lemma tps1_at_1': "tps1 ::: 1 = string_to_contents (f1 x)"
  using tps1_at_1 tps1a by simp

lemma tps1_pos_le: "tps1 :#: 1 \<le> T1 n"
proof -
  have "execute M1 (start_config k1 zs) (T1 n) = (length M1, tps1a)"
    using transforms_def transits_def tps1a(2)
    by (metis (no_types, lifting) execute_after_halting_ge fst_conv start_config_def snd_conv)
  moreover have "execute M1 (start_config k1 zs) (T1 n) <#> 1 \<le> T1 n"
    using head_pos_le_time[OF tm_M1, of 1] k_ge by fastforce
  ultimately show ?thesis
    using tps1_at_1 by simp
qed

lemma length_f1_x: "length (f1 x) \<le> T1 n"
proof -
  have "execute M1 (start_config k1 zs) (T1 n) = (length M1, tps1a)"
    using transforms_def transits_def tps1a(2)
    by (metis (no_types, lifting) execute_after_halting_ge fst_conv start_config_def snd_conv)
  moreover have "(execute M1 (start_config k1 zs) (T1 n) <:> 1) i = \<box>" if "i > T1 n" for i
    using blank_after_time[OF that _ _ tm_M1] k_ge(1) by simp
  ultimately have "(tps1a ::: 1) i = \<box>" if "i > T1 n" for i
    using that by simp
  then have "(string_to_contents (f1 x)) i = \<box>" if "i > T1 n" for i
    using that tps1a(1) by simp
  then have "length (string_to_symbols (f1 x)) \<le> T1 n"
    by (metis length_map order_refl verit_comp_simplify1(3) zero_neq_numeral zero_neq_one)
  then show ?thesis
    by simp
qed

lemma start_config_append:
  "start_config (k1 + k2) zs = (0, snd (start_config k1 zs) @ tps1b)"
proof
  have "k1 > 0"
    using tm_M1 turing_machine_def by simp
  show "fst (start_config (k1 + k2) zs) = fst (0, snd (start_config k1 zs) @ tps1b)"
    using start_config_def by simp
  show "snd (start_config (k1 + k2) zs) = snd (0, snd (start_config k1 zs) @ tps1b)"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    have len: "||start_config k1 zs|| = k1"
      using start_config_length by (simp add: \<open>0 < k1\<close>)
    show "length ?l = length ?r"
      using start_config_length tps1b_def tm_M1 turing_machine_def by simp
    show "?l ! j = ?r ! j" if "j < length ?l" for j
    proof (cases "j < k1")
      case True
      show ?thesis
      proof (cases "j = 0")
        case True
        then show ?thesis
          using start_config_def `k1 > 0` by simp
      next
        case False
        then have 1: "?l ! j = (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)"
          using start_config_def `k1 > 0` True by auto
        have "?r ! j = snd (start_config k1 zs) ! j"
          using True len by (simp add: nth_append)
        then have "?r ! j = (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)"
          using start_config4 `k1 > 0` False True by simp
        then show ?thesis
          using 1 by simp
      qed
    next
      case False
      then have j: "j < k1 + k2" "k1 \<le> j"
        using that \<open>0 < k1\<close> add_gr_0 start_config_length by simp_all
      then have "?r ! j = (\<lfloor>[]\<rfloor>, 0)"
        using tps1b_def by (simp add: False len nth_append)
      moreover have "?l ! j = (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)"
        using start_config4 `k1 > 0` j by simp
      ultimately show ?thesis
        by auto
    qed
  qed
qed

lemma tm1 [transforms_intros]: "transforms tm1 tps0 (T1 n) tps1"
proof -
  let ?M = "append_tapes k1 (k1 + length tps1b) M1"
  have len: "||start_config k1 zs|| = k1"
    using start_config_length[of k1 zs] tm_M1 turing_machine_def by simp
  have "transforms ?M (snd (start_config k1 zs) @ tps1b) (T1 n) (tps1a @ tps1b)"
    using transforms_append_tapes[OF tm_M1 len tps1a(2), of tps1b] .
  moreover have "tps0 = snd (start_config k1 zs) @ tps1b"
    unfolding tps0_def using start_config_append by simp
  ultimately have *: "transforms ?M tps0 (T1 n) tps1"
    using tps1_def by simp

  have "symbols_lt G1 zs"
    using bit_symbols_zs tm_M1 turing_machine_def by auto
  moreover have "turing_machine (k1 + k2) G1 ?M"
    using append_tapes_tm[OF tm_M1, of "k1 + k2"] by (simp add: tps1b_def)
  ultimately have "transforms (enlarged G1 ?M) tps0 (T1 n) tps1"
    using transforms_enlarged * tps0_def by simp
  then show ?thesis
    using tm1_def tps1b_def by simp
qed

lemma clean_string_to_contents: "clean_tape (string_to_contents xs, i)"
  using clean_tape_def by simp

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps1 [1 := tps1 ! 1 |#=| 0]"

lemma length_tps2 [simp]: "length tps2 = k1 + k2"
  using tps2_def tps1_def by (simp add: tps1b_def)

lemma tm2:
  assumes "t = Suc (T1 n + tps1 :#: Suc 0)"
  shows "transforms tm2 tps0 t tps2"
  unfolding tm2_def
proof (tform tps: assms tps2_def)
  show "1 < length tps1"
    using tm_M1 turing_machine_def tps1_def by simp
  show "clean_tape (tps1 ! 1)"
      using tps1a(1) tps1_at_1 clean_tape_def by simp
qed

corollary tm2' [transforms_intros]:
  assumes "t = Suc (2 * T1 n)"
  shows "transforms tm2 tps0 t tps2"
  using assms tm2 tps1_pos_le transforms_monotone by simp

definition tps3 :: "tape list" where
  "tps3 \<equiv> tps2 [1 := tps2 ! 1 |#=| (Suc (length (f1 x))), k1 := tps2 ! 1 |#=| (Suc (length (f1 x)))]"

lemma tm3:
  assumes "t = Suc (Suc (2 * T1 n + Suc (length (f1 x))))"
  shows "transforms tm3 tps0 t tps3"
  unfolding tm3_def
proof (tform tps: k_ge)
  have "Suc 0 < k1 + k2" "0 < k2"
    using k_ge by simp_all
  then have *: "tps2 ! 1 = tps1 ! 1 |#=| 0"
    using tps2_def by (simp add: tps1_def tps1b_def)
  let ?i = "Suc (length (f1 x))"
  show "rneigh (tps2 ! 1) {0} ?i"
    using * tps1_at_1 tps1a by (intro rneighI) auto
  show "tps3 = tps2
    [1 := tps2 ! 1 |+| Suc (length (f1 x)),
     k1 := implant (tps2 ! 1) (tps2 ! k1) (Suc (length (f1 x)))]"
  proof -
    have "tps2 ! 1 |#=| (Suc (length (f1 x))) = tps2 ! 1 |#=| Suc (tps2 :#: 1 + length (f1 x))"
      by (metis "*" One_nat_def add_Suc plus_1_eq_Suc snd_conv)
    moreover have "tps2 ! 1 |#=| ?i = implant (tps2 ! 1) (tps2 ! k1) ?i"
    proof
      have 1: "tps2 ! 1 = (string_to_contents (f1 x), 0)"
        using tps1_at_1' * by simp
      have "tps1 ! k1 = (\<lfloor>[]\<rfloor>, 0)"
        using tps1_def tps1b_def by (simp add: \<open>0 < k2\<close> nth_append)
      then have 2: "tps2 ! k1 = (\<lfloor>[]\<rfloor>, 0)"
        using tps2_def k_ge by simp
      then show "snd (tps2 ! 1 |#=| ?i) = snd (implant (tps2 ! 1) (tps2 ! k1) ?i)"
        using implant by simp
      have "fst (implant (tps2 ! 1) (tps2 ! k1) ?i) i = fst (tps2 ! 1 |#=| ?i) i" for i
        using 1 2 implant by simp
      then show "fst (tps2 ! 1 |#=| ?i) = fst (implant (tps2 ! 1) (tps2 ! k1) ?i)"
        by auto
    qed
    ultimately show ?thesis
      using tps3_def by simp
  qed
  show "t = Suc (2 * T1 n) + Suc (Suc (length (f1 x)))"
    using assms by simp
qed

definition "tps3' \<equiv> tps1a
  [1 := (string_to_contents (f1 x), Suc (length (f1 x)))] @
   ((string_to_contents (f1 x), Suc (length (f1 x))) #
    replicate (k2 - 1) (\<lfloor>[]\<rfloor>, 0))"

lemma tps3': "tps3 = tps3'"
proof (rule nth_equalityI)
  have "length tps3 = k1 + k2"
    using tps3_def by simp
  moreover have "length tps3' = k1 + k2"
    using k_ge(2) tps3'_def by simp
  ultimately show "length tps3 = length tps3'"
    by simp
  show "tps3 ! j = tps3' ! j" if "j < length tps3" for j
  proof (cases "j < k1")
    case True
    then have rhs: "tps3' ! j = (tps1a [1 := (string_to_contents (f1 x), Suc (length (f1 x)))]) ! j"
      by (simp add: tps3'_def nth_append)
    show ?thesis
    proof (cases "j = 1")
      case True
      then have "tps3 ! j = tps2 ! 1 |#=| (Suc (length (f1 x)))"
        using tps3_def Suc_1 Suc_n_not_le_n \<open>length tps3 = k1 + k2\<close> k_ge(1)
          length_tps2 nth_list_update_eq nth_list_update_neq that
        by auto
      then have "tps3 ! j = tps1 ! 1 |#=| (Suc (length (f1 x)))"
        using tps2_def True \<open>length tps3 = k1 + k2\<close> length_tps2 that by auto
      then have "tps3 ! j = (string_to_contents (f1 x), Suc (length (f1 x)))"
        using tps1_at_1 tps1a(1) by simp
      then show ?thesis
        using rhs True k_ge(1) by auto
    next
      case False
      then have "tps3 ! j = tps2 ! j"
        using tps3_def True by simp
      then have "tps3 ! j = tps1 ! j"
        using tps2_def False by simp
      then have "tps3 ! j = tps1a ! j"
        using length_tps1a tps1_def False True by (simp add: nth_append)
      moreover have "tps3' ! j = tps1a ! j"
        using False rhs by simp
      ultimately show ?thesis
        by simp
    qed
  next
    case j_ge: False
    show ?thesis
    proof (cases "j = k1")
      case True
      then have "tps3 ! j = tps2 ! 1 |#=| (Suc (length (f1 x)))"
        using tps3_def that by simp
      then have "tps3 ! j = tps1 ! 1 |#=| (Suc (length (f1 x)))"
        using tps2_def \<open>length tps3 = k1 + k2\<close> length_tps2 Suc_1 Suc_le_lessD tm1_tm turing_machine_def
        by simp
      then have "tps3 ! j = (string_to_contents (f1 x), Suc (length (f1 x)))"
        using tps1_at_1 tps1a(1) by simp
      moreover have "tps3' ! j = (string_to_contents (f1 x), Suc (length (f1 x)))"
        using True tps3'_def
        by (metis (no_types, lifting) length_list_update length_tps1a nth_append_length)
      ultimately show ?thesis
        by simp
    next
      case False
      then have "j > k1"
        using j_ge by simp
      then have "tps3' ! j = ((string_to_contents (f1 x), Suc (length (f1 x))) #
          replicate (k2 - 1) (\<lfloor>[]\<rfloor>, 0)) ! (j - k1)"
        by (simp add: tps3'_def nth_append)
      moreover have "j - k1 < k2"
        by (metis \<open>k1 < j\<close> \<open>length tps3 = k1 + k2\<close> add.commute less_diff_conv2 less_imp_le that)
      ultimately have *: "tps3' ! j = (\<lfloor>[]\<rfloor>, 0)"
        by (metis (no_types, lifting) Suc_leI \<open>k1 < j\<close> add_leD1 le_add_diff_inverse2 less_diff_conv2
          nth_Cons_pos nth_replicate plus_1_eq_Suc zero_less_diff)
      have "tps3 ! j = tps2 ! j"
        using tps3_def \<open>k1 < j\<close> k_ge(1) by simp
      then have "tps3 ! j = tps1 ! j"
        using tps2_def \<open>k1 < j\<close> k_ge(1) by simp
      then have "tps3 ! j = tps1b ! (j - k1)"
        using tps1_def by (simp add: j_ge nth_append)
      then have "tps3 ! j = (\<lfloor>[]\<rfloor>, 0)"
        using tps1b_def by (simp add: \<open>j - k1 < k2\<close>)
      then show ?thesis
        using * by simp
    qed
  qed
qed

lemma tm3' [transforms_intros]:
  assumes "t = Suc (Suc (Suc (3 * T1 n)))"
  shows "transforms tm3 tps0 t tps3'"
proof -
  have "transforms tm3 tps0 (Suc (Suc (2 * T1 n + Suc (length (f1 x))))) tps3"
    using tm3 by simp
  moreover have "t \<ge> Suc (Suc (2 * T1 n + Suc (length (f1 x))))"
    using assms length_f1_x by simp
  ultimately show ?thesis
    using tps3' transforms_monotone by auto
qed

definition "tps4 \<equiv>
  tps1a [1 := (\<lfloor>[]\<rfloor>, 1)] @
  ((string_to_contents (f1 x), Suc (length (f1 x))) #
   replicate (k2 - 1) (\<lfloor>[]\<rfloor>, 0))"

lemma tm4:
  assumes "t = 9 + (3 * T1 n + (Suc (3 * length (string_to_symbols (f1 x)))))"
  shows "transforms tm4 tps0 t tps4"
  unfolding tm4_def
proof (tform)
  show "1 < length tps3'"
    using tps3'_def using tm1_tm turing_machine_def by auto
  let ?zs = "string_to_symbols (f1 x)"
  show "proper_symbols ?zs"
    by simp
  show "tps4 = tps3'[1 := (\<lfloor>[]\<rfloor>, 1)]"
    using tps4_def tps3'_def k_ge(1) length_tps1a by (simp add: list_update_append1)
  show "tps3' ::: 1 = \<lfloor>string_to_symbols (f1 x)\<rfloor>"
  proof -
    have "tps3' ! 1 = (string_to_contents (f1 x), Suc (length (f1 x)))"
      using tps3'_def k_ge(1) length_tps1a by (simp add: nth_append)
    then show ?thesis
      by auto
  qed
  have "tps3' :#: 1 = Suc (length (f1 x))"
    using tps3'_def k_ge(1) length_tps1a by (simp add: nth_append)
  then show "t = Suc (Suc (Suc (3 * T1 n))) +
      (tps3' :#: 1 + 2 * length (string_to_symbols (f1 x)) + 6)"
    using assms by simp
qed

lemma tm4' [transforms_intros]:
  assumes "t = 10 + (6 * T1 n)"
  shows "transforms tm4 tps0 t tps4"
proof (rule transforms_monotone[OF tm4], simp)
  show "10 + (3 * T1 n + 3 * length (f1 x)) \<le> t"
    using length_f1_x assms by simp
qed

definition "tps5 \<equiv>
  tps1a [1 := (\<lfloor>[]\<rfloor>, 1)] @
  ((string_to_contents (f1 x), 0) #
   replicate (k2 - 1) (\<lfloor>[]\<rfloor>, 0))"

lemma tm5:
  assumes "t = 11 + (6 * T1 n + tps4 :#: k1)"
  shows "transforms tm5 tps0 t tps5"
  unfolding tm5_def
proof (tform time: assms)
  show "k1 < length tps4"
    using tps4_def length_tps1a by simp
  show "tps5 = tps4[k1 := tps4 ! k1 |#=| 0]"
    using tps4_def tps5_def length_tps1a
    by (metis (no_types, lifting) fst_conv length_list_update list_update_length nth_append_length)
  show "clean_tape (tps4 ! k1)"
    using tps4_def length_tps1a clean_tape_def
    by (smt (z3) Suc_eq_plus1 add.commute add_cancel_right_right
      fst_conv length_list_update nat.distinct(1) nat_1_add_1 nth_append_length numeral_3_eq_3)
qed

abbreviation "ys \<equiv> string_to_symbols (f1 x)"

abbreviation "m \<equiv> length (f1 x)"

definition "tps5' \<equiv>
  tps1a [1 := (\<lfloor>[]\<rfloor>, 1)] @
  snd (start_config k2 ys)"

lemma tps5': "tps5 = tps5'"
  using tps5_def tps5'_def start_config_def by auto

lemma tm5' [transforms_intros]:
  assumes "t = 12 + 7 * T1 n"
  shows "transforms tm5 tps0 t tps5'"
proof -
  have "tps4 :#: k1 = Suc (length (f1 x))"
    using tps4_def
    by (metis (no_types, lifting) length_list_update length_tps1a nth_append_length snd_conv)
  then have "tps4 :#: k1 \<le> Suc (T1 n)"
    using length_f1_x by simp
  then have "t \<ge> 11 + (6 * T1 n + tps4 :#: k1)"
    using assms by simp
  then show ?thesis
    using tm5 transforms_monotone tps5' by simp
qed

definition tps6b :: "tape list" where
  "tps6b \<equiv> SOME tps. tps ::: 1 = string_to_contents (f2 (f1 x)) \<and>
       transforms M2 (snd (start_config k2 ys)) (T2 m) tps"

lemma tps6b:
  "tps6b ::: 1 = string_to_contents (f2 (f1 x))"
  "transforms M2 (snd (start_config k2 ys)) (T2 m) tps6b"
  using tps6b_def someI_ex[OF computes_in_timeD[OF computes2, of "f1 x"]]
  by simp_all

lemma tps6b_pos_le: "tps6b :#: 1 \<le> T2 m"
proof -
  have "execute M2 (start_config k2 ys) (T2 m) = (length M2, tps6b)"
    using transforms_def transits_def tps6b(2)
    by (metis (no_types, lifting) execute_after_halting_ge fst_conv start_config_def snd_conv)
  moreover have "execute M2 (start_config k2 ys) (T2 m) <#> 1 \<le> T2 m"
    using head_pos_le_time[OF tm_M2, of 1] k_ge by simp
  ultimately show ?thesis
    by simp
qed

lemma length_tps6b: "length tps6b = k2"
  using tm_M2 execute_num_tapes k_ge(2) tps5' tps5'_def tps5_def tps6b(2) transforms_def transits_def
  by (smt (verit, ccfv_threshold) One_nat_def Suc_diff_Suc length_Cons length_replicate less_le_trans
    minus_nat.diff_0 numeral_2_eq_2 prod.sel(2) same_append_eq zero_less_Suc)

lemma length_f2_f1_x: "length (f2 (f1 x)) \<le> T2 m"
proof -
  have "execute M2 (start_config k2 ys) (T2 m) = (length M2, tps6b)"
    using transforms_def transits_def tps6b(2)
    by (metis (no_types, lifting) execute_after_halting_ge fst_conv start_config_def snd_conv)
  moreover have "(execute M2 (start_config k2 ys) (T2 m) <:> 1) i = 0" if "i > T2 m" for i
    using blank_after_time[OF that _ _ tm_M2] k_ge(2) by simp
  ultimately have "(tps6b ::: 1) i = \<box>" if "i > T2 m" for i
    using that by simp
  then have "(string_to_contents (f2 (f1 x))) i = \<box>" if "i > T2 m" for i
    using that tps6b(1) by simp
  then have "length (string_to_symbols (f2 (f1 x))) \<le> T2 m"
    by (metis length_map order_refl verit_comp_simplify1(3) zero_neq_numeral zero_neq_one)
  then show ?thesis
    by simp
qed

lemma enlarged_M2: "transforms (enlarged G2 M2) (snd (start_config k2 ys)) (T2 m) tps6b"
proof -
  have "symbols_lt G2 (string_to_symbols (f1 x))"
    using tm_M2 turing_machine_def by simp
  then show ?thesis
    using transforms_enlarged[OF tm_M2 _ tps6b(2)] by simp
qed

lemma enlarged_M2_tm: "turing_machine k2 G (enlarged G2 M2)"
  using turing_machine_enlarged tm_M2 G2 by simp

definition "tps6 \<equiv> tps1a[1 := (\<lfloor>[]\<rfloor>, 1)] @ tps6b"

lemma tm56 [transforms_intros]: "transforms tm56 tps5' (T2 m) tps6"
  using transforms_prepend_tapes[OF enlarged_M2_tm _ _ enlarged_M2, of "tps1a [1 := (\<lfloor>[]\<rfloor>, 1)]" k1]
    tps5'_def tps6_def tm56_def start_config_length k_ge(2)
  by auto

lemma tps6_at_Suc_k1: "tps6 ::: (k1 + 1) = string_to_contents (f2 (f1 x))"
  and tps6_pos_le: "tps6 :#: (k1 + 1) \<le> T2 m"
proof -
  have "tps6 ! (k1 + 1) = tps6b ! 1"
    using tps6_def length_tps1a length_tps6b by (simp add: nth_append)
  then show
    "tps6 ::: (k1 + 1) = string_to_contents (f2 (f1 x))"
    "tps6 :#: (k1 + 1) \<le> T2 m"
    using tps6b(1) tps6b_pos_le by simp_all
qed

lemma tm6 [transforms_intros]:
  assumes "t = 12 + 7 * T1 n + T2 m"
  shows "transforms tm6 tps0 t tps6"
  unfolding tm6_def by (tform tps: assms)

definition "tps7 \<equiv>
  tps1a[1 := (\<lfloor>[]\<rfloor>, 1)] @
  tps6b[1 := (string_to_contents (f2 (f1 x)), 1)]"

lemma tps7_at_Suc_k1: "tps7 ! (k1 + 1) = (string_to_contents (f2 (f1 x)), 1)"
  using tps7_def k_ge(2) length_tps1a length_tps6b
  by (metis (no_types, lifting) One_nat_def Suc_le_lessD add.commute diff_add_inverse
    length_list_update not_add_less2 nth_append nth_list_update_eq numeral_2_eq_2)

lemma tm7:
  assumes "t = 14 + (7 * T1 n + (T2 m + tps6 :#: Suc k1))"
  shows "transforms tm7 tps0 t tps7"
  unfolding tm7_def
proof (tform time: assms)
  show "k1 + 1 < length tps6"
    using tps6_def k_ge(2) length_tps1a length_tps6b by simp
  show "clean_tape (tps6 ! (k1 + 1))"
    using tps6_at_Suc_k1 clean_tape_def by simp
  show "tps7 = tps6[k1 + 1 := tps6 ! (k1 + 1) |#=| 1]"
  proof -
    have "tps6 ! (k1 + 1) |#=| 1 = (string_to_contents (f2 (f1 x)), 1)"
      using tps6_at_Suc_k1 by simp
    then show ?thesis
      using tps6_def tps7_def length_tps1a length_tps6b k_ge tps7_at_Suc_k1
      by (metis (no_types, lifting) add.commute diff_add_inverse length_list_update
        list_update_append not_add_less2 plus_1_eq_Suc)
  qed
qed

corollary tm7' [transforms_intros]:
  assumes "t = 14 + 7 * T1 n + 2 * T2 m"
  shows "transforms tm7 tps0 t tps7"
proof (rule transforms_monotone[OF tm7], simp)
  show "14 + (7 * T1 n + (T2 (length (f1 x)) + tps6 :#: Suc k1)) \<le> t"
    using assms tps6_pos_le by simp
qed

definition "tps8 \<equiv>
  tps1a[1 := (string_to_contents (f2 (f1 x)), Suc (length (f2 (f1 x))))] @
  tps6b[1 := (string_to_contents (f2 (f1 x)), Suc (length (f2 (f1 x))))]"

lemma tps8_at_1: "tps8 ::: 1 = string_to_contents (f2 (f1 x))"
  using tps8_def length_tps1a k_ge(1)
  by (metis (no_types, lifting) One_nat_def Suc_le_lessD length_list_update nth_append
    nth_list_update_eq numeral_2_eq_2 prod.sel(1))

lemma tm8:
  assumes "t = 15 + 7 * T1 n + 2 * T2 m + length (f2 (f1 x))"
  shows "transforms tm8 tps0 t tps8"
  unfolding tm8_def
proof (tform tps: assms)
  show "k1 + 1 < length tps7"
    using tps7_def length_tps1a length_tps6b k_ge(2) by simp
  show "1 < length tps7"
    using tps7_def length_tps6b k_ge(2) by simp
  let ?n = "length (f2 (f1 x))"
  show "rneigh (tps7 ! (k1 + 1)) {\<box>} ?n"
  proof (rule rneighI)
   show "(tps7 ::: (k1 + 1)) (tps7 :#: (k1 + 1) + ?n) \<in> {\<box>}"
     using tps7_at_Suc_k1 by simp
   show "\<And>n'. n' < ?n \<Longrightarrow> (tps7 ::: (k1 + 1)) (tps7 :#: (k1 + 1) + n') \<notin> {\<box>}"
     using tps7_at_Suc_k1 by simp
  qed
  show "tps8 = tps7
    [k1 + 1 := tps7 ! (k1 + 1) |+| ?n,
     1 := implant (tps7 ! (k1 + 1)) (tps7 ! 1) ?n]"
     (is "tps8 = ?tps")
  proof (rule nth_equalityI)
    show "length tps8 = length ?tps"
      using tps8_def tps7_def by simp
    have len: "length tps8 = k1 + k2"
      using tps8_def length_tps6b by simp
    show "tps8 ! j = ?tps ! j" if "j < length tps8" for j
    proof (cases "j < k1")
      case j_less: True
      then have lhs: "tps8 ! j = tps1a[1 := (string_to_contents (f2 (f1 x)), Suc (length (f2 (f1 x))))] ! j"
        using tps8_def length_tps1a length_tps6b k_ge by (simp add: nth_append)
      show ?thesis
      proof (cases "j = 1")
        case True
        then have 1: "?tps ! j = implant (tps7 ! (k1 + 1)) (tps7 ! 1) ?n"
          using \<open>1 < length tps7\<close> by simp
        have 2: "tps8 ! j = (string_to_contents (f2 (f1 x)), Suc (length (f2 (f1 x))))"
          using lhs True j_less by simp
        have 3: "tps7 ! 1 = (\<lfloor>[]\<rfloor>, 1)"
          using tps7_def length_tps1a
          by (metis (no_types, lifting) True j_less length_list_update nth_append nth_list_update_eq)
        have "implant (string_to_contents (f2 (f1 x)), 1) (\<lfloor>[]\<rfloor>, 1) ?n =
            (string_to_contents (f2 (f1 x)), Suc ?n)"
          using implant contents_def by auto
        then show ?thesis
          using 1 2 3 tps7_at_Suc_k1 by simp
      next
        case False
        then have "?tps ! j = tps7 ! j"
          by (metis One_nat_def Suc_eq_plus1 add.commute j_less not_add_less2 nth_list_update_neq)
        then have "?tps ! j = tps1a ! j"
          using False j_less tps7_def length_tps1a
          by (metis (no_types, lifting) length_list_update nth_append nth_list_update_neq)
        moreover have "tps8 ! j = tps1a ! j"
          using False j_less tps8_def lhs by simp
        ultimately show ?thesis
          by simp
      qed
    next
      case j_ge: False
      then have lhs: "tps8 ! j = tps6b[1 := (string_to_contents (f2 (f1 x)), Suc (length (f2 (f1 x))))] ! (j - k1)"
        using tps8_def length_tps1a length_tps6b k_ge by (simp add: nth_append)
      show ?thesis
      proof (cases "j = Suc k1")
        case True
        then have "tps8 ! j = (string_to_contents (f2 (f1 x)), Suc (length (f2 (f1 x))))"
          using lhs len that length_tps6b by simp
        moreover have "?tps ! j = tps7 ! Suc k1 |+| ?n"
          using True \<open>k1 + 1 < length tps7\<close> k_ge(1) by simp
        ultimately show ?thesis
          using tps7_at_Suc_k1 True by simp
      next
        case False
        then have "tps8 ! j = tps6b ! (j - k1)"
          using lhs by simp
        moreover have "?tps ! j = tps7 ! j"
          using False j_ge that k_ge(1) by simp
        ultimately show ?thesis
          using tps7_def j_ge False length_tps1a
          by (metis (no_types, lifting) add.commute add_diff_inverse_nat length_list_update
            nth_append nth_list_update_neq plus_1_eq_Suc)
      qed
    qed
  qed
qed

lemma tm8':
  assumes "t = 15 + 7 * T1 n + 3 * T2 m"
  shows "transforms tm8 tps0 t tps8"
proof (rule transforms_monotone[OF tm8], simp)
  show "15 + 7 * T1 n + 2 * T2 m + length (f2 (f1 x)) \<le> t"
    using length_f2_f1_x assms by simp
qed

lemma tm8'_mono:
  assumes "mono T2"
    and "t = 15 + 7 * T1 n + 3 * T2 (T1 n)"
  shows "transforms tm8 tps0 t tps8"
proof (rule transforms_monotone[OF tm8'], simp)
  have "T2 (T1 n) \<ge> T2 m"
    using assms(1) length_f1_x monoE by auto
  then show "15 + 7 * T1 n + 3 * T2 m \<le> t"
    using assms(2) by simp
qed

end  (* context x *)

lemma computes_composed_mono:
  assumes "mono T2" and "T = (\<lambda>n. 15 + 7 * T1 n + 3 * T2 (T1 n))"
  shows "computes_in_time (k1 + k2) tm8 (f2 \<circ> f1) T"
proof
  fix x
  have "tps8 x ::: 1 = string_to_contents (f2 (f1 x))"
    using tps8_at_1 by simp
  moreover have "transforms tm8 (snd (start_config (k1 + k2) (string_to_symbols x))) (T (length x)) (tps8 x)"
    using tm8'_mono assms tps0_def zs_def by simp
  ultimately show "\<exists>tps.
      tps ::: 1 = string_to_contents ((f2 \<circ> f1) x) \<and>
      transforms tm8 (snd (start_config (k1 + k2) (string_to_symbols x))) (T (length x)) tps"
    by force
qed

end  (* locale compose *)

lemma computes_composed_poly:
  assumes tm_M1: "turing_machine k1 G1 M1"
    and tm_M2: "turing_machine k2 G2 M2"
    and computes1: "computes_in_time k1 M1 f1 T1"
    and computes2: "computes_in_time k2 M2 f2 T2"
  assumes "big_oh_poly T1" and "big_oh_poly T2"
  shows "\<exists>T k G M. big_oh_poly T \<and> turing_machine k G M \<and> computes_in_time k M (f2 \<circ> f1) T"
proof -
  obtain d1 :: nat where "big_oh T1 (\<lambda>n. n ^ d1)"
    using assms(5) big_oh_poly_def by auto
  obtain b c d2 :: nat where cm: "d2 > 0" "\<forall>n. T2 n \<le> b + c * n ^ d2"
    using big_oh_poly_offset[OF assms(6)] by auto
  let ?U = "\<lambda>n. b + c * n ^ d2"
  have U: "T2 n \<le> ?U n" for n
    using cm by simp
  have "mono ?U"
    by standard (simp add: cm(1))
  have computesU: "computes_in_time k2 M2 f2 ?U"
    using computes_in_time_mono[OF computes2 U] .
  interpret compo: compose k1 k2 G1 G2 M1 M2 T1 ?U f1 f2
    using assms computesU compose.intro by simp
  let ?M = "compo.tm8"
  let ?T = "(\<lambda>n. 15 + 7 * T1 n + 3 * (b + c * T1 n ^ d2))"
  have "computes_in_time (k1 + k2) ?M (f2 \<circ> f1) ?T"
    using compo.computes_composed_mono[OF `mono ?U`, of ?T] by simp
  moreover have "big_oh_poly ?T"
  proof -
    have "big_oh_poly (\<lambda>n. n ^ d2)"
      using big_oh_poly_poly by simp
    moreover have "(\<lambda>n. T1 n ^ d2) = (\<lambda>n. n ^ d2) \<circ> T1"
      by auto
    ultimately have "big_oh_poly (\<lambda>n. T1 n ^ d2)"
      using big_oh_poly_composition[OF assms(5)] by auto
    then have "big_oh_poly (\<lambda>n. 3 * (b + c * T1 n ^ d2))"
      using big_oh_poly_const big_oh_poly_prod big_oh_poly_sum by simp
    then show ?thesis
      using assms(5) big_oh_poly_const big_oh_poly_prod big_oh_poly_sum by simp
  qed
  moreover have "turing_machine (k1 + k2) compo.G ?M"
    using compo.tm8_tm .
  ultimately show ?thesis
    by auto
qed

end
