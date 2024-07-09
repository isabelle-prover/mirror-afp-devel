section "Running Time Formalization"

theory "Schoenhage_Strassen_TM"
  imports
    "Schoenhage_Strassen"
    "../Preliminaries/Schoenhage_Strassen_Preliminaries"
    "Z_mod_Fermat_TM"
    "Karatsuba.Karatsuba_TM"
    "Landau_Symbols.Landau_More"
begin

definition solve_special_residue_problem_tm where
"solve_special_residue_problem_tm n \<xi> \<eta> =1 do {
   n2 \<leftarrow> n +\<^sub>t 2;
   \<xi>mod \<leftarrow> take_tm n2 \<xi>;
   \<delta> \<leftarrow> int_lsbf_mod.subtract_mod_tm n2 \<eta> \<xi>mod;
   pown \<leftarrow> 2 ^\<^sub>t n;
   \<delta>_shifted \<leftarrow> \<delta> >>\<^sub>n\<^sub>t pown;
   \<delta>1 \<leftarrow> \<delta>_shifted +\<^sub>n\<^sub>t \<delta>;
   \<xi> +\<^sub>n\<^sub>t \<delta>1
}"

lemma val_solve_special_residue_problem_tm[simp, val_simp]:
  "val (solve_special_residue_problem_tm n \<xi> \<eta>) = solve_special_residue_problem n \<xi> \<eta>"
proof -
  have a: "n + 2 > 0" by simp
  show ?thesis
  unfolding solve_special_residue_problem_tm_def solve_special_residue_problem_def
  using int_lsbf_mod.val_subtract_mod_tm[OF int_lsbf_mod.intro[OF a]]
  by (simp add: Let_def)
qed

lemma time_solve_special_residue_problem_tm_le:
  "time (solve_special_residue_problem_tm n \<xi> \<eta>) \<le> 245 + 74 * 2 ^ n + 55 * length \<eta> + 2 * length \<xi>"
proof -
  define n2 where "n2 = n + 2"
  define \<xi>mod where "\<xi>mod = take n2 \<xi>"
  define \<delta> where "\<delta> = int_lsbf_mod.subtract_mod n2 \<eta> \<xi>mod"
  define pown where "pown = (2::nat) ^ n"
  define \<delta>_shifted where "\<delta>_shifted = \<delta> >>\<^sub>n pown"
  define \<delta>1 where "\<delta>1 = add_nat \<delta>_shifted \<delta>"
  note defs = n2_def \<xi>mod_def \<delta>_def pown_def \<delta>_shifted_def \<delta>1_def

  interpret mr: int_lsbf_mod n2 apply (intro int_lsbf_mod.intro) unfolding n2_def by simp

  have length_\<xi>mod_le: "length \<xi>mod \<le> n2" unfolding \<xi>mod_def by simp
  have length_\<delta>_le: "length \<delta> \<le> max n2 (length \<eta>)"
    unfolding \<delta>_def mr.subtract_mod_def if_distrib[where f = length] mr.length_reduce
    apply (estimation estimate: conjunct2[OF subtract_nat_aux])
    using length_\<xi>mod_le by auto
  have length_\<delta>1add_le: "max (length \<delta>_shifted) (length \<delta>) \<le> 2 ^ n + (n + 2) + length \<eta>"
      unfolding \<delta>_shifted_def pown_def
      using length_\<delta>_le unfolding n2_def by simp

  have "time (solve_special_residue_problem_tm n \<xi> \<eta>) =
    n + 1 + time (take_tm n2 \<xi>) + time (int_lsbf_mod.subtract_mod_tm n2 \<eta> \<xi>mod) +
    time (2 ^\<^sub>t n) +
    time (\<delta> >>\<^sub>n\<^sub>t pown) +
    time (\<delta>_shifted +\<^sub>n\<^sub>t \<delta>) +
    time (\<xi> +\<^sub>n\<^sub>t \<delta>1) +
    1"
    unfolding solve_special_residue_problem_tm_def tm_time_simps
    by (simp del: One_nat_def add_2_eq_Suc' add: add.assoc[symmetric] defs[symmetric])
  also have "... \<le> n + 1 + (n + 3) + (118 + 51 * (n + 2 + length \<eta>)) + 
    (3 * 2 ^ Suc n + 5 * n + 1) +
    (2 * 2 ^ n + 3) +
    (2 * 2 ^ n + 2 * length \<eta> + 2 * n + 7) +
    (2 * length \<xi> + 2 * 2 ^ n + 2 * n + 2 * length \<eta> + 9) +
    1"
    apply (intro add_mono order.refl)
    subgoal apply (estimation estimate: time_take_tm_le) unfolding n2_def by simp
    subgoal
      apply (estimation estimate: mr.time_subtract_mod_tm_le)
      apply (estimation estimate: length_\<xi>mod_le)
      apply (estimation estimate: Nat_max_le_sum[of "length \<eta>"])
      by (simp add: n2_def Nat_max_le_sum)
    subgoal by (rule time_power_nat_tm_le)
    subgoal unfolding time_shift_right_tm pown_def by simp
    subgoal
      apply (estimation estimate: time_add_nat_tm_le)
      apply (estimation estimate: length_\<delta>1add_le)
      by simp
    subgoal
      apply (estimation estimate: time_add_nat_tm_le)
      unfolding \<delta>1_def
      apply (estimation estimate: length_add_nat_upper)
      apply (estimation estimate: length_\<delta>1add_le)
      apply (estimation estimate: Nat_max_le_sum)
      by simp
    done
  also have "... = 245 + 12 * 2 ^ n + 62 * n + 55 * length \<eta> + 2 * length \<xi>" unfolding n2_def by simp
  also have "... \<le> 245 + 74 * 2 ^ n + 55 * length \<eta> + 2 * length \<xi>"
    using less_exp[of n] by simp
  finally show ?thesis .
qed

fun combine_z_aux_tm where
"combine_z_aux_tm l acc [] =1 rev_tm acc \<bind> concat_tm"
| "combine_z_aux_tm l acc [z] =1 combine_z_aux_tm l (z # acc) []"
| "combine_z_aux_tm l acc (z1 # z2 # zs) =1 do {
    (z1h, z1t) \<leftarrow> split_at_tm l z1;
    r \<leftarrow> z1t +\<^sub>n\<^sub>t z2;
    combine_z_aux_tm l (z1h # acc) (r # zs)
  }"

lemma val_combine_z_aux_tm[simp, val_simp]: "val (combine_z_aux_tm l acc zs) = combine_z_aux l acc zs"
  by (induction l acc zs rule: combine_z_aux.induct; simp)

lemma time_combine_z_aux_tm_le:
  assumes "\<And>z. z \<in> set zs \<Longrightarrow> length z \<le> lz"
  assumes "length z \<le> lz + 1"
  assumes "l > 0"
  shows "time (combine_z_aux_tm l acc (z # zs)) \<le> (2 * l + 2 * lz + 7) * length zs + 3 * (length acc + length zs) + length (concat acc) + length zs * l + lz + 9"
using assms proof (induction zs arbitrary: acc z)
  case Nil
  then show ?case
    by (simp del: One_nat_def)
next
  case (Cons z1 zs)
  then have len_drop_z: "length (drop l z) \<le> lz" by simp
  have lena: "length (add_nat (drop l z) z1) \<le> lz + 1"
    apply (estimation estimate: length_add_nat_upper)
    using len_drop_z Cons.prems by simp
  have "time (combine_z_aux_tm l acc (z # z1 # zs)) =
      time (split_at_tm l z) +
      time (drop l z +\<^sub>n\<^sub>t z1) +
      time (combine_z_aux_tm l (take l z # acc) ((drop l z +\<^sub>n z1) # zs)) + 1"
    by simp
  also have "... \<le>
      (2 * l + 3) +
      (2 * lz + 3) +
      ((2 * l + 2 * lz + 7) * length zs + 3 * (length (take l z # acc) + length zs) +
      length (concat (take l z # acc)) + length zs * l + lz + 9) + 1"
    apply (intro add_mono order.refl)
    subgoal by (simp add: time_split_at_tm)
    subgoal
      apply (estimation estimate: time_add_nat_tm_le)
      using len_drop_z Cons.prems by simp
    subgoal
      apply (intro Cons.IH)
      subgoal using Cons.prems by simp
      subgoal using lena .
      subgoal using Cons.prems(3) .
      done
    done
  also have "... = (2 * l + 2 * lz + 7) * length (z1 # zs) + 3 * (length acc + 1 + length zs) +
      length (concat acc) + length (take l z) + length zs * l + lz + 9"
    by simp
  also have "... \<le> (2 * l + 2 * lz + 7) * length (z1 # zs) + 3 * (length acc + 1 + length zs) +
      length (concat acc) + l + length zs * l + lz + 9"
    apply (intro add_mono order.refl) by simp
  also have "... = (2 * l + 2 * lz + 7) * length (z1 # zs) + 3 * (length acc + length (z1 # zs)) +
      length (concat acc) + length (z1 # zs) * l + lz + 9"
    by simp
  finally show ?case .
qed

definition combine_z_tm where "combine_z_tm l zs =1 combine_z_aux_tm l [] zs"

lemma val_combine_z_tm[simp, val_simp]: "val (combine_z_tm l zs) = combine_z l zs"
  unfolding combine_z_tm_def combine_z_def by simp

lemma time_combine_z_tm_le:
  assumes "\<And>z. z \<in> set zs \<Longrightarrow> length z \<le> lz"
  assumes "l > 0"
  shows "time (combine_z_tm l zs) \<le> 10 + (3 * l + 2 * lz + 10) * length zs"
proof (cases zs)
  case Nil
  then have "time (combine_z_tm l zs) = 5"
    unfolding combine_z_tm_def by simp
  then show ?thesis by simp
next
  case (Cons z zs')
  then have "time (combine_z_tm l zs) = time (combine_z_aux_tm l [] (z # zs')) + 1"
    unfolding combine_z_tm_def by simp
  also have "... \<le> (2 * l + 2 * lz + 7) * length zs' + 3 * (length ([] :: nat_lsbf list) + length zs') + length (concat ([] :: nat_lsbf list)) +
     length zs' * l + lz + 9 + 1"
    apply (intro add_mono time_combine_z_aux_tm_le order.refl)
    subgoal using Cons assms by simp
    subgoal using Cons assms by force
    subgoal using assms(2) .
    done
  also have "... = 10 + (3 * l + 2 * lz + 10) * length zs' + lz"
    by (simp add: add_mult_distrib)
  also have "... \<le> 10 + (3 * l + 2 * lz + 10) * length zs"
    unfolding Cons by simp
  finally show ?thesis .
qed

lemma schoenhage_strassen_tm_termination_aux: "\<not> m < 3 \<Longrightarrow> Suc (m div 2) < m"
  by linarith

function schoenhage_strassen_tm :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"schoenhage_strassen_tm m a b =1 do {
  m_le_3 \<leftarrow> m <\<^sub>t 3;
  if m_le_3 then do {
    ab \<leftarrow> a *\<^sub>n\<^sub>t b;
    int_lsbf_fermat.from_nat_lsbf_tm m ab
  } else do {
    odd_m \<leftarrow> odd_tm m;
    n \<leftarrow> (if odd_m then do {
        m1 \<leftarrow> m +\<^sub>t 1;
        m1 div\<^sub>t 2
      } else do {
        m2 \<leftarrow> m +\<^sub>t 2;
        m2 div\<^sub>t 2
      });
    n_plus_1 \<leftarrow> n +\<^sub>t 1;
    n_minus_1 \<leftarrow> n -\<^sub>t 1;
    n_plus_2 \<leftarrow> n +\<^sub>t 2;
    oe_n \<leftarrow> (if odd_m then return n_plus_1 else return n);
    segment_lens \<leftarrow> 2 ^\<^sub>t n_minus_1;
    a' \<leftarrow> subdivide_tm segment_lens a;
    b' \<leftarrow> subdivide_tm segment_lens b;
    \<alpha> \<leftarrow> map_tm (int_lsbf_mod.reduce_tm n_plus_2) a';
    three_n \<leftarrow> 3 *\<^sub>t n;
    pad_length \<leftarrow> three_n +\<^sub>t 5;
    \<alpha>_padded \<leftarrow> map_tm (fill_tm pad_length) \<alpha>;
    u \<leftarrow> concat_tm \<alpha>_padded;
    \<beta> \<leftarrow> map_tm (int_lsbf_mod.reduce_tm n_plus_2) b';
    \<beta>_padded \<leftarrow> map_tm (fill_tm pad_length) \<beta>;
    v \<leftarrow> concat_tm \<beta>_padded;
    oe_n_plus_1 \<leftarrow> oe_n +\<^sub>t 1;
    two_pow_oe_n_plus_1 \<leftarrow> 2 ^\<^sub>t oe_n_plus_1;
    uv_length \<leftarrow> pad_length *\<^sub>t two_pow_oe_n_plus_1;
    uv_unpadded \<leftarrow> karatsuba_mul_nat_tm u v;
    uv \<leftarrow> ensure_length_tm uv_length uv_unpadded;
    oe_n_minus_1 \<leftarrow> oe_n -\<^sub>t 1;
    two_pow_oe_n_minus_1 \<leftarrow> 2 ^\<^sub>t oe_n_minus_1;
    \<gamma>s \<leftarrow> subdivide_tm pad_length uv;
    \<gamma> \<leftarrow> subdivide_tm two_pow_oe_n_minus_1 \<gamma>s;
    \<gamma>0 \<leftarrow> nth_tm \<gamma> 0;
    \<gamma>1 \<leftarrow> nth_tm \<gamma> 1;
    \<gamma>2 \<leftarrow> nth_tm \<gamma> 2;
    \<gamma>3 \<leftarrow> nth_tm \<gamma> 3;
    \<eta> \<leftarrow> map4_tm
       (\<lambda>x y z w. do {
          xmod \<leftarrow> take_tm n_plus_2 x;
          ymod \<leftarrow> take_tm n_plus_2 y;
          zmod \<leftarrow> take_tm n_plus_2 z;
          wmod \<leftarrow> take_tm n_plus_2 w;
          xy \<leftarrow> int_lsbf_mod.subtract_mod_tm n_plus_2 xmod ymod;
          zw \<leftarrow> int_lsbf_mod.subtract_mod_tm n_plus_2 zmod wmod;
          int_lsbf_mod.add_mod_tm n_plus_2 xy zw
        })
       \<gamma>0 \<gamma>1 \<gamma>2 \<gamma>3;
    prim_root_exponent \<leftarrow> if odd_m then return 1 else return 2;
    fn_carrier_len \<leftarrow> 2 ^\<^sub>t n_plus_1;
    a'_carrier \<leftarrow> map_tm (fill_tm fn_carrier_len) a';
    b'_carrier \<leftarrow> map_tm (fill_tm fn_carrier_len) b';
    a_dft \<leftarrow> int_lsbf_fermat.fft_tm n prim_root_exponent a'_carrier;
    b_dft \<leftarrow> int_lsbf_fermat.fft_tm n prim_root_exponent b'_carrier;
    a_dft_odds \<leftarrow> evens_odds_tm False a_dft;
    b_dft_odds \<leftarrow> evens_odds_tm False b_dft;
    c_dft_odds \<leftarrow> map2_tm (schoenhage_strassen_tm n) a_dft_odds b_dft_odds;
    prim_root_exponent_2 \<leftarrow> prim_root_exponent *\<^sub>t 2;
    c_diffs \<leftarrow> int_lsbf_fermat.ifft_tm n prim_root_exponent_2 c_dft_odds;
    two_pow_oe_n \<leftarrow> 2 ^\<^sub>t oe_n;
    interval1 \<leftarrow> upt_tm 0 two_pow_oe_n_minus_1;
    interval2 \<leftarrow> upt_tm two_pow_oe_n_minus_1 two_pow_oe_n;
    two_pow_n \<leftarrow> 2 ^\<^sub>t n;
    oe_n_plus_two_pow_n \<leftarrow> oe_n +\<^sub>t two_pow_n;
    oe_n_plus_two_pow_n_zeros \<leftarrow> replicate_tm oe_n_plus_two_pow_n False;
    oe_n_plus_two_pow_n_one \<leftarrow> oe_n_plus_two_pow_n_zeros @\<^sub>t [True];
    \<xi>' \<leftarrow> map2_tm (\<lambda>x y. do {
        v1 \<leftarrow> prim_root_exponent *\<^sub>t y;
        v2 \<leftarrow> oe_n +\<^sub>t v1;
        v3 \<leftarrow> v2 -\<^sub>t 1;
        summand1 \<leftarrow> int_lsbf_fermat.divide_by_power_of_2_tm x v3;
        summand2 \<leftarrow> int_lsbf_fermat.from_nat_lsbf_tm n oe_n_plus_two_pow_n_one;
        int_lsbf_fermat.add_fermat_tm n summand1 summand2
      })
      c_diffs interval1;
    \<xi> \<leftarrow> map_tm (int_lsbf_fermat.reduce_tm n) \<xi>';
    z \<leftarrow> map2_tm (solve_special_residue_problem_tm n) \<xi> \<eta>;
    z_filled \<leftarrow> map_tm (fill_tm segment_lens) z;
    z_consts \<leftarrow> replicate_tm two_pow_oe_n_minus_1 oe_n_plus_two_pow_n_one;
    z_complete \<leftarrow> z_filled @\<^sub>t z_consts;
    z_sum \<leftarrow> combine_z_tm segment_lens z_complete;
    result \<leftarrow> int_lsbf_fermat.from_nat_lsbf_tm m z_sum;
    return result
  }
}"
  by pat_completeness auto
termination
  apply (relation "Wellfounded.measure (\<lambda>(n, a, b). n)")
  subgoal by blast
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  subgoal for m by (cases "odd m"; simp)
  done

context schoenhage_strassen_context begin

abbreviation \<gamma>0 where "\<gamma>0 \<equiv> \<gamma> ! 0"
abbreviation \<gamma>1 where "\<gamma>1 \<equiv> \<gamma> ! 1"
abbreviation \<gamma>2 where "\<gamma>2 \<equiv> \<gamma> ! 2"
abbreviation \<gamma>3 where "\<gamma>3 \<equiv> \<gamma> ! 3"

definition fn_carrier_len where "fn_carrier_len = (2::nat) ^ (n + 1)"
definition segment_lens where "segment_lens = (2::nat) ^ (n - 1)"
definition interval1 where "interval1 = [0..<2 ^ (oe_n - 1)]"
definition interval2 where "interval2 = [2 ^ (oe_n - 1)..<2 ^ oe_n]"
definition oe_n_plus_two_pow_n_zeros where "oe_n_plus_two_pow_n_zeros = replicate (oe_n + 2 ^ n) False"
definition oe_n_plus_two_pow_n_one where "oe_n_plus_two_pow_n_one = append oe_n_plus_two_pow_n_zeros [True]"
definition z_complete where "z_complete = z_filled @ z_consts"


lemmas defs' =  
      segment_lens_def fn_carrier_len_def
      c_diffs_def interval1_def interval2_def
      oe_n_plus_two_pow_n_zeros_def oe_n_plus_two_pow_n_one_def
      z_complete_def

lemma z_filled_def': "z_filled = map (fill segment_lens) z"
  unfolding z_filled_def defs'[symmetric] by (rule refl)
lemma z_sum_def': "z_sum = combine_z segment_lens z_complete"
  unfolding z_sum_def defs'[symmetric] by (rule refl)

lemmas defs'' = defs' z_filled_def' z_sum_def'

lemma segment_lens_pos: "segment_lens > 0" unfolding segment_lens_def by simp

(* lengths, carriers etc. *)
lemma length_\<gamma>s: "length \<gamma>s = 2 ^ (oe_n + 1)"
  using scuv(1) unfolding defs[symmetric] .
lemma length_\<gamma>s': "length \<gamma>s = 2 ^ (oe_n - 1) * 4"
  using two_pow_Suc_oe_n_as_prod length_\<gamma>s unfolding defs[symmetric]
  by simp

lemma val_nth_\<gamma>[simp, val_simp]:
      "val (nth_tm \<gamma> 0) = \<gamma> ! 0"
      "val (nth_tm \<gamma> 1) = \<gamma> ! 1"
      "val (nth_tm \<gamma> 2) = \<gamma> ! 2"
      "val (nth_tm \<gamma> 3) = \<gamma> ! 3"
  unfolding defs' using sc\<gamma> by simp_all

lemma val_fft1[simp, val_simp]: "val (int_lsbf_fermat.fft_tm n prim_root_exponent A.num_blocks_carrier) =
      int_lsbf_fermat.fft n prim_root_exponent A.num_blocks_carrier"
      by (intro int_lsbf_fermat.val_fft_tm[where m = oe_n] A.length_num_blocks_carrier)
lemma val_fft2[simp, val_simp]: "val (int_lsbf_fermat.fft_tm n prim_root_exponent B.num_blocks_carrier) =
      int_lsbf_fermat.fft n prim_root_exponent B.num_blocks_carrier"
      by (intro int_lsbf_fermat.val_fft_tm[where m = oe_n] B.length_num_blocks_carrier)

lemma val_ifft[simp, val_simp]: "val (int_lsbf_fermat.ifft_tm n (prim_root_exponent * 2) c_dft_odds) =
                       int_lsbf_fermat.ifft n (prim_root_exponent * 2) c_dft_odds"
  apply (intro int_lsbf_fermat.val_ifft_tm[where m = "oe_n - 1"])
  apply (simp add: c_dft_odds_def)
  done

end

lemma val_schoenhage_strassen_tm[simp, val_simp]:
  assumes "a \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  assumes "b \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  shows "val (schoenhage_strassen_tm m a b) = schoenhage_strassen m a b"
using assms proof (induction m arbitrary: a b rule: less_induct)
  case (less m)
  show ?case
  proof (cases "m < 3")
    case True
    then show ?thesis
      unfolding schoenhage_strassen_tm.simps[of m a b] val_simps
      unfolding schoenhage_strassen.simps[of m a b]
      using int_lsbf_fermat.val_from_nat_lsbf_tm by simp
  next
    case False

    interpret schoenhage_strassen_context m a b
      apply unfold_locales using False less.prems by simp_all
    
    have val_ih: "map2 (\<lambda>x y. val (schoenhage_strassen_tm n x y)) A.num_dft_odds B.num_dft_odds =
      map2 (\<lambda>x y. schoenhage_strassen n x y) A.num_dft_odds B.num_dft_odds"
      apply (intro map_cong refl)
      subgoal premises prems for p
      proof -
        from prems set_zip obtain i
          where i_le: "i < min (length A.num_dft_odds) (length B.num_dft_odds)"
            and p_i: "p = (A.num_dft_odds ! i, B.num_dft_odds ! i)"
          by blast
        then have "i < 2 ^ (oe_n - 1)"
          using A.length_num_dft_odds by simp
        show ?thesis unfolding p_i prod.case
          apply (intro less.IH n_lt_m set_subseteqD A.num_dft_odds_carrier B.num_dft_odds_carrier)
          using i_le by simp_all
      qed
      done

    have "val (schoenhage_strassen_tm m a b) = result"
      unfolding schoenhage_strassen_tm.simps[of m a b]
      unfolding val_simp
        val_times_nat_tm (* TODO declare val_times_nat_tm as val_simp *)
        val_subdivide_tm[OF segment_lens_pos] val_subdivide_tm[OF pad_length_gt_0]
        Znr.val_reduce_tm Znr.val_subtract_mod_tm Znr.val_add_mod_tm
        val_nth_\<gamma> val_subdivide_tm[OF two_pow_pos] val_fft1 val_fft2 val_ih val_ifft
        defs[symmetric] Let_def
        val_subdivide_tm[OF two_pow_pos] Fnr.val_ifft_tm[OF length_c_dft_odds]
      using False by argo
    then show ?thesis using result_eq by argo
  qed
qed

fun schoenhage_strassen_Fm_bound where
"schoenhage_strassen_Fm_bound m = (if m < 3 then 5336 else
  let n = (if odd m then (m + 1) div 2 else (m + 2) div 2);
    oe_n = (if odd m then n + 1 else n) in
    23525 * 2 ^ m + 8093 * (n * 2 ^ (2 * n)) + 8410 +
    time_karatsuba_mul_nat_bound ((3 * n + 5) * 2 ^ oe_n) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1))"

declare schoenhage_strassen_Fm_bound.simps[simp del]

lemma time_schoenhage_strassen_tm_le:
  assumes "a \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  assumes "b \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
  shows "time (schoenhage_strassen_tm m a b) \<le> schoenhage_strassen_Fm_bound m"
  using assms proof (induction m arbitrary: a b rule: less_induct)
  case (less m)
  consider "m = 0" | "m \<ge> 1 \<and> m < 3" | "\<not> m < 3" by linarith
  then show ?case
  proof cases
    case 1
    from less.prems int_lsbf_fermat.fermat_carrier_length
    have len_ab: "length a = 2" "length b = 2" unfolding 1 by simp_all
    then have len_mul_ab: "length (grid_mul_nat a b) \<le> 4"
      using length_grid_mul_nat[of a b] by simp
    from 1 have "time (schoenhage_strassen_tm m a b) =
      time (m <\<^sub>t 3) +
      time (a *\<^sub>n\<^sub>t b) +
      time (int_lsbf_fermat.from_nat_lsbf_tm m (grid_mul_nat a b)) + 1"
      unfolding schoenhage_strassen_tm.simps[of m a b] time_bind_tm val_less_nat_tm
      by (simp del: One_nat_def)
    also have "... \<le> (2 * m + 2) +
      (8 * length a * max (length a) (length b) + 1) +
      int_lsbf_fermat.time_from_nat_lsbf_tm_bound m (length (grid_mul_nat a b)) + 1"
      apply (intro add_mono order.refl)
      subgoal by (simp add: time_less_nat_tm 1)
      subgoal by (rule time_grid_mul_nat_tm_le)
      subgoal by (intro int_lsbf_fermat.time_from_nat_lsbf_tm_le_bound order.refl)
      done
    also have "... \<le> 2 + 33 + 240 + 1"
      apply (intro add_mono order.refl)
      subgoal unfolding 1 by simp
      subgoal unfolding len_ab by simp
      subgoal unfolding int_lsbf_fermat.time_from_nat_lsbf_tm_bound.simps[of 0 "(length (grid_mul_nat a b))"] 1
        using len_mul_ab by simp
      done
    also have "... = 276" by simp
    finally show ?thesis unfolding schoenhage_strassen_Fm_bound.simps[of m] using 1 by simp
  next
    case 2
    then have "(2::nat) ^ (m + 1) \<ge> 4"
      using power_increasing[of 2 "m + 1" "2::nat"] by simp
    from 2 have "(2::nat) ^ (m + 1) \<le> 8"
      using power_increasing[of "m + 1" 3 "2::nat"] by simp
    from less.prems have len_ab: "length a = 2 ^ (m + 1)" "length b = 2 ^ (m + 1)"
      using int_lsbf_fermat.fermat_carrier_length by simp_all
    then have len_ab_le: "length a \<le> 8" "length b \<le> 8"
      using \<open>2 ^ (m + 1) \<le> 8\<close> by linarith+
    have len_mul_ab_le: "length (grid_mul_nat a b) \<le> 2 * 2 ^ (m + 1)"
      using length_grid_mul_nat[of a b] len_ab by simp
    from 2 have "time (schoenhage_strassen_tm m a b) =
      time (m <\<^sub>t 3) +
      time (a *\<^sub>n\<^sub>t b) +
      time (int_lsbf_fermat.from_nat_lsbf_tm m (grid_mul_nat a b)) + 1"
      unfolding schoenhage_strassen_tm.simps[of m a b] time_bind_tm val_less_nat_tm
      by (simp del: One_nat_def)
    also have "... \<le> (2 * m + 2) +
      (8 * length a * max (length a) (length b) + 1) +
      (720 + 512 * 2 ^ (m + 1)) + 1"
      apply (intro add_mono order.refl)
      subgoal by (simp add: time_less_nat_tm 2)
      subgoal by (rule time_grid_mul_nat_tm_le)
      subgoal using int_lsbf_fermat.time_from_nat_lsbf_tm_le[OF \<open>4 \<le> 2 ^ (m + 1)\<close> len_mul_ab_le]
        by simp
      done
    also have "... \<le> 6 + 513 + (720 + 512 * 8) + 1"
      apply (intro add_mono mult_le_mono order.refl)
      subgoal using 2 by simp
      subgoal
        apply (estimation estimate: max.boundedI[OF len_ab_le])
        using len_ab_le by simp
      subgoal using \<open>2 ^ (m + 1) \<le> 8\<close> .
      done
    also have "... = 5336" by simp
    finally show ?thesis unfolding schoenhage_strassen_Fm_bound.simps[of m] using 2 by simp
  next
    case 3

    interpret schoenhage_strassen_context m a b
      apply unfold_locales using 3 less.prems by simp_all

    define time_\<eta> where "time_\<eta> = time (map4_tm
       (\<lambda>x y z w. do {
          xmod \<leftarrow> take_tm (n + 2) x;
          ymod \<leftarrow> take_tm (n + 2) y;
          zmod \<leftarrow> take_tm (n + 2) z;
          wmod \<leftarrow> take_tm (n + 2) w;
          xy \<leftarrow> Znr.subtract_mod_tm xmod ymod;
          zw \<leftarrow> Znr.subtract_mod_tm zmod wmod;
          Znr.add_mod_tm xy zw
        })
       \<gamma>0 \<gamma>1 \<gamma>2 \<gamma>3)" (is "time_\<eta> = time (map4_tm ?\<eta>_fun _ _ _ _)")
    define time_\<xi>' where "time_\<xi>' = time (map2_tm (\<lambda>x y. do {
            v1 \<leftarrow> prim_root_exponent *\<^sub>t y;
            v2 \<leftarrow> oe_n +\<^sub>t v1;
            v3 \<leftarrow> v2 -\<^sub>t 1;
            summand1 \<leftarrow> Fnr.divide_by_power_of_2_tm x v3;
            summand2 \<leftarrow> Fnr.from_nat_lsbf_tm oe_n_plus_two_pow_n_one;
            Fnr.add_fermat_tm summand1 summand2
          })
          c_diffs interval1)"
    define time_\<xi> where "time_\<xi> = time (map_tm (int_lsbf_fermat.reduce_tm n) \<xi>')"
    define time_z where "time_z = time (map2_tm (solve_special_residue_problem_tm n) \<xi> \<eta>)"
    define time_z_filled where "time_z_filled = time (map_tm (fill_tm segment_lens) z)"

    note map_time_defs = time_\<eta>_def time_\<xi>'_def time_\<xi>_def time_z_def time_z_filled_def

    from Fmr.res_carrier_eq have Fm_carrierI: "\<And>i. 0 \<le> i \<Longrightarrow> i < 2 ^ 2 ^ m + 1 \<Longrightarrow> i \<in> carrier Fm"
      by simp

    have length_uv_unpadded_le: "length uv_unpadded \<le> 12 * (3 * n + 5) * 2 ^ oe_n +
    (6 + 2 * karatsuba_lower_bound)"
      unfolding uv_unpadded_def
      apply (estimation estimate: length_karatsuba_mul_nat_le)
      unfolding A.length_num_Zn_pad B.length_num_Zn_pad pad_length_def by simp

    have prim_root_exponent_le: "prim_root_exponent \<le> 2" unfolding prim_root_exponent_def by simp
    then have prim_root_exponent_2_le: "prim_root_exponent * 2 \<le> 4"
      by simp

    have length_interval1: "length interval1 = 2 ^ (oe_n - 1)"
      unfolding interval1_def by simp
    have length_interval2: "length interval2 = 2 ^ (oe_n - 1)"
      unfolding interval2_def using two_pow_oe_n_as_halves by simp
    have length_oe_n_plus_two_pow_n_zeros: "length oe_n_plus_two_pow_n_zeros = oe_n + 2 ^ n"
      unfolding oe_n_plus_two_pow_n_zeros_def by simp
    have length_oe_n_plus_two_pow_n_one: "length oe_n_plus_two_pow_n_one = oe_n + 2 ^ n + 1"
      unfolding oe_n_plus_two_pow_n_one_def
      using length_oe_n_plus_two_pow_n_zeros by simp
    have c_dft_odds_carrier: "set c_dft_odds \<subseteq> Fnr.fermat_non_unique_carrier"
      unfolding c_dft_odds_def
      apply (intro set_subseteqI)
      subgoal premises prems for i
      proof -
        have "map2 (schoenhage_strassen n) A.num_dft_odds B.num_dft_odds ! i =
          schoenhage_strassen n (A.num_dft_odds ! i) (B.num_dft_odds ! i)"
          using nth_map prems by simp
        also have "... \<in> Fnr.fermat_non_unique_carrier"
          apply (intro conjunct2[OF schoenhage_strassen_correct'])
          subgoal
            apply (intro set_subseteqD[OF A.num_dft_odds_carrier])
            using prems by simp
          subgoal
            apply (intro set_subseteqD[OF B.num_dft_odds_carrier])
            using prems by simp
          done
        finally show ?thesis .
      qed
      done
    have c_diffs_carrier: "c_diffs ! i \<in> Fnr.fermat_non_unique_carrier" if "i < 2 ^ (oe_n - 1)" for i
      unfolding c_diffs_def Fnr.ifft.simps
      apply (intro set_subseteqD[OF Fnr.fft_ifft_carrier[of _ "oe_n - 1"]])
      subgoal using length_c_dft_odds .
      subgoal using c_dft_odds_carrier .
      subgoal using Fnr.length_ifft[OF length_c_dft_odds] that by simp
      done
    have \<xi>'_carrier: "\<xi>' ! i \<in> Fnr.fermat_non_unique_carrier" if "i < 2 ^ (oe_n - 1)" for i
    proof -
      from that have "\<xi>' ! i = Fnr.add_fermat
              (Fnr.divide_by_power_of_2 (c_diffs ! i)
                (oe_n + prim_root_exponent * ([0..<2 ^ (oe_n - 1)] ! i) - 1))
              (Fnr.from_nat_lsbf (replicate (oe_n + 2 ^ n) False @ [True]))"
        unfolding \<xi>'_def using nth_map2 that length_c_diffs by simp
      also have "... \<in> Fnr.fermat_non_unique_carrier"
        apply (intro Fnr.add_fermat_closed)
        subgoal
          by (intro Fnr.divide_by_power_of_2_closed that c_diffs_carrier)
        subgoal by (intro Fnr.from_nat_lsbf_correct(1))
        done
      finally show "\<xi>' ! i \<in> Fnr.fermat_non_unique_carrier" .
    qed
    have \<xi>'_carrier': "set \<xi>' \<subseteq> Fnr.fermat_non_unique_carrier"
      apply (intro set_subseteqI \<xi>'_carrier) unfolding length_\<xi>' .
    have length_\<xi>_entries: "length x \<le> 2 ^ n + 2" if "x \<in> set \<xi>" for x
    proof -
      from that obtain x' where "x' \<in> set \<xi>'" "x = Fnr.reduce x'" unfolding \<xi>_def
        by auto
      from that show ?thesis unfolding \<open>x = Fnr.reduce x'\<close>
        apply (intro Fnr.reduce_correct'(2))
        using \<open>x' \<in> set \<xi>'\<close> \<xi>'_carrier' by auto
    qed
    have length_\<eta>_entries: "length (\<eta> ! i) = n + 2" if "i < 2 ^ (oe_n - 1)" for i
    proof -
      have "\<eta> ! i = Znr.add_mod (Znr.subtract_mod (take (n + 2) (\<gamma>0 ! i)) (take (n + 2) (\<gamma>1 ! i)))
            (Znr.subtract_mod (take (n + 2) (\<gamma>2 ! i)) (take (n + 2) (\<gamma>3 ! i)))"
        unfolding \<eta>_def Let_def defs'[symmetric]
        apply (intro nth_map4)
        unfolding length_\<gamma>s defs' using length_\<gamma>_i that by simp_all
      then show ?thesis using Znr.add_mod_closed by simp
    qed
    have length_z_entries: "length (z ! i) \<le> 2 ^ n + n + 4" if "i < 2 ^ (oe_n - 1)" for i
    proof -
      have "z ! i = solve_special_residue_problem n (\<xi> ! i) (\<eta> ! i)"
        unfolding z_def apply (intro nth_map2) using that length_\<xi> length_\<eta> by simp_all
      also have "length ... \<le> max (length (\<xi> ! i))
        (2 ^ n + length (Znr.subtract_mod (\<eta> ! i) (take (n + 2) (\<xi> ! i))) + 1) + 1"
        unfolding solve_special_residue_problem_def Let_def defs[symmetric]
        apply (estimation estimate: length_add_nat_upper)
        apply (estimation estimate: length_add_nat_upper)
        by (simp del: One_nat_def)
      also have "... \<le> max (2 ^ n + 2) ((2 ^ n + (n + 2)) + 1) + 1"
        apply (intro add_mono order.refl max.mono)
        subgoal using length_\<xi>_entries nth_mem[of i \<xi>] length_\<xi> that by simp
        subgoal apply (intro Znr.length_subtract_mod)
          subgoal using length_\<eta>_entries[OF that] by simp
          subgoal by simp
          done
        done
      also have "... = 2 ^ n + n + 4" by simp
      finally show ?thesis .
    qed
    have length_z_filled_entries: "length (z_filled ! i) \<le> 2 ^ n + n + 4" if "i < 2 ^ (oe_n - 1)" for i
    proof -
      have "z_filled ! i = fill (2 ^ (n - 1)) (z ! i)"
        unfolding z_filled_def segment_lens_def
        using nth_map[of i z] unfolding length_z
        using that by auto
      also have "length ... \<le> max (2 ^ (n - 1)) (2 ^ n + n + 4)"
        using length_z_entries[OF that] unfolding length_fill' by simp
      also have "... \<le> 2 ^ n + n + 4"
        apply (intro max.boundedI order.refl)
        using power_increasing[of "n - 1" n "2::nat"] by linarith
      finally show ?thesis .
    qed

    have length_z_complete_entries: "length i \<le> 2 ^ n + n + 4" if "i \<in> set z_complete" for i
    proof -
      from that consider "i \<in> set z_filled" | "i \<in> set z_consts"
        unfolding z_complete_def by auto
      then show ?thesis
      proof cases
        case 1
        show ?thesis
          using iffD1[OF in_set_conv_nth 1] length_z_filled_entries length_z_filled
          by auto
      next
        case 2
        then have i_eq: "i = oe_n_plus_two_pow_n_one"
          unfolding z_consts_def defs'
          by simp
        show ?thesis unfolding i_eq length_oe_n_plus_two_pow_n_one
          using oe_n_le_n by simp
      qed
    qed
    have length_z_complete: "length z_complete = 2 ^ oe_n"
      unfolding z_complete_def
      by (simp add: length_z_filled length_z_consts two_pow_oe_n_as_halves)
    have length_z_sum_le: "length z_sum \<le> 28 * Fmr.e"
    proof -
      have "length z_sum \<le> ((2 ^ n + n + 4) + 1) * length z_complete"
        unfolding z_sum_def z_complete_def
        apply (intro length_combine_z_le segment_lens_pos)
        using length_z_complete_entries z_complete_def by simp_all
      also have "... = (2 ^ n + n + 5) * 2 ^ oe_n"
        unfolding length_z_complete by simp
      also have "... \<le> (2 ^ n + 2 ^ n + 5 * 2 ^ n) * (2 * 2 ^ n)"
        apply (intro mult_le_mono add_mono order.refl)
        subgoal using less_exp by simp
        subgoal by simp (* very crude estimation *)
        subgoal by (estimation estimate: oe_n_le_n; simp)
        done
      also have "... = 14 * 2 ^ (2 * n)"
        by (simp add: mult_2[of n] power_add)
      also have "... \<le> 28 * Fmr.e"
        using two_pow_two_n_le by simp
      finally show ?thesis .
    qed

    have val_ih: "map2 (\<lambda>x y. val (schoenhage_strassen_tm n x y)) A.num_dft_odds B.num_dft_odds =
      c_dft_odds"
      unfolding c_dft_odds_def
      apply (intro map_cong ext refl)
      subgoal premises prems for p
      proof -
        from prems obtain i where p_decomp: "i < length A.num_dft_odds" "i < length B.num_dft_odds"
          "p = (A.num_dft_odds ! i, B.num_dft_odds ! i)"
          using set_zip[of A.num_dft_odds B.num_dft_odds] by auto
        show ?thesis unfolding p_decomp prod.case
          apply (intro val_schoenhage_strassen_tm)
          subgoal using set_subseteqD[OF A.num_dft_odds_carrier]
            using p_decomp by simp
          subgoal using set_subseteqD[OF B.num_dft_odds_carrier]
            using p_decomp by simp
          done
      qed
      done

    have \<xi>'_alt: "map2
               (\<lambda>x y. Fnr.add_fermat
                       (Fmr.divide_by_power_of_2 x (oe_n + prim_root_exponent * y - 1))
                       (Fnr.from_nat_lsbf oe_n_plus_two_pow_n_one))
               c_diffs interval1 = \<xi>'"
      unfolding \<xi>'_def Let_def defs'[symmetric] by (rule refl)

    have "time_\<eta> \<le> ((112 * (n + 2) + 254) + 1) * min (min (min (length \<gamma>0) (length \<gamma>1)) (length \<gamma>2)) (length \<gamma>3) + 1"
      unfolding time_\<eta>_def
      apply (intro time_map4_tm_bounded)
      unfolding tm_time_simps add.assoc[symmetric] val_take_tm Znr.val_subtract_mod_tm Znr.val_add_mod_tm
      subgoal premises prems for x y z w
      proof -
        have "time (take_tm (n + 2) x) + time (take_tm (n + 2) y) + time (take_tm (n + 2) z) + time (take_tm (n + 2) w) +
          time (Znr.subtract_mod_tm (take (n + 2) x) (take (n + 2) y)) +
          time (Znr.subtract_mod_tm (take (n + 2) z) (take (n + 2) w)) +
          time (Znr.add_mod_tm (Znr.subtract_mod (take (n + 2) x) (take (n + 2) y)) (Znr.subtract_mod (take (n + 2) z) (take (n + 2) w))) \<le>
          ((n + 2) + 1) + ((n + 2) + 1) + ((n + 2) + 1) + ((n + 2) + 1) +
          (118 + 51 * (n + 2)) +
          (118 + 51 * (n + 2)) +
          (14 + 4 * (n + 2) + 2 * (n + 2))"
          apply (intro add_mono time_take_tm_le)
          subgoal
            apply (estimation estimate: Znr.time_subtract_mod_tm_le)
            unfolding length_take
            apply (estimation estimate: min.cobounded2)
            apply (estimation estimate: min.cobounded2)
            by (simp add: defs')
          subgoal
            apply (estimation estimate: Znr.time_subtract_mod_tm_le)
            unfolding length_take
            apply (estimation estimate: min.cobounded2)
            apply (estimation estimate: min.cobounded2)
            by (simp add: defs')
          subgoal
            apply (estimation estimate: Znr.time_add_mod_tm_le)
            apply (estimation estimate: Znr.length_subtract_mod[OF length_take_cobounded1 length_take_cobounded1])
            apply (estimation estimate: Znr.length_subtract_mod[OF length_take_cobounded1 length_take_cobounded1])
            apply simp
            done
          done
        also have "... = 112 * (n + 2) + 254" by simp
        finally show ?thesis .
      qed
      done
    also have "... = (255 + 112 * (n + 2)) * 2 ^ (oe_n - 1) + 1"
      unfolding length_\<gamma>s defs' using length_\<gamma>_i by simp
    also have "... \<le> (255 + 112 * (n + 2)) * 2 ^ n + 1 * 2 ^ n"
      apply (intro add_mono mult_le_mono order.refl)
      unfolding oe_n_def by simp_all
    also have "... = (256 + 112 * (n + 2)) * 2 ^ n"
      by (simp add: add_mult_distrib)
    also have "... \<le> (128 * (n + 2) + 112 * (n + 2)) * 2 ^ n"
      apply (intro add_mono mult_le_mono order.refl)
      by simp
    finally have time_\<eta>_le: "time_\<eta> \<le> 240 * (n + 2) * 2 ^ n" by simp

    have oe_n_prim_root_le: "oe_n + prim_root_exponent * y - 1 \<le> fn_carrier_len" if "y \<in> set interval1" for y
    proof -
      have "oe_n + prim_root_exponent * y - 1 \<le> n + prim_root_exponent * y"
        using oe_n_minus_1_le_n by simp
      also have "... \<le> n + prim_root_exponent * 2 ^ (oe_n - 1)"
        using that unfolding interval1_def defs' by simp
      also have "... = n + 2 ^ n"
        unfolding oe_n_def prim_root_exponent_def
        by (cases "odd m"; simp add: n_gt_0 power_Suc[symmetric])
      also have "... \<le> 2 ^ n + 2 ^ n"
        by simp
      also have "... = fn_carrier_len"
        unfolding defs' by simp
      finally show ?thesis .
    qed

    have "time_\<xi>' \<le> ((475 + 378 * Fnr.e) + 2) * length c_diffs + 3"
      unfolding time_\<xi>'_def
      apply (intro time_map2_tm_bounded)
      subgoal unfolding length_c_diffs length_interval1 by (rule refl)
      subgoal premises prems for x y
        unfolding tm_time_simps add.assoc[symmetric] val_times_nat_tm defs[symmetric]
          val_plus_nat_tm val_minus_nat_tm Fmr.val_divide_by_power_of_2_tm
          Fnr.val_from_nat_lsbf_tm
      proof -
        have "time (prim_root_exponent *\<^sub>t y) +
          time (oe_n +\<^sub>t (prim_root_exponent * y)) +
          time ((oe_n + prim_root_exponent * y) -\<^sub>t 1) +
          time (Fmr.divide_by_power_of_2_tm x (oe_n + prim_root_exponent * y - 1)) +
          time (Fnr.from_nat_lsbf_tm oe_n_plus_two_pow_n_one) +
          time
           (Fnr.add_fermat_tm
             (Fmr.divide_by_power_of_2 x (oe_n + prim_root_exponent * y - 1))
             (Fnr.from_nat_lsbf oe_n_plus_two_pow_n_one)) \<le>
          (2 * y + 5) + (oe_n + 1) + 2 + (24 + 26 * fn_carrier_len + 26 * length x) +
          (288 * 1 + 144 + (96 + 192 * 1 + 8 * 1 * 1) * Fnr.e) +
          (13 + 7 * length x + 21 * Fnr.e)" (is "?t \<le> _")
          apply (intro add_mono)
          subgoal unfolding time_times_nat_tm
            apply (estimation estimate: prim_root_exponent_le)
            by simp
          subgoal unfolding time_plus_nat_tm by simp
          subgoal unfolding time_minus_nat_tm by simp
          subgoal apply (estimation estimate: Fmr.time_divide_by_power_of_2_tm_le)
            apply (estimation estimate: oe_n_prim_root_le[OF prems(2)])
            apply (estimation estimate: Nat_max_le_sum)
            by simp
          subgoal
            apply (intro Fnr.time_from_nat_lsbf_tm_le Fnr.e_ge_4 n_gt_0)
            unfolding length_oe_n_plus_two_pow_n_one using oe_n_n_bound_1 by simp
          subgoal
            apply (estimation estimate: Fnr.time_add_fermat_tm_le)
            unfolding Fmr.length_multiply_with_power_of_2 Fnr.length_from_nat_lsbf
            apply (estimation estimate: Nat_max_le_sum)
            by simp
          done
        also have "... = 477 + 2 * y + oe_n + 343 * Fnr.e + 33 * length x"
          unfolding fn_carrier_len_def by simp
        also have "... = 477 + 2 * y + oe_n + 376 * Fnr.e"
          using prems set_subseteqI[OF c_diffs_carrier] length_c_diffs by auto
        also have "... \<le> 477 + 2 * 2 ^ (oe_n - 1) + oe_n + 376 * Fnr.e"
          using prems unfolding interval1_def
          by simp
        also have "... \<le> 477 + oe_n + 377 * Fnr.e"
          unfolding oe_n_def by simp
        also have "... \<le> 475 + 378 * Fnr.e"
          using oe_n_n_bound_1 by simp
        finally show "?t \<le> 475 + 378 * Fnr.e" unfolding defs[symmetric] .
      qed
      done
    also have "... \<le> (475 + 758 * 2 ^ n) * 2 ^ n + 3"
      apply (intro add_mono[of _ _ 3] order.refl mult_le_mono)
      subgoal by simp
      subgoal unfolding length_c_diffs oe_n_def by simp
      done
    also have "... = 3 + 475 * 2 ^ n + 758 * 2 ^ (2 * n)"
      by (simp add: add_mult_distrib power_add mult_2)
    finally have time_\<xi>'_le: "time_\<xi>' \<le> ..." .

    have time_reduce_\<xi>'_nth: "time (Fnr.reduce_tm i) \<le> 155 + 216 * 2 ^ n" if "i \<in> set \<xi>'" for i
    proof -
        have "length i = Fnr.e"
          using iffD1[OF in_set_conv_nth that]
            Fnr.fermat_carrier_length[OF \<xi>'_carrier] length_\<xi>' by auto
        show ?thesis
          by (estimation estimate: Fnr.time_reduce_tm_le)
             (simp add: \<open>length i = Fnr.e\<close>)
    qed

    have "time_\<xi> \<le> ((155 + 216 * 2 ^ n) + 1) * length \<xi>' + 1"
      unfolding time_\<xi>_def
      by (intro time_map_tm_bounded time_reduce_\<xi>'_nth)
    also have "... \<le> (156 + 216 * 2 ^ n) * 2 ^ n + 1"
      unfolding length_\<xi>' oe_n_def by simp
    also have "... = 1 + 156 * 2 ^ n + 216 * 2 ^ (2 * n)"
      by (simp add: add_mult_distrib power_add mult_2)
    finally have time_\<xi>_le: "time_\<xi> \<le> ..." .

    have "time_z \<le> ((245 + 74 * 2 ^ n + 55 * (n + 2) + 2 * (2 ^ n + 2)) + 2) * length \<xi> + 3"
      unfolding time_z_def
      apply (intro time_map2_tm_bounded)
      subgoal unfolding length_\<xi> length_\<eta> by (rule refl)
      subgoal premises prems for x y
        apply (estimation estimate: time_solve_special_residue_problem_tm_le)
        apply (intro add_mono mult_le_mono order.refl)
        subgoal using length_\<eta>_entries length_\<eta> iffD1[OF in_set_conv_nth \<open>y \<in> set \<eta>\<close>] by auto
        subgoal using length_\<xi>_entries[OF \<open>x \<in> set \<xi>\<close>] .
        done
      done
    also have "... = (361 + 76 * 2 ^ n + 55 * n) * 2 ^ (oe_n - 1) + 3"
      unfolding length_\<xi> by simp
    also have "... \<le> (361 + 76 * 2 ^ n + 55 * 2 ^ n) * 2 ^ n + 3"
      apply (intro add_mono order.refl mult_le_mono)
      subgoal using less_exp by simp
      subgoal unfolding oe_n_def by simp
      done
    also have "... = 131 * 2 ^ (2 * n) + 361 * 2 ^ n + 3"
      by (simp add: add_mult_distrib mult_2 power_add)
    finally have time_z_le: "time_z \<le> ..." .

    have "time_z_filled \<le> ((2 * (2 ^ n + n + 4) + 2 ^ (n - 1) + 5) + 1) * length z + 1"
      unfolding time_z_filled_def
      apply (intro time_map_tm_bounded)
      unfolding time_fill_tm segment_lens_def
      using length_z_entries in_set_conv_nth[of _ z] unfolding length_z
      by fastforce
    also have "... \<le> (2 * 2 ^ n + 2 * n + 2 ^ (n - 1) + 14) * 2 ^ n + 1"
      apply (intro add_mono[of _ _ _ 1] mult_le_mono order.refl)
      subgoal by simp
      subgoal unfolding length_z oe_n_def by simp
      done
    also have "... \<le> (5 * 2 ^ n + 14) * 2 ^ n + 1"
      apply (intro add_mono[of _ _ _ 1] mult_le_mono order.refl)
      using less_exp[of n] power_increasing[of "n - 1" n "2::nat"] by linarith
    also have "... = 5 * 2 ^ (2 * n) + 14 * 2 ^ n + 1"
      by (simp add: add_mult_distrib mult_2 power_add)
    finally have time_z_filled_le: "time_z_filled \<le> ..." .

    have "time (map2_tm (schoenhage_strassen_tm n) A.num_dft_odds B.num_dft_odds) \<le>
      (schoenhage_strassen_Fm_bound n + 2) * length A.num_dft_odds + 3"
      apply (intro time_map2_tm_bounded)
      subgoal unfolding A.length_num_dft_odds B.length_num_dft_odds by (rule refl)
      subgoal premises prems for x y
        apply (intro less.IH[OF n_lt_m])
        subgoal using prems A.num_dft_odds_carrier by blast
        subgoal using prems B.num_dft_odds_carrier by blast
        done
      done
    also have "... \<le> schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1) + 2 * 2 ^ n + 3"
      unfolding A.length_num_dft_odds
      using oe_n_minus_1_le_n
      by simp
    finally have recursive_time: "time (map2_tm (schoenhage_strassen_tm n) A.num_dft_odds B.num_dft_odds) \<le>
      ..." .

    have two_pow_pos: "(2::nat) ^ x > 0" for x
      by simp

    have "time (schoenhage_strassen_tm m a b) =
      time (m <\<^sub>t 3) + time (odd_tm m) +
    (if odd m then time (m +\<^sub>t 1) + time ((m + 1) div\<^sub>t 2)
     else time (m +\<^sub>t 2) + time ((m + 2) div\<^sub>t 2)) +
    time (n +\<^sub>t 1) +
    time (n -\<^sub>t 1) +
    time (n +\<^sub>t 2) +
    (if odd m then 0 else 0) +
    time (2 ^\<^sub>t (n - 1)) +
    time (subdivide_tm segment_lens a) +
    time (subdivide_tm segment_lens b) +
    time (map_tm Znr.reduce_tm A.num_blocks) +
    time (3 *\<^sub>t n) +
    time ((3 * n) +\<^sub>t 5) +
    time (map_tm (fill_tm pad_length) A.num_Zn) +
    time (concat_tm (map (fill pad_length) A.num_Zn)) +
    time (map_tm Znr.reduce_tm B.num_blocks) +
    time (map_tm (fill_tm pad_length) B.num_Zn) +
    time (concat_tm (map (fill pad_length) B.num_Zn)) +
    time (oe_n +\<^sub>t 1) +
    time (2 ^\<^sub>t (oe_n + 1)) +
    time (pad_length *\<^sub>t 2 ^ (oe_n + 1)) +
    time (karatsuba_mul_nat_tm A.num_Zn_pad B.num_Zn_pad) +
    time (ensure_length_tm uv_length uv_unpadded) +
    time (oe_n -\<^sub>t 1) +
    time (2 ^\<^sub>t (oe_n - 1)) +
    time (subdivide_tm pad_length uv) +
    time (subdivide_tm (2 ^ (oe_n - 1)) \<gamma>s) +
    time (nth_tm \<gamma> 0) +
    time (nth_tm \<gamma> 1) +
    time (nth_tm \<gamma> 2) +
    time (nth_tm \<gamma> 3) +
    time_\<eta> +
    (if odd m then 0 else 0) +
    time (2 ^\<^sub>t (n + 1)) +
    time (map_tm (fill_tm fn_carrier_len) A.num_blocks) +
    time (map_tm (fill_tm fn_carrier_len) B.num_blocks) +
    time (Fnr.fft_tm prim_root_exponent A.num_blocks_carrier) +
    time (Fnr.fft_tm prim_root_exponent B.num_blocks_carrier) +
    time (evens_odds_tm False A.num_dft) +
    time (evens_odds_tm False B.num_dft) +
    time (map2_tm (schoenhage_strassen_tm n) A.num_dft_odds B.num_dft_odds) +
    time (prim_root_exponent *\<^sub>t 2) +
    time (Fnr.ifft_tm (prim_root_exponent * 2) c_dft_odds) +
    time (2 ^\<^sub>t oe_n) +
    time (upt_tm 0 (2 ^ (oe_n - 1))) +
    time (upt_tm (2 ^ (oe_n - 1)) (2 ^ oe_n)) +
    time (2 ^\<^sub>t n) +
    time (oe_n +\<^sub>t 2 ^ n) +
    time (replicate_tm (oe_n + 2 ^ n) False) +
    time (oe_n_plus_two_pow_n_zeros @\<^sub>t [True]) +
    time_\<xi>' +
    time_\<xi> +
    time_z +
    time (map_tm (fill_tm segment_lens) z) +
    time (replicate_tm (2 ^ (oe_n - 1)) oe_n_plus_two_pow_n_one) +
    time (z_filled @\<^sub>t z_consts) +
    time (combine_z_tm segment_lens z_complete) +
    time (Fmr.from_nat_lsbf_tm z_sum) +
    0 +
    1"
      unfolding schoenhage_strassen_tm.simps[of m a b] tm_time_simps
      unfolding val_simp val_times_nat_tm val_subdivide_tm[OF two_pow_pos] val_subdivide_tm[OF pad_length_gt_0] Znr.val_reduce_tm defs[symmetric]
      Let_def val_nth_\<gamma> val_fft1 val_fft2 val_ifft val_ih Fnr.val_ifft_tm[OF length_c_dft_odds]
      unfolding Eq_FalseI[OF 3] if_False add.assoc[symmetric] time_z_filled_def[symmetric]
      apply (intro arg_cong2[where f = "(+)"] refl)
      unfolding defs''[symmetric] time_\<xi>'_def[symmetric] time_\<eta>_def[symmetric] time_\<xi>_def[symmetric]
        time_z_def[symmetric] time_z_filled_def[symmetric]
      by (intro refl)+
    also have "... \<le> 8 + (8 * m + 14) +
    (28 + 9 * m) +
    (n + 1) +
    2 +
    (n + 1) +
    0 +
    (8 * 2 ^ n + 1) +
    (10 * 2 ^ m + 2 ^ n + 4) +
    (10 * 2 ^ m + 2 ^ n + 4) +
    (((2 ^ n + 2 * n + 12) + 1) * length A.num_blocks + 1) +
    (7 + 3 * n) +
    (6 + 3 * n) +
    (((5 * n + 14) + 1) * length A.num_Zn + 1) +
    (14 * 2 ^ n + 6 * (n * 2 ^ n) + 1) +
    (((2 ^ n + 2 * n + 12) + 1) * length B.num_blocks + 1) +
    (((5 * n + 14) + 1) * length B.num_Zn + 1) +
    (14 * 2 ^ n + 6 * (n * 2 ^ n) + 1) +
    (n + 2) +
    (24 * 2 ^ n + 5 * n + 11) +
    (12 * (n * 2 ^ n) + 20 * 2 ^ n + 6 * n + 11) +
    time (karatsuba_mul_nat_tm A.num_Zn_pad B.num_Zn_pad) +
    (168 * (n * 2 ^ n) + 280 * 2 ^ n + (4 * karatsuba_lower_bound + 19)) +
    2 +
    12 * 2 ^ n +
    (14 + 60 * (n * 2 ^ n) + (100 * 2 ^ n + 6 * n)) +
    (22 * 2 ^ n + 4) +
    (0 + 1) +
    (1 + 1) +
    (2 + 1) +
    (3 + 1) +
    (480 * 2 ^ n + 240 * (n * 2 ^ n)) +
    0 +
    24 * 2 ^ n +
    (((3 * 2 ^ n + 5) + 1) * length A.num_blocks + 1) +
    (((3 * 2 ^ n + 5) + 1) * length B.num_blocks + 1) +
    (2 ^ oe_n * (66 + 87 * Fnr.e) + oe_n * 2 ^ oe_n * (76 + 116 * Fnr.e) +
     8 * prim_root_exponent * 2 ^ (2 * oe_n)) +
    (2 ^ oe_n * (66 + 87 * Fnr.e) + oe_n * 2 ^ oe_n * (76 + 116 * Fnr.e) +
     8 * prim_root_exponent * 2 ^ (2 * oe_n)) +
    (2 * 2 ^ n + 1) +
    (2 * 2 ^ n + 1) +
    (schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1) + 2 * 2 ^ n + 3) +
    9 +
    (2 ^ (oe_n - 1) * (66 + 87 * Fnr.e) +
     (oe_n - 1) * 2 ^ (oe_n - 1) * (76 + 116 * Fnr.e) +
     8 * (prim_root_exponent * 2) * 2 ^ (2 * (oe_n - 1))) +
    24 * 2 ^ n +
    (2 * 2 ^ (2 * n) + 5 * 2 ^ n + 2) +
    (8 * 2 ^ (2 * n) + 10 * 2 ^ n + 2) +
    12 * 2 ^ n +
    (n + 2) +
    (2 ^ n + n + 2) +
    (2 ^ n + n + 2) +
    (3 + 475 * 2 ^ n + 758 * 2 ^ (2 * n)) +
    (1 + 156 * 2 ^ n + 216 * 2 ^ (2 * n)) +
    (131 * 2 ^ (2 * n) + 361 * 2 ^ n + 3) +
    (5 * 2 ^ (2 * n) + 14 * 2 ^ n + 1) +
    (2 ^ n + 1) +
    (2 ^ n + 1) +
    (10 + (3 * segment_lens + 2 * (2 ^ n + n + 4) + 10) * length z_complete) +
    (8208 + 23488 * 2 ^ m) + 0 + 1"
      apply (intro add_mono)
      subgoal unfolding time_less_nat_tm by simp
      subgoal by (rule time_odd_tm_le)
      subgoal
        apply (estimation estimate: if_le_max)
        unfolding time_plus_nat_tm
        apply (estimation estimate: time_divide_nat_tm_le)
        apply (estimation estimate: time_divide_nat_tm_le)
        by simp
      subgoal unfolding time_plus_nat_tm by (rule order.refl)
      subgoal unfolding time_minus_nat_tm by simp
      subgoal unfolding time_plus_nat_tm by (rule order.refl)
      subgoal by simp
      subgoal
        apply (estimation estimate: time_power_nat_tm_le)
        unfolding Suc_diff_1[OF n_gt_0]
        using less_exp[of "n - 1"] power_increasing[of "n - 1" n "2::nat"]
        by linarith
      subgoal
        apply (estimation estimate: time_subdivide_tm_le[OF segment_lens_pos])
        unfolding A.length_num segment_lens_def power_Suc[symmetric]
        Suc_diff_1[OF n_gt_0] by simp
      subgoal
        apply (estimation estimate: time_subdivide_tm_le[OF segment_lens_pos])
        unfolding B.length_num segment_lens_def power_Suc[symmetric]
        Suc_diff_1[OF n_gt_0] by simp
      subgoal
        apply (intro time_map_tm_bounded)
        subgoal premises prems for i
        proof -
          have "time (Znr.reduce_tm i) = 8 + 2 * length i + 2 * n + 4"
            unfolding Znr.time_reduce_tm by simp
          also have "... = 8 + 2 * 2 ^ (n - 1) + 2 * n + 4"
            apply (intro arg_cong2[where f = "(+)"] arg_cong2[where f = "(*)"] refl)
            using A.length_nth_num_blocks iffD1[OF in_set_conv_nth prems]
            unfolding A.length_num_blocks by auto
          also have "... = 2 ^ n + 2 * n + 12"
            unfolding power_Suc[symmetric] Suc_diff_1[OF n_gt_0] by simp
          finally show ?thesis by simp
        qed
        done
      subgoal by (simp del: One_nat_def)
      subgoal by simp
      subgoal apply (intro time_map_tm_bounded)
        subgoal premises prems for i
        proof -
          have "time (fill_tm pad_length i) = 2 * length i + 3 * n + 10"
            unfolding time_fill_tm pad_length_def by simp
          also have "... = 2 * (n + 2) + 3 * n + 10"
            apply (intro arg_cong2[where f = "(+)"] arg_cong2[where f = "(*)"] refl)
            using A.length_nth_num_Zn iffD1[OF in_set_conv_nth prems]
            unfolding A.length_num_Zn by auto
          also have "... = 5 * n + 14"
            by simp
          finally show ?thesis by simp
        qed
        done
      subgoal unfolding time_concat_tm length_map A.num_Zn_pad_def[symmetric] A.length_num_Zn_pad
        unfolding A.length_num_Zn pad_length_def
        apply (estimation estimate: oe_n_le_n)
        by (simp add: add_mult_distrib)
      subgoal
        apply (intro time_map_tm_bounded)
        subgoal premises prems for i
        proof -
          have "time (Znr.reduce_tm i) = 8 + 2 * length i + 2 * n + 4"
            unfolding Znr.time_reduce_tm by simp
          also have "... = 8 + 2 * 2 ^ (n - 1) + 2 * n + 4"
            apply (intro arg_cong2[where f = "(+)"] arg_cong2[where f = "(*)"] refl)
            using B.length_nth_num_blocks iffD1[OF in_set_conv_nth prems]
            unfolding B.length_num_blocks by auto
          also have "... = 2 ^ n + 2 * n + 12"
            unfolding power_Suc[symmetric] Suc_diff_1[OF n_gt_0] by simp
          finally show ?thesis by simp
        qed
        done
      subgoal apply (intro time_map_tm_bounded)
        subgoal premises prems for i
        proof -
          have "time (fill_tm pad_length i) = 2 * length i + 3 * n + 10"
            unfolding time_fill_tm pad_length_def by simp
          also have "... = 2 * (n + 2) + 3 * n + 10"
            apply (intro arg_cong2[where f = "(+)"] arg_cong2[where f = "(*)"] refl)
            using B.length_nth_num_Zn iffD1[OF in_set_conv_nth prems]
            unfolding B.length_num_Zn by auto
          also have "... = 5 * n + 14"
            by simp
          finally show ?thesis by simp
        qed
        done
      subgoal unfolding time_concat_tm length_map B.num_Zn_pad_def[symmetric] B.length_num_Zn_pad
        unfolding B.length_num_Zn pad_length_def
        apply (estimation estimate: oe_n_le_n)
        by (simp add: add_mult_distrib)
      subgoal unfolding oe_n_def by simp
      subgoal
        apply (estimation estimate: time_power_nat_tm_le)
        apply (estimation estimate: oe_n_le_n)
        by simp_all
      subgoal
        unfolding time_times_nat_tm pad_length_def
        unfolding add_mult_distrib add_mult_distrib2
        apply (estimation estimate: oe_n_le_n)
        by simp_all
      subgoal by (rule order.refl)
      subgoal unfolding time_ensure_length_tm
        apply (estimation estimate: length_uv_unpadded_le)
        unfolding uv_length_def pad_length_def
        apply (estimation estimate: oe_n_le_n)
        by (simp_all add: add_mult_distrib)
      subgoal by simp
      subgoal
        apply (estimation estimate: time_power_nat_tm_2_le)
        apply (estimation estimate: oe_n_minus_1_le_n)
        by simp_all
      subgoal
        apply (estimation estimate: time_subdivide_tm_le[OF pad_length_gt_0])
        unfolding uv_length_def length_uv pad_length_def
        apply (estimation estimate: oe_n_le_n)
        by (simp_all add: add_mult_distrib)
      subgoal
        apply (estimation estimate: time_subdivide_tm_le[OF two_pow_pos])
        unfolding length_\<gamma>s'
        apply (estimation estimate: oe_n_minus_1_le_n)
        by simp_all
      subgoal using time_nth_tm[of 0 \<gamma>] sc\<gamma>(1) by simp
      subgoal using time_nth_tm[of 1 \<gamma>] sc\<gamma>(1) by simp
      subgoal using time_nth_tm[of 2 \<gamma>] sc\<gamma>(1) by simp
      subgoal using time_nth_tm[of 3 \<gamma>] sc\<gamma>(1) by simp
      subgoal
        apply (estimation estimate: time_\<eta>_le)
        by (simp add: add_mult_distrib)
      subgoal by simp
      subgoal
        apply (estimation estimate: time_power_nat_tm_2_le)
        by simp
      subgoal apply (intro time_map_tm_bounded)
        unfolding time_fill_tm
        subgoal premises prems for i
        proof -
          have leni: "length i = 2 ^ (n - 1)"
            using iffD1[OF in_set_conv_nth prems]
            unfolding A.length_num_blocks
            using A.length_nth_num_blocks by auto
          show ?thesis unfolding leni power_Suc[symmetric] Suc_diff_1[OF n_gt_0]
          unfolding fn_carrier_len_def
          by simp
      qed
      done
      subgoal apply (intro time_map_tm_bounded)
        unfolding time_fill_tm
        subgoal premises prems for i
        proof -
          have leni: "length i = 2 ^ (n - 1)"
            using iffD1[OF in_set_conv_nth prems]
            unfolding B.length_num_blocks
            using B.length_nth_num_blocks by auto
          show ?thesis unfolding leni power_Suc[symmetric] Suc_diff_1[OF n_gt_0]
          unfolding fn_carrier_len_def
          by simp
      qed
      done
    subgoal apply (intro Fnr.time_fft_tm_le A.length_num_blocks_carrier)
      using A.fill_num_blocks_carrier
      using Fnr.fermat_carrier_length
      unfolding defs[symmetric] by blast
    subgoal apply (intro Fnr.time_fft_tm_le B.length_num_blocks_carrier)
      using B.fill_num_blocks_carrier
      using Fnr.fermat_carrier_length
      unfolding defs[symmetric] by blast
    subgoal
      apply (estimation estimate: time_evens_odds_tm_le)
      unfolding A.length_num_dft
      apply (estimation estimate: oe_n_le_n)
      by simp_all
    subgoal
      apply (estimation estimate: time_evens_odds_tm_le)
      unfolding B.length_num_dft
      apply (estimation estimate: oe_n_le_n)
      by simp_all
    subgoal by (rule recursive_time)
    subgoal using prim_root_exponent_le by simp
    subgoal apply (intro Fnr.time_ifft_tm_le length_c_dft_odds)
      using c_dft_odds_carrier Fnr.fermat_carrier_length by auto
    subgoal
      apply (estimation estimate: time_power_nat_tm_2_le)
      apply (estimation estimate: oe_n_le_n)
      by simp_all
    subgoal apply (estimation estimate: time_upt_tm_le')
      apply (estimation estimate: oe_n_minus_1_le_n)
      by (simp_all only: power_add[symmetric] mult.assoc mult_2[symmetric])
    subgoal apply (estimation estimate: time_upt_tm_le')
      apply (estimation estimate: oe_n_le_n)
      by (simp_all add: power_add[symmetric] mult_2[symmetric])
    subgoal apply (estimation estimate: time_power_nat_tm_2_le)
      by (rule order.refl)
    subgoal using oe_n_le_n by simp
    subgoal unfolding time_replicate_tm
      using oe_n_le_n by simp
    subgoal using oe_n_le_n
      by (simp add: oe_n_plus_two_pow_n_zeros_def)
    subgoal by (rule time_\<xi>'_le)
    subgoal by (rule time_\<xi>_le)
    subgoal by (rule time_z_le)
    subgoal unfolding time_z_filled_def[symmetric] by (rule time_z_filled_le)
    subgoal unfolding time_replicate_tm
      using oe_n_minus_1_le_n by simp
    subgoal using oe_n_minus_1_le_n by (simp add: length_z_filled)
    subgoal apply (intro time_combine_z_tm_le[OF _ segment_lens_pos])
      using length_z_complete_entries .
    subgoal
      apply (estimation estimate: Fmr.time_from_nat_lsbf_tm_le[OF Fmr.e_ge_4, OF m_gt_0 length_z_sum_le])
      by simp
    subgoal by (rule order.refl)
    subgoal by (rule order.refl)
    done
  also have "... \<le> 8410 + 23508 * 2 ^ m + 2069 * 2 ^ n + 1141 * 2 ^ (2 * n) + 29 * n +
    32 * 2 ^ (2 * oe_n) +
    2 * (oe_n * (2 ^ oe_n * (76 + 232 * 2 ^ n))) +
    2 * (2 ^ oe_n * (66 + 174 * 2 ^ n)) +
    2 * (2 ^ oe_n * (6 + 3 * 2 ^ n)) +
    492 * (n * 2 ^ n) +
    2 * (2 ^ oe_n * (15 + 5 * n)) +
    2 * (2 ^ oe_n * (13 + 2 ^ n + 2 * n)) +
    17 * m +
    time (karatsuba_mul_nat_tm A.num_Zn_pad B.num_Zn_pad) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1) +
    2 ^ (oe_n - 1) * (66 + 174 * 2 ^ n) +
    (oe_n - 1) * 2 ^ (oe_n - 1) * (76 + 232 * 2 ^ n) +
    32 * 2 ^ (2 * (oe_n - 1)) +
    (18 + 3 * 2 ^ (n - 1) + 2 * 2 ^ n + 2 * n) * 2 ^ oe_n"
    unfolding A.length_num_blocks A.length_num_Zn B.length_num_blocks B.length_num_Zn
    apply (estimation estimate: prim_root_exponent_le)
    apply (estimation estimate: prim_root_exponent_2_le)
    unfolding segment_lens_def length_z_complete
    by (simp add: add.assoc[symmetric])
  also have "... \<le> 8410 + 23508 * 2 ^ m + 2069 * 2 ^ n + 1141 * 2 ^ (2 * n) + 29 * n +
    128 * 2 ^ (2 * n) +
    2464 * (n * 2 ^ (2 * n)) +
    (264 * 2 ^ n + 696 * 2 ^ (2 * n)) +
    (24 * 2 ^ n + 12 * 2 ^ (2 * n)) +
    492 * (n * 2 ^ n) +
    (60 * 2 ^ n + 20 * (n * 2 ^ n)) +
    (52 * 2 ^ n + 4 * 2 ^ (2 * n) + 8 * (n * 2 ^ n)) +
    17 * m +
    time (karatsuba_mul_nat_tm A.num_Zn_pad B.num_Zn_pad) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1) +
    (66 * 2 ^ n + 174 * 2 ^ (2 * n)) +
    (76 * (n * 2 ^ n) + n * (232 * 2 ^ (2 * n))) +
    32 * 2 ^ (2 * n) +
    (36 * 2 ^ n + 10 * 2 ^ (2 * n) + 4 * (n * 2 ^ n))"
    apply (intro add_mono order.refl)
    subgoal apply (estimation estimate: oe_n_le_n) by simp_all
    subgoal
    proof -
      have "2 * (oe_n * (2 ^ oe_n * (76 + 232 * 2 ^ n))) \<le>
        2 * ((2 * n) * (2 ^ (n + 1) * (76 + 232 * 2 ^ n)))"
        apply (intro add_mono mult_le_mono order.refl)
        subgoal apply (estimation estimate: oe_n_le_n)
          unfolding mult_2 using n_gt_0 by simp
        subgoal by (estimation estimate: oe_n_le_n; simp)
        done
      also have "... = 8 * n * 2 ^ n * (76 + 232 * 2 ^ n)"
        by simp
      also have "... \<le> 8 * n * 2 ^ n * (76 * 2 ^ n + 232 * 2 ^ n)"
        by (intro add_mono mult_le_mono order.refl; simp)
      also have "... = 2464 * (n * 2 ^ (2 * n))"
        by (simp add: mult_2 power_add)
      finally show ?thesis .
    qed
    subgoal apply (estimation estimate: oe_n_le_n)
      by (simp add: add_mult_distrib2 mult_2 power_add)
    subgoal apply (estimation estimate: oe_n_le_n)
      by (simp add: add_mult_distrib2 mult_2 power_add)
    subgoal apply (estimation estimate: oe_n_le_n)
      by (simp add: add_mult_distrib2 mult_2 power_add)
    subgoal apply (estimation estimate: oe_n_le_n)
      by (simp add: add_mult_distrib2 power_add[symmetric])
    subgoal apply (estimation estimate: oe_n_minus_1_le_n)
      by (simp add: add_mult_distrib2 mult_2 power_add)
    subgoal apply (estimation estimate: oe_n_minus_1_le_n)
      by (simp add: add_mult_distrib2 mult_2 power_add)
    subgoal apply (estimation estimate: oe_n_minus_1_le_n)
      by (simp add: add_mult_distrib2 mult_2 power_add)
    subgoal apply (estimation estimate: oe_n_le_n)
      using power_increasing[of "n - 1" n "2::nat"]
      by (simp add: add_mult_distrib2 add_mult_distrib mult_2[of n, symmetric] power_add[symmetric])
    done
  also have "... = 600 * (n * 2 ^ n) + 2197 * 2 ^ (2 * n) + 2571 * 2 ^ n +
    2696 * (n * 2 ^ (2 * n)) +
    8410 +
    23508 * 2 ^ m +
    29 * n +
    17 * m +
    time (karatsuba_mul_nat_tm A.num_Zn_pad B.num_Zn_pad) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
    by (simp add: add.assoc[symmetric])
  also have "... \<le> 600 * (n * 2 ^ n) + 2197 * 2 ^ (2 * n) + 2571 * 2 ^ n +
    2696 * (n * 2 ^ (2 * n)) +
    8410 +
    23508 * 2 ^ m +
    29 * n +
    17 * m +
    time_karatsuba_mul_nat_bound ((3 * n + 5) * 2 ^ oe_n) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
    apply (intro add_mono order.refl time_karatsuba_mul_nat_tm_le)
    unfolding A.length_num_Zn_pad B.length_num_Zn_pad pad_length_def by simp
  also have "... \<le> 600 * (n * 2 ^ (2 * n)) + 2197 * (n * 2 ^ (2 * n)) + 2571 * (n * 2 ^ (2 * n)) +
    2696 * (n * 2 ^ (2 * n)) +
    8410 +
    23508 * 2 ^ m +
    29 * (n * 2 ^ (2 * n)) +
    17 * 2 ^ m +
    time_karatsuba_mul_nat_bound ((3 * n + 5) * 2 ^ oe_n) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
    apply (intro add_mono mult_le_mono order.refl power_increasing)
    subgoal by simp
    subgoal by simp
    subgoal using n_gt_0 by simp
    subgoal using power_increasing[of n "2 * n" "2::nat"] \<open>2 ^ (2 * n) \<le> n * 2 ^ (2 * n)\<close> by linarith
    subgoal by simp
    subgoal by simp
    done
  also have "... = 23525 * 2 ^ m + 8093 * (n * 2 ^ (2 * n)) + 8410 +
    time_karatsuba_mul_nat_bound ((3 * n + 5) * 2 ^ oe_n) +
    4 * karatsuba_lower_bound +
    schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
    by simp
  also have "... = schoenhage_strassen_Fm_bound m"
    unfolding schoenhage_strassen_Fm_bound.simps[of m] Let_def defs[symmetric] using 3 by argo
  finally show ?thesis .
  qed
qed

definition karatsuba_const where
"karatsuba_const = (SOME c. (\<forall>x. x > 0 \<longrightarrow> time_karatsuba_mul_nat_bound x \<le> c * nat (floor (real x powr log 2 3))))"

lemma real_divide_mult_eq:
  assumes "(c :: real) \<noteq> 0"
  shows "a / c * c = a"
  using assms by simp

lemma powr_unbounded:
  assumes "(c :: real) > 0"
  shows "eventually (\<lambda>x. d \<le> x powr c) at_top"
proof (cases "d > 0")
  case True
  define N where "N = d powr (1 / c)"
  have "d \<le> x powr c" if "x \<ge> N" for x
  proof -
    have "d = d powr 1" apply (intro powr_one[symmetric]) using True by simp
    also have "... = (d powr (1 / c)) powr c"
      unfolding powr_powr
      apply (intro arg_cong2[where f = "(powr)"] refl real_divide_mult_eq[symmetric]) using assms by simp
    also have "... = N powr c" unfolding N_def by (rule refl)
    also have "... \<le> x powr c"
      apply (intro powr_mono2)
      subgoal using assms by simp
      subgoal unfolding N_def by (rule powr_ge_pzero)
      subgoal by (rule that)
      done
    finally show ?thesis .
  qed
  then show ?thesis unfolding eventually_at_top_linorder by blast
next
  case False
  then show ?thesis
    apply (intro always_eventually allI)
    subgoal for x using powr_ge_pzero[of x c] by argo
    done
qed

lemma time_kar_le_kar_const:
  assumes "x > 0"
  shows "time_karatsuba_mul_nat_bound x \<le> karatsuba_const * nat (floor (real x powr log 2 3))"
proof -
  have "\<exists>c. (\<forall>x. x \<ge> 1 \<longrightarrow> time_karatsuba_mul_nat_bound x \<le> c * nat (floor (real x powr log 2 3)))"
    apply (intro eventually_early_nat)
    subgoal
      apply (intro bigo_floor)
      subgoal by (rule time_karatsuba_mul_nat_bound_bigo)
      subgoal apply (intro eventually_nat_real[OF powr_unbounded[of "log 2 3" 1]]) by simp
      done
    subgoal premises prems for x
    proof -
      have "real x \<ge> 1" using prems by simp
      then have "real x powr log 2 3 \<ge> 1 powr log 2 3"
        by (intro powr_mono2; simp)
      then have "real x powr log 2 3 \<ge> 1" by simp
      then have "floor (real x powr log 2 3) \<ge> 1" by simp
      then show ?thesis by simp
    qed
    done
  then have "\<forall>x > 0. time_karatsuba_mul_nat_bound x \<le> karatsuba_const * nat \<lfloor>real x powr log 2 3\<rfloor>"
    unfolding karatsuba_const_def
    apply (intro someI_ex[of "\<lambda>c. \<forall>x>0. time_karatsuba_mul_nat_bound x \<le> c * nat \<lfloor>real x powr log 2 3\<rfloor>"])
    by (metis int_one_le_iff_zero_less nat_int nat_mono nat_one_as_int of_nat_0_less_iff)
  then show ?thesis using assms by blast
qed

lemma poly_smallo_exp:
  assumes "c > 1"
  shows "(\<lambda>n. (real n) powr d) \<in> o(\<lambda>n. c powr (real n))"
  by (intro smallo_real_nat_transfer power_smallo_exponential assms)

lemma kar_aux_lem: "(\<lambda>n. real (n * 2 ^ n) powr log 2 3) \<in> O(\<lambda>n. real (2 ^ (2 * n)))"
proof -
  define c where "c = 2 powr (2 / log 2 3 - 1)"
  have "c > 1" unfolding c_def
    apply (intro gr_one_powr)
    subgoal by simp
    subgoal apply simp using less_powr_iff[of 2 3 2] by simp
    done
  have 1: "(log 2 c + 1) * log 2 3 = 2"
  proof -
    have "log 2 c = 2 / log 2 3 - 1"
      unfolding c_def by (intro log_powr_cancel; simp)
    then have "log 2 c + 1 = 2 / log 2 3" by simp
    then have "(log 2 c + 1) * log 2 3 = 2 / log 2 3 * log 2 3" by simp
    also have "... = 2" apply (intro real_divide_mult_eq)
      using zero_less_log_cancel_iff[of 2 3] by linarith
    finally show ?thesis .
  qed
  from poly_smallo_exp[OF \<open>c > 1\<close>, of 1] have "real \<in> o(\<lambda>n. c powr real n)" by simp
  then have "(\<lambda>n. real (n * 2 ^ n)) \<in> o(\<lambda>n. (c powr real n) * real (2 ^ n))"
    by simp
  then have "(\<lambda>n. real (n * 2 ^ n)) \<in> O(\<lambda>n. (c powr real n) * real (2 ^ n))"
    using landau_o.small_imp_big by blast
  then have "(\<lambda>n. real (n * 2 ^ n) powr log 2 3) \<in> O(\<lambda>n. ((c powr real n) * real (2 ^ n)) powr log 2 3)"
    by (intro iffD2[OF bigo_powr_iff]; simp)
  also have "... = O(\<lambda>n. ((c powr real n) * 2 powr (real n)) powr log 2 3)"
    using powr_realpow[of 2] by simp
  also have "... = O(\<lambda>n. (((2 powr log 2 c) powr real n) * 2 powr (real n)) powr log 2 3)"
    using powr_log_cancel[of 2 c] \<open>c > 1\<close> by simp
  also have "... = O(\<lambda>n. 2 powr ((log 2 c * real n + real n) * log 2 3))"
    unfolding powr_powr powr_add[symmetric] by (rule refl)
  also have "... = O(\<lambda>n. 2 powr (real n * (log 2 c + 1) * log 2 3))"
    apply (intro_cong "[cong_tag_1 (\<lambda>f. O(f)), cong_tag_2 (powr), cong_tag_2 (*)]" more: refl ext)
    by argo
  also have "... = O(\<lambda>n. 2 powr (real n * 2))"
    apply (intro_cong "[cong_tag_1 (\<lambda>f. O(f)), cong_tag_2 (powr)]" more: ext refl)
    using 1 by simp
  also have "... = O(\<lambda>n. real (2 ^ (2 * n)))"
    apply (intro_cong "[cong_tag_1 (\<lambda>f. O(f))]" more: ext)
    subgoal for n
      using powr_realpow[of 2 "2 * n", symmetric]
      by (simp add: mult.commute)
    done
  finally show ?thesis .
qed

definition kar_aux_const where "kar_aux_const = (SOME c. \<forall>n \<ge> 1. real (n * 2 ^ n) powr log 2 3 \<le> c * real (2 ^ (2 * n)))"

lemma kar_aux_lem_le:
  assumes "n > 0"
  shows "real (n * 2 ^ n) powr log 2 3 \<le> kar_aux_const * real (2 ^ (2 * n))"
proof -
  have "(\<exists>c. \<forall>n \<ge> 1. real (n * 2 ^ n) powr log 2 3 \<le> c * real (2 ^ (2 * n)))"
    using eventually_early_real[OF kar_aux_lem] by simp
  then have "\<forall>n \<ge> 1. real (n * 2 ^ n) powr log 2 3 \<le> kar_aux_const * real (2 ^ (2 * n))"
    unfolding kar_aux_const_def apply (intro someI_ex[of "\<lambda>c. \<forall>n \<ge> 1. real (n * 2 ^ n) powr log 2 3 \<le> c * real (2 ^ (2 * n))"]) .
  then show ?thesis using assms by simp
qed

lemma kar_aux_const_gt_0: "kar_aux_const > 0"
proof (rule ccontr)
  assume "\<not> kar_aux_const > 0"
  then have "kar_aux_const \<le> 0" by simp
  then show "False" using kar_aux_lem_le[of 1] by simp
qed

definition kar_aux_const_nat where "kar_aux_const_nat = karatsuba_const * nat \<lceil>16 powr log 2 3\<rceil> * nat \<lceil>kar_aux_const\<rceil>"

definition s_const1 where "s_const1 = 55897 + 4 * kar_aux_const_nat"
definition s_const2 where "s_const2 = 8410 + 4 * karatsuba_lower_bound"

function schoenhage_strassen_Fm_bound' :: "nat \<Rightarrow> nat" where
"m < 3 \<Longrightarrow> schoenhage_strassen_Fm_bound' m = 5336"
| "m \<ge> 3 \<Longrightarrow> schoenhage_strassen_Fm_bound' m = s_const1 * (m * 2 ^ m) + s_const2 + schoenhage_strassen_Fm_bound' ((m + 2) div 2) * 2 ^ ((m + 1) div 2)"
  by fastforce+
termination
  by (relation "Wellfounded.measure (\<lambda>m. m)"; simp)

declare schoenhage_strassen_Fm_bound'.simps[simp del]

lemma schoenhage_strassen_Fm_bound_le_schoenhage_strassen_Fm_bound':
  shows "schoenhage_strassen_Fm_bound m \<le> schoenhage_strassen_Fm_bound' m"
proof (induction m rule: less_induct)
  case (less m)
  show ?case
  proof (cases "m < 3")
    case True
    from True have "schoenhage_strassen_Fm_bound m = 5336" unfolding schoenhage_strassen_Fm_bound.simps[of m] by simp
    also have "... = schoenhage_strassen_Fm_bound' m" using schoenhage_strassen_Fm_bound'.simps True by simp
    finally show ?thesis by simp
  next
    case False
    then interpret m_lemmas: m_lemmas m
      by (unfold_locales; simp)
    from False have "m \<ge> 3" by simp

    define n where "n = m_lemmas.n"
    define oe_n where "oe_n = m_lemmas.oe_n"

    have kar_arg_pos: "(3 * n + 5) * 2 ^ oe_n > 0" by simp

    have fm: "schoenhage_strassen_Fm_bound m = 23525 * 2 ^ m + 8093 * (n * 2 ^ (2 * n)) + 8410 +
      time_karatsuba_mul_nat_bound ((3 * n + 5) * 2 ^ oe_n) +
      4 * karatsuba_lower_bound +
      schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)" (is "_ = ?t1 + ?t2 + ?t3 + ?t4 + ?t5 + ?t6")
      unfolding schoenhage_strassen_Fm_bound.simps[of m] n_def oe_n_def using False m_lemmas.n_def m_lemmas.oe_n_def
      by simp
    have "?t4 \<le> karatsuba_const * nat \<lfloor>real ((3 * n + 5) * 2 ^ oe_n) powr log 2 3\<rfloor>"
      by (intro time_kar_le_kar_const[OF kar_arg_pos])
    also have "... \<le> karatsuba_const * nat \<lfloor>real ((8 * n) * 2 ^ (n + 1)) powr log 2 3\<rfloor>"
      apply (intro add_mono order.refl mult_le_mono nat_mono floor_mono powr_mono2 iffD1[OF real_mono] power_increasing)
      using m_lemmas.oe_n_gt_0 m_lemmas.n_gt_0 m_lemmas.oe_n_le_n by (simp_all add: n_def oe_n_def)
    also have "... = karatsuba_const * nat \<lfloor>real (16 * (n * 2 ^ n)) powr log 2 3\<rfloor>"
      by simp
    also have "... = karatsuba_const * nat \<lfloor>(16 powr log 2 3) * ((n * 2 ^ n) powr log 2 3)\<rfloor>"
      unfolding real_multiplicative using powr_mult[of "real 16" "real n * real (2 ^ n)" "log 2 3"]
      by simp
    also have "... \<le> karatsuba_const * nat \<lfloor>(16 powr log 2 3) * (kar_aux_const * real (2 ^ (2 * n)))\<rfloor>"
      apply (intro mult_le_mono order.refl nat_mono floor_mono mult_mono kar_aux_lem_le)
      subgoal using m_lemmas.n_gt_0 unfolding n_def .
      subgoal by simp
      subgoal by simp
      done
    also have "... \<le> karatsuba_const * nat \<lceil>(16 powr log 2 3) * (kar_aux_const * real (2 ^ (2 * n)))\<rceil>"
      by (intro mult_le_mono order.refl nat_mono floor_le_ceiling)
    also have "... \<le> karatsuba_const * (nat (\<lceil>16 powr log 2 3\<rceil> * \<lceil>kar_aux_const * real (2 ^ (2 * n))\<rceil>))"
      using kar_aux_const_gt_0 by (intro mult_le_mono order.refl nat_mono mult_ceiling_le; simp)
    also have "... = karatsuba_const * (nat \<lceil>16 powr log 2 3\<rceil> * nat \<lceil>kar_aux_const * real (2 ^ (2 * n))\<rceil>)"
      apply (intro arg_cong2[where f = "(*)"] refl nat_mult_distrib)
      using powr_ge_pzero[of 16 "log 2 3"] by linarith
    also have "... \<le> karatsuba_const * (nat \<lceil>16 powr log 2 3\<rceil> * nat (\<lceil>kar_aux_const\<rceil> * \<lceil>real (2 ^ (2 * n))\<rceil>))"
      apply (intro mult_le_mono order.refl nat_mono mult_ceiling_le)
      using kar_aux_const_gt_0 by simp_all
    also have "... = karatsuba_const * (nat \<lceil>16 powr log 2 3\<rceil> * (nat \<lceil>kar_aux_const\<rceil> * nat \<lceil>real (2 ^ (2 * n))\<rceil>))"
      apply (intro arg_cong2[where f = "(*)"] refl nat_mult_distrib)
      using kar_aux_const_gt_0 by simp
    also have "... = karatsuba_const * nat \<lceil>16 powr log 2 3\<rceil> * nat \<lceil>kar_aux_const\<rceil> * (2 ^ (2 * n))"
      by simp
    also have "... = kar_aux_const_nat * 2 ^ (2 * n)"
      unfolding kar_aux_const_nat_def[symmetric] by (rule refl)
    also have "... \<le> kar_aux_const_nat * (n * 2 ^ (2 * n))"
      using m_lemmas.n_gt_0 n_def by simp
    finally have t4_le: "?t4 \<le> ..." .
    have "schoenhage_strassen_Fm_bound m \<le> ?t1 + ?t2 + ?t3 + kar_aux_const_nat * (n * 2 ^ (2 * n)) + ?t5 + ?t6"
      unfolding fm
      by (intro add_mono order.refl t4_le)
    also have "... = ?t1 + (8093 + kar_aux_const_nat) * (n * 2 ^ (2 * n)) + 8410 + 4 * karatsuba_lower_bound + schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
      by (simp add: add_mult_distrib)
    also have "... \<le> 23525 * (m * 2 ^ m) + (8093 + kar_aux_const_nat) * (m * (2 * 2 ^ (m + 1))) + 8410 + 4 * karatsuba_lower_bound + schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
      apply (intro add_mono order.refl mult_le_mono)
      subgoal using m_lemmas.m_gt_0 by simp
      subgoal using m_lemmas.n_lt_m n_def by simp
      subgoal using m_lemmas.two_pow_two_n_le n_def by simp
      done
    also have "... = (55897 + 4 * kar_aux_const_nat) * (m * 2 ^ m) + (8410 + 4 * karatsuba_lower_bound) + schoenhage_strassen_Fm_bound n * 2 ^ (oe_n - 1)"
      by (simp add: add_mult_distrib)
    also have "... \<le> (55897 + 4 * kar_aux_const_nat) * (m * 2 ^ m) + (8410 + 4 * karatsuba_lower_bound) + schoenhage_strassen_Fm_bound' n * 2 ^ (oe_n - 1)"
      apply (intro add_mono order.refl mult_le_mono less.IH)
      unfolding n_def using m_lemmas.n_lt_m .
    also have "... = (55897 + 4 * kar_aux_const_nat) * (m * 2 ^ m) + (8410 + 4 * karatsuba_lower_bound) + schoenhage_strassen_Fm_bound' ((m + 2) div 2) * 2 ^ ((m + 1) div 2)"
      apply (intro_cong "[cong_tag_2 (+), cong_tag_2 (*), cong_tag_2 (^), cong_tag_1 schoenhage_strassen_Fm_bound']" more: refl)
      subgoal unfolding n_def m_lemmas.n_def by (cases "odd m"; simp)
      subgoal unfolding oe_n_def m_lemmas.oe_n_def m_lemmas.n_def by (cases "odd m"; simp)
      done
    also have "... = schoenhage_strassen_Fm_bound' m" using schoenhage_strassen_Fm_bound'.simps[of m] False unfolding s_const1_def[symmetric] s_const2_def[symmetric] by simp
    finally show ?thesis .
  qed
qed

definition \<gamma>_0 where "\<gamma>_0 = 2 * s_const1 + s_const2"

lemma schoenhage_strassen_Fm_bound'_oe_rec:
  assumes "n \<ge> 3"
  shows "schoenhage_strassen_Fm_bound' (2 * n - 2) \<le> \<gamma>_0 * n * 2 ^ (2 * n - 2) + schoenhage_strassen_Fm_bound' n * 2 ^ (n - 1)"
  and   "schoenhage_strassen_Fm_bound' (2 * n - 1) \<le> \<gamma>_0 * n * 2 ^ (2 * n - 1) + schoenhage_strassen_Fm_bound' n * 2 ^ n"
proof -
  from assms have r: "2 * n - 2 \<ge> 4" by linarith
  from r have "schoenhage_strassen_Fm_bound' (2 * n - 1) = s_const1 * (2 * n - 1) * 2 ^ (2 * n - 1) + s_const2 + schoenhage_strassen_Fm_bound' n * 2 ^ n"
    using schoenhage_strassen_Fm_bound'.simps[of "2 * n - 1"] by auto
  also have "... \<le> s_const1 * (2 * n) * 2 ^ (2 * n - 1) + s_const2 * (n * 2 ^ (2 * n - 1)) + schoenhage_strassen_Fm_bound' n * 2 ^ n"
    apply (intro add_mono order.refl mult_le_mono)
    subgoal by simp
    subgoal using assms by simp
    done
  also have "... = \<gamma>_0 * n * 2 ^ (2 * n - 1) + schoenhage_strassen_Fm_bound' n * 2 ^ n"
    unfolding \<gamma>_0_def by (simp add: add_mult_distrib)
  finally show "schoenhage_strassen_Fm_bound' (2 * n - 1) \<le> ..." .
  from r have "schoenhage_strassen_Fm_bound' (2 * n - 2) = s_const1 * ((2 * n - 2) * 2 ^ (2 * n - 2)) + s_const2 +
    schoenhage_strassen_Fm_bound' ((2 * n - 2 + 2) div 2) * 2 ^ ((2 * n - 2 + 1) div 2)"
    using schoenhage_strassen_Fm_bound'.simps(2)[of "2 * n - 2"] by fastforce
  also have "... = s_const1 * ((2 * n - 2) * 2 ^ (2 * n - 2)) + s_const2 +
    schoenhage_strassen_Fm_bound' n * 2 ^ (n - 1)"
    apply (intro_cong "[cong_tag_2 (+), cong_tag_2 (*), cong_tag_2 (^), cong_tag_1 schoenhage_strassen_Fm_bound']" more: refl)
    subgoal using r by linarith
    subgoal using r by linarith
    done
  also have "... \<le> s_const1 * ((2 * n) * 2 ^ (2 * n - 2)) + s_const2 * (n * 2 ^ (2 * n - 2)) + schoenhage_strassen_Fm_bound' n * 2 ^ (n - 1)"
    apply (intro add_mono order.refl mult_le_mono)
    subgoal by simp
    subgoal using assms by simp
    done
  also have "... = \<gamma>_0 * n * 2 ^ (2 * n - 2) + schoenhage_strassen_Fm_bound' n * 2 ^ (n - 1)"
    unfolding \<gamma>_0_def by (simp add: add_mult_distrib)
  finally show "schoenhage_strassen_Fm_bound' (2 * n - 2) \<le> ..." .
qed

definition \<gamma> where "\<gamma> = Max {\<gamma>_0, schoenhage_strassen_Fm_bound' 0, schoenhage_strassen_Fm_bound' 1, schoenhage_strassen_Fm_bound' 2, schoenhage_strassen_Fm_bound' 3}"

lemma schoenhage_strassen_Fm_bound'_le_aux1:
  assumes "m \<le> 2 ^ Suc k + 1"
  shows "schoenhage_strassen_Fm_bound' m \<le> \<gamma> * Suc k * 2 ^ (Suc k + m)"
  using assms proof (induction k arbitrary: m rule: less_induct)
  case (less k)
  consider "m \<le> 3" | "m \<ge> 4" by linarith
  then show ?case
  proof cases
    case 1
    then have "m \<in> {0, 1, 2, 3}" by auto
    then have "schoenhage_strassen_Fm_bound' m \<in> {\<gamma>_0, schoenhage_strassen_Fm_bound' 0, schoenhage_strassen_Fm_bound' 1, schoenhage_strassen_Fm_bound' 2, schoenhage_strassen_Fm_bound' 3}" by auto
    then have "schoenhage_strassen_Fm_bound' m \<le> \<gamma>" unfolding \<gamma>_def by (intro Max.coboundedI; simp)
    also have "... = \<gamma> * 1 * 1" by simp
    also have "... \<le> \<gamma> * Suc k * 2 ^ (Suc k + m)"
      by (intro mult_le_mono order.refl; simp)
    finally show ?thesis .
  next
    case 2
    have "k > 0"
    proof (rule ccontr)
      assume "\<not> k > 0"
      with less.prems have "m \<le> 3" by simp
      thus False using 2 by simp
    qed
    then obtain k' where "k = Suc k'" "k' < k"
      using gr0_conv_Suc by auto
    have ih': "schoenhage_strassen_Fm_bound' m \<le> \<gamma> * k * 2 ^ (k + m)" if "m \<le> 2 ^ k + 1" for m
      using less.IH[OF \<open>k' < k\<close>] unfolding \<open>k = Suc k'\<close>[symmetric] using that by simp

    interpret ml: m_lemmas m
      apply unfold_locales
      using 2 by simp

    define n' where "n' = (if odd m then ml.n else ml.n - 1)"
    have "n' = ml.oe_n - 1"
      unfolding n'_def ml.oe_n_def by simp
    have "ml.n + n' = m + 1"
      unfolding ml.m1 \<open>n' = ml.oe_n - 1\<close>
      using Nat.add_diff_assoc[of 1 ml.oe_n ml.n]
      using Nat.diff_add_assoc2[of 1 ml.n ml.oe_n]
      using ml.oe_n_gt_0 ml.n_gt_0
      by simp

    have "ml.n \<ge> 3" using 2 ml.mn by (cases "odd m"; simp)
    have "ml.n \<le> 2 ^ k + 1"
      using less.prems ml.mn by (cases "odd m"; simp)
    note ih = ih'[OF this]

    have "schoenhage_strassen_Fm_bound' m \<le> \<gamma>_0 * ml.n * 2 ^ m + schoenhage_strassen_Fm_bound' ml.n * 2 ^ n'"
      unfolding n'_def
      using schoenhage_strassen_Fm_bound'_oe_rec[OF \<open>ml.n \<ge> 3\<close>] ml.mn
      by (cases "odd m"; algebra)
    also have "... \<le> \<gamma> * ml.n * 2 ^ m + (\<gamma> * k * 2 ^ (k + ml.n)) * 2 ^ n'"
      apply (intro add_mono mult_le_mono order.refl ih)
      apply (unfold \<gamma>_def)
      apply simp
      done
    also have "... = \<gamma> * ml.n * 2 ^ m + \<gamma> * k * 2 ^ (k + ml.n + n')"
      by (simp add: power_add)
    also have "... = \<gamma> * ml.n * 2 ^ m + \<gamma> * k * 2 ^ (k + m + 1)"
      using \<open>ml.n + n' = m + 1\<close> by (simp add: add.assoc)
    also have "... = \<gamma> * 2 ^ m * (ml.n + k * 2 ^ (k + 1))"
      by (simp add: Nat.add_mult_distrib2 power_add)
    also have "... \<le> \<gamma> * 2 ^ m * (2 ^ (k + 1) + k * 2 ^ (k + 1))"
      apply (intro mono_intros)
      apply (estimation estimate: \<open>ml.n \<le> 2 ^ k + 1\<close>)
      apply simp
      done
    also have "... = \<gamma> * 2 ^ m * (k + 1) * 2 ^ (k + 1)"
      by (simp add: Nat.add_mult_distrib2 Nat.add_mult_distrib)
    also have "... = \<gamma> * (k + 1) * 2 ^ (k + 1 + m)"
      by (simp add: power_add Nat.add_mult_distrib)
    finally show ?thesis by simp
  qed
qed

lemma schoenhage_strassen_Fm_bound'_le_aux2:
  assumes "k \<ge> 1"
  assumes "m \<le> 2 ^ k + 1"
  shows "schoenhage_strassen_Fm_bound' m \<le> \<gamma> * k * 2 ^ (k + m)"
proof -
  from assms(1) obtain k' where "k = Suc k'"
    by (metis Suc_le_D numeral_nat(7))
  then show ?thesis using schoenhage_strassen_Fm_bound'_le_aux1[of m k'] assms(2) by argo
qed

subsection "Multiplication in $\\mathbb{N}$"

definition schoenhage_strassen_mul_tm where
"schoenhage_strassen_mul_tm a b =1 do {
  bits_a \<leftarrow> length_tm a \<bind> bitsize_tm;
  bits_b \<leftarrow> length_tm b \<bind> bitsize_tm;
  m' \<leftarrow> max_nat_tm bits_a bits_b;
  m \<leftarrow> m' +\<^sub>t 1;
  m_plus_1 \<leftarrow> m +\<^sub>t 1;
  car_len \<leftarrow> 2 ^\<^sub>t m_plus_1;
  fill_a \<leftarrow> fill_tm car_len a;
  fill_b \<leftarrow> fill_tm car_len b;
  fm_result \<leftarrow> schoenhage_strassen_tm m fill_a fill_b;
  int_lsbf_fermat.reduce_tm m fm_result
}"

lemma val_schoenhage_strassen_mul_tm[simp, val_simp]:
  "val (schoenhage_strassen_mul_tm a b) = schoenhage_strassen_mul a b"
proof -
  interpret schoenhage_strassen_mul_context a b .

  have val_fm[val_simp]: "val (schoenhage_strassen_tm m fill_a fill_b) = schoenhage_strassen m fill_a fill_b"
    apply (intro val_schoenhage_strassen_tm)
    subgoal unfolding fill_a_def car_len_def
      by (intro int_lsbf_fermat.fermat_non_unique_carrierI length_fill length_a')
    subgoal unfolding fill_b_def car_len_def
      by (intro int_lsbf_fermat.fermat_non_unique_carrierI length_fill length_b')
    done

  show ?thesis
  unfolding schoenhage_strassen_mul_tm_def schoenhage_strassen_mul_def
  unfolding val_simp Let_def int_lsbf_fermat.val_reduce_tm defs[symmetric]
  by (rule refl)
qed

lemma real_power: "a > 0 \<Longrightarrow> real ((a :: nat) ^ x) = real a powr real x"
  using powr_realpow[of "real a" x] by simp

definition schoenhage_strassen_bound where
"schoenhage_strassen_bound n = 146 * n + 218 + 4 * (bitsize n + 1) + 126 * 2 ^ (bitsize n + 2) +
    \<gamma> * bitsize (bitsize n + 1) * 2 ^ (bitsize (bitsize n + 1) + (bitsize n + 1))"

theorem time_schoenhage_strassen_mul_tm_le:
  assumes "length a \<le> n" "length b \<le> n"
  shows "time (schoenhage_strassen_mul_tm a b) \<le> schoenhage_strassen_bound n"
proof -
  interpret schoenhage_strassen_mul_context a b .

  have m_le: "m \<le> bitsize n + 1"
    unfolding defs
    by (intro add_mono order.refl max.boundedI bitsize_mono assms)

  have m_gt_0: "m > 0" unfolding m_def by simp

  have bits_a_le: "bits_a \<le> m - 1"
    unfolding bits_a_def 
    by (intro iffD2[OF bitsize_length] length_a)
  have bits_b_le: "bits_b \<le> m - 1"
    unfolding bits_b_def
    by (intro iffD2[OF bitsize_length] length_b)

  have a_carrier: "fill_a \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
    unfolding fill_a_def car_len_def
    by (intro int_lsbf_fermat.fermat_non_unique_carrierI length_fill length_a')
  have b_carrier: "fill_b \<in> int_lsbf_fermat.fermat_non_unique_carrier m"
    unfolding fill_b_def car_len_def
      by (intro int_lsbf_fermat.fermat_non_unique_carrierI length_fill length_b')

  have val_fm: "val (schoenhage_strassen_tm m fill_a fill_b) = schoenhage_strassen m fill_a fill_b"
    by (intro val_schoenhage_strassen_tm a_carrier b_carrier)

  have "time (schoenhage_strassen_mul_tm a b) = time (length_tm a) + time (bitsize_tm (length a)) + time (length_tm b) +
    time (bitsize_tm (length b)) +
    time (max_nat_tm bits_a bits_b) +
    time (m' +\<^sub>t 1) +
    time (m +\<^sub>t 1) +
    time (2 ^\<^sub>t (m + 1)) +
    time (fill_tm car_len a) +
    time (fill_tm car_len b) +
    time (schoenhage_strassen_tm m fill_a fill_b) +
    time (int_lsbf_fermat.reduce_tm m (schoenhage_strassen m fill_a fill_b)) +
    1"
    unfolding schoenhage_strassen_mul_tm_def
    unfolding tm_time_simps defs[symmetric] val_length_tm val_bitsize_tm val_simps
      val_max_nat_tm Let_def val_plus_nat_tm val_power_nat_tm val_fill_tm val_fm add.assoc[symmetric]
    by (rule refl)
  also have "... \<le> (n + 1) + (72 * n + 23) + (n + 1) +
    (72 * n + 23) +
    (2 * (m - 1) + 3) +
    m +
    (m + 1) +
    12 * 2 ^ (m + 1) +
    (3 * 2 ^ (m + 1) + 5) +
    (3 * 2 ^ (m + 1) + 5) +
    schoenhage_strassen_Fm_bound' m +
    (155 + 108 * 2 ^ (m + 1)) + 1"
    apply (intro add_mono order.refl)
    subgoal using assms by simp
    subgoal apply (estimation estimate: time_bitsize_tm_le) using assms by simp
    subgoal using assms by simp
    subgoal apply (estimation estimate: time_bitsize_tm_le) using assms by simp
    subgoal apply (estimation estimate: time_max_nat_tm_le)
      apply (estimation estimate: min.cobounded1)
      apply (estimation estimate: bits_a_le)
      by (rule order.refl)
    subgoal by (simp add: m_def)
    subgoal by simp
    subgoal apply (estimation estimate: time_power_nat_tm_2_le)
      unfolding defs[symmetric] by (rule order.refl)
    subgoal apply (estimation estimate: time_fill_tm_le)
      apply (estimation estimate: length_a')
      unfolding defs[symmetric] by simp
    subgoal apply (estimation estimate: time_fill_tm_le)
      apply (estimation estimate: length_b')
      unfolding defs[symmetric] by simp
    subgoal
      apply (estimation estimate: time_schoenhage_strassen_tm_le[OF a_carrier b_carrier])
      apply (estimation estimate: schoenhage_strassen_Fm_bound_le_schoenhage_strassen_Fm_bound')
      by (rule order.refl)
    subgoal
      apply (estimation estimate: int_lsbf_fermat.time_reduce_tm_le)
      unfolding int_lsbf_fermat.fermat_carrier_length[OF conjunct2[OF schoenhage_strassen_correct'[OF a_carrier b_carrier]]]
      by simp
    done
  also have "... = 146 * n + 218 +
    2 * (m - 1) + 2 * m + 126 * 2 ^ (m + 1) + schoenhage_strassen_Fm_bound' m"
    by simp
  also have "... \<le> 146 * n + 218 +
    4 * m + 126 * 2 ^ (m + 1) + schoenhage_strassen_Fm_bound' m"
    by simp
  also have "... \<le> 146 * n + 218 + 
    4 * m + 126 * 2 ^ (m + 1) + (\<gamma> * bitsize m * 2 ^ (bitsize m + m))"
    apply (intro add_mono order.refl schoenhage_strassen_Fm_bound'_le_aux2)
    subgoal using bitsize_zero_iff[of m] iffD2[OF neq0_conv m_gt_0] by simp
    subgoal using iffD1[OF bitsize_length order.refl[of "bitsize m"]]
      by simp
    done
  also have "... \<le> 146 * n + 218 + 4 * (bitsize n + 1) + 126 * 2 ^ (bitsize n + 2) +
    \<gamma> * bitsize (bitsize n + 1) * 2 ^ (bitsize (bitsize n + 1) + (bitsize n + 1))"
    apply (estimation estimate: m_le)
    by (intro bitsize_mono m_le order.refl)+ simp
  finally show ?thesis unfolding schoenhage_strassen_bound_def[symmetric] .
qed

lemma real_diff: "a \<le> b \<Longrightarrow> real (b - a) = real b - real a"
  by simp

lemma bitsize_le_log: "n > 0 \<Longrightarrow> real (bitsize n) \<le> log 2 (real n) + 1"
proof -
  assume "n > 0"
  then have "bitsize n > 0" using bitsize_zero_iff[of n] by simp
  then have "\<not> (bitsize n \<le> bitsize n - 1)" by simp
  then have "n \<ge> 2 ^ (bitsize n - 1)" using bitsize_length[of n "bitsize n - 1"] by simp
  then have "log 2 (real n) \<ge> real (bitsize n - 1)"
    using le_log2_of_power by simp
  then show ?thesis by simp
qed

lemma powr_mono_base2: "a \<le> b \<Longrightarrow> 2 powr (a :: real) \<le> 2 powr b"
  by (intro powr_mono; simp)

lemma log_mono_base2: "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a \<le> b \<Longrightarrow> log 2 a \<le> log 2 b"
  using log_le_cancel_iff[of 2 a b] by simp

lemma log_nonneg_base2: "x \<ge> 1 \<Longrightarrow> log 2 x \<ge> 0"
  using zero_le_log_cancel_iff[of 2 x] by simp

lemma powr_log_cancel_base2: "x > 0 \<Longrightarrow> 2 powr (log 2 x) = x"
  by (intro powr_log_cancel; simp)

lemma const_bigo_log: "1 \<in> O(log 2)"
proof -
  have 0: "log 2 x \<ge> 1" if "x \<ge> 2" for x
    using log_mono_base2[of 2 x] that by simp
  show ?thesis apply (intro landau_o.bigI[where c = 1])
    subgoal by simp
    subgoal unfolding eventually_at_top_linorder using 0 by fastforce
    done
qed

lemma const_bigo_log_log: "1 \<in> O(\<lambda>x. log 2 (log 2 x))"
proof -
  have "log 2 4 = 2"
    by (metis log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power2_eq_square)
  then have 0: "log 2 x \<ge> 2" if "x \<ge> 4" for x
    using log_mono_base2[of 4 x] that by simp
  have 1: "log 2 (log 2 x) \<ge> 1" if "x \<ge> 4" for x
    using log_mono_base2[of 2 "log 2 x"] that 0[OF that] by simp
  show ?thesis apply (intro landau_o.bigI[where c = 1])
    subgoal by simp
    subgoal unfolding eventually_at_top_linorder using 1 by fastforce
    done
qed

theorem schoenhage_strassen_bound_bigo: "schoenhage_strassen_bound \<in> O(\<lambda>n. n * log 2 n * log 2 (log 2 n))"
proof -

  define explicit_bound where "explicit_bound = (\<lambda>x. 1154 * x + 226 + 4 * log 2 x + (real \<gamma> * 24) * x * log 2 x * log 2 (log 2 x) + (real \<gamma> * 24 * (1 + log 2 3)) * x * log 2 x)"

  have le: "real (schoenhage_strassen_bound n) \<le> explicit_bound (real n)" if "n \<ge> 2" for n
  proof -
    have "(2::nat) > 0" by simp
    from that have "n \<ge> 1" "n > 0" by simp_all
  
    have 0: "bitsize n + 1 > 0" by simp
    define x where "x = real n"
    then have "x \<ge> 2" "x \<ge> 1" "x > 0" using \<open>n \<ge> 2\<close> \<open>n \<ge> 1\<close> \<open>n > 0\<close> by simp_all
  
    have log_ge: "log 2 x \<ge> 1" using log_mono_base2[of 2 x] using \<open>x \<ge> 2\<close> by simp
    then have log_log_ge: "log 2 (log 2 x) \<ge> 0" and "log 2 x > 0" by simp_all
  
    have log_n: "real (bitsize n) \<le> log 2 x + 1"
      unfolding x_def by (rule bitsize_le_log[OF \<open>n > 0\<close>])
  
    have log_log_n: "real (bitsize (bitsize n + 1)) \<le> log 2 (log 2 x) + (1 + log 2 3)"
    proof -
      have "real (bitsize (bitsize n + 1)) \<le> log 2 (real (bitsize n + 1)) + 1"
        apply (intro bitsize_le_log) by simp
      also have "... = log 2 (real (bitsize n) + 1) + 1"
        unfolding real_linear by simp
      also have "... \<le> log 2 (log 2 (real n) + 1 + 1) + 1"
        apply (intro add_mono order.refl log_mono_base2 bitsize_le_log \<open>n > 0\<close>)
        subgoal by simp
        subgoal using log_nonneg_base2[of "real n"] \<open>n \<ge> 1\<close> by linarith
        done
      also have "... = log 2 (log 2 x + 2 * 1) + 1" unfolding x_def by argo
      also have "... \<le> log 2 (log 2 x + 2 * log 2 x) + 1"
        apply (intro add_mono order.refl log_mono_base2 mult_mono)
        using log_ge by simp_all
      also have "... = log 2 (3 * log 2 x) + 1" by simp
      also have "... = (log 2 3 + log 2 (log 2 x)) + 1"
        apply (intro arg_cong2[where f = "(+)"] refl log_mult_pos)
        using log_ge by simp_all
      also have "... = log 2 (log 2 x) + (1 + log 2 3)" by simp
      finally show ?thesis .
    qed
  
    have 1: "0 \<le> log 2 (log 2 x) + (1 + log 2 3)"
      using log_log_ge by simp
  
    have "real (schoenhage_strassen_bound n) = 146 * x + 218 + 4 * (real (bitsize n) + 1) + 126 * 2 powr (real (bitsize n) + 2) +
      real \<gamma> * real (bitsize (bitsize n + 1)) * 2 powr (real (bitsize (bitsize n + 1)) + (real (bitsize n) + 1))"
      unfolding schoenhage_strassen_bound_def real_linear real_multiplicative x_def real_power[OF \<open>2 > 0\<close>]
      by (intro_cong "[cong_tag_2 (+), cong_tag_2 (*), cong_tag_2 (powr)]" more: refl; simp)
    also have "... \<le> 146 * x + 218 + 4 * ((log 2 x + 1) + 1) + 126 * 2 powr ((log 2 x + 1) + 2) +
      real \<gamma> * (log 2 (log 2 x) + (1 + log 2 3)) * 2 powr ((log 2 (log 2 x) + (1 + log 2 3)) + ((log 2 x + 1) + 1))"
      apply (intro add_mono mult_mono order.refl powr_mono_base2 log_n log_log_n mult_nonneg_nonneg 1)
      unfolding x_def by simp_all
    also have "... = 1154 * x + (226 + 4 * log 2 x) + real \<gamma> * (log 2 (log 2 x) + (1 + log 2 3)) * (24 * (log 2 x * x))"
      unfolding powr_add powr_log_cancel_base2[OF \<open>x > 0\<close>] powr_log_cancel_base2[OF \<open>log 2 x > 0\<close>] by simp
    also have "... = 1154 * x + 226 + 4 * log 2 x + (real \<gamma> * 24) * x * log 2 x * log 2 (log 2 x) + (real \<gamma> * 24 * (1 + log 2 3)) * x * log 2 x"
      unfolding distrib_left distrib_right add.assoc[symmetric] mult.assoc[symmetric] by simp
    also have "... = explicit_bound x"
      unfolding explicit_bound_def by (rule refl)
    finally show ?thesis unfolding x_def .
  qed

  have le_bigo: "schoenhage_strassen_bound \<in> O(explicit_bound)"
    apply (intro landau_o.bigI[where c = 1])
    subgoal by simp
    subgoal unfolding eventually_at_top_linorder using le by fastforce
    done

  have bigo: "explicit_bound \<in> O(\<lambda>n. n * log 2 n * log 2 (log 2 n))"
    unfolding explicit_bound_def
    apply (intro sum_in_bigo(1))
    subgoal 
    proof -
      have "(*) 1154 \<in> O(\<lambda>x. x)" by simp
      moreover have "1 \<in> O(\<lambda>x. log 2 x)" by (rule const_bigo_log)
      moreover have "1 \<in> O(\<lambda>x. log 2 (log 2 x))" by (rule const_bigo_log_log)
      ultimately show ?thesis using landau_o.big_mult[of 1 _ _ 1] by auto
    qed
    subgoal
    proof -
      have a: "(\<lambda>x. 225) \<in> O(\<lambda>x. x :: real)" by simp
      have b: "1 \<in> O(\<lambda>x. log 2 x)" by (rule const_bigo_log)
      have c: "(\<lambda>x. 225) \<in> O(\<lambda>x. x * log 2 x)"
        using landau_o.big_mult[OF a b] by simp
      have d: "1 \<in> O(\<lambda>x. log 2 (log 2 x))" by (rule const_bigo_log_log)
      show ?thesis using landau_o.big_mult[OF c d] by simp
    qed
    subgoal
    proof -
      have a: "(\<lambda>x. 4) \<in> O(\<lambda>x. x :: real)" by simp
      have b: "(\<lambda>x. 4 * log 2 x) \<in> O(\<lambda>x. x * log 2 x)"
        by (rule landau_o.big.mult_right[OF a])
      have c: "1 \<in> O(\<lambda>x. log 2 (log 2 x))" by (rule const_bigo_log_log)
      show ?thesis using landau_o.big_mult[OF b c] by simp
    qed
    subgoal
    proof -
      have a: "(\<lambda>x. real \<gamma> * 24 * x) \<in> O(\<lambda>x. x :: real)" by simp
      show ?thesis by (intro landau_o.big.mult_right a)
    qed
    subgoal
    proof -
      have a: "(\<lambda>x. real \<gamma> * 24 * (1 + log 2 3) * x) \<in> O(\<lambda>x. x :: real)" by simp
      have b: "(\<lambda>x. real \<gamma> * 24 * (1 + log 2 3) * x * log 2 x) \<in> O(\<lambda>x. x * log 2 x)"
        by (intro landau_o.big.mult_right a)
      show ?thesis using landau_o.big_mult[OF b const_bigo_log_log] by simp
    qed
    done

  show ?thesis using bigo landau_o.big_trans[OF le_bigo] by blast
qed
end