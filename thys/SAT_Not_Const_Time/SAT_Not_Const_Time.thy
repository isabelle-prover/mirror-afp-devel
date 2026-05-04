theory SAT_Not_Const_Time
  imports
    Main
    "Cook_Levin.Reduction_TM"
begin

section \<open>Constant-Time Lower Bounds\<close>

text \<open>
  This theory establishes that the Boolean Satisfiability Problem (SAT) cannot be 
  decided by a deterministic Turing machine in constant time ($O(1)$). 
  
  The core of the argument rests on an indistinguishability invariant: a Turing 
  machine bounded by constant time $C$ can only ever read the first $C+1$ cells 
  of its input tape. Consequently, any language decided in constant time must be a 
  prefix language. We then show that SAT is not uniquely determined by any finite 
  prefix, yielding the impossibility result.

  Configuration records and the step function are inherited from the 
  Cook-Levin formalization \cite{Cook_Levin-AFP}.
\<close>

subsection \<open>Head-Movement Bounds for Turing Machines\<close>

text \<open>
  We first establish that a Turing machine's head can move at most one cell 
  per execution step. Configuration records and the step function are inherited 
  from \<open>Reduction_TM\<close>. We isolate the position of the input-tape head (tape 0).
\<close>

definition hd_span :: "config \<Rightarrow> nat" where
  "hd_span cfg \<equiv> cfg <#> 0"

lemma le_imp_le_Suc: "n \<le> m \<Longrightarrow> n \<le> Suc m"
  by simp

lemma contents_nil [simp]:
  "\<lfloor>[]\<rfloor> = (\<lambda>i::nat. if i = 0 then 1 else 0)"
  unfolding contents_def
  by auto

lemma start_config_tape1 [simp]:
  assumes "2 \<le> k"
  shows   "(start_config k xs <:> 1) = \<lfloor>[]\<rfloor>"
proof -
  obtain k' where k': "k = Suc (Suc k')"
    using assms nat_le_iff_add by auto
  show ?thesis
    unfolding start_config_def k'
    by simp
qed

lemma start_config_string_tape1[simp]:
  assumes "2 \<le> k"
  shows   "snd (start_config_string k w) ::: 1 = \<lfloor>[]\<rfloor>"
  using assms start_config_tape1 by auto

lemma config_tape_snd[simp]:
  "(snd cfg ::: j) = (cfg <:> j)"
  by (cases cfg) simp

lemma fst_start_config_string [simp]:
  "fst (start_config_string k w) = 0"
  unfolding start_config_def by simp

lemma act_move_bound:
  fixes tp tp' :: tape and a :: action
  assumes "tp' = act a tp"
  shows   "hd_span (q, [tp'] @ tps) \<le> Suc (hd_span (q, [tp] @ tps))"
  unfolding hd_span_def assms by (cases a) (auto split: direction.split)

lemma nth_map2:
  assumes "length xs = length ys"  "i < length xs"
  shows   "(map2 f xs ys) ! i = f (xs ! i) (ys ! i)"
  using assms
  by (induction xs ys rule: list_induct2) (auto simp add: nth_Cons')

lemma map2_act_nth0:
  assumes "length as = length ts"  "ts \<noteq> []"
  shows   "map2 act as ts ! 0 = act (as ! 0) (ts ! 0)"
  using nth_map2[of as ts 0 act] assms by simp

lemma map2_act_nth0_rewrite:
  assumes "as \<noteq> []"  "ts \<noteq> []"
  shows   "map2 act as ts ! 0 = act (as ! 0) (ts ! 0)"
  using assms(1,2) by force

lemma tapes_pos_by_no_unfold [simp]:
  "(tps :: tape list) :#: j = snd (tps ! j)"
  by simp

text \<open>The head position on the input tape is bounded by the number of steps taken.\<close>

lemma sem_head_move_bound:
  fixes cmd :: command and cfg cfg' :: config
  assumes pc  : "proper_command ||cfg|| cmd"
      and step: "cfg' = sem cmd cfg"
  shows   "hd_span cfg' \<le> Suc (hd_span cfg)"
proof -
  obtain q tps where cfg: "cfg = (q, tps)" by (cases cfg) auto
  then have len_cfg: "||cfg|| = length tps" by simp

  have len_read: "length (config_read cfg) = ||cfg||"
    using cfg read_length len_cfg by simp

  obtain st acts where sas: "cmd (config_read cfg) = (st, acts)"
    by (cases "cmd (config_read cfg)") blast
  from step cfg sas have cfg':
    "cfg' = (st, map (\<lambda>(a,tp). act a tp) (zip acts tps))"
    by (simp add: sem_def)

  have acts_len: "length acts = length tps"
    using proper_command_length[OF pc len_read] sas len_cfg
    using len_read by fastforce

  show ?thesis
  proof (cases tps)
    case Nil
    with cfg cfg' show ?thesis
      by (metis Suc_n_not_le_n hd_span_def linorder_le_cases
          list.map_disc_iff snd_eqD zip_eq_Nil_iff)
  next
    case (Cons tp tps')
    then obtain a as where acts: "acts = a # as"
      by (metis Suc_length_conv acts_len)

    define tps0 where "tps0 \<equiv> tp # tps'"

    from cfg' Cons acts tps0_def have cfg'1:
      "cfg' = (st, map2 act (a # as) tps0)" by simp

    have hd_new: "hd_span cfg' = snd (act a tp)"
      unfolding cfg'1 hd_span_def
      using Cons map2_act_nth0_rewrite[of "a # as" tps0] by (simp add:tps0_def)

    have hd_old: "hd_span cfg = snd tp"
      unfolding cfg hd_span_def Cons by simp

    have "hd_span (st, (act a tp) # tps') \<le> Suc (hd_span (st, tp # tps'))"
      using act_move_bound by auto
    then have "snd (act a tp) \<le> Suc (snd tp)"
      by (simp add: hd_span_def)

    with hd_new hd_old show ?thesis by simp
  qed
qed

lemma exe_head_move_bound:
  fixes cfg cfg' :: config
  assumes pm  : "proper_machine ||cfg|| M"
      and step: "cfg' = exe M cfg"
  shows   "hd_span cfg' \<le> Suc (hd_span cfg)"
proof -
  obtain q tps where cfg [simp]: "cfg = (q,tps)" by (cases cfg)
  show ?thesis
  proof (cases "q < length M")
    case False
    hence "cfg' = cfg" using step exe_def by simp
    thus ?thesis by simp
  next
    case True
    define cmd where "cmd = M ! q"
    from step True cmd_def have cfg': "cfg' = sem cmd cfg"
      by (simp add: exe_def)
    have proper_cmd: "proper_command ||cfg|| cmd"
      using pm True cmd_def by simp
    from sem_head_move_bound[OF proper_cmd cfg'] show ?thesis .
  qed
qed

lemma execute_head_pos_le_time:
  fixes M :: machine and cfg cfg' :: config
  assumes pm  : "proper_machine ||cfg|| M"
      and step: "cfg' = execute M cfg t"
  shows   "hd_span cfg' \<le> hd_span cfg + t"
using step pm
proof (induction t arbitrary: cfg cfg')
  case 0
  then show ?case by simp
next
  case (Suc t cfg cfg')
  define cfg1 where "cfg1 = execute M cfg t"
  have IH: "hd_span cfg1 \<le> hd_span cfg + t"
    using Suc.IH Suc.prems cfg1_def by simp

  have step1: "cfg' = exe M cfg1"
    by (simp add: Suc.prems(1) cfg1_def)

  have tapes_eq: "||cfg1|| = ||cfg||"
    using Suc.prems(2) cfg1_def execute_num_tapes_proper by auto
  have pm1: "proper_machine ||cfg1|| M"
    by (simp add: Suc.prems(2) tapes_eq)

  have "hd_span cfg' \<le> Suc (hd_span cfg1)"
    using exe_head_move_bound[OF pm1 step1] .
  also have "\<dots> \<le> Suc (hd_span cfg + t)"
    using IH by simp
  finally show ?case by simp
qed


subsection \<open>Configuration Indistinguishability\<close>

text \<open>
  Two machine configurations are completely indistinguishable to the execution 
  semantics for at least one step if their control states match, their non-input 
  tapes are identical, and their input tapes agree up to the strict bounds 
  of where the read head can currently be located.
\<close>

definition indist :: "nat \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
  "indist C cfg1 cfg2 \<equiv>
     ||cfg1|| = ||cfg2|| \<and>
     fst cfg1 = fst cfg2 \<and>
     (\<forall>j>0. snd cfg1 ! j = snd cfg2 ! j) \<and>
     (\<forall>i\<le>C. (cfg1 <:> 0) i = (cfg2 <:> 0) i) \<and>
     hd_span cfg1 = hd_span cfg2 \<and> hd_span cfg1 \<le> C"

lemma start_config_string_conv [simp]:
  "start_config_string k w = start_config k (string_to_symbols w)"
  by simp

lemma big_oh_constE:
  assumes "big_oh T (\<lambda>n. Suc 0)"
  obtains C where "\<forall>n. T n \<le> C"
proof -
  obtain c m where h: "\<forall>n>m. T n \<le> c"
    using assms unfolding big_oh_def by auto
  have "\<forall>n\<le>m. T n \<le> Max (insert c {T n | n. n \<le> m})"
    by (auto intro!: Max_ge)
  moreover have "\<forall>n>m. T n \<le> Max (insert c {T n | n. n \<le> m})"
    using h by (simp add: Max_ge_iff)
  ultimately have "\<forall>n. T n \<le> Max (insert c {T n | n. n \<le> m})"
    by (meson linorder_le_less_linear)
  thus ?thesis ..
qed

lemma contents_eq_on_prefix:
  assumes EQ: "take (Suc C) w = take (Suc C) v"
  shows   "\<forall>i\<le>Suc C.
             \<lfloor>map (\<lambda>b. if b then 3 else 2) w\<rfloor> i =
             \<lfloor>map (\<lambda>b. if b then 3 else 2) v\<rfloor> i"
proof (intro allI impI)
  fix i :: nat
  assume bound: "i \<le> Suc C"
  let ?f = "\<lambda>b::bool. if b then 3 else 2"

  show "\<lfloor>map ?f w\<rfloor> i = \<lfloor>map ?f v\<rfloor> i"
  proof (cases i)
    case 0
    thus ?thesis by (simp add: contents_def)
  next
    case (Suc j)
    have j_lt: "j < Suc C" using bound Suc by simp

    note take_map = arg_cong[OF EQ, of "map ?f"]
    have nth_eq:
      "map ?f w ! j = map ?f v ! j"
      using j_lt take_map
      by (metis (lifting) ext List.take_map nth_take)

    show ?thesis
    proof (cases "i \<le> length w")
      case True
      hence "j < length w" using Suc by simp
      moreover have "j < length v"
      proof -
        have "length (take (Suc C) w) = length (take (Suc C) v)"
          using EQ by simp
        hence "min (Suc C) (length w) = min (Suc C) (length v)"
          by (simp add: min.commute)
        with \<open>j < length w\<close> j_lt show ?thesis
          by (cases "length w < Suc C"; cases "length v < Suc C") simp_all
      qed
      ultimately show ?thesis
        using nth_eq True
        by (simp add: Suc)
    next
      case False
      then have len_w: "length w < i"
        by (simp add: Suc)
      have len_v: "length v < i"
      proof (rule ccontr)
        assume "\<not> length v < i" 
        then have i_le: "i \<le> length v" by simp
        have take_i_eq: "take i w = take i v"
          using EQ bound
          by (metis min.absorb1 take_take)
        have "take i w = w"
          using len_w by simp
        hence "length w = length (take i v)"
          using take_i_eq by simp
        moreover have "length (take i v) = i"
          using i_le by simp
        ultimately have "length w = i" by simp
        with len_w show False by simp
      qed
      from len_w len_v
      show ?thesis by simp
    qed
  qed
qed

lemma DTIME1_const_time:
  assumes "L \<in> DTIME (\<lambda>n.1)"
  obtains k G M C where
      "turing_machine k G M"
      "computes_in_time k M (characteristic L) (\<lambda>_. C)"
proof -
  obtain k G M T  where
  tm: "turing_machine k G M"
      "big_oh T (\<lambda>n.1)"
      "computes_in_time k M (characteristic L) T"
    using assms unfolding DTIME_def by blast

  obtain C where C: "\<forall>n. T n \<le> C"
    using tm(2) using big_oh_constE by auto

  have "computes_in_time k M (characteristic L) (\<lambda>_. C)"
    using tm(3) C
    unfolding computes_in_time_def 
    by (meson linorder_le_less_linear order_less_imp_not_eq2
        order_less_le_trans)

  thus ?thesis
    using that tm(1) by auto
qed

lemma start_input_prefix_eq:
  assumes "take (Suc C) w = take (Suc C) v"
      and "i \<le> C"
  shows   "(start_config_string k w <:> 0) i =
           (start_config_string k v <:> 0) i"
proof -
  have contents_eq:
    "\<lfloor>string_to_symbols w\<rfloor> i = \<lfloor>string_to_symbols v\<rfloor> i"
  proof -
    have "\<lfloor>map (\<lambda>b. if b then 3 else 2) w\<rfloor> i =
          \<lfloor>map (\<lambda>b. if b then 3 else 2) v\<rfloor> i"
      using assms(1,2) contents_eq_on_prefix le_imp_le_Suc
      by blast
    thus ?thesis
      by blast
  qed
  have lhs: "(start_config_string k w <:> 0) i = \<lfloor>string_to_symbols w\<rfloor> i"
    by (simp add: start_config_def)
  have rhs: "(start_config_string k v <:> 0) i = \<lfloor>string_to_symbols v\<rfloor> i"
    by (simp add: start_config_def)
  from contents_eq lhs rhs show ?thesis
    by presburger
qed

lemma indist_start:
  assumes EQ: "take (Suc C) w = take (Suc C) v"
    and k:  "2 \<le> k"
  shows     "indist C (start_config_string k w) (start_config_string k v)"
  unfolding indist_def
  using EQ start_input_prefix_eq[OF EQ] k
  by (auto simp: hd_span_def start_config_def)

lemma config_read_eq_indist:
  assumes "indist C cfg1 cfg2"
  shows   "config_read cfg1 = config_read cfg2"
proof -
  obtain q1 tps1 where cfg1: "cfg1 = (q1,tps1)" by (cases cfg1)
  obtain q2 tps2 where cfg2: "cfg2 = (q2,tps2)" by (cases cfg2)
  from assms have len: "length tps1 = length tps2"
    unfolding indist_def cfg1 cfg2 by simp
  have read_eq: "tape_read (tps1 ! j) = tape_read (tps2 ! j)"
    if "j < length tps1" for j
  proof (cases j)
    case 0
    then show ?thesis
      using assms unfolding indist_def cfg1 cfg2
      by (metis hd_span_def snd_conv)
  next
    case (Suc i)
    with that have "j > 0" by simp
    moreover from assms have "snd cfg1 ! j = snd cfg2 ! j"
      unfolding indist_def cfg1 cfg2 using \<open>j>0\<close> by simp
    ultimately show ?thesis
      using \<open>j > 0\<close>
      by (metis cfg1 cfg2 fst_conv snd_swap swap_simp)
  qed
  show ?thesis
    unfolding cfg1 cfg2 read_def
    by (metis (mono_tags, lifting) len map_equality_iff read_eq
        snd_conv)
qed

lemma nth_map_act_zip:
  assumes j: "j < length as" and len: "length as = length tps"
  shows "map (\<lambda>(a,tp). act a tp) (zip as tps) ! j = act (as ! j) (tps ! j)"
  using j len by auto

lemma nth_Nil [simp]: "([] :: 'a list) ! n = undefined n"
  by (simp add: nth_def hd_def)

lemma nth_overflow [simp]:
  "length xs \<le> n \<Longrightarrow> xs ! n = undefined (n - length xs)"
  by (induct xs arbitrary: n) (auto split: nat.split)

lemma act_prefix_eq:
  assumes cont: "\<forall>i\<le>C. fst (tp1 :: tape) i = fst tp2 i"
      and head: "snd tp1 = snd tp2"
  shows   "\<forall>i\<le>C. fst (act a tp1) i = fst (act a tp2) i"
  using cont head
  by (cases a) (auto split: direction.split)

lemma act_head_eq:
  assumes "snd (tp1:: tape) = snd tp2"
  shows   "snd (act a tp1) = snd (act a tp2)"
  using assms
  by (metis act split_pairs)

lemma indist_step:
  assumes inv : "indist C cfg1 cfg2"
      and pc  : "proper_command ||cfg1|| cmd"
      and bounds: "hd_span cfg1 < C"
      and s1  : "cfg1' = sem cmd cfg1"
      and s2  : "cfg2' = sem cmd cfg2"
    shows       "indist C cfg1' cfg2'"
proof -
  have rs_eq: "config_read cfg1 = config_read cfg2"
    using inv config_read_eq_indist by blast

  have st_eq: "fst (sem cmd cfg1) = fst (sem cmd cfg2)"
    unfolding sem_def rs_eq
    by (simp add: case_prod_beta)

  obtain st acts where acts: "cmd (config_read cfg1) = (st, acts)"
    by (cases "cmd (config_read cfg1)") blast
  hence cmd2: "cmd (config_read cfg2) = (st, acts)"
    by (simp add: rs_eq)

  define tps1 where "tps1 \<equiv> snd cfg1"
  define tps2 where "tps2 \<equiv> snd cfg2"
  have cfg1': "cfg1' = (st, map (\<lambda>(a,tp). act a tp) (zip acts tps1))"
    using s1 acts tps1_def sem_def by simp
  have cfg2': "cfg2' = (st, map (\<lambda>(a,tp). act a tp) (zip acts tps2))"
    using s2 cmd2 tps2_def sem_def by simp

  have rs_len: "length (config_read cfg1) = ||cfg1||"
    by (simp add: read_length)
  have acts_len: "length acts = ||cfg1||"
    using acts pc rs_len by auto
  hence len_eq: "length acts = length tps1"
    unfolding tps1_def by simp
  have len_eq2: "length acts = length tps2"
    using acts_len inv unfolding indist_def tps2_def
    by presburger

  have tapes_gt0: "\<forall>j>0. snd cfg1' ! j = snd cfg2' ! j"
  proof (intro allI impI)
    fix j :: nat assume j_gt: "j > 0"
    have tps_eq: "tps1 ! j = tps2 ! j"
      using inv j_gt unfolding indist_def tps1_def tps2_def by blast
    show "snd cfg1' ! j = snd cfg2' ! j"
    proof (cases "j < length acts")
      case True
      have "snd cfg1' ! j = act (acts ! j) (tps1 ! j)"
        unfolding cfg1' using nth_map_act_zip[OF True len_eq] by (simp add: tps1_def)
      also have "\<dots> = act (acts ! j) (tps2 ! j)"
        using tps_eq by simp
      also have "\<dots> = snd cfg2' ! j"
        unfolding cfg2' using nth_map_act_zip[OF True len_eq2] by (simp add: tps2_def)
      finally show ?thesis .
    next
      case False
      then show ?thesis
        using cfg1' cfg2' len_eq len_eq2 nth_overflow by auto
    qed
  qed

  have pre_contents: "\<forall>j\<le>C. fst (tps1 ! 0) j = fst (tps2 ! 0) j"
    using inv unfolding indist_def tps1_def tps2_def by blast
  have pre_head: "snd (tps1 ! 0) = snd (tps2 ! 0)"
    using inv unfolding indist_def tps1_def tps2_def
    by (metis hd_span_def)

  have tape0_prefix: "\<forall>i\<le>C. (cfg1' <:> 0) i = (cfg2' <:> 0) i"
  proof (intro allI impI)
    fix i assume i_le: "i \<le> C"
    show "(cfg1' <:> 0) i = (cfg2' <:> 0) i"
    proof (cases acts)
      case Nil
      thus ?thesis unfolding cfg1' cfg2' by simp
    next
      case (Cons a as')
      have idx0: "0 < length acts" using Cons by simp
      have "(cfg1' <:> 0) i = fst (act (acts ! 0) (tps1 ! 0)) i"
        unfolding cfg1' using nth_map_act_zip[OF idx0 len_eq] by (simp add: tps1_def)
      also have "\<dots> = fst (act (acts ! 0) (tps2 ! 0)) i"
        using act_prefix_eq[OF pre_contents pre_head] i_le by simp
      also have "\<dots> = (cfg2' <:> 0) i"
        unfolding cfg2' using nth_map_act_zip[OF idx0 len_eq2] by (simp add: tps2_def)
      finally show ?thesis .
    qed
  qed

  have hd_eq_le: "hd_span cfg1' = hd_span cfg2' \<and> hd_span cfg1' \<le> C"
  proof -
    have eq: "hd_span cfg1' = hd_span cfg2'"
    proof (cases acts)
      case Nil
      thus ?thesis unfolding cfg1' cfg2' hd_span_def by simp
    next
      case (Cons a as')
      have idx0: "0 < length acts" using Cons by simp
      have "snd cfg1' ! 0 = act (acts ! 0) (tps1 ! 0)"
        unfolding cfg1' using nth_map_act_zip[OF idx0 len_eq] by (simp add: tps1_def)
      moreover have "snd cfg2' ! 0 = act (acts ! 0) (tps2 ! 0)"
        unfolding cfg2' using nth_map_act_zip[OF idx0 len_eq2] by (simp add: tps2_def)
      ultimately show ?thesis
        using act_head_eq[OF pre_head] unfolding hd_span_def by simp
    qed
    moreover have le: "hd_span cfg1' \<le> C"
      using sem_head_move_bound[OF pc s1] bounds by simp
    ultimately show ?thesis by blast
  qed

  show "indist C cfg1' cfg2'"
    unfolding indist_def
  proof (intro conjI)
    show "||cfg1'|| = ||cfg2'||" 
      using len_eq len_eq2
      unfolding cfg1' cfg2'
      by simp
    show "fst cfg1' = fst cfg2'" using st_eq s1 s2 by simp
    show "\<forall>j>0. snd cfg1' ! j = snd cfg2' ! j" using tapes_gt0 .
    show "\<forall>i\<le>C. (cfg1' <:> 0) i = (cfg2' <:> 0) i" using tape0_prefix .
    show "hd_span cfg1' = hd_span cfg2'" using hd_eq_le by blast
    show "hd_span cfg1' \<le> C" using hd_eq_le by blast
  qed
qed

lemma indist_execute:
  assumes pm: "proper_machine ||cfg|| M"
      and inv0: "indist C cfg1 cfg2"
      and len: "||cfg1|| = ||cfg||"
      and hd_bound: "hd_span cfg1 + t \<le> C"
  shows "indist C (execute M cfg1 t) (execute M cfg2 t)"
using inv0 hd_bound
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have t_le: "hd_span cfg1 + t \<le> C"
    using Suc.prems(2) by simp
  have ind_t: "indist C (execute M cfg1 t) (execute M cfg2 t)"
    using Suc.IH[OF Suc.prems(1) t_le] .

  define cfg1_t where "cfg1_t = execute M cfg1 t"
  define cfg2_t where "cfg2_t = execute M cfg2 t"

  have hd_t_bound: "hd_span cfg1_t < C"
  proof -
    have pm1: "proper_machine ||cfg1|| M"
      using pm len by simp
    have "hd_span cfg1_t \<le> hd_span cfg1 + t"
      unfolding cfg1_t_def
      using execute_head_pos_le_time[OF pm1 refl] by simp
    also have "\<dots> < C"
      using Suc.prems(2) by simp
    finally show ?thesis .
  qed

  have exec_Suc_1: "execute M cfg1 (Suc t) = exe M cfg1_t"
    unfolding cfg1_t_def by simp
  have exec_Suc_2: "execute M cfg2 (Suc t) = exe M cfg2_t"
    unfolding cfg2_t_def by simp

  show ?case
  proof (cases "fst cfg1_t < length M")
    case False
    have step1: "exe M cfg1_t = cfg1_t"
      unfolding exe_def using False by simp

    have "fst cfg2_t = fst cfg1_t"
      using ind_t unfolding indist_def
      using cfg1_t_def cfg2_t_def by argo
    hence "\<not> (fst cfg2_t < length M)"
      using False by simp
    hence step2: "exe M cfg2_t = cfg2_t"
      unfolding exe_def by simp

    show ?thesis
      unfolding exec_Suc_1 exec_Suc_2
      using cfg1_t_def cfg2_t_def ind_t step1 step2
      by auto
  next
    case True
    define cmd where "cmd = M ! fst cfg1_t"

    have step1: "exe M cfg1_t = sem cmd cfg1_t"
      unfolding exe_def cmd_def using True by simp

    have "fst cfg2_t = fst cfg1_t"
      using ind_t unfolding indist_def
      using cfg1_t_def cfg2_t_def by presburger
    hence step2: "exe M cfg2_t = sem cmd cfg2_t"
      unfolding exe_def cmd_def using True by simp

    have tapes_eq: "||cfg1_t|| = ||cfg||"
      unfolding cfg1_t_def using execute_num_tapes_proper len
      using pm by presburger
    have pm_t: "proper_machine ||cfg1_t|| M"
      using pm tapes_eq by simp
    have pc: "proper_command ||cfg1_t|| cmd"
      using pm_t True cmd_def by simp

    have "indist C (sem cmd cfg1_t) (sem cmd cfg2_t)"
      using cfg1_t_def cfg2_t_def hd_t_bound ind_t indist_step pc
      by blast
    thus ?thesis
      unfolding exec_Suc_1 exec_Suc_2
      using cfg1_t_def cfg2_t_def hd_t_bound ind_t indist_step pc
      using step1 step2 by argo
  qed
qed


subsection \<open>Constant-Time Dependence on Prefix\<close>

text \<open>
  By applying the indist\_execute invariant up to step $C$, we can easily show 
  that two executions starting with the same prefix must deposit the exact same 
  output onto tape 1.
\<close>

lemma exec_same_output_C:
  fixes k C t :: nat  and w v :: string  and G :: nat and M :: machine
  defines "cfgw \<equiv> start_config_string k w"
      and "cfgv \<equiv> start_config_string k v"
  assumes TM   : "turing_machine k G M"
      and EQ   : "take (Suc C) w = take (Suc C) v"
      and LE   : "t \<le> C"
  shows "(execute M cfgw t <:> 1) = (execute M cfgv t <:> 1)"
proof -
  have k_ge_2: "2 \<le> k"
    using TM unfolding turing_machine_def by simp
  
  have len_w: "||cfgw|| = k"
    unfolding cfgw_def using start_config_length k_ge_2
    by (metis bot_nat_0.not_eq_extremum
        not_numeral_le_zero)
  have len_v: "||cfgv|| = k"
    unfolding cfgv_def using start_config_length k_ge_2
    by (metis bot_nat_0.not_eq_extremum
        not_numeral_le_zero)
  have len_eq: "||cfgw|| = ||cfgv||"
    using len_w len_v by simp
    
  have pm: "proper_machine ||cfgw|| M"
    using TM len_w unfolding turing_machine_def
    using nth_mem turing_commandD(1) by blast

  have inv0: "indist C cfgw cfgv"
    unfolding cfgw_def cfgv_def
    using indist_start[OF EQ k_ge_2] .

  have hd_0: "hd_span cfgw = 0"
    unfolding cfgw_def start_config_string_conv hd_span_def start_config_def by simp
  have t_bound: "hd_span cfgw + t \<le> C"
    using hd_0 LE by simp

  have ind_t: "indist C (execute M cfgw t) (execute M cfgv t)"
    using indist_execute inv0 pm t_bound by blast

  have tape1_idx: "1 > (0::nat)" by simp
  have "snd (execute M cfgw t) ! 1 = snd (execute M cfgv t) ! 1"
    using ind_t tape1_idx unfolding indist_def by presburger

  thus ?thesis
    by presburger
qed

lemma string_to_contents_inj:
  assumes "string_to_contents xs = string_to_contents ys"
  shows   "xs = ys"
proof -
  have eq_contents: "\<lfloor>string_to_symbols xs\<rfloor> = \<lfloor>string_to_symbols ys\<rfloor>"
    using assms contents_string_to_contents by simp
  have len: "length xs = length ys"
  proof (rule ccontr)
    assume "length xs \<noteq> length ys"
    then consider (less_xs) "length xs < length ys" | (less_ys) "length ys < length xs"
      by linarith
    then show False
    proof cases
      case less_xs
      define i where "i = Suc (length xs)"
      
      have "\<lfloor>string_to_symbols xs\<rfloor> i = 0"
        unfolding i_def by simp
      moreover have "\<lfloor>string_to_symbols ys\<rfloor> i \<noteq> 0"
        using less_xs i_def by simp
        
      ultimately show False
        using eq_contents by simp
    next
      case less_ys
      define i where "i = Suc (length ys)"
      
      have "\<lfloor>string_to_symbols ys\<rfloor> i = 0"
        unfolding i_def by simp
      moreover have "\<lfloor>string_to_symbols xs\<rfloor> i \<noteq> 0"
        using less_ys i_def by simp
        
      ultimately show False
        using eq_contents by simp
    qed
  qed
  moreover have "xs ! j = ys ! j" if "j < length xs" for j
  proof -
    have "\<lfloor>string_to_symbols xs\<rfloor> (Suc j) = \<lfloor>string_to_symbols ys\<rfloor> (Suc j)"
      using eq_contents by auto
    thus ?thesis
      using that len
      using Suc_1 Suc_diff_1 Suc_le_eq by force
  qed
  ultimately show ?thesis
    by (rule nth_equalityI)
qed

lemma constant_time_depends_on_prefix:
  fixes f :: "string \<Rightarrow> string"
  assumes TM: "turing_machine k G M"
      and CT: "computes_in_time k M f (\<lambda>_. C)"
      and EQ: "take (Suc C) w = take (Suc C) v"
  shows "f w = f v"
proof -
  define cfgw where "cfgw = start_config_string k w"
  define cfgv where "cfgv = start_config_string k v"

  have out_w: "execute M cfgw C <:> 1 = string_to_contents (f w)"
    using computes_in_time_execute[OF CT, of w] unfolding cfgw_def
    by blast

  have out_v: "execute M cfgv C <:> 1 = string_to_contents (f v)"
    using computes_in_time_execute[OF CT, of v] unfolding cfgv_def
    by blast

  have tapes_eq: "execute M cfgw C <:> 1 = execute M cfgv C <:> 1"
    using exec_same_output_C[where k=k and C=C and t=C and w=w and v=v and G=G and M=M]
    using TM EQ le_refl unfolding cfgw_def cfgv_def
    by blast

  have "string_to_contents (f w) = string_to_contents (f v)"
    using out_w out_v tapes_eq
    by presburger

  thus "f w = f v"
    by (rule string_to_contents_inj)
qed

lemma DTIME1_depends_on_prefix:
  fixes L :: language
  assumes "L \<in> DTIME (\<lambda>n. 1)"
  obtains C H where "\<forall>w. w \<in> L \<longleftrightarrow> take (Suc C) w \<in> H"
proof -
  obtain k G M C where tm: "turing_machine k G M" 
    and comp: "computes_in_time k M (characteristic L) (\<lambda>_. C)"
    using DTIME1_const_time[OF assms] by blast

  let ?H = "{u. \<exists>w. u = take (Suc C) w \<and> w \<in> L}"

  have "\<forall>w. w \<in> L \<longleftrightarrow> take (Suc C) w \<in> ?H"
  proof
    fix w show "w \<in> L \<longleftrightarrow> take (Suc C) w \<in> ?H"
    proof
      assume "w \<in> L" 
      then show "take (Suc C) w \<in> ?H" by auto
    next
      assume "take (Suc C) w \<in> ?H"
      then obtain v where eqpref: "take (Suc C) w = take (Suc C) v" and "v \<in> L"
        by auto

      have "characteristic L w = characteristic L v"
        using constant_time_depends_on_prefix[OF tm comp eqpref] .

      thus "w \<in> L"
        using `v \<in> L` unfolding characteristic_def by simp
    qed
  qed

  thus ?thesis
    by (rule that[of C ?H])
qed


subsection \<open>Main Theorem: SAT $\notin$ DTIME(1)\<close>

text \<open>
  The core diagonalization-style argument works by constructing two strings:
  $v$, which is properly formatted but trivially unsatisfiable, and $w$, which 
  shares the same $O(1)$ prefix with $v$ but is engineered via an odd length 
  to be syntactically invalid (and thus conditionally belongs to SAT due to the 
  library's inverted validity mapping for the default case). The hypothesized 
  $O(1)$ decider contradicts itself on this shared prefix.
\<close>

lemma SAT_not_prefix_language:
  shows "\<not> (\<exists>C H. \<forall>w. w \<in> SAT \<longleftrightarrow> take (Suc C) w \<in> H)"
proof
  assume "\<exists>C H. \<forall>w. w \<in> SAT \<longleftrightarrow> take (Suc C) w \<in> H"
  then obtain C H where prefix_decider: "\<forall>w. w \<in> SAT \<longleftrightarrow> take (Suc C) w \<in> H"
    by blast

  define \<phi>_unsat :: formula where "\<phi>_unsat = replicate (Suc C) []"
  have "\<not> satisfiable \<phi>_unsat"
    unfolding \<phi>_unsat_def satisfiable_def satisfies_def satisfies_clause_def 
    by simp
    
  define v where "v = formula_to_string \<phi>_unsat"
  
  have "v \<notin> SAT"
    unfolding SAT_def v_def using `\<not> satisfiable \<phi>_unsat` formula_to_string_inj by auto

  have len_v: "length v \<ge> Suc C"
  proof -
    have "formula_n \<phi>_unsat = replicate (Suc C) []"
      unfolding \<phi>_unsat_def formula_n_def clause_n_def by simp
    hence "nlllength (formula_n \<phi>_unsat) = nlllength (replicate (Suc C) [])"
      by simp
      
    also have "\<dots> = nllength (concat (replicate (Suc C) ([]::nat list))) + length (replicate (Suc C) ([]::nat list))"
      using nlllength_nllength_concat
      by simp
    also have "\<dots> = nllength ([]::nat list) + Suc C"
      by simp
    also have "\<dots> = Suc C"
      by simp
    finally have inner_len: "nlllength (formula_n \<phi>_unsat) = Suc C" .

    have "length v = length (symbols_to_string (binencode (numlistlist (formula_n \<phi>_unsat))))"
      unfolding v_def by simp
    also have "\<dots> = length (binencode (numlistlist (formula_n \<phi>_unsat)))"
      by simp
    also have "\<dots> = 2 * nlllength (formula_n \<phi>_unsat)"
      unfolding nlllength_def by simp
    also have "\<dots> = 2 * Suc C"
      using inner_len by simp
      
    finally show ?thesis 
      by simp
  qed

  define w where "w = (if odd (Suc C) then take (Suc C) v else take (Suc C) v @ [v ! 0])"
  
  have pref_eq: "take (Suc C) w = take (Suc C) v"
    unfolding w_def using len_v by auto
    
  have odd_w: "odd (length w)"
    using len_v unfolding w_def by auto

  have "w \<in> {x. \<not> (\<exists>\<phi>. x = formula_to_string \<phi>)}"
  proof (rule ccontr)
    assume "\<not> w \<in> {x. \<not> (\<exists>\<phi>. x = formula_to_string \<phi>)}"
    then obtain \<phi>' where w_phi: "w = formula_to_string \<phi>'" by auto
    
    have "even (length w)"
      unfolding w_phi 
      by simp 
      
    with odd_w show False by simp
  qed

  then have "w \<in> SAT"
    unfolding SAT_def by blast

  have "take (Suc C) w \<in> H \<longleftrightarrow> take (Suc C) v \<in> H"
    using pref_eq by simp
  
  moreover have "w \<in> SAT \<longleftrightarrow> take (Suc C) w \<in> H"
    using prefix_decider by simp
    
  moreover have "v \<in> SAT \<longleftrightarrow> take (Suc C) v \<in> H"
    using prefix_decider by simp
    
  ultimately show False
    using `w \<in> SAT` `v \<notin> SAT` by simp
qed

theorem SAT_not_const_time:
  shows "SAT \<notin> DTIME (\<lambda>n. 1)"
proof
  assume "SAT \<in> DTIME (\<lambda>n. 1)"
  
  then obtain C H where "\<forall>w. w \<in> SAT \<longleftrightarrow> take (Suc C) w \<in> H"
    using DTIME1_depends_on_prefix by blast
    
  with SAT_not_prefix_language show False
    by blast
qed

end
