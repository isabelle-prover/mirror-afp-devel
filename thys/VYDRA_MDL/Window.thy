theory Window
  imports "HOL-Library.AList" "HOL-Library.Mapping" "HOL-Library.While_Combinator" Timestamp
begin

type_synonym ('a, 'b) mmap = "('a \<times> 'b) list"

(* 'b is a polymorphic input symbol; 'c is a polymorphic DFA state;
   'd is a timestamp; 'e is a submonitor state *)

inductive chain_le :: "'d :: timestamp list \<Rightarrow> bool" where
  chain_le_Nil: "chain_le []"
| chain_le_singleton: "chain_le [x]"
| chain_le_cons: "chain_le (y # xs) \<Longrightarrow> x \<le> y \<Longrightarrow> chain_le (x # y # xs)"

lemma chain_le_app: "chain_le (zs @ [z]) \<Longrightarrow> z \<le> w \<Longrightarrow> chain_le ((zs @ [z]) @ [w])"
  apply (induction "zs @ [z]" arbitrary: zs rule: chain_le.induct)
    apply (auto intro: chain_le.intros)[2]
  subgoal for y xs x zs
    apply (cases zs)
     apply (auto)
    apply (metis append.assoc append_Cons append_Nil chain_le_cons)
    done
  done

inductive reaches_on :: "('e \<Rightarrow> ('e \<times> 'f) option) \<Rightarrow> 'e \<Rightarrow> 'f list \<Rightarrow> 'e \<Rightarrow> bool"
  for run :: "'e \<Rightarrow> ('e \<times> 'f) option" where
    "reaches_on run s [] s"
  | "run s = Some (s', v) \<Longrightarrow> reaches_on run s' vs s'' \<Longrightarrow> reaches_on run s (v # vs) s''"

lemma reaches_on_init_Some: "reaches_on r s xs s' \<Longrightarrow> r s' \<noteq> None \<Longrightarrow> r s \<noteq> None"
  by (auto elim: reaches_on.cases)

lemma reaches_on_split: "reaches_on run s vs s' \<Longrightarrow> i < length vs \<Longrightarrow>
  \<exists>s'' s'''. reaches_on run s (take i vs) s'' \<and> run s'' = Some (s''', vs ! i) \<and> reaches_on run s''' (drop (Suc i) vs) s'"
proof (induction s vs s' arbitrary: i rule: reaches_on.induct)
  case (2 s s' v vs s'')
  show ?case
    using 2(1,2)
  proof (cases i)
    case (Suc n)
    show ?thesis
      using 2
      by (fastforce simp: Suc intro: reaches_on.intros)
  qed (auto intro: reaches_on.intros)
qed auto

lemma reaches_on_split': "reaches_on run s vs s' \<Longrightarrow> i \<le> length vs \<Longrightarrow>
  \<exists>s'' . reaches_on run s (take i vs) s'' \<and> reaches_on run s'' (drop i vs) s'"
proof (induction s vs s' arbitrary: i rule: reaches_on.induct)
  case (2 s s' v vs s'')
  show ?case
    using 2(1,2)
  proof (cases i)
    case (Suc n)
    show ?thesis
      using 2
      by (fastforce simp: Suc intro: reaches_on.intros)
  qed (auto intro: reaches_on.intros)
qed (auto intro: reaches_on.intros)

lemma reaches_on_split_app: "reaches_on run s (vs @ vs') s' \<Longrightarrow>
  \<exists>s''. reaches_on run s vs s'' \<and> reaches_on run s'' vs' s'"
  using reaches_on_split'[where i="length vs", of run s "vs @ vs'" s']
  by auto

lemma reaches_on_inj: "reaches_on run s vs t \<Longrightarrow> reaches_on run s vs' t' \<Longrightarrow>
  length vs = length vs' \<Longrightarrow> vs = vs' \<and> t = t'"
  apply (induction s vs t arbitrary: vs' t' rule: reaches_on.induct)
   apply (auto elim: reaches_on.cases)[1]
  subgoal for s s' v vs s'' vs' t'
    apply (rule reaches_on.cases[of run s' vs s'']; rule reaches_on.cases[of run s vs' t'])
            apply assumption+
        apply auto[2]
      apply fastforce
     apply (metis length_0_conv list.discI)
    apply (metis Pair_inject length_Cons nat.inject option.inject)
    done
  done

lemma reaches_on_split_last: "reaches_on run s (xs @ [x]) s'' \<Longrightarrow>
  \<exists>s'. reaches_on run s xs s' \<and> run s' = Some (s'', x)"
  apply (induction s "xs @ [x]" s'' arbitrary: xs x rule: reaches_on.induct)
   apply simp
  subgoal for s s' v vs s'' xs x
    by (cases vs rule: rev_cases) (fastforce elim: reaches_on.cases intro: reaches_on.intros)+
  done

lemma reaches_on_rev_induct[consumes 1]: "reaches_on run s vs s' \<Longrightarrow>
  (\<And>s. P s [] s) \<Longrightarrow>
  (\<And>s s' v vs s''. reaches_on run s vs s' \<Longrightarrow> P s vs s' \<Longrightarrow> run s' = Some (s'', v) \<Longrightarrow>
    P s (vs @ [v]) s'') \<Longrightarrow>
  P s vs s'"
proof (induction vs arbitrary: s s' rule: rev_induct)
  case (snoc x xs)
  from snoc(2) obtain s'' where s''_def: "reaches_on run s xs s''" "run s'' = Some (s', x)"
    using reaches_on_split_last
    by fast
  show ?case
    using snoc(4)[OF s''_def(1) _ s''_def(2)] snoc(1)[OF s''_def(1) snoc(3,4)]
    by auto
qed (auto elim: reaches_on.cases)

lemma reaches_on_app: "reaches_on run s vs s' \<Longrightarrow> run s' = Some (s'', v) \<Longrightarrow>
  reaches_on run s (vs @ [v]) s''"
  by (induction s vs s' rule: reaches_on.induct) (auto intro: reaches_on.intros)

lemma reaches_on_trans: "reaches_on run s vs s' \<Longrightarrow> reaches_on run s' vs' s'' \<Longrightarrow>
  reaches_on run s (vs @ vs') s''"
  by (induction s vs s' rule: reaches_on.induct) (auto intro: reaches_on.intros)

lemma reaches_onD: "reaches_on run s ((t, b) # vs) s' \<Longrightarrow>
  \<exists>s''. run s = Some (s'', (t, b)) \<and> reaches_on run s'' vs s'"
  by (auto elim: reaches_on.cases)

lemma reaches_on_setD: "reaches_on run s vs s' \<Longrightarrow> x \<in> set vs \<Longrightarrow>
  \<exists>vs' vs'' s''. reaches_on run s (vs' @ [x]) s'' \<and> reaches_on run s'' vs'' s' \<and> vs = vs' @ x # vs''"
proof (induction s vs s' rule: reaches_on_rev_induct)
  case (2 s s' v vs s'')
  show ?case
  proof (cases "x \<in> set vs")
    case True
    obtain vs' vs'' s''' where split_def: "reaches_on run s (vs' @ [x]) s'''"
      "reaches_on run s''' vs'' s'" "vs = vs' @ x # vs''"
      using 2(3)[OF True]
      by auto
    show ?thesis
      using split_def(1,3) reaches_on_app[OF split_def(2) 2(2)]
      by auto
  next
    case False
    have x_v: "x = v"
      using 2(4) False
      by auto
    show ?thesis
      unfolding x_v
      using reaches_on_app[OF 2(1,2)] reaches_on.intros(1)[of run s'']
      by auto
  qed
qed auto

lemma reaches_on_len: "\<exists>vs s'. reaches_on run s vs s' \<and> (length vs = n \<or> run s' = None)"
proof (induction n arbitrary: s)
  case (Suc n)
  show ?case
  proof (cases "run s")
    case (Some x)
    obtain s' v where x_def: "x = (s', v)"
      by (cases x) auto
    obtain vs s'' where s''_def: "reaches_on run s' vs s''" "length vs = n \<or> run s'' = None"
      using Suc[of s']
      by auto
    show ?thesis
      using reaches_on.intros(2)[OF Some[unfolded x_def] s''_def(1)] s''_def(2)
      by fastforce
  qed (auto intro: reaches_on.intros)
qed (auto intro: reaches_on.intros)

lemma reaches_on_NilD: "reaches_on run q [] q' \<Longrightarrow> q = q'"
  by (auto elim: reaches_on.cases)

lemma reaches_on_ConsD: "reaches_on run q (x # xs) q' \<Longrightarrow> \<exists>q''. run q = Some (q'', x) \<and> reaches_on run q'' xs q'"
  by (auto elim: reaches_on.cases)

inductive reaches :: "('e \<Rightarrow> ('e \<times> 'f) option) \<Rightarrow> 'e \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> bool"
  for run :: "'e \<Rightarrow> ('e \<times> 'f) option" where
    "reaches run s 0 s"
  | "run s = Some (s', v) \<Longrightarrow> reaches run s' n s'' \<Longrightarrow> reaches run s (Suc n) s''"

lemma reaches_Suc_split_last: "reaches run s (Suc n) s' \<Longrightarrow> \<exists>s'' x. reaches run s n s'' \<and> run s'' = Some (s', x)"
proof (induction n arbitrary: s)
  case (Suc n)
  obtain s'' x where s''_def: "run s = Some (s'', x)" "reaches run s'' (Suc n) s'"
    using Suc(2)
    by (auto elim: reaches.cases)
  show ?case
    using s''_def(1) Suc(1)[OF s''_def(2)]
    by (auto intro: reaches.intros)
qed (auto elim!: reaches.cases intro: reaches.intros)

lemma reaches_invar: "reaches f x n y \<Longrightarrow> P x \<Longrightarrow> (\<And>z z' v. P z \<Longrightarrow> f z = Some (z', v) \<Longrightarrow> P z') \<Longrightarrow> P y"
  by (induction x n y rule: reaches.induct) auto

lemma reaches_cong: "reaches f x n y \<Longrightarrow> P x \<Longrightarrow> (\<And>z z' v. P z \<Longrightarrow> f z = Some (z', v) \<Longrightarrow> P z') \<Longrightarrow> (\<And>z. P z \<Longrightarrow> f' (g z) = map_option (apfst g) (f z)) \<Longrightarrow> reaches f' (g x) n (g y)"
  by (induction x n y rule: reaches.induct) (auto intro: reaches.intros)

lemma reaches_on_n: "reaches_on run s vs s' \<Longrightarrow> reaches run s (length vs) s'"
  by (induction s vs s' rule: reaches_on.induct) (auto intro: reaches.intros)

lemma reaches_on: "reaches run s n s' \<Longrightarrow> \<exists>vs. reaches_on run s vs s' \<and> length vs = n"
  by (induction s n s' rule: reaches.induct) (auto intro: reaches_on.intros)

definition ts_at :: "('d \<times> 'b) list \<Rightarrow> nat \<Rightarrow> 'd" where
  "ts_at rho i = fst (rho ! i)"

definition bs_at :: "('d \<times> 'b) list \<Rightarrow> nat \<Rightarrow> 'b" where
  "bs_at rho i = snd (rho ! i)"

fun sub_bs :: "('d \<times> 'b) list \<Rightarrow> nat \<times> nat \<Rightarrow> 'b list" where
  "sub_bs rho (i, j) = map (bs_at rho) [i..<j]"

definition steps :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<times> 'b) list \<Rightarrow> 'c \<Rightarrow> nat \<times> nat \<Rightarrow> 'c" where
  "steps step rho q ij = foldl step q (sub_bs rho ij)"

definition acc :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('d \<times> 'b) list \<Rightarrow>
  'c \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "acc step accept rho q ij = accept (steps step rho q ij)"

definition sup_acc :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('d \<times> 'b) list \<Rightarrow>
  'c \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('d \<times> nat) option" where
  "sup_acc step accept rho q i j =
    (let L' = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}; m = Max L' in
    if L' = {} then None else Some (ts_at rho m, m))"

definition sup_leadsto :: "'c \<Rightarrow> ('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('d \<times> 'b) list \<Rightarrow>
  nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'd option" where
  "sup_leadsto init step rho i j q =
    (let L' = {l. l < i \<and> steps step rho init (l, j) = q}; m = Max L' in
    if L' = {} then None else Some (ts_at rho m))"

definition mmap_keys :: "('a, 'b) mmap \<Rightarrow> 'a set" where
  "mmap_keys kvs = set (map fst kvs)"

definition mmap_lookup :: "('a, 'b) mmap \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "mmap_lookup = map_of"

definition valid_s :: "'c \<Rightarrow> ('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('c \<times> 'b, 'c) mapping \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow>
  ('d \<times> 'b) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('c, 'c \<times> ('d \<times> nat) option) mmap \<Rightarrow> bool" where
 "valid_s init step st accept rho u i j s \<equiv>
  (\<forall>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v) \<and>
  (mmap_keys s = {q. (\<exists>l \<le> u. steps step rho init (l, i) = q)} \<and> distinct (map fst s) \<and>
  (\<forall>q. case mmap_lookup s q of None \<Rightarrow> True
  | Some (q', tstp) \<Rightarrow> steps step rho q (i, j) = q' \<and> tstp = sup_acc step accept rho q i j))"

record ('b, 'c, 'd, 't, 'e) args =
  w_init :: 'c
  w_step :: "'c \<Rightarrow> 'b \<Rightarrow> 'c"
  w_accept :: "'c \<Rightarrow> bool"
  w_run_t :: "'t \<Rightarrow> ('t \<times> 'd) option"
  w_read_t :: "'t \<Rightarrow> 'd option"
  w_run_sub :: "'e \<Rightarrow> ('e \<times> 'b) option"

record ('b, 'c, 'd, 't, 'e) window =
  w_st :: "('c \<times> 'b, 'c) mapping"
  w_ac :: "('c, bool) mapping"
  w_i :: nat
  w_ti :: 't
  w_si :: 'e
  w_j :: nat
  w_tj :: 't
  w_sj :: 'e
  w_s :: "('c, 'c \<times> ('d \<times> nat) option) mmap"
  w_e :: "('c, 'd) mmap"

copy_bnf (dead 'b, dead 'c, dead 'd, dead 't, 'e, dead 'ext) window_ext

fun reach_window :: "('b, 'c, 'd, 't, 'e) args \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow>
  ('d \<times> 'b) list \<Rightarrow> nat \<times> 't \<times> 'e \<times> nat \<times> 't \<times> 'e \<Rightarrow> bool" where
  "reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<longleftrightarrow> i \<le> j \<and> length rho = j \<and>
    reaches_on (w_run_t args) t0 (take i (map fst rho)) ti \<and>
    reaches_on (w_run_t args) ti (drop i (map fst rho)) tj \<and>
    reaches_on (w_run_sub args) sub (take i (map snd rho)) si \<and>
    reaches_on (w_run_sub args) si (drop i (map snd rho)) sj"

lemma reach_windowI: "reaches_on (w_run_t args) t0 (take i (map fst rho)) ti \<Longrightarrow>
  reaches_on (w_run_sub args) sub (take i (map snd rho)) si \<Longrightarrow>
  reaches_on (w_run_t args) t0 (map fst rho) tj \<Longrightarrow>
  reaches_on (w_run_sub args) sub (map snd rho) sj \<Longrightarrow>
  i \<le> length rho \<Longrightarrow> length rho = j \<Longrightarrow>
  reach_window args t0 sub rho (i, ti, si, j, tj, sj)"
  by auto (metis reaches_on_split'[of _ _ _ _ i] length_map reaches_on_inj)+

lemma reach_window_shift:
  assumes "reach_window args t0 sub rho (i, ti, si, j, tj, sj)" "i < j"
    "w_run_t args ti = Some (ti', t)" "w_run_sub args si = Some (si', s)"
  shows "reach_window args t0 sub rho (Suc i, ti', si', j, tj, sj)"
  using reaches_on_app[of "w_run_t args" t0 "take i (map fst rho)" ti ti' t]
    reaches_on_app[of "w_run_sub args" sub "take i (map snd rho)" si si' s] assms
  apply (auto)
     apply (smt append_take_drop_id id_take_nth_drop length_map list.discI list.inject
      option.inject reaches_on.cases same_append_eq snd_conv take_Suc_conv_app_nth)
    apply (smt Cons_nth_drop_Suc fst_conv length_map list.discI list.inject option.inject
      reaches_on.cases)
   apply (smt append_take_drop_id id_take_nth_drop length_map list.discI list.inject
      option.inject reaches_on.cases same_append_eq snd_conv take_Suc_conv_app_nth)
  apply (smt Cons_nth_drop_Suc fst_conv length_map list.discI list.inject option.inject
      reaches_on.cases)
  done

lemma reach_window_run_ti: "reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<Longrightarrow>
  i < j \<Longrightarrow> \<exists>ti'. reaches_on (w_run_t args) t0 (take i (map fst rho)) ti \<and>
  w_run_t args ti = Some (ti', ts_at rho i) \<and>
  reaches_on (w_run_t args) ti' (drop (Suc i) (map fst rho)) tj"
  apply (auto simp: ts_at_def elim!: reaches_on.cases[of "w_run_t args" ti "drop i (map fst rho)"])
  using nth_via_drop apply fastforce
  by (metis Cons_nth_drop_Suc length_map list.inject)

lemma reach_window_run_si: "reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<Longrightarrow>
  i < j \<Longrightarrow> \<exists>si'. reaches_on (w_run_sub args) sub (take i (map snd rho)) si \<and>
  w_run_sub args si = Some (si', bs_at rho i) \<and>
  reaches_on (w_run_sub args) si' (drop (Suc i) (map snd rho)) sj"
  apply (auto simp: bs_at_def elim!: reaches_on.cases[of "w_run_sub args" si "drop i (map snd rho)"])
  using nth_via_drop apply fastforce
  by (metis Cons_nth_drop_Suc length_map list.inject)

lemma reach_window_run_tj: "reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<Longrightarrow>
  reaches_on (w_run_t args) t0 (map fst rho) tj"
  using reaches_on_trans
  by fastforce

lemma reach_window_run_sj: "reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<Longrightarrow>
  reaches_on (w_run_sub args) sub (map snd rho) sj"
  using reaches_on_trans
  by fastforce

lemma reach_window_shift_all: "reach_window args t0 sub rho (i, si, ti, j, sj, tj) \<Longrightarrow>
  reach_window args t0 sub rho (j, sj, tj, j, sj, tj)"
  using reach_window_run_tj[of args t0 sub rho] reach_window_run_sj[of args t0 sub rho]
  by (auto intro: reaches_on.intros)

lemma reach_window_app: "reach_window args t0 sub rho (i, si, ti, j, tj, sj) \<Longrightarrow>
  w_run_t args tj = Some (tj', x) \<Longrightarrow> w_run_sub args sj = Some (sj', y) \<Longrightarrow>
  reach_window args t0 sub (rho @ [(x, y)]) (i, si, ti, Suc j, tj', sj')"
  by (fastforce simp add: reaches_on_app)

fun init_args :: "('c \<times> ('c \<Rightarrow> 'b \<Rightarrow> 'c) \<times> ('c \<Rightarrow> bool)) \<Rightarrow>
  (('t \<Rightarrow> ('t \<times> 'd) option) \<times> ('t \<Rightarrow> 'd option)) \<Rightarrow>
  ('e \<Rightarrow> ('e \<times> 'b) option) \<Rightarrow> ('b, 'c, 'd, 't, 'e) args" where
  "init_args (init, step, accept) (run_t, read_t) run_sub =
  \<lparr>w_init = init, w_step = step, w_accept = accept, w_run_t = run_t, w_read_t = read_t, w_run_sub = run_sub\<rparr>"

fun init_window :: "('b, 'c, 'd, 't, 'e) args \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> ('b, 'c, 'd, 't, 'e) window" where
  "init_window args t0 sub = \<lparr>w_st = Mapping.empty, w_ac = Mapping.empty,
  w_i = 0, w_ti = t0, w_si = sub, w_j = 0, w_tj = t0, w_sj = sub,
  w_s =[(w_init args, (w_init args, None))], w_e = []\<rparr>"

definition valid_window :: "('b, 'c, 'd :: timestamp, 't, 'e) args \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> ('d \<times> 'b) list \<Rightarrow>
  ('b, 'c, 'd, 't, 'e) window \<Rightarrow> bool" where
  "valid_window args t0 sub rho w \<longleftrightarrow>
    (let init = w_init args; step = w_step args; accept = w_accept args;
    run_t = w_run_t args; run_sub = w_run_sub args;
    st = w_st w; ac = w_ac w;
    i = w_i w; ti = w_ti w; si = w_si w; j = w_j w; tj = w_tj w; sj = w_sj w;
    s = w_s w; e = w_e w in
    (reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<and>
    (\<forall>i j. i \<le> j \<and> j < length rho \<longrightarrow> ts_at rho i \<le> ts_at rho j) \<and>
    (\<forall>q. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v) \<and>
    (\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q) \<and> distinct (map fst e) \<and>
    valid_s init step st accept rho i i j s))"

lemma valid_init_window: "valid_window args t0 sub [] (init_window args t0 sub)"
  by (auto simp: valid_window_def mmap_keys_def mmap_lookup_def sup_leadsto_def
      valid_s_def steps_def sup_acc_def intro: reaches_on.intros split: option.splits)

lemma steps_app_cong: "j \<le> length rho \<Longrightarrow> steps step (rho @ [x]) q (i, j) =
  steps step rho q (i, j)"
proof -
  assume "j \<le> length rho"
  then have map_cong: "map (bs_at (rho @ [x])) [i..<j] = map (bs_at rho) [i..<j]"
    by (auto simp: bs_at_def nth_append)
  show ?thesis
    by (auto simp: steps_def map_cong)
qed

lemma acc_app_cong: "j < length rho \<Longrightarrow> acc step accept (rho @ [x]) q (i, j) =
  acc step accept rho q (i, j)"
  by (auto simp: acc_def bs_at_def nth_append steps_app_cong)

lemma sup_acc_app_cong: "j \<le> length rho \<Longrightarrow> sup_acc step accept (rho @ [x]) q i j =
  sup_acc step accept rho q i j"
  apply (auto simp: sup_acc_def Let_def ts_at_def nth_append acc_def)
   apply (metis (mono_tags, opaque_lifting) less_eq_Suc_le order_less_le_trans steps_app_cong)+
  done

lemma sup_acc_concat_cong: "j \<le> length rho \<Longrightarrow> sup_acc step accept (rho @ rho') q i j =
  sup_acc step accept rho q i j"
  apply (induction rho' rule: rev_induct)
   apply auto
  apply (smt append.assoc le_add1 le_trans length_append sup_acc_app_cong)
  done

lemma sup_leadsto_app_cong: "i \<le> j \<Longrightarrow> j \<le> length rho \<Longrightarrow>
  sup_leadsto init step (rho @ [x]) i j q = sup_leadsto init step rho i j q"
proof -
  assume assms: "i \<le> j" "j \<le> length rho"
  define L' where "L' = {l. l < i \<and> steps step rho init (l, j) = q}"
  define L'' where "L'' = {l. l < i \<and> steps step (rho @ [x]) init (l, j) = q}"
  show ?thesis
    using assms
    by (cases "L' = {}")
       (auto simp: sup_leadsto_def L'_def L''_def ts_at_def nth_append steps_app_cong)
qed

lemma chain_le:
  fixes xs :: "'d :: timestamp list"
  shows "chain_le xs \<Longrightarrow> i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<le> xs ! j"
proof (induction xs arbitrary: i j rule: chain_le.induct)
  case (chain_le_cons y xs x)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using chain_le_cons
      apply (cases j)
      apply auto
      apply (metis (no_types, lifting) le_add1 le_add_same_cancel1 le_less less_le_trans nth_Cons_0)
      done
  qed auto
qed auto

lemma steps_refl[simp]: "steps step rho q (i, i) = q"
  unfolding steps_def by auto

lemma steps_split: "i < j \<Longrightarrow> steps step rho q (i, j) =
  steps step rho (step q (bs_at rho i)) (Suc i, j)"
  unfolding steps_def by (simp add: upt_rec)

lemma steps_app: "i \<le> j \<Longrightarrow> steps step rho q (i, j + 1) =
  step (steps step rho q (i, j)) (bs_at rho j)"
  unfolding steps_def by auto

lemma steps_appE: "i \<le> j \<Longrightarrow> steps step rho q (i, Suc j) = q' \<Longrightarrow>
  \<exists>q''. steps step rho q (i, j) = q'' \<and> q' = step q'' (bs_at rho j)"
  unfolding steps_def sub_bs.simps by auto

lemma steps_comp: "i \<le> l \<Longrightarrow> l \<le> j \<Longrightarrow> steps step rho q (i, l) = q' \<Longrightarrow>
  steps step rho q' (l, j) = q'' \<Longrightarrow> steps step rho q (i, j) = q''"
proof -
  assume assms: "i \<le> l" "l \<le> j" "steps step rho q (i, l) = q'" "steps step rho q' (l, j) = q''"
  have range_app: "[i..<l] @ [l..<j] = [i..<j]"
    using assms(1,2)
    by (metis le_Suc_ex upt_add_eq_append)
  have "q' = foldl step q (map (bs_at rho) [i..<l])"
    using assms(3) unfolding steps_def by auto
  moreover have "q'' = foldl step q' (map (bs_at rho) [l..<j])"
    using assms(4) unfolding steps_def by auto
  ultimately have "q'' = foldl step q (map (bs_at rho) ([i..<l] @ [l..<j]))"
    by auto
  then show ?thesis
    unfolding steps_def range_app by auto
qed

lemma sup_acc_SomeI: "acc step accept rho q (i, Suc l) \<Longrightarrow> l \<in> {i..<j} \<Longrightarrow>
  \<exists>tp. sup_acc step accept rho q i j = Some (ts_at rho tp, tp) \<and> l \<le> tp \<and> tp < j"
proof -
  assume assms: "acc step accept rho q (i, Suc l)" "l \<in> {i..<j}"
  define L where "L = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}"
  have L_props: "finite L" "L \<noteq> {}" "l \<in> L"
    using assms unfolding L_def by auto
  then show "\<exists>tp. sup_acc step accept rho q i j = Some (ts_at rho tp, tp) \<and> l \<le> tp \<and> tp < j"
    using L_def L_props
    by (auto simp add: sup_acc_def)
       (smt L_props(1) L_props(2) Max_ge Max_in mem_Collect_eq)
qed

lemma sup_acc_Some_ts: "sup_acc step accept rho q i j = Some (ts, tp) \<Longrightarrow> ts = ts_at rho tp"
  by (auto simp add: sup_acc_def Let_def split: if_splits)

lemma sup_acc_SomeE: "sup_acc step accept rho q i j = Some (ts, tp) \<Longrightarrow>
  tp \<in> {i..<j} \<and> acc step accept rho q (i, Suc tp)"
proof -
  assume assms: "sup_acc step accept rho q i j = Some (ts, tp)"
  define L where "L  = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}"
  have L_props: "finite L" "L \<noteq> {}" "Max L = tp"
    unfolding L_def using assms
    by (auto simp add: sup_acc_def Let_def split: if_splits)
  show ?thesis
    using Max_in[OF L_props(1,2)] unfolding L_props(3) unfolding L_def by auto
qed

lemma sup_acc_NoneE: "l \<in> {i..<j} \<Longrightarrow> sup_acc step accept rho q i j = None \<Longrightarrow>
  \<not>acc step accept rho q (i, Suc l)"
  by (auto simp add: sup_acc_def Let_def split: if_splits)

lemma sup_acc_same: "sup_acc step accept rho q i i = None"
  by (auto simp add: sup_acc_def)

lemma sup_acc_None_restrict: "i \<le> j \<Longrightarrow> sup_acc step accept rho q i j = None \<Longrightarrow>
  sup_acc step accept rho (step q (bs_at rho i)) (Suc i) j = None"
  using steps_split
  apply (auto simp add: sup_acc_def Let_def acc_def split: if_splits)
  apply (smt (z3) lessI less_imp_le_nat order_less_le_trans steps_split)
  done

lemma sup_acc_ext_idle: "i \<le> j \<Longrightarrow> \<not>acc step accept rho q (i, Suc j) \<Longrightarrow>
  sup_acc step accept rho q i (Suc j) = sup_acc step accept rho q i j"
proof -
  assume assms: "i \<le> j" "\<not>acc step accept rho q (i, Suc j)"
  define L where "L = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}"
  define L' where "L' = {l \<in> {i..<Suc j}. acc step accept rho q (i, Suc l)}"
  have L_L': "L = L'"
    unfolding L_def L'_def using assms(2) less_antisym by fastforce
  show "sup_acc step accept rho q i (Suc j) = sup_acc step accept rho q i j"
    using L_def L'_def L_L' by (auto simp add: sup_acc_def)
qed

lemma sup_acc_comp_Some_ge: "i \<le> l \<Longrightarrow> l \<le> j \<Longrightarrow> tp \<ge> l \<Longrightarrow>
  sup_acc step accept rho (steps step rho q (i, l)) l j = Some (ts, tp) \<Longrightarrow>
  sup_acc step accept rho q i j = sup_acc step accept rho (steps step rho q (i, l)) l j"
proof -
  assume assms: "i \<le> l" "l \<le> j" "sup_acc step accept rho (steps step rho q (i, l)) l j =
    Some (ts, tp)" "tp \<ge> l"
  define L where "L = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}"
  define L' where "L' = {l' \<in> {l..<j}. acc step accept rho (steps step rho q (i, l)) (l, Suc l')}"
  have L'_props: "finite L'" "L' \<noteq> {}" "tp = Max L'" "ts = ts_at rho tp"
    using assms(3) unfolding L'_def
    by (auto simp add: sup_acc_def Let_def split: if_splits)
  have tp_in_L': "tp \<in> L'"
    using Max_in[OF L'_props(1,2)] unfolding L'_props(3) .
  then have tp_in_L: "tp \<in> L"
    unfolding L_def L'_def using assms(1) steps_comp[OF assms(1,2), of step rho]
    apply (auto simp add: acc_def)
    using steps_comp
    by (metis le_SucI)
  have L_props: "finite L" "L \<noteq> {}"
    using L_def tp_in_L by auto
  have "\<And>l'. l' \<in> L \<Longrightarrow> l' \<le> tp"
  proof -
    fix l'
    assume assm: "l' \<in> L"
    show "l' \<le> tp"
    proof (cases "l' < l")
      case True
      then show ?thesis
        using assms(4) by auto
    next
      case False
      then have "l' \<in> L'"
        using assm
        unfolding L_def L'_def
        by (auto simp add: acc_def) (metis assms(1) less_imp_le_nat not_less_eq steps_comp)
      then show ?thesis
        using Max_eq_iff[OF L'_props(1,2)] L'_props(3) by auto
    qed
  qed
  then have "Max L = tp"
    using Max_eq_iff[OF L_props] tp_in_L by auto
  then have "sup_acc step accept rho q i j = Some (ts, tp)"
    using L_def L_props(2) unfolding L'_props(4)
    by (auto simp add: sup_acc_def)
  then show "sup_acc step accept rho q i j = sup_acc step accept rho (steps step rho q (i, l)) l j"
    using assms(3) by auto
qed

lemma sup_acc_comp_None: "i \<le> l \<Longrightarrow> l \<le> j \<Longrightarrow>
  sup_acc step accept rho (steps step rho q (i, l)) l j = None \<Longrightarrow>
  sup_acc step accept rho q i j = sup_acc step accept rho q i l"
proof (induction "j - l" arbitrary: l)
  case (Suc n)
  have i_lt_j: "i < j"
    using Suc by auto
  have l_lt_j: "l < j"
    using Suc by auto
  have "\<not>acc step accept rho q (i, Suc l)"
    using sup_acc_NoneE[of l l j step accept rho "steps step rho q (i, l)"] Suc(2-)
    by (auto simp add: acc_def steps_def)
  then have "sup_acc step accept rho q i (l + 1) = sup_acc step accept rho q i l"
    using sup_acc_ext_idle[OF Suc(3)] by auto
  moreover have "sup_acc step accept rho (steps step rho q (i, l + 1)) (l + 1) j = None"
    using sup_acc_None_restrict[OF Suc(4,5)] steps_app[OF Suc(3), of step rho]
    by auto
  ultimately show ?case
    using Suc(1)[of "l + 1"] Suc(2,3,4,5)
    by auto
qed (auto simp add: sup_acc_same)

lemma sup_acc_ext: "i \<le> j \<Longrightarrow> acc step accept rho q (i, Suc j) \<Longrightarrow>
  sup_acc step accept rho q i (Suc j) = Some (ts_at rho j, j)"
proof -
  assume assms: "i \<le> j" "acc step accept rho q (i, Suc j)"
  define L' where "L' = {l \<in> {i..<j + 1}. acc step accept rho q (i, Suc l)}"
  have j_in_L': "finite L'" "L' \<noteq> {}" "j \<in> L'"
    using assms unfolding L'_def by auto
  have j_is_Max: "Max L' = j"
    using Max_eq_iff[OF j_in_L'(1,2)] j_in_L'(3)
    by (auto simp add: L'_def)
  show "sup_acc step accept rho q i (Suc j) = Some (ts_at rho j, j)"
    using L'_def j_is_Max j_in_L'(2)
    by (auto simp add: sup_acc_def)
qed

lemma sup_acc_None: "i < j \<Longrightarrow> sup_acc step accept rho q i j = None \<Longrightarrow>
  sup_acc step accept rho (step q (bs_at rho i)) (i + 1) j = None"
  using steps_split[of _ _ step rho]
  by (auto simp add: sup_acc_def Let_def acc_def split: if_splits)

lemma sup_acc_i: "i < j \<Longrightarrow> sup_acc step accept rho q i j = Some (ts, i) \<Longrightarrow>
  sup_acc step accept rho (step q (bs_at rho i)) (Suc i) j = None"
proof (rule ccontr)
  assume assms: "i < j" "sup_acc step accept rho q i j = Some (ts, i)"
    "sup_acc step accept rho (step q (bs_at rho i)) (Suc i) j \<noteq> None"
  from assms(3) obtain l where l_def: "l \<in> {Suc i..<j}"
    "acc step accept rho (step q (bs_at rho i)) (Suc i, Suc l)"
    by (auto simp add: sup_acc_def Let_def split: if_splits)
  define L' where "L' = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}"
  from assms(2) have L'_props: "finite L'" "L' \<noteq> {}" "Max L' = i"
    by (auto simp add: sup_acc_def L'_def Let_def split: if_splits)
  have i_lt_l: "i < l"
    using l_def(1) by auto
  from l_def have "l \<in> L'"
    unfolding L'_def acc_def using steps_split[OF i_lt_l, of step rho] by (auto simp: steps_def)
  then show "False"
    using l_def(1) L'_props Max_ge i_lt_l not_le by auto
qed

lemma sup_acc_l: "i < j \<Longrightarrow> i \<noteq> l \<Longrightarrow> sup_acc step accept rho q i j = Some (ts, l) \<Longrightarrow>
  sup_acc step accept rho q i j = sup_acc step accept rho (step q (bs_at rho i)) (Suc i) j"
proof -
  assume assms: "i < j" "i \<noteq> l" "sup_acc step accept rho q i j = Some (ts, l)"
  define L where "L = {l \<in> {i..<j}. acc step accept rho q (i, Suc l)}"
  define L' where "L' = {l \<in> {Suc i..<j}. acc step accept rho (step q (bs_at rho i)) (Suc i, Suc l)}"
  from assms(3) have L_props: "finite L" "L \<noteq> {}" "l = Max L"
    "sup_acc step accept rho q i j = Some (ts_at rho l, l)"
    by (auto simp add: sup_acc_def L_def Let_def split: if_splits)
  have l_in_L: "l \<in> L"
    using Max_in[OF L_props(1,2)] L_props(3) by auto
  then have i_lt_l: "i < l"
    unfolding L_def using assms(2) by auto
  have l_in_L': "finite L'" "L' \<noteq> {}" "l \<in> L'"
    using steps_split[OF i_lt_l, of step rho q] l_in_L assms(2)
    unfolding L_def L'_def acc_def by (auto simp: steps_def)
  have "\<And>l'. l' \<in> L' \<Longrightarrow> l' \<le> l"
  proof -
    fix l'
    assume assms: "l' \<in> L'"
    have i_lt_l': "i < l'"
      using assms unfolding L'_def by auto
    have "l' \<in> L"
      using steps_split[OF i_lt_l', of step rho] assms unfolding L_def L'_def acc_def by (auto simp: steps_def)
    then show "l' \<le> l"
      using L_props by simp
  qed
  then have l_sup_L': "Max L' = l"
    using Max_eq_iff[OF l_in_L'(1,2)] l_in_L'(3) by auto
  then show "sup_acc step accept rho q i j =
    sup_acc step accept rho (step q (bs_at rho i)) (Suc i) j"
    unfolding L_props(4)
    unfolding sup_acc_def Let_def
    using L'_def l_in_L'(2,3) L_props
    unfolding Suc_eq_plus1 by auto
qed

lemma sup_leadsto_idle: "i < j \<Longrightarrow> steps step rho init (i, j) \<noteq> q \<Longrightarrow>
  sup_leadsto init step rho i j q = sup_leadsto init step rho (i + 1) j q"
proof -
  assume assms: "i < j" "steps step rho init (i, j) \<noteq> q"
  define L where "L = {l. l < i \<and> steps step rho init (l, j) = q}"
  define L' where "L' = {l. l < i + 1 \<and> steps step rho init (l, j) = q}"
  have L_L': "L = L'"
    unfolding L_def L'_def using assms(2) less_antisym
    by fastforce
  show "sup_leadsto init step rho i j q = sup_leadsto init step rho (i + 1) j q"
    using L_def L'_def L_L'
    by (auto simp add: sup_leadsto_def)
qed

lemma sup_leadsto_SomeI: "l < i \<Longrightarrow> steps step rho init (l, j) = q \<Longrightarrow>
  \<exists>l'. sup_leadsto init step rho i j q = Some (ts_at rho l') \<and> l \<le> l' \<and> l' < i"
proof -
  assume assms: "l < i" "steps step rho init (l, j) = q"
  define L' where "L' = {l. l < i \<and> steps step rho init (l, j) = q}"
  have fin_L': "finite L'"
    unfolding L'_def by auto
  moreover have L_nonempty: "L' \<noteq> {}"
    using assms unfolding L'_def
    by (auto simp add: sup_leadsto_def split: if_splits)
  ultimately have "Max L' \<in> L'"
    using Max_in by auto
  then show "\<exists>l'. sup_leadsto init step rho i j q = Some (ts_at rho l') \<and> l \<le> l' \<and> l' < i"
    using L'_def L_nonempty assms
    by (fastforce simp add: sup_leadsto_def split: if_splits)
qed

lemma sup_leadsto_SomeE: "i \<le> j \<Longrightarrow> sup_leadsto init step rho i j q = Some ts \<Longrightarrow>
  \<exists>l < i. steps step rho init (l, j) = q \<and> ts_at rho l = ts"
proof -
  assume assms: "i \<le> j" "sup_leadsto init step rho i j q = Some ts"
  define L' where "L' = {l. l < i \<and> steps step rho init (l, j) = q}"
  have fin_L': "finite L'"
    unfolding L'_def by auto
  moreover have L_nonempty: "L' \<noteq> {}"
    using assms(2) unfolding L'_def
    by (auto simp add: sup_leadsto_def split: if_splits)
  ultimately have "Max L' \<in> L'"
    using Max_in by auto
  then show "\<exists>l < i. steps step rho init (l, j) = q \<and> ts_at rho l = ts"
    using assms(2) L'_def
    apply (auto simp add: sup_leadsto_def split: if_splits)
    using \<open>Max L' \<in> L'\<close> by blast
qed

lemma Mapping_keys_dest: "x \<in> mmap_keys f \<Longrightarrow> \<exists>y. mmap_lookup f x = Some y"
  by (auto simp add: mmap_keys_def mmap_lookup_def weak_map_of_SomeI)

lemma Mapping_keys_intro: "mmap_lookup f x \<noteq> None \<Longrightarrow> x \<in> mmap_keys f"
  by (auto simp add: mmap_keys_def mmap_lookup_def)
     (metis map_of_eq_None_iff option.distinct(1))

lemma Mapping_not_keys_intro: "mmap_lookup f x = None \<Longrightarrow> x \<notin> mmap_keys f"
  unfolding mmap_lookup_def mmap_keys_def
  using weak_map_of_SomeI by force

lemma Mapping_lookup_None_intro: "x \<notin> mmap_keys f \<Longrightarrow> mmap_lookup f x = None"
  unfolding mmap_lookup_def mmap_keys_def
  by (simp add: map_of_eq_None_iff)

primrec mmap_combine :: "'key \<Rightarrow> 'val \<Rightarrow> ('val \<Rightarrow> 'val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow>
  ('key \<times> 'val) list"
  where
  "mmap_combine k v c [] = [(k, v)]"
| "mmap_combine k v c (p # ps) = (case p of (k', v') \<Rightarrow>
    if k = k' then (k, c v' v) # ps else p # mmap_combine k v c ps)"

lemma mmap_combine_distinct_set: "distinct (map fst r) \<Longrightarrow>
  distinct (map fst (mmap_combine k v c r)) \<and>
  set (map fst (mmap_combine k v c r)) = set (map fst r) \<union> {k}"
  by (induction r) force+

lemma mmap_combine_lookup: "distinct (map fst r) \<Longrightarrow> mmap_lookup (mmap_combine k v c r) z =
  (if k = z then (case mmap_lookup r k of None \<Rightarrow> Some v | Some v' \<Rightarrow> Some (c v' v))
  else mmap_lookup r z)"
  using eq_key_imp_eq_value
  by (induction r) (fastforce simp: mmap_lookup_def split: option.splits)+

definition mmap_fold :: "('c, 'd) mmap \<Rightarrow> (('c \<times> 'd) \<Rightarrow> ('c \<times> 'd)) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
  ('c, 'd) mmap \<Rightarrow> ('c, 'd) mmap" where
  "mmap_fold m f c r = foldl (\<lambda>r p. case f p of (k, v) \<Rightarrow> mmap_combine k v c r) r m"

definition mmap_fold' :: "('c, 'd) mmap \<Rightarrow> 'e \<Rightarrow> (('c \<times> 'd) \<times> 'e \<Rightarrow> ('c \<times> 'd) \<times> 'e) \<Rightarrow>
  ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('c, 'd) mmap \<Rightarrow> ('c, 'd) mmap \<times> 'e" where
  "mmap_fold' m e f c r = foldl (\<lambda>(r, e) p. case f (p, e) of ((k, v), e') \<Rightarrow>
    (mmap_combine k v c r, e')) (r, e) m"

lemma mmap_fold'_eq: "mmap_fold' m e f' c r = (m', e') \<Longrightarrow> P e \<Longrightarrow>
  (\<And>p e p' e'. P e \<Longrightarrow> f' (p, e) = (p', e') \<Longrightarrow> p' = f p \<and> P e') \<Longrightarrow>
  m' = mmap_fold m f c r \<and> P e'"
proof (induction m arbitrary: e r m' e')
  case (Cons p m)
  obtain k v e'' where kv_def: "f' (p, e) = ((k, v), e'')" "P e''"
    using Cons
    by (cases "f' (p, e)") fastforce
  have mmap_fold: "mmap_fold m f c (mmap_combine k v c r) = mmap_fold (p # m) f c r"
    using Cons(1)[OF _ kv_def(2), where ?r="mmap_combine k v c r"] Cons(2,3,4)
    by (simp add: mmap_fold_def mmap_fold'_def kv_def(1))
  have mmap_fold': "mmap_fold' m e'' f' c (mmap_combine k v c r) = (m', e')"
    using Cons(2)
    by (auto simp: mmap_fold'_def kv_def)
  show ?case
    using Cons(1)[OF mmap_fold' kv_def(2) Cons(4)]
    unfolding mmap_fold
    by auto
qed (auto simp: mmap_fold_def mmap_fold'_def)

lemma foldl_mmap_combine_distinct_set: "distinct (map fst r) \<Longrightarrow>
  distinct (map fst (mmap_fold m f c r)) \<and>
  set (map fst (mmap_fold m f c r)) = set (map fst r) \<union> set (map (fst \<circ> f) m)"
  apply (induction m arbitrary: r)
  using mmap_combine_distinct_set
   apply (auto simp: mmap_fold_def split: prod.splits)
      apply force
     apply (smt Un_iff fst_conv imageI insert_iff)
  using mk_disjoint_insert
    apply fastforce+
  done

lemma mmap_fold_lookup_rec: "distinct (map fst r) \<Longrightarrow> mmap_lookup (mmap_fold m f c r) z =
  (case map (snd \<circ> f) (filter (\<lambda>(k, v). fst (f (k, v)) = z) m) of [] \<Rightarrow> mmap_lookup r z
  | v # vs \<Rightarrow> (case mmap_lookup r z of None \<Rightarrow> Some (foldl c v vs)
    | Some w \<Rightarrow> Some (foldl c w (v # vs))))"
proof (induction m arbitrary: r)
  case (Cons p ps)
  obtain k v where kv_def: "f p = (k, v)"
    by fastforce
  have distinct: "distinct (map fst (mmap_combine k v c r))"
    using mmap_combine_distinct_set[OF Cons(2)]
    by auto
  show ?case
    using Cons(1)[OF distinct, unfolded mmap_combine_lookup[OF Cons(2)]]
    by (auto simp: mmap_lookup_def kv_def mmap_fold_def split: list.splits option.splits)
qed (auto simp: mmap_fold_def)

lemma mmap_fold_distinct: "distinct (map fst m) \<Longrightarrow> distinct (map fst (mmap_fold m f c []))"
  using foldl_mmap_combine_distinct_set[of "[]"]
  by auto

lemma mmap_fold_set: "distinct (map fst m) \<Longrightarrow>
  set (map fst (mmap_fold m f c [])) = (fst \<circ> f) ` set m"
  using foldl_mmap_combine_distinct_set[of "[]"]
  by force

lemma mmap_lookup_empty: "mmap_lookup [] z = None"
  by (auto simp: mmap_lookup_def)

lemma mmap_fold_lookup: "distinct (map fst m) \<Longrightarrow> mmap_lookup (mmap_fold m f c []) z =
  (case map (snd \<circ> f) (filter (\<lambda>(k, v). fst (f (k, v)) = z) m) of [] \<Rightarrow> None
  | v # vs \<Rightarrow> Some (foldl c v vs))"
  using mmap_fold_lookup_rec[of "[]" _ f c]
  by (auto simp: mmap_lookup_empty split: list.splits)

definition fold_sup :: "('c, 'd :: timestamp) mmap \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('c, 'd) mmap" where
  "fold_sup m f = mmap_fold m (\<lambda>(x, y). (f x, y)) sup []"

lemma mmap_lookup_distinct: "distinct (map fst m) \<Longrightarrow> (k, v) \<in> set m \<Longrightarrow>
  mmap_lookup m k = Some v"
  by (auto simp: mmap_lookup_def)

lemma fold_sup_distinct: "distinct (map fst m) \<Longrightarrow> distinct (map fst (fold_sup m f))"
  using mmap_fold_distinct
  by (auto simp: fold_sup_def)

lemma fold_sup:
  fixes v :: "'d :: timestamp"
  shows "foldl sup v vs = fold sup vs v"
  by (induction vs arbitrary: v) (auto simp: sup.commute)

lemma lookup_fold_sup:
  assumes distinct: "distinct (map fst m)"
  shows "mmap_lookup (fold_sup m f) z =
    (let Z = {x \<in> mmap_keys m. f x = z} in
    if Z = {} then None else Some (Sup_fin ((the \<circ> mmap_lookup m) ` Z)))"
proof (cases "{x \<in> mmap_keys m. f x = z} = {}")
  case True
  have "z \<notin> mmap_keys (mmap_fold m (\<lambda>(x, y). (f x, y)) sup [])"
    using True[unfolded mmap_keys_def] mmap_fold_set[OF distinct]
    by (auto simp: mmap_keys_def)
  then have "mmap_lookup (fold_sup m f) z = None"
    unfolding fold_sup_def
    by (meson Mapping_keys_intro)
  then show ?thesis
    unfolding True
    by auto
next
  case False
  have z_in_keys: "z \<in> mmap_keys (mmap_fold m (\<lambda>(x, y). (f x, y)) sup [])"
    using False[unfolded mmap_keys_def] mmap_fold_set[OF distinct]
    by (force simp: mmap_keys_def)
  obtain v vs where vs_def: "mmap_lookup (fold_sup m f) z = Some (foldl sup v vs)"
    "v # vs = map snd (filter (\<lambda>(k, v). f k = z) m)"
    using mmap_fold_lookup[OF distinct, of "(\<lambda>(x, y). (f x, y))" sup z]
      Mapping_keys_dest[OF z_in_keys]
    by (force simp: fold_sup_def mmap_keys_def comp_def split: list.splits prod.splits)
  have "set (v # vs) = (the \<circ> mmap_lookup m) ` {x \<in> mmap_keys m. f x = z}"
  proof (rule set_eqI, rule iffI)
    fix w
    assume "w \<in> set (v # vs)"
    then obtain x where x_def: "x \<in> mmap_keys m" "f x = z" "(x, w) \<in> set m"
      using vs_def(2)
      by (auto simp add: mmap_keys_def rev_image_eqI)
    show "w \<in> (the \<circ> mmap_lookup m) ` {x \<in> mmap_keys m. f x = z}"
      using x_def(1,2) mmap_lookup_distinct[OF distinct x_def(3)]
      by force
  next
    fix w
    assume "w \<in> (the \<circ> mmap_lookup m) ` {x \<in> mmap_keys m. f x = z}"
    then obtain x where x_def: "x \<in> mmap_keys m" "f x = z" "(x, w) \<in> set m"
      using mmap_lookup_distinct[OF distinct]
      by (auto simp add: Mapping_keys_intro distinct mmap_lookup_def dest: Mapping_keys_dest)
    show "w \<in> set (v # vs)"
      using x_def
      by (force simp: vs_def(2))
  qed
  then have "foldl sup v vs = Sup_fin ((the \<circ> mmap_lookup m) ` {x \<in> mmap_keys m. f x = z})"
    unfolding fold_sup
    by (metis Sup_fin.set_eq_fold)
  then show ?thesis
    using False
    by (auto simp: vs_def(1))
qed

definition mmap_map :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) mmap \<Rightarrow> ('a, 'c) mmap" where
  "mmap_map f m = map (\<lambda>(k, v). (k, f k v)) m"

lemma mmap_map_keys: "mmap_keys (mmap_map f m) = mmap_keys m"
  by (force simp: mmap_map_def mmap_keys_def)

lemma mmap_map_fst: "map fst (mmap_map f m) = map fst m"
  by (auto simp: mmap_map_def)

definition cstep :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('c \<times> 'b, 'c) mapping \<Rightarrow>
  'c \<Rightarrow> 'b \<Rightarrow> ('c \<times> ('c \<times> 'b, 'c) mapping)" where
  "cstep step st q bs = (case Mapping.lookup st (q, bs) of None \<Rightarrow> (let res = step q bs in
    (res, Mapping.update (q, bs) res st)) | Some v \<Rightarrow> (v, st))"

definition cac :: "('c \<Rightarrow> bool) \<Rightarrow> ('c, bool) mapping \<Rightarrow> 'c \<Rightarrow> (bool \<times> ('c, bool) mapping)" where
  "cac accept ac q = (case Mapping.lookup ac q of None \<Rightarrow> (let res = accept q in
    (res, Mapping.update q res ac)) | Some v \<Rightarrow> (v, ac))"

fun mmap_fold_s :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('c \<times> 'b, 'c) mapping \<Rightarrow>
  ('c \<Rightarrow> bool) \<Rightarrow> ('c, bool) mapping \<Rightarrow>
  'b \<Rightarrow> 'd \<Rightarrow> nat \<Rightarrow> ('c, 'c \<times> ('d \<times> nat) option) mmap \<Rightarrow>
  (('c, 'c \<times> ('d \<times> nat) option) mmap \<times> ('c \<times> 'b, 'c) mapping \<times> ('c, bool) mapping)" where
  "mmap_fold_s step st accept ac bs t j [] = ([], st, ac)"
| "mmap_fold_s step st accept ac bs t j ((q, (q', tstp)) # qbss) =
    (let (q'', st') = cstep step st q' bs;
         (\<beta>, ac') = cac accept ac q'';
         (qbss', st'', ac'') = mmap_fold_s step st' accept ac' bs t j qbss in
    ((q, (q'', if \<beta> then Some (t, j) else tstp)) # qbss', st'', ac''))"

lemma mmap_fold_s_sound: "mmap_fold_s step st accept ac bs t j qbss = (qbss', st', ac') \<Longrightarrow>
  (\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v) \<Longrightarrow>
  (\<And>q bs. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v) \<Longrightarrow>
  qbss' = mmap_map (\<lambda>q (q', tstp). (step q' bs, if accept (step q' bs) then Some (t, j) else tstp)) qbss \<and>
  (\<forall>q bs. case Mapping.lookup st' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v) \<and>
  (\<forall>q bs. case Mapping.lookup ac' q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v)"
proof (induction qbss arbitrary: st ac qbss')
  case (Cons a qbss)
  obtain q q' tstp where a_def: "a = (q, (q', tstp))"
    by (cases a) auto
  obtain q'' st'' where q''_def: "cstep step st q' bs = (q'', st'')"
    "q'' = step q' bs"
    using Cons(3)
    by (cases "cstep step st q' bs")
       (auto simp: cstep_def Let_def option.case_eq_if split: option.splits if_splits)
  obtain b ac'' where b_def: "cac accept ac q'' = (b, ac'')"
    "b = accept q''"
    using Cons(4)
    by (cases "cac accept ac q''")
       (auto simp: cac_def Let_def option.case_eq_if split: option.splits if_splits)
  obtain qbss'' where qbss''_def: "mmap_fold_s step st'' accept ac'' bs t j qbss =
    (qbss'', st', ac')" "qbss' = (q, q'', if b then Some (t, j) else tstp) # qbss''"
    using Cons(2)[unfolded a_def mmap_fold_s.simps q''_def(1) b_def(1)]
    unfolding Let_def
    by (auto simp: b_def(1) split: prod.splits)
  have ih: "\<And>q bs. case Mapping.lookup st'' (q, bs) of None \<Rightarrow> True | Some a \<Rightarrow> step q bs = a"
    "\<And>q bs. case Mapping.lookup ac'' q of None \<Rightarrow> True | Some a \<Rightarrow> accept q = a"
    using q''_def b_def Cons(3,4)
    by (auto simp: cstep_def cac_def Let_def Mapping.lookup_update' option.case_eq_if
        split: option.splits if_splits)
  show ?case
    using Cons(1)[OF qbss''_def(1) ih]
    unfolding a_def q''_def(2) b_def(2) qbss''_def(2)
    by (auto simp: mmap_map_def)
qed (auto simp: mmap_map_def)

definition adv_end :: "('b, 'c, 'd :: timestamp, 't, 'e) args \<Rightarrow>
  ('b, 'c, 'd, 't, 'e) window \<Rightarrow> ('b, 'c, 'd, 't, 'e) window option" where
  "adv_end args w = (let step = w_step args; accept = w_accept args;
    run_t = w_run_t args; run_sub = w_run_sub args; st = w_st w; ac = w_ac w;
    j = w_j w; tj = w_tj w; sj = w_sj w; s = w_s w; e = w_e w in
    (case run_t tj of None \<Rightarrow> None | Some (tj', t) \<Rightarrow> (case run_sub sj of None \<Rightarrow> None | Some (sj', bs) \<Rightarrow>
      let (s', st', ac') = mmap_fold_s step st accept ac bs t j s;
      (e', st'') = mmap_fold' e st' (\<lambda>((x, y), st). let (q', st') = cstep step st x bs in ((q', y), st')) sup [] in
      Some (w\<lparr>w_st := st'', w_ac := ac', w_j := Suc j, w_tj := tj', w_sj := sj', w_s := s', w_e := e'\<rparr>))))"

lemma map_values_lookup: "mmap_lookup (mmap_map f m) z = Some v' \<Longrightarrow>
  \<exists>v. mmap_lookup m z = Some v \<and> v' = f z v"
  by (induction m) (auto simp: mmap_lookup_def mmap_map_def)

lemma acc_app:
  assumes "i \<le> j" "steps step rho q (i, Suc j) = q'" "accept q'"
  shows "sup_acc step accept rho q i (Suc j) = Some (ts_at rho j, j)"
proof -
  define L where "L = {l \<in> {i..<Suc j}. accept (steps step rho q (i, Suc l))}"
  have nonempty: "finite L" "L \<noteq> {}"
    using assms unfolding L_def by auto
  moreover have "Max {l \<in> {i..<Suc j}. accept (steps step rho q (i, Suc l))} = j"
    unfolding L_def[symmetric] Max_eq_iff[OF nonempty, of j]
    unfolding L_def using assms by auto
  ultimately show ?thesis
    by (auto simp add: sup_acc_def acc_def L_def)
qed

lemma acc_app_idle:
  assumes "i \<le> j" "steps step rho q (i, Suc j) = q'" "\<not>accept q'"
  shows "sup_acc step accept rho q i (Suc j) = sup_acc step accept rho q i j"
  using assms
  by (auto simp add: sup_acc_def Let_def acc_def elim: less_SucE) (metis less_Suc_eq)+

lemma sup_fin_closed: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
  (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> sup x y \<in> {x, y}) \<Longrightarrow> \<Squnion>\<^sub>f\<^sub>i\<^sub>n A \<in> A"
  apply (induct A rule: finite.induct)
  using Sup_fin.insert
  by auto fastforce

lemma valid_adv_end:
  assumes "valid_window args t0 sub rho w" "w_run_t args (w_tj w) = Some (tj', t)"
    "w_run_sub args (w_sj w) = Some (sj', bs)"
    "\<And>t'. t' \<in> set (map fst rho) \<Longrightarrow> t' \<le> t"
  shows "case adv_end args w of None \<Rightarrow> False | Some w' \<Rightarrow> valid_window args t0 sub (rho @ [(t, bs)]) w'"
proof -
  define init where "init = w_init args"
  define step where "step = w_step args"
  define accept where "accept = w_accept args"
  define run_t where "run_t = w_run_t args"
  define run_sub where "run_sub = w_run_sub args"
  define st where "st = w_st w"
  define ac where "ac = w_ac w"
  define i where "i = w_i w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define j where "j = w_j w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "reach_window args t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "(\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v)"
    "(\<And>q bs. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v)"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q" "distinct (map fst e)"
    "valid_s init step st accept rho i i j s"
    using assms(1)
    unfolding valid_window_def valid_s_def Let_def init_def step_def accept_def run_t_def
        run_sub_def st_def ac_def i_def ti_def si_def j_def tj_def sj_def s_def e_def
    by auto
  have i_j: "i \<le> j"
    using valid_before(1)
    by auto
  have distinct_before: "distinct (map fst s)" "distinct (map fst e)"
    using valid_before
    by (auto simp: valid_s_def)
  note run_tj = assms(2)[folded run_t_def tj_def]
  note run_sj = assms(3)[folded run_sub_def sj_def]
  define rho' where "rho' = rho @ [(t, bs)]"
  have ts_at_mono: "\<And>i j. i \<le> j \<Longrightarrow> j < length rho' \<Longrightarrow> ts_at rho' i \<le> ts_at rho' j"
    using valid_before(2) assms(4)
    by (auto simp: rho'_def ts_at_def nth_append split: option.splits list.splits if_splits)
  obtain s' st' ac' where s'_def: "mmap_fold_s step st accept ac bs t j s = (s', st', ac')"
    apply (cases "mmap_fold_s step st accept ac bs t j s")
    apply (auto)
    done
  have s'_mmap_map: "s' = mmap_map (\<lambda>q (q', tstp).
    (step q' bs, if accept (step q' bs) then Some (t, j) else tstp)) s"
    "(\<And>q bs. case Mapping.lookup st' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v)"
    "(\<And>q bs. case Mapping.lookup ac' q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v)"
    using mmap_fold_s_sound[OF s'_def valid_before(3,4)]
    by auto
  obtain e' st'' where e'_def: "mmap_fold' e st' (\<lambda>((x, y), st).
    let (q', st') = cstep step st x bs in ((q', y), st')) sup [] = (e', st'')"
    by (metis old.prod.exhaust)
  define inv where "inv \<equiv> \<lambda>st'. \<forall>q bs. case Mapping.lookup st' (q, bs) of None \<Rightarrow> True
    | Some v \<Rightarrow> step q bs = v"
  have inv_st': "inv st'"
    using s'_mmap_map(2)
    by (auto simp: inv_def)
  have "\<And>p e p' e'. inv e \<Longrightarrow> (case (p, e) of (x, xa) \<Rightarrow> (case x of (x, y) \<Rightarrow>
    \<lambda>st. let (q', st') = cstep step st x bs in ((q', y), st')) xa) = (p', e') \<Longrightarrow>
    p' = (case p of (x, y) \<Rightarrow> (step x bs, y)) \<and> inv e'"
    by (auto simp: inv_def cstep_def Let_def Mapping.lookup_update' split: option.splits if_splits)
  then have e'_fold_sup_st'': "e' = fold_sup e (\<lambda>q. step q bs)"
    "(\<And>q bs. case Mapping.lookup st'' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v)"
    using mmap_fold'_eq[OF e'_def, of inv "\<lambda>(x, y). (step x bs, y)", OF inv_st']
    by (fastforce simp: fold_sup_def inv_def)+
  have adv_end: "adv_end args w = Some (w\<lparr>w_st := st'', w_ac := ac',
    w_j := Suc j, w_tj := tj', w_sj := sj', w_s := s', w_e := e'\<rparr>)"
    using run_tj run_sj e'_def[unfolded st_def]
    unfolding adv_end_def init_def step_def accept_def run_t_def run_sub_def
      i_def ti_def si_def j_def tj_def sj_def s_def e_def s'_def e'_def
    by (auto simp: Let_def s'_def[unfolded step_def st_def accept_def ac_def j_def s_def])
  have keys_s': "mmap_keys s' = mmap_keys s"
    by (force simp: mmap_keys_def mmap_map_def s'_mmap_map(1))
  have lookup_s: "\<And>q q' tstp. mmap_lookup s q = Some (q', tstp) \<Longrightarrow>
  steps step rho' q (i, j) = q' \<and> tstp = sup_acc step accept rho' q i j"
    using valid_before Mapping_keys_intro
    by (force simp add: Let_def rho'_def valid_s_def steps_app_cong sup_acc_app_cong
        split: option.splits)
  have bs_at_rho'_j: "bs_at rho' j = bs"
    using valid_before
    by (auto simp: rho'_def bs_at_def nth_append)
  have ts_at_rho'_j: "ts_at rho' j = t"
    using valid_before
    by (auto simp: rho'_def ts_at_def nth_append)
  have lookup_s': "\<And>q q' tstp. mmap_lookup s' q = Some (q', tstp) \<Longrightarrow>
  steps step rho' q (i, Suc j) = q' \<and> tstp = sup_acc step accept rho' q i (Suc j)"
  proof -
    fix q q'' tstp'
    assume assm: "mmap_lookup s' q = Some (q'', tstp')"
    obtain q' tstp where "mmap_lookup s q = Some (q', tstp)" "q'' = step q' bs"
      "tstp' = (if accept (step q' bs) then Some (t, j) else tstp)"
      using map_values_lookup[OF assm[unfolded s'_mmap_map]] by auto
    then show "steps step rho' q (i, Suc j) = q'' \<and> tstp' = sup_acc step accept rho' q i (Suc j)"
      using lookup_s
      apply (auto simp: bs_at_rho'_j ts_at_rho'_j)
         apply (metis Suc_eq_plus1 bs_at_rho'_j i_j steps_app)
        apply (metis acc_app bs_at_rho'_j i_j steps_appE ts_at_rho'_j)
       apply (metis Suc_eq_plus1 bs_at_rho'_j i_j steps_app)
      apply (metis (no_types, lifting) acc_app_idle bs_at_rho'_j i_j steps_appE)
      done
  qed
  have lookup_e: "\<And>q. mmap_lookup e q = sup_leadsto init step rho' i j q"
    using valid_before sup_leadsto_app_cong[of _ _ rho init step]
    by (auto simp: rho'_def)
  have keys_e_alt: "mmap_keys e = {q. \<exists>l < i. steps step rho' init (l, j) = q}"
    using valid_before
    apply (auto simp add: sup_leadsto_def rho'_def)
     apply (metis (no_types, lifting) Mapping_keys_dest lookup_e rho'_def sup_leadsto_SomeE)
    apply (metis (no_types, lifting) Mapping_keys_intro option.simps(3) order_refl steps_app_cong)
    done
  have finite_keys_e: "finite (mmap_keys e)"
    unfolding keys_e_alt
    by (rule finite_surj[of "{l. l < i}"]) auto
  have "reaches_on run_sub sub (map snd rho) sj"
    using valid_before reaches_on_trans
    unfolding run_sub_def sub_def
    by fastforce
  then have reaches_on': "reaches_on run_sub sub (map snd rho @ [bs]) sj'"
    using reaches_on_app run_sj
    by fast
  have "reaches_on run_t t0 (map fst rho) tj"
    using valid_before reaches_on_trans
    unfolding run_t_def
    by fastforce
  then have reach_t': "reaches_on run_t t0 (map fst rho') tj'"
    using reaches_on_app run_tj
    unfolding rho'_def
    by fastforce
  have lookup_e': "\<And>q. mmap_lookup e' q = sup_leadsto init step rho' i (Suc j) q"
  proof -
    fix q
    define Z where "Z = {x \<in> mmap_keys e. step x bs = q}"
    show "mmap_lookup e' q = sup_leadsto init step rho' i (Suc j) q"
    proof (cases "Z = {}")
      case True
      then have "mmap_lookup e' q = None"
        using Z_def lookup_fold_sup[OF distinct_before(2)]
        unfolding e'_fold_sup_st''
        by (auto simp: Let_def)
      moreover have "sup_leadsto init step rho' i (Suc j) q = None"
      proof (rule ccontr)
        assume assm: "sup_leadsto init step rho' i (Suc j) q \<noteq> None"
        obtain l where l_def: "l < i" "steps step rho' init (l, Suc j) = q"
          using i_j sup_leadsto_SomeE[of i "Suc j"] assm
          by force
        have l_j: "l \<le> j"
          using less_le_trans[OF l_def(1) i_j] by auto
        obtain q'' where q''_def: "steps step rho' init (l, j) = q''" "step q'' bs = q"
          using steps_appE[OF _ l_def(2)] l_j
          by (auto simp: bs_at_rho'_j)
        then have "q'' \<in> mmap_keys e"
          using keys_e_alt l_def(1)
          by auto
        then show "False"
          using Z_def q''_def(2) True
          by auto
      qed
      ultimately show ?thesis
        by auto
    next
      case False
      then have lookup_e': "mmap_lookup e' q = Some (Sup_fin ((the \<circ> mmap_lookup e) ` Z))"
        using Z_def lookup_fold_sup[OF distinct_before(2)]
        unfolding e'_fold_sup_st''
        by (auto simp: Let_def)
      define L where "L = {l. l < i \<and> steps step rho' init (l, Suc j) = q}"
      have fin_L: "finite L"
        unfolding L_def by auto
      have Z_alt: "Z = {x. \<exists>l < i. steps step rho' init (l, j) = x \<and> step x bs = q}"
        using Z_def[unfolded keys_e_alt] by auto
      have fin_Z: "finite Z"
        unfolding Z_alt by auto
      have L_nonempty: "L \<noteq> {}"
        using L_def Z_alt False i_j steps_app[of _ _ step rho q]
        by (auto simp: bs_at_rho'_j)
          (smt Suc_eq_plus1 bs_at_rho'_j less_irrefl_nat less_le_trans nat_le_linear steps_app)
      have sup_leadsto: "sup_leadsto init step rho' i (Suc j) q = Some (ts_at rho' (Max L))"
        using L_nonempty L_def
        by (auto simp add: sup_leadsto_def)
      have j_lt_rho': "j < length rho'"
        using valid_before
        by (auto simp: rho'_def)
      have "Sup_fin ((the \<circ> mmap_lookup e) ` Z) = ts_at rho' (Max L)"
      proof (rule antisym)
        obtain z ts where zts_def: "z \<in> Z" "(the \<circ> mmap_lookup e) z = ts"
          "Sup_fin ((the \<circ> mmap_lookup e) ` Z) = ts"
        proof -
          assume lassm: "\<And>z ts. z \<in> Z \<Longrightarrow> (the \<circ> mmap_lookup e) z = ts \<Longrightarrow>
          \<Squnion>\<^sub>f\<^sub>i\<^sub>n ((the \<circ> mmap_lookup e) ` Z) = ts \<Longrightarrow> thesis"
          define T where "T = (the \<circ> mmap_lookup e) ` Z"
          have T_sub: "T \<subseteq> ts_at rho' ` {..j}"
            using lookup_e keys_e_alt i_j
            by (auto simp add: T_def Z_def sup_leadsto_def)
          have "finite T" "T \<noteq> {}"
            using fin_Z False
            by (auto simp add: T_def)
          then have sup_in: "\<Squnion>\<^sub>f\<^sub>i\<^sub>n T \<in> T"
          proof (rule sup_fin_closed)
            fix x y
            assume xy: "x \<in> T" "y \<in> T"
            then obtain a c where "x = ts_at rho' a" "y = ts_at rho' c" "a \<le> j" "c \<le> j"
              using T_sub
              by (meson atMost_iff imageE subsetD)
            then show "sup x y \<in> {x, y}"
              using ts_at_mono j_lt_rho'
              by (cases "a \<le> c") (auto simp add: sup.absorb1 sup.absorb2)
          qed
          then show ?thesis
            using lassm
            by (auto simp add: T_def)
        qed
        from zts_def(2) have lookup_e_z: "mmap_lookup e z = Some ts"
          using zts_def(1) Z_def by (auto dest: Mapping_keys_dest)
        have "sup_leadsto init step rho' i j z = Some ts"
          using lookup_e_z lookup_e
          by auto
        then obtain l where l_def: "l < i" "steps step rho' init (l, j) = z" "ts_at rho' l = ts"
          using sup_leadsto_SomeE[OF i_j]
          by (fastforce simp: rho'_def ts_at_def nth_append)
        have l_j: "l \<le> j"
          using less_le_trans[OF l_def(1) i_j] by auto
        have "l \<in> L"
          unfolding L_def using l_def zts_def(1) Z_alt
          by auto (metis (no_types, lifting) Suc_eq_plus1 bs_at_rho'_j l_j steps_app)
        then have "l \<le> Max L" "Max L < i"
          using L_nonempty fin_L
          by (auto simp add: L_def)
        then show "Sup_fin ((the \<circ> mmap_lookup e) ` Z) \<le> ts_at rho' (Max L)"
          unfolding zts_def(3) l_def(3)[symmetric]
          using ts_at_mono i_j j_lt_rho'
          by (auto simp: rho'_def)
      next
        obtain l where l_def: "Max L = l" "l < i" "steps step rho' init (l, Suc j) = q"
          using Max_in[OF fin_L L_nonempty] L_def by auto
        obtain z where z_def: "steps step rho' init (l, j) = z" "step z bs = q"
          using l_def(2,3) i_j bs_at_rho'_j
          by (metis less_imp_le_nat less_le_trans steps_appE)
        have z_in_Z: "z \<in> Z"
          unfolding Z_alt
          using l_def(2) z_def i_j
          by fastforce
        have lookup_e_z: "mmap_lookup e z = sup_leadsto init step rho' i j z"
          using lookup_e z_in_Z Z_alt
          by auto
        obtain l' where l'_def: "sup_leadsto init step rho' i j z = Some (ts_at rho' l')"
          "l \<le> l'" "l' < i"
          using sup_leadsto_SomeI[OF l_def(2) z_def(1)] by auto
        have "ts_at rho' l' \<in> (the \<circ> mmap_lookup e) ` Z"
          using lookup_e_z l'_def(1) z_in_Z
          by force
        then have "ts_at rho' l' \<le> Sup_fin ((the \<circ> mmap_lookup e) ` Z)"
          using Inf_fin_le_Sup_fin fin_Z z_in_Z
          by (simp add: Sup_fin.coboundedI)
        then show "ts_at rho' (Max L) \<le> Sup_fin ((the \<circ> mmap_lookup e) ` Z)"
        unfolding l_def(1)
        using ts_at_mono l'_def(2,3) i_j j_lt_rho'
        by (fastforce simp: rho'_def)
      qed
      then show ?thesis
        unfolding lookup_e' sup_leadsto by auto
    qed
  qed
  have "distinct (map fst s')" "distinct (map fst e')"
    using distinct_before mmap_fold_distinct
    unfolding s'_mmap_map mmap_map_fst e'_fold_sup_st'' fold_sup_def
    by auto
  moreover have "mmap_keys s' = {q. \<exists>l\<le>i. steps step rho' init (l, i) = q}"
    unfolding keys_s' rho'_def
    using valid_before(1,7) valid_s_def[of init step st accept rho i i j s]
    by (auto simp: steps_app_cong[of _ rho step])
  moreover have "reaches_on run_t ti (drop i (map fst rho')) tj'"
    "reaches_on run_sub si (drop i (map snd rho')) sj'"
    using valid_before reaches_on_app run_tj run_sj
    by (auto simp: rho'_def run_t_def run_sub_def)
  ultimately show ?thesis
    unfolding adv_end
    using valid_before lookup_e' lookup_s' ts_at_mono s'_mmap_map(3) e'_fold_sup_st''(2)
    by (fastforce simp: valid_window_def Let_def init_def step_def accept_def run_t_def
        run_sub_def i_def ti_def si_def j_def tj_def sj_def s_def e'_def
        rho'_def valid_s_def intro!: exI[of _ rho'] split: option.splits)
qed

lemma adv_end_bounds:
  assumes "w_run_t args (w_tj w) = Some (tj', t)"
    "w_run_sub args (w_sj w) = Some (sj', bs)"
    "adv_end args w = Some w'"
  shows "w_i w' = w_i w" "w_ti w' = w_ti w" "w_si w' = w_si w"
    "w_j w' = Suc (w_j w)" "w_tj w' = tj'" "w_sj w' = sj'"
  using assms
  by (auto simp: adv_end_def Let_def split: prod.splits)

definition drop_cur :: "nat \<Rightarrow> ('c \<times> ('d \<times> nat) option) \<Rightarrow> ('c \<times> ('d \<times> nat) option)" where
  "drop_cur i = (\<lambda>(q', tstp). (q', case tstp of Some (ts, tp) \<Rightarrow>
    if tp = i then None else tstp | None \<Rightarrow> tstp))"

definition adv_d :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('c \<times> 'b, 'c) mapping \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow>
  ('c, 'c \<times> ('d \<times> nat) option) mmap \<Rightarrow>
  (('c, 'c \<times> ('d \<times> nat) option) mmap \<times> ('c \<times> 'b, 'c) mapping)" where
  "adv_d step st i b s = (mmap_fold' s st (\<lambda>((x, v), st). case cstep step st x b of (x', st') \<Rightarrow>
    ((x', drop_cur i v), st')) (\<lambda>x y. x) [])"

lemma adv_d_mmap_fold:
  assumes inv: "\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v"
  and fold': "mmap_fold' s st (\<lambda>((x, v), st). case cstep step st x bs of (x', st') \<Rightarrow>
    ((x', drop_cur i v), st')) (\<lambda>x y. x) r = (s', st')"
  shows "s' = mmap_fold s (\<lambda>(x, v). (step x bs, drop_cur i v)) (\<lambda>x y. x) r \<and>
    (\<forall>q bs. case Mapping.lookup st' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v)"
proof -
  define inv where "inv \<equiv> \<lambda>st. \<forall>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True
    | Some v \<Rightarrow> step q bs = v"
  have inv_st: "inv st"
    using inv
    by (auto simp: inv_def)
  show ?thesis
    by (rule mmap_fold'_eq[OF fold', of inv "\<lambda>(x, v). (step x bs, drop_cur i v)",
          OF inv_st, unfolded inv_def])
       (auto simp: cstep_def Let_def Mapping.lookup_update'
        split: prod.splits option.splits if_splits)
qed

definition keys_idem :: "('c \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow>
  ('c, 'c \<times> ('d \<times> nat) option) mmap \<Rightarrow> bool" where
  "keys_idem step i b s = (\<forall>x \<in> mmap_keys s. \<forall>x' \<in> mmap_keys s.
    step x b = step x' b \<longrightarrow> drop_cur i (the (mmap_lookup s x)) =
    drop_cur i (the (mmap_lookup s x')))"

lemma adv_d_keys:
  assumes inv: "\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v"
  and distinct: "distinct (map fst s)"
  and adv_d: "adv_d step st i bs s = (s', st')"
shows "mmap_keys s' = (\<lambda>q. step q bs) ` (mmap_keys s)"
  using adv_d_mmap_fold[OF inv adv_d[unfolded adv_d_def]]
    mmap_fold_set[OF distinct]
  unfolding mmap_keys_def
  by fastforce

lemma lookup_adv_d_None:
  assumes inv: "\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v"
    and distinct: "distinct (map fst s)"
    and adv_d: "adv_d step st i bs s = (s', st')"
    and Z_empty: "{x \<in> mmap_keys s. step x bs = z} = {}"
  shows "mmap_lookup s' z = None"
proof -
  have "z \<notin> mmap_keys (mmap_fold s (\<lambda>(x, v). (step x bs, drop_cur i v)) (\<lambda>x y. x) [])"
    using Z_empty[unfolded mmap_keys_def] mmap_fold_set[OF distinct]
    by (auto simp: mmap_keys_def)
  then show ?thesis
    using adv_d adv_d_mmap_fold[OF inv adv_d[unfolded adv_d_def]]
    unfolding adv_d_def
    by (simp add: Mapping_lookup_None_intro)
qed

lemma lookup_adv_d_Some:
  assumes inv: "\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v"
    and distinct: "distinct (map fst s)" and idem: "keys_idem step i bs s"
    and wit: "x \<in> mmap_keys s" "step x bs = z"
    and adv_d: "adv_d step st i bs s = (s', st')"
  shows "mmap_lookup s' z = Some (drop_cur i (the (mmap_lookup s x)))"
proof -
  have z_in_keys: "z \<in> mmap_keys (mmap_fold s (\<lambda>(x, v). (step x bs, drop_cur i v)) (\<lambda>x y. x) [])"
    using wit(1,2)[unfolded mmap_keys_def] mmap_fold_set[OF distinct]
    by (force simp: mmap_keys_def)
  obtain v vs where vs_def: "mmap_lookup s' z = Some (foldl (\<lambda>x y. x) v vs)"
    "v # vs = map (\<lambda>(x, v). drop_cur i v) (filter (\<lambda>(k, v). step k bs = z) s)"
    using adv_d adv_d_mmap_fold[OF inv adv_d[unfolded adv_d_def]]
    unfolding adv_d_def
    using mmap_fold_lookup[OF distinct, of "(\<lambda>(x, v). (step x bs, drop_cur i v))" "\<lambda>x y. x" z]
      Mapping_keys_dest[OF z_in_keys]
    by (force simp: adv_d_def mmap_keys_def split: list.splits)
  have "set (v # vs) = drop_cur i ` (the \<circ> mmap_lookup s) ` {x \<in> mmap_keys s. step x bs = z}"
  proof (rule set_eqI, rule iffI)
    fix w
    assume "w \<in> set (v # vs)"
    then obtain x y where xy_def: "x \<in> mmap_keys s" "step x bs = z" "(x, y) \<in> set s"
      "w = drop_cur i y"
      using vs_def(2)
      by (auto simp add: mmap_keys_def rev_image_eqI)
    show "w \<in> drop_cur i ` (the \<circ> mmap_lookup s) ` {x \<in> mmap_keys s. step x bs = z}"
      using xy_def(1,2,4) mmap_lookup_distinct[OF distinct xy_def(3)]
      by force
  next
    fix w
    assume "w \<in> drop_cur i ` (the \<circ> mmap_lookup s) ` {x \<in> mmap_keys s. step x bs = z}"
    then obtain x y where xy_def: "x \<in> mmap_keys s" "step x bs = z" "(x, y) \<in> set s"
      "w = drop_cur i y"
      using mmap_lookup_distinct[OF distinct]
      by (auto simp add: Mapping_keys_intro distinct mmap_lookup_def dest: Mapping_keys_dest)
    show "w \<in> set (v # vs)"
      using xy_def
      by (force simp: vs_def(2))
  qed
  then have "foldl (\<lambda>x y. x) v vs = drop_cur i (the (mmap_lookup s x))"
    using wit
    apply (induction vs arbitrary: v)
     apply (auto)
     apply (smt empty_is_image idem imageE insert_not_empty keys_idem_def mem_Collect_eq
        the_elem_eq the_elem_image_unique)
    apply (smt Collect_cong idem imageE insert_compr keys_idem_def mem_Collect_eq)
    done
  then show ?thesis
    using wit
    by (auto simp: vs_def(1))
qed

definition "loop_cond j = (\<lambda>(st, ac, i, ti, si, q, s, tstp). i < j \<and> q \<notin> mmap_keys s)"
definition "loop_body step accept run_t run_sub =
  (\<lambda>(st, ac, i, ti, si, q, s, tstp). case run_t ti of Some (ti', t) \<Rightarrow>
  case run_sub si of Some (si', b) \<Rightarrow> case adv_d step st i b s of (s', st') \<Rightarrow>
  case cstep step st' q b of (q', st'') \<Rightarrow> case cac accept ac q' of (\<beta>, ac') \<Rightarrow>
  (st'', ac', Suc i, ti', si', q', s', if \<beta> then Some (t, i) else tstp))"
definition "loop_inv init step accept args t0 sub rho u j tj sj =
  (\<lambda>(st, ac, i, ti, si, q, s, tstp). u + 1 \<le> i \<and>
  reach_window args t0 sub rho (i, ti, si, j, tj, sj) \<and>
  steps step rho init (u + 1, i) = q \<and>
  (\<forall>q. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v) \<and>
  valid_s init step st accept rho u i j s \<and> tstp = sup_acc step accept rho init (u + 1) i)"

definition mmap_update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mmap \<Rightarrow> ('a, 'b) mmap" where
  "mmap_update = AList.update"

lemma mmap_update_distinct: "distinct (map fst m) \<Longrightarrow> distinct (map fst (mmap_update k v m))"
  by (auto simp: mmap_update_def distinct_update)

definition adv_start :: "('b, 'c, 'd :: timestamp, 't, 'e) args \<Rightarrow>
  ('b, 'c, 'd, 't, 'e) window \<Rightarrow> ('b, 'c, 'd, 't, 'e) window" where
  "adv_start args w = (let init = w_init args; step = w_step args; accept = w_accept args;
    run_t = w_run_t args; run_sub = w_run_sub args; st = w_st w; ac = w_ac w;
    i = w_i w; ti = w_ti w; si = w_si w; j = w_j w;
    s = w_s w; e = w_e w in
    (case run_t ti of Some (ti', t) \<Rightarrow> (case run_sub si of Some (si', bs) \<Rightarrow>
    let (s', st') = adv_d step st i bs s;
    e' = mmap_update (fst (the (mmap_lookup s init))) t e;
    (st_cur, ac_cur, i_cur, ti_cur, si_cur, q_cur, s_cur, tstp_cur) =
      while (loop_cond j) (loop_body step accept run_t run_sub)
        (st', ac, Suc i, ti', si', init, s', None);
    s'' = mmap_update init (case mmap_lookup s_cur q_cur of Some (q', tstp') \<Rightarrow>
      (case tstp' of Some (ts, tp) \<Rightarrow> (q', tstp') | None \<Rightarrow> (q', tstp_cur))
      | None \<Rightarrow> (q_cur, tstp_cur)) s' in
    w\<lparr>w_st := st_cur, w_ac := ac_cur, w_i := Suc i, w_ti := ti', w_si := si',
      w_s := s'', w_e := e'\<rparr>)))"

lemma valid_adv_d:
  assumes valid_before: "valid_s init step st accept rho u i j s"
    and u_le_i: "u \<le> i" and i_lt_j: "i < j" and b_def: "b = bs_at rho i"
    and adv_d: "adv_d step st i b s = (s', st')"
  shows "valid_s init step st' accept rho u (i + 1) j s'"
proof -
  have inv_st: "\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v"
    using valid_before by (auto simp add: valid_s_def)
  have keys_s: "mmap_keys s = {q. (\<exists>l \<le> u. steps step rho init (l, i) = q)}"
    using valid_before by (auto simp add: valid_s_def)
  have fin_keys_s: "finite (mmap_keys s)"
    using valid_before by (auto simp add: valid_s_def)
  have lookup_s: "\<And>q q' tstp. mmap_lookup s q = Some (q', tstp) \<Longrightarrow>
    steps step rho q (i, j) = q' \<and> tstp = sup_acc step accept rho q i j"
    using valid_before Mapping_keys_intro
    by (auto simp add: valid_s_def) (smt case_prodD option.simps(5))+
  have drop_cur_i: "\<And>x. x \<in> mmap_keys s \<Longrightarrow> drop_cur i (the (mmap_lookup s x)) =
    (steps step rho (step x (bs_at rho i)) (i + 1, j),
    sup_acc step accept rho (step x (bs_at rho i)) (i + 1) j)"
  proof -
    fix x
    assume assms: "x \<in> mmap_keys s"
    obtain q tstp where q_def: "mmap_lookup s x = Some (q, tstp)"
      using assms(1) by (auto dest: Mapping_keys_dest)
    have q_q': "q = steps step rho (step x (bs_at rho i)) (i + 1, j)"
      "tstp = sup_acc step accept rho x i j"
      using lookup_s[OF q_def] steps_split[OF i_lt_j] assms(1) by auto
    show "drop_cur i (the (mmap_lookup s x)) =
      (steps step rho (step x (bs_at rho i)) (i + 1, j),
      sup_acc step accept rho (step x (bs_at rho i)) (i + 1) j)"
      using q_def sup_acc_None[OF i_lt_j, of step accept rho]
        sup_acc_i[OF i_lt_j, of step accept rho] sup_acc_l[OF i_lt_j, of _ step accept rho]
      unfolding q_q'
      by (auto simp add: drop_cur_def split: option.splits)
  qed
  have valid_drop_cur: "\<And>x x'. x \<in> mmap_keys s \<Longrightarrow> x' \<in> mmap_keys s \<Longrightarrow>
    step x (bs_at rho i) = step x' (bs_at rho i) \<Longrightarrow> drop_cur i (the (mmap_lookup s x)) =
    drop_cur i (the (mmap_lookup s x'))"
    using drop_cur_i by auto
  then have keys_idem: "keys_idem step i b s"
    unfolding keys_idem_def b_def
    by blast
  have distinct: "distinct (map fst s)"
    using valid_before
    by (auto simp: valid_s_def)
  have "(\<lambda>q. step q (bs_at rho i)) ` {q. \<exists>l\<le>u. steps step rho init (l, i) = q} =
    {q. \<exists>l\<le>u. steps step rho init (l, i + 1) = q}"
    using steps_app[of _ i step rho init] u_le_i
    by auto
  then have keys_s': "mmap_keys s' = {q. \<exists>l\<le>u. steps step rho init (l, i + 1) = q}"
    using adv_d_keys[OF _ distinct adv_d] inv_st
    unfolding keys_s b_def
    by auto
  have lookup_s': "\<And>q q' tstp. mmap_lookup s' q = Some (q', tstp) \<Longrightarrow>
    steps step rho q (i + 1, j) = q' \<and> tstp = sup_acc step accept rho q (i + 1) j"
  proof -
    fix q q' tstp
    assume assm: "mmap_lookup s' q = Some (q', tstp)"
    obtain x where wit: "x \<in> mmap_keys s" "step x (bs_at rho i) = q"
      using assm lookup_adv_d_None[OF _ distinct adv_d] inv_st
      by (fastforce simp: b_def)
    have lookup_s'_q: "mmap_lookup s' q = Some (drop_cur i (the (mmap_lookup s x)))"
      using lookup_adv_d_Some[OF _ distinct keys_idem wit[folded b_def] adv_d] inv_st
      by auto
    then show "steps step rho q (i + 1, j) = q' \<and> tstp = sup_acc step accept rho q (i + 1) j"
      using assm
      by (simp add: drop_cur_i wit)
  qed
  have "distinct (map fst s')"
    using mmap_fold_distinct[OF distinct] adv_d_mmap_fold[OF inv_st adv_d[unfolded adv_d_def]]
    unfolding adv_d_def mmap_map_fst
    by auto
  then show "valid_s init step st' accept rho u (i + 1) j s'"
    unfolding valid_s_def
    using keys_s' lookup_s' u_le_i inv_st adv_d[unfolded adv_d_def]
      adv_d_mmap_fold[OF inv_st adv_d[unfolded adv_d_def]]
    by (auto split: option.splits dest: Mapping_keys_dest)
qed

lemma mmap_lookup_update':
  "mmap_lookup (mmap_update k v kvs) z = (if k = z then Some v else mmap_lookup kvs z)"
  unfolding mmap_lookup_def mmap_update_def
  by (auto simp add: update_conv')

lemma mmap_keys_update: "mmap_keys (mmap_update k v kvs) = mmap_keys kvs \<union> {k}"
  by (induction kvs) (auto simp: mmap_keys_def mmap_update_def)

lemma valid_adv_start:
  assumes "valid_window args t0 sub rho w" "w_i w < w_j w"
  shows "valid_window args t0 sub rho (adv_start args w)"
proof -
  define init where "init = w_init args"
  define step where "step = w_step args"
  define accept where "accept = w_accept args"
  define run_t where "run_t = w_run_t args"
  define run_sub where "run_sub = w_run_sub args"
  define st where "st = w_st w"
  define ac where "ac = w_ac w"
  define i where "i = w_i w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define j where "j = w_j w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "reach_window args t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "(\<And>q bs. case Mapping.lookup st (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v)"
    "(\<And>q bs. case Mapping.lookup ac q of None \<Rightarrow> True | Some v \<Rightarrow> accept q = v)"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q" "distinct (map fst e)"
    "valid_s init step st accept rho i i j s"
    using assms(1)
    unfolding valid_window_def valid_s_def Let_def init_def step_def accept_def run_t_def
        run_sub_def st_def ac_def i_def ti_def si_def j_def tj_def sj_def s_def e_def
    by auto
  have distinct_before: "distinct (map fst s)" "distinct (map fst e)"
    using valid_before
    by (auto simp: valid_s_def)
  note i_lt_j = assms(2)[folded i_def j_def]
  obtain ti' si' t b where tb_def: "run_t ti = Some (ti', t)"
    "run_sub si = Some (si', b)"
    "reaches_on run_t ti' (drop (Suc i) (map fst rho)) tj"
    "reaches_on run_sub si' (drop (Suc i) (map snd rho)) sj"
    "t = ts_at rho i" "b = bs_at rho i"
    using valid_before i_lt_j
    apply (auto simp: ts_at_def bs_at_def run_t_def[symmetric] run_sub_def[symmetric]
        elim!: reaches_on.cases[of run_t ti "drop i (map fst rho)" tj]
        reaches_on.cases[of run_sub si "drop i (map snd rho)" sj])
    by (metis Cons_nth_drop_Suc length_map list.inject nth_map)
  have reaches_on_si': "reaches_on run_sub sub (take (Suc i) (map snd rho)) si'"
    using valid_before tb_def(2,3,4) i_lt_j reaches_on_app tb_def(1)
    by (auto simp: run_sub_def sub_def bs_at_def take_Suc_conv_app_nth reaches_on_app tb_def(6))
  have reaches_on_ti': "reaches_on run_t t0 (take (Suc i) (map fst rho)) ti'"
    using valid_before tb_def(2,3,4) i_lt_j reaches_on_app tb_def(1)
    by (auto simp: run_t_def ts_at_def take_Suc_conv_app_nth reaches_on_app tb_def(5))
  define e' where "e' = mmap_update (fst (the (mmap_lookup s init))) t e"
  obtain st' s' where s'_def: "adv_d step st i b s = (s', st')"
    by (metis old.prod.exhaust)
  obtain st_cur ac_cur i_cur ti_cur si_cur q_cur s_cur tstp_cur where loop_def:
    "(st_cur, ac_cur, i_cur, ti_cur, si_cur, q_cur, s_cur, tstp_cur) =
      while (loop_cond j) (loop_body step accept run_t run_sub)
      (st', ac, Suc i, ti', si', init, s', None)"
    by (cases "while (loop_cond j) (loop_body step accept run_t run_sub)
        (st', ac, Suc i, ti', si', init, s', None)") auto
  define s'' where "s'' = mmap_update init (case mmap_lookup s_cur q_cur of
    Some (q', tstp') \<Rightarrow> (case tstp' of Some (ts, tp) \<Rightarrow> (q', tstp') | None \<Rightarrow> (q', tstp_cur))
    | None \<Rightarrow> (q_cur, tstp_cur)) s'"
  have i_le_j: "i \<le> j"
    using i_lt_j by auto
  have length_rho: "length rho = j"
    using valid_before by auto
  have lookup_s: "\<And>q q' tstp. mmap_lookup s q = Some (q', tstp) \<Longrightarrow>
    steps step rho q (i, j) = q' \<and> tstp = sup_acc step accept rho q i j"
    using valid_before Mapping_keys_intro
    by (auto simp: valid_s_def) (smt case_prodD option.simps(5))+
  have init_in_keys_s: "init \<in> mmap_keys s"
    using valid_before by (auto simp add: valid_s_def)
  then have run_init_i_j: "steps step rho init (i, j) = fst (the (mmap_lookup s init))"
    using lookup_s by (auto dest: Mapping_keys_dest)
  have lookup_e: "\<And>q. mmap_lookup e q = sup_leadsto init step rho i j q"
    using valid_before by auto
  have lookup_e': "\<And>q. mmap_lookup e' q = sup_leadsto init step rho (i + 1) j q"
  proof -
    fix q
    show "mmap_lookup e' q = sup_leadsto init step rho (i + 1) j q"
    proof (cases "steps step rho init (i, j) = q")
      case True
      have "Max {l. l < Suc i \<and> steps step rho init (l, j) = steps step rho init (i, j)} = i"
        by (rule iffD2[OF Max_eq_iff]) auto
      then have "sup_leadsto init step rho (i + 1) j q = Some (ts_at rho i)"
        by (auto simp add: sup_leadsto_def True)
      then show ?thesis
        unfolding e'_def using run_init_i_j tb_def
        by (auto simp add: mmap_lookup_update' True)
    next
      case False
      show ?thesis
        using run_init_i_j sup_leadsto_idle[OF i_lt_j False] lookup_e[of q] False
        by (auto simp add: e'_def mmap_lookup_update')
    qed
  qed
  have reach_split: "{q. \<exists>l\<le>i + 1. steps step rho init (l, i + 1) = q} =
    {q. \<exists>l\<le>i. steps step rho init (l, i + 1) = q} \<union> {init}"
    using le_Suc_eq by auto
  have valid_s_i: "valid_s init step st accept rho i i j s"
    using valid_before by auto
  have valid_s'_Suc_i: "valid_s init step st' accept rho i (i + 1) j s'"
    using valid_adv_d[OF valid_s_i order.refl i_lt_j, OF tb_def(6) s'_def] unfolding s'_def .
  have loop: "loop_inv init step accept args t0 sub rho i j tj sj
    (st_cur, ac_cur, i_cur, ti_cur, si_cur, q_cur, s_cur, tstp_cur) \<and>
    \<not>loop_cond j (st_cur, ac_cur, i_cur, ti_cur, si_cur, q_cur, s_cur, tstp_cur)"
    unfolding loop_def
  proof (rule while_rule_lemma[of "loop_inv init step accept args t0 sub rho i j tj sj"
        "loop_cond j" "loop_body step accept run_t run_sub"
        "\<lambda>s. loop_inv init step accept args t0 sub rho i j tj sj s \<and> \<not> loop_cond j s"])
    show "loop_inv init step accept args t0 sub rho i j tj sj
      (st', ac, Suc i, ti', si', init, s', None)"
      unfolding loop_inv_def
      using i_lt_j valid_s'_Suc_i sup_acc_same[of step accept rho]
        length_rho reaches_on_si' reaches_on_ti' tb_def(3,4) valid_before(4)
      by (auto simp: run_t_def run_sub_def split: prod.splits)
  next
    have "{(t, s). loop_inv init step accept args t0 sub rho i j tj sj s \<and>
      loop_cond j s \<and> t = loop_body step accept run_t run_sub s} \<subseteq>
      measure (\<lambda>(st, ac, i_cur, ti, si, q, s, tstp). j - i_cur)"
      unfolding loop_inv_def loop_cond_def loop_body_def
      apply (auto simp: run_t_def run_sub_def split: option.splits)
      apply (metis drop_eq_Nil length_map not_less option.distinct(1) reaches_on.simps)
      apply (metis (no_types, lifting) drop_eq_Nil length_map not_less option.distinct(1)
          reaches_on.simps)
      apply (auto split: prod.splits)
      done
    then show "wf {(t, s). loop_inv init step accept args t0 sub rho i j tj sj s \<and>
      loop_cond j s \<and> t = loop_body step accept run_t run_sub s}"
      using wf_measure wf_subset by auto
  next
    fix state
    assume assms: "loop_inv init step accept args t0 sub rho i j tj sj state"
      "loop_cond j state"
    obtain st_cur ac_cur i_cur ti_cur si_cur q_cur s_cur tstp_cur
      where state_def: "state = (st_cur, ac_cur, i_cur, ti_cur, si_cur, q_cur, s_cur, tstp_cur)"
      by (cases state) auto
    obtain ti'_cur si'_cur t_cur b_cur where tb_cur_def: "run_t ti_cur = Some (ti'_cur, t_cur)"
      "run_sub si_cur = Some (si'_cur, b_cur)"
      "reaches_on run_t ti'_cur (drop (Suc i_cur) (map fst rho)) tj"
      "reaches_on run_sub si'_cur (drop (Suc i_cur) (map snd rho)) sj"
      "t_cur = ts_at rho i_cur" "b_cur = bs_at rho i_cur"
      using assms
      unfolding loop_inv_def loop_cond_def state_def
      apply (auto simp: ts_at_def bs_at_def run_t_def[symmetric] run_sub_def[symmetric]
          elim!: reaches_on.cases[of run_t ti_cur "drop i_cur (map fst rho)" tj]
          reaches_on.cases[of run_sub si_cur "drop i_cur (map snd rho)" sj])
      by (metis Cons_nth_drop_Suc length_map list.inject nth_map)
    obtain s'_cur st'_cur where s'_cur_def: "adv_d step st_cur i_cur b_cur s_cur =
      (s'_cur, st'_cur)"
      by fastforce
    have valid_s'_cur: "valid_s init step st'_cur accept rho i (i_cur + 1) j s'_cur"
      using assms valid_adv_d[of init step st_cur accept rho] tb_cur_def(6) s'_cur_def
      unfolding loop_inv_def loop_cond_def state_def
      by auto
    obtain q' st''_cur where q'_def: "cstep step st'_cur q_cur b_cur = (q', st''_cur)"
      by fastforce
    obtain \<beta> ac'_cur where b_def: "cac accept ac_cur q' = (\<beta>, ac'_cur)"
      by fastforce
    have step: "q' = step q_cur b_cur" "\<And>q bs. case Mapping.lookup st''_cur (q, bs) of
      None \<Rightarrow> True | Some v \<Rightarrow> step q bs = v"
      using valid_s'_cur q'_def
      unfolding valid_s_def
      by (auto simp: cstep_def Let_def Mapping.lookup_update' split: option.splits if_splits)
    have accept: "\<beta> = accept q'" "\<And>q. case Mapping.lookup ac'_cur q of
      None \<Rightarrow> True | Some v \<Rightarrow> accept q = v"
      using assms b_def
      unfolding loop_inv_def state_def
      by (auto simp: cac_def Let_def Mapping.lookup_update' split: option.splits if_splits)
    have steps_q': "steps step rho init (i + 1, Suc i_cur) = q'"
      using assms
      unfolding loop_inv_def state_def
      by auto (metis local.step(1) steps_appE tb_cur_def(6))
    have b_acc: "\<beta> = acc step accept rho init (i + 1, Suc i_cur)"
      unfolding accept(1) acc_def steps_q'
      by (auto simp: tb_cur_def)
    have valid_s''_cur: "valid_s init step st''_cur accept rho i (i_cur + 1) j s'_cur"
      using valid_s'_cur step(2)
      unfolding valid_s_def
      by auto
    have reaches_on_si': "reaches_on run_sub sub (take (Suc i_cur) (map snd rho)) si'_cur"
      using assms
      unfolding loop_inv_def loop_cond_def state_def
      by (auto simp: run_sub_def sub_def bs_at_def take_Suc_conv_app_nth reaches_on_app
          tb_cur_def(2,4,6))
         (metis bs_at_def reaches_on_app run_sub_def tb_cur_def(2) tb_cur_def(6))
    have reaches_on_ti': "reaches_on run_t t0 (take (Suc i_cur) (map fst rho)) ti'_cur"
      using assms
      unfolding loop_inv_def loop_cond_def state_def
      by (auto simp: run_t_def ts_at_def take_Suc_conv_app_nth reaches_on_app tb_cur_def(1,3,5))
         (metis reaches_on_app run_t_def tb_cur_def(1) tb_cur_def(5) ts_at_def)
    have "reach_window args t0 sub rho (Suc i_cur, ti'_cur, si'_cur, j, tj, sj)"
      using reaches_on_si' reaches_on_ti' tb_cur_def(3,4) length_rho assms(2)
      unfolding loop_cond_def state_def
      by (auto simp: run_t_def run_sub_def)
    moreover have "steps step rho init (i + 1, Suc i_cur) = q'"
      using assms steps_app
      unfolding loop_inv_def state_def step(1)
      by (auto simp: tb_cur_def(6))
    ultimately show "loop_inv init step accept args t0 sub rho i j tj sj
      (loop_body step accept run_t run_sub state)"
      using assms accept(2) valid_s''_cur sup_acc_ext[of _ _ step accept rho]
        sup_acc_ext_idle[of _ _ step accept rho]
      unfolding loop_inv_def loop_body_def state_def
      by (auto simp: tb_cur_def(1,2,5) s'_cur_def q'_def b_def b_acc
          split: option.splits prod.splits)
  qed auto
  have valid_stac_cur: "\<forall>q bs. case Mapping.lookup st_cur (q, bs) of None \<Rightarrow> True
    | Some v \<Rightarrow> step q bs = v" "\<forall>q. case Mapping.lookup ac_cur q of None \<Rightarrow> True
    | Some v \<Rightarrow> accept q = v"
    using loop unfolding loop_inv_def valid_s_def
    by auto
  have valid_s'': "valid_s init step st_cur accept rho (i + 1) (i + 1) j s''"
  proof (cases "mmap_lookup s_cur q_cur")
    case None
    then have added: "steps step rho init (i + 1, j) = q_cur"
      "tstp_cur = sup_acc step accept rho init (i + 1) j"
      using loop unfolding loop_inv_def loop_cond_def
      by (auto dest: Mapping_keys_dest)
    have s''_case: "s'' = mmap_update init (q_cur, tstp_cur) s'"
      unfolding s''_def using None by auto
    show ?thesis
      using valid_s'_Suc_i reach_split added mmap_update_distinct valid_stac_cur
      unfolding s''_case valid_s_def mmap_keys_update
      by (auto simp add: mmap_lookup_update' split: option.splits)
  next
    case (Some p)
    obtain q' tstp' where p_def: "p = (q', tstp')"
      by (cases p) auto
    note lookup_s_cur = Some[unfolded p_def]
    have i_cur_in: "i + 1 \<le> i_cur" "i_cur \<le> j"
      using loop unfolding loop_inv_def by auto
    have q_cur_def: "steps step rho init (i + 1, i_cur) = q_cur"
      using loop unfolding loop_inv_def by auto
    have valid_s_cur: "valid_s init step st_cur accept rho i i_cur j s_cur"
      using loop unfolding loop_inv_def by auto
    have q'_steps: "steps step rho q_cur (i_cur, j) = q'"
      using Some valid_s_cur unfolding valid_s_def p_def
      by (auto intro: Mapping_keys_intro) (smt case_prodD option.simps(5))
    have tstp_cur: "tstp_cur = sup_acc step accept rho init (i + 1) i_cur"
      using loop unfolding loop_inv_def by auto
    have tstp': "tstp' = sup_acc step accept rho q_cur i_cur j"
      using loop Some unfolding loop_inv_def p_def valid_s_def
      by (auto intro: Mapping_keys_intro) (smt case_prodD option.simps(5))
    have added: "steps step rho init (i + 1, j) = q'"
      using steps_comp[OF i_cur_in q_cur_def q'_steps] .
    show ?thesis
    proof (cases tstp')
      case None
      have s''_case: "s'' = mmap_update init (q', tstp_cur) s'"
        unfolding s''_def lookup_s_cur None by auto
      have tstp_cur_opt: "tstp_cur = sup_acc step accept rho init (i + 1) j"
        using sup_acc_comp_None[OF i_cur_in, of step accept rho init, unfolded q_cur_def,
            OF tstp'[unfolded None, symmetric]]
        unfolding tstp_cur by auto
      then show ?thesis
        using valid_s'_Suc_i reach_split added mmap_update_distinct valid_stac_cur
        unfolding s''_case valid_s_def mmap_keys_update
        by (auto simp add: mmap_lookup_update' split: option.splits)
    next
      case (Some p')
      obtain ts tp where p'_def: "p' = (ts, tp)"
        by (cases p') auto
      have True: "tp \<ge> i_cur"
        using sup_acc_SomeE[OF tstp'[unfolded Some p'_def, symmetric]] by auto
      have s''_case: "s'' = mmap_update init (q', tstp') s'"
        unfolding s''_def lookup_s_cur Some p'_def using True by auto
      have tstp'_opt: "tstp' = sup_acc step accept rho init (i + 1) j"
        using sup_acc_comp_Some_ge[OF i_cur_in True
            tstp'[unfolded Some p'_def q_cur_def[symmetric], symmetric]]
        unfolding tstp' by (auto simp: q_cur_def[symmetric])
      then show ?thesis
        using valid_s'_Suc_i reach_split added mmap_update_distinct valid_stac_cur
        unfolding s''_case valid_s_def mmap_keys_update
        by (auto simp add: mmap_lookup_update' split: option.splits)
    qed
  qed
  have "distinct (map fst e')"
    using mmap_update_distinct[OF distinct_before(2), unfolded e'_def]
    unfolding e'_def .
  then have "valid_window args t0 sub rho
    (w\<lparr>w_st := st_cur, w_ac := ac_cur, w_i := Suc i, w_ti := ti', w_si := si', w_s := s'', w_e := e'\<rparr>)"
    using i_lt_j lookup_e' valid_s'' length_rho tb_def(3,4) reaches_on_si' reaches_on_ti'
      valid_before[unfolded step_def accept_def] valid_stac_cur(2)[unfolded accept_def]
    by (auto simp: valid_window_def Let_def init_def step_def accept_def run_t_def
        run_sub_def st_def ac_def i_def ti_def si_def j_def tj_def sj_def s_def e_def)
  moreover have "adv_start args w = w\<lparr>w_st := st_cur, w_ac := ac_cur, w_i := Suc i,
    w_ti := ti', w_si := si', w_s := s'', w_e := e'\<rparr>"
    unfolding adv_start_def Let_def s''_def e'_def
    using tb_def(1,2) s'_def i_lt_j loop_def valid_before(3)
    by (auto simp: valid_window_def Let_def init_def step_def accept_def run_t_def
        run_sub_def st_def ac_def i_def ti_def si_def j_def tj_def sj_def s_def e_def
        split: prod.splits)
  ultimately show ?thesis
    by auto
qed

lemma valid_adv_start_bounds:
  assumes "valid_window args t0 sub rho w" "w_i w < w_j w"
  shows "w_i (adv_start args w) = Suc (w_i w)" "w_j (adv_start args w) = w_j w"
    "w_tj (adv_start args w) = w_tj w" "w_sj (adv_start args w) = w_sj w"
  using assms
  by (auto simp: adv_start_def Let_def valid_window_def split: option.splits prod.splits
      elim: reaches_on.cases)

lemma valid_adv_start_bounds':
  assumes "valid_window args t0 sub rho w" "w_run_t args (w_ti w) = Some (ti', t)"
    "w_run_sub args (w_si w) = Some (si', bs)"
  shows "w_ti (adv_start args w) = ti'" "w_si (adv_start args w) = si'"
  using assms
  by (auto simp: adv_start_def Let_def valid_window_def split: option.splits prod.splits)

end
