theory Monitor
  imports MDL Temporal
begin

type_synonym ('h, 't) time = "('h \<times> 't) option"

datatype (dead 'a, dead 't :: timestamp, dead 'h) vydra_aux =
    VYDRA_None
  | VYDRA_Bool bool 'h
  | VYDRA_Atom 'a 'h
  | VYDRA_Neg "('a, 't, 'h) vydra_aux"
  | VYDRA_Bin "bool \<Rightarrow> bool \<Rightarrow> bool" "('a, 't, 'h) vydra_aux" "('a, 't, 'h) vydra_aux"
  | VYDRA_Prev "'t \<I>" "('a, 't, 'h) vydra_aux" 'h "('t \<times> bool) option"
  | VYDRA_Next "'t \<I>" "('a, 't, 'h) vydra_aux" 'h "'t option"
  | VYDRA_Since "'t \<I>" "('a, 't, 'h) vydra_aux" "('a, 't, 'h) vydra_aux" "('h, 't) time" nat nat "nat option" "'t option"
  | VYDRA_Until "'t \<I>" "('h, 't) time" "('a, 't, 'h) vydra_aux" "('a, 't, 'h) vydra_aux" "('h, 't) time" nat "('t \<times> bool \<times> bool) option"
  | VYDRA_MatchP "'t \<I>" "transition iarray" nat
    "(bool iarray, nat set, 't, ('h, 't) time, ('a, 't, 'h) vydra_aux list) window"
  | VYDRA_MatchF "'t \<I>" "transition iarray" nat
    "(bool iarray, nat set, 't, ('h, 't) time, ('a, 't, 'h) vydra_aux list) window"

type_synonym ('a, 't, 'h) vydra = "nat \<times> ('a, 't, 'h) vydra_aux"

fun msize_vydra :: "nat \<Rightarrow> ('a, 't :: timestamp, 'h) vydra_aux \<Rightarrow> nat" where
  "msize_vydra n VYDRA_None = 0"
| "msize_vydra n (VYDRA_Bool b e) = 0"
| "msize_vydra n (VYDRA_Atom a e) = 0"
| "msize_vydra (Suc n) (VYDRA_Bin f v1 v2) = msize_vydra n v1 + msize_vydra n v2 + 1"
| "msize_vydra (Suc n) (VYDRA_Neg v) = msize_vydra n v + 1"
| "msize_vydra (Suc n) (VYDRA_Prev I v e tb) = msize_vydra n v + 1"
| "msize_vydra (Suc n) (VYDRA_Next I v e to) = msize_vydra n v + 1"
| "msize_vydra (Suc n) (VYDRA_Since I vphi vpsi e cphi cpsi cppsi tppsi) = msize_vydra n vphi + msize_vydra n vpsi + 1"
| "msize_vydra (Suc n) (VYDRA_Until I e vphi vpsi epsi c zo) = msize_vydra n vphi + msize_vydra n vpsi + 1"
| "msize_vydra (Suc n) (VYDRA_MatchP I transs qf w) = size_list (msize_vydra n) (w_si w) + size_list (msize_vydra n) (w_sj w) + 1"
| "msize_vydra (Suc n) (VYDRA_MatchF I transs qf w) = size_list (msize_vydra n) (w_si w) + size_list (msize_vydra n) (w_sj w) + 1"
| "msize_vydra _ _ = 0"

fun next_vydra :: "('a, 't :: timestamp, 'h) vydra_aux \<Rightarrow> nat" where
  "next_vydra (VYDRA_Next I v e None) = 1"
| "next_vydra _ = 0"

context
  fixes init_hd :: "'h"
    and run_hd :: "'h \<Rightarrow> ('h \<times> ('t :: timestamp \<times> 'a set)) option"
begin

definition t0 :: "('h, 't) time" where
  "t0 = (case run_hd init_hd of None \<Rightarrow> None | Some (e', (t, X)) \<Rightarrow> Some (e', t))"

fun run_t :: "('h, 't) time \<Rightarrow> (('h, 't) time \<times> 't) option" where
  "run_t None = None"
| "run_t (Some (e, t)) = (case run_hd e of None \<Rightarrow> Some (None, t)
  | Some (e', (t', X)) \<Rightarrow> Some (Some (e', t'), t))"

fun read_t :: "('h, 't) time \<Rightarrow> 't option" where
  "read_t None = None"
| "read_t (Some (e, t)) = Some t"

lemma run_t_read: "run_t x = Some (x', t) \<Longrightarrow> read_t x = Some t"
  by (cases x) (auto split: option.splits)

lemma read_t_run: "read_t x = Some t \<Longrightarrow> \<exists>x'. run_t x = Some (x', t)"
  by (cases x) (auto split: option.splits)

lemma reach_event_t: "reaches_on run_hd e vs e'' \<Longrightarrow> run_hd e = Some (e', (t, X)) \<Longrightarrow>
  run_hd e'' = Some (e''', (t', X')) \<Longrightarrow>
  reaches_on run_t (Some (e', t)) (map fst vs) (Some (e''', t'))"
proof (induction e vs e'' arbitrary: t' X' e''' rule: reaches_on_rev_induct)
  case (2 s s' v vs s'')
  obtain v_t v_X where v_def: "v = (v_t, v_X)"
    by (cases v) auto
  have run_t_s'': "run_t (Some (s'', v_t)) = Some (Some (e''', t'), v_t)"
    by (auto simp: 2(5))
  show ?case
    using reaches_on_app[OF 2(3)[OF 2(4) 2(2)[unfolded v_def]] run_t_s'']
    by (auto simp: v_def)
qed (auto intro: reaches_on.intros)

lemma reach_event_t0_t:
  assumes "reaches_on run_hd init_hd vs e''" "run_hd e'' = Some (e''', (t', X'))"
  shows "reaches_on run_t t0 (map fst vs) (Some (e''', t'))"
proof -
  have t0_not_None: "t0 \<noteq> None"
    apply (rule reaches_on.cases[OF assms(1)])
    using assms(2)
    by (auto simp: t0_def split: option.splits prod.splits)
  then show ?thesis
    using reach_event_t[OF assms(1) _ assms(2)]
    by (auto simp: t0_def split: option.splits)
qed

lemma reaches_on_run_hd_t:
  assumes "reaches_on run_hd init_hd vs e"
  shows "\<exists>x. reaches_on run_t t0 (map fst vs) x"
proof (cases vs rule: rev_cases)
  case (snoc ys y)
  show ?thesis
    using assms
    apply (cases y)
    apply (auto simp: snoc dest!: reaches_on_split_last)
    apply (meson reaches_on_app[OF reach_event_t0_t] read_t.simps(2) read_t_run)
    done
qed (auto intro: reaches_on.intros)

definition "run_subs run = (\<lambda>vs. let vs' = map run vs in
  (if (\<exists>x \<in> set vs'. Option.is_none x) then None
   else Some (map (fst \<circ> the) vs', iarray_of_list (map (snd \<circ> snd \<circ> the) vs'))))"

lemma run_subs_lD: "run_subs run vs = Some (vs', bs) \<Longrightarrow>
  length vs' = length vs \<and> IArray.length bs = length vs"
  by (auto simp: run_subs_def Let_def iarray_of_list_def split: option.splits if_splits)

lemma run_subs_vD: "run_subs run vs = Some (vs', bs) \<Longrightarrow> j < length vs \<Longrightarrow>
  \<exists>vj' tj bj. run (vs ! j) = Some (vj', (tj, bj)) \<and> vs' ! j = vj' \<and> IArray.sub bs j = bj"
  apply (cases "run (vs ! j)")
   apply (auto simp: Option.is_none_def run_subs_def Let_def iarray_of_list_def
      split: option.splits if_splits)
  by (metis image_eqI nth_mem)

fun msize_fmla :: "('a, 'b :: timestamp) formula \<Rightarrow> nat"
  and msize_regex :: "('a, 'b) regex \<Rightarrow> nat" where
  "msize_fmla (Bool b) = 0"
| "msize_fmla (Atom a) = 0"
| "msize_fmla (Neg phi) = Suc (msize_fmla phi)"
| "msize_fmla (Bin f phi psi) = Suc (msize_fmla phi + msize_fmla psi)"
| "msize_fmla (Prev I phi) = Suc (msize_fmla phi)"
| "msize_fmla (Next I phi) = Suc (msize_fmla phi)"
| "msize_fmla (Since phi I psi) = Suc (max (msize_fmla phi) (msize_fmla psi))"
| "msize_fmla (Until phi I psi) = Suc (max (msize_fmla phi) (msize_fmla psi))"
| "msize_fmla (MatchP I r) = Suc (msize_regex r)"
| "msize_fmla (MatchF I r) = Suc (msize_regex r)"
| "msize_regex (Lookahead phi) = msize_fmla phi"
| "msize_regex (Symbol phi) = msize_fmla phi"
| "msize_regex (Plus r s) = max (msize_regex r) (msize_regex s)"
| "msize_regex (Times r s) = max (msize_regex r) (msize_regex s)"
| "msize_regex (Star r) = msize_regex r"

lemma collect_subfmlas_msize: "x \<in> set (collect_subfmlas r []) \<Longrightarrow>
  msize_fmla x \<le> msize_regex r"
proof (induction r)
  case (Lookahead phi)
  then show ?case
    by (auto split: if_splits)
next
  case (Symbol phi)
  then show ?case
    by (auto split: if_splits)
next
  case (Plus r1 r2)
  then show ?case
    by (auto simp: collect_subfmlas_set[of r2 "collect_subfmlas r1 []"])
next
  case (Times r1 r2)
  then show ?case
    by (auto simp: collect_subfmlas_set[of r2 "collect_subfmlas r1 []"])
next
  case (Star r)
  then show ?case
    by fastforce
qed

definition "until_ready I t c zo = (case (c, zo) of (Suc _, Some (t', b1, b2)) \<Rightarrow> (b2 \<and> memL t t' I) \<or> \<not>b1 | _ \<Rightarrow> False)"

definition "while_since_cond I t = (\<lambda>(vpsi, e, cpsi :: nat, cppsi, tppsi). cpsi > 0 \<and> memL (the (read_t e)) t I)"
definition "while_since_body run =
  (\<lambda>(vpsi, e, cpsi :: nat, cppsi, tppsi).
    case run vpsi of Some (vpsi', (t', b')) \<Rightarrow>
      Some (vpsi', fst (the (run_t e)), cpsi - 1, if b' then Some cpsi else cppsi, if b' then Some t' else tppsi)
      | _ \<Rightarrow> None
    )"

definition "while_until_cond I t = (\<lambda>(vphi, vpsi, epsi, c, zo). \<not>until_ready I t c zo \<and> (case read_t epsi of Some t' \<Rightarrow> memR t t' I | None \<Rightarrow> False))"
definition "while_until_body run =
  (\<lambda>(vphi, vpsi, epsi, c, zo). case run_t epsi of Some (epsi', t') \<Rightarrow>
    (case run vphi of Some (vphi', (_, b1)) \<Rightarrow>
      (case run vpsi of Some (vpsi', (_, b2)) \<Rightarrow> Some (vphi', vpsi', epsi', Suc c, Some (t', b1, b2))
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None))"

function (sequential) run :: "nat \<Rightarrow> ('a, 't, 'h) vydra_aux \<Rightarrow> (('a, 't, 'h) vydra_aux \<times> ('t \<times> bool)) option" where
  "run n (VYDRA_None) = None"
| "run n (VYDRA_Bool b e) = (case run_hd e of None \<Rightarrow> None
    | Some (e', (t, _)) \<Rightarrow> Some (VYDRA_Bool b e', (t, b)))"
| "run n (VYDRA_Atom a e) = (case run_hd e of None \<Rightarrow> None
    | Some (e', (t, X)) \<Rightarrow> Some (VYDRA_Atom a e', (t, a \<in> X)))"
| "run (Suc n) (VYDRA_Neg v) = (case run n v of None \<Rightarrow> None
    | Some (v', (t, b)) \<Rightarrow> Some (VYDRA_Neg v', (t, \<not>b)))"
| "run (Suc n) (VYDRA_Bin f vl vr) = (case run n vl of None \<Rightarrow> None
    | Some (vl', (t, bl)) \<Rightarrow> (case run n vr of None \<Rightarrow> None
    | Some (vr', (_, br)) \<Rightarrow> Some (VYDRA_Bin f vl' vr', (t, f bl br))))"
| "run (Suc n) (VYDRA_Prev I v e tb) = (case run_hd e of Some (e', (t, _)) \<Rightarrow>
        (let \<beta> = (case tb of Some (t', b') \<Rightarrow> b' \<and> mem t' t I | None \<Rightarrow> False) in
        case run n v of Some (v', _, b') \<Rightarrow> Some (VYDRA_Prev I v' e' (Some (t, b')), (t, \<beta>))
        | None \<Rightarrow> Some (VYDRA_None, (t, \<beta>)))
    | None \<Rightarrow> None)"
| "run (Suc n) (VYDRA_Next I v e to) = (case run_hd e of Some (e', (t, _)) \<Rightarrow>
    (case to of None \<Rightarrow>
      (case run n v of Some (v', _, _) \<Rightarrow> run (Suc n) (VYDRA_Next I v' e' (Some t))
      | None \<Rightarrow> None)
    | Some t' \<Rightarrow>
      (case run n v of Some (v', _, b) \<Rightarrow> Some (VYDRA_Next I v' e' (Some t), (t', b \<and> mem t' t I))
      | None \<Rightarrow> if mem t' t I then None else Some (VYDRA_None, (t', False))))
    | None \<Rightarrow> None)"
| "run (Suc n) (VYDRA_Since I vphi vpsi e cphi cpsi cppsi tppsi) = (case run n vphi of
    Some (vphi', (t, b1)) \<Rightarrow>
      let cphi = (if b1 then Suc cphi else 0) in
      let cpsi = Suc cpsi in
      let cppsi = map_option Suc cppsi in
      (case while_break (while_since_cond I t) (while_since_body (run n)) (vpsi, e, cpsi, cppsi, tppsi) of Some (vpsi', e', cpsi', cppsi', tppsi') \<Rightarrow>
        (let \<beta> = (case cppsi' of Some k \<Rightarrow> k - 1 \<le> cphi \<and> memR (the tppsi') t I | _ \<Rightarrow> False) in
         Some (VYDRA_Since I vphi' vpsi' e' cphi cpsi' cppsi' tppsi', (t, \<beta>)))
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
| "run (Suc n) (VYDRA_Until I e vphi vpsi epsi c zo) = (case run_t e of Some (e', t) \<Rightarrow>
      (case while_break (while_until_cond I t) (while_until_body (run n)) (vphi, vpsi, epsi, c, zo) of Some (vphi', vpsi', epsi', c', zo') \<Rightarrow>
        if c' = 0 then None else
        (case zo' of Some (t', b1, b2) \<Rightarrow>
          (if b2 \<and> memL t t' I then Some (VYDRA_Until I e' vphi' vpsi' epsi' (c' - 1) zo', (t, True))
          else if \<not>b1 then Some (VYDRA_Until I e' vphi' vpsi' epsi' (c' - 1) zo', (t, False))
          else (case read_t epsi' of Some t' \<Rightarrow> Some (VYDRA_Until I e' vphi' vpsi' epsi' (c' - 1) zo', (t, False)) | _ \<Rightarrow> None))
        | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
| "run (Suc n) (VYDRA_MatchP I transs qf w) =
    (case eval_matchP (init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n))) I w of None \<Rightarrow> None
    | Some ((t, b), w') \<Rightarrow> Some (VYDRA_MatchP I transs qf w', (t, b)))"
| "run (Suc n) (VYDRA_MatchF I transs qf w) =
    (case eval_matchF (init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n))) I w of None \<Rightarrow> None
    | Some ((t, b), w') \<Rightarrow> Some (VYDRA_MatchF I transs qf w', (t, b)))"
| "run _ _ = undefined"
  by pat_completeness auto
termination
  by (relation "(\<lambda>p. size (fst p)) <*mlex*> (\<lambda>p. next_vydra (snd p)) <*mlex*> (\<lambda>p. msize_vydra (fst p) (snd p)) <*mlex*> {}") (auto simp: mlex_prod_def)

lemma wf_since: "wf {(t, s). while_since_cond I tt s \<and> Some t = while_since_body (run n) s}"
proof -
  let ?X = "{(t, s). while_since_cond I tt s \<and> Some t = while_since_body (run n) s}"
  have sub: "?X \<subseteq> measure (\<lambda>(vpsi, e, cpsi, cppsi, tppsi). cpsi)"
    by (auto simp: while_since_cond_def while_since_body_def Let_def split: option.splits)
  then show ?thesis
    using wf_subset[OF wf_measure]
    by auto
qed

definition run_vydra :: "('a, 't, 'h) vydra \<Rightarrow> (('a, 't, 'h) vydra \<times> ('t \<times> bool)) option" where
  "run_vydra v = (case v of (n, w) \<Rightarrow> map_option (apfst (Pair n)) (run n w))"

fun sub :: "nat \<Rightarrow> ('a, 't) formula \<Rightarrow> ('a, 't, 'h) vydra_aux" where
  "sub n (Bool b) = VYDRA_Bool b init_hd"
| "sub n (Atom a) = VYDRA_Atom a init_hd"
| "sub (Suc n) (Neg phi) = VYDRA_Neg (sub n phi)"
| "sub (Suc n) (Bin f phi psi) = VYDRA_Bin f (sub n phi) (sub n psi)"
| "sub (Suc n) (Prev I phi) = VYDRA_Prev I (sub n phi) init_hd None"
| "sub (Suc n) (Next I phi) = VYDRA_Next I (sub n phi) init_hd None"
| "sub (Suc n) (Since phi I psi) = VYDRA_Since I (sub n phi) (sub n psi) t0 0 0 None None"
| "sub (Suc n) (Until phi I psi) = VYDRA_Until I t0 (sub n phi) (sub n psi) t0 0 None"
| "sub (Suc n) (MatchP I r) = (let qf = state_cnt r;
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) in
    VYDRA_MatchP I transs qf (init_window (init_args
      ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n)))
      t0 (map (sub n) (collect_subfmlas r []))))"
| "sub (Suc n) (MatchF I r) = (let qf = state_cnt r;
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) in
    VYDRA_MatchF I transs qf (init_window (init_args
      ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n)))
      t0 (map (sub n) (collect_subfmlas r []))))"
| "sub _ _ = undefined"

definition init_vydra :: "('a, 't) formula \<Rightarrow> ('a, 't, 'h) vydra" where
  "init_vydra \<phi> = (let n = msize_fmla \<phi> in (n, sub n \<phi>))"

end

locale VYDRA_MDL = MDL \<sigma>
  for \<sigma> :: "('a, 't :: timestamp) trace" +
  fixes init_hd :: "'h"
    and run_hd :: "'h \<Rightarrow> ('h \<times> ('t \<times> 'a set)) option"
  assumes run_hd_sound: "reaches run_hd init_hd n s \<Longrightarrow> run_hd s = Some (s', (t, X)) \<Longrightarrow> (t, X) = (\<tau> \<sigma> n, \<Gamma> \<sigma> n)"
begin

lemma reaches_on_run_hd: "reaches_on run_hd init_hd es s \<Longrightarrow> run_hd s = Some (s', (t, X)) \<Longrightarrow> t = \<tau> \<sigma> (length es) \<and> X = \<Gamma> \<sigma> (length es)"
  using run_hd_sound
  by (auto dest: reaches_on_n)

abbreviation "ru_t \<equiv> run_t run_hd"
abbreviation "l_t0 \<equiv> t0 init_hd run_hd"
abbreviation "ru \<equiv> run run_hd"
abbreviation "su \<equiv> sub init_hd run_hd"

lemma ru_t_event: "reaches_on ru_t t ts t' \<Longrightarrow> t = l_t0 \<Longrightarrow> ru_t t' = Some (t'', x) \<Longrightarrow>
  \<exists>rho e tt. t' = Some (e, tt) \<and> reaches_on run_hd init_hd rho e \<and> length rho = Suc (length ts) \<and>
  x = \<tau> \<sigma> (length ts)"
proof (induction t ts t' arbitrary: t'' x rule: reaches_on_rev_induct)
  case (1 s)
  show ?case
    using 1 reaches_on_run_hd[OF reaches_on.intros(1)]
    by (auto simp: t0_def split: option.splits intro!: reaches_on.intros)
next
  case (2 s s' v vs s'')
  obtain rho e tt where rho_def: "s' = Some (e, tt)" "reaches_on run_hd init_hd rho e"
    "length rho = Suc (length vs)"
    using 2(3)[OF 2(4,2)]
    by auto
  then show ?case
    using 2(2,5) reaches_on_app[OF rho_def(2)] reaches_on_run_hd[OF rho_def(2)]
    by (fastforce split: option.splits)
qed

lemma ru_t_tau: "reaches_on ru_t l_t0 ts t' \<Longrightarrow> ru_t t' = Some (t'', x) \<Longrightarrow> x = \<tau> \<sigma> (length ts)"
  using ru_t_event
  by fastforce

lemma ru_t_Some_tau:
  assumes "reaches_on ru_t l_t0 ts (Some (e, t))"
  shows "t = \<tau> \<sigma> (length ts)"
proof -
  obtain z where z_def: "ru_t (Some (e, t)) = Some (z, t)"
    by (cases "run_hd e") auto
  show ?thesis
    by (rule ru_t_tau[OF assms z_def])
qed

lemma ru_t_tau_in:
  assumes "reaches_on ru_t l_t0 ts t" "j < length ts"
  shows "ts ! j = \<tau> \<sigma> j"
proof -
  obtain t' where t'_def: "reaches_on ru_t l_t0 (take j ts) t'" "reaches_on ru_t t' (drop j ts) t"
    using reaches_on_split'[OF assms(1), where ?i=j] assms(2)
    by auto
  have drop: "drop j ts = ts ! j # tl (drop j ts)"
    using assms(2)
    by (cases "drop j ts") (auto simp add: nth_via_drop)
  obtain t'' where t''_def: "ru_t t' = Some (t'', ts ! j)"
    using t'_def(2) assms(2) drop
    by (auto elim: reaches_on.cases)
  show ?thesis
    using ru_t_event[OF t'_def(1) refl t''_def] assms(2)
    by auto
qed

lemmas run_hd_tau_in = ru_t_tau_in[OF reach_event_t0_t, simplified]

fun last_before :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat option" where
  "last_before P 0 = None"
| "last_before P (Suc n) = (if P n then Some n else last_before P n)"

lemma last_before_None: "last_before P n = None \<Longrightarrow> m < n \<Longrightarrow> \<not>P m"
proof (induction P n rule: last_before.induct)
  case (2 P n)
  then show ?case
    by (cases "m = n") (auto split: if_splits)
qed (auto split: if_splits)

lemma last_before_Some: "last_before P n = Some m \<Longrightarrow> m < n \<and> P m \<and> (\<forall>k \<in> {m<..<n}. \<not>P k)"
  apply (induction P n rule: last_before.induct)
   apply (auto split: if_splits)
  apply (metis greaterThanLessThan_iff less_antisym)
  done

inductive wf_vydra :: "('a, 't :: timestamp) formula \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a, 't, 'h) vydra_aux \<Rightarrow> bool" where
  "wf_vydra phi i n w \<Longrightarrow> ru n w = None \<Longrightarrow> wf_vydra (Prev I phi) (Suc i) (Suc n) VYDRA_None"
| "wf_vydra phi i n w \<Longrightarrow> ru n w = None \<Longrightarrow> wf_vydra (Next I phi) i (Suc n) VYDRA_None"
| "reaches_on run_hd init_hd es sub' \<Longrightarrow> length es = i \<Longrightarrow> wf_vydra (Bool b) i n (VYDRA_Bool b sub')"
| "reaches_on run_hd init_hd es sub' \<Longrightarrow> length es = i \<Longrightarrow> wf_vydra (Atom a) i n (VYDRA_Atom a sub')"
| "wf_vydra phi i n v \<Longrightarrow> wf_vydra (Neg phi) i (Suc n) (VYDRA_Neg v)"
| "wf_vydra phi i n v \<Longrightarrow> wf_vydra psi i n v' \<Longrightarrow> wf_vydra (Bin f phi psi) i (Suc n) (VYDRA_Bin f v v')"
| "wf_vydra phi i n v \<Longrightarrow> reaches_on run_hd init_hd es sub' \<Longrightarrow> length es = i \<Longrightarrow>
   wf_vydra (Prev I phi) i (Suc n) (VYDRA_Prev I v sub' (case i of 0 \<Rightarrow> None | Suc j \<Rightarrow> Some (\<tau> \<sigma> j, sat phi j)))"
| "wf_vydra phi i n v \<Longrightarrow> reaches_on run_hd init_hd es sub' \<Longrightarrow> length es = i \<Longrightarrow>
   wf_vydra (Next I phi) (i - 1) (Suc n) (VYDRA_Next I v sub' (case i of 0 \<Rightarrow> None | Suc j \<Rightarrow> Some (\<tau> \<sigma> j)))"
| "wf_vydra phi i n vphi \<Longrightarrow> wf_vydra psi j n vpsi \<Longrightarrow> j \<le> i \<Longrightarrow>
   reaches_on ru_t l_t0 es sub' \<Longrightarrow> length es = j \<Longrightarrow> (\<And>t. t \<in> set es \<Longrightarrow> memL t (\<tau> \<sigma> i) I) \<Longrightarrow>
   cphi = i - (case last_before (\<lambda>k. \<not>sat phi k) i of None \<Rightarrow> 0 | Some k \<Rightarrow> Suc k) \<Longrightarrow> cpsi = i - j \<Longrightarrow>
   cppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (i - k)) \<Longrightarrow>
   tppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (\<tau> \<sigma> k)) \<Longrightarrow>
   wf_vydra (Since phi I psi) i (Suc n) (VYDRA_Since I vphi vpsi sub' cphi cpsi cppsi tppsi)"
| "wf_vydra phi j n vphi \<Longrightarrow> wf_vydra psi j n vpsi \<Longrightarrow> i \<le> j \<Longrightarrow>
   reaches_on ru_t l_t0 es back \<Longrightarrow> length es = i \<Longrightarrow>
   reaches_on ru_t l_t0 es' front \<Longrightarrow> length es' = j \<Longrightarrow> (\<And>t. t \<in> set es' \<Longrightarrow> memR (\<tau> \<sigma> i) t I) \<Longrightarrow>
   c = j - i \<Longrightarrow> z = (case j of 0 \<Rightarrow> None | Suc k \<Rightarrow> Some (\<tau> \<sigma> k, sat phi k, sat psi k)) \<Longrightarrow>
   (\<And>k. k \<in> {i..<j - 1} \<Longrightarrow> sat phi k \<and> (memL (\<tau> \<sigma> i) (\<tau> \<sigma> k) I \<longrightarrow> \<not>sat psi k)) \<Longrightarrow>
   wf_vydra (Until phi I psi) i (Suc n) (VYDRA_Until I back vphi vpsi front c z)"
| "valid_window_matchP args I l_t0 (map (su n) (collect_subfmlas r [])) xs i w \<Longrightarrow>
    n \<ge> msize_regex r \<Longrightarrow> qf = state_cnt r \<Longrightarrow>
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) \<Longrightarrow>
    args = init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (ru_t, read_t) (run_subs (ru n)) \<Longrightarrow>
    wf_vydra (MatchP I r) i (Suc n) (VYDRA_MatchP I transs qf w)"
| "valid_window_matchF args I l_t0 (map (su n) (collect_subfmlas r [])) xs i w \<Longrightarrow>
    n \<ge> msize_regex r \<Longrightarrow> qf = state_cnt r \<Longrightarrow>
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) \<Longrightarrow>
    args = init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (ru_t, read_t) (run_subs (ru n)) \<Longrightarrow>
    wf_vydra (MatchF I r) i (Suc n) (VYDRA_MatchF I transs qf w)"

lemma reach_run_subs_len:
  assumes reaches_ons: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) rho vs"
  shows "length vs = length (collect_subfmlas r [])"
  using reaches_ons run_subs_lD
  by (induction "map (su n) (collect_subfmlas r [])" rho vs rule: reaches_on_rev_induct) fastforce+

lemma reach_run_subs_run:
  assumes reaches_ons: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) rho vs"
    and subfmla: "j < length (collect_subfmlas r [])" "phi = collect_subfmlas r [] ! j"
  shows "\<exists>rho'. reaches_on (ru n) (su n phi) rho' (vs ! j) \<and> length rho' = length rho"
  using reaches_ons subfmla
proof (induction "map (su n) (collect_subfmlas r [])" rho vs rule: reaches_on_rev_induct)
  case 1
  then show ?case
    by (auto intro: reaches_on.intros)
next
  case (2 s' v vs' s'')
  note len_s'_vs = reach_run_subs_len[OF 2(1)]
  obtain rho' where reach_s'_vs: "reaches_on (ru n) (su n phi) rho' (s' ! j)"
    "length rho' = length vs'"
    using 2(2)[OF 2(4,5)]
    by auto
  note run_subslD = run_subs_lD[OF 2(3)]
  note run_subsvD = run_subs_vD[OF 2(3) 2(4)[unfolded len_s'_vs[symmetric]]]
  obtain vj' tj bj where vj'_def: "ru n (s' ! j) = Some (vj', tj, bj)"
    "s'' ! j = vj'" "IArray.sub v j = bj"
    using run_subsvD by auto
  obtain rho'' where rho''_def: "reaches_on (ru n) (su n phi) rho'' (s'' ! j)"
    "length rho'' = Suc (length vs')"
    using reaches_on_app[OF reach_s'_vs(1) vj'_def(1)] vj'_def(2) reach_s'_vs(2)
    by auto
  then show ?case
    using conjunct1[OF run_subslD, unfolded len_s'_vs[symmetric]]
    by auto
qed

lemma IArray_nth_equalityI: "IArray.length xs = length ys \<Longrightarrow>
  (\<And>i. i < IArray.length xs \<Longrightarrow> IArray.sub xs i = ys ! i) \<Longrightarrow> xs = IArray ys"
  by (induction xs arbitrary: ys) (auto intro: nth_equalityI)

lemma bs_sat:
  assumes IH: "\<And>phi i v v' b. phi \<in> set (collect_subfmlas r []) \<Longrightarrow> wf_vydra phi i n v \<Longrightarrow> ru n v = Some (v', b) \<Longrightarrow> snd b = sat phi i"
    and reaches_ons: "\<And>j. j < length (collect_subfmlas r []) \<Longrightarrow> wf_vydra (collect_subfmlas r [] ! j) i n (vs ! j)"
    and run_subs: "run_subs (ru n) vs = Some (vs', bs)" "length vs = length (collect_subfmlas r [])"
  shows "bs = iarray_of_list (map (\<lambda>phi. sat phi i) (collect_subfmlas r []))"
proof -
  have "\<And>j. j < length (collect_subfmlas r []) \<Longrightarrow>
    IArray.sub bs j = sat (collect_subfmlas r [] ! j) i"
  proof -
    fix j
    assume lassm: "j < length (collect_subfmlas r [])"
    define phi where "phi = collect_subfmlas r [] ! j"
    have phi_in_set: "phi \<in> set (collect_subfmlas r [])"
      using lassm
      by (auto simp: phi_def)
    have wf: "wf_vydra phi i n (vs ! j)"
      using reaches_ons lassm phi_def
      by metis
    show "IArray.sub bs j = sat (collect_subfmlas r [] ! j) i"
      using IH(1)[OF phi_in_set wf] run_subs_vD[OF run_subs(1) lassm[folded run_subs(2)]]
      unfolding phi_def[symmetric]
      by auto
  qed
  moreover have "length (IArray.list_of bs) = length vs"
    using run_subs(1)
    by (auto simp: run_subs_def Let_def iarray_of_list_def split: if_splits)
  ultimately show ?thesis
    using run_subs(2)
    by (auto simp: iarray_of_list_def intro!: IArray_nth_equalityI)
qed

lemma run_induct[case_names Bool Atom Neg Bin Prev Next Since Until MatchP MatchF, consumes 1]:
  fixes phi :: "('a, 't) formula"
  assumes "msize_fmla phi \<le> n" "(\<And>b n. P n (Bool b))" "(\<And>a n. P n (Atom a))"
    "(\<And>n phi. msize_fmla phi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P (Suc n) (Neg phi))"
    "(\<And>n f phi psi. msize_fmla (Bin f phi psi) \<le> Suc n \<Longrightarrow> P n phi \<Longrightarrow> P n psi \<Longrightarrow>
      P (Suc n) (Bin f phi psi))"
    "(\<And>n I phi. msize_fmla phi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P (Suc n) (Prev I phi))"
    "(\<And>n I phi. msize_fmla phi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P (Suc n) (Next I phi))"
    "(\<And>n I phi psi. msize_fmla phi \<le> n \<Longrightarrow> msize_fmla psi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P n psi \<Longrightarrow> P (Suc n) (Since phi I psi))"
    "(\<And>n I phi psi. msize_fmla phi \<le> n \<Longrightarrow> msize_fmla psi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P n psi \<Longrightarrow> P (Suc n) (Until phi I psi))"
    "(\<And>n I r. msize_fmla (MatchP I r) \<le> Suc n \<Longrightarrow> (\<And>x. msize_fmla x \<le> n \<Longrightarrow> P n x) \<Longrightarrow>
      P (Suc n) (MatchP I r))"
    "(\<And>n I r. msize_fmla (MatchF I r) \<le> Suc n \<Longrightarrow> (\<And>x. msize_fmla x \<le> n \<Longrightarrow> P n x) \<Longrightarrow>
      P (Suc n) (MatchF I r))"
  shows "P n phi"
  using assms(1)
proof (induction n arbitrary: phi rule: nat_less_induct)
  case (1 n)
  show ?case
  proof (cases n)
    case 0
    show ?thesis
      using 1 assms(2-)
      by (cases phi) (auto simp: 0)
  next
    case (Suc m)
    show ?thesis
      using 1 assms(2-)
      by (cases phi) (auto simp: Suc)
  qed
qed

lemma wf_vydra_sub: "msize_fmla \<phi> \<le> n \<Longrightarrow> wf_vydra \<phi> 0 n (su n \<phi>)"
proof (induction n \<phi> rule: run_induct)
  case (Prev n I phi)
  then show ?case
    using wf_vydra.intros(7)[where ?i=0, OF _ reaches_on.intros(1)]
    by auto
next
  case (Next n I phi)
  then show ?case
    using wf_vydra.intros(8)[where ?i=0, OF _ reaches_on.intros(1)]
    by auto
next
  case (MatchP n I r)
  let ?qf = "state_cnt r"
  let ?transs = "iarray_of_list (build_nfa_impl r (0, ?qf, []))"
  let ?args = "init_args ({0}, NFA.delta' ?transs ?qf, NFA.accept' ?transs ?qf) (ru_t, read_t) (run_subs (ru n))"
  show ?case
    using MatchP valid_init_window[of ?args l_t0 "map (su n) (collect_subfmlas r [])", simplified]
    by (auto simp: Let_def valid_window_matchP_def split: option.splits intro: reaches_on.intros
        intro!: wf_vydra.intros(11)[where ?xs="[]", OF _ _ refl refl refl])
next
  case (MatchF n I r)
  let ?qf = "state_cnt r"
  let ?transs = "iarray_of_list (build_nfa_impl r (0, ?qf, []))"
  let ?args = "init_args ({0}, NFA.delta' ?transs ?qf, NFA.accept' ?transs ?qf) (ru_t, read_t) (run_subs (ru n))"
  show ?case
    using MatchF valid_init_window[of ?args l_t0 "map (su n) (collect_subfmlas r [])", simplified]
    by (auto simp: Let_def valid_window_matchF_def split: option.splits intro: reaches_on.intros
        intro!: wf_vydra.intros(12)[where ?xs="[]", OF _ _ refl refl refl])
qed (auto simp: Let_def intro: wf_vydra.intros reaches_on.intros)

lemma ru_t_Some: "\<exists>e' et. ru_t e = Some (e', et)" if reaches_Suc_i: "reaches_on run_hd init_hd fs f" "length fs = Suc i"
  and aux: "reaches_on ru_t l_t0 es e" "length es \<le> i" for es e
proof -
  obtain fs' ft where ft_def: "reaches_on ru_t l_t0 (map fst (fs' :: ('t \<times> 'a set) list)) (Some (f, ft))"
    "map fst fs = map fst fs' @ [ft]" "length fs' = i"
    using reaches_Suc_i
    by (cases fs rule: rev_cases) (auto dest!: reaches_on_split_last reach_event_t0_t)
  show ?thesis
  proof (cases "length es = i")
    case True
    have e_def: "e = Some (f, ft)"
      using reaches_on_inj[OF aux(1) ft_def(1)]
      by (auto simp: True ft_def(3))
    then show ?thesis
      by (cases "run_hd f") (auto simp: e_def)
  next
    case False
    obtain s' s'' where split: "reaches_on ru_t l_t0 (take (length es) (map fst fs')) s'"
      "ru_t s' = Some (s'', map fst fs' ! (length es))"
      using reaches_on_split[OF ft_def(1), where ?i="length es"] False aux(2)
      by (auto simp: ft_def(3))
    show ?thesis
      using reaches_on_inj[OF aux(1) split(1)] aux(2)
      by (auto simp: ft_def(3) split(2))
  qed
qed

lemma vydra_sound_aux:
  assumes "msize_fmla \<phi> \<le> n" "wf_vydra \<phi> i n v" "ru n v = Some (v', t, b)" "bounded_future_fmla \<phi>" "wf_fmla \<phi>"
  shows "wf_vydra \<phi> (Suc i) n v' \<and> (\<exists>es e. reaches_on run_hd init_hd es e \<and> length es = Suc i) \<and> t = \<tau> \<sigma> i \<and> b = sat \<phi> i"
  using assms
proof (induction n \<phi> arbitrary: i v v' t b rule: run_induct)
  case (Bool \<beta> n)
  then show ?case
    using reaches_on_run_hd reaches_on_app wf_vydra.intros(3)[OF reaches_on_app refl]
    by (fastforce elim!: wf_vydra.cases[of _ _ _ "v"] split: option.splits)
next
  case (Atom a n)
  then show ?case
    using reaches_on_run_hd reaches_on_app wf_vydra.intros(4)[OF reaches_on_app refl]
    by (fastforce elim!: wf_vydra.cases[of _ _ _ v] split: option.splits)
next
  case (Neg n x)
  have IH: "wf_vydra x i n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x (Suc i) n v' \<and> (\<exists>es e. reaches_on run_hd init_hd es e \<and> length es = Suc i) \<and> t = \<tau> \<sigma> i \<and> b = sat x i" for v v' t b
    using Neg(2,5,6)
    by auto
  show ?case
    apply (rule wf_vydra.cases[OF Neg(3)])
    using Neg(4) IH wf_vydra.intros(5)
    by (fastforce split: option.splits)+
next
  case (Bin n f x1 x2)
  have IH1: "wf_vydra x1 i n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x1 (Suc i) n v' \<and> (\<exists>es e. reaches_on run_hd init_hd es e \<and> length es = Suc i) \<and> t = \<tau> \<sigma> i \<and> b = sat x1 i" for v v' t b
    using Bin(2,6,7)
    by auto
  have IH2: "wf_vydra x2 i n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x2 (Suc i) n v' \<and> t = \<tau> \<sigma> i \<and> b = sat x2 i" for v v' t b
    using Bin(3,6,7)
    by auto
  show ?case
    apply (rule wf_vydra.cases[OF Bin(4)])
    using Bin(5) IH1 IH2 wf_vydra.intros(6)
    by (fastforce split: option.splits)+
next
  case (Prev n I phi)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using Prev run_hd_sound[OF reaches.intros(1)] wf_vydra.intros(7)[OF _ reaches_on.intros(2)[OF _ reaches_on.intros(1)], where ?i="Suc 0", simplified]
      by (fastforce split: nat.splits option.splits dest!: reaches_on_NilD elim!: wf_vydra.cases[of _ _ _ v] intro: wf_vydra.intros(1) reaches_on.intros(2)[OF _ reaches_on.intros(1)])
  next
    case (Suc j)
    obtain vphi es sub where v_def: "v = VYDRA_Prev I vphi sub (Some (\<tau> \<sigma> j, sat phi j))"
      "wf_vydra phi i n vphi" "reaches_on run_hd init_hd es sub" "length es = i"
      using Prev(3,4)
      by (auto simp: Suc elim!: wf_vydra.cases[of _ _ _ v])
    obtain sub' X where run_sub: "run_hd sub = Some (sub', (t, X))"
      using Prev(4)
      by (auto simp: v_def(1) Let_def split: option.splits)
    note reaches_sub' = reaches_on_app[OF v_def(3) run_sub]
    have t_def: "t = \<tau> \<sigma> (Suc j)"
      using reaches_on_run_hd[OF v_def(3) run_sub]
      by (auto simp: Suc v_def(2,4))
    show ?thesis
    proof (cases "v' = VYDRA_None")
      case v'_def: True
      show ?thesis
        using Prev(4) v_def(2) reaches_sub'
        by (auto simp: Suc Let_def v_def(1,4) v'_def run_sub t_def split: option.splits intro: wf_vydra.intros(1))
    next
      case False
      obtain vphi' where ru_vphi: "ru n vphi = Some (vphi', (\<tau> \<sigma> i, sat phi i))"
        using Prev(2)[OF v_def(2)] Prev(4,5,6) False
        by (auto simp: v_def(1) Let_def split: option.splits)
      have wf': "wf_vydra phi (Suc (Suc j)) n vphi'"
        using Prev(2)[OF v_def(2) ru_vphi] Prev(5,6)
        by (auto simp: Suc)
      show ?thesis
        using Prev(4) wf_vydra.intros(7)[OF wf' reaches_sub'] reaches_sub'
        by (auto simp: Let_def Suc t_def v_def(1,4) run_sub ru_vphi)
    qed
  qed
next
  case (Next n I phi)
  obtain w sub to es where v_def: "v = VYDRA_Next I w sub to" "wf_vydra phi (length es) n w"
    "reaches_on run_hd init_hd es sub" "length es = (case to of None \<Rightarrow> 0 | _ \<Rightarrow> Suc i)"
    "case to of None \<Rightarrow> i = 0 | Some told \<Rightarrow> told = \<tau> \<sigma> i"
    using Next(3,4)
    by (auto elim!: wf_vydra.cases[of _ _ _ v] split: option.splits nat.splits)
  obtain sub' tnew X where run_sub: "run_hd sub = Some (sub', (tnew, X))"
    using Next(4)
    by (auto simp: v_def(1) split: option.splits)
  have tnew_def: "tnew = \<tau> \<sigma> (length es)"
    using reaches_on_run_hd[OF v_def(3) run_sub]
    by auto
  have aux: ?case if aux_assms: "wf_vydra phi (Suc i) n w"
    "ru (Suc n) (VYDRA_Next I w sub (Some t0)) = Some (v', t, b)"
    "reaches_on run_hd init_hd es sub" "length es = Suc i" "t0 = \<tau> \<sigma> i" for w sub t0 es
    using aux_assms(1,2,5) wf_vydra.intros(2)[OF aux_assms(1)]
      Next(2)[where ?i="Suc i" and ?v="w"] Next(5,6) reaches_on_run_hd[OF aux_assms(3)]
      wf_vydra.intros(8)[OF _ reaches_on_app[OF aux_assms(3)], where ?phi=phi and ?i="Suc (Suc i)" and ?n="n"] aux_assms(3)
    by (auto simp: run_sub aux_assms(4,5) split: option.splits if_splits)
  show ?case
  proof (cases to)
    case None
    obtain w' z where w_def: "ru (Suc n) v = ru (Suc n) (VYDRA_Next I w' sub' (Some tnew))"
      "ru n w = Some (w', z)"
      using Next(4)
      by (cases "ru n w") (auto simp: v_def(1) run_sub None split: option.splits)
    have wf: "wf_vydra phi (Suc i) n w'"
      using v_def w_def(2) Next(2,5,6)
      by (cases z) (auto simp: None intro: wf_vydra.intros(1))
    show ?thesis
      using aux[OF wf Next(4)[unfolded w_def(1)] reaches_on_app[OF v_def(3) run_sub]] v_def(4,5) tnew_def
      by (auto simp: None)
  next
    case (Some z)
    show ?thesis
      using aux[OF _ _ v_def(3), where ?w="w"] v_def(2,4,5) Next(4)
      by (auto simp: v_def(1) Some simp del: run.simps)
  qed
next
  case (Since n I phi psi)
  obtain vphi vpsi e cphi cpsi cppsi tppsi j es where v_def:
    "v = VYDRA_Since I vphi vpsi e cphi cpsi cppsi tppsi"
    "wf_vydra phi i n vphi" "wf_vydra psi j n vpsi" "j \<le> i"
    "reaches_on ru_t l_t0 es e" "length es = j" "\<And>t. t \<in> set es \<Longrightarrow> memL t (\<tau> \<sigma> i) I"
    "cphi = i - (case last_before (\<lambda>k. \<not>sat phi k) i of None \<Rightarrow> 0 | Some k \<Rightarrow> Suc k)" "cpsi = i - j"
    "cppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (i - k))"
    "tppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (\<tau> \<sigma> k))"
    using Since(5)
    by (auto elim: wf_vydra.cases)
  obtain vphi' b1 where run_vphi: "ru n vphi = Some (vphi', t, b1)"
    using Since(6)
    by (auto simp: v_def(1) Let_def split: option.splits)
  obtain fs f where wf_vphi': "wf_vydra phi (Suc i) n vphi'"
    and reaches_Suc_i: "reaches_on run_hd init_hd fs f" "length fs = Suc i"
    and t_def: "t = \<tau> \<sigma> i" and b1_def: "b1 = sat phi i"
    using Since(3)[OF v_def(2) run_vphi] Since(7,8)
    by auto
  note ru_t_Some = ru_t_Some[OF reaches_Suc_i]
  define loop_inv where "loop_inv = (\<lambda>(vpsi, e, cpsi :: nat, cppsi, tppsi).
    let j = Suc i - cpsi in cpsi \<le> Suc i \<and>
    wf_vydra psi j n vpsi \<and> (\<exists>es. reaches_on ru_t l_t0 es e \<and> length es = j \<and> (\<forall>t \<in> set es. memL t (\<tau> \<sigma> i) I)) \<and>
    cppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (Suc i - k)) \<and>
    tppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (\<tau> \<sigma> k)))"
  define loop_init where "loop_init = (vpsi, e, Suc cpsi, map_option Suc cppsi, tppsi)"
  obtain vpsi' e' cpsi' cppsi' tppsi' where loop_def: "while_break (while_since_cond I t) (while_since_body run_hd (ru n)) loop_init =
    Some (vpsi', e', cpsi', cppsi', tppsi')"
    using Since(6)
    by (auto simp: v_def(1) run_vphi loop_init_def Let_def split: option.splits)
  have j_def: "j = i - cpsi"
    using v_def(4,9)
    by auto
  have "cpsi \<le> i"
    using v_def(9)
    by auto
  then have loop_inv_init: "loop_inv loop_init"
    using v_def(3,5,6,7,10,11) last_before_Some
    by (fastforce simp: loop_inv_def loop_init_def Let_def j_def split: option.splits)
  have wf_loop: "wf {(s', s). loop_inv s \<and> while_since_cond I t s \<and> Some s' = while_since_body run_hd (ru n) s}"
    by (auto intro: wf_subset[OF wf_since])
  have step_loop: "loop_inv s'" if loop_assms: "loop_inv s" "while_since_cond I t s" "while_since_body run_hd (ru n) s = Some s'" for s s'
  proof -
    obtain vpsi e cpsi cppsi tppsi where s_def: "s = (vpsi, e, cpsi, cppsi, tppsi)"
      by (cases s) auto
    define j where "j = Suc i - cpsi"
    obtain es where loop_before: "cpsi \<le> Suc i" "wf_vydra psi j n vpsi"
      "reaches_on ru_t l_t0 es e" "length es = j" "\<And>t. t \<in> set es \<Longrightarrow> memL t (\<tau> \<sigma> i) I"
      "cppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (Suc i - k))"
      "tppsi = (case last_before (sat psi) j of None \<Rightarrow> None | Some k \<Rightarrow> Some (\<tau> \<sigma> k))"
      using loop_assms(1)
      by (auto simp: s_def j_def loop_inv_def Let_def)
    obtain tt h where tt_def: "read_t e = Some tt" "memL tt t I" "e = Some (h, tt)"
      using ru_t_Some[OF loop_before(3)] loop_before(4) loop_assms(2)
      by (cases e) (fastforce simp: while_since_cond_def s_def j_def split: option.splits)+
    obtain e' where e'_def: "reaches_on ru_t l_t0 (es @ [tt]) e'" "ru_t e = Some (e', tt)"
      using reaches_on_app[OF loop_before(3)] tt_def(1)
      by (cases "run_hd h") (auto simp: tt_def(3))
    obtain vpsi' t' b' where run_vpsi: "ru n vpsi = Some (vpsi', (t', b'))"
      using loop_assms(3)
      by (auto simp: while_since_body_def s_def Let_def split: option.splits)
    have wf_psi': "wf_vydra psi (Suc j) n vpsi'" and t'_def: "t' = \<tau> \<sigma> j" and b'_def: "b' = sat psi j"
      using Since(4)[OF loop_before(2) run_vpsi] Since(7,8)
      by auto
    define j' where j'_def: "j' = Suc i - (cpsi - Suc 0)"
    have cpsi_pos: "cpsi > 0"
      using loop_assms(2)
      by (auto simp: while_since_cond_def s_def)
    have j'_j: "j' = Suc j"
      using loop_before(1) cpsi_pos
      by (auto simp: j'_def j_def)
    define cppsi' where "cppsi' = (if b' then Some cpsi else cppsi)"
    define tppsi' where "tppsi' = (if b' then Some t' else tppsi)"
    have cppsi': "cppsi' = (case last_before (sat psi) j' of None \<Rightarrow> None | Some k \<Rightarrow> Some (Suc i - k))"
      using cpsi_pos loop_before(1)
      by (auto simp: cppsi'_def b'_def j'_j loop_before(6) j_def)
    have tppsi': "tppsi' = (case last_before (sat psi) j' of None \<Rightarrow> None | Some k \<Rightarrow> Some (\<tau> \<sigma> k))"
      by (auto simp: tppsi'_def t'_def b'_def j'_j loop_before(7) split: option.splits)
    have s'_def: "s' = (vpsi', fst (the (ru_t e)), cpsi - Suc 0, cppsi', tppsi')"
      using loop_assms(3)
      by (auto simp: while_since_body_def s_def run_vpsi cppsi'_def tppsi'_def)
    show ?thesis
      using loop_before(1,4,5) tt_def(2) wf_psi'[folded j'_j] cppsi' tppsi' e'_def(1)
      by (fastforce simp: loop_inv_def s'_def j'_def[symmetric] e'_def(2) j'_j t_def)
  qed
  have loop: "loop_inv (vpsi', e', cpsi', cppsi', tppsi')" "\<not>while_since_cond I t (vpsi', e', cpsi', cppsi', tppsi')"
    using while_break_sound[where ?P="loop_inv" and ?Q="\<lambda>s. loop_inv s \<and> \<not>while_since_cond I t s", OF step_loop _ wf_loop loop_inv_init]
    by (auto simp: loop_def)
  define cphi' where "cphi' = (if b1 then Suc cphi else 0)"
  have v'_def: "v' = VYDRA_Since I vphi' vpsi' e' cphi' cpsi' cppsi' tppsi'"
    and b_def: "b = (case cppsi' of None \<Rightarrow> False | Some k \<Rightarrow> k - 1 \<le> cphi' \<and> memR (the tppsi') t I)"
    using Since(6)
    by (auto simp: v_def(1) run_vphi loop_init_def[symmetric] loop_def cphi'_def Let_def split: option.splits)
  have read_t_e': "cpsi' > 0 \<Longrightarrow> read_t e' = None \<Longrightarrow> False"
    using loop(1) ru_t_Some[where ?e=e'] run_t_read
    by (fastforce simp: loop_inv_def Let_def)
  define j' where "j' = Suc i - cpsi'"
  have wf_vpsi': "wf_vydra psi j' n vpsi'" and cpsi'_le_Suc_i: "cpsi' \<le> Suc i"
    and cppsi'_def: "cppsi' = (case last_before (sat psi) j' of None \<Rightarrow> None | Some k \<Rightarrow> Some (Suc i - k))"
    and tppsi'_def: "tppsi' = (case last_before (sat psi) j' of None \<Rightarrow> None | Some k \<Rightarrow> Some (\<tau> \<sigma> k))"
    using loop(1)
    by (auto simp: loop_inv_def j'_def[symmetric])
  obtain es' where es'_def: "reaches_on ru_t l_t0 es' e'" "length es' = j'" "\<And>t. t \<in> set es' \<Longrightarrow> memL t (\<tau> \<sigma> i) I"
    using loop(1)
    by (auto simp: loop_inv_def j'_def[symmetric])
  have wf_v': "wf_vydra (Since phi I psi) (Suc i) (Suc n) v'"
    and cphi'_sat: "cphi' = Suc i - (case last_before (\<lambda>k. \<not>sat phi k) (Suc i) of None \<Rightarrow> 0 | Some k \<Rightarrow> Suc k)"
    using cpsi'_le_Suc_i last_before_Some es'_def(3) memL_mono'[OF _ \<tau>_mono[of i "Suc i" \<sigma>]]
    by (force simp: v'_def cppsi'_def tppsi'_def j'_def cphi'_def b1_def v_def(8) split: option.splits
        intro!: wf_vydra.intros(9)[OF wf_vphi' wf_vpsi' _ es'_def(1-2)])+
  have "j' = Suc i \<or> \<not>memL (\<tau> \<sigma> j') (\<tau> \<sigma> i) I"
    using loop(2) j'_def read_t_e' ru_t_tau[OF es'_def(1)] read_t_run[where ?run_hd=run_hd]
    by (fastforce simp: while_since_cond_def es'_def(2) t_def split: option.splits)
  then have tau_k_j': "k \<le> i \<Longrightarrow> memL (\<tau> \<sigma> k) (\<tau> \<sigma> i) I \<longleftrightarrow> k < j'" for k
    using ru_t_tau_in[OF es'_def(1)] es'_def(3) \<tau>_mono[of j' k \<sigma>] memL_mono
    by (fastforce simp: es'_def(2) in_set_conv_nth)
  have b_sat: "b = sat (Since phi I psi) i"
  proof (rule iffI)
    assume b: "b"
    obtain m where m_def: "last_before (sat psi) j' = Some m" "i - m \<le> cphi'" "memR (\<tau> \<sigma> m) (\<tau> \<sigma> i) I"
      using b
      by (auto simp: b_def t_def cppsi'_def tppsi'_def split: option.splits)
    note aux = last_before_Some[OF m_def(1)]
    have mem: "mem (\<tau> \<sigma> m) (\<tau> \<sigma> i) I"
      using m_def(3) tau_k_j' aux
      by (auto simp: mem_def j'_def)
    have sat_phi: "sat phi x" if "m < x" "x \<le> i" for x
      using m_def(2) that le_neq_implies_less
      by (fastforce simp: cphi'_sat dest: last_before_None last_before_Some split: option.splits if_splits)
    show "sat (Since phi I psi) i"
      using aux mem sat_phi
      by (auto simp: j'_def intro!: exI[of _ m])
  next
    assume sat: "sat (Since phi I psi) i"
    then obtain k where k_def: "k \<le> i" "mem (\<tau> \<sigma> k) (\<tau> \<sigma> i) I" "sat psi k" "\<And>k'. k < k' \<and> k' \<le> i \<Longrightarrow> sat phi k'"
      by auto
    have k_j': "k < j'"
      using tau_k_j'[OF k_def(1)] k_def(2)
      by (auto simp: mem_def)
    obtain m where m_def: "last_before (sat psi) j' = Some m"
      using last_before_None[where ?P="sat psi" and ?n=j' and ?m=k] k_def(3) k_j'
      by (cases "last_before (sat psi) j'") auto
    have cppsi'_Some: "cppsi' = Some (Suc i - m)"
      by (auto simp: cppsi'_def m_def)
    have tppsi'_Some: "tppsi' = Some (\<tau> \<sigma> m)"
      by (auto simp: tppsi'_def m_def)
    have m_k: "k \<le> m"
      using last_before_Some[OF m_def] k_def(3) k_j'
      by auto
    have tau_i_m: "memR (\<tau> \<sigma> m) (\<tau> \<sigma> i) I"
      using \<tau>_mono[OF m_k, where ?s=\<sigma>] memR_mono k_def(2)
      by (auto simp: mem_def)
    have "i - m \<le> cphi'"
      using k_def(1) k_def(4) m_k
      apply (cases "k = i")
       apply (auto simp: cphi'_sat b1_def dest!: last_before_Some split: option.splits)
      apply (metis diff_le_mono2 le_neq_implies_less le_trans less_imp_le_nat nat_le_linear)
      done
    then show "b"
      using tau_i_m
      by (auto simp: b_def t_def cppsi'_Some tppsi'_Some)
  qed
  show ?case
    using wf_v' reaches_Suc_i
    by (auto simp: t_def b_sat)
next
  case (Until n I phi psi)
  obtain "back" vphi vpsi front c z es es' j where v_def:
    "v = VYDRA_Until I back vphi vpsi front c z"
    "wf_vydra phi j n vphi" "wf_vydra psi j n vpsi" "i \<le> j"
    "reaches_on ru_t l_t0 es back" "length es = i"
    "reaches_on ru_t l_t0 es' front" "length es' = j" "\<And>t. t \<in> set es' \<Longrightarrow> memR (\<tau> \<sigma> i) t I"
    "c = j - i" "z = (case j of 0 \<Rightarrow> None | Suc k \<Rightarrow> Some (\<tau> \<sigma> k, sat phi k, sat psi k))"
    "\<And>k. k \<in> {i..<j - 1} \<Longrightarrow> sat phi k \<and> (memL (\<tau> \<sigma> i) (\<tau> \<sigma> k) I \<longrightarrow> \<not>sat psi k)"
    using Until(5)
    by (auto elim: wf_vydra.cases)
  define loop_init where "loop_init = (vphi, vpsi, front, c, z)"
  obtain back' vphi' vpsi' epsi' c' zo' zt zb1 zb2 where run_back: "ru_t back = Some (back', t)"
    and loop_def: "while_break (while_until_cond I t) (while_until_body run_hd (ru n)) loop_init = Some (vphi', vpsi', epsi', c', zo')"
    and v'_def: "v' = VYDRA_Until I back' vphi' vpsi' epsi' (c' - 1) zo'"
    and c'_pos: "\<not>c' = 0"
    and zo'_Some: "zo' = Some (zt, (zb1, zb2))"
    and b_def: "b = (zb2 \<and> memL t zt I)"
    using Until(6)
    apply (auto simp: v_def(1) Let_def loop_init_def[symmetric] split: option.splits nat.splits if_splits)
    done
  define j' where "j' = i + c'"
  have j_eq: "j = i + c"
    using v_def(4)
    by (auto simp: v_def(10))
  have t_def: "t = \<tau> \<sigma> i"
    using ru_t_tau[OF v_def(5) run_back]
    by (auto simp: v_def(6))
  define loop_inv where "loop_inv = (\<lambda>(vphi, vpsi, epsi, c, zo).
    let j = i + c in
    wf_vydra phi j n vphi \<and> wf_vydra psi j n vpsi \<and>
    (\<exists>gs. reaches_on ru_t l_t0 gs epsi \<and> length gs = j \<and> (\<forall>t. t \<in> set gs \<longrightarrow> memR (\<tau> \<sigma> i) t I)) \<and>
    zo = (case j of 0 \<Rightarrow> None | Suc k \<Rightarrow> Some (\<tau> \<sigma> k, sat phi k, sat psi k)) \<and>
    (\<forall>k. k \<in> {i..<j - 1} \<longrightarrow> sat phi k \<and> (memL (\<tau> \<sigma> i) (\<tau> \<sigma> k) I \<longrightarrow> \<not>sat psi k)))"
  have loop_inv_init: "loop_inv loop_init"
    using v_def(2,3,7,9,12)
    by (auto simp: loop_inv_def loop_init_def j_eq[symmetric] v_def(8,11))
  have loop_step: "loop_inv s'" if loop_assms: "loop_inv s" "while_until_cond I t s" "while_until_body run_hd (ru n) s = Some s'" for s s'
  proof -
    obtain vphi_cur vpsi_cur epsi_cur c_cur zo_cur where s_def: "s = (vphi_cur, vpsi_cur, epsi_cur, c_cur, zo_cur)"
      by (cases s) auto
    define j_cur where "j_cur = i + c_cur"
    obtain epsi'_cur t'_cur vphi'_cur tphi_cur bphi_cur vpsi'_cur tpsi_cur bpsi_cur where
      run_epsi: "ru_t epsi_cur = Some (epsi'_cur, t'_cur)"
      and run_vphi: "ru n vphi_cur = Some (vphi'_cur, (tphi_cur, bphi_cur))"
      and run_vpsi: "ru n vpsi_cur = Some (vpsi'_cur, (tpsi_cur, bpsi_cur))"
      using loop_assms(2,3)
      apply (auto simp: while_until_cond_def while_until_body_def s_def split: option.splits dest: read_t_run[where ?run_hd=run_hd])
      done
    have wf: "wf_vydra phi j_cur n vphi_cur" "wf_vydra psi j_cur n vpsi_cur"
      and zo_cur_def: "zo_cur = (case j_cur of 0 \<Rightarrow> None | Suc k \<Rightarrow> Some (\<tau> \<sigma> k, sat phi k, sat psi k))"
      using loop_assms(1)
      by (auto simp: loop_inv_def s_def j_cur_def[symmetric])
    have wf': "wf_vydra phi (Suc j_cur) n vphi'_cur" "tphi_cur = \<tau> \<sigma> j_cur" "bphi_cur = sat phi j_cur"
      "wf_vydra psi (Suc j_cur) n vpsi'_cur" "tpsi_cur = \<tau> \<sigma> j_cur" "bpsi_cur = sat psi j_cur"
      using Until(3)[OF wf(1) run_vphi] Until(4)[OF wf(2) run_vpsi] Until(7,8)
      apply (auto)
      done
    have s'_def: "s' = (vphi'_cur, vpsi'_cur, epsi'_cur, Suc c_cur, Some (t'_cur, (bphi_cur, bpsi_cur)))"
      using loop_assms(3)
      by (auto simp: while_until_body_def s_def run_epsi run_vphi run_vpsi)
    obtain gs_cur where gs_cur_def: "reaches_on ru_t l_t0 gs_cur epsi_cur"
      "length gs_cur = j_cur" "\<And>t. t \<in> set gs_cur \<Longrightarrow> memR (\<tau> \<sigma> i) t I"
      using loop_assms(1)
      by (auto simp: loop_inv_def s_def j_cur_def[symmetric])
    have t'_cur_def: "t'_cur = \<tau> \<sigma> j_cur"
      using ru_t_tau[OF gs_cur_def(1) run_epsi]
      by (auto simp: gs_cur_def(2))
    have t'_cur_right_I: "memR t t'_cur I"
      using loop_assms(2) run_t_read[OF run_epsi]
      by (auto simp: while_until_cond_def s_def)
    have c_cur_zero: "c_cur = 0 \<Longrightarrow> j_cur = i"
      by (auto simp: j_cur_def)
    have "k \<in> {i..<Suc j_cur - 1} \<Longrightarrow> sat phi k \<and> (memL (\<tau> \<sigma> i) (\<tau> \<sigma> k) I \<longrightarrow> \<not>sat psi k)" for k
      using loop_assms(1,2)
      by (cases "k = j_cur - Suc 0") (auto simp: while_until_cond_def loop_inv_def j_cur_def[symmetric] zo_cur_def s_def until_ready_def t_def split: nat.splits dest: c_cur_zero)
    then show ?thesis
      using wf' t'_cur_right_I
      using reaches_on_app[OF gs_cur_def(1) run_epsi] gs_cur_def(2,3)
      by (auto simp: loop_inv_def s'_def j_cur_def[symmetric] t_def t'_cur_def intro!: exI[of _ "gs_cur @ [t'_cur]"])
  qed
  have wf_loop: "wf {(s', s). loop_inv s \<and> while_until_cond I t s \<and> Some s' = while_until_body run_hd (ru n) s}"
  proof -
    obtain m where m_def: "\<not>\<tau> \<sigma> m \<le> \<tau> \<sigma> i + right I"
      using ex_lt_\<tau>[where ?x="right I" and ?s=\<sigma>] Until(7)
      by auto
    define X where "X = {(s', s). loop_inv s \<and> while_until_cond I t s \<and> Some s' = while_until_body run_hd (ru n) s}"
    have "memR t (\<tau> \<sigma> (i + c)) I \<Longrightarrow> i + c < m" for c
      using m_def order_trans[OF \<tau>_mono[where ?i=m and ?j="i + c" and ?s=\<sigma>]]
      by (fastforce simp: t_def dest!: memR_dest)
    then have "X \<subseteq> measure (\<lambda>(vphi, vpsi, epsi, c, zo). m - c)"
      by (fastforce simp: X_def while_until_cond_def while_until_body_def loop_inv_def Let_def split: option.splits
          dest!: read_t_run[where ?run_hd=run_hd] dest: ru_t_tau)
    then show ?thesis
      using wf_subset
      by (auto simp: X_def[symmetric])
  qed
  have loop: "loop_inv (vphi', vpsi', epsi', c', zo')" "\<not>while_until_cond I t (vphi', vpsi', epsi', c', zo')"
    using while_break_sound[where ?Q="\<lambda>s. loop_inv s \<and> \<not>while_until_cond I t s", OF _ _ wf_loop loop_inv_init] loop_step
    by (auto simp: loop_def)
  have tau_right_I: "k < j' \<Longrightarrow> memR (\<tau> \<sigma> i) (\<tau> \<sigma> k) I" for k
    using loop(1) ru_t_tau_in
    by (auto simp: loop_inv_def j'_def[symmetric] in_set_conv_nth)
  have read_t_epsi': "read_t epsi' = Some et \<Longrightarrow> et = \<tau> \<sigma> j'" for et
    using loop(1) ru_t_tau
    by (fastforce simp: loop_inv_def Let_def j'_def dest!: read_t_run[where ?run_hd=run_hd])
  have end_cond: "until_ready I t c' zo' \<or> \<not>(memR (\<tau> \<sigma> i) (\<tau> \<sigma> j') I)"
    unfolding t_def[symmetric]
    using Until(6) c'_pos loop(2)[unfolded while_until_cond_def]
    by (auto simp: until_ready_def v_def(1) run_back loop_init_def[symmetric] loop_def zo'_Some split: if_splits option.splits nat.splits dest: read_t_epsi')
  have Suc_i_le_j': "Suc i \<le> j'" and c'_j': "c' - Suc 0 = j' - Suc i"
    using end_cond c'_pos
    by (auto simp: until_ready_def j'_def split: nat.splits)
  have zo'_def: "zo' = (case j' of 0 \<Rightarrow> None | Suc k \<Rightarrow> Some (\<tau> \<sigma> k, sat phi k, sat psi k))"
    and sat_phi: "k \<in> {i..<j' - 1} \<Longrightarrow> sat phi k"
    and not_sat_psi: "k \<in> {i..<j' - 1} \<Longrightarrow> memL (\<tau> \<sigma> i) (\<tau> \<sigma> k) I \<Longrightarrow> \<not>sat psi k" for k
    using loop(1)
    by (auto simp: loop_inv_def j'_def[symmetric])
  have b_sat: "b = sat (Until phi I psi) i"
  proof (rule iffI)
    assume b: "b"
    have mem: "mem (\<tau> \<sigma> i) (\<tau> \<sigma> (j' - Suc 0)) I"
      using b zo'_def tau_right_I[where ?k="j' - 1"]
      by (auto simp: mem_def b_def t_def zo'_Some split: nat.splits)
    have sat_psi: "sat psi (j' - 1)"
      using b zo'_def
      by (auto simp: b_def zo'_Some split: nat.splits)
    show "sat (Until phi I psi) i"
      using Suc_i_le_j' mem sat_psi sat_phi
      by (auto intro!: exI[of _ "j' - 1"])
  next
    assume "sat (Until phi I psi) i"
    then obtain k where k_def: "i \<le> k" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> k) I" "sat psi k" "\<forall>m \<in> {i..<k}. sat phi m"
      by auto
    define X where "X = {m \<in> {i..k}. memL (\<tau> \<sigma> i) (\<tau> \<sigma> m) I \<and> sat psi m}"
    have fin_X: "finite X" and X_nonempty: "X \<noteq> {}" and k_X: "k \<in> X"
      using k_def
      by (auto simp: X_def mem_def)
    define km where "km = Min X"
    note aux = Min_in[OF fin_X X_nonempty, folded km_def]
    have km_def: "i \<le> km" "km \<le> k" "memL (\<tau> \<sigma> i) (\<tau> \<sigma> km) I" "sat psi km" "\<forall>m \<in> {i..<km}. sat phi m"
      "\<forall>m \<in> {i..<km}. memL (\<tau> \<sigma> i) (\<tau> \<sigma> m) I \<longrightarrow> \<not>sat psi m"
      using aux Min_le[OF fin_X, folded km_def] k_def(4)
      by (fastforce simp: X_def)+
    have j'_le_km: "j' - 1 \<le> km"
      using not_sat_psi[OF _ km_def(3)] km_def(1,4)
      by fastforce
    show "b"
    proof (cases "j' - 1 < km")
      case True
      have "until_ready I t c' zo'"
        using end_cond True km_def(2) k_def(2) memR_mono'[OF _ \<tau>_mono[where ?i=j' and ?j=k and ?s=\<sigma>]]
        by (auto simp: mem_def)
      then show ?thesis
        using c'_pos zo'_def km_def(5) Suc_i_le_j' True
        by (auto simp: until_ready_def zo'_Some b_def split: nat.splits)
    next
      case False
      have km_j': "km = j' - 1"
        using j'_le_km False
        by auto
      show ?thesis
        using c'_pos zo'_def km_def(3,4)
        by (auto simp: zo'_Some b_def km_j' t_def split: nat.splits)
    qed
  qed
  obtain gs where gs_def: "reaches_on ru_t l_t0 gs epsi'" "length gs = j'"
    "\<And>t. t \<in> set gs \<Longrightarrow> memR (\<tau> \<sigma> i) t I"
    using loop(1)
    by (auto simp: loop_inv_def j'_def[symmetric])
  note aux = \<tau>_mono[where ?s=\<sigma> and ?i=i and ?j="Suc i"]
  have wf_v': "wf_vydra (Until phi I psi) (Suc i) (Suc n) v'"
    unfolding v'_def
    apply (rule wf_vydra.intros(10)[where ?j=j' and ?es'=gs])
    using loop(1) reaches_on_app[OF v_def(5) run_back] Suc_i_le_j' c'_j' memL_mono[OF _ aux] memR_mono[OF _ aux] gs_def
    by (auto simp: loop_inv_def j'_def[symmetric] v_def(6,8))
  show ?case
    using wf_v' ru_t_event[OF v_def(5) refl run_back]
    by (auto simp: b_sat v_def(6))
next
  case (MatchP n I r)
  have IH: "x \<in> set (collect_subfmlas r []) \<Longrightarrow> wf_vydra x j n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x (Suc j) n v' \<and> t = \<tau> \<sigma> j \<and> b = sat x j" for x j v v' t b
    using MatchP(2,1,5,6) le_trans[OF collect_subfmlas_msize]
    using bf_collect_subfmlas[where ?r="r" and ?phis="[]"]
    by (fastforce simp: collect_subfmlas_atms[where ?phis="[]", simplified, symmetric])
  have "reaches_on (ru n) (su n phi) vs v \<Longrightarrow> wf_vydra phi (length vs) n v" if phi: "phi \<in> set (collect_subfmlas r [])" for phi vs v
    apply (induction vs arbitrary: v rule: rev_induct)
    using MatchP(1) wf_vydra_sub collect_subfmlas_msize[OF phi]
     apply (auto elim!: reaches_on.cases)[1]
    using IH[OF phi]
    apply (fastforce dest!: reaches_on_split_last)
    done
  then have wf: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) bs s \<Longrightarrow> j < length (collect_subfmlas r []) \<Longrightarrow>
    wf_vydra (collect_subfmlas r [] ! j) (length bs) n (s ! j)" for bs s j
    using reach_run_subs_run
    by (fastforce simp: in_set_conv_nth)
  let ?qf = "state_cnt r"
  let ?transs = "iarray_of_list (build_nfa_impl r (0, ?qf, []))"
  define args where "args = init_args ({0}, NFA.delta' ?transs ?qf, NFA.accept' ?transs ?qf) (ru_t, read_t) (run_subs (ru n))"
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[where ?r=r and ?n=n, OF _ wf _ reach_run_subs_len[where ?n=n]] IH run_t_read[of run_hd]
      read_t_run[of _ _ run_hd] ru_t_tau MatchP(5) collect_subfmlas_atms[where ?phis="[]"]
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  obtain w xs where w_def: "v = VYDRA_MatchP I ?transs ?qf w"
    "valid_window_matchP args I l_t0 (map (su n) (collect_subfmlas r [])) xs i w"
    using MatchP(3,4)
    by (auto simp: args_def elim!: wf_vydra.cases[of _ _ _ v])
  obtain tj' t' sj' bs where somes: "w_run_t args (w_tj w) = Some (tj', t')"
   "w_run_sub args (w_sj w) = Some (sj', bs)"
   using MatchP(4)
   by (auto simp: w_def(1) adv_end_def args_def Let_def split: option.splits prod.splits)
  obtain w' where w'_def: "eval_mP I w = Some ((\<tau> \<sigma> i, sat (MatchP I r) i), w')"
    "t' = \<tau> \<sigma> i" "valid_matchP I l_t0 (map (su n) (collect_subfmlas r [])) (xs @ [(t', bs)]) (Suc i) w'"
    using valid_eval_matchP[OF w_def(2) somes] MatchP(6)
    by auto
  have v'_def: "v' = VYDRA_MatchP I ?transs ?qf w'" "(t, b) = (\<tau> \<sigma> i, sat (MatchP I r) i)"
    using MatchP(4)
    by (auto simp: w_def(1) args_def[symmetric] w'_def(1) simp del: eval_matchP.simps init_args.simps)
  have len_xs: "length xs = i"
    using w'_def(3)
    by (auto simp: valid_window_matchP_def)
  have "\<exists>es e. reaches_on run_hd init_hd es e \<and> length es = Suc i"
    using ru_t_event valid_window_matchP_reach_tj[OF w_def(2)] somes(1) len_xs
    by (fastforce simp: args_def)
  then show ?case
    using MatchP(1) v'_def(2)  w'_def(3)
    by (auto simp: v'_def(1) args_def[symmetric] simp del: init_args.simps intro!: wf_vydra.intros(11))
next
  case (MatchF n I r)
  have IH: "x \<in> set (collect_subfmlas r []) \<Longrightarrow> wf_vydra x j n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x (Suc j) n v' \<and> t = \<tau> \<sigma> j \<and> b = sat x j" for x j v v' t b
    using MatchF(2,1,5,6) le_trans[OF collect_subfmlas_msize]
    using bf_collect_subfmlas[where ?r="r" and ?phis="[]"]
    by (fastforce simp: collect_subfmlas_atms[where ?phis="[]", simplified, symmetric])
  have "reaches_on (ru n) (su n phi) vs v \<Longrightarrow> wf_vydra phi (length vs) n v" if phi: "phi \<in> set (collect_subfmlas r [])" for phi vs v
    apply (induction vs arbitrary: v rule: rev_induct)
    using MatchF(1) wf_vydra_sub collect_subfmlas_msize[OF phi]
     apply (auto elim!: reaches_on.cases)[1]
    using IH[OF phi]
    apply (fastforce dest!: reaches_on_split_last)
    done
  then have wf: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) bs s \<Longrightarrow> j < length (collect_subfmlas r []) \<Longrightarrow>
    wf_vydra (collect_subfmlas r [] ! j) (length bs) n (s ! j)" for bs s j
    using reach_run_subs_run
    by (fastforce simp: in_set_conv_nth)
  let ?qf = "state_cnt r"
  let ?transs = "iarray_of_list (build_nfa_impl r (0, ?qf, []))"
  define args where "args = init_args ({0}, NFA.delta' ?transs ?qf, NFA.accept' ?transs ?qf) (ru_t, read_t) (run_subs (ru n))"
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[where ?r=r and ?n=n, OF _ wf _ reach_run_subs_len[where ?n=n]] IH run_t_read[of run_hd]
      read_t_run[of _ _ run_hd] ru_t_tau MatchF(5) collect_subfmlas_atms[where ?phis="[]"]
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  obtain w xs where w_def: "v = VYDRA_MatchF I ?transs ?qf w"
    "valid_window_matchF args I l_t0 (map (su n) (collect_subfmlas r [])) xs i w"
    using MatchF(3,4)
    by (auto simp: args_def elim!: wf_vydra.cases[of _ _ _ v])
  obtain w' rho' where w'_def: "eval_mF I w = Some ((t, b), w')" "valid_matchF I l_t0 (map (su n) (collect_subfmlas r [])) rho' (Suc i) w'" "t = \<tau> \<sigma> i" "b = sat (MatchF I r) i"
    using valid_eval_matchF_sound[OF w_def(2)] MatchF(4,5,6)
    by (fastforce simp: w_def(1) args_def[symmetric] simp del: eval_matchF.simps init_args.simps split: option.splits)
  have v'_def: "v' = VYDRA_MatchF I ?transs ?qf w'"
    using MatchF(4)
    by (auto simp: w_def(1) args_def[symmetric] w'_def(1) simp del: eval_matchF.simps init_args.simps)
  obtain w_ti' ti where ru_w_ti: "ru_t (w_ti w) = Some (w_ti', ti)"
    using MatchF(4) read_t_run
    by (auto simp: w_def(1) args_def split: option.splits)
  have "\<exists>es e. reaches_on run_hd init_hd es e \<and> length es = Suc i"
    using w_def(2) ru_t_event[OF _ refl ru_w_ti, where ?ts="take (w_i w) (map fst xs)"]
    by (auto simp: valid_window_matchF_def args_def)
  then show ?case
    using MatchF(1) w'_def(2)
    by (auto simp: v'_def(1) args_def[symmetric] w'_def(3,4) simp del: init_args.simps intro!: wf_vydra.intros(12))
qed

lemma reaches_ons_run_lD: "reaches_on (run_subs (ru n)) vs ws vs' \<Longrightarrow>
  length vs = length vs'"
  by (induction vs ws vs' rule: reaches_on_rev_induct)
     (auto simp: run_subs_def Let_def split: option.splits if_splits)

lemma reaches_ons_run_vD: "reaches_on (run_subs (ru n)) vs ws vs' \<Longrightarrow>
  i < length vs \<Longrightarrow> (\<exists>ys. reaches_on (ru n) (vs ! i) ys (vs' ! i) \<and> length ys = length ws)"
proof (induction vs ws vs' rule: reaches_on_rev_induct)
  case (2 s s' bs bss s'')
  obtain ys where ys_def: "reaches_on (ru n) (s ! i) ys (s' ! i)"
    "length s = length s'" "length ys = length bss"
    using reaches_ons_run_lD[OF 2(1)] 2(3)[OF 2(4)]
    by auto
  obtain tb where tb_def: "ru n (s' ! i) = Some (s'' ! i, tb)"
    using run_subs_vD[OF 2(2) 2(4)[unfolded ys_def(2)]]
    by auto
  show ?case
    using reaches_on_app[OF ys_def(1) tb_def(1)] ys_def(2,3) tb_def
    by auto
qed (auto intro: reaches_on.intros)

lemma reaches_ons_runI:
  assumes "\<And>phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow> \<exists>ws v. reaches_on (ru n) (su n phi) ws v \<and> length ws = i"
  shows "\<exists>ws v. reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) ws v \<and> length ws = i"
  using assms
proof (induction i)
  case 0
  show ?case
    by (fastforce intro: reaches_on.intros)
next
  case (Suc i)
  have IH': "\<And>phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow> \<exists>ws v. reaches_on (ru n) (su n phi) ws v \<and> length ws = i \<and> ru n v \<noteq> None"
  proof -
    fix phi
    assume lassm: "phi \<in> set (collect_subfmlas r [])"
    obtain ws v where ws_def: "reaches_on (ru n) (su n phi) ws v"
      "length ws = Suc i"
      using Suc(2)[OF lassm]
      by auto
    obtain y ys where ws_snoc: "ws = ys @ [y]"
      using ws_def(2)
      by (cases ws rule: rev_cases) auto
    show "\<exists>ws v. reaches_on (ru n) (su n phi) ws v \<and> length ws = i \<and> ru n v \<noteq> None"
      using reaches_on_split_last[OF ws_def(1)[unfolded ws_snoc]] ws_def(2) ws_snoc
      by fastforce
  qed
  obtain ws v where ws_def: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) ws v" "length ws = i"
    using Suc(1) IH'
    by blast
  have "x \<in> set v \<Longrightarrow> Option.is_none (ru n x) \<Longrightarrow> False" for x
    using ws_def IH'
    by (auto simp: in_set_conv_nth) (metis is_none_code(2) reach_run_subs_len reach_run_subs_run reaches_on_inj)
  then obtain v' tb where v'_def: "run_subs (ru n) v = Some (v', tb)"
    by (fastforce simp: run_subs_def Let_def)
  show ?case
    using reaches_on_app[OF ws_def(1) v'_def] ws_def(2)
    by fastforce
qed

lemma reaches_on_takeWhile: "reaches_on r s vs s' \<Longrightarrow> r s' = Some (s'', v) \<Longrightarrow> \<not>f v \<Longrightarrow>
  vs' = takeWhile f vs \<Longrightarrow>
  \<exists>t' t'' v'. reaches_on r s vs' t' \<and> r t' = Some (t'', v') \<and> \<not>f v' \<and>
  reaches_on r t' (drop (length vs') vs) s'"
  by (induction s vs s' arbitrary: vs' rule: reaches_on.induct) (auto intro: reaches_on.intros)

lemma reaches_on_suffix:
  assumes "reaches_on r s vs s'" "reaches_on r s vs' s''" "length vs' \<le> length vs"
  shows "\<exists>vs''. reaches_on r s'' vs'' s' \<and> vs = vs' @ vs''"
  using reaches_on_split'[where ?i="length vs'", OF assms(1,3)] assms(3) reaches_on_inj[OF assms(2)]
  by (metis add_diff_cancel_right' append_take_drop_id diff_diff_cancel length_append length_drop)

lemma vydra_wf_reaches_on:
  assumes "\<And>j v. j < i \<Longrightarrow> wf_vydra \<phi> j n v \<Longrightarrow> ru n v = None \<Longrightarrow> False" "bounded_future_fmla \<phi>" "wf_fmla \<phi>" "msize_fmla \<phi> \<le> n"
  shows "\<exists>vs v. reaches_on (ru n) (su n \<phi>) vs v \<and> wf_vydra \<phi> i n v \<and> length vs = i"
  using assms(1)
proof (induction i)
  case (Suc i)
  obtain vs v where IH: "reaches_on (ru n) (su n \<phi>) vs v" "wf_vydra \<phi> i n v" "length vs = i"
    using Suc(1) Suc(2)[OF less_SucI]
    by auto
  show ?case
    using reaches_on_app[OF IH(1)] Suc(2)[OF _ IH(2)] vydra_sound_aux[OF assms(4) IH(2) _ assms(2,3)] IH(3)
    by fastforce
qed (auto intro: reaches_on.intros wf_vydra_sub[OF assms(4)])

lemma reaches_on_Some:
  assumes "reaches_on r s vs s'" "reaches_on r s vs' s''" "length vs < length vs'"
  shows "\<exists>s''' x. r s' = Some (s''', x)"
  using reaches_on_split[OF assms(2,3)] reaches_on_inj[OF assms(1)] assms(3)
  by auto

lemma reaches_on_progress:
  assumes "reaches_on run_hd init_hd vs e"
  shows "progress phi (map fst vs) \<le> length vs"
  using progress_le_ts[of "map fst vs" phi] reaches_on_run_hd \<tau>_fin
  by (fastforce dest!: reaches_on_setD[OF assms] reaches_on_split_last)

lemma vydra_complete_aux:
  assumes prefix: "reaches_on run_hd init_hd vs e"
    and run: "wf_vydra \<phi> i n v" "ru n v = None" "i < progress \<phi> (map fst vs)" "bounded_future_fmla \<phi>" "wf_fmla \<phi>"
    and msize: "msize_fmla \<phi> \<le> n"
  shows "False"
  using msize run
proof (induction n \<phi> arbitrary: i v rule: run_induct)
  case (Bool b n)
  have False if v_def: "v = VYDRA_Bool b g" for g
  proof -
    obtain es where g_def: "reaches_on run_hd init_hd es g" "length es = i"
      using Bool(1)
      by (auto simp: v_def elim: wf_vydra.cases)
    show False
      using Bool(2) reaches_on_Some[OF g_def(1) prefix] Bool(3)
      by (auto simp: v_def g_def(2) split: option.splits)
  qed
  then show False
    using Bool(1)
    by (auto elim!: wf_vydra.cases[of _ _ _ v])
next
  case (Atom a n)
  have False if v_def: "v = VYDRA_Atom a g" for g
  proof -
    obtain es where g_def: "reaches_on run_hd init_hd es g" "length es = i"
      using Atom(1)
      by (auto simp: v_def elim: wf_vydra.cases)
    show False
      using Atom(2) reaches_on_Some[OF g_def(1) prefix] Atom(3)
      by (auto simp: v_def g_def(2) split: option.splits)
  qed
  then show False
    using Atom(1)
    by (auto elim!: wf_vydra.cases[of _ _ _ v])
next
  case (Neg n phi)
  show ?case
    apply (rule wf_vydra.cases[OF Neg(3)])
    using Neg
    by (fastforce split: option.splits)+
next
  case (Bin n f phi psi)
  show ?case
    apply (rule wf_vydra.cases[OF Bin(4)])
    using Bin
    by (fastforce split: option.splits)+
next
  case (Prev n I phi)
  show ?case
  proof (cases i)
    case 0
    obtain vphi where v_def: "v = VYDRA_Prev I vphi init_hd None"
      using Prev(3)
      by (auto simp: 0 dest: reaches_on_NilD elim!: wf_vydra.cases[of "Prev I phi"])
    show ?thesis
      using Prev(4,5) prefix
      by (auto simp: 0 v_def elim: reaches_on.cases split: option.splits)
  next
    case (Suc j)
    show ?thesis
    proof (cases "v = VYDRA_None")
      case v_def: True
      obtain w where w_def: "wf_vydra phi j n w" "ru n w = None"
        using Prev(3)
        by (auto simp: Suc v_def elim!: wf_vydra.cases[of "Prev I phi"])
      show ?thesis
        using Prev(2)[OF w_def(1,2)] Prev(5,6,7)
        by (auto simp: Suc)
    next
      case False
      obtain vphi tphi bphi es g where v_def: "v = VYDRA_Prev I vphi g (Some (tphi, bphi))"
        "wf_vydra phi (Suc j) n vphi" "reaches_on run_hd init_hd es g" "length es = Suc j"
        using Prev(3) False
        by (auto simp: Suc elim!: wf_vydra.cases[of "Prev I phi"])
      show ?thesis
        using Prev(4,5) reaches_on_Some[OF v_def(3) prefix]
        by (auto simp: Let_def Suc v_def(1,4) split: option.splits)
    qed
  qed
next
  case (Next n I phi)
  show ?case
  proof (cases "v = VYDRA_None")
    case True
    obtain w where w_def: "wf_vydra phi i n w" "ru n w = None"
      using Next(3)
      by (auto simp: True elim: wf_vydra.cases)
    show ?thesis
      using Next(2)[OF w_def] Next(5,6,7)
      by (auto split: nat.splits)
  next
    case False
    obtain w sub to es where v_def: "v = VYDRA_Next I w sub to" "wf_vydra phi (length es) n w"
      "reaches_on run_hd init_hd es sub" "length es = (case to of None \<Rightarrow> 0 | _ \<Rightarrow> Suc i)"
      "case to of None \<Rightarrow> i = 0 | Some told \<Rightarrow> told = \<tau> \<sigma> i"
      using Next(3) False
      by (auto elim!: wf_vydra.cases[of _ _ _ v] split: option.splits nat.splits)
    show ?thesis
    proof (cases to)
      case None
      obtain w' tw' bw' where w'_def: "ru n w = Some (w', (tw', bw'))"
        using Next(2)[OF v_def(2)] Next(5,6,7)
        by (fastforce simp: v_def(4) None split: nat.splits)
      have wf: "wf_vydra phi (Suc (length es)) n w'"
        using v_def(4,5) vydra_sound_aux[OF Next(1) v_def(2) w'_def] Next(6,7)
        by (auto simp: None)
      show ?thesis
        using Next(2)[OF wf] Next(4,5,6,7) reaches_on_Some[OF v_def(3) prefix]
          reaches_on_Some[OF reaches_on_app[OF v_def(3)] prefix] reaches_on_progress[OF prefix, where ?phi=phi]
        by (cases vs) (fastforce simp: v_def(1,4) w'_def None split: option.splits nat.splits if_splits)+
    next
      case (Some z)
      show ?thesis
        using Next(2)[OF v_def(2)] Next(4,5,6,7) reaches_on_Some[OF v_def(3) prefix] reaches_on_progress[OF prefix, where ?phi=phi]
        by (auto simp: v_def(1,4) Some split: option.splits nat.splits)
    qed
  qed
next
  case (Since n I phi psi)
  obtain vphi vpsi g cphi cpsi cppsi tppsi j gs where v_def:
    "v = VYDRA_Since I vphi vpsi g cphi cpsi cppsi tppsi"
    "wf_vydra phi i n vphi" "wf_vydra psi j n vpsi" "j \<le> i"
    "reaches_on ru_t l_t0 gs g" "length gs = j" "cpsi = i - j"
    using Since(5)
    by (auto elim: wf_vydra.cases)
  obtain vphi' t1 b1 where run_vphi: "ru n vphi = Some (vphi', t1, b1)"
    using Since(3)[OF v_def(2)] Since(7,8,9)
    by fastforce
  obtain cs c where wf_vphi': "wf_vydra phi (Suc i) n vphi'"
    and reaches_Suc_i: "reaches_on run_hd init_hd cs c" "length cs = Suc i"
    and t1_def: "t1 = \<tau> \<sigma> i"
    using vydra_sound_aux[OF Since(1) v_def(2) run_vphi] Since(8,9)
    by auto
  note ru_t_Some = ru_t_Some[OF reaches_Suc_i]
  define loop_inv where "loop_inv = (\<lambda>(vpsi, e, cpsi :: nat, cppsi :: nat option, tppsi :: 't option).
    let j = Suc i - cpsi in cpsi \<le> Suc i \<and> wf_vydra psi j n vpsi \<and> (\<exists>es. reaches_on ru_t l_t0 es e \<and> length es = j))"
  define loop_init where "loop_init = (vpsi, g, Suc cpsi, map_option Suc cppsi, tppsi)"
  have j_def: "j = i - cpsi" and cpsi_i: "cpsi \<le> i"
    using v_def(4,7)
    by auto
  then have loop_inv_init: "loop_inv loop_init"
    using v_def(3,5,6,7) last_before_Some
    by (fastforce simp: loop_inv_def loop_init_def Let_def j_def split: option.splits)
  have wf_loop: "wf {(s', s). loop_inv s \<and> while_since_cond I t1 s \<and> Some s' = while_since_body run_hd (ru n) s}"
    by (auto intro: wf_subset[OF wf_since])
  have step_loop: "pred_option' loop_inv (while_since_body run_hd (ru n) s)"
    if loop_assms: "loop_inv s" "while_since_cond I t1 s" for s
  proof -
    obtain vpsi d cpsi cppsi tppsi where s_def: "s = (vpsi, d, cpsi, cppsi, tppsi)"
      by (cases s) auto
    have cpsi_pos: "cpsi > 0"
      using loop_assms(2)
      by (auto simp: while_since_cond_def s_def)
    define j where "j = Suc i - cpsi"
    have j_i: "j \<le> i"
      using cpsi_pos
      by (auto simp: j_def)
    obtain ds where loop_before: "cpsi \<le> Suc i" "wf_vydra psi j n vpsi" "reaches_on ru_t l_t0 ds d" "length ds = j"
      using loop_assms(1)
      by (auto simp: s_def j_def loop_inv_def Let_def)
    obtain h tt where tt_def: "read_t d = Some tt" "d = Some (h, tt)"
      using ru_t_Some[OF loop_before(3)] loop_before(4) loop_assms(2)
      by (cases d) (fastforce simp: while_since_cond_def s_def j_def split: option.splits)+
    obtain d' where d'_def: "reaches_on ru_t l_t0 (ds @ [tt]) d'" "ru_t d = Some (d', tt)"
      using reaches_on_app[OF loop_before(3)] tt_def(1)
      by (cases "run_hd h") (auto simp: tt_def(2))
    obtain vpsi' tpsi' bpsi' where run_vpsi: "ru n vpsi = Some (vpsi', (tpsi', bpsi'))"
      using Since(4) j_i Since(7,8,9) loop_before(2)
      by fastforce
    have wf_psi': "wf_vydra psi (Suc j) n vpsi'" and t'_def: "tpsi' = \<tau> \<sigma> j" and b'_def: "bpsi' = sat psi j"
      using vydra_sound_aux[OF Since(2) loop_before(2) run_vpsi] Since(8,9)
      by auto
    define j' where j'_def: "j' = Suc i - (cpsi - Suc 0)"
    have j'_j: "j' = Suc j"
      using loop_before(1) cpsi_pos
      by (auto simp: j'_def j_def)
    show ?thesis
      using wf_psi'(1) loop_before(1,4) d'_def(1)
      by (fastforce simp: while_since_body_def s_def run_vpsi pred_option'_def loop_inv_def j'_def[symmetric] j'_j d'_def(2) t1_def)
  qed
  show ?case
    using while_break_complete[OF step_loop _ wf_loop loop_inv_init, where ?Q="\<lambda>_. True"] Since(6)
    by (auto simp: pred_option'_def v_def(1) run_vphi Let_def loop_init_def split: option.splits)
next
  case (Until n I phi psi)
  obtain "back" vphi vpsi front c z es es' j where v_def:
    "v = VYDRA_Until I back vphi vpsi front c z"
    "wf_vydra phi j n vphi" "wf_vydra psi j n vpsi" "i \<le> j"
    "reaches_on ru_t l_t0 es back" "length es = i"
    "reaches_on ru_t l_t0 es' front" "length es' = j" "\<And>t. t \<in> set es' \<Longrightarrow> memR (\<tau> \<sigma> i) t I"
    "c = j - i" "z = (case j of 0 \<Rightarrow> None | Suc k \<Rightarrow> Some (\<tau> \<sigma> k, sat phi k, sat psi k))"
    "\<And>k. k \<in> {i..<j - 1} \<Longrightarrow> sat phi k \<and> (memL (\<tau> \<sigma> i) (\<tau> \<sigma> k) I \<longrightarrow> \<not>sat psi k)"
    using Until(5)
    by (auto simp: elim: wf_vydra.cases)
  have ru_t_Some: "reaches_on ru_t l_t0 gs g \<Longrightarrow> length gs < length vs \<Longrightarrow> \<exists>g' gt. ru_t g = Some (g', gt)" for gs g
    using reaches_on_Some reaches_on_run_hd_t[OF prefix]
    by fastforce
  have vs_tau: "map fst vs ! k = \<tau> \<sigma> k" if k_vs: "k < length vs" for k
    using reaches_on_split[OF prefix k_vs] run_hd_sound k_vs
    apply (cases "vs ! k")
    apply (auto)
    apply (metis fst_conv length_map nth_map prefix reaches_on_run_hd_t ru_t_tau_in)
    done
  define m where "m = min (length (map fst vs) - 1) (min (progress phi (map fst vs)) (progress psi (map fst vs)))"
  have m_vs: "m < length vs"
    using Until(7)
    by (cases vs) (auto simp: m_def split: if_splits)
  define A where "A = {j. 0 \<le> j \<and> j \<le> m \<and> memR (map fst vs ! j) (map fst vs ! m) I}"
  have m_A: "m \<in> A"
    using memR_tfin_refl[OF \<tau>_fin] vs_tau[OF m_vs]
    by (fastforce simp: A_def)
  then have A_nonempty: "A \<noteq> {}"
    by auto
  have A_finite: "finite A"
    by (auto simp: A_def)
  have p: "progress (Until phi I psi) (map fst vs) = Min A"
    using Until(7)
    unfolding progress.simps m_def[symmetric] Let_def A_def[symmetric]
    by auto
  have i_A: "i \<notin> A"
    using Until(7) A_finite A_nonempty
    by (auto simp del: progress.simps simp: p)
  have i_m: "i < m"
    using Until(7) m_A A_finite A_nonempty
    by (auto simp del: progress.simps simp: p)
  have memR_i_m: "\<not>memR (map fst vs ! i) (map fst vs ! m) I"
    using i_A i_m
    by (auto simp: A_def)
  have i_vs: "i < length vs"
    using i_m m_vs
    by auto
  have j_m: "j \<le> m"
    using ru_t_tau_in[OF v_def(7), of m] v_def(9)[of "\<tau> \<sigma> m"] memR_i_m
    unfolding vs_tau[OF i_vs] vs_tau[OF m_vs]
    by (force simp: in_set_conv_nth v_def(8))
  have j_vs: "j < length vs"
    using j_m m_vs
    by auto
  obtain back' t where run_back: "ru_t back = Some (back', t)" and t_def: "t = \<tau> \<sigma> i"
    using ru_t_Some[OF v_def(5)] v_def(4) j_vs ru_t_tau[OF v_def(5)]
    by (fastforce simp: v_def(6))
  define loop_inv where "loop_inv = (\<lambda>(vphi, vpsi, front, c, z :: ('t \<times> bool \<times> bool) option).
    let j = i + c in wf_vydra phi j n vphi \<and> wf_vydra psi j n vpsi \<and> j < length vs \<and>
    (\<exists>es'. reaches_on ru_t l_t0 es' front \<and> length es' = j) \<and>
    (z = None \<longrightarrow> j = 0))"
  define loop_init where "loop_init = (vphi, vpsi, front, c, z)"
  have j_eq: "j = i + c"
    using v_def(4)
    by (auto simp: v_def(10))
  have "j = 0 \<Longrightarrow> c = 0"
    by (auto simp: j_eq)
  then have loop_inv_init: "loop_inv loop_init"
    using v_def(2,3,4,7,8,9,11) j_vs
    by (auto simp: loop_inv_def loop_init_def j_eq[symmetric] split: nat.splits)
  have loop_step: "pred_option' loop_inv (while_until_body run_hd (ru n) s)" if loop_assms: "loop_inv s" "while_until_cond I t s" for s
  proof -
    obtain vphi_cur vpsi_cur epsi_cur c_cur zo_cur where s_def: "s = (vphi_cur, vpsi_cur, epsi_cur, c_cur, zo_cur)"
      by (cases s) auto
    define j_cur where "j_cur = i + c_cur"
    obtain gs where wf: "wf_vydra phi j_cur n vphi_cur" "wf_vydra psi j_cur n vpsi_cur"
      and gs_def: "reaches_on ru_t l_t0 gs epsi_cur" "length gs = j_cur"
      and j_cur_vs: "j_cur < length vs"
      using loop_assms(1)
      by (auto simp: loop_inv_def s_def j_cur_def[symmetric])
    obtain epsi'_cur t'_cur where run_epsi: "ru_t epsi_cur = Some (epsi'_cur, t'_cur)"
      and t'_cur_def: "t'_cur = \<tau> \<sigma> (length gs)"
      using ru_t_Some[OF gs_def(1)] ru_t_event[OF gs_def(1) refl] j_cur_vs
      by (auto simp: gs_def(2))
    have j_m: "j_cur < m"
      using loop_assms(2) memR_i_m memR_mono'[OF _ \<tau>_mono, of _ _ _ _ m]
      unfolding vs_tau[OF i_vs] vs_tau[OF m_vs]
      by (fastforce simp: gs_def(2) while_until_cond_def s_def run_t_read[OF run_epsi] t_def t'_cur_def)
    have j_cur_prog_phi: "j_cur < progress phi (map fst vs)"
      using j_m
      by (auto simp: m_def)
    have j_cur_prog_psi: "j_cur < progress psi (map fst vs)"
      using j_m
      by (auto simp: m_def)
    obtain vphi'_cur tphi_cur bphi_cur where run_vphi: "ru n vphi_cur = Some (vphi'_cur, (tphi_cur, bphi_cur))"
      using Until(3)[OF wf(1) _ j_cur_prog_phi] Until(8,9)
      by fastforce
    obtain vpsi'_cur tpsi_cur bpsi_cur where run_vpsi: "ru n vpsi_cur = Some (vpsi'_cur, (tpsi_cur, bpsi_cur))"
      using Until(4)[OF wf(2) _ j_cur_prog_psi] Until(8,9)
      by fastforce
    have wf': "wf_vydra phi (Suc j_cur) n vphi'_cur" "wf_vydra psi (Suc j_cur) n vpsi'_cur"
      using vydra_sound_aux[OF Until(1) wf(1) run_vphi] vydra_sound_aux[OF Until(2) wf(2) run_vpsi] Until(8,9)
      by auto
    show ?thesis
      using wf' reaches_on_app[OF gs_def(1) run_epsi] gs_def(2) j_m m_vs
      by (auto simp: pred_option'_def while_until_body_def s_def run_epsi run_vphi run_vpsi loop_inv_def j_cur_def[symmetric])
  qed
  have wf_loop: "wf {(s', s). loop_inv s \<and> while_until_cond I t s \<and> Some s' = while_until_body run_hd (ru n) s}"
  proof -
    obtain m where m_def: "\<not>\<tau> \<sigma> m \<le> \<tau> \<sigma> i + right I"
      using ex_lt_\<tau>[where ?x="right I" and ?s=\<sigma>] Until(8)
      by auto
    define X where "X = {(s', s). loop_inv s \<and> while_until_cond I t s \<and> Some s' = while_until_body run_hd (ru n) s}"
    have "memR t (\<tau> \<sigma> (i + c)) I \<Longrightarrow> i + c < m" for c
      using m_def order_trans[OF \<tau>_mono[where ?i=m and ?j="i + c" and ?s=\<sigma>]]
      by (fastforce simp: t_def dest!: memR_dest)
    then have "X \<subseteq> measure (\<lambda>(vphi, vpsi, epsi, c, zo). m - c)"
      by (fastforce simp: X_def while_until_cond_def while_until_body_def loop_inv_def Let_def split: option.splits
          dest!: read_t_run[where ?run_hd=run_hd] dest: ru_t_tau)
    then show ?thesis
      using wf_subset
      by (auto simp: X_def[symmetric])
  qed
  obtain vphi' vpsi' front' c' z' where loop:
    "while_break (while_until_cond I t) (while_until_body run_hd (ru n)) loop_init = Some (vphi', vpsi', front', c', z')"
    "loop_inv (vphi', vpsi', front', c', z')" "\<not>while_until_cond I t (vphi', vpsi', front', c', z')"
    using while_break_complete[where ?P="loop_inv", OF loop_step _ wf_loop loop_inv_init]
    by (cases "while_break (while_until_cond I t) (while_until_body run_hd (ru n)) loop_init") (force simp: pred_option'_def)+
  define j' where "j' = i + c'"
  obtain tf where read_front': "read_t front' = Some tf"
    using loop(2)
    by (auto simp: loop_inv_def j'_def[symmetric] dest!: ru_t_Some run_t_read[where ?run_hd=run_hd])
  have tf_fin: "tf \<in> tfin"
    using loop(2) ru_t_Some[where ?g=front'] ru_t_tau[where ?t'=front'] read_t_run[OF read_front'] \<tau>_fin[where ?\<sigma>=\<sigma>]
    by (fastforce simp: loop_inv_def j'_def[symmetric])
  have c'_pos: "c' = 0 \<Longrightarrow> False"
    using loop(2,3) ru_t_tau ru_t_tau[OF reaches_on.intros(1)] read_t_run[OF read_front']
      memR_tfin_refl[OF tf_fin]
    by (fastforce simp: loop_inv_def while_until_cond_def until_ready_def read_front' t_def dest!: reaches_on_NilD)
  have z'_Some: "z' = None \<Longrightarrow> False"
    using loop(2) c'_pos
    by (auto simp: loop_inv_def j'_def[symmetric])
  show ?case
    using Until(6) c'_pos z'_Some
    by (auto simp: v_def(1) run_back loop_init_def[symmetric] loop(1) read_front' split: if_splits option.splits)
next
  case (MatchP n I r)
  have msize_sub: "\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n"
    using le_trans[OF collect_subfmlas_msize] MatchP(1)
    by auto
  have sound: "x \<in> set (collect_subfmlas r []) \<Longrightarrow> wf_vydra x j n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x (Suc j) n v' \<and> t = \<tau> \<sigma> j \<and> b = sat x j" for x j v v' t b
    using MatchP vydra_sound_aux[OF msize_sub] le_trans[OF collect_subfmlas_msize]
    using bf_collect_subfmlas[where ?r="r" and ?phis="[]"]
    by (fastforce simp: collect_subfmlas_atms[where ?phis="[]", simplified, symmetric])
  have "reaches_on (ru n) (su n phi) vs v \<Longrightarrow> wf_vydra phi (length vs) n v" if phi: "phi \<in> set (collect_subfmlas r [])" for phi vs v
    apply (induction vs arbitrary: v rule: rev_induct)
    using MatchP(1) wf_vydra_sub collect_subfmlas_msize[OF phi]
     apply (auto elim!: reaches_on.cases)[1]
    using sound[OF phi]
    apply (fastforce dest!: reaches_on_split_last)
    done
  then have wf: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) bs s \<Longrightarrow> j < length (collect_subfmlas r []) \<Longrightarrow>
    wf_vydra (collect_subfmlas r [] ! j) (length bs) n (s ! j)" for bs s j
    using reach_run_subs_run
    by (fastforce simp: in_set_conv_nth)
  let ?qf = "state_cnt r"
  let ?transs = "iarray_of_list (build_nfa_impl r (0, ?qf, []))"
  define args where "args = init_args ({0}, NFA.delta' ?transs ?qf, NFA.accept' ?transs ?qf) (ru_t, read_t) (run_subs (ru n))"
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[where ?r=r and ?n=n, OF _ wf _ reach_run_subs_len[where ?n=n]] sound run_t_read[of run_hd]
      read_t_run[of _ _ run_hd] ru_t_tau MatchP(5) collect_subfmlas_atms[where ?phis="[]"]
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  obtain w xs where w_def: "v = VYDRA_MatchP I ?transs ?qf w"
    "valid_window_matchP args I l_t0 (map (su n) (collect_subfmlas r [])) xs i w"
    using MatchP(3)
    by (auto simp: args_def elim!: wf_vydra.cases)
  note args' = args_def[unfolded init_args.simps, symmetric]
  have run_args: "w_run_t args = ru_t" "w_run_sub args = run_subs (ru n)"
    by (auto simp: args_def)
  have len_xs: "length xs = i"
    using w_def(2)
    by (auto simp: valid_window_matchP_def)
  obtain ej tj where w_tj: "ru_t (w_tj w) = Some (ej, tj)"
    using reaches_on_Some[OF valid_window_matchP_reach_tj[OF w_def(2)]] reaches_on_run_hd_t[OF prefix]
      MatchP(5) reaches_on_progress[OF prefix, where ?phi="MatchP I r"]
    by (fastforce simp: run_args len_xs simp del: progress.simps)
  have "run_subs (ru n) (w_sj w) = None"
    using valid_eval_matchP[OF w_def(2), unfolded run_args] w_tj MatchP(4,7)
    by (cases "run_subs (ru n) (w_sj w)") (auto simp: w_def(1) args' simp del: eval_matchP.simps split: option.splits)
  then obtain j where j_def: "j < length (w_sj w)" "ru n (w_sj w ! j) = None"
    by (auto simp: run_subs_def Let_def in_set_conv_nth Option.is_none_def split: if_splits)
  have len_w_sj: "length (w_sj w) = length (collect_subfmlas r [])"
    using valid_window_matchP_reach_sj[OF w_def(2)] reach_run_subs_len
    by (auto simp: run_args)
  define phi where "phi = collect_subfmlas r [] ! j"
  have phi_in_set: "phi \<in> set (collect_subfmlas r [])"
    using j_def(1)
    by (auto simp: phi_def in_set_conv_nth len_w_sj)
  have wf: "wf_vydra phi i n (w_sj w ! j)"
    using valid_window_matchP_reach_sj[OF w_def(2)] wf[folded len_w_sj, OF _ j_def(1)] len_xs
    by (fastforce simp: run_args phi_def)
  have "i < progress phi (map fst vs)"
    using MatchP(5) phi_in_set atms_nonempty[of r] atms_finite[of r] collect_subfmlas_atms[of r "[]"]
    by auto
  then show ?case
    using MatchP(2)[OF msize_sub[OF phi_in_set] wf j_def(2)] MatchP(6,7) phi_in_set
      bf_collect_subfmlas[where ?r="r" and ?phis="[]"]
    by (auto simp: collect_subfmlas_atms)
next
  case (MatchF n I r)
  have subfmla: "msize_fmla x \<le> n" "bounded_future_fmla x" "wf_fmla x" if "x \<in> set (collect_subfmlas r [])" for x
    using that MatchF(1,6,7) le_trans[OF collect_subfmlas_msize] bf_collect_subfmlas[where ?r="r" and ?phis="[]" and ?phi=x]
      collect_subfmlas_atms[where ?phis="[]" and ?r=r]
    by auto
  have sound: "x \<in> set (collect_subfmlas r []) \<Longrightarrow> wf_vydra x j n v \<Longrightarrow> ru n v = Some (v', t, b) \<Longrightarrow> wf_vydra x (Suc j) n v' \<and> t = \<tau> \<sigma> j \<and> b = sat x j" for x j v v' t b
    using MatchF vydra_sound_aux subfmla
    by fastforce
  have "reaches_on (ru n) (su n phi) vs v \<Longrightarrow> wf_vydra phi (length vs) n v" if phi: "phi \<in> set (collect_subfmlas r [])" for phi vs v
    apply (induction vs arbitrary: v rule: rev_induct)
    using MatchF(1) wf_vydra_sub subfmla(1)[OF phi] sound[OF phi]
     apply (auto elim!: reaches_on.cases)[1]
    using sound[OF phi]
    apply (fastforce dest!: reaches_on_split_last)
    done
  then have wf: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) bs s \<Longrightarrow> j < length (collect_subfmlas r []) \<Longrightarrow>
    wf_vydra (collect_subfmlas r [] ! j) (length bs) n (s ! j)" for bs s j
    using reach_run_subs_run
    by (fastforce simp: in_set_conv_nth)
  let ?qf = "state_cnt r"
  let ?transs = "iarray_of_list (build_nfa_impl r (0, ?qf, []))"
  define args where "args = init_args ({0}, NFA.delta' ?transs ?qf, NFA.accept' ?transs ?qf) (ru_t, read_t) (run_subs (ru n))"
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[where ?r=r and ?n=n, OF _ wf _ reach_run_subs_len[where ?n=n]] sound run_t_read[of run_hd]
      read_t_run[of _ _ run_hd] ru_t_tau MatchF(5) subfmla
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  obtain w xs where w_def: "v = VYDRA_MatchF I ?transs ?qf w"
    "valid_window_matchF args I l_t0 (map (su n) (collect_subfmlas r [])) xs i w"
    using MatchF(3)
    by (auto simp: args_def elim!: wf_vydra.cases)
  note args' = args_def[unfolded init_args.simps, symmetric]
  have run_args: "w_run_t args = ru_t" "w_read_t args = read_t" "w_run_sub args = run_subs (ru n)"
    by (auto simp: args_def)
  have vs_tau: "map fst vs ! k = \<tau> \<sigma> k" if k_vs: "k < length vs" for k
    using reaches_on_split[OF prefix k_vs] run_hd_sound k_vs
    apply (cases "vs ! k")
    apply (auto)
    apply (metis fst_conv length_map nth_map prefix reaches_on_run_hd_t ru_t_tau_in)
    done
  define m where "m = min (length (map fst vs) - 1) (Min ((\<lambda>f. progress f (map fst vs)) ` atms r))"
  have m_vs: "m < length vs"
    using MatchF(5)
    by (cases vs) (auto simp: m_def split: if_splits)
  define A where "A = {j. 0 \<le> j \<and> j \<le> m \<and> memR (map fst vs ! j) (map fst vs ! m) I}"
  have m_A: "m \<in> A"
    using memR_tfin_refl[OF \<tau>_fin] vs_tau[OF m_vs]
    by (fastforce simp: A_def)
  then have A_nonempty: "A \<noteq> {}"
    by auto
  have A_finite: "finite A"
    by (auto simp: A_def)
  have p: "progress (MatchF I r) (map fst vs) = Min A"
    using MatchF(5)
    unfolding progress.simps m_def[symmetric] Let_def A_def[symmetric]
    by auto
  have i_A: "i \<notin> A"
    using MatchF(5) A_finite A_nonempty
    by (auto simp del: progress.simps simp: p)
  have i_m: "i < m"
    using MatchF(5) m_A A_finite A_nonempty
    by (auto simp del: progress.simps simp: p)
  have memR_i_m: "\<not>memR (map fst vs ! i) (map fst vs ! m) I"
    using i_A i_m
    by (auto simp: A_def)
  have i_vs: "i < length vs"
    using i_m m_vs
    by auto
  obtain ti where read_ti: "w_read_t args (w_ti w) = Some ti"
    using w_def(2) reaches_on_Some[where ?r=ru_t and ?s=l_t0 and ?s'="w_ti w"]
      reaches_on_run_hd_t[OF prefix] i_vs run_t_read[where ?t="w_ti w"]
    by (fastforce simp: valid_window_matchF_def run_args)
  have ti_def: "ti = \<tau> \<sigma> i"
    using w_def(2) ru_t_tau read_t_run[OF read_ti]
    by (fastforce simp: valid_window_matchF_def run_args)
  note reach_tj = valid_window_matchF_reach_tj[OF w_def(2), unfolded run_args]
  note reach_sj = valid_window_matchF_reach_sj[OF w_def(2), unfolded run_args]
  have len_xs: "length xs = w_j w" and memR_xs: "\<And>l. l\<in>{w_i w..<w_j w} \<Longrightarrow> memR (ts_at xs i) (ts_at xs l) I"
    and i_def: "w_i w = i"
    using w_def(2)
    unfolding valid_window_matchF_def
    by (auto simp: valid_window_matchF_def run_args)
  have j_m: "w_j w \<le> m"
    using ru_t_tau_in[OF reach_tj, of i] ru_t_tau_in[OF reach_tj, of m] memR_i_m i_m memR_xs[of m]
    unfolding vs_tau[OF i_vs] vs_tau[OF m_vs]
    by (force simp: in_set_conv_nth len_xs ts_at_def i_def)
  obtain tm tm' where tm_def: "reaches_on ru_t l_t0 (take m (map fst vs)) tm"
    "ru_t tm = Some (tm', fst (vs ! m))"
    using reaches_on_split[where ?i=m] reaches_on_run_hd_t[OF prefix] m_vs
    by fastforce
  have reach_tj_m: "reaches_on (w_run_t args) (w_tj w) (drop (w_j w) (take m (map fst vs))) tm"
    using reaches_on_split'[OF tm_def(1), where ?i="w_j w"] reaches_on_inj[OF reach_tj] m_vs j_m
    by (auto simp: len_xs run_args)
  have vs_m: "fst (vs ! m) = \<tau> \<sigma> m"
    using vs_tau[OF m_vs] m_vs
    by auto
  have memR_ti_m: "\<not>memR ti (\<tau> \<sigma> m) I"
    using memR_i_m
    unfolding vs_tau[OF i_vs] vs_tau[OF m_vs]
    by (auto simp: ti_def)
  have m_prog: "m \<le> progress phi (map fst vs)" if "phi \<in> set (collect_subfmlas r [])" for phi
    using collect_subfmlas_atms[where ?r=r and ?phis="[]"] that atms_finite[of r]
    by (auto simp: m_def min.coboundedI2)
  obtain ws s where ws_def: "reaches_on (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) ws s" "length ws = m"
    using reaches_ons_runI[where ?r=r and ?n=n and ?i=m]
      vydra_wf_reaches_on[where ?i=m and ?n=n] subfmla
      MatchF(2) m_prog
    by fastforce
  have reach_sj_m: "reaches_on (run_subs (ru n)) (w_sj w) (drop (w_j w) ws) s"
    using reaches_on_split'[OF ws_def(1), where ?i="w_j w"] reaches_on_inj[OF reach_sj] i_m j_m
    by (auto simp: ws_def(2) len_xs)
  define rho where "rho = zip (drop (w_j w) (take m (map fst vs))) (drop (w_j w) ws)"
  have map_fst_rho: "map fst rho = drop (w_j w) (take m (map fst vs))"
    and map_snd_rho: "map snd rho = drop (w_j w) ws"
    using ws_def(2) j_m m_vs
    by (auto simp: rho_def)
  show False
    using valid_eval_matchF_complete[OF w_def(2) reach_tj_m[folded map_fst_rho] reach_sj_m[folded map_snd_rho run_args] read_ti run_t_read[OF tm_def(2)[folded run_args], unfolded vs_m] memR_ti_m] MatchF(4,7)
    by (auto simp: w_def(1) args_def simp del: eval_matchF.simps)
qed

definition "ru' \<phi> = ru (msize_fmla \<phi>)"
definition "su' \<phi> = su (msize_fmla \<phi>) \<phi>"

lemma vydra_wf:
  assumes "reaches (ru n) (su n \<phi>) i v" "bounded_future_fmla \<phi>" "wf_fmla \<phi>" "msize_fmla \<phi> \<le> n"
  shows "wf_vydra \<phi> i n v"
  using assms(1)
proof (induction i arbitrary: v)
  case 0
  then show ?case
    using wf_vydra_sub[OF assms(4)]
    by (auto elim: reaches.cases)
next
  case (Suc i)
  show ?case
    using reaches_Suc_split_last[OF Suc(2)] Suc(1) vydra_sound_aux[OF assms(4) _ _ assms(2,3)]
    by fastforce
qed

lemma vydra_sound':
  assumes "reaches (ru' \<phi>) (su' \<phi>) n v" "ru' \<phi> v = Some (v', (t, b))" "bounded_future_fmla \<phi>" "wf_fmla \<phi>"
  shows "(t, b) = (\<tau> \<sigma> n, sat \<phi> n)"
  using vydra_sound_aux[OF order.refl vydra_wf[OF assms(1)[unfolded ru'_def su'_def] assms(3,4) order.refl] assms(2)[unfolded ru'_def] assms(3,4)]
  by auto

lemma vydra_complete':
  assumes prefix: "reaches_on run_hd init_hd vs e"
    and prog: "n < progress \<phi> (map fst vs)" "bounded_future_fmla \<phi>" "wf_fmla \<phi>"
  shows "\<exists>v v'. reaches (ru' \<phi>) (su' \<phi>) n v \<and> ru' \<phi> v = Some (v', (\<tau> \<sigma> n, sat \<phi> n))"
proof -
  have aux: "False" if aux_assms: "j \<le> n" "wf_vydra \<phi> j (msize_fmla \<phi>) v" "ru (msize_fmla \<phi>) v = None" for j v
    using vydra_complete_aux[OF prefix aux_assms(2,3) _ prog(2-)] aux_assms(1) prog(1)
    by auto
  obtain ws v where ws_def: "reaches_on (ru' \<phi>) (su' \<phi>) ws v" "wf_vydra \<phi> n (msize_fmla \<phi>) v" "length ws = n"
    using vydra_wf_reaches_on[OF _ prog(2,3)] aux[OF less_imp_le_nat]
    unfolding ru'_def su'_def
    by blast
  have ru_Some: "ru' \<phi> v \<noteq> None"
    using aux[OF order.refl ws_def(2)]
    by (fastforce simp: ru'_def)
  obtain v' t b where tb_def: "ru' \<phi> v = Some (v', (t, b))"
    using ru_Some
    by auto
  show ?thesis
    using reaches_on_n[OF ws_def(1)] tb_def vydra_sound'[OF reaches_on_n[OF ws_def(1)] tb_def prog(2,3)]
    by (auto simp: ws_def(3))
qed

lemma map_option_apfst_idle: "map_option (apfst snd) (map_option (apfst (Pair n)) x) = x"
  by (cases x) auto

lemma vydra_sound:
  assumes "reaches (run_vydra run_hd) (init_vydra init_hd run_hd \<phi>) n v" "run_vydra run_hd v = Some (v', (t, b))" "bounded_future_fmla \<phi>" "wf_fmla \<phi>"
  shows "(t, b) = (\<tau> \<sigma> n, sat \<phi> n)"
proof -
  have fst_v: "fst v = msize_fmla \<phi>"
    by (rule reaches_invar[OF assms(1)]) (auto simp: init_vydra_def run_vydra_def Let_def)
  have "reaches (ru' \<phi>) (su' \<phi>) n (snd v)"
    using reaches_cong[OF assms(1), where ?P="\<lambda>(m, w). m = msize_fmla \<phi>" and ?g=snd]
    by (auto simp: init_vydra_def run_vydra_def ru'_def su'_def map_option_apfst_idle Let_def simp del: sub.simps)
  then show ?thesis
    using vydra_sound'[OF _ _ assms(3,4)] assms(2) fst_v
    by (auto simp: run_vydra_def ru'_def split: prod.splits)
qed

lemma vydra_complete:
  assumes prefix: "reaches_on run_hd init_hd vs e"
    and prog: "n < progress \<phi> (map fst vs)" "bounded_future_fmla \<phi>" "wf_fmla \<phi>"
  shows "\<exists>v v'. reaches (run_vydra run_hd) (init_vydra init_hd run_hd \<phi>) n v \<and> run_vydra run_hd v = Some (v', (\<tau> \<sigma> n, sat \<phi> n))"
proof -
  obtain v v' where wits: "reaches (ru' \<phi>) (su' \<phi>) n v" "ru' \<phi> v = Some (v', \<tau> \<sigma> n, sat \<phi> n)"
    using vydra_complete'[OF assms]
    by auto
  have reach: "reaches (run_vydra run_hd) (init_vydra init_hd run_hd \<phi>) n (msize_fmla \<phi>, v)"
    using reaches_cong[OF wits(1), where ?P="\<lambda>x. True" and ?f'="run_vydra run_hd" and ?g="Pair (msize_fmla \<phi>)"]
    by (auto simp: init_vydra_def run_vydra_def ru'_def su'_def Let_def simp del: sub.simps)
  show ?thesis
    apply (rule exI[of _ "(msize_fmla \<phi>, v)"])
    apply (rule exI[of _ "(msize_fmla \<phi>, v')"])
    apply (auto simp: run_vydra_def wits(2)[unfolded ru'_def] intro: reach)
    done
qed

end

context MDL
begin

lemma reach_elem:
  assumes "reaches (\<lambda>i. if P i then Some (Suc i, (\<tau> \<sigma> i, \<Gamma> \<sigma> i)) else None) s n s'" "s = 0"
  shows "s' = n"
proof -
  obtain vs where vs_def: "reaches_on (\<lambda>i. if P i then Some (Suc i, (\<tau> \<sigma> i, \<Gamma> \<sigma> i)) else None) s vs s'" "length vs = n"
    using reaches_on[OF assms(1)]
    by auto
  have "s' = length vs"
    using vs_def(1) assms(2)
    by (induction s vs s' rule: reaches_on_rev_induct) (auto split: if_splits)
  then show ?thesis
    using vs_def(2)
    by auto
qed

interpretation default_vydra: VYDRA_MDL \<sigma> 0 "\<lambda>i. Some (Suc i, (\<tau> \<sigma> i, \<Gamma> \<sigma> i))"
  using reach_elem[where ?P="\<lambda>_. True"]
  by unfold_locales auto

end

lemma reaches_inj: "reaches r s i t \<Longrightarrow> reaches r s i t' \<Longrightarrow> t = t'"
  using reaches_on_inj reaches_on
  by metis

lemma progress_sound:
  assumes
    "\<And>n. n < length ts \<Longrightarrow> ts ! n = \<tau> \<sigma> n"
    "\<And>n. n < length ts \<Longrightarrow> \<tau> \<sigma> n = \<tau> \<sigma>' n"
    "\<And>n. n < length ts \<Longrightarrow> \<Gamma> \<sigma> n = \<Gamma> \<sigma>' n"
    "n < progress phi ts"
    "bounded_future_fmla phi"
    "wf_fmla phi"
  shows "MDL.sat \<sigma> phi n \<longleftrightarrow> MDL.sat \<sigma>' phi n"
proof -
  define run_hd where "run_hd = (\<lambda>i. if i < length ts then Some (Suc i, (\<tau> \<sigma> i, \<Gamma> \<sigma> i)) else None)"
  interpret vydra: VYDRA_MDL \<sigma> 0 run_hd
    using MDL.reach_elem[where ?P="\<lambda>i. i < length ts"]
    by unfold_locales (auto simp: run_hd_def split: if_splits)
  define run_hd' where "run_hd' = (\<lambda>i. if i < length ts then Some (Suc i, (\<tau> \<sigma>' i, \<Gamma> \<sigma>' i)) else None)"
  interpret vydra': VYDRA_MDL \<sigma>' 0 run_hd'
    using MDL.reach_elem[where ?P="\<lambda>i. i < length ts"]
    by unfold_locales (auto simp: run_hd'_def split: if_splits)
  have run_hd_hd': "run_hd = run_hd'"
    using assms(1-3)
    by (auto simp: run_hd_def run_hd'_def)
  have reaches_run_hd: "n \<le> length ts \<Longrightarrow> reaches_on run_hd 0 (map (\<lambda>i. (\<tau> \<sigma> i, \<Gamma> \<sigma> i)) [0..<n]) n" for n
    by (induction n) (auto simp: run_hd_def intro: reaches_on.intros(1) intro!: reaches_on_app)
  have ts_map: "ts = map fst (map (\<lambda>i. (\<tau> \<sigma> i, \<Gamma> \<sigma> i)) [0..<length ts])"
    by (subst map_nth[symmetric]) (auto simp: assms(1))
  obtain v v' where vv_def: "reaches (run_vydra run_hd) (init_vydra 0 run_hd phi) n v" "run_vydra run_hd v = Some (v', \<tau> \<sigma> n, vydra.sat phi n)"
    using vydra.vydra_complete[OF reaches_run_hd[OF order.refl] _ assms(5,6)] assms(4)
    unfolding ts_map[symmetric]
    by blast
  have reaches_run_hd': "n \<le> length ts \<Longrightarrow> reaches_on run_hd' 0 (map (\<lambda>i. (\<tau> \<sigma>' i, \<Gamma> \<sigma>' i)) [0..<n]) n" for n
    by (induction n) (auto simp: run_hd'_def intro: reaches_on.intros(1) intro!: reaches_on_app)
  have ts'_map: "ts = map fst (map (\<lambda>i. (\<tau> \<sigma>' i, \<Gamma> \<sigma>' i)) [0..<length ts])"
    by (subst map_nth[symmetric]) (auto simp: assms(1,2))
  obtain w w' where ww_def: "reaches (run_vydra run_hd') (init_vydra 0 run_hd' phi) n w" "run_vydra run_hd' w = Some (w', \<tau> \<sigma>' n, vydra'.sat phi n)"
    using vydra'.vydra_complete[OF reaches_run_hd'[OF order.refl] _ assms(5,6)] assms(4)
    unfolding ts'_map[symmetric]
    by blast
  note v_w = reaches_inj[OF vv_def(1) ww_def(1)[folded run_hd_hd']]
  show ?thesis
    using vv_def(2) ww_def(2)
    by (auto simp: run_hd_hd' v_w)
qed

end
